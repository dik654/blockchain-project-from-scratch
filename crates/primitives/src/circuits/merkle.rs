// Step 10b: Merkle proof 검증을 R1CS 회로로 표현
//
// native verify_merkle_proof:
//   1. current = H(key, value)
//   2. for each level: current = H(sibling, current) or H(current, sibling)
//   3. current == root
//
// R1CS 변환:
//   각 레벨:
//     boolean 제약: bit · (1 - bit) = 0            (1개)
//     조건부 선택: left/right = mux(bit, current, sibling) (2개)
//     Poseidon 해시: ~634개 제약 (full circuit)
//   루트 등치 제약: 1개
//
// 총 제약 ≈ depth × (3 + Poseidon) + Poseidon(leaf) + 1

use crate::field::Fr;
use crate::hash::poseidon::PoseidonParams;
use crate::r1cs::{ConstraintSystem, Variable, LinearCombination, Circuit};
use super::poseidon::poseidon_hash_circuit;

// ── 기본 가젯 ──────────────────────────────────────────

/// Boolean 가젯: b ∈ {0, 1}
///
/// 제약: b · (1 - b) = 0
/// b=0: 0·1=0 ✓,  b=1: 1·0=0 ✓,  b=2: 2·(-1)≠0 ✗
fn enforce_boolean(cs: &mut ConstraintSystem, b: Variable) {
    cs.enforce(
        LinearCombination::from(b),
        LinearCombination::from(Variable::One).add(-Fr::ONE, b),
        LinearCombination::zero(),
    );
}

/// 조건부 선택(mux) 가젯: result = if bit then when_true else when_false
///
/// result = when_false + bit · (when_true - when_false)
///
/// 보조 변수: t = bit · (when_true - when_false)
/// 제약: bit · (when_true - when_false) = t    (1개)
///
/// 반환: (result Variable, result value)
///
/// 주의: bit이 boolean임은 별도로 enforce_boolean으로 보장해야 함
fn mux_circuit(
    cs: &mut ConstraintSystem,
    bit: Variable,
    bit_val: Fr,
    when_true: Variable,
    when_true_val: Fr,
    when_false: Variable,
    when_false_val: Fr,
) -> (Variable, Fr) {
    let diff_val = when_true_val - when_false_val;
    let t_val = bit_val * diff_val;
    let result_val = when_false_val + t_val;

    let t = cs.alloc_witness(t_val);
    let result = cs.alloc_witness(result_val);

    // bit · (when_true - when_false) = t
    cs.enforce(
        LinearCombination::from(bit),
        LinearCombination::from(when_true).add(-Fr::ONE, when_false),
        LinearCombination::from(t),
    );

    // when_false + t = result  →  (when_false + t) · 1 = result
    cs.enforce(
        LinearCombination::from(when_false).add(Fr::ONE, t),
        LinearCombination::from(Variable::One),
        LinearCombination::from(result),
    );

    (result, result_val)
}

// ── Merkle proof 회로 ──────────────────────────────────

/// Merkle proof 검증 회로
///
/// 공개 입력: root
/// 비공개 입력: key, value, siblings (경로의 형제 해시들)
///
/// 검증 로직:
///   1. leaf = H(key, value)
///   2. 각 레벨: bit에 따라 (left, right) 결정 → H(left, right)
///   3. 최종 해시 == root
pub struct MerkleProofCircuit {
    pub root: Fr,
    pub key: Fr,
    pub value: Fr,
    pub siblings: Vec<Fr>,
    pub depth: usize,
    pub params: PoseidonParams,
}

impl Circuit for MerkleProofCircuit {
    fn synthesize(&self, cs: &mut ConstraintSystem) {
        let key_repr = self.key.to_repr();

        // 공개 입력: root
        let root_var = cs.alloc_instance(self.root);

        // 비공개 입력: key, value
        let _key_var = cs.alloc_witness(self.key);
        let _value_var = cs.alloc_witness(self.value);

        // Step 1: leaf = H(key, value)
        let (mut current_var, mut current_val) = poseidon_hash_circuit(
            cs,
            self.key,
            self.value,
            &self.params,
        );

        // Step 2: 각 레벨에서 형제와 해시
        for level in 0..self.depth {
            let sibling_val = self.siblings[level];
            let sibling_var = cs.alloc_witness(sibling_val);

            // key의 level번째 비트
            let bit = get_bit(&key_repr, level);
            let bit_val = if bit { Fr::ONE } else { Fr::ZERO };
            let bit_var = cs.alloc_witness(bit_val);

            // bit ∈ {0, 1}
            enforce_boolean(cs, bit_var);

            // bit = 0 → H(current, sibling): current가 왼쪽
            // bit = 1 → H(sibling, current): sibling이 왼쪽
            //
            // left  = mux(bit, sibling, current)  → bit=0: current, bit=1: sibling
            // right = mux(bit, current, sibling)  → bit=0: sibling, bit=1: current
            let (_left_var, left_val) = mux_circuit(
                cs, bit_var, bit_val,
                sibling_var, sibling_val,
                current_var, current_val,
            );
            let (_right_var, right_val) = mux_circuit(
                cs, bit_var, bit_val,
                current_var, current_val,
                sibling_var, sibling_val,
            );

            // H(left, right)
            let (hash_var, hash_val) = poseidon_hash_circuit(
                cs, left_val, right_val, &self.params,
            );

            current_var = hash_var;
            current_val = hash_val;
        }

        // Step 3: current == root
        cs.enforce(
            LinearCombination::from(current_var),
            LinearCombination::from(Variable::One),
            LinearCombination::from(root_var),
        );
    }
}

/// Fr 원소의 raw representation에서 i번째 비트 추출
fn get_bit(repr: &[u64; 4], i: usize) -> bool {
    if i >= 256 { return false; }
    let limb = i / 64;
    let bit = i % 64;
    (repr[limb] >> bit) & 1 == 1
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::merkle::{SparseMerkleTree, verify_merkle_proof};

    const TEST_DEPTH: usize = 4;

    #[test]
    fn boolean_gadget() {
        // b = 0
        let mut cs = ConstraintSystem::new();
        let b = cs.alloc_witness(Fr::ZERO);
        enforce_boolean(&mut cs, b);
        assert!(cs.is_satisfied());

        // b = 1
        let mut cs = ConstraintSystem::new();
        let b = cs.alloc_witness(Fr::ONE);
        enforce_boolean(&mut cs, b);
        assert!(cs.is_satisfied());

        // b = 2 → 실패
        let mut cs = ConstraintSystem::new();
        let b = cs.alloc_witness(Fr::from_u64(2));
        enforce_boolean(&mut cs, b);
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn mux_select_false() {
        let mut cs = ConstraintSystem::new();
        let bit = cs.alloc_witness(Fr::ZERO);
        let x = cs.alloc_witness(Fr::from_u64(42));
        let y = cs.alloc_witness(Fr::from_u64(99));

        let (_, result_val) = mux_circuit(
            &mut cs, bit, Fr::ZERO,
            x, Fr::from_u64(42),
            y, Fr::from_u64(99),
        );

        assert_eq!(result_val, Fr::from_u64(99)); // bit=0 → when_false
        assert!(cs.is_satisfied());
    }

    #[test]
    fn mux_select_true() {
        let mut cs = ConstraintSystem::new();
        let bit = cs.alloc_witness(Fr::ONE);
        let x = cs.alloc_witness(Fr::from_u64(42));
        let y = cs.alloc_witness(Fr::from_u64(99));

        let (_, result_val) = mux_circuit(
            &mut cs, bit, Fr::ONE,
            x, Fr::from_u64(42),
            y, Fr::from_u64(99),
        );

        assert_eq!(result_val, Fr::from_u64(42)); // bit=1 → when_true
        assert!(cs.is_satisfied());
    }

    #[test]
    fn merkle_circuit_matches_native() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let key = Fr::from_u64(5);
        let value = Fr::from_u64(42);
        tree.insert(key, value);

        let proof = tree.prove(&key);

        // native 검증
        assert!(verify_merkle_proof(tree.root, key, value, &proof));

        // circuit 검증
        let circuit = MerkleProofCircuit {
            root: tree.root,
            key,
            value,
            siblings: proof.siblings.clone(),
            depth: TEST_DEPTH,
            params: PoseidonParams::new(),
        };

        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        assert!(cs.is_satisfied());
        // 공개 입력(root)이 올바른지
        assert_eq!(cs.values[1], tree.root);
    }

    #[test]
    fn merkle_circuit_wrong_root_fails() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let key = Fr::from_u64(5);
        let value = Fr::from_u64(42);
        tree.insert(key, value);
        let proof = tree.prove(&key);

        let circuit = MerkleProofCircuit {
            root: Fr::from_u64(999), // 잘못된 루트
            key,
            value,
            siblings: proof.siblings.clone(),
            depth: TEST_DEPTH,
            params: PoseidonParams::new(),
        };

        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        assert!(!cs.is_satisfied());
    }

    #[test]
    fn merkle_circuit_wrong_value_fails() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let key = Fr::from_u64(5);
        tree.insert(key, Fr::from_u64(42));
        let proof = tree.prove(&key);

        let circuit = MerkleProofCircuit {
            root: tree.root,
            key,
            value: Fr::from_u64(99), // 잘못된 값
            siblings: proof.siblings.clone(),
            depth: TEST_DEPTH,
            params: PoseidonParams::new(),
        };

        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        assert!(!cs.is_satisfied());
    }

    #[test]
    fn merkle_circuit_multiple_entries() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);

        // key < 2^depth = 16 이어야 함 (depth=4에서 모든 키가 같은 루트 서브트리)
        let entries: Vec<(Fr, Fr)> = vec![
            (Fr::from_u64(1), Fr::from_u64(100)),
            (Fr::from_u64(5), Fr::from_u64(200)),
            (Fr::from_u64(12), Fr::from_u64(300)),
        ];

        for &(k, v) in &entries {
            tree.insert(k, v);
        }

        // 모든 엔트리에 대해 회로 검증
        for (entry_idx, &(k, v)) in entries.iter().enumerate() {
            let proof = tree.prove(&k);

            // native 검증 먼저 확인
            assert!(verify_merkle_proof(tree.root, k, v, &proof),
                "native verify failed for entry {}", entry_idx);

            let circuit = MerkleProofCircuit {
                root: tree.root,
                key: k,
                value: v,
                siblings: proof.siblings.clone(),
                depth: TEST_DEPTH,
                params: PoseidonParams::new(),
            };

            let mut cs = ConstraintSystem::new();
            circuit.synthesize(&mut cs);

            if let Some(idx) = cs.which_unsatisfied() {
                panic!("entry {} (key={:?}): constraint {} of {} failed",
                    entry_idx, k.to_repr()[0], idx, cs.num_constraints());
            }
        }
    }

    #[test]
    fn merkle_circuit_constraint_count() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        tree.insert(Fr::from_u64(1), Fr::from_u64(100));
        let proof = tree.prove(&Fr::from_u64(1));

        let circuit = MerkleProofCircuit {
            root: tree.root,
            key: Fr::from_u64(1),
            value: Fr::from_u64(100),
            siblings: proof.siblings,
            depth: TEST_DEPTH,
            params: PoseidonParams::new(),
        };

        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        println!("Merkle circuit (depth={}): {} constraints, {} variables",
            TEST_DEPTH, cs.num_constraints(), cs.num_variables());
        assert!(cs.is_satisfied());
    }
}
