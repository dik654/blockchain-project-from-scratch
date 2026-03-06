// Step 10a: Poseidon 해시를 R1CS 회로로 표현
//
// native Poseidon:
//   S-box: x → x⁵ (체 연산 3회: x², x⁴, x⁵)
//   MDS: 행렬-벡터 곱 (선형 연산)
//   라운드: AddRC → S-box → MDS, 65회 반복
//
// R1CS 변환:
//   S-box: 3개 제약 (x² = t1, t1² = t2, t2·x = y)
//   MDS: 0개 제약 (선형결합으로 흡수)
//   AddRC: 0개 제약 (선형결합의 상수항)
//
// 총 제약:
//   Full rounds: 8 × 3 (S-box/원소) × 3 (원소) = 72
//   Partial rounds: 57 × 3 (S-box) × 1 (첫 번째만) = 171
//   합계: 243개

use crate::field::Fr;
use crate::hash::poseidon::{PoseidonParams, T, RF, RP};
use crate::r1cs::{ConstraintSystem, Variable, LinearCombination, Circuit};

// ── 기본 가젯 ──────────────────────────────────────────

/// S-box 가젯: y = x⁵
///
/// 3개의 보조 변수와 3개의 제약:
///   t1 = x * x      (x²)
///   t2 = t1 * t1     (x⁴)
///   y  = t2 * x      (x⁵)
///
/// 반환: y를 나타내는 Variable
fn sbox_circuit(cs: &mut ConstraintSystem, x: Variable, x_val: Fr) -> (Variable, Fr) {
    let x2_val = x_val.square();
    let x4_val = x2_val.square();
    let x5_val = x4_val * x_val;

    let t1 = cs.alloc_witness(x2_val);
    let t2 = cs.alloc_witness(x4_val);
    let y = cs.alloc_witness(x5_val);

    // x * x = t1
    cs.enforce(
        LinearCombination::from(x),
        LinearCombination::from(x),
        LinearCombination::from(t1),
    );
    // t1 * t1 = t2
    cs.enforce(
        LinearCombination::from(t1),
        LinearCombination::from(t1),
        LinearCombination::from(t2),
    );
    // t2 * x = y
    cs.enforce(
        LinearCombination::from(t2),
        LinearCombination::from(x),
        LinearCombination::from(y),
    );

    (y, x5_val)
}

// ── Poseidon 회로 ──────────────────────────────────────

/// Poseidon 2-to-1 해시 회로
///
/// native poseidon_hash(left, right)와 동일한 계산을
/// R1CS 제약으로 표현
pub struct PoseidonCircuit {
    pub left: Fr,
    pub right: Fr,
    pub params: PoseidonParams,
}

impl Circuit for PoseidonCircuit {
    fn synthesize(&self, cs: &mut ConstraintSystem) {
        let (hash_var, hash_val) = poseidon_hash_circuit(
            cs,
            self.left,
            self.right,
            &self.params,
        );

        // 해시 결과를 공개 출력으로
        let expected = cs.alloc_instance(hash_val);
        cs.enforce(
            LinearCombination::from(hash_var),
            LinearCombination::from(Variable::One),
            LinearCombination::from(expected),
        );
    }
}

/// Poseidon 해시를 R1CS로 합성 — 내부 함수
///
/// 반환: (해시 결과 Variable, 해시 결과 Fr 값)
/// 다른 회로(Merkle)에서 재사용 가능
pub fn poseidon_hash_circuit(
    cs: &mut ConstraintSystem,
    left: Fr,
    right: Fr,
    params: &PoseidonParams,
) -> (Variable, Fr) {
    // Sponge 초기 상태: [0, left, right]
    let mut state_vals: [Fr; T] = [Fr::ZERO, left, right];
    let mut state_vars: [Variable; T] = [
        cs.alloc_witness(Fr::ZERO),
        cs.alloc_witness(left),
        cs.alloc_witness(right),
    ];

    let half_rf = RF / 2;

    // Phase 1: RF/2 = 4 full rounds
    for r in 0..half_rf {
        let offset = r * T;
        let rc = &params.round_constants[offset..offset + T];

        // AddRC + S-box (all elements) + MDS
        full_round(cs, &mut state_vars, &mut state_vals, rc, &params.mds);
    }

    // Phase 2: RP = 57 partial rounds
    for r in 0..RP {
        let offset = (half_rf + r) * T;
        let rc = &params.round_constants[offset..offset + T];

        // AddRC + S-box (first element only) + MDS
        partial_round(cs, &mut state_vars, &mut state_vals, rc, &params.mds);
    }

    // Phase 3: RF/2 = 4 full rounds
    for r in 0..half_rf {
        let offset = (half_rf + RP + r) * T;
        let rc = &params.round_constants[offset..offset + T];

        full_round(cs, &mut state_vars, &mut state_vals, rc, &params.mds);
    }

    // 출력: state[1] (첫 번째 rate 원소)
    (state_vars[1], state_vals[1])
}

/// Full round: 모든 원소에 S-box 적용
///
/// 1. AddRoundConstants (선형 → 제약 0개)
/// 2. S-box on ALL elements (비선형 → 제약 3×T = 9개)
/// 3. MDS mix (선형 → 제약 0개)
///
/// S-box 입력이 "state + rc"인 선형결합이므로,
/// 먼저 state + rc를 보조 변수에 고정한 뒤 S-box 적용
fn full_round(
    cs: &mut ConstraintSystem,
    state_vars: &mut [Variable; T],
    state_vals: &mut [Fr; T],
    rc: &[Fr],
    mds: &[[Fr; T]; T],
) {
    // Step 1: AddRC — 각 원소에 라운드 상수 더함
    let mut after_rc_vals = [Fr::ZERO; T];
    let mut after_rc_vars = [Variable::One; T]; // placeholder
    for i in 0..T {
        after_rc_vals[i] = state_vals[i] + rc[i];
        // (state + rc)를 보조 변수로 고정
        after_rc_vars[i] = cs.alloc_witness(after_rc_vals[i]);
        // 제약: state + rc·One = after_rc  →  (state + rc) · 1 = after_rc
        cs.enforce(
            LinearCombination::from(state_vars[i]).add(rc[i], Variable::One),
            LinearCombination::from(Variable::One),
            LinearCombination::from(after_rc_vars[i]),
        );
    }

    // Step 2: S-box on ALL elements
    let mut after_sbox_vals = [Fr::ZERO; T];
    let mut after_sbox_vars = [Variable::One; T];
    for i in 0..T {
        let (var, val) = sbox_circuit(cs, after_rc_vars[i], after_rc_vals[i]);
        after_sbox_vars[i] = var;
        after_sbox_vals[i] = val;
    }

    // Step 3: MDS mix — 선형결합이므로 보조 변수만 할당
    let mut new_vals = [Fr::ZERO; T];
    for i in 0..T {
        for j in 0..T {
            new_vals[i] = new_vals[i] + mds[i][j] * after_sbox_vals[j];
        }
        state_vars[i] = cs.alloc_witness(new_vals[i]);
        // MDS 선형결합을 제약으로 고정
        let mut lc = LinearCombination::zero();
        for j in 0..T {
            lc = lc.add(mds[i][j], after_sbox_vars[j]);
        }
        cs.enforce(
            lc,
            LinearCombination::from(Variable::One),
            LinearCombination::from(state_vars[i]),
        );
    }

    *state_vals = new_vals;
}

/// Partial round: 첫 번째 원소에만 S-box 적용
///
/// 1. AddRoundConstants (선형 → 제약 0개)
/// 2. S-box on FIRST element only (비선형 → 제약 3개)
/// 3. MDS mix (선형 → 제약 0개)
fn partial_round(
    cs: &mut ConstraintSystem,
    state_vars: &mut [Variable; T],
    state_vals: &mut [Fr; T],
    rc: &[Fr],
    mds: &[[Fr; T]; T],
) {
    // Step 1: AddRC
    let mut after_rc_vals = [Fr::ZERO; T];
    let mut after_rc_vars = [Variable::One; T];
    for i in 0..T {
        after_rc_vals[i] = state_vals[i] + rc[i];
        after_rc_vars[i] = cs.alloc_witness(after_rc_vals[i]);
        cs.enforce(
            LinearCombination::from(state_vars[i]).add(rc[i], Variable::One),
            LinearCombination::from(Variable::One),
            LinearCombination::from(after_rc_vars[i]),
        );
    }

    // Step 2: S-box on FIRST element only
    let mut after_sbox_vals = after_rc_vals;
    let mut after_sbox_vars: [Variable; T] = after_rc_vars;
    let (var, val) = sbox_circuit(cs, after_rc_vars[0], after_rc_vals[0]);
    after_sbox_vars[0] = var;
    after_sbox_vals[0] = val;

    // Step 3: MDS mix
    let mut new_vals = [Fr::ZERO; T];
    for i in 0..T {
        for j in 0..T {
            new_vals[i] = new_vals[i] + mds[i][j] * after_sbox_vals[j];
        }
        state_vars[i] = cs.alloc_witness(new_vals[i]);
        let mut lc = LinearCombination::zero();
        for j in 0..T {
            lc = lc.add(mds[i][j], after_sbox_vars[j]);
        }
        cs.enforce(
            lc,
            LinearCombination::from(Variable::One),
            LinearCombination::from(state_vars[i]),
        );
    }

    *state_vals = new_vals;
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::poseidon::{poseidon_hash_with_params, sbox as native_sbox};

    #[test]
    fn sbox_gadget_matches_native() {
        let mut cs = ConstraintSystem::new();
        let x_val = Fr::from_u64(7);
        let x = cs.alloc_witness(x_val);
        let (_, y_val) = sbox_circuit(&mut cs, x, x_val);

        assert_eq!(y_val, native_sbox(x_val));
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 3);
    }

    #[test]
    fn sbox_gadget_zero() {
        let mut cs = ConstraintSystem::new();
        let x_val = Fr::ZERO;
        let x = cs.alloc_witness(x_val);
        let (_, y_val) = sbox_circuit(&mut cs, x, x_val);

        assert_eq!(y_val, Fr::ZERO);
        assert!(cs.is_satisfied());
    }

    #[test]
    fn poseidon_circuit_matches_native() {
        let params = PoseidonParams::new();
        let left = Fr::from_u64(1);
        let right = Fr::from_u64(2);

        // native
        let native_hash = poseidon_hash_with_params(&params, left, right);

        // circuit
        let circuit = PoseidonCircuit {
            left,
            right,
            params: PoseidonParams::new(),
        };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        assert!(cs.is_satisfied());

        // circuit의 instance(공개 출력) = native 해시값
        // values[1]이 첫 번째 instance
        assert_eq!(cs.values[1], native_hash);
    }

    #[test]
    fn poseidon_circuit_different_inputs() {
        let params = PoseidonParams::new();

        let inputs = [
            (Fr::ZERO, Fr::ZERO),
            (Fr::from_u64(42), Fr::from_u64(0)),
            (Fr::from_u64(100), Fr::from_u64(200)),
        ];

        for (left, right) in inputs {
            let native = poseidon_hash_with_params(&params, left, right);

            let mut cs = ConstraintSystem::new();
            let (_hash_var, hash_val) = poseidon_hash_circuit(
                &mut cs, left, right, &PoseidonParams::new(),
            );

            assert_eq!(hash_val, native);
            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn poseidon_circuit_constraint_count() {
        let mut cs = ConstraintSystem::new();
        let circuit = PoseidonCircuit {
            left: Fr::from_u64(1),
            right: Fr::from_u64(2),
            params: PoseidonParams::new(),
        };
        circuit.synthesize(&mut cs);

        // 각 라운드 구조:
        //   AddRC: T개 제약 (보조 변수 고정)
        //   S-box: 3개 제약/원소
        //   MDS:   T개 제약 (보조 변수 고정)
        //
        // Full round: T(AddRC) + 3T(S-box) + T(MDS) = 5T = 15
        // Partial round: T(AddRC) + 3(S-box first only) + T(MDS) = 2T+3 = 9
        //
        // Full: 8 × 15 = 120
        // Partial: 57 × 9 = 513
        // Output equality: 1
        // Total = 120 + 513 + 1 = 634
        let total = cs.num_constraints();
        println!("Poseidon circuit constraints: {}", total);
        println!("Variables: {}", cs.num_variables());

        // 정확한 제약 수 검증
        let expected = 8 * (T + 3 * T + T) + 57 * (T + 3 + T) + 1;
        assert_eq!(total, expected);
        assert!(cs.is_satisfied());
    }

    #[test]
    fn poseidon_circuit_wrong_output_fails() {
        let mut cs = ConstraintSystem::new();
        let left = Fr::from_u64(1);
        let right = Fr::from_u64(2);
        let params = PoseidonParams::new();

        let (hash_var, _) = poseidon_hash_circuit(&mut cs, left, right, &params);

        // 잘못된 출력값을 instance로 강제
        let wrong = cs.alloc_instance(Fr::from_u64(999));
        cs.enforce(
            LinearCombination::from(hash_var),
            LinearCombination::from(Variable::One),
            LinearCombination::from(wrong),
        );

        assert!(!cs.is_satisfied());
    }
}
