// Step 08a: Sparse Merkle Tree — Poseidon 기반 멤버십 증명
//
// 2^depth개의 리프를 가진 이진 해시 트리. 대부분의 리프는 비어 있으므로
// 기본 해시(default_hashes)로 대체하여 효율적으로 저장.
//
// 핵심 연산:
//   parent = poseidon_hash(left_child, right_child)
//   → 2-to-1 해시를 반복 적용하여 root 하나로 전체 집합을 요약
//
// 사용처:
//   Step 25: chain state tree (계정 상태의 암호학적 요약)
//   Step 43-45: privacy mixer (commitment 멤버십 증명)
//   Step 10: R1CS 가젯 (회로 안에서의 Merkle 검증)

use std::collections::HashMap;
use crate::field::Fr;
use crate::hash::poseidon::{poseidon_hash_with_params, PoseidonParams};

// ── 비트 연산 헬퍼 ──────────────────────────────────────

/// Fr 원소의 raw representation에서 i번째 비트 추출
///
/// key의 비트가 트리 경로를 결정:
///   bit = 0 → 왼쪽 자식,  bit = 1 → 오른쪽 자식
fn get_bit(repr: &[u64; 4], i: usize) -> bool {
    if i >= 256 { return false; }
    let limb = i / 64;
    let bit = i % 64;
    (repr[limb] >> bit) & 1 == 1
}

/// [u64; 4]를 n비트 오른쪽 시프트
///
/// 레벨 i에서의 노드 인덱스 = key >> i
fn shr_bits(val: &[u64; 4], n: usize) -> [u64; 4] {
    if n >= 256 { return [0; 4]; }
    if n == 0 { return *val; }
    let word_shift = n / 64;
    let bit_shift = n % 64;
    let mut result = [0u64; 4];
    for i in 0..(4 - word_shift) {
        result[i] = val[i + word_shift] >> bit_shift;
        if bit_shift > 0 && i + word_shift + 1 < 4 {
            result[i] |= val[i + word_shift + 1] << (64 - bit_shift);
        }
    }
    result
}

/// 비트 0 반전 — 형제 노드의 인덱스를 구할 때 사용
///
/// 같은 레벨에서 형제(sibling)는 인덱스의 최하위 비트만 다르다
fn flip_bit0(val: &[u64; 4]) -> [u64; 4] {
    [val[0] ^ 1, val[1], val[2], val[3]]
}

// ── Merkle Proof ────────────────────────────────────────

/// 머클 증명: 경로상의 형제 노드 해시값들
///
/// 증명 크기: depth개의 Fr 원소
/// 검증 비용: depth회의 Poseidon 해시
pub struct MerkleProof {
    pub siblings: Vec<Fr>,
}

// ── Sparse Merkle Tree ──────────────────────────────────

/// Poseidon 기반 Sparse Merkle Tree
///
/// 키 공간: Fr 원소의 비트 표현 → 2^depth개의 가능한 리프
/// 대부분 비어 있으므로 기본 해시(default_hashes)로 대체
/// 실제 저장: 삽입된 키의 경로상 노드만 HashMap에 보관
pub struct SparseMerkleTree {
    pub depth: usize,
    pub root: Fr,
    /// default_hashes[i] = 높이 i에서의 빈 서브트리 해시
    ///   default[0] = ZERO (빈 리프)
    ///   default[i+1] = H(default[i], default[i])
    default_hashes: Vec<Fr>,
    /// (level, index) → 해시값
    /// level 0 = 리프, level depth = 루트
    /// index = key_repr >> level
    nodes: HashMap<(usize, [u64; 4]), Fr>,
    /// key_repr → value (원본 값 저장, get용)
    leaves: HashMap<[u64; 4], Fr>,
    params: PoseidonParams,
}

impl SparseMerkleTree {
    /// 빈 트리 생성
    ///
    /// default_hashes를 미리 계산:
    ///   default[0] = ZERO (빈 리프)
    ///   default[i+1] = H(default[i], default[i])
    pub fn new(depth: usize) -> Self {
        let params = PoseidonParams::new();

        let mut default_hashes = vec![Fr::ZERO; depth + 1];
        for i in 0..depth {
            default_hashes[i + 1] = poseidon_hash_with_params(
                &params,
                default_hashes[i],
                default_hashes[i],
            );
        }
        let root = default_hashes[depth];

        SparseMerkleTree {
            depth,
            root,
            default_hashes,
            nodes: HashMap::new(),
            leaves: HashMap::new(),
            params,
        }
    }

    /// 키-값 쌍 삽입 (또는 갱신)
    ///
    /// 1. 리프 해시 = H(key, value) — key 포함으로 second preimage 방지
    /// 2. 리프에서 루트까지 경로의 모든 중간 노드를 재계산
    ///
    /// 비용: depth회의 Poseidon 해시
    pub fn insert(&mut self, key: Fr, value: Fr) {
        let key_repr = key.to_repr();

        // 원본 값 저장
        self.leaves.insert(key_repr, value);

        // 리프 해시 = H(key, value)
        let leaf_hash = poseidon_hash_with_params(&self.params, key, value);
        self.nodes.insert((0, key_repr), leaf_hash);

        let mut current = leaf_hash;

        // 리프(level 0)에서 루트(level depth)까지 경로 갱신
        for level in 0..self.depth {
            let node_idx = shr_bits(&key_repr, level);
            let sibling_idx = flip_bit0(&node_idx);

            let sibling = self.nodes
                .get(&(level, sibling_idx))
                .copied()
                .unwrap_or(self.default_hashes[level]);

            // bit = 0이면 current가 왼쪽, sibling이 오른쪽
            // bit = 1이면 sibling이 왼쪽, current가 오른쪽
            current = if !get_bit(&key_repr, level) {
                poseidon_hash_with_params(&self.params, current, sibling)
            } else {
                poseidon_hash_with_params(&self.params, sibling, current)
            };

            let parent_idx = shr_bits(&key_repr, level + 1);
            self.nodes.insert((level + 1, parent_idx), current);
        }

        self.root = current;
    }

    /// 키로 값 조회
    pub fn get(&self, key: &Fr) -> Option<Fr> {
        self.leaves.get(&key.to_repr()).copied()
    }

    /// 머클 증명 생성
    ///
    /// key의 경로를 따라 각 레벨의 형제 노드 해시를 수집
    /// 이 siblings + key + value로 루트를 재구성하여 검증 가능
    pub fn prove(&self, key: &Fr) -> MerkleProof {
        let key_repr = key.to_repr();
        let mut siblings = Vec::with_capacity(self.depth);

        for level in 0..self.depth {
            let node_idx = shr_bits(&key_repr, level);
            let sibling_idx = flip_bit0(&node_idx);

            let sibling = self.nodes
                .get(&(level, sibling_idx))
                .copied()
                .unwrap_or(self.default_hashes[level]);

            siblings.push(sibling);
        }

        MerkleProof { siblings }
    }
}

// ── 증명 검증 (독립 함수) ──────────────────────────────

/// 머클 증명 검증
///
/// 트리 없이도 root, key, value, proof만으로 검증 가능
/// → ZK 검증자가 트리를 갖고 있지 않아도 됨
///
/// 알고리즘:
///   1. current = H(key, value)  (리프 해시 재계산)
///   2. 각 레벨: bit에 따라 H(current, sibling) 또는 H(sibling, current)
///   3. 최종 current == root이면 유효
pub fn verify_merkle_proof(
    root: Fr,
    key: Fr,
    value: Fr,
    proof: &MerkleProof,
) -> bool {
    let params = PoseidonParams::new();
    let key_repr = key.to_repr();
    let mut current = poseidon_hash_with_params(&params, key, value);

    for (level, sibling) in proof.siblings.iter().enumerate() {
        current = if !get_bit(&key_repr, level) {
            poseidon_hash_with_params(&params, current, *sibling)
        } else {
            poseidon_hash_with_params(&params, *sibling, current)
        };
    }

    current == root
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // 테스트용 작은 깊이 (depth=256이면 해시 256회/insert로 느림)
    const TEST_DEPTH: usize = 8;

    #[test]
    fn empty_tree_has_nonzero_root() {
        let tree = SparseMerkleTree::new(TEST_DEPTH);
        // H(H(H(...ZERO...))) ≠ ZERO
        assert!(!tree.root.is_zero());
    }

    #[test]
    fn insert_changes_root() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let old_root = tree.root;
        tree.insert(Fr::from_u64(1), Fr::from_u64(42));
        assert_ne!(tree.root, old_root);
    }

    #[test]
    fn get_returns_inserted_value() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let key = Fr::from_u64(5);
        let value = Fr::from_u64(100);
        tree.insert(key, value);
        assert_eq!(tree.get(&key), Some(value));
    }

    #[test]
    fn get_returns_none_for_absent_key() {
        let tree = SparseMerkleTree::new(TEST_DEPTH);
        assert_eq!(tree.get(&Fr::from_u64(99)), None);
    }

    #[test]
    fn proof_verifies() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let key = Fr::from_u64(7);
        let value = Fr::from_u64(42);
        tree.insert(key, value);

        let proof = tree.prove(&key);
        assert!(verify_merkle_proof(tree.root, key, value, &proof));
    }

    #[test]
    fn proof_fails_wrong_value() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let key = Fr::from_u64(7);
        tree.insert(key, Fr::from_u64(42));

        let proof = tree.prove(&key);
        assert!(!verify_merkle_proof(tree.root, key, Fr::from_u64(99), &proof));
    }

    #[test]
    fn proof_fails_wrong_root() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let key = Fr::from_u64(7);
        let value = Fr::from_u64(42);
        tree.insert(key, value);

        let proof = tree.prove(&key);
        assert!(!verify_merkle_proof(Fr::from_u64(1), key, value, &proof));
    }

    #[test]
    fn multiple_inserts_all_verifiable() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let entries: Vec<(Fr, Fr)> = (0..5)
            .map(|i| (Fr::from_u64(i * 10 + 1), Fr::from_u64(i * 100)))
            .collect();

        for &(key, value) in &entries {
            tree.insert(key, value);
        }

        for &(key, value) in &entries {
            let proof = tree.prove(&key);
            assert!(verify_merkle_proof(tree.root, key, value, &proof));
        }
    }

    #[test]
    fn overwrite_updates_root_and_proof() {
        let mut tree = SparseMerkleTree::new(TEST_DEPTH);
        let key = Fr::from_u64(3);
        tree.insert(key, Fr::from_u64(100));
        let root1 = tree.root;

        tree.insert(key, Fr::from_u64(200));
        let root2 = tree.root;

        assert_ne!(root1, root2);
        assert_eq!(tree.get(&key), Some(Fr::from_u64(200)));

        let proof = tree.prove(&key);
        assert!(verify_merkle_proof(root2, key, Fr::from_u64(200), &proof));
    }

    #[test]
    fn deterministic_root() {
        let mut t1 = SparseMerkleTree::new(TEST_DEPTH);
        let mut t2 = SparseMerkleTree::new(TEST_DEPTH);

        t1.insert(Fr::from_u64(1), Fr::from_u64(10));
        t1.insert(Fr::from_u64(2), Fr::from_u64(20));

        t2.insert(Fr::from_u64(1), Fr::from_u64(10));
        t2.insert(Fr::from_u64(2), Fr::from_u64(20));

        assert_eq!(t1.root, t2.root);
    }

    #[test]
    fn different_keys_different_roots() {
        let mut t1 = SparseMerkleTree::new(TEST_DEPTH);
        let mut t2 = SparseMerkleTree::new(TEST_DEPTH);

        t1.insert(Fr::from_u64(1), Fr::from_u64(42));
        t2.insert(Fr::from_u64(2), Fr::from_u64(42));

        assert_ne!(t1.root, t2.root);
    }
}
