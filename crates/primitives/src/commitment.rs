// Step 08b: Commitment — 값 은닉 + 나중에 검증
//
// commit(value, randomness) = poseidon_hash(value, randomness)
//
// Hiding: randomness가 균일 랜덤이면, commitment에서 value를 역산 불가
//   → Poseidon의 pre-image resistance (2^127)
//
// Binding: 같은 commitment에 다른 (value, randomness)를 찾는 것은
//   → Poseidon의 collision resistance (2^127)
//
// 왜 해시 기반인가 (vs Pedersen v·g + r·h):
//   - ZK 회로에서 ~250 제약 (Pedersen은 ~수천, scalar mul 필요)
//   - Mixer/Semaphore에서는 동형성이 불필요
//   - Step 07의 Poseidon을 직접 재사용
//
// 사용처:
//   Step 43: Note commitment = H(nullifier, secret)
//   Step 44: Commitment pool (Merkle tree에 commitment 삽입)
//   Step 45: Mixer 회로 (commitment 재계산을 ZK로 증명)

use crate::field::Fr;
use crate::hash::poseidon::poseidon_hash;

/// 커밋먼트 생성
///
/// commit(value, randomness) = poseidon_hash(value, randomness)
///
/// value: 은닉할 값
/// randomness: 블라인딩 팩터 (hiding을 위해 반드시 랜덤이어야 함)
pub fn commit(value: Fr, randomness: Fr) -> Fr {
    poseidon_hash(value, randomness)
}

/// 커밋먼트 검증 (open)
///
/// commitment을 열어서 원래 값이 맞는지 확인:
///   H(value, randomness) == commitment?
pub fn verify_commitment(commitment: Fr, value: Fr, randomness: Fr) -> bool {
    commit(value, randomness) == commitment
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commit_and_verify() {
        let value = Fr::from_u64(42);
        let randomness = Fr::from_u64(12345);
        let c = commit(value, randomness);
        assert!(verify_commitment(c, value, randomness));
    }

    #[test]
    fn wrong_value_fails() {
        let value = Fr::from_u64(42);
        let randomness = Fr::from_u64(12345);
        let c = commit(value, randomness);
        assert!(!verify_commitment(c, Fr::from_u64(99), randomness));
    }

    #[test]
    fn wrong_randomness_fails() {
        let value = Fr::from_u64(42);
        let randomness = Fr::from_u64(12345);
        let c = commit(value, randomness);
        assert!(!verify_commitment(c, value, Fr::from_u64(99999)));
    }

    #[test]
    fn deterministic() {
        let v = Fr::from_u64(7);
        let r = Fr::from_u64(13);
        assert_eq!(commit(v, r), commit(v, r));
    }

    #[test]
    fn hiding_different_randomness() {
        // 같은 value, 다른 randomness → 다른 commitment (hiding)
        let value = Fr::from_u64(42);
        let c1 = commit(value, Fr::from_u64(1));
        let c2 = commit(value, Fr::from_u64(2));
        assert_ne!(c1, c2);
    }

    #[test]
    fn binding_different_value() {
        // 다른 value, 같은 randomness → 다른 commitment (binding)
        let r = Fr::from_u64(100);
        let c1 = commit(Fr::from_u64(1), r);
        let c2 = commit(Fr::from_u64(2), r);
        assert_ne!(c1, c2);
    }

    #[test]
    fn commitment_is_nonzero() {
        // H(0, 0) ≠ 0 (Poseidon 출력은 거의 항상 비영)
        let c = commit(Fr::ZERO, Fr::ZERO);
        assert!(!c.is_zero());
    }
}
