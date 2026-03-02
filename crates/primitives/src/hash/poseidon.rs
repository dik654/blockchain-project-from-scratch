// Step 07: Poseidon 해시 — ZK-friendly 해시 함수
//
// SHA-256은 비트 연산(XOR, 회전, 시프트) → 회로에서 ~25,000 제약
// Poseidon은 체 산술만 사용(add, mul, pow) → ~250 제약
//
// 구조:
//   Sponge(capacity=1, rate=2) + Permutation(full rounds + partial rounds)
//
// BN254 Fr 위에서 동작 — Fr.mul/Fr.pow만으로 해시 구현

use crate::field::Fr;

// ── 파라미터 상수 ──────────────────────────────────────────

/// 상태 너비: capacity(1) + rate(2) = 3
pub const T: usize = 3;
/// S-box 지수: x → x⁵ (gcd(5, r-1) = 1이므로 S-box가 순열)
pub const ALPHA: u64 = 5;
/// Full rounds (S-box를 모든 원소에 적용): 4 + 4 = 8
pub const RF: usize = 8;
/// Partial rounds (S-box를 첫 번째 원소에만 적용): 57
pub const RP: usize = 57;
/// 총 라운드 수
pub const NUM_ROUNDS: usize = RF + RP; // 65

// ── Poseidon 파라미터 ─────────────────────────────────────

/// Poseidon 해시 파라미터
///
/// - round_constants: 라운드마다 상태에 더하는 상수 (T × NUM_ROUNDS = 195개)
/// - mds: Maximum Distance Separable 행렬 (T × T, 확산용)
pub struct PoseidonParams {
    pub round_constants: Vec<Fr>,
    pub mds: [[Fr; T]; T],
}

impl PoseidonParams {
    /// BN254 Fr 위의 Poseidon 파라미터 생성
    pub fn new() -> Self {
        PoseidonParams {
            round_constants: generate_round_constants(),
            mds: generate_mds(),
        }
    }
}

// ── S-box ──────────────────────────────────────────────────

/// S-box: x → x⁵
///
/// α = 5인 이유: gcd(5, r-1) = 1이어야 S-box가 순열(역함수 존재)
/// BN254의 r-1은 5의 배수가 아니므로 조건 충족
///
/// Fp 곱셈 횟수: square 2번 + mul 1번 = 3회
pub fn sbox(x: Fr) -> Fr {
    let x2 = x.square();
    let x4 = x2.square();
    x4 * x // x⁴ · x = x⁵
}

// ── MDS 행렬 ──────────────────────────────────────────────

/// MDS 행렬 생성
///
/// MDS = Maximum Distance Separable
/// 모든 정방 부분행렬의 행렬식 ≠ 0 → 최대 확산(diffusion)
///
/// [[2, 1, 1],
///  [1, 2, 1],
///  [1, 1, 2]]
///
/// 검증:
///   1×1 부분행렬: {2, 1} → 모두 ≠ 0 ✓
///   2×2 부분행렬: det ∈ {3, 1, -1} → 모두 ≠ 0 ✓
///   3×3: det = 4 ≠ 0 ✓
fn generate_mds() -> [[Fr; T]; T] {
    let one = Fr::from_u64(1);
    let two = Fr::from_u64(2);
    [
        [two, one, one],
        [one, two, one],
        [one, one, two],
    ]
}

/// MDS 행렬 곱: result = M · state
///
/// 행렬-벡터 곱으로 상태를 혼합 — 한 원소의 변화가 모든 원소로 확산
fn mds_mix(state: &[Fr; T], mds: &[[Fr; T]; T]) -> [Fr; T] {
    let mut result = [Fr::ZERO; T];
    for i in 0..T {
        for j in 0..T {
            result[i] = result[i] + mds[i][j] * state[j];
        }
    }
    result
}

// ── 라운드 상수 ───────────────────────────────────────────

/// 라운드 상수 결정론적 생성
///
/// 시드에서 시작하여 반복적으로 S-box 적용:
///   state_{i+1} = (state_i + i + 1)^5
///
/// 생성 과정이 결정론적이므로 같은 파라미터를 재현 가능
fn generate_round_constants() -> Vec<Fr> {
    let count = T * NUM_ROUNDS; // 3 × 65 = 195
    let mut constants = Vec::with_capacity(count);
    let mut state = Fr::from_u64(0);
    for i in 0..count {
        // 카운터를 더해서 각 상수가 고유하게
        state = state + Fr::from_u64(i as u64 + 1);
        // S-box 적용으로 비선형성 확보
        state = sbox(state);
        constants.push(state);
    }
    constants
}

// ── Poseidon 순열 (Permutation) ───────────────────────────

/// Poseidon 순열
///
/// 3단계 구조:
///   1. RF/2 full rounds  — 모든 원소에 S-box 적용 (혼란 최대)
///   2. RP partial rounds — 첫 번째 원소에만 S-box (효율성)
///   3. RF/2 full rounds  — 다시 모든 원소에 S-box (마무리)
///
/// 각 라운드:
///   1. AddRoundConstants — 상수 덧셈 (대칭성 파괴)
///   2. S-box — 비선형 변환 (x → x⁵)
///   3. MDS mix — 선형 확산 (행렬 곱)
pub fn poseidon_permutation(state: &mut [Fr; T], params: &PoseidonParams) {
    let half_rf = RF / 2; // 4

    // Phase 1: RF/2 = 4 full rounds
    for r in 0..half_rf {
        let offset = r * T;
        // AddRoundConstants
        for i in 0..T {
            state[i] = state[i] + params.round_constants[offset + i];
        }
        // S-box: ALL elements (full round)
        for i in 0..T {
            state[i] = sbox(state[i]);
        }
        // MDS mix
        *state = mds_mix(state, &params.mds);
    }

    // Phase 2: RP = 57 partial rounds
    for r in 0..RP {
        let offset = (half_rf + r) * T;
        // AddRoundConstants
        for i in 0..T {
            state[i] = state[i] + params.round_constants[offset + i];
        }
        // S-box: ONLY first element (partial round → 효율성)
        state[0] = sbox(state[0]);
        // MDS mix
        *state = mds_mix(state, &params.mds);
    }

    // Phase 3: RF/2 = 4 full rounds
    for r in 0..half_rf {
        let offset = (half_rf + RP + r) * T;
        // AddRoundConstants
        for i in 0..T {
            state[i] = state[i] + params.round_constants[offset + i];
        }
        // S-box: ALL elements (full round)
        for i in 0..T {
            state[i] = sbox(state[i]);
        }
        // MDS mix
        *state = mds_mix(state, &params.mds);
    }
}

// ── 해시 함수 ─────────────────────────────────────────────

/// 2-to-1 Poseidon 해시
///
/// Sponge 구조:
///   state = [capacity, rate₀, rate₁]
///         = [0,        left,  right ]
///
/// capacity = 0: 도메인 분리용 (다른 용도에서 다른 값)
/// rate: 입력이 들어가는 위치
///
/// Permutation 적용 후 state[1] (첫 번째 rate 원소) 반환
pub fn poseidon_hash(left: Fr, right: Fr) -> Fr {
    let params = PoseidonParams::new();
    poseidon_hash_with_params(&params, left, right)
}

/// 파라미터를 외부에서 전달하는 버전 (반복 호출 시 효율적)
pub fn poseidon_hash_with_params(params: &PoseidonParams, left: Fr, right: Fr) -> Fr {
    // Sponge: [capacity=0, rate₀=left, rate₁=right]
    let mut state = [Fr::ZERO, left, right];
    poseidon_permutation(&mut state, params);
    state[1] // 첫 번째 rate 원소가 해시 출력
}

// ── 테스트 ────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ─ S-box 검증 ─

    #[test]
    fn sbox_basic() {
        // 3⁵ = 243
        assert_eq!(sbox(Fr::from_u64(3)), Fr::from_u64(243));
    }

    #[test]
    fn sbox_two() {
        // 2⁵ = 32
        assert_eq!(sbox(Fr::from_u64(2)), Fr::from_u64(32));
    }

    #[test]
    fn sbox_one() {
        // 1⁵ = 1
        assert_eq!(sbox(Fr::ONE), Fr::ONE);
    }

    #[test]
    fn sbox_zero() {
        // 0⁵ = 0
        assert_eq!(sbox(Fr::ZERO), Fr::ZERO);
    }

    // ─ MDS 행렬 검증 ─

    #[test]
    fn mds_preserves_zero() {
        // M · [0, 0, 0] = [0, 0, 0]
        let mds = generate_mds();
        assert_eq!(mds_mix(&[Fr::ZERO; T], &mds), [Fr::ZERO; T]);
    }

    #[test]
    fn mds_basic() {
        // M · [1, 0, 0] = [2, 1, 1] (첫 번째 열)
        let mds = generate_mds();
        let state = [Fr::ONE, Fr::ZERO, Fr::ZERO];
        let result = mds_mix(&state, &mds);
        assert_eq!(result[0], Fr::from_u64(2));
        assert_eq!(result[1], Fr::from_u64(1));
        assert_eq!(result[2], Fr::from_u64(1));
    }

    #[test]
    fn mds_full() {
        // M · [1, 2, 3] = [2+2+3, 1+4+3, 1+2+6] = [7, 8, 9]
        let mds = generate_mds();
        let state = [Fr::from_u64(1), Fr::from_u64(2), Fr::from_u64(3)];
        let result = mds_mix(&state, &mds);
        assert_eq!(result[0], Fr::from_u64(7));
        assert_eq!(result[1], Fr::from_u64(8));
        assert_eq!(result[2], Fr::from_u64(9));
    }

    // ─ 라운드 상수 검증 ─

    #[test]
    fn round_constants_deterministic() {
        let c1 = generate_round_constants();
        let c2 = generate_round_constants();
        assert_eq!(c1.len(), c2.len());
        for (a, b) in c1.iter().zip(c2.iter()) {
            assert_eq!(a, b);
        }
    }

    #[test]
    fn round_constants_count() {
        let c = generate_round_constants();
        assert_eq!(c.len(), T * NUM_ROUNDS); // 195
    }

    #[test]
    fn round_constants_all_nonzero() {
        let c = generate_round_constants();
        for (i, val) in c.iter().enumerate() {
            assert!(!val.is_zero(), "round constant {} is zero", i);
        }
    }

    // ─ 순열 검증 ─

    #[test]
    fn permutation_changes_state() {
        let params = PoseidonParams::new();
        let original = [Fr::from_u64(1), Fr::from_u64(2), Fr::from_u64(3)];
        let mut state = original;
        poseidon_permutation(&mut state, &params);
        assert_ne!(state, original);
    }

    #[test]
    fn permutation_deterministic() {
        let params = PoseidonParams::new();
        let input = [Fr::from_u64(42), Fr::from_u64(0), Fr::from_u64(1)];

        let mut s1 = input;
        let mut s2 = input;
        poseidon_permutation(&mut s1, &params);
        poseidon_permutation(&mut s2, &params);
        assert_eq!(s1, s2);
    }

    #[test]
    fn permutation_different_inputs() {
        let params = PoseidonParams::new();
        let mut s1 = [Fr::from_u64(1), Fr::from_u64(2), Fr::from_u64(3)];
        let mut s2 = [Fr::from_u64(1), Fr::from_u64(2), Fr::from_u64(4)];
        poseidon_permutation(&mut s1, &params);
        poseidon_permutation(&mut s2, &params);
        assert_ne!(s1, s2);
    }

    // ─ 해시 검증 ─

    #[test]
    fn hash_determinism() {
        let a = Fr::from_u64(1);
        let b = Fr::from_u64(2);
        assert_eq!(poseidon_hash(a, b), poseidon_hash(a, b));
    }

    #[test]
    fn hash_nonzero_output() {
        // hash(0, 0)도 0이 아닌 값을 반환
        let h = poseidon_hash(Fr::ZERO, Fr::ZERO);
        assert!(!h.is_zero());
    }

    #[test]
    fn hash_collision_resistance_right() {
        // 오른쪽 입력만 다르면 → 다른 해시
        let h1 = poseidon_hash(Fr::from_u64(1), Fr::from_u64(2));
        let h2 = poseidon_hash(Fr::from_u64(1), Fr::from_u64(3));
        assert_ne!(h1, h2);
    }

    #[test]
    fn hash_collision_resistance_left() {
        // 왼쪽 입력만 다르면 → 다른 해시
        let h1 = poseidon_hash(Fr::from_u64(1), Fr::from_u64(2));
        let h2 = poseidon_hash(Fr::from_u64(3), Fr::from_u64(2));
        assert_ne!(h1, h2);
    }

    #[test]
    fn hash_order_matters() {
        // hash(a, b) ≠ hash(b, a) — 입력 순서가 중요
        let h1 = poseidon_hash(Fr::from_u64(1), Fr::from_u64(2));
        let h2 = poseidon_hash(Fr::from_u64(2), Fr::from_u64(1));
        assert_ne!(h1, h2);
    }

    #[test]
    fn hash_sensitivity() {
        // 입력을 1만 바꿔도 출력이 완전히 달라져야 함 (avalanche)
        let h1 = poseidon_hash(Fr::from_u64(100), Fr::from_u64(200));
        let h2 = poseidon_hash(Fr::from_u64(101), Fr::from_u64(200));
        assert_ne!(h1, h2);
    }

    #[test]
    fn hash_with_params_matches() {
        // poseidon_hash와 poseidon_hash_with_params가 동일한 결과
        let params = PoseidonParams::new();
        let a = Fr::from_u64(7);
        let b = Fr::from_u64(13);
        assert_eq!(
            poseidon_hash(a, b),
            poseidon_hash_with_params(&params, a, b)
        );
    }
}
