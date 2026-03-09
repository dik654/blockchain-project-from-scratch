// Step 13: KZG 다항식 Commitment — 페어링 기반 다항식 약정
//
// KZG란?
//   Kate-Zaverucha-Goldberg (2010)가 제안한 다항식 commitment 스킴
//   - 다항식을 하나의 타원곡선 점으로 commit (O(1) 크기)
//   - 특정 점에서의 evaluation을 pairing check로 증명
//   - PLONK의 핵심 빌딩 블록
//
// Groth16과의 차이:
//   Groth16: per-circuit setup (회로마다 새 τ, α, β, γ, δ 필요)
//   KZG: universal setup (한 번의 τ 생성으로 모든 다항식에 재사용)
//
// 전체 흐름:
//   1. Trusted Setup: 랜덤 τ → SRS = { [τⁱ]₁, [τʲ]₂ }
//   2. Commit: 다항식 f(x) → [f(τ)]₁ (하나의 G1 점)
//   3. Open: 점 z에서 f(z)=y를 증명하는 증거 π 생성
//   4. Verify: 페어링 체크로 π 검증
//
// 핵심 아이디어:
//   f(z) = y  ⟺  (x - z) | (f(x) - y)
//   즉, q(x) = (f(x) - y) / (x - z) 가 다항식이어야 함
//
//   SRS로 commit하면:
//     e(π, [τ - z]₂) = e(C - [y]₁, G₂)
//   검증자는 τ를 모르지만 페어링으로 이 관계를 확인 가능
//
// 보안 모델:
//   - τ는 setup 후 반드시 삭제 (toxic waste)
//   - Groth16보다 단순한 setup (τ 하나만 필요, α/β/γ/δ 불필요)
//   - binding: 다른 다항식 → 다른 commitment (DL 가정)
//   - hiding: τ가 비밀이면 commitment에서 다항식 복원 불가
//
// 검증 방정식 유도:
//   q(x) = (f(x) - y) / (x - z)
//   ⟹ f(x) - y = q(x) · (x - z)
//   τ에서 평가:
//   ⟹ f(τ) - y = q(τ) · (τ - z)
//   커브 포인트로:
//   ⟹ [f(τ)]₁ - [y]₁ = q(τ) · [τ - z]  (스칼라 관계)
//   페어링으로 확인:
//   ⟹ e([q(τ)]₁, [τ - z]₂) = e([f(τ) - y]₁, G₂)
//
//   2-pairing 최적화 (G2 scalar_mul 회피):
//   ⟹ e(π, [τ]₂) = e(C - [y]₁ + z·π, G₂)

use crate::field::Fr;
use crate::curve::{G1, G2, pairing};
use crate::qap::Polynomial;

use rand::Rng;

// ── 랜덤 Fr 생성 ────────────────────────────────────────

/// 랜덤 Fr 원소 생성
///
/// 4개의 u64 랜덤 → Fr::from_raw로 Montgomery 변환
fn random_fr<R: Rng>(rng: &mut R) -> Fr {
    let limbs: [u64; 4] = [
        rng.gen(), rng.gen(), rng.gen(), rng.gen(),
    ];
    Fr::from_raw(limbs)
}

/// 0이 아닌 랜덤 Fr 원소 (toxic waste에 사용)
fn random_nonzero_fr<R: Rng>(rng: &mut R) -> Fr {
    loop {
        let f = random_fr(rng);
        if !f.is_zero() { return f; }
    }
}

// ── 자료구조 ────────────────────────────────────────────

/// SRS (Structured Reference String) — Universal Setup 결과
///
/// Groth16의 (ProvingKey, VerifyingKey)와 달리,
/// KGZ의 SRS는 **universal** — 한 번 생성하면 어떤 다항식에도 재사용.
///
/// 구조:
///   g1_powers[i] = [τⁱ]₁  (i = 0, 1, ..., max_degree)
///   g2_powers[j] = [τʲ]₂  (j = 0, 1, ..., max_degree_g2)
///
/// G2 powers가 필요한 이유:
///   단일 점 검증: [τ⁰]₂ = G₂ 와 [τ¹]₂ 만 있으면 충분
///   다중 점 검증: vanishing polynomial Z(x)의 commitment [Z(τ)]₂ 필요
///                 → degree(Z) = 점의 수 만큼의 G2 powers 필요
pub struct SRS {
    /// [τ⁰]₁, [τ¹]₁, ..., [τ^max_degree]₁
    pub g1_powers: Vec<G1>,
    /// [τ⁰]₂, [τ¹]₂, ..., [τ^max_degree_g2]₂
    pub g2_powers: Vec<G2>,
}

/// KZG Commitment — 다항식의 약정
///
/// C = [f(τ)]₁ = Σᵢ fᵢ · [τⁱ]₁
///
/// 하나의 G1 점으로 다항식 전체를 표현
/// BN254에서 commitment 크기 = 64바이트
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Commitment(pub G1);

/// KZG Opening Proof — 단일 점 평가 증명
///
/// f(z) = y 를 증명하기 위한 데이터:
///   point: 평가 점 z
///   value: 평가 값 y = f(z)
///   proof: π = [q(τ)]₁ where q(x) = (f(x) - y) / (x - z)
pub struct Opening {
    pub point: Fr,
    pub value: Fr,
    pub proof: G1,
}

/// KZG Batch Opening — 다중 점 평가 증명
///
/// f(z₁)=y₁, ..., f(zₖ)=yₖ 를 한 번에 증명
///
/// 알고리즘:
///   Z(x) = ∏(x - zᵢ)           ← vanishing polynomial
///   I(x) s.t. I(zᵢ) = yᵢ       ← interpolation polynomial
///   q(x) = (f(x) - I(x)) / Z(x) ← quotient
///   π = commit(q)
pub struct BatchOpening {
    pub points: Vec<Fr>,
    pub values: Vec<Fr>,
    pub proof: G1,
}

// ── Trusted Setup ───────────────────────────────────────

/// Trusted Setup — SRS 생성
///
/// τ를 랜덤 생성하고 powers of τ를 커브 포인트로 인코딩한다.
///
/// max_degree: G1 powers의 최대 차수 (G1 크기 = max_degree + 1)
/// max_degree_g2: G2 powers의 최대 차수
///   단일 점 검증만 필요하면 1이면 충분 ([τ⁰]₂, [τ¹]₂)
///   batch k점 검증이면 k 이상 필요
///
/// ⚠️ τ는 이 함수 종료 시 스택에서 소멸 (Rust 소유권)
///    프로덕션에서는 MPC 세레모니로 τ를 분산 생성
pub fn setup<R: Rng>(
    max_degree: usize,
    max_degree_g2: usize,
    rng: &mut R,
) -> SRS {
    let tau = random_nonzero_fr(rng);
    let g1 = G1::generator();
    let g2 = G2::generator();

    // G1 powers: [τ⁰]₁, [τ¹]₁, ..., [τ^max_degree]₁
    let mut g1_powers = Vec::with_capacity(max_degree + 1);
    let mut tau_power = Fr::ONE;
    for _ in 0..=max_degree {
        g1_powers.push(g1.scalar_mul(&tau_power.to_repr()));
        tau_power = tau_power * tau;
    }

    // G2 powers: [τ⁰]₂, [τ¹]₂, ..., [τ^max_degree_g2]₂
    let mut g2_powers = Vec::with_capacity(max_degree_g2 + 1);
    tau_power = Fr::ONE;
    for _ in 0..=max_degree_g2 {
        g2_powers.push(g2.scalar_mul(&tau_power.to_repr()));
        tau_power = tau_power * tau;
    }

    SRS { g1_powers, g2_powers }
}

// ── Commit ──────────────────────────────────────────────

/// 다항식을 G1에서 commit
///
/// commit(f) = Σᵢ fᵢ · [τⁱ]₁ = [f(τ)]₁
///
/// 시간 복잡도: O(d) 스칼라 곱 (d = 다항식 차수)
/// 결과 크기: 하나의 G1 점 (64바이트)
pub fn commit(srs: &SRS, poly: &Polynomial) -> Commitment {
    if poly.is_zero() {
        return Commitment(G1::identity());
    }
    assert!(
        poly.coeffs.len() <= srs.g1_powers.len(),
        "polynomial degree {} exceeds SRS max degree {}",
        poly.degree(), srs.g1_powers.len() - 1
    );

    let mut result = G1::identity();
    for (i, &coeff) in poly.coeffs.iter().enumerate() {
        if !coeff.is_zero() {
            result = result + srs.g1_powers[i].scalar_mul(&coeff.to_repr());
        }
    }
    Commitment(result)
}

/// 다항식을 G2에서 commit (batch verification용)
///
/// vanishing polynomial [Z(τ)]₂ 계산에 필요
fn commit_g2(srs: &SRS, poly: &Polynomial) -> G2 {
    if poly.is_zero() {
        return G2::identity();
    }
    assert!(
        poly.coeffs.len() <= srs.g2_powers.len(),
        "polynomial degree {} exceeds SRS G2 max degree {}",
        poly.degree(), srs.g2_powers.len() - 1
    );

    let mut result = G2::identity();
    for (i, &coeff) in poly.coeffs.iter().enumerate() {
        if !coeff.is_zero() {
            result = result + srs.g2_powers[i].scalar_mul(&coeff.to_repr());
        }
    }
    result
}

// ── Open (단일 점) ──────────────────────────────────────

/// 단일 점 opening proof 생성
///
/// f(z) = y 임을 증명하는 π 생성
///
/// 알고리즘:
///   1. y = f(z) 계산
///   2. n(x) = f(x) - y          ← n(z) = f(z) - y = 0
///   3. d(x) = x - z
///   4. q(x) = n(x) / d(x)      ← 나머지 없이 나누어짐 (n(z)=0이므로)
///   5. π = commit(q) = [q(τ)]₁
pub fn open(srs: &SRS, poly: &Polynomial, point: Fr) -> Opening {
    let value = poly.eval(point);

    // n(x) = f(x) - y
    let y_poly = Polynomial::constant(value);
    let numerator = poly - &y_poly;

    // d(x) = x - z
    let denominator = Polynomial::from_coeffs(vec![-point, Fr::ONE]);

    // q(x) = n(x) / d(x)
    let (quotient, remainder) = numerator.div_rem(&denominator);
    debug_assert!(
        remainder.is_zero(),
        "f(z) = y should make (f(x) - y) divisible by (x - z)"
    );

    let proof = commit(srs, &quotient).0;

    Opening { point, value, proof }
}

// ── Verify (단일 점) ────────────────────────────────────

/// 단일 점 opening 검증
///
/// 검증 방정식 (2-pairing 최적화):
///   e(π, [τ]₂) == e(C - [y]₁ + z·π, G₂)
///
/// 유도:
///   f(τ) - y = q(τ) · (τ - z)
///
///   naive 형태:
///     e(π, [τ]₂ - z·G₂) = e(C - [y]₁, G₂)
///
///   최적화:
///     e(π, [τ]₂) · e(-π, z·G₂) = e(C - [y]₁, G₂)
///     e(π, [τ]₂) = e(C - [y]₁ + z·π, G₂)
///
///   2번째 형태가 G2에서의 scalar_mul을 피해 더 효율적
pub fn verify(srs: &SRS, commitment: &Commitment, opening: &Opening) -> bool {
    assert!(
        srs.g2_powers.len() >= 2,
        "SRS needs at least [τ⁰]₂ and [τ¹]₂ for verification"
    );

    let g1 = G1::generator();
    let g2 = srs.g2_powers[0];    // G₂ = [τ⁰]₂
    let tau_g2 = srs.g2_powers[1]; // [τ]₂

    let z = opening.point;
    let y = opening.value;
    let pi = opening.proof;

    // LHS: e(π, [τ]₂)
    let lhs = pairing(&pi, &tau_g2);

    // RHS: e(C - [y]₁ + z·π, G₂)
    let y_g1 = g1.scalar_mul(&y.to_repr());
    let z_pi = pi.scalar_mul(&z.to_repr());
    let rhs_g1 = commitment.0 + (-y_g1) + z_pi;
    let rhs = pairing(&rhs_g1, &g2);

    lhs == rhs
}

// ── Batch Open (다중 점) ────────────────────────────────

/// vanishing polynomial: Z(x) = ∏(x - zᵢ)
fn vanishing_poly(points: &[Fr]) -> Polynomial {
    let mut result = Polynomial::from_coeffs(vec![Fr::ONE]);
    for &z in points {
        let factor = Polynomial::from_coeffs(vec![-z, Fr::ONE]);
        result = &result * &factor;
    }
    result
}

/// 다중 점 opening proof 생성
///
/// f(z₁)=y₁, ..., f(zₖ)=yₖ 를 한 번에 증명
///
/// 알고리즘:
///   1. 각 점에서 평가값 계산: yᵢ = f(zᵢ)
///   2. vanishing polynomial: Z(x) = ∏(x - zᵢ)
///   3. interpolation polynomial: I(x) s.t. I(zᵢ) = yᵢ
///      → Lagrange 보간으로 구성
///   4. f(x) - I(x)는 모든 zᵢ에서 0
///      → Z(x) | (f(x) - I(x))
///   5. quotient: q(x) = (f(x) - I(x)) / Z(x)
///   6. proof: π = commit(q) = [q(τ)]₁
pub fn batch_open(srs: &SRS, poly: &Polynomial, points: &[Fr]) -> BatchOpening {
    assert!(!points.is_empty(), "at least one point required");

    // 1. 평가값 계산
    let values: Vec<Fr> = points.iter().map(|&z| poly.eval(z)).collect();

    // 2. vanishing polynomial: Z(x) = ∏(x - zᵢ)
    let vanishing = vanishing_poly(points);

    // 3. interpolation polynomial: I(zᵢ) = yᵢ
    let interp_points: Vec<(Fr, Fr)> = points.iter()
        .zip(values.iter())
        .map(|(&z, &y)| (z, y))
        .collect();
    let interpolation = Polynomial::lagrange_interpolate(&interp_points);

    // 4. quotient: (f(x) - I(x)) / Z(x)
    let numerator = poly - &interpolation;
    let (quotient, remainder) = numerator.div_rem(&vanishing);
    debug_assert!(
        remainder.is_zero(),
        "f(x) - I(x) should be divisible by Z(x)"
    );

    // 5. π = commit(q)
    let proof = commit(srs, &quotient).0;

    BatchOpening {
        points: points.to_vec(),
        values,
        proof,
    }
}

// ── Batch Verify (다중 점) ──────────────────────────────

/// 다중 점 opening 검증
///
/// 검증 방정식:
///   e(π, [Z(τ)]₂) = e(C - [I(τ)]₁, G₂)
///
/// 유도:
///   q(x) = (f(x) - I(x)) / Z(x)
///   → f(τ) - I(τ) = q(τ) · Z(τ)
///   → e([q(τ)]₁, [Z(τ)]₂) = e([f(τ) - I(τ)]₁, G₂)
///   → e(π, [Z(τ)]₂) = e(C - [I(τ)]₁, G₂)
///
/// [Z(τ)]₂ 계산에 G2 powers 필요: degree(Z) = 점의 수
pub fn batch_verify(
    srs: &SRS,
    commitment: &Commitment,
    opening: &BatchOpening,
) -> bool {
    assert!(!opening.points.is_empty());

    let g2 = srs.g2_powers[0]; // G₂

    // 1. vanishing polynomial: Z(x) = ∏(x - zᵢ)
    let vanishing = vanishing_poly(&opening.points);
    assert!(
        vanishing.coeffs.len() <= srs.g2_powers.len(),
        "vanishing polynomial degree {} exceeds SRS G2 max degree {}",
        vanishing.degree(), srs.g2_powers.len() - 1
    );

    // 2. [Z(τ)]₂ — G2에서 commit
    let z_g2 = commit_g2(srs, &vanishing);

    // 3. interpolation polynomial: I(x) s.t. I(zᵢ) = yᵢ
    let interp_points: Vec<(Fr, Fr)> = opening.points.iter()
        .zip(opening.values.iter())
        .map(|(&z, &y)| (z, y))
        .collect();
    let interpolation = Polynomial::lagrange_interpolate(&interp_points);

    // 4. [I(τ)]₁ — G1에서 commit
    let i_commitment = commit(srs, &interpolation);

    // 5. 검증: e(π, [Z(τ)]₂) = e(C - [I(τ)]₁, G₂)
    let lhs = pairing(&opening.proof, &z_g2);
    let rhs_g1 = commitment.0 + (-i_commitment.0);
    let rhs = pairing(&rhs_g1, &g2);

    lhs == rhs
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    // ── SRS 구조 테스트 ──────────────────────────────────

    #[test]
    fn srs_structure() {
        // SRS가 올바른 크기로 생성되는지 확인
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 2, &mut rng);
        assert_eq!(srs.g1_powers.len(), 5); // degree 0..4
        assert_eq!(srs.g2_powers.len(), 3); // degree 0..2
    }

    #[test]
    fn srs_g1_powers_consistent() {
        // τ의 powers가 일관되는지 pairing으로 확인:
        //   e([τ¹]₁, [τ¹]₂) = e([τ²]₁, [τ⁰]₂)
        //   양변 = e(G₁, G₂)^(τ²)
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 2, &mut rng);

        let lhs = pairing(&srs.g1_powers[1], &srs.g2_powers[1]);
        let rhs = pairing(&srs.g1_powers[2], &srs.g2_powers[0]);
        assert_eq!(lhs, rhs);
    }

    // ── Commit 테스트 ────────────────────────────────────

    #[test]
    fn commit_constant() {
        // f(x) = 5 → C = 5 · [τ⁰]₁ = 5 · G₁
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::constant(Fr::from_u64(5));
        let c = commit(&srs, &poly);
        let expected = G1::generator().scalar_mul(&Fr::from_u64(5).to_repr());
        assert_eq!(c.0, expected);
    }

    #[test]
    fn commit_zero() {
        // f(x) = 0 → C = identity
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::zero();
        let c = commit(&srs, &poly);
        assert_eq!(c.0, G1::identity());
    }

    // ── 단일 점 Open/Verify 테스트 ──────────────────────

    #[test]
    fn open_verify_linear() {
        // f(x) = 2x + 3, z=5 → y=13
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(2)]);
        let c = commit(&srs, &poly);
        let opening = open(&srs, &poly, Fr::from_u64(5));

        assert_eq!(opening.value, Fr::from_u64(13));
        assert!(verify(&srs, &c, &opening));
    }

    #[test]
    fn open_verify_quadratic() {
        // f(x) = x² + 2x + 1, z=3 → y=9+6+1=16
        let mut rng = ChaCha20Rng::seed_from_u64(100);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::from_coeffs(vec![
            Fr::from_u64(1), Fr::from_u64(2), Fr::from_u64(1),
        ]);
        let c = commit(&srs, &poly);
        let opening = open(&srs, &poly, Fr::from_u64(3));

        assert_eq!(opening.value, Fr::from_u64(16));
        assert!(verify(&srs, &c, &opening));
    }

    #[test]
    fn open_verify_at_zero() {
        // f(x) = x³ + 1, z=0 → y=1
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::from_coeffs(vec![
            Fr::from_u64(1), Fr::ZERO, Fr::ZERO, Fr::from_u64(1),
        ]);
        let c = commit(&srs, &poly);
        let opening = open(&srs, &poly, Fr::ZERO);

        assert_eq!(opening.value, Fr::from_u64(1));
        assert!(verify(&srs, &c, &opening));
    }

    #[test]
    fn open_verify_cubic() {
        // f(x) = x³ + 2x² + 3x + 4, z=2 → y=8+8+6+4=26
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::from_coeffs(vec![
            Fr::from_u64(4), Fr::from_u64(3), Fr::from_u64(2), Fr::from_u64(1),
        ]);
        let c = commit(&srs, &poly);
        let opening = open(&srs, &poly, Fr::from_u64(2));

        assert_eq!(opening.value, Fr::from_u64(26));
        assert!(verify(&srs, &c, &opening));
    }

    #[test]
    fn multiple_openings_same_commitment() {
        // 같은 다항식, 같은 commitment, 여러 점에서 open → 각각 verify 성공
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::from_coeffs(vec![
            Fr::from_u64(1), Fr::from_u64(1), Fr::from_u64(1),
        ]); // x² + x + 1

        let c = commit(&srs, &poly);

        for z in [0u64, 1, 2, 5, 100] {
            let opening = open(&srs, &poly, Fr::from_u64(z));
            assert!(verify(&srs, &c, &opening),
                "verification failed at z={}", z);
        }
    }

    // ── 검증 실패 테스트 ─────────────────────────────────

    #[test]
    fn verify_wrong_value_fails() {
        // f(x) = 2x + 3, z=5 → y=13이지만 y=99로 위조
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(2)]);
        let c = commit(&srs, &poly);
        let mut opening = open(&srs, &poly, Fr::from_u64(5));

        opening.value = Fr::from_u64(99);
        assert!(!verify(&srs, &c, &opening));
    }

    #[test]
    fn verify_wrong_point_fails() {
        // z=5에서 열었지만 z=7로 변조
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(2)]);
        let c = commit(&srs, &poly);
        let mut opening = open(&srs, &poly, Fr::from_u64(5));

        opening.point = Fr::from_u64(7);
        assert!(!verify(&srs, &c, &opening));
    }

    #[test]
    fn verify_tampered_proof_fails() {
        // proof π를 변조
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(2)]);
        let c = commit(&srs, &poly);
        let mut opening = open(&srs, &poly, Fr::from_u64(5));

        opening.proof = opening.proof + G1::generator();
        assert!(!verify(&srs, &c, &opening));
    }

    #[test]
    fn verify_wrong_commitment_fails() {
        // 다른 다항식의 commitment으로 검증 시도
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly1 = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(2)]);
        let poly2 = Polynomial::from_coeffs(vec![Fr::from_u64(7), Fr::from_u64(5)]);
        let c2 = commit(&srs, &poly2); // 다른 다항식의 commitment
        let opening = open(&srs, &poly1, Fr::from_u64(5));

        assert!(!verify(&srs, &c2, &opening));
    }

    // ── Commitment 속성 테스트 ───────────────────────────

    #[test]
    fn commitment_binding() {
        // 다른 다항식 → 다른 commitment (binding 속성)
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly1 = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(2)]);
        let poly2 = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(4)]);
        let c1 = commit(&srs, &poly1);
        let c2 = commit(&srs, &poly2);
        assert_ne!(c1, c2);
    }

    #[test]
    fn different_srs_different_commitment() {
        // 다른 τ → 같은 다항식이어도 다른 commitment
        let mut rng1 = ChaCha20Rng::seed_from_u64(42);
        let mut rng2 = ChaCha20Rng::seed_from_u64(99);
        let srs1 = setup(4, 1, &mut rng1);
        let srs2 = setup(4, 1, &mut rng2);
        let poly = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(2)]);
        let c1 = commit(&srs1, &poly);
        let c2 = commit(&srs2, &poly);
        assert_ne!(c1, c2);
    }

    #[test]
    fn commitment_additivity() {
        // commit(f) + commit(g) = commit(f + g) — 동형 속성
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let f = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(2)]);
        let g = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(4)]);
        let fg = &f + &g;

        let cf = commit(&srs, &f);
        let cg = commit(&srs, &g);
        let cfg = commit(&srs, &fg);

        assert_eq!(cf.0 + cg.0, cfg.0);
    }

    // ── Batch Open/Verify 테스트 ─────────────────────────

    #[test]
    fn batch_open_verify() {
        // f(x) = x² + 1, points [1, 2, 3] → values [2, 5, 10]
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 3, &mut rng); // G2 degree ≥ #points
        let poly = Polynomial::from_coeffs(vec![
            Fr::from_u64(1), Fr::ZERO, Fr::from_u64(1),
        ]);
        let c = commit(&srs, &poly);
        let points = vec![Fr::from_u64(1), Fr::from_u64(2), Fr::from_u64(3)];
        let opening = batch_open(&srs, &poly, &points);

        assert_eq!(opening.values[0], Fr::from_u64(2));   // 1+1
        assert_eq!(opening.values[1], Fr::from_u64(5));   // 4+1
        assert_eq!(opening.values[2], Fr::from_u64(10));  // 9+1
        assert!(batch_verify(&srs, &c, &opening));
    }

    #[test]
    fn batch_verify_wrong_value_fails() {
        // batch 값 하나 위조 → 검증 실패
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 3, &mut rng);
        let poly = Polynomial::from_coeffs(vec![
            Fr::from_u64(1), Fr::ZERO, Fr::from_u64(1),
        ]);
        let c = commit(&srs, &poly);
        let points = vec![Fr::from_u64(1), Fr::from_u64(2), Fr::from_u64(3)];
        let mut opening = batch_open(&srs, &poly, &points);

        opening.values[1] = Fr::from_u64(999);
        assert!(!batch_verify(&srs, &c, &opening));
    }

    #[test]
    fn batch_single_point_consistency() {
        // batch_open 1점 = single open 의미적 동일 → 각각 검증 성공
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let srs = setup(4, 1, &mut rng);
        let poly = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(2)]);
        let c = commit(&srs, &poly);

        let single = open(&srs, &poly, Fr::from_u64(5));
        let batch = batch_open(&srs, &poly, &[Fr::from_u64(5)]);

        assert_eq!(single.value, batch.values[0]);
        assert!(verify(&srs, &c, &single));
        assert!(batch_verify(&srs, &c, &batch));
    }
}
