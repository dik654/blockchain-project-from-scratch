// Step 16: PLONK Prover/Verifier
//
// PLONK이란?
//   Permutations over Lagrange-bases for Oecumenical Noninteractive
//   arguments of Knowledge (Gabizon-Williamson-Ciobotaru, 2019)
//
// 이 모듈의 역할:
//   Steps 13-15에서 구축한 빌딩 블록을 결합하여 완전한 증명 시스템 구현:
//   - KZG polynomial commitment (Step 13)
//   - PLONKish arithmetization + permutation argument (Step 14)
//   - Fiat-Shamir heuristic로 비대화형 변환
//
// 프로토콜 개요 (5 라운드):
//   Round 1: Wire 다항식 commit → [a]₁, [b]₁, [c]₁
//   Round 2: Permutation grand product Z(x) commit → [Z]₁
//   Round 3: Quotient 다항식 T(x) 분할 commit → [t_lo]₁, [t_mid]₁, [t_hi]₁
//   Round 4: 챌린지 점 ζ에서 평가값 계산
//   Round 5: Opening proof 생성 → W_ζ, W_{ζω}
//
// 검증:
//   Verifier는 증명에서 Fiat-Shamir 챌린지를 재현하고,
//   linearization commitment + batched pairing check로 검증
//
// 설계 결정:
//   - Blinding 없음 (교육용: zero-knowledge 속성 생략)
//   - Plookup 미포함 (permutation-only PLONK)
//   - Poseidon hash 기반 Fiat-Shamir transcript
//
// 의존성:
//   kzg::{SRS, Commitment, setup, commit} — 다항식 commitment
//   plonk::{Domain, K1, K2} — 평가 도메인
//   plonk::arithmetization — 제약 시스템
//   plonk::permutation — permutation argument
//   hash::poseidon — Fiat-Shamir 해시

use crate::field::{Fr, Fp};
use crate::curve::{G1, pairing};
use crate::qap::Polynomial;
use crate::kzg::{self, SRS, Commitment};
use crate::hash::poseidon::poseidon_hash;
use super::{Domain, K1, K2};
use super::arithmetization::PlonkConstraintSystem;
use super::permutation::{compute_permutation_polynomials, compute_grand_product};

use rand::Rng;

// ── G1 → Fr 변환 (transcript용) ──────────────────────────

/// G1 점을 transcript에 넣기 위해 Fr 값으로 변환
///
/// Jacobian (X, Y, Z) → affine x좌표 = X/Z² → Fp → Fr
/// identity 점은 Fr::ZERO로 매핑
fn g1_to_fr(point: &G1) -> Fr {
    if point.is_identity() {
        return Fr::ZERO;
    }
    let z_inv = point.z.inv().expect("non-identity point has invertible Z");
    let z_inv_sq = z_inv * z_inv;
    let affine_x: Fp = point.x * z_inv_sq;
    // Fp와 Fr은 같은 [u64; 4] 표현 → from_raw로 mod r 축소
    Fr::from_raw(affine_x.to_repr())
}

// ── Fiat-Shamir Transcript ───────────────────────────────

/// Fiat-Shamir 트랜스크립트
///
/// Prover와 verifier가 동일한 순서로 데이터를 추가하면
/// 동일한 챌린지가 도출된다. Poseidon hash 사용.
struct Transcript {
    state: Fr,
}

impl Transcript {
    /// 빈 트랜스크립트 생성
    fn new() -> Self {
        Transcript { state: Fr::ZERO }
    }

    /// KZG commitment (G1 점) 추가
    fn append_commitment(&mut self, c: &Commitment) {
        let fr_val = g1_to_fr(&c.0);
        self.state = poseidon_hash(self.state, fr_val);
    }

    /// 스칼라 값 추가
    fn append_scalar(&mut self, s: &Fr) {
        self.state = poseidon_hash(self.state, *s);
    }

    /// 챌린지 도출
    ///
    /// Fr::ONE과 해시하여 domain separation 보장
    fn challenge(&mut self) -> Fr {
        self.state = poseidon_hash(self.state, Fr::ONE);
        self.state
    }
}

// ── 자료구조 ─────────────────────────────────────────────

/// Verification Key — 회로 구조에서 미리 계산
///
/// Selector와 permutation 다항식의 KZG commitment 포함.
/// Witness에 독립적 — 같은 회로 구조면 같은 VK.
pub struct VerifyingKey {
    /// Selector 다항식 commitments
    pub q_l_comm: Commitment,
    pub q_r_comm: Commitment,
    pub q_o_comm: Commitment,
    pub q_m_comm: Commitment,
    pub q_c_comm: Commitment,
    /// Permutation 다항식 commitments
    pub sigma_a_comm: Commitment,
    pub sigma_b_comm: Commitment,
    pub sigma_c_comm: Commitment,
    /// 도메인 크기 (게이트 수, 2의 거듭제곱)
    pub n: usize,
    /// n차 단위근
    pub omega: Fr,
}

/// PLONK Setup 결과: SRS + VerifyingKey
pub struct PlonkSetupParams {
    pub srs: SRS,
    pub vk: VerifyingKey,
}

/// PLONK 증명 — 5-round 프로토콜의 출력
///
/// 크기: 7 G1 commitments + 6 Fr evaluations + 2 G1 opening proofs
///      = 9 G1 점 + 6 Fr 스칼라
pub struct PlonkProof {
    // Round 1: wire commitments
    pub a_comm: Commitment,
    pub b_comm: Commitment,
    pub c_comm: Commitment,
    // Round 2: permutation grand product
    pub z_comm: Commitment,
    // Round 3: quotient polynomial (3분할)
    pub t_lo_comm: Commitment,
    pub t_mid_comm: Commitment,
    pub t_hi_comm: Commitment,
    // Round 4: ζ에서의 평가값
    pub a_eval: Fr,
    pub b_eval: Fr,
    pub c_eval: Fr,
    pub sigma_a_eval: Fr,
    pub sigma_b_eval: Fr,
    pub z_omega_eval: Fr,
    // Round 5: opening proofs
    pub w_zeta: G1,
    pub w_zeta_omega: G1,
}

// ── Setup ────────────────────────────────────────────────

/// PLONK Setup: SRS 생성 + selector/permutation commit → VerifyingKey
///
/// 전제 조건:
///   - cs는 pad_to_power_of_two() 완료 상태
///   - domain.n == cs.num_gates()
///
/// SRS max_degree = 3n + 5:
///   quotient T(x)는 degree ~3(n-1), 여유분 포함
pub fn plonk_setup<R: Rng>(
    cs: &PlonkConstraintSystem,
    domain: &Domain,
    rng: &mut R,
) -> PlonkSetupParams {
    let n = domain.n;
    assert_eq!(cs.num_gates(), n, "CS must be padded to domain size");

    // SRS 생성: G1은 3n+5, G2는 1 (단일점 검증용)
    let srs = kzg::setup(3 * n + 5, 1, rng);

    // Selector 다항식 commit
    let selectors = cs.selector_polynomials(domain);
    let q_l_comm = kzg::commit(&srs, &selectors.q_l);
    let q_r_comm = kzg::commit(&srs, &selectors.q_r);
    let q_o_comm = kzg::commit(&srs, &selectors.q_o);
    let q_m_comm = kzg::commit(&srs, &selectors.q_m);
    let q_c_comm = kzg::commit(&srs, &selectors.q_c);

    // Permutation 다항식 commit
    let (sigma_a, sigma_b, sigma_c) = compute_permutation_polynomials(cs, domain);
    let sigma_a_comm = kzg::commit(&srs, &sigma_a);
    let sigma_b_comm = kzg::commit(&srs, &sigma_b);
    let sigma_c_comm = kzg::commit(&srs, &sigma_c);

    PlonkSetupParams {
        srs,
        vk: VerifyingKey {
            q_l_comm,
            q_r_comm,
            q_o_comm,
            q_m_comm,
            q_c_comm,
            sigma_a_comm,
            sigma_b_comm,
            sigma_c_comm,
            n,
            omega: domain.omega,
        },
    }
}

// ── Prove ────────────────────────────────────────────────

/// PLONK 증명 생성 (5-round Fiat-Shamir)
///
/// 전제 조건:
///   - cs는 pad_to_power_of_two() 완료, is_satisfied() == true
///   - domain.n == cs.num_gates()
///   - srs.g1_powers.len() >= 3n + 6
pub fn prove(
    srs: &SRS,
    cs: &PlonkConstraintSystem,
    domain: &Domain,
) -> PlonkProof {
    let n = domain.n;
    let omega = domain.omega;
    let k1 = Fr::from_u64(K1);
    let k2 = Fr::from_u64(K2);

    // ── 사전 계산 ──────────────────────────────────────
    let selectors = cs.selector_polynomials(domain);
    let (a_poly, b_poly, c_poly) = cs.wire_polynomials(domain);
    let (sigma_a, sigma_b, sigma_c) = compute_permutation_polynomials(cs, domain);

    let mut transcript = Transcript::new();

    // ── Round 1: Wire Commitments ──────────────────────
    let a_comm = kzg::commit(srs, &a_poly);
    let b_comm = kzg::commit(srs, &b_poly);
    let c_comm = kzg::commit(srs, &c_poly);

    transcript.append_commitment(&a_comm);
    transcript.append_commitment(&b_comm);
    transcript.append_commitment(&c_comm);

    // ── Round 2: Permutation Grand Product ─────────────
    let beta = transcript.challenge();
    let gamma = transcript.challenge();

    let z_poly = compute_grand_product(
        cs, domain, &sigma_a, &sigma_b, &sigma_c, beta, gamma,
    );
    let z_comm = kzg::commit(srs, &z_poly);

    transcript.append_commitment(&z_comm);

    // ── Round 3: Quotient Polynomial ───────────────────
    let alpha = transcript.challenge();
    let alpha_sq = alpha * alpha;

    // Gate constraint: G(x) = q_L·a + q_R·b + q_O·c + q_M·(a·b) + q_C
    let ab_poly = &a_poly * &b_poly;
    let gate_constraint =
        &(&(&(&selectors.q_l * &a_poly) + &(&selectors.q_r * &b_poly))
            + &(&selectors.q_o * &c_poly))
            + &(&(&selectors.q_m * &ab_poly) + &selectors.q_c);

    // Z(ωx) — shifted polynomial: coeffs[i] *= ω^i
    let z_shifted = {
        let mut coeffs = z_poly.coeffs.clone();
        let mut omega_pow = Fr::ONE;
        for c in coeffs.iter_mut() {
            *c = *c * omega_pow;
            omega_pow = omega_pow * omega;
        }
        Polynomial::from_coeffs(coeffs)
    };

    // Permutation constraint 1:
    //   P1(x) = Z(x)·(a+β·x+γ)(b+β·K₁·x+γ)(c+β·K₂·x+γ)
    //         - Z(ωx)·(a+β·σ_A+γ)(b+β·σ_B+γ)(c+β·σ_C+γ)

    // Identity 쪽: (a(x) + β·x + γ), (b(x) + β·K₁·x + γ), (c(x) + β·K₂·x + γ)
    let beta_x = Polynomial::from_coeffs(vec![gamma, beta]);
    let beta_k1_x = Polynomial::from_coeffs(vec![gamma, beta * k1]);
    let beta_k2_x = Polynomial::from_coeffs(vec![gamma, beta * k2]);

    let term_a_id = &a_poly + &beta_x;
    let term_b_id = &b_poly + &beta_k1_x;
    let term_c_id = &c_poly + &beta_k2_x;

    let id_product = &z_poly * &(&term_a_id * &(&term_b_id * &term_c_id));

    // Sigma 쪽: (a(x) + β·σ_A(x) + γ), ...
    let gamma_const = Polynomial::constant(gamma);
    let term_a_sigma = &a_poly + &(&sigma_a.scale(beta) + &gamma_const);
    let term_b_sigma = &b_poly + &(&sigma_b.scale(beta) + &gamma_const);
    let term_c_sigma = &c_poly + &(&sigma_c.scale(beta) + &gamma_const);

    let sigma_product = &z_shifted * &(&term_a_sigma * &(&term_b_sigma * &term_c_sigma));

    let perm_constraint_1 = &id_product - &sigma_product;

    // Permutation constraint 2: (Z(x) - 1) · L₁(x)
    // L₁(ωⁱ) = 1 if i=0, 0 otherwise
    let l1 = {
        let points: Vec<(Fr, Fr)> = (0..n)
            .map(|i| {
                let val = if i == 0 { Fr::ONE } else { Fr::ZERO };
                (domain.elements[i], val)
            })
            .collect();
        Polynomial::lagrange_interpolate(&points)
    };

    let z_minus_one = &z_poly - &Polynomial::constant(Fr::ONE);
    let perm_constraint_2 = &z_minus_one * &l1;

    // 결합: numerator = G + α·P1 + α²·P2
    let combined = &(&gate_constraint + &perm_constraint_1.scale(alpha))
        + &perm_constraint_2.scale(alpha_sq);

    // Z_H(x) = x^n - 1
    let z_h = {
        let mut coeffs = vec![Fr::ZERO; n + 1];
        coeffs[0] = -Fr::ONE;
        coeffs[n] = Fr::ONE;
        Polynomial::from_coeffs(coeffs)
    };

    // T(x) = combined / Z_H(x)
    let (t_poly, remainder) = combined.div_rem(&z_h);
    debug_assert!(
        remainder.is_zero(),
        "quotient polynomial remainder must be zero"
    );

    // T 3분할: t_lo(x) + x^n·t_mid(x) + x^{2n}·t_hi(x)
    let t_coeffs = &t_poly.coeffs;
    let t_len = t_coeffs.len();

    let t_lo = Polynomial::from_coeffs(
        t_coeffs[..n.min(t_len)].to_vec(),
    );
    let t_mid = if n < t_len {
        Polynomial::from_coeffs(t_coeffs[n..(2 * n).min(t_len)].to_vec())
    } else {
        Polynomial::zero()
    };
    let t_hi = if 2 * n < t_len {
        Polynomial::from_coeffs(t_coeffs[2 * n..].to_vec())
    } else {
        Polynomial::zero()
    };

    let t_lo_comm = kzg::commit(srs, &t_lo);
    let t_mid_comm = kzg::commit(srs, &t_mid);
    let t_hi_comm = kzg::commit(srs, &t_hi);

    transcript.append_commitment(&t_lo_comm);
    transcript.append_commitment(&t_mid_comm);
    transcript.append_commitment(&t_hi_comm);

    // ── Round 4: Evaluations at ζ ──────────────────────
    let zeta = transcript.challenge();

    let a_eval = a_poly.eval(zeta);
    let b_eval = b_poly.eval(zeta);
    let c_eval = c_poly.eval(zeta);
    let sigma_a_eval = sigma_a.eval(zeta);
    let sigma_b_eval = sigma_b.eval(zeta);
    let z_omega_eval = z_poly.eval(zeta * omega);

    transcript.append_scalar(&a_eval);
    transcript.append_scalar(&b_eval);
    transcript.append_scalar(&c_eval);
    transcript.append_scalar(&sigma_a_eval);
    transcript.append_scalar(&sigma_b_eval);
    transcript.append_scalar(&z_omega_eval);

    // ── Round 5: Opening Proofs ────────────────────────
    let nu = transcript.challenge();

    // ζ^n, ζ^{2n}
    let zeta_n = {
        let mut z = Fr::ONE;
        for _ in 0..n {
            z = z * zeta;
        }
        z
    };
    let zeta_2n = zeta_n * zeta_n;
    let z_h_zeta = zeta_n - Fr::ONE; // Z_H(ζ) = ζ^n - 1

    // L₁(ζ) = (ζ^n - 1) / (n · (ζ - 1))
    let l1_zeta = z_h_zeta
        * (Fr::from_u64(n as u64) * (zeta - Fr::ONE))
            .inv()
            .expect("n*(zeta-1) must be invertible");

    // Linearization polynomial r(x)
    //
    // 표준 PLONK linearization: 다항식곱을 스칼라·다항식으로 분해
    //
    // Gate 부분: q_L(x)·ā + q_R(x)·b̄ + q_O(x)·c̄ + q_M(x)·ā·b̄ + q_C(x)
    //   → G(ζ) 그대로 (wire 값을 스칼라로 대체)
    //
    // Permutation 부분: σ_C(x)를 다항식으로 유지, 나머지는 스칼라 평가값 사용
    //   → r(ζ) = P1(ζ) + 상수잔여 → 상수잔여를 빼서 r(ζ)=0 보장
    //
    // 상수잔여 = α · z̄_ω · perm_den_partial · (c̄+γ) + α² · L₁(ζ)
    //   원인 1: σ 쪽에서 (c̄+β·σ_C(ζ)+γ)를 β·σ_C(x)만 다항식으로 남기므로 (c̄+γ) 부분이 잔여
    //   원인 2: P2 = (Z-1)·L₁ → linearization에서 Z(x)·L₁(ζ)만 사용, -L₁(ζ) 잔여

    let r_gate = &(&(&selectors.q_l.scale(a_eval) + &selectors.q_r.scale(b_eval))
        + &selectors.q_o.scale(c_eval))
        + &(&selectors.q_m.scale(a_eval * b_eval) + &selectors.q_c);

    let perm_num = (a_eval + beta * zeta + gamma)
        * (b_eval + beta * k1 * zeta + gamma)
        * (c_eval + beta * k2 * zeta + gamma);
    let perm_den_partial = (a_eval + beta * sigma_a_eval + gamma)
        * (b_eval + beta * sigma_b_eval + gamma);

    let r_perm = &z_poly.scale(alpha * perm_num + alpha_sq * l1_zeta)
        - &sigma_c.scale(alpha * perm_den_partial * z_omega_eval * beta);

    let t_combined = &(&t_lo + &t_mid.scale(zeta_n)) + &t_hi.scale(zeta_2n);
    let r_quot = t_combined.scale(z_h_zeta);

    // 상수잔여 보정: r(ζ) = 0이 되도록
    let r_constant = alpha * z_omega_eval * perm_den_partial * (c_eval + gamma)
        + alpha_sq * l1_zeta;

    let r_poly_pre = &(&r_gate + &r_perm) - &r_quot;
    let r_poly = &r_poly_pre - &Polynomial::constant(r_constant);

    // Batch opening at ζ:
    // W_ζ(x) = [r(x) + ν·(a(x)-ā) + ν²·(b(x)-b̄) + ν³·(c(x)-c̄)
    //          + ν⁴·(σ_A(x)-σ̄_A) + ν⁵·(σ_B(x)-σ̄_B)] / (x-ζ)
    let nu2 = nu * nu;
    let nu3 = nu2 * nu;
    let nu4 = nu3 * nu;
    let nu5 = nu4 * nu;

    let batch_poly = &(&(&(&(&r_poly
        + &(&a_poly - &Polynomial::constant(a_eval)).scale(nu))
        + &(&b_poly - &Polynomial::constant(b_eval)).scale(nu2))
        + &(&c_poly - &Polynomial::constant(c_eval)).scale(nu3))
        + &(&sigma_a - &Polynomial::constant(sigma_a_eval)).scale(nu4))
        + &(&sigma_b - &Polynomial::constant(sigma_b_eval)).scale(nu5);

    let divisor_zeta = Polynomial::from_coeffs(vec![-zeta, Fr::ONE]);
    let (w_zeta_poly, rem) = batch_poly.div_rem(&divisor_zeta);
    debug_assert!(rem.is_zero(), "batch opening remainder at zeta must be zero");
    let w_zeta = kzg::commit(srs, &w_zeta_poly).0;

    // Opening at ζω:
    // W_{ζω}(x) = [Z(x) - z̄_ω] / (x - ζω)
    let z_minus_eval = &z_poly - &Polynomial::constant(z_omega_eval);
    let divisor_zeta_omega = Polynomial::from_coeffs(vec![-(zeta * omega), Fr::ONE]);
    let (w_zeta_omega_poly, rem2) = z_minus_eval.div_rem(&divisor_zeta_omega);
    debug_assert!(rem2.is_zero(), "opening remainder at zeta*omega must be zero");
    let w_zeta_omega = kzg::commit(srs, &w_zeta_omega_poly).0;

    PlonkProof {
        a_comm,
        b_comm,
        c_comm,
        z_comm,
        t_lo_comm,
        t_mid_comm,
        t_hi_comm,
        a_eval,
        b_eval,
        c_eval,
        sigma_a_eval,
        sigma_b_eval,
        z_omega_eval,
        w_zeta,
        w_zeta_omega,
    }
}

// ── Verify ───────────────────────────────────────────────

/// PLONK 증명 검증
///
/// Fiat-Shamir 챌린지를 재현하고 batched pairing check로 검증.
///
/// public_inputs: 공개 입력 값 (현재 미사용, 빈 슬라이스 전달)
pub fn verify(
    srs: &SRS,
    vk: &VerifyingKey,
    proof: &PlonkProof,
    _public_inputs: &[Fr],
) -> bool {
    let n = vk.n;
    let omega = vk.omega;
    let k1 = Fr::from_u64(K1);
    let k2 = Fr::from_u64(K2);

    // ── Step 1: Fiat-Shamir 챌린지 재현 ────────────────
    let mut transcript = Transcript::new();

    // Round 1
    transcript.append_commitment(&proof.a_comm);
    transcript.append_commitment(&proof.b_comm);
    transcript.append_commitment(&proof.c_comm);
    let beta = transcript.challenge();
    let gamma = transcript.challenge();

    // Round 2
    transcript.append_commitment(&proof.z_comm);
    let alpha = transcript.challenge();
    let alpha_sq = alpha * alpha;

    // Round 3
    transcript.append_commitment(&proof.t_lo_comm);
    transcript.append_commitment(&proof.t_mid_comm);
    transcript.append_commitment(&proof.t_hi_comm);
    let zeta = transcript.challenge();

    // Round 4
    transcript.append_scalar(&proof.a_eval);
    transcript.append_scalar(&proof.b_eval);
    transcript.append_scalar(&proof.c_eval);
    transcript.append_scalar(&proof.sigma_a_eval);
    transcript.append_scalar(&proof.sigma_b_eval);
    transcript.append_scalar(&proof.z_omega_eval);
    let nu = transcript.challenge();
    let u = transcript.challenge();

    // ── Step 2: Z_H(ζ), L₁(ζ) 계산 ───────────────────
    let zeta_n = {
        let mut z = Fr::ONE;
        for _ in 0..n {
            z = z * zeta;
        }
        z
    };
    let zeta_2n = zeta_n * zeta_n;
    let z_h_zeta = zeta_n - Fr::ONE;

    // L₁(ζ) = (ζⁿ - 1) / (n · (ζ - 1))
    let denom = Fr::from_u64(n as u64) * (zeta - Fr::ONE);
    let l1_zeta = match denom.inv() {
        Some(inv) => z_h_zeta * inv,
        None => return false, // ζ = 1이면 검증 불가 (확률 무시)
    };

    // ── Step 3: Linearization commitment [r]₁ ──────────
    //
    // [r]₁ = ā·[q_L]₁ + b̄·[q_R]₁ + c̄·[q_O]₁ + (ā·b̄)·[q_M]₁ + [q_C]₁
    //      + (α·perm_num + α²·L₁(ζ))·[Z]₁
    //      - α·perm_den_partial·z̄_ω·β·[σ_C]₁
    //      - z_h_ζ·([t_lo]₁ + ζⁿ·[t_mid]₁ + ζ²ⁿ·[t_hi]₁)
    //      - r_constant · G₁  (상수잔여 보정)
    //
    // r_constant = α·z̄_ω·perm_den_partial·(c̄+γ) + α²·L₁(ζ)
    //   prover가 r(ζ)=0 되도록 빼놓은 상수 → verifier도 동일하게 보정

    let perm_num = (proof.a_eval + beta * zeta + gamma)
        * (proof.b_eval + beta * k1 * zeta + gamma)
        * (proof.c_eval + beta * k2 * zeta + gamma);
    let perm_den_partial = (proof.a_eval + beta * proof.sigma_a_eval + gamma)
        * (proof.b_eval + beta * proof.sigma_b_eval + gamma);

    // 상수잔여: prover 쪽과 동일한 값
    let r_constant = alpha * proof.z_omega_eval * perm_den_partial
        * (proof.c_eval + gamma)
        + alpha_sq * l1_zeta;

    let r_comm =
        // Gate 부분: selector commitments의 선형 결합
        vk.q_l_comm.0.scalar_mul(&proof.a_eval.to_repr())
        + vk.q_r_comm.0.scalar_mul(&proof.b_eval.to_repr())
        + vk.q_o_comm.0.scalar_mul(&proof.c_eval.to_repr())
        + vk.q_m_comm.0.scalar_mul(&(proof.a_eval * proof.b_eval).to_repr())
        + vk.q_c_comm.0
        // Permutation 부분
        + proof.z_comm.0.scalar_mul(
            &(alpha * perm_num + alpha_sq * l1_zeta).to_repr(),
        )
        + (-vk.sigma_c_comm.0.scalar_mul(
            &(alpha * perm_den_partial * proof.z_omega_eval * beta).to_repr(),
        ))
        // Quotient 부분
        + (-proof.t_lo_comm.0.scalar_mul(&z_h_zeta.to_repr()))
        + (-proof.t_mid_comm.0.scalar_mul(&(z_h_zeta * zeta_n).to_repr()))
        + (-proof.t_hi_comm.0.scalar_mul(&(z_h_zeta * zeta_2n).to_repr()))
        // 상수잔여 보정: -r_constant · G₁ = commit(constant(-r_constant))
        + (-G1::generator().scalar_mul(&r_constant.to_repr()));

    // ── Step 4: Batched commitment F ───────────────────
    //
    // F = [r]₁ + ν·[a]₁ + ν²·[b]₁ + ν³·[c]₁ + ν⁴·[σ_A]₁ + ν⁵·[σ_B]₁
    //   + u·[Z]₁    ← ζω 개구점의 Z(x) commitment
    //
    // u·[Z]₁ 유래:
    //   W_{ζω}는 Z(x)를 ζω에서 여는 증거.
    //   두 개구점 (ζ, ζω)을 랜덤 u로 결합할 때
    //   Z의 commitment가 u 가중치로 F에 합류.
    let nu2 = nu * nu;
    let nu3 = nu2 * nu;
    let nu4 = nu3 * nu;
    let nu5 = nu4 * nu;

    let f_comm = r_comm
        + proof.a_comm.0.scalar_mul(&nu.to_repr())
        + proof.b_comm.0.scalar_mul(&nu2.to_repr())
        + proof.c_comm.0.scalar_mul(&nu3.to_repr())
        + vk.sigma_a_comm.0.scalar_mul(&nu4.to_repr())
        + vk.sigma_b_comm.0.scalar_mul(&nu5.to_repr())
        + proof.z_comm.0.scalar_mul(&u.to_repr());

    // ── Step 5: Batched evaluation E ───────────────────
    //
    // E = 0 (r(ζ)=0) + ν·ā + ν²·b̄ + ... + ν⁵·σ̄_B + u·z̄_ω
    //
    // u·z̄_ω: W_{ζω}가 Z(ζω) = z̄_ω를 증명하므로 평가값에 포함
    let e_scalar = nu * proof.a_eval
        + nu2 * proof.b_eval
        + nu3 * proof.c_eval
        + nu4 * proof.sigma_a_eval
        + nu5 * proof.sigma_b_eval
        + u * proof.z_omega_eval;

    let e_g1 = G1::generator().scalar_mul(&e_scalar.to_repr());

    // ── Step 6: Pairing Check ──────────────────────────
    //
    // e(W_ζ + u·W_{ζω}, [τ]₂) = e(ζ·W_ζ + u·ζω·W_{ζω} + F - [E]₁, G₂)

    let g2 = srs.g2_powers[0];     // [τ⁰]₂ = G₂
    let tau_g2 = srs.g2_powers[1]; // [τ¹]₂

    // LHS: e(W_ζ + u·W_{ζω}, [τ]₂)
    let lhs_g1 = proof.w_zeta + proof.w_zeta_omega.scalar_mul(&u.to_repr());
    let lhs = pairing(&lhs_g1, &tau_g2);

    // RHS: e(ζ·W_ζ + u·ζ·ω·W_{ζω} + F - [E]₁, G₂)
    let rhs_g1 = proof.w_zeta.scalar_mul(&zeta.to_repr())
        + proof.w_zeta_omega.scalar_mul(&(u * zeta * omega).to_repr())
        + f_comm
        + (-e_g1);
    let rhs = pairing(&rhs_g1, &g2);

    lhs == rhs
}

// ── 테스트 ───────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonk::{PlonkGate, PlonkCircuit, WirePosition, Column};
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    // ── 헬퍼: setup + prove + verify 파이프라인 ────────

    fn setup_prove_verify<C: PlonkCircuit>(circuit: &C, seed: u64) -> (PlonkProof, bool) {
        let mut cs = PlonkConstraintSystem::new();
        circuit.synthesize(&mut cs);
        assert!(cs.is_satisfied(), "circuit must be satisfied");
        assert!(cs.are_copy_constraints_satisfied(), "copy constraints must hold");

        let n = cs.pad_to_power_of_two();
        let domain = Domain::new(n);

        let mut rng = ChaCha20Rng::seed_from_u64(seed);
        let params = plonk_setup(&cs, &domain, &mut rng);

        let proof = prove(&params.srs, &cs, &domain);
        let valid = verify(&params.srs, &params.vk, &proof, &[]);
        (proof, valid)
    }

    // ── 테스트 회로 정의 ───────────────────────────────

    /// a + b = c
    struct AddCircuit { a: u64, b: u64 }
    impl PlonkCircuit for AddCircuit {
        fn synthesize(&self, cs: &mut PlonkConstraintSystem) {
            let a = cs.alloc_variable(Fr::from_u64(self.a));
            let b = cs.alloc_variable(Fr::from_u64(self.b));
            let c = cs.alloc_variable(Fr::from_u64(self.a + self.b));
            cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        }
    }

    /// a * b = c
    struct MulCircuit { a: u64, b: u64 }
    impl PlonkCircuit for MulCircuit {
        fn synthesize(&self, cs: &mut PlonkConstraintSystem) {
            let a = cs.alloc_variable(Fr::from_u64(self.a));
            let b = cs.alloc_variable(Fr::from_u64(self.b));
            let c = cs.alloc_variable(Fr::from_u64(self.a * self.b));
            cs.add_gate(PlonkGate::multiplication_gate(), a, b, c);
        }
    }

    /// x³ + x + 5 = y
    struct CubicCircuit { x: u64 }
    impl PlonkCircuit for CubicCircuit {
        fn synthesize(&self, cs: &mut PlonkConstraintSystem) {
            let x_val = Fr::from_u64(self.x);
            let v1_val = x_val * x_val;
            let v2_val = v1_val * x_val;
            let y_val = v2_val + x_val + Fr::from_u64(5);

            let x = cs.alloc_variable(x_val);
            let v1 = cs.alloc_variable(v1_val);
            let v2 = cs.alloc_variable(v2_val);
            let y = cs.alloc_variable(y_val);

            // Gate 0: x * x = v1
            cs.add_gate(PlonkGate::multiplication_gate(), x, x, v1);
            // Gate 1: v1 * x = v2
            cs.add_gate(PlonkGate::multiplication_gate(), v1, x, v2);
            // Gate 2: v2 + x + 5 = y → q_L·v2 + q_R·x + q_O·y + q_C = 0
            cs.add_gate(
                PlonkGate {
                    q_l: Fr::ONE,
                    q_r: Fr::ONE,
                    q_o: -Fr::ONE,
                    q_m: Fr::ZERO,
                    q_c: Fr::from_u64(5),
                },
                v2, x, y,
            );

            // Copy constraints
            cs.copy_constraint(
                WirePosition { column: Column::A, row: 0 },
                WirePosition { column: Column::B, row: 0 },
            );
            cs.copy_constraint(
                WirePosition { column: Column::B, row: 0 },
                WirePosition { column: Column::B, row: 1 },
            );
            cs.copy_constraint(
                WirePosition { column: Column::B, row: 1 },
                WirePosition { column: Column::B, row: 2 },
            );
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 0 },
                WirePosition { column: Column::A, row: 1 },
            );
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 1 },
                WirePosition { column: Column::A, row: 2 },
            );
        }
    }

    /// Boolean constraint: a·(1-a) = 0
    struct BoolCircuit { val: u64 }
    impl PlonkCircuit for BoolCircuit {
        fn synthesize(&self, cs: &mut PlonkConstraintSystem) {
            let a = cs.alloc_variable(Fr::from_u64(self.val));
            // boolean gate: q_L·a + q_M·a·b = 0, where b=a
            cs.add_gate(PlonkGate::boolean_gate(), a, a, a);
            // b=a enforced by using same variable index
            // No copy constraint needed since same wire index
        }
    }

    /// 8-gate chain: a₀ + a₁ = s₁, s₁ + a₂ = s₂, ..., s₇ * 1 = result
    struct LargerCircuit;
    impl PlonkCircuit for LargerCircuit {
        fn synthesize(&self, cs: &mut PlonkConstraintSystem) {
            // 8개의 값: 1, 2, 3, ..., 8
            let vars: Vec<usize> = (1..=8u64)
                .map(|v| cs.alloc_variable(Fr::from_u64(v)))
                .collect();

            // Gate 0: 1 + 2 = 3
            let sum1 = cs.alloc_variable(Fr::from_u64(3));
            cs.add_gate(PlonkGate::addition_gate(), vars[0], vars[1], sum1);

            // Gate 1: 3 + 3 = 6
            let sum2 = cs.alloc_variable(Fr::from_u64(6));
            cs.add_gate(PlonkGate::addition_gate(), sum1, vars[2], sum2);
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 0 },
                WirePosition { column: Column::A, row: 1 },
            );

            // Gate 2: 6 + 4 = 10
            let sum3 = cs.alloc_variable(Fr::from_u64(10));
            cs.add_gate(PlonkGate::addition_gate(), sum2, vars[3], sum3);
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 1 },
                WirePosition { column: Column::A, row: 2 },
            );

            // Gate 3: 10 + 5 = 15
            let sum4 = cs.alloc_variable(Fr::from_u64(15));
            cs.add_gate(PlonkGate::addition_gate(), sum3, vars[4], sum4);
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 2 },
                WirePosition { column: Column::A, row: 3 },
            );

            // Gate 4: 15 + 6 = 21
            let sum5 = cs.alloc_variable(Fr::from_u64(21));
            cs.add_gate(PlonkGate::addition_gate(), sum4, vars[5], sum5);
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 3 },
                WirePosition { column: Column::A, row: 4 },
            );

            // Gate 5: 21 + 7 = 28
            let sum6 = cs.alloc_variable(Fr::from_u64(28));
            cs.add_gate(PlonkGate::addition_gate(), sum5, vars[6], sum6);
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 4 },
                WirePosition { column: Column::A, row: 5 },
            );

            // Gate 6: 28 + 8 = 36
            let sum7 = cs.alloc_variable(Fr::from_u64(36));
            cs.add_gate(PlonkGate::addition_gate(), sum6, vars[7], sum7);
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 5 },
                WirePosition { column: Column::A, row: 6 },
            );

            // Gate 7: 36 * 1 = 36 (identity check via multiplication)
            let one = cs.alloc_variable(Fr::ONE);
            let result = cs.alloc_variable(Fr::from_u64(36));
            cs.add_gate(PlonkGate::multiplication_gate(), sum7, one, result);
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 6 },
                WirePosition { column: Column::A, row: 7 },
            );
        }
    }

    // ── Transcript 테스트 ──────────────────────────────

    #[test]
    fn transcript_deterministic() {
        // 같은 입력 → 같은 챌린지
        let comm = Commitment(G1::generator());

        let mut t1 = Transcript::new();
        t1.append_commitment(&comm);
        let c1 = t1.challenge();

        let mut t2 = Transcript::new();
        t2.append_commitment(&comm);
        let c2 = t2.challenge();

        assert_eq!(c1, c2);
    }

    #[test]
    fn transcript_different_inputs() {
        // 다른 입력 → 다른 챌린지
        let comm1 = Commitment(G1::generator());
        let comm2 = Commitment(G1::generator() + G1::generator());

        let mut t1 = Transcript::new();
        t1.append_commitment(&comm1);
        let c1 = t1.challenge();

        let mut t2 = Transcript::new();
        t2.append_commitment(&comm2);
        let c2 = t2.challenge();

        assert_ne!(c1, c2);
    }

    // ── E2E Prove/Verify 테스트 ────────────────────────

    #[test]
    fn prove_verify_addition() {
        // a + b = c: 3 + 4 = 7
        let circuit = AddCircuit { a: 3, b: 4 };
        let (_, valid) = setup_prove_verify(&circuit, 42);
        assert!(valid, "addition circuit proof should verify");
    }

    #[test]
    fn prove_verify_multiplication() {
        // a * b = c: 5 * 7 = 35
        let circuit = MulCircuit { a: 5, b: 7 };
        let (_, valid) = setup_prove_verify(&circuit, 100);
        assert!(valid, "multiplication circuit proof should verify");
    }

    #[test]
    fn prove_verify_cubic() {
        // x³ + x + 5 = y, x=3 → y=35
        let circuit = CubicCircuit { x: 3 };
        let (_, valid) = setup_prove_verify(&circuit, 42);
        assert!(valid, "cubic circuit proof should verify");
    }

    #[test]
    fn prove_verify_boolean() {
        // a·(1-a)=0, a=0
        let circuit0 = BoolCircuit { val: 0 };
        let (_, valid0) = setup_prove_verify(&circuit0, 42);
        assert!(valid0, "boolean circuit a=0 should verify");

        // a=1
        let circuit1 = BoolCircuit { val: 1 };
        let (_, valid1) = setup_prove_verify(&circuit1, 42);
        assert!(valid1, "boolean circuit a=1 should verify");
    }

    #[test]
    fn prove_verify_larger_circuit() {
        // 8 gates: 1+2+3+...+8 = 36, then 36*1=36
        let circuit = LargerCircuit;
        let (_, valid) = setup_prove_verify(&circuit, 42);
        assert!(valid, "larger circuit proof should verify");
    }

    // ── Soundness 테스트 ───────────────────────────────

    #[test]
    fn tampered_commitment_fails() {
        let circuit = AddCircuit { a: 3, b: 4 };
        let (mut proof, _) = setup_prove_verify(&circuit, 42);

        // a_comm 변조
        proof.a_comm = Commitment(proof.a_comm.0 + G1::generator());

        // 재검증을 위해 동일한 setup 필요
        let mut cs = PlonkConstraintSystem::new();
        circuit.synthesize(&mut cs);
        let n = cs.pad_to_power_of_two();
        let domain = Domain::new(n);
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let params = plonk_setup(&cs, &domain, &mut rng);

        assert!(!verify(&params.srs, &params.vk, &proof, &[]));
    }

    #[test]
    fn tampered_evaluation_fails() {
        let circuit = AddCircuit { a: 3, b: 4 };
        let (mut proof, _) = setup_prove_verify(&circuit, 42);

        // a_eval 변조
        proof.a_eval = proof.a_eval + Fr::ONE;

        let mut cs = PlonkConstraintSystem::new();
        circuit.synthesize(&mut cs);
        let n = cs.pad_to_power_of_two();
        let domain = Domain::new(n);
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let params = plonk_setup(&cs, &domain, &mut rng);

        assert!(!verify(&params.srs, &params.vk, &proof, &[]));
    }

    #[test]
    fn tampered_opening_fails() {
        let circuit = AddCircuit { a: 3, b: 4 };
        let (mut proof, _) = setup_prove_verify(&circuit, 42);

        // w_zeta 변조
        proof.w_zeta = proof.w_zeta + G1::generator();

        let mut cs = PlonkConstraintSystem::new();
        circuit.synthesize(&mut cs);
        let n = cs.pad_to_power_of_two();
        let domain = Domain::new(n);
        let mut rng = ChaCha20Rng::seed_from_u64(42);
        let params = plonk_setup(&cs, &domain, &mut rng);

        assert!(!verify(&params.srs, &params.vk, &proof, &[]));
    }

    #[test]
    fn cross_circuit_verification_fails() {
        // 회로 A의 증명을 회로 B의 VK로 검증 → 실패
        let circuit_a = AddCircuit { a: 3, b: 4 };
        let circuit_b = MulCircuit { a: 5, b: 7 };

        // Circuit A: setup + prove
        let mut cs_a = PlonkConstraintSystem::new();
        circuit_a.synthesize(&mut cs_a);
        let n_a = cs_a.pad_to_power_of_two();
        let domain_a = Domain::new(n_a);
        let mut rng_a = ChaCha20Rng::seed_from_u64(42);
        let params_a = plonk_setup(&cs_a, &domain_a, &mut rng_a);
        let proof_a = prove(&params_a.srs, &cs_a, &domain_a);

        // Circuit B: setup
        let mut cs_b = PlonkConstraintSystem::new();
        circuit_b.synthesize(&mut cs_b);
        let n_b = cs_b.pad_to_power_of_two();
        let domain_b = Domain::new(n_b);
        let mut rng_b = ChaCha20Rng::seed_from_u64(99);
        let params_b = plonk_setup(&cs_b, &domain_b, &mut rng_b);

        // 회로 A의 증명을 회로 B의 VK로 검증 → 실패해야 함
        assert!(!verify(&params_b.srs, &params_b.vk, &proof_a, &[]));
    }
}
