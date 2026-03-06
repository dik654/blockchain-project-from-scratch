// Step 12: Groth16 — ZK-SNARK 증명 시스템
//
// Groth16이란?
//   Jens Groth (2016)가 제안한 ZK-SNARK 프로토콜
//   - 128바이트 증명: G1 2개 (A, C) + G2 1개 (B)
//   - O(1) 검증: 페어링 3개만으로 검증 완료
//   - Ethereum zk-rollup 검증의 표준
//
// 전체 흐름:
//   1. Trusted Setup: QAP + 랜덤 toxic waste → (ProvingKey, VerifyingKey)
//   2. Prove: ProvingKey + witness → Proof
//   3. Verify: VerifyingKey + public_inputs + Proof → bool
//
// 핵심 아이디어:
//   QAP의 다항식 관계 a(τ)·b(τ) - c(τ) = h(τ)·t(τ)를
//   타원곡선 위에서 pairing으로 검증
//
//   toxic waste τ를 모르는 검증자도
//     e(A, B) = e(α, β) · e(IC_sum, [γ]₂) · e(C, [δ]₂)
//   만으로 증명의 유효성을 확인할 수 있다
//
// 보안 모델:
//   - τ, α, β, γ, δ는 setup 후 반드시 삭제 (toxic waste)
//   - 이 값들을 알면 가짜 증명 생성 가능 → "trusted setup" 필요성
//   - r, s (블라인딩 팩터)가 영지식성(zero-knowledge) 보장
//
// 검증 방정식 유도:
//   A = α + a(τ) + rδ     (in G1)
//   B = β + b(τ) + sδ     (in G2)
//
//   e(A, B) = e(α + a(τ) + rδ,  β + b(τ) + sδ)
//
//   쌍선형성으로 전개:
//     = e(α,β) · e(α,b(τ)) · e(α,sδ)
//       · e(a(τ),β) · e(a(τ),b(τ)) · e(a(τ),sδ)
//       · e(rδ,β) · e(rδ,b(τ)) · e(rδ,sδ)
//
//   QAP 조건 a(τ)b(τ) = c(τ) + h(τ)t(τ) 대입:
//     = e(α,β)
//       · e^(αb(τ) + βa(τ) + c(τ))      ← IC + L 항
//       · e^(h(τ)t(τ))                    ← h 기여분
//       · e^(sα + sa(τ) + rβ + rb(τ) + rsδ) · e^(δ)  ← 블라인딩
//
//   IC (public vars, γ로 나눔) / L (private vars, δ로 나눔) 분리:
//     ∴ e(A,B) = e(α,β) · e(IC_sum, [γ]₂) · e(C, [δ]₂)

use crate::field::{Fr, Fp12};
use crate::curve::{G1, G2, pairing};
use crate::qap::QAP;

use rand::Rng;

// ── 랜덤 Fr 생성 ────────────────────────────────────────

/// 랜덤 Fr 원소 생성
///
/// 4개의 u64 랜덤 → Fr::from_raw로 Montgomery 변환
/// from_raw가 자동으로 mod r 수행
fn random_fr<R: Rng>(rng: &mut R) -> Fr {
    let limbs: [u64; 4] = [
        rng.gen(), rng.gen(), rng.gen(), rng.gen(),
    ];
    Fr::from_raw(limbs)
}

/// 0이 아닌 랜덤 Fr 원소
///
/// toxic waste는 0이면 안 됨 (역원이 필요하므로)
fn random_nonzero_fr<R: Rng>(rng: &mut R) -> Fr {
    loop {
        let f = random_fr(rng);
        if !f.is_zero() { return f; }
    }
}

// ── 자료구조 ────────────────────────────────────────────

/// 증명 키 (Proving Key)
///
/// setup에서 생성되며, 증명자가 보관한다.
/// toxic waste가 커브 포인트로 인코딩되어 있으므로
/// 이 키만으로는 toxic waste를 복원할 수 없다 (ECDLP의 어려움).
pub struct ProvingKey {
    // ── 기본 파라미터 (커브 포인트) ──
    alpha_g1: G1,       // [α]₁
    beta_g1: G1,        // [β]₁  — C 계산 시 B_g1에 필요
    beta_g2: G2,        // [β]₂  — B 계산에 필요
    delta_g1: G1,       // [δ]₁  — 블라인딩에 필요
    delta_g2: G2,       // [δ]₂  — 블라인딩에 필요

    // ── QAP 다항식 평가 (τ에서) ──
    //
    // 각 변수 j에 대해 aⱼ(τ), bⱼ(τ)를 커브 포인트로 인코딩
    a_query: Vec<G1>,       // [aⱼ(τ)]₁ — 모든 변수 j (A 계산용)
    b_g1_query: Vec<G1>,    // [bⱼ(τ)]₁ — 모든 변수 j (C 내 B_g1 계산용)
    b_g2_query: Vec<G2>,    // [bⱼ(τ)]₂ — 모든 변수 j (B 계산용)

    // ── 개인 변수용 키 ──
    //
    // lcⱼ = β·aⱼ(τ) + α·bⱼ(τ) + cⱼ(τ)
    // private 변수: lcⱼ/δ로 나누어 커브 포인트로 인코딩
    l_query: Vec<G1>,       // [(β·aⱼ(τ)+α·bⱼ(τ)+cⱼ(τ))/δ]₁  (private j)

    // ── h(x) 다항식 계수용 키 ──
    //
    // h(x)의 계수 hᵢ를 커브 포인트에 결합하기 위한 키
    h_query: Vec<G1>,       // [τⁱ·t(τ)/δ]₁  for i = 0..m-1

    // ── 메타데이터 ──
    num_instance: usize,
    num_variables: usize,
}

/// 검증 키 (Verifying Key)
///
/// setup에서 생성되며, 검증자가 보관한다.
/// 검증에 필요한 최소한의 정보만 포함:
///   - e(α, β) 사전 계산값
///   - γ, δ의 G2 포인트
///   - IC (public variable commitment)
pub struct VerifyingKey {
    alpha_beta_gt: Fp12,    // e(α, β) — 사전 계산
    gamma_g2: G2,           // [γ]₂
    delta_g2: G2,           // [δ]₂
    // IC: 공개 변수의 commitment
    //   ic[0] = [(β·a₀(τ)+α·b₀(τ)+c₀(τ))/γ]₁  (One 변수)
    //   ic[j] = [(β·aⱼ(τ)+α·bⱼ(τ)+cⱼ(τ))/γ]₁  (Instance 변수)
    ic: Vec<G1>,
}

/// 증명 (Proof)
///
/// Groth16 증명은 3개의 커브 포인트:
///   A ∈ G1, B ∈ G2, C ∈ G1
///
/// BN254에서 G1 점 = 2×32 = 64바이트, G2 점 = 2×64 = 128바이트
/// 총 증명 크기 = 64 + 128 + 64 = 256바이트
pub struct Proof {
    pub a: G1,     // A ∈ G1
    pub b: G2,     // B ∈ G2
    pub c: G1,     // C ∈ G1
}

// ── Trusted Setup ───────────────────────────────────────

/// Trusted Setup — QAP를 커브 포인트로 인코딩
///
/// toxic waste (τ, α, β, γ, δ)를 생성하고,
/// QAP 다항식을 τ에서 평가하여 커브 포인트로 변환한다.
///
/// ⚠️ toxic waste는 이 함수 종료 시 Rust의 소유권 시스템에 의해
///    스택에서 소멸된다. 실제 프로덕션에서는 MPC 기반 세레모니를 사용하여
///    어떤 단일 참여자도 전체 toxic waste를 알 수 없도록 한다.
///
/// 변수 인덱싱:
///   j=0: One (상수 1)
///   j=1..num_instance: Instance (공개 변수) → IC에 포함
///   j=(num_instance+1)..n-1: Witness (비공개 변수) → L에 포함
pub fn setup<R: Rng>(qap: &QAP, rng: &mut R) -> (ProvingKey, VerifyingKey) {
    let n = qap.num_variables;
    let m = qap.domain.len(); // 제약 수

    // ── 1. Toxic waste 생성 ──
    //
    // 5개의 랜덤 스칼라 (0이 아닌 Fr 원소)
    // 이 값들을 아는 자는 가짜 증명을 만들 수 있으므로
    // setup 후 반드시 삭제해야 한다
    let tau = random_nonzero_fr(rng);     // 비밀 평가점
    let alpha = random_nonzero_fr(rng);   // 지식 계수
    let beta = random_nonzero_fr(rng);    // 교차항 계수
    let gamma = random_nonzero_fr(rng);   // public 구분자
    let delta = random_nonzero_fr(rng);   // private 구분자

    let gamma_inv = gamma.inv().unwrap();
    let delta_inv = delta.inv().unwrap();

    let g1 = G1::generator();
    let g2 = G2::generator();

    // ── 2. 기본 커브 포인트 ──
    let alpha_g1 = g1.scalar_mul(&alpha.to_repr());
    let beta_g1 = g1.scalar_mul(&beta.to_repr());
    let beta_g2 = g2.scalar_mul(&beta.to_repr());
    let delta_g1 = g1.scalar_mul(&delta.to_repr());
    let delta_g2 = g2.scalar_mul(&delta.to_repr());
    let gamma_g2 = g2.scalar_mul(&gamma.to_repr());

    // ── 3. QAP 다항식을 τ에서 평가 ──
    //
    // 각 변수 j에 대해: aⱼ(τ), bⱼ(τ), cⱼ(τ) ∈ Fr
    let mut a_at_tau = Vec::with_capacity(n);
    let mut b_at_tau = Vec::with_capacity(n);
    let mut c_at_tau = Vec::with_capacity(n);

    for j in 0..n {
        a_at_tau.push(qap.a_polys[j].eval(tau));
        b_at_tau.push(qap.b_polys[j].eval(tau));
        c_at_tau.push(qap.c_polys[j].eval(tau));
    }

    // ── 4. Query 벡터 생성 ──
    //
    // a_query[j] = [aⱼ(τ)]₁: A 증명 원소 계산에 사용
    // b_g1_query[j] = [bⱼ(τ)]₁: C 계산 시 B_g1에 사용
    // b_g2_query[j] = [bⱼ(τ)]₂: B 증명 원소 계산에 사용
    let a_query: Vec<G1> = a_at_tau.iter()
        .map(|&a| g1.scalar_mul(&a.to_repr()))
        .collect();
    let b_g1_query: Vec<G1> = b_at_tau.iter()
        .map(|&b| g1.scalar_mul(&b.to_repr()))
        .collect();
    let b_g2_query: Vec<G2> = b_at_tau.iter()
        .map(|&b| g2.scalar_mul(&b.to_repr()))
        .collect();

    // ── 5. IC (공개 변수) vs L (비공개 변수) 분리 ──
    //
    // lcⱼ = β·aⱼ(τ) + α·bⱼ(τ) + cⱼ(τ)
    //
    // 공개 변수 (j = 0..=num_instance):
    //   ic[j] = [lcⱼ / γ]₁  → 검증 방정식에서 e(IC_sum, [γ]₂)로 γ 소거
    //
    // 비공개 변수 (j = num_instance+1..n-1):
    //   l_query[j'] = [lcⱼ / δ]₁  → 검증 방정식에서 e(C, [δ]₂)로 δ 소거
    let num_public = qap.num_instance + 1; // One + Instance 변수

    let mut ic = Vec::with_capacity(num_public);
    for j in 0..num_public {
        let lc = beta * a_at_tau[j] + alpha * b_at_tau[j] + c_at_tau[j];
        let val = lc * gamma_inv;
        ic.push(g1.scalar_mul(&val.to_repr()));
    }

    let num_private = n - num_public;
    let mut l_query = Vec::with_capacity(num_private);
    for j in num_public..n {
        let lc = beta * a_at_tau[j] + alpha * b_at_tau[j] + c_at_tau[j];
        let val = lc * delta_inv;
        l_query.push(g1.scalar_mul(&val.to_repr()));
    }

    // ── 6. h_query 생성 ──
    //
    // h(x) = Σᵢ hᵢ · xⁱ (degree ≤ m-2)
    // h_query[i] = [τⁱ · t(τ) / δ]₁
    //
    // 검증 방정식에서:
    //   Σ hᵢ · h_query[i] = [h(τ)·t(τ)/δ]₁
    //   e([h(τ)·t(τ)/δ]₁, [δ]₂) = e(G1, G2)^(h(τ)·t(τ))
    let t_at_tau = qap.t.eval(tau);
    let t_delta_inv = t_at_tau * delta_inv;

    let h_len = m.saturating_sub(1); // max(0, m-1)
    let mut h_query = Vec::with_capacity(h_len);
    let mut tau_power = Fr::ONE; // τ⁰ = 1
    for _i in 0..h_len {
        let val = tau_power * t_delta_inv;
        h_query.push(g1.scalar_mul(&val.to_repr()));
        tau_power = tau_power * tau;
    }

    // ── 7. 검증키에 e(α, β) 사전 계산 ──
    let alpha_beta_gt = pairing(&alpha_g1, &beta_g2);

    let pk = ProvingKey {
        alpha_g1, beta_g1, beta_g2, delta_g1, delta_g2,
        a_query, b_g1_query, b_g2_query,
        l_query, h_query,
        num_instance: qap.num_instance,
        num_variables: n,
    };

    let vk = VerifyingKey {
        alpha_beta_gt,
        gamma_g2,
        delta_g2,
        ic,
    };

    (pk, vk)
}

// ── Prove ───────────────────────────────────────────────

/// 증명 생성
///
/// witness: 전체 변수 벡터 [1, instance..., witness...]
///   cs.values를 그대로 전달하면 된다
///
/// 흐름:
///   1. h(x) = (a(x)·b(x) - c(x)) / t(x) 계산
///      → QAP 불만족이면 None 반환
///   2. 블라인딩 팩터 r, s 랜덤 생성
///   3. A = [α]₁ + Σ wⱼ·[aⱼ(τ)]₁ + r·[δ]₁
///   4. B = [β]₂ + Σ wⱼ·[bⱼ(τ)]₂ + s·[δ]₂
///   5. C = Σ_{private j} wⱼ·[lⱼ]₁ + Σ hᵢ·[h_query_i]₁
///          + s·A + r·B' - r·s·[δ]₁
///
/// 블라인딩 (r, s)의 역할:
///   A, B, C에 랜덤 δ항을 추가하여
///   검증 방정식은 유지하면서 witness 정보를 숨긴다
///   → 영지식성(zero-knowledge) 보장
pub fn prove<R: Rng>(
    pk: &ProvingKey,
    qap: &QAP,
    witness: &[Fr],
    rng: &mut R,
) -> Option<Proof> {
    assert_eq!(witness.len(), pk.num_variables);

    // ── 1. h(x) 계산 ──
    // QAP 불만족이면 h가 다항식이 되지 않아 None 반환
    let h = qap.compute_h(witness)?;

    // ── 2. 블라인딩 팩터 ──
    let r = random_fr(rng);
    let s = random_fr(rng);

    // ── 3. A ∈ G1 ──
    //
    // A = [α]₁ + Σⱼ wⱼ·[aⱼ(τ)]₁ + r·[δ]₁
    //
    // witness 값이 0인 변수는 기여하지 않으므로 건너뛴다
    let mut proof_a = pk.alpha_g1;
    for j in 0..pk.num_variables {
        if !witness[j].is_zero() {
            proof_a = proof_a + pk.a_query[j].scalar_mul(&witness[j].to_repr());
        }
    }
    proof_a = proof_a + pk.delta_g1.scalar_mul(&r.to_repr());

    // ── 4. B ∈ G2 ──
    //
    // B = [β]₂ + Σⱼ wⱼ·[bⱼ(τ)]₂ + s·[δ]₂
    let mut proof_b = pk.beta_g2;
    for j in 0..pk.num_variables {
        if !witness[j].is_zero() {
            proof_b = proof_b + pk.b_g2_query[j].scalar_mul(&witness[j].to_repr());
        }
    }
    proof_b = proof_b + pk.delta_g2.scalar_mul(&s.to_repr());

    // ── 5. B' ∈ G1 (C 계산용) ──
    //
    // B를 G1에서도 계산 — C = ... + r·B' 에 필요
    let mut b_g1 = pk.beta_g1;
    for j in 0..pk.num_variables {
        if !witness[j].is_zero() {
            b_g1 = b_g1 + pk.b_g1_query[j].scalar_mul(&witness[j].to_repr());
        }
    }
    b_g1 = b_g1 + pk.delta_g1.scalar_mul(&s.to_repr());

    // ── 6. C ∈ G1 ──
    //
    // C = Σ_{private j} wⱼ · l_query[j']
    //   + Σᵢ hᵢ · h_query[i]
    //   + s·A + r·B' - r·s·[δ]₁
    //
    // 각 항의 의미:
    //   private 기여: 비공개 변수의 (β·aⱼ(τ)+α·bⱼ(τ)+cⱼ(τ))/δ
    //   h 기여: h(τ)·t(τ)/δ — QAP 만족의 증거
    //   블라인딩: s·A + r·B' - r·s·[δ]₁ — 영지식성 보장
    let num_public = pk.num_instance + 1;
    let mut proof_c = G1::identity();

    // 비공개 변수 기여분
    for (idx, j) in (num_public..pk.num_variables).enumerate() {
        if !witness[j].is_zero() {
            proof_c = proof_c + pk.l_query[idx].scalar_mul(&witness[j].to_repr());
        }
    }

    // h(x) 기여분
    for (i, &h_coeff) in h.coeffs.iter().enumerate() {
        if !h_coeff.is_zero() && i < pk.h_query.len() {
            proof_c = proof_c + pk.h_query[i].scalar_mul(&h_coeff.to_repr());
        }
    }

    // 블라인딩: s·A + r·B' - r·s·[δ]₁
    proof_c = proof_c + proof_a.scalar_mul(&s.to_repr());
    proof_c = proof_c + b_g1.scalar_mul(&r.to_repr());
    let rs = r * s;
    proof_c = proof_c + (-pk.delta_g1.scalar_mul(&rs.to_repr()));

    Some(Proof {
        a: proof_a,
        b: proof_b,
        c: proof_c,
    })
}

// ── Verify ──────────────────────────────────────────────

/// 증명 검증
///
/// 검증 방정식:
///   e(A, B) = e(α, β) · e(IC_sum, [γ]₂) · e(C, [δ]₂)
///
/// IC_sum 계산:
///   IC_sum = ic[0] + Σⱼ public_inputs[j] · ic[j+1]
///
/// 왜 3개의 pairing으로 충분한가?
///   - e(α, β): 증명 구조의 정당성 (α, β가 올바르게 사용됨)
///   - e(IC_sum, [γ]₂): 공개 입력이 올바르게 포함됨
///   - e(C, [δ]₂): 비공개 변수 + h(τ)t(τ) + 블라인딩이 일관됨
///
/// public_inputs: Instance 변수값만 (One 제외)
///   cs.values[1..=cs.num_instance]를 전달
pub fn verify(vk: &VerifyingKey, public_inputs: &[Fr], proof: &Proof) -> bool {
    assert_eq!(public_inputs.len() + 1, vk.ic.len());

    // ── 1. IC_sum 계산 ──
    //
    // IC_sum = ic[0] + Σⱼ public_inputs[j] · ic[j+1]
    //
    // ic[0]은 One 변수(항상 1)에 대응하므로 그대로 더하고,
    // 나머지는 실제 공개 입력값으로 스칼라 곱한다
    let mut ic_sum = vk.ic[0];
    for (j, &input) in public_inputs.iter().enumerate() {
        if !input.is_zero() {
            ic_sum = ic_sum + vk.ic[j + 1].scalar_mul(&input.to_repr());
        }
    }

    // ── 2. 검증 방정식 확인 ──
    //
    // LHS: e(A, B)
    // RHS: e(α,β) · e(IC_sum, [γ]₂) · e(C, [δ]₂)
    let lhs = pairing(&proof.a, &proof.b);
    let rhs = vk.alpha_beta_gt
        * pairing(&ic_sum, &vk.gamma_g2)
        * pairing(&proof.c, &vk.delta_g2);

    lhs == rhs
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1cs::{ConstraintSystem, LinearCombination, Variable, Circuit};
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    // ── 테스트 회로 정의 ─────────────────────────────────

    /// f(x) = x³ + x + 5 = y
    ///
    /// R1CS (3 제약):
    ///   제약 1: x · x = t1
    ///   제약 2: t1 · x = t2
    ///   제약 3: (t2 + x + 5) · 1 = y
    ///
    /// 변수: One, y(instance), x(witness), t1(witness), t2(witness)
    struct CubicCircuit {
        x: Fr,
    }

    impl Circuit for CubicCircuit {
        fn synthesize(&self, cs: &mut ConstraintSystem) {
            let x_val = self.x;
            let t1_val = x_val * x_val;
            let t2_val = t1_val * x_val;
            let y_val = t2_val + x_val + Fr::from_u64(5);

            let x = cs.alloc_witness(x_val);
            let y = cs.alloc_instance(y_val);
            let t1 = cs.alloc_witness(t1_val);
            let t2 = cs.alloc_witness(t2_val);

            // x · x = t1
            cs.enforce(
                LinearCombination::from(x),
                LinearCombination::from(x),
                LinearCombination::from(t1),
            );
            // t1 · x = t2
            cs.enforce(
                LinearCombination::from(t1),
                LinearCombination::from(x),
                LinearCombination::from(t2),
            );
            // (t2 + x + 5) · 1 = y
            cs.enforce(
                LinearCombination::from(t2)
                    .add(Fr::ONE, x)
                    .add(Fr::from_u64(5), Variable::One),
                LinearCombination::from(Variable::One),
                LinearCombination::from(y),
            );
        }
    }

    /// 헬퍼: 회로 → QAP + witness 추출
    fn setup_circuit(circuit: &impl Circuit) -> (QAP, Vec<Fr>) {
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);
        assert!(cs.is_satisfied());
        let witness = cs.values.clone();
        let qap = QAP::from_r1cs(&cs);
        (qap, witness)
    }

    /// 헬퍼: 공개 입력 추출 (One 제외)
    fn public_inputs(cs: &ConstraintSystem) -> Vec<Fr> {
        cs.values[1..=cs.num_instance].to_vec()
    }

    // ── 기본 동작 테스트 ─────────────────────────────────

    #[test]
    fn groth16_cubic_valid() {
        // x³ + x + 5 = y, x=3 → y=35
        let circuit = CubicCircuit { x: Fr::from_u64(3) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);
        let pub_inputs = public_inputs(&cs);

        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();
        assert!(verify(&vk, &pub_inputs, &proof));
    }

    #[test]
    fn groth16_cubic_different_input() {
        // x=5 → y=5³+5+5 = 135
        let circuit = CubicCircuit { x: Fr::from_u64(5) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);
        let pub_inputs = public_inputs(&cs);

        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(100);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();
        assert!(verify(&vk, &pub_inputs, &proof));
    }

    // ── 잘못된 입력 테스트 ───────────────────────────────

    #[test]
    fn groth16_wrong_public_input() {
        // 올바른 witness로 증명, 하지만 검증 시 틀린 공개 입력 사용
        let circuit = CubicCircuit { x: Fr::from_u64(3) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();

        // 틀린 공개 입력: y=999 (실제는 35)
        let wrong_inputs = vec![Fr::from_u64(999)];
        assert!(!verify(&vk, &wrong_inputs, &proof));
    }

    #[test]
    fn groth16_wrong_witness() {
        // 잘못된 witness → QAP 불만족 → prove 실패
        let mut cs = ConstraintSystem::new();
        let x_val = Fr::from_u64(3);
        let t1_val = x_val * x_val;
        let t2_val = t1_val * x_val;

        let x = cs.alloc_witness(x_val);
        let _y = cs.alloc_instance(Fr::from_u64(999)); // 틀린 출력
        let t1 = cs.alloc_witness(t1_val);
        let t2 = cs.alloc_witness(t2_val);

        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(x),
            LinearCombination::from(t1),
        );
        cs.enforce(
            LinearCombination::from(t1),
            LinearCombination::from(x),
            LinearCombination::from(t2),
        );
        cs.enforce(
            LinearCombination::from(t2)
                .add(Fr::ONE, x)
                .add(Fr::from_u64(5), Variable::One),
            LinearCombination::from(Variable::One),
            LinearCombination::from(Variable::Instance(0)),
        );

        assert!(!cs.is_satisfied()); // R1CS 불만족

        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let (pk, _vk) = setup(&qap, &mut rng);
        // 잘못된 witness → h(x)가 다항식이 아님 → None
        assert!(prove(&pk, &qap, &cs.values, &mut rng).is_none());
    }

    // ── 변조 감지 테스트 ─────────────────────────────────

    #[test]
    fn groth16_tampered_proof_a() {
        let circuit = CubicCircuit { x: Fr::from_u64(3) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);
        let pub_inputs = public_inputs(&cs);

        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();

        // A를 변조
        let tampered = Proof {
            a: proof.a + G1::generator(),
            b: proof.b,
            c: proof.c,
        };
        assert!(!verify(&vk, &pub_inputs, &tampered));
    }

    #[test]
    fn groth16_tampered_proof_b() {
        let circuit = CubicCircuit { x: Fr::from_u64(3) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);
        let pub_inputs = public_inputs(&cs);

        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();

        // B를 변조
        let tampered = Proof {
            a: proof.a,
            b: proof.b + G2::generator(),
            c: proof.c,
        };
        assert!(!verify(&vk, &pub_inputs, &tampered));
    }

    #[test]
    fn groth16_tampered_proof_c() {
        let circuit = CubicCircuit { x: Fr::from_u64(3) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);
        let pub_inputs = public_inputs(&cs);

        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(42);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();

        // C를 변조
        let tampered = Proof {
            a: proof.a,
            b: proof.b,
            c: proof.c + G1::generator(),
        };
        assert!(!verify(&vk, &pub_inputs, &tampered));
    }

    // ── 다양한 회로 테스트 ───────────────────────────────

    #[test]
    fn groth16_multiply_circuit() {
        // x · y = z (1 제약, m=1)
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_witness(Fr::from_u64(4));
        let z = cs.alloc_instance(Fr::from_u64(12));

        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(y),
            LinearCombination::from(z),
        );

        assert!(cs.is_satisfied());
        let pub_inputs = public_inputs(&cs);
        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(77);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();
        assert!(verify(&vk, &pub_inputs, &proof));
    }

    #[test]
    fn groth16_pythagorean() {
        // x² + y² = z² (3 제약)
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_witness(Fr::from_u64(4));
        let z = cs.alloc_instance(Fr::from_u64(5));
        let x_sq = cs.alloc_witness(Fr::from_u64(9));
        let y_sq = cs.alloc_witness(Fr::from_u64(16));

        // x · x = x_sq
        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(x),
            LinearCombination::from(x_sq),
        );
        // y · y = y_sq
        cs.enforce(
            LinearCombination::from(y),
            LinearCombination::from(y),
            LinearCombination::from(y_sq),
        );
        // z · z = x_sq + y_sq
        cs.enforce(
            LinearCombination::from(z),
            LinearCombination::from(z),
            LinearCombination::from(x_sq).add(Fr::ONE, y_sq),
        );

        assert!(cs.is_satisfied());
        let pub_inputs = public_inputs(&cs);
        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(88);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();
        assert!(verify(&vk, &pub_inputs, &proof));
    }

    #[test]
    fn groth16_conditional() {
        // if b then x else y (3 제약)
        let mut cs = ConstraintSystem::new();
        let b = cs.alloc_witness(Fr::ONE);          // b = 1
        let x = cs.alloc_witness(Fr::from_u64(42));  // x = 42
        let y = cs.alloc_witness(Fr::from_u64(99));  // y = 99
        let t_val = Fr::ONE * (Fr::from_u64(42) - Fr::from_u64(99)); // b*(x-y)
        let t = cs.alloc_witness(t_val);
        let result_val = Fr::from_u64(99) + t_val;   // y + t = 42
        let result = cs.alloc_instance(result_val);

        // b · (1-b) = 0  (부울 제약)
        cs.enforce(
            LinearCombination::from(b),
            LinearCombination::from(Variable::One).add(-Fr::ONE, b),
            LinearCombination::zero(),
        );
        // b · (x-y) = t
        cs.enforce(
            LinearCombination::from(b),
            LinearCombination::from(x).add(-Fr::ONE, y),
            LinearCombination::from(t),
        );
        // (y+t) · 1 = result
        cs.enforce(
            LinearCombination::from(y).add(Fr::ONE, t),
            LinearCombination::from(Variable::One),
            LinearCombination::from(result),
        );

        assert!(cs.is_satisfied());
        let pub_inputs = public_inputs(&cs);
        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(55);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();
        assert!(verify(&vk, &pub_inputs, &proof));
    }

    // ── 영지식성 테스트 ──────────────────────────────────

    #[test]
    fn groth16_proof_independence() {
        // 같은 회로, 같은 witness, 다른 rng → 다른 증명
        // (블라인딩 팩터 r, s가 다르므로)
        let circuit = CubicCircuit { x: Fr::from_u64(3) };
        let (qap, witness) = setup_circuit(&circuit);

        let mut rng = ChaCha20Rng::seed_from_u64(1);

        // 같은 setup 키 사용
        let (pk, vk) = setup(&qap, &mut rng);

        // 서로 다른 rng로 증명 생성
        let mut rng_prove1 = ChaCha20Rng::seed_from_u64(100);
        let mut rng_prove2 = ChaCha20Rng::seed_from_u64(200);

        let proof1 = prove(&pk, &qap, &witness, &mut rng_prove1).unwrap();
        let proof2 = prove(&pk, &qap, &witness, &mut rng_prove2).unwrap();

        // 두 증명 모두 유효
        let pub_inputs: Vec<Fr> = witness[1..=qap.num_instance].to_vec();
        assert!(verify(&vk, &pub_inputs, &proof1));
        assert!(verify(&vk, &pub_inputs, &proof2));

        // 하지만 증명값은 다름 (영지식성)
        assert_ne!(proof1.a, proof2.a);
    }

    // ── Edge case 테스트 ─────────────────────────────────

    #[test]
    fn groth16_zero_witness_values() {
        // x · y = z, x=0, y=5, z=0
        // witness에 0인 값이 포함된 경우
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::ZERO);
        let y = cs.alloc_witness(Fr::from_u64(5));
        let z = cs.alloc_instance(Fr::ZERO);

        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(y),
            LinearCombination::from(z),
        );

        assert!(cs.is_satisfied());
        let pub_inputs = public_inputs(&cs);
        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(33);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();
        assert!(verify(&vk, &pub_inputs, &proof));
    }

    #[test]
    fn groth16_empty_circuit() {
        // 제약 0개 (m=0) — edge case
        // QAP 도메인이 비어있고, t(x) = 1, h(x) = 0
        let cs = ConstraintSystem::new();
        let pub_inputs: Vec<Fr> = vec![];

        let qap = QAP::from_r1cs(&cs);
        let mut rng = ChaCha20Rng::seed_from_u64(11);

        let (pk, vk) = setup(&qap, &mut rng);
        let proof = prove(&pk, &qap, &cs.values, &mut rng).unwrap();
        assert!(verify(&vk, &pub_inputs, &proof));
    }
}
