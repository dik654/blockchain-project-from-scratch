// Step 6: Optimal Ate Pairing — e: G1 × G2 → GT ⊂ Fp12*
//
// 페어링이란?
//   두 타원곡선 군(G1, G2)의 점을 받아 유한체(GT = Fp12*)의 원소를 출력하는 쌍선형 사상
//   e(aP, bQ) = e(P, Q)^(ab) — 이 성질이 ZK 증명 검증의 핵심
//
// BN254 Optimal Ate Pairing:
//   1. Miller loop: |6u+2| 파라미터의 NAF 표현으로 line function을 반복 평가
//   2. Final exponentiation: f^((p^12-1)/r)
//
// BN254 파라미터: u = 0x44E992B44A6909F1

use crate::field::{Fp, Fp2, Fp6, Fp12};
use crate::curve::{G1Affine, G2Affine, G1, G2};

// |6u+2| NAF (LSB first, 65 entries) — go-ethereum 참조
const ATE_NAF: [i8; 65] = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0,
    0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 1,
    1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1,
    1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, 1, 1,
];

/// Fp를 Fp2에 embed
fn embed(x: Fp) -> Fp2 { Fp2::new(x, Fp::ZERO) }

/// Fp2 실수 상수
fn fp2c(n: u64) -> Fp2 { Fp2::new(Fp::from_u64(n), Fp::ZERO) }

// ─── Line function ──────────────────────────────────────
//
// D-type twist: ψ(X',Y') = (X'·v, Y'·w³)  maps E'(Fp2) → E(Fp12)
// ψ⁻¹(P) = (xP/v, yP/w³)  maps E(Fp) → E'(Fp12)
//
// l_{T}(ψ⁻¹(P)) = yP/w³ - yT - λ(xP/v - xT)
//
// ×w³ 해서 분모 제거 (final exp에서 소거):
//   w³·l = yP + (-λ·xP)·w + (λ·xT - yT)·w³
//
// w = w, w³ = w·v (since w² = v)이므로:
//   c0 = Fp6(embed(yP), 0, 0)
//   c1 = Fp6(-λ·embed(xP), λ·xT - yT, 0)

/// line function result as Fp12
fn line_eval(lambda: Fp2, xt: Fp2, yt: Fp2, p: &G1Affine) -> Fp12 {
    Fp12::new(
        Fp6::new(embed(p.y), Fp2::ZERO, Fp2::ZERO),
        Fp6::new(-(lambda * embed(p.x)), lambda * xt - yt, Fp2::ZERO),
    )
}

/// 접선 (doubling step): T에서의 접선, P에서 평가
fn line_double(t: &G2Affine, p: &G1Affine) -> (G2Affine, Fp12) {
    let lambda = (fp2c(3) * t.x.square()) * (fp2c(2) * t.y).inv().unwrap();
    let x2t = lambda.square() - fp2c(2) * t.x;
    let y2t = lambda * (t.x - x2t) - t.y;
    (G2Affine::new(x2t, y2t), line_eval(lambda, t.x, t.y, p))
}

/// 할선 (addition step): T, Q를 지나는 직선, P에서 평가
fn line_add(t: &G2Affine, q: &G2Affine, p: &G1Affine) -> (G2Affine, Fp12) {
    let lambda = (q.y - t.y) * (q.x - t.x).inv().unwrap();
    let xr = lambda.square() - t.x - q.x;
    let yr = lambda * (t.x - xr) - t.y;
    (G2Affine::new(xr, yr), line_eval(lambda, t.x, t.y, p))
}

// ─── Frobenius on G2 ────────────────────────────────────
// π(x,y)  = (conj(x)·γ₁₁, conj(y)·γ₂₁)
// π²(x,y) = (x·γ₁₂, -y)   (γ₂₂ = -1)

fn frobenius_g2(q: &G2Affine) -> G2Affine {
    // γ₁₁ = ξ^((p-1)/3)
    let g11 = Fp2::new(
        Fp::from_raw([0x99e39557176f553d, 0xb78cc310c2c3330c,
                       0x4c0bec3cf559b143, 0x2fb347984f7911f7]),
        Fp::from_raw([0x1665d51c640fcba2, 0x32ae2a1d0b7c9dce,
                       0x4ba4cc8bd75a0794, 0x16c9e55061ebae20]),
    );
    // γ₂₁ = ξ^((p-1)/2)
    let g21 = Fp2::new(
        Fp::from_raw([0xdc54014671a0135a, 0xdbaae0eda9c95998,
                       0xdc5ec698b6e2f9b9, 0x063cf305489af5dc]),
        Fp::from_raw([0x82d37f632623b0e3, 0x21807dc98fa25bd2,
                       0x0704b5a7ec796f2b, 0x07c03cbcac41049a]),
    );
    G2Affine::new(q.x.conjugate() * g11, q.y.conjugate() * g21)
}

fn frobenius_g2_sq(q: &G2Affine) -> G2Affine {
    // γ₁₂ = ξ^((p²-1)/3) — real (c1=0)
    let g12 = Fp2::new(
        Fp::from_raw([0xe4bd44e5607cfd48, 0xc28f069fbb966e3d,
                       0x5e6dd9e7e0acccb0, 0x30644e72e131a029]),
        Fp::ZERO,
    );
    // γ₂₂ = ξ^((p²-1)/2) = -1
    // π²(x,y) = (x·γ₁₂, -y)
    G2Affine::new(q.x * g12, -q.y)
}

// ─── Miller loop ────────────────────────────────────────

fn miller_loop(p: &G1Affine, q: &G2Affine) -> Fp12 {
    if p.infinity || q.infinity { return Fp12::ONE; }

    let mut f = Fp12::ONE;
    let mut t = *q;
    let neg_q = G2Affine::new(q.x, -q.y);

    // NAF is LSB first; iterate from MSB (index 64) to LSB (index 0)
    // MSB (index 64 = 1) initializes T = Q (already done)
    for i in (0..64).rev() {
        let (new_t, line) = line_double(&t, p);
        t = new_t;
        f = f.square() * line;

        match ATE_NAF[i] {
            1 => {
                let (new_t, line) = line_add(&t, q, p);
                t = new_t;
                f = f * line;
            }
            -1 => {
                let (new_t, line) = line_add(&t, &neg_q, p);
                t = new_t;
                f = f * line;
            }
            _ => {}
        }
    }

    // BN 보정항: Q1 = π(Q), Q2 = -π²(Q)
    let q1 = frobenius_g2(q);
    let q2_neg = {
        let q2 = frobenius_g2_sq(q);
        G2Affine::new(q2.x, -q2.y)  // -(x·γ, -y) = (x·γ, y)
    };

    let (new_t, line) = line_add(&t, &q1, p);
    t = new_t;
    f = f * line;

    let (_new_t, line) = line_add(&t, &q2_neg, p);
    f = f * line;

    f
}

// ─── Frobenius maps on Fp12 ─────────────────────────────

/// Fp6 Frobenius²: a^(p²)
fn fp6_frob2(a: &Fp6) -> Fp6 {
    // x^(p²) = x for x∈Fp2, but v^(p²) 보정 필요
    let gv1 = Fp2::new(
        Fp::from_raw([0xe4bd44e5607cfd48, 0xc28f069fbb966e3d,
                       0x5e6dd9e7e0acccb0, 0x30644e72e131a029]),
        Fp::ZERO,
    );
    let gv2 = Fp2::new(
        Fp::from_raw([0x5763473177fffffe, 0xd4f263f1acdb5c4f,
                       0x59e26bcea0d48bac, 0x0000000000000000]),
        Fp::ZERO,
    );
    Fp6::new(a.c0, a.c1 * gv1, a.c2 * gv2)
}

/// Fp12 Frobenius²: f^(p²)
fn fp12_frob2(f: &Fp12) -> Fp12 {
    let c0 = fp6_frob2(&f.c0);
    let c1 = fp6_frob2(&f.c1);
    // w^(p²) = w · ξ^((p²-1)/6)
    let gw = Fp2::new(
        Fp::from_raw([0xe4bd44e5607cfd49, 0xc28f069fbb966e3d,
                       0x5e6dd9e7e0acccb0, 0x30644e72e131a029]),
        Fp::ZERO,
    );
    Fp12::new(c0, Fp12::new(Fp6::ZERO, Fp6::new(c1.c0 * gw, c1.c1 * gw, c1.c2 * gw)).c1)
}

// ─── Final exponentiation ───────────────────────────────
//
// f^((p^12-1)/r) = f^((p^6-1)(p^2+1)(p^4-p^2+1)/r)
//
// Easy part 1: f^(p^6-1) = conj(f) · f⁻¹
// Easy part 2: result^(p^2+1) = frob²(result) · result
// Hard part:   result^((p^4-p^2+1)/r) — precomputed exponent

fn final_exponentiation(f: Fp12) -> Fp12 {
    // Easy part 1: f^(p^6-1)
    let f_inv = f.inv().unwrap();
    let r1 = f.conjugate() * f_inv;

    // Easy part 2: r1^(p^2+1)
    let r2 = fp12_frob2(&r1) * r1;

    // Hard part: r2^((p^4-p^2+1)/r)
    // 761-bit exponent, precomputed
    let hard_exp: [u64; 12] = [
        0xe81bb482ccdf42b1, 0x5abf5cc4f49c36d4,
        0xf1154e7e1da014fd, 0xdcc7b44c87cdbacf,
        0xaaa441e3954bcf8a, 0x6b887d56d5095f23,
        0x79581e16f3fd90c6, 0x3b1b1355d189227d,
        0x4e529a5861876f6b, 0x6c0eb522d5b12278,
        0x331ec15183177faf, 0x01baaa710b0759ad,
    ];
    r2.pow(&hard_exp)
}

/// 페어링 함수: e(P, Q) → GT ⊂ Fp12*
pub fn pairing(p: &G1, q: &G2) -> Fp12 {
    let p_aff = p.to_affine();
    let q_aff = q.to_affine();
    if p_aff.infinity || q_aff.infinity { return Fp12::ONE; }
    let f = miller_loop(&p_aff, &q_aff);
    final_exponentiation(f)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pairing_of_identity_is_one() {
        assert_eq!(pairing(&G1::identity(), &G2::generator()), Fp12::ONE);
    }

    #[test]
    fn pairing_identity_g2() {
        assert_eq!(pairing(&G1::generator(), &G2::identity()), Fp12::ONE);
    }

    #[test]
    fn pairing_non_degenerate() {
        let e = pairing(&G1::generator(), &G2::generator());
        assert_ne!(e, Fp12::ONE);
        assert_ne!(e, Fp12::ZERO);
    }

    #[test]
    fn pairing_bilinearity_lhs() {
        // e(aP, Q) = e(P, Q)^a
        let p = G1::generator();
        let q = G2::generator();
        let lhs = pairing(&p.scalar_mul(&[7, 0, 0, 0]), &q);
        let rhs = pairing(&p, &q).pow(&[7]);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn pairing_bilinearity_rhs() {
        // e(P, bQ) = e(P, Q)^b
        let p = G1::generator();
        let q = G2::generator();
        let lhs = pairing(&p, &q.scalar_mul(&[5, 0, 0, 0]));
        let rhs = pairing(&p, &q).pow(&[5]);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn pairing_bilinearity_both() {
        // e(aP, bQ) = e(P, Q)^(ab)
        let p = G1::generator();
        let q = G2::generator();
        let lhs = pairing(&p.scalar_mul(&[3, 0, 0, 0]), &q.scalar_mul(&[5, 0, 0, 0]));
        let rhs = pairing(&p, &q).pow(&[15]);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn pairing_negation() {
        // e(P, -Q) · e(P, Q) = 1
        let p = G1::generator();
        let q = G2::generator();
        let e1 = pairing(&p, &q);
        let e2 = pairing(&p, &q.neg());
        assert_eq!(e1 * e2, Fp12::ONE);
    }

    #[test]
    fn pairing_result_has_order_r() {
        // e(P, Q)^r = 1
        let e = pairing(&G1::generator(), &G2::generator());
        let r: [u64; 4] = [
            0x43e1f593f0000001, 0x2833e84879b97091,
            0xb85045b68181585d, 0x30644e72e131a029,
        ];
        assert_eq!(e.pow(&r), Fp12::ONE);
    }
}
