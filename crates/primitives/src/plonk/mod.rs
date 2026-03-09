// Step 14: PLONKish Arithmetization + Permutation Argument
//
// PLONK이란?
//   Permutations over Lagrange-bases for Oecumenical Noninteractive
//   arguments of Knowledge (Gabizon-Williamson-Ciobotaru, 2019)
//
// R1CS와의 핵심 차이:
//   R1CS: (a·s)(b·s) = (c·s) — 행렬 3개, 곱셈 하나 = 제약 하나
//   PLONKish: q_L·a + q_R·b + q_O·c + q_M·a·b + q_C = 0 — 범용 게이트
//
// 이 모듈의 범위:
//   1. arithmetization: 범용 게이트 + 제약 시스템
//   2. permutation: copy constraint를 grand product로 증명
//   3. lookup: Plookup — lookup argument (테이블 멤버십 증명)
//
//   PLONK prover/verifier는 Step 16에서 구현 (이 단계는 기반만)
//
// 의존성:
//   field::Fr — 스칼라체
//   qap::Polynomial — 다항식 산술 (Lagrange 보간, eval 등)

pub mod arithmetization;
pub mod permutation;
pub mod lookup;
pub mod prover;

use crate::field::Fr;

pub use arithmetization::{
    Column, PlonkConstraintSystem, PlonkGate, SelectorPolynomials, WireIndex, WirePosition,
};
pub use permutation::{
    compute_grand_product, compute_permutation_polynomials, verify_grand_product_closes,
};
pub use lookup::{
    LookupTable, PlookupError, PlookupProof,
    compute_sorted_list, compute_lookup_grand_product,
    verify_lookup_grand_product, compute_plookup,
};
pub use prover::{
    PlonkProof, PlonkSetupParams, VerifyingKey,
    plonk_setup, prove, verify,
};

// ── 코셋 상수 ─────────────────────────────────────────────
//
// PLONK은 3개의 wire column (A, B, C)을 구분하기 위해 코셋을 사용:
//   Column A: {ω⁰, ω¹, ..., ω^(n-1)}          (H 자체)
//   Column B: {K1·ω⁰, K1·ω¹, ..., K1·ω^(n-1)} (K1·H)
//   Column C: {K2·ω⁰, K2·ω¹, ..., K2·ω^(n-1)} (K2·H)
//
// K1=2, K2=3은 H의 원소가 아니므로 3개의 코셋이 서로소 (disjoint)
pub const K1: u64 = 2;
pub const K2: u64 = 3;

// ── Roots of Unity ────────────────────────────────────────
//
// BN254 Fr의 TWO_ADICITY = 28:
//   r - 1 = 2^28 · t (t는 홀수)
//   → 최대 2^28 크기의 multiplicative subgroup 지원
//
// ROOT_OF_UNITY_2_28 = 5^((r-1)/2^28) mod r
//   이 값을 2^(28-k)번 제곱하면 2^k-th root of unity를 얻음
const ROOT_OF_UNITY_2_28_RAW: [u64; 4] = [
    0x9bd61b6e725b19f0,
    0x402d111e41112ed4,
    0x00e0a7eb8ef62abc,
    0x2a3c09f0a58a7e85,
];

// ── Domain ────────────────────────────────────────────────

/// 평가 도메인 H = {1, ω, ω², ..., ω^(n-1)}
///
/// PLONK은 이 도메인 위에서 다항식을 평가한다.
/// n은 반드시 2의 거듭제곱이어야 함.
pub struct Domain {
    pub n: usize,
    pub omega: Fr,
    pub omega_inv: Fr,
    pub elements: Vec<Fr>,
}

impl Domain {
    /// 크기 n의 도메인 생성 (n은 2의 거듭제곱, n ≤ 2^28)
    ///
    /// ω = ROOT_OF_UNITY_2_28 ^ (2^(28 - log2(n)))
    pub fn new(n: usize) -> Self {
        assert!(n >= 2, "domain size must be at least 2");
        assert!(n.is_power_of_two(), "domain size must be power of 2");
        let log_n = n.trailing_zeros() as usize;
        assert!(log_n <= 28, "domain size exceeds max 2^28");

        // ω = ROOT_2_28 ^ (2^(28 - log_n))
        let root = Fr::from_raw(ROOT_OF_UNITY_2_28_RAW);
        let mut omega = root;
        for _ in 0..(28 - log_n) {
            omega = omega * omega;
        }

        let omega_inv = omega.inv().expect("omega must be invertible");

        // 도메인 원소: [1, ω, ω², ..., ω^(n-1)]
        let mut elements = Vec::with_capacity(n);
        let mut current = Fr::ONE;
        for _ in 0..n {
            elements.push(current);
            current = current * omega;
        }

        // ω^n = 1 검증
        debug_assert!(
            current == Fr::ONE,
            "omega^n must equal 1"
        );

        Domain { n, omega, omega_inv, elements }
    }
}

// ── PlonkCircuit trait ────────────────────────────────────

/// PLONK 회로 trait — R1CS의 Circuit trait에 대응
///
/// synthesize()에서 변수 할당 + 게이트 추가 + copy constraint 설정
pub trait PlonkCircuit {
    fn synthesize(&self, cs: &mut PlonkConstraintSystem);
}

// ── 테스트 ────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::Fr;

    #[test]
    fn domain_roots_of_unity() {
        // 여러 크기의 도메인에서 ω^n = 1, ω^(n/2) ≠ 1 확인
        for &size in &[2, 4, 8, 16] {
            let domain = Domain::new(size);

            assert_eq!(domain.n, size);
            assert_eq!(domain.elements.len(), size);

            // ω^n = 1
            let mut omega_n = Fr::ONE;
            for _ in 0..size {
                omega_n = omega_n * domain.omega;
            }
            assert_eq!(omega_n, Fr::ONE, "omega^n must equal 1 for n={}", size);

            // ω^(n/2) ≠ 1 (primitive root)
            let mut omega_half = Fr::ONE;
            for _ in 0..size / 2 {
                omega_half = omega_half * domain.omega;
            }
            assert_ne!(omega_half, Fr::ONE, "omega^(n/2) must not equal 1 for n={}", size);

            // ω^(n/2) = -1
            assert_eq!(omega_half, -Fr::ONE, "omega^(n/2) must equal -1 for n={}", size);

            // 모든 원소가 서로 다른지 확인
            for i in 0..size {
                for j in i + 1..size {
                    assert_ne!(
                        domain.elements[i], domain.elements[j],
                        "domain elements must be distinct"
                    );
                }
            }

            // 첫 번째 원소 = 1
            assert_eq!(domain.elements[0], Fr::ONE);
        }
    }

    // ── End-to-End: PlonkCircuit trait 테스트 ──────────────

    struct AddCircuit {
        a: u64,
        b: u64,
    }

    impl PlonkCircuit for AddCircuit {
        fn synthesize(&self, cs: &mut PlonkConstraintSystem) {
            let a = cs.alloc_variable(Fr::from_u64(self.a));
            let b = cs.alloc_variable(Fr::from_u64(self.b));
            let c = cs.alloc_variable(Fr::from_u64(self.a + self.b));
            cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        }
    }

    #[test]
    fn plonk_circuit_trait() {
        // a + b = c 회로: synthesize → 검증 → 다항식 추출 → grand product
        let circuit = AddCircuit { a: 3, b: 4 };
        let mut cs = PlonkConstraintSystem::new();
        circuit.synthesize(&mut cs);

        assert!(cs.is_satisfied());
        let n = cs.pad_to_power_of_two();
        assert!(n >= 2);

        let domain = Domain::new(n);
        let selectors = cs.selector_polynomials(&domain);
        let (a_poly, b_poly, c_poly) = cs.wire_polynomials(&domain);

        // 도메인 점에서 게이트 방정식 확인
        for i in 0..n {
            let omega_i = domain.elements[i];
            let a_val = a_poly.eval(omega_i);
            let b_val = b_poly.eval(omega_i);
            let c_val = c_poly.eval(omega_i);
            let result = selectors.q_l.eval(omega_i) * a_val
                + selectors.q_r.eval(omega_i) * b_val
                + selectors.q_o.eval(omega_i) * c_val
                + selectors.q_m.eval(omega_i) * a_val * b_val
                + selectors.q_c.eval(omega_i);
            assert!(result.is_zero(), "gate equation failed at row {}", i);
        }

        // grand product (copy constraint 없음 → Z = 1)
        let (sigma_a, sigma_b, sigma_c) =
            compute_permutation_polynomials(&cs, &domain);
        let beta = Fr::from_u64(7);
        let gamma = Fr::from_u64(11);
        let z = compute_grand_product(
            &cs, &domain, &sigma_a, &sigma_b, &sigma_c, beta, gamma,
        );
        assert!(verify_grand_product_closes(
            &cs, &domain, &sigma_a, &sigma_b, &sigma_c, &z, beta, gamma,
        ));
    }

    // ── End-to-End: x³ + x + 5 = y ───────────────────────

    struct CubicCircuit {
        x: u64,
    }

    impl PlonkCircuit for CubicCircuit {
        fn synthesize(&self, cs: &mut PlonkConstraintSystem) {
            let x_val = Fr::from_u64(self.x);
            let v1_val = x_val * x_val;           // x²
            let v2_val = v1_val * x_val;           // x³
            let y_val = v2_val + x_val + Fr::from_u64(5); // x³+x+5

            let x = cs.alloc_variable(x_val);
            let v1 = cs.alloc_variable(v1_val);
            let v2 = cs.alloc_variable(v2_val);
            let y = cs.alloc_variable(y_val);

            // Gate 0: x * x = v1
            cs.add_gate(PlonkGate::multiplication_gate(), x, x, v1);
            // Gate 1: v1 * x = v2
            cs.add_gate(PlonkGate::multiplication_gate(), v1, x, v2);
            // Gate 2: v2 + x + 5 = y
            //   q_L·a + q_R·b + q_O·c + q_C = 0
            //   1·v2 + 1·x + (-1)·y + 5 = 0
            cs.add_gate(
                PlonkGate { q_l: Fr::ONE, q_r: Fr::ONE, q_o: -Fr::ONE, q_m: Fr::ZERO, q_c: Fr::from_u64(5) },
                v2, x, y,
            );

            // Copy constraints:
            // x는 (A,0), (B,0), (B,1), (B,2) 에서 사용
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
            // v1은 (C,0), (A,1) 에서 사용
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 0 },
                WirePosition { column: Column::A, row: 1 },
            );
            // v2는 (C,1), (A,2) 에서 사용
            cs.copy_constraint(
                WirePosition { column: Column::C, row: 1 },
                WirePosition { column: Column::A, row: 2 },
            );
        }
    }

    #[test]
    fn cubic_circuit_plonk() {
        // x³ + x + 5 = y, x=3 → y=35
        let circuit = CubicCircuit { x: 3 };
        let mut cs = PlonkConstraintSystem::new();
        circuit.synthesize(&mut cs);

        assert!(cs.is_satisfied());
        assert!(cs.are_copy_constraints_satisfied());

        let n = cs.pad_to_power_of_two();
        assert_eq!(n, 4); // 3 real gates + 1 dummy → 4

        let domain = Domain::new(n);

        // 다항식 추출
        let selectors = cs.selector_polynomials(&domain);
        let (a_poly, b_poly, c_poly) = cs.wire_polynomials(&domain);

        // 게이트 방정식 확인 (다항식 수준)
        for i in 0..n {
            let w = domain.elements[i];
            let a = a_poly.eval(w);
            let b = b_poly.eval(w);
            let c = c_poly.eval(w);
            let result = selectors.q_l.eval(w) * a
                + selectors.q_r.eval(w) * b
                + selectors.q_o.eval(w) * c
                + selectors.q_m.eval(w) * a * b
                + selectors.q_c.eval(w);
            assert!(result.is_zero(), "gate equation failed at row {}", i);
        }

        // Permutation + grand product
        let (sigma_a, sigma_b, sigma_c) =
            compute_permutation_polynomials(&cs, &domain);
        let beta = Fr::from_u64(13);
        let gamma = Fr::from_u64(17);
        let z = compute_grand_product(
            &cs, &domain, &sigma_a, &sigma_b, &sigma_c, beta, gamma,
        );
        assert!(verify_grand_product_closes(
            &cs, &domain, &sigma_a, &sigma_b, &sigma_c, &z, beta, gamma,
        ));
    }
}
