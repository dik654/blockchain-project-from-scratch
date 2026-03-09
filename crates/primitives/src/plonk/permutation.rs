// Permutation Argument — copy constraint를 grand product로 증명
//
// 핵심 아이디어:
//   "와이어 A의 0번 = 와이어 B의 1번" 같은 copy constraint를
//   permutation σ로 인코딩하고, grand product Z(x)로 증명한다.
//
// 알고리즘:
//   1. copy constraint들을 모아 permutation σ 구성 (cycle 표현)
//   2. σ를 다항식으로 인코딩: σ_A(ωⁱ) = position_tag(σ(A,i))
//   3. 랜덤 β, γ로 grand product Z(x) 계산
//   4. Z가 1로 돌아오면 → permutation 만족 (copy constraints 성립)
//
// Position tag:
//   각 wire position을 고유한 Fr 값으로 식별
//   (A, i) → ωⁱ,  (B, i) → K1·ωⁱ,  (C, i) → K2·ωⁱ
//   3개의 코셋이 서로소이므로 3n개 tag가 모두 distinct

use crate::field::Fr;
use crate::qap::Polynomial;
use super::arithmetization::{Column, PlonkConstraintSystem, WirePosition};
use super::{Domain, K1, K2};

// ── Position Tag ──────────────────────────────────────────

/// wire position의 고유 tag 계산
///
/// (A, i) → 1 · ωⁱ
/// (B, i) → K1 · ωⁱ
/// (C, i) → K2 · ωⁱ
fn position_tag(col: Column, row: usize, domain: &Domain) -> Fr {
    let k = match col {
        Column::A => Fr::ONE,
        Column::B => Fr::from_u64(K1),
        Column::C => Fr::from_u64(K2),
    };
    k * domain.elements[row]
}

// ── Permutation 계산 (Union-Find) ─────────────────────────

/// Wire position을 선형 인덱스로 변환
///   A: 0..n, B: n..2n, C: 2n..3n
fn pos_to_idx(pos: WirePosition, n: usize) -> usize {
    let base = match pos.column {
        Column::A => 0,
        Column::B => n,
        Column::C => 2 * n,
    };
    base + pos.row
}

/// 선형 인덱스를 wire position으로 변환
fn idx_to_pos(idx: usize, n: usize) -> WirePosition {
    if idx < n {
        WirePosition { column: Column::A, row: idx }
    } else if idx < 2 * n {
        WirePosition { column: Column::B, row: idx - n }
    } else {
        WirePosition { column: Column::C, row: idx - 2 * n }
    }
}

/// Union-Find: find with path compression
fn find(parent: &mut Vec<usize>, mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]]; // path halving
        x = parent[x];
    }
    x
}

/// Union-Find: union by linking
fn union(parent: &mut Vec<usize>, x: usize, y: usize) {
    let rx = find(parent, x);
    let ry = find(parent, y);
    if rx != ry {
        parent[rx] = ry;
    }
}

/// Copy constraint들로부터 permutation σ 구성
///
/// σ는 cycle 표현: 같은 equivalence class의 position들이 cycle을 형성
///
/// 반환: sigma[idx] = σ가 가리키는 다음 position의 인덱스
fn compute_sigma(
    n: usize,
    copy_constraints: &[(WirePosition, WirePosition)],
) -> Vec<usize> {
    let total = 3 * n;

    // 1. Union-Find 초기화
    let mut parent: Vec<usize> = (0..total).collect();

    // 2. Copy constraint 처리
    for &(p, q) in copy_constraints {
        let pi = pos_to_idx(p, n);
        let qi = pos_to_idx(q, n);
        union(&mut parent, pi, qi);
    }

    // 3. Equivalence class별로 그룹핑
    let mut classes: std::collections::HashMap<usize, Vec<usize>> =
        std::collections::HashMap::new();
    for i in 0..total {
        let root = find(&mut parent, i);
        classes.entry(root).or_default().push(i);
    }

    // 4. 각 class 내에서 cycle 구성
    //    [p₁, p₂, ..., pₖ] → p₁→p₂→...→pₖ→p₁
    let mut sigma: Vec<usize> = (0..total).collect(); // identity
    for (_, class) in &classes {
        if class.len() == 1 {
            // self-loop (identity)
            continue;
        }
        for i in 0..class.len() {
            let next = if i + 1 < class.len() { class[i + 1] } else { class[0] };
            sigma[class[i]] = next;
        }
    }

    sigma
}

// ── Permutation Polynomials ───────────────────────────────

/// Permutation 다항식 σ_A, σ_B, σ_C 계산
///
/// σ_A(ωⁱ) = position_tag(σ(A, i))
/// σ_B(ωⁱ) = position_tag(σ(B, i))
/// σ_C(ωⁱ) = position_tag(σ(C, i))
///
/// copy constraint가 없으면 σ = identity:
///   σ_A(ωⁱ) = ωⁱ, σ_B(ωⁱ) = K1·ωⁱ, σ_C(ωⁱ) = K2·ωⁱ
pub fn compute_permutation_polynomials(
    cs: &PlonkConstraintSystem,
    domain: &Domain,
) -> (Polynomial, Polynomial, Polynomial) {
    let n = domain.n;
    let sigma = compute_sigma(n, cs.copy_constraints());

    // σ_A: σ_A(ωⁱ) = tag of σ(A, i)
    let sigma_a_points: Vec<(Fr, Fr)> = (0..n)
        .map(|i| {
            let from_idx = pos_to_idx(WirePosition { column: Column::A, row: i }, n);
            let to = idx_to_pos(sigma[from_idx], n);
            (domain.elements[i], position_tag(to.column, to.row, domain))
        })
        .collect();

    // σ_B: σ_B(ωⁱ) = tag of σ(B, i)
    let sigma_b_points: Vec<(Fr, Fr)> = (0..n)
        .map(|i| {
            let from_idx = pos_to_idx(WirePosition { column: Column::B, row: i }, n);
            let to = idx_to_pos(sigma[from_idx], n);
            (domain.elements[i], position_tag(to.column, to.row, domain))
        })
        .collect();

    // σ_C: σ_C(ωⁱ) = tag of σ(C, i)
    let sigma_c_points: Vec<(Fr, Fr)> = (0..n)
        .map(|i| {
            let from_idx = pos_to_idx(WirePosition { column: Column::C, row: i }, n);
            let to = idx_to_pos(sigma[from_idx], n);
            (domain.elements[i], position_tag(to.column, to.row, domain))
        })
        .collect();

    (
        Polynomial::lagrange_interpolate(&sigma_a_points),
        Polynomial::lagrange_interpolate(&sigma_b_points),
        Polynomial::lagrange_interpolate(&sigma_c_points),
    )
}

// ── Grand Product Z(x) ───────────────────────────────────

/// Grand product 다항식 Z(x) 계산
///
/// Z(ω⁰) = 1
/// Z(ω^(i+1)) = Z(ωⁱ) · num(i) / den(i)
///
/// num(i) = (aᵢ + β·ωⁱ + γ)(bᵢ + β·K1·ωⁱ + γ)(cᵢ + β·K2·ωⁱ + γ)
/// den(i) = (aᵢ + β·σ_A(ωⁱ) + γ)(bᵢ + β·σ_B(ωⁱ) + γ)(cᵢ + β·σ_C(ωⁱ) + γ)
///
/// copy constraint가 만족되면 grand product가 telescope → Z(ω^n) = 1
pub fn compute_grand_product(
    cs: &PlonkConstraintSystem,
    domain: &Domain,
    sigma_a: &Polynomial,
    sigma_b: &Polynomial,
    sigma_c: &Polynomial,
    beta: Fr,
    gamma: Fr,
) -> Polynomial {
    let n = domain.n;
    let k1 = Fr::from_u64(K1);
    let k2 = Fr::from_u64(K2);

    let mut z_values = Vec::with_capacity(n);
    z_values.push(Fr::ONE); // Z(ω⁰) = 1

    for i in 0..n - 1 {
        let omega_i = domain.elements[i];
        let a_i = cs.wire_value(WirePosition { column: Column::A, row: i });
        let b_i = cs.wire_value(WirePosition { column: Column::B, row: i });
        let c_i = cs.wire_value(WirePosition { column: Column::C, row: i });

        // numerator: identity tag 사용
        let num = (a_i + beta * omega_i + gamma)
            * (b_i + beta * k1 * omega_i + gamma)
            * (c_i + beta * k2 * omega_i + gamma);

        // denominator: sigma tag 사용
        let den = (a_i + beta * sigma_a.eval(omega_i) + gamma)
            * (b_i + beta * sigma_b.eval(omega_i) + gamma)
            * (c_i + beta * sigma_c.eval(omega_i) + gamma);

        let den_inv = den.inv().expect("denominator must be non-zero");
        let z_next = z_values[i] * num * den_inv;
        z_values.push(z_next);
    }

    // Z(x)를 도메인 점에서 Lagrange 보간
    let points: Vec<(Fr, Fr)> = (0..n)
        .map(|i| (domain.elements[i], z_values[i]))
        .collect();
    Polynomial::lagrange_interpolate(&points)
}

/// Grand product가 닫히는지 확인 (Z가 1로 돌아오는지)
///
/// 마지막 행의 numerator/denominator를 곱한 후 1이 되어야 함:
///   Z(ω^(n-1)) · num(n-1) / den(n-1) = 1
pub fn verify_grand_product_closes(
    cs: &PlonkConstraintSystem,
    domain: &Domain,
    sigma_a: &Polynomial,
    sigma_b: &Polynomial,
    sigma_c: &Polynomial,
    z_poly: &Polynomial,
    beta: Fr,
    gamma: Fr,
) -> bool {
    let n = domain.n;
    let k1 = Fr::from_u64(K1);
    let k2 = Fr::from_u64(K2);
    let last = n - 1;
    let omega_last = domain.elements[last];

    let a_last = cs.wire_value(WirePosition { column: Column::A, row: last });
    let b_last = cs.wire_value(WirePosition { column: Column::B, row: last });
    let c_last = cs.wire_value(WirePosition { column: Column::C, row: last });

    let num = (a_last + beta * omega_last + gamma)
        * (b_last + beta * k1 * omega_last + gamma)
        * (c_last + beta * k2 * omega_last + gamma);

    let den = (a_last + beta * sigma_a.eval(omega_last) + gamma)
        * (b_last + beta * sigma_b.eval(omega_last) + gamma)
        * (c_last + beta * sigma_c.eval(omega_last) + gamma);

    let z_last = z_poly.eval(omega_last);
    let final_value = z_last * num * den.inv().expect("non-zero");

    final_value == Fr::ONE
}

// ── 테스트 ────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::arithmetization::PlonkGate;

    fn make_two_gate_cs() -> (PlonkConstraintSystem, usize) {
        // Gate 0: add, 3+4=7
        // Gate 1: mul, 7*2=14
        // Copy: (C,0) ↔ (A,1) — output of gate 0 = input of gate 1
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(3));
        let b = cs.alloc_variable(Fr::from_u64(4));
        let c = cs.alloc_variable(Fr::from_u64(7));
        let d = cs.alloc_variable(Fr::from_u64(2));
        let e = cs.alloc_variable(Fr::from_u64(14));

        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        cs.add_gate(PlonkGate::multiplication_gate(), c, d, e);
        cs.copy_constraint(
            WirePosition { column: Column::C, row: 0 },
            WirePosition { column: Column::A, row: 1 },
        );

        let n = cs.pad_to_power_of_two();
        (cs, n)
    }

    // ── Permutation 구조 테스트 ───────────────────────────

    #[test]
    fn identity_permutation() {
        // Copy constraint 없으면 σ = identity
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(1));
        let b = cs.alloc_variable(Fr::from_u64(2));
        let c = cs.alloc_variable(Fr::from_u64(3));
        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        let n = cs.pad_to_power_of_two();
        let domain = Domain::new(n);

        let (sa, sb, sc) = compute_permutation_polynomials(&cs, &domain);

        // identity: σ_A(ωⁱ) = ωⁱ, σ_B(ωⁱ) = K1·ωⁱ, σ_C(ωⁱ) = K2·ωⁱ
        for i in 0..n {
            let w = domain.elements[i];
            assert_eq!(sa.eval(w), w, "sigma_A identity at {}", i);
            assert_eq!(sb.eval(w), Fr::from_u64(K1) * w, "sigma_B identity at {}", i);
            assert_eq!(sc.eval(w), Fr::from_u64(K2) * w, "sigma_C identity at {}", i);
        }
    }

    #[test]
    fn copy_constraint_permutation() {
        // (C,0) ↔ (A,1): cycle (C,0) → (A,1) → (C,0)
        let (cs, n) = make_two_gate_cs();
        let _domain = Domain::new(n);
        let sigma = compute_sigma(n, cs.copy_constraints());

        // σ(C, 0) should point to (A, 1)
        let c0 = pos_to_idx(WirePosition { column: Column::C, row: 0 }, n);
        let a1 = pos_to_idx(WirePosition { column: Column::A, row: 1 }, n);
        assert_eq!(sigma[c0], a1);
        assert_eq!(sigma[a1], c0);
    }

    #[test]
    fn multiple_copy_constraints_chain() {
        // 3개 chain: (A,0) ↔ (B,1) ↔ (C,0) → 3-cycle
        let mut cs = PlonkConstraintSystem::new();
        let x = cs.alloc_variable(Fr::from_u64(5));
        let zero = cs.alloc_variable(Fr::ZERO);
        cs.add_gate(PlonkGate::dummy_gate(), x, zero, x);
        cs.add_gate(PlonkGate::dummy_gate(), zero, x, zero);
        let n = cs.pad_to_power_of_two();

        cs.copy_constraint(
            WirePosition { column: Column::A, row: 0 },
            WirePosition { column: Column::B, row: 1 },
        );
        cs.copy_constraint(
            WirePosition { column: Column::B, row: 1 },
            WirePosition { column: Column::C, row: 0 },
        );

        let sigma = compute_sigma(n, cs.copy_constraints());

        let a0 = pos_to_idx(WirePosition { column: Column::A, row: 0 }, n);
        let b1 = pos_to_idx(WirePosition { column: Column::B, row: 1 }, n);
        let c0 = pos_to_idx(WirePosition { column: Column::C, row: 0 }, n);

        // cycle: a0 → b1 → c0 → a0
        assert_eq!(sigma[a0], b1);
        assert_eq!(sigma[b1], c0);
        assert_eq!(sigma[c0], a0);
    }

    #[test]
    fn copy_constraint_violation_detected() {
        // copy constraint가 있지만 값이 다른 경우
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(3));
        let b = cs.alloc_variable(Fr::from_u64(4));
        let c = cs.alloc_variable(Fr::from_u64(7));
        // 일부러 다른 값
        let d = cs.alloc_variable(Fr::from_u64(99)); // c=7 ≠ d=99

        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        cs.add_gate(PlonkGate::dummy_gate(), d, d, d);

        // (C,0)=7 ↔ (A,1)=99 — 값이 다름!
        cs.copy_constraint(
            WirePosition { column: Column::C, row: 0 },
            WirePosition { column: Column::A, row: 1 },
        );

        assert!(!cs.are_copy_constraints_satisfied());
    }

    // ── Grand Product Z(x) 테스트 ─────────────────────────

    #[test]
    fn grand_product_identity() {
        // Copy constraint 없음 → Z(x) = 1 (상수)
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(3));
        let b = cs.alloc_variable(Fr::from_u64(4));
        let c = cs.alloc_variable(Fr::from_u64(7));
        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        let n = cs.pad_to_power_of_two();
        let domain = Domain::new(n);

        let (sa, sb, sc) = compute_permutation_polynomials(&cs, &domain);
        let beta = Fr::from_u64(7);
        let gamma = Fr::from_u64(11);
        let z = compute_grand_product(&cs, &domain, &sa, &sb, &sc, beta, gamma);

        // identity permutation → num = den → Z(ωⁱ) = 1 for all i
        for i in 0..n {
            assert_eq!(z.eval(domain.elements[i]), Fr::ONE, "Z should be 1 at {}", i);
        }
    }

    #[test]
    fn grand_product_with_copy_constraints() {
        // Copy constraint가 만족된 경우 → Z closes (1로 돌아옴)
        let (cs, n) = make_two_gate_cs();
        let domain = Domain::new(n);

        let (sa, sb, sc) = compute_permutation_polynomials(&cs, &domain);
        let beta = Fr::from_u64(7);
        let gamma = Fr::from_u64(11);
        let z = compute_grand_product(&cs, &domain, &sa, &sb, &sc, beta, gamma);

        // Z가 닫히는지 확인
        assert!(verify_grand_product_closes(
            &cs, &domain, &sa, &sb, &sc, &z, beta, gamma,
        ));
    }

    #[test]
    fn grand_product_violation_does_not_close() {
        // Copy constraint가 있지만 값이 다른 경우 → Z doesn't close
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(3));
        let b = cs.alloc_variable(Fr::from_u64(4));
        let c = cs.alloc_variable(Fr::from_u64(7));
        let d = cs.alloc_variable(Fr::from_u64(99)); // c=7이 아닌 99
        let e = cs.alloc_variable(Fr::from_u64(198));

        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        cs.add_gate(PlonkGate::multiplication_gate(), d, b, e);

        // (C,0)=7 ↔ (A,1)=99 — 값 불일치!
        cs.copy_constraint(
            WirePosition { column: Column::C, row: 0 },
            WirePosition { column: Column::A, row: 1 },
        );

        let n = cs.pad_to_power_of_two();
        let domain = Domain::new(n);

        let (sa, sb, sc) = compute_permutation_polynomials(&cs, &domain);
        let beta = Fr::from_u64(7);
        let gamma = Fr::from_u64(11);
        let z = compute_grand_product(&cs, &domain, &sa, &sb, &sc, beta, gamma);

        // Z가 닫히지 않아야 함
        assert!(!verify_grand_product_closes(
            &cs, &domain, &sa, &sb, &sc, &z, beta, gamma,
        ));
    }
}
