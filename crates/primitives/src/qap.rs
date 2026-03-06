// Step 11: QAP (Quadratic Arithmetic Program)
//
// R1CS → QAP 변환:
//   R1CS: m개의 제약, n개의 변수
//     제약 i: ⟨aᵢ, s⟩ · ⟨bᵢ, s⟩ = ⟨cᵢ, s⟩
//
//   QAP: 다항식 형태로 변환
//     도메인 D = {ω₁, ..., ωₘ} 선택 (m개의 서로 다른 Fr 원소)
//
//     각 변수 j에 대해 다항식 보간:
//       aⱼ(ωᵢ) = A[i,j]  (행렬 A의 j번째 열)
//       bⱼ(ωᵢ) = B[i,j]
//       cⱼ(ωᵢ) = C[i,j]
//
//     witness s로 결합:
//       a(x) = Σⱼ sⱼ · aⱼ(x)
//       b(x) = Σⱼ sⱼ · bⱼ(x)
//       c(x) = Σⱼ sⱼ · cⱼ(x)
//
//     핵심 동치:
//       R1CS 만족 ⟺ a(x)·b(x) - c(x) ≡ 0 (mod t(x))
//       여기서 t(x) = ∏(x - ωᵢ) (소거 다항식)
//
//     증명자는 h(x) = (a(x)·b(x) - c(x)) / t(x) 를 계산
//     검증자는 a(τ)·b(τ) - c(τ) = h(τ)·t(τ) 를 pairing으로 확인
//
// 왜 다항식인가?
//   - m개의 등식 검사를 "하나의 다항식 항등식"으로 압축
//   - 다항식 commitment + pairing으로 "값을 몰라도" 검증 가능
//   - Schwartz-Zippel 보조정리: 랜덤 τ에서 성립하면
//     전체 다항식이 같을 확률이 압도적

use crate::field::Fr;
use crate::r1cs::ConstraintSystem;

// ── 다항식 ──────────────────────────────────────────────

/// 다항식: p(x) = coeffs[0] + coeffs[1]·x + coeffs[2]·x² + ...
///
/// 계수 표현 (coefficient form)
/// 교육용으로 O(n²) 연산 사용 — FFT 미적용
#[derive(Debug, Clone)]
pub struct Polynomial {
    pub coeffs: Vec<Fr>,
}

impl Polynomial {
    /// 영 다항식
    pub fn zero() -> Self {
        Polynomial { coeffs: vec![] }
    }

    /// 상수 다항식: p(x) = c
    pub fn constant(c: Fr) -> Self {
        if c.is_zero() {
            Self::zero()
        } else {
            Polynomial { coeffs: vec![c] }
        }
    }

    /// 계수로 생성
    pub fn from_coeffs(coeffs: Vec<Fr>) -> Self {
        let mut p = Polynomial { coeffs };
        p.trim();
        p
    }

    /// 영 다항식인지
    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// 차수 (영 다항식은 0 반환)
    pub fn degree(&self) -> usize {
        if self.coeffs.is_empty() { 0 } else { self.coeffs.len() - 1 }
    }

    /// 선행 0 제거
    fn trim(&mut self) {
        while let Some(&c) = self.coeffs.last() {
            if c.is_zero() {
                self.coeffs.pop();
            } else {
                break;
            }
        }
    }

    /// 점 x에서 평가: Horner's method
    ///
    /// p(x) = (...((aₙx + aₙ₋₁)x + aₙ₋₂)x + ...) + a₀
    ///
    /// O(n) — 나이브 방식 O(n²)보다 효율적
    pub fn eval(&self, x: Fr) -> Fr {
        if self.coeffs.is_empty() {
            return Fr::ZERO;
        }
        let mut result = Fr::ZERO;
        for &c in self.coeffs.iter().rev() {
            result = result * x + c;
        }
        result
    }

    /// 스칼라 곱: s · p(x)
    pub fn scale(&self, s: Fr) -> Self {
        if s.is_zero() {
            return Self::zero();
        }
        Polynomial::from_coeffs(
            self.coeffs.iter().map(|&c| c * s).collect()
        )
    }

    /// Lagrange 보간
    ///
    /// n개의 점 (x₀,y₀), ..., (xₙ₋₁,yₙ₋₁)이 주어지면
    /// p(xᵢ) = yᵢ를 만족하는 유일한 degree < n 다항식 반환
    ///
    /// p(x) = Σᵢ yᵢ · Lᵢ(x)
    /// Lᵢ(x) = ∏_{j≠i} (x - xⱼ) / (xᵢ - xⱼ)
    ///
    /// O(n²) — FFT 기반 O(n log² n)보다 느리지만 교육용으로 충분
    pub fn lagrange_interpolate(points: &[(Fr, Fr)]) -> Self {
        let n = points.len();
        if n == 0 {
            return Self::zero();
        }

        let mut result = vec![Fr::ZERO; n];

        for i in 0..n {
            let (xi, yi) = points[i];
            if yi.is_zero() {
                continue;
            }

            // 분모: ∏_{j≠i} (xᵢ - xⱼ) — 스칼라
            let mut denom = Fr::ONE;
            for j in 0..n {
                if j != i {
                    denom = denom * (xi - points[j].0);
                }
            }
            let denom_inv = denom.inv().expect("domain points must be distinct");

            // 분자: Lᵢ(x) = ∏_{j≠i} (x - xⱼ) — 다항식
            // 하나씩 곱하여 계수 벡터 구축
            let mut basis = vec![Fr::ZERO; n];
            basis[0] = Fr::ONE;
            let mut deg = 0;

            for j in 0..n {
                if j == i {
                    continue;
                }
                let xj = points[j].0;

                // basis(x) *= (x - xⱼ)
                //   새 계수[k] = 이전 계수[k-1] - xⱼ · 이전 계수[k]
                for k in (1..=deg + 1).rev() {
                    basis[k] = basis[k - 1] - basis[k] * xj;
                }
                basis[0] = -basis[0] * xj;
                deg += 1;
            }

            // result += yᵢ · (1/denom) · basis
            let coeff = yi * denom_inv;
            for k in 0..n {
                result[k] = result[k] + coeff * basis[k];
            }
        }

        Polynomial::from_coeffs(result)
    }

    /// 다항식 나눗셈: self = quotient · divisor + remainder
    ///
    /// polynomial long division
    /// 반환: (quotient, remainder)
    pub fn div_rem(&self, divisor: &Self) -> (Self, Self) {
        if divisor.is_zero() {
            panic!("division by zero polynomial");
        }

        if self.is_zero() || self.degree() < divisor.degree() {
            return (Self::zero(), self.clone());
        }

        let mut remainder = self.coeffs.clone();
        let divisor_lead_inv = divisor.coeffs.last().unwrap().inv()
            .expect("leading coefficient must be non-zero");
        let div_deg = divisor.degree();
        let quot_deg = self.degree() - div_deg;

        let mut quotient = vec![Fr::ZERO; quot_deg + 1];

        for i in (0..=quot_deg).rev() {
            let coeff = remainder[i + div_deg] * divisor_lead_inv;
            quotient[i] = coeff;
            for j in 0..=div_deg {
                remainder[i + j] = remainder[i + j] - coeff * divisor.coeffs[j];
            }
        }

        (Polynomial::from_coeffs(quotient), Polynomial::from_coeffs(remainder))
    }
}

// ── 연산자 오버로딩 ──────────────────────────────────────

impl std::ops::Add for &Polynomial {
    type Output = Polynomial;
    fn add(self, rhs: &Polynomial) -> Polynomial {
        let len = std::cmp::max(self.coeffs.len(), rhs.coeffs.len());
        let mut coeffs = vec![Fr::ZERO; len];
        for (i, &c) in self.coeffs.iter().enumerate() {
            coeffs[i] = coeffs[i] + c;
        }
        for (i, &c) in rhs.coeffs.iter().enumerate() {
            coeffs[i] = coeffs[i] + c;
        }
        Polynomial::from_coeffs(coeffs)
    }
}

impl std::ops::Sub for &Polynomial {
    type Output = Polynomial;
    fn sub(self, rhs: &Polynomial) -> Polynomial {
        let len = std::cmp::max(self.coeffs.len(), rhs.coeffs.len());
        let mut coeffs = vec![Fr::ZERO; len];
        for (i, &c) in self.coeffs.iter().enumerate() {
            coeffs[i] = coeffs[i] + c;
        }
        for (i, &c) in rhs.coeffs.iter().enumerate() {
            coeffs[i] = coeffs[i] - c;
        }
        Polynomial::from_coeffs(coeffs)
    }
}

impl std::ops::Mul for &Polynomial {
    type Output = Polynomial;
    fn mul(self, rhs: &Polynomial) -> Polynomial {
        if self.is_zero() || rhs.is_zero() {
            return Polynomial::zero();
        }
        let len = self.coeffs.len() + rhs.coeffs.len() - 1;
        let mut coeffs = vec![Fr::ZERO; len];
        for (i, &a) in self.coeffs.iter().enumerate() {
            for (j, &b) in rhs.coeffs.iter().enumerate() {
                coeffs[i + j] = coeffs[i + j] + a * b;
            }
        }
        Polynomial::from_coeffs(coeffs)
    }
}

impl PartialEq for Polynomial {
    fn eq(&self, other: &Self) -> bool {
        let len = std::cmp::max(self.coeffs.len(), other.coeffs.len());
        for i in 0..len {
            let ca = if i < self.coeffs.len() { self.coeffs[i] } else { Fr::ZERO };
            let cb = if i < other.coeffs.len() { other.coeffs[i] } else { Fr::ZERO };
            if ca != cb {
                return false;
            }
        }
        true
    }
}

impl Eq for Polynomial {}

// ── 소거 다항식 ──────────────────────────────────────────

/// 소거 다항식: t(x) = ∏ᵢ (x - ωᵢ)
///
/// 도메인의 모든 점에서 0이 되는 다항식
/// QAP에서 "모든 제약을 만족" ⟺ "t(x)로 나누어떨어짐"
pub fn vanishing_polynomial(domain: &[Fr]) -> Polynomial {
    let mut result = Polynomial::from_coeffs(vec![Fr::ONE]);
    for &omega in domain {
        let factor = Polynomial::from_coeffs(vec![-omega, Fr::ONE]);
        result = &result * &factor;
    }
    result
}

// ── QAP ──────────────────────────────────────────────────

/// QAP (Quadratic Arithmetic Program)
///
/// R1CS 행렬 (A, B, C)를 다항식으로 변환한 결과
///
/// 핵심 동치:
///   R1CS 만족 ⟺ a(x)·b(x) - c(x) ≡ 0 (mod t(x))
///   ⟺ h(x) = (a(x)·b(x) - c(x)) / t(x) 가 다항식
pub struct QAP {
    /// aⱼ(x): 행렬 A의 j번째 열을 보간한 다항식
    pub a_polys: Vec<Polynomial>,
    /// bⱼ(x): 행렬 B의 j번째 열
    pub b_polys: Vec<Polynomial>,
    /// cⱼ(x): 행렬 C의 j번째 열
    pub c_polys: Vec<Polynomial>,
    /// t(x) = ∏(x - ωᵢ): 소거 다항식
    pub t: Polynomial,
    /// 도메인: {ω₁, ..., ωₘ}
    pub domain: Vec<Fr>,
    pub num_instance: usize,
    pub num_variables: usize,
}

impl QAP {
    /// R1CS → QAP 변환
    ///
    /// 1. 도메인 선택: ωᵢ = i+1 (단순 선택, 교육용)
    /// 2. 각 변수 j에 대해: A[*,j], B[*,j], C[*,j] 열을 다항식으로 보간
    /// 3. 소거 다항식 t(x) 계산
    ///
    /// 프로덕션에서는 roots of unity를 사용하여 FFT 기반 O(n log n) 보간 가능
    /// 여기서는 임의 점 {1, 2, ..., m}을 사용하여 O(n²) Lagrange 보간
    pub fn from_r1cs(cs: &ConstraintSystem) -> Self {
        let m = cs.num_constraints();
        let n = cs.num_variables();

        // 도메인: {1, 2, ..., m}
        let domain: Vec<Fr> = (1..=m as u64).map(Fr::from_u64).collect();

        // 희소 행렬 추출
        let (a_mat, b_mat, c_mat) = cs.to_matrices();

        // 각 변수(열)에 대해 다항식 보간
        let a_polys = columns_to_polynomials(&a_mat, n, &domain);
        let b_polys = columns_to_polynomials(&b_mat, n, &domain);
        let c_polys = columns_to_polynomials(&c_mat, n, &domain);

        // 소거 다항식
        let t = vanishing_polynomial(&domain);

        QAP {
            a_polys,
            b_polys,
            c_polys,
            t,
            domain,
            num_instance: cs.num_instance,
            num_variables: n,
        }
    }

    /// witness로 결합 다항식 계산
    ///
    /// a(x) = Σⱼ sⱼ · aⱼ(x)
    /// b(x) = Σⱼ sⱼ · bⱼ(x)
    /// c(x) = Σⱼ sⱼ · cⱼ(x)
    pub fn compute_witness_polys(
        &self,
        witness: &[Fr],
    ) -> (Polynomial, Polynomial, Polynomial) {
        assert_eq!(witness.len(), self.num_variables);

        let mut a = Polynomial::zero();
        let mut b = Polynomial::zero();
        let mut c = Polynomial::zero();

        for j in 0..self.num_variables {
            if !witness[j].is_zero() {
                a = &a + &self.a_polys[j].scale(witness[j]);
                b = &b + &self.b_polys[j].scale(witness[j]);
                c = &c + &self.c_polys[j].scale(witness[j]);
            }
        }

        (a, b, c)
    }

    /// h(x) = (a(x)·b(x) - c(x)) / t(x) 계산
    ///
    /// R1CS가 만족되면 나누어떨어져 Some(h) 반환
    /// 만족되지 않으면 나머지가 있어 None 반환
    pub fn compute_h(&self, witness: &[Fr]) -> Option<Polynomial> {
        let (a, b, c) = self.compute_witness_polys(witness);

        // p(x) = a(x)·b(x) - c(x)
        let ab = &a * &b;
        let p = &ab - &c;

        // p(x) / t(x) = (h(x), remainder)
        let (h, rem) = p.div_rem(&self.t);

        if rem.is_zero() {
            Some(h)
        } else {
            None
        }
    }

    /// QAP 만족 여부 검증
    ///
    /// a(x)·b(x) - c(x)가 t(x)로 나누어떨어지는지 확인
    pub fn verify(&self, witness: &[Fr]) -> bool {
        self.compute_h(witness).is_some()
    }

    /// 도메인의 각 점에서 다항식 동치 검증 (디버깅용)
    ///
    /// 모든 ωᵢ에서 a(ωᵢ)·b(ωᵢ) = c(ωᵢ) 인지 확인
    pub fn verify_at_domain(&self, witness: &[Fr]) -> bool {
        let (a, b, c) = self.compute_witness_polys(witness);

        for &omega in &self.domain {
            let a_val = a.eval(omega);
            let b_val = b.eval(omega);
            let c_val = c.eval(omega);
            if a_val * b_val != c_val {
                return false;
            }
        }
        true
    }
}

/// 희소 행렬의 각 열을 다항식으로 보간
///
/// 행렬의 j번째 열: 값 A[i,j]을 점 ωᵢ에서 보간
fn columns_to_polynomials(
    matrix: &[Vec<(usize, Fr)>],
    num_vars: usize,
    domain: &[Fr],
) -> Vec<Polynomial> {
    let m = matrix.len();

    if m == 0 {
        return vec![Polynomial::zero(); num_vars];
    }

    (0..num_vars).map(|j| {
        // 열 j의 모든 값 수집
        let mut all_zero = true;
        let points: Vec<(Fr, Fr)> = (0..m).map(|i| {
            let val = matrix[i].iter()
                .find(|&&(col, _)| col == j)
                .map(|&(_, v)| v)
                .unwrap_or(Fr::ZERO);
            if !val.is_zero() {
                all_zero = false;
            }
            (domain[i], val)
        }).collect();

        // 열이 전부 0이면 보간 생략
        if all_zero {
            Polynomial::zero()
        } else {
            Polynomial::lagrange_interpolate(&points)
        }
    }).collect()
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::r1cs::{LinearCombination, Variable, Circuit};

    // ── 다항식 기본 ──────────────────────────────────────

    #[test]
    fn poly_zero() {
        let p = Polynomial::zero();
        assert!(p.is_zero());
        assert_eq!(p.eval(Fr::from_u64(42)), Fr::ZERO);
    }

    #[test]
    fn poly_constant() {
        let p = Polynomial::constant(Fr::from_u64(7));
        assert_eq!(p.eval(Fr::from_u64(0)), Fr::from_u64(7));
        assert_eq!(p.eval(Fr::from_u64(100)), Fr::from_u64(7));
        assert_eq!(p.degree(), 0);
    }

    #[test]
    fn poly_linear() {
        // p(x) = 2x + 3
        let p = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(2)]);
        assert_eq!(p.eval(Fr::from_u64(0)), Fr::from_u64(3));
        assert_eq!(p.eval(Fr::from_u64(1)), Fr::from_u64(5));
        assert_eq!(p.eval(Fr::from_u64(5)), Fr::from_u64(13));
        assert_eq!(p.degree(), 1);
    }

    #[test]
    fn poly_quadratic() {
        // p(x) = x² + 2x + 1 = (x+1)²
        let p = Polynomial::from_coeffs(vec![
            Fr::from_u64(1), Fr::from_u64(2), Fr::from_u64(1),
        ]);
        assert_eq!(p.eval(Fr::from_u64(0)), Fr::from_u64(1));  // 1
        assert_eq!(p.eval(Fr::from_u64(1)), Fr::from_u64(4));  // 4
        assert_eq!(p.eval(Fr::from_u64(2)), Fr::from_u64(9));  // 9
        assert_eq!(p.eval(Fr::from_u64(3)), Fr::from_u64(16)); // 16
    }

    // ── 다항식 산술 ──────────────────────────────────────

    #[test]
    fn poly_add() {
        // (x + 1) + (2x + 3) = 3x + 4
        let a = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(1)]);
        let b = Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(2)]);
        let c = &a + &b;
        assert_eq!(c, Polynomial::from_coeffs(vec![Fr::from_u64(4), Fr::from_u64(3)]));
    }

    #[test]
    fn poly_sub() {
        // (3x + 5) - (x + 2) = 2x + 3
        let a = Polynomial::from_coeffs(vec![Fr::from_u64(5), Fr::from_u64(3)]);
        let b = Polynomial::from_coeffs(vec![Fr::from_u64(2), Fr::from_u64(1)]);
        let c = &a - &b;
        assert_eq!(c, Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(2)]));
    }

    #[test]
    fn poly_mul() {
        // (x + 1)(x + 2) = x² + 3x + 2
        let a = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(1)]);
        let b = Polynomial::from_coeffs(vec![Fr::from_u64(2), Fr::from_u64(1)]);
        let c = &a * &b;
        assert_eq!(c, Polynomial::from_coeffs(vec![
            Fr::from_u64(2), Fr::from_u64(3), Fr::from_u64(1),
        ]));
    }

    #[test]
    fn poly_mul_by_zero() {
        let a = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(1)]);
        let z = Polynomial::zero();
        assert!((&a * &z).is_zero());
        assert!((&z * &a).is_zero());
    }

    #[test]
    fn poly_scale() {
        // 3 · (x + 1) = 3x + 3
        let p = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(1)]);
        let q = p.scale(Fr::from_u64(3));
        assert_eq!(q, Polynomial::from_coeffs(vec![Fr::from_u64(3), Fr::from_u64(3)]));
    }

    // ── Lagrange 보간 ────────────────────────────────────

    #[test]
    fn lagrange_single_point() {
        // 1개의 점: (3, 7) → p(x) = 7
        let p = Polynomial::lagrange_interpolate(&[
            (Fr::from_u64(3), Fr::from_u64(7)),
        ]);
        assert_eq!(p.eval(Fr::from_u64(3)), Fr::from_u64(7));
        assert_eq!(p.degree(), 0);
    }

    #[test]
    fn lagrange_two_points() {
        // 2개의 점: (1, 3), (2, 5) → p(x) = 2x + 1
        let p = Polynomial::lagrange_interpolate(&[
            (Fr::from_u64(1), Fr::from_u64(3)),
            (Fr::from_u64(2), Fr::from_u64(5)),
        ]);
        assert_eq!(p.eval(Fr::from_u64(1)), Fr::from_u64(3));
        assert_eq!(p.eval(Fr::from_u64(2)), Fr::from_u64(5));
        assert_eq!(p.eval(Fr::from_u64(0)), Fr::from_u64(1)); // 2·0 + 1
        assert_eq!(p.degree(), 1);
    }

    #[test]
    fn lagrange_three_points() {
        // 3개의 점: (1, 1), (2, 4), (3, 9) → p(x) = x²
        let p = Polynomial::lagrange_interpolate(&[
            (Fr::from_u64(1), Fr::from_u64(1)),
            (Fr::from_u64(2), Fr::from_u64(4)),
            (Fr::from_u64(3), Fr::from_u64(9)),
        ]);
        assert_eq!(p.eval(Fr::from_u64(1)), Fr::from_u64(1));
        assert_eq!(p.eval(Fr::from_u64(2)), Fr::from_u64(4));
        assert_eq!(p.eval(Fr::from_u64(3)), Fr::from_u64(9));
        assert_eq!(p.eval(Fr::from_u64(4)), Fr::from_u64(16));
        assert_eq!(p.eval(Fr::from_u64(0)), Fr::ZERO);
    }

    #[test]
    fn lagrange_with_zeros() {
        // (1, 0), (2, 0), (3, 5) → 일부 yᵢ가 0인 경우
        let p = Polynomial::lagrange_interpolate(&[
            (Fr::from_u64(1), Fr::ZERO),
            (Fr::from_u64(2), Fr::ZERO),
            (Fr::from_u64(3), Fr::from_u64(5)),
        ]);
        assert_eq!(p.eval(Fr::from_u64(1)), Fr::ZERO);
        assert_eq!(p.eval(Fr::from_u64(2)), Fr::ZERO);
        assert_eq!(p.eval(Fr::from_u64(3)), Fr::from_u64(5));
    }

    #[test]
    fn lagrange_all_zeros() {
        let p = Polynomial::lagrange_interpolate(&[
            (Fr::from_u64(1), Fr::ZERO),
            (Fr::from_u64(2), Fr::ZERO),
            (Fr::from_u64(3), Fr::ZERO),
        ]);
        assert!(p.is_zero());
    }

    // ── 다항식 나눗셈 ────────────────────────────────────

    #[test]
    fn poly_div_exact() {
        // (x² + 3x + 2) / (x + 1) = (x + 2), remainder = 0
        let dividend = Polynomial::from_coeffs(vec![
            Fr::from_u64(2), Fr::from_u64(3), Fr::from_u64(1),
        ]);
        let divisor = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(1)]);
        let (q, r) = dividend.div_rem(&divisor);

        assert_eq!(q, Polynomial::from_coeffs(vec![Fr::from_u64(2), Fr::from_u64(1)]));
        assert!(r.is_zero());
    }

    #[test]
    fn poly_div_with_remainder() {
        // (x² + 1) / (x + 1) = (x - 1), remainder = 2
        let dividend = Polynomial::from_coeffs(vec![
            Fr::from_u64(1), Fr::ZERO, Fr::from_u64(1),
        ]);
        let divisor = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(1)]);
        let (q, r) = dividend.div_rem(&divisor);

        assert_eq!(q, Polynomial::from_coeffs(vec![-Fr::ONE, Fr::ONE]));
        assert_eq!(r, Polynomial::constant(Fr::from_u64(2)));

        // 검증: dividend = q * divisor + r
        let reconstructed = &(&q * &divisor) + &r;
        assert_eq!(reconstructed, dividend);
    }

    #[test]
    fn poly_div_lower_degree() {
        // degree(dividend) < degree(divisor) → q=0, r=dividend
        let dividend = Polynomial::from_coeffs(vec![Fr::from_u64(5)]);
        let divisor = Polynomial::from_coeffs(vec![Fr::from_u64(1), Fr::from_u64(1)]);
        let (q, r) = dividend.div_rem(&divisor);
        assert!(q.is_zero());
        assert_eq!(r, dividend);
    }

    // ── 소거 다항식 ──────────────────────────────────────

    #[test]
    fn vanishing_at_domain() {
        let domain = vec![Fr::from_u64(1), Fr::from_u64(2), Fr::from_u64(3)];
        let t = vanishing_polynomial(&domain);

        // 도메인의 모든 점에서 0
        for &omega in &domain {
            assert_eq!(t.eval(omega), Fr::ZERO);
        }

        // 도메인 밖에서는 0이 아님
        assert_ne!(t.eval(Fr::from_u64(4)), Fr::ZERO);
        assert_ne!(t.eval(Fr::from_u64(0)), Fr::ZERO);

        // degree = |domain|
        assert_eq!(t.degree(), 3);
    }

    #[test]
    fn vanishing_coefficients() {
        // t(x) = (x-1)(x-2) = x² - 3x + 2
        let domain = vec![Fr::from_u64(1), Fr::from_u64(2)];
        let t = vanishing_polynomial(&domain);
        assert_eq!(t, Polynomial::from_coeffs(vec![
            Fr::from_u64(2), -Fr::from_u64(3), Fr::ONE,
        ]));
    }

    // ── QAP: 단순 곱셈 회로 ─────────────────────────────

    #[test]
    fn qap_multiply() {
        // 회로: x * y = z (1 제약, 4 변수)
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

        // R1CS → QAP
        let qap = QAP::from_r1cs(&cs);

        assert_eq!(qap.domain.len(), 1);       // 1 제약
        assert_eq!(qap.num_variables, 4);       // One, z, x, y
        assert_eq!(qap.t.degree(), 1);          // t(x) = x - 1

        // 도메인에서 검증
        assert!(qap.verify_at_domain(&cs.values));

        // h(x) 계산 (나누어떨어져야 함)
        assert!(qap.verify(&cs.values));

        let h = qap.compute_h(&cs.values).unwrap();
        // 1 제약이면 h의 degree ≤ 2·0 - 1 = -1, 즉 h = 0 (상수)
        // a(x)=3, b(x)=4, c(x)=12 → a·b - c = 0, h = 0/t = 0
        assert!(h.is_zero());
    }

    // ── QAP: 3차 다항식 회로 ─────────────────────────────

    /// f(x) = x³ + x + 5 = y
    ///
    /// R1CS:
    ///   제약 1: x * x = t1
    ///   제약 2: t1 * x = t2
    ///   제약 3: (t2 + x + 5) * 1 = y
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
                LinearCombination::from(y),
            );
        }
    }

    #[test]
    fn qap_cubic() {
        let circuit = CubicCircuit { x: Fr::from_u64(3) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 3);

        let qap = QAP::from_r1cs(&cs);

        assert_eq!(qap.domain.len(), 3);
        assert_eq!(qap.t.degree(), 3);

        // 도메인에서 검증
        assert!(qap.verify_at_domain(&cs.values));

        // h(x) 존재 (valid witness)
        assert!(qap.verify(&cs.values));

        let h = qap.compute_h(&cs.values).unwrap();
        // degree(h) ≤ 2(m-1) - m = m - 2 = 1
        assert!(h.degree() <= 1);

        // 항등식 검증: a(x)·b(x) - c(x) = h(x)·t(x) 를 랜덤 점에서 확인
        let (a, b, c) = qap.compute_witness_polys(&cs.values);
        let tau = Fr::from_u64(42); // 랜덤 점
        let lhs = a.eval(tau) * b.eval(tau) - c.eval(tau);
        let rhs = h.eval(tau) * qap.t.eval(tau);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn qap_cubic_different_inputs() {
        for x_val in [0u64, 1, 2, 5, 100] {
            let circuit = CubicCircuit { x: Fr::from_u64(x_val) };
            let mut cs = ConstraintSystem::new();
            circuit.synthesize(&mut cs);

            assert!(cs.is_satisfied());

            let qap = QAP::from_r1cs(&cs);
            assert!(qap.verify(&cs.values),
                "QAP failed for x={}", x_val);
        }
    }

    // ── QAP: 잘못된 witness ──────────────────────────────

    #[test]
    fn qap_wrong_witness_fails() {
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_witness(Fr::from_u64(4));
        let _z = cs.alloc_instance(Fr::from_u64(11)); // 3*4 ≠ 11

        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(y),
            LinearCombination::from(Variable::Instance(0)),
        );

        // R1CS 불만족
        assert!(!cs.is_satisfied());

        // QAP도 불만족 (h(x)가 다항식이 아님)
        let qap = QAP::from_r1cs(&cs);
        assert!(!qap.verify(&cs.values));
        assert!(qap.compute_h(&cs.values).is_none());
    }

    #[test]
    fn qap_cubic_wrong_output_fails() {
        let mut cs = ConstraintSystem::new();
        let x_val = Fr::from_u64(3);
        let t1_val = x_val * x_val;
        let t2_val = t1_val * x_val;

        let x = cs.alloc_witness(x_val);
        let _y = cs.alloc_instance(Fr::from_u64(999)); // 잘못된 출력
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

        assert!(!cs.is_satisfied());

        let qap = QAP::from_r1cs(&cs);
        assert!(!qap.verify(&cs.values));
    }

    // ── QAP: 다항식 보간 검증 ────────────────────────────

    #[test]
    fn qap_polynomials_match_r1cs_at_domain() {
        // 3 제약 회로
        let circuit = CubicCircuit { x: Fr::from_u64(3) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        let qap = QAP::from_r1cs(&cs);
        let (a_mat, b_mat, c_mat) = cs.to_matrices();

        // 각 도메인 점 ωᵢ에서 aⱼ(ωᵢ) = A[i,j] 확인
        for (i, &omega) in qap.domain.iter().enumerate() {
            for j in 0..qap.num_variables {
                let expected = a_mat[i].iter()
                    .find(|&&(col, _)| col == j)
                    .map(|&(_, v)| v)
                    .unwrap_or(Fr::ZERO);
                let actual = qap.a_polys[j].eval(omega);
                assert_eq!(actual, expected,
                    "A poly mismatch at constraint {}, variable {}", i, j);
            }
            for j in 0..qap.num_variables {
                let expected = b_mat[i].iter()
                    .find(|&&(col, _)| col == j)
                    .map(|&(_, v)| v)
                    .unwrap_or(Fr::ZERO);
                let actual = qap.b_polys[j].eval(omega);
                assert_eq!(actual, expected,
                    "B poly mismatch at constraint {}, variable {}", i, j);
            }
            for j in 0..qap.num_variables {
                let expected = c_mat[i].iter()
                    .find(|&&(col, _)| col == j)
                    .map(|&(_, v)| v)
                    .unwrap_or(Fr::ZERO);
                let actual = qap.c_polys[j].eval(omega);
                assert_eq!(actual, expected,
                    "C poly mismatch at constraint {}, variable {}", i, j);
            }
        }
    }

    // ── QAP: h(x)·t(x) 항등식 ───────────────────────────

    #[test]
    fn qap_identity_holds_everywhere() {
        let circuit = CubicCircuit { x: Fr::from_u64(7) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        let qap = QAP::from_r1cs(&cs);
        let h = qap.compute_h(&cs.values).unwrap();
        let (a, b, c) = qap.compute_witness_polys(&cs.values);

        // 여러 랜덤 점에서 a(τ)·b(τ) - c(τ) = h(τ)·t(τ) 확인
        for tau_raw in [10u64, 42, 100, 999, 12345] {
            let tau = Fr::from_u64(tau_raw);
            let lhs = a.eval(tau) * b.eval(tau) - c.eval(tau);
            let rhs = h.eval(tau) * qap.t.eval(tau);
            assert_eq!(lhs, rhs, "identity failed at tau={}", tau_raw);
        }
    }

    // ── QAP: 피타고라스 회로 ─────────────────────────────

    #[test]
    fn qap_pythagorean() {
        // x² + y² = z²: 3 제약
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_witness(Fr::from_u64(4));
        let z = cs.alloc_witness(Fr::from_u64(5));
        let x_sq = cs.alloc_witness(Fr::from_u64(9));
        let y_sq = cs.alloc_witness(Fr::from_u64(16));

        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(x),
            LinearCombination::from(x_sq),
        );
        cs.enforce(
            LinearCombination::from(y),
            LinearCombination::from(y),
            LinearCombination::from(y_sq),
        );
        cs.enforce(
            LinearCombination::from(z),
            LinearCombination::from(z),
            LinearCombination::from(x_sq).add(Fr::ONE, y_sq),
        );

        assert!(cs.is_satisfied());

        let qap = QAP::from_r1cs(&cs);
        assert!(qap.verify(&cs.values));

        // 항등식 검증
        let h = qap.compute_h(&cs.values).unwrap();
        let (a, b, c) = qap.compute_witness_polys(&cs.values);
        let tau = Fr::from_u64(42);
        assert_eq!(
            a.eval(tau) * b.eval(tau) - c.eval(tau),
            h.eval(tau) * qap.t.eval(tau),
        );
    }

    // ── QAP: 조건부 선택 회로 ────────────────────────────

    #[test]
    fn qap_conditional() {
        // if b then x else y (3 제약)
        let mut cs = ConstraintSystem::new();
        let b = cs.alloc_witness(Fr::ONE);
        let x = cs.alloc_witness(Fr::from_u64(42));
        let y = cs.alloc_witness(Fr::from_u64(99));
        let t_val = Fr::ONE * (Fr::from_u64(42) - Fr::from_u64(99));
        let t = cs.alloc_witness(t_val);
        let result_val = Fr::from_u64(99) + t_val;
        let result = cs.alloc_instance(result_val);

        // b · (1-b) = 0
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

        let qap = QAP::from_r1cs(&cs);
        assert!(qap.verify(&cs.values));
    }

    // ── QAP: 빈 회로 ────────────────────────────────────

    #[test]
    fn qap_empty_circuit() {
        let cs = ConstraintSystem::new();
        let qap = QAP::from_r1cs(&cs);

        assert_eq!(qap.domain.len(), 0);
        assert_eq!(qap.num_variables, 1); // One만
        assert!(qap.verify(&cs.values));
    }

    // ── QAP: degree 검증 ─────────────────────────────────

    #[test]
    fn qap_degree_bounds() {
        let circuit = CubicCircuit { x: Fr::from_u64(5) };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);

        let m = cs.num_constraints(); // 3
        let qap = QAP::from_r1cs(&cs);
        let (a, b, c) = qap.compute_witness_polys(&cs.values);
        let h = qap.compute_h(&cs.values).unwrap();

        // a, b, c: degree ≤ m-1
        assert!(a.degree() <= m - 1);
        assert!(b.degree() <= m - 1);
        assert!(c.degree() <= m - 1);

        // t: degree = m
        assert_eq!(qap.t.degree(), m);

        // h: degree ≤ m-2 (= 2(m-1) - m)
        assert!(h.degree() <= m - 2);
    }
}
