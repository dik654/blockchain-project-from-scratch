// Step 4-1: Fp6 — 3차 확장체
//
// 타워 구조: Fp → Fp2 → Fp6 → Fp12
//                       ^^^^
// Fp6 = Fp2[v] / (v³ - β)  여기서 β = 9 + u ∈ Fp2
//
// 원소: c₀ + c₁·v + c₂·v²  (c₀, c₁, c₂ ∈ Fp2)
//   v³ = β (non-residue)
//
// Fp2가 복소수(2차원)라면, Fp6는 "3차원 복소수"
// Fp2 위에 새로운 미지수 v를 도입하고, v³ = β로 차수를 제한
//
// 덧셈: 각 성분끼리 (Fp2와 동일한 패턴)

use super::fp2::Fp2;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fp6 {
    pub c0: Fp2, // 상수항
    pub c1: Fp2, // v의 계수
    pub c2: Fp2, // v²의 계수
}

impl Fp6 {
    pub const ZERO: Fp6 = Fp6 { c0: Fp2::ZERO, c1: Fp2::ZERO, c2: Fp2::ZERO };
    pub const ONE: Fp6 = Fp6 { c0: Fp2::ONE, c1: Fp2::ZERO, c2: Fp2::ZERO };

    pub fn new(c0: Fp2, c1: Fp2, c2: Fp2) -> Self {
        Fp6 { c0, c1, c2 }
    }

    pub fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero()
    }

    pub fn add(&self, rhs: &Fp6) -> Fp6 {
        Fp6 {
            c0: self.c0 + rhs.c0,
            c1: self.c1 + rhs.c1,
            c2: self.c2 + rhs.c2,
        }
    }

    pub fn sub(&self, rhs: &Fp6) -> Fp6 {
        Fp6 {
            c0: self.c0 - rhs.c0,
            c1: self.c1 - rhs.c1,
            c2: self.c2 - rhs.c2,
        }
    }

    pub fn neg(&self) -> Fp6 {
        Fp6 {
            c0: -self.c0,
            c1: -self.c1,
            c2: -self.c2,
        }
    }

    /// x · v — Fp12 확장의 non-residue 곱셈
    ///
    /// Fp12 = Fp6[w] / (w² - v) 에서 w² = v이므로,
    /// Fp12 곱셈에서 w² 항을 줄일 때 이 함수가 필요하다
    ///
    /// v · (c₀ + c₁v + c₂v²) = c₂β + c₀v + c₁v²
    /// (v³ = β이므로 c₂v³ = c₂β)
    pub fn mul_by_nonresidue(&self) -> Fp6 {
        Fp6 {
            c0: self.c2.mul_by_nonresidue(), // c₂ · β
            c1: self.c0,                      // c₀
            c2: self.c1,                      // c₁
        }
    }
}

// Step 4-2: Fp6 곱셈 + inv
//
// 곱셈에서 v³ = β가 작용한다:
//   (a₀+a₁v+a₂v²)(b₀+b₁v+b₂v²) 를 전개하면 v³ 이상의 항이 나오고,
//   v³ = β로 대체하여 차수를 낮춘다
//
// Karatsuba로 Fp2 곱셈 9회 → 6회:
//   v₀ = a₀b₀, v₁ = a₁b₁, v₂ = a₂b₂
//   c₀ = v₀ + β·((a₁+a₂)(b₁+b₂) - v₁ - v₂)
//   c₁ = (a₀+a₁)(b₀+b₁) - v₀ - v₁ + β·v₂
//   c₂ = (a₀+a₂)(b₀+b₂) - v₀ + v₁ - v₂
//
// inv: Fp2로 norm을 내려서 Fp2의 inv를 사용

impl Fp6 {
    /// Fp6 곱셈 — Karatsuba: Fp2 곱셈 6회
    pub fn mul(&self, rhs: &Fp6) -> Fp6 {
        let v0 = self.c0 * rhs.c0;
        let v1 = self.c1 * rhs.c1;
        let v2 = self.c2 * rhs.c2;

        // c₀ = v₀ + β·(a₁b₂ + a₂b₁)
        let c0 = v0 + ((self.c1 + self.c2) * (rhs.c1 + rhs.c2) - v1 - v2)
            .mul_by_nonresidue();

        // c₁ = a₀b₁ + a₁b₀ + β·v₂
        let c1 = (self.c0 + self.c1) * (rhs.c0 + rhs.c1) - v0 - v1
            + v2.mul_by_nonresidue();

        // c₂ = a₀b₂ + a₁b₁ + a₂b₀
        let c2 = (self.c0 + self.c2) * (rhs.c0 + rhs.c2) - v0 + v1 - v2;

        Fp6 { c0, c1, c2 }
    }

    pub fn square(&self) -> Fp6 {
        self.mul(self)
    }

    /// Fp6의 역원: norm을 Fp2로 내려서 계산
    ///
    /// t₀ = a₀² - β·a₁a₂
    /// t₁ = β·a₂² - a₀a₁
    /// t₂ = a₁² - a₀a₂
    /// norm = a₀t₀ + β·(a₂t₁ + a₁t₂)  ∈ Fp2
    /// a⁻¹ = (t₀ + t₁v + t₂v²) · norm⁻¹
    pub fn inv(&self) -> Option<Fp6> {
        let c0s = self.c0.square();
        let c1s = self.c1.square();
        let c2s = self.c2.square();
        let c01 = self.c0 * self.c1;
        let c02 = self.c0 * self.c2;
        let c12 = self.c1 * self.c2;

        let t0 = c0s - c12.mul_by_nonresidue();
        let t1 = c2s.mul_by_nonresidue() - c01;
        let t2 = c1s - c02;

        // norm ∈ Fp2 — 차원이 Fp6 → Fp2로 내려간다
        let norm = self.c0 * t0
            + (self.c2 * t1 + self.c1 * t2).mul_by_nonresidue();
        let norm_inv = norm.inv()?;

        Some(Fp6 {
            c0: t0 * norm_inv,
            c1: t1 * norm_inv,
            c2: t2 * norm_inv,
        })
    }
}

impl std::ops::Mul for Fp6 {
    type Output = Fp6;
    fn mul(self, rhs: Fp6) -> Fp6 { Fp6::mul(&self, &rhs) }
}

impl std::ops::Add for Fp6 {
    type Output = Fp6;
    fn add(self, rhs: Fp6) -> Fp6 { Fp6::add(&self, &rhs) }
}

impl std::ops::Sub for Fp6 {
    type Output = Fp6;
    fn sub(self, rhs: Fp6) -> Fp6 { Fp6::sub(&self, &rhs) }
}

impl std::ops::Neg for Fp6 {
    type Output = Fp6;
    fn neg(self) -> Fp6 { Fp6::neg(&self) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::fp::Fp;

    fn fp2(a: u64, b: u64) -> Fp2 {
        Fp2::new(Fp::from_u64(a), Fp::from_u64(b))
    }

    fn fp6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> Fp6 {
        Fp6::new(fp2(a, b), fp2(c, d), fp2(e, f))
    }

    #[test]
    fn zero_is_zero() {
        assert!(Fp6::ZERO.is_zero());
    }

    #[test]
    fn one_is_not_zero() {
        assert!(!Fp6::ONE.is_zero());
    }

    #[test]
    fn add_components() {
        let a = fp6(1, 2, 3, 4, 5, 6);
        let b = fp6(10, 20, 30, 40, 50, 60);
        assert_eq!(a + b, fp6(11, 22, 33, 44, 55, 66));
    }

    #[test]
    fn sub_components() {
        let a = fp6(11, 22, 33, 44, 55, 66);
        let b = fp6(1, 2, 3, 4, 5, 6);
        assert_eq!(a - b, fp6(10, 20, 30, 40, 50, 60));
    }

    #[test]
    fn neg_and_add_is_zero() {
        let a = fp6(3, 5, 7, 11, 13, 17);
        assert_eq!(a + (-a), Fp6::ZERO);
    }

    #[test]
    fn additive_identity() {
        let a = fp6(3, 5, 7, 11, 13, 17);
        assert_eq!(a + Fp6::ZERO, a);
    }

    #[test]
    fn mul_by_nonresidue_basic() {
        // β = 9 + u
        // (3 + 5u) · (9 + u) = (27 - 5) + (3 + 45)u = 22 + 48u
        let x = fp2(3, 5);
        let result = x.mul_by_nonresidue();
        assert_eq!(result, fp2(22, 48));
    }

    // Step 4-2 테스트

    #[test]
    fn mul_identity() {
        let a = fp6(3, 5, 7, 11, 13, 17);
        assert_eq!(a * Fp6::ONE, a);
        assert_eq!(Fp6::ONE * a, a);
    }

    #[test]
    fn square_matches_mul() {
        let a = fp6(3, 5, 7, 11, 13, 17);
        assert_eq!(a.square(), a * a);
    }

    #[test]
    fn mul_commutativity() {
        let a = fp6(3, 5, 7, 11, 13, 17);
        let b = fp6(2, 4, 6, 8, 10, 12);
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn mul_associativity() {
        let a = fp6(1, 2, 3, 4, 5, 6);
        let b = fp6(7, 8, 9, 10, 11, 12);
        let c = fp6(13, 14, 15, 16, 17, 18);
        assert_eq!((a * b) * c, a * (b * c));
    }

    #[test]
    fn mul_distributivity() {
        let a = fp6(1, 2, 3, 4, 5, 6);
        let b = fp6(7, 8, 9, 10, 11, 12);
        let c = fp6(13, 14, 15, 16, 17, 18);
        assert_eq!(a * (b + c), a * b + a * c);
    }

    #[test]
    fn inv_basic() {
        let a = fp6(3, 5, 7, 11, 13, 17);
        let a_inv = a.inv().unwrap();
        assert_eq!(a * a_inv, Fp6::ONE);
    }

    #[test]
    fn inv_of_zero_is_none() {
        assert!(Fp6::ZERO.inv().is_none());
    }

    #[test]
    fn inv_of_one_is_one() {
        assert_eq!(Fp6::ONE.inv().unwrap(), Fp6::ONE);
    }
}
