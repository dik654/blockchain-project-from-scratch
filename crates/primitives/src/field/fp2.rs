// Step 3-3: Fp2 — 이차 확장체
//
// 왜 필요한가?
//   BN254의 G2 점은 Fp 하나로는 좌표를 표현할 수 없다
//   Fp를 "복소수처럼" 확장한 Fp2가 G2의 좌표 체
//
// 구조: a₀ + a₁·u  (a₀, a₁ ∈ Fp)
//   u² = -1  (BN254의 경우)
//
// 복소수와의 대응:
//   실수 ↔ Fp
//   허수단위 i ↔ u
//   복소수 a + bi ↔ Fp2 원소 a₀ + a₁·u
//
// 덧셈: 각 성분끼리 더함 (복소수와 동일)
//   (a₀+a₁u) + (b₀+b₁u) = (a₀+b₀) + (a₁+b₁)u

use super::fp::Fp;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fp2 {
    pub c0: Fp, // 실수부
    pub c1: Fp, // 허수부 (u의 계수)
}

impl Fp2 {
    /// 0 = 0 + 0·u
    pub const ZERO: Fp2 = Fp2 { c0: Fp::ZERO, c1: Fp::ZERO };

    /// 1 = 1 + 0·u
    pub const ONE: Fp2 = Fp2 { c0: Fp::ONE, c1: Fp::ZERO };

    pub fn new(c0: Fp, c1: Fp) -> Self {
        Fp2 { c0, c1 }
    }

    pub fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    /// (a₀+a₁u) + (b₀+b₁u) = (a₀+b₀) + (a₁+b₁)u
    pub fn add(&self, rhs: &Fp2) -> Fp2 {
        Fp2 {
            c0: self.c0 + rhs.c0,
            c1: self.c1 + rhs.c1,
        }
    }

    /// (a₀+a₁u) - (b₀+b₁u) = (a₀-b₀) + (a₁-b₁)u
    pub fn sub(&self, rhs: &Fp2) -> Fp2 {
        Fp2 {
            c0: self.c0 - rhs.c0,
            c1: self.c1 - rhs.c1,
        }
    }

    /// -(a₀+a₁u) = (-a₀) + (-a₁)u
    pub fn neg(&self) -> Fp2 {
        Fp2 {
            c0: -self.c0,
            c1: -self.c1,
        }
    }
}

// Step 3-4: Fp2 곱셈, conjugate, norm, inv, frobenius
//
// 곱셈에서 u² = -1이 처음으로 작용한다:
//   (a₀+a₁u)(b₀+b₁u) = a₀b₀ + a₁b₁·u² + (a₀b₁+a₁b₀)u
//                      = (a₀b₀ - a₁b₁) + (a₀b₁ + a₁b₀)u
//
// Karatsuba 트릭으로 곱셈 4회 → 3회로 줄임:
//   v₀ = a₀·b₀, v₁ = a₁·b₁
//   c₀ = v₀ - v₁
//   c₁ = (a₀+a₁)(b₀+b₁) - v₀ - v₁
//
// conjugate(켤레): a₀ + a₁u → a₀ - a₁u  (복소수의 켤레와 동일)
// norm(노름): a · conj(a) = a₀² + a₁²    (결과가 Fp — 차원이 내려감!)
// inv(역원): a⁻¹ = conj(a) · norm(a)⁻¹
// frobenius: x^p 사상. BN254에서 frobenius = conjugate

impl Fp2 {
    /// (a₀+a₁u)(b₀+b₁u) — Karatsuba: Fp 곱셈 3회
    pub fn mul(&self, rhs: &Fp2) -> Fp2 {
        let v0 = self.c0 * rhs.c0; // a₀·b₀
        let v1 = self.c1 * rhs.c1; // a₁·b₁

        // c₁ = (a₀+a₁)(b₀+b₁) - v₀ - v₁ = a₀b₁ + a₁b₀
        let c1 = (self.c0 + self.c1) * (rhs.c0 + rhs.c1) - v0 - v1;
        // c₀ = v₀ - v₁ = a₀b₀ - a₁b₁  (u² = -1이므로)
        let c0 = v0 - v1;

        Fp2 { c0, c1 }
    }

    /// (a₀+a₁u)² = (a₀²-a₁²) + 2a₀a₁u
    pub fn square(&self) -> Fp2 {
        // (a₀+a₁)(a₀-a₁) = a₀²-a₁² — Fp 곱셈 1회로 c₀ 계산
        let c0 = (self.c0 + self.c1) * (self.c0 - self.c1);
        let c1 = self.c0 * self.c1 + self.c0 * self.c1; // 2·a₀·a₁

        Fp2 { c0, c1 }
    }

    /// 켤레: a₀ + a₁u → a₀ - a₁u
    pub fn conjugate(&self) -> Fp2 {
        Fp2 {
            c0: self.c0,
            c1: -self.c1,
        }
    }

    /// 노름: a · conj(a) = a₀² + a₁² ∈ Fp
    /// 결과가 Fp2가 아니라 Fp — 차원이 하나 내려간다
    pub fn norm(&self) -> Fp {
        self.c0 * self.c0 + self.c1 * self.c1
    }

    /// a⁻¹ = conj(a) / norm(a)
    /// norm은 Fp 원소이므로 Fp의 inv를 사용
    pub fn inv(&self) -> Option<Fp2> {
        let n = self.norm();
        let n_inv = n.inv()?; // Fp의 역원
        let conj = self.conjugate();
        Some(Fp2 {
            c0: conj.c0 * n_inv,
            c1: conj.c1 * n_inv,
        })
    }

    /// Frobenius 사상: x → x^p
    /// BN254에서 u^p = -u이므로, frobenius = conjugate
    pub fn frobenius_map(&self) -> Fp2 {
        self.conjugate()
    }

    /// x · β 여기서 β = 9 + u (Fp6 확장의 non-residue)
    ///
    /// Fp6 = Fp2[v] / (v³ - β) 에서 v³ = β이므로,
    /// v³ 이상의 항을 줄일 때 이 함수가 필요하다
    ///
    /// (a + bu)(9 + u) = (9a - b) + (a + 9b)u
    pub fn mul_by_nonresidue(&self) -> Fp2 {
        let nine = Fp::from_u64(9);
        Fp2 {
            c0: nine * self.c0 - self.c1,
            c1: self.c0 + nine * self.c1,
        }
    }
}

impl std::ops::Mul for Fp2 {
    type Output = Fp2;
    fn mul(self, rhs: Fp2) -> Fp2 { Fp2::mul(&self, &rhs) }
}

impl std::fmt::Display for Fp2 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Fp2({} + {}·u)", self.c0, self.c1)
    }
}

impl std::ops::Add for Fp2 {
    type Output = Fp2;
    fn add(self, rhs: Fp2) -> Fp2 { Fp2::add(&self, &rhs) }
}

impl std::ops::Sub for Fp2 {
    type Output = Fp2;
    fn sub(self, rhs: Fp2) -> Fp2 { Fp2::sub(&self, &rhs) }
}

impl std::ops::Neg for Fp2 {
    type Output = Fp2;
    fn neg(self) -> Fp2 { Fp2::neg(&self) }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fp2(a: u64, b: u64) -> Fp2 {
        Fp2::new(Fp::from_u64(a), Fp::from_u64(b))
    }

    #[test]
    fn zero_is_zero() {
        assert!(Fp2::ZERO.is_zero());
    }

    #[test]
    fn one_is_not_zero() {
        assert!(!Fp2::ONE.is_zero());
    }

    #[test]
    fn add_components() {
        // (3 + 5u) + (7 + 2u) = (10 + 7u)
        let a = fp2(3, 5);
        let b = fp2(7, 2);
        assert_eq!(a + b, fp2(10, 7));
    }

    #[test]
    fn sub_components() {
        // (10 + 7u) - (3 + 5u) = (7 + 2u)
        let a = fp2(10, 7);
        let b = fp2(3, 5);
        assert_eq!(a - b, fp2(7, 2));
    }

    #[test]
    fn neg_and_add_is_zero() {
        let a = fp2(42, 17);
        assert_eq!(a + (-a), Fp2::ZERO);
    }

    #[test]
    fn additive_identity() {
        let a = fp2(13, 29);
        assert_eq!(a + Fp2::ZERO, a);
    }

    // Step 3-4 테스트

    #[test]
    fn mul_basic() {
        // (3 + 5u)(7 + 2u) = 21 + 6u + 35u + 10u²
        //                   = 21 + 41u + 10·(-1) = 11 + 41u
        let a = fp2(3, 5);
        let b = fp2(7, 2);
        assert_eq!(a * b, fp2(11, 41));
    }

    #[test]
    fn mul_pure_imaginary() {
        // (0 + 3u)(0 + 4u) = 12·u² = -12
        let a = fp2(0, 3);
        let b = fp2(0, 4);
        let result = a * b;
        assert_eq!(result.c1, Fp::ZERO); // 허수부 0
        assert_eq!(result, Fp2::new(-Fp::from_u64(12), Fp::ZERO));
    }

    #[test]
    fn square_matches_mul() {
        let a = fp2(5, 7);
        assert_eq!(a.square(), a * a);
    }

    #[test]
    fn conjugate_basic() {
        // conj(3 + 5u) = 3 - 5u
        let a = fp2(3, 5);
        let conj = a.conjugate();
        assert_eq!(conj.c0, Fp::from_u64(3));
        assert_eq!(conj.c1, -Fp::from_u64(5));
    }

    #[test]
    fn norm_basic() {
        // norm(3 + 4u) = 9 + 16 = 25
        let a = fp2(3, 4);
        assert_eq!(a.norm(), Fp::from_u64(25));
    }

    #[test]
    fn a_times_conjugate_is_norm() {
        let a = fp2(3, 4);
        let product = a * a.conjugate();
        // a·conj(a) = norm(a) ∈ Fp (허수부 = 0)
        assert_eq!(product.c1, Fp::ZERO);
        assert_eq!(product.c0, Fp::from_u64(25));
    }

    #[test]
    fn inv_basic() {
        let a = fp2(3, 4);
        let a_inv = a.inv().unwrap();
        assert_eq!(a * a_inv, Fp2::ONE);
    }

    #[test]
    fn inv_of_zero_is_none() {
        assert!(Fp2::ZERO.inv().is_none());
    }

    #[test]
    fn frobenius_is_conjugate() {
        let a = fp2(13, 29);
        assert_eq!(a.frobenius_map(), a.conjugate());
    }

    #[test]
    fn frobenius_twice_is_identity() {
        // x^{p^2} = x (Fp2의 원소에 frobenius를 2번 적용하면 원래 값)
        let a = fp2(7, 11);
        assert_eq!(a.frobenius_map().frobenius_map(), a);
    }

    #[test]
    fn field_axioms() {
        let a = fp2(3, 5);
        let b = fp2(7, 2);
        let c = fp2(11, 13);
        // 교환법칙
        assert_eq!(a * b, b * a);
        // 결합법칙
        assert_eq!((a * b) * c, a * (b * c));
        // 분배법칙
        assert_eq!(a * (b + c), a * b + a * c);
        // 항등원
        assert_eq!(a * Fp2::ONE, a);
    }
}
