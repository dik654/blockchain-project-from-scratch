// Step 4-3: Fp12 — 타워의 최상층
//
// 타워 구조: Fp → Fp2 → Fp6 → Fp12
//                              ^^^^
// Fp12 = Fp6[w] / (w² - v)  여기서 v ∈ Fp6
//
// 원소: c₀ + c₁·w  (c₀, c₁ ∈ Fp6)
//   w² = v (Fp6의 변수)
//
// 페어링 e(G1, G2)의 결과가 바로 이 Fp12의 원소
// BN254의 embedding degree k=12 → GT ⊂ Fp12*

use super::fp6::Fp6;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fp12 {
    pub c0: Fp6, // 상수항
    pub c1: Fp6, // w의 계수
}

impl Fp12 {
    pub const ZERO: Fp12 = Fp12 { c0: Fp6::ZERO, c1: Fp6::ZERO };
    pub const ONE: Fp12 = Fp12 { c0: Fp6::ONE, c1: Fp6::ZERO };

    pub fn new(c0: Fp6, c1: Fp6) -> Self {
        Fp12 { c0, c1 }
    }

    pub fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    pub fn add(&self, rhs: &Fp12) -> Fp12 {
        Fp12 {
            c0: self.c0 + rhs.c0,
            c1: self.c1 + rhs.c1,
        }
    }

    pub fn sub(&self, rhs: &Fp12) -> Fp12 {
        Fp12 {
            c0: self.c0 - rhs.c0,
            c1: self.c1 - rhs.c1,
        }
    }

    pub fn neg(&self) -> Fp12 {
        Fp12 {
            c0: -self.c0,
            c1: -self.c1,
        }
    }

    /// Fp12 곱셈 — Karatsuba: Fp6 곱셈 3회
    ///
    /// (a₀ + a₁w)(b₀ + b₁w) = a₀b₀ + a₁b₁·w² + (a₀b₁ + a₁b₀)w
    ///                        = a₀b₀ + a₁b₁·v + (a₀b₁ + a₁b₀)w
    ///
    /// Karatsuba:
    ///   v₀ = a₀b₀, v₁ = a₁b₁
    ///   c₀ = v₀ + v₁·v        (v = Fp6의 non-residue)
    ///   c₁ = (a₀+a₁)(b₀+b₁) - v₀ - v₁
    pub fn mul(&self, rhs: &Fp12) -> Fp12 {
        let v0 = self.c0 * rhs.c0; // Fp6 곱셈 ①
        let v1 = self.c1 * rhs.c1; // Fp6 곱셈 ②

        // c₁ = (a₀+a₁)(b₀+b₁) - v₀ - v₁
        let c1 = (self.c0 + self.c1) * (rhs.c0 + rhs.c1) - v0 - v1; // ③

        // c₀ = v₀ + v₁·v  (w² = v이므로)
        let c0 = v0 + v1.mul_by_nonresidue();

        Fp12 { c0, c1 }
    }

    pub fn square(&self) -> Fp12 {
        self.mul(self)
    }

    /// Fp12의 켤레: c₀ + c₁w → c₀ - c₁w
    ///
    /// Fp12 = Fp6[w]/(w²-v)에서 w → -w 사상
    /// 페어링 final exponentiation의 "easy part"에서 사용
    pub fn conjugate(&self) -> Fp12 {
        Fp12 {
            c0: self.c0,
            c1: -self.c1,
        }
    }

    /// Fp12 거듭제곱: a^exp (square-and-multiply)
    /// final exponentiation에서 사용
    pub fn pow(&self, exp: &[u64]) -> Fp12 {
        let mut result = Fp12::ONE;
        let mut base = *self;
        for &limb in exp.iter() {
            for j in 0..64 {
                if (limb >> j) & 1 == 1 {
                    result = result * base;
                }
                base = base.square();
            }
        }
        result
    }

    /// Fp12의 역원: conj(a) / norm(a)
    ///
    /// norm = c₀² - v·c₁²  ∈ Fp6
    /// a⁻¹ = conj(a) · norm⁻¹
    pub fn inv(&self) -> Option<Fp12> {
        let c0s = self.c0.square();
        let c1s = self.c1.square();

        // norm = c₀² - v·c₁² ∈ Fp6  (차원이 Fp12 → Fp6로 내려감)
        let norm = c0s - c1s.mul_by_nonresidue();
        let norm_inv = norm.inv()?;

        Some(Fp12 {
            c0: self.c0.mul(&norm_inv),
            c1: self.c1.neg().mul(&norm_inv),
        })
    }
}

impl std::ops::Mul for Fp12 {
    type Output = Fp12;
    fn mul(self, rhs: Fp12) -> Fp12 { Fp12::mul(&self, &rhs) }
}

impl std::ops::Add for Fp12 {
    type Output = Fp12;
    fn add(self, rhs: Fp12) -> Fp12 { Fp12::add(&self, &rhs) }
}

impl std::ops::Sub for Fp12 {
    type Output = Fp12;
    fn sub(self, rhs: Fp12) -> Fp12 { Fp12::sub(&self, &rhs) }
}

impl std::ops::Neg for Fp12 {
    type Output = Fp12;
    fn neg(self) -> Fp12 { Fp12::neg(&self) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::fp::Fp;
    use crate::field::fp2::Fp2;

    fn fp2(a: u64, b: u64) -> Fp2 {
        Fp2::new(Fp::from_u64(a), Fp::from_u64(b))
    }

    fn fp6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> Fp6 {
        Fp6::new(fp2(a, b), fp2(c, d), fp2(e, f))
    }

    fn fp12(vals: [u64; 12]) -> Fp12 {
        Fp12::new(
            fp6(vals[0], vals[1], vals[2], vals[3], vals[4], vals[5]),
            fp6(vals[6], vals[7], vals[8], vals[9], vals[10], vals[11]),
        )
    }

    #[test]
    fn zero_is_zero() {
        assert!(Fp12::ZERO.is_zero());
    }

    #[test]
    fn one_is_not_zero() {
        assert!(!Fp12::ONE.is_zero());
    }

    #[test]
    fn add_sub() {
        let a = fp12([1,2,3,4,5,6,7,8,9,10,11,12]);
        let b = fp12([10,20,30,40,50,60,70,80,90,100,110,120]);
        let sum = a + b;
        assert_eq!(sum - b, a);
        assert_eq!(sum - a, b);
    }

    #[test]
    fn neg_and_add_is_zero() {
        let a = fp12([3,5,7,11,13,17,19,23,29,31,37,41]);
        assert_eq!(a + (-a), Fp12::ZERO);
    }

    #[test]
    fn mul_identity() {
        let a = fp12([3,5,7,11,13,17,19,23,29,31,37,41]);
        assert_eq!(a * Fp12::ONE, a);
        assert_eq!(Fp12::ONE * a, a);
    }

    #[test]
    fn square_matches_mul() {
        let a = fp12([3,5,7,11,13,17,19,23,29,31,37,41]);
        assert_eq!(a.square(), a * a);
    }

    #[test]
    fn mul_commutativity() {
        let a = fp12([3,5,7,11,13,17,19,23,29,31,37,41]);
        let b = fp12([2,4,6,8,10,12,14,16,18,20,22,24]);
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn mul_associativity() {
        let a = fp12([1,2,3,4,5,6,7,8,9,10,11,12]);
        let b = fp12([13,14,15,16,17,18,19,20,21,22,23,24]);
        let c = fp12([25,26,27,28,29,30,31,32,33,34,35,36]);
        assert_eq!((a * b) * c, a * (b * c));
    }

    #[test]
    fn mul_distributivity() {
        let a = fp12([1,2,3,4,5,6,7,8,9,10,11,12]);
        let b = fp12([13,14,15,16,17,18,19,20,21,22,23,24]);
        let c = fp12([25,26,27,28,29,30,31,32,33,34,35,36]);
        assert_eq!(a * (b + c), a * b + a * c);
    }

    #[test]
    fn conjugate_basic() {
        let a = fp12([3,5,7,11,13,17,19,23,29,31,37,41]);
        let conj = a.conjugate();
        assert_eq!(conj.c0, a.c0);
        assert_eq!(conj.c1, -a.c1);
    }

    #[test]
    fn inv_basic() {
        let a = fp12([3,5,7,11,13,17,19,23,29,31,37,41]);
        let a_inv = a.inv().unwrap();
        assert_eq!(a * a_inv, Fp12::ONE);
    }

    #[test]
    fn inv_of_zero_is_none() {
        assert!(Fp12::ZERO.inv().is_none());
    }

    #[test]
    fn inv_of_one_is_one() {
        assert_eq!(Fp12::ONE.inv().unwrap(), Fp12::ONE);
    }
}
