use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

use super::{adc, sbb, mac};

// Step 2-1: 254-bit 소수를 u64 4개로 표현하기
//
// 왜 [u64; 4]인가?
// BN254의 소수 p는 254-bit → u64 하나는 64-bit → 최소 4개 필요 (4 × 64 = 256 ≥ 254)
// little-endian: limbs[0]이 최하위, limbs[3]이 최상위

/// BN254 base field modulus p
/// p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
const MODULUS: [u64; 4] = [
    0x3c208c16d87cfd47, // 최하위 64-bit
    0x97816a916871ca8d,
    0xb85045b68181585d,
    0x30644e72e131a029, // 최상위 64-bit
];

/// BN254 base field element — 내부는 Montgomery form
/// 저장값: a_mont = a * R mod p
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fp(pub(crate) [u64; 4]);

impl Fp {
    pub const ZERO: Fp = Fp([0, 0, 0, 0]);

    /// 1의 Montgomery form = R mod p
    pub const ONE: Fp = Fp(R);

    pub fn is_zero(&self) -> bool {
        self.0 == [0, 0, 0, 0]
    }
}

// Step 2-4: Montgomery 곱셈
//
// 문제: (a * b) mod p를 하려면 나눗셈이 필요하다 → 느리다
// 해결: 수를 "Montgomery form"으로 저장하면 나눗셈 없이 곱셈 가능
//
// Montgomery form: a를 저장할 때 a 대신 (a * R mod p)를 저장
//   R = 2^256 (limb 수 × 64)
//
// 곱셈: a_mont * b_mont를 곱하면 a*b*R^2가 되는데,
//   REDC로 R을 하나 제거하면 a*b*R = (a*b)_mont ← 우리가 원하는 것!
//
// REDC의 핵심: R = 2^256이므로 "R로 나누기" = "256-bit 오른쪽 시프트"
//   단, mod p를 유지하기 위해 INV 상수를 이용

/// R = 2^256 mod p
/// Montgomery form에서 1의 표현: 1_mont = 1 * R mod p = R
const R: [u64; 4] = [
    0xd35d438dc58f0d9d,
    0x0a78eb28f5c70b3d,
    0x666ea36f7879462c,
    0x0e0a77c19a07df2f,
];

/// R^2 mod p — normal → Montgomery 변환에 사용
/// from_raw(a) = mont_mul(a, R^2) = a * R^2 * R^{-1} = a * R = a_mont
const R2: [u64; 4] = [
    0xf32cfc5b538afa89,
    0xb5e71911d44501fb,
    0x47ab1eff0a417ff6,
    0x06d89f71cab8351f,
];

/// INV = -p^{-1} mod 2^64 — REDC에서 "하위 limb을 0으로 만드는" 마법 상수
/// Newton's method로 컴파일 타임에 계산
const INV: u64 = {
    let p0 = MODULUS[0];
    let mut inv = 1u64;
    // 각 반복마다 정밀도 2배: 1→2→4→8→16→32→64 bit
    inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
    inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
    inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
    inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
    inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
    inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
    inv.wrapping_neg()
};

impl Fp {
    /// normal → Montgomery: a → a * R mod p
    pub fn from_raw(v: [u64; 4]) -> Self {
        // mont_mul(a, R^2) = a * R^2 * R^{-1} = a * R
        Fp(v).mont_mul(&Fp(R2))
    }

    /// u64 → Fp
    pub fn from_u64(v: u64) -> Self {
        Fp::from_raw([v, 0, 0, 0])
    }

    /// Montgomery → normal: a_mont → a_mont * R^{-1} mod p
    pub fn to_repr(&self) -> [u64; 4] {
        // REDC(a_mont) = a_mont * R^{-1} = a
        let mut t = [0u64; 8];
        t[0] = self.0[0];
        t[1] = self.0[1];
        t[2] = self.0[2];
        t[3] = self.0[3];
        Self::mont_reduce_inner(&t)
    }

    /// Montgomery 곱셈: a_mont * b_mont * R^{-1} mod p
    pub fn mont_mul(&self, rhs: &Fp) -> Fp {
        // 1단계: schoolbook 4×4 곱셈 → 8-limb 결과
        let mut t = [0u64; 8];

        // self[0] × rhs 전체
        let (t0, carry) = mac(0, self.0[0], rhs.0[0], 0);
        let (t1, carry) = mac(0, self.0[0], rhs.0[1], carry);
        let (t2, carry) = mac(0, self.0[0], rhs.0[2], carry);
        let (t3, t4) = mac(0, self.0[0], rhs.0[3], carry);
        t[0] = t0;

        // self[1] × rhs, 기존 값에 누적
        let (t1, carry) = mac(t1, self.0[1], rhs.0[0], 0);
        let (t2, carry) = mac(t2, self.0[1], rhs.0[1], carry);
        let (t3, carry) = mac(t3, self.0[1], rhs.0[2], carry);
        let (t4, t5) = mac(t4, self.0[1], rhs.0[3], carry);
        t[1] = t1;

        // self[2] × rhs
        let (t2, carry) = mac(t2, self.0[2], rhs.0[0], 0);
        let (t3, carry) = mac(t3, self.0[2], rhs.0[1], carry);
        let (t4, carry) = mac(t4, self.0[2], rhs.0[2], carry);
        let (t5, t6) = mac(t5, self.0[2], rhs.0[3], carry);
        t[2] = t2;

        // self[3] × rhs
        let (t3, carry) = mac(t3, self.0[3], rhs.0[0], 0);
        let (t4, carry) = mac(t4, self.0[3], rhs.0[1], carry);
        let (t5, carry) = mac(t5, self.0[3], rhs.0[2], carry);
        let (t6, t7) = mac(t6, self.0[3], rhs.0[3], carry);
        t[3] = t3;
        t[4] = t4;
        t[5] = t5;
        t[6] = t6;
        t[7] = t7;

        // 2단계: Montgomery reduction (REDC)
        Fp(Self::mont_reduce_inner(&t))
    }

    /// REDC: 8-limb → 4-limb
    /// 각 반복에서 하위 limb을 0으로 만들고, 결과를 오른쪽으로 밀어낸다
    fn mont_reduce_inner(t: &[u64; 8]) -> [u64; 4] {
        let mut r = *t;

        for i in 0..4 {
            // m을 잘 골라서 (r[i] + m * p)의 하위 64-bit가 0이 되게 한다
            // m = r[i] * INV mod 2^64
            let m = r[i].wrapping_mul(INV);

            // r += m * p (하위 limb은 0이 되어 사라짐)
            let (_, carry) = mac(r[i], m, MODULUS[0], 0);
            let (res, carry) = mac(r[i + 1], m, MODULUS[1], carry);
            r[i + 1] = res;
            let (res, carry) = mac(r[i + 2], m, MODULUS[2], carry);
            r[i + 2] = res;
            let (res, carry) = mac(r[i + 3], m, MODULUS[3], carry);
            r[i + 3] = res;

            // carry를 상위 limb으로 전파
            if i + 4 < 8 {
                let (res, c2) = r[i + 4].overflowing_add(carry);
                r[i + 4] = res;
                if c2 && i + 5 < 8 {
                    let (res, c3) = r[i + 5].overflowing_add(1);
                    r[i + 5] = res;
                    if c3 && i + 6 < 8 {
                        r[i + 6] = r[i + 6].wrapping_add(1);
                    }
                }
            }
        }

        // 4번 반복 후 하위 4 limb은 모두 0 → 상위 4 limb이 결과
        sub_if_gte([r[4], r[5], r[6], r[7]]).0
    }
}

// Step 2-5: square, pow, inv
//
// mont_mul 하나로 세 가지를 만든다:
//   square: a * a (자기 자신과 곱셈)
//   pow: square-and-multiply로 거듭제곱
//   inv: Fermat의 소정리 — a^{p-2} mod p = a^{-1}

impl Fp {
    /// a^2 = mont_mul(a, a)
    pub fn square(&self) -> Fp {
        self.mont_mul(self)
    }

    /// a^exp — 오른쪽에서 왼쪽으로 비트를 보며 square-and-multiply
    pub fn pow(&self, exp: &[u64; 4]) -> Fp {
        let mut result = Fp::ONE;
        let mut base = *self;

        for &limb in exp.iter() {
            for j in 0..64 {
                if (limb >> j) & 1 == 1 {
                    result = result.mont_mul(&base);
                }
                base = base.square();
            }
        }
        result
    }

    /// a^{-1} mod p = a^{p-2} mod p (Fermat's little theorem)
    /// p가 소수이므로 a^{p-1} ≡ 1, 양변을 a로 나누면 a^{p-2} ≡ a^{-1}
    pub fn inv(&self) -> Option<Fp> {
        if self.is_zero() {
            return None; // 0에는 역원이 없다
        }
        Some(self.pow(&[MODULUS[0] - 2, MODULUS[1], MODULUS[2], MODULUS[3]]))
    }
}

// Step 2-6: 연산자 오버로딩
//
// Rust의 trait으로 +, -, *, - 연산자를 Fp에 붙인다
// a.mont_mul(&b) 대신 a * b로 쓸 수 있게

impl Add for Fp {
    type Output = Fp;
    fn add(self, rhs: Fp) -> Fp { Fp::add(&self, &rhs) }
}

impl Add<&Fp> for Fp {
    type Output = Fp;
    fn add(self, rhs: &Fp) -> Fp { Fp::add(&self, rhs) }
}

impl Sub for Fp {
    type Output = Fp;
    fn sub(self, rhs: Fp) -> Fp { Fp::sub(&self, &rhs) }
}

impl Sub<&Fp> for Fp {
    type Output = Fp;
    fn sub(self, rhs: &Fp) -> Fp { Fp::sub(&self, rhs) }
}

impl Mul for Fp {
    type Output = Fp;
    fn mul(self, rhs: Fp) -> Fp { self.mont_mul(&rhs) }
}

impl Mul<&Fp> for Fp {
    type Output = Fp;
    fn mul(self, rhs: &Fp) -> Fp { self.mont_mul(rhs) }
}

impl Neg for Fp {
    type Output = Fp;
    fn neg(self) -> Fp { Fp::neg(&self) }
}

impl fmt::Display for Fp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let r = self.to_repr();
        write!(f, "Fp(0x{:016x}{:016x}{:016x}{:016x})", r[3], r[2], r[1], r[0])
    }
}

// Step 2-3: 모듈러 덧셈/뺄셈
//
// 유한체에서는 모든 연산 결과가 [0, p) 범위 안에 있어야 한다
// 덧셈: 그냥 더하고, 결과 >= p이면 p를 뺀다
// 뺄셈: 그냥 빼고, underflow면 p를 더한다
// 부정: 0이면 0, 아니면 p - a

impl Fp {
    /// (a + b) mod p
    pub fn add(&self, rhs: &Fp) -> Fp {
        // 4개 limb을 순서대로 더하며 carry 전파
        let (d0, carry) = self.0[0].overflowing_add(rhs.0[0]);
        let (d1, carry) = adc(self.0[1], rhs.0[1], carry);
        let (d2, carry) = adc(self.0[2], rhs.0[2], carry);
        let (d3, _) = adc(self.0[3], rhs.0[3], carry);

        // 결과가 p 이상이면 p를 빼서 [0, p) 범위로
        sub_if_gte([d0, d1, d2, d3])
    }

    /// (a - b) mod p
    pub fn sub(&self, rhs: &Fp) -> Fp {
        let (d0, borrow) = self.0[0].overflowing_sub(rhs.0[0]);
        let (d1, borrow) = sbb(self.0[1], rhs.0[1], borrow);
        let (d2, borrow) = sbb(self.0[2], rhs.0[2], borrow);
        let (d3, borrow) = sbb(self.0[3], rhs.0[3], borrow);

        if borrow {
            // a < b → 결과가 음수 → p를 더하면 동일한 값 (mod p)
            let (d0, carry) = d0.overflowing_add(MODULUS[0]);
            let (d1, carry) = adc(d1, MODULUS[1], carry);
            let (d2, carry) = adc(d2, MODULUS[2], carry);
            let (d3, _) = adc(d3, MODULUS[3], carry);
            Fp([d0, d1, d2, d3])
        } else {
            Fp([d0, d1, d2, d3])
        }
    }

    /// -a mod p
    pub fn neg(&self) -> Fp {
        if self.is_zero() {
            *self
        } else {
            // p - a
            let (d0, borrow) = MODULUS[0].overflowing_sub(self.0[0]);
            let (d1, borrow) = sbb(MODULUS[1], self.0[1], borrow);
            let (d2, borrow) = sbb(MODULUS[2], self.0[2], borrow);
            let (d3, _) = sbb(MODULUS[3], self.0[3], borrow);
            Fp([d0, d1, d2, d3])
        }
    }
}

/// 결과 >= p이면 p를 빼서 정규화
fn sub_if_gte(v: [u64; 4]) -> Fp {
    // 일단 p를 빼본다
    let (d0, borrow) = v[0].overflowing_sub(MODULUS[0]);
    let (d1, borrow) = sbb(v[1], MODULUS[1], borrow);
    let (d2, borrow) = sbb(v[2], MODULUS[2], borrow);
    let (d3, borrow) = sbb(v[3], MODULUS[3], borrow);

    if borrow {
        Fp(v) // v < p → 원래 값 유지
    } else {
        Fp([d0, d1, d2, d3]) // v >= p → 뺀 값 사용
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn modulus_is_254_bits() {
        let top = MODULUS[3];
        let bit_len = 64 - top.leading_zeros();
        let total_bits = 192 + bit_len;
        assert_eq!(total_bits, 254);
    }

    #[test]
    fn zero_is_zero() {
        assert!(Fp::ZERO.is_zero());
    }

    #[test]
    fn nonzero_is_not_zero() {
        assert!(!Fp([1, 0, 0, 0]).is_zero());
    }

    // Step 2-2 테스트

    #[test]
    fn adc_no_overflow() {
        let (sum, carry) = adc(3, 5, false);
        assert_eq!(sum, 8);
        assert!(!carry);
    }

    #[test]
    fn adc_overflow() {
        // u64::MAX + 1 → 넘침, carry 발생
        let (sum, carry) = adc(u64::MAX, 1, false);
        assert_eq!(sum, 0);
        assert!(carry);
    }

    #[test]
    fn sbb_no_underflow() {
        let (diff, borrow) = sbb(10, 3, false);
        assert_eq!(diff, 7);
        assert!(!borrow);
    }

    #[test]
    fn sbb_underflow() {
        // 0 - 1 → 빌림 발생, 결과는 u64::MAX
        let (diff, borrow) = sbb(0, 1, false);
        assert_eq!(diff, u64::MAX);
        assert!(borrow);
    }

    #[test]
    fn mac_small() {
        // 0 + 3 * 7 + 0 = 21
        let (lo, hi) = mac(0, 3, 7, 0);
        assert_eq!(lo, 21);
        assert_eq!(hi, 0);
    }

    #[test]
    fn mac_overflow_to_hi() {
        // u64::MAX * u64::MAX = (2^64-1)^2 = 2^128 - 2^65 + 1
        let (lo, hi) = mac(0, u64::MAX, u64::MAX, 0);
        assert_eq!(lo, 1);
        assert_eq!(hi, u64::MAX - 1);
    }

    // Step 2-4 테스트

    #[test]
    fn inv_constant_is_correct() {
        // p0 * INV ≡ -1 (mod 2^64)
        let check = MODULUS[0].wrapping_mul(INV);
        assert_eq!(check.wrapping_add(1), 0);
    }

    #[test]
    fn montgomery_roundtrip() {
        // from_raw(42) → to_repr() == [42, 0, 0, 0]
        let raw = [42u64, 0, 0, 0];
        let fp = Fp::from_raw(raw);
        assert_eq!(fp.to_repr(), raw);
    }

    #[test]
    fn from_u64_zero_and_one() {
        assert_eq!(Fp::from_u64(0), Fp::ZERO);
        assert_eq!(Fp::from_u64(1), Fp::ONE);
    }

    #[test]
    fn mont_mul_small() {
        // 6 * 7 = 42
        let a = Fp::from_u64(6);
        let b = Fp::from_u64(7);
        assert_eq!(a.mont_mul(&b), Fp::from_u64(42));
    }

    #[test]
    fn mont_mul_identity() {
        // a * 1 = a
        let a = Fp::from_u64(123);
        assert_eq!(a.mont_mul(&Fp::ONE), a);
    }

    // Step 2-5 테스트

    #[test]
    fn square_small() {
        let a = Fp::from_u64(9);
        assert_eq!(a.square(), Fp::from_u64(81));
    }

    #[test]
    fn square_equals_mul_self() {
        let a = Fp::from_u64(123);
        assert_eq!(a.square(), a.mont_mul(&a));
    }

    #[test]
    fn pow_small() {
        // 3^10 = 59049
        let result = Fp::from_u64(3).pow(&[10, 0, 0, 0]);
        assert_eq!(result, Fp::from_u64(59049));
    }

    #[test]
    fn inv_of_seven() {
        let a = Fp::from_u64(7);
        let a_inv = a.inv().expect("7의 역원 존재");
        // a * a^{-1} = 1
        assert_eq!(a.mont_mul(&a_inv), Fp::ONE);
    }

    #[test]
    fn inv_of_one() {
        assert_eq!(Fp::ONE.inv().unwrap(), Fp::ONE);
    }

    #[test]
    fn inv_of_zero_is_none() {
        assert!(Fp::ZERO.inv().is_none());
    }

    #[test]
    fn p_minus_one_squared_is_one() {
        // p-1 ≡ -1 (mod p), (-1)^2 = 1
        let p_minus_1 = Fp::from_raw([MODULUS[0] - 1, MODULUS[1], MODULUS[2], MODULUS[3]]);
        assert_eq!(p_minus_1.square(), Fp::ONE);
    }

    // Step 2-3 테스트

    #[test]
    fn add_small() {
        let a = Fp([7, 0, 0, 0]);
        let b = Fp([11, 0, 0, 0]);
        assert_eq!(a.add(&b), Fp([18, 0, 0, 0]));
    }

    #[test]
    fn add_wraps_mod_p() {
        // (p-1) + 1 = 0 mod p
        let p_minus_1 = Fp([MODULUS[0] - 1, MODULUS[1], MODULUS[2], MODULUS[3]]);
        let one = Fp([1, 0, 0, 0]);
        assert_eq!(p_minus_1.add(&one), Fp::ZERO);
    }

    #[test]
    fn sub_small() {
        let a = Fp([20, 0, 0, 0]);
        let b = Fp([7, 0, 0, 0]);
        assert_eq!(a.sub(&b), Fp([13, 0, 0, 0]));
    }

    #[test]
    fn sub_underflow_wraps() {
        // 3 - 7 → underflow → 결과 + 7 하면 다시 3
        let a = Fp([3, 0, 0, 0]);
        let b = Fp([7, 0, 0, 0]);
        let c = a.sub(&b);
        assert_eq!(c.add(&Fp([7, 0, 0, 0])), Fp([3, 0, 0, 0]));
    }

    #[test]
    fn neg_plus_self_is_zero() {
        let a = Fp([42, 0, 0, 0]);
        assert_eq!(a.add(&a.neg()), Fp::ZERO);
    }

    #[test]
    fn neg_zero_is_zero() {
        assert_eq!(Fp::ZERO.neg(), Fp::ZERO);
    }

    // Step 2-6 테스트: 연산자 + 체 공리

    #[test]
    fn operator_syntax() {
        let a = Fp::from_u64(6);
        let b = Fp::from_u64(7);
        assert_eq!(a + b, Fp::from_u64(13));
        assert_eq!(a * b, Fp::from_u64(42));
        assert_eq!(b - a, Fp::from_u64(1));
        assert_eq!(a + (-a), Fp::ZERO);
    }

    #[test]
    fn additive_identity() {
        // a + 0 = a
        let a = Fp::from_u64(42);
        assert_eq!(a + Fp::ZERO, a);
        assert_eq!(Fp::ZERO + a, a);
    }

    #[test]
    fn multiplicative_identity() {
        // a * 1 = a
        let a = Fp::from_u64(42);
        assert_eq!(a * Fp::ONE, a);
        assert_eq!(Fp::ONE * a, a);
    }

    #[test]
    fn commutativity() {
        let a = Fp::from_u64(13);
        let b = Fp::from_u64(29);
        assert_eq!(a + b, b + a);
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn associativity() {
        let a = Fp::from_u64(3);
        let b = Fp::from_u64(7);
        let c = Fp::from_u64(11);
        assert_eq!((a + b) + c, a + (b + c));
        assert_eq!((a * b) * c, a * (b * c));
    }

    #[test]
    fn distributivity() {
        // a * (b + c) = a*b + a*c
        let a = Fp::from_u64(3);
        let b = Fp::from_u64(7);
        let c = Fp::from_u64(11);
        assert_eq!(a * (b + c), a * b + a * c);
    }

    #[test]
    fn inverse_larger_value() {
        let a = Fp::from_raw([0xdeadbeef, 0xcafebabe, 0, 0]);
        let a_inv = a.inv().unwrap();
        assert_eq!(a * a_inv, Fp::ONE);
    }

    #[test]
    fn display_format() {
        let a = Fp::from_u64(42);
        let s = format!("{}", a);
        assert!(s.starts_with("Fp(0x"));
    }
}
