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

/// BN254 base field element
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Fp(pub(crate) [u64; 4]);

impl Fp {
    pub const ZERO: Fp = Fp([0, 0, 0, 0]);

    pub fn is_zero(&self) -> bool {
        self.0 == [0, 0, 0, 0]
    }
}

// Step 2-2: 큰 수 산술의 빌딩 블록
//
// 문제: u64 + u64가 64-bit를 넘으면?
// → carry(올림)를 다음 limb으로 전파해야 한다
// 이 세 함수가 [u64; 4] 산술의 기초가 된다

/// a + b + carry_in → (합, carry_out)
#[inline(always)]
fn adc(a: u64, b: u64, carry: bool) -> (u64, bool) {
    let (s1, c1) = a.overflowing_add(b);
    let (s2, c2) = s1.overflowing_add(carry as u64);
    (s2, c1 | c2)
}

/// a - b - borrow_in → (차, borrow_out)
#[inline(always)]
fn sbb(a: u64, b: u64, borrow: bool) -> (u64, bool) {
    let (s1, b1) = a.overflowing_sub(b);
    let (s2, b2) = s1.overflowing_sub(borrow as u64);
    (s2, b1 | b2)
}

/// acc + a * b + carry → (lo_64bit, hi_64bit)
/// u128로 확장해서 오버플로 없이 계산
#[inline(always)]
fn mac(acc: u64, a: u64, b: u64, carry: u64) -> (u64, u64) {
    let wide = acc as u128 + (a as u128) * (b as u128) + carry as u128;
    (wide as u64, (wide >> 64) as u64)
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
}
