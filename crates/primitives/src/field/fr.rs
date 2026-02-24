// Step 3-1 ~ 3-2: Fr — BN254 스칼라체
//
// Fp와 Fr의 차이:
//   Fp: 좌표를 표현하는 체. modulus = p (base field prime)
//   Fr: 스칼라를 표현하는 체. modulus = r (커브의 위수, group order)
//
// ZK 증명에서 witness는 Fr 원소로 표현된다
//
// 구현은 Fp와 100% 동일 — define_prime_field! 매크로에 상수만 넣으면 끝

use super::{adc, sbb, mac};

// 매크로 한 줄로 Fr의 모든 산술이 생성된다
// (Fp는 학습용으로 수동 구현, Fr은 매크로로 코드 재사용)
super::define_prime_field!(
    Fr,
    // r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    modulus: [
        0x43e1f593f0000001,
        0x2833e84879b97091,
        0xb85045b68181585d,
        0x30644e72e131a029
    ],
    // R = 2^256 mod r
    r: [
        0xac96341c4ffffffb,
        0x36fc76959f60cd29,
        0x666ea36f7879462e,
        0x0e0a77c19a07df2f
    ],
    // R^2 mod r
    r2: [
        0x1bb8e645ae216da7,
        0x53fe3ab1e35c59e3,
        0x8c49833d53bb8085,
        0x0216d0b17f4e44a5
    ]
);

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
        assert!(Fr::ZERO.is_zero());
    }

    #[test]
    fn nonzero_is_not_zero() {
        assert!(!Fr([1, 0, 0, 0]).is_zero());
    }

    #[test]
    fn inv_constant_is_correct() {
        let check = MODULUS[0].wrapping_mul(INV);
        assert_eq!(check.wrapping_add(1), 0);
    }

    #[test]
    fn montgomery_roundtrip() {
        let raw = [42u64, 0, 0, 0];
        let fr = Fr::from_raw(raw);
        assert_eq!(fr.to_repr(), raw);
    }

    #[test]
    fn from_u64_zero_and_one() {
        assert_eq!(Fr::from_u64(0), Fr::ZERO);
        assert_eq!(Fr::from_u64(1), Fr::ONE);
    }

    #[test]
    fn mul_small() {
        let a = Fr::from_u64(6);
        let b = Fr::from_u64(7);
        assert_eq!(a * b, Fr::from_u64(42));
    }

    #[test]
    fn add_sub() {
        let a = Fr::from_u64(100);
        let b = Fr::from_u64(42);
        assert_eq!((a - b), Fr::from_u64(58));
        assert_eq!((a + b), Fr::from_u64(142));
    }

    #[test]
    fn inverse() {
        let a = Fr::from_u64(7);
        let a_inv = a.inv().unwrap();
        assert_eq!(a * a_inv, Fr::ONE);
    }

    #[test]
    fn field_axioms() {
        let a = Fr::from_u64(3);
        let b = Fr::from_u64(7);
        let c = Fr::from_u64(11);
        // 교환법칙
        assert_eq!(a + b, b + a);
        assert_eq!(a * b, b * a);
        // 결합법칙
        assert_eq!((a + b) + c, a + (b + c));
        assert_eq!((a * b) * c, a * (b * c));
        // 분배법칙
        assert_eq!(a * (b + c), a * b + a * c);
        // 항등원
        assert_eq!(a + Fr::ZERO, a);
        assert_eq!(a * Fr::ONE, a);
        // 역원
        assert_eq!(a + (-a), Fr::ZERO);
    }
}
