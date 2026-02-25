// Step 3-2: 유한체 공용 헬퍼 + 매크로
//
// adc, sbb, mac은 Fp와 Fr 모두에서 사용되므로 공용 모듈로 분리
// define_prime_field! 매크로로 상수만 바꿔서 새 유한체 타입을 생성

/// a + b + carry → (합, carry)
#[inline(always)]
pub(crate) fn adc(a: u64, b: u64, carry: bool) -> (u64, bool) {
    let (s1, c1) = a.overflowing_add(b);
    let (s2, c2) = s1.overflowing_add(carry as u64);
    (s2, c1 | c2)
}

/// a - b - borrow → (차, borrow)
#[inline(always)]
pub(crate) fn sbb(a: u64, b: u64, borrow: bool) -> (u64, bool) {
    let (s1, b1) = a.overflowing_sub(b);
    let (s2, b2) = s1.overflowing_sub(borrow as u64);
    (s2, b1 | b2)
}

/// acc + a * b + carry → (lo, hi)
#[inline(always)]
pub(crate) fn mac(acc: u64, a: u64, b: u64, carry: u64) -> (u64, u64) {
    let wide = acc as u128 + (a as u128) * (b as u128) + carry as u128;
    (wide as u64, (wide >> 64) as u64)
}

/// 상수(MODULUS, R, R2)만 넣으면 완전한 유한체 타입이 생성되는 매크로
///
/// Fp와 Fr은 산술 로직이 100% 동일 — 다른 것은 이 상수뿐:
///   MODULUS: 어떤 소수로 나눌지
///   R: Montgomery form의 1 (2^256 mod MODULUS)
///   R2: normal → Montgomery 변환용 (2^512 mod MODULUS)
///   INV: REDC용 마법 상수 (MODULUS[0]에서 자동 계산)
macro_rules! define_prime_field {
    (
        $name:ident,
        modulus: [$m0:expr, $m1:expr, $m2:expr, $m3:expr],
        r: [$r0:expr, $r1:expr, $r2:expr, $r3:expr],
        r2: [$r2_0:expr, $r2_1:expr, $r2_2:expr, $r2_3:expr]
    ) => {
        const MODULUS: [u64; 4] = [$m0, $m1, $m2, $m3];
        const R: [u64; 4] = [$r0, $r1, $r2, $r3];
        const R2: [u64; 4] = [$r2_0, $r2_1, $r2_2, $r2_3];

        const INV: u64 = {
            let p0 = MODULUS[0];
            let mut inv = 1u64;
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
            inv = inv.wrapping_mul(2u64.wrapping_sub(p0.wrapping_mul(inv)));
            inv.wrapping_neg()
        };

        #[derive(Clone, Copy, PartialEq, Eq, Debug)]
        pub struct $name(pub(crate) [u64; 4]);

        impl $name {
            pub const ZERO: $name = $name([0, 0, 0, 0]);
            pub const ONE: $name = $name(R);

            pub fn is_zero(&self) -> bool { self.0 == [0, 0, 0, 0] }

            pub fn from_raw(v: [u64; 4]) -> Self {
                $name(v).mont_mul(&$name(R2))
            }

            pub fn from_u64(v: u64) -> Self { Self::from_raw([v, 0, 0, 0]) }

            pub fn to_repr(&self) -> [u64; 4] {
                let mut t = [0u64; 8];
                t[0] = self.0[0]; t[1] = self.0[1];
                t[2] = self.0[2]; t[3] = self.0[3];
                Self::mont_reduce_inner(&t)
            }

            pub fn mont_mul(&self, rhs: &$name) -> $name {
                let mut t = [0u64; 8];
                let (t0, carry) = mac(0, self.0[0], rhs.0[0], 0);
                let (t1, carry) = mac(0, self.0[0], rhs.0[1], carry);
                let (t2, carry) = mac(0, self.0[0], rhs.0[2], carry);
                let (t3, t4)    = mac(0, self.0[0], rhs.0[3], carry);
                t[0] = t0;
                let (t1, carry) = mac(t1, self.0[1], rhs.0[0], 0);
                let (t2, carry) = mac(t2, self.0[1], rhs.0[1], carry);
                let (t3, carry) = mac(t3, self.0[1], rhs.0[2], carry);
                let (t4, t5)    = mac(t4, self.0[1], rhs.0[3], carry);
                t[1] = t1;
                let (t2, carry) = mac(t2, self.0[2], rhs.0[0], 0);
                let (t3, carry) = mac(t3, self.0[2], rhs.0[1], carry);
                let (t4, carry) = mac(t4, self.0[2], rhs.0[2], carry);
                let (t5, t6)    = mac(t5, self.0[2], rhs.0[3], carry);
                t[2] = t2;
                let (t3, carry) = mac(t3, self.0[3], rhs.0[0], 0);
                let (t4, carry) = mac(t4, self.0[3], rhs.0[1], carry);
                let (t5, carry) = mac(t5, self.0[3], rhs.0[2], carry);
                let (t6, t7)    = mac(t6, self.0[3], rhs.0[3], carry);
                t[3] = t3; t[4] = t4; t[5] = t5; t[6] = t6; t[7] = t7;
                $name(Self::mont_reduce_inner(&t))
            }

            fn mont_reduce_inner(t: &[u64; 8]) -> [u64; 4] {
                let mut r = *t;
                for i in 0..4 {
                    let m = r[i].wrapping_mul(INV);
                    let (_, carry) = mac(r[i], m, MODULUS[0], 0);
                    let (res, carry) = mac(r[i+1], m, MODULUS[1], carry);
                    r[i+1] = res;
                    let (res, carry) = mac(r[i+2], m, MODULUS[2], carry);
                    r[i+2] = res;
                    let (res, carry) = mac(r[i+3], m, MODULUS[3], carry);
                    r[i+3] = res;
                    if i + 4 < 8 {
                        let (res, c2) = r[i+4].overflowing_add(carry);
                        r[i+4] = res;
                        if c2 && i + 5 < 8 {
                            let (res, c3) = r[i+5].overflowing_add(1);
                            r[i+5] = res;
                            if c3 && i + 6 < 8 {
                                r[i+6] = r[i+6].wrapping_add(1);
                            }
                        }
                    }
                }
                sub_if_gte([r[4], r[5], r[6], r[7]]).0
            }

            pub fn add(&self, rhs: &$name) -> $name {
                let (d0, carry) = self.0[0].overflowing_add(rhs.0[0]);
                let (d1, carry) = adc(self.0[1], rhs.0[1], carry);
                let (d2, carry) = adc(self.0[2], rhs.0[2], carry);
                let (d3, _)     = adc(self.0[3], rhs.0[3], carry);
                sub_if_gte([d0, d1, d2, d3])
            }

            pub fn sub(&self, rhs: &$name) -> $name {
                let (d0, borrow) = self.0[0].overflowing_sub(rhs.0[0]);
                let (d1, borrow) = sbb(self.0[1], rhs.0[1], borrow);
                let (d2, borrow) = sbb(self.0[2], rhs.0[2], borrow);
                let (d3, borrow) = sbb(self.0[3], rhs.0[3], borrow);
                if borrow {
                    let (d0, carry) = d0.overflowing_add(MODULUS[0]);
                    let (d1, carry) = adc(d1, MODULUS[1], carry);
                    let (d2, carry) = adc(d2, MODULUS[2], carry);
                    let (d3, _)     = adc(d3, MODULUS[3], carry);
                    $name([d0, d1, d2, d3])
                } else {
                    $name([d0, d1, d2, d3])
                }
            }

            pub fn neg(&self) -> $name {
                if self.is_zero() {
                    *self
                } else {
                    let (d0, borrow) = MODULUS[0].overflowing_sub(self.0[0]);
                    let (d1, borrow) = sbb(MODULUS[1], self.0[1], borrow);
                    let (d2, borrow) = sbb(MODULUS[2], self.0[2], borrow);
                    let (d3, _)      = sbb(MODULUS[3], self.0[3], borrow);
                    $name([d0, d1, d2, d3])
                }
            }

            pub fn square(&self) -> $name { self.mont_mul(self) }

            pub fn pow(&self, exp: &[u64; 4]) -> $name {
                let mut result = Self::ONE;
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

            pub fn inv(&self) -> Option<$name> {
                if self.is_zero() { return None; }
                Some(self.pow(&[MODULUS[0] - 2, MODULUS[1], MODULUS[2], MODULUS[3]]))
            }
        }

        fn sub_if_gte(v: [u64; 4]) -> $name {
            let (d0, borrow) = v[0].overflowing_sub(MODULUS[0]);
            let (d1, borrow) = sbb(v[1], MODULUS[1], borrow);
            let (d2, borrow) = sbb(v[2], MODULUS[2], borrow);
            let (d3, borrow) = sbb(v[3], MODULUS[3], borrow);
            if borrow { $name(v) } else { $name([d0, d1, d2, d3]) }
        }

        impl std::ops::Add for $name {
            type Output = $name;
            fn add(self, rhs: $name) -> $name { $name::add(&self, &rhs) }
        }
        impl std::ops::Add<&$name> for $name {
            type Output = $name;
            fn add(self, rhs: &$name) -> $name { $name::add(&self, rhs) }
        }
        impl std::ops::Sub for $name {
            type Output = $name;
            fn sub(self, rhs: $name) -> $name { $name::sub(&self, &rhs) }
        }
        impl std::ops::Sub<&$name> for $name {
            type Output = $name;
            fn sub(self, rhs: &$name) -> $name { $name::sub(&self, rhs) }
        }
        impl std::ops::Mul for $name {
            type Output = $name;
            fn mul(self, rhs: $name) -> $name { self.mont_mul(&rhs) }
        }
        impl std::ops::Mul<&$name> for $name {
            type Output = $name;
            fn mul(self, rhs: &$name) -> $name { self.mont_mul(rhs) }
        }
        impl std::ops::Neg for $name {
            type Output = $name;
            fn neg(self) -> $name { $name::neg(&self) }
        }
        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let repr = self.to_repr();
                write!(f, "{}(0x{:016x}{:016x}{:016x}{:016x})",
                    stringify!($name), repr[3], repr[2], repr[1], repr[0])
            }
        }
    };
}
pub(crate) use define_prime_field;

pub mod fp;
pub mod fr;
pub mod fp2;
pub mod fp6;
pub mod fp12;

pub use fp::Fp;
pub use fr::Fr;
pub use fp2::Fp2;
pub use fp6::Fp6;
pub use fp12::Fp12;
