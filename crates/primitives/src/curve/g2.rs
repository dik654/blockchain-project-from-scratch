// Step 5-2: G2 — BN254 트위스트 커브 위의 타원곡선 군
//
// G2는 "진짜로는" E(Fp12) 위의 점이지만,
// sextic twist를 사용하면 Fp2 위의 점으로 표현 가능
//   → Fp12 산술 대신 Fp2 산술 → 차원 12 → 2로 줄어듦
//
// 트위스트 커브: Y² = X³ + b'
//   b' = b/ξ = 3/(9+u)  (D-type sextic twist)
//   ξ = 9+u = Fp6의 non-residue
//
// G1과 동일한 인터페이스 — 좌표 타입만 Fp → Fp2로 바뀜

use crate::field::{Fp, Fp2};

/// Fp2에 "실수" 상수를 만드는 헬퍼 (허수부 = 0)
fn fp2_const(n: u64) -> Fp2 {
    Fp2::new(Fp::from_u64(n), Fp::ZERO)
}

/// G2 트위스트 커브 파라미터: b' = b/ξ = 3/(9+u)
fn twist_b() -> Fp2 {
    let b = fp2_const(3);
    let xi = Fp2::new(Fp::from_u64(9), Fp::from_u64(1));
    b * xi.inv().unwrap()
}

/// Affine 좌표 — 외부 인터페이스용
#[derive(Clone, Copy, Debug)]
pub struct G2Affine {
    pub x: Fp2,
    pub y: Fp2,
    pub infinity: bool,
}

impl G2Affine {
    pub fn identity() -> Self {
        G2Affine { x: Fp2::ZERO, y: Fp2::ZERO, infinity: true }
    }

    pub fn new(x: Fp2, y: Fp2) -> Self {
        G2Affine { x, y, infinity: false }
    }

    /// y² = x³ + b'
    pub fn is_on_curve(&self) -> bool {
        if self.infinity { return true; }
        let b = twist_b();
        self.y.square() == self.x.square() * self.x + b
    }

    /// Affine → Jacobian
    pub fn to_projective(&self) -> G2 {
        if self.infinity {
            G2::identity()
        } else {
            G2 { x: self.x, y: self.y, z: Fp2::ONE }
        }
    }
}

impl PartialEq for G2Affine {
    fn eq(&self, other: &Self) -> bool {
        if self.infinity && other.infinity { return true; }
        if self.infinity || other.infinity { return false; }
        self.x == other.x && self.y == other.y
    }
}
impl Eq for G2Affine {}

/// Jacobian 좌표 — 내부 연산용
/// (X, Y, Z) → affine (X/Z², Y/Z³)
#[derive(Clone, Copy, Debug)]
pub struct G2 {
    pub x: Fp2,
    pub y: Fp2,
    pub z: Fp2,
}

impl G2 {
    /// 항등원 (무한원점)
    pub fn identity() -> Self {
        G2 { x: Fp2::ZERO, y: Fp2::ONE, z: Fp2::ZERO }
    }

    /// BN254 표준 G2 생성자
    pub fn generator() -> Self {
        let x = Fp2::new(
            Fp::from_raw([
                0x46debd5cd992f6ed, 0x674322d4f75edadd,
                0x426a00665e5c4479, 0x1800deef121f1e76,
            ]),
            Fp::from_raw([
                0x97e485b7aef312c2, 0xf1aa493335a9e712,
                0x7260bfb731fb5d25, 0x198e9393920d483a,
            ]),
        );
        let y = Fp2::new(
            Fp::from_raw([
                0x4ce6cc0166fa7daa, 0xe3d1e7690c43d37b,
                0x4aab71808dcb408f, 0x12c85ea5db8c6deb,
            ]),
            Fp::from_raw([
                0x55acdadcd122975b, 0xbc4b313370b38ef3,
                0xec9e99ad690c3395, 0x090689d0585ff075,
            ]),
        );
        G2 { x, y, z: Fp2::ONE }
    }

    pub fn is_identity(&self) -> bool {
        self.z.is_zero()
    }

    /// Y² = X³ + b'·Z⁶
    pub fn is_on_curve(&self) -> bool {
        if self.is_identity() { return true; }
        let b = twist_b();
        let z2 = self.z.square();
        let z6 = z2.square() * z2;
        self.y.square() == self.x.square() * self.x + b * z6
    }

    /// -(X, Y, Z) = (X, -Y, Z)
    pub fn neg(&self) -> G2 {
        G2 { x: self.x, y: -self.y, z: self.z }
    }

    /// 점 더블링: 2P — G1과 동일한 공식, 좌표 타입만 Fp2
    pub fn double(&self) -> G2 {
        if self.is_identity() || self.y.is_zero() {
            return G2::identity();
        }

        let two = fp2_const(2);
        let three = fp2_const(3);
        let four = fp2_const(4);
        let eight = fp2_const(8);

        let a = self.y.square();
        let b = four * self.x * a;
        let c = eight * a.square();
        let d = three * self.x.square();

        let x3 = d.square() - two * b;
        let y3 = d * (b - x3) - c;
        let z3 = two * self.y * self.z;

        G2 { x: x3, y: y3, z: z3 }
    }

    /// 점 덧셈: P + Q — G1과 동일한 공식, 좌표 타입만 Fp2
    pub fn add(&self, rhs: &G2) -> G2 {
        if self.is_identity() { return *rhs; }
        if rhs.is_identity() { return *self; }

        let z1s = self.z.square();
        let z2s = rhs.z.square();

        let u1 = self.x * z2s;
        let u2 = rhs.x * z1s;
        let s1 = self.y * z2s * rhs.z;
        let s2 = rhs.y * z1s * self.z;

        if u1 == u2 {
            if s1 == s2 {
                return self.double();
            } else {
                return G2::identity();
            }
        }

        let h = u2 - u1;
        let r = s2 - s1;
        let h2 = h.square();
        let h3 = h * h2;
        let u1h2 = u1 * h2;

        let x3 = r.square() - h3 - fp2_const(2) * u1h2;
        let y3 = r * (u1h2 - x3) - s1 * h3;
        let z3 = h * self.z * rhs.z;

        G2 { x: x3, y: y3, z: z3 }
    }

    /// 스칼라 곱: k·P (double-and-add)
    pub fn scalar_mul(&self, scalar: &[u64; 4]) -> G2 {
        let mut result = G2::identity();
        let mut base = *self;
        for &limb in scalar.iter() {
            for j in 0..64 {
                if (limb >> j) & 1 == 1 {
                    result = result.add(&base);
                }
                base = base.double();
            }
        }
        result
    }

    /// Jacobian → Affine: (X, Y, Z) → (X/Z², Y/Z³)
    pub fn to_affine(&self) -> G2Affine {
        if self.is_identity() {
            return G2Affine::identity();
        }
        let z_inv = self.z.inv().unwrap();
        let z_inv2 = z_inv.square();
        let z_inv3 = z_inv2 * z_inv;
        G2Affine {
            x: self.x * z_inv2,
            y: self.y * z_inv3,
            infinity: false,
        }
    }
}

impl PartialEq for G2 {
    fn eq(&self, other: &Self) -> bool {
        if self.is_identity() && other.is_identity() { return true; }
        if self.is_identity() || other.is_identity() { return false; }
        let z1s = self.z.square();
        let z2s = other.z.square();
        self.x * z2s == other.x * z1s
            && self.y * z2s * other.z == other.y * z1s * self.z
    }
}
impl Eq for G2 {}

impl std::ops::Add for G2 {
    type Output = G2;
    fn add(self, rhs: G2) -> G2 { G2::add(&self, &rhs) }
}

impl std::ops::Neg for G2 {
    type Output = G2;
    fn neg(self) -> G2 { G2::neg(&self) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generator_is_on_curve() {
        let g = G2::generator();
        assert!(g.is_on_curve());
    }

    #[test]
    fn identity_is_on_curve() {
        assert!(G2::identity().is_on_curve());
    }

    #[test]
    fn generator_affine_is_on_curve() {
        let g = G2::generator().to_affine();
        assert!(g.is_on_curve());
    }

    #[test]
    fn identity_add() {
        let g = G2::generator();
        let o = G2::identity();
        assert_eq!(g + o, g);
        assert_eq!(o + g, g);
    }

    #[test]
    fn neg_add_is_identity() {
        let g = G2::generator();
        assert_eq!(g + (-g), G2::identity());
    }

    #[test]
    fn double_matches_add() {
        let g = G2::generator();
        assert_eq!(g.double(), g + g);
    }

    #[test]
    fn double_is_on_curve() {
        let g2 = G2::generator().double();
        assert!(g2.is_on_curve());
    }

    #[test]
    fn add_commutativity() {
        let g = G2::generator();
        let g2 = g.double();
        assert_eq!(g + g2, g2 + g);
    }

    #[test]
    fn scalar_mul_one() {
        let g = G2::generator();
        assert_eq!(g.scalar_mul(&[1, 0, 0, 0]), g);
    }

    #[test]
    fn scalar_mul_two() {
        let g = G2::generator();
        assert_eq!(g.scalar_mul(&[2, 0, 0, 0]), g.double());
    }

    #[test]
    fn scalar_mul_three() {
        let g = G2::generator();
        assert_eq!(g.scalar_mul(&[3, 0, 0, 0]), g.double() + g);
    }

    #[test]
    fn scalar_mul_order_gives_identity() {
        // r·G = O (G2의 위수도 r)
        let g = G2::generator();
        let r = [
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ];
        assert_eq!(g.scalar_mul(&r), G2::identity());
    }

    #[test]
    fn to_affine_roundtrip() {
        let g = G2::generator();
        let g3 = (g + g + g).to_affine();
        assert!(g3.is_on_curve());
        assert_eq!(g3.to_projective().to_affine(), g3);
    }

    #[test]
    fn scalar_mul_distributive() {
        let g = G2::generator();
        assert_eq!(
            g.scalar_mul(&[5, 0, 0, 0]),
            g.scalar_mul(&[2, 0, 0, 0]) + g.scalar_mul(&[3, 0, 0, 0])
        );
    }
}
