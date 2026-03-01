// Step 5-1: G1 — BN254 기저체 위의 타원곡선 군
//
// BN254: y² = x³ + 3  (a = 0, b = 3)
//
// 왜 타원곡선인가?
//   유한체 위에 정의된 타원곡선의 점들은 "군"을 이루고,
//   이 군에서의 이산로그 문제(ECDLP)가 어려움 → 암호학적 안전성
//
// Affine 좌표 (x, y):
//   직관적이지만, 점 덧셈마다 역원(Fp::inv) 필요 — 비싸다!
//
// Jacobian 좌표 (X, Y, Z):
//   affine (x, y) = (X/Z², Y/Z³)
//   역원 없이 덧셈/더블링 가능 → to_affine 할 때만 역원 1번
//
// G1 = Fp 위의 점 (좌표가 Fp 원소)
// G2 = Fp2 위의 점 (다음 스탭)

use crate::field::Fp;

/// Affine 좌표 — 외부 인터페이스용
#[derive(Clone, Copy, Debug)]
pub struct G1Affine {
    pub x: Fp,
    pub y: Fp,
    pub infinity: bool,
}

impl G1Affine {
    pub fn identity() -> Self {
        G1Affine { x: Fp::ZERO, y: Fp::ZERO, infinity: true }
    }

    pub fn new(x: Fp, y: Fp) -> Self {
        G1Affine { x, y, infinity: false }
    }

    /// y² = x³ + 3
    pub fn is_on_curve(&self) -> bool {
        if self.infinity { return true; }
        let b = Fp::from_u64(3);
        self.y.square() == self.x.square() * self.x + b
    }

    /// Affine → Jacobian
    pub fn to_projective(&self) -> G1 {
        if self.infinity {
            G1::identity()
        } else {
            G1 { x: self.x, y: self.y, z: Fp::ONE }
        }
    }
}

impl PartialEq for G1Affine {
    fn eq(&self, other: &Self) -> bool {
        if self.infinity && other.infinity { return true; }
        if self.infinity || other.infinity { return false; }
        self.x == other.x && self.y == other.y
    }
}
impl Eq for G1Affine {}

/// Jacobian 좌표 — 내부 연산용
/// (X, Y, Z) → affine (X/Z², Y/Z³)
#[derive(Clone, Copy, Debug)]
pub struct G1 {
    pub x: Fp,
    pub y: Fp,
    pub z: Fp,
}

impl G1 {
    /// 항등원 (무한원점): Z = 0인 점
    pub fn identity() -> Self {
        G1 { x: Fp::ZERO, y: Fp::ONE, z: Fp::ZERO }
    }

    /// BN254 G1 생성자: affine (1, 2)
    /// 확인: 2² = 4 = 1³ + 3 ✓
    pub fn generator() -> Self {
        G1 {
            x: Fp::from_u64(1),
            y: Fp::from_u64(2),
            z: Fp::ONE,
        }
    }

    pub fn is_identity(&self) -> bool {
        self.z.is_zero()
    }

    /// Jacobian 좌표에서 커브 위 확인: Y² = X³ + b·Z⁶
    pub fn is_on_curve(&self) -> bool {
        if self.is_identity() { return true; }
        let b = Fp::from_u64(3);
        let z2 = self.z.square();
        let z6 = z2.square() * z2;
        self.y.square() == self.x.square() * self.x + b * z6
    }

    /// 역원: -(X, Y, Z) = (X, -Y, Z)
    pub fn neg(&self) -> G1 {
        G1 { x: self.x, y: -self.y, z: self.z }
    }

    /// 점 더블링: 2P
    ///
    /// a=0이므로 단순화:
    ///   A = Y²,  B = 4·X·A,  C = 8·A²,  D = 3·X²
    ///   X₃ = D² - 2B
    ///   Y₃ = D·(B - X₃) - C
    ///   Z₃ = 2·Y·Z
    pub fn double(&self) -> G1 {
        if self.is_identity() || self.y.is_zero() {
            return G1::identity();
        }

        let two = Fp::from_u64(2);
        let three = Fp::from_u64(3);
        let four = Fp::from_u64(4);
        let eight = Fp::from_u64(8);

        let a = self.y.square();
        let b = four * self.x * a;
        let c = eight * a.square();
        let d = three * self.x.square(); // 3X² (a=0이므로 +aZ⁴ 항 없음)

        let x3 = d.square() - two * b;
        let y3 = d * (b - x3) - c;
        let z3 = two * self.y * self.z;

        G1 { x: x3, y: y3, z: z3 }
    }

    /// 점 덧셈: P + Q
    ///
    /// U₁ = X₁Z₂², U₂ = X₂Z₁²
    /// S₁ = Y₁Z₂³, S₂ = Y₂Z₁³
    /// H = U₂ - U₁, R = S₂ - S₁
    /// X₃ = R² - H³ - 2U₁H²
    /// Y₃ = R(U₁H² - X₃) - S₁H³
    /// Z₃ = H·Z₁·Z₂
    pub fn add(&self, rhs: &G1) -> G1 {
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
                return self.double(); // P == Q
            } else {
                return G1::identity(); // P == -Q
            }
        }

        let h = u2 - u1;
        let r = s2 - s1;
        let h2 = h.square();
        let h3 = h * h2;
        let u1h2 = u1 * h2;

        let x3 = r.square() - h3 - Fp::from_u64(2) * u1h2;
        let y3 = r * (u1h2 - x3) - s1 * h3;
        let z3 = h * self.z * rhs.z;

        G1 { x: x3, y: y3, z: z3 }
    }

    /// 스칼라 곱: k·P (double-and-add)
    ///
    /// k의 각 비트를 순회하며:
    ///   비트가 1이면 result += base
    ///   base를 매번 더블링
    pub fn scalar_mul(&self, scalar: &[u64; 4]) -> G1 {
        let mut result = G1::identity();
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
    /// 역원 호출은 이 순간에만 1번
    pub fn to_affine(&self) -> G1Affine {
        if self.is_identity() {
            return G1Affine::identity();
        }
        let z_inv = self.z.inv().unwrap();
        let z_inv2 = z_inv.square();
        let z_inv3 = z_inv2 * z_inv;
        G1Affine {
            x: self.x * z_inv2,
            y: self.y * z_inv3,
            infinity: false,
        }
    }
}

impl PartialEq for G1 {
    fn eq(&self, other: &Self) -> bool {
        if self.is_identity() && other.is_identity() { return true; }
        if self.is_identity() || other.is_identity() { return false; }
        // X₁Z₂² == X₂Z₁² and Y₁Z₂³ == Y₂Z₁³
        let z1s = self.z.square();
        let z2s = other.z.square();
        self.x * z2s == other.x * z1s
            && self.y * z2s * other.z == other.y * z1s * self.z
    }
}
impl Eq for G1 {}

impl std::ops::Add for G1 {
    type Output = G1;
    fn add(self, rhs: G1) -> G1 { G1::add(&self, &rhs) }
}

impl std::ops::Neg for G1 {
    type Output = G1;
    fn neg(self) -> G1 { G1::neg(&self) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generator_is_on_curve() {
        let g = G1::generator();
        assert!(g.is_on_curve());
    }

    #[test]
    fn identity_is_on_curve() {
        assert!(G1::identity().is_on_curve());
    }

    #[test]
    fn generator_affine_is_on_curve() {
        let g = G1::generator().to_affine();
        assert!(g.is_on_curve());
        assert_eq!(g.x, Fp::from_u64(1));
        assert_eq!(g.y, Fp::from_u64(2));
    }

    #[test]
    fn identity_add() {
        let g = G1::generator();
        let o = G1::identity();
        assert_eq!(g + o, g); // P + O = P
        assert_eq!(o + g, g); // O + P = P
    }

    #[test]
    fn neg_add_is_identity() {
        let g = G1::generator();
        assert_eq!(g + (-g), G1::identity()); // P + (-P) = O
    }

    #[test]
    fn double_matches_add() {
        let g = G1::generator();
        assert_eq!(g.double(), g + g); // 2P = P + P
    }

    #[test]
    fn double_is_on_curve() {
        let g2 = G1::generator().double();
        assert!(g2.is_on_curve());
    }

    #[test]
    fn add_commutativity() {
        let g = G1::generator();
        let g2 = g.double();
        assert_eq!(g + g2, g2 + g);
    }

    #[test]
    fn add_associativity() {
        let g = G1::generator();
        let g2 = g.double();
        let g3 = g2 + g;
        // (G + 2G) + 3G == G + (2G + 3G)
        assert_eq!((g + g2) + g3, g + (g2 + g3));
    }

    #[test]
    fn scalar_mul_one() {
        let g = G1::generator();
        assert_eq!(g.scalar_mul(&[1, 0, 0, 0]), g);
    }

    #[test]
    fn scalar_mul_two() {
        let g = G1::generator();
        assert_eq!(g.scalar_mul(&[2, 0, 0, 0]), g.double());
    }

    #[test]
    fn scalar_mul_three() {
        let g = G1::generator();
        assert_eq!(g.scalar_mul(&[3, 0, 0, 0]), g.double() + g);
    }

    #[test]
    fn scalar_mul_order_gives_identity() {
        // r·G = O (G1의 위수가 r)
        // r = BN254 scalar field order
        let g = G1::generator();
        let r = [
            0x43e1f593f0000001,
            0x2833e84879b97091,
            0xb85045b68181585d,
            0x30644e72e131a029,
        ];
        assert_eq!(g.scalar_mul(&r), G1::identity());
    }

    #[test]
    fn to_affine_roundtrip() {
        let g = G1::generator();
        let g3 = (g + g + g).to_affine();
        assert!(g3.is_on_curve());
        // affine → jacobian → affine
        assert_eq!(g3.to_projective().to_affine(), g3);
    }

    #[test]
    fn scalar_mul_distributive() {
        // 5G = 2G + 3G
        let g = G1::generator();
        assert_eq!(
            g.scalar_mul(&[5, 0, 0, 0]),
            g.scalar_mul(&[2, 0, 0, 0]) + g.scalar_mul(&[3, 0, 0, 0])
        );
    }
}
