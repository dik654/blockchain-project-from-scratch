// Step 08c: Schnorr 서명 — G1 위의 이산로그 기반 전자서명
//
// 왜 Schnorr인가 (vs EdDSA):
//   EdDSA는 별도의 커브(ed-on-bn254)가 필요 — 새로운 커브를 구현해야 함
//   Schnorr은 임의의 그룹 위에서 동작 → Step 05의 G1을 그대로 재사용
//
// 서명: σ = (R, s)
//   R = k·G           (난스의 공개 부분)
//   e = H(R || m || pk)  (Fiat-Shamir 챌린지)
//   s = k + e·sk      (응답)
//
// 검증: s·G == R + e·pk
//   정당성: s·G = (k + e·sk)·G = k·G + e·sk·G = R + e·pk ✓
//
// 보안 기반: ECDLP on BN254 G1 (≈ 2^128 보안)
//
// 사용처:
//   Step 26: 트랜잭션 서명 (송금 인증)
//   Step 30: Attestation 서명 (합의)

use crate::field::Fr;
use crate::curve::g1::{G1, G1Affine};
use crate::hash::poseidon::poseidon_hash;

// ── 키 타입 ─────────────────────────────────────────────

/// 비밀키: Fr 스칼라 (랜덤)
///
/// 보안: pk에서 sk를 복원하는 것 = ECDLP ≈ 2^128 연산
pub struct SecretKey(pub Fr);

/// 공개키: G1 점 (sk·G)
pub struct PublicKey(pub G1);

/// 서명: (R, s)
///
/// R: 난스의 공개 부분 (k·G의 affine 좌표)
/// s: 챌린지에 대한 응답 (k + e·sk)
pub struct Signature {
    pub r: G1Affine,
    pub s: Fr,
}

// ── 키 생성 ─────────────────────────────────────────────

impl SecretKey {
    /// 스칼라로부터 비밀키 생성
    ///
    /// 프로덕션에서는 안전한 난수 생성기로 sk를 선택해야 함
    /// (여기서는 교육 목적으로 호출자가 직접 Fr 값을 제공)
    pub fn from_scalar(sk: Fr) -> Self {
        assert!(!sk.is_zero(), "secret key must not be zero");
        SecretKey(sk)
    }

    /// 공개키 = sk · G (생성자의 스칼라 곱)
    pub fn public_key(&self) -> PublicKey {
        PublicKey(G1::generator().scalar_mul(&self.0.to_repr()))
    }
}

// ── 챌린지 해시 ─────────────────────────────────────────

/// Fiat-Shamir 챌린지: e = H(R || m || pk)
///
/// 대화식 Σ-프로토콜에서 검증자가 보내는 랜덤 챌린지를
/// 해시로 대체하여 비대화식 서명 스킴으로 변환
///
/// R, pk의 좌표(Fp)를 Fr로 인코딩하여 Poseidon 입력으로 사용:
///   Fr::from_raw(fp.0) — Fp의 내부 표현을 Fr 값으로 재해석
///   (같은 크기의 254-bit 체이므로 결정론적·충돌 방지 인코딩)
fn challenge_hash(r_point: &G1Affine, message: Fr, pk: &G1Affine) -> Fr {
    // R = (rx, ry) → H(rx, ry)
    let rx = Fr::from_raw(r_point.x.0);
    let ry = Fr::from_raw(r_point.y.0);
    let r_hash = poseidon_hash(rx, ry);

    // pk = (pkx, pky) → H(pkx, pky)
    let pkx = Fr::from_raw(pk.x.0);
    let pky = Fr::from_raw(pk.y.0);
    let pk_hash = poseidon_hash(pkx, pky);

    // e = H(r_hash, H(message, pk_hash))
    let msg_hash = poseidon_hash(message, pk_hash);
    poseidon_hash(r_hash, msg_hash)
}

// ── 서명 ────────────────────────────────────────────────

/// Schnorr 서명 생성
///
/// 1. R = nonce · G                 (난스의 공개 부분)
/// 2. e = H(R || m || pk)           (Fiat-Shamir 챌린지)
/// 3. s = nonce + e · sk            (응답)
///
/// ⚠ nonce는 반드시 매번 다른 랜덤 값이어야 함!
///   같은 nonce로 두 메시지에 서명하면 sk가 즉시 노출됨:
///   s₁ - s₂ = (e₁ - e₂) · sk → sk = (s₁ - s₂) / (e₁ - e₂)
pub fn sign(sk: &SecretKey, message: Fr, nonce: Fr) -> Signature {
    assert!(!nonce.is_zero(), "nonce must not be zero");

    // R = k · G
    let r_point = G1::generator().scalar_mul(&nonce.to_repr());
    let r_affine = r_point.to_affine();

    // e = H(R || m || pk)
    let pk = sk.public_key();
    let pk_affine = pk.0.to_affine();
    let e = challenge_hash(&r_affine, message, &pk_affine);

    // s = k + e · sk  (Fr 산술)
    let s = nonce + e * sk.0;

    Signature { r: r_affine, s }
}

/// Schnorr 서명 검증
///
/// 1. e = H(R || m || pk)
/// 2. s · G == R + e · pk ?
///
/// 정당성 증명:
///   s·G = (k + e·sk)·G = k·G + e·(sk·G) = R + e·pk ✓
pub fn verify(pk: &PublicKey, message: Fr, sig: &Signature) -> bool {
    let pk_affine = pk.0.to_affine();
    let e = challenge_hash(&sig.r, message, &pk_affine);

    // 좌변: s · G
    let s_g = G1::generator().scalar_mul(&sig.s.to_repr());

    // 우변: R + e · pk
    let e_pk = pk.0.scalar_mul(&e.to_repr());
    let r_plus_e_pk = sig.r.to_projective().add(&e_pk);

    s_g == r_plus_e_pk
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn test_keypair() -> (SecretKey, PublicKey) {
        let sk = SecretKey::from_scalar(Fr::from_u64(42));
        let pk = sk.public_key();
        (sk, pk)
    }

    #[test]
    fn sign_and_verify() {
        let (sk, pk) = test_keypair();
        let msg = Fr::from_u64(123);
        let nonce = Fr::from_u64(7777);

        let sig = sign(&sk, msg, nonce);
        assert!(verify(&pk, msg, &sig));
    }

    #[test]
    fn wrong_message_fails() {
        let (sk, pk) = test_keypair();
        let nonce = Fr::from_u64(7777);

        let sig = sign(&sk, Fr::from_u64(123), nonce);
        assert!(!verify(&pk, Fr::from_u64(456), &sig));
    }

    #[test]
    fn wrong_pubkey_fails() {
        let (sk, _pk) = test_keypair();
        let other_sk = SecretKey::from_scalar(Fr::from_u64(99));
        let other_pk = other_sk.public_key();

        let msg = Fr::from_u64(123);
        let nonce = Fr::from_u64(7777);

        let sig = sign(&sk, msg, nonce);
        assert!(!verify(&other_pk, msg, &sig));
    }

    #[test]
    fn tampered_r_fails() {
        let (sk, pk) = test_keypair();
        let msg = Fr::from_u64(123);
        let nonce = Fr::from_u64(7777);

        let sig = sign(&sk, msg, nonce);

        // R을 다른 점으로 교체
        let fake_r = G1::generator().scalar_mul(&[999, 0, 0, 0]).to_affine();
        let tampered = Signature { r: fake_r, s: sig.s };
        assert!(!verify(&pk, msg, &tampered));
    }

    #[test]
    fn tampered_s_fails() {
        let (sk, pk) = test_keypair();
        let msg = Fr::from_u64(123);
        let nonce = Fr::from_u64(7777);

        let sig = sign(&sk, msg, nonce);

        // s를 다른 값으로 교체
        let tampered = Signature { r: sig.r, s: Fr::from_u64(1) };
        assert!(!verify(&pk, msg, &tampered));
    }

    #[test]
    fn different_messages_different_signatures() {
        let (sk, _pk) = test_keypair();
        let nonce1 = Fr::from_u64(111);
        let nonce2 = Fr::from_u64(222);

        let sig1 = sign(&sk, Fr::from_u64(1), nonce1);
        let sig2 = sign(&sk, Fr::from_u64(2), nonce2);

        assert_ne!(sig1.s, sig2.s);
    }

    #[test]
    fn deterministic_same_inputs() {
        let (sk, _pk) = test_keypair();
        let msg = Fr::from_u64(123);
        let nonce = Fr::from_u64(7777);

        let sig1 = sign(&sk, msg, nonce);
        let sig2 = sign(&sk, msg, nonce);

        assert_eq!(sig1.r, sig2.r);
        assert_eq!(sig1.s, sig2.s);
    }

    #[test]
    fn public_key_on_curve() {
        let (_sk, pk) = test_keypair();
        assert!(pk.0.is_on_curve());
    }
}
