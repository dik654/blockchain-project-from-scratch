// Step 15: Plookup — lookup argument
//
// Plookup이란?
//   "이 값이 미리 정의된 테이블에 있는가?"를 증명하는 프로토콜
//   (Gabizon-Williamson, 2020)
//
// 왜 필요한가?
//   range check (0 ≤ x < 2^8)를 PLONK만으로 하면:
//     - 8비트 분해: 8개 boolean gate + 결합 gates = ~16 제약
//   Plookup으로:
//     - 256개 엔트리 테이블 1개 + lookup 1개 = O(1) 제약
//
// 핵심 아이디어:
//   1. 테이블 T = {t₀, ..., t_{n-1}} (정렬된 순서)
//   2. 조회값 f = {f₀, ..., f_{m-1}} (witness에서)
//   3. f ∪ T를 T의 순서로 정렬 → s
//   4. s를 중첩 분리: h1 = s[..n], h2 = s[n-1..] (h1[last]=h2[0])
//   5. grand product Z(x)로 정렬의 올바름 증명
//
// Grand product:
//   Z(ω⁰) = 1
//   Z(ω^(i+1)) = Z(ωⁱ) ·
//     (1+β)·(γ+fᵢ)·(γ(1+β)+tᵢ+β·tᵢ₊₁)
//     ─────────────────────────────────────────
//     (γ(1+β)+h1ᵢ+β·h1ᵢ₊₁)·(γ(1+β)+h2ᵢ+β·h2ᵢ₊₁)
//
// 의존성:
//   field::Fr — 스칼라체
//   qap::Polynomial — 다항식 (Lagrange 보간, eval)
//   plonk::Domain — 평가 도메인
//   plonk::arithmetization — PlonkConstraintSystem, Column, WirePosition

use crate::field::Fr;
use crate::qap::Polynomial;
use super::Domain;
use super::arithmetization::{PlonkConstraintSystem, WirePosition};
use std::cmp::Ordering;

// ── Fr 비교 헬퍼 ────────────────────────────────────────

/// Fr 원소 비교 (to_repr 기반, 상위 limb부터)
///
/// Fr은 Ord를 구현하지 않으므로 canonical representation으로 비교
fn fr_cmp(a: &Fr, b: &Fr) -> Ordering {
    let ar = a.to_repr();
    let br = b.to_repr();
    for i in (0..4).rev() {
        match ar[i].cmp(&br[i]) {
            Ordering::Equal => continue,
            other => return other,
        }
    }
    Ordering::Equal
}

// ── PlookupError ────────────────────────────────────────

/// Plookup 오류
#[derive(Debug)]
pub enum PlookupError {
    /// 조회 값이 테이블에 없음
    ValueNotInTable(Fr),
    /// 테이블이 비어 있음
    EmptyTable,
}

// ── LookupTable ─────────────────────────────────────────

/// 미리 정의된 lookup 테이블
///
/// 테이블의 각 값은 Fr 원소.
/// 다중 컬럼 테이블(XOR: a, b, c)은 랜덤 선형 결합으로
/// 단일 Fr 값으로 인코딩: v = a + α·b + α²·c
#[derive(Debug, Clone)]
pub struct LookupTable {
    /// 테이블 값들 (정렬된 순서)
    pub values: Vec<Fr>,
}

impl LookupTable {
    /// 값 목록으로 테이블 생성 (Fr 순서로 정렬)
    pub fn new(mut values: Vec<Fr>) -> Self {
        values.sort_by(|a, b| fr_cmp(a, b));
        LookupTable { values }
    }

    /// Range 테이블: {0, 1, 2, ..., 2^n - 1}
    ///
    /// range check에 사용: "이 값이 n비트 안에 들어가는가?"
    /// n=8 → {0, 1, ..., 255}
    pub fn range_table(n: u32) -> Self {
        assert!(n <= 20, "range table too large (max 2^20)");
        let size = 1u64 << n;
        let values: Vec<Fr> = (0..size).map(Fr::from_u64).collect();
        // 0, 1, 2, ... 순서는 이미 Fr 순서와 동일 (작은 값)
        LookupTable { values }
    }

    /// XOR 테이블: 모든 (a, b, a⊕b) 조합을 인코딩
    ///
    /// bits=4 → a, b ∈ {0..15}, 256개 엔트리
    /// 인코딩: v = a + α·b + α²·(a XOR b), α = 2^bits
    ///
    /// α = 2^bits이면 각 항이 겹치지 않아 유일하게 디코딩 가능
    pub fn xor_table(bits: u32) -> Self {
        assert!(bits <= 8, "XOR table too large (max 8 bits)");
        let size = 1u64 << bits;
        let alpha = Fr::from_u64(size);
        let alpha_sq = alpha * alpha;
        let mut values = Vec::with_capacity((size * size) as usize);

        for a in 0..size {
            for b in 0..size {
                let c = a ^ b;
                let encoded = Fr::from_u64(a) + alpha * Fr::from_u64(b)
                    + alpha_sq * Fr::from_u64(c);
                values.push(encoded);
            }
        }

        LookupTable::new(values)
    }

    /// AND 테이블: 모든 (a, b, a&b) 조합을 인코딩
    ///
    /// bits=4 → a, b ∈ {0..15}, 256개 엔트리
    /// 인코딩: v = a + α·b + α²·(a AND b), α = 2^bits
    pub fn and_table(bits: u32) -> Self {
        assert!(bits <= 8, "AND table too large (max 8 bits)");
        let size = 1u64 << bits;
        let alpha = Fr::from_u64(size);
        let alpha_sq = alpha * alpha;
        let mut values = Vec::with_capacity((size * size) as usize);

        for a in 0..size {
            for b in 0..size {
                let c = a & b;
                let encoded = Fr::from_u64(a) + alpha * Fr::from_u64(b)
                    + alpha_sq * Fr::from_u64(c);
                values.push(encoded);
            }
        }

        LookupTable::new(values)
    }

    /// 테이블 크기
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// 값이 테이블에 있는지 확인
    pub fn contains(&self, val: &Fr) -> bool {
        self.values.iter().any(|v| v == val)
    }
}

// ── Sorted List 계산 ────────────────────────────────────

/// f ∪ T를 T의 순서로 정렬하여 두 절반으로 분리 (1개 원소 중첩)
///
/// 정렬 규칙: T의 순서를 유지하면서 f의 원소를 삽입
///   T가 [t₀, t₁, ...] 이면, tᵢ와 tᵢ₊₁ 사이에
///   값이 tᵢ인 f의 원소들을 삽입
///
/// 반환: (h1, h2) — h1[last] = h2[0] (중첩)
///   h1 = sorted[..n]    (n = |T|)
///   h2 = sorted[n-1..]  (length = |f| + 1)
///
/// 중첩이 필요한 이유:
///   h1, h2의 연속 쌍이 전체 sorted list의 연속 쌍을 빠짐없이 커버해야
///   grand product가 올바르게 닫힘 (telescope to 1)
pub fn compute_sorted_list(
    f_values: &[Fr],
    table: &LookupTable,
) -> Result<(Vec<Fr>, Vec<Fr>), PlookupError> {
    if table.values.is_empty() {
        return Err(PlookupError::EmptyTable);
    }

    // f의 각 값이 T에 있는지 확인 + 빈도 맵 구축
    // (Fr에 Hash가 없으므로 Vec<(Fr, usize)>로 관리)
    let mut freq: Vec<(Fr, usize)> = Vec::new();
    for &fv in f_values {
        if !table.contains(&fv) {
            return Err(PlookupError::ValueNotInTable(fv));
        }
        if let Some(entry) = freq.iter_mut().find(|(v, _)| *v == fv) {
            entry.1 += 1;
        } else {
            freq.push((fv, 1));
        }
    }

    // T 순서대로 정렬된 리스트 구축
    let mut sorted = Vec::with_capacity(table.values.len() + f_values.len());
    for &tv in &table.values {
        sorted.push(tv);
        // f에서 이 값과 같은 것들을 삽입
        if let Some(entry) = freq.iter_mut().find(|(v, _)| *v == tv) {
            for _ in 0..entry.1 {
                sorted.push(tv);
            }
            entry.1 = 0; // consumed
        }
    }

    // h1, h2로 분리 (1개 원소 중첩 — 연속 쌍이 연결되어야 함)
    let n = table.values.len();
    let h1 = sorted[..n].to_vec();
    let h2 = sorted[n - 1..].to_vec(); // h2[0] = h1[last] (overlap)

    Ok((h1, h2))
}

// ── Grand Product Z_lookup ──────────────────────────────

/// Plookup grand product Z_lookup(x) 계산
///
/// Z(ω⁰) = 1
/// Z(ω^(i+1)) = Z(ωⁱ) ·
///   (1+β)·(γ+fᵢ)·(γ(1+β)+tᵢ+β·tᵢ₊₁)
///   ───────────────────────────────────────
///   (γ(1+β)+h1ᵢ+β·h1ᵢ₊₁)·(γ(1+β)+h2ᵢ+β·h2ᵢ₊₁)
///
/// f, t, h1, h2는 도메인 크기로 패딩된 상태
pub fn compute_lookup_grand_product(
    f: &[Fr],
    t: &[Fr],
    h1: &[Fr],
    h2: &[Fr],
    beta: Fr,
    gamma: Fr,
    domain: &Domain,
) -> Polynomial {
    let n = domain.n;
    assert_eq!(f.len(), n);
    assert_eq!(t.len(), n);
    assert_eq!(h1.len(), n);
    assert_eq!(h2.len(), n);

    let one_plus_beta = Fr::ONE + beta;
    let gamma_one_plus_beta = gamma * one_plus_beta;

    let mut z_values = Vec::with_capacity(n);
    z_values.push(Fr::ONE); // Z(ω⁰) = 1

    for i in 0..n - 1 {
        let next_i = i + 1; // h, t의 i+1번째 원소 (패딩된 범위 내)

        let num = one_plus_beta
            * (gamma + f[i])
            * (gamma_one_plus_beta + t[i] + beta * t[next_i]);

        let den = (gamma_one_plus_beta + h1[i] + beta * h1[next_i])
            * (gamma_one_plus_beta + h2[i] + beta * h2[next_i]);

        let den_inv = den.inv().expect("denominator must be invertible");
        z_values.push(z_values[i] * num * den_inv);
    }

    // Lagrange 보간으로 다항식 구성
    let points: Vec<(Fr, Fr)> = (0..n)
        .map(|i| (domain.elements[i], z_values[i]))
        .collect();
    Polynomial::lagrange_interpolate(&points)
}

/// Grand product가 닫히는지 확인 (Z가 1로 돌아오는지)
///
/// 마지막 행까지 포함한 전체 곱 = 1 확인
pub fn verify_lookup_grand_product(
    f: &[Fr],
    t: &[Fr],
    h1: &[Fr],
    h2: &[Fr],
    _z_poly: &Polynomial,
    beta: Fr,
    gamma: Fr,
    domain: &Domain,
) -> bool {
    let n = domain.n;

    let one_plus_beta = Fr::ONE + beta;
    let gamma_one_plus_beta = gamma * one_plus_beta;

    // N-1 스텝의 곱이 1인지 확인 (compute_lookup_grand_product과 동일)
    //
    // f는 N-1개의 유효 원소 (마지막 원소는 미사용)
    // t, h1, h2는 N개의 원소 (연속 쌍 N-1개)
    // 다항식 등식: ∏ num(i)/den(i) = 1 ↔ Z(ω^(N-1)) = 1
    let mut total = Fr::ONE;
    for i in 0..n - 1 {
        let num = one_plus_beta
            * (gamma + f[i])
            * (gamma_one_plus_beta + t[i] + beta * t[i + 1]);

        let den = (gamma_one_plus_beta + h1[i] + beta * h1[i + 1])
            * (gamma_one_plus_beta + h2[i] + beta * h2[i + 1]);

        let den_inv = den.inv().expect("denominator must be invertible");
        total = total * num * den_inv;
    }

    total == Fr::ONE
}

// ── PlookupProof ────────────────────────────────────────

/// Plookup 증명 데이터
pub struct PlookupProof {
    /// 조회값 다항식
    pub f_poly: Polynomial,
    /// 테이블 다항식
    pub t_poly: Polynomial,
    /// sorted list 첫 절반
    pub h1_poly: Polynomial,
    /// sorted list 둘째 절반
    pub h2_poly: Polynomial,
    /// Grand product Z_lookup(x)
    pub z_poly: Polynomial,
}

// ── 전체 파이프라인 ─────────────────────────────────────

/// PlonkConstraintSystem에서 Plookup 증명 데이터를 생성
///
/// 전체 파이프라인:
///   1. CS에서 lookup 값(f) 추출
///   2. 도메인 크기 N 결정
///   3. f를 N-1개, t를 N개로 확장 (더미 lookup = t[last])
///   4. 확장된 데이터로 sorted list 계산 → h1, h2 (각 N개)
///   5. 모두 다항식으로 보간
///   6. grand product Z_lookup 계산 (N-1 스텝)
///
/// 왜 확장이 필요한가?
///   sorted list를 확장된 데이터로 계산해야 h1, h2가 정확히
///   domain_size 길이가 되어 grand product가 올바르게 닫힘.
///   사후 패딩은 multiset 관계를 깨뜨림.
///
/// 현재는 단일 테이블(table_id=0)만 지원
pub fn compute_plookup(
    cs: &PlonkConstraintSystem,
    beta: Fr,
    gamma: Fr,
) -> PlookupProof {
    assert!(!cs.lookup_tables.is_empty(), "no lookup tables registered");

    // 1. lookup 값(f) 추출 — table_id=0인 것만
    let f_raw: Vec<Fr> = cs.lookup_entries.iter()
        .filter(|&&(_, _, tid)| tid == 0)
        .map(|&(row, col, _)| cs.wire_value(WirePosition { column: col, row }))
        .collect();

    // 2. 도메인 크기 결정
    let table_values = &cs.lookup_tables[0];
    let t_last = *table_values.last().expect("table must not be empty");
    let required = std::cmp::max(table_values.len(), f_raw.len() + 1);
    let domain_size = required.next_power_of_two().max(2);
    let domain = Domain::new(domain_size);

    // 3. f와 t를 확장
    //    t: domain_size 길이로 (t_last 반복)
    //    f: domain_size - 1 길이로 (더미 lookup = t_last)
    //
    //    |sorted| = |f_ext| + |t_ext| = (N-1) + N = 2N-1
    //    → h1 = sorted[..N], h2 = sorted[N-1..] 각각 정확히 N개
    let mut t_ext = table_values.clone();
    while t_ext.len() < domain_size { t_ext.push(t_last); }

    let mut f_ext = f_raw.clone();
    while f_ext.len() < domain_size - 1 { f_ext.push(t_last); }

    // 4. 확장된 데이터로 sorted list 계산
    let table_ext = LookupTable { values: t_ext.clone() };
    let (h1, h2) = compute_sorted_list(&f_ext, &table_ext)
        .expect("all lookup values must be in table");

    // f를 domain_size로 확장 (f[N-1]은 grand product 계산에서 미사용)
    f_ext.push(t_last);

    // 5. 다항식 보간
    let interp = |vals: &[Fr]| -> Polynomial {
        let points: Vec<(Fr, Fr)> = vals.iter().enumerate()
            .map(|(i, &v)| (domain.elements[i], v))
            .collect();
        Polynomial::lagrange_interpolate(&points)
    };

    let f_poly = interp(&f_ext);
    let t_poly = interp(&t_ext);
    let h1_poly = interp(&h1);
    let h2_poly = interp(&h2);

    // 6. grand product 계산
    let z_poly = compute_lookup_grand_product(
        &f_ext, &t_ext, &h1, &h2,
        beta, gamma, &domain,
    );

    PlookupProof { f_poly, t_poly, h1_poly, h2_poly, z_poly }
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::plonk::{Column, PlonkGate};

    // ── LookupTable 테스트 ──────────────────────────────

    #[test]
    fn range_table_values() {
        let table = LookupTable::range_table(4);
        assert_eq!(table.len(), 16);
        for i in 0..16u64 {
            assert!(table.contains(&Fr::from_u64(i)),
                "range table must contain {}", i);
        }
        assert!(!table.contains(&Fr::from_u64(16)));
    }

    #[test]
    fn range_table_8bit() {
        let table = LookupTable::range_table(8);
        assert_eq!(table.len(), 256);
        assert!(table.contains(&Fr::from_u64(0)));
        assert!(table.contains(&Fr::from_u64(255)));
        assert!(!table.contains(&Fr::from_u64(256)));
    }

    #[test]
    fn xor_table_2bit() {
        // 2비트: a, b ∈ {0,1,2,3}, 총 16개 엔트리
        let table = LookupTable::xor_table(2);
        assert_eq!(table.len(), 16);

        // (2, 3, 2^3=1): encoded = 2 + 4·3 + 16·1 = 2+12+16 = 30
        let alpha = Fr::from_u64(4);
        let alpha_sq = Fr::from_u64(16);
        let encoded = Fr::from_u64(2) + alpha * Fr::from_u64(3)
            + alpha_sq * Fr::from_u64(1);
        assert!(table.contains(&encoded),
            "XOR table must contain (2, 3, 2^3=1)");

        // (0, 0, 0): encoded = 0
        assert!(table.contains(&Fr::ZERO),
            "XOR table must contain (0, 0, 0)");
    }

    #[test]
    fn and_table_2bit() {
        let table = LookupTable::and_table(2);
        assert_eq!(table.len(), 16);

        // (3, 2, 3&2=2): encoded = 3 + 4·2 + 16·2 = 3+8+32 = 43
        let alpha = Fr::from_u64(4);
        let alpha_sq = Fr::from_u64(16);
        let encoded = Fr::from_u64(3) + alpha * Fr::from_u64(2)
            + alpha_sq * Fr::from_u64(2);
        assert!(table.contains(&encoded),
            "AND table must contain (3, 2, 3&2=2)");
    }

    #[test]
    fn table_contains() {
        let table = LookupTable::range_table(8);
        assert!(table.contains(&Fr::from_u64(100)));
        assert!(table.contains(&Fr::from_u64(0)));
        assert!(table.contains(&Fr::from_u64(255)));
        assert!(!table.contains(&Fr::from_u64(256)));
        assert!(!table.contains(&Fr::from_u64(1000)));
    }

    // ── Sorted List 테스트 ──────────────────────────────

    #[test]
    fn sorted_list_simple() {
        // T=[0,1,2,3], f=[1,3]
        let table = LookupTable::range_table(2); // {0,1,2,3}
        let f = vec![Fr::from_u64(1), Fr::from_u64(3)];

        let (h1, h2) = compute_sorted_list(&f, &table).unwrap();

        // sorted = [0, 1, 1, 2, 3, 3]
        // h1 = sorted[..4] = [0, 1, 1, 2]
        // h2 = sorted[3..] = [2, 3, 3]  (overlap at sorted[3]=2)
        assert_eq!(h1.len(), 4); // |T|
        assert_eq!(h2.len(), 3); // |f| + 1 (overlap)

        // h1
        assert_eq!(h1[0], Fr::from_u64(0));
        assert_eq!(h1[1], Fr::from_u64(1));
        assert_eq!(h1[2], Fr::from_u64(1));
        assert_eq!(h1[3], Fr::from_u64(2));
        // h2 = [2, 3, 3], h2[0] = h1[last] (overlap)
        assert_eq!(h2[0], Fr::from_u64(2));
        assert_eq!(h2[1], Fr::from_u64(3));
        assert_eq!(h2[2], Fr::from_u64(3));
    }

    #[test]
    fn sorted_list_all_same() {
        // T=[0,1,2], f=[1,1,1]
        let table = LookupTable::new(vec![
            Fr::from_u64(0), Fr::from_u64(1), Fr::from_u64(2),
        ]);
        let f = vec![Fr::from_u64(1), Fr::from_u64(1), Fr::from_u64(1)];

        let (h1, h2) = compute_sorted_list(&f, &table).unwrap();

        // sorted = [0, 1, 1, 1, 1, 2]
        // h1 = sorted[..3] = [0, 1, 1]
        // h2 = sorted[2..] = [1, 1, 1, 2]  (overlap at sorted[2]=1)
        assert_eq!(h1.len(), 3); // |T|
        assert_eq!(h2.len(), 4); // |f| + 1 (overlap)

        assert_eq!(h1[0], Fr::from_u64(0));
        assert_eq!(h1[1], Fr::from_u64(1));
        assert_eq!(h1[2], Fr::from_u64(1));
        assert_eq!(h2[0], Fr::from_u64(1)); // overlap: h1[last] = h2[0]
        assert_eq!(h2[1], Fr::from_u64(1));
        assert_eq!(h2[2], Fr::from_u64(1));
        assert_eq!(h2[3], Fr::from_u64(2));
    }

    #[test]
    fn sorted_list_not_in_table() {
        let table = LookupTable::range_table(2); // {0,1,2,3}
        let f = vec![Fr::from_u64(5)]; // not in table!

        let result = compute_sorted_list(&f, &table);
        assert!(result.is_err());
        match result {
            Err(PlookupError::ValueNotInTable(v)) => {
                assert_eq!(v, Fr::from_u64(5));
            }
            _ => panic!("expected ValueNotInTable error"),
        }
    }

    // ── Grand Product 테스트 ────────────────────────────

    /// 확장 + sorted list + grand product 헬퍼
    ///
    /// 테스트에서 반복되는 패턴을 추출:
    ///   1. 도메인 크기 N 결정
    ///   2. f를 N-1, t를 N으로 확장 (t_last로 채움)
    ///   3. 확장된 데이터로 sorted list 계산 → h1, h2 (각 N)
    ///   4. f를 N으로 확장 (마지막 원소 미사용)
    ///   5. grand product 계산 + 검증
    fn extend_and_verify(
        f_raw: &[Fr],
        table: &LookupTable,
        beta: Fr,
        gamma: Fr,
    ) -> bool {
        let t_last = *table.values.last().unwrap();
        let required = std::cmp::max(table.len(), f_raw.len() + 1);
        let n = required.next_power_of_two().max(2);
        let domain = Domain::new(n);

        // t를 N으로 확장
        let mut t_ext = table.values.clone();
        while t_ext.len() < n { t_ext.push(t_last); }

        // f를 N-1로 확장 (더미 lookup = t_last)
        let mut f_ext: Vec<Fr> = f_raw.to_vec();
        while f_ext.len() < n - 1 { f_ext.push(t_last); }

        // 확장된 데이터로 sorted list 계산
        let table_ext = LookupTable { values: t_ext.clone() };
        let (h1, h2) = compute_sorted_list(&f_ext, &table_ext).unwrap();

        // f를 N으로 확장 (f[N-1]은 미사용)
        f_ext.push(t_last);

        let z = compute_lookup_grand_product(
            &f_ext, &t_ext, &h1, &h2,
            beta, gamma, &domain,
        );

        verify_lookup_grand_product(
            &f_ext, &t_ext, &h1, &h2,
            &z, beta, gamma, &domain,
        )
    }

    #[test]
    fn grand_product_simple() {
        // T=[0,1,2,3], f=[1,2]
        let table = LookupTable::range_table(2);
        let f = vec![Fr::from_u64(1), Fr::from_u64(2)];

        let beta = Fr::from_u64(7);
        let gamma = Fr::from_u64(11);

        assert!(extend_and_verify(&f, &table, beta, gamma),
            "grand product must close for valid lookup");
    }

    #[test]
    fn grand_product_range_8bit() {
        // 256개 테이블, f=[0, 42, 100, 255]
        let table = LookupTable::range_table(8);
        let f = vec![
            Fr::from_u64(0), Fr::from_u64(42),
            Fr::from_u64(100), Fr::from_u64(255),
        ];

        let beta = Fr::from_u64(13);
        let gamma = Fr::from_u64(17);

        assert!(extend_and_verify(&f, &table, beta, gamma),
            "grand product must close for 8-bit range lookup");
    }

    #[test]
    fn grand_product_violation() {
        // f=[5]가 T=[0,1,2,3]에 없으면 sorted_list 에러
        let table = LookupTable::range_table(2);
        let f = vec![Fr::from_u64(5)];

        let result = compute_sorted_list(&f, &table);
        assert!(result.is_err(), "value not in table should fail");
    }

    // ── CS 통합 테스트 ──────────────────────────────────

    #[test]
    fn cs_register_and_lookup() {
        let mut cs = PlonkConstraintSystem::new();

        // range table 등록
        let table = LookupTable::range_table(8);
        let tid = cs.register_table(table.values.clone());

        // 변수 할당 + 게이트
        let x = cs.alloc_variable(Fr::from_u64(42));
        let dummy = cs.alloc_variable(Fr::ZERO);
        cs.add_gate(PlonkGate::dummy_gate(), x, dummy, dummy);

        // lookup 추가: gate 0의 wire A가 테이블에 있어야 함
        cs.add_lookup(0, Column::A, tid);

        assert!(cs.are_lookups_satisfied(),
            "42 is in range [0, 255]");

        // 실패 케이스: 테이블에 없는 값
        let mut cs2 = PlonkConstraintSystem::new();
        let tid2 = cs2.register_table(table.values.clone());
        let y = cs2.alloc_variable(Fr::from_u64(256)); // out of range!
        let dummy2 = cs2.alloc_variable(Fr::ZERO);
        cs2.add_gate(PlonkGate::dummy_gate(), y, dummy2, dummy2);
        cs2.add_lookup(0, Column::A, tid2);

        assert!(!cs2.are_lookups_satisfied(),
            "256 is NOT in range [0, 255]");
    }

    #[test]
    fn cs_q_lookup_selector() {
        // 4개 게이트 중 gate 1만 lookup
        let mut cs = PlonkConstraintSystem::new();
        let table = LookupTable::range_table(4);
        let tid = cs.register_table(table.values);

        let a = cs.alloc_variable(Fr::from_u64(1));
        let b = cs.alloc_variable(Fr::from_u64(2));
        let c = cs.alloc_variable(Fr::from_u64(3));
        let d = cs.alloc_variable(Fr::from_u64(5));

        cs.add_gate(PlonkGate::addition_gate(), a, b, c); // gate 0: no lookup
        cs.add_gate(PlonkGate::dummy_gate(), d, a, a);     // gate 1: lookup
        cs.add_gate(PlonkGate::addition_gate(), a, b, c); // gate 2: no lookup
        cs.add_gate(PlonkGate::addition_gate(), a, b, c); // gate 3: no lookup

        cs.add_lookup(1, Column::A, tid); // gate 1에만 lookup

        let domain = Domain::new(4);
        let sel = cs.selector_polynomials(&domain);

        assert_eq!(sel.q_lookup.eval(domain.elements[0]), Fr::ZERO,
            "gate 0: no lookup");
        assert_eq!(sel.q_lookup.eval(domain.elements[1]), Fr::ONE,
            "gate 1: has lookup");
        assert_eq!(sel.q_lookup.eval(domain.elements[2]), Fr::ZERO,
            "gate 2: no lookup");
        assert_eq!(sel.q_lookup.eval(domain.elements[3]), Fr::ZERO,
            "gate 3: no lookup");
    }

    // ── End-to-End 테스트 ───────────────────────────────

    #[test]
    fn plookup_xor_table() {
        // XOR(1, 2) = 3 을 lookup으로 증명
        let mut cs = PlonkConstraintSystem::new();

        let xor_table = LookupTable::xor_table(2);
        let tid = cs.register_table(xor_table.values);

        // (1, 2, 1^2=3) 인코딩: 1 + 4·2 + 16·3 = 1+8+48 = 57
        let alpha = Fr::from_u64(4);
        let alpha_sq = Fr::from_u64(16);
        let encoded = Fr::from_u64(1) + alpha * Fr::from_u64(2)
            + alpha_sq * Fr::from_u64(3);

        let enc_var = cs.alloc_variable(encoded);
        let dummy = cs.alloc_variable(Fr::ZERO);
        cs.add_gate(PlonkGate::dummy_gate(), enc_var, dummy, dummy);
        cs.add_lookup(0, Column::A, tid);

        assert!(cs.are_lookups_satisfied());

        let beta = Fr::from_u64(7);
        let gamma = Fr::from_u64(11);
        let proof = compute_plookup(&cs, beta, gamma);

        // Z(ω⁰) = 1 확인
        let plookup_domain_size = {
            let table_len = cs.lookup_tables[0].len();
            let f_len = 1; // 하나의 lookup entry
            let required = std::cmp::max(table_len, f_len) + 1;
            required.next_power_of_two().max(2)
        };
        let plookup_domain = Domain::new(plookup_domain_size);
        assert_eq!(proof.z_poly.eval(plookup_domain.elements[0]), Fr::ONE,
            "Z(omega^0) must be 1");
    }

    #[test]
    fn plookup_range_check_end_to_end() {
        // 여러 값의 range check: 0 ≤ x < 16
        let mut cs = PlonkConstraintSystem::new();

        let table = LookupTable::range_table(4); // {0..15}
        let tid = cs.register_table(table.values);

        let vals = [0u64, 5, 10, 15];
        let dummy = cs.alloc_variable(Fr::ZERO);

        for (i, &v) in vals.iter().enumerate() {
            let x = cs.alloc_variable(Fr::from_u64(v));
            cs.add_gate(PlonkGate::dummy_gate(), x, dummy, dummy);
            cs.add_lookup(i, Column::A, tid);
        }

        assert!(cs.are_lookups_satisfied());

        let beta = Fr::from_u64(19);
        let gamma = Fr::from_u64(23);
        let proof = compute_plookup(&cs, beta, gamma);

        // grand product가 닫히는지 간접 확인: Z(ω⁰) = 1
        let table_len = cs.lookup_tables[0].len();
        let f_len = vals.len();
        let required = std::cmp::max(table_len, f_len + 1);
        let domain_size = required.next_power_of_two().max(2);
        let domain = Domain::new(domain_size);

        assert_eq!(proof.z_poly.eval(domain.elements[0]), Fr::ONE);

        // extend_and_verify로 독립 검증
        let f_values: Vec<Fr> = vals.iter().map(|&v| Fr::from_u64(v)).collect();
        let table_vals = cs.lookup_tables[0].clone();
        let lookup_table = LookupTable { values: table_vals };

        assert!(extend_and_verify(&f_values, &lookup_table, beta, gamma),
            "end-to-end range check must pass");
    }
}
