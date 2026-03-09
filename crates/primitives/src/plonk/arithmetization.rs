// PLONKish Arithmetization — 범용 게이트와 제약 시스템
//
// R1CS vs PLONKish:
//   R1CS:     (Σ aᵢsᵢ)(Σ bᵢsᵢ) = (Σ cᵢsᵢ)    — 곱셈 전용
//   PLONKish: q_L·a + q_R·b + q_O·c + q_M·a·b + q_C = 0  — 범용
//
// 장점:
//   - selector(q_L, q_R, ...)로 게이트 유형을 선택
//   - 덧셈과 곱셈을 하나의 제약으로 표현 가능
//   - custom gate 확장 가능 (q_M=1, q_L=1 → a·b + a = c)
//
// 구조:
//   - PlonkGate: 5개의 selector 계수
//   - PlonkConstraintSystem: 변수 풀 + 게이트 인스턴스 + copy constraints

use crate::field::Fr;
use crate::qap::Polynomial;
use super::Domain;

// ── Wire Position ─────────────────────────────────────────

/// Wire column: 각 게이트에는 3개의 wire (A=left, B=right, C=output)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Column {
    A,
    B,
    C,
}

/// Wire position = (column, row)
///
/// n개의 게이트가 있으면 총 3n개의 wire position:
///   (A,0), (A,1), ..., (A,n-1)
///   (B,0), (B,1), ..., (B,n-1)
///   (C,0), (C,1), ..., (C,n-1)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WirePosition {
    pub column: Column,
    pub row: usize,
}

/// 변수 풀의 인덱스
pub type WireIndex = usize;

// ── PlonkGate ─────────────────────────────────────────────

/// PLONKish 게이트: q_L·a + q_R·b + q_O·c + q_M·a·b + q_C = 0
///
/// 5개의 selector 계수로 게이트의 유형을 결정한다.
#[derive(Debug, Clone, Copy)]
pub struct PlonkGate {
    pub q_l: Fr,
    pub q_r: Fr,
    pub q_o: Fr,
    pub q_m: Fr,
    pub q_c: Fr,
}

impl PlonkGate {
    /// 덧셈 게이트: a + b = c
    /// 1·a + 1·b + (-1)·c + 0·a·b + 0 = 0
    pub fn addition_gate() -> Self {
        PlonkGate {
            q_l: Fr::ONE,
            q_r: Fr::ONE,
            q_o: -Fr::ONE,
            q_m: Fr::ZERO,
            q_c: Fr::ZERO,
        }
    }

    /// 곱셈 게이트: a · b = c
    /// 0·a + 0·b + (-1)·c + 1·a·b + 0 = 0
    pub fn multiplication_gate() -> Self {
        PlonkGate {
            q_l: Fr::ZERO,
            q_r: Fr::ZERO,
            q_o: -Fr::ONE,
            q_m: Fr::ONE,
            q_c: Fr::ZERO,
        }
    }

    /// 상수 게이트: a = c
    /// 1·a + 0·b + 0·c + 0·a·b + (-c) = 0
    pub fn constant_gate(c: Fr) -> Self {
        PlonkGate {
            q_l: Fr::ONE,
            q_r: Fr::ZERO,
            q_o: Fr::ZERO,
            q_m: Fr::ZERO,
            q_c: -c,
        }
    }

    /// 불린 게이트: a·(1-a) = 0
    /// a - a² = 0 → 1·a + 0·b + 0·c + (-1)·a·b + 0 = 0
    /// (b = a 를 copy constraint로 강제)
    pub fn boolean_gate() -> Self {
        PlonkGate {
            q_l: Fr::ONE,
            q_r: Fr::ZERO,
            q_o: Fr::ZERO,
            q_m: -Fr::ONE,
            q_c: Fr::ZERO,
        }
    }

    /// 더미 게이트: 0 = 0 (패딩용, 항상 만족)
    pub fn dummy_gate() -> Self {
        PlonkGate {
            q_l: Fr::ZERO,
            q_r: Fr::ZERO,
            q_o: Fr::ZERO,
            q_m: Fr::ZERO,
            q_c: Fr::ZERO,
        }
    }

    /// 게이트 방정식이 주어진 wire 값으로 만족되는지 확인
    pub fn is_satisfied(&self, a: Fr, b: Fr, c: Fr) -> bool {
        let result = self.q_l * a + self.q_r * b + self.q_o * c
            + self.q_m * a * b + self.q_c;
        result.is_zero()
    }
}

// ── Gate Instance (내부) ──────────────────────────────────

/// 게이트 인스턴스: selector + wire 변수 인덱스
struct GateInstance {
    gate: PlonkGate,
    a: WireIndex,
    b: WireIndex,
    c: WireIndex,
}

// ── Selector Polynomials ──────────────────────────────────

/// selector 다항식 모음
pub struct SelectorPolynomials {
    pub q_l: Polynomial,
    pub q_r: Polynomial,
    pub q_o: Polynomial,
    pub q_m: Polynomial,
    pub q_c: Polynomial,
    /// Lookup selector: q_lookup(ωⁱ) = 1 if gate i has lookup, 0 otherwise
    pub q_lookup: Polynomial,
}

// ── PlonkConstraintSystem ─────────────────────────────────

/// PLONKish 제약 시스템
///
/// 사용 순서:
///   1. alloc_variable(value) — 변수 할당
///   2. add_gate(gate, a, b, c) — 게이트 추가
///   3. copy_constraint(p, q) — wire 동치 관계
///   4. register_table() / add_lookup() — lookup 제약 (선택)
///   5. pad_to_power_of_two() — 패딩
///   6. selector_polynomials() / wire_polynomials() — 다항식 추출
pub struct PlonkConstraintSystem {
    /// 변수 풀: values[i] = i번째 변수의 값
    pub values: Vec<Fr>,
    /// 게이트 인스턴스 목록
    gates: Vec<GateInstance>,
    /// Copy constraints: 같은 값이어야 하는 wire position 쌍
    copy_constraints: Vec<(WirePosition, WirePosition)>,
    /// 공개 입력 수 (처음 num_public_inputs개 변수가 공개)
    pub num_public_inputs: usize,
    /// Lookup 테이블: 각 테이블의 값 목록
    pub(crate) lookup_tables: Vec<Vec<Fr>>,
    /// Lookup 제약: (gate row, wire column, table id)
    pub(crate) lookup_entries: Vec<(usize, Column, usize)>,
}

impl PlonkConstraintSystem {
    /// 빈 제약 시스템 생성
    pub fn new() -> Self {
        PlonkConstraintSystem {
            values: Vec::new(),
            gates: Vec::new(),
            copy_constraints: Vec::new(),
            num_public_inputs: 0,
            lookup_tables: Vec::new(),
            lookup_entries: Vec::new(),
        }
    }

    /// 변수 할당 (비공개)
    pub fn alloc_variable(&mut self, value: Fr) -> WireIndex {
        let idx = self.values.len();
        self.values.push(value);
        idx
    }

    /// 공개 입력 변수 할당
    pub fn alloc_public_input(&mut self, value: Fr) -> WireIndex {
        let idx = self.alloc_variable(value);
        self.num_public_inputs += 1;
        idx
    }

    /// 게이트 인스턴스 추가
    ///
    /// gate: selector 계수
    /// a, b, c: 각 wire에 할당할 변수 인덱스
    pub fn add_gate(&mut self, gate: PlonkGate, a: WireIndex, b: WireIndex, c: WireIndex) {
        self.gates.push(GateInstance { gate, a, b, c });
    }

    /// Copy constraint 추가: wire_i와 wire_j의 값이 같아야 함
    pub fn copy_constraint(&mut self, wire_i: WirePosition, wire_j: WirePosition) {
        self.copy_constraints.push((wire_i, wire_j));
    }

    /// 게이트 수
    pub fn num_gates(&self) -> usize {
        self.gates.len()
    }

    /// 특정 wire position의 값 조회
    pub fn wire_value(&self, pos: WirePosition) -> Fr {
        let gate = &self.gates[pos.row];
        let idx = match pos.column {
            Column::A => gate.a,
            Column::B => gate.b,
            Column::C => gate.c,
        };
        self.values[idx]
    }

    /// 모든 게이트 방정식이 만족되는지 확인
    pub fn is_satisfied(&self) -> bool {
        for gate_inst in &self.gates {
            let a = self.values[gate_inst.a];
            let b = self.values[gate_inst.b];
            let c = self.values[gate_inst.c];
            if !gate_inst.gate.is_satisfied(a, b, c) {
                return false;
            }
        }
        true
    }

    /// 모든 copy constraint가 만족되는지 확인
    pub fn are_copy_constraints_satisfied(&self) -> bool {
        for &(p, q) in &self.copy_constraints {
            if self.wire_value(p) != self.wire_value(q) {
                return false;
            }
        }
        true
    }

    /// Copy constraints 참조
    pub fn copy_constraints(&self) -> &[(WirePosition, WirePosition)] {
        &self.copy_constraints
    }

    /// 게이트 수를 2의 거듭제곱으로 패딩
    ///
    /// 더미 게이트(모든 selector=0)를 추가하여 도메인 크기를 맞춤.
    /// 더미 wire는 값 0인 변수를 사용.
    pub fn pad_to_power_of_two(&mut self) -> usize {
        let n = self.gates.len();
        let target = if n <= 2 {
            2
        } else {
            n.next_power_of_two()
        };

        if target > n {
            // 패딩용 dummy 변수 (값 = 0)
            let dummy = self.alloc_variable(Fr::ZERO);
            for _ in n..target {
                self.add_gate(PlonkGate::dummy_gate(), dummy, dummy, dummy);
            }
        }

        target
    }

    /// Selector 다항식 추출
    ///
    /// 각 selector의 값을 도메인 점에서 Lagrange 보간:
    ///   q_L(ωⁱ) = gates[i].gate.q_l
    pub fn selector_polynomials(&self, domain: &Domain) -> SelectorPolynomials {
        let n = domain.n;
        assert_eq!(self.gates.len(), n, "gate count must match domain size");

        let mut ql_points = Vec::with_capacity(n);
        let mut qr_points = Vec::with_capacity(n);
        let mut qo_points = Vec::with_capacity(n);
        let mut qm_points = Vec::with_capacity(n);
        let mut qc_points = Vec::with_capacity(n);
        let mut qlookup_points = Vec::with_capacity(n);

        // lookup이 있는 행 집합 구성
        let mut lookup_rows = std::collections::HashSet::new();
        for &(row, _, _) in &self.lookup_entries {
            lookup_rows.insert(row);
        }

        for i in 0..n {
            let w = domain.elements[i];
            let g = &self.gates[i].gate;
            ql_points.push((w, g.q_l));
            qr_points.push((w, g.q_r));
            qo_points.push((w, g.q_o));
            qm_points.push((w, g.q_m));
            qc_points.push((w, g.q_c));
            let qlookup_val = if lookup_rows.contains(&i) { Fr::ONE } else { Fr::ZERO };
            qlookup_points.push((w, qlookup_val));
        }

        SelectorPolynomials {
            q_l: Polynomial::lagrange_interpolate(&ql_points),
            q_r: Polynomial::lagrange_interpolate(&qr_points),
            q_o: Polynomial::lagrange_interpolate(&qo_points),
            q_m: Polynomial::lagrange_interpolate(&qm_points),
            q_c: Polynomial::lagrange_interpolate(&qc_points),
            q_lookup: Polynomial::lagrange_interpolate(&qlookup_points),
        }
    }

    // ── Lookup 관련 메서드 ─────────────────────────────────

    /// Lookup 테이블 등록, 테이블 ID 반환
    pub fn register_table(&mut self, values: Vec<Fr>) -> usize {
        let id = self.lookup_tables.len();
        self.lookup_tables.push(values);
        id
    }

    /// Lookup 제약 추가: gate `row`의 wire `column`의 값이
    /// table_id의 테이블에 있어야 함
    pub fn add_lookup(&mut self, row: usize, column: Column, table_id: usize) {
        assert!(table_id < self.lookup_tables.len(), "invalid table id");
        self.lookup_entries.push((row, column, table_id));
    }

    /// 모든 lookup 제약이 만족되는지 확인 (디버깅용)
    pub fn are_lookups_satisfied(&self) -> bool {
        for &(row, col, tid) in &self.lookup_entries {
            let val = self.wire_value(WirePosition { column: col, row });
            if !self.lookup_tables[tid].contains(&val) {
                return false;
            }
        }
        true
    }

    /// Wire 다항식 추출
    ///
    /// a(ωⁱ) = wire A의 값 at gate i
    /// b(ωⁱ) = wire B의 값 at gate i
    /// c(ωⁱ) = wire C의 값 at gate i
    pub fn wire_polynomials(&self, domain: &Domain) -> (Polynomial, Polynomial, Polynomial) {
        let n = domain.n;
        assert_eq!(self.gates.len(), n, "gate count must match domain size");

        let mut a_points = Vec::with_capacity(n);
        let mut b_points = Vec::with_capacity(n);
        let mut c_points = Vec::with_capacity(n);

        for i in 0..n {
            let w = domain.elements[i];
            a_points.push((w, self.values[self.gates[i].a]));
            b_points.push((w, self.values[self.gates[i].b]));
            c_points.push((w, self.values[self.gates[i].c]));
        }

        (
            Polynomial::lagrange_interpolate(&a_points),
            Polynomial::lagrange_interpolate(&b_points),
            Polynomial::lagrange_interpolate(&c_points),
        )
    }
}

// ── 테스트 ────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── PlonkGate 테스트 ──────────────────────────────────

    #[test]
    fn addition_gate_satisfied() {
        let gate = PlonkGate::addition_gate();
        // 3 + 4 = 7
        assert!(gate.is_satisfied(Fr::from_u64(3), Fr::from_u64(4), Fr::from_u64(7)));
        // 3 + 4 ≠ 8
        assert!(!gate.is_satisfied(Fr::from_u64(3), Fr::from_u64(4), Fr::from_u64(8)));
    }

    #[test]
    fn multiplication_gate_satisfied() {
        let gate = PlonkGate::multiplication_gate();
        // 3 * 4 = 12
        assert!(gate.is_satisfied(Fr::from_u64(3), Fr::from_u64(4), Fr::from_u64(12)));
        // 3 * 4 ≠ 11
        assert!(!gate.is_satisfied(Fr::from_u64(3), Fr::from_u64(4), Fr::from_u64(11)));
    }

    #[test]
    fn constant_gate_satisfied() {
        let gate = PlonkGate::constant_gate(Fr::from_u64(42));
        // a = 42
        assert!(gate.is_satisfied(Fr::from_u64(42), Fr::ZERO, Fr::ZERO));
        // a = 41 ✗
        assert!(!gate.is_satisfied(Fr::from_u64(41), Fr::ZERO, Fr::ZERO));
    }

    #[test]
    fn boolean_gate_satisfied() {
        let gate = PlonkGate::boolean_gate();
        // a=0: 0·(1-0)=0 → q_L·0 + q_M·0·0 = 0 ✓
        assert!(gate.is_satisfied(Fr::ZERO, Fr::ZERO, Fr::ZERO));
        // a=1: 1-1=0 → q_L·1 + q_M·1·1 = 1-1=0 ✓
        assert!(gate.is_satisfied(Fr::ONE, Fr::ONE, Fr::ZERO));
        // a=2: 2-4=-2 ≠ 0 ✗
        assert!(!gate.is_satisfied(Fr::from_u64(2), Fr::from_u64(2), Fr::ZERO));
    }

    // ── PlonkConstraintSystem 테스트 ──────────────────────

    #[test]
    fn alloc_variable() {
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(10));
        let b = cs.alloc_variable(Fr::from_u64(20));
        let c = cs.alloc_variable(Fr::from_u64(30));

        assert_eq!(a, 0);
        assert_eq!(b, 1);
        assert_eq!(c, 2);
        assert_eq!(cs.values[a], Fr::from_u64(10));
        assert_eq!(cs.values[b], Fr::from_u64(20));
        assert_eq!(cs.values[c], Fr::from_u64(30));
    }

    #[test]
    fn add_gate_check_satisfied() {
        // 2게이트 회로: (3 + 4 = 7) 후 (7 * 2 = 14)
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(3));
        let b = cs.alloc_variable(Fr::from_u64(4));
        let c = cs.alloc_variable(Fr::from_u64(7));
        let d = cs.alloc_variable(Fr::from_u64(2));
        let e = cs.alloc_variable(Fr::from_u64(14));

        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        cs.add_gate(PlonkGate::multiplication_gate(), c, d, e);

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_gates(), 2);
    }

    #[test]
    fn wrong_witness_fails() {
        // 3 + 4 = 8? → 불만족
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(3));
        let b = cs.alloc_variable(Fr::from_u64(4));
        let c = cs.alloc_variable(Fr::from_u64(8)); // wrong!

        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        assert!(!cs.is_satisfied());
    }

    #[test]
    fn pad_to_power_of_two() {
        // 3 gates → 4 after padding
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(1));
        let b = cs.alloc_variable(Fr::from_u64(2));
        let c = cs.alloc_variable(Fr::from_u64(3));

        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        cs.add_gate(PlonkGate::addition_gate(), a, b, c);

        assert_eq!(cs.num_gates(), 3);
        let n = cs.pad_to_power_of_two();
        assert_eq!(n, 4);
        assert_eq!(cs.num_gates(), 4);

        // 패딩 후에도 만족
        assert!(cs.is_satisfied());
    }

    // ── Selector / Wire 다항식 테스트 ─────────────────────

    #[test]
    fn selector_polynomials_at_domain() {
        // add gate + mul gate → 패딩 → 도메인 위에서 selector 확인
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(3));
        let b = cs.alloc_variable(Fr::from_u64(4));
        let c = cs.alloc_variable(Fr::from_u64(7));
        let d = cs.alloc_variable(Fr::from_u64(2));
        let e = cs.alloc_variable(Fr::from_u64(14));

        cs.add_gate(PlonkGate::addition_gate(), a, b, c); // gate 0
        cs.add_gate(PlonkGate::multiplication_gate(), c, d, e); // gate 1

        let n = cs.pad_to_power_of_two(); // 2 → 2
        let domain = Domain::new(n);
        let sel = cs.selector_polynomials(&domain);

        // gate 0 (add): q_l=1, q_r=1, q_o=-1, q_m=0, q_c=0
        assert_eq!(sel.q_l.eval(domain.elements[0]), Fr::ONE);
        assert_eq!(sel.q_r.eval(domain.elements[0]), Fr::ONE);
        assert_eq!(sel.q_o.eval(domain.elements[0]), -Fr::ONE);
        assert_eq!(sel.q_m.eval(domain.elements[0]), Fr::ZERO);
        assert_eq!(sel.q_c.eval(domain.elements[0]), Fr::ZERO);

        // gate 1 (mul): q_l=0, q_r=0, q_o=-1, q_m=1, q_c=0
        assert_eq!(sel.q_l.eval(domain.elements[1]), Fr::ZERO);
        assert_eq!(sel.q_m.eval(domain.elements[1]), Fr::ONE);
    }

    #[test]
    fn wire_polynomials_at_domain() {
        let mut cs = PlonkConstraintSystem::new();
        let a = cs.alloc_variable(Fr::from_u64(3));
        let b = cs.alloc_variable(Fr::from_u64(4));
        let c = cs.alloc_variable(Fr::from_u64(7));
        let d = cs.alloc_variable(Fr::from_u64(2));
        let e = cs.alloc_variable(Fr::from_u64(14));

        cs.add_gate(PlonkGate::addition_gate(), a, b, c);
        cs.add_gate(PlonkGate::multiplication_gate(), c, d, e);

        let n = cs.pad_to_power_of_two();
        let domain = Domain::new(n);
        let (a_poly, b_poly, c_poly) = cs.wire_polynomials(&domain);

        // gate 0: a=3, b=4, c=7
        assert_eq!(a_poly.eval(domain.elements[0]), Fr::from_u64(3));
        assert_eq!(b_poly.eval(domain.elements[0]), Fr::from_u64(4));
        assert_eq!(c_poly.eval(domain.elements[0]), Fr::from_u64(7));

        // gate 1: a=7, b=2, c=14
        assert_eq!(a_poly.eval(domain.elements[1]), Fr::from_u64(7));
        assert_eq!(b_poly.eval(domain.elements[1]), Fr::from_u64(2));
        assert_eq!(c_poly.eval(domain.elements[1]), Fr::from_u64(14));
    }

    #[test]
    fn gate_equation_via_polynomials() {
        // 다항식으로 평가한 게이트 방정식이 도메인 위에서 0인지 확인
        let mut cs = PlonkConstraintSystem::new();
        let x = cs.alloc_variable(Fr::from_u64(5));
        let y = cs.alloc_variable(Fr::from_u64(3));
        let sum = cs.alloc_variable(Fr::from_u64(8));
        let prod = cs.alloc_variable(Fr::from_u64(15));

        cs.add_gate(PlonkGate::addition_gate(), x, y, sum);
        cs.add_gate(PlonkGate::multiplication_gate(), x, y, prod);

        let n = cs.pad_to_power_of_two();
        let domain = Domain::new(n);
        let sel = cs.selector_polynomials(&domain);
        let (a_poly, b_poly, c_poly) = cs.wire_polynomials(&domain);

        for i in 0..n {
            let w = domain.elements[i];
            let a = a_poly.eval(w);
            let b = b_poly.eval(w);
            let c = c_poly.eval(w);
            let result = sel.q_l.eval(w) * a
                + sel.q_r.eval(w) * b
                + sel.q_o.eval(w) * c
                + sel.q_m.eval(w) * a * b
                + sel.q_c.eval(w);
            assert!(
                result.is_zero(),
                "gate equation not zero at domain point {}",
                i
            );
        }
    }
}
