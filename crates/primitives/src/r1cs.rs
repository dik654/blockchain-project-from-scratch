// Step 09: R1CS (Rank-1 Constraint System)
//
// ZK 증명의 "중간 표현(IR)":
//   프로그램 → R1CS → QAP → Groth16
//
// 핵심 아이디어:
//   모든 계산을 "곱셈 하나"의 형태로 분해:
//   ⟨a, s⟩ · ⟨b, s⟩ = ⟨c, s⟩
//
//   덧셈은 선형결합으로 흡수 → 제약 0개
//   곱셈 하나 = 제약 1개
//
// 변수 종류:
//   One — 상수 1 (선형결합에서 상수항 표현용)
//   Instance — 공개 입력/출력 (검증자가 아는 값)
//   Witness — 비공개 입력 (증명자만 아는 값)

use crate::field::Fr;

// ── 변수 ────────────────────────────────────────────────

/// R1CS 변수
///
/// witness 벡터 s = [1, instance₁, ..., instanceₗ, witness₁, ..., witnessₘ]
/// 에서의 위치를 나타냄
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Variable {
    /// 상수 1 — s[0]에 항상 1이 들어 있음
    /// 선형결합에서 상수항을 표현: 5 = 5 · One
    One,
    /// 공개 입력/출력 — 검증자가 알고 있는 값
    Instance(usize),
    /// 비공개 입력 — 증명자만 아는 값 (ZK의 핵심)
    Witness(usize),
}

impl Variable {
    /// witness 벡터에서의 인덱스
    ///
    /// 배치: [One, Instance(0), Instance(1), ..., Witness(0), Witness(1), ...]
    fn index(&self, num_instance: usize) -> usize {
        match self {
            Variable::One => 0,
            Variable::Instance(i) => 1 + i,
            Variable::Witness(i) => 1 + num_instance + i,
        }
    }
}

// ── 선형결합 (Linear Combination) ───────────────────────

/// 선형결합: Σ cᵢ · xᵢ
///
/// R1CS 제약의 각 항(A, B, C)은 선형결합으로 표현됨
/// 덧셈은 선형결합 내에서 "무료" — 새 제약 없이 표현 가능
///
/// 예: 3x + 5y + 7 = [(x, 3), (y, 5), (One, 7)]
#[derive(Debug, Clone)]
pub struct LinearCombination {
    pub terms: Vec<(Variable, Fr)>,
}

impl LinearCombination {
    /// 빈 선형결합 (= 0)
    pub fn zero() -> Self {
        LinearCombination { terms: vec![] }
    }

    /// 단일 변수: 1 · var
    pub fn from(var: Variable) -> Self {
        LinearCombination {
            terms: vec![(var, Fr::ONE)],
        }
    }

    /// 항 추가 (builder): + coeff · var
    pub fn add(mut self, coeff: Fr, var: Variable) -> Self {
        self.terms.push((var, coeff));
        self
    }

    /// 항 추가 (in-place): + coeff · var
    pub fn add_assign(&mut self, coeff: Fr, var: Variable) {
        self.terms.push((var, coeff));
    }

    /// witness 벡터에 대해 선형결합을 평가: Σ cᵢ · s[index(xᵢ)]
    fn evaluate(&self, values: &[Fr], num_instance: usize) -> Fr {
        let mut sum = Fr::ZERO;
        for &(var, coeff) in &self.terms {
            sum = sum + coeff * values[var.index(num_instance)];
        }
        sum
    }
}

// ── 제약 시스템 ────────────────────────────────────────

/// R1CS 제약 시스템
///
/// 제약의 형태: ⟨A, s⟩ · ⟨B, s⟩ = ⟨C, s⟩
/// A, B, C는 각각 LinearCombination
///
/// 빌더 패턴으로 사용:
///   1. alloc_instance / alloc_witness로 변수 할당
///   2. enforce()로 제약 추가
///   3. is_satisfied()로 모든 제약 만족 확인
///   4. to_matrices()로 (A, B, C) 희소 행렬 추출
pub struct ConstraintSystem {
    /// witness 벡터: [1, instance₁, ..., witness₁, ...]
    pub values: Vec<Fr>,
    pub num_instance: usize,
    pub num_witness: usize,
    /// 제약 목록: (A, B, C) 선형결합 트리플
    pub constraints: Vec<(LinearCombination, LinearCombination, LinearCombination)>,
}

impl ConstraintSystem {
    /// 빈 제약 시스템 생성
    ///
    /// values[0] = 1 (One 변수)
    pub fn new() -> Self {
        ConstraintSystem {
            values: vec![Fr::ONE], // s[0] = 1
            num_instance: 0,
            num_witness: 0,
            constraints: vec![],
        }
    }

    /// 공개 변수(instance) 할당
    ///
    /// 검증자가 아는 값. 증명의 공개 입력/출력이 됨.
    /// instance는 witness보다 먼저 할당해야 함.
    pub fn alloc_instance(&mut self, value: Fr) -> Variable {
        let idx = self.num_instance;
        self.num_instance += 1;
        // instance는 One 바로 뒤에 배치
        // values = [1, inst0, inst1, ..., wit0, wit1, ...]
        self.values.insert(1 + idx, value);
        Variable::Instance(idx)
    }

    /// 비공개 변수(witness) 할당
    ///
    /// 증명자만 아는 값. ZK의 "비밀".
    pub fn alloc_witness(&mut self, value: Fr) -> Variable {
        let idx = self.num_witness;
        self.num_witness += 1;
        self.values.push(value);
        Variable::Witness(idx)
    }

    /// 제약 추가: A · B = C
    ///
    /// 곱셈 하나 = 제약 하나
    /// 덧셈은 LinearCombination에 항을 추가하면 되므로 제약 불필요
    pub fn enforce(
        &mut self,
        a: LinearCombination,
        b: LinearCombination,
        c: LinearCombination,
    ) {
        self.constraints.push((a, b, c));
    }

    /// 모든 제약을 만족하는지 검증
    ///
    /// 각 제약 (A, B, C)에 대해: eval(A) * eval(B) == eval(C)
    /// 하나라도 실패하면 false
    ///
    /// 용도: 디버깅/테스트 (증명자가 witness를 대입하여 검산)
    /// Groth16은 이것을 "값을 모르고도" 검증하는 것
    pub fn is_satisfied(&self) -> bool {
        for (a, b, c) in &self.constraints {
            let a_val = a.evaluate(&self.values, self.num_instance);
            let b_val = b.evaluate(&self.values, self.num_instance);
            let c_val = c.evaluate(&self.values, self.num_instance);
            if a_val * b_val != c_val {
                return false;
            }
        }
        true
    }

    /// 만족하지 않는 첫 번째 제약의 인덱스 반환 (디버깅용)
    pub fn which_unsatisfied(&self) -> Option<usize> {
        for (idx, (a, b, c)) in self.constraints.iter().enumerate() {
            let a_val = a.evaluate(&self.values, self.num_instance);
            let b_val = b.evaluate(&self.values, self.num_instance);
            let c_val = c.evaluate(&self.values, self.num_instance);
            if a_val * b_val != c_val {
                return Some(idx);
            }
        }
        None
    }

    /// 총 변수 수: 1 (One) + instance + witness
    pub fn num_variables(&self) -> usize {
        1 + self.num_instance + self.num_witness
    }

    /// 제약 수
    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    /// (A, B, C) 희소 행렬 추출
    ///
    /// 각 행렬: Vec<Vec<(usize, Fr)>>
    ///   외부 Vec: 행 (= 제약 인덱스)
    ///   내부 Vec: (열 인덱스, 계수) 쌍 (= 희소 표현)
    ///
    /// 열 인덱스 = Variable의 index()
    ///
    /// Step 11(QAP)에서 이 행렬을 다항식으로 변환
    pub fn to_matrices(
        &self,
    ) -> (Vec<Vec<(usize, Fr)>>, Vec<Vec<(usize, Fr)>>, Vec<Vec<(usize, Fr)>>) {
        let mut a_mat = Vec::with_capacity(self.constraints.len());
        let mut b_mat = Vec::with_capacity(self.constraints.len());
        let mut c_mat = Vec::with_capacity(self.constraints.len());

        for (a, b, c) in &self.constraints {
            a_mat.push(self.lc_to_sparse(a));
            b_mat.push(self.lc_to_sparse(b));
            c_mat.push(self.lc_to_sparse(c));
        }

        (a_mat, b_mat, c_mat)
    }

    /// LinearCombination → 희소 벡터
    fn lc_to_sparse(&self, lc: &LinearCombination) -> Vec<(usize, Fr)> {
        lc.terms
            .iter()
            .map(|&(var, coeff)| (var.index(self.num_instance), coeff))
            .collect()
    }
}

/// 회로 = "어떤 계산을 R1CS로 표현하는 방법"
///
/// synthesize()가 ConstraintSystem에 변수와 제약을 추가
/// 같은 Circuit 구현을 setup, prove, verify에서 재사용
pub trait Circuit {
    fn synthesize(&self, cs: &mut ConstraintSystem);
}

// ── 테스트 ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ─ 기본 곱셈: x * y = z ─

    #[test]
    fn multiply_satisfied() {
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_witness(Fr::from_u64(4));
        let z = cs.alloc_instance(Fr::from_u64(12));

        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(y),
            LinearCombination::from(z),
        );

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 1);
        assert_eq!(cs.num_variables(), 4); // One + z + x + y
    }

    #[test]
    fn multiply_wrong_witness() {
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_witness(Fr::from_u64(4));
        let z = cs.alloc_instance(Fr::from_u64(11)); // 3*4 ≠ 11

        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(y),
            LinearCombination::from(z),
        );

        assert!(!cs.is_satisfied());
    }

    // ─ 피타고라스: x² + y² = z² ─

    #[test]
    fn pythagorean_satisfied() {
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_witness(Fr::from_u64(4));
        let z = cs.alloc_witness(Fr::from_u64(5));
        let x_sq = cs.alloc_witness(Fr::from_u64(9));
        let y_sq = cs.alloc_witness(Fr::from_u64(16));

        // 제약 1: x * x = x_sq
        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(x),
            LinearCombination::from(x_sq),
        );

        // 제약 2: y * y = y_sq
        cs.enforce(
            LinearCombination::from(y),
            LinearCombination::from(y),
            LinearCombination::from(y_sq),
        );

        // 제약 3: z * z = x_sq + y_sq
        cs.enforce(
            LinearCombination::from(z),
            LinearCombination::from(z),
            LinearCombination::from(x_sq).add(Fr::ONE, y_sq),
        );

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 3);
    }

    #[test]
    fn pythagorean_wrong() {
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_witness(Fr::from_u64(4));
        let z = cs.alloc_witness(Fr::from_u64(6)); // 3²+4²≠6²
        let x_sq = cs.alloc_witness(Fr::from_u64(9));
        let y_sq = cs.alloc_witness(Fr::from_u64(16));

        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(x),
            LinearCombination::from(x_sq),
        );
        cs.enforce(
            LinearCombination::from(y),
            LinearCombination::from(y),
            LinearCombination::from(y_sq),
        );
        cs.enforce(
            LinearCombination::from(z),
            LinearCombination::from(z),
            LinearCombination::from(x_sq).add(Fr::ONE, y_sq),
        );

        assert!(!cs.is_satisfied());
    }

    // ─ 상수항 사용: (x + 5) * 1 = y ─

    #[test]
    fn constant_term() {
        // y = x + 5, x=3 → y=8
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_instance(Fr::from_u64(8));

        // (x + 5·One) · 1 = y
        cs.enforce(
            LinearCombination::from(x).add(Fr::from_u64(5), Variable::One),
            LinearCombination::from(Variable::One),
            LinearCombination::from(y),
        );

        assert!(cs.is_satisfied());
    }

    // ─ Circuit trait ─

    struct MultiplyCircuit {
        x: Fr,
        y: Fr,
    }

    impl Circuit for MultiplyCircuit {
        fn synthesize(&self, cs: &mut ConstraintSystem) {
            let x = cs.alloc_witness(self.x);
            let y = cs.alloc_witness(self.y);
            let z = cs.alloc_instance(self.x * self.y);

            cs.enforce(
                LinearCombination::from(x),
                LinearCombination::from(y),
                LinearCombination::from(z),
            );
        }
    }

    #[test]
    fn circuit_trait() {
        let circuit = MultiplyCircuit {
            x: Fr::from_u64(7),
            y: Fr::from_u64(8),
        };
        let mut cs = ConstraintSystem::new();
        circuit.synthesize(&mut cs);
        assert!(cs.is_satisfied());
    }

    // ─ to_matrices ─

    #[test]
    fn matrices_simple() {
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_witness(Fr::from_u64(4));
        let z = cs.alloc_instance(Fr::from_u64(12));

        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(y),
            LinearCombination::from(z),
        );

        let (a, b, c) = cs.to_matrices();
        assert_eq!(a.len(), 1);
        assert_eq!(b.len(), 1);
        assert_eq!(c.len(), 1);

        // A: x는 인덱스 2 (One=0, z=1, x=2, y=3)
        assert_eq!(a[0].len(), 1);
        assert_eq!(a[0][0].0, 2);
        assert_eq!(a[0][0].1, Fr::ONE);

        // B: y는 인덱스 3
        assert_eq!(b[0][0].0, 3);

        // C: z는 인덱스 1
        assert_eq!(c[0][0].0, 1);
    }

    // ─ 조건문: if b then x else y ─

    #[test]
    fn conditional_select() {
        // result = b * x + (1-b) * y = y + b * (x - y)
        let mut cs = ConstraintSystem::new();
        let b = cs.alloc_witness(Fr::ONE); // b = 1 → select x
        let x = cs.alloc_witness(Fr::from_u64(42));
        let y = cs.alloc_witness(Fr::from_u64(99));

        // 보조 변수: t = b * (x - y)
        let t_val = Fr::ONE * (Fr::from_u64(42) - Fr::from_u64(99));
        let t = cs.alloc_witness(t_val);

        // result = y + t
        let result_val = Fr::from_u64(99) + t_val;
        let result = cs.alloc_instance(result_val);

        // 제약 1: b * (1 - b) = 0 (boolean)
        cs.enforce(
            LinearCombination::from(b),
            LinearCombination::from(Variable::One).add(-Fr::ONE, b),
            LinearCombination::zero(),
        );

        // 제약 2: b * (x - y) = t
        cs.enforce(
            LinearCombination::from(b),
            LinearCombination::from(x).add(-Fr::ONE, y),
            LinearCombination::from(t),
        );

        // 제약 3: (y + t) * 1 = result
        cs.enforce(
            LinearCombination::from(y).add(Fr::ONE, t),
            LinearCombination::from(Variable::One),
            LinearCombination::from(result),
        );

        assert!(cs.is_satisfied());
        assert_eq!(result_val, Fr::from_u64(42)); // b=1이므로 x 선택
    }

    // ─ x³ + x + 5 = y ─

    #[test]
    fn cubic_polynomial() {
        // f(x) = x³ + x + 5, x=3 → y=35
        let mut cs = ConstraintSystem::new();
        let x = cs.alloc_witness(Fr::from_u64(3));
        let y = cs.alloc_instance(Fr::from_u64(35));

        // 보조 변수
        let t1 = cs.alloc_witness(Fr::from_u64(9));  // x²
        let t2 = cs.alloc_witness(Fr::from_u64(27)); // x³

        // 제약 1: x * x = t1
        cs.enforce(
            LinearCombination::from(x),
            LinearCombination::from(x),
            LinearCombination::from(t1),
        );

        // 제약 2: t1 * x = t2
        cs.enforce(
            LinearCombination::from(t1),
            LinearCombination::from(x),
            LinearCombination::from(t2),
        );

        // 제약 3: (t2 + x + 5) * 1 = y
        cs.enforce(
            LinearCombination::from(t2)
                .add(Fr::ONE, x)
                .add(Fr::from_u64(5), Variable::One),
            LinearCombination::from(Variable::One),
            LinearCombination::from(y),
        );

        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 3);
    }

    // ─ 빈 제약 시스템 ─

    #[test]
    fn empty_system_satisfied() {
        let cs = ConstraintSystem::new();
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);
        assert_eq!(cs.num_variables(), 1); // One만
    }
}
