use std::marker::PhantomData;

use ark_ff::PrimeField;
use enum_dispatch::enum_dispatch;
use strum::{EnumCount, IntoEnumIterator};
use strum_macros::{EnumCount as EnumCountMacro, EnumIter};

pub trait R1CSInputType: Clone + Copy + IntoEnumIterator {}

#[derive(Clone, Copy, Debug)]
enum Variable<I: R1CSInputType> {
    Input(I),
    Auxiliary(usize),
    Constant,
}

// type LinearComb<I> = Vec<Variable<I>>;

enum Metavariable<I: R1CSInputType> {
    Single(Variable<I>),
    Double(Variable<I>, Variable<I>),
    Triple(Variable<I>, Variable<I>, Variable<I>),
    Quad(Variable<I>, Variable<I>, Variable<I>, Variable<I>),
}

// TODO(sragss): Could use to share aux.
struct ConstraintSet<I: R1CSInputType> {
    constraints: Vec<Constraint<I>>,
}

struct Constraint<I: R1CSInputType> {
    a: Vec<(Variable<I>, i64)>,
    b: Vec<(Variable<I>, i64)>,
    c: Vec<(Variable<I>, i64)>,
}

impl<I: R1CSInputType> Constraint<I> {
    pub fn eq(left: Variable<I>, right: Variable<I>) -> Self {
        // (left - right) * right = 0
        Self {
            a: vec![(left, 1), (right, -1)],
            b: vec![(right, 1)],
            c: vec![],
        }
    }

    pub fn binary(var: Variable<I>) -> Self {
        // var * (1 - var)
        Self {
            a: vec![(var, 1)],
            b: vec![(var, -1), (Variable::Constant, 1)],
            c: vec![],
        }
    }

    pub fn if_else(
        condition: Variable<I>,
        true_outcome: Variable<I>,
        false_outcome: Variable<I>,
    ) -> (Self, Variable<I>) {
        // result = condition * true_coutcome + (1 - condition) * false_outcome
        // => condition * (true_outcome - false_outcome) = (result - false_outcome)

        // TODO(sragss): How compute aux?
        // - Return lambda -> fn(z: Vec<F>) -> F;
        // - self.type = ConstraintType::IfElse
        // - self.aux_type = AuxType::IfElse
        // ..
        // Push up to Builder level.

        // TODO(sragss): How to do combined if else?
        // true_outcome = 4 * Inputs::A + 1200  --- 1200 here is a constant.
        let result = Variable::Auxiliary(0);
        let constraint = Self {
            a: vec![(condition, 1)],
            b: vec![(true_outcome, 1), (false_outcome, -1)],
            c: vec![(condition, 1), (result, -1)],
        };
        (constraint, result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(EnumIter, Clone, Copy)]
    enum TestInputs {
        InputA,
        InputB,
        InputC,
    }

    impl R1CSInputType for TestInputs {}

    fn check_sat(
        constraint: &Constraint<TestInputs>,
        input_a: i64,
        input_b: i64,
        input_c: i64,
    ) -> bool {
        let mut a = 0;
        let mut b = 0;
        let mut c = 0;
        for (matrix_index, constraint) in [
            constraint.a.clone(),
            constraint.b.clone(),
            constraint.c.clone(),
        ]
        .iter()
        .enumerate()
        {
            for (var, value) in constraint {
                let variable_value: i64 = match var {
                    Variable::Input(input) => match input {
                        TestInputs::InputA => input_a,
                        TestInputs::InputB => input_b,
                        TestInputs::InputC => input_c,
                        _ => panic!("shouldn't happen"),
                    },
                    Variable::Constant => 1,
                    _ => panic!("shouldn't happen"),
                };
                if matrix_index == 0 {
                    a += variable_value * value;
                } else if matrix_index == 1 {
                    b += variable_value * value;
                } else if matrix_index == 2 {
                    c += variable_value * value;
                }
            }
        }
        println!("a * b == c      {a} * {b} == {c}");
        a * b == c
    }

    #[test]
    fn test_eq_constraint() {
        let left = Variable::Input(TestInputs::InputA);
        let right = Variable::Input(TestInputs::InputB);
        let constraint = Constraint::eq(left, right);
        assert!(check_sat(&constraint, 12, 12, 0));
        assert!(!check_sat(&constraint, 12, 20, 0));
    }

    #[test]
    fn test_binary_constraint() {
        let var = Variable::Input(TestInputs::InputA);
        let constraint = Constraint::binary(var);
        assert!(check_sat(&constraint, 0, 0, 0));
        assert!(check_sat(&constraint, 1, 0, 0));
        assert!(!check_sat(&constraint, 2, 0, 0));
    }

    #[test]
    fn test_if_else_constraint() {
        // let condition = Variable::Auxiliary(1);
        // let true_outcome = Variable::Auxiliary(2);
        // let false_outcome = Variable::Auxiliary(3);
        // let (constraint, result) = Constraint::if_else(condition, true_outcome, false_outcome);

        // assert_eq!(constraint.a, vec![(condition, 1)]);
        // assert_eq!(constraint.b, vec![(true_outcome, 1), (false_outcome, -1)]);
        // assert_eq!(constraint.c, vec![(condition, 1), (false_outcome, -1)]);
        // assert_eq!(result, Variable::Auxiliary(0));
    }
}

#[derive(EnumIter, Clone, Copy)]
enum InputConfigPrimeField {
    PcIn,
    PcOut,
    BytecodeA,
    BytecodeVOpcode,
    BytecodeVRs1,
    BytecodeVRs2,
    BytecodeVRd,
    BytecodeVImm,
}
impl R1CSInputType for InputConfigPrimeField {}

#[derive(EnumIter, Clone, Copy)]
enum InputConfigTowerField {
    PcIn,
    PcOut,
}
impl R1CSInputType for InputConfigTowerField {}

trait R1CSConstraintSubset<F> {
    type Inputs: R1CSInputType;

    fn constraints(&self) -> Vec<Constraint<Self::Inputs>>;

    fn compute_aux(&self) -> Vec<F>;
}

struct Term<I: R1CSInputType>(Variable<I>, i64);
struct LinearCombination<I: R1CSInputType>(Vec<Term<I>>);

impl<I: R1CSInputType> LinearCombination<I> {
    fn sum2(one: impl Into<Term<I>>, two: impl Into<Term<I>>) -> Self {
        LinearCombination(vec![one.into(), two.into()])
    }
}

trait LinearCombo<I: R1CSInputType> {
    fn into_linear_combo(self) -> Vec<(Variable<I>, i64)>;
}

impl<I: R1CSInputType> LinearCombo<I> for Variable<I> {
    fn into_linear_combo(self) -> Vec<(Variable<I>, i64)> {
        vec![(self, 1)]
    }
}

impl<I: R1CSInputType> LinearCombo<I> for LinearCombination<I> {
    fn into_linear_combo(self) -> Vec<(Variable<I>, i64)> {
        todo!();
    }
}

impl<I: R1CSInputType> Into<Term<I>> for Variable<I> {
    fn into(self) -> Term<I> {
        Term(self, 1)
    }
}

impl<I: R1CSInputType> Into<Term<I>> for (Variable<I>, i64) {
    fn into(self) -> Term<I> {
        Term(self.0, self.1)
    }
}

impl Into<Variable<InputConfigPrimeField>> for InputConfigPrimeField {
    fn into(self) -> Variable<InputConfigPrimeField> {
        Variable::Input(self)
    }
}

impl Into<(Variable<InputConfigPrimeField>, i64)> for InputConfigPrimeField {
    fn into(self) -> (Variable<InputConfigPrimeField>, i64) {
        (Variable::Input(self), 1)
    }
}

impl Into<Variable<InputConfigTowerField>> for InputConfigTowerField {
    fn into(self) -> Variable<InputConfigTowerField> {
        Variable::Input(self)
    }
}

impl Into<Term<InputConfigPrimeField>> for InputConfigPrimeField {
    fn into(self) -> Term<InputConfigPrimeField> {
        Term(Variable::Input(self), 1)
    }
}

impl Into<Term<InputConfigPrimeField>> for (InputConfigPrimeField, i64) {
    fn into(self) -> Term<InputConfigPrimeField> {
        Term(Variable::Input(self.0), self.1)
    }
}

impl Into<LinearCombination<InputConfigPrimeField>> for Term<InputConfigPrimeField> {
    fn into(self) -> LinearCombination<InputConfigPrimeField> {
        LinearCombination(vec![self])
    }
}

impl Into<LinearCombination<InputConfigPrimeField>> for InputConfigPrimeField {
    fn into(self) -> LinearCombination<InputConfigPrimeField> {
        LinearCombination(vec![Term(Variable::Input(self), 1)])
    }
}

struct FakeConstraintSubset();
impl<F: PrimeField> R1CSConstraintSubset<F> for FakeConstraintSubset {
    type Inputs = InputConfigPrimeField;
    fn constraints(&self) -> Vec<Constraint<Self::Inputs>> {
        vec![Constraint::eq(
            Variable::Input(InputConfigPrimeField::BytecodeA),
            Variable::Input(InputConfigPrimeField::BytecodeVImm),
        )]
    }
    fn compute_aux(&self) -> Vec<F> {
        vec![]
    }
}

struct FakeTowerConstraintSubset();
impl<F: PrimeField> R1CSConstraintSubset<F> for FakeTowerConstraintSubset {
    type Inputs = InputConfigTowerField;
    fn constraints(&self) -> Vec<Constraint<Self::Inputs>> {
        vec![]
    }
    fn compute_aux(&self) -> Vec<F> {
        vec![]
    }
}

// #[enum_dispatch]
// trait JoltInstruction<CircuitInputs>: Clone + Send + Sync {
//     fn constraints<F: PrimeField>(&self) -> impl R1CSConstraintSubset<F, Inputs = CircuitInputs>;
// }

#[allow(non_camel_case_types)]
#[repr(u8)]
#[derive(Clone, EnumIter, EnumCountMacro)]
// #[enum_dispatch(JoltInstruction)]
pub enum RV32IPrimeField {
    ADD(AddInstruction),
    SUB(SubInstruction),
}

#[derive(Clone, Default)]
pub struct AddInstruction();
impl<F: PrimeField> R1CSConstraintSubset<F> for AddInstruction {
    type Inputs = InputConfigPrimeField;

    fn constraints(&self) -> Vec<Constraint<Self::Inputs>> {
        todo!()
    }

    fn compute_aux(&self) -> Vec<F> {
        todo!()
    }
}

#[derive(Clone, Default)]
pub struct SubInstruction();
impl<F: PrimeField> R1CSConstraintSubset<F> for SubInstruction {
    type Inputs = InputConfigPrimeField;

    fn constraints(&self) -> Vec<Constraint<Self::Inputs>> {
        todo!()
    }

    fn compute_aux(&self) -> Vec<F> {
        todo!()
    }
}

#[derive(Clone, Default)]
pub struct SubInstructionPrimeFieldConsraints();
impl<F: PrimeField> R1CSConstraintSubset<F> for SubInstructionPrimeFieldConsraints {
    type Inputs = InputConfigPrimeField;

    fn constraints(&self) -> Vec<Constraint<Self::Inputs>> {
        todo!()
    }

    fn compute_aux(&self) -> Vec<F> {
        todo!()
    }
}

#[derive(Clone, Default)]
pub struct SubInstructionTowerFieldConsraints();
impl<F: PrimeField> R1CSConstraintSubset<F> for SubInstructionTowerFieldConsraints {
    type Inputs = InputConfigTowerField;

    fn constraints(&self) -> Vec<Constraint<Self::Inputs>> {
        todo!()
    }

    fn compute_aux(&self) -> Vec<F> {
        todo!()
    }
}

// TODO(sragss):
// - How does this actually work with PrimeField / TowerField (wrappers?)
// - Cleanliness of wiring the Inputs associated type
// - Can I restrict JoltInstruction to ensure that it has implemented the R1CSConstraintSubset trait

fn main() {
    // let mut builder = R1CSBuilder::<ark_bn254::Fr, InputConfigPrimeField>::new();
    // for instruction in RV32IPrimeField::iter() {
    //     // TODO: Enum dispatch should be unrolling to this.
    //     match instruction {
    //         RV32IPrimeField::ADD(inner) => {
    //             builder.append_constraints(R1CSConstraintSubset::<ark_bn254::Fr>::constraints(&inner));
    //         },
    //         RV32IPrimeField::SUB(inner) => {
    //             builder.append_constraints(R1CSConstraintSubset::<ark_bn254::Fr>::constraints(&inner));
    //             // inner.constraints::<ark_bn254::Fr>();
    //         }
    //     }
    // }
}
