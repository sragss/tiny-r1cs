use std::marker::PhantomData;
use std::fmt::Debug;
use ark_ff::PrimeField;
use strum::{EnumCount, IntoEnumIterator};
use strum_macros::{EnumCount, EnumIter};

pub trait R1CSInputType: Clone + Copy + Debug + IntoEnumIterator + EnumCount + Into<usize> {}

#[derive(EnumIter, EnumCount, Clone, Copy, Debug)]
#[repr(usize)]
enum InputConfigPrimeField {
    PcIn,
    PcOut,
    BytecodeA,
    BytecodeVOpcode,
    BytecodeVRs1,
    BytecodeVRs2,
    BytecodeVRd,
    BytecodeVImm
}
impl R1CSInputType for InputConfigPrimeField {}





#[derive(Clone, Copy, Debug)]
enum Variable<I: R1CSInputType> {
    Input(I),
    Auxiliary(usize),
    Constant,
}


/// Constraints over a single row. Each variable points to a single item in Z and the corresponding coefficient.
#[derive(Clone, Debug)]
struct Constraint<I: R1CSInputType> {
    a: LC<I>,
    b: LC<I>,
    c: LC<I>,
}


// TODO(sragss): Current thinking is that this is overkill
impl<I: R1CSInputType> Constraint<I> {
    pub fn eq(left: Variable<I>, right: Variable<I>) -> Self {
        // (left - right) * right = 0
        Self {
            a: LC(vec![Term(left, 1), Term(right, -1)]),
            b: LC(vec![Term(Variable::Constant, 1)]),
            c: LC(vec![])
        }
    }

    pub fn binary(var: Variable<I>) -> Self {
        // var * (1 - var)
        Self {
            a: LC(vec![Term(var, 1)]),
            b: LC(vec![Term(var, -1), Term(Variable::Constant, 1)]),
            c: LC(vec![])
        }
    }
}







struct R1CSInstance<F: PrimeField> {
    pub a: Vec<(usize, usize, F)>,
    pub b: Vec<(usize, usize, F)>,
    pub c: Vec<(usize, usize, F)>,
}

struct R1CSBuilder<F: PrimeField, I: R1CSInputType> {
    constraints: Vec<Constraint<I>>,
    next_aux: usize,
    // compute_aux_funcs: Vec<Box<dyn Fn() -> Vec<F>>>,
    _marker: PhantomData<(F, I)>
}

impl<F: PrimeField, I: R1CSInputType> R1CSBuilder<F, I> {
    fn new() -> Self {
        Self {
            constraints: vec![],
            next_aux: 0,
            _marker: PhantomData
        }
    }

    fn materialize(&mut self) -> R1CSInstance<F> {
        todo!("allocate constraints")
    }

    fn constrain_eq(&mut self, left: impl Into<LC<I>>, right: impl Into<LC<I>>) {
        let left: LC<I> = left.into();
        let right: LC<I> = right.into();

        // (left - right) * right == 0
        let a = left - right.clone();
        let b = right.0;
        let constraint = Constraint {
            a,
            b: LC(b),
            c: LC(vec![])
        };
        println!("constraint {:?}", constraint);
        self.constraints.push(constraint);
    }

    fn constrain_if_else(
        &mut self, 
        condition: impl Into<LC<I>>, 
        result_true: impl Into<LC<I>>, 
        result_false: impl Into<LC<I>>, 
        alleged_result: impl Into<LC<I>>) {
            let condition: LC<I> = condition.into();
            let result_true: LC<I> = result_true.into();
            let result_false: LC<I> = result_false.into();
            let alleged_result: LC<I> = alleged_result.into();

            // result = condition * true_coutcome + (1 - condition) * false_outcome
            // => condition * (true_outcome - false_outcome) = (result - false_outcome)

            let constraint = Constraint {
                a: condition.clone(),
                b: (result_true - result_false.clone()),
                c: (alleged_result - result_false)
            };
            self.constraints.push(constraint);
    }

    #[must_use]
    fn allocate_if_else(&mut self, condition: impl Into<LC<I>>, result_true: impl Into<LC<I>>, result_false: impl Into<LC<I>>) -> Variable<I> {
        let result = Variable::Auxiliary(self.next_aux);
        self.next_aux += 1;

        self.constrain_if_else(condition, result_true, result_false, result);
        result
    }
}






trait R1CSConstraintBuilder<F: PrimeField> {
    type Inputs: R1CSInputType;

    fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>);
}


#[cfg(test)]
mod tests {
    use crate::impl_auto_conversions;

    use super::*;
    use ark_bn254::Fr;

    fn constraint_is_sat<I: R1CSInputType>(constraint: &Constraint<I>, inputs: &Vec<i64>) -> bool {
        // Find the number of variables and the number of aux. Inputs should be equal to this combined length
        let num_input=  I::COUNT;
        let mut num_aux = 0;

        let mut aux_set = std::collections::HashSet::new();
        for constraint in [&constraint.a, &constraint.b, &constraint.c] {
            for Term(var, _value) in &constraint.0 {
                if let Variable::Auxiliary(aux) = var {
                    aux_set.insert(aux);
                }
            }
        }
        num_aux = aux_set.len();
        if aux_set.len() > 0 {
            assert_eq!(num_aux, *aux_set.iter().max().unwrap() + 1); // Ensure there are no gaps
        }
        let aux_index = |aux_index: usize| num_input + aux_index;

        let num_vars = num_input + num_aux;
        assert!(num_vars == inputs.len());

        let mut a = 0;
        let mut b = 0;
        let mut c = 0;
        let mut buckets = [&mut a, &mut b, &mut c];
        let constraints = [&constraint.a, &constraint.b, &constraint.c];
        for (bucket, constraint) in buckets.iter_mut().zip(constraints.iter()) {
            for Term(var, coefficient) in constraint.0.iter() {
                match var {
                    Variable::Input(input) => {
                        let in_u: usize = (*input).into();
                        **bucket += inputs[in_u] * *coefficient;
                    },
                    Variable::Auxiliary(aux) => {
                        **bucket += inputs[aux_index(*aux)] * *coefficient;
                    },
                    Variable::Constant => {
                        **bucket += *coefficient;
                    }
                }
            }
        }

        println!("a * b == c      {a} * {b} == {c}");

        a * b == c
    }

    #[test]
    fn constraints() {
        let eq_constraint = Constraint::eq(Variable::Input(TestInputs::PcIn), Variable::Input(TestInputs::PcOut));
        let mut z = vec![0i64; TestInputs::COUNT];
        z[TestInputs::PcIn as usize] = 1;
        z[TestInputs::PcOut as usize] = 1;
        assert!(constraint_is_sat(&eq_constraint, &z));
        z[TestInputs::PcOut as usize] = 2;
        assert!(!constraint_is_sat(&eq_constraint, &z));
    }

    #[derive(EnumIter, EnumCount, Clone, Copy, Debug)]
    #[repr(usize)]
    enum TestInputs {
        PcIn,
        PcOut,
        BytecodeA,
        BytecodeVOpcode,
        BytecodeVRS1,
        BytecodeVRS2,
        BytecodeVRD,
        BytecodeVImm
    }
    impl R1CSInputType for TestInputs {}
    impl_auto_conversions!(TestInputs);

    #[test]
    fn eq_builder() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // PcIn + PcOut == BytecodeA + 2 BytecodeVOpcode
        struct TestConstraints();
        impl<F: PrimeField> R1CSConstraintBuilder<F> for TestConstraints {
            type Inputs = TestInputs;
            fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>) {
                let left = LC::sum2(Self::Inputs::PcIn, Self::Inputs::PcOut);
                let right = LC::sum2(Self::Inputs::BytecodeA, (Self::Inputs::BytecodeVOpcode, 2i64));
                builder.constrain_eq(left, right);
            }
        }

        let concrete_constraints = TestConstraints();
        concrete_constraints.build_constraints(&mut builder);
        assert!(builder.constraints.len() == 1);
        let constraint = &builder.constraints[0];
        let mut z = vec![0i64; TestInputs::COUNT];

        // 2 + 6 == 6 + 2*1
        z[TestInputs::PcIn as usize] = 2;
        z[TestInputs::PcOut as usize] = 6;
        z[TestInputs::BytecodeA as usize] = 6;
        z[TestInputs::BytecodeVOpcode as usize] = 1;
        assert!(constraint_is_sat(&constraint, &z));

        // 2 + 6 != 6 + 2*2
        z[TestInputs::BytecodeVOpcode as usize] = 2;
        assert!(!constraint_is_sat(&constraint, &z));
    }

    #[test]
    fn if_else_builder() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // condition * (true_outcome - false_outcome) = (result - false_outcome)
        // PcIn * (BytecodeVRS1 - BytecodeVRS2) == BytecodeA - BytecodeVRS2 
        // If PcIn == 1: BytecodeA = BytecodeVRS1
        // If PcIn == 0: BytecodeA = BytecodeVRS2
        struct TestConstraints();
        impl<F: PrimeField> R1CSConstraintBuilder<F> for TestConstraints {
            type Inputs = TestInputs;
            fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>) {
                let condition = Self::Inputs::PcIn;
                let true_outcome = Self::Inputs::BytecodeVRS1;
                let false_outcome = Self::Inputs::BytecodeVRS2;
                let alleged_result = Self::Inputs::BytecodeA;
                builder.constrain_if_else(condition, true_outcome, false_outcome, alleged_result);
            }
        }

        let concrete_constraints = TestConstraints();
        concrete_constraints.build_constraints(&mut builder);
        assert!(builder.constraints.len() == 1);
        let constraint = &builder.constraints[0];

        let mut z = vec![0i64; TestInputs::COUNT];
        z[TestInputs::PcIn as usize] = 1;
        z[TestInputs::BytecodeA as usize] = 6;
        z[TestInputs::BytecodeVRS1 as usize] = 6;
        z[TestInputs::BytecodeVRS2 as usize] = 10;
        assert!(constraint_is_sat(&constraint, &z));
        z[TestInputs::PcIn as usize] = 0;
        assert!(!constraint_is_sat(&constraint, &z));
        z[TestInputs::BytecodeA as usize] = 10;
        assert!(constraint_is_sat(&constraint, &z));
    }

    #[test]
    fn alloc_if_else_builder() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // condition * (true_outcome - false_outcome) = (result - false_outcome)
        // PcIn * (BytecodeVRS1 - BytecodeVRS2) == AUX_RESULT - BytecodeVRS2 
        // If PcIn == 1: AUX_RESULT = BytecodeVRS1
        // If PcIn == 0: AUX_RESULT = BytecodeVRS2
        // AUX_RESULT == BytecodeVImm
        struct TestConstraints();
        impl<F: PrimeField> R1CSConstraintBuilder<F> for TestConstraints {
            type Inputs = TestInputs;
            fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>) {
                let condition = Self::Inputs::PcIn;
                let true_outcome = Self::Inputs::BytecodeVRS1;
                let false_outcome = Self::Inputs::BytecodeVRS2;
                let branch_result = builder.allocate_if_else(condition, true_outcome, false_outcome);
                builder.constrain_eq(branch_result, Self::Inputs::BytecodeVImm);
            }
        }

        let concrete_constraints = TestConstraints();
        concrete_constraints.build_constraints(&mut builder);
        assert!(builder.constraints.len() == 2);
        let (branch_constraint,  eq_constraint) = (&builder.constraints[0], & builder.constraints[1]);

        let mut z = vec![0i64; TestInputs::COUNT + 1]; // 1 aux
        let true_branch_result: i64 = 12;
        let false_branch_result: i64 = 10;
        let aux_index = TestInputs::COUNT as usize;
        z[TestInputs::PcIn as usize] = 1;
        z[TestInputs::BytecodeVRS1 as usize] = true_branch_result;
        z[TestInputs::BytecodeVRS2 as usize] = false_branch_result;
        z[TestInputs::BytecodeVImm as usize] =  true_branch_result;
        z[aux_index] = true_branch_result;
        assert!(constraint_is_sat(&branch_constraint, &z));
        assert!(constraint_is_sat(&eq_constraint, &z));

        z[aux_index] = false_branch_result;
        assert!(!constraint_is_sat(&branch_constraint, &z));
        assert!(!constraint_is_sat(&eq_constraint, &z));

        z[TestInputs::BytecodeVImm as usize] = false_branch_result;
        assert!(!constraint_is_sat(&branch_constraint, &z));
        assert!(constraint_is_sat(&eq_constraint, &z));

        z[TestInputs::PcIn as usize] = 0;
        assert!(constraint_is_sat(&branch_constraint, &z));
        assert!(constraint_is_sat(&eq_constraint, &z));
    }
}


















#[derive(Clone, Copy, Debug)]
struct Term<I: R1CSInputType>(Variable<I>, i64);

/// Linear combination.
#[derive(Clone, Debug)]
struct LC<I: R1CSInputType>(Vec<Term<I>>);

impl<I: R1CSInputType> LC<I> {
    fn terms(&self) -> usize {
        self.0.len()
    }

    fn sum2(one: impl Into<Term<I>>, two: impl Into<Term<I>>) -> Self {
        LC(vec![one.into(), two.into()])
    }
}
impl<I: R1CSInputType> std::ops::Add for LC<I> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let mut combined_terms = self.0;
        combined_terms.extend(other.0);
        LC(combined_terms)
    }
}
impl<I: R1CSInputType> std::ops::Sub for LC<I> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut combined_terms = self.0;
        combined_terms.extend((-other).0);
        LC(combined_terms)
    }
}












impl<I: R1CSInputType> std::ops::Neg for Term<I> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Term(self.0, self.1 * -1)
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

impl<I: R1CSInputType> Into<LC<I>> for Term<I> {
    fn into(self) -> LC<I> {
        LC(vec![self])
    }
}

impl<I: R1CSInputType> Into<LC<I>> for Variable<I> {
    fn into(self) -> LC<I> {
        LC(vec![Term(self, 1)])
    }
}

impl<I: R1CSInputType> std::ops::Neg for LC<I> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let neg_terms = self.0.into_iter().map(|term| -term).collect();
        LC(neg_terms)
    }
}


// For each R1CS config, these need to be written concretely for the R1CSInputType
#[macro_export]
macro_rules! impl_auto_conversions {
    ($ConcreteInput:ty) => {
        type ConcreteInput = $ConcreteInput;

        impl Into<usize> for ConcreteInput {
            fn into(self) -> usize {
                self as usize
            }
        }
        impl Into<Variable<ConcreteInput>> for ConcreteInput {
            fn into(self) -> Variable<ConcreteInput> {
                Variable::Input(self)
            }
        }

        impl Into<(Variable<ConcreteInput>, i64)> for ConcreteInput {
            fn into(self) -> (Variable<ConcreteInput>, i64) {
                (Variable::Input(self), 1)
            }
        }
        impl Into<Term<ConcreteInput>> for ConcreteInput {
            fn into(self) -> Term<ConcreteInput> {
                Term(Variable::Input(self), 1)
            }
        }

        impl Into<Term<ConcreteInput>> for (ConcreteInput, i64) {
            fn into(self) -> Term<ConcreteInput> {
                Term(Variable::Input(self.0), self.1)
            }
        }

        impl Into<LC<ConcreteInput>> for ConcreteInput {
            fn into(self) -> LC<ConcreteInput> {
                LC(vec![Term(Variable::Input(self), 1)])
            }
        }
    };
}

impl_auto_conversions!(InputConfigPrimeField);
