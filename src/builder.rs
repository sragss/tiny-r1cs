use std::{marker::PhantomData, ops::Range};
use std::fmt::Debug;
use strum::{EnumCount, IntoEnumIterator};
use strum_macros::{EnumCount, EnumIter};
use jolt_core::poly::field::JoltField;

use crate::{impl_r1cs_input_lc_conversions, ops::{ConstraintInput, Term, Variable, LC}};




/// Constraints over a single row. Each variable points to a single item in Z and the corresponding coefficient.
#[derive(Clone, Debug)]
struct Constraint<I: ConstraintInput> {
    a: LC<I>,
    b: LC<I>,
    c: LC<I>,
}

struct AuxComputation<F: JoltField, I: ConstraintInput> {
    symbolic_inputs: Vec<LC<I>>,
    flat_vars: Vec<Variable<I>>,
    input_to_flat: Vec<Option<Range<usize>>>,
    compute: Box<dyn Fn(&[F]) -> F>
}

impl<F: JoltField, I: ConstraintInput> AuxComputation<F, I> {
    fn new(symbolic_inputs: Vec<LC<I>>, compute: Box<dyn Fn(&[F]) -> F>) -> Self {
        let flat_var_count: usize = symbolic_inputs.iter().map(|input| input.num_vars()).sum();
        let mut flat_vars = Vec::with_capacity(flat_var_count);
        let mut input_to_flat = Vec::with_capacity(symbolic_inputs.len());

        let mut range_start_index = 0;
        for input in &symbolic_inputs {
            let terms = input.terms();
            let num_vars= input.num_vars();
            for term in terms {
                if let Variable::Constant = term.0 {
                    continue;
                }
                flat_vars.push(term.0.clone());
            }
            if num_vars > 0 {
                input_to_flat.push(Some(range_start_index..(range_start_index + num_vars)));
                range_start_index += num_vars;
            } else {
                input_to_flat.push(None);
            }
        }
        assert_eq!(flat_vars.len(), flat_var_count);
        
        Self {
            symbolic_inputs,
            flat_vars,
            input_to_flat,
            compute
        }
    }


    /// Takes one value per value in flat_vars.
    fn compute(&self, values: &[F]) -> F {
        assert_eq!(values.len(), self.flat_vars.len());
        assert_eq!(self.input_to_flat.len(), self.symbolic_inputs.len());
        let computed_inputs: Vec<_> = self.symbolic_inputs.iter().enumerate()
            .map(|(input_index, input_lc)| {
                let values = if let Some(range) = self.input_to_flat[input_index].clone() {
                    &values[range]
                } else {
                    &[]
                };
                input_lc.evaluate(values)
            })
            .collect();
        (self.compute)(&computed_inputs)
    }
}

impl<I: ConstraintInput> Constraint<I> {
    // pub fn eq(left: Variable<I>, right: Variable<I>) -> Self {
    //     // (left - right) * right = 0
    //     Self {
    //         a: Term(left, 1) - Term(right, 1),
    //         b: LC(vec![Term(Variable::Constant, 1)]),
    //         c: LC(vec![])
    //     }
    // }

    // pub fn binary(var: Variable<I>) -> Self {
    //     // var * (1 - var)
    //     Self {
    //         a: LC(vec![Term(var, 1)]),
    //         b: LC(vec![Term(var, -1), Term(Variable::Constant, 1)]),
    //         c: LC(vec![])
    //     }
    // }
}







struct R1CSInstance<F: JoltField> {
    pub a: Vec<(usize, usize, F)>,
    pub b: Vec<(usize, usize, F)>,
    pub c: Vec<(usize, usize, F)>,
}

struct R1CSBuilder<F: JoltField, I: ConstraintInput> {
    constraints: Vec<Constraint<I>>,
    next_aux: usize,
    aux_computations: Vec<AuxComputation<F, I>>,
    // compute_aux_funcs: Vec<Box<dyn Fn() -> Vec<F>>>,
    _marker: PhantomData<(F, I)>
}

impl<F: JoltField, I: ConstraintInput> R1CSBuilder<F, I> {
    pub fn new() -> Self {
        Self {
            constraints: vec![],
            next_aux: 0,
            aux_computations: vec![],
            _marker: PhantomData
        }
    }

    fn allocate_aux(&mut self, aux_computation: AuxComputation<F, I>) -> Variable<I> {
        let new_aux = Variable::Auxiliary(self.next_aux);
        self.next_aux += 1;
        self.aux_computations.push(aux_computation);

        new_aux
    }

    /// Index of variable within z.
    pub fn witness_index(&self, var: impl Into<Variable<I>>) -> usize {
        let var: Variable<I> = var.into();
        match var {
            Variable::Input(inner) => {
                inner.into()
            },
            Variable::Auxiliary(aux_index) => {
                I::COUNT + aux_index
            },
            Variable::Constant => {
               I::COUNT + self.next_aux 
            }
        }
    }

    pub fn materialize(&mut self) -> R1CSInstance<F> {
        todo!("allocate constraints")
    }

    pub fn constrain_eq(&mut self, left: impl Into<LC<I>>, right: impl Into<LC<I>>) {
        // left - right == 0
        let left: LC<I> = left.into();
        let right: LC<I> = right.into();

        let a = left - right.clone();
        let b = Variable::Constant.into();
        let constraint = Constraint {
            a,
            b,
            c: LC::zero()
        };
        self.constraints.push(constraint);
    }

    pub fn constrain_eq_conditional(&mut self, condition: impl Into<LC<I>>, left: impl Into<LC<I>>, right: impl Into<LC<I>>) {
        // condition  * (left - right) == 0
        let condition: LC<I> = condition.into();
        let left: LC<I> = left.into();
        let right: LC<I> = right.into();

        let a = condition;
        let b = left - right;
        let c = LC::zero();
        let constraint = Constraint { a, b, c };
        self.constraints.push(constraint);
    }

    pub fn constrain_binary(&mut self, value: impl Into<LC<I>>) {
        let one: LC<I> = Variable::Constant.into();
        let value: LC<I> = value.into();
        // value * (1 - value)
        let constraint = Constraint {
            a: value.clone(),
            b: one - value,
            c: LC::zero()
        };
        self.constraints.push(constraint);
    }

    pub fn constrain_if_else(
        &mut self, 
        condition: impl Into<LC<I>>, 
        result_true: impl Into<LC<I>>, 
        result_false: impl Into<LC<I>>, 
        alleged_result: impl Into<LC<I>>) {
            let condition: LC<I> = condition.into();
            let result_true: LC<I> = result_true.into();
            let result_false: LC<I> = result_false.into();
            let alleged_result: LC<I> = alleged_result.into();

            // result == condition * true_coutcome + (1 - condition) * false_outcome
            // simplify to single mul, single constraint => condition * (true_outcome - false_outcome) == (result - false_outcome)

            let constraint = Constraint {
                a: condition.clone(),
                b: (result_true - result_false.clone()),
                c: (alleged_result - result_false)
            };
            self.constraints.push(constraint);
    }


    #[must_use]
    pub fn allocate_if_else(&mut self, condition: impl Into<LC<I>>, result_true: impl Into<LC<I>>, result_false: impl Into<LC<I>>) -> Variable<I> {
        let (condition, result_true, result_false) = (condition.into(), result_true.into(), result_false.into());

        let compute_aux= Self::compute_if_else(&condition, &result_true, &result_false);
        let aux_var = self.allocate_aux(compute_aux);

        self.constrain_if_else(condition, result_true, result_false, aux_var);
        aux_var
    }

    fn compute_if_else(condition: &LC<I>, result_true: &LC<I>, result_false: &LC<I>) -> AuxComputation<F, I> {
        // aux = (condition == 1) ? result_true : result_false;
        let if_else = |values: &[F]| -> F {
            assert_eq!(values.len(), 3);
            let condition = values[0];
            let result_true = values[1];
            let result_false = values[2];

            if condition.is_one() {
                result_true
            } else {
                result_false
            }
        };

        AuxComputation::new(
            vec![condition.clone(), result_true.clone(), result_false.clone()], 
            Box::new(if_else)
        )
    }

    // TODO(sragss): Technically we could use unpacked: Vec<LC<I>> here easily, but it feels like it would confuse the API.
    pub fn constrain_pack_le(
        &mut self,
        unpacked: Vec<Variable<I>>,
        result: impl Into<LC<I>>,
        operand_bits: usize
    ) {
        // Pack unpacked via a simple weighted linear combination
        // A + 2 * B + 4 * C + 8 * D, ...
        let packed: Vec<Term<I>> = unpacked.into_iter().enumerate().map(|(idx, unpacked)| Term(unpacked, 1 << (idx * operand_bits))).collect();
        self.constrain_eq(packed, result);
    }

    #[must_use]
    pub fn allocate_pack_le(&mut self, unpacked: Vec<Variable<I>>, operand_bits: usize) -> Variable<I> {
        let packed = self.allocate_aux(Self::compute_pack_le(&unpacked, operand_bits));

        self.constrain_pack_le(unpacked, packed, operand_bits);
        packed
    }

    fn compute_pack_le(to_pack: &[Variable<I>], operand_bits: usize) -> AuxComputation<F, I> {
        let pack = move |values: &[F]| -> F {
            values.into_iter().enumerate().fold(F::zero(), |acc, (idx, &value)| {
                acc + value * F::from_u64(1 << (idx * operand_bits)).unwrap()
            })
        };

        AuxComputation::new(
            to_pack.iter().cloned().map(|sym| sym.into()).collect(),
            Box::new(pack)
        )
    }

    pub fn constrain_pack_be(
        &mut self,
        unpacked: Vec<Variable<I>>,
        result: impl Into<LC<I>>,
        operand_bits: usize
    ) {
        // Pack unpacked via a simple weighted linear combination
        // A + 2 * B + 4 * C + 8 * D, ...
        // Note: Packing order is reversed from constrain_pack_le
        let packed: Vec<Term<I>> = unpacked.into_iter().rev().enumerate().map(|(idx, unpacked)| Term(unpacked, 1 << (idx * operand_bits))).collect();
        self.constrain_eq(packed, result);
    }

    #[must_use]
    pub fn allocate_pack_be(&mut self, unpacked: Vec<Variable<I>>, operand_bits: usize) -> Variable<I> {
        let packed = self.allocate_aux(Self::compute_pack_be(&unpacked, operand_bits));

        self.constrain_pack_be(unpacked, packed, operand_bits);
        packed
    }

    fn compute_pack_be(to_pack: &[Variable<I>], operand_bits: usize) -> AuxComputation<F, I> {
        let pack = move |values: &[F]| -> F {
            values.into_iter().rev().enumerate().fold(F::zero(), |acc, (idx, &value)| {
                acc + value * F::from_u64(1 << (idx * operand_bits)).unwrap()
            })
        };

        AuxComputation::new(
            to_pack.iter().cloned().map(|sym| sym.into()).collect(),
            Box::new(pack)
        )
    }

    /// Constrain x * y == z
    pub fn constrain_prod(&mut self, x: impl Into<LC<I>>, y: impl Into<LC<I>>, z: impl Into<LC<I>>) {
        let constraint = Constraint {
            a: x.into(),
            b: y.into(),
            c: z.into()
        };
        self.constraints.push(constraint);
    }

    #[must_use]
    pub fn allocate_prod(&mut self, x: impl Into<LC<I>>, y: impl Into<LC<I>>) -> Variable<I> {
        let (x, y) = (x.into(), y.into());
        let z = self.allocate_aux(Self::compute_prod(&x, &y));

        self.constrain_prod(x, y, z);
        z
    }

    fn compute_prod(x: &LC<I>, y: &LC<I>) -> AuxComputation<F, I> {
        let prod = |values: &[F]| {
            assert_eq!(values.len(), 2);

            values[0] * values[1]
        };

        AuxComputation::new(
            vec![x.clone(), y.clone()],
            Box::new(prod)
        )
    }
}






trait R1CSConstraintBuilder<F: JoltField> {
    type Inputs: ConstraintInput;

    fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>);
}


#[cfg(test)]
mod tests {
    use crate::{impl_r1cs_input_lc_conversions, input_range};

    use super::*;
    use ark_bn254::Fr;

    fn constraint_is_sat<I: ConstraintInput>(constraint: &Constraint<I>, inputs: &Vec<i64>) -> bool {
        // Find the number of variables and the number of aux. Inputs should be equal to this combined length
        let num_input=  I::COUNT;
        let mut num_aux = 0;

        let mut aux_set = std::collections::HashSet::new();
        for constraint in [&constraint.a, &constraint.b, &constraint.c] {
            for Term(var, _value) in constraint.terms() {
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
        assert_eq!(num_vars, inputs.len());

        let mut a = 0;
        let mut b = 0;
        let mut c = 0;
        let mut buckets = [&mut a, &mut b, &mut c];
        let constraints = [&constraint.a, &constraint.b, &constraint.c];
        for (bucket, constraint) in buckets.iter_mut().zip(constraints.iter()) {
            for Term(var, coefficient) in constraint.terms() {
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

    // #[test]
    // fn constraints() {
    //     let eq_constraint = Constraint::eq(Variable::Input(TestInputs::PcIn), Variable::Input(TestInputs::PcOut));
    //     let mut z = vec![0i64; TestInputs::COUNT];
    //     z[TestInputs::PcIn as usize] = 1;
    //     z[TestInputs::PcOut as usize] = 1;
    //     assert!(constraint_is_sat(&eq_constraint, &z));
    //     z[TestInputs::PcOut as usize] = 2;
    //     assert!(!constraint_is_sat(&eq_constraint, &z));
    // }

    #[allow(non_camel_case_types)]
    #[derive(EnumIter, EnumCount, Clone, Copy, Debug, PartialEq)]
    #[repr(usize)]
    enum TestInputs {
        PcIn,
        PcOut,
        BytecodeA,
        BytecodeVOpcode,
        BytecodeVRS1,
        BytecodeVRS2,
        BytecodeVRD,
        BytecodeVImm,
        RAMA,
        RAMRS1,
        RAMRS2,
        RAMByte0,
        RAMByte1,
        RAMByte2,
        RAMByte3,
        OpFlags0,
        OpFlags1,
        OpFlags2,
        OpFlags3,
        OpFlags_SignImm
    }
    impl ConstraintInput for TestInputs {}
    impl_r1cs_input_lc_conversions!(TestInputs);

    #[test]
    fn aux_compute_simple() {
        let fake_lambda = |input: &[Fr]| {
            assert_eq!(input.len(), 1);
            input[0]
        };
        let lc = vec![LC::sum2(12i64, 20i64)];
        let aux = AuxComputation::<Fr, TestInputs>::new(lc, Box::new(fake_lambda));
        let result = aux.compute(&[]);
        assert_eq!(result, Fr::from(32));
    }

    #[test]
    fn aux_compute_advanced() {
        // (12 + 20) * (BytecodeA + Aux(0)) - 3 * Aux(1)
        let symbolic_inputs = vec![
            LC::sum2(12i64, 20i64), 
            LC::sum2(TestInputs::BytecodeA, Variable::Auxiliary(0)),
            (3 * Variable::Auxiliary(1)).into()
        ];
        let fake_lambda = |input: &[Fr]| {
            assert_eq!(input.len(), 3);
            input[0] * input[1] - input[2]
        };
        let aux = AuxComputation::<Fr, TestInputs>::new(symbolic_inputs, Box::new(fake_lambda));
        let result = aux.compute(&[Fr::from(5), Fr::from(10), Fr::from(7)]);
        assert_eq!(result, Fr::from((12 + 20) * (5 + 10) - (3 * 7)));
    }

    #[test]
    fn eq_builder() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // PcIn + PcOut == BytecodeA + 2 BytecodeVOpcode
        struct TestConstraints();
        impl<F: JoltField> R1CSConstraintBuilder<F> for TestConstraints {
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
        impl<F: JoltField> R1CSConstraintBuilder<F> for TestConstraints {
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
        impl<F: JoltField> R1CSConstraintBuilder<F> for TestConstraints {
            type Inputs = TestInputs;
            fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>) {
                let condition = LC::sum2(Self::Inputs::PcIn, Self::Inputs::PcOut);
                let true_outcome = Self::Inputs::BytecodeVRS1;
                let false_outcome = Self::Inputs::BytecodeVRS2;
                let branch_result = builder.allocate_if_else(condition, true_outcome, false_outcome);
                builder.constrain_eq(branch_result, Self::Inputs::BytecodeVImm);
            }
        }

        let concrete_constraints = TestConstraints();
        concrete_constraints.build_constraints(&mut builder);
        assert_eq!(builder.constraints.len(), 2);
        let (branch_constraint,  eq_constraint) = (&builder.constraints[0], & builder.constraints[1]);

        let mut z = vec![0i64; TestInputs::COUNT + 1]; // 1 aux
        let true_branch_result: i64 = 12;
        let false_branch_result: i64 = 10;
        let aux_index = builder.witness_index(Variable::Auxiliary(0));
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

        assert_eq!(builder.aux_computations.len(), 1);
        let compute_2 = builder.aux_computations[0].compute(&[Fr::one(), Fr::zero(), Fr::from(2), Fr::from(3)]);
        assert_eq!(compute_2, Fr::from(2));
        let compute_2 = builder.aux_computations[0].compute(&[Fr::zero(), Fr::one(), Fr::from(2), Fr::from(3)]);
        assert_eq!(compute_2, Fr::from(2));
        let compute_3 = builder.aux_computations[0].compute(&[Fr::zero(), Fr::zero(), Fr::from(2), Fr::from(3)]);
        assert_eq!(compute_3, Fr::from(3));
    }

    #[test]
    fn packing_le_builder() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // pack_le(OpFlags0, OpFlags1, OpFlags2, OpFlags3) == BytecodeA
        struct TestConstraints();
        impl<F: JoltField> R1CSConstraintBuilder<F> for TestConstraints {
            type Inputs = TestInputs;
            fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>) {
                let result = Variable::Input(TestInputs::BytecodeA);
                let unpacked: Vec<Variable<TestInputs>> = vec![TestInputs::OpFlags0.into(), TestInputs::OpFlags1.into(), TestInputs::OpFlags2.into(), TestInputs::OpFlags3.into()];
                builder.constrain_pack_le(unpacked, result, 1);
            }
        }

        let concrete_constraints = TestConstraints();
        concrete_constraints.build_constraints(&mut builder);
        assert_eq!(builder.constraints.len(), 1);
        let constraint = &builder.constraints[0];

        // 1101 == 13
        let mut z = vec![0i64; TestInputs::COUNT];
        // (little endian)
        z[TestInputs::OpFlags0 as usize] = 1;
        z[TestInputs::OpFlags1 as usize] = 0;
        z[TestInputs::OpFlags2 as usize] = 1;
        z[TestInputs::OpFlags3 as usize] = 1;
        z[TestInputs::BytecodeA as usize] = 13;

        assert!(constraint_is_sat(&constraint, &z));
    }

    #[test]
    fn alloc_packing_le_builder() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // pack_le(OpFlags0, OpFlags1, OpFlags2, OpFlags3) == Aux(0)
        struct TestConstraints();
        impl<F: JoltField> R1CSConstraintBuilder<F> for TestConstraints {
            type Inputs = TestInputs;
            fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>) {
                let unpacked: Vec<Variable<TestInputs>> = vec![TestInputs::OpFlags0.into(), TestInputs::OpFlags1.into(), TestInputs::OpFlags2.into(), TestInputs::OpFlags3.into()];
                let _result = builder.allocate_pack_le(unpacked, 1);
            }
        }

        let concrete_constraints = TestConstraints();
        concrete_constraints.build_constraints(&mut builder);
        assert_eq!(builder.constraints.len(), 1);
        let constraint = &builder.constraints[0];

        // 1101 == 13
        let mut z = vec![0i64; TestInputs::COUNT + 1];
        // (little endian)
        z[TestInputs::OpFlags0 as usize] = 1;
        z[TestInputs::OpFlags1 as usize] = 0;
        z[TestInputs::OpFlags2 as usize] = 1;
        z[TestInputs::OpFlags3 as usize] = 1;

        assert_eq!(builder.aux_computations.len(), 1);
        let computed_aux = builder.aux_computations[0].compute(&vec![Fr::one(), Fr::zero(), Fr::one(), Fr::one()]);
        assert_eq!(computed_aux, Fr::from(13));
        z[builder.witness_index(Variable::Auxiliary(0))] = 13;
        assert!(constraint_is_sat(&constraint, &z));
    }

    #[test]
    fn packing_be_builder() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // pack_be(OpFlags0, OpFlags1, OpFlags2, OpFlags3) == BytecodeA
        struct TestConstraints();
        impl<F: JoltField> R1CSConstraintBuilder<F> for TestConstraints {
            type Inputs = TestInputs;
            fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>) {
                let result = Variable::Input(TestInputs::BytecodeA);
                let unpacked: Vec<Variable<TestInputs>> = vec![TestInputs::OpFlags0.into(), TestInputs::OpFlags1.into(), TestInputs::OpFlags2.into(), TestInputs::OpFlags3.into()];
                builder.constrain_pack_be(unpacked, result, 1);
            }
        }

        let concrete_constraints = TestConstraints();
        concrete_constraints.build_constraints(&mut builder);
        assert_eq!(builder.constraints.len(), 1);
        let constraint = &builder.constraints[0];

        // 1101 == 13
        let mut z = vec![0i64; TestInputs::COUNT];
        // (big endian)
        z[TestInputs::OpFlags0 as usize] = 1;
        z[TestInputs::OpFlags1 as usize] = 1;
        z[TestInputs::OpFlags2 as usize] = 0;
        z[TestInputs::OpFlags3 as usize] = 1;
        z[TestInputs::BytecodeA as usize] = 13;

        assert!(constraint_is_sat(&constraint, &z));
    }

    #[test]
    fn prod() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // OpFlags0 * OpFlags1 == BytecodeA
        // OpFlags2 * OpFlags3 == Aux
        struct TestConstraints();
        impl<F: JoltField> R1CSConstraintBuilder<F> for TestConstraints {
            type Inputs = TestInputs;
            fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>) {
                builder.constrain_prod(TestInputs::OpFlags0, TestInputs::OpFlags1, TestInputs::BytecodeA);
                let _aux = builder.allocate_prod(TestInputs::OpFlags2, TestInputs::OpFlags3);
            }
        }

        let concrete_constraints = TestConstraints();
        concrete_constraints.build_constraints(&mut builder);
        assert_eq!(builder.constraints.len(), 2);
        assert_eq!(builder.next_aux, 1);

        let mut z = vec![0i64; TestInputs::COUNT];
        // x * y == z
        z[TestInputs::OpFlags0 as usize] = 7;
        z[TestInputs::OpFlags1 as usize] = 10;
        z[TestInputs::BytecodeA as usize] = 70;
        assert!(constraint_is_sat(&builder.constraints[0], &z));
        z[TestInputs::BytecodeA as usize] = 71;
        assert!(!constraint_is_sat(&builder.constraints[0], &z));

        // x * y == aux
        z[TestInputs::OpFlags2 as usize] = 5;
        z[TestInputs::OpFlags3 as usize] = 7;
        z.push(35);
        assert!(constraint_is_sat(&builder.constraints[1], &z));
        z[builder.witness_index(Variable::Auxiliary(0))] = 36;
        assert!(!constraint_is_sat(&builder.constraints[1], &z));
    }

    #[test]
    fn alloc_prod() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // OpFlags0 * OpFlags1 == Aux(0)
        struct TestConstraints();
        impl<F: JoltField> R1CSConstraintBuilder<F> for TestConstraints {   
            type Inputs = TestInputs;
            fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>) {
                let _aux = builder.allocate_prod(TestInputs::OpFlags0, TestInputs::OpFlags1);
            }
        }

        let constraints = TestConstraints();
        constraints.build_constraints(&mut builder);
        assert_eq!(builder.constraints.len(), 1);
        assert_eq!(builder.next_aux, 1);

        let mut z = vec![0i64; TestInputs::COUNT + 1];
        z[builder.witness_index(TestInputs::OpFlags0)] = 7;
        z[builder.witness_index(TestInputs::OpFlags1)] = 5;
        z[builder.witness_index(Variable::Auxiliary(0))] = 35;

        assert!(constraint_is_sat(&builder.constraints[0], &z));
        z[builder.witness_index(Variable::Auxiliary(0))] = 36;
        assert!(!constraint_is_sat(&builder.constraints[0], &z));
    }

    #[allow(non_camel_case_types)]
    #[derive(EnumIter, EnumCount, Clone, Copy, Debug, PartialEq)]
    #[repr(usize)]
    enum JoltInputs {
        PcIn,
        PcOut,

        Bytecode_A,
        // Bytecode_V
        Bytecode_Opcode,
        Bytecode_RS1,
        Bytecode_RS2,
        Bytecode_RD,
        Bytecode_Imm,

        RAM_A,
        // Ram_V
        RAM_Read_RD,
        RAM_Read_RS1,
        RAM_Read_RS2,
        RAM_Read_Byte0,
        RAM_Read_Byte1,
        RAM_Read_Byte2,
        RAM_Read_Byte3,
        RAM_Write_RD,
        RAM_Write_Byte0,
        RAM_Write_Byte1,
        RAM_Write_Byte2,
        RAM_Write_Byte3,

        ChunksX_0,
        ChunksX_1,
        ChunksX_2,
        ChunksX_3,

        ChunksY_0,
        ChunksY_1,
        ChunksY_2,
        ChunksY_3,

        ChunksQ_0,
        ChunksQ_1,
        ChunksQ_2,
        ChunksQ_3,

        LookupOutput,

        // TODO(sragss): Better names for first 2.
        OpFlags0,
        OpFlags1,
        OpFlags_IsLoad,
        OpFlags_IsStore,
        OpFlags_IsJmp,
        OpFlags_IsBranch,
        OpFlags_LookupOutToRd,
        OpFlags_SignImm,
        OpFlags_IsConcat,

        // Instruction Flags
        IF_Add,
        IF_Sub,
        IF_And,
        IF_Or,
        IF_Xor,
        IF_Lb,
        IF_Lh,
        IF_Sb,
        IF_Sh,
        IF_Sw,
        IF_Beq,
        IF_Bge,
        IF_Bgeu,
        IF_Bne,
        IF_Slt,
        IF_Sltu,
        IF_Sll,
        IF_Sra,
        IF_Srl,
    }
    impl_r1cs_input_lc_conversions!(JoltInputs);
    impl ConstraintInput for JoltInputs {}

    const PC_START_ADDRESS: i64 = 0x80000000;
    const PC_NOOP_SHIFT: i64 = 4;
    const MEMORY_START: i64 = 128; // TODO(sragss): Non constant.
    const LOG_M: usize = 16;
    const OPERAND_SIZE: usize = LOG_M / 2;


    #[test]
    fn jolt() {
        let mut builder = R1CSBuilder::<Fr, JoltInputs>::new();

        struct JoltConstraints();
        impl<F: JoltField> R1CSConstraintBuilder<F> for JoltConstraints {
            type Inputs = JoltInputs;
            fn build_constraints(&self, cs: &mut R1CSBuilder<F, Self::Inputs>) {
                let op_flag_inputs = input_range!(JoltInputs::OpFlags0, JoltInputs::OpFlags_IsConcat);
                for op_flag_input in op_flag_inputs {
                    cs.constrain_binary(op_flag_input);
                }
                for instruction_flag_input in input_range!(JoltInputs::IF_Add, JoltInputs::IF_Srl) {
                    cs.constrain_binary(instruction_flag_input);
                }

                cs.constrain_eq(JoltInputs::PcIn, JoltInputs::Bytecode_A);

                cs.constrain_pack_be(op_flag_inputs.to_vec(), JoltInputs::Bytecode_Opcode, 1);

                let ram_writes = input_range!(JoltInputs::RAM_Read_Byte0, JoltInputs::RAM_Read_Byte3);
                let packed_load_store = cs.allocate_pack_le(ram_writes.to_vec(), 8);

                let real_pc = LC::sum2(4i64 * JoltInputs::PcIn, PC_START_ADDRESS + PC_NOOP_SHIFT);
                let x = cs.allocate_if_else(JoltInputs::OpFlags0, JoltInputs::RAM_Read_RS1, real_pc);
                let y = cs.allocate_if_else(JoltInputs::OpFlags1, JoltInputs::RAM_Read_RS2, JoltInputs::Bytecode_Imm);

                let signed_output = LC::sub2(JoltInputs::Bytecode_Imm, 0xffffffffi64 - 1i64); // TODO(sragss): Comment about twos-complement.
                let imm_signed = cs.allocate_if_else(JoltInputs::OpFlags_SignImm, JoltInputs::Bytecode_Imm, signed_output);

                let flag_0_or_1_condition = LC::sum2(JoltInputs::OpFlags0, JoltInputs::OpFlags1);
                cs.constrain_eq_conditional(flag_0_or_1_condition, LC::sum2(JoltInputs::RAM_Read_RS1, imm_signed), LC::sum2(JoltInputs::RAM_A, MEMORY_START));

                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsLoad, JoltInputs::RAM_Read_Byte0, JoltInputs::RAM_Write_Byte0);
                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsLoad, JoltInputs::RAM_Read_Byte1, JoltInputs::RAM_Write_Byte1);
                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsLoad, JoltInputs::RAM_Read_Byte2, JoltInputs::RAM_Write_Byte2);
                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsLoad, JoltInputs::RAM_Read_Byte3, JoltInputs::RAM_Write_Byte3);

                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsStore, packed_load_store, JoltInputs::LookupOutput);

                let packed_query = cs.allocate_pack_be(input_range!(JoltInputs::ChunksQ_0, JoltInputs::ChunksQ_3).to_vec(), LOG_M);
                cs.constrain_eq_conditional(JoltInputs::IF_Add, packed_query, x + y);
                cs.constrain_eq_conditional(JoltInputs::IF_Sub, packed_query, x - y); // TODO(sragss): Twos complement.
                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsLoad, packed_query, packed_load_store);
                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsStore, packed_query, JoltInputs::RAM_Read_RS2);

                // TODO(sragss): BE or LE
                // TODO(sragss): Uses 2 excess constraints for condition gating. Could make constrain_pack_be_conditional... Or make everything conditional...
                let chunked_x = cs.allocate_pack_be(input_range!(JoltInputs::ChunksX_0, JoltInputs::ChunksX_3).to_vec(), OPERAND_SIZE);
                let chunked_y= cs.allocate_pack_be(input_range!(JoltInputs::ChunksY_0, JoltInputs::ChunksY_3).to_vec(), OPERAND_SIZE);
                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsConcat, chunked_x, x);
                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsConcat, chunked_y, y);

                // TODO(sragss): Some concat bullshit here.

                // if (rd != 0 && if_update_rd_with_lookup_output == 1) constrain(rd_val == LookupOutput)
                // if (rd != 0 && is_jump_instr == 1) constrain(rd_val == 4 * PC)
                let rd_nonzero_and_lookup_to_rd = cs.allocate_prod(JoltInputs::Bytecode_RD, JoltInputs::OpFlags_LookupOutToRd);
                cs.constrain_eq_conditional(rd_nonzero_and_lookup_to_rd, JoltInputs::RAM_Write_RD, JoltInputs::LookupOutput);
                let rd_nonzero_and_jmp = cs.allocate_prod(JoltInputs::Bytecode_RD, JoltInputs::OpFlags_IsJmp);
                let lhs = LC::sum2(JoltInputs::PcIn, PC_START_ADDRESS - PC_NOOP_SHIFT);
                let rhs = JoltInputs::RAM_Write_RD;
                cs.constrain_eq_conditional(rd_nonzero_and_jmp, lhs, rhs);


                // TODO(sragss): PC incrementing constraints. Next PC: Check if it's a branch and the lookup output is 1. Check if it's a jump.

            }
        }

        let jolt_constraints = JoltConstraints();
        jolt_constraints.build_constraints(&mut builder);

        todo!()
    }
}
















