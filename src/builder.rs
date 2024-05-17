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
            a: Term(left, 1) - Term(right, 1),
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
        // left - right == 0
        let left: LC<I> = left.into();
        let right: LC<I> = right.into();

        let a = left - right.clone();
        let b = Variable::Constant.into();
        let constraint = Constraint {
            a,
            b,
            c: LC(vec![])
        };
        println!("constraint {:?}", constraint);
        self.constraints.push(constraint);
    }

    fn constrain_eq_conditional(&mut self, condition: impl Into<LC<I>>, left: impl Into<LC<I>>, right: impl Into<LC<I>>) {
        // condition  * (left - right) == 0
        let condition: LC<I> = condition.into();
        let left: LC<I> = left.into();
        let right: LC<I> = right.into();

        let a = condition;
        let b = left - right;
        let c = LC(vec![]);;
        let constraint = Constraint { a, b, c };
        self.constraints.push(constraint);
    }

    fn constrain_binary(&mut self, value: impl Into<LC<I>>) {
        let one: LC<I> = Variable::Constant.into();
        let value: LC<I> = value.into();
        // value * (1 - value)
        let constraint = Constraint {
            a: value.clone(),
            b: one - value,
            c: LC(vec![])
        };
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
    fn allocate_if_else(&mut self, condition: impl Into<LC<I>>, result_true: impl Into<LC<I>>, result_false: impl Into<LC<I>>) -> Variable<I> {
        let result = Variable::Auxiliary(self.next_aux);
        self.next_aux += 1;

        self.constrain_if_else(condition, result_true, result_false, result);
        result
    }

    // TODO(sragss): Technically we could use unpacked: Vec<LC<I>> here easily, but it feels like it would confuse the API.
    fn constrain_pack_le(
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
    fn allocate_pack_le(&mut self, unpacked: Vec<Variable<I>>, operand_bits: usize) -> Variable<I> {
        let result = Variable::Auxiliary(self.next_aux);
        self.next_aux += 1;

        self.constrain_pack_le(unpacked, result, operand_bits);
        result
    }

    fn constrain_pack_be(
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
    fn allocate_pack_be(&mut self, unpacked: Vec<Variable<I>>, operand_bits: usize) -> Variable<I> {
        let result = Variable::Auxiliary(self.next_aux);
        self.next_aux += 1;

        self.constrain_pack_be(unpacked, result, operand_bits);
        result
    }

    /// Constrain x * y == z
    fn constrain_prod(&mut self, x: impl Into<LC<I>>, y: impl Into<LC<I>>, z: impl Into<LC<I>>) {
        let constraint = Constraint {
            a: x.into(),
            b: y.into(),
            c: z.into()
        };
        self.constraints.push(constraint);
    }

    #[must_use]
    fn allocate_prod(&mut self, x: impl Into<LC<I>>, y: impl Into<LC<I>>) -> Variable<I> {
        let result = Variable::Auxiliary(self.next_aux);
        self.next_aux += 1;

        self.constrain_prod(x, y, result);
        result
    }
}






trait R1CSConstraintBuilder<F: PrimeField> {
    type Inputs: R1CSInputType;

    fn build_constraints(&self, builder: &mut R1CSBuilder<F, Self::Inputs>);
}


#[cfg(test)]
mod tests {
    use crate::{impl_auto_conversions, enum_range, input_enum_range};

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
        assert_eq!(num_vars, inputs.len());

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

    #[allow(non_camel_case_types)]
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
        assert_eq!(builder.constraints.len(), 2);
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

    #[test]
    fn packing_le_builder() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // pack_le(OpFlags0, OpFlags1, OpFlags2, OpFlags3) == BytecodeA
        struct TestConstraints();
        impl<F: PrimeField> R1CSConstraintBuilder<F> for TestConstraints {
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
    fn packing_be_builder() {
        let mut builder = R1CSBuilder::<Fr, TestInputs>::new();

        // pack_be(OpFlags0, OpFlags1, OpFlags2, OpFlags3) == BytecodeA
        struct TestConstraints();
        impl<F: PrimeField> R1CSConstraintBuilder<F> for TestConstraints {
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
        // OpFlags2 * OpFlags3 == Au
        struct TestConstraints();
        impl<F: PrimeField> R1CSConstraintBuilder<F> for TestConstraints {
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
        z[TestInputs::COUNT] = 36;
        assert!(!constraint_is_sat(&builder.constraints[1], &z));
    }

    #[allow(non_camel_case_types)]
    #[derive(EnumIter, EnumCount, Clone, Copy, Debug)]
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
    impl R1CSInputType for JoltInputs {}
    impl_auto_conversions!(JoltInputs);

    const PC_START_ADDRESS: i64 = 0x80000000;
    const PC_NOOP_SHIFT: i64 = 4;
    const MEMORY_START: i64 = 128; // TODO(sragss): Non constant.
    const LOG_M: usize = 16;
    const OPERAND_SIZE: usize = LOG_M / 2;


    #[test]
    fn jolt() {
        let mut builder = R1CSBuilder::<Fr, JoltInputs>::new();

        struct JoltConstraints();
        impl<F: PrimeField> R1CSConstraintBuilder<F> for JoltConstraints {
            type Inputs = JoltInputs;
            fn build_constraints(&self, cs: &mut R1CSBuilder<F, Self::Inputs>) {
                let op_flag_inputs = input_enum_range!(JoltInputs::OpFlags0, JoltInputs::OpFlags_IsConcat);
                for op_flag_input in op_flag_inputs {
                    cs.constrain_binary(op_flag_input);
                }
                for instruction_flag_input in input_enum_range!(JoltInputs::IF_Add, JoltInputs::IF_Srl) {
                    cs.constrain_binary(instruction_flag_input);
                }

                cs.constrain_eq(JoltInputs::PcIn, JoltInputs::Bytecode_A);

                cs.constrain_pack_be(op_flag_inputs.to_vec(), JoltInputs::Bytecode_Opcode, 1);

                let ram_writes = input_enum_range!(JoltInputs::RAM_Read_Byte0, JoltInputs::RAM_Read_Byte3);
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

                let packed_query = cs.allocate_pack_be(input_enum_range!(JoltInputs::ChunksQ_0, JoltInputs::ChunksQ_3).to_vec(), LOG_M);
                cs.constrain_eq_conditional(JoltInputs::IF_Add, packed_query, x + y);
                cs.constrain_eq_conditional(JoltInputs::IF_Sub, packed_query, x - y); // TODO(sragss): Twos complement.
                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsLoad, packed_query, packed_load_store);
                cs.constrain_eq_conditional(JoltInputs::OpFlags_IsStore, packed_query, JoltInputs::RAM_Read_RS2);

                // TODO(sragss): BE or LE
                // TODO(sragss): Uses 2 excess constraints for condition gating. Could make constrain_pack_be_conditional... Or make everything conditional...
                let chunked_x = cs.allocate_pack_be(input_enum_range!(JoltInputs::ChunksX_0, JoltInputs::ChunksX_3).to_vec(), OPERAND_SIZE);
                let chunked_y= cs.allocate_pack_be(input_enum_range!(JoltInputs::ChunksY_0, JoltInputs::ChunksY_3).to_vec(), OPERAND_SIZE);
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

    /// a - b -> LC
    fn sub2(a: impl Into<LC<I>>, b: impl Into<LC<I>>) -> Self {
        let a: LC<I> = a.into();
        let b: LC<I> = b.into();

        a - b
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

impl<I: R1CSInputType> std::ops::Add for Term<I> {
    type Output = LC<I>;

    fn add(self, other: Self) -> Self::Output {
        LC(vec![self, other])
    }
}

impl<I: R1CSInputType> std::ops::Sub for Term<I> {
    type Output = LC<I>;

    fn sub(self, other: Self) -> Self::Output {
        LC(vec![self, -other])
    }
}












// Implementations for Term<I>
impl<I: R1CSInputType> std::ops::Neg for Term<I> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Term(self.0, self.1 * -1)
    }
}

impl<I: R1CSInputType> Into<Term<I>> for i64 {
    fn into(self) -> Term<I> {
        Term(Variable::Constant, self)
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

impl<I: R1CSInputType> std::ops::Add for Variable<I> {
    type Output = LC<I>;

    fn add(self, other: Self) -> Self::Output {
        LC(vec![Term(self, 1), Term(other, 1)])
    }
}
impl<I: R1CSInputType> std::ops::Sub for Variable<I> {
    type Output = LC<I>;

    fn sub(self, other: Self) -> Self::Output {
        LC(vec![Term(self, 1), Term(other, -1)])
    }
}

// Implementations for LC<I>
impl<I: R1CSInputType> Into<LC<I>> for i64 {
    fn into(self) -> LC<I> {
        LC(vec![Term(Variable::Constant, self)])
    }
}

impl<I: R1CSInputType> Into<LC<I>> for Variable<I> {
    fn into(self) -> LC<I> {
        LC(vec![Term(self, 1)])
    }
}

impl<I: R1CSInputType> Into<LC<I>> for Term<I> {
    fn into(self) -> LC<I> {
        LC(vec![self])
    }
}

impl<I: R1CSInputType> Into<LC<I>> for Vec<Term<I>> {
    fn into(self) -> LC<I> {
        LC(self)
    }
}

impl<I: R1CSInputType> std::ops::Neg for LC<I> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let neg_terms = self.0.into_iter().map(|term| -term).collect();
        LC(neg_terms)
    }
}

// Implementations for Variable<I>
impl<I: R1CSInputType> std::ops::Mul<i64> for Variable<I> {
    type Output = Term<I>;

    fn mul(self, other: i64) -> Self::Output {
        Term(self, other)
    }
}

impl<I: R1CSInputType> std::ops::Mul<Variable<I>> for i64 {
    type Output = Term<I>;

    fn mul(self, other: Variable<I>) -> Self::Output {
        Term(other, self)
    }
}


// For each R1CS config, these need to be written concretely for the R1CSInputType
#[macro_export]
macro_rules! impl_auto_conversions {
    ($ConcreteInput:ty) => {
        impl Into<usize> for $ConcreteInput {
            fn into(self) -> usize {
                self as usize
            }
        }
        impl Into<Variable<$ConcreteInput>> for $ConcreteInput {
            fn into(self) -> Variable<$ConcreteInput> {
                Variable::Input(self)
            }
        }

        impl Into<(Variable<$ConcreteInput>, i64)> for $ConcreteInput {
            fn into(self) -> (Variable<$ConcreteInput>, i64) {
                (Variable::Input(self), 1)
            }
        }
        impl Into<Term<$ConcreteInput>> for $ConcreteInput {
            fn into(self) -> Term<$ConcreteInput> {
                Term(Variable::Input(self), 1)
            }
        }

        impl Into<Term<$ConcreteInput>> for ($ConcreteInput, i64) {
            fn into(self) -> Term<$ConcreteInput> {
                Term(Variable::Input(self.0), self.1)
            }
        }

        impl Into<LC<$ConcreteInput>> for $ConcreteInput {
            fn into(self) -> LC<$ConcreteInput> {
                LC(vec![Term(Variable::Input(self), 1)])
            }
        }

        impl Into<LC<$ConcreteInput>> for Vec<$ConcreteInput> {
            fn into(self) -> LC<$ConcreteInput> {
                let terms: Vec<Term<$ConcreteInput>> = self.into_iter().map(Into::into).collect();
                LC(terms)
            }
        }

        impl std::ops::Mul<i64> for $ConcreteInput {
            type Output = Term<$ConcreteInput>;

            fn mul(self, rhs: i64) -> Self::Output {
                Term(Variable::Input(self), rhs)
            }
        }

        impl std::ops::Mul<$ConcreteInput> for i64 {
            type Output = Term<$ConcreteInput>;

            fn mul(self, rhs: $ConcreteInput) -> Self::Output {
                Term(Variable::Input(rhs), self)
            }
        }
        
    };
}

#[macro_export]
macro_rules! enum_range {
    ($start:path, $end:path) => {
        {
            let mut arr = [$start; ($end as usize) - ($start as usize) + 1];
            for i in ($start as usize)..=($end as usize) {
                arr[i - ($start as usize)] = unsafe { std::mem::transmute::<usize, _>(i) };
            }
            arr
        }
    };
}

#[macro_export]
macro_rules! input_enum_range {
    ($start:path, $end:path) => {
        {
            let mut arr = [Variable::Input($start); ($end as usize) - ($start as usize) + 1];
            for i in ($start as usize)..=($end as usize) {
                arr[i - ($start as usize)] = Variable::Input(unsafe { std::mem::transmute::<usize, _>(i) });
            }
            arr
        }
    };
}

impl_auto_conversions!(InputConfigPrimeField);
