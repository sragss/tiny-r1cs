use ark_ff::PrimeField;
use strum::IntoEnumIterator;
use strum_macros::{EnumCount, EnumIter};



pub trait R1CSInputType: Clone + Copy + IntoEnumIterator {}

#[derive(EnumIter, Clone, Copy)]
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


#[derive(EnumIter, Clone, Copy)]
enum InputConfigTowerField {
    PcIn,
    PcOut
}
impl R1CSInputType for InputConfigTowerField {}







#[derive(Clone, Copy, Debug)]
enum Variable<I: R1CSInputType> {
    Input(I),
    Auxiliary(usize),
    Constant,
}
struct Constraint<I: R1CSInputType> {
    a: Vec<(Variable<I>, i64)>,
    b: Vec<(Variable<I>, i64)>,
    c: Vec<(Variable<I>, i64)>,
}






trait R1CSConstraintSubset<F> {
    type Inputs: R1CSInputType;

    fn constraints(&self) -> Vec<Constraint<Self::Inputs>>;

    fn compute_aux(&self) -> Vec<F>;
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
#[derive(Clone, EnumIter, EnumCount)]
// #[enum_dispatch(JoltInstruction)]
pub enum RV32IPrimeField {
    ADD(AddInstruction),
    SUB(SubInstruction)
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