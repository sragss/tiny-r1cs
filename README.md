# tiny-r1cs
*Repo to try out a simple R1CS programming API likely to be used in [Jolt](https://github.com/a16z/jolt)*

Known issues:
- Linear combinations do not auto validate or combine like terms


```rust
#[derive(EnumIter, EnumCount, Clone, Copy, Debug, PartialEq)]
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
impl ConstraintInput for InputConfigPrimeField {}
impl_r1cs_input_lc_conversions!(InputConfigPrimeField);
```