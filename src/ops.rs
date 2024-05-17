/// Defines the Linear Combination (LC) object and associated operations.
/// A LinearCombination is a vector of Terms, where each Term is a pair of a Variable and a coefficient.
 
use std::fmt::Debug;
use strum::{EnumCount, IntoEnumIterator};


pub trait ConstraintInput: Clone + Copy + Debug + PartialEq + IntoEnumIterator + EnumCount + Into<usize> {}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Variable<I: ConstraintInput> {
    Input(I),
    Auxiliary(usize),
    Constant,
}

#[derive(Clone, Copy, Debug)]
pub struct Term<I: ConstraintInput>(pub Variable<I>, pub i64);

/// Linear Combination of terms.
#[derive(Clone, Debug)]
pub struct LC<I: ConstraintInput>(Vec<Term<I>>);

impl<I: ConstraintInput> LC<I> {
    pub fn new(terms: Vec<Term<I>>) -> Self {
        LC(terms)
    }

    pub fn zero() -> Self {
        LC(vec![])
    }

    pub fn terms(&self) -> &[Term<I>] {
        &self.0
    }

    pub fn num_terms(&self) -> usize {
        self.0.len()
    }

    /// LC(a) + LC(b) -> LC(a + b)
    pub fn sum2(a: impl Into<Term<I>>, b: impl Into<Term<I>>) -> Self {
        LC(vec![a.into(), b.into()])
    }

    /// LC(a) - LC(b) -> LC(a - b)
    pub fn sub2(a: impl Into<LC<I>>, b: impl Into<LC<I>>) -> Self {
        let a: LC<I> = a.into();
        let b: LC<I> = b.into();

        a - b
    }
}


// Arithmetic for LC

impl<I: ConstraintInput> std::ops::Add for LC<I> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        let mut combined_terms = self.0;
        combined_terms.extend(other.0);
        LC(combined_terms)
    }
}

impl<I: ConstraintInput> std::ops::Neg for LC<I> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let neg_terms = self.0.into_iter().map(|term| -term).collect();
        LC(neg_terms)
    }
}

impl<I: ConstraintInput> std::ops::Sub for LC<I> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        let mut combined_terms = self.0;
        combined_terms.extend((-other).0);
        LC(combined_terms)
    }
}


// Arithmetic for Term<I>

impl<I: ConstraintInput> std::ops::Add for Term<I> {
    type Output = LC<I>;

    fn add(self, other: Self) -> Self::Output {
        LC(vec![self, other])
    }
}

impl<I: ConstraintInput> std::ops::Sub for Term<I> {
    type Output = LC<I>;

    fn sub(self, other: Self) -> Self::Output {
        LC(vec![self, -other])
    }
}

impl<I: ConstraintInput> std::ops::Neg for Term<I> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Term(self.0, self.1 * -1)
    }
}

impl<I: ConstraintInput> Into<Term<I>> for i64 {
    fn into(self) -> Term<I> {
        Term(Variable::Constant, self)
    }
}

impl<I: ConstraintInput> Into<Term<I>> for Variable<I> {
    fn into(self) -> Term<I> {
        Term(self, 1)
    }
}

impl<I: ConstraintInput> Into<Term<I>> for (Variable<I>, i64) {
    fn into(self) -> Term<I> {
        Term(self.0, self.1)
    }
}

impl<I: ConstraintInput> std::ops::Add for Variable<I> {
    type Output = LC<I>;

    fn add(self, other: Self) -> Self::Output {
        LC(vec![Term(self, 1), Term(other, 1)])
    }
}
impl<I: ConstraintInput> std::ops::Sub for Variable<I> {
    type Output = LC<I>;

    fn sub(self, other: Self) -> Self::Output {
        LC(vec![Term(self, 1), Term(other, -1)])
    }
}


// Into<LC<I>>

impl<I: ConstraintInput> Into<LC<I>> for i64 {
    fn into(self) -> LC<I> {
        LC(vec![Term(Variable::Constant, self)])
    }
}

impl<I: ConstraintInput> Into<LC<I>> for Variable<I> {
    fn into(self) -> LC<I> {
        LC(vec![Term(self, 1)])
    }
}

impl<I: ConstraintInput> Into<LC<I>> for Term<I> {
    fn into(self) -> LC<I> {
        LC(vec![self])
    }
}

impl<I: ConstraintInput> Into<LC<I>> for Vec<Term<I>> {
    fn into(self) -> LC<I> {
        LC(self)
    }
}


// Generic arithmetic for Variable<I>

impl<I: ConstraintInput> std::ops::Mul<i64> for Variable<I> {
    type Output = Term<I>;

    fn mul(self, other: i64) -> Self::Output {
        Term(self, other)
    }
}

impl<I: ConstraintInput> std::ops::Mul<Variable<I>> for i64 {
    type Output = Term<I>;

    fn mul(self, other: Variable<I>) -> Self::Output {
        Term(other, self)
    }
}


/// Conversions and arithmetic for concrete ConstraintInput
#[macro_export]
macro_rules! impl_r1cs_input_lc_conversions {
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
                Term(Variable::Input(self), 1).into()
            }
        }

        impl Into<LC<$ConcreteInput>> for Vec<$ConcreteInput> {
            fn into(self) -> LC<$ConcreteInput> {
                let terms: Vec<Term<$ConcreteInput>> = self.into_iter().map(Into::into).collect();
                LC::new(terms)
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

/// ```rust
/// use tiny_r1cs::enum_range;
/// #[derive(Debug, PartialEq, Clone, Copy)]
/// #[repr(usize)]
/// pub enum Ex {
///     A,
///     B,
///     C,
///     D
/// }
/// 
/// 
/// let range = enum_range!(Ex::B, Ex::D);
/// assert_eq!(range, [Ex::B, Ex::C, Ex::D]);
/// ```
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

/// ```rust
/// use tiny_r1cs::enum_range_wrap;
/// 
/// #[derive(Debug, PartialEq, Clone, Copy)]
/// #[repr(usize)]
/// pub enum Ex {
///     A,
///     B,
///     C,
///     D
/// }
/// 
/// #[derive(Debug, PartialEq, Clone, Copy)]
/// pub struct Wrapper<I>(I);
/// 
/// let range = enum_range_wrap!(Wrapper, Ex::B, Ex::D);
/// assert_eq!(range, [Wrapper(Ex::B), Wrapper(Ex::C), Wrapper(Ex::D)]);
/// 
/// #[derive(Debug, PartialEq, Clone, Copy)]
/// pub enum WrapperEnum<I> {
///     A(I),
///     B(I)
/// }
/// 
/// let range = enum_range_wrap!(WrapperEnum::A, Ex::B, Ex::D);
/// assert_eq!(range, [WrapperEnum::A(Ex::B), WrapperEnum::A(Ex::C), WrapperEnum::A(Ex::D)]);
/// ```
#[macro_export]
macro_rules! enum_range_wrap {
    ($InputWrapper:ident, $start:path, $end:path) => {
        {
            let mut arr = [$InputWrapper($start); ($end as usize) - ($start as usize) + 1];
            for i in ($start as usize)..=($end as usize) {
                arr[i - ($start as usize)] = $InputWrapper(unsafe { std::mem::transmute::<usize, _>(i) });
            }
            arr
        }
    };
    ($InputWrapper:ident::$Variant:ident, $start:path, $end:path) => {
        {
            let mut arr = [$InputWrapper::$Variant($start); ($end as usize) - ($start as usize) + 1];
            for i in ($start as usize)..=($end as usize) {
                arr[i - ($start as usize)] = $InputWrapper::$Variant(unsafe { std::mem::transmute::<usize, _>(i) });
            }
            arr
        }
    };
}

/// ```rust
/// use tiny_r1cs::input_range;
/// # use tiny_r1cs::enum_input_range;
/// # use tiny_r1cs::ops::{R1CSInputType, Variable};
/// # use strum_macros::{EnumCount, EnumIter};
/// 
/// # #[derive(Clone, Copy, Debug, PartialEq, EnumCount, EnumIter)]
/// #[repr(usize)]
/// pub enum Inputs {
///     A,
///     B,
///     C,
///     D
/// }
/// #
/// # impl Into<usize> for Inputs {
/// #   fn into(self) -> usize {
/// #       self as usize
/// #   }
/// # }
/// #
/// impl R1CSInputType for Inputs {};
/// 
/// let range = input_range!(Inputs::B, Inputs::D);
/// let expected_range = [Variable::Input(Inputs::B), Variable::Input(Inputs::C), Variable::Input(Inputs::D)];
/// assert_eq!(range, expected_range);
/// ```
#[macro_export]
macro_rules! input_range {
    ($start:path, $end:path) => {
        crate::enum_range_wrap!(Variable::Input, $start, $end)
    };
    ($Variant:ident, $start:path, $end:path) => {
        crate::enum_range_wrap!(Variable::Input::$Variant, $start, $end)
    };
}