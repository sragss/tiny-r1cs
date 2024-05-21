use strum::IntoEnumIterator;

pub trait R1CSInputType: Clone + Copy + IntoEnumIterator {}

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

impl<I: R1CSInputType> Constraint<I> {
    pub fn eq(left: Variable<I>, right: Variable<I>) -> Self {
        // (left - right) * right = 0
        Self {
            a: vec![(left, 1), (right, -1)],
            b: vec![(Variable::Constant, 1)],
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
        // result - false_outcome = condition * true_outcome - condition * false_outcome
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
    use strum_macros::EnumIter;

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
