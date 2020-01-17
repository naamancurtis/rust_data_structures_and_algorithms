//! # Recursion
//!
//! This library contains the recursive solutions to some common programming problems (mainly mathematical in nature)

use std::ops::Mul;

/// Write out a function that works out the factorial for any given integer
///
/// # Examples
/// ```rust
/// use problem_solving_patterns::recursion::factorial;
///
/// let result = factorial(4);
/// assert_eq!(result, 24);
/// ```
pub fn factorial(num: u32) -> u32 {
    if num == 0 || num == 1 {
        return 1;
    }
    num * factorial(num - 1)
}

#[cfg(test)]
mod factorial_tests {
    use super::*;

    #[test]
    fn test_zero() {
        let result = factorial(0);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_one() {
        let result = factorial(1);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_two() {
        let result = factorial(2);
        assert_eq!(result, 2);
    }

    #[test]
    fn test_seven() {
        let result = factorial(7);
        assert_eq!(result, 5040);
    }
}

/// Write out a function that accepts a number and returns the nth number in the
/// Fibonacci sequence.
///
/// # Examples
/// ```rust
/// use problem_solving_patterns::recursion::fibonacci;
///
/// let result = fibonacci(4);
/// assert_eq!(result, 3);
/// ```
pub fn fibonacci(num: i32) -> i32 {
    if num == 0 || num == 1 {
        return num;
    }
    fibonacci(num - 2) + fibonacci(num - 1)
}

#[cfg(test)]
mod fibonacci_tests {
    use super::*;

    #[test]
    fn test_ten() {
        let result = fibonacci(10);
        assert_eq!(result, 55);
    }

    #[test]
    fn test_twenty_eight() {
        let result = fibonacci(28);
        assert_eq!(result, 317811);
    }

    #[test]
    fn test_thirty_five() {
        let result = fibonacci(35);
        assert_eq!(result, 9227465);
    }
}

/// Write out a function that takes two positive integers, a base and an exponent, and recursively
/// calculates the power of the base to the exponent.
///
/// # Examples
/// ```rust
/// use problem_solving_patterns::recursion::power;
///
/// let result = power(2, 2);
/// assert_eq!(result, 4);
/// ```
pub fn power(base: i32, exponent: i32) -> i32 {
    assert!(base > 0 && exponent >= 0);
    if exponent == 0 {
        return 1;
    }
    base * power(base, exponent - 1)
}

#[cfg(test)]
mod power_tests {
    use super::*;

    #[test]
    fn test_exponent_zero() {
        let result = power(2, 0);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_exponent_cube() {
        let result = power(2, 3);
        assert_eq!(result, 8);
    }

    #[test]
    fn test_exponent_2() {
        let result = power(10, 4);
        assert_eq!(result, 10000);
    }
}

/// Write out a function that recursively calculates the product of an array
///
/// # Examples
/// ```rust
/// use problem_solving_patterns::recursion::product_of_array;
///
/// let result = product_of_array(&vec![1,2,3,4]);
/// assert_eq!(result, 24);
/// ```
///
/// This has been implemented recusively inline with the challenge, however in reality
/// something like this is much more effectively done with something like:
///
/// ```text
/// let product = collection.iter().fold(1i32, |a, &b| a * b);
/// // or
/// let product = collection.iter().product::<i32>();
/// ```
///
pub fn product_of_array<T>(arr: &[T]) -> T
where
    T: Copy + Mul<T, Output = T> + From<i32>,
{
    if arr.is_empty() {
        return 1.into();
    }
    arr[0] * product_of_array(&arr[1..])
}

#[cfg(test)]
mod product_of_array_tests {
    use super::*;

    #[test]
    fn test_1() {
        let result = product_of_array(&vec![1, 2, 3]);
        assert_eq!(result, 6);
    }

    #[test]
    fn test_2() {
        let result = product_of_array(&vec![1, 2, 3, 10]);
        assert_eq!(result, 60);
    }
}
