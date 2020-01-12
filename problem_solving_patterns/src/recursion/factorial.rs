/// ## Recursion: Factorial Challenge
/// Write out a function that works out the factorial of any given integer
///
/// ```
/// use problem_solving_patterns::recursion::factorial::recursive_factorial;
///
/// fn test_four() {
///     let result = recursive_factorial(4);
///     assert_eq!(result, 24);
/// }
///
pub fn recursive_factorial(num: i32) -> i32 {
    assert!(num >= 0);
    if num == 0 || num == 1 {
        return 1;
    }
    num * recursive_factorial(num - 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero() {
        let result = recursive_factorial(0);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_one() {
        let result = recursive_factorial(1);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_two() {
        let result = recursive_factorial(2);
        assert_eq!(result, 2);
    }

    #[test]
    fn test_seven() {
        let result = recursive_factorial(7);
        assert_eq!(result, 5040);
    }
}
