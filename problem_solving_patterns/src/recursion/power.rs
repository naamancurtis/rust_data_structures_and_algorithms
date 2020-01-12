/// ## Recursion: Power Challenge
/// Write out a function that takes two positive integers, a base and an exponent, and recursively
/// calculates the power of the base to the exponent.
///
/// ```
/// use problem_solving_patterns::recursion::power::recursive_power;
///
/// fn test_valid_substring() {
///     let result = recursive_power(2, 2);
///     assert_eq!(result, 4);
/// }
///
pub fn recursive_power(base: i32, exponent: i32) -> i32 {
    assert!(base > 0 && exponent >= 0);
    if exponent == 0 {
        return 1;
    }
    base * recursive_power(base, exponent - 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_exponent_zero() {
        let result = recursive_power(2, 0);
        assert_eq!(result, 1);
    }

    #[test]
    fn test_exponent_cube() {
        let result = recursive_power(2, 3);
        assert_eq!(result, 8);
    }

    #[test]
    fn test_exponent_2() {
        let result = recursive_power(10, 4);
        assert_eq!(result, 10000);
    }
}
