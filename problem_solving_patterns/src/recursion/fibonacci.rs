/// ## Recursion: Fibonacci Challenge
/// Write out a function that accepts a number and returns the nth number in the
/// Fibonacci sequence.
///
/// ```
/// use problem_solving_patterns::recursion::fibonacci::recursive_fibonacci;
///
/// fn test_four() {
///     let result = recursive_fibonacci(4);
///     assert_eq!(result, 3);
/// }
///
pub fn recursive_fibonacci(num: i32) -> i32 {
    if num == 0 || num == 1 {
        return num;
    }
    recursive_fibonacci(num - 2) + recursive_fibonacci(num - 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ten() {
        let result = recursive_fibonacci(10);
        assert_eq!(result, 55);
    }

    #[test]
    fn test_twenty_eight() {
        let result = recursive_fibonacci(28);
        assert_eq!(result, 317811);
    }

    #[test]
    fn test_thirty_five() {
        let result = recursive_fibonacci(35);
        assert_eq!(result, 9227465);
    }
}
