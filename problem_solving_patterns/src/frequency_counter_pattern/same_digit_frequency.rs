use std::collections::HashMap;

/// ## Same Digit Frequency Challenge
/// Given two positive integers, find out if the two numbers have the same freqency of digits
///
/// ```
/// use problem_solving_patterns::frequency_counter_pattern::same_digit_frequency::same_digit_frequency;
///
/// fn test_valid_digits() {
///     let result = same_digit_frequency(123456, 654321);
///     assert_eq!(result, true);
/// }
/// ```
pub fn same_digit_frequency(num1: u32, num2: u32) -> bool {
    /*
        The only way of checking that two numbers have the same number of digits in
        (without converting to a string or array) is to loop over each digit in
        the number and count them. As such, no tangible time is saved in comparing
        the lengths of each number prior to carrying out the required logic for the
        algorithm
    */

    let mut map = HashMap::new();

    // Base for the numerical system
    let base = 10;

    let mut number_to_loop_over = num1;

    // Loop over the first number
    while number_to_loop_over != 0 {
        let key = number_to_loop_over % base;
        match map.get_mut(&key) {
            Some(count) => *count += 1,
            _ => {
                map.insert(key, 1);
            }
        }
        number_to_loop_over /= base;
    }

    let mut number_to_loop_over = num2;

    // Loop over the second number
    while number_to_loop_over != 0 {
        let key = number_to_loop_over % base;
        match map.get_mut(&key) {
            Some(count) if *count > 0 => *count -= 1,
            _ => {
                return false;
            }
        }
        number_to_loop_over /= base;
    }

    map.values().all(|digit| digit == &0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_same_digits() {
        let result = same_digit_frequency(11111, 11111);
        assert_eq!(result, true);
    }

    #[test]
    fn test_same_digits_different_length() {
        let result = same_digit_frequency(1111, 11111);
        assert_eq!(result, false);
    }

    #[test]
    fn test_same_digits_different_length_2() {
        let result = same_digit_frequency(11111, 1111);
        assert_eq!(result, false);
    }

    #[test]
    fn test_different_length_numbers() {
        let result = same_digit_frequency(123, 1234);
        assert_eq!(result, false);
    }

    #[test]
    fn test_different_length_numbers_2() {
        let result = same_digit_frequency(1234, 123);
        assert_eq!(result, false);
    }

    #[test]
    fn test_zero() {
        let result = same_digit_frequency(0, 123);
        assert_eq!(result, false);
    }
}
