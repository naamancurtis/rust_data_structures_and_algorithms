//! # Frequency Counter Pattern
//!
//! This pattern uses some form of constant time lookup data structure
//! to store frequencies of elements in an array.
//!
//! This allows for frequency counting to occur in **O**(n) time as opposed to requiring nested loops for comparisons.

use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;

/// Given a collection of arguments, identify if there are any duplicates in the collection
///
/// # Examples
/// ```rust
/// use problem_solving_patterns::frequency_counter_pattern::are_there_duplicates;
///
/// let result = are_there_duplicates(&vec![1,2,3,1]);
/// assert_eq!(result, true);
/// ```
pub fn are_there_duplicates<T>(arr: &[T]) -> bool
where
    T: Hash + Clone + Eq,
{
    let hash_set: HashSet<_> = arr.iter().collect();
    arr.len() != hash_set.len()
}

#[cfg(test)]
mod are_there_duplicates_tests {
    use super::*;

    #[test]
    fn test_no_duplicates() {
        let result = are_there_duplicates(&vec![1, 2, 3, 4]);
        assert_eq!(result, false);
    }

    #[test]
    fn test_multiple_duplicates() {
        let result = are_there_duplicates(&vec![1, 1, 2, 3, 3, 4]);
        assert_eq!(result, true);
    }

    #[test]
    fn test_empty_array() {
        let input: Vec<i32> = Vec::new();
        let result = are_there_duplicates(&input);
        assert_eq!(result, false);
    }
}

/// Given two positive integers, find out if the two numbers have the same frequency of digits.
///
/// # Examples
/// ```rust
/// use problem_solving_patterns::frequency_counter_pattern::same_digit_frequency;
///
/// let result = same_digit_frequency(123456, 654321);
/// assert_eq!(result, true);
/// ```
pub fn same_digit_frequency(num1: i32, num2: i32) -> bool {
    let num1 = num1.abs();
    let num2 = num2.abs();
    let digit_length_counter = |num: f32| -> i32 { num.log10() as i32 + 1 };

    if digit_length_counter(num1 as f32) != digit_length_counter(num2 as f32) {
        return false;
    }

    let mut map = HashMap::new();

    const NUMERICAL_BASE: i32 = 10;

    let mut number_to_loop_over = num1;

    // Loop over the first number
    while number_to_loop_over != 0 {
        let key = number_to_loop_over % NUMERICAL_BASE;
        match map.get_mut(&key) {
            Some(count) => *count += 1,
            _ => {
                map.insert(key, 1);
            }
        }
        number_to_loop_over /= NUMERICAL_BASE;
    }

    let mut number_to_loop_over = num2;

    // Loop over the second number
    while number_to_loop_over != 0 {
        let key = number_to_loop_over % NUMERICAL_BASE;
        match map.get_mut(&key) {
            Some(count) if *count > 0 => *count -= 1,
            _ => {
                return false;
            }
        }
        number_to_loop_over /= NUMERICAL_BASE;
    }

    map.values().all(|digit| digit == &0)
}

#[cfg(test)]
mod same_digit_frequency_tests {
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

/// Create a function that takes two strings and returns a boolean of whether one string
/// is an anagram for the other
///
/// # Examples
/// ```
/// use problem_solving_patterns::frequency_counter_pattern::valid_anagram;
///
/// let result = valid_anagram("anagram", "gramana");
/// assert_eq!(result, true);
/// ```
pub fn valid_anagram(string_1: &str, string_2: &str) -> bool {
    if string_1.len() != string_2.len() {
        return false;
    }

    let mut char_map = HashMap::new();

    for char in string_1.chars() {
        match char_map.get_mut(&char) {
            Some(count) => *count += 1,
            _ => {
                char_map.insert(char, 1);
            }
        }
    }

    for char in string_2.chars() {
        match char_map.get_mut(&char) {
            Some(count) if *count > 0 => *count -= 1,
            _ => return false,
        }
    }

    true
}

#[cfg(test)]
mod valid_anagram_tests {
    use super::*;

    #[test]
    fn test_valid_anagram_2() {
        let result = valid_anagram("abc", "cba");
        assert_eq!(result, true);
    }

    #[test]
    fn test_strings_of_different_length() {
        let result = valid_anagram("anagram", "gramanas");
        assert_eq!(result, false);
    }

    #[test]
    fn test_invalid_anagram() {
        let result = valid_anagram("anagram", "gramann");
        assert_eq!(result, false);
    }

    #[test]
    fn test_invalid_anagram_2() {
        let result = valid_anagram("anagram", "grammmm");
        assert_eq!(result, false);
    }
}
