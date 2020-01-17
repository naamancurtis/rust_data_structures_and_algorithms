//! # Multiple Pointers Pattern
//!
//! This pattern uses multiple pointers to track various comparisons and conditions throughout
//! a sorted array allowing dynamic comparisons to occur more effectively without the need
//! for nested loops

extern crate num;
extern crate unicode_segmentation;

use num::{Integer, Num, ToPrimitive};
use std::cmp::Ordering;
use std::iter::Sum;
use unicode_segmentation::UnicodeSegmentation;

/// Given a sorted collection of integers, find out if there are any pair of numbers within the
/// collection that when averaged equal the target value
///
/// ```rust
/// use problem_solving_patterns::multiple_pointers_pattern::average_pair;
///
/// let result = average_pair(&vec![1,2,3,4,5,6], 4.5);
/// assert_eq!(result, true);
/// ```
pub fn average_pair<I, N>(arr: &[I], target_average: N) -> bool
where
    I: Integer + ToPrimitive + PartialOrd + Sum<I> + Copy,
    N: Num + ToPrimitive + PartialOrd,
{
    if arr.len() < 2 {
        return false;
    }

    let mut pointer_1 = 0;
    let mut pointer_2 = arr.len() - 1;

    let average_fn = |ptr_1: usize, ptr_2: usize| -> f64 {
        (ToPrimitive::to_f64(&(arr[ptr_1] + arr[ptr_2])).unwrap() / 2f64)
    };

    let target_average = ToPrimitive::to_f64(&target_average).unwrap();
    let mut average = average_fn(pointer_1, pointer_2);

    while (average - target_average).abs() > 0.005 {
        if pointer_2 - pointer_1 == 1 {
            return false;
        }

        match average.partial_cmp(&target_average) {
            Some(Ordering::Less) => pointer_1 += 1,
            Some(Ordering::Greater) => pointer_2 -= 1,
            // We're handling the equals case within epsilon for the while loop
            _ => continue,
        }
        average = average_fn(pointer_1, pointer_2);
    }

    true
}

#[cfg(test)]
mod average_pair_tests {
    use super::*;

    #[test]
    fn test_valid_arguments_2() {
        let result = average_pair(&vec![1, 2, 3], 2.5);
        assert_eq!(result, true);
    }

    #[test]
    fn test_longer_array() {
        let result = average_pair(&vec![1, 3, 6, 7, 9, 10, 22, 25], 9.5);
        assert_eq!(result, true);
    }

    #[test]
    fn test_invalid_arguments() {
        let result = average_pair(&vec![-10, -3, 0, 1, 2, 3], 4.1);
        assert_eq!(result, false);
    }

    #[test]
    fn test_empty_array() {
        let arr: Vec<u8> = vec![];
        let result = average_pair(&arr, 10);
        assert_eq!(result, false);
    }
}

/// Create a function that accepts a sorted collection and returns a count of the number of unique
/// values in that array.
///
/// # Examples
/// ```rust
/// use problem_solving_patterns::multiple_pointers_pattern::count_unique;
///
/// let result = count_unique(&vec![1, 1, 1, 1, 2, 3, 4]);
/// assert_eq!(result, 4);
/// ```
pub fn count_unique<T>(collection: &[T]) -> u32
where
    T: PartialEq,
{
    if collection.is_empty() {
        return 0;
    }

    let mut pointer: usize = 0;
    let mut counter = 1;

    collection.iter().enumerate().for_each(|(index, value)| {
        if value != &collection[pointer] {
            counter += 1;
            pointer = index;
        }
    });

    counter
}

#[cfg(test)]
mod count_unique_tests {
    use super::*;

    #[test]
    fn parses_an_empty_vec() {
        let arr: [u32; 0] = [];
        let result = count_unique(&arr);
        assert_eq!(result, 0);
    }

    #[test]
    fn parses_a_i32_vec() {
        let result = count_unique(&vec![1, 2, 3, 4]);
        assert_eq!(result, 4);
    }

    #[test]
    fn parses_a_i32_vec_with_multiple_duplicate_values() {
        let result = count_unique(&vec![1, 1, 1, 1, 2, 2, 3, 3, 4, 10, 11]);
        assert_eq!(result, 6);
    }

    #[test]
    fn parses_a_i32_vec_with_negative_values() {
        let result = count_unique(&vec![-10, -5, 1, 1, 2, 2, 3, 3, 4, 10, 11]);
        assert_eq!(result, 8);
    }

    #[test]
    fn parses_a_str_vec() {
        let result = count_unique(&vec!["test", "test", "help"]);
        assert_eq!(result, 2);
    }

    #[test]
    fn parses_a_string_vec() {
        let result = count_unique(&vec![
            String::from("test"),
            String::from("test"),
            String::from("help"),
        ]);
        assert_eq!(result, 2);
    }
}

/// Given two strings, establish whether or not the first string is a subsequence of the second
///
/// ### Notes
/// The solution below stays true to the design pattern specified and creates a reliable method of
/// iterating over the characters in a string before carrying out the comparasion logic.
/// It does this because attempting to iterate over Rust strings can have unexpected
/// behaviour due to their implementation.
///
/// Although the above solution is reliable, works and is true to the design pattern,
/// it is likely a better solution can be found in the standard library - for example:
///
/// ```text
/// full_string.contains(sub_string.as_str())
/// ```
///
/// # Examples
/// ```rust
/// use problem_solving_patterns::multiple_pointers_pattern::is_subsequence;
///
/// let result = is_subsequence(String::from("test"), String::from("A test string"));
/// assert_eq!(result, true);
/// ```
pub fn is_subsequence(mut sub_string: String, mut full_string: String) -> bool {
    if sub_string.is_empty() || full_string.is_empty() || sub_string.len() > full_string.len() {
        return false;
    }

    sub_string.make_ascii_lowercase();
    full_string.make_ascii_lowercase();

    let sub_string =
        UnicodeSegmentation::graphemes(sub_string.as_str(), true).collect::<Vec<&str>>();
    let sub_string_length = sub_string.len();
    let full_string =
        UnicodeSegmentation::graphemes(full_string.as_str(), true).collect::<Vec<&str>>();

    let mut pointer_1 = 0;

    while pointer_1 <= full_string.len() - sub_string_length {
        if full_string[pointer_1] == sub_string[0]
            && full_string[pointer_1 + sub_string_length - 1] == sub_string[sub_string_length - 1]
        {
            for i in 1..sub_string_length {
                if full_string[pointer_1 + i] != sub_string[i] {
                    break;
                }
            }
            return true;
        }
        pointer_1 += 1;
    }
    false
}

#[cfg(test)]
mod is_subsequence_tests {
    use super::*;

    #[test]
    fn test_valid_substring_start() {
        let result = is_subsequence(String::from("test"), String::from("test a string"));
        assert_eq!(result, true);
    }

    #[test]
    fn test_valid_substring_end() {
        let result = is_subsequence(String::from("test"), String::from("A test"));
        assert_eq!(result, true);
    }

    #[test]
    fn test_one_word() {
        let result = is_subsequence(String::from("test"), String::from("thisisateststring"));
        assert_eq!(result, true);
    }

    #[test]
    fn test_case_insensitive() {
        let result = is_subsequence(String::from("test"), String::from("this is a TeSt string"));
        assert_eq!(result, true);
    }

    #[test]
    fn test_invalid_substring() {
        let result = is_subsequence(
            String::from("test"),
            String::from("There is nothing in this string"),
        );
        assert_eq!(result, false);
    }

    #[test]
    fn test_invalid_substring_start() {
        let result = is_subsequence(String::from("test"), String::from("tes this string"));
        assert_eq!(result, false);
    }

    #[test]
    fn test_invalid_substring_end() {
        let result = is_subsequence(String::from("test"), String::from("this tes"));
        assert_eq!(result, false);
    }

    #[test]
    fn test_empty_string() {
        let result = is_subsequence(String::from("Test"), String::from(""));
        assert_eq!(result, false);
    }

    #[test]
    fn test_empty_sub_string() {
        let result = is_subsequence(String::from(""), String::from("Test"));
        assert_eq!(result, false);
    }

    #[test]
    fn test_empty_strings() {
        let result = is_subsequence(String::from(""), String::from(""));
        assert_eq!(result, false);
    }

    #[test]
    fn test_sub_string_larger() {
        let result = is_subsequence(String::from("Testing"), String::from("test"));
        assert_eq!(result, false);
    }
}
