//! # Radix Sort
//!
//! Radix Sort an integer sorting algorithm that sorts data with integer keys instead of
//! performing comparisons between values.
//!
//! Elements are parsed right to left one digit at a time and grouped into buckets on each iteration
//! (where the number of buckets is dictated by the _numerical base_ of the integer)
//!
//! - Time Complexity: **O**( d(n + b)) where:
//!     - `d` _is the number of digits in each number_
//!     - `n` _is the number of numbers_
//!     - `b` _is the numerical base of the number_
//!     - As such, in the event that `d` is constant and `b` isn't much greater than `n`, the sort can be carried out in approximately linear time
//!
//! - Space Complexity: **O**( bn )

const NUMERICAL_BASE: u32 = 10;

/// Takes a `Vec<u32>` and returns a `Vec<u32>` sorted in ascending order
///
/// Sorting occurs without comparison between numbers
///
/// # Examples
/// ```rust
/// use sorting::radix_sort::radix_sort;
///
/// let arr = vec![10, 20, 1, 3, 50, 30, 39, 2783, 9539, 2303, 1283, 2, 3, 6, 50];
/// let mut expected = arr.clone();
///
/// expected.sort();
/// let result = radix_sort(arr);
///
/// assert_eq!(result, expected)
/// ```
pub fn radix_sort(mut arr: Vec<u32>) -> Vec<u32> {
    if arr.len() <= 1 {
        return arr;
    }

    let mut max_digit_count = 0;
    let mut i = 0;

    loop {
        let mut buckets: Vec<Vec<u32>> = vec![Vec::with_capacity(arr.len() / 2); 10];

        arr.iter().for_each(|digit| {
            // On the first iteration of the loop, work out the largest digit number in the array
            if i == 0 {
                let digit_count = digit_count(*digit);
                if digit_count > max_digit_count {
                    max_digit_count = digit_count;
                }
            }
            let digit_index = get_digit(*digit as u64, i);
            buckets[digit_index].push(*digit);
        });

        arr = buckets
            .to_owned()
            .iter()
            .flatten()
            .cloned()
            .collect::<Vec<u32>>();

        i += 1;

        if i > max_digit_count {
            break;
        }
    }
    arr
}

/// This function takes a positive integer and an index and returns the digit at that index.
///
/// Numbers are indexed from right to left, with the `0-9` being index `[0]`, the `10s`
/// being index `[1]`, the `100s` being index `[2]` etc.
///
/// Note: Assumes base 10 numerical system
///
/// If the index is greater than the total number of digits, then 0 is returned
fn get_digit(number: u64, index: u32) -> usize {
    let base = NUMERICAL_BASE as u64;
    ((number / base.pow(index)) % base) as usize
}

#[test]
fn test_get_digit_single_digit() {
    assert_eq!(get_digit(1, 0), 1)
}

#[test]
fn test_get_digit_single_digit_2() {
    assert_eq!(get_digit(2, 0), 2)
}

#[test]
fn test_get_digit_at_positive() {
    assert_eq!(get_digit(12345, 2), 3)
}

#[test]
fn test_get_digit_over_length() {
    assert_eq!(get_digit(12345, 10), 0)
}

#[test]
fn test_get_digit_zero() {
    assert_eq!(get_digit(0, 1), 0)
}

/// Returns the total number of digits in a number
///
/// Note: Assumes base 10 numerical system
fn digit_count(num: u32) -> u32 {
    if num == 0 {
        return 1;
    }
    let num = num as f32;
    num.log10() as u32 + 1
}

#[test]
fn test_digit_count_zero() {
    assert_eq!(digit_count(0), 1)
}

#[test]
fn test_digit_count_positive() {
    assert_eq!(digit_count(12345), 5)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_vec() {
        let arr: Vec<u32> = vec![];
        let expected: Vec<u32> = vec![];
        let result = radix_sort(arr);
        assert_eq!(result, expected)
    }

    #[test]
    fn test_same_digit_vec() {
        let arr: Vec<u32> = vec![1, 1, 1, 1, 1, 1];
        let expected: Vec<u32> = vec![1, 1, 1, 1, 1, 1];
        let result = radix_sort(arr);
        assert_eq!(result, expected)
    }

    #[test]
    fn test_almost_same_digit_vec() {
        let arr: Vec<u32> = vec![1, 1, 2, 1, 1, 1];
        let expected: Vec<u32> = vec![1, 1, 1, 1, 1, 2];
        let result = radix_sort(arr);
        assert_eq!(result, expected)
    }

    #[test]
    fn test_almost_same_digit_vec_start() {
        let arr: Vec<u32> = vec![2, 1, 1, 1, 1, 1];
        let expected: Vec<u32> = vec![1, 1, 1, 1, 1, 2];
        let result = radix_sort(arr);
        assert_eq!(result, expected)
    }

    #[test]
    fn test_almost_same_digit_vec_end() {
        let arr: Vec<u32> = vec![1, 1, 1, 1, 1, 2];
        let expected: Vec<u32> = vec![1, 1, 1, 1, 1, 2];
        let result = radix_sort(arr);
        assert_eq!(result, expected)
    }

    #[test]
    fn test_sorted() {
        let arr: Vec<u32> = vec![1, 2, 3, 4, 5, 6, 7];
        let expected: Vec<u32> = vec![1, 2, 3, 4, 5, 6, 7];
        let result = radix_sort(arr);
        assert_eq!(result, expected)
    }

    #[test]
    fn test_reverse_sorted() {
        let arr: Vec<u32> = vec![7, 6, 5, 4, 3, 2, 1];
        let expected: Vec<u32> = vec![1, 2, 3, 4, 5, 6, 7];
        let result = radix_sort(arr);
        assert_eq!(result, expected)
    }
}
