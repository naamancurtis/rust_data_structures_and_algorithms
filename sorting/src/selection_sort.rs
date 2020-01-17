//! # Selection Sort
//!
//! Selection sort is a simple sorting algorithm that sorts an array by repeatedly finding
//! the minimum element from an unsorted portion of the array and placing it at the beginning
//!
//! - Time Complexity: **O**(n^2)
//! - Space Complexity: **O**(1)

use std::cmp::Ordering;

/// Shorthand helper function which carries out sorting of a slice of `T` _where_ `T: Ord`
///
/// ```
/// use sorting::selection_sort::selection_sort;
///
/// let mut arr = vec![37, 45, 29, 8];
/// selection_sort(&mut arr);
/// assert_eq!(arr, [8, 29, 37, 45]);
/// ```
pub fn selection_sort<T>(arr: &mut [T])
where
    T: Ord,
{
    selection_sort_by(arr, &|x, y| x.cmp(y))
}

/// Carries out sorting of a slice of `T` using the provided comparator function `F`
///
/// ```
/// use sorting::selection_sort::selection_sort_by;
///
/// let mut arr = vec![37, 45, 29, 8];
/// selection_sort_by(&mut arr, &|x, y| x.cmp(y));
/// assert_eq!(arr, [8, 29, 37, 45]);
/// ```
pub fn selection_sort_by<T, F>(arr: &mut [T], cmp: &F)
where
    F: Fn(&T, &T) -> Ordering,
{
    if arr.is_empty() {
        return;
    }
    let mut pointer = 0;

    while pointer < arr.len() {
        match arr
            .iter()
            .enumerate()
            .skip(pointer)
            .min_by(|(_, x), (_, y)| cmp(x, y))
        {
            Some((i, _)) if pointer != i => arr.swap(pointer, i),
            _ => {}
        }
        pointer += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semi_sorted() {
        let mut arr = vec![1, 23, 2, 32, 29, 33];
        selection_sort(&mut arr);
        assert_eq!(arr, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        selection_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        selection_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<u8> = vec![];
        selection_sort(&mut arr);
        assert_eq!(arr, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        selection_sort(&mut arr);
        assert_eq!(arr, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        selection_sort(&mut arr);
        assert_eq!(arr, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }
}
