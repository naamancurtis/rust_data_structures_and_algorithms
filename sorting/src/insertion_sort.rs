//! # Insertion Sort
//!
//! Is a simple sorting algorithm that builds the sorted array one element at a time by maintaining a sorted
//! sub-array into which elements are inserted.
//!
//! - Time Complexity: **O**(n^2)
//! - Space Complexity: **O**(_log_(n))

use std::cmp::Ordering;

/// Shorthand helper function which carries out sorting of a slice of `T` _where_ `T: Ord`
///
/// # Examples
/// ```rust
/// use sorting::insertion_sort::insertion_sort;
///
/// fn test_simple_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     insertion_sort(&mut arr);
///     assert_eq!(arr, [8, 29, 37, 45]);
/// }
/// ```
pub fn insertion_sort<T>(arr: &mut [T])
where
    T: Ord,
{
    insertion_sort_by(arr, &|x, y| x.cmp(y))
}

/// Carries out sorting of a slice of `T` using the provided comparator function `F`
///
/// # Examples
/// ```rust
/// use sorting::insertion_sort::insertion_sort_by;
///
/// fn simple_sort() {
///     let mut arr = vec![37, 45, 29, 8 ,10];
///     insertion_sort_by(&mut arr, &|x, y| x.cmp(y));
///     assert_eq!(arr, [8, 10, 29, 37, 45]);
/// }
/// ```
pub fn insertion_sort_by<T, F>(arr: &mut [T], cmp: &F)
where
    F: Fn(&T, &T) -> Ordering,
{
    if arr.is_empty() {
        return;
    }

    for i in 1..arr.len() {
        for j in (1..=i).rev() {
            if cmp(&arr[j], &arr[j - 1]) == Ordering::Less {
                arr.swap(j, j - 1);
            } else {
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semi_sorted() {
        let mut arr = vec![1, 23, 2, 32, 29, 33];
        insertion_sort(&mut arr);
        assert_eq!(arr, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        insertion_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        insertion_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<u32> = vec![];
        insertion_sort(&mut arr);
        assert_eq!(arr, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        insertion_sort(&mut arr);
        assert_eq!(arr, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        insertion_sort(&mut arr);
        assert_eq!(arr, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }
}
