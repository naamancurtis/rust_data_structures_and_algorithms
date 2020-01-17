//! # Bubble Sort
//!
//! Bubble Sort is a simple sorting algorithm that works by repeatedly swapping adjacent
//! elements if they are in the wrong order
//!
//! - Time Complexity: **O**(n^2)
//! - Space Complexity: **O**(1)

use std::cmp::Ordering;

/// Shorthand helper function which carries out sorting of a slice of `T` _where_ `T: Ord`
///
/// ```rust
/// use sorting::bubble_sort::bubble_sort;
///
/// let mut arr = vec![37, 45, 29, 8];
/// bubble_sort(&mut arr);
/// assert_eq!(arr, [8, 29, 37, 45]);
/// ```
pub fn bubble_sort<T>(arr: &mut [T])
where
    T: Ord,
{
    bubble_sort_by(arr, &|x, y| x.cmp(y))
}

/// Carries out sorting of a slice of `T` using the provided comparator function `F`
///
/// ```rust
/// use sorting::bubble_sort::bubble_sort_by;
///
/// let mut arr = vec![37, 45, 29, 8];
/// bubble_sort_by(&mut arr, &|x, y| x.cmp(y));
/// assert_eq!(arr, [8, 29, 37, 45]);
/// ```
pub fn bubble_sort_by<T, F>(arr: &mut [T], cmp: &F)
where
    F: Fn(&T, &T) -> Ordering,
{
    let mut no_swaps;

    for i in (0..arr.len()).rev() {
        no_swaps = true;
        for j in 0..i {
            if cmp(&arr[j], &arr[j + 1]) == Ordering::Greater {
                arr.swap(j, j + 1);
                no_swaps = false;
            }
        }
        if no_swaps {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semi_sorted() {
        let mut arr = vec![1, 23, 2, 32, 29, 33];
        bubble_sort(&mut arr);
        assert_eq!(arr, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        bubble_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        bubble_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<u8> = vec![];
        bubble_sort(&mut arr);
        assert_eq!(arr, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        bubble_sort(&mut arr);
        assert_eq!(arr, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        bubble_sort(&mut arr);
        assert_eq!(arr, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }
}
