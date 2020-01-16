//! # Quick Sort
//!
//! Quick Sort is a Divide and Conquer algorithm. It picks an element as a pivot and partitions a given array around the picked pivot.
//! It recursively applies the same partitioning logic to the partitioned arrays until the entire collection is sorted
//!
//! - Time Complexity: Average: **O**(n _log_(n)) | Worst case **O**(n^2)
//! - Space Complexity: **O**(_log_(n))
//!
//! Implementation is based off [Ironsort](https://github.com/kyrias/ironsort/) however it includes some optimisations:
//! - __Median of Three__ pivot strategy too counter sorted/reverse-sorted input
//! - __Min Array Length Cut-off__ to switch to a non-recursive sort _(Insertion Sort)_ when the length of the array drops below 10

use crate::insertion_sort::insertion_sort_by;
use std::cmp;
use std::cmp::Ordering;

const INSERTION_SORT_CUT_OFF: usize = 10;

/// Shorthand helper function which carries out in-place sorting of a slice of `T` _where_ `T: Ord`
///
/// When any call to the function passes an array where `array.len() < 10` it instead
/// defaults to using the insertion_sort defined in this library.
///
/// # Examples
/// ```rust
/// use sorting::quick_sort::quick_sort;
///
/// fn simple_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     quick_sort(&mut arr);
///     assert_eq!(arr, [8, 29, 37, 45]);
/// }
/// ```
pub fn quick_sort<T>(arr: &mut [T])
where
    T: Ord,
{
    partition(arr, &|x, y| x.cmp(y))
}

/// Carries out in-place sorting of a slice of `T` using the provided comparator function `F`
///
/// When any call to the function passes an array where `array.len() < 10` it instead
/// defaults to using the insertion_sort defined in this library.
///
/// # Examples
/// ```rust
/// use sorting::quick_sort::quick_sort_by;
///
/// fn simple_sort() {
///     let mut arr = vec![37, 45, 29, 8 ,10];
///     quick_sort_by(&mut arr, &|x, y| x.cmp(y));
///     assert_eq!(arr, [8, 10, 29, 37, 45]);
/// }
/// ```
pub fn quick_sort_by<T, F>(arr: &mut [T], cmp: &F)
where
    F: Fn(&T, &T) -> Ordering,
{
    partition(arr, cmp);
}

/// Implementation of _Hoare's Partition Scheme_ along with a _Median of Three Values_ pivot strategy.
/// If the array length reduces to below 10 it instead uses an insertion sort to sort the remaining array.
fn partition<T, F>(arr: &mut [T], cmp: &F)
where
    F: Fn(&T, &T) -> Ordering,
{
    let len = arr.len();
    if len <= 1 {
        return;
    }

    if len < INSERTION_SORT_CUT_OFF {
        insertion_sort_by(arr, cmp);
        return;
    }

    let start = 0;
    let pivot = 0;

    {
        // Median of Three
        let end = len - 1;
        let mid = end / 2;

        if cmp(&arr[mid], &arr[start]) == Ordering::Less {
            arr.swap(mid, start);
        }
        if cmp(&arr[end], &arr[start]) == Ordering::Less {
            arr.swap(end, start);
        }
        if cmp(&arr[end], &arr[mid]) == Ordering::Less {
            arr.swap(end, mid);
        }
    }

    let mut left_ptr = 1;
    let mut right_ptr = arr.len() - 1;

    // Iterate over the collection from both sides
    loop {
        // For as long as the elements are less than the pivot, move the left pointer in
        while left_ptr < len && cmp(&arr[left_ptr], &arr[pivot]) != Ordering::Greater {
            left_ptr += 1;
        }

        // For as long as the element are greater than the pivot, move the right pointer in
        while right_ptr > start && cmp(&arr[right_ptr], &arr[pivot]) != Ordering::Less {
            right_ptr -= 1;
        }

        // Check to ensure that the pointers don't pass each other
        if left_ptr >= right_ptr {
            break;
        }

        // To hit this point in code, the left pointer must have found something greater than
        // the pivot and the right pointer must have found something less than the pivot.
        // Therefore we can swap these two values and then move the pointers 1 element inwards
        // ready for the next iteration of the loop
        arr.swap(left_ptr, right_ptr);
        left_ptr += 1;
        right_ptr -= 1;
    }

    // Once we've broken out of the loop, the right_ptr points to a value lower than the pivot
    // Our pivot value was held in the [0] index of the collection, therefore we can swap the
    // two to complete this iteration of the sort
    arr.swap(pivot, right_ptr);

    // Recursively call this fn with the values from the start of the array up to
    // (but not including) the pivot
    partition(&mut arr[0..cmp::min(left_ptr - 1, right_ptr)], cmp);
    // Recursively call this fn with the values from the index 1 above the pivot till the
    // end of the array
    partition(&mut arr[cmp::max(left_ptr, right_ptr + 1)..], cmp);
}

#[cfg(test)]
extern crate rand;

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{self, Rng};

    #[test]
    fn test_semi_sorted() {
        let mut arr = vec![1, 23, 2, 32, 29, 33, 24, 156, 23, 2381, 23, 3, 2, 3];
        quick_sort(&mut arr);
        assert_eq!(arr, [1, 2, 2, 3, 3, 23, 23, 23, 24, 29, 32, 33, 156, 2381]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        quick_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        quick_sort(&mut arr);
        assert_eq!(arr, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<u32> = vec![];
        quick_sort(&mut arr);
        assert_eq!(arr, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        quick_sort(&mut arr);
        assert_eq!(arr, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        quick_sort(&mut arr);
        assert_eq!(arr, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }

    #[test]
    fn test_long_zeroes() {
        let mut vec = vec![0u8; 10000];
        quick_sort(&mut vec);
        for i in 0..vec.len() - 1 {
            assert!(vec[i] <= vec[i + 1])
        }
    }

    #[test]
    fn test_random() {
        let mut rng = rand::thread_rng();
        let mut vec = (0..10000)
            .map(|x| x * rng.gen_range(-10, 10))
            .collect::<Vec<i32>>();
        quick_sort(&mut vec);
        for i in 0..vec.len() - 1 {
            assert!(vec[i] <= vec[i + 1])
        }
    }
}
