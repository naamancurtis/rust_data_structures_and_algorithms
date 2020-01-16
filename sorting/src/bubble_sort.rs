/// ## Bubble Sort
/// Given an unsorted collection, return a sorted collection through the use of the
/// bubble sort algorithm.
///
/// As the collection is parsed, the largest values should bubble up to the RHS of
/// the collection over time.
///
/// Time Complexity: O(n^2)
/// Space Complexity: O(1)
///
/// ```
/// use sorting::bubble_sort::bubble_sort;
///
/// fn test_simple_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     let result = bubble_sort(&mut arr);
///     assert_eq!(result, [8, 29, 37, 45]);
/// }
/// ```
pub fn bubble_sort<T>(collection: &mut [T]) -> &[T]
where
    T: PartialOrd + PartialEq + Copy,
{
    let mut no_swaps;

    for i in (0..collection.len()).rev() {
        no_swaps = true;
        for j in 0..i {
            if collection[j] > collection[j + 1] {
                collection.swap(j, j + 1);
                no_swaps = false;
            }
        }
        if no_swaps {
            break;
        }
    }

    collection
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semi_sorted() {
        let mut arr = vec![1, 23, 2, 32, 29, 33];
        let result = bubble_sort(&mut arr);
        assert_eq!(result, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        let result = bubble_sort(&mut arr);
        assert_eq!(result, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        let result = bubble_sort(&mut arr);
        assert_eq!(result, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr = vec![];
        let result: &[u32] = bubble_sort(&mut arr);
        assert_eq!(result, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        let result = bubble_sort(&mut arr);
        assert_eq!(result, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        let result = bubble_sort(&mut arr);
        assert_eq!(result, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }
}