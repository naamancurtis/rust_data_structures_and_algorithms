/// ## Insertion Sort
/// Given an unsorted collection, return a sorted collection through the use of the
/// insertion sort algorithm.
///
/// As the collection is parsed, the sort gradually builds up a sorted sub-array which
/// values are inserted into in order.
///
/// Insertion sort can be useful in certain situations
///  - If your collection is very nearly sorted
///  - If you don't have the complete collection when the function is invoked (ie. streaming
///    data) and need to add to the collection as new data comes in.
///
/// Time Complexity: O(n^2)
/// Space Complexity: O(1)
///
/// ```
/// use sorting::insertion_sort::insertion_sort;
///
/// fn test_simple_sort() {
///     let mut arr = vec![37, 45, 29, 8];
///     let result = insertion_sort(&mut arr);
///     assert_eq!(result, [8, 29, 37, 45]);
/// }
/// ```
pub fn insertion_sort<T>(collection: &mut [T]) -> &[T] where T: PartialOrd {
    if collection.is_empty() {
        return collection;
    }

    for i in 1..collection.len() {
        for j in (1..=i).rev() {
            if collection[j] < collection[j - 1] {
                collection.swap(j, j - 1);
            } else {
                break;
            }
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
        let result = insertion_sort(&mut arr);
        assert_eq!(result, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let mut arr = vec![50, 25, 10, 5, 1];
        let result = insertion_sort(&mut arr);
        assert_eq!(result, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let mut arr = vec![1, 5, 10, 25, 50];
        let result = insertion_sort(&mut arr);
        assert_eq!(result, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let mut arr = vec![];
        let result: &[u32] = insertion_sort(&mut arr);
        assert_eq!(result, []);
    }

    #[test]
    fn test_len_two() {
        let mut arr = vec![5, 1];
        let result = insertion_sort(&mut arr);
        assert_eq!(result, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let mut arr = vec![50, 75, 1, 1, 3, 4, 5, 6, 50];
        let result = insertion_sort(&mut arr);
        assert_eq!(result, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }
}