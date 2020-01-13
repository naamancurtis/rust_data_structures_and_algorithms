/// ## Bubble Sort
/// Given an unsorted collection, return a sorted collection through the use of the
/// bubble sort algorithm
///
/// ```
/// use sorting::bubble_sort::bubble_sort;
///
/// fn test_simple_sort() {
///     let result = bubble_sort(vec![37, 45, 29, 8]);
///     assert_eq!(result, [8, 29, 37, 45]);
/// }
/// ```
pub fn bubble_sort<T>(mut collection: Vec<T>) -> Vec<T>
where
    T: PartialOrd + PartialEq,
{
    for i in (0..collection.len()).rev() {
        for j in 0..i {
            if collection[j] > collection[j + 1] {
                collection.swap(j, j + 1);
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
        let result = bubble_sort(vec![1, 23, 2, 32, 29, 33]);
        assert_eq!(result, [1, 2, 23, 29, 32, 33]);
    }

    #[test]
    fn test_backwards() {
        let result = bubble_sort(vec![50, 25, 10, 5, 1]);
        assert_eq!(result, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_sorted() {
        let result = bubble_sort(vec![1, 5, 10, 25, 50]);
        assert_eq!(result, [1, 5, 10, 25, 50]);
    }

    #[test]
    fn test_empty() {
        let result: Vec<u32> = bubble_sort(vec![]);
        assert_eq!(result, []);
    }

    #[test]
    fn test_len_two() {
        let result = bubble_sort(vec![5, 1]);
        assert_eq!(result, [1, 5]);
    }

    #[test]
    fn test_partially_sorted() {
        let result = bubble_sort(vec![50, 75, 1, 1, 3, 4, 5, 6, 50]);
        assert_eq!(result, [1, 1, 3, 4, 5, 6, 50, 50, 75]);
    }
}
