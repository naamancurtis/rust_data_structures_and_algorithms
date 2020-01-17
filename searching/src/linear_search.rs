/// Given a sorted array and a value, this function parses the collection and returns the
/// index where that value resides via a linear search
///
/// If the value is not present within the array `None` is returned
///
/// - Time Complexity: **O**(n)
/// - Space Complexity: **O**(1)
///
/// ```rust
/// use searching::linear_search::linear_search;
///
/// let result = linear_search(&vec![10, 15, 20, 25, 30], 15);
/// assert_eq!(result, Some(1));
/// ```
pub fn linear_search<T>(collection: &[T], target_value: T) -> Option<usize>
where
    T: PartialEq,
{
    collection.iter().position(|el| el == &target_value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_middle() {
        let result = linear_search(&vec![9, 8, 7, 6, 5, 4, 3, 2, 1, 0], 4);
        assert_eq!(result, Some(5));
    }

    #[test]
    fn test_single_element() {
        let result = linear_search(&vec![100], 100);
        assert_eq!(result, Some(0));
    }

    #[test]
    fn test_not_in_array() {
        let result = linear_search(&vec![1, 2, 3, 4, 5], 6);
        assert_eq!(result, None);
    }

    #[test]
    fn test_not_in_array_2() {
        let result = linear_search(&vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], 11);
        assert_eq!(result, None);
    }

    #[test]
    fn test_empty_array() {
        let result = linear_search(&vec![], 10);
        assert_eq!(result, None);
    }

    #[test]
    fn test_str_array() {
        let result = linear_search(&vec!["test", "this", "array"], "this");
        assert_eq!(result, Some(1));
    }

    #[test]
    fn test_string_array() {
        let result = linear_search(
            &vec![
                String::from("test"),
                String::from("this"),
                String::from("array"),
            ],
            String::from("this"),
        );
        assert_eq!(result, Some(1));
    }

    #[test]
    fn test_not_in_str_array() {
        let result = linear_search(&vec!["test", "this", "array"], "value");
        assert_eq!(result, None);
    }
}
