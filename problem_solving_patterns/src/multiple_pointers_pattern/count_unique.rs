/// ## Count Unique Challenge
/// Create a function that accepts a sorted collection and returns a count of the number of unique
/// values in that array.
///
/// ```
/// use problem_solving_patterns::multiple_pointers_pattern::count_unique::count_unique;
///
/// fn test_count_integers() {
///     let result = count_unique(&vec![1, 1, 1, 1, 2, 3, 4]);
///     assert_eq!(result, 4);
/// }
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
mod tests {
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
