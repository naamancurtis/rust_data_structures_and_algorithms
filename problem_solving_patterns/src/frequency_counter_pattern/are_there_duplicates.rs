use std::collections::HashSet;
use std::hash::Hash;

/// ## Are There Duplicates Challenge
/// Given a collection of arguments, identify if there are any duplicates in the collection
///
/// ```
/// use problem_solving_patterns::frequency_counter_pattern::are_there_duplicates::are_there_duplicates;
///
/// fn test_duplicates() {
///     let result = are_there_duplicates(&vec![1,2,3,1]);
///     assert_eq!(result, true);
/// }
/// ```
pub fn are_there_duplicates<T>(collection: &[T]) -> bool
where
    T: Hash + Clone + Eq,
{
    let hash_set: HashSet<_> = collection.iter().collect();
    collection.len() != hash_set.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_no_duplicates() {
        let result = are_there_duplicates(&vec![1, 2, 3, 4]);
        assert_eq!(result, false);
    }

    #[test]
    fn test_multiple_duplicates() {
        let result = are_there_duplicates(&vec![1, 1, 2, 3, 3, 4]);
        assert_eq!(result, true);
    }

    #[test]
    fn test_empty_array() {
        let input: Vec<i32> = Vec::new();
        let result = are_there_duplicates(&input);
        assert_eq!(result, false);
    }
}
