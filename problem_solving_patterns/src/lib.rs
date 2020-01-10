/// # Frequency Counter Pattern
///
/// Uses some form of constant time lookup data structure to store frequencies of elements
/// in an iterable.
/// This allows for frequency counting in O(n) time as opposed to requiring nested loops.
pub mod frequency_counter_pattern {
    use std::collections::HashMap;

    /// ## Valid Anagram Challenge
    /// Create a function that takes two strings and returns a boolean of whether one string
    /// is an anagram for the other
    ///
    /// ```
    /// use self::problem_solving_patterns::frequency_counter_pattern::valid_anagram;
    ///
    /// fn test_valid_anagram() {
    ///     let result = valid_anagram("anagram", "gramana");
    ///     assert_eq!(result, true);
    /// }
    /// ```
    pub fn valid_anagram(string_1: &str, string_2: &str) -> bool {
        if string_1.len() != string_2.len() {
            return false;
        }

        let mut char_map = HashMap::new();

        for char in string_1.chars() {
            match char_map.get_mut(&char) {
                Some(count) => *count += 1,
                _ => {
                    char_map.insert(char, 1);
                }
            }
        }

        for char in string_2.chars() {
            match char_map.get_mut(&char) {
                Some(count) if *count > 0 => *count -= 1,
                _ => return false,
            }
        }

        true
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_valid_anagram_2() {
            let result = valid_anagram("abc", "cba");
            assert_eq!(result, true);
        }

        #[test]
        fn test_strings_of_different_length() {
            let result = valid_anagram("anagram", "gramanas");
            assert_eq!(result, false);
        }

        #[test]
        fn test_invalid_anagram() {
            let result = valid_anagram("anagram", "gramann");
            assert_eq!(result, false);
        }

        #[test]
        fn test_invalid_anagram_2() {
            let result = valid_anagram("anagram", "grammmm");
            assert_eq!(result, false);
        }
    }
}

/// # Multiple Pointers Pattern
///
/// Although this specific implementation doesn't use multiple pointers
/// it effectively uses a pointer to track a comparision within the collection
/// without having to loop through the collection multiple times
pub mod multiple_pointers_pattern {

    /// ## Count Unique Challenge
    /// Create a function that accepts a sorted collection and returns a count of the number of unique
    /// values in that array.
    /// ```
    /// use self::problem_solving_patterns::multiple_pointers_pattern::count_unique;
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
        if collection.len() == 0 {
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
}
