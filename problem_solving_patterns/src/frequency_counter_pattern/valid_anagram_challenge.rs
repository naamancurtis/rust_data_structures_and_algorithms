use std::collections::HashMap;

/// ## Valid Anagram Challenge
/// Create a function that takes two strings and returns a boolean of whether one string
/// is an anagram for the other
///
/// ```
/// use problem_solving_patterns::frequency_counter_pattern::valid_anagram_challenge::valid_anagram;
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
