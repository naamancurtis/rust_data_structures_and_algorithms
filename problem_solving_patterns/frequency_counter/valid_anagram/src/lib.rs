/*
    Given two strings, write a function to determine if the second string is an anagram of the first
*/

use std::collections::hash_map::HashMap;

pub fn valid_anagram(string_1: &str, string_2: &str) -> bool {
    if string_1.len() != string_2.len() {
        return false;
    };

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
    fn test_empty_string() {
        let result = valid_anagram("", "");
        assert_eq!(result, true);
    }

    #[test]
    fn test_same_letters_incorrect_frequency() {
        let result = valid_anagram("aaz", "zza");
        assert_eq!(result, false);
    }

    #[test]
    fn test_valid_anagram() {
        let result = valid_anagram("anagram", "nagaram");
        assert_eq!(result, true);
    }

    #[test]
    fn test_invalid_anagram() {
        let result = valid_anagram("rat", "car");
        assert_eq!(result, false);
    }

    #[test]
    fn test_same_word_missing_letters() {
        let result = valid_anagram("awesome", "awesom");
        assert_eq!(result, false);
    }

    #[test]
    fn test_gibberish() {
        let result = valid_anagram("amanaplanacanalpanama", "acanalmanplanpanama");
        assert_eq!(result, false);
    }

    #[test]
    fn test_valid_anagram_2() {
        let result = valid_anagram("qwerty", "ytrewq");
        assert_eq!(result, true);
    }

    #[test]
    fn test_reversed_words() {
        let result = valid_anagram("texttwisttime", "timetwisttext");
        assert_eq!(result, true);
    }
}
