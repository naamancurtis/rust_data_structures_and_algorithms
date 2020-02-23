#![allow(dead_code)]

//! # Hash Table
//!
//! This is a very simple implementation of a Hash Table just to walk through the steps involved
//! in creating one. It's not optimised, nor does it expose any form of comprehensive public API
//! and shouldn't be used in any real code.
//!
//! The hash fn (CustomHash Trait) for strings is pretty much arbitrary, although is good enough
//! to mimic a proper hash fn

/// Num of buckets in the length should be Prime
///
/// Collision Resolution
/// - Separate Chaining
struct HashTable<K, V>
where
    K: CustomHash + PartialEq,
{
    base: Vec<Vec<(K, V)>>,
    num_buckets: usize,
}

impl<K, V> Default for HashTable<K, V>
where
    K: CustomHash + PartialEq,
{
    /// Default capacity is a Prime number
    fn default() -> Self {
        Self::new(53)
    }
}

impl<K, V> HashTable<K, V>
where
    K: CustomHash + PartialEq,
{
    pub fn new(num_buckets: usize) -> Self {
        let mut v = Vec::with_capacity(num_buckets);
        // Although this isn't efficient, we'd have to use unsafe to create a union type between a vec and a ()
        for _ in 0..num_buckets {
            v.push(Vec::new())
        }
        Self {
            base: v,
            num_buckets,
        }
    }

    pub fn set(&mut self, key: K, value: V) {
        let hash = self.hash(&key);
        self.base[hash].push((key, value));
    }

    pub fn get(&self, key: K) -> Option<&V> {
        let hash = self.hash(&key);
        self.base[hash]
            .iter()
            .find(|(k, _)| *k == key)
            .map(|(_, v)| v)
    }

    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        let hash = self.hash(&key);
        self.base[hash]
            .iter_mut()
            .find(|(k, _)| *k == key)
            .map(|(_, v)| v)
    }

    pub fn remove(&mut self, key: K) -> Option<(K, V)> {
        let hash = self.hash(&key);
        match self.base[hash]
            .iter()
            .enumerate()
            .find(|(_, (k, _))| *k == key)
            .map(|(i, _)| i)
        {
            Some(i) => Some(self.base[hash].remove(i)),
            None => None,
        }
    }

    pub fn has(&self, key: K) -> bool {
        let hash = self.hash(&key);
        self.base[hash].iter().any(|(k, _)| *k == key)
    }

    pub fn keys(&self) -> Vec<&K> {
        self.base
            .iter()
            .filter(|bucket| !bucket.is_empty())
            .map(|bucket| bucket.iter().map(|(k, _)| k))
            .flatten()
            .collect()
    }

    pub fn values(&self) -> Vec<&V> {
        self.base
            .iter()
            .filter(|bucket| !bucket.is_empty())
            .map(|bucket| bucket.iter().map(|(_, v)| v))
            .flatten()
            .collect()
    }

    pub fn keys_and_values(&self) -> Vec<&(K, V)> {
        self.base
            .iter()
            .filter(|bucket| !bucket.is_empty())
            .flatten()
            .collect()
    }

    fn hash(&self, key: &K) -> usize {
        key.custom_hash(self.num_buckets)
    }
}

trait CustomHash {
    fn custom_hash(&self, num_buckets: usize) -> usize;
}

impl CustomHash for String {
    fn custom_hash(&self, num_buckets: usize) -> usize {
        let mut total = 0;
        let weird_prime = 31;

        self.chars()
            .take(self.len().min(50)) // An upper bound for a "constant time" hash
            .for_each(|c| {
                let mut c_code = c as u8;
                if c_code > 96 {
                    c_code -= 96;
                }
                total = (total * weird_prime + c_code as usize) % num_buckets;
            });
        total
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_returns_same_result() {
        let str = String::from("test");
        let str_2 = String::from("abcdefg");
        let result1 = str.custom_hash(13);
        let result2 = str.custom_hash(13);
        let result3 = str.custom_hash(13);
        let result4 = str_2.custom_hash(13);

        assert_eq!(result1, result2);
        assert_eq!(result1, result3);
        assert_eq!(result2, result3);
        assert!(!(result3 == result4));
    }

    #[test]
    fn set_get() {
        let mut table = HashTable::default();
        table.set("test".to_string(), 50);
        table.set("test_two".to_string(), 100);

        assert!(table.has("test".to_string()));
        assert!(table.has("test_two".to_string()));

        assert_eq!(table.get("test".to_string()), Some(&50));
        assert_eq!(table.get("test_two".to_string()), Some(&100));
    }

    #[test]
    fn remove() {
        let mut table = HashTable::default();
        table.set("test".to_string(), 50);
        table.set("test_two".to_string(), 100);

        assert!(table.has("test".to_string()));
        assert!(table.has("test_two".to_string()));

        assert_eq!(
            table.remove("test".to_string()),
            Some(("test".to_string(), 50))
        );
        assert!(!table.has("test".to_string()));
        assert!(table.has("test_two".to_string()));
    }

    #[test]
    fn looping() {
        let mut table = HashTable::default();
        table.set("test".to_string(), 50);
        table.set("test_two".to_string(), 100);
        table.set("test_three".to_string(), 150);

        let keys = table.keys();
        let values = table.values();
        let keys_values = table.keys_and_values();

        assert_eq!(keys.len(), 3);
        assert_eq!(values.len(), 3);
        assert_eq!(keys_values.len(), 3);

        let keys_expected = vec![
            String::from("test"),
            String::from("test_two"),
            String::from("test_three"),
        ];

        let values_expected = vec![50, 100, 150];

        let kv_expected = vec![
            ("test".to_string(), 50),
            ("test_two".to_string(), 100),
            ("test_three".to_string(), 150),
        ];

        keys.into_iter()
            .for_each(|key| assert!(keys_expected.contains(key)));

        values
            .into_iter()
            .for_each(|key| assert!(values_expected.contains(key)));

        keys_values
            .into_iter()
            .for_each(|key| assert!(kv_expected.contains(key)));
    }
}
