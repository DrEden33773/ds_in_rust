#![allow(dead_code)]

mod p {
  use std::{collections::HashMap, hash::Hash};

  struct User {
    id: u128,
    name: String,
  }

  struct Room<'a, K: Hash + Clone + Eq, V: Clone> {
    key_refs: Vec<&'a K>,
    map: HashMap<K, V>,
  }

  impl<'a, K: Hash + Clone + Eq, V: Clone> Room<'a, K, V> {
    fn new(map: HashMap<K, V>) -> Self {
      Self {
        key_refs: vec![],
        map,
      }
    }

    fn query(&mut self, key: &'a K) {
      if self.map.contains_key(key) {
        self.key_refs.push(key);
      }
    }
  }

  #[test]
  fn demo() {
    let map = vec![("a", 1), ("b", 2), ("c", 3)]
      .into_iter()
      .collect::<HashMap<_, _>>();

    let mut room = Room::new(map);

    room.query(&"a");
    room.query(&"b");
    room.query(&"c");

    let mut map = HashMap::<i32, i32>::new();

    map.entry(1);
  }

  #[test]
  fn hash_set_enumerate() {
    let set = vec![1, 2, 3]
      .into_iter()
      .collect::<std::collections::HashSet<_>>();

    for (i, e) in set.iter().enumerate() {
      println!("{}: {}", i, e);
    }
  }
}
