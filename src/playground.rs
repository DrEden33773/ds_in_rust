#![allow(dead_code)]

mod p {
  use std::{collections::HashMap, hash::Hash};

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

  fn demo() {
    let map = vec![("a", 1), ("b", 2), ("c", 3)]
      .into_iter()
      .collect::<HashMap<_, _>>();

    let mut room = Room::new(map);

    room.query(&"a");
    room.query(&"b");
    room.query(&"c");
  }
}
