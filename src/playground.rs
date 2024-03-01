#![allow(dead_code)]

mod p {
  use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
  };

  struct User {
    id: u64,
    name: String,
  }

  impl Display for User {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      write!(f, "User {{ id: {}, name: {} }}", self.id, self.name)
    }
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

  struct Wrapper<K: Hash, V>(HashMap<K, V>);

  struct NamedWrapper<K: Hash, V> {
    pub val: HashMap<K, V>,
  }

  fn receiver<K: Hash + Debug, V: Debug>(Wrapper(map): Wrapper<K, V>) {
    println!("{:?}", map);
  }

  fn named_receiver<K: Hash + Debug, V: Debug>(NamedWrapper { val }: NamedWrapper<K, V>) {
    println!("{:?}", val);
  }

  #[test]
  fn test_receiver() {
    let map = vec![("a", 1), ("b", 2), ("c", 3)]
      .into_iter()
      .collect::<HashMap<_, _>>();

    receiver(Wrapper(map.clone()));
    named_receiver(NamedWrapper { val: map });
  }
}
