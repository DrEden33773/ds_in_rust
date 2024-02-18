use std::{
  collections::{HashMap, HashSet},
  hash::Hash,
};

pub struct DisjointSet<T: Hash + Eq> {
  ei_map: HashMap<T, usize>,
  ie_map: HashMap<usize, T>,
  parent: Vec<usize>,
  size: Vec<usize>,
  root_num: usize,
}

impl<T: Hash + Eq> DisjointSet<T> {
  pub fn get_root(&self, key: &T) -> Option<&T> {
    let &i = self.ei_map.get(key)?;
    let mut i = i;
    while i != self.parent[i] {
      i = self.parent[i];
    }
    self.ie_map.get(&i)
  }

  pub fn find(&self, lhs: &T, rhs: &T) -> bool {
    self.get_root(lhs) == self.get_root(rhs)
  }

  pub fn find_and_compress(&mut self, lhs: &T, rhs: &T) -> bool {
    let lhs = self.ei_map.get(lhs);
    let rhs = self.ei_map.get(rhs);
    if lhs.is_none() || rhs.is_none() {
      return false;
    }

    let lhs_index = *lhs.unwrap();
    let rhs_index = *rhs.unwrap();
    self.get_root_index(lhs_index) == self.get_root_index(rhs_index)
  }

  #[allow(clippy::result_unit_err)]
  pub fn unite(&mut self, lhs: &T, rhs: &T) -> Result<(), ()> {
    let lhs = *self.ei_map.get(lhs).ok_or(())?;
    let rhs = *self.ei_map.get(rhs).ok_or(())?;

    let l = self.get_root_index(lhs);
    let r = self.get_root_index(rhs);
    if l == r {
      return Ok(());
    }

    self.parent[l] = r;
    self.root_num -= 1;
    Ok(())
  }

  #[allow(clippy::result_unit_err)]
  pub fn unite_by_size(&mut self, lhs: &T, rhs: &T) -> Result<(), ()> {
    let lhs = *self.ei_map.get(lhs).ok_or(())?;
    let rhs = *self.ei_map.get(rhs).ok_or(())?;

    let l = self.get_root_index(lhs);
    let r = self.get_root_index(rhs);
    if l == r {
      return Ok(());
    }

    if self.size[l] < self.size[r] {
      self.parent[l] = r;
      self.size[r] += self.size[l];
    } else {
      self.parent[r] = l;
      self.size[l] += self.size[r];
    }

    self.root_num -= 1;
    Ok(())
  }
}

impl<T: Hash + Eq> DisjointSet<T> {
  pub fn root_num(&self) -> usize {
    self.root_num
  }

  fn get_root_index(&mut self, index: usize) -> usize {
    if self.parent[index] == index {
      index
    } else {
      self.parent[index] = self.get_root_index(self.parent[index]);
      self.parent[index]
    }
  }
}

impl<T: Hash + Eq + Clone> DisjointSet<T> {
  pub fn new(items: impl Iterator<Item = T>) -> Self {
    let unique_items = items.collect::<HashSet<_>>();
    let len = unique_items.len();

    let ei_map = unique_items
      .into_iter()
      .enumerate()
      .map(|(i, e)| (e, i))
      .collect::<HashMap<_, _>>();
    let ie_map = ei_map
      .iter()
      .map(|(e, i)| (*i, e.clone()))
      .collect::<HashMap<_, _>>();
    let parent = (0..len).collect::<Vec<_>>();
    let size = vec![1; len];

    Self {
      ei_map,
      ie_map,
      parent,
      size,
      root_num: len,
    }
  }
}

#[cfg(test)]
mod test_disjoint_set {
  use super::*;

  fn covered_pair<T: Clone>(input: impl Iterator<Item = T>) -> Vec<(T, T)> {
    let mut result = vec![];
    let input = input.collect::<Vec<_>>();
    for i in 0..input.len() {
      for j in i + 1..input.len() {
        result.push((input[i].clone(), input[j].clone()));
      }
    }
    result
  }

  fn covered_pair_between<T: Clone>(
    lhs: impl Iterator<Item = T>,
    rhs: impl Iterator<Item = T>,
  ) -> Vec<(T, T)> {
    let mut result = vec![];
    let lhs = lhs.collect::<Vec<_>>();
    let rhs = rhs.collect::<Vec<_>>();
    for l in lhs.iter() {
      for r in rhs.iter() {
        result.push((l.clone(), r.clone()));
      }
    }
    result
  }

  /// This case comes from: [oi-wiki-dsu-unite-example](https://oi-wiki.org/ds/images/disjoint-set-merge.svg)
  #[test]
  fn test_disjoint_set() {
    let mut ds = DisjointSet::new('a'..='h');

    assert_eq!(ds.unite_by_size(&'b', &'a'), Ok(()));
    assert_eq!(ds.unite_by_size(&'c', &'a'), Ok(()));
    assert_eq!(ds.unite_by_size(&'d', &'c'), Ok(()));
    assert_eq!(ds.unite_by_size(&'e', &'c'), Ok(()));

    for (lhs, rhs) in covered_pair('a'..='e') {
      assert!(ds.find(&lhs, &rhs));
    }
    for (lhs, rhs) in covered_pair('f'..='h') {
      assert!(!ds.find(&lhs, &rhs));
    }
    for (lhs, rhs) in covered_pair_between('a'..='e', 'f'..='h') {
      assert!(!ds.find(&lhs, &rhs));
    }

    assert_eq!(ds.unite_by_size(&'g', &'f'), Ok(()));
    assert_eq!(ds.unite_by_size(&'h', &'g'), Ok(()));

    for (lhs, rhs) in covered_pair('a'..='e') {
      assert!(ds.find(&lhs, &rhs));
    }
    for (lhs, rhs) in covered_pair('f'..='h') {
      assert!(ds.find(&lhs, &rhs));
    }
    for (lhs, rhs) in covered_pair_between('a'..='e', 'f'..='h') {
      assert!(!ds.find(&lhs, &rhs));
    }

    assert_eq!(ds.unite_by_size(&'h', &'a'), Ok(()));

    for (lhs, rhs) in covered_pair('a'..='e') {
      assert!(ds.find(&lhs, &rhs));
    }
    for (lhs, rhs) in covered_pair('f'..='h') {
      assert!(ds.find(&lhs, &rhs));
    }
    for (lhs, rhs) in covered_pair_between('a'..='e', 'f'..='h') {
      assert!(ds.find(&lhs, &rhs));
    }
  }
}
