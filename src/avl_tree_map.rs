#![allow(dead_code)]

use std::{cell::RefCell, rc::Rc};

#[derive(PartialEq, PartialOrd)]
struct Entry<'a, K: PartialEq + PartialOrd, V: PartialEq> {
  key: &'a K,
  value: &'a V,
}

struct Node<K: PartialEq + PartialOrd, V: PartialEq> {
  key: K,
  value: V,
  left: Option<Rc<RefCell<Node<K, V>>>>,
  right: Option<Rc<RefCell<Node<K, V>>>>,
  height: usize,
}

impl<K: PartialEq + PartialOrd, V: PartialEq> Node<K, V> {
  pub fn new(key: K, value: V) -> Self {
    Node {
      key,
      value,
      left: None,
      right: None,
      height: 1,
    }
  }

  pub fn is_leaf(&self) -> bool {
    self.left.is_none() && self.right.is_none()
  }

  pub fn update_height(&mut self) {
    self.height = if self.is_leaf() {
      1
    } else {
      let l = self.left.as_ref().map_or(0, |node| node.borrow().height);
      let r = self.right.as_ref().map_or(0, |node| node.borrow().height);
      1 + l.max(r)
    };
  }

  pub fn factor(&self) -> isize {
    if self.is_leaf() {
      0
    } else {
      let l = self.left.as_ref().map_or(0, |node| node.borrow().height);
      let r = self.right.as_ref().map_or(0, |node| node.borrow().height);
      (l as isize) - (r as isize)
    }
  }

  pub fn entry(&self) -> Entry<K, V> {
    Entry {
      key: &self.key,
      value: &self.value,
    }
  }
}

pub struct AvlTreeMap {}
