#![allow(dead_code)]

use std::{cell::RefCell, rc::Rc};

struct Node<T> {
  val: T,
  left: Option<Rc<RefCell<Node<T>>>>,
  right: Option<Rc<RefCell<Node<T>>>>,
}

impl<T> Node<T> {
  pub fn new(val: T) -> Self {
    Self {
      val,
      left: None,
      right: None,
    }
  }

  pub fn is_leaf(&self) -> bool {
    self.left.is_none() && self.right.is_none()
  }
}

#[derive(Default)]
pub struct BinaryTree<T> {
  root: Option<Rc<RefCell<Node<T>>>>,
  len: usize,
}
