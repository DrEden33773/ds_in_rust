use crate::linked_list::LinkedList;
use std::fmt::{Debug, Display};

pub mod iter;

#[derive(Default)]
pub struct ListDeque<T: Default> {
  list: LinkedList<T>,
}

impl<T: Default> ListDeque<T> {
  pub fn new() -> Self {
    Self {
      list: LinkedList::new(),
    }
  }

  pub fn len(&self) -> usize {
    self.list.len()
  }

  pub fn is_empty(&self) -> bool {
    self.list.is_empty()
  }
}

impl<T: Default> ListDeque<T> {
  pub fn push_back(&mut self, value: T) {
    self.list.push_back(value);
  }

  pub fn push_front(&mut self, value: T) {
    self.list.push_front(value);
  }

  pub fn pop_back(&mut self) -> Option<T> {
    self.list.pop_back()
  }

  pub fn pop_front(&mut self) -> Option<T> {
    self.list.pop_front()
  }

  pub fn peek_back(&self) -> Option<&T> {
    self.list.last()
  }

  pub fn peek_front(&self) -> Option<&T> {
    self.list.first()
  }

  pub fn peek_back_mut(&mut self) -> Option<&mut T> {
    self.list.last_mut()
  }

  pub fn peek_front_mut(&mut self) -> Option<&mut T> {
    self.list.first_mut()
  }
}

impl<T: Default + Clone> Clone for ListDeque<T> {
  fn clone(&self) -> Self {
    Self {
      list: self.list.clone(),
    }
  }
}

impl<T: Default + Ord> Ord for ListDeque<T> {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    self.list.cmp(&other.list)
  }
}

impl<T: Default + PartialOrd> PartialOrd for ListDeque<T> {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    self.list.partial_cmp(&other.list)
  }
}

impl<T: Default + Eq> Eq for ListDeque<T> {}

impl<T: Default + PartialEq> PartialEq for ListDeque<T> {
  fn eq(&self, other: &Self) -> bool {
    self.list == other.list
  }
}

impl<T: Default + Display> Display for ListDeque<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.write_fmt(format_args!("{}", self.list))
  }
}

impl<T: Default + Debug> Debug for ListDeque<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("ListDeque")
      .field("list", &self.list)
      .finish()
  }
}

#[cfg(test)]
mod test_list_deque {
  use super::*;

  #[test]
  fn stack() {
    let mut stack = ListDeque::new();
    for e in 0..3 {
      stack.push_back(e);
    }
    for e in (0..3).rev() {
      assert_eq!(stack.pop_back(), Some(e));
    }
  }

  #[test]
  fn queue() {
    let mut queue = ListDeque::new();
    for e in 0..3 {
      queue.push_back(e);
    }
    for e in 0..3 {
      assert_eq!(queue.pop_front(), Some(e));
    }
  }

  #[test]
  fn peek_methods() {
    let mut stack: ListDeque<_> = (0..10).collect();
    assert_eq!(stack.peek_front(), Some(&0));
    *stack.peek_front_mut().unwrap() -= 1;
    assert_eq!(stack.peek_front(), Some(&-1));
    assert_eq!(stack.peek_back(), Some(&9));
    *stack.peek_back_mut().unwrap() += 1;
    assert_eq!(stack.peek_back(), Some(&10));
  }
}
