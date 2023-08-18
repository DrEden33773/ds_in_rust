use std::{
  fmt::{Debug, Display},
  ptr::NonNull,
};

const INIT_CAPACITY: usize = 8;
const EXPAND_FACTOR: usize = 2;

pub mod iter;

#[derive(Debug)]
pub struct Vector<T> {
  data: NonNull<T>,
  len: usize,
  capacity: usize,
}

impl<T: Clone> Clone for Vector<T> {
  fn clone(&self) -> Self {
    self.iter().cloned().collect()
  }
}

impl<T: PartialOrd> PartialOrd for Vector<T> {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    if self.len != other.len {
      return self.len.partial_cmp(&other.len);
    }
    for (l, r) in self.iter().zip(other.iter()) {
      match l.partial_cmp(r) {
        Some(std::cmp::Ordering::Equal) => continue,
        x => return x,
      }
    }
    Some(std::cmp::Ordering::Equal)
  }
}

impl<T: Ord> Ord for Vector<T> {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    if self.len != other.len {
      return self.len.cmp(&other.len);
    }
    for (l, r) in self.iter().zip(other.iter()) {
      match l.cmp(r) {
        std::cmp::Ordering::Equal => continue,
        x => return x,
      }
    }
    std::cmp::Ordering::Equal
  }
}

impl<T: PartialEq> PartialEq for Vector<T> {
  fn eq(&self, other: &Self) -> bool {
    if self.len != other.len {
      return false;
    }
    for (l, r) in self.iter().zip(other.iter()) {
      if l != r {
        return false;
      }
    }
    true
  }
}

impl<T: Eq> Eq for Vector<T> {}

impl<T: Display> Display for Vector<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "[")?;
    for (i, e) in self.iter().enumerate() {
      write!(f, "{}", e)?;
      if i < self.len - 1 {
        write!(f, ", ")?;
      }
    }
    write!(f, "]")
  }
}

impl<T> std::ops::Index<usize> for Vector<T> {
  type Output = T;

  fn index(&self, index: usize) -> &Self::Output {
    if index >= self.len {
      panic!("index out of bounds");
    }
    unsafe { self.data.as_ptr().add(index).as_ref().unwrap() }
  }
}

impl<T> std::ops::IndexMut<usize> for Vector<T> {
  fn index_mut(&mut self, index: usize) -> &mut Self::Output {
    if index >= self.len {
      panic!("index out of bounds");
    }
    unsafe { self.data.as_ptr().add(index).as_mut().unwrap() }
  }
}

impl<T> Default for Vector<T> {
  fn default() -> Self {
    Self::new()
  }
}

impl<T> Vector<T> {
  pub fn new() -> Self {
    let layout = std::alloc::Layout::array::<T>(INIT_CAPACITY).unwrap();
    let ptr = unsafe { std::alloc::alloc(layout) };
    Self {
      data: unsafe { NonNull::new_unchecked(ptr as *mut T) },
      len: 0,
      capacity: INIT_CAPACITY,
    }
  }

  pub fn with_capacity(capacity: usize) -> Self {
    let layout = std::alloc::Layout::array::<T>(capacity).unwrap();
    let ptr = unsafe { std::alloc::alloc(layout) };
    Self {
      data: unsafe { NonNull::new_unchecked(ptr as *mut T) },
      len: 0,
      capacity,
    }
  }
}

impl<T> Drop for Vector<T> {
  fn drop(&mut self) {
    let layout = std::alloc::Layout::array::<T>(self.capacity).unwrap();
    unsafe {
      std::alloc::dealloc(self.data.as_ptr() as *mut u8, layout);
    }
  }
}

impl<T> Vector<T> {
  fn auto_expand(&mut self) {
    let new_capacity = if self.capacity != 0 {
      self.capacity * EXPAND_FACTOR
    } else {
      INIT_CAPACITY
    };
    let layout = std::alloc::Layout::array::<T>(new_capacity).unwrap();
    let new_ptr = unsafe { std::alloc::alloc(layout) };
    let new_data = unsafe { NonNull::new_unchecked(new_ptr as *mut T) };
    unsafe {
      std::ptr::copy_nonoverlapping(self.data.as_ptr(), new_data.as_ptr(), self.len);
      std::alloc::dealloc(self.data.as_ptr() as *mut u8, layout);
    }
    self.data = new_data;
    self.capacity = new_capacity;
  }

  pub fn reserve(&mut self, additional: usize) {
    if self.capacity - self.len < additional {
      let new_capacity = self.capacity + additional;
      let layout = std::alloc::Layout::array::<T>(new_capacity).unwrap();
      let new_ptr = unsafe { std::alloc::alloc(layout) };
      let new_data = unsafe { NonNull::new_unchecked(new_ptr as *mut T) };
      unsafe {
        std::ptr::copy_nonoverlapping(self.data.as_ptr(), new_data.as_ptr(), self.len);
        std::alloc::dealloc(self.data.as_ptr() as *mut u8, layout);
      }
      self.data = new_data;
      self.capacity = new_capacity;
    }
  }

  pub fn shrink(&mut self) {
    let layout = std::alloc::Layout::array::<T>(self.len).unwrap();
    let new_ptr = unsafe { std::alloc::alloc(layout) };
    let new_data = unsafe { NonNull::new_unchecked(new_ptr as *mut T) };
    unsafe {
      std::ptr::copy_nonoverlapping(self.data.as_ptr(), new_data.as_ptr(), self.len);
      std::alloc::dealloc(self.data.as_ptr() as *mut u8, layout);
    }
    self.data = new_data;
    self.capacity = self.len;
  }
}

impl<T> Vector<T> {
  pub fn push(&mut self, value: T) {
    if self.len == self.capacity {
      self.auto_expand();
    }
    unsafe {
      std::ptr::write(self.data.as_ptr().add(self.len), value);
    }
    self.len += 1;
  }

  pub fn push_to_nth(&mut self, value: T, n: usize) -> Option<&T> {
    if n > self.len {
      return None;
    }
    if self.len == self.capacity {
      self.auto_expand();
    }
    let ret = unsafe { self.data.as_ptr().add(n).as_ref() };
    unsafe {
      std::ptr::copy(
        self.data.as_ptr().add(n),
        self.data.as_ptr().add(n + 1),
        self.len - n,
      );
      std::ptr::write(self.data.as_ptr().add(n), value);
    }
    self.len += 1;
    ret
  }
}

impl<T> Vector<T> {
  pub fn pop(&mut self) -> Option<T> {
    if self.len == 0 {
      return None;
    }
    self.len -= 1;
    unsafe { Some(std::ptr::read(self.data.as_ptr().add(self.len))) }
  }

  pub fn clear(&mut self) {
    self.len = 0;
  }

  pub fn complete_clear(&mut self) {
    self.len = 0;
    self.shrink();
  }
}

impl<T> Vector<T> {
  pub fn get(&mut self, n: usize) -> Option<&T> {
    if n >= self.len {
      return None;
    }
    unsafe { (self.data.as_ptr().add(n)).as_ref() }
  }

  pub fn get_mut(&mut self, n: usize) -> Option<&mut T> {
    if n >= self.len {
      return None;
    }
    unsafe { (self.data.as_ptr().add(n)).as_mut() }
  }

  pub fn first(&mut self) -> Option<&T> {
    self.get(0)
  }

  pub fn first_mut(&mut self) -> Option<&mut T> {
    self.get_mut(0)
  }

  pub fn last(&mut self) -> Option<&T> {
    self.get(self.len - 1)
  }

  pub fn last_mut(&mut self) -> Option<&mut T> {
    self.get_mut(self.len - 1)
  }
}

impl<T> Vector<T> {
  pub fn len(&self) -> usize {
    self.len
  }

  pub fn is_empty(&self) -> bool {
    self.len == 0
  }

  pub fn capacity(&self) -> usize {
    self.capacity
  }
}

#[cfg(test)]
mod test_vector {
  use super::*;

  #[test]
  fn drop_shrink_expand() {
    let mut vec = Vector::<()>::new();
    assert_eq!(vec.capacity, INIT_CAPACITY);
    vec.auto_expand();
    assert_eq!(vec.capacity, INIT_CAPACITY * EXPAND_FACTOR);
    drop(vec);
    let mut vec = Vector::<()>::new();
    assert_eq!(vec.capacity, INIT_CAPACITY);
    vec.shrink();
    assert_eq!(vec.capacity, 0);
  }

  #[test]
  fn push_pop() {
    let mut vec = Vector::new();
    for e in 1..10 {
      vec.push(e);
    }
    vec.push_to_nth(0, 0);
    let mut collected = vec![];
    for i in 0..vec.len() {
      collected.push(vec[i]);
    }
    assert_eq!(collected, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
  }

  #[test]
  fn get_and_get_mut() {
    let mut vec = Vector::new();
    for e in 0..10 {
      vec.push(e);
    }
    vec.push(9);
    assert_eq!(vec.last(), Some(&9));
    *vec.last_mut().unwrap() += 1;
    assert_eq!(vec.last(), Some(&10));
    assert_eq!(vec.first(), Some(&0));
    *vec.first_mut().unwrap() -= 1;
    assert_eq!(vec.first(), Some(&-1));
  }

  #[test]
  fn iter_with_rev() {
    let builder = 0..10;
    let vec = builder.clone().rev().collect::<Vector<_>>();
    for (&actual, expect) in vec.into_iter().zip(builder.rev()) {
      assert_eq!(actual, expect);
    }
  }

  #[test]
  fn iter_mut_with_rev() {
    let builder = 0..10;
    let mut vec = builder.clone().rev().collect::<Vector<_>>();
    vec.iter_mut().for_each(|e| *e += 1);
    for (&actual, expect) in vec.into_iter().zip(builder.rev().map(|e| e + 1)) {
      assert_eq!(actual, expect);
    }
  }

  #[test]
  fn assign_capacity() {
    let mut vec = Vector::<()>::with_capacity(0);
    assert_eq!(vec.capacity(), 0);
    (0..INIT_CAPACITY).for_each(|_| vec.push(()));
    assert_eq!(vec.capacity(), INIT_CAPACITY);
    vec.reserve(4);
    assert_eq!(vec.capacity(), vec.len() + 4);
  }

  #[test]
  fn format() {
    let vec = Vector::from_iter([1, 2, 3, 3, 2, 1]);
    assert_eq!(format!("{}", vec), "[1, 2, 3, 3, 2, 1]");
  }

  #[test]
  fn clear_and_drop() {
    let mut vec = Vector::from_iter([1, 2, 3, 3, 2, 1]);
    assert_eq!(vec.len(), 6);
    vec.clear();
    assert_eq!(vec.capacity(), INIT_CAPACITY);
    assert_eq!(vec.len(), 0);
    vec.push(1);
    assert_eq!(vec.capacity(), INIT_CAPACITY);
    assert_eq!(vec.len(), 1);
    vec.complete_clear();
    assert_eq!(vec.capacity(), 0);
    assert_eq!(vec.len(), 0);
    drop(vec);
  }
}
