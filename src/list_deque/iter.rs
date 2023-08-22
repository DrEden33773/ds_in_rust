use super::*;
use crate::linked_list::iter::Iter;

impl<T: Default> FromIterator<T> for ListDeque<T> {
  fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
    Self {
      list: iter.into_iter().collect(),
    }
  }
}

impl<'a, T: Default> IntoIterator for &'a ListDeque<T> {
  type Item = &'a T;
  type IntoIter = Iter<'a, T>;
  fn into_iter(self) -> Self::IntoIter {
    self.list.into_iter()
  }
}
