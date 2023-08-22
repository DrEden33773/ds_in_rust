use super::*;

macro_rules! impl_to_slice {
  ($range_type:ty) => {
    impl<T> std::ops::Index<$range_type> for Vector<T> {
      type Output = [T];

      fn index(&self, index: $range_type) -> &Self::Output {
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), self.len) }
          .get(index)
          .unwrap()
      }
    }

    impl<T> std::ops::IndexMut<$range_type> for Vector<T> {
      fn index_mut(&mut self, index: $range_type) -> &mut Self::Output {
        unsafe { std::slice::from_raw_parts_mut(self.data.as_ptr(), self.len) }
          .get_mut(index)
          .unwrap()
      }
    }
  };
}

// &vec[l..r], &mut vec[l..r]
impl_to_slice!(std::ops::Range<usize>);

// &vec[l..=r], &mut vec[l..=r]
impl_to_slice!(std::ops::RangeInclusive<usize>);

// &vec[l..], &mut vec[l..]
impl_to_slice!(std::ops::RangeFrom<usize>);

// &vec[..r], &mut vec[..r]
impl_to_slice!(std::ops::RangeTo<usize>);

// &vec[..=r], &mut vec[..=r]
impl_to_slice!(std::ops::RangeToInclusive<usize>);

// &vec[..], &mut vec[..]
impl_to_slice!(std::ops::RangeFull);
