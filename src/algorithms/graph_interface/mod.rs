pub mod extreme_path;

pub struct Edge<Node, Value> {
  pub(crate) dst: Node,
  pub(crate) cost: Value,
}

impl<Node, Value> Edge<Node, Value> {
  pub fn new(dst: Node, cost: Value) -> Self {
    Self { dst, cost }
  }
}

impl<Node: Copy, Value: Copy> Copy for Edge<Node, Value> {}

impl<Node: Clone, Value: Clone> Clone for Edge<Node, Value> {
  fn clone(&self) -> Self {
    Self {
      dst: self.dst.clone(),
      cost: self.cost.clone(),
    }
  }
}

impl<Node: Default, Value: Default> Default for Edge<Node, Value> {
  fn default() -> Self {
    Self {
      dst: Default::default(),
      cost: Default::default(),
    }
  }
}

pub struct Accumulation<Node, Value, const MAXIMUM: bool = false> {
  pub(crate) dst: Node,
  pub(crate) cost: Value,
}

impl<Node, Value: Ord, const MAXIMUM: bool> Ord for Accumulation<Node, Value, MAXIMUM> {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    let order = self.cost.cmp(&other.cost);
    if !MAXIMUM {
      order.reverse()
    } else {
      order
    }
  }
}

impl<Node, Value: PartialOrd, const MAXIMUM: bool> PartialOrd
  for Accumulation<Node, Value, MAXIMUM>
{
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    let wrapped_order = self.cost.partial_cmp(&other.cost);
    if !MAXIMUM {
      wrapped_order.map(|res| res.reverse())
    } else {
      wrapped_order
    }
  }
}

impl<Node, Value: Eq, const MAXIMUM: bool> Eq for Accumulation<Node, Value, MAXIMUM> {}

impl<Node, Value: PartialEq, const MAXIMUM: bool> PartialEq for Accumulation<Node, Value, MAXIMUM> {
  fn eq(&self, other: &Self) -> bool {
    self.cost == other.cost
  }
}

impl<Node: Copy, Value: Copy, const MAXIMUM: bool> Copy for Accumulation<Node, Value, MAXIMUM> {}

impl<Node: Clone, Value: Clone, const MAXIMUM: bool> Clone for Accumulation<Node, Value, MAXIMUM> {
  fn clone(&self) -> Self {
    Self {
      dst: self.dst.clone(),
      cost: self.cost.clone(),
    }
  }
}

impl<Node: Default, Value: Default, const MAXIMUM: bool> Default
  for Accumulation<Node, Value, MAXIMUM>
{
  fn default() -> Self {
    Self {
      dst: Default::default(),
      cost: Default::default(),
    }
  }
}
