use std::{
  collections::{BinaryHeap, HashMap},
  hash::Hash,
  ops::ControlFlow,
};

use super::*;

pub trait Bounded {
  fn min() -> Self;
  fn max() -> Self;
}

/// To implement [`Bounded`] and [`Monotonous`] for basic types
/// which has `MIN` and `MAX` constants.
#[macro_export]
macro_rules! impl_bounded {
  ($($t:ty),*) => {
    $(
      impl Bounded for $t {
        fn min() -> Self {
          Self::MIN
        }
        fn max() -> Self {
          Self::MAX
        }
      }
    )*
  };
}

impl_bounded!(u8, u16, u32, u64, u128, usize);
impl_bounded!(i8, i16, i32, i64, i128, isize);
impl_bounded!(f32, f64);

pub struct GreedyExtremePathExecutor<'map, Node, Val, BOP, const REVERSED: bool = false>
where
  Node: Hash,
  Val: Ord + Bounded,
  BOP: Fn(Val, Val) -> Val,
{
  cost_cache: HashMap<Node, Val>,
  path_cache: HashMap<Node, Node>,
  heap: BinaryHeap<Accumulation<Node, Val, REVERSED>>,
  src: Option<Node>,
  adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>,
  bop: BOP,
  last_accumulation: Option<Accumulation<Node, Val, REVERSED>>,
  self_cost: Val,
}

#[allow(unused)]
pub type GreedyShortestPathExecutor<'map, Node, Val, BOP> =
  GreedyExtremePathExecutor<'map, Node, Val, BOP, false>;

#[allow(unused)]
pub type GreedyLongestPathExecutor<'map, Node, Val, BOP> =
  GreedyExtremePathExecutor<'map, Node, Val, BOP, true>;

impl<'map, Node, Val, BOP> GreedyExtremePathExecutor<'map, Node, Val, BOP>
where
  Node: Hash,
  Val: Ord + Bounded,
  BOP: Fn(Val, Val) -> Val,
{
  pub fn new(adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>, bop: BOP, self_cost: Val) -> Self {
    Self {
      cost_cache: HashMap::new(),
      path_cache: HashMap::new(),
      heap: BinaryHeap::new(),
      src: None,
      adj_map,
      bop,
      last_accumulation: None,
      self_cost,
    }
  }
}

impl<'map, Node, Val, BOP> GreedyExtremePathExecutor<'map, Node, Val, BOP, true>
where
  Node: Hash,
  Val: Ord + Bounded,
  BOP: Fn(Val, Val) -> Val,
{
  pub fn new(adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>, bop: BOP, self_cost: Val) -> Self {
    Self {
      cost_cache: HashMap::new(),
      path_cache: HashMap::new(),
      heap: BinaryHeap::new(),
      src: None,
      adj_map,
      bop,
      last_accumulation: None,
      self_cost,
    }
  }
}

impl<Node, Val, BOP, const REVERSED: bool> GreedyExtremePathExecutor<'_, Node, Val, BOP, REVERSED>
where
  Node: Hash + Clone + Eq,
  Val: Ord + Clone + Bounded,
  BOP: Fn(Val, Val) -> Val,
{
  fn clear_all_cache(&mut self) {
    self.cost_cache.clear();
    self.path_cache.clear();
    self.heap.clear();
    self.last_accumulation = None;
  }

  fn init(&mut self, node: Node) {
    self.src = Some(node.clone());
    self.cost_cache.insert(node.clone(), self.self_cost.clone());
    self.path_cache.insert(node.clone(), node.clone());
    self.heap.push(Accumulation {
      dst: node,
      cost: self.self_cost.clone(),
    });
  }

  fn compare_and_swap(&mut self, node: Node) {
    if let Some(ref old_node) = self.src {
      if *old_node != node {
        self.clear_all_cache();
        self.init(node);
      }
    } else {
      self.init(node);
    }
  }

  fn resume_from_last_mutated_query(&mut self, goal: &Node) -> ControlFlow<Option<Val>, ()> {
    if let Some(Accumulation {
      dst: picked,
      cost: src_to_picked,
    }) = self.last_accumulation.clone()
    {
      if picked == *goal {
        self.last_accumulation = Some(Accumulation {
          dst: picked.clone(),
          cost: src_to_picked.clone(),
        });
        return ControlFlow::Break(Some(src_to_picked));
      }

      if let Some(old_dist) = self.cost_cache.get(&picked) {
        if !REVERSED && src_to_picked > *old_dist {
          return ControlFlow::Continue(());
        }
        if REVERSED && src_to_picked < *old_dist {
          return ControlFlow::Continue(());
        }
      }

      let edges = self.adj_map.get(&picked);

      if edges.is_none() {
        return ControlFlow::Continue(());
      }

      for Edge {
        dst,
        cost: picked_to_next,
      } in edges.cloned().unwrap()
      {
        let src_to_next = (self.bop)(src_to_picked.clone(), picked_to_next.clone());
        let should_update = if !REVERSED {
          src_to_next
            < *self
              .cost_cache
              .get(&dst)
              .unwrap_or(&<Val as Bounded>::max())
        } else {
          src_to_next
            > *self
              .cost_cache
              .get(&dst)
              .unwrap_or(&<Val as Bounded>::min())
        };
        if should_update {
          self.cost_cache.insert(dst.clone(), src_to_next.clone());
          self.path_cache.insert(dst.clone(), picked.clone());
          self.heap.push(Accumulation {
            dst,
            cost: src_to_next,
          });
        }
      }
    }

    ControlFlow::Continue(())
  }

  pub fn extreme_cost(&mut self, src: Node, goal: Node) -> Option<Val> {
    if !self.adj_map.contains_key(&src) || !self.adj_map.contains_key(&goal) {
      return None;
    }

    self.compare_and_swap(src);

    if let Some(dist) = self.cost_cache.get(&goal) {
      return Some(dist.clone());
    }

    match self.resume_from_last_mutated_query(&goal) {
      ControlFlow::Break(res) => return res,
      ControlFlow::Continue(_) => {}
    };

    while let Some(Accumulation {
      dst: picked,
      cost: src_to_picked,
    }) = self.heap.pop()
    {
      if picked == goal {
        self.last_accumulation = Some(Accumulation {
          dst: picked.clone(),
          cost: src_to_picked.clone(),
        });
        return Some(src_to_picked);
      }

      if let Some(old_dist) = self.cost_cache.get(&picked) {
        if !REVERSED && src_to_picked > *old_dist {
          continue;
        }
        if REVERSED && src_to_picked < *old_dist {
          continue;
        }
      }

      for Edge {
        dst,
        cost: picked_to_next,
      } in self.adj_map.get(&picked)?.clone()
      {
        let src_to_next = (self.bop)(src_to_picked.clone(), picked_to_next.clone());
        let should_update = if !REVERSED {
          src_to_next
            < *self
              .cost_cache
              .get(&dst)
              .unwrap_or(&<Val as Bounded>::max())
        } else {
          src_to_next
            > *self
              .cost_cache
              .get(&dst)
              .unwrap_or(&<Val as Bounded>::min())
        };
        if should_update {
          self.cost_cache.insert(dst.clone(), src_to_next.clone());
          self.path_cache.insert(dst.clone(), picked.clone());
          self.heap.push(Accumulation {
            dst,
            cost: src_to_next,
          });
        }
      }
    }

    None
  }

  pub fn extreme_path(&mut self, src: Node, goal: Node) -> Vec<Node> {
    if !self.adj_map.contains_key(&src) || !self.adj_map.contains_key(&goal) {
      return vec![];
    }

    // 1. execute `self.extreme_cost()` first
    let cost = self.extreme_cost(src.clone(), goal.clone());
    if cost.is_none() {
      return vec![];
    }
    // 2. build result
    let mut result = vec![];
    let mut current = goal;
    while current != src {
      result.push(current.clone());
      current = self.path_cache.get(&current).unwrap().clone();
    }
    result.push(src);
    result.reverse();
    // 3. done!
    result
  }
}

#[cfg(test)]
mod test_extreme_cost {
  use super::*;
  use ordered_float::NotNan;

  /// This is the directed graph we're going to use.
  ///
  /// The node numbers correspond to the different states,
  /// and the edge weights symbolize the cost of moving
  /// from one node to another.
  ///
  /// Note that the edges are one-way.
  ///
  /// ```txt
  ///                  7
  ///          +-----------------+
  ///          |                 |
  ///          v   1        2    |  2
  ///          0 -----> 1 -----> 3 ---> 4
  ///          |        ^        ^      ^
  ///          |        | 1      |      |
  ///          |        |        | 3    | 1
  ///          +------> 2 -------+      |
  ///           10      |               |
  ///                   +---------------+
  /// ```
  ///
  /// The graph is represented as an adjacency list where each index,
  /// corresponding to a node value, has a list of outgoing edges.
  ///
  /// Chosen for its efficiency.
  #[test]
  fn test_official_case() {
    let adj_map = [
      // Node 0
      vec![Edge::new(2, 10usize), Edge::new(1, 1)],
      // Node 1
      vec![Edge::new(3, 2)],
      // Node 2
      vec![Edge::new(1, 1), Edge::new(3, 3), Edge::new(4, 1)],
      // Node 3
      vec![Edge::new(0, 7), Edge::new(4, 2)],
      // Node 4
      vec![],
    ]
    .into_iter()
    .enumerate()
    .collect::<HashMap<usize, Vec<Edge<usize, usize>>>>();

    let mut shortest = GreedyShortestPathExecutor::new(&adj_map, |a, b| a + b, 0);

    for node in 0..=4 {
      assert_eq!(shortest.extreme_cost(node, node), Some(0));
    }

    assert_eq!(shortest.extreme_cost(0, 1), Some(1));
    assert_eq!(shortest.extreme_cost(0, 3), Some(3));
    assert_eq!(shortest.extreme_cost(3, 0), Some(7));
    assert_eq!(shortest.extreme_cost(4, 0), None);
    assert_eq!(shortest.extreme_cost(2, 4), Some(1));
    assert_eq!(shortest.extreme_cost(3, 4), Some(2));
    assert_eq!(shortest.extreme_cost(0, 4), Some(5));
    assert_eq!(shortest.extreme_cost(2, 1), Some(1));
    assert_eq!(shortest.extreme_cost(4, 1), None);
    assert_eq!(shortest.extreme_cost(1, 2), Some(19));
    assert_eq!(shortest.extreme_cost(3, 1), Some(8));

    assert_eq!(shortest.extreme_cost(114514, 1919810), None);
  }

  #[test]
  fn test_isolated_vertices() {
    let adj_map = [
      // Node 0
      vec![],
      // Node 1
      vec![],
      // Node 2
      vec![],
      // Node 3
      vec![],
      // Node 4
      vec![],
    ]
    .into_iter()
    .enumerate()
    .collect::<HashMap<usize, Vec<Edge<_, usize>>>>();

    let mut shortest = GreedyShortestPathExecutor::new(&adj_map, |a, b| a + b, 0);

    assert_eq!(shortest.extreme_cost(0, 1), None);
    assert_eq!(shortest.extreme_cost(0, 3), None);
    assert_eq!(shortest.extreme_cost(3, 0), None);
    assert_eq!(shortest.extreme_cost(4, 0), None);
    assert_eq!(shortest.extreme_cost(2, 4), None);
    assert_eq!(shortest.extreme_cost(3, 4), None);
    assert_eq!(shortest.extreme_cost(0, 4), None);
    assert_eq!(shortest.extreme_cost(2, 1), None);
    assert_eq!(shortest.extreme_cost(4, 1), None);

    let mut longest = GreedyLongestPathExecutor::new(&adj_map, |a, b| a + b, 0);

    assert_eq!(longest.extreme_cost(0, 1), None);
    assert_eq!(longest.extreme_cost(0, 3), None);
    assert_eq!(longest.extreme_cost(3, 0), None);
    assert_eq!(longest.extreme_cost(4, 0), None);
    assert_eq!(longest.extreme_cost(2, 4), None);
    assert_eq!(longest.extreme_cost(3, 4), None);
    assert_eq!(longest.extreme_cost(0, 4), None);
    assert_eq!(longest.extreme_cost(2, 1), None);
    assert_eq!(longest.extreme_cost(4, 1), None);
  }

  #[test]
  fn test_attached_vertices() {
    const ZERO_COST: i32 = 0;
    let adj_map = [
      // Node 0
      vec![Edge::new(1, ZERO_COST), Edge::new(2, ZERO_COST)],
      // Node 1
      vec![Edge::new(0, ZERO_COST), Edge::new(2, ZERO_COST)],
      // Node 2
      vec![Edge::new(0, ZERO_COST), Edge::new(1, ZERO_COST)],
    ]
    .into_iter()
    .enumerate()
    .collect::<HashMap<_, _>>();

    let mut shortest = GreedyShortestPathExecutor::new(&adj_map, |a, b| a + b, 0);

    assert_eq!(shortest.extreme_cost(0, 1), Some(0));
    assert_eq!(shortest.extreme_cost(0, 2), Some(0));
    assert_eq!(shortest.extreme_cost(1, 0), Some(0));
    assert_eq!(shortest.extreme_cost(1, 2), Some(0));
    assert_eq!(shortest.extreme_cost(2, 0), Some(0));
    assert_eq!(shortest.extreme_cost(2, 1), Some(0));

    let mut longest = GreedyLongestPathExecutor::new(&adj_map, |a, b| a + b, 0);

    assert_eq!(longest.extreme_cost(0, 1), Some(0));
    assert_eq!(longest.extreme_cost(0, 2), Some(0));
    assert_eq!(longest.extreme_cost(1, 0), Some(0));
    assert_eq!(longest.extreme_cost(1, 2), Some(0));
    assert_eq!(longest.extreme_cost(2, 0), Some(0));
    assert_eq!(longest.extreme_cost(2, 1), Some(0));
  }

  #[test]
  fn test_leetcode_case() {
    impl Bounded for NotNan<f64> {
      fn min() -> Self {
        NotNan::new(0.0).unwrap()
      }
      fn max() -> Self {
        NotNan::new(1.0).unwrap()
      }
    }

    let edges = vec![(1, 4), (2, 4), (0, 4), (0, 3), (0, 2), (2, 3)];
    let succ_proc = vec![0.37, 0.17, 0.93, 0.23, 0.39, 0.04];

    let mut adj_map: HashMap<i32, Vec<Edge<i32, NotNan<f64>>>> = HashMap::new();

    for ((src, dst), cost) in edges.into_iter().zip(succ_proc) {
      adj_map
        .entry(src)
        .or_default()
        .push(Edge::new(dst, NotNan::new(cost).unwrap()));

      // ATTENTION: According to the test case of `leetcode_1514`,
      // all of the edges in the graph should be `double-arrowed`

      adj_map
        .entry(dst)
        .or_default()
        .push(Edge::new(src, NotNan::new(cost).unwrap()));
    }

    let mut max_probability =
      GreedyLongestPathExecutor::new(&adj_map, |a, b| a * b, NotNan::new(1.0).unwrap());

    assert_eq!(
      max_probability.extreme_cost(3, 4),
      Some(NotNan::new(0.2139).unwrap())
    );
  }
}

#[cfg(test)]
mod test_extreme_path {
  use super::*;

  /// This is the directed graph we're going to use.
  ///
  /// The node numbers correspond to the different states,
  /// and the edge weights symbolize the cost of moving
  /// from one node to another.
  ///
  /// Note that the edges are one-way.
  ///
  /// ```txt
  ///                  7
  ///          +-----------------+
  ///          |                 |
  ///          v   1        2    |  2
  ///          0 -----> 1 -----> 3 ---> 4
  ///          |        ^        ^      ^
  ///          |        | 1      |      |
  ///          |        |        | 3    | 1
  ///          +------> 2 -------+      |
  ///           10      |               |
  ///                   +---------------+
  /// ```
  ///
  /// The graph is represented as an adjacency list where each index,
  /// corresponding to a node value, has a list of outgoing edges.
  ///
  /// Chosen for its efficiency.
  #[test]
  fn test_official_case() {
    let adj_map = [
      // Node 0
      vec![Edge::new(2, 10usize), Edge::new(1, 1)],
      // Node 1
      vec![Edge::new(3, 2)],
      // Node 2
      vec![Edge::new(1, 1), Edge::new(3, 3), Edge::new(4, 1)],
      // Node 3
      vec![Edge::new(0, 7), Edge::new(4, 2)],
      // Node 4
      vec![],
    ]
    .into_iter()
    .enumerate()
    .collect::<HashMap<usize, Vec<Edge<usize, usize>>>>();

    let mut shortest = GreedyShortestPathExecutor::new(&adj_map, |a, b| a + b, 0);

    for node in 0..=4 {
      assert_eq!(shortest.extreme_path(node, node), [node]);
    }

    assert_eq!(shortest.extreme_path(0, 1), [0, 1]);
    assert_eq!(shortest.extreme_path(0, 3), [0, 1, 3]);
    assert_eq!(shortest.extreme_path(3, 0), [3, 0]);
    assert_eq!(shortest.extreme_path(4, 0), []);
    assert_eq!(shortest.extreme_path(2, 4), [2, 4]);
    assert_eq!(shortest.extreme_path(3, 4), [3, 4]);
    assert_eq!(shortest.extreme_path(0, 4), [0, 1, 3, 4]);
    assert_eq!(shortest.extreme_path(2, 1), [2, 1]);
    assert_eq!(shortest.extreme_path(4, 1), []);
    assert_eq!(shortest.extreme_path(1, 2), [1, 3, 0, 2]);
    assert_eq!(shortest.extreme_path(3, 1), [3, 0, 1]);

    assert_eq!(shortest.extreme_path(114514, 1919810), []);
  }
}
