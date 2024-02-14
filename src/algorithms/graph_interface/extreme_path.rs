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

pub trait Monotonous: Bounded {}

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
      impl Monotonous for $t {}
    )*
  };
}

impl_bounded!(u8, u16, u32, u64, u128, usize);

pub struct ExtremePathExecutor<'map, Node, Val, BOP, const REVERSED: bool = false>
where
  Node: Hash,
  Val: Ord + Bounded + Monotonous,
  BOP: Fn(Val, Val) -> Val,
{
  pub(crate) dist_cache: HashMap<Node, Val>,
  pub(crate) path_cache: HashMap<Node, Node>,
  pub(crate) heap: BinaryHeap<Accumulation<Node, Val, REVERSED>>,
  pub(crate) src: Option<Node>,
  pub(crate) adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>,
  pub(crate) binary_op: BOP,
  last_accumulation: Option<Accumulation<Node, Val, REVERSED>>,
  self_cost: Val,
}

#[allow(unused)]
type ShortestPathExecutor<'map, Node, Val, BOP> = ExtremePathExecutor<'map, Node, Val, BOP>;

#[allow(unused)]
type LongestPathExecutor<'map, Node, Val, BOP> = ExtremePathExecutor<'map, Node, Val, BOP, true>;

impl<'map, Node, Val, BOP> ExtremePathExecutor<'map, Node, Val, BOP>
where
  Node: Hash,
  Val: Ord + Bounded + Monotonous,
  BOP: Fn(Val, Val) -> Val,
{
  pub fn new(
    adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>,
    binary_op: BOP,
    self_cost: Val,
  ) -> Self {
    Self {
      dist_cache: HashMap::new(),
      path_cache: HashMap::new(),
      heap: BinaryHeap::new(),
      src: None,
      adj_map,
      binary_op,
      last_accumulation: None,
      self_cost,
    }
  }
}

impl<'map, Node, Val, BOP> ExtremePathExecutor<'map, Node, Val, BOP, true>
where
  Node: Hash,
  Val: Ord + Bounded + Monotonous,
  BOP: Fn(Val, Val) -> Val,
{
  pub fn new(
    adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>,
    binary_op: BOP,
    self_cost: Val,
  ) -> Self {
    Self {
      dist_cache: HashMap::new(),
      path_cache: HashMap::new(),
      heap: BinaryHeap::new(),
      src: None,
      adj_map,
      binary_op,
      last_accumulation: None,
      self_cost,
    }
  }
}

impl<Node, Val, BOP, const REVERSED: bool> ExtremePathExecutor<'_, Node, Val, BOP, REVERSED>
where
  Node: Hash + Clone + Eq,
  Val: Ord + Clone + Bounded + Monotonous,
  BOP: Fn(Val, Val) -> Val,
{
  fn clear_all_cache(&mut self) {
    self.dist_cache.clear();
    self.path_cache.clear();
    self.heap.clear();
    self.last_accumulation = None;
  }

  fn init(&mut self, node: Node) {
    self.src = Some(node.clone());
    self.dist_cache.insert(node.clone(), self.self_cost.clone());
    self.path_cache.insert(node.clone(), node.clone());
    self.heap.push(Accumulation {
      dst: node,
      cost: self.self_cost.clone(),
    });
  }

  fn cas(&mut self, node: Node) {
    if let Some(ref old_node) = self.src {
      if *old_node != node {
        self.clear_all_cache();
        self.init(node);
      }
    } else {
      self.init(node);
    }
  }

  fn resume_from_prev_extreme_dist_query(&mut self, goal: &Node) -> ControlFlow<Option<Val>, ()> {
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

      if let Some(old_dist) = self.dist_cache.get(&picked) {
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
        let src_to_next = (self.binary_op)(src_to_picked.clone(), picked_to_next.clone());
        let should_update = if !REVERSED {
          src_to_next
            < *self
              .dist_cache
              .get(&dst)
              .unwrap_or(&<Val as Bounded>::max())
        } else {
          src_to_next
            > *self
              .dist_cache
              .get(&dst)
              .unwrap_or(&<Val as Bounded>::min())
        };
        if should_update {
          self.dist_cache.insert(dst.clone(), src_to_next.clone());
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

  pub fn extreme_dist(&mut self, src: Node, goal: Node) -> Option<Val> {
    self.cas(src);

    if let Some(dist) = self.dist_cache.get(&goal) {
      return Some(dist.clone());
    }

    match self.resume_from_prev_extreme_dist_query(&goal) {
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

      if let Some(old_dist) = self.dist_cache.get(&picked) {
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
        let src_to_next = (self.binary_op)(src_to_picked.clone(), picked_to_next.clone());
        let should_update = if !REVERSED {
          src_to_next
            < *self
              .dist_cache
              .get(&dst)
              .unwrap_or(&<Val as Bounded>::max())
        } else {
          src_to_next
            > *self
              .dist_cache
              .get(&dst)
              .unwrap_or(&<Val as Bounded>::min())
        };
        if should_update {
          self.dist_cache.insert(dst.clone(), src_to_next.clone());
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
}

#[cfg(test)]
mod test_shortest_path_executor {
  use ordered_float::NotNan;

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
    .collect::<HashMap<_, _>>();

    let mut shortest = ShortestPathExecutor::new(&adj_map, |a, b| a + b, 0);

    assert_eq!(shortest.extreme_dist(0, 1), Some(1));
    assert_eq!(shortest.extreme_dist(0, 3), Some(3));
    assert_eq!(shortest.extreme_dist(3, 0), Some(7));
    assert_eq!(shortest.extreme_dist(4, 0), None);
    assert_eq!(shortest.extreme_dist(2, 4), Some(1));
    assert_eq!(shortest.extreme_dist(3, 4), Some(2));
    assert_eq!(shortest.extreme_dist(0, 4), Some(5));
    assert_eq!(shortest.extreme_dist(2, 1), Some(1));
    assert_eq!(shortest.extreme_dist(4, 1), None);
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

    impl Monotonous for NotNan<f64> {}

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

    let mut max_prob = LongestPathExecutor::new(&adj_map, |a, b| a * b, NotNan::new(1.0).unwrap());

    assert_eq!(
      max_prob.extreme_dist(3, 4),
      Some(NotNan::new(0.2139).unwrap())
    );
  }
}
