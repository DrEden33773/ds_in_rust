use crate::lru_cache::LruCache;

use self::greedy_extreme_path::Bounded;
use super::*;
use std::{
  collections::{BinaryHeap, HashMap},
  hash::Hash,
  ops::ControlFlow,
};

#[allow(dead_code)]
pub struct CachedGreedyExtremePathView<'map, Node, Val, BOP, const REVERSED: bool = false>
where
  Node: Hash,
  Val: Ord + Bounded,
  BOP: Fn(Val, Val) -> Val,
{
  cost_cache: LruCache<&'map Node, HashMap<&'map Node, Val>>,
  path_cache: LruCache<&'map Node, HashMap<&'map Node, &'map Node>>,
  heap_cache: LruCache<&'map Node, BinaryHeap<Accumulation<&'map Node, Val, REVERSED>>>,
  src_cache: LruCache<&'map Node, Option<&'map Node>>,
  adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>,
  bop: BOP,
  last_accumulation_cache: LruCache<&'map Node, Option<Accumulation<&'map Node, Val, REVERSED>>>,
  self_cost: Val,
}

#[allow(unused)]
pub type CachedGreedyShortestPathView<'map, Node, Val, BOP> =
  CachedGreedyExtremePathView<'map, Node, Val, BOP, false>;

#[allow(unused)]
pub type CachedGreedyLongestPathView<'map, Node, Val, BOP> =
  CachedGreedyExtremePathView<'map, Node, Val, BOP, true>;

impl<'map, Node, Val, BOP, const REVERSED: bool>
  CachedGreedyExtremePathView<'map, Node, Val, BOP, REVERSED>
where
  Node: Hash + Eq,
  Val: Ord + Bounded,
  BOP: Fn(Val, Val) -> Val,
{
  pub fn new(adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>, bop: BOP, self_cost: Val) -> Self {
    #[cfg(not(test))]
    return Self::new_with_cache_capacity(adj_map, bop, self_cost, 4);

    #[cfg(test)]
    return Self::new_with_cache_capacity(adj_map, bop, self_cost, 8);
  }

  pub fn new_with_cache_capacity(
    adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>,
    bop: BOP,
    self_cost: Val,
    capacity: usize,
  ) -> Self {
    Self {
      cost_cache: LruCache::new(capacity),
      path_cache: LruCache::new(capacity),
      heap_cache: LruCache::new(capacity),
      src_cache: LruCache::new(capacity),
      adj_map,
      bop,
      last_accumulation_cache: LruCache::new(capacity),
      self_cost,
    }
  }
}

impl<'map, Node, Val, BOP, const REVERSED: bool>
  CachedGreedyExtremePathView<'map, Node, Val, BOP, REVERSED>
where
  Node: Hash + Clone + Eq,
  Val: Ord + Clone + Bounded,
  BOP: Fn(Val, Val) -> Val,
{
  fn build_cache(&mut self, node: &'map Node) {
    let mut cost = HashMap::new();
    let mut path = HashMap::new();
    let mut heap = BinaryHeap::new();
    let src = Some(node);
    let last_accumulation = None;

    cost.insert(node, self.self_cost.clone());
    path.insert(node, node);
    heap.push(Accumulation {
      dst: node,
      cost: self.self_cost.clone(),
    });

    self.cost_cache.put(node, cost);
    self.path_cache.put(node, path);
    self.heap_cache.put(node, heap);
    self.src_cache.put(node, src);
    self.last_accumulation_cache.put(node, last_accumulation);
  }

  fn resume_from_last_mutated_query(
    &mut self,
    src: &'map Node,
    goal: &Node,
  ) -> ControlFlow<Option<Val>, ()> {
    let heap = self.heap_cache.get_mut_unwrapped(&src);
    let cost = self.cost_cache.get_mut_unwrapped(&src);
    let path = self.path_cache.get_mut_unwrapped(&src);
    let last_accumulation = self.last_accumulation_cache.get_mut_unwrapped(&src);

    if let Some(Accumulation {
      dst: picked,
      cost: src_to_picked,
    }) = last_accumulation.clone()
    {
      if picked == goal {
        *last_accumulation = Some(Accumulation {
          dst: picked,
          cost: src_to_picked.clone(),
        });
        return ControlFlow::Break(Some(src_to_picked.clone()));
      }

      if let Some(old_dist) = cost.get(picked) {
        if !REVERSED && src_to_picked > *old_dist {
          return ControlFlow::Continue(());
        }
        if REVERSED && src_to_picked < *old_dist {
          return ControlFlow::Continue(());
        }
      }

      let edges = self.adj_map.get(picked);
      if edges.is_none() {
        return ControlFlow::Continue(());
      }

      for Edge {
        dst,
        cost: picked_to_next,
      } in edges.unwrap()
      {
        let src_to_next = (self.bop)(src_to_picked.clone(), picked_to_next.clone());
        let should_update = if !REVERSED {
          src_to_next < *cost.get(dst).unwrap_or(&<Val as Bounded>::max())
        } else {
          src_to_next > *cost.get(dst).unwrap_or(&<Val as Bounded>::min())
        };
        if should_update {
          cost.insert(dst, src_to_next.clone());
          path.insert(dst, picked);
          heap.push(Accumulation {
            dst,
            cost: src_to_next,
          });
        }
      }
    }

    ControlFlow::Continue(())
  }

  pub fn extreme_cost(&mut self, src: &'map Node, goal: &Node) -> Option<Val> {
    if !self.adj_map.contains_key(src) || !self.adj_map.contains_key(goal) {
      return None;
    }

    if !self.src_cache.contains_key(&src) {
      self.build_cache(src);
    }

    if let Some(dist) = self.cost_cache.get_unwrapped(&src).get(goal) {
      return Some(dist.clone());
    }

    match self.resume_from_last_mutated_query(src, goal) {
      ControlFlow::Break(res) => return res,
      ControlFlow::Continue(_) => {}
    };

    let cost = self.cost_cache.get_mut_unwrapped(&src);
    let heap = self.heap_cache.get_mut_unwrapped(&src);
    let path = self.path_cache.get_mut_unwrapped(&src);
    let last_accumulation = self.last_accumulation_cache.get_mut_unwrapped(&src);

    while let Some(Accumulation {
      dst: picked,
      cost: src_to_picked,
    }) = heap.pop()
    {
      if picked == goal {
        *last_accumulation = Some(Accumulation {
          dst: picked,
          cost: src_to_picked.clone(),
        });
        return Some(src_to_picked.clone());
      }

      if let Some(old_dist) = cost.get(picked) {
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
      } in self.adj_map.get(picked)?
      {
        let src_to_next = (self.bop)(src_to_picked.clone(), picked_to_next.clone());
        let should_update = if !REVERSED {
          src_to_next < *cost.get(dst).unwrap_or(&<Val as Bounded>::max())
        } else {
          src_to_next > *cost.get(dst).unwrap_or(&<Val as Bounded>::min())
        };
        if should_update {
          cost.insert(dst, src_to_next.clone());
          path.insert(dst, picked);
          heap.push(Accumulation {
            dst,
            cost: src_to_next,
          });
        }
      }
    }

    None
  }

  pub fn extreme_path(&mut self, src: &'map Node, goal: &Node) -> Vec<Node> {
    if !self.adj_map.contains_key(src) || !self.adj_map.contains_key(goal) {
      return vec![];
    }

    // 1. execute `self.extreme_cost()` first
    let cost = self.extreme_cost(src, goal);
    if cost.is_none() {
      return vec![];
    }
    // 2. build result
    let mut result = vec![];
    let mut current = goal;
    while current != src {
      result.push(current.clone());
      current = self.path_cache.get_unwrapped(&src).get(current).unwrap();
    }
    result.push(src.clone());
    result.reverse();

    // 3. done!
    result
  }
}

#[cfg(test)]
mod test_cached_extreme_cost {
  use super::*;
  use ordered_float::NotNan;
  use std::ops::Mul;

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

    let test_cases = vec![
      (&0, &1, Some(1)),
      (&0, &3, Some(3)),
      (&3, &0, Some(7)),
      (&4, &0, None),
      (&2, &4, Some(1)),
      (&3, &4, Some(2)),
      (&0, &4, Some(5)),
      (&2, &1, Some(1)),
      (&4, &1, None),
      (&1, &2, Some(19)),
      (&3, &1, Some(8)),
      (&114514, &1919810, None),
    ];

    let mut shortest = CachedGreedyShortestPathView::new(&adj_map, |a, b| a + b, 0);

    for (start, end, expected_cost) in test_cases {
      println!("Testing: ({start}, {end}, {expected_cost:?})");
      assert_eq!(shortest.extreme_cost(start, end), expected_cost);
    }
  }

  #[test]
  fn test_official_case_with_queries_exiled() {
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

    let mut shortest =
      CachedGreedyShortestPathView::new_with_cache_capacity(&adj_map, |a, b| a + b, 0, 4);

    assert_eq!(shortest.extreme_cost(&0, &1), Some(1));
    assert_eq!(shortest.extreme_cost(&0, &3), Some(3));
    assert_eq!(shortest.extreme_cost(&3, &0), Some(7));
    assert_eq!(shortest.extreme_cost(&4, &0), None);
    assert_eq!(shortest.extreme_cost(&2, &4), Some(1));
    assert_eq!(shortest.extreme_cost(&3, &4), Some(2));
    assert_eq!(shortest.extreme_cost(&0, &4), Some(5));
    assert_eq!(shortest.extreme_cost(&2, &1), Some(1));
    assert_eq!(shortest.extreme_cost(&4, &1), None);
    assert_eq!(shortest.extreme_cost(&1, &2), Some(19));
    assert_eq!(shortest.extreme_cost(&3, &1), Some(8));
    assert_eq!(shortest.extreme_cost(&114514, &1919810), None);
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

    let test_cases = vec![
      (&0, &1, None),
      (&0, &3, None),
      (&3, &0, None),
      (&4, &0, None),
      (&2, &4, None),
      (&3, &4, None),
      (&0, &4, None),
      (&2, &1, None),
      (&4, &1, None),
    ];

    let mut shortest = CachedGreedyShortestPathView::new(&adj_map, |a, b| a + b, 0);

    for (start, end, expected_cost) in &test_cases {
      assert_eq!(shortest.extreme_cost(start, end), *expected_cost);
    }

    let mut longest = CachedGreedyLongestPathView::new(&adj_map, |a, b| a + b, 0);

    for (start, end, expected_cost) in test_cases {
      assert_eq!(longest.extreme_cost(start, end), expected_cost);
    }
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

    let test_cases = vec![
      (&0, &1, Some(0)),
      (&0, &2, Some(0)),
      (&1, &0, Some(0)),
      (&1, &2, Some(0)),
      (&2, &0, Some(0)),
      (&2, &1, Some(0)),
    ];

    let mut shortest = CachedGreedyShortestPathView::new(&adj_map, |a, b| a + b, 0);

    for (start, end, expected_cost) in &test_cases {
      assert_eq!(shortest.extreme_cost(start, end), *expected_cost);
    }

    let mut longest = CachedGreedyLongestPathView::new(&adj_map, |a, b| a + b, 0);

    for (start, end, expected_cost) in test_cases {
      assert_eq!(longest.extreme_cost(start, end), expected_cost);
    }
  }

  #[test]
  fn test_leetcode_case() {
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    struct Possibility(NotNan<f64>);

    impl Bounded for Possibility {
      fn min() -> Self {
        Possibility(NotNan::new(0.0).unwrap())
      }

      fn max() -> Self {
        Possibility(NotNan::new(1.0).unwrap())
      }
    }

    impl Mul for Possibility {
      type Output = Self;

      fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
      }
    }

    impl From<NotNan<f64>> for Possibility {
      fn from(value: NotNan<f64>) -> Self {
        Self(value)
      }
    }

    let edges = vec![(1, 4), (2, 4), (0, 4), (0, 3), (0, 2), (2, 3)];
    let succ_proc = vec![0.37, 0.17, 0.93, 0.23, 0.39, 0.04];

    let mut adj_map: HashMap<i32, Vec<Edge<i32, Possibility>>> = HashMap::new();

    for ((src, dst), cost) in edges.into_iter().zip(succ_proc) {
      adj_map
        .entry(src)
        .or_default()
        .push(Edge::new(dst, NotNan::new(cost).unwrap().into()));

      // ATTENTION: According to the test case of `leetcode_1514`,
      // all of the edges in the graph should be `double-arrowed`

      adj_map
        .entry(dst)
        .or_default()
        .push(Edge::new(src, NotNan::new(cost).unwrap().into()));
    }

    let mut max_probability =
      CachedGreedyLongestPathView::new(&adj_map, |a, b| a * b, NotNan::new(1.0).unwrap().into());

    assert_eq!(
      max_probability.extreme_cost(&3, &4),
      Some(NotNan::new(0.2139).unwrap().into())
    );
  }
}

#[cfg(test)]
mod test_cached_extreme_path {
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

    let mut shortest = CachedGreedyShortestPathView::new(&adj_map, |a, b| a + b, 0);

    let test_cases = vec![
      (&0, &1, vec![0, 1]),
      (&0, &3, vec![0, 1, 3]),
      (&3, &0, vec![3, 0]),
      (&4, &0, vec![]),
      (&2, &4, vec![2, 4]),
      (&3, &4, vec![3, 4]),
      (&0, &4, vec![0, 1, 3, 4]),
      (&2, &1, vec![2, 1]),
      (&4, &1, vec![]),
      (&1, &2, vec![1, 3, 0, 2]),
      (&3, &1, vec![3, 0, 1]),
      (&114514, &1919810, vec![]),
    ];

    for (start, end, expected_path) in test_cases {
      println!("Testing: ({start}, {end}, {:?})", expected_path.clone());
      assert_eq!(shortest.extreme_path(start, end), expected_path);
    }
  }
}
