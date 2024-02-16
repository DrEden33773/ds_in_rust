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
    Self::new_with_cache_capacity(adj_map, bop, self_cost, 4)
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

    match self.resume_from_last_mutated_query(src, goal) {
      ControlFlow::Break(res) => return res,
      ControlFlow::Continue(_) => {}
    };

    let heap = self.heap_cache.get_mut_unwrapped(&src);
    let cost = self.cost_cache.get_mut_unwrapped(&src);
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
