use crate::lru_cache::LruCache;

use self::greedy_extreme_path::Bounded;
use super::*;
use std::{
  collections::{BinaryHeap, HashMap},
  hash::Hash,
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
  heap: LruCache<&'map Node, BinaryHeap<Accumulation<&'map Node, Val, REVERSED>>>,
  src: LruCache<&'map Node, Option<&'map Node>>,
  adj_map: &'map HashMap<Node, Vec<Edge<Node, Val>>>,
  bop: BOP,
  last_accumulation: LruCache<&'map Node, Option<Accumulation<&'map Node, Val, REVERSED>>>,
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
      heap: LruCache::new(capacity),
      src: LruCache::new(capacity),
      adj_map,
      bop,
      last_accumulation: LruCache::new(capacity),
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
  pub fn extreme_cost(&mut self, src: &'map Node, goal: &Node) -> Option<Val> {
    if !self.adj_map.contains_key(src) || !self.adj_map.contains_key(goal) {
      return None;
    }

    todo!()
  }
}
