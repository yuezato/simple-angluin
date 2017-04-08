{-# LANGUAGE ScopedTypeVariables #-}

module Minimize where

import DFA
import Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set

dist_table :: forall state. (Ord state) => DFA state -> Set (state, state)
dist_table dfa@(states, sigma, delta, _, qF) = iter initial_set
  where
    pairs :: Set (state, state)
    pairs = set_prod states states
    
    expand :: Char -> Set (state, state) -> Set (state, state)
    expand c cur =
      Set.fromList
      [ (p, q) |
        p <- Set.toList states, q <- Set.toList states,
        Set.member (delta (p, c), delta (q, c)) cur == True ]

    initial_set :: Set (state, state)
    initial_set = Set.fromList
      [ (p, q) |
        p <- Set.toList states, q <- Set.toList states,
        Set.member p qF /= Set.member q qF ]

    iter :: Set (state, state) -> Set (state, state)
    iter cur =
      let expanded = Set.union cur (Set.unions [ expand c cur | c <- Set.toList sigma ]) in
      if Set.isProperSubsetOf cur expanded
      then iter expanded
      else expanded

build_eqrel :: forall e. Ord e => Set e -> Set (e, e) -> Set (e, e)
build_eqrel entire noteq = Set.difference univ_rel noteq
  where
    univ_rel :: Set (e, e)
    univ_rel = Set.fromList [ (p, q) | p <- Set.toList entire, q <- Set.toList entire ]

build_quo :: forall e. Ord e => Set (e, e) -> Set (Set e)
build_quo eqrel = Set.fromList [ corr x | x <- Set.toList entire ]
  where
    entire :: Set e
    entire = Set.map fst eqrel

    corr :: e -> Set e
    corr x = Set.fromList [ y | y <- Set.toList entire, Set.member (x, y) eqrel ]
    
get_equiv_class :: Ord e => e -> Set (e, e) -> Set e
get_equiv_class x eqrel = Set.fromList [ b | (a, b) <- Set.toList eqrel, a == x ]

minimize :: forall state. Ord state => DFA state -> DFA (Set state)
minimize dfa@(states, sigma, trans, qinit, qF) = (quo_set, sigma, quo_trans, quo_init, quo_F)
  where
    eq_rel :: Set (state, state)
    eq_rel = build_eqrel states (dist_table dfa)
    
    quo_set :: Set (Set state)
    quo_set = build_quo eq_rel

    equiv_class :: state -> Set state
    equiv_class q = get_equiv_class q eq_rel

    quo_init :: Set state
    quo_init = equiv_class qinit

    quo_F :: Set (Set state)
    quo_F = Set.map equiv_class qF

    quo_trans :: Trans (Set state)
    quo_trans (eq_class, c) = equiv_class (trans (Set.elemAt 0 eq_class, c))
