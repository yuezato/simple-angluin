{-# LANGUAGE ScopedTypeVariables #-}

module WarshallFloyd where

import DFA
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe (fromJust)
import Control.Applicative ( (<|>) )

all_paths :: forall state. (Ord state) => DFA state -> (state -> state -> Maybe String)
all_paths dfa@(entire, sigma, delta, _, _) = foldr step dict entire_l
  where
    entire_l :: [ state ]
    entire_l = Set.toList entire
    
    dict :: state -> state -> Maybe String
    dict p q =
      case [ [c] | c <- Set.toList sigma, delta (p, c) == q ] of
        [] -> Nothing
        (x : _) -> Just x

    join (Just x) _       = Just x
    join Nothing (Just y) = Just y
    join Nothing Nothing  = Nothing

    step :: state -> (state -> state -> Maybe String) -> (state -> state -> Maybe String)
    step k dict = new_dict
      where
        new_dict p q = (dict p q) <|> (liftM2 (++) (dict p k) (dict k q))

accessible' :: forall state. Ord state => DFA state -> Set (state, String)
accessible' dfa@(states, sigma, delta, qinit, qf) = Set.fromList [ (q, fromJust $ witness q) | q <- Set.toList states, witness q /= Nothing ]
  where
    witness q = (all_paths dfa) qinit q
    
