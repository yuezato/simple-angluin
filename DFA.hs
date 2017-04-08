{-# LANGUAGE ScopedTypeVariables #-}

module DFA where

import Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace

type Trans state = (state, Char) -> state

{-
 DFA A is a 5-tuple (Q, \Sigma, \delta, q_init, F)
-}
type DFA state = (Set state, Set Char, Trans state, state, Set state)

dfa_show :: forall state. Show state => DFA state -> String
dfa_show dfa@(states, sigma, delta, qinit, qF) =
  unlines [ to_s p c (delta (p, c)) | p <- Set.toList states, c <- Set.toList sigma ] ++
  "initial: " ++ show qinit ++ "\n" ++
  "acceptings: " ++ show (Set.toList qF)
  where
    to_s :: state -> Char -> state -> String
    to_s p c q = (show p) ++ " --" ++ [c] ++ "--> " ++ (show q)

dfa_dump :: forall state. Show state => DFA state -> IO ()
dfa_dump = putStrLn . dfa_show

{-
Check if a given function `delta` is defined for any pair of `Q` and `\Sigma`
-}
--is_valid_delta :: (Eq state) => Set state -> Set Char -> Trans state -> Bool
--is_valid_delta states sigma delta =
--  and [ delta (s, c) /= Nothing | s <- Set.toList states, c <- Set.toList sigma ]

{-
Check if a given DFA is valid
-}
--dfa_is_valid :: (Eq state, Ord state) => DFA state -> Bool
--dfa_is_valid dfa@(states, sigma, delta, qinit, qF) =
--  is_valid_delta states sigma delta &&
--  Set.member qinit states &&
--  Set.isSubsetOf qF states


{-
run(q, epsilon) = q,
run(q, a w)     = run(delta(q, a), w).
-}
run :: DFA state -> state -> String -> state
run dfa@(states, sigma, delta, _, _) q "" = q
run dfa@(states, sigma, delta, _, _) q (a:w) = run dfa (delta (q, a)) w


{-
recognize q w = true   iff    w \in L(M)
-}
recognize :: Ord state => DFA state -> String -> Bool
recognize dfa@(_, _, _, qinit, qF) w = Set.member (run dfa qinit w) qF


{-
(q, w) \in accessible p    iff    q_init -- w --> q
-}
accessible :: forall state. Ord state => DFA state -> Set (state, String)
accessible dfa@(states, sigma, delta, qinit, qf) = iter (Set.fromList [(qinit, "")])
  where
    expand :: Char -> Set (state, String) -> Set (state, String)
    expand c acc = Set.fromList [ (delta (p, c), w ++ [c]) | (p, w) <- Set.toList acc ]
    
    iter :: Set (state, String) -> Set (state, String)
    iter acc =
      let expanded :: Set (state, String) = Set.unions [ expand c acc | c <- Set.toList sigma ] in
      let cur = Set.union acc expanded in
      if Set.isProperSubsetOf (Set.map fst acc) (Set.map fst cur)
      then iter cur
      else cur

{-
L(M) = \emptyset -> is_empty M = Nothing
L(M) <> \emptyset -> is_empty M = Just w for some w s.t. w in L(M)
-}
is_empty :: forall state. Ord state => DFA state -> Maybe String
is_empty dfa@(states, sigma, trans, qinit, qf) =
  let acc = accessible dfa in
  let coacc = [ (q, w) | (q, w) <- Set.toList acc, Set.member q qf == True ] in
  case coacc of
    [] -> Nothing
    (q, w) : _ -> Just w

set_prod :: (Ord a, Ord b) => Set a -> Set b -> Set (a, b)
set_prod set1 set2 =
  Set.fromList [ (x, y) | x <- Set.toList set1, y <- Set.toList set2 ]

{-
For two DFAs A and B,
(dfa_intersect A B) is a dfa such that L(A) \cap L(B) = L(dfa_intersect A B).
-}
dfa_intersect :: forall state1 state2. (Ord state1, Ord state2) => DFA state1 -> DFA state2 -> DFA (state1, state2)
dfa_intersect
  dfa1@(states1, sigma1, trans1, qinit1, qf1)
  dfa2@(states2, sigma2, trans2, qinit2, qf2)
  | sigma1 == sigma2 = (paired_states, sigma1, new_trans, new_init, new_acceptings)
  | sigma1 /= sigma2 = error "the input alphabets of the given DFAs are different."
  where
    paired_states :: Set (state1, state2)
    paired_states = set_prod states1 states2

    new_init :: (state1, state2)
    new_init = (qinit1, qinit2)

    new_acceptings :: Set (state1, state2)
    new_acceptings = set_prod qf1 qf2

    new_trans :: Trans (state1, state2)
    new_trans ((p, q), c) = (trans1 (p, c), trans2 (q, c))

{-
For a DFA A, complement A is a DFA such that L(complement A) = Sigma^* \setminus L(A).
-}
dfa_complement :: Ord state => DFA state -> DFA state
dfa_complement dfa@(states, sigma, trans, qinit, qF) =
  (states, sigma, trans, qinit, Set.difference states qF)


{-
dfa_subtract A B = Just w ---> w \in L(A) \setminus L(B)
dfa_subtract A B = Nothing --> L(A) \setminus L(B) = \emptyset
-}
dfa_subtract :: (Ord state1, Ord state2) => DFA state1 -> DFA state2 -> Maybe String
dfa_subtract dfa1 dfa2 = is_empty $ dfa_intersect dfa1 (dfa_complement dfa2)


dfa_eq' :: (Ord state1, Ord state2) => DFA state1 -> DFA state2 -> Bool
dfa_eq' dfa1 dfa2 =
  (dfa_subtract dfa1 dfa2 == Nothing) && (dfa_subtract dfa2 dfa1 == Nothing)

symmetric_diff :: (Ord state1, Ord state2) => DFA state1 -> DFA state2 -> Maybe String
symmetric_diff dfa1 dfa2 =
  case dfa_subtract dfa1 dfa2 of
    Nothing -> dfa_subtract dfa2 dfa1
    Just w  -> Just w
  

{-
Sample1
-}
three_states :: Set Integer
three_states = Set.fromList [1, 2, 3]

two_characters :: Set Char
two_characters = Set.fromList ['a', 'b']

trans_sample1 (1, 'a') = 1
trans_sample1 (1, 'b') = 2
trans_sample1 (2, 'a') = 3
trans_sample1 (2, 'b') = 2
trans_sample1 (3, 'a') = 3
trans_sample1 (3, 'b') = 3

dfa_sample1 :: DFA Integer
dfa_sample1 = (three_states, two_characters, trans_sample1, 1, Set.fromList [1, 2])


{-
Sample2
-}
-- two_states :: Set Integer
two_states = Set.fromList [1, 2]

trans_sample2 (1, 'a') = 1
trans_sample2 (1, 'b') = 2
trans_sample2 (2, 'a') = 2
trans_sample2 (2, 'b') = 1

dfa_sample2 :: DFA Int
dfa_sample2 = (two_states, two_characters, trans_sample2, 1, Set.fromList [1, 2])


-- make_dfa [ (0, 'a', 1) ]

make_dfa :: forall state. (Show state, Ord state) => [(state, Char, state)] -> state -> [state] -> DFA state
make_dfa table qinit qF =
  let dom = [ p | (p, c, q) <- table ] in
  let cod = [ q | (p, c, q) <- table ] in
  let sigma = [ c | (p, c, q) <- table ] in
  (Set.fromList $ dom ++ cod, Set.fromList sigma, delta, qinit, Set.fromList qF)
  where
    delta :: (state, Char) -> state
    delta (p, c) =
      case [ q | (p', c', q) <- table, p' == p, c' == c ] of
        [] -> error $ "δ(" ++ (show p) ++ ", " ++ (show c) ++ ") is not defined."
        [q] -> q
        qs -> error $ "δ(" ++ show p ++ ", " ++ show c ++ ") = " ++ show qs ++ "is nondeterministic."

(→) (a, b) c = (a, b, c)
 
dfa_sample2' = make_dfa [ (1, 'a') → 1, (1, 'b') → 2, (2, 'a') → 2, (2, 'b') → 1 ] 1 [1, 2]


