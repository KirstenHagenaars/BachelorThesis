module Blank where

import Prelude
import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.ProofCombinators
import Data.List


{-@ type Ordlist a = [a]<{\x v -> x <= v}> @-}

{-@ app_qs :: piv:a
-> Ordlist {v:a | v <=  piv} 
-> Ordlist {v:a | v > piv} 
-> Ordlist a 
 @-}
app_qs pivot [] ys  = pivot : ys
app_qs pivot (x:xs) ys  = x : app_qs pivot xs ys


{-@ quicksort :: Ord a => l:[a] -> Ordlist a / [len l] @-}
quicksort  [] = []
quicksort (x:xs) = app_qs x (quicksort ([y | y <- xs, y <= x ])) (quicksort ([y | y <- xs, y > x ]))




{-@ merge :: Ord a => l:Ordlist a -> l':Ordlist a -> Ordlist a / [len l + len l'] @-}
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = if x <= y then x : merge xs (y:ys) else y : merge (x:xs) ys


{-@ mergesort :: Ord a => l:[a] -> Ordlist a / [len l] @-}
mergesort [] = []
mergesort [x] = [x]
mergesort l = merge (mergesort first) (mergesort second)
    where first = take half l
          second = drop half l
          half = length l `div` 2












