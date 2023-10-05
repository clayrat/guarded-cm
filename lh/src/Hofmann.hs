{-# LANGUAGE GADTs #-}

module Hofmann where

import Later

data Tree a = Leaf a | Node a (Tree a) (Tree a)

data Rou a where 
    OverA :: Rou a 
    NextR :: ((Later (Rou a) -> Later (List a)) -> List a) -> Rou a 

unfold :: Rou a -> (Later (Rou a) -> Later (List a)) -> Later (List a)
unfold OverA f = f (L OverA)
unfold (NextR g) f = L (g f) 

{-@ br :: t:Tree a -> Rou a -> Rou a / [treeSize t] @-}
br :: Tree a -> Rou a -> Rou a
br (Leaf a) r = NextR (\f -> a `Cons` unfold r f) 
br (Node a l r) r' = NextR (\f -> a `Cons` unfold r' (\d -> f (mapL (br l . (br r)) d)))

ex :: Rou a -> List a
ex = fix (\f x -> case x of 
                    OverA -> Nil
                    NextR g -> g (appL f))


bfs :: Tree a -> List a
bfs t = ex (br t OverA)


{-@ measure treeSize @-}
{-@ treeSize :: Tree a -> Nat @-}
treeSize :: Tree a -> Int
treeSize (Leaf _)     = 0
treeSize (Node _ l r) = 1 + treeSize l + treeSize r


