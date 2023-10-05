{-# LANGUAGE GADTs #-}

module Later where 

-------------------------------------------------------------------------------
-- | Later Library ------------------------------------------------------------
-------------------------------------------------------------------------------

mapL :: (a -> b) -> Later a -> Later b
mapL f l = appL (L f) l

appL :: Later (a -> b) -> Later a -> Later b
appL (L f) (L a) = L (f a)

{-@ lazy fix @-}
fix :: (Later a -> a) -> a
fix f = f (L (fix f))


data Later a = L a    

data List a where
    Nil  :: List a
    Cons :: a -> Later (List a) -> List a


