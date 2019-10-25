{-# LANGUAGE Rank2Types #-}

module Utils
    ( dfold'
    )
where

import           Clash.Prelude
import           Data.Proxy
import           Data.Kind
import           Data.Singletons.Prelude        ( TyFun
                                                , Apply
                                                , type (@@)
                                                )

dfold'
    :: forall p k a
     . (KnownNat k)
    => Proxy (p :: TyFun Nat Type -> Type)
    -> (  forall l
        . (KnownNat l, l <= k - 1)
       => SNat l
       -> a
       -> p @@ l
       -> p @@ (l + 1)
       )
    -> (p @@ 0)
    -> Vec k a
    -> (p @@ k)
dfold' Proxy f z = go
  where
    go :: (KnownNat n, n <= k) => Vec n a -> p @@ n
    go Nil           = z
    go (y `Cons` ys) = f (lengthS ys) y (go ys)
{-# NOINLINE dfold' #-}
