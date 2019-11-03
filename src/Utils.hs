{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Utils
    ( dfold'
    , dtfold'
    )
where

import           Clash.Prelude
import           Data.Proxy
import           Data.Kind
import           Data.Singletons.Prelude        ( TyFun
                                                , Apply
                                                , type (@@)
                                                )
import           Data.Constraint
import           Data.Constraint.Nat

import qualified Data.List                     as L

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
    go :: forall n . (KnownNat n, n <= k) => Vec n a -> p @@ n
    go Nil           = z
    go (y `Cons` ys) = f SNat y (go ys)
{-# NOINLINE dfold' #-}

dtfold'
    :: forall p k a
     . (KnownNat k)
    => Proxy (p :: TyFun Nat Type -> Type)
    -> (a -> p @@ 0)
    -> (  forall l
        . (KnownNat l, l <= k - 1)
       => SNat l
       -> p @@ l
       -> p @@ l
       -> p @@ (l + 1)
       )
    -> Vec (2 ^ k) a
    -> (p @@ k)
dtfold' Proxy f g = go
  where
    go :: forall n . (KnownNat n, n <= k) => Vec (2 ^ n) a -> p @@ n
    go (x `Cons` Nil) = f x
    go xs@(_ `Cons` _ `Cons` _) =
        case leTrans @(n - 1) @n @(k - 1) *** leTrans @(n - 1) @n @k of
            Sub Dict -> g SNat (go xsl) (go xsr)
                where (xsl, xsr) = splitAtI xs
{-# NOINLINE dtfold' #-}

foldDF
    :: forall dom k a
     . (KnownNat k)
    => (forall a . a -> a -> a)
    -> DataFlow dom (Vec (2 ^ k) Bool) Bool (Vec (2 ^ k) a) a
foldDF f = DF go
  where
    go
        :: forall n
         . (KnownNat n)
        => Signal dom (Vec n a)
        -> Signal dom (Vec n Bool)
        -> Signal dom Bool
        -> (Signal dom a, Signal dom Bool, Signal dom (Vec n Bool))
    go ds vs r = (d, v, rs)
      where
        (dsl, dsr)     = unbundle $ splitAtI <$> ds
        (vsl, vsr)     = unbundle $ splitAtI <$> vs
        rs             = (++) <$> rsl <*> rsr

        (dl, vl, rsl ) = go dsl vsl rl
        (dr, vr, rsr ) = go dsr vsr rr

        (d , v , rlrr) = df (lockStep `seqDF` pureDF (uncurry f))
                            (bundle (dl, dr))
                            (bundle (vl, vr))
                            r
        (rl, rr) = unbundle rlrr
