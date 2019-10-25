{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ExplicitNamespaces #-}

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
import           Data.Constraint
import           Data.Constraint.Nat

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
    go (y `Cons` ys) = f (SNat @(n - 1)) y (go ys)
{-# NOINLINE dfold' #-}

dtfold'
    :: forall p k a
     . KnownNat k
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
dtfold' _ f g = go
  where
    go :: forall n . (KnownNat n, n <= k) => Vec (2 ^ n) a -> p @@ n
    go (x `Cons` Nil) = f x
    go xs@(_ `Cons` (_ `Cons` _)) =
        case leTrans @(n - 1) @n @(k - 1) *** leTrans @(n - 1) @n @k of
            Sub Dict -> g (SNat @(n - 1)) (go xsl) (go xsr)
                where (xsl, xsr) = splitAtI xs
{-# NOINLINE dtfold' #-}

dtfold''
    :: forall p k a
     . (KnownNat k)
    => Proxy (p :: TyFun Nat Type -> Type)
    -> (a -> p @@ 1)
    -> (  forall l r
        . SNat l
       -> SNat r
       -> p @@ l
       -> p @@ r
       -> p @@ (l + r)
       )
    -> Vec k a
    -> p @@ k
dtfold'' _ f g = go
  where
    go :: forall n . (KnownNat n, n <= k) => Vec n a -> p @@ n
    go (   x          `Cons` Nil) = f x
    go xs@(_ `Cons` _ `Cons` _  ) = case divMonotone2 @n @1 @2 of
        Sub Dict -> case leTrans @(Div n 2) @n @k *** leTrans @(n - Div n 2) @n @k of
            Sub Dict -> g (SNat @(Div n 2))
                          (SNat @(n - Div n 2))
                          (go xsl)
                          (go xsr)
                where (xsl, xsr) = splitAtI xs
{-# NOINLINE dtfold'' #-}
