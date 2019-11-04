{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ViewPatterns #-}

module Utils
    ( dfold'
    , dtfold'
    , dfoldDF'
    , dtfoldDF'
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
import           Clash.Signal.Internal          ( Signal((:-)) )

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

dfoldDF'
    :: forall dom p k a
     . (KnownDomain dom, KnownNat k, NFDataX a)
    => Proxy (p :: TyFun Nat Type -> Type)
    -> (  forall l
        . (KnownNat l, l <= k - 1)
       => SNat l
       -> DataFlow dom Bool Bool (a, p @@ l) (p @@ (l + 1))
       )
    -> p @@ 0
    -> DataFlow dom (Vec k Bool) Bool (Vec k a) (p @@ k)
dfoldDF' Proxy f z = DF go
  where
    go
        :: forall n
         . (KnownNat n, n <= k)
        => Signal dom (Vec n a)
        -> Signal dom (Vec n Bool)
        -> Signal dom Bool
        -> ( Signal dom (p @@ n)
           , Signal dom Bool
           , Signal dom (Vec n Bool)
           )
    go (Nil :- _) (Nil :- _) r = (pure z, pure True, pure Nil)
    go ds@((_ `Cons` _) :- _) vs@((_ `Cons` _) :- _) r =
        case leTrans @(n - 1) @n @k of
            Sub Dict -> (d, v, Cons <$> rsh <*> rst)
      where
        (d', v', rst                  ) = go (tail <$> ds) (tail <$> vs) r'
        (d , v , unbundle -> (rsh, r')) = df (lockStep `seqDF` f SNat)
                                             (bundle (head <$> ds, d'))
                                             (bundle (head <$> vs, v'))
                                             r
{-# NOINLINE dfoldDF' #-}

dtfoldDF'
    :: forall dom p k a
     . (KnownDomain dom, KnownNat k, NFDataX a)
    => Proxy (p :: TyFun Nat Type -> Type)
    -> DataFlow dom Bool Bool a (p @@ 0)
    -> (  forall l
        . (KnownNat l, l <= k - 1)
       => SNat l
       -> DataFlow dom Bool Bool (p @@ l, p @@ l) (p @@ (l + 1))
       )
    -> DataFlow dom (Vec (2 ^ k) Bool) Bool (Vec (2 ^ k) a) (p @@ k)
dtfoldDF' Proxy f g = DF go
  where
    go
        :: forall n
         . (KnownNat n, n <= k)
        => Signal dom (Vec (2 ^ n) a)
        -> Signal dom (Vec (2 ^ n) Bool)
        -> Signal dom Bool
        -> ( Signal dom (p @@ n)
           , Signal dom Bool
           , Signal dom (Vec (2 ^ n) Bool)
           )
    go d@((_ `Cons` Nil) :- _) v@((_ `Cons` Nil) :- _) r =
        (d', v', repeat <$> r')
        where (d', v', r') = df f (head <$> d) (head <$> v) r
    go ds@((_ `Cons` _ `Cons` _) :- _) vs@((_ `Cons` _ `Cons` _) :- _) r =
        case leTrans @(n - 1) @n @(k - 1) *** leTrans @(n - 1) @n @k of
            Sub Dict -> (d, v, rs)
              where
                (unbundle -> (dsl, dsr))       = splitAtI <$> ds
                (unbundle -> (vsl, vsr))       = splitAtI <$> vs
                rs                             = (++) <$> rsl <*> rsr

                (dl, vl, rsl                 ) = go dsl vsl rl
                (dr, vr, rsr                 ) = go dsr vsr rr

                (d , v , unbundle -> (rl, rr)) = df (lockStep `seqDF` g SNat)
                                                    (bundle (dl, dr))
                                                    (bundle (vl, vr))
                                                    r
{-# NOINLINE dtfoldDF' #-}
