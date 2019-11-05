{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ViewPatterns #-}

module Utils
    ( dfold'
    , dtfold'
    , foldrDF
    , foldDF
    , unfoldDF
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
dtfold' Proxy f0 fn = go
  where
    go :: forall n . (KnownNat n, n <= k) => Vec (2 ^ n) a -> p @@ n
    go (x `Cons` Nil) = f0 x
    go xs@(_ `Cons` _ `Cons` _) =
        case leTrans @(n - 1) @n @(k - 1) *** leTrans @(n - 1) @n @k of
            Sub Dict -> fn SNat (go xsl) (go xsr)
                where (xsl, xsr) = splitAtI xs
{-# NOINLINE dtfold' #-}

foldrDF
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
foldrDF Proxy f z = DF go
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
            Sub Dict -> (d, v, Cons <$> rsHead <*> rsTail)
      where
        (d', v', rsTail                  ) = go (tail <$> ds) (tail <$> vs) r'
        (d , v , unbundle -> (rsHead, r')) = df (lockStep `seqDF` f SNat)
                                                (bundle (head <$> ds, d'))
                                                (bundle (head <$> vs, v'))
                                                r
{-# NOINLINE foldrDF #-}

foldDF
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
foldDF Proxy f0 fn = DF $ go SNat
  where
    go
        :: forall n
         . (KnownNat n, n <= k)
        => SNat n
        -> Signal dom (Vec (2 ^ n) a)
        -> Signal dom (Vec (2 ^ n) Bool)
        -> Signal dom Bool
        -> ( Signal dom (p @@ n)
           , Signal dom Bool
           , Signal dom (Vec (2 ^ n) Bool)
           )
    go SNat d@((_ `Cons` Nil) :- _) v@((_ `Cons` Nil) :- _) r =
        (d', v', repeat <$> r')
        where (d', v', r') = df f0 (head <$> d) (head <$> v) r
    go SNat ds@((_ `Cons` _ `Cons` _) :- _) vs@((_ `Cons` _ `Cons` _) :- _) r =
        case leTrans @(n - 1) @n @(k - 1) *** leTrans @(n - 1) @n @k of
            Sub Dict -> (d, v, rs)
              where
                (unbundle -> (dsl, dsr))       = splitAtI <$> ds
                (unbundle -> (vsl, vsr))       = splitAtI <$> vs
                rs                             = (++) <$> rsl <*> rsr

                (dl, vl, rsl                 ) = go (SNat @(n - 1)) dsl vsl rl
                (dr, vr, rsr                 ) = go (SNat @(n - 1)) dsr vsr rr

                (d , v , unbundle -> (rl, rr)) = df
                    (lockStep `seqDF` fn SNat)
                    (bundle (dl, dr))
                    (bundle (vl, vr))
                    r
{-# NOINLINE foldDF #-}

unfoldDF
    :: forall dom p k a
     . (KnownDomain dom, KnownNat k, NFDataX a)
    => Proxy (p :: TyFun Nat Type -> Type)
    -> (  forall l
        . (KnownNat l, l <= k - 1)
       => SNat l
       -> DataFlow
              dom
              Bool
              Bool
              (p @@ l)
              (p @@ (l + 1), p @@ (l + 1))
       )
    -> DataFlow dom Bool Bool (p @@ k) a
    -> DataFlow dom Bool (Vec (2 ^ k) Bool) (p @@ 0) (Vec (2 ^ k) a)
unfoldDF Proxy fn fk = DF $ go SNat
  where
    go
        :: forall n
         . (KnownNat n, n <= k)
        => SNat n
        -> Signal dom (p @@ (k - n))
        -> Signal dom Bool
        -> Signal dom (Vec (2 ^ n) Bool)
        -> ( Signal dom (Vec (2 ^ n) a)
           , Signal dom (Vec (2 ^ n) Bool)
           , Signal dom Bool
           )
    go SNat d v r@((_ `Cons` Nil) :- _) = (repeat <$> d', repeat <$> v', r')
        where (d', v', r') = df fk d v (head <$> r)
    go SNat d v rs@((_ `Cons` _ `Cons` _) :- _) =
        case leTrans @(n - 1) @n @k of
            Sub Dict -> (ds, vs, r)
              where
                (unbundle -> (dl, dr), unbundle -> (vl, vr), r) =
                    df (fn SNat `seqDF` stepLock) d v (bundle (rl, rr))

                (dsl, vsl, rl)           = go (SNat @(n - 1)) dl vl rsl
                (dsr, vsr, rr)           = go (SNat @(n - 1)) dr vr rsr

                ds                       = (++) <$> dsl <*> dsr
                vs                       = (++) <$> vsl <*> vsr
                (unbundle -> (rsl, rsr)) = splitAtI <$> rs
{-# NOINLINE unfoldDF #-}
