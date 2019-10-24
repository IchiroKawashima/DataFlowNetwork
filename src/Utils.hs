{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}

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

data Shifter (k :: Nat) (f :: TyFun Nat Type) :: Type
type instance Apply (Shifter k) l = (BitVector l, BitVector (2 ^ (k - l)))

shifter :: forall k . (KnownNat k, 1 <= k) => BitVector (2 ^ k) -> BitVector k
shifter x = fst $ dfold' (Proxy @(Shifter k)) sft (def, x) $ repeat ()
  where
    sft
        :: forall l
         . (KnownNat l, l <= k - 1)
        => SNat l
        -> ()
        -> Shifter k @@ l
        -> Shifter k @@ (l + 1)
    sft SNat () (shift, remnant) =
        case plusMonotone1 @l @(k - 1) @1 *** plusMinusInverse3 @1 @k of
            Sub Dict
                | bitToBool $ reduceOr lowerBits -> (shift ++# 0, lowerBits)
                | otherwise                      -> (shift ++# 1, higherBits)
                where (higherBits, lowerBits) = split remnant

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
