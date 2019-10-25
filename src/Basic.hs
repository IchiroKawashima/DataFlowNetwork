{-# LANGUAGE UndecidableInstances #-}

module Basic
    ( encoder
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

import           Utils

data Encoder (k :: Nat) (f :: TyFun Nat Type) :: Type
type instance Apply (Encoder k) l = (BitVector l, BitVector (2 ^ (k - l)))

encoder :: forall k . (KnownNat k, 1 <= k) => BitVector (2 ^ k) -> BitVector k
encoder x = fst $ dfold' (Proxy @(Encoder k)) enc (def, x) $ repeat ()
  where
    enc
        :: forall l
         . (KnownNat l, l <= k - 1)
        => SNat l
        -> ()
        -> Encoder k @@ l
        -> Encoder k @@ (l + 1)
    enc SNat () (shift, remnant) =
        case plusMonotone1 @l @(k - 1) @1 *** plusMinusInverse3 @1 @k of
            Sub Dict
                | bitToBool $ reduceOr lowerBits -> (shift ++# 0, lowerBits)
                | otherwise                      -> (shift ++# 1, higherBits)
                where (higherBits, lowerBits) = split remnant
