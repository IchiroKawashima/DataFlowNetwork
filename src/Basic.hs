{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExplicitNamespaces #-}

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

import qualified Data.List                     as L

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

data Macc (int :: Nat) (frac :: Nat) (f :: TyFun Nat Type) :: Type
type instance Apply (Macc int frac) l = SFixed (l + int + int) frac

macc
    :: (KnownNat int, KnownNat frac, KnownNat k)
    => Vec (2 ^ k) (SFixed int frac)
    -> Vec (2 ^ k) (SFixed int frac)
    -> SFixed (k + int + int) frac
macc = ((.) . (.))
    (dtfold' (Proxy :: Proxy (Macc int frac))
             (resizeF . uncurry mul)
             (const add)
    )
    zip

-- macc'
--     :: (KnownNat int, KnownNat frac, KnownNat k)
--     => Vec (2 ^ k) (DataFlow dom Bool Bool (SFixed int frac) ())
--     -> Vec (2 ^ k) (DataFlow dom Bool Bool (SFixed int frac))
--     -> DataFlow dom Bool Bool (SFixed (k + int + int) frac)
-- macc' xs ys = dtfold' (Proxy :: Proxy (Macc int frac)) (pureDF (resizeF . uncurry mul)) (\SNat -> lockStep `seqDF` pureDF add) $ zip xs ys

-- macc' xs ys = fold (undefined ) $ zipWith (pureDF *) xs ys

-- data Macc' (a :: Type) (k :: Nat) (f :: TyFun Nat Type) :: Type
-- type instance Apply (Macc' a k) l = Vec (k - l) a

-- macc' = dtfold' Proxy f g
--   where
--     f = idDF
--     g = pureDF const

