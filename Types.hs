{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE DataKinds, GADTs, KindSignatures, TypeFamilies, TypeInType, TypeOperators, UnicodeSyntax, StandaloneDeriving #-}

module Understanding.Types where

import GHC.TypeLits
import GHC.Types (Type)

data T p (size ∷ Nat) where
  TZ ∷ T p 0
  TS ∷ (Show p, (m + 1) ~ n) ⇒
    { payload ∷ p
    , next    ∷ T a m } → T a n
deriving instance Show p ⇒ Show (T p s)

class MeasuredMonoid a where
  mmempty  ∷ a 0
  mmappend ∷ a n → a m → a (n + m)

instance MeasuredMonoid (T p) where
  mmempty    = TZ
  mmappend     TZ         TZ      = TZ
  mmappend     TZ      t@(TS _ _) = t
  mmappend  t@(TS _ _)    TZ      = t
  mmappend tl@(TS pl nl)  tr      = TS pl $ mmappend nl tr

(<>) ∷ MeasuredMonoid a ⇒ a n → a m → a (m + n)
(<>) = mmappend

-- * Success, due to use of OPTIONS_GHC -fplugin GHC.TypeLits.Normalise
-- > :t TZ <> TZ
-- TZ <> TZ :: T p 0
-- > TS 1 TZ <> TS 0 TZ
-- TS {payload = 1, next = TS {payload = 0, next = TZ}}
-- > :t TS 1 TZ <> TS 0 TZ
-- TS 1 TZ <> TS 0 TZ :: T a 2

-- * Failure due to lack of inductive structure of GHC.TypeLits.Nat
--
-- error:
--     • Could not deduce: CmpNat ((m1 + m) + 1) (n + m) ~ 'EQ
--         arising from a use of ‘TS’
--       from the context: (Show p1, CmpNat (m1 + 1) n ~ 'EQ)
--         bound by a pattern with constructor:
--                    TS :: forall k (a :: k) (n :: Nat) p (m :: Nat).
--                          (Show p, CmpNat (m + 1) n ~ 'EQ) =>
--                          p -> T a m -> T a n,
--                  in an equation for ‘mmappend’
--         at /home/deepfire/src/haskell-understanding/Types.hs:24:16-23
--     • In the expression: TS pl
--       In the expression: TS pl $ mmappend nl tr
--       In an equation for ‘mmappend’:
--           mmappend tl@(TS pl nl) tr = TS pl $ mmappend nl tr
--     • Relevant bindings include
--         tr :: T p m
--           (bound at /home/deepfire/src/haskell-understanding/Types.hs:24:27)
--         nl :: T p m1
--           (bound at /home/deepfire/src/haskell-understanding/Types.hs:24:22)
--         tl :: T p n
--           (bound at /home/deepfire/src/haskell-understanding/Types.hs:24:12)
--         mmappend :: T p n -> T p m -> T p (n + m)
--           (bound at /home/deepfire/src/haskell-understanding/Types.hs:21:3)

-- instance Monoid (T d p) where
--   mempty    = TZ
--   mappend     TZ         TZ      = TZ
--   mappend     TZ      t@(TS _ _) = t
--   mappend  t@(TS _ _)    TZ      = t
--   mappend tl@(TS pl nl)  tr      = TS pl $ mappend nl tr

-- * Failure due to forced type equality of regular monoid operation arguments.
--
-- error:
--     • Couldn't match type ‘d’ with ‘0’
--       ‘d’ is a rigid type variable bound by
--         the instance declaration
--         at /home/deepfire/src/haskell-understanding/Types.hs:13:10
--       Expected type: T d p
--         Actual type: T 0 p
--     • In the expression: TZ
--       In an equation for ‘mempty’: mempty = TZ
--       In the instance declaration for ‘Monoid (T d p)’
--     • Relevant bindings include
--         mempty :: T d p
--           (bound at /home/deepfire/src/haskell-understanding/Types.hs:14:3)
