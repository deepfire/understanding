{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnicodeSyntax #-}

module Understanding.Polymorphism where

-- * Machinery
class Slicy a where
    slicyInt  ∷ a → Maybe Int
    slicyBool ∷ a → Maybe Bool

data WSlicy where
    WSlicy ∷ ∀ a.Slicy a ⇒ a → WSlicy

data Slice a where
    SInt  ∷ Int  → Slice Int
    SBool ∷ Bool → Slice Bool

data WSlice where
    WSlice ∷ ∀ a.Slice a → WSlice

-- * Exhibit I:  Projection
sliceInt ∷ Slice a → Maybe Int
sliceInt (SInt i)  = Just i
sliceInt (SBool _) = Nothing

instance Slicy Int where
    slicyInt    = Just
    slicyBool _ = Nothing
instance Slicy Bool where
    slicyInt  _ = Nothing
    slicyBool   = Just

-- * Exhibit II:  Heterogeneity

-- ** Processing heterogenae
add_slices ∷ [WSlice] → Int
add_slices ss = sum [ i
                    | WSlice (SInt i) ← ss ]

add_slicys ∷ [WSlicy] → Int
add_slicys ss = sum [ case slicyInt x of
                        Nothing → 0
                        Just i  → i
                    | WSlicy x ← ss ]

-- ** Heterogenous storage
slices ∷ [WSlice]
slices = [ WSlice (SInt 0)
         , WSlice (SBool False) ]

slicys ∷ [WSlicy]
slicys = [ WSlicy (0 ∷ Int)
         , WSlicy False ]
