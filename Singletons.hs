--
-- Full dependent types in Haskell
-- ===============================
--
-- So you still think that Haskell doesn't have dependent types?  This
-- little demonstration of the singletons library will change your mind.
-- You need at least GHC 7.8.  Ready?
--
-- Our goal is to write a version of 'filter' that is less
-- boolean-blind.  Rather than using a boolean predicate we will base
-- our filtering on a formal, decidable property.  The resulting list
-- will not only contain the elements that have the property, but also
-- the corresponding proofs for each element.  The Agda type of this
-- function would be:
--
--     filterP :
--         ∀ {ℓ p} {A : Set ℓ} {P : A → Set p} →
--         Decidable P → List A → List (Σ A P)
--
-- Notice that this function requires three features that we don't
-- regularly have in Haskell:
--
--   * the dependent function arrow (aka dependent products),
--   * quantification over dependent types,
--   * first class existentials (aka dependent sums).
--
-- First let's get the extensions out of the way.  They are mostly the
-- usual type-level computation stuff, but two relatively new extensions
-- are extremely valuable for writing proofs:  LambdaCase (≥ 7.6) and
-- EmptyCase (≥ 7.8).
--
-- As always TemplateHaskell needs justification:  The singletons
-- library generates singleton types and type functions for you.  We
-- don't use it to a large extent here, but it still saves a few
-- keystrokes for what is really completely uninteresting boilerplate
-- you don't want to write by hand.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}


-- Dependent types are best served with a selection of non-totality
-- errors.  The easiest way to get them is to just enable warnings and
-- turn them into errors.  Unfortunately that doesn't turn Haskell into
-- a total language, but at least some stupid mistakes are caught.

--{-# OPTIONS_GHC -Wall -Werror #-}

module Main where

import Data.Singletons.Decide
import Data.Singletons.TH


-- So our goal first requires properties along with decision functions.
-- Most of what we need for decidable properties is defined by the
-- singletons library, except the type of unary decision functions.
-- Here it is:

type Decidable p = forall n. Sing n -> Decision (p n)


-- No demonstration of dependent types is complete without natural
-- numbers. =)
--
-- This is the only place where we use TemplateHaskell.  It generates
-- the corresponding singleton type and some lifting/lowering
-- boilerplate that we'll need later.

singletons [d|
    data Nat = Z | S Nat  deriving (Show)
    |]


-- The following is one of the properties we want to filter for.  This
-- type is only inhabitated for even arguments:

data Even :: Nat -> * where
    Even0 :: Even Z
    EvenS :: Even n -> Even (S (S n))


-- And whether a natural number is even is of course decidable, so the
-- following function decides it:

isEven :: Decidable Even
isEven SZ = Proved Even0
isEven (SS SZ) = Disproved (\case {})
isEven (SS (SS n)) =
    case isEven n of
      Proved p    -> Proved (EvenS p)
      Disproved _ -> Disproved (\case {})


-- However, beware of a subtlety here.  Haskell does not distinguish
-- between induction and coinduction.  In particular evenness is
-- *undecidable* for a coinductively defined Nat type (let's call it
-- Conat), so in a proper proof assistant like Agda the compiler would
-- accept 'isEven' for Nat, but reject it for Conat.  Totality is so
-- subtle and so easy to get wrong that you should probably prototype
-- your code in a real proof assistant first (note: termination checking
-- is *disabled* by default in Idris!).
--
-- So far we have seen nothing special.  This is all the usual stuff
-- from what is called *lightweight dependent types*.  The dependent
-- function arrow (Pi types) also comes pretty much for free when you
-- use the singletons library.
--
-- For this example we need more than that though.  We need dependent
-- type *polymorphism* (quantification over *dependent* types), and we
-- need first class existentials, which you may know better under the
-- name *dependent sums* (Sigma types).  With those you can actually
-- prove that Haskell is as expressive as a dependently typed language.
-- See the singletons paper for details.
--
-- Here it is, dependent sums:

data Exists :: KProxy a -> (a -> *) -> * where
    Pair :: Sing (x :: a) -> b x -> Exists ('KProxy :: KProxy a) b


-- Too simple to be true?  Nope, this is full dependent sums. =)
--
-- The KProxy kind is just a promoted version of Proxy.  While Proxy is
-- used to communicate types, KProxy is used to communicate kinds.  This
-- wrapping is necessary, because in Haskell types and kinds live on
-- separate levels.
--
-- The 'Exists' type already shows how to get polymorphic dependent
-- types.  The only missing ingredient is a bridge between the type and
-- kind levels without giving up polymorphism.  That's exactly the
-- purpose of the 'SingKind' class.  We again need some proxying for
-- communication.  To make this a bit more convenient, singletons
-- provides the 'KindOf' and 'Demote' aliases.  All they do is to hide
-- 'KProxy'.  One little awkwardness is that they require a throwaway
-- type variable.  I use 'z' here:

filterP ::
    forall (a :: *) (p :: sa -> *) z.
    (SingKind (KindOf (z :: sa)), Demote (z :: sa) ~ a)
    => Decidable p
    -> [a]
    -> [Exists (KindOf (z :: sa)) p]


-- How to read this type signature?  First ignore the context.  It's
-- just for bookkeeping:
--
--     filterP ::
--         forall (a :: *) (p :: sa -> *) z.
--         Decidable p
--         -> [a]
--         -> [Exists (KindOf (z :: sa)) p]
--
-- Both 'KindOf (z :: sa)' (type level) and 'sa' (kind level) represent
-- the type 'a'.  If you imagine a collapse between the type and kind
-- levels (as in a dependently typed language), then the type signature
-- becomes:
--
--     filterP ::
--         forall (a :: *) (p :: a -> *).
--         Decidable p -> [a] -> [Exists a p]
--
-- Except the missing universe levels this looks pretty much like the
-- Agda version!  Here's the Agda version without universe polymorphism,
-- just for comparison (with the optional "∀" just written for clarity):
--
--     filterP :
--         ∀ {A : Set} {P : A → Set} →
--         Decidable P → List A → List (Σ A P)
--
-- What does the implementation look like?  We need an explicit bridge
-- between the value and type levels and also a way to introduce the
-- existential from the value level.  That's the purpose of
-- 'withSomeSing'.  Again this is just bookkeeping.  All it does is to
-- promote regular values to singletons.  Other than that the
-- implementation is pretty straightforward:

filterP _ [] = []
filterP dec (x:xs) =
    withSomeSing x $ \sx ->
        case dec sx of
          Proved p    -> Pair sx p : filterP dec xs
          Disproved _ -> filterP dec xs


-- Here is an example using the 'Even' property.  Dependent types are
-- not just great for correctness, but also for documentation.  Notice
-- how the application to 'isEven' refines the type.  Now just from the
-- type signature you can immediately see that this function takes a
-- list of natural numbers and returns a list of even numbers, including
-- a proof of their evenness:

filterEven :: [Nat] -> [Exists (KindOf (x :: Nat)) Even]
filterEven = filterP isEven


-- Do you "love" propositional equality as much as I do?  Being equal to
-- a certain element by prop. eq. is of course also a property, but it's
-- not decidable in general.  That's the purpose of singletons'
-- awkwardly named 'SDecide' class.  Prop. eq. itself is encoded in
-- singletons' predefined (:~:) type.  It has the usual definition.

filterElem ::
    (SDecide (KindOf (z :: sa)), SingKind (KindOf (z :: sa)), Demote (z :: sa) ~ a)
    => Sing x -> [a] -> [Exists (KindOf (z :: sa)) ((:~:) x)]
filterElem x = filterP (x %~)


-- Conclusion:  All of this is really amazing, but it still doesn't turn
-- Haskell into a fully fledged dependently typed language.  There is a
-- clear distinction between types and kinds, so every communication
-- between the two levels is ad hoc and explicit, at least technically.
-- A lot of clever machinery underlies the singletons library to make
-- dependently typed programming practical and to some extent enjoyable.
--
-- So singletons work for now, but the long term solution is to get
-- language-level support for dependent types.  This is unlikely to
-- happen for Haskell, because it would change the language to such an
-- extent that we couldn't really call it Haskell anymore.
--
-- Edwin Brady has taken a step into the right direction by designing
-- Idris as a dependently typed language, while strictly keeping it a
-- *programming language* and providing most of the conveniences of
-- Haskell along with a number of its own.  This is important, because
-- we need dependent types not only for writing proofs, but also for
-- writing programs -- actual programs that are supposed to run and do
-- something interesting.
--
-- But then of course this is whining on an extremely high level.  As
-- Haskell programmers we're complaining about the lack of advanced type
-- system features, while the rest of the world is still suffering from
-- Java, PHP and Python.
--
-- Yes, all three in the same sentence.  I'm comparing them to Haskell,
-- not to each other.  Compared to Haskell, all of them are broken.

main :: IO ()
main =
    let n+t=zipWith id.cycle$ replicate n id++[(++t).filter(>'9')]in
    mapM_ putStrLn.(4+"Buzz").(2+"Fizz").map show$[1..]
