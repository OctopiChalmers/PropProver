module Prop where

import Types

----------------------------------------
-- Builders

false, (⊥) :: Prop
false = Bot
(⊥) = Bot

neg :: Prop -> Prop
neg = Neg

(/\), (∧) :: Prop -> Prop -> Prop
(/\) = And
(∧) = And
infixl 7 /\
infixl 7 ∧

(\/), (∨) :: Prop -> Prop -> Prop
(\/) = Or
(∨) = Or
infixl 6 \/
infixl 6 ∨

(==>), (⇒) :: Prop -> Prop -> Prop
(==>) = Imp
(⇒) = Imp
infixr 5 ==>
infixr 5 ⇒

(===), (≡) :: Prop -> Prop -> Prop
(===) = Eq
(≡) = Eq
infix 4 ===
infix 4 ≡

----------------------------------------
-- Predicates over Props

isBinary :: Prop -> Bool
isBinary Bot    = False
isBinary Var {} = False
isBinary Neg {} = False
isBinary _      = True

isNeg :: Prop -> Bool
isNeg Neg {} = True
isNeg _      = False

isAnd :: Prop -> Bool
isAnd And {} = True
isAnd _      = False

isOr :: Prop -> Bool
isOr Or {} = True
isOr _      = False

isImp :: Prop -> Bool
isImp Imp {} = True
isImp _      = False

isEq :: Prop -> Bool
isEq Eq {} = True
isEq _     = False

subterms :: Prop -> [Prop]
subterms = \case
  Bot -> []
  Var _ -> []
  Neg x -> [x]
  And x y -> [x, y]
  Or  x y -> [x, y]
  Imp x y -> [x, y]
  Eq  x y -> [x, y]
