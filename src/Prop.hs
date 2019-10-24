{-# LANGUAGE LambdaCase #-}
module Prop where

----------------------------------------
-- | Identifiers

newtype Var = MkVar { unVar :: Int }
  deriving (Show, Eq, Ord)

----------------------------------------
-- | Propositional values

data Prop =
   Bot
 | Var Var
 | Neg Prop
 | And Prop Prop
 | Or  Prop Prop
 | Imp Prop Prop
 | Eq  Prop Prop
  deriving (Show, Eq)

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

----------------------------------------
-- Infix builders

false :: Prop
false = Bot

neg :: Prop -> Prop
neg = Neg

(/\) :: Prop -> Prop -> Prop
(/\) = And
infixl 7 /\

(\/) :: Prop -> Prop -> Prop
(\/) = Or
infixl 6 \/

(==>) :: Prop -> Prop -> Prop
(==>) = Imp
infixr 5 ==>

(===) :: Prop -> Prop -> Prop
(===) = Eq
infix 4 ===
