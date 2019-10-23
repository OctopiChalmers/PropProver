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

(<=>) :: Prop -> Prop -> Prop
(<=>) = Eq
infix 4 <=>

false :: Prop
false = Bot
