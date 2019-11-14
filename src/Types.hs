{-# LANGUAGE TemplateHaskell #-}
module Types where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import TH
import BinderAnn.Monadic

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

----------------------------------------
-- | Tautologies

newtype Tautology = Tautology { getTautology :: Prop }
  deriving Show

----------------------------------------
-- | Hypotheses

newtype Hyp = MkHyp { unHyp :: Int }
  deriving (Show, Eq, Ord)

class IsHyp a where
  hyp :: a -> Hyp

instance IsHyp Hyp where
  hyp = id

instance IsHyp Int where
  hyp = MkHyp

-- Some template haskell magic to have H0..H100 as valid hypotheses
mkH 100 ''IsHyp 'hyp 'MkHyp

----------------------------------------
-- | Proof state

type Goal = Prop

type Context = Map Hyp Prop
type Axioms  = Map Hyp Prop

type VarInfo = Map Var SrcInfo
type HypInfo = Map Hyp SrcInfo

data ProofState = ProofState
  -- | Proof state
  { ps_vars     :: Set Var
  , ps_axioms   :: Axioms
  , ps_goal     :: Goal
  , ps_subgoals :: [(Goal, Context)]
  -- | Source annotations
  , ps_ann_vars :: VarInfo
  , ps_ann_hyps :: HypInfo
  , ps_ann_curr :: Maybe SrcInfo
  -- | Serial number generators
  , ps_var_uniq :: Int
  , ps_hyp_uniq :: Int
  } deriving Show

emptyProofState :: ProofState
emptyProofState =
  ProofState Set.empty Map.empty (Neg Bot) [] Map.empty Map.empty Nothing 0 0

(+=) :: Ord k => Map k v -> (k, v) -> Map k v
(+=) m (k,v) = Map.insert k v m

(!) :: Ord k => Map k v -> k -> Maybe v
(!) = flip Map.lookup

elems :: Map k a -> [a]
elems = Map.elems

----------------------------------------
-- | Proof errors

data ProofError =
    IncompleteProof       ProofState
  | ReachedBreakpoint     ProofState
  | InexistentHypothesis  ProofState String Hyp
  | InvalidTactic         ProofState String
  | NoMoreSubgoals        ProofState String
  deriving Show
