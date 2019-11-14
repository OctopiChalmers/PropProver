module MonadProof where

import Control.Monad.State
import Control.Monad.Except

import qualified Data.Map as Map
import qualified Data.Set as Set

import BinderAnn.Monadic

import Types

----------------------------------------
-- | Monads for proving stuff

type MonadProof m =
  ( MonadState ProofState m
  , MonadError ProofError m
  )

----------------------------------------
-- Basic proof constructions

-- Instantiate new propositional variables
variable :: MonadProof m => m Prop
variable = freshVar

class MonadProof m => Variables m a where
  variables :: m a

instance MonadProof m => Variables m (Prop, Prop) where
  variables = (,) <$> freshVar <*> freshVar

instance MonadProof m => Variables m (Prop, Prop, Prop) where
  variables = (,,) <$> freshVar <*> freshVar <*> freshVar


-- Create a proof for a given goal
proof :: MonadProof m => Prop -> m Tautology -> m Tautology
proof goal body = do
  ps <- get

  setGoal goal
  setSubgoals [(goal, Map.empty)]
  tauto <- body

  put ps
  return tauto

-- Complete a proof gracefully
qed :: MonadProof m => m Tautology
qed = do
  ps <- get
  if null (ps_subgoals ps)
    then return (Tautology (ps_goal ps))
    else incompleteProof

-- Create a breakpoint within a proof
breakpoint :: MonadProof m => m ()
breakpoint = get >>= \ps ->
  throwError (ReachedBreakpoint ps)

-- Create axioms
axiom :: MonadProof m => Prop -> m Hyp
axiom prop = state $ \ps ->
  let uniq = ps_hyp_uniq ps; axm = MkHyp uniq
  in (axm, ps { ps_hyp_uniq = uniq + 1
              , ps_axioms = Map.insert axm prop (ps_axioms ps)})



----------------------------------------
-- | Proof state operations

-- Create a fresh variable
freshVar :: MonadProof m => m Prop
freshVar = state $ \ps ->
  let uniq = ps_var_uniq ps; v = MkVar uniq
  in (Var v, ps { ps_var_uniq = uniq + 1, ps_vars = Set.insert v (ps_vars ps)})

-- Create a fresh hypothesis
freshHyp :: MonadProof m => m Hyp
freshHyp = state $ \ps ->
  let uniq = ps_hyp_uniq ps; h = MkHyp uniq
  in (h, ps { ps_hyp_uniq = uniq + 1 })


-- Operations over goals and subgoals
getGoal :: MonadProof m => m Goal
getGoal = gets ps_goal

setGoal :: MonadProof m => Goal -> m ()
setGoal goal = modify $ \ps ->
  ps { ps_goal = goal }

setSubgoals :: MonadProof m => [(Goal, Context)] -> m ()
setSubgoals subgoals = modify $ \ps ->
  ps { ps_subgoals = subgoals }

getSubgoals :: MonadProof m => m [(Goal, Context)]
getSubgoals = gets ps_subgoals


----------------------------------------
-- | Error throwers

incompleteProof :: MonadProof m => m a
incompleteProof = get >>= \ps ->
  throwError (IncompleteProof ps)

inexistentHypothesis :: MonadProof m => String -> Hyp -> m a
inexistentHypothesis name h = get >>= \ps ->
  throwError (InexistentHypothesis ps name h)

invalidTactic :: MonadProof m => String -> m a
invalidTactic name = get >>= \ps ->
  throwError (InvalidTactic ps name)

noMoreSubgoals :: MonadProof m => String -> m a
noMoreSubgoals name = get >>= \ps ->
  throwError (NoMoreSubgoals ps name)

----------------------------------------
-- Proof source annotations

instance MonadProof m => Annotated SrcInfo m Prop where
  annotateM pp info = do
    setCurrCommandSrcInfo info
    p <- pp
    case p of
      Var v -> insertVarSrcInfo v info >> return p
      _     -> return p

instance MonadProof m => Annotated SrcInfo m Hyp where
  annotateM ph info = do
    setCurrCommandSrcInfo info
    h <- ph
    insertHypSrcInfo h info
    return h

instance MonadProof m => Annotated SrcInfo m () where
  annotateM pu info = do
    setCurrCommandSrcInfo info
    () <- pu
    return ()

-- Operations over source annotations
insertVarSrcInfo :: MonadProof m => Var -> SrcInfo -> m ()
insertVarSrcInfo i info = modify $ \ps ->
  ps { ps_ann_vars = Map.insert i info (ps_ann_vars ps) }

insertHypSrcInfo :: MonadProof m => Hyp -> SrcInfo -> m ()
insertHypSrcInfo h info = modify $ \ps ->
  ps { ps_ann_hyps = Map.insert h info (ps_ann_hyps ps) }

setCurrCommandSrcInfo :: MonadProof m => SrcInfo -> m ()
setCurrCommandSrcInfo info = modify $ \ps ->
  ps { ps_ann_curr = Just info }
