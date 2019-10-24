{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module Proof where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Identity

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Annotated.Monadic
import Peekaboo.Monadic

import Prop

----------------------------------------
-- | Proof errors

data ProofError =
    IncompleteProof       ProofState
  | InexistentHypothesis  ProofState String Hyp
  | InvalidTactic         ProofState String
  | NoMoreSubgoals        ProofState String
  deriving Show

-- Error throwers
incompleteProof :: Proof a
incompleteProof = get >>= \ps ->
  throwError (IncompleteProof ps)

inexistentHypothesis :: String -> Hyp -> Proof a
inexistentHypothesis name h = get >>= \ps ->
  throwError (InexistentHypothesis ps name h)

invalidTactic :: String -> Proof a
invalidTactic name = get >>= \ps ->
  throwError (InvalidTactic ps name)

noMoreSubgoals :: String -> Proof a
noMoreSubgoals name = get >>= \ps ->
  throwError (NoMoreSubgoals ps name)


-- Pretty printing errors
printErrorHeaderWithLocation :: ProofState -> IO ()
printErrorHeaderWithLocation ps =
  case ps_ann_last ps of
    Just (MkSrcInfo _ (Just (f,r,c))) ->
      putStrLn $ "Error at " ++ f ++ ":" ++ show (r, c)
    _ -> return ()

printCurrentLocation :: ProofState -> IO ()
printCurrentLocation ps =
  case ps_ann_last ps of
    Just (MkSrcInfo _ (Just (f,r,c))) -> do
      putStrLn $ "Current position: " ++ f ++ ":" ++ show (r, c)
    _ -> return ()

printProofState :: ProofState -> IO ()
printProofState ps = do
  let subgoals = length (ps_subgoals ps)
  let subgoalsword = if subgoals == 1 then "subgoal" else "subgoals"
  putStrLn $ show subgoals ++ " " ++ subgoalsword ++ "\n"
  forM_ (Set.elems (ps_vars ps)) $ \i -> do
    putStrLn $ pprVar ps i ++ " : Prop"
  forM_ (Map.assocs (ps_axioms ps)) $ \(axm, prop) -> do
    putStrLn $ pprHyp ps axm ++ " : " ++ pprProp ps prop
  forM_ (Map.assocs (snd (head (ps_subgoals ps)))) $ \(h, prop) -> do
    putStrLn $ pprHyp ps h ++ " : " ++ pprProp ps prop
  putStrLn $ "========================================"
  putStrLn $ pprProp ps (fst (head (ps_subgoals ps)))

printInexistentHypothesis :: ProofState -> String -> Hyp -> IO ()
printInexistentHypothesis ps name h = do
  printErrorHeaderWithLocation ps
  putStrLn $ "\n----------------------------------------\n"
  printProofState ps
  putStrLn $ "\nThe hypothesis <" ++ pprHyp ps h ++ "> does not exist"
  putStrLn $ "When aplying the tactic <" ++ name ++ "> to the current goal"

printInvalidTactic :: ProofState -> String -> IO ()
printInvalidTactic ps name = do
  printErrorHeaderWithLocation ps
  putStrLn $ "Cannot apply tactic <" ++ name ++ "> to the current goal"
  putStrLn $ "----------------------------------------\n"
  printProofState ps

printNoMoreSubgoals :: ProofState -> String -> IO ()
printNoMoreSubgoals ps name = do
  printErrorHeaderWithLocation ps
  putStrLn $ "No subgoals left in this branch to apply tactic <" ++ name ++ ">"
  putStrLn $ "----------------------------------------\n"
  printProofState ps

printIncompleteProof :: ProofState -> IO ()
printIncompleteProof ps = do
  printCurrentLocation ps
  putStrLn $ "\n----------------------------------------\n"
  printProofState ps

-- Pretty printing hypotheses
pprHyp :: ProofState -> Hyp -> String
pprHyp ps h
  | Just (MkSrcInfo (Just name) _) <- Map.lookup h (ps_ann_hyps ps) = name
  | otherwise = "H" ++ show (unHyp h)

-- Pretty printing propositions
pprVar :: ProofState -> Var -> String
pprVar ps i
  | Just (MkSrcInfo (Just name) _) <- Map.lookup i (ps_ann_vars ps) = name
  | otherwise = "v_" ++ show (unVar i)

pprProp :: ProofState -> Prop -> String
pprProp ps = \case
  Bot ->
    "⊥"
  Var v ->
    pprVar ps v
  Neg x ->
    "~" ++ parensIf (isBinary x) (pprProp ps x)
  And x y ->
    parensIf (isOr x  || isImp x || isEq x) (pprProp ps x)
    ++ " /\\ " ++
    parensIf (isOr y  || isImp y || isEq y) (pprProp ps y)
  Or  x y ->
    parensIf (isImp x || isEq  x) (pprProp ps x)
    ++ " \\/ " ++
    parensIf (isImp y || isEq  y) (pprProp ps y)
  Imp x y ->
    parensIf (isEq x) (pprProp ps x)
    ++ " ==> " ++
    parensIf (isEq y) (pprProp ps y)
  Eq  x y ->
    pprProp ps x
    ++ " === " ++
    pprProp ps y

parensIf :: Bool -> String -> String
parensIf True str = "(" ++ str ++ ")"
parensIf _    str = str

----------------------------------------
-- | Proof state


newtype Hyp = MkHyp { unHyp :: Int }
  deriving (Show, Eq, Ord)

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
  , ps_ann_last :: Maybe SrcInfo
  -- | Serial number generators
  , ps_var_uniq :: Int
  , ps_hyp_uniq :: Int
  } deriving Show

emptyProofState :: ProofState
emptyProofState =
  ProofState Set.empty Map.empty (Neg Bot) [] Map.empty Map.empty Nothing 0 0

----------------------------------------
-- | The proof type

type Proof = StateT ProofState (ExceptT ProofError Identity)

-- Runners
runProof :: Proof a -> Either ProofError a
runProof = runIdentity . runExceptT . flip evalStateT emptyProofState

runProofInteractive :: Proof a -> IO ()
runProofInteractive p =
  case runProof p of
    Right _                               -> putStrLn "No more subgoals."
    Left (InvalidTactic ps name)          -> printInvalidTactic ps name
    Left (IncompleteProof ps)             -> printIncompleteProof ps
    Left (NoMoreSubgoals ps name)         -> printNoMoreSubgoals ps name
    Left (InexistentHypothesis ps name h) -> printInexistentHypothesis ps name h


----------------------------------------
-- Basic proof constructions

newtype Tautology = Tautology { getTautology :: Prop } deriving Show


-- Create a proof for a given goal
proof :: Prop -> Proof Tautology -> Proof Tautology
proof goal body = do
  setGoal goal
  setSubgoals [(goal, Map.empty)]
  body

-- Complete a proof gracefully
qed :: Proof Tautology
qed = do
  ps <- get
  if null (ps_subgoals ps)
    then return (Tautology (ps_goal ps))
    else incompleteProof

-- Create axioms
axiom :: Prop -> Proof Hyp
axiom prop = state $ \ps ->
  let uniq = ps_hyp_uniq ps; axm = MkHyp uniq
  in (axm, ps { ps_hyp_uniq = uniq + 1, ps_axioms = Map.insert axm prop (ps_axioms ps)})

-- Bring new variables to life
freshVar :: Proof Prop
freshVar = state $ \ps ->
  let uniq = ps_var_uniq ps; v = MkVar uniq
  in (Var v, ps { ps_var_uniq = uniq + 1, ps_vars = Set.insert v (ps_vars ps)})

var :: Proof Prop
var = freshVar

class Variables a where
  vars :: Proof a

instance Variables (Prop, Prop) where
  vars = (,) <$> var <*> var

instance Variables (Prop, Prop, Prop) where
  vars = (,,) <$> var <*> var <*> var


-- Operations over hypotheses
hyp :: Int -> Hyp
hyp = MkHyp

freshHyp :: Proof Hyp
freshHyp = state $ \ps ->
  let uniq = ps_hyp_uniq ps; h = MkHyp uniq
  in (h, ps { ps_hyp_uniq = uniq + 1 })

(+=) :: Ord k => Map k v -> (k, v) -> Map k v
(+=) m (k,v) = Map.insert k v m

(!) :: Ord k => Map k v -> k -> Maybe v
(!) = flip Map.lookup

elems :: Map k a -> [a]
elems = Map.elems


-- Operations over goals and subgoals
setGoal :: Goal -> Proof ()
setGoal goal = modify $ \ps ->
  ps { ps_goal = goal }

setSubgoals :: [(Goal, Context)] -> Proof ()
setSubgoals subgoals = modify $ \ps ->
  ps { ps_subgoals = subgoals }

getSubgoals :: Proof [(Goal, Context)]
getSubgoals = gets ps_subgoals


----------------------------------------
-- Proof source annotations

instance Annotated SrcInfo Proof Prop where
  annotateM info pp = do
    p <- pp
    setLastCommandSrcInfo info
    case p of
      Var v -> insertVarSrcInfo v info >> return p
      _     -> return p

instance Annotated SrcInfo Proof Hyp where
  annotateM info ph = do
    h <- ph
    insertHypSrcInfo h info
    setLastCommandSrcInfo info
    return h

instance Annotated SrcInfo Proof () where
  annotateM info pu = do
    () <- pu
    setLastCommandSrcInfo info
    return ()

-- Operations over source annotations
insertVarSrcInfo :: Var -> SrcInfo -> Proof ()
insertVarSrcInfo i info = modify $ \ps ->
  ps { ps_ann_vars = Map.insert i info (ps_ann_vars ps) }

insertHypSrcInfo :: Hyp -> SrcInfo -> Proof ()
insertHypSrcInfo h info = modify $ \ps ->
  ps { ps_ann_hyps = Map.insert h info (ps_ann_hyps ps) }

setLastCommandSrcInfo :: SrcInfo -> Proof ()
setLastCommandSrcInfo info = modify $ \ps ->
  ps { ps_ann_last = Just info }
