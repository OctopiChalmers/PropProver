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
    IncompleteProof ProofState
  | InvalidTactic   ProofState String
  | NoMoreSubgoals  ProofState String
  deriving Show

-- Error throwers
incompleteProof :: Proof a
incompleteProof = get >>= \ps -> throwError (IncompleteProof ps)

invalidTactic :: String -> Proof a
invalidTactic name = get >>= \ps -> throwError (InvalidTactic ps name)

noMoreSubgoals :: String -> Proof a
noMoreSubgoals name = get >>= \ps -> throwError (NoMoreSubgoals ps name)


-- Pretty printing errors
printInvalidTactic :: ProofState -> String -> IO ()
printInvalidTactic ps name = do
  case ps_ann_last ps of
    Just (MkSrcInfo _ (Just (f,r,c))) ->
      putStrLn $ "Error at: " ++ f ++ ":" ++ show (r, c)
    _ -> return ()
  putStrLn $ "Cannot apply tactic <" ++ name ++ "> to the current subgoal:"
  putStrLn $ pprProp ps (head (ps_subgoals ps))

printIncompleteProof :: ProofState -> IO ()
printIncompleteProof ps = do
  putStrLn $ show (length (ps_subgoals ps)) ++ " subgoals:"
  forM_ (Set.elems (ps_variables ps)) $ \i -> do
    putStrLn $ pprVar ps i ++ " : Prop"
  forM_ (Map.assocs (ps_hyps ps)) $ \(h, prop) -> do
    putStrLn $ pprHyp ps h ++ " : " ++ pprProp ps prop
  putStrLn "----------------------------------------"
  putStrLn $ pprProp ps (head (ps_subgoals ps))

printNoMoreSubgoals :: ProofState -> String -> IO ()
printNoMoreSubgoals ps name = do
  case ps_ann_last ps of
    Just (MkSrcInfo _ (Just (f,r,c))) ->
      putStrLn $ "Error at: " ++ f ++ ":" ++ show (r,c)
    _ -> return ()
  putStrLn $ "No subgoals left in this branch to apply tactic <" ++ name ++ ">"

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
  Bot -> "⊥"
  Var v -> pprVar ps v
  Neg p -> "¬(" ++ pprProp ps p ++ ")"
  And x y -> "(" ++ pprProp ps x ++ " /\\ " ++ pprProp ps y ++ ")"
  Or  x y -> "(" ++ pprProp ps x ++ " \\/ " ++ pprProp ps y ++ ")"
  Imp x y -> "(" ++ pprProp ps x ++ " ==> " ++ pprProp ps y ++ ")"
  Eq  x y -> "(" ++ pprProp ps x ++ " <=> " ++ pprProp ps y ++ ")"

----------------------------------------
-- | Proof state

type Goal = Prop

newtype Hyp = MkHyp { unHyp :: Int }
  deriving (Show, Eq, Ord)

data ProofState = ProofState
  { ps_variables :: Set Var
  , ps_hyps :: Map Hyp Prop
  , ps_goal :: Goal
  , ps_subgoals :: [Goal]
  , ps_ann_vars :: Map Var SrcInfo
  , ps_ann_hyps :: Map Hyp SrcInfo
  , ps_ann_last :: Maybe SrcInfo
  , ps_var_uniq :: Int
  , ps_hyp_uniq :: Int
  } deriving Show

emptyProofState :: ProofState
emptyProofState =
  ProofState Set.empty Map.empty (Neg Bot) [] Map.empty Map.empty Nothing 0 0


----------------------------------------
-- | The proof type

type Proof = StateT ProofState (ExceptT ProofError IO)

-- Runners
runProof :: Proof a -> IO (Either ProofError a)
runProof = runExceptT . flip evalStateT emptyProofState

runProofInteractive :: Proof a -> IO ()
runProofInteractive p =
  runProof p >>= \case
    Right _ -> putStrLn "No more subgoals"
    Left (InvalidTactic ps name)  -> printInvalidTactic ps name
    Left (IncompleteProof ps)     -> printIncompleteProof ps
    Left (NoMoreSubgoals ps name) -> printNoMoreSubgoals ps name


----------------------------------------
-- Basic proof constructions

-- Bring new variables to life
var :: Proof Prop
var = newVar

class Variables a where
  vars :: Proof a

instance Variables (Prop, Prop) where
  vars = (,) <$> var <*> var

instance Variables (Prop, Prop, Prop) where
  vars = (,,) <$> var <*> var <*> var

-- Creaate a proof target
proof :: Prop -> Proof Prop -> Proof Prop
proof goal body = do
  setGoal goal
  setSubgoals [goal]
  body

-- Complete a proof gracefully
qed :: Proof Prop
qed = do
  ps <- get
  if null (ps_subgoals ps)
    then return (ps_goal ps)
    else incompleteProof


-- Operations over variables
newVar :: Proof Prop
newVar = state $ \ps ->
  (Var (MkVar (ps_var_uniq ps)),
   ps { ps_var_uniq = ps_var_uniq ps + 1
      , ps_variables = Set.insert (MkVar (ps_var_uniq ps)) (ps_variables ps)
      })

----------------------------------------
-- Proof source annotations

instance Annotated SrcInfo Proof Prop where
  annotateM info pp = do
    p <- pp
    case p of
      Var v -> insertVarSrcInfo v info >> return p
      _     -> return p

instance Annotated SrcInfo Proof Hyp where
  annotateM info ph = do
    h <- ph
    insertHypSrcInfo h info
    return h

instance Annotated SrcInfo Proof () where
  annotateM info pu = do
    () <- pu
    setLastTacticSrcInfo info
    return ()

----------------------------------------
-- Proof state operations

-- Operations over hypotheses
hyp :: Int -> Hyp
hyp = MkHyp

newHyp :: Prop -> Proof Hyp
newHyp prop = state $ \ps ->
  (MkHyp (ps_var_uniq ps),
   ps { ps_hyp_uniq = ps_hyp_uniq ps + 1
      , ps_hyps = Map.insert (MkHyp (ps_hyp_uniq ps)) prop (ps_hyps ps)
      })

lookupHyp :: Hyp -> Proof (Maybe Prop)
lookupHyp i = Map.lookup i <$> gets ps_hyps

getHyps :: Proof (Map Hyp Prop)
getHyps = gets ps_hyps

setHyps :: Map Hyp Prop -> Proof ()
setHyps hyps = modify $ \ps ->
  ps { ps_hyps = hyps }


-- Operations over goals and subgoals
setGoal :: Goal -> Proof ()
setGoal goal = modify $ \ps ->
  ps { ps_goal = goal }

setSubgoals :: [Goal] -> Proof ()
setSubgoals subgoals = modify $ \ps ->
  ps { ps_subgoals = subgoals }

getSubgoals :: Proof [Goal]
getSubgoals = gets ps_subgoals

-- Operations over source annotations
insertVarSrcInfo :: Var -> SrcInfo -> Proof ()
insertVarSrcInfo i info = modify $ \ps ->
  ps { ps_ann_vars = Map.insert i info (ps_ann_vars ps) }

insertHypSrcInfo :: Hyp -> SrcInfo -> Proof ()
insertHypSrcInfo h info = modify $ \ps ->
  ps { ps_ann_hyps = Map.insert h info (ps_ann_hyps ps) }

setLastTacticSrcInfo :: SrcInfo -> Proof ()
setLastTacticSrcInfo info = modify $ \ps ->
  ps { ps_ann_last = Just info }
