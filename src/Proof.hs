module Proof where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Identity

import Types
import Pretty

----------------------------------------
-- | The proof type

type Proof = StateT ProofState (ExceptT ProofError Identity)

runProof :: Proof a -> Either ProofError a
runProof = runIdentity . runExceptT . flip evalStateT emptyProofState


-- Run a proof and pretty print the result
prover :: Proof a -> IO ()
prover p = do
  putStrLn "\n*** PropProver ***"
  case runProof p of
    Right _                               -> putStrLn "No more subgoals."
    Left (IncompleteProof ps)             -> printIncompleteProof ps
    Left (ReachedBreakpoint ps)           -> printBreakpoint ps
    Left (InvalidTactic ps name)          -> printInvalidTactic ps name
    Left (NoMoreSubgoals ps name)         -> printNoMoreSubgoals ps name
    Left (InexistentHypothesis ps name h) -> printInexistentHypothesis ps name h
