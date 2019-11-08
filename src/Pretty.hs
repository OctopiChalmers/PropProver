module Pretty where

import Data.List
import Control.Monad

import qualified Data.Map as Map
import qualified Data.Set as Set

import MonadAnn.Monadic

import Types
import Prop

-- Pretty printing errors
printErrorHeaderWithLocation :: ProofState -> IO ()
printErrorHeaderWithLocation ps =
  case ps_ann_curr ps of
    Just (Info _ (Just (f,r,c))) ->
      putStrLn $ "Error at " ++ f ++ ":" ++ show (r, c)
    _ -> return ()

printBreakpointLocation :: ProofState -> IO ()
printBreakpointLocation ps =
  case ps_ann_curr ps of
    Just (Info _ (Just (f,r,c))) -> do
      putStrLn $ "Reached breakpoint at: " ++ f ++ ":" ++ show (r, c)
    _ -> return ()

printCurrentLocation :: ProofState -> IO ()
printCurrentLocation ps =
  case ps_ann_curr ps of
    Just (Info _ (Just (f,r,c))) -> do
      putStrLn $ "Current position: " ++ f ++ ":" ++ show (r, c)
    _ -> return ()

printProofState :: ProofState -> IO ()
printProofState ps = do
  let subgoals = length (ps_subgoals ps)
  let subgoalsword = if subgoals == 1 then "subgoal" else "subgoals"
  putStrLn $ show subgoals ++ " " ++ subgoalsword
  putStrLn $ intercalate ", " (pprVar ps <$> Set.elems (ps_vars ps)) ++ " : Prop"
  forM_ (Map.assocs (ps_axioms ps)) $ \(axm, prop) -> do
    putStrLn $ pprHyp ps axm ++ " : " ++ pprProp ps prop
  when (not (null (ps_subgoals ps))) $ do
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

printBreakpoint :: ProofState -> IO ()
printBreakpoint ps = do
  printBreakpointLocation ps
  putStrLn $ "\n----------------------------------------\n"
  printProofState ps

printIncompleteProof :: ProofState -> IO ()
printIncompleteProof ps = do
  printCurrentLocation ps
  putStrLn $ "\n----------------------------------------\n"
  printProofState ps

-- Pretty printing hypotheses
pprHyp :: ProofState -> Hyp -> String
pprHyp ps h
  | Just (Info (Just name) _) <- Map.lookup h (ps_ann_hyps ps) = name
  | otherwise = "H" ++ show (unHyp h)

-- Pretty printing propositions
pprVar :: ProofState -> Var -> String
pprVar ps i
  | Just (Info (Just name) _) <- Map.lookup i (ps_ann_vars ps) = name
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
