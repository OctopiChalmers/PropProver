module Tactics where

import Types
import MonadProof

badSubgoal :: MonadProof m => String -> [(Goal, Context)] -> m a
badSubgoal name = \case
  _:_ -> invalidTactic  name
  []  -> noMoreSubgoals name

badHyp :: MonadProof m => String -> Hyp -> Maybe Prop -> m a
badHyp name h = \case
  Just _  -> invalidTactic name
  Nothing -> inexistentHypothesis name h

----------------------------------------
-- Cheaty and trivial tactics

admit :: MonadProof m => m ()
admit = getSubgoals >>= \case
  _ : rest ->
    setSubgoals rest
  goal ->
    badSubgoal "admit" goal

idtac :: MonadProof m => m ()
idtac = return ()

----------------------------------------
-- Tactics for manipulating the goal

intro :: MonadProof m => m Hyp
intro = getSubgoals >>= \case
  (Imp x y, ctx) : rest -> do
    h <- freshHyp
    setSubgoals ((y, ctx += (h, x)) : rest)
    return h
  (Neg x, ctx) : rest -> do
    h <- freshHyp
    setSubgoals ((Bot, ctx += (h, x)) : rest)
    return h
  goal ->
    badSubgoal "intro" goal

exact :: (MonadProof m, IsHyp h) => h -> m ()
exact h = getSubgoals >>= \case
  (goal, ctx) : rest
    | ctx ! hyp h == Just goal ->
      setSubgoals rest
  goal ->
    badSubgoal "exact" goal

assumption :: MonadProof m => m ()
assumption = getSubgoals >>= \case
  (goal, ctx) : rest
    | goal `elem` ctx ->
      setSubgoals rest
  goal ->
    badSubgoal "assumption" goal

split :: MonadProof m => m ()
split = getSubgoals >>= \case
  (And x y, ctx) : rest ->
    setSubgoals ((x, ctx) : (y, ctx) : rest)
  (Eq x y, ctx) : rest ->
    setSubgoals ((Imp x y, ctx) : (Imp y x, ctx) : rest)
  goal ->
    badSubgoal "split" goal

left :: MonadProof m => m ()
left = getSubgoals >>= \case
  (Or x _, ctx) : rest ->
    setSubgoals ((x, ctx) : rest)
  goal ->
    badSubgoal "left" goal

right :: MonadProof m => m ()
right = getSubgoals >>= \case
  (Or _ y, ctx) : rest ->
    setSubgoals ((y, ctx) : rest)
  goal ->
    badSubgoal "left" goal

----------------------------------------
-- Tactics for manipulating the hypotheses

pose :: MonadProof m => m Tautology -> m Hyp
pose proof_tauto = getSubgoals >>= \case
  (goal, ctx) : rest -> do
    Tautology prop <- proof_tauto
    h <- freshHyp
    setSubgoals ((goal, ctx += (h, prop)) : rest)
    return h
  goal ->
    badSubgoal "pose" goal

destruct :: (MonadProof m, IsHyp h) => h -> m (Hyp, Hyp)
destruct h = getSubgoals >>= \case
  (goal, ctx) : rest ->
    case ctx ! hyp h of
      Just (And x y) -> do
        hx <- freshHyp
        hy <- freshHyp
        setSubgoals ((goal, ctx += (hx, x) += (hy, y)) : rest)
        return (hx, hy)
      Just (Eq x y) -> do
        hx <- freshHyp
        hy <- freshHyp
        setSubgoals ((goal, ctx += (hx, Imp x y) += (hy, Imp y x)) : rest)
        return (hx, hy)
      mbp -> badHyp "destruct" (hyp h) mbp
  goal ->
    badSubgoal "destruct" goal

contradiction :: MonadProof m => m ()
contradiction = getSubgoals >>= \case
  (_, ctx) : rest -> do
    let pairs = [ (x, y) | Neg x <- elems ctx, y <- elems ctx, x == y ]
    if length pairs > 0
      then setSubgoals rest
      else invalidTactic "contradiction"
  goal ->
    badSubgoal "destruct" goal

elim :: (MonadProof m, IsHyp h) => h -> m (Hyp, Hyp)
elim h = getSubgoals >>= \case
  (goal, ctx) : rest -> do
    case ctx ! hyp h of
      Just (Or x y) -> do
        hx <- freshHyp
        hy <- freshHyp
        setSubgoals ((goal, ctx += (hx, x)) : (goal, ctx += (hy, y)) : rest)
        return (hx, hy)
      mbp -> badHyp "elim" (hyp h) mbp
  goal ->
    badSubgoal "elim" goal


apply :: (MonadProof m, IsHyp ha, IsHyp hf) => ha -> hf -> m Hyp
apply harg hfun = getSubgoals >>= \case
  (goal, ctx) : rest ->
    case (ctx ! hyp harg, ctx ! hyp hfun) of
      (Just h, Just (Imp x y))
        | h == x -> do
            hy <- freshHyp
            setSubgoals ((goal, ctx += (hy, y)) : rest)
            return hy
      mbp -> badHyp "apply" (hyp harg) (fst mbp)
  goal ->
    badSubgoal "elim" goal

unfold :: MonadProof m => m ()
unfold = getSubgoals >>= \case
  (Neg x, ctx) : rest ->
    setSubgoals ((Imp x Bot, ctx) : rest)
  (Eq x y, ctx) : rest ->
    setSubgoals ((And (Imp x y) (Imp y x), ctx) : rest)
  goal ->
    badSubgoal "unfold" goal
