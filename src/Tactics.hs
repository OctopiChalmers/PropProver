{-# LANGUAGE LambdaCase #-}

module Tactics where

import Prop
import Proof

badSubgoal :: String -> [(Goal, Context)] -> Proof a
badSubgoal name = \case
  _:_ -> invalidTactic  name
  []  -> noMoreSubgoals name

badHyp :: String -> Hyp -> Maybe Prop -> Proof a
badHyp name h = \case
  Just _  -> invalidTactic name
  Nothing -> inexistentHypothesis name h

----------------------------------------
-- Cheaty and trivial tactics

admit :: Proof ()
admit = getSubgoals >>= \case
  _ : rest -> do
    setSubgoals rest
  goal ->
    badSubgoal "admit" goal


idtac :: Proof ()
idtac = return ()

----------------------------------------
-- Tactics for manipulating the goal

intro :: Proof Hyp
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

exact :: Hyp -> Proof ()
exact h = getSubgoals >>= \case
  (goal, ctx) : rest
    | ctx ! h == Just goal ->
      setSubgoals rest
  goal ->
    badSubgoal "exact" goal

assumption :: Proof ()
assumption = getSubgoals >>= \case
  (goal, ctx) : rest
    | goal `elem` ctx ->
      setSubgoals rest
  goal ->
    badSubgoal "assumption" goal

split :: Proof ()
split = getSubgoals >>= \case
  (And x y, ctx) : rest ->
    setSubgoals ((x, ctx) : (y, ctx) : rest)
  (Eq x y, ctx) : rest ->
    setSubgoals ((Imp x y, ctx) : (Imp y x, ctx) : rest)
  goal ->
    badSubgoal "split" goal

left :: Proof ()
left = getSubgoals >>= \case
  (Or x _, ctx) : rest ->
    setSubgoals ((x, ctx) : rest)
  goal ->
    badSubgoal "left" goal

right :: Proof ()
right = getSubgoals >>= \case
  (Or _ y, ctx) : rest ->
    setSubgoals ((y, ctx) : rest)
  goal ->
    badSubgoal "left" goal

----------------------------------------
-- Tactics for manipulating the hypotheses

pose :: Tautology -> Proof Hyp
pose (Tautology prop) = getSubgoals >>= \case
  (goal, ctx) : rest -> do
    h <- freshHyp
    setSubgoals ((goal, ctx += (h, prop)) : rest)
    return h
  goal ->
    badSubgoal "unfold" goal

destruct :: Hyp -> Proof (Hyp, Hyp)
destruct h = getSubgoals >>= \case
  (goal, ctx) : rest ->
    case ctx ! h of
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
      mbp -> badHyp "destruct" h mbp
  goal ->
    badSubgoal "destruct" goal


contradiction :: Proof ()
contradiction = getSubgoals >>= \case
  (_, ctx) : rest -> do
    let pairs = [ (x, y) | Neg x <- elems ctx, y <- elems ctx, x == y ]
    if length pairs > 0
      then setSubgoals rest
      else invalidTactic "contradiction"
  goal ->
    badSubgoal "destruct" goal

elim :: Hyp -> Proof (Hyp, Hyp)
elim h = getSubgoals >>= \case
  (goal, ctx) : rest -> do
    case ctx ! h of
      Just (Or x y) -> do
        hx <- freshHyp
        hy <- freshHyp
        setSubgoals ((goal, ctx += (hx, x)) : (goal, ctx += (hy, y)) : rest)
        return (hx, hy)
      mbp -> badHyp "elim" h mbp
  goal ->
    badSubgoal "elim" goal


apply :: Hyp -> Hyp -> Proof Hyp
apply harg hfun = getSubgoals >>= \case
  (goal, ctx) : rest -> do
    case (ctx ! harg, ctx ! hfun) of
      (Just h, Just (Imp x y))
        | h == x -> do
            hy <- freshHyp
            setSubgoals ((goal, ctx += (hy, y)) : rest)
            return hy
      mbp -> badHyp "apply" harg (fst mbp)
  goal ->
    badSubgoal "elim" goal

unfold :: Proof ()
unfold = getSubgoals >>= \case
  (Neg x, ctx) : rest -> do
    setSubgoals ((Imp x Bot, ctx) : rest)
  (Eq x y, ctx) : rest -> do
    setSubgoals ((And (Imp x y) (Imp y x), ctx) : rest)
  goal ->
    badSubgoal "unfold" goal
