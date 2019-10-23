{-# LANGUAGE LambdaCase #-}

module Tactics where

import Prop
import Proof

idtac :: Proof ()
idtac = return ()

intro :: Proof Hyp
intro = getSubgoals >>= \case
  Imp x y : rest -> do
    setSubgoals (y : rest)
    newHyp x
  goal : _ -> invalidTactic "intro"
  _        -> noMoreSubgoals "intro"

exact :: Hyp -> Proof ()
exact i = do
  hyp <- lookupHyp i
  getSubgoals >>= \case
    g : rest | hyp == Just g -> setSubgoals rest
    goal : _                 -> invalidTactic "exact"
    _                        -> noMoreSubgoals "exact"

assumption :: Proof ()
assumption = do
  hyps <- getHyps
  getSubgoals >>= \case
    goal : rest | goal `elem` hyps -> setSubgoals rest
    goal : _                       -> invalidTactic "assumption"
    _                              -> noMoreSubgoals "assumption"

split :: Proof () -> Proof ()
split body = do
  hyps <- getHyps
  getSubgoals >>= \case
    And x y : rest -> do
      setSubgoals [x, y]
      body
      qed
      setSubgoals rest
      setHyps hyps
    goal : _ -> invalidTactic "split"
    _        -> noMoreSubgoals "split"

left :: Proof () -> Proof ()
left body = do
  hyps <- getHyps
  getSubgoals >>= \case
    Or x _ : rest -> do
      setSubgoals [x]
      body
      qed
      setSubgoals rest
      setHyps hyps
    goal : _ -> invalidTactic "left"
    _        -> noMoreSubgoals "left"

right :: Proof () -> Proof ()
right body = do
  hyps <- getHyps
  getSubgoals >>= \case
    Or x _ : rest -> do
      setSubgoals [x]
      body
      qed
      setSubgoals rest
      setHyps hyps
    goal : _ -> invalidTactic "right"
    _        -> noMoreSubgoals "right"
