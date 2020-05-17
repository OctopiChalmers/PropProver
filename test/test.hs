{-# OPTIONS_GHC -fplugin BinderAnn.Monadic #-}
import PropProver


{- launch an "interactive" proof assistant -}
main = prover do

  {- create some propositional variables -}
  (p, q, r) <- variables

  {- state some axioms -}
  -- axiom_classic <- axiom (p \/ neg p)

  {- prove some stuff -}
  trivial      p
  modus_ponens p q
  de_morgan    p q
  dist_and_or  p q r


{-  p ==> p  -}
trivial p =
  proof (p ==> p) do
    hp <- intro
    exact hp
    qed

{-  p /\ (p ==> q) ==> q  -}
modus_ponens p q =
  proof (p /\ (p ==> q) ==> q) do



    qed

{-  neg p \/ neg q ==> neg (p /\ q)  -}
de_morgan p q =
  proof (neg p \/ neg q ==> neg (p /\ q)) do

    {- we can reuse proofs! -}
    mp_lemma <- pose (modus_ponens (neg q) (p /\ q))

    np_or_nq <- intro
    p_and_q  <- intro
    (hp, hq) <- destruct p_and_q
    elim np_or_nq
    contradiction
    contradiction
    qed

{-  p /\ (q \/ r) ==> (p /\ q) \/ (p /\ r)  -}
dist_and_or p q r =
  proof (p /\ (q \/ r) ==> p /\ q \/ p /\ r) do
    h1 <- intro
    (hp, hpq) <- destruct h1
    elim hpq
    left
    split
    assumption
    assumption
    right
    split
    assumption
    assumption
    qed


twice :: Monad m => m a -> m (a, a)
twice m = do
  x <- m
  return (x, x)
