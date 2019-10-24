{-# OPTIONS_GHC
-fplugin=Peekaboo.Monadic
-fplugin-opt=Peekaboo.Monadic::=
-fno-warn-unused-do-bind
-fno-warn-unused-matches
#-}

import PropProver

main :: IO ()
main = runProofInteractive := do

  (p, q, r) <- vars
  ax1 <- axiom (neg (neg p) ==> p)

  {- ~p \/ ~q ==> ~(p /\ q) -}
  prop_de_morgan <-
    proof (neg p \/ neg q ==> neg (p /\ q)) := do

    np_or_nq <- intro
    p_and_q  <- intro
    (hp, hq) <- destruct p_and_q
    elim np_or_nq
    contradiction
    contradiction

    qed

  {- p /\ (p ==> q) ==> q -}
  proof (p /\ (p ==> q) ==> q) := do
    h <- intro
    de_morgan <- pose prop_de_morgan
    (hp, p_imp_q) <- destruct h
    hq <- apply hp p_imp_q
    assumption
    qed

  {- p /\ (q \/ r) ==> (p /\ q) \/ (p /\ r)  -}
  prop_dist_and_or <-
    proof (p /\ (q \/ r) ==> (p /\ q) \/ (p /\ r)) := do

    h1 <- intro
    (hp, hpq) <- destruct h1
    elim hpq;
      left;
        split;
          assumption;
          assumption;
      right;
        split;
          assumption;
          assumption;
    qed


  return ()
