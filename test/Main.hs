import PropProver

{- launch an "interactive" proof assistant -}
main = prover $ do

  {- create some propositional variables -}
  (p, q, r) <- vars

  {- state axioms -}
  axiom_double_neg <- axiom (neg (neg p) === p)

  {- prove some stuff -}
  -- trivial      p
  modus_ponens p q
  de_morgan    p q
  dist_and_or  p q r


{- p ==> p -}
trivial p =
  proof (p ==> p) $ do
    intro
    assumption
    qed

{- p /\ (p ==> q) ==> q -}
modus_ponens p q =
  proof (p /\ (p ==> q) ==> q) $ do
    h_p_pq <- intro
    (h_p, h_pq) <- destruct h_p_pq
    h_q <- apply h_p h_pq
    exact h_q
    qed

{- neg p \/ neg q ==> neg (p /\ q) -}
de_morgan p q =
  proof (neg p \/ neg q ==> neg (p /\ q)) $ do

    {- we can reuse proofs! -}
    mp_lemma <- pose (modus_ponens (neg q) (p /\ q))

    np_or_nq <- intro
    p_and_q  <- intro
    (hp, hq) <- destruct p_and_q
    elim np_or_nq
    contradiction
    contradiction
    qed

{- p /\ (q \/ r) ==> (p /\ q) \/ (p /\ r) -}
dist_and_or p q r =
  proof (p /\ (q \/ r) ==> p /\ q \/ p /\ r) $ do
    h1 <- intro
    (hp, hpq) <- destruct h1
    elim hpq
    left
    breakpoint
    split
    assumption
    assumption
    right
    split
    assumption
    assumption

    qed
