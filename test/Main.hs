{-#
OPTIONS_GHC -fplugin BinderAnn.Monadic
#-}
import PropProver

{- run a proof -}
main = prover $ do

  {- propositional variables -}
  (p, q) <- variables

  {- prove modus ponens -}
  proof (p /\ (p ==> q) ==> q) $ do
    h_and <- intro
    (hp, hpq) <- destruct h_and
    assumption
    breakpoint
    hq <- apply hp hpq
    exact hq

    qed
