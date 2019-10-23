import PropProver

main :: IO ()
main = runProofInteractive $ do

  (p, q) <- vars

  proof (p ==> q ==> p /\ q) $ do
    intro
    intro

    split $ do
      assumption
      exact (hyp 1) 
    
    qed
