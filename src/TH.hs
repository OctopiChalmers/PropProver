{-# LANGUAGE TemplateHaskell #-}
module TH where

import Language.Haskell.TH

mkH :: Integer -> Name -> Name -> Name -> Q [Dec]
mkH sizeH isHyp hyp mkHyp = do
  -- dec <- dataD (cxt []) (mkName "H") [] Nothing (mkConHn <$> [1..sizeH]) []
  dec <- dataD (cxt []) (mkName "H") [] Nothing (mkConHn <$> [0..sizeH]) []
  ins <- instanceD (cxt []) (conT isHyp `appT` conT (mkName "H"))
           [funD hyp (mkHypHn <$> [0..sizeH])]
  return [dec, ins]
  where
    mkConHn n = normalC (mkHn n) []
    mkHypHn n = clause [conP (mkHn n) []] (normalB (mkMkHyp n)) []
    mkMkHyp n = conE mkHyp `appE` litE (IntegerL n)
    mkHn    n = mkName ("H" ++ show n)

  -- [d| data H = $(mkConHn <$> [0..10]) |]
