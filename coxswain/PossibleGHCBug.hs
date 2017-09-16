{-# LANGUAGE TypeFamilyDependencies #-}

type family T (a :: *) = (r :: *) | r -> a where

f :: (T a ~ T b) => a -> b
f x = x

{- Error message in 8.2.1:

PossibleGHCBug.hs:6:7: error:
    * Could not deduce: a ~ b
      from the context: T a ~ T b
        bound by the type signature for:
                   f :: forall a b. T a ~ T b => a -> b
        at PossibleGHCBug.hs:5:1-26
      `a' is a rigid type variable bound by
        the type signature for:
          f :: forall a b. T a ~ T b => a -> b
        at PossibleGHCBug.hs:5:1-26
      `b' is a rigid type variable bound by
        the type signature for:
          f :: forall a b. T a ~ T b => a -> b
        at PossibleGHCBug.hs:5:1-26
    * In the expression: x
      In an equation for `f': f x = x
    * Relevant bindings include
        x :: a (bound at PossibleGHCBug.hs:6:3)
        f :: a -> b (bound at PossibleGHCBug.hs:6:1)

-}

{- Traced via a no-op TcPlugin:

-------- #1
given only [[G] $d~_a19m {0}:: (fsk0_a19j[fsk] :: *) ~ (fsk0_a19j[fsk] :: *) (CDictCan),
            [G] $d~~_a19n {0}:: (fsk0_a19j[fsk] :: *) ~~ (fsk0_a19j[fsk] :: *) (CDictCan),
            [G] cobox_a19k {0}:: (T b_a198[sk:2] :: *) ~# (fsk0_a19j[fsk] :: *) (CFunEqCan),
            [G] cobox_a19i {0}:: (T a_a197[sk:2] :: *) ~# (fsk0_a19h[fsk] :: *) (CFunEqCan),
            [G] cobox_a19l {1}:: (fsk0_a19h[fsk] :: *) ~# (fsk1_a19j[fsk] :: *) (CTyEqCan)]
given only zonked [[G] $d~_a19m {0}:: (T b_a198[sk:2] :: *) ~ (T b_a198[sk:2] :: *) (CDictCan),
                   [G] $d~~_a19n {0}:: (T b_a198[sk:2] :: *) ~~ (T b_a198[sk:2] :: *) (CDictCan),
                   [G] cobox_a19k {0}:: (T b_a198[sk:2] :: *) ~# (T b_a198[sk:2] :: *) (CNonCanonical),
                   [G] cobox_a19i {0}:: (T a_a197[sk:2] :: *) ~# (T a_a197[sk:2] :: *) (CNonCanonical),
                   [G] cobox_a19l {1}:: (T a_a197[sk:2] :: *) ~# (T b_a198[sk:2] :: *) (CNonCanonical)]
vars [a_a197[sk:2], b_a198[sk:2], fsk_a19h[fsk], fsk_a19j[fsk]]
untouchables [fsk_a19j[fsk], fsk_a19h[fsk], b_a198[sk:2], a_a197[sk:2]]
-------- #2
given only [[G] $d~_a1cG {0}:: (fsk0_a1cD[fsk] :: *) ~ (fsk0_a1cD[fsk] :: *) (CDictCan),
            [G] $d~~_a1cH {0}:: (fsk0_a1cD[fsk] :: *) ~~ (fsk0_a1cD[fsk] :: *) (CDictCan),
            [G] cobox_a1cE {0}:: (T b_a1ct[sk:2] :: *) ~# (fsk0_a1cD[fsk] :: *) (CFunEqCan),
            [G] cobox_a1cC {0}:: (T a_a1cs[sk:2] :: *) ~# (fsk0_a1cB[fsk] :: *) (CFunEqCan),
            [G] cobox_a1cF {1}:: (fsk0_a1cB[fsk] :: *) ~# (fsk1_a1cD[fsk] :: *) (CTyEqCan)]
given only zonked [[G] $d~_a1cG {0}:: (T b_a1ct[sk:2] :: *) ~ (T b_a1ct[sk:2] :: *) (CDictCan),
                   [G] $d~~_a1cH {0}:: (T b_a1ct[sk:2] :: *) ~~ (T b_a1ct[sk:2] :: *) (CDictCan),
                   [G] cobox_a1cE {0}:: (T b_a1ct[sk:2] :: *) ~# (T b_a1ct[sk:2] :: *) (CNonCanonical),
                   [G] cobox_a1cC {0}:: (T a_a1cs[sk:2] :: *) ~# (T a_a1cs[sk:2] :: *) (CNonCanonical),
                   [G] cobox_a1cF {1}:: (T a_a1cs[sk:2] :: *) ~# (T b_a1ct[sk:2] :: *) (CNonCanonical)]
vars [a_a1cs[sk:2], b_a1ct[sk:2], fsk_a1cB[fsk], fsk_a1cD[fsk]]
untouchables [fsk_a1cD[fsk], fsk_a1cB[fsk], b_a1ct[sk:2], a_a1cs[sk:2]]
-------- #3
given [[G] $d~_a1cG {0}:: (fsk0_a1cD[fsk] :: *) ~ (fsk0_a1cD[fsk] :: *) (CDictCan),
       [G] $d~~_a1cH {0}:: (fsk0_a1cD[fsk] :: *) ~~ (fsk0_a1cD[fsk] :: *) (CDictCan),
       [G] cobox_a1cE {0}:: (T b_a1ct[sk:2] :: *) ~# (fsk0_a1cD[fsk] :: *) (CFunEqCan),
       [G] cobox_a1cC {0}:: (T a_a1cs[sk:2] :: *) ~# (fsk0_a1cB[fsk] :: *) (CFunEqCan),
       [G] cobox_a1cF {1}:: (fsk0_a1cB[fsk] :: *) ~# (fsk1_a1cD[fsk] :: *) (CTyEqCan)]
given zonked [[G] $d~_a1cG {0}:: (T b_a1ct[sk:2] :: *) ~ (T b_a1ct[sk:2] :: *) (CDictCan),
              [G] $d~~_a1cH {0}:: (T b_a1ct[sk:2] :: *) ~~ (T b_a1ct[sk:2] :: *) (CDictCan),
              [G] cobox_a1cE {0}:: (T b_a1ct[sk:2] :: *) ~# (T b_a1ct[sk:2] :: *) (CNonCanonical),
              [G] cobox_a1cC {0}:: (T a_a1cs[sk:2] :: *) ~# (T a_a1cs[sk:2] :: *) (CNonCanonical),
              [G] cobox_a1cF {1}:: (T a_a1cs[sk:2] :: *) ~# (T b_a1ct[sk:2] :: *) (CNonCanonical)]
derived []
wanted [[WD] hole{a1cw} {0}:: (a_a1cs[sk:2] :: *) ~# (b_a1ct[sk:2] :: *) (CNonCanonical)]
vars [a_a1cs[sk:2], b_a1ct[sk:2], fsk_a1cB[fsk], fsk_a1cD[fsk]]
untouchables [fsk_a1cD[fsk], fsk_a1cB[fsk], b_a1ct[sk:2], a_a1cs[sk:2]]
-}
