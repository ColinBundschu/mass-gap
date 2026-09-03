import MassGap.Reconstruct
import MassGapChecks.Groundreads
import MassGapChecks.Momentfold
/-!
The check module for `thm:reconstruct`: the batteries read the
Euclidean families' weight folds, the families' Gram positivity and
the moment solve by kernel `decide` beside the theorem routes, at the
Euclidean fixtures `ChecksGroundreads` publishes and the quadratic
head `ChecksMomentfold` publishes.

The fold block reads the order-one gap `[2]` at the congruence `[1]`
with the root `2` at the scale `1`, the certificate `(2, 1)` at the
count three, and the two solved witnesses, the lower `[1]` at the
clearing `3` and the upper `[3]` at the clearing `5`: at the probes
`1` and `2` the upper family's third power reads `54` against the
fold `27 · 2`, its root entry `27` pinned at `5³ · 27 = 15³ · 1`, and
the lower family's third power reads `2` against the fold `1 · 2`,
its root entry pinned at `3³ · 1 = 3³ · 1`; the order-two gap
`diag(0, 2)` at the identity congruence reads both arms, the kernel
root at the full gap `3` and the positive root at the representative
`2`, the upper witness `diag(15, 9)` at the clearing `15` and the
lower `diag(3, 1)` at `3`, the folds `4833` and `29` at the probes
`(1, 1)` and `(1, 2)` with the four root entries pinned.  The
families' Grams at the two probes decide positive semidefinite
beside their routes.

The binders: the certificate's gap witness is load-bearing at the
lower family, the forged witness `(2, 2)` refusing the certificate
and parting the root pin at `3³ · 1` against `6³ · 1`; the two solve
identities refuse at their own forges, the upper clearing `4`
parting the upper pin and the lower clearing `4` the lower pin, and
the upper solve parts the fold outright at an upper witness off the
congruence's diagonal; the split certificate refuses at the forged
scale `2`, parting both pins at the doubled weight; the certificate's
arm is the upper datum's positivity, `thm:groundreads`(v)'s frame at
the fold and the pin — at the gap `[-1]` with the upper witness `[3]`
solving at the clearing `2` the arm refuses while the fold and the
pin read outright, `2³ · 27 = 6³ · 1` — and load-bearing at the
family's Gram: at the gap `[-5]` the upper witness `[-3]` solves at
the clearing `2`, the arm refuses, and the Gram at the one probe
reads `-27`, its split counting a reversal; the certificate's cap is
`thm:groundreads`(v)'s frame at the lower family, the cap `1` refusing
the certificate with the fold and the pins free of it; and the
probes' orders are `def:ground`'s matched-list frame, the fold
truncating at the shorter operand in either direction.

The solve block reads the quadratic head at the degree one: the
adjugate against the streams' data reads the moment vector at the
determinant `4`, decided beside the route; the bond datum `4`, the
profile's linear `5` and the ground `(6, 4, 3)` off the recurrence
each refuse their read and part the solve, and the degree floor is
the square system's shape frame (`momentfold.momSys_len`), the read
at the degree vacant holding at the padded rows.
-/
set_option maxHeartbeats 4000000

open ground elim inertia groundreads momentfold reconstruct

private def xP : List BPair := [⟨2, 1⟩]
private def yP : List BPair := [⟨3, 1⟩]
private theorem harmOne : ∀ k, k < lOne.length →
    ((ground.getAt (BPair.unit, Pos.one, BPair.unit) lOne k).1).oneValue
        BPair.unit
      ∨ ((ground.getAt (BPair.unit, Pos.one, BPair.unit) lOne k).1).oneValue
          (BPair.ofPos (ground.getAt (Pos.one, Pos.one) wsOne k).1) :=
  eucRead_arm 1 1 2 1 (posOfSucc 2) lOne wsOne hwOne

/-! ## The order-one gap at the positive arm -/

/-- The upper family's third power at the probes reads the diagonal
fold, and its root entry is pinned at the arm's power. -/
private abbrev hiFoldOne : Prop :=
  (minor tOne.val * minor tOne.val
      * dotP xP (matVec (matPow vwOne 1 3) yP)).oneValue
    (dotP (split.vDiagL (matPow vwOne 1 3) tOne)
      (List.zipWith (· * ·) (matVec tOne.val xP) (matVec tOne.val yP)))

private abbrev hiPinOne (vc : Pos) : Prop :=
  (ground.bpow (BPair.ofPos (posOfSucc 2 * ((1 : Pos) * 1))
        + (⟨3, 1⟩ : BPair).scale 1) 3
      * ground.getAt BPair.unit
          (split.vDiagL (matPow vwOne 1 3) tOne) 0).oneValue
    (ground.bpow (BPair.ofPos ((posOfSucc 2 * ((1 : Pos) * 1)) * vc)) 3
      * ((⟨2, 1⟩ : BPair) * BPair.ofPos 1))

example : hiFoldOne := by decide +kernel
example : hiPinOne 5 := by decide +kernel
example : (dotP xP (matVec (matPow vwOne 1 3) yP)).oneValue
    (BPair.ofPos 54) := by decide +kernel
example : (ground.getAt BPair.unit
    (split.vDiagL (matPow vwOne 1 3) tOne) 0).oneValue (BPair.ofPos 27) := by
  decide +kernel
example : hiFoldOne :=
  (euc_hi_fold etOne tOne tOne lOne hdOne 1 1 5 2 wsOne harmOne vwOne hVsOne
    hVOne xP yP rfl rfl).1
example : hiPinOne 5 :=
  (euc_hi_fold etOne tOne tOne lOne hdOne 1 1 5 2 wsOne harmOne vwOne hVsOne
    hVOne xP yP rfl rfl).2 0 (by decide +kernel) ⟨3, 1⟩ ⟨2, 1⟩ 1 rfl

/-- The lower family's third power at the probes reads the diagonal
fold, and its root entry is pinned at the witnessed gap's power. -/
private abbrev loFoldOne : Prop :=
  (minor tOne.val * minor tOne.val
      * dotP xP (matVec (matPow lwOne 1 3) yP)).oneValue
    (dotP (split.vDiagL (matPow lwOne 1 3) tOne)
      (List.zipWith (· * ·) (matVec tOne.val xP) (matVec tOne.val yP)))

private abbrev loPinOne (g lc : Pos) : Prop :=
  (ground.bpow (BPair.ofPos (posOfSucc 2 * ((1 : Pos) * 1))) 3
      * ground.getAt BPair.unit
          (split.vDiagL (matPow lwOne 1 3) tOne) 0).oneValue
    (ground.bpow (BPair.ofPos (g * lc)) 3
      * ((⟨2, 1⟩ : BPair) * BPair.ofPos 1))

example : loFoldOne := by decide +kernel
example : loPinOne 1 3 := by decide +kernel
example : (dotP xP (matVec (matPow lwOne 1 3) yP)).oneValue
    (BPair.ofPos 2) := by decide +kernel
example : loFoldOne :=
  (euc_lo_fold etOne tOne tOne lOne hdOne 1 1 2 1 3 2 wsOne hwOne lwOne hLsOne
    hLOne xP yP rfl rfl).1
example : loPinOne 1 3 :=
  (euc_lo_fold etOne tOne tOne lOne hdOne 1 1 2 1 3 2 wsOne hwOne lwOne hLsOne
    hLOne xP yP rfl rfl).2 0 (by decide +kernel) ⟨3, 1⟩ ⟨2, 1⟩ 1 rfl

/-! ## The order-two gap at both arms -/

private def xK : List BPair := [⟨2, 1⟩, ⟨2, 1⟩]
private def yK : List BPair := [⟨2, 1⟩, ⟨3, 1⟩]
private theorem harmKer : ∀ k, k < lKer.length →
    ((ground.getAt (BPair.unit, Pos.one, BPair.unit) lKer k).1).oneValue
        BPair.unit
      ∨ ((ground.getAt (BPair.unit, Pos.one, BPair.unit) lKer k).1).oneValue
          (BPair.ofPos (ground.getAt (Pos.one, Pos.one) wsKer k).1) :=
  eucRead_arm 1 1 2 1 (posOfSucc 2) lKer wsKer hwKer

private abbrev hiFoldKer (V : Mat) : Prop :=
  (minor id2.val * minor id2.val
      * dotP xK (matVec (matPow V 2 3) yK)).oneValue
    (dotP (split.vDiagL (matPow V 2 3) id2)
      (List.zipWith (· * ·) (matVec id2.val xK) (matVec id2.val yK)))

private abbrev loFoldKer : Prop :=
  (minor id2.val * minor id2.val
      * dotP xK (matVec (matPow lwKer 2 3) yK)).oneValue
    (dotP (split.vDiagL (matPow lwKer 2 3) id2)
      (List.zipWith (· * ·) (matVec id2.val xK) (matVec id2.val yK)))

example : hiFoldKer vwKer := by decide +kernel
example : (dotP xK (matVec (matPow vwKer 2 3) yK)).oneValue
    (BPair.ofPos 4833) := by decide +kernel
example : hiFoldKer vwKer :=
  (euc_hi_fold etKer id2 id2 lKer hdKer 1 1 15 2 wsKer harmKer vwKer hVsKer
    hVKer xK yK rfl rfl).1
example : loFoldKer := by decide +kernel
example : (dotP xK (matVec (matPow lwKer 2 3) yK)).oneValue
    (BPair.ofPos 29) := by decide +kernel
example : loFoldKer :=
  (euc_lo_fold etKer id2 id2 lKer hdKer 1 1 2 1 3 2 wsKer hwKer lwKer hLsKer
    hLKer xK yK rfl rfl).1

/-- The four root entries at the two arms, each pinned at its
clearing. -/
private abbrev hiPinKer (j : Nat) (nj : BPair) : Prop :=
  (ground.bpow (BPair.ofPos (posOfSucc 2 * ((1 : Pos) * 1)) + nj.scale 1) 3
      * ground.getAt BPair.unit
          (split.vDiagL (matPow vwKer 2 3) id2) j).oneValue
    (ground.bpow (BPair.ofPos ((posOfSucc 2 * ((1 : Pos) * 1)) * 15)) 3
      * ((⟨2, 1⟩ : BPair) * BPair.ofPos 1))

private abbrev loPinKer (j : Nat) (g : Pos) : Prop :=
  (ground.bpow (BPair.ofPos (posOfSucc 2 * ((1 : Pos) * 1))) 3
      * ground.getAt BPair.unit
          (split.vDiagL (matPow lwKer 2 3) id2) j).oneValue
    (ground.bpow (BPair.ofPos (g * 3)) 3
      * ((⟨2, 1⟩ : BPair) * BPair.ofPos 1))

example : hiPinKer 0 BPair.unit := by decide +kernel
example : hiPinKer 1 ⟨3, 1⟩ := by decide +kernel
example : loPinKer 0 3 := by decide +kernel
example : loPinKer 1 1 := by decide +kernel
example : hiPinKer 0 BPair.unit :=
  (euc_hi_fold etKer id2 id2 lKer hdKer 1 1 15 2 wsKer harmKer vwKer hVsKer
    hVKer xK yK rfl rfl).2 0 (by decide +kernel) BPair.unit ⟨2, 1⟩ 1 rfl
example : hiPinKer 1 ⟨3, 1⟩ :=
  (euc_hi_fold etKer id2 id2 lKer hdKer 1 1 15 2 wsKer harmKer vwKer hVsKer
    hVKer xK yK rfl rfl).2 1 (by decide +kernel) ⟨3, 1⟩ ⟨2, 1⟩ 1 rfl
example : loPinKer 0 3 :=
  (euc_lo_fold etKer id2 id2 lKer hdKer 1 1 2 1 3 2 wsKer hwKer lwKer hLsKer
    hLKer xK yK rfl rfl).2 0 (by decide +kernel) BPair.unit ⟨2, 1⟩ 1 rfl
example : loPinKer 1 1 :=
  (euc_lo_fold etKer id2 id2 lKer hdKer 1 1 2 1 3 2 wsKer hwKer lwKer hLsKer
    hLKer xK yK rfl rfl).2 1 (by decide +kernel) ⟨3, 1⟩ ⟨2, 1⟩ 1 rfl

/-! ## The families' Grams at the probes -/

private def probes : List (List BPair) := [xK, yK]

example : matOneValue (famGram (matPow vwKer 2 3) probes)
    [[⟨4105, 1⟩, ⟨4834, 1⟩], [⟨4834, 1⟩, ⟨6292, 1⟩]] := by decide +kernel
example : splitRead (famGram (matPow vwKer 2 3) probes)
    (mkSplit 2 (famGram (matPow vwKer 2 3) probes)) := by decide +kernel
example : psdAt (mkSplit 2 (famGram (matPow vwKer 2 3) probes)) := by
  decide +kernel
example : psdAt (mkSplit 2 (famGram (matPow vwKer 2 3) probes)) :=
  family_hi_psd etKer id2 id2 lKer hdKer 1 1 15 2 wsKer harmKer vwKer hVsKer
    hVKer probes (by decide +kernel) _ (by decide +kernel)
example : splitRead (famGram (matPow lwKer 2 3) probes)
    (mkSplit 2 (famGram (matPow lwKer 2 3) probes)) := by decide +kernel
example : psdAt (mkSplit 2 (famGram (matPow lwKer 2 3) probes)) := by
  decide +kernel
example : psdAt (mkSplit 2 (famGram (matPow lwKer 2 3) probes)) :=
  family_lo_psd etKer id2 id2 lKer hdKer 1 1 2 1 3 2 wsKer hwKer lwKer hLsKer
    hLKer probes (by decide +kernel) _ (by decide +kernel)

/-! ## The binders at their forges -/

/-- The certificate's gap witness is load-bearing at the lower
family: the forged witness `(2, 2)` refuses the certificate and parts
the root pin. -/
example : ¬ eucRead 1 1 2 1 (posOfSucc 2) lOne [(2, 2)] := by decide +kernel
example : ¬ loPinOne 2 3 := by decide +kernel

/-- The upper solve identity refuses at the clearing `4` and its pin
parts there; at an upper witness off the congruence's diagonal the
solve identity holds at no clearing and the fold parts outright. -/
example : ¬ elim.matOneValue
    (matAdd (inertia.matScale (posOfSucc 2 * 1) vwOne)
      (inertia.matScale 1 (matMul etOne vwOne)))
    (inertia.matScale ((posOfSucc 2 * 1) * 4) (idMat 1)) := by decide +kernel
example : ¬ hiPinOne 4 := by decide +kernel

private def vwOff : Mat := [[⟨16, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨10, 1⟩]]

example : ¬ elim.matOneValue
    (matAdd (inertia.matScale (posOfSucc 2 * 1) vwOff)
      (inertia.matScale 1 (matMul etKer vwOff)))
    (inertia.matScale ((posOfSucc 2 * 1) * 15) (idMat 2)) := by decide +kernel
example : ¬ hiFoldKer vwOff := by decide +kernel

/-- The lower solve identity refuses at the clearing `4` and its pin
parts there. -/
example : ¬ elim.matOneValue
    (matAdd (inertia.matScale (posOfSucc 2 * 1) lwOne)
      (inertia.matScale (1 * 4) etOne))
    (inertia.matScale ((posOfSucc 2 * 1) * 4) (idMat 1)) := by decide +kernel
example : ¬ loPinOne 1 4 := by decide +kernel

/-- The split certificate refuses at the forged scale `2`, and both
pins part at the doubled weight. -/
private def lTwo : List (BPair × Pos × BPair) := [(⟨3, 1⟩, 1, ⟨3, 1⟩)]

example : ¬ split.diagRead etOne (idMat 1) tOne tOne lTwo := by decide +kernel
example : eucRead 1 1 2 1 (posOfSucc 2) lTwo wsOne := by decide +kernel
example : ¬ (ground.bpow (BPair.ofPos (posOfSucc 2 * ((1 : Pos) * 1))
      + (⟨3, 1⟩ : BPair).scale 1) 3
    * ground.getAt BPair.unit
        (split.vDiagL (matPow vwOne 1 3) tOne) 0).oneValue
    (ground.bpow (BPair.ofPos ((posOfSucc 2 * ((1 : Pos) * 1)) * 5)) 3
      * ((⟨3, 1⟩ : BPair) * BPair.ofPos 1)) := by decide +kernel
example : ¬ (ground.bpow (BPair.ofPos (posOfSucc 2 * ((1 : Pos) * 1))) 3
    * ground.getAt BPair.unit
        (split.vDiagL (matPow lwOne 1 3) tOne) 0).oneValue
    (ground.bpow (BPair.ofPos ((1 : Pos) * 3)) 3
      * ((⟨3, 1⟩ : BPair) * BPair.ofPos 1)) := by decide +kernel

/-- The certificate's arm is `thm:groundreads`(v)'s frame at the fold
and the pin: at the gap `[-1]` the upper witness `[3]` solves at the
clearing `2`, the arm refuses at the negative root, and the fold with
the pin reads outright. -/
private def etNeg : Mat := [[⟨1, 2⟩]]
private def lNeg : List (BPair × Pos × BPair) := [(⟨1, 2⟩, 1, ⟨2, 1⟩)]

example : split.diagRead etNeg (idMat 1) tOne tOne lNeg := by decide +kernel
example : ¬ eucRead 1 1 2 1 (posOfSucc 2) lNeg wsOne := by decide +kernel
example : ¬ (((⟨1, 2⟩ : BPair).oneValue BPair.unit)
    ∨ ((⟨1, 2⟩ : BPair).oneValue (BPair.ofPos 2))) := by decide +kernel
example : elim.matOneValue
    (matAdd (inertia.matScale (posOfSucc 2 * 1) vwOne)
      (inertia.matScale 1 (matMul etNeg vwOne)))
    (inertia.matScale ((posOfSucc 2 * 1) * 2) (idMat 1)) := by decide +kernel
example : (ground.bpow (BPair.ofPos (posOfSucc 2 * ((1 : Pos) * 1))
      + (⟨1, 2⟩ : BPair).scale 1) 3
    * ground.getAt BPair.unit
        (split.vDiagL (matPow vwOne 1 3) tOne) 0).oneValue
    (ground.bpow (BPair.ofPos ((posOfSucc 2 * ((1 : Pos) * 1)) * 2)) 3
      * ((⟨2, 1⟩ : BPair) * BPair.ofPos 1)) := by decide +kernel

/-- The arm is load-bearing at the family's Gram: at the gap `[-5]`
the upper witness `[-3]` solves at the clearing `2`, the arm refuses,
and the family's Gram at the one probe reads `-27`, its split
counting a reversal. -/
private def etM5 : Mat := [[⟨1, 6⟩]]
private def lM5 : List (BPair × Pos × BPair) := [(⟨1, 6⟩, 1, ⟨2, 1⟩)]
private def vwM5 : Mat := [[⟨1, 4⟩]]

example : split.diagRead etM5 (idMat 1) tOne tOne lM5 := by decide +kernel
example : ¬ (((⟨1, 6⟩ : BPair).oneValue BPair.unit)
    ∨ ((⟨1, 6⟩ : BPair).oneValue (BPair.ofPos 2))) := by decide +kernel
example : elim.matOneValue
    (matAdd (inertia.matScale (posOfSucc 2 * 1) vwM5)
      (inertia.matScale 1 (matMul etM5 vwM5)))
    (inertia.matScale ((posOfSucc 2 * 1) * 2) (idMat 1)) := by decide +kernel
example : matOneValue (famGram (matPow vwM5 1 3) [xP]) [[⟨1, 28⟩]] := by
  decide +kernel
example : splitRead (famGram (matPow vwM5 1 3) [xP])
    (mkSplit 1 (famGram (matPow vwM5 1 3) [xP])) := by decide +kernel
example : ¬ psdAt (mkSplit 1 (famGram (matPow vwM5 1 3) [xP])) := by
  decide +kernel

/-- The certificate's cap is `thm:groundreads`(v)'s frame at the lower
family: the cap `1` refuses the certificate while the fold and the
pins, free of the cap, read outright. -/
example : ¬ eucRead 1 1 1 1 (posOfSucc 2) lOne wsOne := by decide +kernel

/-- The probes' orders are the matched-list frame: at a probe one
member short or one member long the fold truncates at the shorter
operand and reads outright. -/
example : (minor id2.val * minor id2.val
      * dotP [(⟨2, 1⟩ : BPair)] (matVec (matPow vwKer 2 3) yK)).oneValue
    (dotP (split.vDiagL (matPow vwKer 2 3) id2)
      (List.zipWith (· * ·) (matVec id2.val [(⟨2, 1⟩ : BPair)])
        (matVec id2.val yK))) := by decide +kernel
example : (minor id2.val * minor id2.val
      * dotP [(⟨2, 1⟩ : BPair), ⟨2, 1⟩, ⟨2, 1⟩]
          (matVec (matPow vwKer 2 3) yK)).oneValue
    (dotP (split.vDiagL (matPow vwKer 2 3) id2)
      (List.zipWith (· * ·)
        (matVec id2.val [(⟨2, 1⟩ : BPair), ⟨2, 1⟩, ⟨2, 1⟩])
        (matVec id2.val yK))) := by decide +kernel

/-! ## The moment solve -/

/-- The solve at the head: the adjugate against the data reads the
moment vector at the determinant `4`. -/
private abbrev solveRead (p1 β : BPair) (psi : List BPair) (K : Nat) : Prop :=
  poly.oneValue
    (matVec (adjM (momentfold.momSys K pH2 p1 (BPair.ofNat 2) β))
      (momentfold.momRhs psi (BPair.ofNat 3) K))
    (vecScale (detL (momentfold.momSys K pH2 p1 (BPair.ofNat 2) β))
      (momentfold.momVec psi K))

set_option maxRecDepth 100000 in
example : solveRead (BPair.ofNat 6) (BPair.ofNat 3) psiH 1 := by decide +kernel
set_option maxRecDepth 100000 in
example : (detL (momentfold.momSys 1 pH2 (BPair.ofNat 6) (BPair.ofNat 2)
    (BPair.ofNat 3))).oneValue (BPair.ofNat 4) := by decide +kernel
example : solveRead (BPair.ofNat 6) (BPair.ofNat 3) psiH 1 :=
  moment_solve aH bH psiH pH2 (BPair.ofNat 6) (BPair.ofNat 2) (BPair.ofNat 3) 1
    readH profH bondH (Nat.le_refl 1)

/-- The bond datum, the profile's linear constant and the ground each
refuse their read and part the solve. -/
example : ¬ momentfold.constBond bH (BPair.ofNat 4) := by decide +kernel
set_option maxRecDepth 100000 in
example : ¬ solveRead (BPair.ofNat 6) (BPair.ofNat 4) psiH 1 := by
  decide +kernel
example : ¬ momentfold.diagProf aH pH2 (BPair.ofNat 5) (BPair.ofNat 2) := by
  decide +kernel
set_option maxRecDepth 100000 in
example : ¬ solveRead (BPair.ofNat 5) (BPair.ofNat 3) psiH 1 := by
  decide +kernel

private def psiX : List BPair := [BPair.ofNat 6, BPair.ofNat 4, BPair.ofNat 3]

example : ¬ momentfold.recRead aH bH psiX := by decide +kernel
set_option maxRecDepth 100000 in
example : ¬ solveRead (BPair.ofNat 6) (BPair.ofNat 3) psiX 1 := by
  decide +kernel

/-- The degree floor is the square system's shape frame
(`momentfold.momSys_len`): at the vacant degree the read holds at the
padded rows. -/
example : ¬ (1 ≤ 0) := by decide +kernel
set_option maxRecDepth 100000 in
example : solveRead (BPair.ofNat 6) (BPair.ofNat 3) psiH 0 := by decide +kernel
