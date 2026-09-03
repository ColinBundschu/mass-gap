import MassGap.Cornerblock
/-!
The check module for `lem:cornerpivot` (vii)'s ball tier, the
center family the battery's shared certificate datum: the constant
families at the center three, witness a third and image
eight-thirds over the unit bond and gram, the ratio pairs
`λ = 1/2`, `y0 = 2`, `ρ = 2/3`, `ρ∘ = 11/30`, `λ∘ = 2/3`.  The
one-depth transport (`ball_step_of`) rides the three-slab chain
`tridiag(3,3,3; 1,1)`'s slab step at the pivots `(21/8, 8/3, 3)`
and the family's evaluated center, with the modulus refusal at the
deepened center `6` — the defect capped at four, the modulus
seventeen against four parting, the conclusion at minus eight
against minus twenty-seven — and the member-symmetry binder's
load-bearing record at the order-two unbalanced center
`diag(100, 2)`: the antisymmetric bond deviation stands every
co-binder while the transported ball parts at `100/201` against
the radius `[1 : 1000]`.  The chain's stated splits are isolated
at the lied certificate list and the forged head pivot, each
parting the fold at one; the seed's cap is isolated at the
negative one-slab chain `A = -2`, the deviation `-5` outside the
radius.  The compression lifts (`strict_lift`, `cap_lift`): the
mixed block `[[0,1],[1,0]]` compressed along `(1, -1)` occupies
the count at one and `diag(-1, -2)` at the identity compression
occupies it at two, the tie, the strict read and the discriminant
refused in turn.  The rebound (`crossing_rebound`,
`rebound_floor`): the order-one crossing `-2` at its split's one
lower unit reads the display at eight against twelve with the
witness, the join and the split parting it in turn, and the
order-two crossing `diag(-2, 3)` reads the transfer occupied at
three with the display tight at four; the seed floor is refused
three ways, the transfer's cap at two against one, the repaired
pair's seed comparison at six against five, and the chain's own
crossing at the forged diagonal floor `(9, 1)`.  The dominance
tail (`domRead`, `domTail_psd`, `domTail_cross`): the three-slab
chain `tridiag(3, 1, 2; 1, 2)` runs the pivots `(4, -1, 2)` with
the crossing at the middle pivot and one depth of tail, the tail's
split reading the upper side throughout and the crossing's split
at the floor list's own position; the dominance floors are
isolated at the four-slab chain `(0, 1, 2, 3; 1, 1, 3)` whose
deepest floor lies at nine over the vacant diagonal, the count
parting at two against one; the crossing count at the
crossing-free chain `tridiag(3, 3, 3; 1, 2)`, the pivots
`(12/5, 5/3, 3)` all positive with the count parting at nought
against one; and the assembled datum's split at the forged leading
entry.  The family's walked segment (`famChainRead`,
`famChain_psd`) reads deep-first over the depth range at the
scale one against the clearing two hundred, every one of the ten
conjuncts refusal-isolated with the depth orientation pinned at a
depth-varying diagonal family — the deep-first read decides true
and the shallow-first spelling refuses — and the seed handover
isolated on both arms at two forged centers.  The chain's count
closes at the certificate (`famChainCount`): the whole chain
`tridiag(3, 2, 3; 1, 3)` at the order-one crossing and the
order-four chain at the order-two crossing `diag(-1, 2)` each
close the assembled datum's count at one through the theorem,
decided raw beside it, the walked segment the boundary slab at
the family's own read.
-/
set_option maxHeartbeats 4000000

open ground poly elim inertia greenprod spectator cornerpivot

private def gW : Mat := [[⟨2, 1⟩]]
private def spK : Split 1 := ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩
private def spOne (a : BPair) : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one a], 0, rfl⟩

/-! Clause (vii)'s center family, the battery's shared certificate
datum: the constant families at the center three (the matrix
twenty-four hundred at the clearing eight hundred), the witness a
third and the image eight-thirds, the ratio pairs `λ = 1/2`,
`y0 = 2`, `ρ = 2/3`, `ρ∘ = 11/30` and `λ∘ = 2/3` at the two
identities `2·(2·(2·3)) = 24 = 1·((2·3 + 2·1)·3)` and
`11·27 + 4·60 = 537 ≤ 540`, and the unit bond and gram. -/

private def c3P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 3]], ([] : poly.PPoly))
private def c4P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 4]], ([] : poly.PPoly))
private def c12P : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 12]], ([] : poly.PPoly))
private def c1P : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 1]], ([] : poly.PPoly))
private def bx1 (f1L : Nat) (K : Nat) : BoxCert :=
  ⟨⟨BPair.ofNat 1, 2⟩, ⟨BPair.ofNat 2, 1⟩, [], [], [],
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat f1L, BPair.unit, BPair.ofNat 1, BPair.unit, K⟩
private def c8P : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 8]], ([] : poly.PPoly))

private def wB : elim.Mat := [[BPair.ofNat 1]]
private def wG : elim.Mat := [[BPair.ofNat 1]]
private def wAf : List (List (poly.PPoly × poly.PPoly)) := [[c3P]]
private def wCf : PfMQ := ([[c12P]], c4P)
private def wWf : PfMQ := ([[c1P]], c3P)
private def wIf : PfMQ := ([[c8P]], c3P)
private def wFam : CenterFam :=
  ⟨1, wAf, wCf, wWf, wIf, (1, 2), (2, 1), (2, 3), (11, 30),
   (2, 3), (BPair.ofNat 1, 200),
   [bx1 1 1], [bx1 1 1], [bx1 1 1], [bx1 1 1],
   bx1 1 0, bx1 1 0, bx1 1 0⟩

example : famRead wFam wB wG := by decide +kernel

/-! The chain's data: the slabs `A = 3` at the bonds `B = 1` and
the pivots `(21/8, 8/3, 3)` with the witnesses `(3/8, 1/3)` — the
family walk below reads them at the center family's own evaluated
centers. -/

private def aC : Mat := [[⟨4, 1⟩]]
private def bC : Mat := [[⟨2, 1⟩]]
private def x0C : MatQ := ([[⟨22, 1⟩]], 8)
private def xmC : MatQ := ([[⟨9, 1⟩]], 3)
private def ycC : MatQ := ([[⟨4, 1⟩]], 1)
private def cxC : MatQ := ([[⟨4, 1⟩]], 8)
private def ccC : MatQ := ([[⟨2, 1⟩]], 3)

private def chDiag : List Mat := [aC, aC, aC]
private def chOff : List Mat := [bC, bC]
private def chXs : List MatQ := [x0C, xmC, ycC]
private def chRs : List MatQ := [cxC, ccC]
example : tailRead chDiag chOff chXs chRs [1, 1, 1] := by decide +kernel

/-! The one-depth transport at the chain's slab `0 → 1` step: the
member `8/3` about the center `3` at the radius one carries to the
deeper pivot `21/8` about the same center, the contraction `λ = 1/3`
at the modulus `λ∘ = 1/2` — the deviation `-3/8` priced at minus
three against eight and minus eight against minus three. -/

example : capQ (devQ xmC ycC) gW 1 1 (spOne ⟨5, 1⟩) (spOne ⟨3, 1⟩) := by
  decide +kernel

example : (quadForm (devQ x0C ycC).1 [⟨2, 1⟩]).scale 1
    ≤ (quadForm gW [⟨2, 1⟩]).scale (1 * (devQ x0C ycC).2) := by
  decide +kernel
example : ((quadForm gW [⟨2, 1⟩]).scale (1 * (devQ x0C ycC).2)).swap
    ≤ (quadForm (devQ x0C ycC).1 [⟨2, 1⟩]).scale 1 := by decide +kernel

example : (∀ w : List BPair, w.length = 1 →
      (quadForm (devQ x0C ycC).1 w).scale 1
        ≤ (quadForm gW w).scale (1 * (devQ x0C ycC).2))
    ∧ (∀ w : List BPair, w.length = 1 →
      ((quadForm gW w).scale (1 * (devQ x0C ycC).2)).swap
        ≤ (quadForm (devQ x0C ycC).1 w).scale 1) :=
  ball_step_of (o := 1) (o' := 1) xmC x0C ycC xmC ycC cxC ccC
    aC bC gW gW 1 3 2 1 1 1 1 2 1 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (fun w hw => cap_hi (devQ xmC ycC) gW 1 1 (spOne ⟨5, 1⟩)
      (spOne ⟨3, 1⟩) (by decide +kernel) w hw)
    (fun w hw => cap_lo (devQ xmC ycC) gW 1 1 (spOne ⟨5, 1⟩)
      (spOne ⟨3, 1⟩) (by decide +kernel) w hw)
    (floor_all ycC gW 2 1 1 1 spK (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
    (contract_all (transfer ccC) gW gW 1 3 spK (by decide +kernel))
    (by decide +kernel)
    (fun h => Nat.noConfusion h)
    (fun w hw => cap_hi (devQ xmC ycC) gW 1 2 (spOne ⟨6, 1⟩)
      (spOne ⟨2, 1⟩) (by decide +kernel) w hw)
    (fun w hw => cap_lo (devQ xmC ycC) gW 1 2 (spOne ⟨6, 1⟩)
      (spOne ⟨2, 1⟩) (by decide +kernel) w hw)
    (by decide +kernel) (by decide +kernel)

/-! The transport's modulus binder, isolated at the deepened center
`6`: the defect `-10/3` still caps at four, the modulus parts at
seventeen against four, and the conclusion parts beside it at minus
eight against minus twenty-seven. -/

private def ycdF : MatQ := ([[⟨7, 1⟩]], 1)

example : capQ (devQ xmC ycdF) gW 4 1 (spOne ⟨23, 1⟩)
    (spOne ⟨3, 1⟩) := by decide +kernel
example : ¬ (4 * ((2 * 2) * 1) + (1 * 1) * (1 * 1)
    ≤ 1 * (1 * (2 * 2))) := by decide +kernel
example : ¬ (((quadForm gW [⟨2, 1⟩]).scale
      (1 * (devQ x0C ycdF).2)).swap
    ≤ (quadForm (devQ x0C ycdF).1 [⟨2, 1⟩]).scale 1) := by
  decide +kernel

/-! The transport's member-symmetry record at order two: the
unbalanced center `diag(100, 2)` at the floor `y0 = 1` and radius
`[1 : 1000]`, the member the center joined to the antisymmetric
bond deviation whose form reads its own swap — unit-valued at
every vector, inside every radius — while the transported ball
parts at the image deviation `100/201`, the refused transpose read
beside the parted conclusion with every co-binder standing. -/

private def u2 : BPair := BPair.unit
private def gI2 : Mat := idMat 2
private def g4C : Mat := [[⟨5, 1⟩]]
private def ycV : MatQ := ([[⟨101, 1⟩, u2], [u2, ⟨3, 1⟩]], 1)
private def xV : MatQ := ([[⟨101, 1⟩, ⟨2, 1⟩], [⟨1, 2⟩, ⟨3, 1⟩]], 1)
private def ccV : MatQ := ([[⟨2, 1⟩], [u2]], 1)
private def cxV : MatQ := ([[⟨201, 1⟩], [⟨101, 1⟩]], 201)
private def bV : Mat := [[⟨101, 1⟩, u2]]
private def aV : Mat := [[⟨201, 1⟩]]
private def ymidV : MatQ := ([[⟨101, 1⟩]], 1)
private def xdpV : MatQ := ([[⟨20201, 1⟩]], 201)
private def dKV : Mat := [[u2, ⟨2, 1⟩], [⟨1, 2⟩, u2]]
private def spFV : Split 2 :=
  mkSplit 2 (siteDatum (matScale (1 * 1000) ycV.1)
    (matScale (1 * (1 * 1000 + 1 * 1)) gI2))

private theorem dKVSwap (w : List BPair) (hw : w.length = 2) :
    (quadForm dKV w).oneValue (quadForm dKV w).swap :=
  BPair.oneValue_trans
    (BPair.oneValue_symm
      (elim.dotN_transpose_flip dKV 2 (by decide +kernel) w w hw hw))
    (BPair.oneValue_trans
      (elim.dotN_matVec_congrM (transposeM dKV) (matSwap dKV) w w
        (by decide +kernel))
      (inertia.quadForm_swap dKV w))

private theorem idPsdV (w : List BPair) (hw : w.length = 2) :
    BPair.unit ≤ quadForm gI2 w :=
  ground.leB_of_not_lt
    (inertia.psd_all gI2 (mkSplit 2 gI2)
      (by decide +kernel) (by decide +kernel) w hw)

private theorem dKVUnitLe (w : List BPair) (hw : w.length = 2) :
    BPair.unit ≤ quadForm dKV w :=
  ground.unitLeOfSwap (Or.inl (BPair.oneValue_symm (dKVSwap w hw)))

private theorem dKVLeUnit (w : List BPair) (hw : w.length = 2) :
    quadForm dKV w ≤ BPair.unit :=
  ground.leB_swap
    (ground.unitLeOfSwap (z := (quadForm dKV w).swap)
      (Or.inl (dKVSwap w hw)))

private theorem qDV (w : List BPair) :
    (quadForm (devQ xV ycV).1 w).oneValue (quadForm dKV w) :=
  elim.dotN_matVec_congrM _ _ w w (by decide +kernel)

private theorem devVHi : ∀ w : List BPair, w.length = 2 →
    (quadForm (devQ xV ycV).1 w).scale 1000
      ≤ (quadForm gI2 w).scale (1 * (devQ xV ycV).2) :=
  fun w hw =>
    ground.leB_trans
      (ground.leB_scale
        (ground.leB_congr_left (BPair.oneValue_symm (qDV w))
          (dKVLeUnit w hw)) 1000)
      (ground.leB_congr_left (ground.unitScale 1000)
        (ground.unitLeScale (1 * (devQ xV ycV).2) (idPsdV w hw)))

private theorem devVLo : ∀ w : List BPair, w.length = 2 →
    ((quadForm gI2 w).scale (1 * (devQ xV ycV).2)).swap
      ≤ (quadForm (devQ xV ycV).1 w).scale 1000 :=
  fun w hw =>
    ground.leB_trans
      (ground.leB_swap
        (ground.unitLeScale (1 * (devQ xV ycV).2) (idPsdV w hw)))
      (ground.leB_trans
        (ground.leB_congr_right (ground.unitScale 1000)
          (ground.leB_refl BPair.unit))
        (ground.leB_scale
          (ground.leB_congr_right (BPair.oneValue_symm (qDV w))
            (dKVUnitLe w hw)) 1000))

example : matOneValue (transposeM ycV.1) ycV.1 := by decide +kernel
example : oneValueQ (mulQ xV cxV) (ofM (transposeM bV)) := by
  decide +kernel
example : oneValueQ (addQ xdpV (mulQ (ofM bV) cxV)) (ofM aV) := by
  decide +kernel
example : oneValueQ (mulQ ycV ccV) (ofM (transposeM bV)) := by
  decide +kernel
example : oneValueQ (addQ ymidV (mulQ (ofM bV) ccV)) (ofM aV) := by
  decide +kernel
example : floorRead ycV gI2 1 1 1 1000 spFV := by decide +kernel
example : contractRead (transfer ccV) gI2 g4C 1 2 spK := by
  decide +kernel
example : capQ (devQ ymidV ymidV) g4C 1 2000 (spOne ⟨5, 1⟩)
    (spOne ⟨5, 1⟩) := by decide +kernel
example : (1 : Pos) * (1001 * (2 * 1000))
    = 1 * ((1 * 1000 + 1 * 1) * 2000) := by decide +kernel
example : (1 : Pos) * ((2000 * 2000) * 1000)
      + (1001 * 1001) * (1 * 2000)
    ≤ 1 * (2000 * (2000 * 2000)) := by decide +kernel
example : ∀ w : List BPair, w.length = 2 →
    (quadForm (devQ xV ycV).1 w).scale 1000
      ≤ (quadForm gI2 w).scale (1 * (devQ xV ycV).2) := devVHi
example : ∀ w : List BPair, w.length = 2 →
    ((quadForm gI2 w).scale (1 * (devQ xV ycV).2)).swap
      ≤ (quadForm (devQ xV ycV).1 w).scale 1000 := devVLo
example : ¬ matOneValue (transposeM xV.1) xV.1 := by decide +kernel
example : ¬ ((quadForm (devQ xdpV ymidV).1 [⟨2, 1⟩]).scale 1000
    ≤ (quadForm g4C [⟨2, 1⟩]).scale
      (1 * (devQ xdpV ymidV).2)) := by decide +kernel

/-! The chain's stated splits at the three pivots
`(21/8, 8/3, 3)`: each split sits at the identity congruence on
its own pivot's block, every block above the sum's unit, so the
slab fold of the reversal counts is the count's unit — the fold
decided raw, the theorem route the family walk below. -/

private def chSps : List ((k : Nat) × Split k) :=
  [⟨1, spOne ⟨22, 1⟩⟩, ⟨1, spOne ⟨9, 1⟩⟩, ⟨1, spOne ⟨4, 1⟩⟩]

example : revListRead chXs chSps := by decide +kernel
example : revFold chSps = 0 := by decide +kernel

/-! The compression lifts at the identity congruence
(`strict_lift`, `cap_lift`): the strict lift's datum is the mixed
block `[[0,1],[1,0]]` compressed along the column `(1, -1)`, whose
compression reads minus two, and the count is occupied at one; the
cap lift's datum is `diag(-1, -2)` at the identity compression, the
two coordinate members reading minus one and minus two with the
vacant cross against the product's quadruple eight, and the count
is occupied at two.  The compression's shape binders (`hPl`, `hPr`)
are the certificate-shape frame at the truncating folds, no refusal
cell of their own.  The refusals name the reads that bite: the tie
at the forged compression minus two against the identity datum's
own two, the strict read at that honest compression, the
discriminant at the datum `diag(-1, 2)` whose product's quadruple
reads minus eight, and the cap's strict read at the identity
datum — each with the count parted beside it. -/

private def liMix : Mat := [[⟨1, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 1⟩]]
private def liId : Mat := [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]]
private def liNeg : Mat := [[⟨1, 2⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨1, 3⟩]]
private def liMxd : Mat := [[⟨1, 2⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩]]
private def liCol : Mat := [[⟨2, 1⟩], [⟨1, 2⟩]]
private def liWn : Mat := [[⟨1, 3⟩]]
private def liWp : Mat := [[⟨3, 1⟩]]
private def liX1 : List BPair := [⟨2, 1⟩]
private def liXa : List BPair := [⟨2, 1⟩, ⟨1, 1⟩]
private def liXb : List BPair := [⟨1, 1⟩, ⟨2, 1⟩]

private def liSpMix : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two ⟨1, 1⟩ ⟨2, 1⟩ ⟨1, 1⟩], 0, rfl⟩
private def liSpId : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨2, 1⟩, .one ⟨2, 1⟩], 0, rfl⟩
private def liSpNeg : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 2⟩, .one ⟨1, 3⟩], 0, rfl⟩
private def liSpMxd : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 2⟩, .one ⟨3, 1⟩], 0, rfl⟩

example : splitRead liMix liSpMix := by decide +kernel
example : matOneValue (matMul (transposeM liCol) (matMul liMix liCol))
    liWn := by decide +kernel
example : quadForm liWn liX1 < BPair.unit := by decide +kernel
example : (1 : Nat) ≤ revAt liSpMix := by decide +kernel
example : (1 : Nat) ≤ revAt liSpMix :=
  strict_lift (n := 2) (m := 1) liMix liCol liWn liSpMix liX1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Refusal naming `strict_lift`'s tie: at the identity datum the
column's compression reads two, so the forged compression minus two
parts, and the count parts beside it at the vacant fold. -/
example : splitRead liId liSpId := by decide +kernel
example : ¬ matOneValue (matMul (transposeM liCol) (matMul liId liCol))
    liWn := by decide +kernel
example : quadForm liWn liX1 < BPair.unit := by decide +kernel
example : ¬ ((1 : Nat) ≤ revAt liSpId) := by decide +kernel

/-- Refusal naming `strict_lift`'s strict read: the honest
compression at the identity datum reads two, at or above the sum's
unit, and the count parts beside it. -/
example : matOneValue (matMul (transposeM liCol) (matMul liId liCol))
    liWp := by decide +kernel
example : ¬ (quadForm liWp liX1 < BPair.unit) := by decide +kernel

example : splitRead liNeg liSpNeg := by decide +kernel
example : matOneValue (matMul (transposeM liId) (matMul liNeg liId))
    liNeg := by decide +kernel
example : quadForm liNeg liXa < BPair.unit := by decide +kernel
example : (dotN liXa (matVec liNeg liXb) + dotN liXb (matVec liNeg liXa))
      * (dotN liXa (matVec liNeg liXb) + dotN liXb (matVec liNeg liXa))
    < BPair.ofNat 4 * (quadForm liNeg liXa * quadForm liNeg liXb) := by
  decide +kernel
example : (2 : Nat) ≤ revAt liSpNeg := by decide +kernel
example : (2 : Nat) ≤ revAt liSpNeg :=
  cap_lift (n := 2) (m := 2) liNeg liId liNeg liSpNeg liXa liXb
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Refusal naming `cap_lift`'s discriminant: at the datum
`diag(-1, 2)` the vacant cross reads the sum's unit against the
product's quadruple minus eight, and the count parts at one. -/
example : splitRead liMxd liSpMxd := by decide +kernel
example : matOneValue (matMul (transposeM liId) (matMul liMxd liId))
    liMxd := by decide +kernel
example : quadForm liMxd liXa < BPair.unit := by decide +kernel
example : ¬ ((dotN liXa (matVec liMxd liXb)
        + dotN liXb (matVec liMxd liXa))
      * (dotN liXa (matVec liMxd liXb)
        + dotN liXb (matVec liMxd liXa))
    < BPair.ofNat 4 * (quadForm liMxd liXa * quadForm liMxd liXb)) := by
  decide +kernel
example : ¬ ((2 : Nat) ≤ revAt liSpMxd) := by decide +kernel

/-- Refusal naming `cap_lift`'s strict read: at the identity datum
the leading member reads the sum's unit's upper side while the
discriminant stands, and the count parts at the vacant fold. -/
example : matOneValue (matMul (transposeM liId) (matMul liId liId))
    liId := by decide +kernel
example : ¬ (quadForm liId liXa < BPair.unit) := by decide +kernel
example : (dotN liXa (matVec liId liXb) + dotN liXb (matVec liId liXa))
      * (dotN liXa (matVec liId liXb) + dotN liXb (matVec liId liXa))
    < BPair.ofNat 4 * (quadForm liId liXa * quadForm liId liXb) := by
  decide +kernel
example : ¬ ((2 : Nat) ≤ revAt liSpId) := by decide +kernel

/-- Refusal naming `cap_lift`'s tie: at the identity datum the
identity compression reads the identity, so the forged compression
`diag(-1, -2)` parts while its own two reads stand, and the count
parts at the vacant fold. -/
example : ¬ matOneValue (matMul (transposeM liId) (matMul liId liId))
    liNeg := by decide +kernel
example : quadForm liNeg liXa < BPair.unit := by decide +kernel
example : (dotN liXa (matVec liNeg liXb) + dotN liXb (matVec liNeg liXa))
      * (dotN liXa (matVec liNeg liXb) + dotN liXb (matVec liNeg liXa))
    < BPair.ofNat 4 * (quadForm liNeg liXa * quadForm liNeg liXb) := by
  decide +kernel

/-! Clause (vii)'s rebound at the order-one crossing: the crossing
pivot `-2` at its split's one lower unit, the bond `1`, the
recursion witness `-1/2`, the following diagonal `1` and pivot
`3/2` — the witness and join identities decided, the crossing's
count read one, and the display decided raw and landed through the
theorem, the positive part the withdrawn vacant read at eight
against twelve. -/

private def crXc : MatQ := ([[⟨1, 3⟩]], 1)
private def crSp : Split 1 := spOne ⟨1, 3⟩
private def crB : Mat := [[⟨2, 1⟩]]
private def crR : MatQ := ([[⟨1, 2⟩]], 2)
private def crA : Mat := [[⟨2, 1⟩]]
private def crXf : MatQ := ([[⟨4, 1⟩]], 2)

example : oneValueQ (mulQ crXc crR) (ofM (transposeM crB)) := by
  decide +kernel
example : oneValueQ (addQ crXf (mulQ (ofM crB) crR)) (ofM crA) := by
  decide +kernel
example : splitRead crXc.1 crSp := by decide +kernel
example : revAt crSp = 1 := by decide +kernel

example : minor crSp.T.val * minor crSp.T.val
      * ((quadForm crA [⟨2, 1⟩]).scale
          (crXc.2 * (crXf.2 * (crR.2 * crR.2))))
    ≤ minor crSp.T.val * minor crSp.T.val
        * ((quadForm crXf.1 [⟨2, 1⟩]).scale
            (crXc.2 * (crR.2 * crR.2)))
      + (quadForm (blockMat (posBlocks crSp.blocks) crSp.kern)
          (matVec crSp.Tw.val (matVec crR.1 [⟨2, 1⟩]))).scale
          crXf.2 := by decide +kernel

example : ∀ u : List BPair, u.length = 1 →
    minor crSp.T.val * minor crSp.T.val
        * ((quadForm crA u).scale
            (crXc.2 * (crXf.2 * (crR.2 * crR.2))))
      ≤ minor crSp.T.val * minor crSp.T.val
          * ((quadForm crXf.1 u).scale (crXc.2 * (crR.2 * crR.2)))
        + (quadForm (blockMat (posBlocks crSp.blocks) crSp.kern)
            (matVec crSp.Tw.val (matVec crR.1 u))).scale crXf.2 :=
  crossing_rebound (o := 1) (o' := 1) crXf crXc crR crA crB crSp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Refusal naming the witness identity: the forged witness `2`
with the join repaired at the following pivot `-1` parts the
display at one against minus one, the crossing pivot's read
untransported. -/
private def crR5 : MatQ := ([[⟨3, 1⟩]], 1)
private def crXf5 : MatQ := ([[⟨1, 2⟩]], 1)

example : ¬ oneValueQ (mulQ crXc crR5) (ofM (transposeM crB)) := by
  decide +kernel
example : oneValueQ (addQ crXf5 (mulQ (ofM crB) crR5)) (ofM crA) := by
  decide +kernel
example : ¬ (minor crSp.T.val * minor crSp.T.val
      * ((quadForm crA [⟨2, 1⟩]).scale
          (crXc.2 * (crXf5.2 * (crR5.2 * crR5.2))))
    ≤ minor crSp.T.val * minor crSp.T.val
        * ((quadForm crXf5.1 [⟨2, 1⟩]).scale
            (crXc.2 * (crR5.2 * crR5.2)))
      + (quadForm (blockMat (posBlocks crSp.blocks) crSp.kern)
          (matVec crSp.Tw.val (matVec crR5.1 [⟨2, 1⟩]))).scale
          crXf5.2) := by decide +kernel

/-- Refusal naming the join: the honest witness with the following
pivot forged at `-1` parts the join's sum at minus three halves
against one and the display at four against minus four. -/
example : ¬ oneValueQ (addQ crXf5 (mulQ (ofM crB) crR)) (ofM crA) := by
  decide +kernel
example : ¬ (minor crSp.T.val * minor crSp.T.val
      * ((quadForm crA [⟨2, 1⟩]).scale
          (crXc.2 * (crXf5.2 * (crR.2 * crR.2))))
    ≤ minor crSp.T.val * minor crSp.T.val
        * ((quadForm crXf5.1 [⟨2, 1⟩]).scale
            (crXc.2 * (crR.2 * crR.2)))
      + (quadForm (blockMat (posBlocks crSp.blocks) crSp.kern)
          (matVec crSp.Tw.val (matVec crR.1 [⟨2, 1⟩]))).scale
          crXf5.2) := by decide +kernel

/-- Refusal naming the split: the positive crossing `+2` at the
honest witness and join against the lied split at the lower entry
parts the display at eight against four, the true sandwich's
weight underpriced by the withdrawn read. -/
private def crXc7 : MatQ := ([[⟨3, 1⟩]], 1)
private def crR7 : MatQ := ([[⟨2, 1⟩]], 2)
private def crXf7 : MatQ := ([[⟨2, 1⟩]], 2)

example : oneValueQ (mulQ crXc7 crR7) (ofM (transposeM crB)) := by
  decide +kernel
example : oneValueQ (addQ crXf7 (mulQ (ofM crB) crR7)) (ofM crA) := by
  decide +kernel
example : ¬ splitRead crXc7.1 crSp := by decide +kernel
example : ¬ (minor crSp.T.val * minor crSp.T.val
      * ((quadForm crA [⟨2, 1⟩]).scale
          (crXc7.2 * (crXf7.2 * (crR7.2 * crR7.2))))
    ≤ minor crSp.T.val * minor crSp.T.val
        * ((quadForm crXf7.1 [⟨2, 1⟩]).scale
            (crXc7.2 * (crR7.2 * crR7.2)))
      + (quadForm (blockMat (posBlocks crSp.blocks) crSp.kern)
          (matVec crSp.Tw.val (matVec crR7.1 [⟨2, 1⟩]))).scale
          crXf7.2) := by decide +kernel

/-! The chain's stated splits, isolated: the lied certificate list
at the standing chain refuses its head split against the pivot
`21/8` with the fold parting at one; and the forged head pivot `-2`
at its own honest split refuses the tail recursion's join while the
certificate list and the symmetric diagonal's fold stand, the fold
parting at one — the symmetry fold's own parting record is the
recursion tier's, the asymmetric one-slab seed at the tail walk's
battery. -/

private def spsL : List ((k : Nat) × Split k) :=
  [⟨1, spOne ⟨1, 3⟩⟩, ⟨1, spOne ⟨9, 1⟩⟩, ⟨1, spOne ⟨4, 1⟩⟩]

example : ¬ revListRead chXs spsL := by decide +kernel
example : revFold spsL = 1 := by decide +kernel

private def xsT : List MatQ := [([[⟨1, 3⟩]], 1), xmC, ycC]

example : revListRead xsT spsL := by decide +kernel
example : ¬ tailRead chDiag chOff xsT chRs [1, 1, 1] := by
  decide +kernel
example : symRead chDiag := by decide +kernel

/-! Clause (vii)'s rebound at the order-two crossing, the transfer
occupied and the display tight: the crossing pivot `diag(-2, 3)`
at its split's one lower unit, the identity witness, the bond the
pivot's own read, the following pivot `diag(5, 1)` and diagonal
`diag(3, 4)` — at the vector `(0, 1)` the positive part reads
three, the display reads equal members at four, and the display
with the transfer withdrawn parts at four against one, the
transfer summand's own isolation.  The shape and order binders
(`hk`, `hk'`, `hXf`, `hB`, `hR`) are the certificate-shape frame
at the truncating folds. -/

private def c2Xc : MatQ :=
  ([[⟨1, 3⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨4, 1⟩]], 1)
private def c2Sp : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.one ⟨1, 3⟩, .one ⟨4, 1⟩], 0, rfl⟩
private def c2B : Mat := [[⟨1, 3⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨4, 1⟩]]
private def c2R : MatQ :=
  ([[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], 1)
private def c2A : Mat := [[⟨4, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨5, 1⟩]]
private def c2Xf : MatQ :=
  ([[⟨6, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], 1)
private def c2U : List BPair := [⟨1, 1⟩, ⟨2, 1⟩]

example : oneValueQ (mulQ c2Xc c2R) (ofM (transposeM c2B)) := by
  decide +kernel
example : oneValueQ (addQ c2Xf (mulQ (ofM c2B) c2R)) (ofM c2A) := by
  decide +kernel
example : splitRead c2Xc.1 c2Sp := by decide +kernel
example : revAt c2Sp = 1 := by decide +kernel

example : minor c2Sp.T.val * minor c2Sp.T.val
      * ((quadForm c2A c2U).scale (c2Xc.2 * (c2Xf.2 * (c2R.2 * c2R.2))))
    ≤ minor c2Sp.T.val * minor c2Sp.T.val
        * ((quadForm c2Xf.1 c2U).scale (c2Xc.2 * (c2R.2 * c2R.2)))
      + (quadForm (blockMat (posBlocks c2Sp.blocks) c2Sp.kern)
          (matVec c2Sp.Tw.val (matVec c2R.1 c2U))).scale c2Xf.2 := by
  decide +kernel

example : ¬ (minor c2Sp.T.val * minor c2Sp.T.val
      * ((quadForm c2A c2U).scale (c2Xc.2 * (c2Xf.2 * (c2R.2 * c2R.2))))
    ≤ minor c2Sp.T.val * minor c2Sp.T.val
        * ((quadForm c2Xf.1 c2U).scale (c2Xc.2 * (c2R.2 * c2R.2)))) := by
  decide +kernel

example : ∀ u : List BPair, u.length = 2 →
    minor c2Sp.T.val * minor c2Sp.T.val
        * ((quadForm c2A u).scale (c2Xc.2 * (c2Xf.2 * (c2R.2 * c2R.2))))
      ≤ minor c2Sp.T.val * minor c2Sp.T.val
          * ((quadForm c2Xf.1 u).scale (c2Xc.2 * (c2R.2 * c2R.2)))
        + (quadForm (blockMat (posBlocks c2Sp.blocks) c2Sp.kern)
            (matVec c2Sp.Tw.val (matVec c2R.1 u))).scale c2Xf.2 :=
  crossing_rebound (o := 2) (o' := 2) c2Xf c2Xc c2R c2A c2B c2Sp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! Clause (vii)'s dominance tail at the three-slab chain
`tridiag(3, 1, 2; 1, 2)`: the recursion's pivots `(4, -1, 2)` with
the witnesses `(-1, 1)`, the crossing at the middle pivot `-1` and
the dominance tail one depth deep — the diagonal's floor `(3, 1)`
at the slab `A₀ = 3` and the depth's floor `(2, 1)`, the transfer
pair `(1, 1)` at the crossing's withdrawn diagonal, and the seed
comparison tight at three.  The certificate's pass reads beside the
tier's theorems at it: the tail's stated split reads the upper side
throughout and the crossing's split sits at the floor list's own
position; the count's close at the family is the walked chain
below.  The shape binders (`hk`, `hk'`, `hXf`, `hB`, `hR` and
the comparisons' operand shapes) are the certificate-shape frame at
the truncating folds.  The tail recursion and the pivots'
certificate list are load-bearing at the count's own class: the
lied certificate list against the pivot and the forged head pivot
at its honest split each part the fold at one. -/

private def bA0 : Mat := [[⟨4, 1⟩]]
private def bA1 : Mat := [[⟨2, 1⟩]]
private def bA2 : Mat := [[⟨3, 1⟩]]
private def bB0 : Mat := [[⟨2, 1⟩]]
private def bB1 : Mat := [[⟨3, 1⟩]]
private def bDiag : List Mat := [bA0, bA1, bA2]
private def bOff : List Mat := [bB0, bB1]
private def bNs : List Nat := [1, 1, 1]

private def bX0 : MatQ := ([[⟨5, 1⟩]], 1)
private def bX1 : MatQ := ([[⟨1, 2⟩]], 1)
private def bX2 : MatQ := ([[⟨3, 1⟩]], 1)
private def bXs : List MatQ := [bX0, bX1, bX2]
private def bR0 : MatQ := ([[⟨1, 2⟩]], 1)
private def bR1 : MatQ := ([[⟨2, 1⟩]], 1)
private def bRs : List MatQ := [bR0, bR1]

private def bSps : List ((k : Nat) × Split k) :=
  [⟨1, spOne ⟨5, 1⟩⟩, ⟨1, spOne ⟨1, 2⟩⟩, ⟨1, spOne ⟨3, 1⟩⟩]

/-- The assembled chain's congruence at the columns
`e₀ + e₁ - e₂`, `e₁ - e₂`, `e₂`, the images the recursion's own
pivots. -/
private def bT : Mat :=
  [[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨1, 2⟩, ⟨2, 1⟩]]
private def bTw : Mat :=
  [[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩]]
private def bSP : Split 3 :=
  ⟨⟨bT, rfl⟩, ⟨bTw, rfl⟩,
   [.one ⟨5, 1⟩, .one ⟨1, 2⟩, .one ⟨3, 1⟩], 0, rfl⟩

private def bSpc : (k : Nat) × Split k := ⟨1, spOne ⟨1, 2⟩⟩
private def bSpT : (k : Nat) × Split k := ⟨1, spOne ⟨2, 1⟩⟩
private def bD : DomStep := ⟨1, (3, 1), (2, 1), spK⟩
private def bDs : List DomStep := [bD]
private def bCs : List ((k : Nat) × (Pos × Pos) × Split k) := []


example : tailRead bDiag bOff bXs bRs bNs := by decide +kernel
example : revListRead bXs bSps := by decide +kernel
example : splitRead (assemble bDiag bOff) bSP := by decide +kernel
example : revAt bSP = 1 := by decide +kernel
example : domRead bSpc bSpT 1 1 bDiag bOff bXs bRs bNs bDs bCs := by
  decide +kernel

/-! The tier's two theorems at the certificate: the tail's stated
splits read the upper side throughout and the crossing's split sits
at the floor list's own position — each decided raw beside its
theorem route; the count's close is the family tier's below. -/

example : ∀ i, i < bDs.length → ∀ s : (k : Nat) × Split k,
    splitRead (ground.getAt dM bXs i).1 s.2 → psdAt s.2 :=
  domTail_psd bSpc bSpT 1 1 bDiag bOff bXs bRs bNs bDs bCs
    (by decide +kernel) (by decide +kernel)
example : psdAt (spOne ⟨5, 1⟩) := by decide +kernel

example : splitRead (ground.getAt dM bXs bDs.length).1 bSpc.2 :=
  domTail_cross bSpc bSpT 1 1 bDiag bOff bXs bRs bNs bDs bCs
    (by decide +kernel)
example : splitRead bX1.1 (spOne ⟨1, 2⟩) := by decide +kernel

/-! The rebound's seed floor (`rebound_floor`) at the chain's own
crossing: the diagonal's floor `(3, 1)` reads the slab three
against the coordinates' fold of squares, the transfer's cap
`(1, 1)` reads the withdrawn diagonal vacant against the unit, and
the seed comparison closes tight at three — the following pivot
four at or beyond twice the fold, decided raw at `u = [1]` beside
the theorem route.  The comparisons' operand shapes are the
certificate-shape frame at the truncating folds. -/

private def bU : List BPair := [⟨2, 1⟩]

private theorem bDfloorR : ∀ u : List BPair, u.length = 1 →
    (dotN u u).scale 3 ≤ (quadForm bA0 u).scale 1 :=
  fun u hu =>
    ground.leB_congr
      (BPair.oneValue_trans (quadForm_scale 3 (idMat 1) u)
        (BPair.scale_congr 3 (dotN_congrR u _ _ (matVec_idMat 1 u hu))))
      (quadForm_scale 1 bA0 u)
      (le_all (matScale 3 (idMat 1)) (matScale 1 bA0) spK
        (by decide +kernel) (by decide +kernel) (by decide +kernel) u hu)

private theorem bTcapR : ∀ u : List BPair, u.length = 1 →
    (quadForm (blockMat (posBlocks bSpc.2.blocks) bSpc.2.kern)
        (matVec (matMul bSpc.2.Tw.val bR0.1) u)).scale 1
      ≤ minor bSpc.2.T.val * minor bSpc.2.T.val
          * ((dotN u u).scale (1 * (bX1.2 * (bR0.2 * bR0.2)))) :=
  fun u hu =>
    ground.leB_congr
      (BPair.oneValue_trans
        (quadForm_scale 1
          (matMul (transposeM (matMul bSpc.2.Tw.val bR0.1))
            (matMul (blockMat (posBlocks bSpc.2.blocks) bSpc.2.kern)
              (matMul bSpc.2.Tw.val bR0.1))) u)
        (BPair.scale_congr 1
          (BPair.oneValue_symm
            (congQuad (blockMat (posBlocks bSpc.2.blocks) bSpc.2.kern)
              (matMul bSpc.2.Tw.val bR0.1) 1 1 (by decide +kernel)
              (rowsLen_of_sqAt
                (show sqAt (matMul bSpc.2.Tw.val bR0.1) 1 by
                  decide +kernel))
              (by decide +kernel) u hu))))
      (BPair.oneValue_trans
        (quadForm_scaleB
          ((minor bSpc.2.T.val * minor bSpc.2.T.val)
            * BPair.ofPos (1 * (bX1.2 * (bR0.2 * bR0.2)))) (idMat 1) u)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (dotN_congrR u _ _ (matVec_idMat 1 u hu)))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.ofPos_scale (1 * (bX1.2 * (bR0.2 * bR0.2)))
                (dotN u u))))))
      (le_all
        (matScale 1 (matMul
          (transposeM (matMul bSpc.2.Tw.val bR0.1))
          (matMul (blockMat (posBlocks bSpc.2.blocks) bSpc.2.kern)
            (matMul bSpc.2.Tw.val bR0.1))))
        (matScaleB
          ((minor bSpc.2.T.val * minor bSpc.2.T.val)
            * BPair.ofPos (1 * (bX1.2 * (bR0.2 * bR0.2))))
          (idMat 1))
        bSpT.2 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) u hu)

example : (dotN bU bU).scale (2 * bX0.2)
    ≤ (quadForm bX0.1 bU).scale 1 := by decide +kernel

example : ∀ u : List BPair, u.length = 1 →
    (dotN u u).scale (2 * bX0.2) ≤ (quadForm bX0.1 u).scale 1 :=
  rebound_floor (o := 1) (o' := 1) bX0 bX1 bR0 bA0 bB0 bSpc.2
    3 1 1 1 2 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    bDfloorR bTcapR (by decide +kernel)

/-! The seed floor's isolating refusals.  The first two sit at the
order-two crossing `diag(-1, 2)` with the witness `(0, 1)ᵀ`, the
bond `(0, 2)`, the slab five and the following pivot three — the
witness and join identities and the crossing's split standing, the
transfer's image `diag(0, 2)` reading two at `u = [1]`.  The
transfer's cap at the pair `(1, 1)` parts at two against one with
the diagonal's floor `(3, 1)`-tight at five and the seed comparison
closing at five, and the conclusion parts beside it at four against
three; at the pair `(2, 1)` the cap closes tight at two while the
seed comparison at the floor `(4, 1)` parts at six against five,
the conclusion parting beside it again.  The third sits at the
chain's own crossing with the diagonal's floor forged to `(9, 1)`:
the floor parts at nine against three while the transfer's cap
reads the withdrawn diagonal vacant and the seed comparison closes
at nine, the conclusion parting at eight against four.  The fourth
and fifth sit at the band-one crossing's own fixture with the
diagonal floor `(1, 1)` tight, the transfer's cap `(1, 4)` at the
vacant withdrawal and the seed comparison at six against eight:
the forged witness with its repaired join, and the honest witness
with the forged following pivot, each part the seed floor at one
against minus two.  The split class is the module's standing
crossing refusal at `crossing_rebound`. -/

private def rXc : MatQ := ([[⟨1, 2⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩]], 1)
private def rSp : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨1, 2⟩, .one ⟨3, 1⟩], 0, rfl⟩
private def rR : MatQ := ([[⟨1, 1⟩], [⟨2, 1⟩]], 1)
private def rB : Mat := [[⟨1, 1⟩, ⟨3, 1⟩]]
private def rA : Mat := [[⟨6, 1⟩]]
private def rXf : MatQ := ([[⟨4, 1⟩]], 1)

example : oneValueQ (mulQ rXc rR) (ofM (transposeM rB)) := by
  decide +kernel
example : oneValueQ (addQ rXf (mulQ (ofM rB) rR)) (ofM rA) := by
  decide +kernel
example : splitRead rXc.1 rSp := by decide +kernel

example : (dotN bU bU).scale 5 ≤ (quadForm rA bU).scale 1 := by
  decide +kernel
example : ((4 : Pos) * 1 + 1 * 1) * 1 ≤ 5 * (1 * 1) := by decide +kernel
example : ¬ ((quadForm (blockMat (posBlocks rSp.blocks) rSp.kern)
      (matVec (matMul rSp.Tw.val rR.1) bU)).scale 1
    ≤ minor rSp.T.val * minor rSp.T.val
        * ((dotN bU bU).scale (1 * (rXc.2 * (rR.2 * rR.2))))) := by
  decide +kernel
example : ¬ ((dotN bU bU).scale (4 * rXf.2)
    ≤ (quadForm rXf.1 bU).scale 1) := by decide +kernel

example : (quadForm (blockMat (posBlocks rSp.blocks) rSp.kern)
      (matVec (matMul rSp.Tw.val rR.1) bU)).scale 1
    ≤ minor rSp.T.val * minor rSp.T.val
        * ((dotN bU bU).scale (2 * (rXc.2 * (rR.2 * rR.2)))) := by
  decide +kernel
example : ¬ (((4 : Pos) * 1 + 2 * 1) * 1 ≤ 5 * (1 * 1)) := by
  decide +kernel

example : ¬ ((dotN bU bU).scale 9 ≤ (quadForm bA0 bU).scale 1) := by
  decide +kernel
example : (quadForm (blockMat (posBlocks bSpc.2.blocks) bSpc.2.kern)
      (matVec (matMul bSpc.2.Tw.val bR0.1) bU)).scale 1
    ≤ minor bSpc.2.T.val * minor bSpc.2.T.val
        * ((dotN bU bU).scale (1 * (bX1.2 * (bR0.2 * bR0.2)))) := by
  decide +kernel
example : ((8 : Pos) * 1 + 1 * 1) * 1 ≤ 9 * (1 * 1) := by decide +kernel
example : ¬ ((dotN bU bU).scale (8 * bX0.2)
    ≤ (quadForm bX0.1 bU).scale 1) := by decide +kernel

example : (dotN bU bU).scale 1 ≤ (quadForm crA bU).scale 1 := by
  decide +kernel
example : (quadForm (blockMat (posBlocks crSp.blocks) crSp.kern)
      (matVec (matMul crSp.Tw.val crR5.1) bU)).scale 4
    ≤ minor crSp.T.val * minor crSp.T.val
        * ((dotN bU bU).scale (1 * (crXc.2 * (crR5.2 * crR5.2)))) := by
  decide +kernel
example : ((1 : Pos) * 4 + 1 * 2) * 1 ≤ 1 * (2 * 4) := by
  decide +kernel
example : ¬ ((dotN bU bU).scale (1 * crXf5.2)
    ≤ (quadForm crXf5.1 bU).scale 2) := by decide +kernel
example : (quadForm (blockMat (posBlocks crSp.blocks) crSp.kern)
      (matVec (matMul crSp.Tw.val crR.1) bU)).scale 4
    ≤ minor crSp.T.val * minor crSp.T.val
        * ((dotN bU bU).scale (1 * (crXc.2 * (crR.2 * crR.2)))) := by
  decide +kernel

/-! The crossing count's isolating refusal: the crossing-free chain
`tridiag(3, 3, 3; 1, 2)`, whose recursion runs the pivots
`(12/5, 5/3, 3)` at the witnesses `(3/5, 2/3)` — no crossing
anywhere.  Every read of the tier stands — the tail recursion, the
pivots' certificate list, the assembled datum's split, the
dominance tail at the diagonal floor `(3, 1)` and the depth floor
`(2, 1)` with the transfer's cap at thirty inside seventy-five, and
the walked segment's family read at the boundary slab — while the
crossing's count reads the middle split vacant, and the assembled
datum's count parts beside it at nought against one. -/

private def hnA : Mat := [[⟨4, 1⟩]]
private def hnX0 : MatQ := ([[⟨13, 1⟩]], 5)
private def hnX1 : MatQ := ([[⟨6, 1⟩]], 3)
private def hnDiag : List Mat := [hnA, hnA, hnA]
private def hnXs : List MatQ := [hnX0, hnX1, ofM hnA]
private def hnRs : List MatQ := [([[⟨4, 1⟩]], 5), ([[⟨3, 1⟩]], 3)]
private def hnSps : List ((k : Nat) × Split k) :=
  [⟨1, spOne ⟨13, 1⟩⟩, ⟨1, spOne ⟨6, 1⟩⟩, ⟨1, spOne ⟨4, 1⟩⟩]

private def hnT : Mat :=
  [[⟨6, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 4⟩, ⟨4, 1⟩, ⟨1, 1⟩],
   [⟨3, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]]
private def hnTw : Mat :=
  [[⟨4, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨4, 1⟩, ⟨6, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨11, 1⟩, ⟨16, 1⟩]]
private def hnSP : Split 3 :=
  ⟨⟨hnT, rfl⟩, ⟨hnTw, rfl⟩,
   [.one ⟨61, 1⟩, .one ⟨16, 1⟩, .one ⟨4, 1⟩], 0, rfl⟩

private def hnSpc : (k : Nat) × Split k := ⟨1, spOne ⟨6, 1⟩⟩
private def hnSpT : (k : Nat) × Split k := ⟨1, spOne ⟨31, 1⟩⟩
private def hnDs : List DomStep := [⟨1, (3, 1), (2, 1), spK⟩]
private def dSp : (k : Nat) × Split k := ⟨1, spK⟩

example : tailRead hnDiag bOff hnXs hnRs bNs := by decide +kernel
example : revListRead hnXs hnSps := by decide +kernel
example : splitRead (assemble hnDiag bOff) hnSP := by decide +kernel
example : domRead hnSpc hnSpT 1 1 hnDiag bOff hnXs hnRs bNs hnDs
    bCs := by decide +kernel
example : famChainRead wFam wB 1 200 1 12 (hnDiag.drop (hnDs.length + 1))
    (bOff.drop (hnDs.length + 1)) (bNs.drop (hnDs.length + 1)) := by
  decide +kernel
example : symRead (hnDiag.drop (hnDs.length + 1)) := by decide +kernel
example : ¬ (revAt (ground.getAt dSp hnSps hnDs.length).2 = 1) := by
  decide +kernel
example : ¬ (revAt hnSP = 1) := by decide +kernel

/-! The assembled datum's split is load-bearing: the chain's own
congruence with the crossing's lower unit forged to its upper
partner leaves the block list off the congruence's read, the split
refuses whole, and the count parts beside it at nought against
one. -/

private def bSPf : Split 3 :=
  ⟨⟨bT, rfl⟩, ⟨bTw, rfl⟩,
   [.one ⟨5, 1⟩, .one ⟨2, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩

example : ¬ splitRead (assemble bDiag bOff) bSPf := by decide +kernel
example : ¬ (revAt bSPf = 1) := by decide +kernel

/-! The dominance tail's floors are load-bearing: four slabs at the
diagonals `(0, 1, 2, 3)` and the bonds `(1, 1, 3)`, whose recursion
runs the pivots `(-1/2, 2, -1, 3)` — the crossing at the third slab
and the deepest pivot below the vacant read through the positive
middle.  Every other read of the tier stands — the tail recursion,
the pivots' certificate list at the fold's two, the assembled
datum's split at its two reversals, the bond's square cap, both
cross-multiplied comparisons, the crossing's one count, and the
walked segment's family read at the boundary slab — while the
deepest slab's diagonal
floor lies at nine over the vacant diagonal, its read refusing at
the negative datum, so the dominance tail's read refuses whole and
the assembled datum's count parts beside it at two against one. -/

private def hdDiag : List Mat :=
  [[[⟨1, 1⟩]], [[⟨2, 1⟩]], [[⟨3, 1⟩]], [[⟨4, 1⟩]]]
private def hdOff : List Mat := [bB0, bB0, [[⟨4, 1⟩]]]
private def hdNs : List Nat := [1, 1, 1, 1]
private def hdXs : List MatQ :=
  [([[⟨1, 3⟩]], (4 : Pos)), ([[⟨3, 1⟩]], 1), ([[⟨1, 2⟩]], 1),
   ofM [[⟨4, 1⟩]]]
private def hdRs : List MatQ :=
  [([[⟨2, 1⟩]], (2 : Pos)), ([[⟨1, 2⟩]], 1), ([[⟨2, 1⟩]], 1)]
private def hdSps : List ((k : Nat) × Split k) :=
  [⟨1, spOne ⟨1, 3⟩⟩, ⟨1, spOne ⟨3, 1⟩⟩, ⟨1, spOne ⟨1, 2⟩⟩,
   ⟨1, spOne ⟨4, 1⟩⟩]

private def hdT : Mat :=
  [[⟨3, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩],
   [⟨2, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨2, 1⟩]]
private def hdTw : Mat :=
  [[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨2, 1⟩, ⟨3, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨1, 3⟩, ⟨3, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 1⟩, ⟨3, 1⟩]]
private def hdSP : Split 4 :=
  ⟨⟨hdT, rfl⟩, ⟨hdTw, rfl⟩,
   [.one ⟨1, 3⟩, .one ⟨3, 1⟩, .one ⟨1, 2⟩, .one ⟨4, 1⟩], 0, rfl⟩

private def hdSpc : (k : Nat) × Split k := ⟨1, spOne ⟨1, 2⟩⟩
private def hdSpT : (k : Nat) × Split k := ⟨1, spOne ⟨2, 1⟩⟩
private def hdDs : List DomStep :=
  [⟨1, (9, 1), (1, 4), spOne ⟨1, 10⟩⟩, ⟨1, (1, 1), (1, 2), spK⟩]
private def hdCs : List ((k : Nat) × (Pos × Pos) × Split k) := [⟨1, (1, 1), spK⟩]

example : tailRead hdDiag hdOff hdXs hdRs hdNs := by decide +kernel
example : revListRead hdXs hdSps := by decide +kernel
example : revFold hdSps = 2 := by decide +kernel
example : splitRead (assemble hdDiag hdOff) hdSP := by decide +kernel
example : leAt (matScale (1 : Pos) (matMul bB0 (transposeM bB0)))
    (matScale (1 : Pos) (idMat 1)) spK := by decide +kernel
example : (1 : Pos) * (1 * (1 * 1)) + 1 * (2 * (1 * 4))
    ≤ 9 * (4 * (1 * 1)) := by decide +kernel
example : ((1 : Pos) * 2 + 1 * 2) * 1 ≤ 1 * (2 * 2) := by
  decide +kernel
example : revAt (ground.getAt dSp hdSps hdDs.length).2 = 1 := by
  decide +kernel
example : famChainRead wFam wB 1 200 1 12 (hdDiag.drop (hdDs.length + 1))
    (hdOff.drop (hdDs.length + 1)) (hdNs.drop (hdDs.length + 1)) := by
  decide +kernel
example : symRead (hdDiag.drop (hdDs.length + 1)) := by decide +kernel
example : ¬ leAt (matScale (9 : Pos) (idMat 1))
    (matScale (1 : Pos) [[⟨1, 1⟩]]) (spOne ⟨1, 10⟩) := by
  decide +kernel
example : ¬ domRead hdSpc hdSpT 1 2 hdDiag hdOff hdXs hdRs hdNs
    hdDs hdCs := by decide +kernel
example : ¬ (revAt hdSP = 1) := by decide +kernel

/-! Clause (vii)'s whole chain at the mixed crossing: three slabs
at the orders `(1, 2, 1)`, the diagonals `(5, diag(1, 2), 2)` at
the bonds `(0, 2)` and `(2, 0)ᵀ`, whose tail recursion runs the
pivots `(3, diag(-1, 2), 2)` at the witnesses `(0, 1)ᵀ` and
`(1, 0)`.  The crossing sits at the order-two pivot, its split
through the congruence at the columns `e₀ + e₁`, `4e₀ + 2e₁` of
minor `-2`, the lower unit `-8` beside the kept upper block `1`;
the transfer's cap reads occupied at the kept upper block, the
witness's image `(-4, 1)ᵀ` at the withdrawn diagonal's read
sixteen against the squared minor's four at the cap pair `(4, 1)`,
tight; the seed comparison closes tight at five with the deepest
slab's diagonal floor tight at five; and the assembled order-four
datum's count closes at one through the certificate, decided raw
beside the theorem route. -/

private def mxA0 : Mat := [[⟨6, 1⟩]]
private def mxA1 : Mat := [[⟨2, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩]]
private def mxB0 : Mat := [[⟨1, 1⟩, ⟨3, 1⟩]]
private def mxB1 : Mat := [[⟨3, 1⟩], [⟨1, 1⟩]]
private def mxDiag : List Mat := [mxA0, mxA1, bA2]
private def mxOff : List Mat := [mxB0, mxB1]
private def mxNs : List Nat := [1, 2, 1]

private def mxX0 : MatQ := ([[⟨4, 1⟩]], 1)
private def mxXs : List MatQ := [mxX0, rXc, bX2]
private def mxR2 : MatQ := ([[⟨2, 1⟩, ⟨1, 1⟩]], 1)
private def mxRs : List MatQ := [rR, mxR2]

private def mxSpT_ : Mat := [[⟨2, 1⟩, ⟨5, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]
private def mxSpTw_ : Mat := [[⟨3, 1⟩, ⟨1, 5⟩], [⟨1, 2⟩, ⟨2, 1⟩]]
private def mxSp : Split 2 :=
  ⟨⟨mxSpT_, rfl⟩, ⟨mxSpTw_, rfl⟩, [.one ⟨2, 1⟩, .one ⟨1, 9⟩], 0, rfl⟩
private def mxSps : List ((k : Nat) × Split k) :=
  [⟨1, spOne ⟨4, 1⟩⟩, ⟨2, mxSp⟩, ⟨1, spOne ⟨3, 1⟩⟩]

/-- The assembled chain's congruence at the columns
`e₀ - e₂`, `e₁ - e₃`, `e₂`, `e₃`, the images the recursion's own
pivots. -/
private def mxT : Mat :=
  [[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩]]
private def mxTw : Mat :=
  [[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]]
private def mxSP : Split 4 :=
  ⟨⟨mxT, rfl⟩, ⟨mxTw, rfl⟩,
   [.one ⟨4, 1⟩, .one ⟨1, 2⟩, .one ⟨3, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩

private def mxSpc : (k : Nat) × Split k := ⟨2, mxSp⟩
private def mxSpT : (k : Nat) × Split k := ⟨1, spK⟩
private def mxD : DomStep := ⟨1, (5, 1), (1, 1), spK⟩
private def mxDs : List DomStep := [mxD]

example : tailRead mxDiag mxOff mxXs mxRs mxNs := by decide +kernel
example : revListRead mxXs mxSps := by decide +kernel
example : revFold mxSps = 1 := by decide +kernel
example : splitRead (assemble mxDiag mxOff) mxSP := by decide +kernel
example : revAt mxSP = 1 := by decide +kernel
example : domRead mxSpc mxSpT 4 1 mxDiag mxOff mxXs mxRs mxNs mxDs
    bCs := by decide +kernel
example : leAt
    (matScale (1 : Pos) (matMul
      (transposeM (matMul mxSp.Tw.val rR.1))
      (matMul (blockMat (posBlocks mxSp.blocks) mxSp.kern)
        (matMul mxSp.Tw.val rR.1))))
    (matScaleB ((minor mxSp.T.val * minor mxSp.T.val)
      * BPair.ofPos (4 * (rXc.2 * (rR.2 * rR.2)))) (idMat 1))
    spK := by decide +kernel
example : ((1 : Pos) * 1 + 4 * 1) * 1 ≤ 5 * (1 * 1) := by
  decide +kernel
example : revAt (ground.getAt dSp mxSps mxDs.length).2 = 1 := by
  decide +kernel


/-! Clause (vii)'s center family at the order-two bulk: the diagonal
family `diag(3) + eta` at unit bonds and gram, the constant center
`5/2` at the clearing four with its witness `2/5` at the clearing
five and the image `13/5 + eta`, the pairs `lam = 1/2`, `y0 = 2`,
`rho = 1/5`, `dft = 3/25`, `lc = 11/20`, and the ceiling `1/200` on
the box `[1/2, 2]` in the square scale.  The two recursion ties
close exactly, the four site values read `diag(9)`, `diag(6)`,
`10 -+ 500 eta` and `110 +- 500 eta`, each row's dominance read one
box certificate at the diagonal less the off-row magnitude fold —
the cap certificates at the clearing power one, the shifted
clearing's canonical representative's own degree — the three
clearings' box certificates at the ceiling's own floor, and the
family decides whole.  The refusals isolate the read's data: the
diagonal's row count at a third row and its width at a widened row,
each with the image tie standing at the junk keys' vacant folds;
the witness clearing at six, the two ties refusing jointly at their
one shared datum with every gap certificate, both clearings' reads
and both moduli standing; the defect pair at `1/100`, the upper
arm's gap refusing with the lower arm's fresh certificate, the
moduli and every other read standing — the lower arm's isolation
the arms' shared-pair frame at this refusal's own swap; the
sign-blind clearing at minus two over minus five, the ties
standing at the cross-multiplied blindness with the witness
clearing's box read refusing; the modulus tie at `12/20` against
its second comparison standing; the modulus cap at `30/2` with both
cap arms' gaps standing; the contraction gap at `lam = 1/3` with
the modulus pair re-tied at `11/30`; and the floor gap at
`y0 = 12/5` re-tied at `13/24`.  The further sections isolate the
two stated matrices' shapes, the gram's, the center's and the
image's exchange conjuncts — the center's at the degenerate bond
whose vacant witness leaves the image the diagonal family's own,
the image's at the tie-consistent asymmetric diagonal family — the
three families' shapes, the center clearing's box read, the image
clearing's certificate and its sign at the negative-diagonal gram,
and the image tie's spelling at a non-symmetric bond; the
orders' guard `hnz` of `ball_step_of` rides its constituent
`image_contract_of`, whose isolating refusal at the collapsed
shallower order is the Spectator battery's. -/

private def c2P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 2]], ([] : poly.PPoly))
private def c5P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 5]], ([] : poly.PPoly))
private def c6P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 6]], ([] : poly.PPoly))
private def c10P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 10]], ([] : poly.PPoly))
private def c13P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 13]], ([] : poly.PPoly))
private def pEta : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 1]], ([] : poly.PPoly))
private def p5Eta : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 5]], ([] : poly.PPoly))

private def bfAf : List (List (poly.PPoly × poly.PPoly)) :=
  [[c3P, pEta], [pEta, c3P]]
private def bfCf : PfMQ := ([[c10P, vacProf], [vacProf, c10P]], c4P)
private def bfWf : PfMQ := ([[c2P, vacProf], [vacProf, c2P]], c5P)
private def bfIf : PfMQ := ([[c13P, p5Eta], [p5Eta, c13P]], c5P)


private def bfFix : CenterFam :=
  ⟨2, bfAf, bfCf, bfWf, bfIf, (1, 2), (2, 1), (1, 5), (3, 25),
   (11, 20), (BPair.ofNat 1, 200),
   [bx1 1 1, bx1 1 1], [bx1 1 1, bx1 1 1],
   [bx1 3 1, bx1 3 1], [bx1 3 1, bx1 3 1],
   bx1 1 0, bx1 1 0, bx1 1 0⟩

example : pfmOneValue (contrSiteF bfWf (idMat 2) 1 2)
    [[([[BPair.ofNat 9]], ([] : poly.PPoly)), vacProf],
     [vacProf, ([[BPair.ofNat 9]], ([] : poly.PPoly))]] := by
  decide +kernel
example : pfmOneValue (floorSiteF bfCf (idMat 2) 2 1 1 5)
    [[c6P, vacProf], [vacProf, c6P]] := by decide +kernel
example : pfmOneValue (dcapHiSiteF bfCf bfIf (idMat 2) 3 25)
    [[c10P, ([[BPair.unit, (BPair.ofNat 500).swap]], ([] : poly.PPoly))],
     [([[BPair.unit, (BPair.ofNat 500).swap]], ([] : poly.PPoly)),
      c10P]] := by decide +kernel
example : pfmOneValue (dcapLoSiteF bfCf bfIf (idMat 2) 3 25)
    [[([[BPair.ofNat 110]], ([] : poly.PPoly)),
      ([[BPair.unit, BPair.ofNat 500]], ([] : poly.PPoly))],
     [([[BPair.unit, BPair.ofNat 500]], ([] : poly.PPoly)),
      ([[BPair.ofNat 110]], ([] : poly.PPoly))]] := by decide +kernel

example : famRead bfFix (idMat 2) (idMat 2) := by decide +kernel

private def bfFixR0 : CenterFam :=
  { bfFix with Af := [[c3P, pEta, c3P], [pEta, c3P]] }
example : ¬ famRead bfFixR0 (idMat 2) (idMat 2) := by decide +kernel
example : pfmQOneValue bfFixR0.If
    (pfmQadd (ofPfm bfFixR0.Af)
      (pfmQmul (ofPfm (ofMatProf (idMat 2)))
        (pfmQswap bfFixR0.Wf))) := by decide +kernel

private def bfFixRL : CenterFam :=
  { bfFix with Af := [[c3P, pEta], [pEta, c3P], [pEta, c3P]] }
example : ¬ famRead bfFixRL (idMat 2) (idMat 2) := by decide +kernel
example : elim.rowsLen bfFixRL.o bfFixRL.Af
    ∧ pfmQOneValue bfFixRL.If
      (pfmQadd (ofPfm bfFixRL.Af)
        (pfmQmul (ofPfm (ofMatProf (idMat 2)))
          (pfmQswap bfFixRL.Wf))) := by decide +kernel

private def bfFixR1 : CenterFam :=
  { bfFix with Wf := ([[c2P, vacProf], [vacProf, c2P]], c6P) }
example : ¬ famRead bfFixR1 (idMat 2) (idMat 2) := by decide +kernel
example : domCertGo (BPair.ofNat 1) 200 0
    (contrSiteF bfFixR1.Wf (idMat 2) 1 2) [bx1 1 1, bx1 1 1] := by
  decide +kernel
example : boxRead c6P (BPair.ofNat 1) 200 (bx1 1 0) := by decide +kernel

private def bfFixR2 : CenterFam :=
  { { bfFix with dft := (1, 100) } with bxL := [bx1 11 1, bx1 11 1] }
example : ¬ famRead bfFixR2 (idMat 2) (idMat 2) := by decide +kernel
example : domCertGo (BPair.ofNat 1) 200 0
    (dcapLoSiteF bfCf bfIf (idMat 2) 1 100) [bx1 11 1, bx1 11 1] := by
  decide +kernel
example : (1 : Pos) * ((20 * 20) * 5) + (11 * 11) * (1 * 100)
    ≤ 1 * (100 * (20 * 20)) := by decide +kernel

private def bfFixR4 : CenterFam :=
  { bfFix with
    Wf := ([[(⟨[[(⟨1, 3⟩ : BPair)]], ([] : poly.PPoly)⟩ :
        poly.PPoly × poly.PPoly), vacProf],
      [vacProf, (⟨[[(⟨1, 3⟩ : BPair)]], ([] : poly.PPoly)⟩ :
        poly.PPoly × poly.PPoly)]],
      (⟨[[(⟨1, 6⟩ : BPair)]], ([] : poly.PPoly)⟩ :
        poly.PPoly × poly.PPoly)) }
example : ¬ famRead bfFixR4 (idMat 2) (idMat 2) := by decide +kernel
example : pfmQOneValue (pfmQmul bfFixR4.Cf (pfmQshift bfFixR4.Wf))
    (ofPfm (ofMatProf (transposeM (idMat 2)))) := by decide +kernel
example : domCertGo (BPair.ofNat 1) 200 0
    (contrSiteF bfFixR4.Wf (idMat 2) 1 2) [bx1 1 1, bx1 1 1] := by
  decide +kernel

private def bfFixR5 : CenterFam := { bfFix with lc := (12, 20) }
example : ¬ famRead bfFixR5 (idMat 2) (idMat 2) := by decide +kernel
example : (3 : Pos) * ((20 * 20) * 5) + (12 * 12) * (1 * 25)
    ≤ 1 * (25 * (20 * 20)) := by decide +kernel

private def bfFixR6 : CenterFam := { bfFix with dft := (30, 2) }
example : ¬ famRead bfFixR6 (idMat 2) (idMat 2) := by decide +kernel
example : domCertGo (BPair.ofNat 1) 200 0
    (dcapHiSiteF bfCf bfIf (idMat 2) 30 2) [bx1 3 1, bx1 3 1] := by
  decide +kernel
example : domCertGo (BPair.ofNat 1) 200 0
    (dcapLoSiteF bfCf bfIf (idMat 2) 30 2) [bx1 3 1, bx1 3 1] := by
  decide +kernel

private def bfFixR7 : CenterFam :=
  { bfFix with lam := (1, 3), lc := (11, 30) }
example : ¬ famRead bfFixR7 (idMat 2) (idMat 2) := by decide +kernel
example : (2 : Pos) * (11 * (3 * 5)) = 1 * ((2 * 5 + 1 * 1) * 30) := by
  decide +kernel
example : (3 : Pos) * ((30 * 30) * 5) + (11 * 11) * (1 * 25)
    ≤ 1 * (25 * (30 * 30)) := by decide +kernel

private def bfFixR8 : CenterFam :=
  { bfFix with y0 := (12, 5), lc := (13, 24) }
example : ¬ famRead bfFixR8 (idMat 2) (idMat 2) := by decide +kernel
example : (12 : Pos) * (13 * (2 * 5)) = 1 * ((12 * 5 + 1 * 5) * 24) := by
  decide +kernel
example : (3 : Pos) * ((24 * 24) * 5) + (13 * 13) * (1 * 25)
    ≤ 1 * (25 * (24 * 24)) := by decide +kernel

/-! The two stated matrices' shape reads: the bond widened at its
second row parts its shape alone, both ties standing at the junk
key's vacant folds, and the gram widened at its second row parts
its shape with its exchange read jointly — the exchange read is
shape-carrying — the contraction walk standing at the ragged
datum's truncated folds. -/

private def bfBW : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 1, BPair.ofNat 7]]
example : ¬ famRead bfFix bfBW (idMat 2) := by decide +kernel
example : pfmQOneValue (pfmQmul bfFix.Cf (pfmQshift bfFix.Wf))
      (ofPfm (ofMatProf (transposeM bfBW)))
    ∧ pfmQOneValue bfFix.If
      (pfmQadd (ofPfm bfFix.Af)
        (pfmQmul (ofPfm (ofMatProf bfBW)) (pfmQswap bfFix.Wf))) := by
  decide +kernel
example : ¬ famRead bfFix (idMat 2) bfBW := by decide +kernel
example : ¬ elim.matOneValue (elim.transposeM bfBW) bfBW := by
  decide +kernel
example : domCertGo bfFix.e0.1 bfFix.e0.2 0
    (contrSiteF bfFix.Wf bfBW 1 2) bfFix.bxC := by decide +kernel

/-! The gram's exchange conjunct isolated: a family at the
non-symmetric gram `[[3, 1], [-1, 3]]` whose every further conjunct
decides true — the walks read row magnitudes and the ties read the
bond alone, every one blind to the gram's antisymmetric part, so
the exchange conjunct is the one guard (`thm:decimation`(ii)'s
symmetric datum, the certificate's own read). -/

private def bfGns : elim.Mat :=
  [[BPair.ofNat 3, BPair.ofNat 1],
   [(BPair.ofNat 1).swap, BPair.ofNat 3]]
private def bfB3 : elim.Mat :=
  [[BPair.ofNat 3, BPair.unit], [BPair.unit, BPair.ofNat 3]]
private def c11P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 11]], ([] : poly.PPoly))
private def c30P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 30]], ([] : poly.PPoly))
private def c101P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 101]], ([] : poly.PPoly))
private def bfNS : CenterFam :=
  ⟨2, [[c11P, vacProf], [vacProf, c11P]],
   ([[c30P, vacProf], [vacProf, c30P]], c3P),
   ([[c3P, vacProf], [vacProf, c3P]], c10P),
   ([[c101P, vacProf], [vacProf, c101P]], c10P),
   (1, 2), (2, 1), (1, 5), (1, 8), (11, 20), (BPair.ofNat 1, 200),
   [bx1 1 1, bx1 1 1], [bx1 1 1, bx1 1 1],
   [bx1 1 2, bx1 1 2], [bx1 1 2, bx1 1 2],
   bx1 1 0, bx1 1 0, bx1 1 0⟩
example : ¬ famRead bfNS bfB3 bfGns := by decide +kernel
example : ¬ elim.matOneValue (elim.transposeM bfGns) bfGns := by
  decide +kernel
example : domCertGo bfNS.e0.1 bfNS.e0.2 0
      (contrSiteF bfNS.Wf bfGns 1 2) bfNS.bxC
    ∧ domCertGo bfNS.e0.1 bfNS.e0.2 0
      (floorSiteF bfNS.Cf bfGns 2 1 1 5) bfNS.bxF := by decide +kernel

/-! The two exchange conjuncts parting jointly: the
upper-triangular center `[[10, eta], [0, 10]]` with its witness
`[[40, -4 eta], [0, 40]]` at the clearing one hundred solving both
recursion ties exactly and the image `[[260, 104 eta], [100 eta,
260]]`, the four walks certified at their own boxes — every further
conjunct decides true, and the center's and the image's exchange
reads (`lem:spectator`(iii)) part together at this fixture, the
triangular center forcing the image's own asymmetry through the
recursion's join.  The image exchange's own isolation is the
forged-diagonal fixture below. -/

private def c40P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 40]], ([] : poly.PPoly))
private def c100P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 100]], ([] : poly.PPoly))
private def c260P : poly.PPoly × poly.PPoly := ([[BPair.ofNat 260]], ([] : poly.PPoly))
private def m4Eta : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, (BPair.ofNat 4).swap]], ([] : poly.PPoly))
private def p104Eta : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 104]], ([] : poly.PPoly))
private def p100Eta : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 100]], ([] : poly.PPoly))
private def bxS (f1L f1D K : Nat) : BoxCert :=
  ⟨⟨BPair.ofNat 1, 2⟩, ⟨BPair.ofNat 2, 1⟩, [], [], [],
   BPair.ofNat 8, BPair.ofNat 2, BPair.ofNat 4,
   BPair.ofNat f1L, BPair.ofNat f1D, BPair.ofNat 1, BPair.unit, K⟩
private def bfCS : CenterFam :=
  ⟨2, bfAf, ([[c10P, pEta], [vacProf, c10P]], c4P),
   ([[c40P, m4Eta], [vacProf, c40P]], c100P),
   ([[c260P, p104Eta], [p100Eta, c260P]], c100P),
   (1, 2), (2, 1), (1, 5), (3, 25), (11, 20), (BPair.ofNat 1, 200),
   [bxS 4 1 2, bxS 4 1 2], [bx1 1 1, bx1 1 1],
   [bxS 40 1 1, bxS 51 1 1], [bxS 40 1 1, bxS 51 1 1],
   bx1 1 0, bx1 1 0, bx1 1 0⟩
example : ¬ famRead bfCS (idMat 2) (idMat 2) := by decide +kernel
example : ¬ pfmOneValue (pfmTr bfCS.Cf.1) bfCS.Cf.1
    ∧ ¬ pfmOneValue (pfmTr bfCS.If.1) bfCS.If.1 := by decide +kernel
example : boxRead bfCS.If.2 bfCS.e0.1 bfCS.e0.2 bfCS.bxClI := by
  decide +kernel
example : pfmQOneValue (pfmQmul bfCS.Cf (pfmQshift bfCS.Wf))
      (ofPfm (ofMatProf (transposeM (idMat 2))))
    ∧ pfmQOneValue bfCS.If
      (pfmQadd (ofPfm bfCS.Af)
        (pfmQmul (ofPfm (ofMatProf (idMat 2))) (pfmQswap bfCS.Wf))) := by
  decide +kernel
example : domCertGo bfCS.e0.1 bfCS.e0.2 0
      (dcapHiSiteF bfCS.Cf bfCS.If (idMat 2) 3 25) bfCS.bxU
    ∧ domCertGo bfCS.e0.1 bfCS.e0.2 0
      (dcapLoSiteF bfCS.Cf bfCS.If (idMat 2) 3 25) bfCS.bxL := by
  decide +kernel

/-! The three families' shape reads: the center's width forge parts
its shape with its exchange jointly (the exchange read is
shape-carrying), the witness's parts its shape with the witness tie
jointly (the widened product moves the tie's own shape), and the
image's parts its shape with its own exchange and the image tie
jointly (the exchange read is shape-carrying and the widened family
sits on the tie's own side) — each forge's further walks standing at
the truncated folds. -/

private def bfRCsh : CenterFam :=
  { bfFix with Cf := ([[c10P, vacProf, c10P], [vacProf, c10P, c10P]], c4P) }
example : ¬ famRead bfRCsh (idMat 2) (idMat 2) := by decide +kernel
example : pfmQOneValue (pfmQmul bfRCsh.Cf (pfmQshift bfRCsh.Wf))
      (ofPfm (ofMatProf (transposeM (idMat 2))))
    ∧ domCertGo bfRCsh.e0.1 bfRCsh.e0.2 0
      (floorSiteF bfRCsh.Cf (idMat 2) 2 1 1 5) bfRCsh.bxF := by
  decide +kernel

private def bfRWsh : CenterFam :=
  { bfFix with Wf := ([[c2P, vacProf, c2P], [vacProf, c2P, c2P]], c5P) }
example : ¬ famRead bfRWsh (idMat 2) (idMat 2) := by decide +kernel
example : ¬ pfmQOneValue (pfmQmul bfRWsh.Cf (pfmQshift bfRWsh.Wf))
    (ofPfm (ofMatProf (transposeM (idMat 2)))) := by decide +kernel

private def bfRIsh : CenterFam :=
  { bfFix with If := ([[c13P, p5Eta, c2P], [p5Eta, c13P, c2P]], c5P) }
example : ¬ famRead bfRIsh (idMat 2) (idMat 2) := by decide +kernel
example : ¬ pfmQOneValue bfRIsh.If
    (pfmQadd (ofPfm bfRIsh.Af)
      (pfmQmul (ofPfm (ofMatProf (idMat 2))) (pfmQswap bfRIsh.Wf))) := by
  decide +kernel
example : domCertGo bfRIsh.e0.1 bfRIsh.e0.2 0
    (dcapHiSiteF bfRIsh.Cf bfRIsh.If (idMat 2) 3 25) bfRIsh.bxU := by
  decide +kernel

/-! The center clearing's box read isolated: the certificate's floor
forged at five over the clearing four, the witness clearing's read
standing. -/

private def bfR11 : CenterFam := { bfFix with bxClC := bx1 5 0 }
example : ¬ famRead bfR11 (idMat 2) (idMat 2) := by decide +kernel
example : ¬ boxRead bfR11.Cf.2 bfR11.e0.1 bfR11.e0.2 bfR11.bxClC := by
  decide +kernel
example : boxRead bfR11.Wf.2 bfR11.e0.1 bfR11.e0.2 bfR11.bxClW := by
  decide +kernel

/-! The image family's exchange conjunct isolated: the diagonal
family carries the asymmetric scale row `[[3, eta], [2 eta, 3]]`, so
the recursion's join reads the image `[[13, 5 eta], [10 eta, 13]]`
at the clearing five — both ties close exactly, the defect cap's two
site values read `10 -+ (500 eta, 1000 eta)` and `110 +- (500 eta,
1000 eta)` with the deeper row's own certificate at the floor six,
and every further conjunct decides true; the located symmetric
image's read (`lem:spectator`(iii), `thm:decimation`(ii)'s symmetric
datum at the cap's site) is the one guard. -/

private def p2Eta : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 2]], ([] : poly.PPoly))
private def p10Eta : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 10]], ([] : poly.PPoly))
private def bfFixIS : CenterFam :=
  { bfFix with
    Af := [[c3P, pEta], [p2Eta, c3P]],
    If := ([[c13P, p5Eta], [p10Eta, c13P]], c5P),
    bxU := [bx1 3 1, bx1 6 1],
    bxL := [bx1 3 1, bx1 6 1] }
example : pfmOneValue (dcapHiSiteF bfFixIS.Cf bfFixIS.If (idMat 2) 3 25)
    [[c10P, ([[BPair.unit, (BPair.ofNat 500).swap]], ([] : poly.PPoly))],
     [([[BPair.unit, (BPair.ofNat 1000).swap]], ([] : poly.PPoly)),
      c10P]] := by decide +kernel
example : ¬ famRead bfFixIS (idMat 2) (idMat 2) := by decide +kernel
example : ¬ pfmOneValue (pfmTr bfFixIS.If.1) bfFixIS.If.1 := by
  decide +kernel
example : bfFixIS.Af.length = bfFixIS.o ∧ elim.rowsLen bfFixIS.o bfFixIS.Af
    ∧ bfFixIS.Cf.1.length = bfFixIS.o ∧ elim.rowsLen bfFixIS.o bfFixIS.Cf.1
    ∧ bfFixIS.Wf.1.length = bfFixIS.o ∧ elim.rowsLen bfFixIS.o bfFixIS.Wf.1
    ∧ bfFixIS.If.1.length = bfFixIS.o ∧ elim.rowsLen bfFixIS.o bfFixIS.If.1
    ∧ elim.sqAt (idMat 2) bfFixIS.o ∧ elim.sqAt (idMat 2) bfFixIS.o
    ∧ matOneValue (transposeM (idMat 2)) (idMat 2)
    ∧ pfmOneValue (pfmTr bfFixIS.Cf.1) bfFixIS.Cf.1
    ∧ pfmQOneValue (pfmQmul bfFixIS.Cf (pfmQshift bfFixIS.Wf))
        (ofPfm (ofMatProf (transposeM (idMat 2))))
    ∧ pfmQOneValue bfFixIS.If
        (pfmQadd (ofPfm bfFixIS.Af)
          (pfmQmul (ofPfm (ofMatProf (idMat 2))) (pfmQswap bfFixIS.Wf)))
    ∧ domCertGo bfFixIS.e0.1 bfFixIS.e0.2 0
        (contrSiteF bfFixIS.Wf (idMat 2) bfFixIS.lam.1 bfFixIS.lam.2)
        bfFixIS.bxC
    ∧ domCertGo bfFixIS.e0.1 bfFixIS.e0.2 0
        (floorSiteF bfFixIS.Cf (idMat 2) bfFixIS.y0.1 bfFixIS.y0.2
          bfFixIS.rho.1 bfFixIS.rho.2) bfFixIS.bxF
    ∧ domCertGo bfFixIS.e0.1 bfFixIS.e0.2 0
        (dcapHiSiteF bfFixIS.Cf bfFixIS.If (idMat 2) bfFixIS.dft.1
          bfFixIS.dft.2) bfFixIS.bxU
    ∧ domCertGo bfFixIS.e0.1 bfFixIS.e0.2 0
        (dcapLoSiteF bfFixIS.Cf bfFixIS.If (idMat 2) bfFixIS.dft.1
          bfFixIS.dft.2) bfFixIS.bxL
    ∧ boxRead bfFixIS.Cf.2 bfFixIS.e0.1 bfFixIS.e0.2 bfFixIS.bxClC
    ∧ boxRead bfFixIS.Wf.2 bfFixIS.e0.1 bfFixIS.e0.2 bfFixIS.bxClW
    ∧ boxRead bfFixIS.If.2 bfFixIS.e0.1 bfFixIS.e0.2 bfFixIS.bxClI
    ∧ bfFixIS.y0.1 * (bfFixIS.lc.1 * (bfFixIS.lam.2 * bfFixIS.rho.2))
        = bfFixIS.lam.1
          * ((bfFixIS.y0.1 * bfFixIS.rho.2 + bfFixIS.rho.1 * bfFixIS.y0.2)
            * bfFixIS.lc.2)
    ∧ bfFixIS.dft.1 * ((bfFixIS.lc.2 * bfFixIS.lc.2) * bfFixIS.rho.2)
          + (bfFixIS.lc.1 * bfFixIS.lc.1) * (bfFixIS.rho.1 * bfFixIS.dft.2)
        ≤ bfFixIS.rho.1
          * (bfFixIS.dft.2 * (bfFixIS.lc.2 * bfFixIS.lc.2)) := by
  decide +kernel

/-! The image clearing's box read isolated: the certificate's floor
forged at five against the image's clearing five, the center's and
the witness's reads standing. -/

private def bfR12 : CenterFam := { bfFix with bxClI := bx1 5 0 }
example : ¬ famRead bfR12 (idMat 2) (idMat 2) := by decide +kernel
example : ¬ boxRead bfR12.If.2 bfR12.e0.1 bfR12.e0.2 bfR12.bxClI := by
  decide +kernel
example : boxRead bfR12.Cf.2 bfR12.e0.1 bfR12.e0.2 bfR12.bxClC
    ∧ boxRead bfR12.Wf.2 bfR12.e0.1 bfR12.e0.2 bfR12.bxClW := by
  decide +kernel

/-! The image clearing's sign pin at its own forge: a gram of
negative diagonal admits every dominance walk with the image
family's clearing on its lower side — the two recursion ties
cross-multiplied blind to the joint sign, the four site data
positive at the crossed signs — and the image clearing's box read
alone refuses: the stated clearing slot's side is the
certificate's own datum, the deviation's two-sided cap
(`lem:spectator`(iii)) reading it. -/

private def n13P : poly.PPoly × poly.PPoly :=
  ([[(BPair.ofNat 13).swap]], ([] : poly.PPoly))
private def n5P : poly.PPoly × poly.PPoly :=
  ([[(BPair.ofNat 5).swap]], ([] : poly.PPoly))
private def ngG : elim.Mat := [[(BPair.ofNat 1).swap]]
private def ngB : elim.Mat := [[BPair.ofNat 1]]
private def ngAf : List (List (poly.PPoly × poly.PPoly)) := [[c3P]]
private def ngCf : PfMQ := ([[c10P]], c4P)
private def ngWf : PfMQ := ([[c2P]], c5P)
private def ngIf : PfMQ := ([[n13P]], n5P)

private def bfNG : CenterFam :=
  ⟨1, ngAf, ngCf, ngWf, ngIf, (1, 3), (2, 1), (1, 5), (3, 25),
   (11, 30), (BPair.ofNat 1, 200),
   [bx1 1 1], [bx1 1 1], [bx1 1 1], [bx1 1 1],
   bx1 1 0, bx1 1 0, bx1 1 0⟩

example : pfmOneValue (contrSiteF ngWf ngG 1 3)
    [[([[BPair.ofNat 11]], ([] : poly.PPoly))]] := by decide +kernel
example : pfmOneValue (floorSiteF ngCf ngG 2 1 1 5)
    [[([[BPair.ofNat 94]], ([] : poly.PPoly))]] := by decide +kernel
example : pfmOneValue (dcapHiSiteF ngCf ngIf ngG 3 25)
    [[([[BPair.ofNat 110]], ([] : poly.PPoly))]] := by decide +kernel
example : pfmOneValue (dcapLoSiteF ngCf ngIf ngG 3 25)
    [[([[BPair.ofNat 10]], ([] : poly.PPoly))]] := by decide +kernel
example : bfNG.Af.length = bfNG.o ∧ elim.rowsLen bfNG.o bfNG.Af
    ∧ bfNG.Cf.1.length = bfNG.o ∧ elim.rowsLen bfNG.o bfNG.Cf.1
    ∧ bfNG.Wf.1.length = bfNG.o ∧ elim.rowsLen bfNG.o bfNG.Wf.1
    ∧ bfNG.If.1.length = bfNG.o ∧ elim.rowsLen bfNG.o bfNG.If.1
    ∧ elim.sqAt ngB bfNG.o ∧ elim.sqAt ngG bfNG.o
    ∧ matOneValue (transposeM ngG) ngG
    ∧ pfmOneValue (pfmTr bfNG.Cf.1) bfNG.Cf.1
    ∧ pfmOneValue (pfmTr bfNG.If.1) bfNG.If.1
    ∧ pfmQOneValue (pfmQmul bfNG.Cf (pfmQshift bfNG.Wf))
        (ofPfm (ofMatProf (transposeM ngB)))
    ∧ pfmQOneValue bfNG.If
        (pfmQadd (ofPfm bfNG.Af)
          (pfmQmul (ofPfm (ofMatProf ngB)) (pfmQswap bfNG.Wf)))
    ∧ domCertGo bfNG.e0.1 bfNG.e0.2 0
        (contrSiteF bfNG.Wf ngG bfNG.lam.1 bfNG.lam.2) bfNG.bxC
    ∧ domCertGo bfNG.e0.1 bfNG.e0.2 0
        (floorSiteF bfNG.Cf ngG bfNG.y0.1 bfNG.y0.2 bfNG.rho.1
          bfNG.rho.2) bfNG.bxF
    ∧ domCertGo bfNG.e0.1 bfNG.e0.2 0
        (dcapHiSiteF bfNG.Cf bfNG.If ngG bfNG.dft.1 bfNG.dft.2) bfNG.bxU
    ∧ domCertGo bfNG.e0.1 bfNG.e0.2 0
        (dcapLoSiteF bfNG.Cf bfNG.If ngG bfNG.dft.1 bfNG.dft.2) bfNG.bxL
    ∧ boxRead bfNG.Cf.2 bfNG.e0.1 bfNG.e0.2 bfNG.bxClC
    ∧ boxRead bfNG.Wf.2 bfNG.e0.1 bfNG.e0.2 bfNG.bxClW
    ∧ bfNG.y0.1 * (bfNG.lc.1 * (bfNG.lam.2 * bfNG.rho.2))
        = bfNG.lam.1
          * ((bfNG.y0.1 * bfNG.rho.2 + bfNG.rho.1 * bfNG.y0.2) * bfNG.lc.2)
    ∧ bfNG.dft.1 * ((bfNG.lc.2 * bfNG.lc.2) * bfNG.rho.2)
          + (bfNG.lc.1 * bfNG.lc.1) * (bfNG.rho.1 * bfNG.dft.2)
        ≤ bfNG.rho.1 * (bfNG.dft.2 * (bfNG.lc.2 * bfNG.lc.2)) := by
  decide +kernel
example : ¬ boxRead ngIf.2 bfNG.e0.1 bfNG.e0.2 bfNG.bxClI := by
  decide +kernel
example : ¬ famRead bfNG ngB ngG := by decide +kernel

/-! The center's exchange at its own isolation: the bond at the
sum's unit forces the witness family's vacant read through the
recursion's tie, the image family the diagonal family's own at its
clearing, so the image's exchange stands with every walk, tie,
clearing and modulus read while the center's exchange alone
refuses. -/

private def p4Eta : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 4]], ([] : poly.PPoly))
private def cxB : elim.Mat :=
  [[BPair.unit, BPair.unit], [BPair.unit, BPair.unit]]
private def cxAf : List (List (poly.PPoly × poly.PPoly)) :=
  [[c3P, pEta], [pEta, c3P]]
private def cxCf : PfMQ := ([[c10P, pEta], [vacProf, c10P]], c4P)
private def cxWf : PfMQ :=
  ([[vacProf, vacProf], [vacProf, vacProf]], c5P)
private def cxIf : PfMQ := ([[c12P, p4Eta], [p4Eta, c12P]], c4P)

private def bfCX : CenterFam :=
  ⟨2, cxAf, cxCf, cxWf, cxIf, (1, 5), (9, 10), (3, 2), (4, 5),
   (8, 15), (BPair.ofNat 1, 200),
   [bx1 1 1, bx1 1 1], [bx1 3 1, bx1 3 1],
   [bx1 3 1, bx1 3 1], [bx1 3 1, bx1 3 1],
   bx1 1 0, bx1 1 0, bx1 1 0⟩

example : pfmOneValue (floorSiteF cxCf (idMat 2) 9 10 3 2)
    [[([[BPair.ofNat 8]], ([] : poly.PPoly)),
      ([[BPair.unit, BPair.ofNat 20]], ([] : poly.PPoly))],
     [vacProf, ([[BPair.ofNat 8]], ([] : poly.PPoly))]] := by
  decide +kernel
example : pfmOneValue (dcapHiSiteF cxCf cxIf (idMat 2) 4 5)
    [[([[BPair.ofNat 24]], ([] : poly.PPoly)),
      ([[BPair.unit, (BPair.ofNat 60).swap]], ([] : poly.PPoly))],
     [([[BPair.unit, (BPair.ofNat 80).swap]], ([] : poly.PPoly)),
      ([[BPair.ofNat 24]], ([] : poly.PPoly))]] := by decide +kernel
example : bfCX.Af.length = bfCX.o ∧ elim.rowsLen bfCX.o bfCX.Af
    ∧ bfCX.Cf.1.length = bfCX.o ∧ elim.rowsLen bfCX.o bfCX.Cf.1
    ∧ bfCX.Wf.1.length = bfCX.o ∧ elim.rowsLen bfCX.o bfCX.Wf.1
    ∧ bfCX.If.1.length = bfCX.o ∧ elim.rowsLen bfCX.o bfCX.If.1
    ∧ elim.sqAt cxB bfCX.o ∧ elim.sqAt (idMat 2) bfCX.o
    ∧ matOneValue (transposeM (idMat 2)) (idMat 2)
    ∧ pfmOneValue (pfmTr bfCX.If.1) bfCX.If.1
    ∧ pfmQOneValue (pfmQmul bfCX.Cf (pfmQshift bfCX.Wf))
        (ofPfm (ofMatProf (transposeM cxB)))
    ∧ pfmQOneValue bfCX.If
        (pfmQadd (ofPfm bfCX.Af)
          (pfmQmul (ofPfm (ofMatProf cxB)) (pfmQswap bfCX.Wf)))
    ∧ domCertGo bfCX.e0.1 bfCX.e0.2 0
        (contrSiteF bfCX.Wf (idMat 2) bfCX.lam.1 bfCX.lam.2) bfCX.bxC
    ∧ domCertGo bfCX.e0.1 bfCX.e0.2 0
        (floorSiteF bfCX.Cf (idMat 2) bfCX.y0.1 bfCX.y0.2 bfCX.rho.1
          bfCX.rho.2) bfCX.bxF
    ∧ domCertGo bfCX.e0.1 bfCX.e0.2 0
        (dcapHiSiteF bfCX.Cf bfCX.If (idMat 2) bfCX.dft.1 bfCX.dft.2)
        bfCX.bxU
    ∧ domCertGo bfCX.e0.1 bfCX.e0.2 0
        (dcapLoSiteF bfCX.Cf bfCX.If (idMat 2) bfCX.dft.1 bfCX.dft.2)
        bfCX.bxL
    ∧ boxRead bfCX.Cf.2 bfCX.e0.1 bfCX.e0.2 bfCX.bxClC
    ∧ boxRead bfCX.Wf.2 bfCX.e0.1 bfCX.e0.2 bfCX.bxClW
    ∧ boxRead bfCX.If.2 bfCX.e0.1 bfCX.e0.2 bfCX.bxClI
    ∧ bfCX.y0.1 * (bfCX.lc.1 * (bfCX.lam.2 * bfCX.rho.2))
        = bfCX.lam.1
          * ((bfCX.y0.1 * bfCX.rho.2 + bfCX.rho.1 * bfCX.y0.2) * bfCX.lc.2)
    ∧ bfCX.dft.1 * ((bfCX.lc.2 * bfCX.lc.2) * bfCX.rho.2)
          + (bfCX.lc.1 * bfCX.lc.1) * (bfCX.rho.1 * bfCX.dft.2)
        ≤ bfCX.rho.1 * (bfCX.dft.2 * (bfCX.lc.2 * bfCX.lc.2)) := by
  decide +kernel
example : ¬ pfmOneValue (pfmTr cxCf.1) cxCf.1 := by decide +kernel
example : ¬ famRead bfCX cxB (idMat 2) := by decide +kernel

/-! The image tie's spelling pinned at a non-symmetric bond: the
witness solves its tie at the bond's exchange, the image joins the
bond's own multiple of the witness — and the exchange written into
the join instead decides false, the recursion's join the bond
itself (`lem:spectator`(i)'s display). -/

private def bfBns : elim.Mat :=
  [[BPair.ofNat 1, BPair.ofNat 1], [BPair.unit, BPair.ofNat 1]]
private def bfAfD : List (List (poly.PPoly × poly.PPoly)) :=
  [[c3P, vacProf], [vacProf, c3P]]
private def m2P : poly.PPoly × poly.PPoly :=
  ([[(⟨1, 3⟩ : BPair)]], ([] : poly.PPoly))
private def bfWfB : PfMQ := ([[c2P, vacProf], [c2P, c2P]], c5P)
private def bfIfB : PfMQ := ([[c11P, m2P], [m2P, c13P]], c5P)
example : pfmQOneValue (pfmQmul ([[c10P, vacProf],
      [vacProf, c10P]], c4P) (pfmQshift bfWfB))
    (ofPfm (ofMatProf (transposeM bfBns))) := by decide +kernel
example : pfmQOneValue bfIfB
    (pfmQadd (ofPfm bfAfD)
      (pfmQmul (ofPfm (ofMatProf bfBns)) (pfmQswap bfWfB))) := by
  decide +kernel
example : ¬ pfmQOneValue bfIfB
    (pfmQadd (ofPfm bfAfD)
      (pfmQmul (ofPfm (ofMatProf (transposeM bfBns)))
        (pfmQswap bfWfB))) := by decide +kernel


/-! Clause (vii)'s four count reshapes at the evaluated data: each
site datum's dominance certificate walk prices its evaluated form
at or above the sum's unit, and the form's decomposition reads that
price as the pointwise count the tex states — the floor's center
comparison, the contraction's transfer comparison and the defect
cap's two arms, the margins the clearings' own evaluated reads.
The theorem routes run at the order-two bulk's data with the walks
and boxes the family's own conjuncts, the shape binders discharged
through the family's shape read (`pfmShape_le`), the depth twelve
and the clearing power one, and the margins `(cC, cW, cI) =
(800, 1000, 1000)`; the raw cells read the same instances at
two vectors with the evaluated data displayed.  The parted variants
forge the scales past their margins: the floor at `y0 = 12/5`
against the doubled center margin, the contraction at `lam = 1/26`,
the defect cap at `1/100`, and the center margin doubled to
sixteen hundred.  The shape binders' own refusal is the cleared
evaluation's faithfulness at the scalar: a two-key factor read
against the nought power splits false.  The box-membership binder
carries no forge at this fixture — the center's clearing is
depth-free, so the floor's comparison stands at the depth
twenty-one outside the box, and the binder's isolation is
`domCert_form`'s own committed refusal at the walk.  The
family's defect reads positive, the swapped left side under every
scale of the right, so the lower arm's edge reads at the one-key
pair `lvCf`, `lvIf`: the image below the shifted center, the
defect's evaluated datum the balance partner of `1680000` at the
clearing `800000`, the comparison through the theorem and decided
raw at the ratio twenty-two against ten with two lower refused,
the site datum's read and its walk beside them. -/

private def bfMC : elim.Mat := evalPfm bfCf.1 12 1 200 1
private def bfMW : elim.Mat := evalPfm bfWf.1 12 1 200 1
private def bfMI : elim.Mat := evalPfm bfIf.1 12 1 200 1

example : (BPair.ofPos 800).oneValue (evalProf bfCf.2 12 1 200 1)
    ∧ (BPair.ofPos 1000).oneValue (evalProf bfWf.2 12 1 200 1)
    ∧ (BPair.ofPos 1000).oneValue (evalProf bfIf.2 12 1 200 1)
    ∧ (BPair.ofPos 800).oneValue (evalProf bfCf.2 13 1 200 1) := by
  decide +kernel
example : elim.matOneValue bfMC
    [[BPair.ofNat 2000, BPair.unit], [BPair.unit, BPair.ofNat 2000]] := by
  decide +kernel
example : elim.matOneValue bfMI
    [[BPair.ofNat 2600, BPair.ofNat 5],
     [BPair.ofNat 5, BPair.ofNat 2600]] := by decide +kernel
example : elim.matOneValue (devQ (bfMI, 1000) (bfMC, 800)).1
    [[BPair.ofNat 80000, BPair.ofNat 4000],
     [BPair.ofNat 4000, BPair.ofNat 80000]] := by decide +kernel

example : (quadForm (idMat 2) [BPair.ofNat 1, BPair.unit]).scale
      (800 * (2 * 5 + 1 * 1))
    ≤ (quadForm bfMC
        [BPair.ofNat 1, BPair.unit]).scale (1 * 5) :=
  floorCount_ptw bfCf (idMat 2) 2 2 1 1 5 (BPair.ofNat 1) 200
    [bx1 1 1, bx1 1 1] 12 1 1 200 800
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (pfmShape_le (by decide +kernel) 12) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    [BPair.ofNat 1, BPair.unit] rfl

example : (quadForm (idMat 2)
      (elim.matVec (elim.matSwap bfMW)
        [BPair.ofNat 1, BPair.unit])).scale (2 * 2)
    ≤ (quadForm (idMat 2) [BPair.ofNat 1, BPair.unit]).scale
        (1 * 1 * (1000 * 1000)) :=
  contrCount_ptw bfWf (idMat 2) 2 1 2 (BPair.ofNat 1) 200
    [bx1 1 1, bx1 1 1] 12 1 1 200 1000
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (pfmShape_le (by decide +kernel) 12) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    [BPair.ofNat 1, BPair.unit] rfl

example : (quadForm (devQ (bfMI, 1000)
        (bfMC, 800)).1
      [BPair.ofNat 1, BPair.unit]).scale 25
    ≤ (quadForm (idMat 2) [BPair.ofNat 1, BPair.unit]).scale
        (3 * (devQ (bfMI, 1000)
          (bfMC, 800)).2) :=
  dcapCount_hi bfCf bfIf (idMat 2) 2 3 25 (BPair.ofNat 1) 200
    [bx1 3 1, bx1 3 1] 12 1 1 200 1000 800
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (pfmShape_le (by decide +kernel) 12) (by decide +kernel)
    (pfmShape_le (by decide +kernel) 12) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    [BPair.ofNat 1, BPair.unit] rfl

example : ((quadForm (idMat 2) [BPair.ofNat 1, BPair.unit]).scale
        (3 * (devQ (bfMI, 1000)
          (bfMC, 800)).2)).swap
    ≤ (quadForm (devQ (bfMI, 1000)
        (bfMC, 800)).1
      [BPair.ofNat 1, BPair.unit]).scale 25 :=
  dcapCount_lo bfCf bfIf (idMat 2) 2 3 25 (BPair.ofNat 1) 200
    [bx1 3 1, bx1 3 1] 12 1 1 200 1000 800
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (pfmShape_le (by decide +kernel) 12) (by decide +kernel)
    (pfmShape_le (by decide +kernel) 12) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    [BPair.ofNat 1, BPair.unit] rfl

example : (quadForm (idMat 2)
      [BPair.ofNat 2, (BPair.ofNat 3).swap]).scale (800 * (2 * 5 + 1 * 1))
    ≤ (quadForm bfMC [BPair.ofNat 2, (BPair.ofNat 3).swap]).scale
        (1 * 5) := by decide +kernel
example : (quadForm (idMat 2)
      (elim.matVec (elim.matSwap bfMW)
        [BPair.ofNat 2, (BPair.ofNat 3).swap])).scale (2 * 2)
    ≤ (quadForm (idMat 2)
        [BPair.ofNat 2, (BPair.ofNat 3).swap]).scale
        (1 * 1 * (1000 * 1000)) := by decide +kernel
example : (quadForm (devQ (bfMI, 1000) (bfMC, 800)).1
      [BPair.ofNat 1, BPair.ofNat 1]).scale 25
    ≤ (quadForm (idMat 2) [BPair.ofNat 1, BPair.ofNat 1]).scale
        (3 * (devQ (bfMI, 1000) (bfMC, 800)).2) := by decide +kernel

example : ¬ ((quadForm (idMat 2) [BPair.ofNat 1, BPair.unit]).scale
      (800 * (12 * 5 + 1 * 5))
    ≤ (quadForm bfMC [BPair.ofNat 1, BPair.unit]).scale (5 * 5)) := by
  decide +kernel
example : ¬ ((quadForm (idMat 2) [BPair.ofNat 1, BPair.unit]).scale
      (1600 * 11)
    ≤ (quadForm bfMC [BPair.ofNat 1, BPair.unit]).scale (1 * 5)) := by
  decide +kernel
example : ¬ ((quadForm (idMat 2)
      (elim.matVec (elim.matSwap bfMW) [BPair.ofNat 1, BPair.unit])).scale
        (26 * 26)
    ≤ (quadForm (idMat 2) [BPair.ofNat 1, BPair.unit]).scale
        (1 * 1 * (1000 * 1000))) := by decide +kernel
example : ¬ ((quadForm (devQ (bfMI, 1000) (bfMC, 800)).1
      [BPair.ofNat 1, BPair.unit]).scale 100
    ≤ (quadForm (idMat 2) [BPair.ofNat 1, BPair.unit]).scale
        (1 * (devQ (bfMI, 1000) (bfMC, 800)).2)) := by decide +kernel

example : (quadForm (idMat 2) [BPair.ofNat 1, BPair.unit]).scale
      (800 * (2 * 5 + 1 * 1))
    ≤ (quadForm (evalPfm bfCf.1 21 1 200 1)
        [BPair.ofNat 1, BPair.unit]).scale (1 * 5) := by decide +kernel

example : ¬ (poly.evalClear
      (poly.mul [BPair.ofNat 1, BPair.ofNat 1]
        [BPair.ofNat 1, BPair.ofNat 1]) (BPair.ofNat 1) 2
      (1 + 0)).oneValue
      (poly.evalClear [BPair.ofNat 1, BPair.ofNat 1] (BPair.ofNat 1) 2 1
        * poly.evalClear [BPair.ofNat 1, BPair.ofNat 1]
          (BPair.ofNat 1) 2 0) := by
  decide +kernel

private def lvCf : PfMQ := ([[c10P]], c4P)
private def lvIf : PfMQ := ([[c2P]], c5P)
private def lvMI : elim.Mat := evalPfm lvIf.1 12 1 200 1
private def lvMC : elim.Mat := evalPfm lvCf.1 12 1 200 1

example : elim.matOneValue (devQ (lvMI, 1000) (lvMC, 800)).1
    [[(BPair.ofNat 1680000).swap]] := by decide +kernel
example : pfmOneValue (dcapLoSiteF lvCf lvIf [[BPair.ofNat 1]] 22 10)
    [[([[BPair.ofNat 20]], ([] : poly.PPoly))]] := by decide +kernel
example : domCertGo (BPair.ofNat 1) 200 0
    (dcapLoSiteF lvCf lvIf [[BPair.ofNat 1]] 22 10) [bx1 1 1] := by
  decide +kernel

example : ((quadForm [[BPair.ofNat 1]] [BPair.ofNat 1]).scale
      (22 * (devQ (lvMI, 1000) (lvMC, 800)).2)).swap
    ≤ (quadForm (devQ (lvMI, 1000) (lvMC, 800)).1
        [BPair.ofNat 1]).scale 10 :=
  dcapCount_lo lvCf lvIf [[BPair.ofNat 1]] 1 22 10 (BPair.ofNat 1) 200
    [bx1 1 1] 12 1 1 200 1000 800
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (pfmShape_le (by decide +kernel) 12) (by decide +kernel)
    (pfmShape_le (by decide +kernel) 12) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    [BPair.ofNat 1] rfl

example : ((quadForm [[BPair.ofNat 1]] [BPair.ofNat 1]).scale
      (22 * (devQ (lvMI, 1000) (lvMC, 800)).2)).swap
    ≤ (quadForm (devQ (lvMI, 1000) (lvMC, 800)).1
        [BPair.ofNat 1]).scale 10 := by decide +kernel

example : ¬ (((quadForm [[BPair.ofNat 1]] [BPair.ofNat 1]).scale
      (20 * (devQ (lvMI, 1000) (lvMC, 800)).2)).swap
    ≤ (quadForm (devQ (lvMI, 1000) (lvMC, 800)).1
        [BPair.ofNat 1]).scale 10) := by decide +kernel

/-! The defect's pairing pinned at a depth-varying center: at a
center family with an occupied square-scale key the collapse moves
with the depth — 544 at twelve against 569 at thirteen — and the
defect's evaluated datum reads the deeper center's transfer image
against the slab's own center, the balance partner of 64000 at the
depth twelve, with the read at the shifted center (the partner of
89000) refused: the centers' consecutive drift is the defect's own
summand (`lem:cornerpivot`(vii)). -/

private def cS : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat 2], [BPair.ofNat 1]], ([] : poly.PPoly))
private def dvCf : PfMQ := ([[cS]], c4P)
private def dvIf : PfMQ := ([[c3P]], c5P)

example : elim.matOneValue (evalPfm dvCf.1 12 1 200 1)
      [[BPair.ofNat 544]]
    ∧ elim.matOneValue (evalPfm dvCf.1 13 1 200 1)
      [[BPair.ofNat 569]] := by decide +kernel
example : elim.matOneValue (evalPfm (devFam dvCf dvIf).1 12 1 200 2)
    [[(BPair.ofNat 64000).swap]] := by decide +kernel
example : ¬ elim.matOneValue (evalPfm (devFam dvCf dvIf).1 12 1 200 2)
    [[(BPair.ofNat 89000).swap]] := by decide +kernel

/-! The walked segment's certificate at the family, deep-first: the
two-slab chain at the diagonal three and the bond one, its pivots
eight-thirds and three, over the depth range twelve to thirteen at
the scale one against the clearing two hundred and the stated scale
power one — position nought the deep pivot at depth thirteen and the
last position the boundary seed at depth twelve, the stated scale
`Pos.powC` two hundred, the diagonal's evaluated family six
hundred.  The deep pivot's deviation is minus a third and the seed
pivot's is the sum's unit — the boundary seed's cap holds at every
radius.  Every one of the stated
read's ten conjuncts carries its refusal below — the order list at
a forged two, the diagonal tie at a forged four, the bond tie at a
forged two, each walk box's clearing power at a forged three and
each clearing certificate's at a forged two — with the boundary
binders exercised at the base three hundred (the deeper point
453.005 and the boundary point four hundred fifty both outside the
box's one-half to two) and the stated power nought; and the
handover's own datum is isolated at two forged centers, one per
seed arm. -/


private def wDiag : List elim.Mat := [[[BPair.ofNat 3]], [[BPair.ofNat 3]]]
private def wOff : List elim.Mat := [wB]
private def wNs : List Nat := [1, 1]
private def wXs : List MatQ :=
  [([[BPair.ofNat 8]], (3 : Pos)), ofM [[BPair.ofNat 3]]]
private def wRs : List MatQ := [([[BPair.ofNat 1]], (3 : Pos))]

example : tailRead wDiag wOff wXs wRs wNs := by decide +kernel
example : greenprod.symRead wDiag := by decide +kernel
example : elim.matOneValue (inertia.matScale (Pos.powC 200 1) [[BPair.ofNat 3]])
      (evalPfm wAf 12 1 200 1)
    ∧ elim.matOneValue (inertia.matScale (Pos.powC 200 1) [[BPair.ofNat 3]])
      (evalPfm wAf 13 1 200 1) := by decide +kernel
example : famChainRead wFam wB 1 200 1 12 wDiag wOff wNs := by
  decide +kernel

/-! The seed pivot's deviation at the boundary end, depth twelve the
last position: the center reads twenty-four hundred at the clearing
eight hundred, the diagonal three, so the deviation is the sum's
unit and the cap holds at the radius two-thirds, the two splits the
unit congruence at sixteen hundred. -/

example : elim.matOneValue (evalPfm wCf.1 12 1 200 1)
    [[BPair.ofNat 2400]] := by decide +kernel
example : (BPair.ofPos (800 : Pos)).oneValue
    (evalProf wCf.2 12 1 200 1) := by decide +kernel
example : elim.matOneValue
    (devQ (ofM [[BPair.ofNat 3]]) (famYc wFam 1 200 1 12)).1
    [[BPair.unit]] := by decide +kernel

private def wYcS : MatQ := famYc wFam 1 200 1 12
private def wSp : Split 1 := spOne (BPair.ofNat 1600)

private theorem wCap : capQ (devQ (ofM [[BPair.ofNat 3]]) wYcS) wG 2 3
    wSp wSp := by decide +kernel

/-! The stated splits and the walk's conclusion: each pivot's split
sits at the identity congruence on its own block, both blocks above
the sum's unit, so the slab fold of the reversal counts is the
count's unit — the fold decided raw and the conclusion landed
through the theorem at the family's own evaluated reads. -/

private def wSps : List ((n : Nat) × Split n) :=
  [⟨1, spOne (BPair.ofNat 8)⟩, ⟨1, spOne (BPair.ofNat 3)⟩]

example : revListRead wXs wSps := by decide +kernel
example : revFold wSps = 0 := by decide +kernel

example : revFold wSps = 0 :=
  famChain_psd wFam wB wG 1 200 1 12 wDiag wOff wXs wRs wNs
    wSps wSp wSp (by decide +kernel) (by decide +kernel)
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    wCap
    (by decide +kernel)

/-! The stated read's refusals, one per conjunct: the order list,
the diagonal tie and the bond tie at forged data, each walk box and
each clearing certificate at a forged clearing power with every
further conjunct standing, and the two boundary binders at the base
three hundred and the stated power nought. -/

private def wFgDiag : List elim.Mat :=
  [[[BPair.ofNat 4]], [[BPair.ofNat 3]]]
private def wFam0 : CenterFam :=
  ⟨1, wAf, wCf, wWf, wIf, (1, 2), (2, 1), (2, 3), (11, 30),
   (2, 3), (BPair.ofNat 1, 200),
   [bx1 1 1], [bx1 1 1], [bx1 1 1], [bx1 1 1],
   bx1 1 1, bx1 1 1, bx1 1 1⟩

example : ¬ famChainRead wFam wB 1 200 1 12 wDiag wOff [1, 2] := by
  decide +kernel
example : ¬ famChainRead wFam wB 1 200 1 12 wFgDiag wOff wNs := by
  decide +kernel
example : ¬ famChainRead wFam wB 1 200 1 12 wDiag
    [[[BPair.ofNat 2]]] wNs := by decide +kernel
example : ¬ famChainRead wFam wB 1 200 1 300 wDiag wOff wNs := by
  decide +kernel
example : ¬ famChainRead wFam0 wB 1 200 0 12 wDiag wOff wNs := by
  decide +kernel
example : ¬ famChainRead { wFam with bxC := [bx1 1 3] } wB 1 200 1 12
    wDiag wOff wNs := by decide +kernel
example : ¬ famChainRead { wFam with bxF := [bx1 1 3] } wB 1 200 1 12
    wDiag wOff wNs := by decide +kernel
example : ¬ famChainRead { wFam with bxU := [bx1 1 3] } wB 1 200 1 12
    wDiag wOff wNs := by decide +kernel
example : ¬ famChainRead { wFam with bxL := [bx1 1 3] } wB 1 200 1 12
    wDiag wOff wNs := by decide +kernel
example : ¬ famChainRead { wFam with bxClC := bx1 1 2 } wB 1 200 1 12
    wDiag wOff wNs := by decide +kernel
example : ¬ famChainRead { wFam with bxClW := bx1 1 2 } wB 1 200 1 12
    wDiag wOff wNs := by decide +kernel
example : ¬ famChainRead { wFam with bxClI := bx1 1 2 } wB 1 200 1 12
    wDiag wOff wNs := by decide +kernel

/-! The depth orientation pinned at a depth-varying diagonal family:
the family two hundred at the square-scale key evaluates to
twenty-eight thousand eight hundred at depth twelve and thirty-three
thousand eight hundred at thirteen, so the stated diagonals read
deep-first — one hundred sixty-nine at position nought against one
hundred forty-four at the boundary — and the shallow-first spelling
refuses outright. -/

private def sAf : poly.PPoly × poly.PPoly :=
  ([[BPair.unit], [BPair.ofNat 200]], ([] : poly.PPoly))
private def vAf : List (List (poly.PPoly × poly.PPoly)) := [[sAf]]
private def vFam : CenterFam :=
  ⟨1, vAf, wCf, wWf, wIf, (1, 2), (2, 1), (2, 3), (11, 30),
   (2, 3), (BPair.ofNat 1, 200),
   [bx1 1 1], [bx1 1 1], [bx1 1 1], [bx1 1 1],
   bx1 1 0, bx1 1 0, bx1 1 0⟩
private def vDiag : List elim.Mat :=
  [[[BPair.ofNat 169]], [[BPair.ofNat 144]]]

example : elim.matOneValue (evalPfm vAf 12 1 200 1)
      [[BPair.ofNat 28800]]
    ∧ elim.matOneValue (evalPfm vAf 13 1 200 1)
      [[BPair.ofNat 33800]] := by decide +kernel
example : famChainRead vFam wB 1 200 1 12 vDiag wOff wNs := by
  decide +kernel
example : ¬ famChainRead vFam wB 1 200 1 12
    [[[BPair.ofNat 144]], [[BPair.ofNat 169]]] wOff wNs := by
  decide +kernel

/-! The seed cap's two arms at two forged centers, one parting per
arm.  The center six against the diagonal three reads the deviation
minus three at the clearing eight hundred, whose upper side at the
radius two-thirds still holds — minus seven thousand two hundred
against sixteen hundred — while the lower side parts at minus
sixteen hundred against minus seven thousand two hundred; and the
mirror center two reads the deviation eight hundred, whose lower
side holds at minus sixteen hundred against twenty-four hundred
while the upper side parts at twenty-four hundred against sixteen
hundred: each arm of the seed's stated cap prices its own side, no
split pair standing where either parting fires (`cap_hi`/`cap_lo`
read every split pair to the parted side).  The seed's cap is the
certificate's stated datum at its two split witnesses, consumed at
the walk's base; at a chain of the committed family the diagonal
tie reads the boundary at the family's own diagonal, whose
deviation from the center is vacant, so no chain forge reaches the
cap while the further binders stand — the two partings above are
the datum's own two sides' pins. -/

private def wFgYc : MatQ := (([[BPair.ofNat 4800]] : elim.Mat), (800 : Pos))

example : elim.matOneValue (devQ (ofM [[BPair.ofNat 3]]) wFgYc).1
    [[(BPair.ofNat 2400).swap]] := by decide +kernel
example : (quadForm (devQ (ofM [[BPair.ofNat 3]]) wFgYc).1
      [BPair.ofNat 1]).scale 3
    ≤ (quadForm wG [BPair.ofNat 1]).scale
        (2 * (devQ (ofM [[BPair.ofNat 3]]) wFgYc).2) := by decide +kernel
example : ¬ (((quadForm wG [BPair.ofNat 1]).scale
      (2 * (devQ (ofM [[BPair.ofNat 3]]) wFgYc).2)).swap
    ≤ (quadForm (devQ (ofM [[BPair.ofNat 3]]) wFgYc).1
        [BPair.ofNat 1]).scale 3) := by decide +kernel

private def wFgYc2 : MatQ := (([[BPair.ofNat 1600]] : elim.Mat), (800 : Pos))

example : elim.matOneValue (devQ (ofM [[BPair.ofNat 3]]) wFgYc2).1
    [[BPair.ofNat 800]] := by decide +kernel
example : ¬ ((quadForm (devQ (ofM [[BPair.ofNat 3]]) wFgYc2).1
      [BPair.ofNat 1]).scale 3
    ≤ (quadForm wG [BPair.ofNat 1]).scale
        (2 * (devQ (ofM [[BPair.ofNat 3]]) wFgYc2).2)) := by decide +kernel
example : ((quadForm wG [BPair.ofNat 1]).scale
      (2 * (devQ (ofM [[BPair.ofNat 3]]) wFgYc2).2)).swap
    ≤ (quadForm (devQ (ofM [[BPair.ofNat 3]]) wFgYc2).1
        [BPair.ofNat 1]).scale 3 := by decide +kernel

/-! The family walk at the three-slab chain: the constant diagonals
three over the depth range twelve to fourteen, the pivots
`(21/8, 8/3, 3)` each split at the identity congruence on its own
block, all above the sum's unit, and the slab fold of the reversal
counts is the count's unit — the conclusion landed through the
family walk at the chain's own stated data. -/

example : famChainRead wFam wB 1 200 1 12 chDiag chOff [1, 1, 1] := by
  decide +kernel

example : revFold chSps = 0 :=
  famChain_psd wFam wB wG 1 200 1 12 chDiag chOff chXs chRs [1, 1, 1]
    chSps wSp wSp (by decide +kernel) (by decide +kernel)
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    wCap
    (by decide +kernel)

/-! Clause (vii)'s whole chain at the family: the three-slab chain
`tridiag(3, 2, 3; 1, 3)` runs the pivots `(4, -1, 3)` at the
witnesses `(-1, 1)`, the crossing at the middle pivot with one
depth of dominance tail — the diagonal's floor `(3, 1)` tight at
the slab three, the depth's floor `(2, 1)` with the seed comparison
tight at three, and the transfer's cap one at the crossing's
withdrawn diagonal — and the walked segment the boundary slab three
at the family's own read.  The assembled datum's count closes at
one through `famChainCount`, decided raw beside the theorem
route. -/

private def fA0 : Mat := [[⟨4, 1⟩]]
private def fA1 : Mat := [[⟨3, 1⟩]]
private def fB0 : Mat := [[⟨2, 1⟩]]
private def fB1 : Mat := [[⟨4, 1⟩]]
private def fDiag : List Mat := [fA0, fA1, fA0]
private def fOff : List Mat := [fB0, fB1]
private def fNs : List Nat := [1, 1, 1]
private def fXs : List MatQ :=
  [([[⟨5, 1⟩]], 1), ([[⟨1, 2⟩]], 1), ofM fA0]
private def fRs : List MatQ := [([[⟨1, 2⟩]], 1), ([[⟨2, 1⟩]], 1)]
private def fSps : List ((k : Nat) × Split k) :=
  [⟨1, spOne ⟨5, 1⟩⟩, ⟨1, spOne ⟨1, 2⟩⟩, ⟨1, spOne ⟨4, 1⟩⟩]

/-- The assembled chain's congruence at the columns
`e₀ + e₁ - e₂`, `e₁ - e₂`, `e₂`, the images the recursion's own
pivots. -/
private def fT : Mat :=
  [[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨1, 2⟩, ⟨2, 1⟩]]
private def fTw : Mat :=
  [[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩]]
private def fSP : Split 3 :=
  ⟨⟨fT, rfl⟩, ⟨fTw, rfl⟩,
   [.one ⟨5, 1⟩, .one ⟨1, 2⟩, .one ⟨4, 1⟩], 0, rfl⟩

private def fSpc : (k : Nat) × Split k := ⟨1, spOne ⟨1, 2⟩⟩
private def fSpT : (k : Nat) × Split k := ⟨1, spOne ⟨2, 1⟩⟩
private def fDs : List DomStep := [⟨1, (3, 1), (2, 1), spK⟩]
private def fCs : List ((k : Nat) × (Pos × Pos) × Split k) := []

example : tailRead fDiag fOff fXs fRs fNs := by decide +kernel
example : revListRead fXs fSps := by decide +kernel
example : splitRead (assemble fDiag fOff) fSP := by decide +kernel
example : revAt fSP = 1 := by decide +kernel
example : domRead fSpc fSpT 1 1 fDiag fOff fXs fRs fNs fDs fCs := by
  decide +kernel
example : famChainRead wFam wB 1 200 1 12 (fDiag.drop (fDs.length + 1))
    (fOff.drop (fDs.length + 1)) (fNs.drop (fDs.length + 1)) := by
  decide +kernel

example : revAt fSP = 1 :=
  famChainCount wFam wB wG 1 200 1 12 fSpc fSpT 1 1 fDiag fOff fNs
    fXs fRs fDs fCs fSps fSP wSp wSp
    (by decide +kernel) (by decide +kernel)
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (fun _ => show revAt (spOne ⟨1, 2⟩) = 1 by decide +kernel)
    (by decide +kernel)
    wCap

/-! Clause (vii)'s whole chain at the order-two crossing: three
slabs at the orders `(1, 2, 1)`, the diagonals
`(4, diag(2, 2), 3)` at the bonds `(1, 0)` and `(3, 0)ᵀ`, whose
recursion runs the pivots `(5, diag(-1, 2), 3)` at the witnesses
`(-1, 0)ᵀ` and `(1, 0)` — the crossing the order-two pivot at its
one lower unit, the transfer's cap three at the withdrawn
diagonal's kept upper block, the diagonal's floor `(4, 1)` tight
at the slab four and the seed comparison tight at four — and the
walked segment the boundary slab three at the family's own read;
the assembled order-four datum's count closes at one through the
certificate, decided raw beside the theorem route. -/

private def m2A0 : Mat := [[⟨5, 1⟩]]
private def m2A1 : Mat := [[⟨3, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩]]
private def m2B0 : Mat := [[⟨2, 1⟩, ⟨1, 1⟩]]
private def m2B1 : Mat := [[⟨4, 1⟩], [⟨1, 1⟩]]
private def m2Diag : List Mat := [m2A0, m2A1, fA0]
private def m2Off : List Mat := [m2B0, m2B1]
private def m2Ns : List Nat := [1, 2, 1]
private def m2X1 : MatQ :=
  ([[⟨1, 2⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩]], 1)
private def m2Xs : List MatQ := [([[⟨6, 1⟩]], 1), m2X1, ofM fA0]
private def m2Rs : List MatQ :=
  [([[⟨1, 2⟩], [⟨1, 1⟩]], 1), ([[⟨2, 1⟩, ⟨1, 1⟩]], 1)]
private def m2Sp : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨3, 1⟩], 0, rfl⟩
private def m2Sps : List ((k : Nat) × Split k) :=
  [⟨1, spOne ⟨6, 1⟩⟩, ⟨2, m2Sp⟩, ⟨1, spOne ⟨4, 1⟩⟩]

/-- The assembled chain's congruence at the columns `e₀ + e₁ - e₃`,
`e₁ - e₃`, `e₂`, `e₃`, the images the recursion's own pivots. -/
private def m2T : Mat :=
  [[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨2, 1⟩]]
private def m2Tw : Mat :=
  [[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩],
   [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]]
private def m2SP : Split 4 :=
  ⟨⟨m2T, rfl⟩, ⟨m2Tw, rfl⟩,
   [.one ⟨6, 1⟩, .one ⟨1, 2⟩, .one ⟨3, 1⟩, .one ⟨4, 1⟩], 0, rfl⟩

private def m2Spc : (k : Nat) × Split k := ⟨2, m2Sp⟩
private def m2SpT : (k : Nat) × Split k := ⟨1, spOne ⟨4, 1⟩⟩
private def m2Ds : List DomStep := [⟨1, (4, 1), (1, 1), spK⟩]

example : tailRead m2Diag m2Off m2Xs m2Rs m2Ns := by decide +kernel
example : revListRead m2Xs m2Sps := by decide +kernel
example : splitRead (assemble m2Diag m2Off) m2SP := by decide +kernel
example : revAt m2SP = 1 := by decide +kernel
example : domRead m2Spc m2SpT 3 1 m2Diag m2Off m2Xs m2Rs m2Ns m2Ds
    fCs := by decide +kernel
example : revAt (ground.getAt dSp m2Sps m2Ds.length).2 = 1 := by
  decide +kernel
example : famChainRead wFam wB 1 200 1 12
    (m2Diag.drop (m2Ds.length + 1)) (m2Off.drop (m2Ds.length + 1))
    (m2Ns.drop (m2Ds.length + 1)) := by decide +kernel

example : revAt m2SP = 1 :=
  famChainCount wFam wB wG 1 200 1 12 m2Spc m2SpT 3 1 m2Diag m2Off
    m2Ns m2Xs m2Rs m2Ds fCs m2Sps m2SP wSp wSp
    (by decide +kernel) (by decide +kernel)
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (fun d => pfmShape_le (by decide +kernel) d)
    (fun d => poly.capOfLen (depthPoly_ble (by decide +kernel) d))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (fun _ => show revAt m2Sp = 1 by decide +kernel)
    (by decide +kernel)
    wCap
