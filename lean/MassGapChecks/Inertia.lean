import MassGap.Inertia
/-!
The check module for `lem:inertia`: the batteries re-read the pivot
split's identity instances by kernel `decide` — diagonal data at the
identity congruence with the kernel block trailing, a
positive-definite datum at an integer congruence (the clearing's
route), the mixed 2×2 block at its lower-side determinant, an
indefinite datum's split against Jacobi's rule (the coherence of the
two routes), the three-order psd chain, a rank-deficient datum's
kernel block, and the positive rescaling fixing the count.  The two
lists ride their own reads at the committed splits — the shapes and
the two counts joining at the order, the complement family's
independence at a unit-tail combination — and the general tier's
three theorems stand beside the counts they price: the exchange at
one datum's two splits, the monotonicity at a committed
positive-semidefinite difference, and the compression at two-column,
outer-column and empty selectors, each with the committed refusal
naming the hypothesis that bites — a non-psd difference reversing
the count order, and a forged compressed datum refused at the
congruence identity.  The tier's last two members ride beside them:
the balance-pair rescaling at the doubled indefinite datum — the
committed scaled split against the computed one, the count fixed,
and the refusal reading the block data genuinely moved — and the
dual forcing clause at the diagonal's own complement family, its
count joining the reversal count inside the order.  The addition at
a nonsingular principal pivot rides last: the `1 + 2` instance at
its solve witness with the three splits committed, the count
identity read both through the theorem and by the kernel, and the
forged witness's refusal isolating the solve.  The block-diagonal
instance closes the module: the `1 + 2` join at an off-block of
equal members with its two splits committed, and one pivot pair at
two off-blocks isolating that hypothesis — the counts adding at
equal members and parting at the occupied off-block.  The cleared
congruence rides on its own beside the split reads: the
positive-definite datum's pair pinned at `clearedCongr`, and the
isolating refusal at the determinant conjunct alone — the
equal-membered square's two product reads decided beside it.  The
congruence tier rides at the end: the datum's exchange off its
certificate, the count's invariance at a determinant-one congruence
with its image's own split — the refusal at the equal-membered scale
isolating the scale's off-unit read, every co-binder decided — the
join's form split at a `2 + 1` blocked vector with the row-count
binders' refusal at a vacant coupling, and the positive rescaling's
minor and entrywise reads.  The consequences tier closes the module
at the two compression corners: a `1 + 1` join's two corner counts
against the join's own, and the cap's compression at each corner —
the assembled cap's two splits decided, the two block ties decided,
and the corner caps concluded — with the forged assembled cap's
refusal isolating the cap binder at the corner where the conclusion
parts with it.  The determinant's split at the cleared deflation
closes the module: at a one-by-one pivot two against a one-by-one
coupling, tail and witness one, the pivot's determinant against the
deflation's and the pivot's square against the whole's read four
together, decided and through the theorem; the solve binder refuses
at a witness two against the coupling one, and the pivot's
determinant binder is the clause's frame at the split, both sides
reading the unit at a vacant pivot.  The block table's two small
orders ride next: the order-one row at an entry below the unit and
the order-two row at the mixed block of determinant `-4`, each
split decided and each count read through the general theorem, with
the diagonal certificate at a stated entry list beside them — the
three-order datum `diag(2, -2, 1)` split at its own entries and its
count the list's side fold, both read twice, and the refusal at an
entry on the sum's unit naming the nonsingularity binder.  The
existence clause closes the module at four data — an order-one
pivot, the mixed 2×2 whose diagonal reads the unit, a three-order
datum whose leading entry reads the unit so the descent exchanges
places before pivoting, and the vacant datum whose whole order is
the kernel block — each split decided at the construction and read
again through `mkSplit_read` with its count pinned, the vacant
datum's rank read beside it.  The cap algebra closes the module:
the trailing pad's entries pinned at a one-by-one deviation, the
block cap padded to the joined order, the two summands' caps
joined at the sum, and the cap rescaled and respelt, each read by
the kernel and again through its own theorem, with the two
refusals naming the binder that bites at each.  The withdrawn
diagonal's rank-one read rides last (`split_posPart`): at the
order-one datum two the kept upper entry prices the form at its
own, at the order-one datum minus two the withdrawn entry prices
it at the vacant read, and the split read is load-bearing — a
forged split at the entry minus one against the datum two refuses
the congruence with the display parting beside it, two against the
withdrawn vacant read.  The one-sided comparison closes the module
(`leAt`, `le_all`): the datum zero under the datum one at the site
datum's own order-one split, the comparison decided and the two
forms' order through the theorem, the theorem's shape binders the
certificate-shape frame at the truncating folds, and the exchanged
pair's refusal isolating the positive-semidefinite conjunct — the
site datum minus one occupying the count with the display parting
beside it.  The grouped form closes the module (`blockScaled_psd`):
the three-order gram `diag(1) ⊕ [[2, 1], [1, 2]]` at the two groups
`[0]` and `[1, 2]` scaled by the weights minus one and two, its
selection at the second group `[[4, 2], [2, 4]]` positive
semidefinite through the theorem beside its own `decide`, and the
weight binder's refusal at the first group, the weight minus one off
its upper side with the selection `[[-1]]` occupying the count.
-/

namespace inertia
set_option maxHeartbeats 4000000

open ground elim

/-- The order-one split at a stated diagonal entry, the one-site
records' shared fixture. -/
private def u : BPair := BPair.unit

/-! Diagonal data at the identity congruence: `diag(2, -1, 0)`, the
kernel block trailing, one lower-side unit. -/

private def sDiag : Mat := [[⟨3, 1⟩, u, u], [u, ⟨1, 2⟩, u], [u, u, u]]
private def spDiag : Split 3 :=
  ⟨⟨idMat 3, rfl⟩, ⟨idMat 3, rfl⟩, [.one ⟨3, 1⟩, .one ⟨1, 2⟩], 1, rfl⟩

theorem pin1 : splitRead sDiag spDiag := by decide +kernel
theorem pin2 : revAt spDiag = 1 := by decide +kernel
theorem pin3 : ¬ psdAt spDiag := by decide +kernel
theorem pin4 : rankAt spDiag = 2 := by decide +kernel

/-! A positive-definite datum at an integer congruence:
`[[2,1],[1,2]]` splits at `T = [[1,-1],[1,1]]` to `diag(6, 2)`, the
clearing absorbed by the block diagonal. -/

private def sPd : Mat := [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]
private def spPd : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 2⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨7, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩

/-! The cleared congruence read on its own at the positive-definite
datum's pair: `T = [[1,-1],[1,1]]` against its adjugate at the
determinant two, and the isolating refusal at the determinant
conjunct alone — the pair of equal-membered squares reads both
products against its own equal-membered determinant, so the two
product conjuncts hold while the determinant sits on the unit. -/

private def tSing : SqMat 2 := ⟨[[u, u], [u, u]], rfl⟩

theorem pin5 : clearedCongr spPd.T spPd.Tw := by decide +kernel
theorem pin6 : ¬ clearedCongr tSing tSing := by decide +kernel

/-- Refusal isolating the product conjuncts: the descent's minor
sits off the unit while the identity in the witness slot fails both
product reads. -/
theorem pin7 : (elim.minor spPd.T.val).offUnit := by decide +kernel
theorem pin8 : ¬ clearedCongr spPd.T
    (⟨elim.idMat 2, by decide +kernel⟩ : elim.SqMat 2) := by decide +kernel
theorem pin9 : matOneValue (matMul tSing.val tSing.val)
    (matScaleB (minor tSing.val) (idMat 2)) := by decide +kernel

theorem pin10 : splitRead sPd spPd := by decide +kernel
theorem pin11 : psdAt spPd := by decide +kernel
theorem pin12 : pdAt spPd := by decide +kernel
theorem pin13 : jacobiRev sPd = 0 := by decide +kernel
theorem pin14 : minorsUnequal sPd := by decide +kernel

/-! The mixed 2×2 block: `[[0,1],[1,0]]` at its lower-side
determinant, one unit per side. -/

private def spMix : Split 2 := ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two u ⟨2, 1⟩ u], 0, rfl⟩

theorem pin15 : splitRead exch2 spMix := by decide +kernel
theorem pin16 : revAt spMix = 1 := by decide +kernel

/-! An indefinite datum against Jacobi's rule: `[[1,2],[2,1]]`
splits at `T = [[1,-2],[0,1]]` to `diag(1, -3)`, and the minor
sequence `1, 1, -3` reads the one reversal, the two routes'
coherence. -/

private def sInd : Mat := [[⟨2, 1⟩, ⟨3, 1⟩], [⟨3, 1⟩, ⟨2, 1⟩]]
private def spInd : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 3⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨3, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨2, 1⟩, .one ⟨1, 4⟩], 0, rfl⟩

theorem pin17 : splitRead sInd spInd := by decide +kernel
theorem pin18 : revAt spInd = 1 := by decide +kernel
theorem pin19 : jacobiRev sInd = 1 := by decide +kernel
theorem pin20 : minorsUnequal sInd := by decide +kernel

/-! The three-order psd chain `[[2,1,0],[1,2,1],[0,1,2]]`: the
split at the cleared descent's congruence, Jacobi's rule at the
minors `2, 3, 4`, and the leading compression's count at or below
the whole's. -/

private def sChain : Mat :=
  [[⟨3, 1⟩, ⟨2, 1⟩, u], [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨3, 1⟩]]
private def spChain : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩, ⟨1, 3⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨4, 1⟩]], rfl⟩,
   ⟨[[⟨7, 1⟩, ⟨4, 1⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨4, 1⟩, ⟨3, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨3, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨7, 1⟩, .one ⟨13, 1⟩], 0, rfl⟩

theorem pin21 : splitRead sChain spChain := by decide +kernel
theorem pin22 : psdAt spChain := by decide +kernel
theorem pin23 : minorsUnequal sChain := by decide +kernel
theorem pin24 : jacobiRev sChain = 0 := by decide +kernel
theorem pin25 : jacobiRev [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]
    ≤ jacobiRev sChain := by decide +kernel

/-! A rank-deficient datum's kernel block: `[[1,1],[1,1]]` at
`T = [[1,-1],[0,1]]`, one nonsingular order with the kernel
trailing. -/

private def sKer : Mat := [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]
private def spKer : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩, [.one ⟨2, 1⟩], 1, rfl⟩

theorem pin26 : splitRead sKer spKer := by decide +kernel
theorem pin27 : psdAt spKer := by decide +kernel
theorem pin28 : ¬ pdAt spKer := by decide +kernel
theorem pin29 : rankAt spKer = 1 := by decide +kernel

/-! The positive rescaling fixes the count: `3 S` at the same
congruence splits to the scaled diagonal at one lower-side unit. -/

private def spInd3 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 3⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨3, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩, .one ⟨1, 10⟩], 0, rfl⟩

theorem pin30 : splitRead (matScale 3 sInd) spInd3 := by decide +kernel
theorem pin31 : revAt spInd3 = revAt spInd := by decide +kernel

/-! The rescaling's transport at the balance-pair weighting: `2 S`
at `[[1,2],[2,1]]` splits at `spInd`'s own congruence to the scaled
diagonal `diag(2, -6)` — the committed split beside the computed one
(`scaleSplit`, the blocks scaled entrywise), the invariance theorem's
count identity beside the raw decision, and the block data genuinely
moved, the refusal naming the scale. -/

private def wTwo : BPair := ⟨3, 1⟩

private def spIndScale : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 3⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨3, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨1, 7⟩], 0, rfl⟩

theorem pin32 : matOneValue (matScaleB wTwo sInd)
    [[⟨3, 1⟩, ⟨5, 1⟩], [⟨5, 1⟩, ⟨3, 1⟩]] := by decide +kernel
theorem pin33 : splitRead (matScaleB wTwo sInd) spIndScale := by decide +kernel

theorem pin34 : revAt spIndScale = revAt spInd :=
  rev_scale wTwo (by decide +kernel) sInd spInd spIndScale (by decide +kernel) (by decide +kernel)

theorem pin35 : revAt spIndScale = revAt spInd := by decide +kernel

theorem pin36 : splitRead (matScaleB wTwo sInd) (scaleSplit wTwo spInd) :=
  scaleSplit_read wTwo (by decide +kernel) sInd spInd (by decide +kernel)

theorem pin37 : splitRead (matScaleB wTwo sInd) (scaleSplit wTwo spInd) := by decide +kernel

theorem pin38 : revAt (scaleSplit wTwo spInd) = revAt spInd :=
  scaleSplit_rev wTwo (by decide +kernel) spInd

theorem pin39 : revAt (scaleSplit wTwo spInd) = revAt spInd := by decide +kernel

theorem pin40 : matOneValue (blockMat (scaleSplit wTwo spInd).blocks 0)
    [[⟨3, 1⟩, u], [u, ⟨1, 7⟩]] := by decide +kernel

theorem pin41 : ¬ matOneValue (blockMat (scaleSplit wTwo spInd).blocks 0)
    (blockMat spInd.blocks 0) := by decide +kernel

/-! The diagonal's site structure: the datum at a form pair reads
entrywise, `A = B + S`, with the entry read decided and through the
theorem — the first member's entry joined to the second's memberwise
swap.  Every load-bearing binder refuses at the theorem's own
conclusion read at the forge: either member ragged at the truncated
seam, either member short of the row key, and the beyond-order
column key at the vacant read. -/

theorem pin42 : matOneValue
    (siteDatum [[⟨3, 1⟩, u], [u, ⟨3, 1⟩]] [[⟨2, 1⟩, u], [u, ⟨5, 1⟩]])
    [[⟨2, 1⟩, u], [u, ⟨1, 3⟩]] := by decide +kernel

theorem pin43 : elim.sqAt (idMat 3) 3 := by decide +kernel
theorem pin44 : elim.sqAt (idMat 3) 3 := sqAt_idMat 3

private def sdA : Mat := [[⟨3, 1⟩, ⟨1, 2⟩], [⟨2, 1⟩, ⟨3, 1⟩]]
private def sdB : Mat := [[⟨2, 1⟩, ⟨1, 4⟩], [⟨1, 6⟩, ⟨5, 1⟩]]
private def sdAr : Mat := [[⟨3, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩]]
private def sdBr : Mat := [[⟨2, 1⟩], [⟨1, 6⟩, ⟨5, 1⟩]]
private def sdA1 : Mat := [[⟨3, 1⟩, ⟨1, 2⟩]]
private def sdB1 : Mat := [[⟨2, 1⟩, ⟨1, 4⟩]]

theorem pin45 : getAt u (getAt [] (siteDatum sdA sdB) 0) 1
    = (⟨1, 2⟩ : BPair) + (⟨1, 4⟩ : BPair).swap := by decide +kernel
theorem pin46 : getAt u (getAt [] (siteDatum sdA sdB) 0) 1
    = (⟨1, 2⟩ : BPair) + (⟨1, 4⟩ : BPair).swap :=
  siteDatum_entry sdA sdB 2 (by decide +kernel) (by decide +kernel) 0 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin47 : ¬ (getAt u (getAt [] (siteDatum sdAr sdB) 0) 1
    = getAt u (getAt [] sdAr 0) 1
      + (getAt u (getAt [] sdB 0) 1).swap) := by decide +kernel
theorem pin48 : ¬ (getAt u (getAt [] (siteDatum sdA sdBr) 0) 1
    = getAt u (getAt [] sdA 0) 1
      + (getAt u (getAt [] sdBr 0) 1).swap) := by decide +kernel
theorem pin49 : ¬ (getAt u (getAt [] (siteDatum sdA1 sdB) 1) 1
    = getAt u (getAt [] sdA1 1) 1
      + (getAt u (getAt [] sdB 1) 1).swap) := by decide +kernel
theorem pin50 : ¬ (getAt u (getAt [] (siteDatum sdA sdB1) 1) 1
    = getAt u (getAt [] sdA 1) 1
      + (getAt u (getAt [] sdB1 1) 1).swap) := by decide +kernel
theorem pin51 : ¬ (getAt u (getAt [] (siteDatum sdA sdB) 0) 2
    = getAt u (getAt [] sdA 0) 2
      + (getAt u (getAt [] sdB 0) 2).swap) := by decide +kernel

/-! The two-sided cap: `[[1,2],[2,1]]` capped at `4·I`, the two
splits at their 2×2 blocks on the upper side. -/

theorem pin52 : capAt sInd (matScale 4 (idMat 2))
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two ⟨4, 1⟩ ⟨1, 3⟩ ⟨4, 1⟩], 0, rfl⟩
      : Split 2)
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two ⟨6, 1⟩ ⟨3, 1⟩ ⟨6, 1⟩], 0, rfl⟩
      : Split 2) := by decide +kernel

/-! The rank-swap identity's instance: the memberwise swap at the
one congruence, the two counts joining to the rank. -/

private def spIndSw : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 3⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨3, 1⟩], [⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨4, 1⟩], 0, rfl⟩

theorem pin53 : splitRead (matSwap sInd) spIndSw := by decide +kernel
theorem pin54 : revAt spInd + revAt spIndSw = rankAt spInd := by decide +kernel

/-! The transport tier at the committed data: the
positive-semidefinite split's theorem read beside the kernel's own at
a stated vector, and the occupied count's witness clause beside the
decided lower-side read at the indefinite diagonal's own place. -/

theorem pin55 : ¬ (dotN [⟨2, 1⟩, ⟨1, 2⟩] (matVec sPd [⟨2, 1⟩, ⟨1, 2⟩])
    < BPair.unit) :=
  psd_all sPd spPd (by decide +kernel) (by decide +kernel) [⟨2, 1⟩, ⟨1, 2⟩] rfl

theorem pin56 : ¬ (dotN [⟨2, 1⟩, ⟨1, 2⟩] (matVec sPd [⟨2, 1⟩, ⟨1, 2⟩])
    < BPair.unit) := by decide +kernel

theorem pin57 : ∃ w : List BPair, w.length = 3
    ∧ dotN w (matVec sDiag w) < BPair.unit :=
  rev_witness sDiag spDiag (by decide +kernel) (by decide +kernel)

theorem pin58 : dotN [u, ⟨2, 1⟩, u] (matVec sDiag [u, ⟨2, 1⟩, u])
    < BPair.unit := by decide +kernel

/-! The order tie's refusal: a datum off the certificate's stated
order is refused at the chokepoint's shape read; an
under-dimensioned congruence is unrepresentable at the carrier,
the type the guard. -/

theorem pin59 : ¬ splitRead [[⟨1, 2⟩]]
    (⟨⟨[], rfl⟩, ⟨[], rfl⟩, [], 0, rfl⟩ : Split 0) := by decide +kernel

/-! `lem:inertia`'s two lists at the committed splits: the lower
list one vector per lower-side unit, the complement list the rest of
the order with the kernel block's columns trailing, the two counts
joining at the split's order, and the strict and side reads at
stated coefficient vectors beside the kernel's own decisions. -/

theorem pin60 : matOneValue (lowerList spDiag) [[u, ⟨2, 1⟩, u]] := by decide +kernel
theorem pin61 : matOneValue (complList spDiag)
    [[⟨2, 1⟩, u, u], [u, u, ⟨2, 1⟩]] := by decide +kernel
theorem pin62 : (lowerList spDiag).length = revAt spDiag := by decide +kernel
theorem pin63 : revAt spDiag + (complList spDiag).length = 3 := by decide +kernel

theorem pin64 : (lowerList spPd).length = 0 := by decide +kernel
theorem pin65 : matOneValue (complList spPd)
    [[⟨2, 1⟩, ⟨2, 1⟩], [⟨1, 2⟩, ⟨2, 1⟩]] := by decide +kernel
theorem pin66 : revAt spPd + (complList spPd).length = 2 := by decide +kernel

theorem pin67 : matOneValue (lowerList spMix) [[⟨1, 2⟩, ⟨3, 1⟩]] := by decide +kernel
theorem pin68 : matOneValue (complList spMix) [[⟨1, 2⟩, ⟨1, 3⟩]] := by decide +kernel
theorem pin69 : (lowerList spMix).length = revAt spMix := by decide +kernel
theorem pin70 : revAt spMix + (complList spMix).length = 2 := by decide +kernel

theorem pin71 : dotN (combo 3 [⟨2, 1⟩] (lowerList spDiag))
    (matVec sDiag (combo 3 [⟨2, 1⟩] (lowerList spDiag))) < BPair.unit :=
  lowerList_strict sDiag spDiag (by decide +kernel) [⟨2, 1⟩] (by decide +kernel) (by decide +kernel)

theorem pin72 : dotN (combo 3 [⟨2, 1⟩] (lowerList spDiag))
    (matVec sDiag (combo 3 [⟨2, 1⟩] (lowerList spDiag)))
    < BPair.unit := by decide +kernel

theorem pin73 : dotN (combo 2 [⟨2, 1⟩] (lowerList spMix))
    (matVec exch2 (combo 2 [⟨2, 1⟩] (lowerList spMix))) < BPair.unit :=
  lowerList_strict exch2 spMix (by decide +kernel) [⟨2, 1⟩] (by decide +kernel) (by decide +kernel)

theorem pin74 : ¬ (dotN (combo 2 [⟨3, 1⟩] (complList spMix))
    (matVec exch2 (combo 2 [⟨3, 1⟩] (complList spMix))) < BPair.unit) :=
  complList_side exch2 spMix (by decide +kernel) [⟨3, 1⟩] (by decide +kernel)

theorem pin75 : ¬ (dotN (combo 2 [⟨3, 1⟩] (complList spMix))
    (matVec exch2 (combo 2 [⟨3, 1⟩] (complList spMix)))
    < BPair.unit) := by decide +kernel

/-! The count's three general reads at the committed data.  The
exchange: `[[1,2],[2,1]]` splits a second time at the lower
congruence `T = [[1,0],[-2,1]]` to `diag(-3, 1)`, the pivot order
reversed against `spInd`'s, and the two splits read the one count. -/

private def spInd2 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, u], [⟨1, 3⟩, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, u], [⟨3, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 4⟩, .one ⟨2, 1⟩], 0, rfl⟩

theorem pin76 : splitRead sInd spInd2 := by decide +kernel

theorem pin77 : revAt spInd = revAt spInd2 :=
  rev_exchange sInd spInd spInd2 (by decide +kernel) (by decide +kernel)

theorem pin78 : revAt spInd = revAt spInd2 := by decide +kernel

/-! The monotonicity at a positive-semidefinite difference:
`[[1,2],[2,1]] ⪯ [[2,1],[1,2]]`, the site datum `[[1,-1],[-1,1]]`
splitting at `T = [[1,1],[0,1]]` to the rank-one block with the
kernel trailing, so the upper datum's count sits at or below the
lower's. -/

private def spDiff : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨2, 1⟩], 1, rfl⟩

theorem pin79 : splitRead (siteDatum sPd sInd) spDiff := by decide +kernel
theorem pin80 : psdAt spDiff := by decide +kernel

theorem pin81 : revAt spPd ≤ revAt spInd :=
  rev_mono sInd sPd spDiff spInd spPd (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem pin82 : revAt spPd ≤ revAt spInd := by decide +kernel

/-! The compression comparison at a two-column selector:
`diag(2, -1, 0)` compressed to its leading `diag(2, -1)` keeps the
count, and compressed to `diag(2, 0)` at the outer columns drops
it — the cap the theorem states in both instances. -/

private def pLead : Mat := [[⟨2, 1⟩, u], [u, ⟨2, 1⟩], [u, u]]
private def pOuter : Mat := [[⟨2, 1⟩, u], [u, u], [u, ⟨2, 1⟩]]

private def spLead : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨1, 2⟩], 0, rfl⟩
private def spOuter : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨3, 1⟩], 1, rfl⟩

theorem pin83 : splitRead
    (matMul (transposeM pLead) (matMul sDiag pLead)) spLead := by decide +kernel
theorem pin84 : splitRead
    (matMul (transposeM pOuter) (matMul sDiag pOuter)) spOuter := by decide +kernel

theorem pin85 : revAt spLead ≤ revAt spDiag :=
  rev_compress sDiag pLead (by decide +kernel) rfl (by decide +kernel) spLead
    (by decide +kernel) spDiag (by decide +kernel)

theorem pin86 : revAt spLead ≤ revAt spDiag := by decide +kernel

theorem pin87 : revAt spOuter ≤ revAt spDiag :=
  rev_compress sDiag pOuter (by decide +kernel) rfl (by decide +kernel) spOuter
    (by decide +kernel) spDiag (by decide +kernel)

theorem pin88 : revAt spOuter ≤ revAt spDiag := by decide +kernel

/-! The two lists' own reads at the committed splits: the shapes off
the certificate alone, the lower count at the reversal count and the
two counts joining at the order, each theorem beside the raw
decision. -/

theorem pin89 : rowsLen 3 (lowerList spDiag) := lowerList_rowsLen spDiag
theorem pin90 : rowsLen 3 (lowerList spDiag) := by decide +kernel

theorem pin91 : rowsLen 3 (complList spDiag) := complList_rowsLen spDiag
theorem pin92 : rowsLen 3 (complList spDiag) := by decide +kernel

theorem pin93 : rowsLen 2 (lowerList spMix) := lowerList_rowsLen spMix
theorem pin94 : rowsLen 2 (complList spMix) := complList_rowsLen spMix

theorem pin95 : (lowerList spDiag).length = revAt spDiag :=
  lowerList_length sDiag spDiag (by decide +kernel)
theorem pin96 : (lowerList spDiag).length = revAt spDiag := by decide +kernel

theorem pin97 : revAt spDiag + (complList spDiag).length = 3 :=
  complList_length sDiag spDiag (by decide +kernel)
theorem pin98 : revAt spDiag + (complList spDiag).length = 3 := by decide +kernel

theorem pin99 : (lowerList spMix).length = revAt spMix :=
  lowerList_length exch2 spMix (by decide +kernel)
theorem pin100 : revAt spMix + (complList spMix).length = 2 :=
  complList_length exch2 spMix (by decide +kernel)

/-! The complement family's independence at the diagonal's two
complement columns: the unit-tail combination reads unit
coefficients, the clearing's transport. -/

theorem pin101 : poly.unitTail [u, u] :=
  complList_indep sDiag spDiag (by decide +kernel) [u, u] (by decide +kernel) (by decide +kernel)

theorem pin102 : poly.unitTail (combo 3 [u, u] (complList spDiag)) := by decide +kernel
theorem pin103 : poly.unitTail [u, u] := by decide +kernel

/-! The dual forcing clause at the diagonal's own complement family:
independent by the clearing's transport and at or above the sum's
unit at every combination, its count joins the reversal count inside
the order — `2 + 1 ≤ 3`, the theorem's own read beside the raw
arithmetic. -/

theorem pin104 : (complList spDiag).length + revAt spDiag ≤ 3 :=
  forcing_upper sDiag spDiag (by decide +kernel) (complList spDiag)
    (complList_rowsLen spDiag)
    (complList_indep sDiag spDiag (by decide +kernel))
    (complList_side sDiag spDiag (by decide +kernel))

theorem pin105 : (complList spDiag).length + revAt spDiag ≤ 3 := by decide +kernel

theorem pin106 : 2 + 1 ≤ 3 := by decide +kernel

/-! The monotonicity's positive-semidefinite hypothesis biting: the
difference the other way, `[[2,1],[1,2]] ⪯̸ [[1,2],[2,1]]`, splits at
one reversal, and the count order reverses with it — the split data
of both matrices and the site datum's own split all committed, the
psd read alone between them and a false conclusion. -/

private def spDiffRev : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 2⟩], 1, rfl⟩

theorem pin107 : splitRead (siteDatum sInd sPd) spDiffRev := by decide +kernel
theorem pin108 : ¬ psdAt spDiffRev := by decide +kernel
theorem pin109 : ¬ (revAt spInd ≤ revAt spPd) := by decide +kernel

/-! The compression's congruence identity biting: a forged compressed
datum at the leading selector — two lower-side entries where the
product carries one — is refused at the split read, and its count
sits past the datum's own. -/

private def spForge : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨1, 2⟩], 0, rfl⟩

theorem pin110 : ¬ splitRead
    (matMul (transposeM pLead) (matMul sDiag pLead)) spForge := by decide +kernel
theorem pin111 : ¬ (revAt spForge ≤ revAt spDiag) := by decide +kernel

/-! The empty selector: the compression at the vacant carrier, the
compressed datum the empty matrix at the vacant split, the cap
reading the datum's own count from below. -/

private def pNil : Mat := [[], [], []]
private def spNil : Split 0 := ⟨⟨[], rfl⟩, ⟨[], rfl⟩, [], 0, rfl⟩

theorem pin112 : splitRead (matMul (transposeM pNil) (matMul sDiag pNil))
    spNil := by decide +kernel

theorem pin113 : revAt spNil ≤ revAt spDiag :=
  rev_compress sDiag pNil (by decide +kernel) rfl (by decide +kernel) spNil
    (by decide +kernel) spDiag (by decide +kernel)

theorem pin114 : revAt spNil ≤ revAt spDiag := by decide +kernel

/-! `lem:inertia`'s addition at a nonsingular principal pivot, the
`1 + 2` instance: the pivot `[2]`, the coupling `[1, -1]`, the
trailing block `diag(-1, 2)` and the solve witness `C = [1, -1]` at
`P C = 2 B`.  The assembled datum is `[[2,1,-1],[1,-1,0],[-1,0,2]]`
at the lift's own congruence (the columns `2 e₁`, `(1,-2,0)`,
`(-1,0,-2)` — the padding above the negated determinant), splitting
to `diag(8) ⊕ [[-6,2],[2,6]]`; the deflation is the cleared Schur
complement `4 Q - 2 Bᵀ C = [[-6,2],[2,6]]` itself, one lower-side
unit at its negative determinant, and the pivot's count is zero —
`1 = 0 + 1`, the theorem's read beside the raw decision.  The
refusal isolates the solve: the forged witness `C' = [-5, 5]` fails
the solve read, its own deflation `[[6,-10],[-10,18]]` is positive
definite at a committed split, and the count identity genuinely
fails there. -/

private def aP : Mat := [[⟨3, 1⟩]]
private def aB : Mat := [[⟨2, 1⟩, ⟨1, 2⟩]]
private def aQ : Mat := [[⟨1, 2⟩, u], [u, ⟨3, 1⟩]]
private def aCw : Mat := [[⟨2, 1⟩, ⟨1, 2⟩]]

theorem pin115 : blockJoin aP aB aQ
    = [[⟨3, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩], [⟨2, 1⟩, ⟨1, 2⟩, u],
       [⟨1, 2⟩, u, ⟨3, 1⟩]] := by decide +kernel

theorem pin116 : matOneValue (deflMat aP aB aQ aCw)
    [[⟨1, 7⟩, ⟨3, 1⟩], [⟨3, 1⟩, ⟨7, 1⟩]] := by decide +kernel

theorem pin117 : matOneValue (matMul aP aCw) (matScaleB (minor aP) aB) := by decide +kernel

theorem pin118 : matOneValue (transposeM aP) aP := by decide +kernel
theorem pin119 : ¬ (minor aP).oneValue BPair.unit := by decide +kernel

private def aSpS : Split 3 :=
  ⟨⟨[[⟨3, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨1, 3⟩, u], [u, u, ⟨1, 3⟩]], rfl⟩,
   ⟨[[⟨5, 1⟩, ⟨3, 1⟩, ⟨1, 3⟩], [u, ⟨1, 5⟩, u], [u, u, ⟨1, 5⟩]], rfl⟩,
   [.one ⟨9, 1⟩, .two ⟨1, 7⟩ ⟨3, 1⟩ ⟨7, 1⟩], 0, rfl⟩

private def aSpP : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one ⟨3, 1⟩], 0, rfl⟩

private def aSpD : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 3⟩], [u, ⟨1, 7⟩]], rfl⟩,
   ⟨[[⟨1, 7⟩, ⟨3, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨1, 7⟩, .one ⟨241, 1⟩], 0, rfl⟩

theorem pin120 : splitRead (blockJoin aP aB aQ) aSpS := by decide +kernel
theorem pin121 : splitRead aP aSpP := by decide +kernel
theorem pin122 : splitRead (deflMat aP aB aQ aCw) aSpD := by decide +kernel

theorem pin123 : revAt aSpS = 1 := by decide +kernel
theorem pin124 : revAt aSpP = 0 := by decide +kernel
theorem pin125 : revAt aSpD = 1 := by decide +kernel

theorem pin126 : revAt aSpS = revAt aSpP + revAt aSpD :=
  rev_add (k := 1) (m := 2) aP aB aQ aCw (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    aSpS (by decide +kernel) aSpP (by decide +kernel) aSpD (by decide +kernel)

theorem pin127 : revAt aSpS = revAt aSpP + revAt aSpD := by decide +kernel

/-! The solve witness biting: the forged witness is refused at the
solve read, and its deflation's own split reads a count the addition
would have to carry — `1 ≠ 0 + 0`. -/

private def aCwBad : Mat := [[⟨1, 6⟩, ⟨6, 1⟩]]

theorem pin128 : ¬ matOneValue (matMul aP aCwBad)
    (matScaleB (minor aP) aB) := by decide +kernel

theorem pin129 : matOneValue (deflMat aP aB aQ aCwBad)
    [[⟨7, 1⟩, ⟨1, 11⟩], [⟨1, 11⟩, ⟨19, 1⟩]] := by decide +kernel

private def aSpDBad : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨11, 1⟩], [u, ⟨7, 1⟩]], rfl⟩,
   ⟨[[⟨7, 1⟩, ⟨1, 11⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨7, 1⟩, .one ⟨49, 1⟩], 0, rfl⟩

theorem pin130 : splitRead (deflMat aP aB aQ aCwBad) aSpDBad := by decide +kernel
theorem pin131 : psdAt aSpDBad := by decide +kernel
theorem pin132 : ¬ (revAt aSpS = revAt aSpP + revAt aSpDBad) := by decide +kernel

/-! The biting hypotheses, refused at committed data: the
positivity in the count preservation — an off-unit lower-side
scale keeps the congruence read while moving the count — and the
independence in the dual clause — a doubled complement family
keeps every at-or-above read while breaking the price. -/

theorem pin133 : splitRead (matScaleB ⟨1, 2⟩ sPd) (scaleSplit ⟨1, 2⟩ spPd) := by
  decide +kernel
theorem pin134 : ¬ (revAt (scaleSplit ⟨1, 2⟩ spPd) = revAt spPd) := by decide +kernel
theorem pin135 : ¬ ((complList spDiag ++ complList spDiag).length
    + revAt spDiag ≤ 3) := by decide +kernel

/-! `lem:inertia`'s addition at a block diagonal, the `1 + 2`
instance at the addition's own pivot and trailing data: the pivot
`[2]` beside `diag(-1, 2)` at an off-block of equal members, the
join `diag(2, -1, 2)` splitting at the identity congruence, and the
count `1 = 0 + 1` read both through the theorem and by the kernel. -/

private def jSpQ : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨3, 1⟩], 0, rfl⟩

private def jSpJ : Split 3 :=
  ⟨⟨idMat 3, rfl⟩, ⟨idMat 3, rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨1, 2⟩, .one ⟨3, 1⟩], 0, rfl⟩

theorem pin136 : blockJoin aP (List.replicate 1 (List.replicate 2 u)) aQ
    = [[⟨3, 1⟩, u, u], [u, ⟨1, 2⟩, u], [u, u, ⟨3, 1⟩]] := by decide +kernel

theorem pin137 : splitRead aQ jSpQ := by decide +kernel
theorem pin138 : splitRead
    (blockJoin aP (List.replicate 1 (List.replicate 2 u)) aQ) jSpJ := by
  decide +kernel

theorem pin139 : revAt jSpJ = revAt aSpP + revAt jSpQ :=
  rev_join (k := 1) (m := 2) aP aQ
    aSpP (by decide +kernel) jSpQ (by decide +kernel) jSpJ (by decide +kernel)

theorem pin140 : revAt jSpJ = revAt aSpP + revAt jSpQ := by decide +kernel

/-! The off-block's own reading biting, at one pivot pair and two
off-blocks: at equal members the join `diag(2, 2)` reads the two
counts' sum at the sum's unit, and at the occupied off-block `[3]`
the join `[[2,3],[3,2]]` reads one lower-side unit at its mixed
block — the counts genuinely part. -/

private def jSpNull : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩

private def jB : Mat := [[⟨4, 1⟩]]

private def jSpB : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.two ⟨3, 1⟩ ⟨4, 1⟩ ⟨3, 1⟩], 0, rfl⟩

theorem pin141 : splitRead
    (blockJoin aP (List.replicate 1 (List.replicate 1 u)) aP) jSpNull := by
  decide +kernel

theorem pin142 : revAt jSpNull = revAt aSpP + revAt aSpP :=
  rev_join (k := 1) (m := 1) aP aP
    aSpP (by decide +kernel) aSpP (by decide +kernel) jSpNull (by decide +kernel)

theorem pin143 : blockJoin aP jB aP = [[⟨3, 1⟩, ⟨4, 1⟩], [⟨4, 1⟩, ⟨3, 1⟩]] := by
  decide +kernel
theorem pin144 : splitRead (blockJoin aP jB aP) jSpB := by decide +kernel
theorem pin145 : ¬ (revAt jSpB = revAt aSpP + revAt aSpP) := by decide +kernel

/-! The identity's own product and the witness's fixed read: the
identity against a stated matrix is that matrix (`idMat_matMul`,
the one-index pairing at the diagonal key), and at the
orthogonality `Tᵀ T = 1` a `T`-fixed matrix is fixed by the witness
too (`fixed_transpose`).  The bench is the order-two exchange, its
own transpose and inverse, with the equal-entry matrix its fixed
one; the refusal sits at the identity, off that exchange's fixed
set. -/


theorem pin146 : matOneValue (matMul (idMat 2) exch2) exch2 :=
  idMat_matMul (k := 2) 2 exch2 (by decide +kernel) rfl (by decide +kernel)

theorem pin147 : matOneValue (matMul (idMat 3) (idMat 3)) (idMat 3) :=
  idMat_matMul (k := 3) 3 (idMat 3) (rowsLen_idMat 3) (length_idMat 3) (by decide +kernel)

private def exFix : Mat := [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]

theorem pin148 : matOneValue (matMul (transposeM exch2) exFix) exFix :=
  fixed_transpose 2 exch2 exFix (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)

theorem pin149 : ¬ matOneValue (matMul exch2 (idMat 2)) (idMat 2) := by decide +kernel

/-! `lem:inertia`'s congruence tier at committed data: the datum's
own exchange read off a certificate (`splitRead_symm`), the count's
invariance under a two-sided congruence (`rev_congr`), the join's
pairing split at blocked vectors (`quadJoin`), and the ground
rescaling against the balance weighting (`matScale_scaleB`). -/

/-! The exchange read at the positive-definite datum: its
certificate prices the datum against its own transpose. -/

theorem pin150 : matOneValue sPd (transposeM sPd) :=
  splitRead_symm sPd spPd (by decide +kernel)

theorem pin151 : matOneValue sPd (transposeM sPd) := by decide +kernel

/-! The count's invariance at a congruence of determinant one:
`T = [[1,1],[0,1]]` against its adjugate `W = [[1,-1],[0,1]]`, the
two products at `c = 1` on the identity.  The image
`Tᵀ [[2,1],[1,2]] T = [[2,3],[3,6]]` splits at the cleared descent's
congruence `[[1,-3],[0,2]]` to `diag(2, 6)`, and the two counts read
one value through the theorem and by the kernel. -/

private def cT : Mat := [[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]]
private def cW : Mat := [[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]]

private def spCg : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 4⟩], [u, ⟨3, 1⟩]], rfl⟩,
   ⟨[[⟨3, 1⟩, ⟨4, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨7, 1⟩], 0, rfl⟩

theorem pin152 : matOneValue (matMul cT cW) (matScaleB ⟨2, 1⟩ (idMat 2)) := by decide +kernel
theorem pin153 : matOneValue (matMul cW cT) (matScaleB ⟨2, 1⟩ (idMat 2)) := by decide +kernel
theorem pin154 : matMul (transposeM cT) (matMul sPd cT)
    = [[⟨3, 1⟩, ⟨4, 1⟩], [⟨4, 1⟩, ⟨7, 1⟩]] := by decide +kernel
theorem pin155 : splitRead (matMul (transposeM cT) (matMul sPd cT)) spCg := by decide +kernel

theorem pin156 : revAt spCg = revAt spPd :=
  rev_congr sPd cT cW ⟨2, 1⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) spPd (by decide +kernel) spCg (by decide +kernel)

theorem pin157 : revAt spCg = revAt spPd := by decide +kernel

/-! The scale's off-unit conjunct biting: at the equal-membered
scale the congruence collapses to the matrix of equal-membered
entries, whose two products read the scaled identity at that very
scale, so every binder besides that conjunct passes — the mixed
datum's own split, the image's all-kernel split, and the two square
reads — while the counts part at `0` against `1`. -/

private def nT : Mat := [[u, u], [u, u]]
private def spNullK : Split 2 := ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [], 2, rfl⟩

theorem pin158 : u.oneValue BPair.unit := by decide +kernel
theorem pin159 : matOneValue (matMul nT nT) (matScaleB u (idMat 2)) := by decide +kernel
theorem pin160 : sqAt exch2 2 ∧ sqAt nT 2 := by decide +kernel
theorem pin161 : splitRead (matMul (transposeM nT) (matMul exch2 nT)) spNullK := by
  decide +kernel
theorem pin162 : ¬ (revAt spNullK = revAt spMix) := by decide +kernel

/-! The join's pairing split at a `2 + 1` instance: the pivot
`[[1,2],[2,3]]`, the coupling `(1,2)ᵀ` and the trailing `[5]` at the
blocked vector `(1,2 ; 3)`, the four block reads joining through the
theorem and by the kernel beside it. -/

private def qP : Mat := [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨4, 1⟩]]
private def qB : Mat := [[⟨2, 1⟩], [⟨3, 1⟩]]
private def qQ : Mat := [[⟨6, 1⟩]]
private def qa : List BPair := [⟨2, 1⟩, ⟨3, 1⟩]
private def qb : List BPair := [⟨4, 1⟩]

theorem pin163 : (dotN (qa ++ qb) (matVec (blockJoin qP qB qQ) (qa ++ qb))).oneValue
    ((dotN qa (matVec qP qa) + dotN qa (matVec qB qb))
      + (dotN qb (matVec (transposeM qB) qa) + dotN qb (matVec qQ qb))) :=
  quadJoin qP qB qQ 2 1 (by decide +kernel) rfl rfl rfl (by decide +kernel) rfl
    qa qb qa qb rfl rfl rfl

theorem pin164 : (dotN (qa ++ qb) (matVec (blockJoin qP qB qQ) (qa ++ qb))).oneValue
    ((dotN qa (matVec qP qa) + dotN qa (matVec qB qb))
      + (dotN qb (matVec (transposeM qB) qa) + dotN qb (matVec qQ qb))) := by
  decide +kernel

/-! The row-count binders biting: at a vacant coupling the two width
binders pass over the vacant row list, while the join truncates to
the vacant matrix and the four block reads price `5 + 63` against
it. -/

private def tP : Mat := [[⟨6, 1⟩]]
private def tQ : Mat := [[⟨8, 1⟩]]
private def ta : List BPair := [⟨3, 1⟩]
private def tb : List BPair := [⟨4, 1⟩]

theorem pin165 : rowsLen 1 tP ∧ rowsLen 1 (transposeM ([] : Mat)) := by decide +kernel

theorem pin166 : ¬ ((dotN (ta ++ tb) (matVec (blockJoin tP ([] : Mat) tQ)
      (ta ++ tb))).oneValue
    ((dotN ta (matVec tP ta) + dotN ta (matVec ([] : Mat) tb))
      + (dotN tb (matVec (transposeM ([] : Mat)) ta)
        + dotN tb (matVec tQ tb)))) := by
  decide +kernel

/-! The ground rescaling against the balance weighting entrywise,
the theorem beside the kernel's decision. -/

theorem pin167 : matOneValue (matScale 3 sPd) (matScaleB (BPair.ofPos 3) sPd) :=
  matScale_scaleB 3 sPd

theorem pin168 : matOneValue (matScale 3 sPd) (matScaleB (BPair.ofPos 3) sPd) := by
  decide +kernel

/-! The count engine's public kit at committed data, one read per
member: the join's action and the transpose adjoint, the form
fold's additivity, congruence and unit read, the padding with its
two reads, the unit-tail sum reads, the strict sums, the single
fold, the leading scale, and the swap through the weighting. -/

private def kv : List BPair := [⟨3, 1⟩, ⟨1, 2⟩]
private def kw : List BPair := [⟨2, 1⟩]

theorem pin169 : poly.oneValue (matVec (blockJoin qP qB qQ) (kv ++ kw))
    (vecAdd (matVec qP kv) (matVec qB kw)
      ++ vecAdd (matVec (transposeM qB) kv) (matVec qQ kw)) :=
  matVec_blockJoin qP qB qQ kv kw (by decide +kernel) (by decide +kernel)

theorem pin170 : (dotN kw (matVec (transposeM qB) kv)).oneValue
    (dotN kv (matVec qB kw)) :=
  adjB qB 2 1 rfl (by decide +kernel) kw rfl kv rfl

theorem pin171 : (dotN (vecAdd kv kv) (matVec qP (vecAdd kv kv))).oneValue
    ((dotN kv (matVec qP kv) + dotN kv (matVec qP kv))
      + (dotN kv (matVec qP kv) + dotN kv (matVec qP kv))) :=
  quadAdd qP 2 (by decide +kernel) rfl kv kv rfl rfl

theorem pin172 : (dotN kv (matVec qP kv)).oneValue
    (dotN [⟨4, 2⟩, ⟨2, 3⟩] (matVec qP [⟨4, 2⟩, ⟨2, 3⟩])) :=
  quad_congr qP kv [⟨4, 2⟩, ⟨2, 3⟩] (by decide +kernel)

theorem pin173 : (dotN [u, u] (matVec qP [u, u])).oneValue BPair.unit :=
  quadNull qP [u, u] (by decide +kernel)

theorem pin174 : matVec (padR 1 2) kv = vecAdd [u] [u] ++ kv → True :=
  fun _ => trivial
theorem pin175 : (padR 1 2).length = 3 := padR_len 1 2
theorem pin176 : poly.oneValue (matVec (padR 1 2) kv)
    (List.replicate 1 BPair.unit ++ kv) := padR_act 1 2 kv rfl

theorem pin177 : poly.unitTail [⟨2, 2⟩] :=
  unitTailAddRight [⟨2, 2⟩] [⟨3, 3⟩] rfl (by decide +kernel) (by decide +kernel)
theorem pin178 : poly.unitTail [⟨3, 3⟩] :=
  unitTailAddLeft [⟨2, 2⟩] [⟨3, 3⟩] rfl (by decide +kernel) (by decide +kernel)

theorem pin179 : (⟨1, 2⟩ : BPair) + ⟨2, 2⟩ < BPair.unit :=
  ltUnitAddLe (by decide +kernel) (by decide +kernel)
theorem pin180 : (⟨2, 2⟩ : BPair) + ⟨1, 2⟩ < BPair.unit :=
  leAddLtUnit (by decide +kernel) (by decide +kernel)

theorem pin181 : (dotN [⟨3, 1⟩] [⟨2, 1⟩]).oneValue (⟨3, 1⟩ * ⟨2, 1⟩) :=
  dotN_single ⟨3, 1⟩ ⟨2, 1⟩
theorem pin182 : (dotN (elim.vecScale ⟨3, 1⟩ kv) kw).oneValue
    (⟨3, 1⟩ * dotN kv kw) → True := fun _ => trivial
theorem pin183 : (dotN (elim.vecScale ⟨3, 1⟩ [⟨2, 1⟩]) [⟨4, 1⟩]).oneValue
    (⟨3, 1⟩ * dotN [⟨2, 1⟩] [⟨4, 1⟩]) :=
  dotN_scaleRow_free ⟨3, 1⟩ [⟨2, 1⟩] [⟨4, 1⟩]
theorem pin184 : elim.vecScale ⟨3, 1⟩ (kv.map BPair.swap)
    = (elim.vecScale ⟨3, 1⟩ kv).map BPair.swap :=
  elim.vecScale_swapMap ⟨3, 1⟩ kv

/-! The transports' refusals: the exchange read's certificate
binder at a datum off its own transpose, and the congruence
witness's two product reads at their one forgery — a one-sided
witness at square integer carriers forces the other side through
the adjugate, so the two reads share their record. -/

private def sNs : Mat := [[u, ⟨2, 1⟩], [u, u]]

theorem pin185 : ¬ splitRead sNs spPd := by decide +kernel
theorem pin186 : ¬ matOneValue sNs (transposeM sNs) := by decide +kernel

private def tCol : Mat := [[⟨2, 1⟩, u], [u, u]]

theorem pin187 : ¬ matOneValue (matMul tCol (idMat 2))
    (matScaleB ⟨2, 1⟩ (idMat 2)) := by decide +kernel
theorem pin188 : splitRead (matMul (transposeM tCol) (matMul exch2 tCol))
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [], 2, rfl⟩ : Split 2) := by decide +kernel
theorem pin189 : ¬ (revAt (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [], 2, rfl⟩ : Split 2)
    = revAt spMix) := by decide +kernel

/-! The join split's two row-count binders at their own forgeries:
a vacant pivot and a vacant trailing block each collapse the join's
truncating folds against the four standing reads, the width frames
vacuous beside them — the refusals at the short side, where the
row-count read alone parts. -/

theorem pin190 : rowsLen 1 ([] : Mat) ∧ (¬ (([] : Mat).length = 1)) := by decide +kernel
theorem pin191 : ¬ ((dotN (ta ++ tb) (matVec (blockJoin ([] : Mat) [[⟨2, 1⟩]] tQ)
      (ta ++ tb))).oneValue
    ((dotN ta (matVec ([] : Mat) ta) + dotN ta (matVec [[⟨2, 1⟩]] tb))
      + (dotN tb (matVec (transposeM [[⟨2, 1⟩]]) ta)
        + dotN tb (matVec tQ tb)))) := by decide +kernel

theorem pin192 : ¬ ((dotN (ta ++ tb) (matVec (blockJoin tP [[⟨2, 1⟩]] ([] : Mat))
      (ta ++ tb))).oneValue
    ((dotN ta (matVec tP ta) + dotN ta (matVec [[⟨2, 1⟩]] tb))
      + (dotN tb (matVec (transposeM [[⟨2, 1⟩]]) ta)
        + dotN tb (matVec ([] : Mat) tb)))) := by decide +kernel

/-! The identity's rows at the indicator: the entry read at the
flipped-guard display, the old inline spelling identified with the
indicator, and the occupied-row discrimination control. -/

theorem pin193 : ∀ i < 4, (List.range 4).map (fun j =>
    if i == j then BPair.ofPos Pos.one else BPair.unit)
      = elim.idRow 4 i := by decide +kernel
theorem pin194 : ∀ i < 4, ∀ j < 4, ground.getAt BPair.unit
    (ground.getAt ([] : List BPair) (elim.idMat 4) i) j
  = (if j = i then BPair.ofNat 1 else BPair.unit) := by decide +kernel
theorem pin195 : ¬ (∀ i < 3, ∀ j < 3, ground.getAt BPair.unit
    (ground.getAt ([] : List BPair) (elim.idMat 3) i) j
      = BPair.unit) := by decide +kernel

/-! The compression corners at a `1 + 1` join: the pivot block
`[-3]`, the coupling `[1]` and the trailing block `[5]` assemble
`[[-3,1],[1,5]]`, which splits at the determinant-three congruence
`T = [[1,1],[0,3]]` to `diag(-3, 48)` — one reversal.  The pivot
corner's own count is that one and the trailing corner's is vacant,
so each corner's count sits at or below the join's
(`rev_head_le`, `rev_tail_le` at the blocking tie). -/

private def crP : Mat := [[⟨1, 4⟩]]
private def crB : Mat := [[⟨2, 1⟩]]
private def crQ : Mat := [[⟨6, 1⟩]]
private def crS : Mat := blockJoin crP crB crQ

private def crUp : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩
private def crDn : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩
private def crT3 : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨4, 1⟩]], rfl⟩
private def crTw3 : SqMat 2 := ⟨[[⟨4, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩

private def crSp1 (a : BPair) : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one a], 0, rfl⟩
private def crSpJ : Split 2 :=
  ⟨crT3, crTw3, [.one ⟨1, 4⟩, .one ⟨49, 1⟩], 0, rfl⟩

theorem pin196 : splitRead crS crSpJ := by decide +kernel
theorem pin197 : splitRead crP (crSp1 ⟨1, 4⟩) := by decide +kernel
theorem pin198 : splitRead crQ (crSp1 ⟨6, 1⟩) := by decide +kernel
theorem pin199 : revAt crSpJ = 1 := by decide +kernel

theorem pin200 : (1 : Nat) ≤ 1 :=
  rev_head_le (k := 1) (m := 1) crS crP crB crQ (by decide +kernel) (by decide +kernel)
    (crSp1 ⟨1, 4⟩) (by decide +kernel) crSpJ (by decide +kernel)

theorem pin201 : (0 : Nat) ≤ 1 :=
  rev_tail_le (k := 1) (m := 1) crS crP crB crQ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (crSp1 ⟨6, 1⟩) (by decide +kernel) crSpJ (by decide +kernel)

/-! The cap's compression at each corner: the magnetic part
`[[-1,1],[1,-1]]` is capped by `[[2,0],[0,2]]`, the site datum
`[[3,-1],[-1,3]]` splitting to `diag(3, 24)` and the sum
`[[1,1],[1,1]]` to `diag(1, 0)` with its kernel block trailing —
both counts vacant.  The two block ties carry their own couplings,
the site side's the sum side's memberwise swap, and each corner's
`[-1]` against `[2]` is a cap in turn (`capAt_compress` at the pivot
corner, `capAt_compress_tail` at the trailing one). -/

private def crM1 : Mat := [[⟨1, 2⟩]]
private def crM2 : Mat := [[⟨1, 2⟩]]
private def crC1 : Mat := [[⟨3, 1⟩]]
private def crC2 : Mat := [[⟨3, 1⟩]]
private def crBC : Mat := [[⟨1, 2⟩]]
private def crMag : Mat := blockJoin crM1 crB crM2
private def crCap : Mat := blockJoin crC1 (elim.nullMat 1 1) crC2

private def crSpU : Split 2 :=
  ⟨crT3, crTw3, [.one ⟨4, 1⟩, .one ⟨25, 1⟩], 0, rfl⟩
private def crSpL : Split 2 := ⟨crDn, crUp, [.one ⟨2, 1⟩], 1, rfl⟩

theorem pin202 : capAt crMag crCap crSpU crSpL := by decide +kernel
theorem pin203 : matOneValue (siteDatum crCap crMag)
    (blockJoin (siteDatum crC1 crM1) crBC (siteDatum crC2 crM2)) := by
  decide +kernel
theorem pin204 : matOneValue (matAdd crCap crMag)
    (blockJoin (matAdd crC1 crM1) crB (matAdd crC2 crM2)) := by decide +kernel

theorem pin205 : capAt crM1 crC1 (crSp1 ⟨4, 1⟩) (crSp1 ⟨2, 1⟩) :=
  capAt_compress (k := 1) (m := 1) crMag crCap crM1 crC1 crB crBC crM2 crC2
    crSpU crSpL (crSp1 ⟨4, 1⟩) (crSp1 ⟨2, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem pin206 : capAt crM2 crC2 (crSp1 ⟨4, 1⟩) (crSp1 ⟨2, 1⟩) :=
  capAt_compress_tail (k := 1) (m := 1) crMag crCap crM1 crC1 crB crBC
    crM2 crC2 crSpU crSpL (crSp1 ⟨4, 1⟩) (crSp1 ⟨2, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The cap binder's refusal at the pivot corner: a vacant pivot
weight takes the assembled cap's sum to `[[-1,1],[1,1]]`, one mixed
block at determinant `−2` and its count occupied, so the assembled
read is refused — and the corner's own sum `[-1]` is occupied with
it, the conclusion parting exactly where the binder does. -/

private def crC1f : Mat := [[u]]
private def crCapF : Mat := blockJoin crC1f (elim.nullMat 1 1) crC2
private def crSpUf : Split 2 :=
  ⟨crUp, crDn, [.one ⟨2, 1⟩, .one ⟨3, 1⟩], 0, rfl⟩
private def crSpLf : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two ⟨1, 2⟩ ⟨2, 1⟩ ⟨2, 1⟩], 0, rfl⟩

theorem pin207 : splitRead (siteDatum crCapF crMag) crSpUf := by decide +kernel
theorem pin208 : splitRead (matAdd crCapF crMag) crSpLf := by decide +kernel
theorem pin209 : ¬ capAt crMag crCapF crSpUf crSpLf := by decide +kernel
theorem pin210 : splitRead (siteDatum crC1f crM1) (crSp1 ⟨2, 1⟩) := by decide +kernel
theorem pin211 : splitRead (matAdd crC1f crM1) (crSp1 ⟨1, 2⟩) := by decide +kernel
theorem pin212 : ¬ capAt crM1 crC1f (crSp1 ⟨2, 1⟩) (crSp1 ⟨1, 2⟩) := by decide +kernel

/-! The determinant's split at the cleared deflation, `1 + 1`. -/

private def dsP : Mat := [[⟨3, 1⟩]]
private def dsO : Mat := [[⟨2, 1⟩]]

theorem pin213 : (minor dsP * minor (deflMat dsP dsO dsO dsO)).oneValue
    (ground.bpow (minor dsP) (2 * 1) * minor (blockJoin dsP dsO dsO)) := by
  decide +kernel
theorem pin214 : (minor dsP * minor (deflMat dsP dsO dsO dsO)).oneValue
    ⟨5, 1⟩ := by decide +kernel
theorem pin215 : (minor dsP * minor (deflMat dsP dsO dsO dsO)).oneValue
    (ground.bpow (minor dsP) (2 * 1) * minor (blockJoin dsP dsO dsO)) :=
  minor_deflMat (k := 1) (m := 1) dsP dsO dsO dsO (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin216 : ¬ matOneValue (matMul dsO dsP) (matScaleB (minor dsO) dsO) := by
  decide +kernel
theorem pin217 : ¬ (minor dsO * minor (deflMat dsO dsO dsO dsP)).oneValue
    (ground.bpow (minor dsO) (2 * 1) * minor (blockJoin dsO dsO dsO)) := by
  decide +kernel

/-! The block table's two small orders: the order-one row at an
entry below the unit, and the order-two row at the mixed block —
determinant `-4` at a vacant diagonal — each count decided beside
its reading through the general theorem. -/

private def btA : BPair := ⟨1, 3⟩
private def btB : BPair := ⟨3, 1⟩

theorem pin218 : splitRead [[btA]] (inertia.oneSplit [btA]) := by decide +kernel
theorem pin219 : revAt (inertia.oneSplit [btA]) = 1 := by decide +kernel
theorem pin220 : revAt (inertia.oneSplit [btA]) = (SBlock.one btA).rev :=
  rev_one (by decide +kernel) (inertia.oneSplit [btA]) (by decide +kernel)

private def btSp : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two u btB u], 0, rfl⟩

theorem pin221 : (SBlock.two u btB u).det.oneValue ⟨1, 5⟩ := by decide +kernel
theorem pin222 : splitRead [[u, btB], [btB, u]] btSp := by decide +kernel
theorem pin223 : revAt btSp = 1 := by decide +kernel
theorem pin224 : revAt btSp = (SBlock.two u btB u).rev :=
  rev_two (b' := btB) (by decide +kernel) (by decide +kernel) btSp
    (by decide +kernel)

/-! The diagonal certificate at a stated entry list: the three-order
diagonal datum `diag(2, -2, 1)` splitting at its own entries, one
order-one block each, decided and through the theorem, with the
reversal count the entry list's own side fold — one lower side, so
count `1` — read both ways; and the refusal at a list carrying an
entry on the sum's unit, where the shape and congruence binders
stand and the nonsingularity binder alone fails, and at an occupied
coupling, where the block-diagonal binder alone fails. -/

private def dgL : List BPair := [⟨3, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]
private def dgM : Mat := [[⟨3, 1⟩, u, u], [u, ⟨1, 3⟩, u], [u, u, ⟨2, 1⟩]]

theorem pin225 : splitRead dgM (oneSplit dgL) := by decide +kernel
theorem pin226 : splitRead dgM (oneSplit dgL) :=
  oneSplit_read dgL dgM (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin227 : revAt (oneSplit dgL) = 1 := by decide +kernel
theorem pin228 : dgL.foldl (fun m d => m + (SBlock.one d).rev) 0 = 1 := by
  decide +kernel
theorem pin229 : revAt (oneSplit dgL)
    = dgL.foldl (fun m d => m + (SBlock.one d).rev) 0 :=
  revAt_oneSplit dgL

private def dgU : List BPair := [⟨3, 1⟩, u, ⟨2, 1⟩]
private def dgN : Mat := [[⟨3, 1⟩, u, u], [u, u, u], [u, u, ⟨2, 1⟩]]

theorem pin230 : sqAt dgN dgU.length := by decide +kernel
theorem pin231 : matOneValue dgN (blockMat (dgU.map SBlock.one) 0) := by
  decide +kernel
theorem pin232 : ¬ ((dgU.all (fun d => !(decide (d.oneValue BPair.unit))))
    = true) := by decide +kernel
theorem pin233 : ¬ splitRead dgN (oneSplit dgU) := by decide +kernel

/-! The block-diagonal binder isolated: a datum off the list's
block diagonal — an occupied coupling — with the shape and
nonsingularity binders standing, refusing the split. -/

private def dgOff : Mat :=
  [[⟨3, 1⟩, ⟨2, 1⟩, u], [⟨2, 1⟩, ⟨1, 3⟩, u], [u, u, ⟨2, 1⟩]]

theorem pin234 : sqAt dgOff dgL.length := by decide +kernel
theorem pin235 : (dgL.all (fun d => !(decide (d.oneValue BPair.unit))))
    = true := by decide +kernel
theorem pin236 : ¬ matOneValue dgOff (blockMat (dgL.map SBlock.one) 0) := by
  decide +kernel
theorem pin237 : ¬ splitRead dgOff (oneSplit dgL) := by decide +kernel


/-! The block table's side reads, decided and through the theorems:
the order-one block at either side, and the order-two block at the
three determinant-and-entry cases. -/

theorem pin238 : (SBlock.one ⟨3, 1⟩).rev = 0 := by decide +kernel
theorem pin239 : (SBlock.one ⟨3, 1⟩).rev = 0 :=
  rev_one_le (by decide +kernel)
theorem pin240 : (SBlock.one ⟨1, 3⟩).rev = 1 := by decide +kernel
theorem pin241 : (SBlock.one ⟨1, 3⟩).rev = 1 :=
  rev_one_lt (by decide +kernel)
theorem pin242 : (SBlock.two ⟨1, 1⟩ ⟨3, 1⟩ ⟨1, 1⟩).rev = 1 := by decide +kernel
theorem pin243 : (SBlock.two ⟨1, 1⟩ ⟨3, 1⟩ ⟨1, 1⟩).rev = 1 :=
  rev_two_detLt (by decide +kernel)
theorem pin244 : (SBlock.two ⟨1, 3⟩ ⟨1, 1⟩ ⟨1, 3⟩).rev = 2 := by decide +kernel
theorem pin245 : (SBlock.two ⟨1, 3⟩ ⟨1, 1⟩ ⟨1, 3⟩).rev = 2 :=
  rev_two_cols (by decide +kernel) (by decide +kernel)
theorem pin246 : (SBlock.two ⟨3, 1⟩ ⟨1, 1⟩ ⟨3, 1⟩).rev = 0 := by decide +kernel
theorem pin247 : (SBlock.two ⟨3, 1⟩ ⟨1, 1⟩ ⟨3, 1⟩).rev = 0 :=
  rev_two_nil (by decide +kernel) (by decide +kernel)
theorem pin248 : (0 : Nat) < (SBlock.one ⟨3, 1⟩).order := order_pos _


/-! `lem:inertia`'s existence clause at four data: the order-one
pivot at a leading entry above the unit, the mixed 2×2 whose
diagonal reads the unit so the descent's pivot is the off-diagonal
pair, a three-order datum whose leading entry reads the unit so the
descent exchanges places before pivoting at a further diagonal
entry, and the vacant datum whose whole order is the kernel block.
Each split is decided at the construction and read again through
the general theorem with the datum's order and exchange decided
beside it, and each count is pinned; the vacant datum's rank read
closes the module. -/

private def exOne : Mat := [[⟨3, 1⟩]]
private def exTwo : Mat := [[u, ⟨3, 1⟩], [⟨3, 1⟩, u]]
private def exThree : Mat :=
  [[u, ⟨2, 1⟩, u], [⟨2, 1⟩, ⟨1, 2⟩, u], [u, u, ⟨4, 1⟩]]
private def exKer : Mat := [[u, u], [u, u]]

theorem pin249 : splitRead exOne (mkSplit 1 exOne) := by decide +kernel
theorem pin250 : splitRead exOne (mkSplit 1 exOne) :=
  mkSplit_read 1 exOne (by decide +kernel) (by decide +kernel)
theorem pin251 : revAt (mkSplit 1 exOne) = 0 := by decide +kernel

theorem pin252 : splitRead exTwo (mkSplit 2 exTwo) := by decide +kernel
theorem pin253 : splitRead exTwo (mkSplit 2 exTwo) :=
  mkSplit_read 2 exTwo (by decide +kernel) (by decide +kernel)
theorem pin254 : revAt (mkSplit 2 exTwo) = 1 := by decide +kernel

theorem pin255 : splitRead exThree (mkSplit 3 exThree) := by decide +kernel
theorem pin256 : splitRead exThree (mkSplit 3 exThree) :=
  mkSplit_read 3 exThree (by decide +kernel) (by decide +kernel)
theorem pin257 : revAt (mkSplit 3 exThree) = 1 := by decide +kernel

theorem pin258 : splitRead exKer (mkSplit 2 exKer) := by decide +kernel
theorem pin259 : splitRead exKer (mkSplit 2 exKer) :=
  mkSplit_read 2 exKer (by decide +kernel) (by decide +kernel)
theorem pin260 : revAt (mkSplit 2 exKer) = 0 := by decide +kernel
theorem pin261 : rankAt (mkSplit 2 exKer) = 0 := by decide +kernel

/-! The cap algebra at data: the trailing pad's four entries pinned
at a one-by-one deviation — the three leading entries at the sum's
unit and the trailing entry the deviation's own — the block cap
padded to the joined order, the two summands' caps joined at the
sum, the cap rescaled at the weight two, and the cap respelt across
an entrywise read of both its data, each read by the kernel and
again through its own theorem, with two refusals naming the binder
that bites: the block cap's upper split at a deviation four against
the identity's one, and the second summand's upper split at a
deviation five against its own cap two. -/

private def cpD : Mat := [[⟨2, 1⟩]]
private def cpSpU : Split 1 :=
  mkSplit 1 (siteDatum (matScale 2 (idMat 1)) (matScale 1 cpD))
private def cpSpL : Split 1 :=
  mkSplit 1 (matAdd (matScale 2 (idMat 1)) (matScale 1 cpD))
private def cpSpU2 : Split (1 + 1) :=
  mkSplit (1 + 1)
    (siteDatum (matScale 2 (idMat (1 + 1))) (matScale 1 (trailPad 1 cpD)))
private def cpSpL2 : Split (1 + 1) :=
  mkSplit (1 + 1)
    (matAdd (matScale 2 (idMat (1 + 1))) (matScale 1 (trailPad 1 cpD)))

theorem pin262 : matOneValue (trailPad 1 [[⟨3, 1⟩]]) [[u, u], [u, ⟨3, 1⟩]] := by
  decide +kernel

theorem pin263 : capAt (matScale 1 cpD) (matScale 2 (idMat 1)) cpSpU cpSpL := by
  decide +kernel
theorem pin264 : capAt (matScale 1 (trailPad 1 cpD)) (matScale 2 (idMat (1 + 1)))
    cpSpU2 cpSpL2 := by decide +kernel
theorem pin265 : capAt (matScale 1 (trailPad 1 cpD)) (matScale 2 (idMat (1 + 1)))
    cpSpU2 cpSpL2 :=
  capAt_trailPad (k := 1) (m := 1) cpD 2 1 cpSpU cpSpL (by decide +kernel)
    cpSpU2 cpSpL2 (by decide +kernel) (by decide +kernel)

private def caS1 : Mat := [[⟨2, 1⟩]]
private def caC1 : Mat := [[⟨4, 1⟩]]
private def caS2 : Mat := [[⟨1, 2⟩]]
private def caC2 : Mat := [[⟨3, 1⟩]]
private def caSpU1 : Split 1 := mkSplit 1 (siteDatum caC1 caS1)
private def caSpL1 : Split 1 := mkSplit 1 (matAdd caC1 caS1)
private def caSpU2 : Split 1 := mkSplit 1 (siteDatum caC2 caS2)
private def caSpL2 : Split 1 := mkSplit 1 (matAdd caC2 caS2)
private def caSpU : Split 1 :=
  mkSplit 1 (siteDatum (matAdd caC1 caC2) (matAdd caS1 caS2))
private def caSpL : Split 1 :=
  mkSplit 1 (matAdd (matAdd caC1 caC2) (matAdd caS1 caS2))

theorem pin266 : capAt caS1 caC1 caSpU1 caSpL1 := by decide +kernel
theorem pin267 : capAt caS2 caC2 caSpU2 caSpL2 := by decide +kernel
theorem pin268 : capAt (matAdd caS1 caS2) (matAdd caC1 caC2) caSpU caSpL := by
  decide +kernel
theorem pin269 : capAt (matAdd caS1 caS2) (matAdd caC1 caC2) caSpU caSpL :=
  capAt_add caS1 caC1 caS2 caC2 caSpU1 caSpL1 caSpU2 caSpL2 caSpU caSpL
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem pin270 : capAt (matScale 2 caS1) (matScale 2 caC1)
    (scaleSplit (BPair.ofPos 2) caSpU1)
    (scaleSplit (BPair.ofPos 2) caSpL1) := by decide +kernel
theorem pin271 : capAt (matScale 2 caS1) (matScale 2 caC1)
    (scaleSplit (BPair.ofPos 2) caSpU1)
    (scaleSplit (BPair.ofPos 2) caSpL1) :=
  capAt_scale caS1 caC1 2 caSpU1 caSpL1 (by decide +kernel)

private def cgS : Mat := [[⟨3, 2⟩]]
private def cgC : Mat := [[⟨5, 2⟩]]

theorem pin272 : capAt cgS cgC caSpU1 caSpL1 := by decide +kernel
theorem pin273 : capAt cgS cgC caSpU1 caSpL1 :=
  capAt_congr caS1 caC1 cgS cgC caSpU1 caSpL1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

private def cfD : Mat := [[⟨5, 1⟩]]
private def cfSpU1 : Split 1 :=
  mkSplit 1 (siteDatum (matScale 1 (idMat 1)) (matScale 1 cfD))
private def cfSpL1 : Split 1 :=
  mkSplit 1 (matAdd (matScale 1 (idMat 1)) (matScale 1 cfD))
private def cfSpU : Split (1 + 1) :=
  mkSplit (1 + 1)
    (siteDatum (matScale 1 (idMat (1 + 1))) (matScale 1 (trailPad 1 cfD)))
private def cfSpL : Split (1 + 1) :=
  mkSplit (1 + 1)
    (matAdd (matScale 1 (idMat (1 + 1))) (matScale 1 (trailPad 1 cfD)))

/-- Refusal naming `capAt_trailPad`'s block-cap binder: at a
deviation of four against the identity's one the block's upper
split reads the lower side, and the padded join's upper split reads
it at the trailing place. -/
theorem pin274 : ¬ capAt (matScale 1 cfD) (matScale 1 (idMat 1)) cfSpU1 cfSpL1 := by
  decide +kernel
theorem pin275 : ¬ capAt (matScale 1 (trailPad 1 cfD)) (matScale 1 (idMat (1 + 1)))
    cfSpU cfSpL := by decide +kernel

private def cbS2 : Mat := [[⟨6, 1⟩]]
private def cbSpU2 : Split 1 := mkSplit 1 (siteDatum caC2 cbS2)
private def cbSpL2 : Split 1 := mkSplit 1 (matAdd caC2 cbS2)
private def cbSpU : Split 1 :=
  mkSplit 1 (siteDatum (matAdd caC1 caC2) (matAdd caS1 cbS2))
private def cbSpL : Split 1 :=
  mkSplit 1 (matAdd (matAdd caC1 caC2) (matAdd caS1 cbS2))

/-- Refusal naming `capAt_add`'s second-summand binder: at a
deviation of five against a cap of two that summand's upper split
reads the lower side, and the sum's own upper split reads it
beside it. -/
theorem pin276 : ¬ capAt cbS2 caC2 cbSpU2 cbSpL2 := by decide +kernel
theorem pin277 : ¬ capAt (matAdd caS1 cbS2) (matAdd caC1 caC2) cbSpU cbSpL := by
  decide +kernel

/-! The withdrawn diagonal's rank-one read at the identity
congruence: the kept upper entry two prices its own form, the
withdrawn lower entry minus two prices its form at the vacant read,
and the forged split at the entry minus one against the datum two
refuses the congruence with the display parting beside it. -/

private def ppUp : Mat := [[⟨3, 1⟩]]
private def ppDn : Mat := [[⟨1, 3⟩]]
private def ppV : List BPair := [⟨2, 1⟩]
private def ppForge : Split 1 := inertia.oneSplit [⟨1, 2⟩]

theorem pin278 : splitRead ppUp (inertia.oneSplit [⟨3, 1⟩]) := by decide +kernel
theorem pin279 : minor (inertia.oneSplit [⟨3, 1⟩]).T.val * minor (inertia.oneSplit [⟨3, 1⟩]).T.val
      * quadForm ppUp ppV
    ≤ quadForm (blockMat (posBlocks (inertia.oneSplit [⟨3, 1⟩]).blocks)
        (inertia.oneSplit [⟨3, 1⟩]).kern)
      (matVec (inertia.oneSplit [⟨3, 1⟩]).Tw.val ppV) := by decide +kernel
theorem pin280 : minor (inertia.oneSplit [⟨3, 1⟩]).T.val * minor (inertia.oneSplit [⟨3, 1⟩]).T.val
      * quadForm ppUp ppV
    ≤ quadForm (blockMat (posBlocks (inertia.oneSplit [⟨3, 1⟩]).blocks)
        (inertia.oneSplit [⟨3, 1⟩]).kern)
      (matVec (inertia.oneSplit [⟨3, 1⟩]).Tw.val ppV) :=
  split_posPart ppUp (inertia.oneSplit [⟨3, 1⟩]) (by decide +kernel) ppV
    (by decide +kernel)

theorem pin281 : splitRead ppDn (inertia.oneSplit [⟨1, 3⟩]) := by decide +kernel
theorem pin282 : minor (inertia.oneSplit [⟨1, 3⟩]).T.val * minor (inertia.oneSplit [⟨1, 3⟩]).T.val
      * quadForm ppDn ppV
    ≤ quadForm (blockMat (posBlocks (inertia.oneSplit [⟨1, 3⟩]).blocks)
        (inertia.oneSplit [⟨1, 3⟩]).kern)
      (matVec (inertia.oneSplit [⟨1, 3⟩]).Tw.val ppV) := by decide +kernel
theorem pin283 : minor (inertia.oneSplit [⟨1, 3⟩]).T.val * minor (inertia.oneSplit [⟨1, 3⟩]).T.val
      * quadForm ppDn ppV
    ≤ quadForm (blockMat (posBlocks (inertia.oneSplit [⟨1, 3⟩]).blocks)
        (inertia.oneSplit [⟨1, 3⟩]).kern)
      (matVec (inertia.oneSplit [⟨1, 3⟩]).Tw.val ppV) :=
  split_posPart ppDn (inertia.oneSplit [⟨1, 3⟩]) (by decide +kernel) ppV
    (by decide +kernel)

/-- Refusal naming `split_posPart`'s split read: the forged
order-one split carries the entry minus one against the datum two,
the congruence identity parting, and the display parts beside it —
the datum's form two against the withdrawn vacant read. -/
theorem pin284 : ¬ splitRead ppUp ppForge := by decide +kernel
theorem pin285 : ¬ (minor ppForge.T.val * minor ppForge.T.val
      * quadForm ppUp ppV
    ≤ quadForm (blockMat (posBlocks ppForge.blocks) ppForge.kern)
      (matVec ppForge.Tw.val ppV)) := by decide +kernel

/-! The one-sided comparison's read at one split: the datum zero
under the datum one — the site datum `C − S` reads the entry one,
its order-one split at that entry, and the two forms' order landed
through `le_all` beside the decided display — with the refusal at
the exchanged pair, where the site datum reads minus one, the
split's block occupies the count and the psd conjunct parts with
the display beside it. -/

private def leS : Mat := [[u]]
private def leC : Mat := [[⟨2, 1⟩]]
private def leV : List BPair := [⟨2, 1⟩]

theorem pin286 : matOneValue (siteDatum leC leS) [[⟨3, 2⟩]] := by decide +kernel
theorem pin287 : leAt leS leC (inertia.oneSplit [⟨3, 2⟩]) := by decide +kernel
theorem pin288 : quadForm leS leV ≤ quadForm leC leV := by decide +kernel
theorem pin289 : quadForm leS leV ≤ quadForm leC leV :=
  le_all leS leC (inertia.oneSplit [⟨3, 2⟩]) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) leV (by decide +kernel)

/-- Refusal naming `leAt`'s positive-semidefinite conjunct: at the
exchanged pair the site datum reads minus one, its split reads that
datum while the block occupies the count, and the two forms' order
parts beside it — one against zero. -/

private def leS' : Mat := [[⟨2, 1⟩]]
private def leC' : Mat := [[u]]

theorem pin290 : matOneValue (siteDatum leC' leS') [[⟨2, 3⟩]] := by decide +kernel
theorem pin291 : splitRead (siteDatum leC' leS') (inertia.oneSplit [⟨2, 3⟩]) := by
  decide +kernel
theorem pin292 : ¬ psdAt (inertia.oneSplit [⟨2, 3⟩]) := by decide +kernel
theorem pin293 : ¬ leAt leS' leC' (inertia.oneSplit [⟨2, 3⟩]) := by decide +kernel
theorem pin294 : ¬ (quadForm leS' leV ≤ quadForm leC' leV) := by decide +kernel

/-! The forcing clause at two vectors at the two-by-two data, the two
members the coordinate vectors.  At the diagonal `diag(-1, -1)` the leading
entry sits below the sum's unit and the doubled cross read, vacant,
sits below the diagonal product's quadruple `4`, so every split
reads the count at two — the split at the identity's own congruence
reads exactly two; the strict forcing at one member reads the count
at one from the leading entry alone.  Each binder is isolated in turn: at the
identity the doubled cross read still sits below the quadruple while
the leading entry sits above the unit, and its split reads the count
nought; at the diagonal `diag(-1, 1)` the leading entry sits below
the unit while the quadruple is `-4`, below the vacant cross read,
and its split reads the count one. -/

private def xCap : List BPair := [BPair.ofNat 1, BPair.unit]
private def yCap : List BPair := [BPair.unit, BPair.ofNat 1]
private def sTwo : elim.Mat := [[⟨1, 2⟩, BPair.unit], [BPair.unit, ⟨1, 2⟩]]
private def sSingle : elim.Mat := [[⟨1, 2⟩, BPair.unit], [BPair.unit, ⟨2, 1⟩]]

private def spTwo : inertia.Split 2 :=
  ⟨⟨elim.idMat 2, rfl⟩, ⟨elim.idMat 2, rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨1, 2⟩], 0, rfl⟩
private def spNone : inertia.Split 2 :=
  ⟨⟨elim.idMat 2, rfl⟩, ⟨elim.idMat 2, rfl⟩,
   [.one ⟨2, 1⟩, .one ⟨2, 1⟩], 0, rfl⟩
private def spSingle : inertia.Split 2 :=
  ⟨⟨elim.idMat 2, rfl⟩, ⟨elim.idMat 2, rfl⟩,
   [.one ⟨1, 2⟩, .one ⟨2, 1⟩], 0, rfl⟩

theorem pin295 : inertia.splitRead sTwo spTwo := by decide +kernel
theorem pin296 : inertia.splitRead (elim.idMat 2) spNone := by decide +kernel
theorem pin297 : inertia.splitRead sSingle spSingle := by decide +kernel

theorem pin298 : 2 ≤ inertia.revAt spTwo :=
  inertia.capForcing sTwo xCap yCap rfl rfl (by decide +kernel) (by decide +kernel)
    spTwo (by decide +kernel)

theorem pin299 : inertia.revAt spTwo = 2 := by decide +kernel

theorem pin300 : ¬ (inertia.quadForm (elim.idMat 2) xCap < BPair.unit) := by
  decide +kernel

theorem pin301 : (elim.dotN xCap (elim.matVec (elim.idMat 2) yCap)
      + elim.dotN yCap (elim.matVec (elim.idMat 2) xCap))
    * (elim.dotN xCap (elim.matVec (elim.idMat 2) yCap)
      + elim.dotN yCap (elim.matVec (elim.idMat 2) xCap))
  < BPair.ofNat 4 * (inertia.quadForm (elim.idMat 2) xCap
      * inertia.quadForm (elim.idMat 2) yCap) := by decide +kernel

theorem pin302 : ¬ (2 ≤ inertia.revAt spNone) := by decide +kernel

theorem pin303 : inertia.quadForm sSingle xCap < BPair.unit := by decide +kernel

theorem pin304 : ¬ ((elim.dotN xCap (elim.matVec sSingle yCap)
      + elim.dotN yCap (elim.matVec sSingle xCap))
    * (elim.dotN xCap (elim.matVec sSingle yCap)
      + elim.dotN yCap (elim.matVec sSingle xCap))
  < BPair.ofNat 4 * (inertia.quadForm sSingle xCap
      * inertia.quadForm sSingle yCap)) := by decide +kernel

theorem pin305 : ¬ (2 ≤ inertia.revAt spSingle) := by decide +kernel

theorem pin306 : 1 ≤ inertia.revAt spSingle :=
  inertia.strictForcing sSingle xCap rfl (by decide +kernel) spSingle (by decide +kernel)

theorem pin307 : inertia.revAt spSingle = 1 := by decide +kernel

theorem pin308 : ¬ (1 ≤ inertia.revAt spNone) := by decide +kernel

/-! The positive form's cross read (`psd_cross`, `lem:cornerkey`'s cap): at
the positive-definite datum and the two unit vectors the exchanged
pairings' sum `2` squares to `4` at or below four times the forms'
product `16`, decided and through the theorem; at the diagonal datum
with its lower-side unit the split reads but the positive read refuses,
and the cross read parts, `0` against `4 · (2 · -1)`. -/
theorem pin309 : (elim.dotN [⟨2, 1⟩, u] (elim.matVec sPd [u, ⟨2, 1⟩])
      + elim.dotN [u, ⟨2, 1⟩] (elim.matVec sPd [⟨2, 1⟩, u]))
    * (elim.dotN [⟨2, 1⟩, u] (elim.matVec sPd [u, ⟨2, 1⟩])
      + elim.dotN [u, ⟨2, 1⟩] (elim.matVec sPd [⟨2, 1⟩, u]))
    ≤ BPair.ofNat 4 * (inertia.quadForm sPd [⟨2, 1⟩, u]
      * inertia.quadForm sPd [u, ⟨2, 1⟩]) := by decide +kernel
theorem pin310 : (elim.dotN [⟨2, 1⟩, u] (elim.matVec sPd [u, ⟨2, 1⟩])
      + elim.dotN [u, ⟨2, 1⟩] (elim.matVec sPd [⟨2, 1⟩, u]))
    * (elim.dotN [⟨2, 1⟩, u] (elim.matVec sPd [u, ⟨2, 1⟩])
      + elim.dotN [u, ⟨2, 1⟩] (elim.matVec sPd [⟨2, 1⟩, u]))
    ≤ BPair.ofNat 4 * (inertia.quadForm sPd [⟨2, 1⟩, u]
      * inertia.quadForm sPd [u, ⟨2, 1⟩]) :=
  inertia.psd_cross sPd spPd (by decide +kernel) (by decide +kernel) _ _ rfl rfl
theorem pin311 : ¬ ((elim.dotN [⟨2, 1⟩, u, u] (elim.matVec sDiag [u, ⟨2, 1⟩, u])
      + elim.dotN [u, ⟨2, 1⟩, u] (elim.matVec sDiag [⟨2, 1⟩, u, u]))
    * (elim.dotN [⟨2, 1⟩, u, u] (elim.matVec sDiag [u, ⟨2, 1⟩, u])
      + elim.dotN [u, ⟨2, 1⟩, u] (elim.matVec sDiag [⟨2, 1⟩, u, u]))
    ≤ BPair.ofNat 4 * (inertia.quadForm sDiag [⟨2, 1⟩, u, u]
      * inertia.quadForm sDiag [u, ⟨2, 1⟩, u])) := by decide +kernel

/-! The block sum (`lem:inertia`'s addition at a block diagonal): the
two splits' block sum read at the block diagonal by kernel and
through `splitRead_blockSplit`, at a leading split whose kernel is
occupied (its columns collected to the tail, the congruence the
columns' exchange), at determinants off one (the witnesses scaled at
each other's determinant, the sum's determinant the product), at a
vacant order on either side, and refused at the kernel on the wrong
side of the join. -/

/-- The identity congruence at one kernel column. -/
private def sK : Split 1 :=
  ⟨⟨[[BPair.ofNat 1]], by decide⟩, ⟨[[BPair.ofNat 1]], by decide⟩, [], 1, rfl⟩
private def s2 : Mat := [[BPair.ofNat 2, BPair.ofNat 1], [BPair.ofNat 1, BPair.ofNat 2]]
/-- A split of `s2` at the congruence determinant two. -/
private def sp2 : Split 2 :=
  ⟨⟨[[BPair.ofNat 1, (BPair.ofNat 1).swap], [BPair.unit, BPair.ofNat 2]], by decide⟩,
   ⟨[[BPair.ofNat 2, BPair.ofNat 1], [BPair.unit, BPair.ofNat 1]], by decide⟩,
   [.one (BPair.ofNat 2), .one (BPair.ofNat 6)], 0, rfl⟩
private def s1 : Mat := [[BPair.ofNat 3]]

theorem pin312 : splitRead [[BPair.unit]] sK ∧ splitRead s2 sp2 ∧ pdAt sp2
    ∧ (minor sp2.T.val).oneValue (BPair.ofNat 2)
    ∧ splitRead s1 (scalarSplit 1 (posOfSucc 2)) := by decide +kernel
-- the leading kernel collected to the tail: the congruence the columns' exchange
theorem pin313 : (blockSplit sK (scalarSplit 1 Pos.one)).T.val
      = [[BPair.unit, BPair.ofNat 1], [BPair.ofNat 1, BPair.unit]]
    ∧ (blockSplit sK (scalarSplit 1 Pos.one)).kern = 1
    ∧ splitRead (blockDiag 1 1 [[BPair.unit]] [[BPair.ofNat 1]])
        (blockSplit sK (scalarSplit 1 Pos.one))
    ∧ splitRead (blockDiag 1 1 [[BPair.ofNat 1]] [[BPair.unit]])
        (blockSplit (scalarSplit 1 Pos.one) sK)
    ∧ splitRead (blockDiag 1 2 [[BPair.unit]] s2) (blockSplit sK sp2)
    ∧ (minor (blockSplit sK sp2).T.val).oneValue (BPair.ofNat 2)
    ∧ ¬ splitRead (blockDiag 1 1 [[BPair.unit]] [[BPair.ofNat 1]])
        (blockSplit (scalarSplit 1 Pos.one) sK) := by decide +kernel
theorem pin314 : splitRead (blockDiag 1 1 [[BPair.unit]] [[BPair.ofNat 1]])
    (blockSplit sK (scalarSplit 1 Pos.one)) :=
  splitRead_blockSplit _ _ sK (scalarSplit 1 Pos.one) (by decide +kernel)
    (scalarSplit_read_idMat 1)
-- the witnesses scaled at each other's determinant
theorem pin315 : splitRead (blockDiag 2 1 s2 s1) (blockSplit sp2 (scalarSplit 1 (posOfSucc 2)))
    ∧ splitRead (blockDiag 1 2 s1 s2) (blockSplit (scalarSplit 1 (posOfSucc 2)) sp2)
    ∧ splitRead (blockDiag 2 2 s2 s2) (blockSplit sp2 sp2)
    ∧ (minor (blockSplit sp2 sp2).T.val).oneValue (BPair.ofNat 4)
    ∧ pdAt (blockSplit sp2 sp2) := by decide +kernel
theorem pin316 : splitRead (blockDiag 2 2 s2 s2) (blockSplit sp2 sp2) :=
  splitRead_blockSplit s2 s2 sp2 sp2 (by decide +kernel) (by decide +kernel)
-- a vacant order on either side
theorem pin317 : (minor ([] : Mat)).oneValue (BPair.ofNat 1)
    ∧ splitRead (blockDiag 0 1 [] s1)
        (blockSplit (scalarSplit 0 Pos.one) (scalarSplit 1 (posOfSucc 2)))
    ∧ splitRead (blockDiag 1 0 s1 [])
        (blockSplit (scalarSplit 1 (posOfSucc 2)) (scalarSplit 0 Pos.one))
    ∧ splitRead (blockDiag 0 2 [] s2) (blockSplit (scalarSplit 0 Pos.one) sp2)
    ∧ splitRead (blockDiag 2 0 s2 []) (blockSplit sp2 (scalarSplit 0 Pos.one)) := by
  decide +kernel
theorem pin318 : splitRead (blockDiag 0 2 [] s2) (blockSplit (scalarSplit 0 Pos.one) sp2) :=
  splitRead_blockSplit _ _ (scalarSplit 0 Pos.one) sp2 (scalarSplit_read_idMat 0)
    (by decide +kernel)

/-! The reads at designated places.  The places' permutation at the
rotation `(2, 0, 1)` of the addition's assembled datum conjugates it
to its selection, whose split at the diagonal `2, 6, -15` reads the
one count through the theorem and decided; the distinctness is
load-bearing at the repeated key list `(2, 2, 0)`, whose selection
splits at the diagonal `2, 6` with the kernel block occupied and its
count parting.  The addition at the designated places `2 | 0, 1`:
the pivot `2` at the key `2`, the deflation `[[6, 4], [4, -4]]` at
the adjugate's solve, the count one on both sides through the
theorem and decided; the pivot's determinant is load-bearing at the
transposition datum, whose pivot at the vacant key reads the unit
with the deflation vacant and its solve read passing while the
datum's count reads one.  The kernel witness at the datum of equal
entries: the congruence's image of the kernel column, `(-1, 1)`,
off the unit family with its form at the sum's unit, the witness
through the theorem; and the datum's determinant reads the unit
there against the assembled datum's off it at the vacant kernel,
the kernel's vacancy the theorem's one binder.  The adjugate's solve
at orders two and three through the theorem and decided. -/

private def dM : Mat := blockJoin aP aB aQ
private def dL : List Nat := [2, 0, 1]
private def dSpL : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨3, 1⟩, ⟨1, 3⟩], [u, u, ⟨4, 1⟩]], rfl⟩,
   ⟨[[⟨7, 1⟩, ⟨1, 4⟩, u], [u, ⟨4, 1⟩, ⟨3, 1⟩], [u, u, ⟨3, 1⟩]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨7, 1⟩, .one ⟨1, 16⟩], 0, rfl⟩

theorem pin319 : splitRead (selM dL dL dM) dSpL := by decide +kernel
theorem pin320 : revAt dSpL = revAt aSpS :=
  rev_perm (n := 3) dM dL (by decide +kernel) rfl (by decide +kernel)
    (by decide +kernel) aSpS (by decide +kernel) dSpL (by decide +kernel)
theorem pin321 : revAt dSpL = 1 := by decide +kernel

private def dRep : List Nat := [2, 2, 0]
private def dSpRep : Split 3 :=
  ⟨⟨[[⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 2⟩], [u, u, ⟨2, 1⟩], [u, ⟨3, 1⟩, u]], rfl⟩,
   ⟨[[⟨1, 3⟩, ⟨1, 3⟩, ⟨2, 1⟩], [u, u, ⟨1, 2⟩], [u, ⟨1, 3⟩, u]], rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨7, 1⟩], 1, rfl⟩

theorem pin322 : ¬ ground.distinctList dRep := by decide +kernel
theorem pin323 : splitRead (selM dRep dRep dM) dSpRep := by decide +kernel
theorem pin324 : ¬ (revAt dSpRep = revAt aSpS) := by decide +kernel

private def dCw : Mat := matMul (adjM (selM [2] [2] dM)) (selM [2] [0, 1] dM)
private def dSpD : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 3⟩], [u, ⟨4, 1⟩]], rfl⟩,
   ⟨[[⟨4, 1⟩, ⟨3, 1⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨7, 1⟩, .one ⟨1, 61⟩], 0, rfl⟩

theorem pin325 : matOneValue (deflMat (selM [2] [2] dM) (selM [2] [0, 1] dM)
    (selM [0, 1] [0, 1] dM) dCw) [[⟨7, 1⟩, ⟨5, 1⟩], [⟨5, 1⟩, ⟨1, 5⟩]] := by
  decide +kernel
theorem pin326 : splitRead (selM [2] [2] dM) aSpP := by decide +kernel
theorem pin327 : splitRead (deflMat (selM [2] [2] dM) (selM [2] [0, 1] dM)
    (selM [0, 1] [0, 1] dM) dCw) dSpD := by decide +kernel
theorem pin328 : revAt aSpS = revAt aSpP + revAt dSpD :=
  rev_places (n := 3) dM [2] [0, 1] (by decide) (by decide +kernel)
    (by decide +kernel) rfl (by decide +kernel) (by decide +kernel) dCw
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) aSpS (by decide +kernel) aSpP (by decide +kernel)
    dSpD (by decide +kernel)
theorem pin329 : revAt aSpS = revAt aSpP + revAt dSpD := by decide +kernel

private def dM2 : Mat := [[u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, u], [u, u, ⟨2, 1⟩]]
private def dSpM2 : Split 3 :=
  ⟨⟨idMat 3, rfl⟩, ⟨idMat 3, rfl⟩, [.two u ⟨2, 1⟩ u, .one ⟨2, 1⟩], 0, rfl⟩
private def dSpP0 : Split 1 := ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [], 1, rfl⟩
private def dSpD0 : Split 2 := ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [], 2, rfl⟩
private def dCw0 : Mat := [[u, u]]

theorem pin330 : splitRead dM2 dSpM2 := by decide +kernel
theorem pin331 : splitRead (selM [0] [0] dM2) dSpP0 := by decide +kernel
theorem pin332 : matOneValue (matMul (selM [0] [0] dM2) dCw0)
    (matScaleB (minor (selM [0] [0] dM2)) (selM [0] [1, 2] dM2)) := by
  decide +kernel
theorem pin333 : (minor (selM [0] [0] dM2)).oneValue BPair.unit := by decide +kernel
theorem pin334 : splitRead (deflMat (selM [0] [0] dM2) (selM [0] [1, 2] dM2)
    (selM [1, 2] [1, 2] dM2) dCw0) dSpD0 := by decide +kernel
theorem pin335 : ¬ (revAt dSpM2 = revAt dSpP0 + revAt dSpD0) := by decide +kernel

private def kK : Mat := [[⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]
private def kSp : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 2⟩], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩]], rfl⟩, [.one ⟨2, 1⟩], 1, rfl⟩
private def kU : List BPair := [⟨1, 2⟩, ⟨2, 1⟩]

theorem pin336 : splitRead kK kSp := by decide +kernel
theorem pin337 : ¬ poly.unitTail kU := by decide +kernel
theorem pin338 : (dotN kU (matVec kK kU)).oneValue BPair.unit := by decide +kernel
theorem pin339 : ∃ v : List BPair, v.length = 2 ∧ ¬ poly.unitTail v
    ∧ (dotN v (matVec kK v)).oneValue BPair.unit :=
  kern_witness kK kSp (by decide +kernel) (by decide)
theorem pin340 : (minor kK).oneValue BPair.unit := by decide +kernel
theorem pin341 : ¬ (minor dM).oneValue BPair.unit :=
  minor_of_kern dM aSpS (by decide +kernel) rfl
theorem pin342 : ¬ (minor dM).oneValue BPair.unit := by decide +kernel

private def qBa : Mat := [[⟨2, 1⟩, ⟨3, 1⟩], [⟨4, 1⟩, ⟨5, 1⟩]]
private def qB3 : Mat := [[⟨2, 1⟩, u], [u, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]

theorem pin343 : matOneValue (matMul aQ (matMul (adjM aQ) qBa))
    (matScaleB (minor aQ) qBa) :=
  adjM_solve (k := 2) (m := 2) aQ qBa (by decide +kernel) rfl (by decide +kernel)
    (by decide)
theorem pin344 : matOneValue (matMul aQ (matMul (adjM aQ) qBa))
    (matScaleB (minor aQ) qBa) := by decide +kernel
theorem pin345 : matOneValue (matMul dM (matMul (adjM dM) qB3))
    (matScaleB (minor dM) qB3) :=
  adjM_solve (k := 3) (m := 2) dM qB3 (by decide +kernel) rfl (by decide +kernel)
    (by decide)
theorem pin346 : matOneValue (matMul dM (matMul (adjM dM) qB3))
    (matScaleB (minor dM) qB3) := by decide +kernel

/-! The grouped form: the gram `diag(1) ⊕ [[2, 1], [1, 2]]` scaled at
the two groups by the weights minus one and two. -/

private def gB : Mat := [[⟨2, 1⟩, u, u], [u, ⟨3, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨3, 1⟩]]
private def xB : Mat := [[⟨1, 2⟩, u, u], [u, ⟨5, 1⟩, ⟨3, 1⟩], [u, ⟨3, 1⟩, ⟨5, 1⟩]]
private def wB : Nat → BPair := fun t => if t = 0 then ⟨1, 2⟩ else ⟨3, 1⟩
private def keyB : Nat → Nat := fun j => if j = 0 then 0 else 1
private def grpB : List (List Nat) := placesBy keyB 3

private theorem gB_read : splitRead gB (mkSplit 3 gB) :=
  mkSplit_read 3 gB (by decide +kernel) (by decide +kernel)
private theorem crossB : ((List.range 3).all (fun j => (List.range 3).all (fun i =>
    decide (groupOf j grpB = groupOf i grpB)
      || decide ((getAt u (getAt [] gB j) i).oneValue u)))) = true := by
  decide +kernel
private theorem entB : ((List.range 3).all (fun j => (List.range 3).all (fun i =>
    decide ((getAt u (getAt [] xB j) i).oneValue
      (wB j * getAt u (getAt [] gB j) i))))) = true := by
  decide +kernel
private theorem agrB : ((List.range 3).all (fun j => (List.range 3).all (fun i =>
    !decide (groupOf j grpB = groupOf i grpB)
      || decide ((wB j).oneValue (wB i))))) = true := by
  decide +kernel
private theorem remB : (([1, 2] : List Nat).all (fun i =>
    decide (u ≤ wB i))) = true := by decide +kernel

theorem pin347 : psdAt (mkSplit 2 (selM [1, 2] [1, 2] xB)) :=
  blockScaled_psd gB xB (by decide +kernel) (by decide +kernel) (Nat.succ_pos 2)
    (mkSplit 3 gB) gB_read (by decide +kernel) grpB
    (placesBy_partition keyB 3).1 (placesBy_partition keyB 3).2.1
    (placesBy_partition keyB 3).2.2.1 (placesBy_partition keyB 3).2.2.2
    (fun j i hj hi hne => by
      have h := ground.all_range_read 3 (ground.all_range_read 3 crossB j hj) i hi
      cases hg : decide (groupOf j grpB = groupOf i grpB) with
      | true => exact absurd (of_decide_eq_true hg) hne
      | false => rw [hg] at h; exact of_decide_eq_true h)
    wB
    (fun j i hj hi hg => by
      have h := ground.all_range_read 3 (ground.all_range_read 3 agrB j hj) i hi
      cases hgd : decide (groupOf j grpB = groupOf i grpB) with
      | true => rw [hgd] at h; exact of_decide_eq_true h
      | false => exact absurd hg (of_decide_eq_false hgd))
    (fun j i hj hi => of_decide_eq_true (ground.all_range_read 3
      (ground.all_range_read 3 entB j hj) i hi))
    [1, 2] (by decide +kernel) (Nat.succ_pos 1)
    (fun i hi => of_decide_eq_true (ground.all_of_mem _ _ remB i hi))
    (mkSplit 2 (selM [1, 2] [1, 2] xB))
    (mkSplit_read 2 _ (by decide +kernel) (by decide +kernel))
theorem pin348 : grpB = [[0], [1, 2]] ∧ psdAt (mkSplit 2 (selM [1, 2] [1, 2] xB)) := by
  decide +kernel
theorem pin349 : ¬ (u ≤ wB 0) := by decide +kernel
theorem pin350 : ¬ psdAt (mkSplit 1 (selM [0] [0] xB)) := by decide +kernel

/-! The join's entry and its symmetry at the `1 + 2` join `aP`, `aB`,
`aQ`: the entry read through `entry_blockJoin` at the trailing row's
head column (the coupling's exchange) and at the trailing keys (the
trailing block), each against the kernel's decision; the refusal at
a coupling one column short, the join then one row short and the
trailing entry read at the default; the symmetry through
`symmRead_blockJoin` at the symmetric blocks, and its refusal at a
trailing block off its own transpose. -/

private def aBshort : Mat := [[⟨2, 1⟩]]
private def aQoff : Mat := [[⟨1, 2⟩, u], [⟨2, 1⟩, ⟨3, 1⟩]]

theorem pin351 : ground.getAt u (ground.getAt [] (blockJoin aP aB aQ) 2) 0 = ⟨1, 2⟩
    ∧ ground.getAt u (ground.getAt [] (blockJoin aP aB aQ) 2) 2 = ⟨3, 1⟩ :=
  ⟨(entry_blockJoin (k := 1) (m := 2) aP aB aQ (by decide) rfl (by decide +kernel) rfl (by decide +kernel) rfl 2 0
      (by decide)).trans (by decide +kernel),
   (entry_blockJoin (k := 1) (m := 2) aP aB aQ (by decide) rfl (by decide +kernel) rfl (by decide +kernel) rfl 2 2
      (by decide)).trans (by decide +kernel)⟩
theorem pin352 : ¬ (ground.getAt u (ground.getAt [] (blockJoin aP aBshort aQ) 2) 2 = ⟨3, 1⟩) := by
  decide +kernel
theorem pin353 : symmRead (blockJoin aP aB aQ) :=
  symmRead_blockJoin (k := 1) (m := 2) aP aB aQ (by decide) (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin354 : ¬ symmRead (blockJoin aP aB aQoff) := by decide +kernel

/-! The once-cleared deflation's symmetry at a pivot off the unit
(`deflMatP_symm`), routed at a nonsingular pivot of a symmetric
square beside the decided read, the witness the adjugate's solve;
and its pivot binder isolated at a singular pivot whose free witness
holds the solve read, the pivot's product with it the sum's unit at
every entry, while the once-cleared deflation refuses the symmetry,
the coupling's transpose against the witness a lower triangle. -/

private def sM : Mat :=
  [[⟨2, 1⟩, u, u, ⟨2, 1⟩], [u, u, ⟨2, 1⟩, ⟨2, 1⟩],
   [u, ⟨2, 1⟩, u, u], [⟨2, 1⟩, ⟨2, 1⟩, u, u]]
private def sCwA : Mat :=
  matMul (adjM (selM [1, 2] [1, 2] sM)) (selM [1, 2] [0, 3] sM)
private def sCw : Mat := [[u, u], [⟨2, 1⟩, u]]

theorem pin355 : matOneValue
    (transposeM (deflMatP (selM [1, 2] [1, 2] sM) (selM [1, 2] [0, 3] sM)
      (selM [0, 3] [0, 3] sM) sCwA))
    (deflMatP (selM [1, 2] [1, 2] sM) (selM [1, 2] [0, 3] sM)
      (selM [0, 3] [0, 3] sM) sCwA) :=
  deflMatP_symm (n := 4) sM [1, 2] [0, 3] (by decide) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide) sCwA (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin356 : matOneValue
    (transposeM (deflMatP (selM [1, 2] [1, 2] sM) (selM [1, 2] [0, 3] sM)
      (selM [0, 3] [0, 3] sM) sCwA))
    (deflMatP (selM [1, 2] [1, 2] sM) (selM [1, 2] [0, 3] sM)
      (selM [0, 3] [0, 3] sM) sCwA) := by decide +kernel
theorem pin357 : matOneValue (matMul (selM [0, 1] [0, 1] sM) sCw)
    (matScaleB (minor (selM [0, 1] [0, 1] sM)) (selM [0, 1] [2, 3] sM)) := by
  decide +kernel
theorem pin358 : (minor (selM [0, 1] [0, 1] sM)).oneValue BPair.unit := by
  decide +kernel
theorem pin359 : ¬ matOneValue
    (transposeM (deflMatP (selM [0, 1] [0, 1] sM) (selM [0, 1] [2, 3] sM)
      (selM [2, 3] [2, 3] sM) sCw))
    (deflMatP (selM [0, 1] [0, 1] sM) (selM [0, 1] [2, 3] sM)
      (selM [2, 3] [2, 3] sM) sCw) := by decide +kernel

/-! The swapped once-cleared deflation's count at a pivot keeping its
lower side (`rev_placesM`), its side binder isolated at a pivot
keeping its upper side: the solve holds, the pivot's determinant sits
above the unit, and the count read refuses, the swapped deflation a
lower-side entry the datum's count does not hold. -/

private def rM : Mat := [[⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]]
private def rCw : Mat := [[⟨2, 1⟩]]

theorem pin360 : matOneValue (matMul (selM [0] [0] rM) rCw)
    (matScaleB (minor (selM [0] [0] rM)) (selM [0] [1] rM)) := by decide +kernel
theorem pin361 : BPair.unit < minor (selM [0] [0] rM) := by decide +kernel
theorem pin362 : ¬ (revAt (mkSplit 2 rM)
    = revAt (mkSplit 1 (selM [0] [0] rM))
      + revAt (mkSplit 1 (matSwap (deflMatP (selM [0] [0] rM) (selM [0] [1] rM)
        (selM [1] [1] rM) rCw)))) := by decide +kernel

end inertia
