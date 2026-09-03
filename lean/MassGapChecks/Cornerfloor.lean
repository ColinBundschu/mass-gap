import MassGap.Cornerfloor
import MassGap.Cornerstore
/-!
The check module for `lem:corner`'s cell floor at the seam.  The
seam tie runs at the residue `2`: the well head at the rate `[1 : 1]`
and the scale `[1 : 1]` at the order two, and at the rate `[3 : 2]`
and the scale `[2 : 3]` at the order three, each read entrywise
against the seam pencil's site by kernel `decide` beside the
`well_seam` route, with the rate's second member isolated at the
vacant rate second member, where the well's bond reads the sum's unit
against the line site's occupied bond.  The vacant rate's line reads
its count vacant at the order three over the well's own computed
split (`base_psd`) and at the seam pencil (`base_count`), and the
rate `[9 : 1]` at the scale `[2 : 3]` reads its count one at the
well and at the seam pencil through `line_count`, the count carried
across the two splits.

The store's cell reads at the residue `2`'s certificate
(`cornerpivot.disconjC`): the scale `[1 : 524288]` at the ceiling,
the endpoint key `1654` decided with its two neighbors refused (the
comparison at `1653`, the leastness at `1655`), and the cut member
`[6 : 5]` at the gap one with its line at or below the stated rate
`[8 : 1]`, the lower rate's two data decided once and read two-sided
at `633` against `100`; the member `[4 : 3]` refuses the rate
conjunct, and the scale `[2 : 524288]` refuses the ceiling.  The
member's gap `1 ≤ g` is the frame `lem:cornerpivot`(vi) states, a
member beyond one, and its join `b + g = a` is `def:ground`'s gap
field of the stated order, neither parted at the store's order.  On
that cell the flat window, the floor and the chain's occupied count
at the member line are read at the theorem routes over every order
beyond the endpoint depth, the splits universally bound and the
chain's coupling shape `hB` the frame `truncation.count_head_le`
states, the floor's two members decided positive beside
`floor_pos`.
-/

open ground elim inertia certconstruct corner cornerpivot

set_option maxRecDepth 8192

/-! ## The seam tie -/

example : matOneValue (wellMat 2 1 1 1 1 2) (seamSite 2 1 1 2 1 1 2) := by
  decide +kernel
example : matOneValue (wellMat 2 1 1 1 1 2) (seamSite 2 1 1 2 1 1 2) :=
  well_seam 2 1 1 2 (by decide +kernel) 1 1 2

example : matOneValue (wellMat 2 3 2 2 3 3) (seamSite 2 3 2 2 2 3 3) := by
  decide +kernel
example : matOneValue (wellMat 2 3 2 2 3 3) (seamSite 2 3 2 2 2 3 3) :=
  well_seam 2 3 2 2 (by decide +kernel) 2 3 3

/-- The rate's second member is load-bearing: at the vacant second
member the well's bond weight reads the sum's unit while the line
site's bond, cleared at the padded scale one, stays occupied. -/
example : ¬ matOneValue (wellMat 2 1 0 1 1 2) (seamSite 2 1 0 2 1 1 2) := by
  decide +kernel

example : sqAt (headE 2 3) 3 := by decide +kernel
example : sqAt (headE 2 3) 3 := headE_sq 2 3
example : sqAt (headM 2 3) 3 := by decide +kernel
example : sqAt (headM 2 3) 3 := headM_sq 2 3
example : sqAt (seamSite 2 3 2 2 2 3 3) 3 := by decide +kernel
example : sqAt (seamSite 2 3 2 2 2 3 3) 3 := lineSite_sq 2 3 2 2 2 3 3

/-! ## The vacant rate's line -/

example : splitRead (wellMat 2 0 1 1 1 3) (mkSplit 3 (wellMat 2 0 1 1 1 3)) := by
  decide +kernel
example : revAt (mkSplit 3 (wellMat 2 0 1 1 1 3)) = 0 := by decide +kernel
example : revAt (mkSplit 3 (wellMat 2 0 1 1 1 3)) = 0 :=
  base_psd 2 1 (by decide +kernel) 1 1 3 (mkSplit 3 (wellMat 2 0 1 1 1 3))
    (by decide +kernel)

example : countAtPair
    (matScale (posOfSucc (1 - 1))
      (cornerPencil (headE 2 3) (matScale (posOfSucc 2) (headM 2 3)) 1 1))
    (idMat 3) (lineX 2 0 1 1) (lineY 2 2 1 1) 0
    (mkSplit 3 (seamSite 2 0 1 2 1 1 3)) := by decide +kernel
example : countAtPair
    (matScale (posOfSucc (1 - 1))
      (cornerPencil (headE 2 3) (matScale (posOfSucc 2) (headM 2 3)) 1 1))
    (idMat 3) (lineX 2 0 1 1) (lineY 2 2 1 1) 0
    (mkSplit 3 (seamSite 2 0 1 2 1 1 3)) :=
  base_count 2 1 2 (by decide +kernel) 1 1 3 (mkSplit 3 (wellMat 2 0 1 1 1 3))
    (mkSplit 3 (seamSite 2 0 1 2 1 1 3)) (by decide +kernel)
    (by decide +kernel)

/-! ## The count carried across the seam at an occupied rate -/

example : revAt (mkSplit 3 (wellMat 2 9 1 2 3 3)) = 1 := by decide +kernel

example : countAtPair
    (matScale (posOfSucc (1 - 1))
      (cornerPencil (headE 2 3) (matScale (posOfSucc 2) (headM 2 3)) 2 3))
    (idMat 3) (lineX 2 9 2 3) (lineY 2 2 1 3) 1
    (mkSplit 3 (seamSite 2 9 1 2 2 3 3)) := by decide +kernel
example : countAtPair
    (matScale (posOfSucc (1 - 1))
      (cornerPencil (headE 2 3) (matScale (posOfSucc 2) (headM 2 3)) 2 3))
    (idMat 3) (lineX 2 9 2 3) (lineY 2 2 1 3) 1
    (mkSplit 3 (seamSite 2 9 1 2 2 3 3)) :=
  line_count 2 9 1 2 (by decide +kernel) 2 3 3 1
    (mkSplit 3 (wellMat 2 9 1 2 3 3)) (mkSplit 3 (seamSite 2 9 1 2 2 3 3))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ## The store's cell -/

private def enS : Pos := 1
private def edS : Pos := 524288
private def nS : Nat := 1654

private theorem storeE :
    BPair.ofPos enS * BPair.ofPos disconjC.e0d
      ≤ disconjC.e0n * BPair.ofPos edS := by decide +kernel

private theorem storeEnd : endRead (posVal enS) (posVal edS) preR nS := by
  decide +kernel

/-- The lower rate's two data at the store, decided once and read
by every comparison below. -/
private theorem qNumS : qLowNum (posVal enS) (posVal edS) preR nS
    = 23426036834085297096095917457612244 := by decide +kernel
private theorem qDenS : qLowDen (posVal enS) (posVal edS) preR nS
    = 3700753448353625677535191597842432 := by decide +kernel

private theorem storeRate :
    6 * qLowNum (posVal enS) (posVal edS) preR nS * disconjC.qcD
      ≤ disconjC.qcN * (5 * qLowDen (posVal enS) (posVal edS) preR nS) := by
  rw [qNumS, qDenS]
  decide +kernel

private theorem storeCell : cellRead preR disconjC enS edS nS 6 5 1 :=
  ⟨disconjC_read, storeE, storeEnd, rfl, Nat.le_refl 1, storeRate⟩

/-- The lower rate reads `633` against `100` at the store, two-sided. -/
example : 633 * qLowDen (posVal enS) (posVal edS) preR nS
    ≤ 100 * qLowNum (posVal enS) (posVal edS) preR nS := by
  rw [qNumS, qDenS]
  decide +kernel
example : 100 * qLowNum (posVal enS) (posVal edS) preR nS
    < 634 * qLowDen (posVal enS) (posVal edS) preR nS := by
  rw [qNumS, qDenS]
  decide +kernel

example : ¬ endRead (posVal enS) (posVal edS) preR 1653 := by decide +kernel
example : ¬ endRead (posVal enS) (posVal edS) preR 1655 := by decide +kernel

/-- The rate conjunct is load-bearing: the member `[4 : 3]` sits
beyond the stated rate at the lower rate `633` against `100`. -/
example : ¬ (4 * qLowNum (posVal enS) (posVal edS) preR nS * disconjC.qcD
    ≤ disconjC.qcN * (3 * qLowDen (posVal enS) (posVal edS) preR nS)) := by
  rw [qNumS, qDenS]
  decide +kernel

/-- The ceiling conjunct is load-bearing: the scale `[2 : 524288]`
sits beyond the certificate's ceiling. -/
example : ¬ (BPair.ofPos 2 * BPair.ofPos disconjC.e0d
    ≤ disconjC.e0n * BPair.ofPos edS) := by decide +kernel

example : 0 < floorN enS edS preR nS 1 := by
  show 0 < 1 * qLowNum (posVal enS) (posVal edS) preR nS
  rw [qNumS]
  decide +kernel
example : 0 < floorD enS edS preR nS 5 := by
  show 0 < 5 * qLowDen (posVal enS) (posVal edS) preR nS
  rw [qDenS]
  decide +kernel
example : 0 < floorN enS edS preR nS 1 ∧ 0 < floorD enS edS preR nS 5 :=
  floor_pos storeCell

example (n : Nat) (hNn : nS ≤ n) (sp : Split n)
    (hsp : splitRead (wellMat preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
      (5 * qLowDen (posVal enS) (posVal edS) preR nS) enS edS n) sp) :
    revAt sp = 1 :=
  cut_flat storeCell n hNn sp hsp

example (n : Nat) (hNn : nS ≤ n) (sp sp' : Split n)
    (hsp : splitRead (wellMat preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
      (5 * qLowDen (posVal enS) (posVal edS) preR nS) enS edS n) sp)
    (hsp' : splitRead (seamSite preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
      (5 * qLowDen (posVal enS) (posVal edS) preR nS) 2 enS edS n) sp') :
    countAtPair
      (matScale (posOfSucc (5 * qLowDen (posVal enS) (posVal edS) preR nS - 1))
        (cornerPencil (headE preR n) (matScale (posOfSucc preR) (headM 2 n))
          enS edS))
      (idMat n) (lineX preR (6 * qLowNum (posVal enS) (posVal edS) preR nS) enS edS)
      (lineY preR 2 (5 * qLowDen (posVal enS) (posVal edS) preR nS) edS) 1 sp' :=
  line_flat storeCell 2 n hNn sp sp' hsp hsp'

example (n : Nat) (hNn : nS ≤ n) {m : Nat} (H G Q G2 B : Mat) (nf : Nat)
    (sp sp' : Split n) (spF : Split (n + m))
    (hsp : splitRead (wellMat preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
      (5 * qLowDen (posVal enS) (posVal edS) preR nS) enS edS n) sp)
    (hsp' : splitRead (seamSite preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
      (5 * qLowDen (posVal enS) (posVal edS) preR nS) 2 enS edS n) sp')
    (hB : B.length = n)
    (htie : matOneValue
      (siteDatum
        (matAdd H (matScale
          (lineY preR 2 (5 * qLowDen (posVal enS) (posVal edS) preR nS) edS) G))
        (matScale (lineX preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
          enS edS) G))
      (blockJoin
        (siteDatum
          (matAdd
            (matScale (posOfSucc (5 * qLowDen (posVal enS) (posVal edS) preR nS - 1))
              (cornerPencil (headE preR n)
                (matScale (posOfSucc preR) (headM 2 n)) enS edS))
            (matScale (lineY preR 2 (5 * qLowDen (posVal enS) (posVal edS) preR nS)
              edS) (idMat n)))
          (matScale (lineX preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
            enS edS) (idMat n)))
        B
        (siteDatum
          (matAdd Q (matScale
            (lineY preR 2 (5 * qLowDen (posVal enS) (posVal edS) preR nS) edS) G2))
          (matScale (lineX preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
            enS edS) G2))))
    (hf : countAtPair H G
      (lineX preR (6 * qLowNum (posVal enS) (posVal edS) preR nS) enS edS)
      (lineY preR 2 (5 * qLowDen (posVal enS) (posVal edS) preR nS) edS) nf spF) :
    1 ≤ nf :=
  ground_below_line storeCell 2 n hNn H G Q G2 B nf sp sp' spF hsp hsp' hB
    htie hf
