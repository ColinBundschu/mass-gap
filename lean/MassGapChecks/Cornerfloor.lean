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

The transported cells read at the store's own data
(`lem:cornerpivot`(vi)): the residue-two cell at the tied scale
`[26 : 5·1654²]` under the ceiling, the cut member `[6 : 5]` under
the transported rate at the lower rate's decided data, and the
member's line read at `cornerpivot.resRate`'s route with the key's
bracket at `1653` decided; the ceiling conjunct refused at the key
`1651`, the rate conjunct at the member `[4 : 3]`, the residue
conjunct at the residue one, and `resRate`'s bracket binder at the
scale `[1000 : 1]`, where the bracket refuses and the member's line
sits beyond the transported rate.  The residue-one cell reads at the
scale itself with the key `1495`, its two neighbors refused, the cut
member `[41 : 40]` under the stated rate at the lower rate's decided
data and at `cornerpivot.oneRate`'s route, the rate conjunct refused
at `[42 : 40]` and `oneRate`'s bracket binder at the scale
`[1000 : 1]`; `resRate`'s key clearing twenty residues refused at
the residue `200` with the key `1652`, and `oneRate`'s key
comparison refused at the scale `[1 : 10000000]`, each parting the
member's line alone; the floor's two shape binders refused at the
vacant gap and the vacant member.  The flat windows at both cells
are read at the theorem routes over every order beyond the key.
The key floors `1652 ≤ N` and `1495 ≤ N` of the two rate reads are
the tex's frame, the ceiling's read, the two cleared displays
holding from the keys `151` and `364` (`ChecksCornerpivot`).
-/

open ground elim inertia certconstruct corner cornerpivot

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
  floor_pos enS edS preR nS 1 5 storeEnd.1 (Nat.le_refl 1) (by decide)

/-- The floor's two shape binders are load-bearing: at the vacant
gap the first member reads the sum's unit, at the vacant cut member
the second. -/
example : ¬ (0 < floorN enS edS preR nS 0) := by
  show ¬ (0 < 0 * qLowNum (posVal enS) (posVal edS) preR nS)
  rw [Nat.zero_mul]
  decide
example : ¬ (0 < floorD enS edS preR nS 0) := by
  show ¬ (0 < 0 * qLowDen (posVal enS) (posVal edS) preR nS)
  rw [Nat.zero_mul]
  decide

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
  line_count preR _ _ 2 (by rw [qDenS]; decide +kernel) enS edS n 1 sp sp' hsp
    (cut_flat storeCell n hNn sp hsp) hsp'

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
  ground_below_line preR _ _ 2 (by rw [qDenS]; decide +kernel) enS edS n H G Q G2 B nf
    sp sp' spF hsp (cut_flat storeCell n hNn sp hsp) hsp' hB htie hf

/-! ## The transported cells at the store -/

private theorem storeCeilT :
    BPair.ofPos 26 * BPair.ofPos disconjC.e0d
      ≤ disconjC.e0n * BPair.ofPos (tieScaleD nS) := by decide +kernel

private theorem storeRateT :
    6 * qLowNum (posVal enS) (posVal edS) preR nS * posVal enS
        * (disconjC.qcD * (5 * nS * nS))
      ≤ disconjC.qcN * 26
        * (5 * qLowDen (posVal enS) (posVal edS) preR nS * posVal edS) := by
  rw [qNumS, qDenS]
  decide +kernel

private theorem storeCellT : cellReadT preR disconjC enS edS nS 6 5 1 :=
  ⟨by decide, disconjC_read, storeCeilT, storeEnd, rfl, Nat.le_refl 1, storeRateT⟩

/-- The transported rate's member `[6 : 5]` reads at the theorem
route: the key's bracket at `1653` and the key clearing twenty
residues at the residue two. -/
example : 6 * qLowNum (posVal enS) (posVal edS) preR nS * posVal enS
      * (1 * (5 * nS * nS))
    ≤ 8 * 26 * (5 * qLowDen (posVal enS) (posVal edS) preR nS * posVal edS) :=
  resRate (posVal enS) (posVal edS) preR nS (by decide) (by decide)
    (by decide +kernel)

/-- The tied scale's ceiling conjunct is load-bearing: at the key
`1651` the tied scale sits beyond the certificate's ceiling. -/
example : ¬ (BPair.ofPos 26 * BPair.ofPos disconjC.e0d
    ≤ disconjC.e0n * BPair.ofPos (tieScaleD 1651)) := by decide +kernel

/-- The transported rate conjunct is load-bearing: the member
`[4 : 3]` sits beyond the transported rate at the store. -/
example : ¬ (4 * qLowNum (posVal enS) (posVal edS) preR nS * posVal enS
      * (disconjC.qcD * (5 * nS * nS))
    ≤ disconjC.qcN * 26
      * (3 * qLowDen (posVal enS) (posVal edS) preR nS * posVal edS)) := by
  rw [qNumS, qDenS]
  decide +kernel

/-- The residue conjunct refuses at the residue one. -/
example : ¬ cellReadT 1 disconjC enS edS nS 6 5 1 := fun h => absurd h.1 (by decide)

/-- The key's bracket binder of `resRate` is load-bearing: at a scale
whose first member is `1000` against `1` the bracket refuses and the
member's line sits beyond the transported rate. -/
example : ¬ (40 * (1652 - 1) ^ 4 * 1000 ^ 2 < 363 * (2 + 1) * 1 ^ 2) := by
  decide +kernel
example : ¬ (6 * qLowNum 1000 1 2 1652 * 1000 * (1 * (5 * 1652 * 1652))
    ≤ 8 * 26 * (5 * qLowDen 1000 1 2 1652 * 1)) := by decide +kernel

/-- The key clearing twenty residues is load-bearing at `resRate`: at
the residue `200` with the key `1652` at the scale `[1 : 63899]` the
bracket holds and the key comparison holds, the key sits under
twenty residues, and the member's line sits beyond the transported
rate. -/
example : 40 * (1652 - 1) ^ 4 * 1 ^ 2 < 363 * (200 + 1) * 63899 ^ 2 := by
  decide +kernel
example : 363 * (200 + 1) * 63899 ^ 2 ≤ 40 * 1652 ^ 4 * 1 ^ 2 := by decide +kernel
example : ¬ (20 * 200 ≤ 1652) := by decide
example : ¬ (6 * qLowNum 1 63899 200 1652 * 1 * (1 * (5 * 1652 * 1652))
    ≤ 8 * 26 * (5 * qLowDen 1 63899 200 1652 * 1)) := by decide +kernel

example (n : Nat) (hNn : nS ≤ n) (sp : Split n)
    (hsp : splitRead (wellMat preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
      (5 * qLowDen (posVal enS) (posVal edS) preR nS) enS edS n) sp) :
    revAt sp = 1 :=
  cut_flat_T storeCellT n hNn sp hsp

/-! ## The residue-one cell at the store's scale -/

private def nO : Nat := 1495

private theorem storeEndO : endRead (posVal enS) (posVal edS) 1 nO := by
  decide +kernel

private theorem qNumO : qLowNum (posVal enS) (posVal edS) 1 nO
    = 7699016543785802407062498393736704 := by decide +kernel
private theorem qDenO : qLowDen (posVal enS) (posVal edS) 1 nO
    = 993459301769947933037121603895296 := by decide +kernel

private theorem storeRateO :
    41 * qLowNum (posVal enS) (posVal edS) 1 nO * disconjC.qcD
      ≤ disconjC.qcN * (40 * qLowDen (posVal enS) (posVal edS) 1 nO) := by
  rw [qNumO, qDenO]
  decide +kernel

private theorem storeCellS : cellReadS disconjC enS edS nO 41 40 1 :=
  ⟨disconjC_read, storeE, storeEndO, rfl, Nat.le_refl 1, storeRateO⟩

/-- The stated rate's member `[41 : 40]` reads at the theorem route
at the residue one: the key from `1495` with its bracket and its
comparison. -/
example : 41 * qLowNum (posVal enS) (posVal edS) 1 nO * 1
    ≤ 8 * (40 * qLowDen (posVal enS) (posVal edS) 1 nO) :=
  oneRate (posVal enS) (posVal edS) nO (by decide) (by decide +kernel)
    (by decide +kernel)

example : ¬ endRead (posVal enS) (posVal edS) 1 1494 := by decide +kernel
example : ¬ endRead (posVal enS) (posVal edS) 1 1496 := by decide +kernel

/-- The stated-rate conjunct is load-bearing at the residue one: the
member `[42 : 40]` sits beyond the stated rate. -/
example : ¬ (42 * qLowNum (posVal enS) (posVal edS) 1 nO * disconjC.qcD
    ≤ disconjC.qcN * (40 * qLowDen (posVal enS) (posVal edS) 1 nO)) := by
  rw [qNumO, qDenO]
  decide +kernel

/-- The key's bracket binder of `oneRate` is load-bearing: at the
scale `[1000 : 1]` the bracket refuses and the member's line sits
beyond the stated rate. -/
example : ¬ (40 * (1495 - 1) ^ 4 * 1000 ^ 2 < 363 * (1 + 1) * 1 ^ 2) := by
  decide +kernel
example : ¬ (41 * qLowNum 1000 1 1 1495 * 1 ≤ 8 * (40 * qLowDen 1000 1 1 1495)) := by
  decide +kernel

/-- The key's comparison binder of `oneRate` is load-bearing: at the
scale `[1 : 10000000]` the bracket holds at the key `1495`, the
comparison refuses, and the member's line sits beyond the stated
rate. -/
example : 40 * (1495 - 1) ^ 4 * 1 ^ 2 < 363 * (1 + 1) * 10000000 ^ 2 := by
  decide +kernel
example : ¬ (363 * (1 + 1) * 10000000 ^ 2 ≤ 40 * 1495 ^ 4 * 1 ^ 2) := by decide +kernel
example : ¬ (41 * qLowNum 1 10000000 1 1495 * 1 ≤ 8 * (40 * qLowDen 1 10000000 1 1495)) := by
  decide +kernel

example (n : Nat) (hNn : nO ≤ n) (sp : Split n)
    (hsp : splitRead (wellMat 1 (41 * qLowNum (posVal enS) (posVal edS) 1 nO)
      (40 * qLowDen (posVal enS) (posVal edS) 1 nO) enS edS n) sp) :
    revAt sp = 1 :=
  cut_flat_S storeCellS n hNn sp hsp
