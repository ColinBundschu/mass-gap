import MassGap.Cornerfloor
import MassGap.Cornerstore
/-!
The check module for `lem:cornerfloor` at the seam.  The
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

namespace cornerfloor

open ground elim inertia certconstruct corner cornerfloor cornerpivot

/-! ## The seam tie -/

theorem pin1 : matOneValue (wellMat 2 1 1 1 1 2) (seamSite 2 1 1 2 1 1 2) := by
  decide +kernel
theorem pin2 : matOneValue (wellMat 2 1 1 1 1 2) (seamSite 2 1 1 2 1 1 2) :=
  well_seam 2 1 1 2 (by decide +kernel) 1 1 2

theorem pin3 : matOneValue (wellMat 2 3 2 2 3 3) (seamSite 2 3 2 2 2 3 3) := by
  decide +kernel
theorem pin4 : matOneValue (wellMat 2 3 2 2 3 3) (seamSite 2 3 2 2 2 3 3) :=
  well_seam 2 3 2 2 (by decide +kernel) 2 3 3

/-- The rate's second member is load-bearing: at the vacant second
member the well's bond weight reads the sum's unit while the line
site's bond, cleared at the padded scale one, stays occupied. -/
theorem pin5 : ¬ matOneValue (wellMat 2 1 0 1 1 2) (seamSite 2 1 0 2 1 1 2) := by
  decide +kernel

theorem pin6 : sqAt (headE 2 3) 3 := by decide +kernel
theorem pin7 : sqAt (headE 2 3) 3 := headE_sq 2 3
theorem pin8 : sqAt (headM 2 3) 3 := by decide +kernel
theorem pin9 : sqAt (headM 2 3) 3 := headM_sq 2 3
theorem pin10 : sqAt (seamSite 2 3 2 2 2 3 3) 3 := by decide +kernel
theorem pin11 : sqAt (seamSite 2 3 2 2 2 3 3) 3 := lineSite_sq 2 3 2 2 2 3 3

/-! ## The vacant rate's line -/

theorem pin12 : splitRead (wellMat 2 0 1 1 1 3) (mkSplit 3 (wellMat 2 0 1 1 1 3)) := by
  decide +kernel
theorem pin13 : revAt (mkSplit 3 (wellMat 2 0 1 1 1 3)) = 0 := by decide +kernel
theorem pin14 : revAt (mkSplit 3 (wellMat 2 0 1 1 1 3)) = 0 :=
  base_psd 2 1 (by decide +kernel) 1 1 3 (mkSplit 3 (wellMat 2 0 1 1 1 3))
    (by decide +kernel)

theorem pin15 : countAtPair
    (matScale (posOfSucc (1 - 1))
      (cornerPencil (headE 2 3) (matScale (posOfSucc 2) (headM 2 3)) 1 1))
    (idMat 3) (lineX 2 0 1 1) (lineY 2 2 1 1) 0
    (mkSplit 3 (seamSite 2 0 1 2 1 1 3)) := by decide +kernel
theorem pin16 : countAtPair
    (matScale (posOfSucc (1 - 1))
      (cornerPencil (headE 2 3) (matScale (posOfSucc 2) (headM 2 3)) 1 1))
    (idMat 3) (lineX 2 0 1 1) (lineY 2 2 1 1) 0
    (mkSplit 3 (seamSite 2 0 1 2 1 1 3)) :=
  base_count 2 1 2 (by decide +kernel) 1 1 3 (mkSplit 3 (wellMat 2 0 1 1 1 3))
    (mkSplit 3 (seamSite 2 0 1 2 1 1 3)) (by decide +kernel)
    (by decide +kernel)

/-! ## The count carried across the seam at an occupied rate -/

theorem pin17 : revAt (mkSplit 3 (wellMat 2 9 1 2 3 3)) = 1 := by decide +kernel

theorem pin18 : countAtPair
    (matScale (posOfSucc (1 - 1))
      (cornerPencil (headE 2 3) (matScale (posOfSucc 2) (headM 2 3)) 2 3))
    (idMat 3) (lineX 2 9 2 3) (lineY 2 2 1 3) 1
    (mkSplit 3 (seamSite 2 9 1 2 2 3 3)) := by decide +kernel
theorem pin19 : countAtPair
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
theorem pin20 : 633 * qLowDen (posVal enS) (posVal edS) preR nS
    ≤ 100 * qLowNum (posVal enS) (posVal edS) preR nS := by
  rw [qNumS, qDenS]
  decide +kernel
theorem pin21 : 100 * qLowNum (posVal enS) (posVal edS) preR nS
    < 634 * qLowDen (posVal enS) (posVal edS) preR nS := by
  rw [qNumS, qDenS]
  decide +kernel

theorem pin22 : ¬ endRead (posVal enS) (posVal edS) preR 1653 := by decide +kernel
theorem pin23 : ¬ endRead (posVal enS) (posVal edS) preR 1655 := by decide +kernel

/-- The rate conjunct is load-bearing: the member `[4 : 3]` sits
beyond the stated rate at the lower rate `633` against `100`. -/
theorem pin24 : ¬ (4 * qLowNum (posVal enS) (posVal edS) preR nS * disconjC.qcD
    ≤ disconjC.qcN * (3 * qLowDen (posVal enS) (posVal edS) preR nS)) := by
  rw [qNumS, qDenS]
  decide +kernel

/-- The ceiling conjunct is load-bearing: the scale `[2 : 524288]`
sits beyond the certificate's ceiling. -/
theorem pin25 : ¬ (BPair.ofPos 2 * BPair.ofPos disconjC.e0d
    ≤ disconjC.e0n * BPair.ofPos edS) := by decide +kernel

theorem pin26 : 0 < floorN enS edS preR nS 1 := by
  show 0 < 1 * qLowNum (posVal enS) (posVal edS) preR nS
  rw [qNumS]
  decide +kernel
theorem pin27 : 0 < floorD enS edS preR nS 5 := by
  show 0 < 5 * qLowDen (posVal enS) (posVal edS) preR nS
  rw [qDenS]
  decide +kernel
theorem pin28 : 0 < floorN enS edS preR nS 1 ∧ 0 < floorD enS edS preR nS 5 :=
  floor_pos enS edS preR nS 1 5 storeEnd.1 (Nat.le_refl 1) (by decide)

/-- The floor's two shape binders are load-bearing: at the vacant
gap the first member reads the sum's unit, at the vacant cut member
the second. -/
theorem pin29 : ¬ (0 < floorN enS edS preR nS 0) := by
  show ¬ (0 < 0 * qLowNum (posVal enS) (posVal edS) preR nS)
  rw [Nat.zero_mul]
  decide
theorem pin30 : ¬ (0 < floorD enS edS preR nS 0) := by
  show ¬ (0 < 0 * qLowDen (posVal enS) (posVal edS) preR nS)
  rw [Nat.zero_mul]
  decide

theorem pin31 (n : Nat) (hNn : nS ≤ n) (sp : Split n)
    (hsp : splitRead (wellMat preR (6 * qLowNum (posVal enS) (posVal edS) preR nS)
      (5 * qLowDen (posVal enS) (posVal edS) preR nS) enS edS n) sp) :
    revAt sp = 1 :=
  cut_flat storeCell n hNn sp hsp

theorem pin32 (n : Nat) (hNn : nS ≤ n) (sp sp' : Split n)
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

theorem pin33 (n : Nat) (hNn : nS ≤ n) {m : Nat} (H G Q G2 B : Mat) (nf : Nat)
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
theorem pin34 : 6 * qLowNum (posVal enS) (posVal edS) preR nS * posVal enS
      * (1 * (5 * nS * nS))
    ≤ 8 * 26 * (5 * qLowDen (posVal enS) (posVal edS) preR nS * posVal edS) :=
  resRate (posVal enS) (posVal edS) preR nS (by decide) (by decide)
    (by decide +kernel)

/-- The tied scale's ceiling conjunct is load-bearing: at the key
`1651` the tied scale sits beyond the certificate's ceiling. -/
theorem pin35 : ¬ (BPair.ofPos 26 * BPair.ofPos disconjC.e0d
    ≤ disconjC.e0n * BPair.ofPos (tieScaleD 1651)) := by decide +kernel

/-- The transported rate conjunct is load-bearing: the member
`[4 : 3]` sits beyond the transported rate at the store. -/
theorem pin36 : ¬ (4 * qLowNum (posVal enS) (posVal edS) preR nS * posVal enS
      * (disconjC.qcD * (5 * nS * nS))
    ≤ disconjC.qcN * 26
      * (3 * qLowDen (posVal enS) (posVal edS) preR nS * posVal edS)) := by
  rw [qNumS, qDenS]
  decide +kernel

/-- The residue conjunct refuses at the residue one. -/
theorem pin37 : ¬ cellReadT 1 disconjC enS edS nS 6 5 1 := fun h => absurd h.1 (by decide)

/-- The key's bracket binder of `resRate` is load-bearing: at a scale
whose first member is `1000` against `1` the bracket refuses and the
member's line sits beyond the transported rate. -/
theorem pin38 : ¬ (40 * (1652 - 1) ^ 4 * 1000 ^ 2 < 363 * (2 + 1) * 1 ^ 2) := by
  decide +kernel
theorem pin39 : ¬ (6 * qLowNum 1000 1 2 1652 * 1000 * (1 * (5 * 1652 * 1652))
    ≤ 8 * 26 * (5 * qLowDen 1000 1 2 1652 * 1)) := by decide +kernel

/-- The key clearing twenty residues is load-bearing at `resRate`: at
the residue `200` with the key `1652` at the scale `[1 : 63899]` the
bracket holds and the key comparison holds, the key sits under
twenty residues, and the member's line sits beyond the transported
rate. -/
theorem pin40 : 40 * (1652 - 1) ^ 4 * 1 ^ 2 < 363 * (200 + 1) * 63899 ^ 2 := by
  decide +kernel
theorem pin41 : 363 * (200 + 1) * 63899 ^ 2 ≤ 40 * 1652 ^ 4 * 1 ^ 2 := by decide +kernel
theorem pin42 : ¬ (20 * 200 ≤ 1652) := by decide
theorem pin43 : ¬ (6 * qLowNum 1 63899 200 1652 * 1 * (1 * (5 * 1652 * 1652))
    ≤ 8 * 26 * (5 * qLowDen 1 63899 200 1652 * 1)) := by decide +kernel

theorem pin44 (n : Nat) (hNn : nS ≤ n) (sp : Split n)
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
theorem pin45 : 41 * qLowNum (posVal enS) (posVal edS) 1 nO * 1
    ≤ 8 * (40 * qLowDen (posVal enS) (posVal edS) 1 nO) :=
  oneRate (posVal enS) (posVal edS) nO (by decide) (by decide +kernel)
    (by decide +kernel)

theorem pin46 : ¬ endRead (posVal enS) (posVal edS) 1 1494 := by decide +kernel
theorem pin47 : ¬ endRead (posVal enS) (posVal edS) 1 1496 := by decide +kernel

/-- The stated-rate conjunct is load-bearing at the residue one: the
member `[42 : 40]` sits beyond the stated rate. -/
theorem pin48 : ¬ (42 * qLowNum (posVal enS) (posVal edS) 1 nO * disconjC.qcD
    ≤ disconjC.qcN * (40 * qLowDen (posVal enS) (posVal edS) 1 nO)) := by
  rw [qNumO, qDenO]
  decide +kernel

/-- The key's bracket binder of `oneRate` is load-bearing: at the
scale `[1000 : 1]` the bracket refuses and the member's line sits
beyond the stated rate. -/
theorem pin49 : ¬ (40 * (1495 - 1) ^ 4 * 1000 ^ 2 < 363 * (1 + 1) * 1 ^ 2) := by
  decide +kernel
theorem pin50 : ¬ (41 * qLowNum 1000 1 1 1495 * 1 ≤ 8 * (40 * qLowDen 1000 1 1 1495)) := by
  decide +kernel

/-- The key's comparison binder of `oneRate` is load-bearing: at the
scale `[1 : 10000000]` the bracket holds at the key `1495`, the
comparison refuses, and the member's line sits beyond the stated
rate. -/
theorem pin51 : 40 * (1495 - 1) ^ 4 * 1 ^ 2 < 363 * (1 + 1) * 10000000 ^ 2 := by
  decide +kernel
theorem pin52 : ¬ (363 * (1 + 1) * 10000000 ^ 2 ≤ 40 * 1495 ^ 4 * 1 ^ 2) := by decide +kernel
theorem pin53 : ¬ (41 * qLowNum 1 10000000 1 1495 * 1 ≤ 8 * (40 * qLowDen 1 10000000 1 1495)) := by
  decide +kernel

theorem pin54 (n : Nat) (hNn : nO ≤ n) (sp : Split n)
    (hsp : splitRead (wellMat 1 (41 * qLowNum (posVal enS) (posVal edS) 1 nO)
      (40 * qLowDen (posVal enS) (posVal edS) 1 nO) enS edS n) sp) :
    revAt sp = 1 :=
  cut_flat_S storeCellS n hNn sp hsp

/-! The extent toy's data: its corner divisor's display and the extent
read's certificate data. -/

private def u : BPair := BPair.unit

private def xDiv : poly.Poly :=
  [u, u, u, u, ⟨1, 81⟩, u, ⟨41, 1⟩, u, ⟨1, 6⟩]

private def xCt : cellcount.DivCert :=
  ⟨[⟨1, 5⟩, ⟨1, 1⟩], [⟨21, 1⟩, ⟨1, 1⟩, ⟨1, 6⟩], [⟨1, 1⟩, ⟨1, 21⟩],
   [⟨1, 21⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨6, 1⟩], [⟨21, 1⟩, ⟨1, 1⟩, ⟨1, 6⟩],
   [⟨1, 11⟩, ⟨1, 1⟩], [⟨1, 1⟩, ⟨6, 1⟩],
   1, 1, 1, 1, ⟨1, 401⟩, ⟨1, 201⟩⟩

private def xH : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩,
   [.one ⟨3, 1⟩, .one ⟨201, 1⟩], 0, rfl⟩

private def xB1 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1001, 1⟩], [u, ⟨201, 1⟩]], rfl⟩,
   ⟨[[⟨201, 1⟩, ⟨1, 1001⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨201, 1⟩, .one ⟨600000001, 1⟩], 0, rfl⟩

private def xB2 : Split 2 :=
  ⟨⟨[[⟨2, 1⟩, ⟨4001, 1⟩], [u, ⟨351, 1⟩]], rfl⟩,
   ⟨[[⟨351, 1⟩, ⟨1, 4001⟩], [u, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨351, 1⟩, .one ⟨1, 1312500001⟩], 0, rfl⟩

/-! ## The extent interval's mixed window

At `E = I`, `M = diag(1, 20)` over the unit gram, the level
`⟨1 : 6⟩` and the scales `1 < 2 < 3` at the common clearing one:
the bottom and top scales read count one, the pencils
`diag(0, -19)`, `diag(8, -11)` at the level's site `diag(5, -14)`,
`diag(13, -6)`, so the middle scale's count is one by
`interval_flat`, decided beside the route at `diag(8, -11)`; the
electric form's positive-semidefinite binder is load-bearing at
the indefinite `E = diag(1, -1)`, `M = diag(5, -2)` at the level
`⟨1 : 1⟩`, where the bottom and top read one while the middle reads
two; the top's read isolates at the scales `1 < 4 < 5`, the bottom
one and the top vacant, and the bottom's read at the level
`⟨20 : 1⟩` and the scales `1 < 3 < 5`, the top one and the bottom
two.  The height's clearance reads at the scales `[1 : 1] ≤ [2 : 1]`,
the floor `[1 : 2]` against the level `[3 : 1]`, with the scales'
order load-bearing at the scale `[10 : 1]` and the top's clearance
at the floor `1` against the level `1`; and the extent's
positivity reads the root-bearing head's extent bracket `[2, 4]`
above the sum's unit through `contactcell.extentRead_pos`. -/

private def iE : Mat := [[⟨2, 1⟩, u], [u, ⟨2, 1⟩]]
private def iM : Mat := [[⟨2, 1⟩, u], [u, ⟨21, 1⟩]]

private def iSite (en : Pos) : Mat :=
  siteDatum (matAdd (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM en 1))
    (matScale 6 (idMat 2))) (matScale 1 (idMat 2))

private theorem iBot : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM 1 1)) (idMat 2) 1 6 1
    (mkSplit 2 (iSite 1)) := by decide +kernel
private theorem iMid : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM 2 1)) (idMat 2) 1 6 1
    (mkSplit 2 (iSite 2)) := by decide +kernel
private theorem iTop : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM 3 1)) (idMat 2) 1 6 1
    (mkSplit 2 (iSite 3)) := by decide +kernel

theorem pin55 : (1 : Nat) = 1 :=
  interval_flat iE iM (idMat 2) 1 1 2 1 3 1 1 6 1 1 1
    (mkSplit 2 (iSite 1)) (mkSplit 2 (iSite 2)) (mkSplit 2 (iSite 3))
    (scalarSplit 2 1) (scalarSplit 2 3) (scalarSplit 2 5) 3 5
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    iBot iMid iTop (Nat.le_refl 1) (Nat.le_refl 1)

private def nE : Mat := [[⟨2, 1⟩, u], [u, ⟨1, 2⟩]]
private def nM : Mat := [[⟨6, 1⟩, u], [u, ⟨1, 3⟩]]

private def nSite (en : Pos) : Mat :=
  siteDatum (matAdd (matScale (1 * 1 * (1 * 1)) (cornerPencil nE nM en 1))
    (matScale 1 (idMat 2))) (matScale 1 (idMat 2))

/-- The electric form's positivity is load-bearing: at the
indefinite `E` the two end scales read one and the middle two. -/
theorem pin56 : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil nE nM 1 1)) (idMat 2) 1 1 1
    (mkSplit 2 (nSite 1)) := by decide +kernel
theorem pin57 : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil nE nM 2 1)) (idMat 2) 1 1 2
    (mkSplit 2 (nSite 2)) := by decide +kernel
theorem pin58 : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil nE nM 3 1)) (idMat 2) 1 1 1
    (mkSplit 2 (nSite 3)) := by decide +kernel
theorem pin59 : splitRead nE (mkSplit 2 nE) := by decide +kernel
theorem pin60 : ¬ psdAt (mkSplit 2 nE) := by decide +kernel

/-- The top's read is load-bearing: at the level `⟨1 : 6⟩` and the
scales `1 < 4 < 5` the bottom reads one while the top reads
vacant, the middle vacant with it. -/
theorem pin61 : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM 4 1)) (idMat 2) 1 6 0
    (mkSplit 2 (iSite 4)) := by decide +kernel
theorem pin62 : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM 5 1)) (idMat 2) 1 6 0
    (mkSplit 2 (iSite 5)) := by decide +kernel
theorem pin63 : (1 : Pos) * 1 * (1 * 1) + 15 = 4 * 4 * (1 * 1) := by decide +kernel
theorem pin64 : (4 : Pos) * 4 * (1 * 1) + 9 = 5 * 5 * (1 * 1) := by decide +kernel
theorem pin65 : splitRead (matScale (1 * 1 * 15) iE) (scalarSplit 2 15) := by
  decide +kernel

private def iSite20 (en : Pos) : Mat :=
  siteDatum (matAdd (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM en 1))
    (matScale 1 (idMat 2))) (matScale 20 (idMat 2))

/-- The bottom's read is load-bearing: at the level `⟨20 : 1⟩` and
the scales `1 < 3 < 5` the top reads one while the bottom reads
two, the middle two with it. -/
theorem pin66 : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM 1 1)) (idMat 2) 20 1 2
    (mkSplit 2 (iSite20 1)) := by decide +kernel
theorem pin67 : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM 3 1)) (idMat 2) 20 1 2
    (mkSplit 2 (iSite20 3)) := by decide +kernel
theorem pin68 : countAtPair
    (matScale (1 * 1 * (1 * 1)) (cornerPencil iE iM 5 1)) (idMat 2) 20 1 1
    (mkSplit 2 (iSite20 5)) := by decide +kernel
theorem pin69 : (1 : Pos) * 1 * (1 * 1) + 8 = 3 * 3 * (1 * 1) := by decide +kernel
theorem pin70 : (3 : Pos) * 3 * (1 * 1) + 16 = 5 * 5 * (1 * 1) := by decide +kernel
theorem pin71 : splitRead (matScale (1 * 1 * 8) iE) (scalarSplit 2 8) := by
  decide +kernel
theorem pin72 : splitRead (matScale (1 * 1 * 16) iE) (scalarSplit 2 16) := by
  decide +kernel

theorem pin73 : (1 : Pos) * 1 * 1 ≤ 3 * (2 * 1) := by decide +kernel
theorem pin74 : (1 : Pos) * 1 * 1 ≤ 3 * (2 * 1) :=
  height_clears 1 2 3 1 1 1 2 1 (by decide +kernel) (by decide +kernel)

/-- The top's clearance is load-bearing: at the floor `1` against the
level `1` and the scales `2 ≤ 2` the clearance parts at the top and
at the conclusion together. -/
theorem pin75 : (2 : Pos) * 1 ≤ 2 * 1 := by decide +kernel
theorem pin76 : ¬ ((1 : Pos) * 2 * 1 ≤ 1 * (1 * 1)) := by decide +kernel

/-- The scales' order is load-bearing: at the scale `[10 : 1]` beyond
the top the floor's clearance at the top parts at the scale. -/
theorem pin77 : ¬ ((10 : Pos) * 1 ≤ 2 * 1) := by decide +kernel
theorem pin78 : ¬ ((1 : Pos) * 10 * 1 ≤ 3 * (2 * 1)) := by decide +kernel

theorem pin79 : BPair.unit < (⟨2, 1⟩ : BPair) := by decide +kernel
theorem pin80 : BPair.unit < (⟨2, 1⟩ : BPair) :=
  contactcell.extentRead_pos xDiv 4 xCt ⟨2, 1⟩ ⟨4, 1⟩ 1 xH xB1 xH xB2 (by decide +kernel)

end cornerfloor
