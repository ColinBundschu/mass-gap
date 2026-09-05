import MassGap.Corner
import MassGap.Cornerpivot
/-!
`lem:corner`'s cell floor at the seam: the flat step's height extent
on the corner cell, read at the corner disconjugacy certificate's
own lines, its positivity the certificate's, and the window's
transport to the chain.

The certificate's lines are corner levels.  `lem:cornerpivot`(ii)
reads the probe line at a pair rate `q = [qn : qd]` as the level
`λ` at the join `λ + c₁ + 2 = qη`, the walk's band top `c₁ + 2`
cross-added, and the band-one head at the dual pencil is the seam
pencil's own at the tower's data (`lem:dualtrunc`): `headE` is the
tower's electric read cleared at the residue's constant, the
diagonal `4(m² + rm)` deep-first (`prop:anchor`'s
`ĉ₂(mθ) = [m(m+r) : r+1]` at `con:xfusion`'s `E = 4ĉ₂`), `headM`
the walk's Jacobi matrix at the base `c`, the diagonal `c` at unit
bonds (`prop:row`), and the unit gram; the rate line's level members
are `lineX` and `lineY`, the level `⟨(r+1)qn·en·ed : (r+1)(c+2)qd·ed²⟩`
at the pencil cleared by `qd` and the residue's `r + 1`, each member
at its successor padding (the balance pair's one-member site,
`def:ground`).  `well_seam` is the tie: the well head is the seam
pencil's site at the rate line entry by entry, the diagonal
`2(r+1)qd·ed² + 4qd(m² + rm)en² − (r+1)qn·en·ed` the band read
`2 + ηW` cleared, the bonds the residue's clearing of the unit bond,
and `line_count` reads it at the count carrier: the well head's count
at a rate line is the seam pencil's count at the line's level
members (`certconstruct.countAtPair`), the reversal count one value
at the two splits.

The cell's datum is `cellRead`: the certificate's read
(`cornerpivot.certRead`) with the scale under its ceiling, the
endpoint key at the scale (`cornerpivot.endRead`), and a cut member
`μ = [a : b]` beyond one at the gap `g` with its line at or below the
stated rate.  On it the flat window is `cut_flat`: the count reads
one at the member's line at every order beyond the endpoint depth
and every split, the family the count's witness from below
(`cornerpivot.witCount`) and the certificate its cap from above
(`cornerpivot.certCount`), so the ground root is simple over the
cell, the multiplicity the count (`thm:SO`; `thm:divisorid`(iii)),
`line_count` its read at the seam pencil; `base_psd` reads the count
vacant at the vacant rate's line, every pivot clear at the diagonal
`2 + ηW` (`lem:cornerpivot`(iv) at the constant supersolution, the
diagonal clearing the bond's double at the electric member's
margin), `base_count` its read at the seam pencil; and `floor_pos`
reads the floor, the rates' gap `o = [g : b]·q₋` at a cut member
beyond one and a key beyond one, positive by its shape.

The residue direction reads at the one certificate transported
across the residues (`lem:cornerpivot`(vi)).  `cellReadT` is the
transported cell at a residue at or beyond two: the reference
certificate's read at the residue two, the tied scale `[26 : 5N²]`
under the certificate's ceiling, the endpoint key at the member's
scale and residue, and a cut member beyond one whose line sits at or
below the transported rate, the certificate's stated rate at the tied
scale; `cellReadS` is the residue-one cell, the certificate's read at
the residue two, the scale under the ceiling, the key at the residue
one, and a cut member whose line sits at or below the stated rate at
the scale itself.  On each the flat window is the count transport:
`cut_flat_T` reads the count one at the member line, the witness
family from below and the residue-two head's count at its line from
above, the residue-`r` diagonal dominating the residue-two diagonal
at the tied scale (`cornerpivot.resDiag` at the tie
`cornerpivot.tieRead`) and the reversal count monotone at a diagonal
datum on its upper side (`cornerpivot.well_dominate`), the
residue-two count at most one under the ceiling
(`cornerpivot.certCount`); `cut_flat_S` reads it at the scale itself
(`cornerpivot.oneDiag`).

The heights read two-sided on the cell at the chain:
`ground_below_line` transports a line of count one to the chain's
head at the corner's levels, the well its leading block at the fiber
datum's site tie, the compression's counts at or below the chain's
(`truncation.count_head_le`, `lem:inertia`'s compression), so the
chain's count at the member line is occupied and its ground sits at
or below the line.
-/

namespace corner
open ground elim inertia certconstruct

/-- The tower's electric read at the corner head, cleared at the
residue's constant: the diagonal `4(m² + rm)` at the depths
`n, …, 1` deep-first (`prop:anchor`'s `ĉ₂(mθ) = [m(m+r) : r+1]`
at `con:xfusion`'s diagonal `E = 4ĉ₂`). -/
def headE (r n : Nat) : Mat :=
  split.diagM ((List.range n).map (fun k =>
    BPair.ofNat (4 * ((n - k) * (n - k) + r * (n - k)))))

/-- The walk's Jacobi matrix at the base `c`, the member's `c₁`
(`prop:row`; `xfusion.c1`): the diagonal `c` at unit bonds, the
band-one head's magnetic member. -/
def headM (c n : Nat) : Mat :=
  greenprod.assemble ((List.range n).map (fun _ => [[BPair.ofNat c]]))
    ((List.range (n - 1)).map (fun _ => [[BPair.ofNat 1]]))

/-- The rate line's first level member, `(r+1)·qn·en·ed` at its
successor padding. -/
def lineX (r qn : Nat) (en ed : Pos) : Pos :=
  posOfSucc ((r + 1) * (qn * (posVal en * posVal ed)))

/-- The rate line's second level member, the band top cross-added:
`(r+1)(c+2)·qd·ed²` at its successor padding. -/
def lineY (r c qd : Nat) (ed : Pos) : Pos :=
  posOfSucc ((r + 1) * ((c + 2) * (qd * (posVal ed * posVal ed))))

/-- The seam pencil's site at the rate line: the corner pencil at
the tower's data cleared by the rate's second member, at the line's
level members over the unit gram. -/
def seamSite (r qn qd c : Nat) (en ed : Pos) (n : Nat) : Mat :=
  siteDatum
    (matAdd
      (matScale (posOfSucc (qd - 1))
        (cornerPencil (headE r n) (matScale (posOfSucc r) (headM c n))
          en ed))
      (matScale (lineY r c qd ed) (idMat n)))
    (matScale (lineX r qn en ed) (idMat n))

/-- The tower's diagonal list has the head's order. -/
private theorem headE_list_len (r n : Nat) :
    ((List.range n).map (fun k =>
      BPair.ofNat (4 * ((n - k) * (n - k) + r * (n - k))))).length = n :=
  ground.length_mapRange _ n

/-- The tower's electric read is square at the order. -/
theorem headE_sq (r n : Nat) : sqAt (headE r n) n :=
  sqAt_of ((split.diagM_len _).trans (headE_list_len r n))
    (split.diagM_shape _ n (headE_list_len r n))

/-- The walk's diagonal list has the head's order. -/
private theorem headM_diag_len (c n : Nat) :
    ((List.range n).map (fun _ => BPair.ofNat c)).length = n :=
  ground.length_mapRange _ n

/-- The walk's bond list has the head's order less one. -/
private theorem headM_off_len (n : Nat) :
    ((List.range (n - 1)).map (fun _ => BPair.ofNat 1)).length = n - 1 :=
  ground.length_mapRange _ (n - 1)

/-- The two lists' counts meet the chain's tie at an occupied
order. -/
private theorem headM_tie (c m : Nat) :
    ((List.range (m + 1 - 1)).map (fun _ => BPair.ofNat 1)).length + 1
      = ((List.range (m + 1)).map (fun _ => BPair.ofNat c)).length := by
  rw [headM_off_len (m + 1), headM_diag_len c (m + 1)]
  rfl

/-- The walk's Jacobi matrix is the scalar chain at its two lists. -/
private theorem headM_chain (c n : Nat) :
    headM c n
      = greenprod.assemble
          (((List.range n).map (fun _ => BPair.ofNat c)).map (fun x => [[x]]))
          (((List.range (n - 1)).map (fun _ => BPair.ofNat 1)).map
            (fun x => [[x]])) := by
  show greenprod.assemble
      ((List.range n).map (fun _ => [[BPair.ofNat c]]))
      ((List.range (n - 1)).map (fun _ => [[BPair.ofNat 1]])) = _
  rw [ground.map_map (fun _ : Nat => BPair.ofNat c) (fun x => [[x]])
      (List.range n),
    ground.map_map (fun _ : Nat => BPair.ofNat 1) (fun x => [[x]])
      (List.range (n - 1))]

/-- The walk's Jacobi matrix is square at the order. -/
theorem headM_sq (c : Nat) : ∀ n : Nat, sqAt (headM c n) n
  | 0 => sqAt_of rfl trivial
  | m + 1 => by
    rw [headM_chain c (m + 1)]
    have hl := (greenprod.chainLen _ _ (headM_tie c m)).1
    have hr := greenprod.chainRows _ _ (headM_tie c m)
    rw [headM_diag_len c (m + 1)] at hl hr
    exact sqAt_of hl hr

/-- The walk's entry at a key pair inside the order is the chain
chart at its two constant lists. -/
private theorem headM_entry (c m i j : Nat) (hi : i < m + 1)
    (hj : j < m + 1) :
    ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (headM c (m + 1)) i) j
      = greenprod.chainAt ((List.range (m + 1)).map (fun _ => BPair.ofNat c))
          ((List.range (m + 1 - 1)).map (fun _ => BPair.ofNat 1)) i j := by
  rw [headM_chain c (m + 1)]
  exact greenprod.chainEntry _ _ (headM_tie c m) i j
    (by rw [headM_diag_len c (m + 1)]; exact hi)
    (by rw [headM_diag_len c (m + 1)]; exact hj)

/-- The corner pencil at the tower's data is square at the order. -/
theorem headPencil_sq (r c : Nat) (en ed : Pos) (n : Nat) :
    sqAt (cornerPencil (headE r n) (matScale (posOfSucc r) (headM c n))
      en ed) n :=
  sqAt_siteDatum n _ _
    (sqAt_matScale n (en * en) _ (headE_sq r n))
    (sqAt_matScale n (ed * ed) _
      (sqAt_matScale n (posOfSucc r) _ (headM_sq c n)))

/-- The rate line's site is square at the order. -/
theorem lineSite_sq (r qn qd c : Nat) (en ed : Pos) (n : Nat) :
    sqAt (seamSite r qn qd c en ed n) n :=
  sqAt_siteDatum n _ _
    (sqAt_matAdd n _ _
      (sqAt_matScale n _ _ (headPencil_sq r c en ed n))
      (sqAt_matScale n _ _ (sqAt_idMat n)))
    (sqAt_matScale n _ _ (sqAt_idMat n))

/-- The rate line's site entry at a key pair inside the order: the
tower's electric entry at the scale's square joined to the walk's
entry at the residue's clearing and the scale's second square
swapped, the sum cleared at the rate's second member, and the unit
gram's entry at the two level members, the second swapped. -/
private theorem lineSite_entry (r qn qd c : Nat) (en ed : Pos)
    (n i j : Nat) (hi : i < n) (hj : j < n) :
    ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (seamSite r qn qd c en ed n) i) j
      = (((ground.getAt BPair.unit (ground.getAt ([] : List BPair)
            (headE r n) i) j).scale (en * en)
          + (((ground.getAt BPair.unit (ground.getAt ([] : List BPair)
              (headM c n) i) j).scale (posOfSucc r)).scale
                (ed * ed)).swap).scale (posOfSucc (qd - 1))
        + (ground.getAt BPair.unit (ground.getAt ([] : List BPair)
            (idMat n) i) j).scale (lineY r c qd ed))
      + ((ground.getAt BPair.unit (ground.getAt ([] : List BPair)
          (idMat n) i) j).scale (lineX r qn en ed)).swap := by
  have hP := headPencil_sq r c en ed n
  have hPq : sqAt (matScale (posOfSucc (qd - 1))
      (cornerPencil (headE r n) (matScale (posOfSucc r) (headM c n))
        en ed)) n := sqAt_matScale n _ _ hP
  have hY : sqAt (matScale (lineY r c qd ed) (idMat n)) n :=
    sqAt_matScale n _ _ (sqAt_idMat n)
  have hX : sqAt (matScale (lineX r qn en ed) (idMat n)) n :=
    sqAt_matScale n _ _ (sqAt_idMat n)
  have hA : sqAt (matAdd (matScale (posOfSucc (qd - 1))
      (cornerPencil (headE r n) (matScale (posOfSucc r) (headM c n))
        en ed)) (matScale (lineY r c qd ed) (idMat n))) n :=
    sqAt_matAdd n _ _ hPq hY
  have hE := headE_sq r n
  have hMr : sqAt (matScale (posOfSucc r) (headM c n)) n :=
    sqAt_matScale n _ _ (headM_sq c n)
  have hEs : sqAt (matScale (en * en) (headE r n)) n :=
    sqAt_matScale n _ _ hE
  have hMs : sqAt (matScale (ed * ed) (matScale (posOfSucc r) (headM c n)))
      n := sqAt_matScale n _ _ hMr
  show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
      (siteDatum _ _) i) j = _
  rw [siteDatum_entry _ _ n (rowsLen_of_sqAt hA) (rowsLen_of_sqAt hX) i j
      (by rw [sqAt_len hA]; exact hi) (by rw [sqAt_len hX]; exact hi) hj,
    entry_matAdd _ _ n (rowsLen_of_sqAt hPq) (rowsLen_of_sqAt hY) i j
      (by rw [sqAt_len hPq]; exact hi) (by rw [sqAt_len hY]; exact hi) hj,
    matScale_entry (posOfSucc (qd - 1))
      (cornerPencil (headE r n) (matScale (posOfSucc r) (headM c n)) en ed)
      i j (by rw [sqAt_len hP]; exact hi)
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt hP)
        (by rw [sqAt_len hP]; exact hi)]; exact hj),
    matScale_entry (lineY r c qd ed) (idMat n) i j
      (by rw [idMat_len]; exact hi)
      (by rw [rowsLen_getAt _ i (idMat_rows n) (by rw [idMat_len]; exact hi)]
          exact hj),
    matScale_entry (lineX r qn en ed) (idMat n) i j
      (by rw [idMat_len]; exact hi)
      (by rw [rowsLen_getAt _ i (idMat_rows n) (by rw [idMat_len]; exact hi)]
          exact hj)]
  show ((ground.getAt BPair.unit (ground.getAt ([] : List BPair)
      (siteDatum (matScale (en * en) (headE r n))
        (matScale (ed * ed) (matScale (posOfSucc r) (headM c n)))) i) j).scale
        (posOfSucc (qd - 1)) + _) + _ = _
  rw [siteDatum_entry _ _ n (rowsLen_of_sqAt hEs) (rowsLen_of_sqAt hMs) i j
      (by rw [sqAt_len hEs]; exact hi) (by rw [sqAt_len hMs]; exact hi) hj,
    matScale_entry (en * en) (headE r n) i j (by rw [sqAt_len hE]; exact hi)
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt hE)
        (by rw [sqAt_len hE]; exact hi)]; exact hj),
    matScale_entry (ed * ed) (matScale (posOfSucc r) (headM c n)) i j
      (by rw [sqAt_len hMr]; exact hi)
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt hMr)
        (by rw [sqAt_len hMr]; exact hi)]; exact hj),
    matScale_entry (posOfSucc r) (headM c n) i j
      (by rw [sqAt_len (headM_sq c n)]; exact hi)
      (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt (headM_sq c n))
        (by rw [sqAt_len (headM_sq c n)]; exact hi)]; exact hj)]

/-! The balance-carrier kit at the tie: a count's rescaling reads the
count's product and the seam's two natural identities collect the
diagonal's and the bond's count forms. -/

/-- A count's rescaling reads the count's product with the scale's
value. -/
private theorem nfScale : ∀ (a : Nat) (w : Pos),
    ((BPair.ofNat a).scale w).oneValue (BPair.ofNat (a * posVal w))
  | 0, w => by
    rw [Nat.zero_mul]
    exact BPair.unit_scale w
  | k + 1, w => by
    show ((BPair.ofPos (posOfSucc k)).scale w).oneValue _
    refine BPair.oneValue_trans (BPair.scale_ofPos (posOfSucc k) w) ?_
    rw [BPair.ofPos_val, ground.val_mul]
    exact BPair.oneValue_refl _

/-- The seam's summands regroup: the electric term with the cleared
band read joined to the walk's term, against the band read leading
and the rate's member joined last. -/
private theorem sumArr (A Cc T Q : Nat) :
    A + (Cc + T + 1) + Q = T + A + (Cc + (Q + 1)) := by
  rw [Nat.add_comm T A, Nat.add_assoc A T (Cc + (Q + 1)),
    Nat.add_assoc A (Cc + T + 1) Q]
  refine congrArg (fun z => A + z) ?_
  rw [Nat.add_assoc (Cc + T) 1 Q, Nat.add_comm 1 Q, Nat.add_comm Cc T,
    Nat.add_assoc T Cc (Q + 1)]

/-- The seam's diagonal identity at the naturals: the tower's
electric term with the band top's cross-added member and the rate's
member against the band read's clearing, the electric term again,
the walk's diagonal at the residue's clearing and the rate's member,
one natural identity at the cleared data. -/
private theorem seamNat (r qn qd c M en ed : Nat) :
    4 * (M * M + r * M) * (en * en * qd)
        + ((r + 1) * ((c + 2) * (qd * (ed * ed))) + 1)
      + (r + 1) * qn * en * ed
    = 2 * ((r + 1) * qd * ed * ed) + 4 * qd * (M * M + r * M) * en * en
      + (c * ((r + 1) * (ed * ed * qd))
        + ((r + 1) * (qn * (en * ed)) + 1)) := by
  have e1 : 4 * (M * M + r * M) * (en * en * qd)
      = 4 * qd * (M * M + r * M) * en * en :=
    ground.monEq [M * M + r * M, en, qd]
      (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0))
        (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.var 2)))
      (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 2))
        (Mon.var 0)) (Mon.var 1)) (Mon.var 1))
      (by decide +kernel) (by decide +kernel)
  have e2 : (r + 1) * (c * (qd * (ed * ed)))
      = c * ((r + 1) * (ed * ed * qd)) :=
    ground.monEq [r + 1, c, qd, ed]
      (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1)
        (Mon.mul (Mon.var 2) (Mon.mul (Mon.var 3) (Mon.var 3)))))
      (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 0)
        (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 3)) (Mon.var 2))))
      (by decide +kernel) (by decide +kernel)
  have e3 : (r + 1) * (2 * (qd * (ed * ed)))
      = 2 * ((r + 1) * qd * ed * ed) :=
    ground.monEq [r + 1, qd, ed]
      (Mon.mul (Mon.var 0) (Mon.mul (Mon.cst 2)
        (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 2) (Mon.var 2)))))
      (Mon.mul (Mon.cst 2) (Mon.mul (Mon.mul (Mon.mul (Mon.var 0)
        (Mon.var 1)) (Mon.var 2)) (Mon.var 2)))
      (by decide +kernel) (by decide +kernel)
  have e4 : (r + 1) * qn * en * ed = (r + 1) * (qn * (en * ed)) :=
    ground.monEq [r + 1, qn, en, ed]
      (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
        (Mon.var 3))
      (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1)
        (Mon.mul (Mon.var 2) (Mon.var 3))))
      (by decide +kernel) (by decide +kernel)
  rw [ground.mulAddR c 2 (qd * (ed * ed)),
    Nat.left_distrib (r + 1) (c * (qd * (ed * ed))) (2 * (qd * (ed * ed))),
    e1, e2, e3, e4]
  exact sumArr _ _ _ _

/-- The seam's bond identity at the naturals. -/
private theorem bondNat (r qd ed : Nat) :
    (r + 1) * qd * ed * ed = 1 * ((r + 1) * (ed * ed * qd)) :=
  ground.monEq [r + 1, qd, ed]
    (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
      (Mon.var 2))
    (Mon.mul (Mon.cst 1) (Mon.mul (Mon.var 0)
      (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 1))))
    (by decide +kernel) (by decide +kernel)

/-- A rescaling by the rate's padded second member reads the rate's
own value. -/
private theorem val_rate {qd : Nat} (hqd : 1 ≤ qd) :
    posVal (posOfSucc (qd - 1)) = qd := by
  show qd - 1 + 1 = qd
  exact ground.subAdd hqd

/-- The residue's padded successor reads the residue's successor. -/
private theorem val_succ (r : Nat) : posVal (posOfSucc r) = r + 1 := rfl

/-- The rate line's site entry at the diagonal reads the four-term
count form at the tower's depth. -/
private theorem siteDiag_nf (r qn qd c M : Nat) (hqd : 1 ≤ qd)
    (en ed : Pos) :
    ((((BPair.ofNat (4 * (M * M + r * M))).scale (en * en)
        + (((BPair.ofNat c).scale (posOfSucc r)).scale (ed * ed)).swap).scale
          (posOfSucc (qd - 1))
      + (BPair.ofNat 1).scale (lineY r c qd ed))
      + ((BPair.ofNat 1).scale (lineX r qn en ed)).swap).oneValue
      (BPair.ofNat (4 * (M * M + r * M) * (posVal en * posVal en * qd)
          + ((r + 1) * ((c + 2) * (qd * (posVal ed * posVal ed))) + 1))
        + (BPair.ofNat (c * ((r + 1) * (posVal ed * posVal ed * qd))
          + ((r + 1) * (qn * (posVal en * posVal ed)) + 1))).swap) := by
  have u1 : (((BPair.ofNat (4 * (M * M + r * M))).scale (en * en)).scale
        (posOfSucc (qd - 1))).oneValue
      (BPair.ofNat (4 * (M * M + r * M) * (posVal en * posVal en * qd))) := by
    rw [BPair.scale_scale]
    refine BPair.oneValue_trans (nfScale _ _) ?_
    rw [ground.val_mul, ground.val_mul, val_rate hqd]
    exact BPair.oneValue_refl _
  have u2 : (((((BPair.ofNat c).scale (posOfSucc r)).scale
        (ed * ed)).swap).scale (posOfSucc (qd - 1))).oneValue
      (BPair.ofNat (c * ((r + 1) * (posVal ed * posVal ed * qd)))).swap := by
    rw [BPair.scale_swap, BPair.scale_scale, BPair.scale_scale]
    refine ground.swap_congr ?_
    refine BPair.oneValue_trans (nfScale _ _) ?_
    rw [ground.val_mul, ground.val_mul, ground.val_mul, val_rate hqd,
      val_succ]
    exact BPair.oneValue_refl _
  have u3 : ((BPair.ofNat 1).scale (lineY r c qd ed)).oneValue
      (BPair.ofNat ((r + 1) * ((c + 2) * (qd * (posVal ed * posVal ed)))
        + 1)) := by
    refine BPair.oneValue_trans (nfScale 1 _) ?_
    rw [Nat.one_mul]
    exact BPair.oneValue_refl _
  have u4 : (((BPair.ofNat 1).scale (lineX r qn en ed)).swap).oneValue
      (BPair.ofNat ((r + 1) * (qn * (posVal en * posVal ed)) + 1)).swap := by
    refine ground.swap_congr ?_
    refine BPair.oneValue_trans (nfScale 1 _) ?_
    rw [Nat.one_mul]
    exact BPair.oneValue_refl _
  rw [BPair.scale_add]
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.add_congr (BPair.add_congr u1 u2) u3) u4) ?_
  rw [BPair.add_assoc (BPair.ofNat _ + (BPair.ofNat _).swap),
    BPair.add_add_comm]
  refine BPair.add_congr (BPair.oneValue_symm (BPair.ofNat_add _ _)) ?_
  rw [BPair.swap_add]
  exact ground.swap_congr (BPair.oneValue_symm (BPair.ofNat_add _ _))

/-- A unit's rescaling swapped reads the unit. -/
private theorem unitScaleSwap (w : Pos) :
    ((BPair.unit.scale w).swap).oneValue BPair.unit :=
  ground.swap_congr (BPair.unit_scale w)

/-- The rate line's site entry at a bond reads the bond's swapped
count form. -/
private theorem siteBond_nf (r qn qd c : Nat) (hqd : 1 ≤ qd) (en ed : Pos) :
    (((BPair.unit.scale (en * en)
        + (((BPair.ofNat 1).scale (posOfSucc r)).scale (ed * ed)).swap).scale
          (posOfSucc (qd - 1))
      + BPair.unit.scale (lineY r c qd ed))
      + (BPair.unit.scale (lineX r qn en ed)).swap).oneValue
      (BPair.ofNat (1 * ((r + 1) * (posVal ed * posVal ed * qd)))).swap := by
  have u1 : ((BPair.unit.scale (en * en)).scale (posOfSucc (qd - 1))).oneValue
      BPair.unit := by
    rw [BPair.scale_scale]
    exact BPair.unit_scale _
  have u2 : (((((BPair.ofNat 1).scale (posOfSucc r)).scale
        (ed * ed)).swap).scale (posOfSucc (qd - 1))).oneValue
      (BPair.ofNat (1 * ((r + 1) * (posVal ed * posVal ed * qd)))).swap := by
    rw [BPair.scale_swap, BPair.scale_scale, BPair.scale_scale]
    refine ground.swap_congr ?_
    refine BPair.oneValue_trans (nfScale _ _) ?_
    rw [ground.val_mul, ground.val_mul, ground.val_mul, val_rate hqd,
      val_succ]
    exact BPair.oneValue_refl _
  rw [BPair.scale_add]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (BPair.add_congr u1 u2)
        (BPair.unit_scale _))
      (unitScaleSwap _)) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact BPair.unit_add _

/-- The rate line's site entry beyond the band reads the unit. -/
private theorem siteFar_nf (r qn qd c : Nat) (en ed : Pos) :
    (((BPair.unit.scale (en * en)
        + ((BPair.unit.scale (posOfSucc r)).scale (ed * ed)).swap).scale
          (posOfSucc (qd - 1))
      + BPair.unit.scale (lineY r c qd ed))
      + (BPair.unit.scale (lineX r qn en ed)).swap).oneValue BPair.unit := by
  have v1 : ((BPair.unit.scale (en * en)).scale (posOfSucc (qd - 1))).oneValue
      BPair.unit := by
    rw [BPair.scale_scale]
    exact BPair.unit_scale _
  have v2 : ((((BPair.unit.scale (posOfSucc r)).scale (ed * ed)).swap).scale
        (posOfSucc (qd - 1))).oneValue BPair.unit := by
    rw [BPair.scale_swap, BPair.scale_scale, BPair.scale_scale]
    exact unitScaleSwap _
  rw [BPair.scale_add]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (BPair.add_congr v1 v2) (BPair.unit_scale _))
      (unitScaleSwap _)) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact BPair.add_unit _

/-- The tower's electric entry at a key pair inside the order: the
depth's cleared read on the diagonal, the unit off it. -/
private theorem headE_entry (r n i j : Nat) (hi : i < n) (hj : j < n) :
    ground.getAt BPair.unit (ground.getAt ([] : List BPair) (headE r n) i) j
      = if j = i then BPair.ofNat (4 * ((n - i) * (n - i) + r * (n - i)))
        else BPair.unit := by
  show ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) (split.diagM _) i) j = _
  rw [split.diagM_entry _ i j (by rw [headE_list_len]; exact hi)
      (by rw [headE_list_len]; exact hj),
    ground.getAt_map_range BPair.unit _ n i, if_pos hi]

/-- The well head is the seam pencil's site at the rate line: the
band-one head at the dual pencil reads the corner pencil at the
tower's data, the level members the line's own at the band top's
join (`lem:cornerpivot`(ii); `lem:dualtrunc`), entry by entry: the
diagonal the band read `2 + ηW` cleared, the bonds the residue's
clearing of the unit bond, the far entries the unit. -/
theorem well_seam (r qn qd c : Nat) (hqd : 1 ≤ qd) (en ed : Pos) :
    ∀ n : Nat, matOneValue (cornerpivot.wellMat r qn qd en ed n)
      (seamSite r qn qd c en ed n)
  | 0 =>
    matOne_of_entries _ _ 0 rfl trivial
      (sqAt_len (lineSite_sq r qn qd c en ed 0))
      (rowsLen_of_sqAt (lineSite_sq r qn qd c en ed 0))
      (fun i _ hi _ => absurd hi (Nat.not_lt_zero i))
  | m + 1 => by
    have hS := lineSite_sq r qn qd c en ed (m + 1)
    refine matOne_of_entries _ _ (m + 1) (cornerpivot.wellLen r qn qd en ed m)
      (cornerpivot.wellRows r qn qd en ed m) (sqAt_len hS)
      (rowsLen_of_sqAt hS) ?_
    intro i j hi hj
    rw [cornerpivot.wellEntry r qn qd en ed m i j hi hj,
      lineSite_entry r qn qd c en ed (m + 1) i j hi hj,
      headE_entry r (m + 1) i j hi hj, headM_entry c m i j hi hj,
      getAt_idMat (m + 1) i j hi hj]
    match Nat.decEq j i with
    | isTrue hji =>
      rw [if_pos hji, if_pos hji, hji, greenprod.chainAt_diag,
        greenprod.chainAt_diag,
        cornerpivot.wDiagE_at r qn qd en ed (m + 1) i hi,
        ground.getAt_map_range BPair.unit _ (m + 1) i, if_pos hi]
      refine BPair.oneValue_trans
        (cornerpivot.wellDiag_count r qn qd (m + 1 - i) en ed) ?_
      refine BPair.oneValue_trans ?_
        (BPair.oneValue_symm (siteDiag_nf r qn qd c (m + 1 - i) hqd en ed))
      exact BPair.ofCounts_crossed
        (seamNat r qn qd c (m + 1 - i) (posVal en) (posVal ed)).symm
    | isFalse hji =>
      rw [if_neg hji, if_neg hji]
      match Nat.decEq (j + 1) i with
      | isTrue hlo =>
        have hjm : j < m + 1 - 1 := by
          show j < m
          exact Nat.lt_of_succ_lt_succ
            (by show j + 1 < m + 1; rw [hlo]; exact hi)
        rw [greenprod.chainAt_low _ _ i j hji hlo,
          greenprod.chainAt_low _ _ i j hji hlo,
          cornerpivot.wOffE_at r qd ed (m + 1) j hjm,
          ground.getAt_map_range BPair.unit _ (m + 1 - 1) j, if_pos hjm]
        refine BPair.oneValue_trans ?_
          (BPair.oneValue_symm (siteBond_nf r qn qd c hqd en ed))
        refine ground.swap_congr ?_
        refine BPair.oneValue_trans (cornerpivot.wellBond_count r qd ed) ?_
        rw [bondNat r qd (posVal ed)]
        exact BPair.oneValue_refl _
      | isFalse hlo =>
        match Nat.decEq (i + 1) j with
        | isTrue hup =>
          have him : i < m + 1 - 1 := by
            show i < m
            exact Nat.lt_of_succ_lt_succ
              (by show i + 1 < m + 1; rw [hup]; exact hj)
          rw [greenprod.chainAt_up _ _ i j hji hlo hup,
            greenprod.chainAt_up _ _ i j hji hlo hup,
            cornerpivot.wOffE_at r qd ed (m + 1) i him,
            ground.getAt_map_range BPair.unit _ (m + 1 - 1) i, if_pos him]
          refine BPair.oneValue_trans ?_
            (BPair.oneValue_symm (siteBond_nf r qn qd c hqd en ed))
          refine ground.swap_congr ?_
          refine BPair.oneValue_trans (cornerpivot.wellBond_count r qd ed) ?_
          rw [bondNat r qd (posVal ed)]
          exact BPair.oneValue_refl _
        | isFalse hup =>
          rw [greenprod.chainAt_far _ _ i j hji hlo hup,
            greenprod.chainAt_far _ _ i j hji hlo hup]
          exact BPair.oneValue_symm (siteFar_nf r qn qd c en ed)

/-- The well head's count at a rate line is the seam pencil's count
at the line's level members: a split of the well head and a split of
the line's site read one reversal count (`lem:inertia`'s two-splits
exchange at the seam tie), the count carried onto
`certconstruct.countAtPair` at the tower's data. -/
theorem line_count (r qn qd c : Nat) (hqd : 1 ≤ qd) (en ed : Pos)
    (n k : Nat) (sp sp' : Split n)
    (hsp : splitRead (cornerpivot.wellMat r qn qd en ed n) sp)
    (hk : revAt sp = k)
    (hsp' : splitRead (seamSite r qn qd c en ed n) sp') :
    countAtPair
      (matScale (posOfSucc (qd - 1))
        (cornerPencil (headE r n) (matScale (posOfSucc r) (headM c n)) en ed))
      (idMat n) (lineX r qn en ed) (lineY r c qd ed) k sp' :=
  ⟨sqAt_matScale n _ _ (headPencil_sq r c en ed n), sqAt_idMat n, hsp',
   (rev_exchange (seamSite r qn qd c en ed n) sp' sp hsp'
     (splitRead_congr _ _ (lineSite_sq r qn qd c en ed n)
       (well_seam r qn qd c hqd en ed n) sp hsp)).trans hk⟩

/-! The cell's datum and its flat window: the certificate's read at
the scale under its ceiling, the endpoint key, and a cut member's
line at or below the stated rate; on it the count reads one at the
member's line, vacant at the vacant rate's line, and the floor is the
rates' gap, positive by its shape. -/

/-- The cell's datum at a scale: the corner disconjugacy
certificate's read, the scale under the certificate's ceiling, the
endpoint key at the scale (`lem:cornerpivot`(v)), and a cut member
`[a : b]` beyond one at the gap `g` whose line sits at or below the
stated rate (`lem:cornerpivot`(vi)), the member's second datum
occupied at the rate's read. -/
def cellRead (r : Nat) (C : cornerpivot.DisconjCert) (en ed : Pos)
    (N a b g : Nat) : Prop :=
  cornerpivot.certRead r C
  ∧ BPair.ofPos en * BPair.ofPos C.e0d ≤ C.e0n * BPair.ofPos ed
  ∧ cornerpivot.endRead (posVal en) (posVal ed) r N
  ∧ b + g = a ∧ 1 ≤ g
  ∧ a * cornerpivot.qLowNum (posVal en) (posVal ed) r N * C.qcD
      ≤ C.qcN * (b * cornerpivot.qLowDen (posVal en) (posVal ed) r N)

instance (r : Nat) (C : cornerpivot.DisconjCert) (en ed : Pos)
    (N a b g : Nat) : Decidable (cellRead r C en ed N a b g) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The floor's first member, the rates' gap `[g : b]·q₋`
cross-multiplied. -/
def floorN (en ed : Pos) (r N g : Nat) : Nat :=
  g * cornerpivot.qLowNum (posVal en) (posVal ed) r N

/-- The floor's second member. -/
def floorD (en ed : Pos) (r N b : Nat) : Nat :=
  b * cornerpivot.qLowDen (posVal en) (posVal ed) r N

/-- A cut member's line second member is occupied: the member's
first datum is occupied at the gap and the lower rate's first datum
at the key, so a rate's read caps an occupied product and its right
side's second factor is occupied with it. -/
private theorem den_pos (en ed : Pos) (r N a b g X Y Z : Nat) (hab : b + g = a)
    (hg : 1 ≤ g) (hN : 2 ≤ N) (hX : 0 < X)
    (h : a * cornerpivot.qLowNum (posVal en) (posVal ed) r N * X
      ≤ Y * (b * cornerpivot.qLowDen (posVal en) (posVal ed) r N * Z)) :
    1 ≤ b * cornerpivot.qLowDen (posVal en) (posVal ed) r N :=
  have hq := cornerpivot.qLowPos (posVal en) (posVal ed) r N (posVal_pos en)
    (posVal_pos ed) hN
  have ha : 1 ≤ a := hab ▸ Nat.le_trans hg (Nat.le_add_left g b)
  (ground.mulPosSplit (ground.mulPosSplit (Nat.lt_of_lt_of_le
    (Nat.mul_pos (Nat.mul_pos ha hq.1) hX) h)).2).1

/-- The flat window at the member's line: at every order beyond the
endpoint depth and every split the count reads one, the witness
family from below (`cornerpivot.witCount`) and the certificate from
above (`cornerpivot.certCount`), so the ground root is simple over
the cell, its multiplicity the count (`thm:SO`;
`thm:divisorid`(iii)), and the counting function flat from the lower
line to the member's (`lem:cornerpivot`(vi)). -/
theorem cut_flat {r : Nat} {C : cornerpivot.DisconjCert} {en ed : Pos}
    {N a b g : Nat} (h : cellRead r C en ed N a b g)
    (n : Nat) (hNn : N ≤ n) (sp : Split n)
    (hsp : splitRead (cornerpivot.wellMat r
      (a * cornerpivot.qLowNum (posVal en) (posVal ed) r N)
      (b * cornerpivot.qLowDen (posVal en) (posVal ed) r N) en ed n) sp) :
    revAt sp = 1 :=
  Nat.le_antisymm
    (cornerpivot.certCount r C _ _ n en ed h.1 h.2.1 h.2.2.2.2.2
      (den_pos en ed r N a b g C.qcD C.qcN 1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.1.1 h.1.1
        (by rw [Nat.mul_one]; exact h.2.2.2.2.2)) sp hsp)
    (cornerpivot.witCount en ed r N n a b g h.2.2.1.1 hNn h.2.2.2.1
      h.2.2.2.2.1 sp hsp)

/-- The transported cell at a residue at or beyond two
(`lem:cornerpivot`(vi)): the reference certificate's read at the
residue two, the tied scale `[26 : 5N²]` under the certificate's
ceiling, the endpoint key at the member's scale and residue, and a
cut member `[a : b]` beyond one at the gap `g` whose line sits at or
below the transported rate `[cn·26 : cd·5N²η]`, the certificate's
stated rate at the tied scale. -/
def cellReadT (r : Nat) (C : cornerpivot.DisconjCert) (en ed : Pos)
    (N a b g : Nat) : Prop :=
  2 ≤ r
  ∧ cornerpivot.certRead 2 C
  ∧ BPair.ofPos 26 * BPair.ofPos C.e0d
      ≤ C.e0n * BPair.ofPos (cornerpivot.tieScaleD N)
  ∧ cornerpivot.endRead (posVal en) (posVal ed) r N
  ∧ b + g = a ∧ 1 ≤ g
  ∧ a * cornerpivot.qLowNum (posVal en) (posVal ed) r N * posVal en
        * (C.qcD * (5 * N * N))
      ≤ C.qcN * 26
        * (b * cornerpivot.qLowDen (posVal en) (posVal ed) r N * posVal ed)

instance (r : Nat) (C : cornerpivot.DisconjCert) (en ed : Pos)
    (N a b g : Nat) : Decidable (cellReadT r C en ed N a b g) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The transported cell at the residue one (`lem:cornerpivot`(vi)):
the reference certificate's read at the residue two, the scale under
the certificate's ceiling, the endpoint key at the scale and the
residue one, and a cut member `[a : b]` beyond one at the gap `g`
whose line sits at or below the certificate's stated rate at the
scale itself. -/
def cellReadS (C : cornerpivot.DisconjCert) (en ed : Pos) (N a b g : Nat) :
    Prop :=
  cornerpivot.certRead 2 C
  ∧ BPair.ofPos en * BPair.ofPos C.e0d ≤ C.e0n * BPair.ofPos ed
  ∧ cornerpivot.endRead (posVal en) (posVal ed) 1 N
  ∧ b + g = a ∧ 1 ≤ g
  ∧ a * cornerpivot.qLowNum (posVal en) (posVal ed) 1 N * C.qcD
      ≤ C.qcN * (b * cornerpivot.qLowDen (posVal en) (posVal ed) 1 N)

instance (C : cornerpivot.DisconjCert) (en ed : Pos) (N a b g : Nat) :
    Decidable (cellReadS C en ed N a b g) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

private theorem rateT_l (a Q E N cd : Nat) :
    a * Q * E * (5 * N * N) * cd
      = a * Q * E * (cd * (5 * N * N)) :=
  ground.monEq [a, Q, E, N, cd]
    (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 3)) (Mon.var 3))) (Mon.var 4))
    (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.mul (Mon.var 4) (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 3)) (Mon.var 3))))
    (by decide +kernel) (by decide +kernel)
private theorem rateT_r (cn b Qd D : Nat) :
    cn * (b * Qd) * D * 26
      = cn * 26 * (b * Qd * D) :=
  ground.monEq [cn, b, Qd, D]
    (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1) (Mon.var 2))) (Mon.var 3)) (Mon.cst 26))
    (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 26)) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3)))
    (by decide +kernel) (by decide +kernel)

/-- The flat window at the transported cell's member line: at every
order beyond the endpoint depth and every split the count reads one,
the witness family from below (`cornerpivot.witCount`) and the
residue-two certificate from above through the count transport —
the residue-`r` diagonal dominating the residue-two diagonal at the
tied scale (`cornerpivot.resDiag` at the tie `cornerpivot.tieRead`),
the residue-two head's count at its line at most one under the
certificate's ceiling (`cornerpivot.certCount`), and the reversal
count monotone at a diagonal datum on its upper side
(`cornerpivot.well_dominate`; `lem:cornerpivot`(vi)). -/
theorem cut_flat_T {r : Nat} {C : cornerpivot.DisconjCert} {en ed : Pos}
    {N a b g : Nat} (h : cellReadT r C en ed N a b g)
    (n : Nat) (hNn : N ≤ n) (sp : Split n)
    (hsp : splitRead (cornerpivot.wellMat r
      (a * cornerpivot.qLowNum (posVal en) (posVal ed) r N)
      (b * cornerpivot.qLowDen (posVal en) (posVal ed) r N) en ed n) sp) :
    revAt sp = 1 := by
  obtain ⟨hr, hC, hceil, hend, hab, hg, hrate⟩ := h
  have hN2 : 2 ≤ N := hend.1
  have hN1 : 1 ≤ N := Nat.le_trans (by decide) hN2
  refine Nat.le_antisymm ?_ (cornerpivot.witCount en ed r N n a b g hN2 hNn hab hg sp hsp)
  cases n with
  | zero => rw [revAt_zero sp]; exact Nat.zero_le 1
  | succ m =>
  have hsp₂ := mkSplit_read (m + 1) _
    (sqAt_of (cornerpivot.wellLen 2 C.qcN C.qcD 26 (cornerpivot.tieScaleD N) m)
      (cornerpivot.wellRows 2 C.qcN C.qcD 26 (cornerpivot.tieScaleD N) m))
    (cornerpivot.wellMat_sym 2 C.qcN C.qcD 26 (cornerpivot.tieScaleD N) (m + 1))
  refine Nat.le_trans (cornerpivot.well_dominate r _ _ 2 C.qcN C.qcD
    (den_pos en ed r N a b g (posVal en * (C.qcD * (5 * N * N))) (C.qcN * 26) (posVal ed)
      hab hg hN2
      (Nat.mul_pos (posVal_pos en) (Nat.mul_pos hC.1 (Nat.mul_pos
        (Nat.mul_pos (by decide : 0 < 5) (Nat.lt_of_lt_of_le (by decide : 0 < 2) hN2))
        (Nat.lt_of_lt_of_le (by decide : 0 < 2) hN2))))
      (by
        rw [← ground.mulAssoc (a * cornerpivot.qLowNum (posVal en) (posVal ed) r N)
          (posVal en) (C.qcD * (5 * N * N))]
        exact hrate)) hC.1 en ed 26
    (cornerpivot.tieScaleD N)
    (m + 1) ?_ sp _ hsp hsp₂)
    (cornerpivot.certCount 2 C C.qcN C.qcD (m + 1) 26 (cornerpivot.tieScaleD N) hC
      hceil (Nat.le_refl _) hC.1 _ hsp₂)
  intro k _ _
  have htie : (r + 1) * (posVal 26 * posVal 26) * (posVal ed * posVal ed)
      ≤ 3 * (posVal (cornerpivot.tieScaleD N) * posVal (cornerpivot.tieScaleD N))
        * (posVal en * posVal en) := by
    rw [cornerpivot.tieScaleD_val N hN1]
    exact cornerpivot.tieRead (posVal en) (posVal ed) r N hend.2.1
  have hrate' : a * cornerpivot.qLowNum (posVal en) (posVal ed) r N * posVal en
        * posVal (cornerpivot.tieScaleD N) * C.qcD
      ≤ C.qcN * (b * cornerpivot.qLowDen (posVal en) (posVal ed) r N) * posVal ed
        * posVal 26 := by
    rw [cornerpivot.tieScaleD_val N hN1]
    show a * cornerpivot.qLowNum (posVal en) (posVal ed) r N * posVal en
        * (5 * N * N) * C.qcD
      ≤ C.qcN * (b * cornerpivot.qLowDen (posVal en) (posVal ed) r N) * posVal ed
        * 26
    rw [rateT_l, rateT_r]
    exact hrate
  exact cornerpivot.resDiag r _ _ C.qcN C.qcD hr en ed 26 (cornerpivot.tieScaleD N)
    htie hrate' k

/-- The flat window at the residue-one cell's member line: the count
reads one at every order beyond the endpoint depth and every split,
the witness family from below and the residue-two certificate from
above at the scale itself, the residue-one diagonal dominating the
residue-two diagonal at the stated rate (`cornerpivot.oneDiag`;
`cornerpivot.well_dominate`; `lem:cornerpivot`(vi)). -/
theorem cut_flat_S {C : cornerpivot.DisconjCert} {en ed : Pos}
    {N a b g : Nat} (h : cellReadS C en ed N a b g)
    (n : Nat) (hNn : N ≤ n) (sp : Split n)
    (hsp : splitRead (cornerpivot.wellMat 1
      (a * cornerpivot.qLowNum (posVal en) (posVal ed) 1 N)
      (b * cornerpivot.qLowDen (posVal en) (posVal ed) 1 N) en ed n) sp) :
    revAt sp = 1 := by
  obtain ⟨hC, hceil, hend, hab, hg, hrate⟩ := h
  have hN2 : 2 ≤ N := hend.1
  refine Nat.le_antisymm ?_ (cornerpivot.witCount en ed 1 N n a b g hN2 hNn hab hg sp hsp)
  cases n with
  | zero => rw [revAt_zero sp]; exact Nat.zero_le 1
  | succ m =>
  have hsp₂ := mkSplit_read (m + 1) _
    (sqAt_of (cornerpivot.wellLen 2 C.qcN C.qcD en ed m)
      (cornerpivot.wellRows 2 C.qcN C.qcD en ed m))
    (cornerpivot.wellMat_sym 2 C.qcN C.qcD en ed (m + 1))
  refine Nat.le_trans (cornerpivot.well_dominate 1 _ _ 2 C.qcN C.qcD
    (den_pos en ed 1 N a b g C.qcD C.qcN 1 hab hg hN2 hC.1 (by rw [Nat.mul_one]; exact hrate))
    hC.1 en ed en ed (m + 1) ?_ sp _ hsp hsp₂)
    (cornerpivot.certCount 2 C C.qcN C.qcD (m + 1) en ed hC hceil (Nat.le_refl _)
      hC.1 _ hsp₂)
  intro k _ _
  exact cornerpivot.oneDiag _ _ C.qcN C.qcD en ed hrate k

/-- The floor is positive by its shape: both members of the rates'
gap `[g : b]·q₋` are occupied at the cut member's own data and the
endpoint key (`lem:cornerpivot`(v),(vi)), the member beyond one at
the gap and the key beyond one. -/
theorem floor_pos (en ed : Pos) (r N g b : Nat) (hN : 2 ≤ N) (hg : 1 ≤ g)
    (hb : 1 ≤ b) :
    0 < floorN en ed r N g ∧ 0 < floorD en ed r N b :=
  have hq := cornerpivot.qLowPos (posVal en) (posVal ed) r N (posVal_pos en)
    (posVal_pos ed) hN
  ⟨Nat.mul_pos hg hq.1, Nat.mul_pos hb hq.2⟩

/-! The vacant rate's line: the diagonal `2 + ηW` at the vacant rate
clears the bond's double by the electric member's margin, so the
constant list is the supersolution and every pivot stays clear to
the head's end (`lem:cornerpivot`(iv)), the count vacant. -/

/-- The well's diagonal at the vacant rate sits at or beyond the
bond's double. -/
private theorem diag_vac (r qd M : Nat) (en ed : Pos) :
    cornerpivot.wellBond r qd ed * BPair.ofNat 2
      ≤ cornerpivot.wellDiag r 0 qd en ed M := by
  refine ground.leB_congr_right
    (BPair.oneValue_symm (cornerpivot.wellDiag_read r 0 qd M en ed)) ?_
  have hT3 : ((BPair.ofNat ((r + 1) * 0) * BPair.ofPos en
      * BPair.ofPos ed).swap).oneValue BPair.unit := by
    rw [Nat.mul_zero]
    show ((BPair.ofNat 0 * BPair.ofPos en * BPair.ofPos ed).swap).oneValue
      BPair.unit.swap
    refine ground.swap_congr ?_
    exact BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.oneValue_refl _)) (BPair.unit_mul _)))
      (BPair.unit_mul _)
  have hT2 : BPair.unit ≤ BPair.ofNat (4 * qd * (M * M + r * M))
      * BPair.ofPos en * BPair.ofPos en :=
    ground.unitLeMul (ground.unitLeMul (ground.unitLeOfNat _)
      (ground.leB_of_lt (ground.unitLtOfPos en)))
      (ground.leB_of_lt (ground.unitLtOfPos en))
  refine ground.leB_congr_left
    (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofNat 2) _)) ?_
  refine ground.leB_congr_left (BPair.add_unit _)
    (ground.leB_add (ground.leB_refl _) ?_)
  exact ground.unitLeAdd hT2
    (ground.leB_congr_right (BPair.oneValue_symm hT3) (ground.leB_refl _))

/-- The vacant rate's line counts vacant: at the vacant rate the
well's diagonal clears the bond's double at every depth, so the
constant list is the supersolution and every pivot of the walk stays
clear to the head's end (`lem:cornerpivot`(iv)'s dominance tail at
the constant list), the reversal count vacant at every split. -/
theorem base_psd (r qd : Nat) (hqd : 1 ≤ qd) (en ed : Pos) (n : Nat)
    (sp : Split n)
    (hsp : splitRead (cornerpivot.wellMat r 0 qd en ed n) sp) :
    revAt sp = 0 := by
  refine cornerpivot.certRevZero r 0 qd en ed n ?_ sp hsp
  have hβ : BPair.unit < cornerpivot.wellBond r qd ed :=
    ground.unitLtMul (ground.unitLtMul
      (ground.unitLtNat (Nat.mul_pos (Nat.succ_pos r) hqd))
      (ground.unitLtOfPos ed)) (ground.unitLtOfPos ed)
  have hall := cornerpivot.tail_clear
    (fun m => cornerpivot.wellDiag r 0 qd en ed (m + 1))
    (cornerpivot.wellWalk r 0 qd en ed) (cornerpivot.wellBond r qd ed) n hβ
    (fun k _ => cornerpivot.walk_rec (cornerpivot.wellBond r qd ed)
      (fun m => cornerpivot.wellDiag r 0 qd en ed (m + 1)) k)
    (fun k _ => diag_vac r qd (k + 2) en ed)
    (ground.unitLtOfPos (posOfSucc 0))
    (ground.leB_trans
      (ground.leB_mulR (ground.leB_of_lt hβ)
        (by decide +kernel : BPair.ofNat 1 ≤ BPair.ofNat 2))
      (diag_vac r qd 1 en ed))
  exact fun k hk => hall k (Nat.le_of_lt hk)

/-- The vacant count at the seam pencil: the corner pencil's count
at the vacant rate's line reads vacant at every order and split. -/
theorem base_count (r qd c : Nat) (hqd : 1 ≤ qd) (en ed : Pos) (n : Nat)
    (sp sp' : Split n)
    (hsp : splitRead (cornerpivot.wellMat r 0 qd en ed n) sp)
    (hsp' : splitRead (seamSite r 0 qd c en ed n) sp') :
    countAtPair
      (matScale (posOfSucc (qd - 1))
        (cornerPencil (headE r n) (matScale (posOfSucc r) (headM c n)) en ed))
      (idMat n) (lineX r 0 en ed) (lineY r c qd ed) 0 sp' :=
  line_count r 0 qd c hqd en ed n 0 sp sp' hsp
    (base_psd r qd hqd en ed n sp hsp) hsp'

/-! The chain's read at the member line: the compression's counts sit
at or below the chain's (`lem:inertia`), so at the well's site tied
as the chain's leading block the chain's count at the member line is
occupied, its ground at or below the line; the bordered pencil's
counts sit at or above (`contactcell.count_bord_le`), the chain's
second root at or beyond every level the bordered pencil counts at
most one, the two root bounds exchanging. -/

/-- The chain's count at the member line is occupied: the seam
pencil's count one at a line of count one (`line_count`, the count
one the cell floor's stated datum at the member line, `lem:corner`)
carried to the chain whose site the seam's leading block ties
(`truncation.count_head_le`). -/
theorem ground_below_line (r qn qd c : Nat) (hqd : 1 ≤ qd) (en ed : Pos)
    (n : Nat) {m : Nat} (H G Q G2 B : Mat) (nf : Nat)
    (sp sp' : Split n) (spF : Split (n + m))
    (hsp : splitRead (cornerpivot.wellMat r qn qd en ed n) sp)
    (hone : revAt sp = 1)
    (hsp' : splitRead (seamSite r qn qd c en ed n) sp')
    (hB : B.length = n)
    (htie : matOneValue
      (siteDatum (matAdd H (matScale (lineY r c qd ed) G))
        (matScale (lineX r qn en ed) G))
      (blockJoin
        (siteDatum
          (matAdd
            (matScale (posOfSucc (qd - 1))
              (cornerPencil (headE r n) (matScale (posOfSucc r) (headM c n))
                en ed))
            (matScale (lineY r c qd ed) (idMat n)))
          (matScale (lineX r qn en ed) (idMat n)))
        B
        (siteDatum (matAdd Q (matScale (lineY r c qd ed) G2))
          (matScale (lineX r qn en ed) G2))))
    (hf : countAtPair H G (lineX r qn en ed) (lineY r c qd ed) nf spF) :
    1 ≤ nf :=
  truncation.count_head_le H G _ (idMat n) B Q G2 _ _ 1 nf sp' spF hB htie
    (line_count r qn qd c hqd en ed n 1 sp sp' hsp hone hsp') hf

end corner
