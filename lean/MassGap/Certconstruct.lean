import MassGap.Inertia
import MassGap.Split
import MassGap.Windowsep
/-!
`thm:certconstruct` — the counts, the designation, and the witness:
`count(a) = rev(H : aG)` at a pair level cleared to the integer
carrier (`countRead`, the split the count's certificate at the pair's
stated order — the tex's symmetric `A, B` of order `N`, the
pair-order conjuncts every leaf read's own — exact by the
symmetric elimination), the balance-pair level's count with the
second member cross-added onto the pencil's own side (`countAtPair`,
`rev(H + yG : xG)`), the designation of a jump — two counts at a
gap over an ordered level pair (`desigRead`), with the least root's
sharpening to the pair at the lower level positive semidefinite
(`leastRead`) — and clause (2)'s witness, a vector with the pair's
reads exchanged (`witnessRead` at the quadratic form's fold).  The
refinement's existence at every stated width is the emission's
algorithm, an emitted designation entering as certificate data with
its reads re-read at every verification, the tex's own emission
clause.  The statement's site is a positive-definite gram, the
`pdAt` split of `G`'s own datum the site's read, the committed
batteries at the unit gram.
`lem:dualtrunc`'s seam identity rides the same carrier: at the ray's
positive factor the pencil and both of the level's members rescale
together and the count is unchanged (`countAtPair_scale`,
`countAtPair_unscale`), the reversal blind to the factor
(`lem:inertia`, `inertia.rev_scale`), so a stored level names its
representative; and the count is monotone at a positive-semidefinite
site difference with the pencil and the level each free to move
(`countAtPair_mono`), `lem:inertia`'s monotone read at the
count carrier.  `lem:corner`'s join read rides that monotonicity:
the two levels' difference site is one pencil at two balance-pair
levels and reads the gram's scalar copy, the cross-added level
order's margin the scalar (`siteDiff_scalar`), so a level whose
count is vacant sits at or below a level whose count is occupied
(`count_below_occupied` at `inertia.scalarSplit`'s certificate).
A level pair crossed by one weight on both members
reads one count at one split (`countAtPair_cross`), the crossing's
gram copy and that copy's swap a balanced pair at the sum's unit.
The form fold and its decomposition stand at `inertia`, the site
datum's own module (`quadForm` with `quadForm_add`, `quadForm_swap`,
`quadForm_scale` and the site corollaries): the site datum's form
against the sum's unit is the two members' comparison, the bridge
every count's consumer — `witnessRead` here among them — reads its
requirement through.
-/

namespace certconstruct
open ground elim inertia

/-- The count's certificate at a pair level `[an : ad]`:
`count(a) = rev(H : aG)` cleared, the split's read with its
lower-side fold at the stated value. -/
def countRead {o : Nat} (H G : Mat) (an ad : Pos) (n : Nat) (sp : Split o) : Prop :=
  sqAt H o ∧ sqAt G o
  ∧ splitRead (siteDatum (matScale ad H) (matScale an G)) sp
  ∧ revAt sp = n

instance {o : Nat} (H G : Mat) (an ad : Pos) (n : Nat) (sp : Split o) :
    Decidable (countRead H G an ad n sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The count at a balance-pair level `⟨x : y⟩`: the second member
cross-added onto the pencil's own side, `rev(H + yG : xG)`. -/
def countAtPair {o : Nat} (H G : Mat) (x y : Pos) (n : Nat) (sp : Split o) : Prop :=
  sqAt H o ∧ sqAt G o
  ∧ splitRead (siteDatum (matAdd H (matScale y G)) (matScale x G)) sp
  ∧ revAt sp = n

instance {o : Nat} (H G : Mat) (x y : Pos) (n : Nat) (sp : Split o) :
    Decidable (countAtPair H G x y n sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The site matrices at a diagonal shift are one matrix: the
gram's weighted copy crosses the sum onto the level's member. -/
private theorem siteShift (H G : Mat) (c y : Pos) :
    matAdd (matAdd (matScale c G) H) (matScale y G)
      = matAdd H (matScale (y + c) G) := by
  rw [matScale_addW y c G, elim.matAdd_comm (matScale c G) H,
    elim.matAdd_assoc H (matScale c G) (matScale y G),
    elim.matAdd_comm (matScale c G) (matScale y G)]

/-- The count certificate at a gram-diagonal shift of the pencil is
the certificate at the shift cross-added onto the level: the shifted
pencil and the shifted level read one site matrix
(`lem:chargedcell`(iii), the charged head's count at the intensive
head's shifted level). -/
theorem countAtPair_shift {o : Nat} (H G : Mat) (c x y : Pos)
    (n : Nat) (sp : Split o) (hH : sqAt H o) :
    countAtPair (matAdd (matScale c G) H) G x y n sp
      ↔ countAtPair H G x (y + c) n sp := by
  constructor
  · intro h
    match h with
    | ⟨_, hG, hsplit, hrev⟩ =>
      refine ⟨hH, hG, ?_, hrev⟩
      rw [← siteShift H G c y]
      exact hsplit
  · intro h
    match h with
    | ⟨_, hG, hsplit, hrev⟩ =>
      refine ⟨elim.sqAt_matAdd o (matScale c G) H
        (sqAt_matScale o c G hG) hH, hG, ?_, hrev⟩
      rw [siteShift H G c y]
      exact hsplit

/-- The site matrices at a level pair crossed by one weight are one
matrix up to a balanced copy: the crossing adds the gram's weighted
copy and that copy's swap. -/
private theorem siteCross (H G : Mat) (c x y : Pos) :
    siteDatum (matAdd H (matScale (y + c) G)) (matScale (x + c) G)
      = matAdd (matAdd (matSwap (matScale c G)) (matScale c G))
          (siteDatum (matAdd H (matScale y G)) (matScale x G)) := by
  show matAdd (matAdd H (matScale (y + c) G))
      (matSwap (matScale (x + c) G))
    = matAdd (matAdd (matSwap (matScale c G)) (matScale c G))
        (matAdd (matAdd H (matScale y G)) (matSwap (matScale x G)))
  rw [matScale_addW y c G, matScale_addW x c G,
    elim.matSwap_matAdd (matScale x G) (matScale c G),
    ← elim.matAdd_assoc H (matScale y G) (matScale c G),
    elim.matAdd_shuffle (matAdd H (matScale y G)) (matScale c G)
      (matSwap (matScale x G)) (matSwap (matScale c G)),
    elim.matAdd_comm
      (matAdd (matAdd H (matScale y G)) (matSwap (matScale x G)))
      (matAdd (matScale c G) (matSwap (matScale c G))),
    elim.matAdd_comm (matScale c G) (matSwap (matScale c G))]

/-- The count at a level pair crossed by one weight on both members
is the count at the pair itself, one split reading both site
matrices: the crossing enters as the gram's weighted copy against
that copy's swap, a balanced pair at the sum's unit
(`lem:inertia`, the count at the datum's value). -/
theorem countAtPair_cross {o : Nat} (H G : Mat) (c x y : Pos)
    (n : Nat) (sp : Split o)
    (h : countAtPair H G x y n sp) :
    countAtPair H G (x + c) (y + c) n sp := by
  have hGc : sqAt (matScale c G) o := sqAt_matScale o c G h.2.1
  have hZ : sqAt (matAdd (matSwap (matScale c G)) (matScale c G)) o :=
    elim.sqAt_matAdd o (matSwap (matScale c G)) (matScale c G)
      (elim.sqAt_matSwap o (matScale c G) hGc) hGc
  have hD : sqAt (siteDatum (matAdd H (matScale y G)) (matScale x G)) o :=
    h.2.2.1.1
  have hD' : sqAt (siteDatum (matAdd H (matScale (y + c) G))
      (matScale (x + c) G)) o :=
    sqAt_siteDatum o _ _
      (elim.sqAt_matAdd o H (matScale (y + c) G) h.1
        (sqAt_matScale o (y + c) G h.2.1))
      (sqAt_matScale o (x + c) G h.2.1)
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  refine inertia.splitRead_congr _ _ hD' (elim.matOne_symm ?_) sp h.2.2.1
  rw [siteCross H G c x y]
  exact elim.matAdd_nullL _ _
    (elim.matNull_swap_add (elim.matOne_refl (matScale c G)))
    ((elim.sqAt_len hZ).trans (elim.sqAt_len hD).symm)
    (elim.rowsLen_of_sqAt hZ) (elim.rowsLen_of_sqAt hD)

/-! `lem:dualtrunc`'s seam identity at the count carrier: the ray at
end weights `[q² : p²]` names one integer pencil pair with site datum
`S`, the two coordinates' representatives are the datum's positive
rescalings, and
`count_{[1:τ²]}(λ) = count_S(q²λ) = count_{[σ:1]}(σλ)` at every
level, the reversal count blind to the positive factors
(`lem:inertia`).  The rescaling passes the site datum's own
structure — the entrywise sum, the memberwise swap, the composition
of two weights — and lands the balance weighting at `[c]`. -/

/-- The site datum of the `c`-scaled pencil at the `c`-scaled level
is the unscaled datum rescaled: the weight passes the sum and the
memberwise swap and composes with each member's own. -/
private theorem siteScale (c x y : Pos) (H G : Mat) :
    matScale c (siteDatum (matAdd H (matScale y G)) (matScale x G))
      = siteDatum (matAdd (matScale c H) (matScale (c * y) G))
          (matScale (c * x) G) := by
  show matScale c
      (matAdd (matAdd H (matScale y G)) (matSwap (matScale x G)))
    = matAdd (matAdd (matScale c H) (matScale (c * y) G))
        (matSwap (matScale (c * x) G))
  rw [matScale_matAdd c (matAdd H (matScale y G)) (matSwap (matScale x G)),
    matScale_matAdd c H (matScale y G), matScale_matScale y c G,
    matScale_matSwap c (matScale x G), matScale_matScale x c G]

/-- The seam transport forward (`lem:dualtrunc`): the count at a
level carries onto the `c`-scaled pencil at the `c`-scaled level,
the level's two members scaled by the one factor.  The scaled
certificate's split is stated data; its count is the unscaled
count, the reversal blind to the positive factor. -/
theorem countAtPair_scale {o : Nat} (c : Pos) (H G : Mat)
    (x y : Pos) (n : Nat) (sp sp' : Split o)
    (h : countAtPair H G x y n sp)
    (h' : splitRead (siteDatum
        (matAdd (matScale c H) (matScale (c * y) G))
        (matScale (c * x) G)) sp') :
    countAtPair (matScale c H) G (c * x) (c * y) n sp' :=
  ⟨sqAt_matScale o c H h.1, h.2.1, h',
   (rev_scalePos c
     (siteDatum (matAdd H (matScale y G)) (matScale x G)) sp sp'
     h.2.2.1 (by rw [siteScale c x y H G]; exact h')).trans
     h.2.2.2⟩

/-- The seam transport back (`lem:dualtrunc`): the `c`-scaled
pencil's count at the `c`-scaled level is the unscaled level's
count at the unscaled pencil, the pencil's order the scaled
certificate's own read reflected. -/
theorem countAtPair_unscale {o : Nat} (c : Pos) (H G : Mat)
    (x y : Pos) (n : Nat) (sp sp' : Split o)
    (h : countAtPair (matScale c H) G (c * x) (c * y) n sp')
    (hs : splitRead (siteDatum
        (matAdd H (matScale y G)) (matScale x G)) sp) :
    countAtPair H G x y n sp :=
  ⟨sqAt_matScale_reflect c H h.1, h.2.1, hs,
   (rev_scalePos c
     (siteDatum (matAdd H (matScale y G)) (matScale x G)) sp sp'
     hs (by rw [siteScale c x y H G]; exact h.2.2.1)).symm.trans
     h.2.2.2⟩

/-- The count's monotonicity at a positive-semidefinite site
difference: a pencil-and-level pair whose site datum sits at or
above a second's carries a count at or below the second's, the
pencil and the level each free to move (`lem:inertia`'s monotone
read at the count carrier). -/
theorem countAtPair_mono {o : Nat} (H H' G : Mat) (x y x' y' : Pos)
    (n n' : Nat) (sp sp' spd : Split o)
    (hd : splitRead (siteDatum
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (siteDatum (matAdd H' (matScale y' G)) (matScale x' G))) spd)
    (hpsd : psdAt spd)
    (h : countAtPair H G x y n sp)
    (h' : countAtPair H' G x' y' n' sp') :
    n ≤ n' := by
  have hmono := inertia.rev_mono
    (siteDatum (matAdd H' (matScale y' G)) (matScale x' G))
    (siteDatum (matAdd H (matScale y G)) (matScale x G))
    spd sp' sp hd hpsd h'.2.2.1 h.2.2.1
  rw [h.2.2.2, h'.2.2.2] at hmono
  exact hmono

/-- The two levels' difference site reads the gram's scalar copy:
one pencil at two balance-pair levels, the cross-added level order's
margin the scalar (`lem:corner`'s join read, the difference site at
the monotone count read). -/
theorem siteDiff_scalar {o : Nat} (H G : Mat) (hH : sqAt H o)
    (hG : sqAt G o) (lx ly gx gy c : Pos)
    (hc : lx + gy + c = gx + ly) :
    matOneValue
      (siteDatum
        (siteDatum (matAdd H (matScale ly G)) (matScale lx G))
        (siteDatum (matAdd H (matScale gy G)) (matScale gx G)))
      (matScale c G) := by
  have hly : ly + gx = gy + lx + c := by
    rw [ground.add_comm ly gx, ← hc, ground.add_comm lx gy]
  have hW : sqAt (matScale (gy + lx) G) o := sqAt_matScale o (gy + lx) G hG
  have hcG : sqAt (matScale c G) o := sqAt_matScale o c G hG
  have hN1 : sqAt (matAdd H (matSwap H)) o :=
    elim.sqAt_matAdd o H (matSwap H) hH (elim.sqAt_matSwap o H hH)
  have hN2 : sqAt (matAdd (matScale (gy + lx) G)
      (matSwap (matScale (gy + lx) G))) o :=
    elim.sqAt_matAdd o _ _ hW (elim.sqAt_matSwap o _ hW)
  have hsum : sqAt (matAdd (matAdd (matScale (gy + lx) G)
      (matSwap (matScale (gy + lx) G))) (matScale c G)) o :=
    elim.sqAt_matAdd o _ _ hN2 hcG
  show matOneValue
    (matAdd (matAdd (matAdd H (matScale ly G)) (matSwap (matScale lx G)))
      (matSwap (matAdd (matAdd H (matScale gy G))
        (matSwap (matScale gx G)))))
    (matScale c G)
  rw [elim.matSwap_matAdd (matAdd H (matScale gy G))
      (matSwap (matScale gx G)),
    elim.matSwap_matAdd H (matScale gy G),
    elim.matSwap_matSwap (matScale gx G),
    elim.matAdd_shuffle (matAdd H (matScale ly G))
      (matSwap (matScale lx G))
      (matAdd (matSwap H) (matSwap (matScale gy G))) (matScale gx G),
    elim.matAdd_shuffle H (matScale ly G) (matSwap H)
      (matSwap (matScale gy G)),
    elim.matAdd_assoc (matAdd H (matSwap H))
      (matAdd (matScale ly G) (matSwap (matScale gy G)))
      (matAdd (matSwap (matScale lx G)) (matScale gx G)),
    elim.matAdd_comm (matSwap (matScale lx G)) (matScale gx G),
    elim.matAdd_shuffle (matScale ly G) (matSwap (matScale gy G))
      (matScale gx G) (matSwap (matScale lx G)),
    ← matScale_addW ly gx G,
    ← elim.matSwap_matAdd (matScale gy G) (matScale lx G),
    ← matScale_addW gy lx G, hly, matScale_addW (gy + lx) c G,
    elim.matAdd_assoc (matScale (gy + lx) G) (matScale c G)
      (matSwap (matScale (gy + lx) G)),
    elim.matAdd_comm (matScale c G) (matSwap (matScale (gy + lx) G)),
    ← elim.matAdd_assoc (matScale (gy + lx) G)
      (matSwap (matScale (gy + lx) G)) (matScale c G)]
  refine elim.matOne_trans (elim.matAdd_nullL _ _
    (elim.matNull_add_swap H)
    ((elim.sqAt_len hN1).trans (elim.sqAt_len hsum).symm)
    (elim.rowsLen_of_sqAt hN1) (elim.rowsLen_of_sqAt hsum)) ?_
  exact elim.matAdd_nullL _ _
    (elim.matNull_add_swap (matScale (gy + lx) G))
    ((elim.sqAt_len hN2).trans (elim.sqAt_len hcG).symm)
    (elim.rowsLen_of_sqAt hN2) (elim.rowsLen_of_sqAt hcG)

/-- The two levels' difference site at equal cross-added levels is
null: the pencil's balanced double against the collected weights'
balanced double, every entry at the sum's unit. -/
theorem siteDiff_null (H G : Mat) (lx ly gx gy : Pos)
    (hc : lx + gy = gx + ly) :
    elim.matNull
      (siteDatum
        (siteDatum (matAdd H (matScale ly G)) (matScale lx G))
        (siteDatum (matAdd H (matScale gy G)) (matScale gx G))) := by
  have hly : ly + gx = gy + lx := by
    rw [ground.add_comm ly gx, ← hc, ground.add_comm lx gy]
  show elim.matNull
    (matAdd (matAdd (matAdd H (matScale ly G)) (matSwap (matScale lx G)))
      (matSwap (matAdd (matAdd H (matScale gy G))
        (matSwap (matScale gx G)))))
  rw [elim.matSwap_matAdd (matAdd H (matScale gy G))
      (matSwap (matScale gx G)),
    elim.matSwap_matAdd H (matScale gy G),
    elim.matSwap_matSwap (matScale gx G),
    elim.matAdd_shuffle (matAdd H (matScale ly G))
      (matSwap (matScale lx G))
      (matAdd (matSwap H) (matSwap (matScale gy G))) (matScale gx G),
    elim.matAdd_shuffle H (matScale ly G) (matSwap H)
      (matSwap (matScale gy G)),
    elim.matAdd_assoc (matAdd H (matSwap H))
      (matAdd (matScale ly G) (matSwap (matScale gy G)))
      (matAdd (matSwap (matScale lx G)) (matScale gx G)),
    elim.matAdd_comm (matSwap (matScale lx G)) (matScale gx G),
    elim.matAdd_shuffle (matScale ly G) (matSwap (matScale gy G))
      (matScale gx G) (matSwap (matScale lx G)),
    ← matScale_addW ly gx G,
    ← elim.matSwap_matAdd (matScale gy G) (matScale lx G),
    ← matScale_addW gy lx G, hly]
  exact elim.matNull_matAdd (elim.matNull_add_swap H)
    (elim.matNull_add_swap (matScale (gy + lx) G))

/-- The drift sits strictly below any occupied margin at the unit
gram: a level whose count is vacant reads strictly below a level
whose count is occupied — the cross-added order at the difference
site's scalar certificate, the equal-level reading refused at the
vacant certificate (`lem:corner`'s join read; `lem:inertia`'s
monotone count read). -/
theorem count_below_occupied {o : Nat} (H : Mat) (gx gy lx ly : Pos)
    (n : Nat) (spg spl : Split o)
    (hvac : countAtPair H (idMat o) gx gy 0 spg)
    (hocc : countAtPair H (idMat o) lx ly n spl)
    (hn : 1 ≤ n) :
    gx + ly < lx + gy := by
  match ground.trich (lx + gy) (gx + ly) with
  | .lt c hc =>
    have hd : splitRead
        (siteDatum
          (siteDatum (matAdd H (matScale ly (idMat o)))
            (matScale lx (idMat o)))
          (siteDatum (matAdd H (matScale gy (idMat o)))
            (matScale gx (idMat o))))
        (inertia.scalarSplit o c) :=
      inertia.scalarSplit_read c _
        (sqAt_siteDatum o _ _
          (sqAt_siteDatum o _ _
            (elim.sqAt_matAdd o H _ hocc.1
              (sqAt_matScale o ly (idMat o) hocc.2.1))
            (sqAt_matScale o lx (idMat o) hocc.2.1))
          (sqAt_siteDatum o _ _
            (elim.sqAt_matAdd o H _ hocc.1
              (sqAt_matScale o gy (idMat o) hocc.2.1))
            (sqAt_matScale o gx (idMat o) hocc.2.1)))
        (siteDiff_scalar H (idMat o) hocc.1 hocc.2.1 lx ly gx gy c hc)
    have hmono := countAtPair_mono H H (idMat o) lx ly gx gy n 0
      spl spg (inertia.scalarSplit o c) hd
      (inertia.scalarSplit_psd o c) hocc hvac
    exact absurd (Nat.le_trans hn hmono) (Nat.not_succ_le_zero 0)
  | .eq he =>
    have hd : splitRead
        (siteDatum
          (siteDatum (matAdd H (matScale ly (idMat o)))
            (matScale lx (idMat o)))
          (siteDatum (matAdd H (matScale gy (idMat o)))
            (matScale gx (idMat o))))
        (inertia.unitSplit o) :=
      inertia.unitSplit_read _
        (sqAt_siteDatum o _ _
          (sqAt_siteDatum o _ _
            (elim.sqAt_matAdd o H _ hocc.1
              (sqAt_matScale o ly (idMat o) hocc.2.1))
            (sqAt_matScale o lx (idMat o) hocc.2.1))
          (sqAt_siteDatum o _ _
            (elim.sqAt_matAdd o H _ hocc.1
              (sqAt_matScale o gy (idMat o) hocc.2.1))
            (sqAt_matScale o gx (idMat o) hocc.2.1)))
        (siteDiff_null H (idMat o) lx ly gx gy he)
    have hmono := countAtPair_mono H H (idMat o) lx ly gx gy n 0
      spl spg (inertia.unitSplit o) hd
      (inertia.unitSplit_psd o) hocc hvac
    exact absurd (Nat.le_trans hn hmono) (Nat.not_succ_le_zero 0)
  | .gt c hc => exact ⟨c, hc⟩

/-- A designation's arithmetic at the levels `[ln : ld] < [hn : hd]`:
the two counts read at a gap of at least one at their splits; the
whole designation joins the width clause below (`desigWhole`). -/
def desigRead {o : Nat} (H G : Mat) (ln ld hn hd : Pos) (g : Nat)
    (spl sph : Split o) : Prop :=
  sqAt H o ∧ sqAt G o
  ∧ ln * hd < hn * ld
  ∧ splitRead (siteDatum (matScale ld H) (matScale ln G)) spl
  ∧ splitRead (siteDatum (matScale hd H) (matScale hn G)) sph
  ∧ revAt spl + g = revAt sph
  ∧ 1 ≤ g

instance {o : Nat} (H G : Mat) (ln ld hn hd : Pos) (g : Nat)
    (spl sph : Split o) :
    Decidable (desigRead H G ln ld hn hd g spl sph) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The designation whole, the tex's one datum `(l, h, w)`: the
counts at a gap, the width joining the endpoints (`l + w = h`, one
cross-multiplied read), and the width at most the pencil
determinant's `δ` (`lem:split`'s `χ` at `thm:windowsep`'s
separation read) — the reads its whole verification.  The width
clause reads the pencil polynomial's one-value class
(`windowsep.sepRead_congr`), so the instance decides it at the
descent's representative at a square frame (`elim.pdetD_eq`),
the fold branch the ragged frames'. -/
def desigWhole {o : Nat} (H G : Mat) (ln ld hn hd wn wd : Pos)
    (g : Nat) (spl sph : Split o) : Prop :=
  desigRead H G ln ld hn hd g spl sph
  ∧ hn * (ld * wd) = ln * (hd * wd) + wn * (ld * hd)
  ∧ windowsep.sepRead (split.charPoly H G) wn wd

instance {o : Nat} (H G : Mat) (ln ld hn hd wn wd : Pos) (g : Nat)
    (spl sph : Split o) :
    Decidable (desigWhole H G ln ld hn hd wn wd g spl sph) :=
  let Z := split.zMat H G
  match elim.decRowsLen Z.length Z with
  | isTrue hsq =>
    decidable_of_iff
      (desigRead H G ln ld hn hd g spl sph
       ∧ hn * (ld * wd) = ln * (hd * wd) + wn * (ld * hd)
       ∧ windowsep.sepRead (elim.pdetD Z) wn wd)
      ⟨fun x => ⟨x.1, x.2.1,
        (windowsep.sepRead_congr
          (elim.pdetD_eq Z hsq) wn wd).mp x.2.2⟩,
       fun x => ⟨x.1, x.2.1,
        (windowsep.sepRead_congr
          (elim.pdetD_eq Z hsq) wn wd).mpr x.2.2⟩⟩
  | isFalse _ =>
    inferInstanceAs
      (Decidable (desigRead H G ln ld hn hd g spl sph
       ∧ hn * (ld * wd) = ln * (hd * wd) + wn * (ld * hd)
       ∧ windowsep.sepRead (split.charPoly H G) wn wd))

/-- The least root's sharpening: the pair at the lower level
positive semidefinite, one split and one count, with the upper
level's count occupied. -/
def leastRead {o : Nat} (H G : Mat) (ln ld hn hd : Pos)
    (spl sph : Split o) : Prop :=
  sqAt H o ∧ sqAt G o
  ∧ ln * hd < hn * ld
  ∧ splitRead (siteDatum (matScale ld H) (matScale ln G)) spl
  ∧ psdAt spl
  ∧ splitRead (siteDatum (matScale hd H) (matScale hn G)) sph
  ∧ 1 ≤ revAt sph

instance {o : Nat} (H G : Mat) (ln ld hn hd : Pos) (spl sph : Split o) :
    Decidable (leastRead H G ln ld hn hd spl sph) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Clause (2)'s witness: a vector with `uᵀBu` exceeding `uᵀAu`,
the reversal's read off the elimination — at `(H : aG)` the
certificate's witness whenever the count is occupied.  The read is
refutation-monotone at the carrier: a shorter or longer vector
reads a compression, and a compression's failure is the window's,
so the bare witness under-claims at worst. -/
def witnessRead (A B : Mat) (u : List BPair) : Prop :=
  quadForm A u < quadForm B u

instance (A B : Mat) (u : List BPair) :
    Decidable (witnessRead A B u) :=
  inferInstanceAs (Decidable (_ < _))

end certconstruct
