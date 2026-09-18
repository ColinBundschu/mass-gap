import MassGap.Gappos
import MassGap.Lattice
/-!
`lem:freecell` — the free cell's certificate and its extent.

The certificate is the supplied scalar-dominance instance of
`lem:freecell`, a read on one window pencil: the cell
from the free end at a fixed pair of absolute levels
(`gappos.cellsRead` at one cell on the decimated head), the cell's
boundary families at the `α = 1`
representative (`freeList`), and the extent as the families' root
list's first positive member (`listExtent`). The row-cap data are
verified by `capRead`: each stated tower row's electric diagonal
entry is at or beyond the head bound, and its full magnetic off-row
magnitude fold at the floor is within the stated cap of that entry.
The scalar comparison family has two linear reads in the magnetic
weight (`domDiv`): at the head bound `Λ_h` beyond the certificate's
upper level `ℓ₊`, the read at the bound is
`c₂(f)(Λ_h − ℓ₊) − τ² 2 d_L pv Λ_h`, and the leading side in the
row variable, `c₂(f) − τ² 2 d_L pv`. The data are `d_L`, the
per-vertex plaquette count `pv` read at the direction count
(`con:lattice`, `lattice.vertexPlaq`) and the member floor `c₂(f)`.
At a diagonal electric matrix and the unit Gram these comparisons
price the row gaps with the magnetic diagonal term included, the
scalar instance of `thm:decimation`(ii). The cell's count covers verify the actual
supplied pencil and Gram. The jump family, the two level
carriers' determinants, has its roots off the cell's segment at the
cell's own covers, the theorem `freeRead_jump`
(`gappos.cell_rootfree`, `lem:cellcount`'s cover the determinant's
root-freeness read), so the list holds the dominance divisor with
the stated further families, the deck and tension families'
polynomials in the root coordinate (`fams`).  `listExtent` reads the
extent at the list: the designated member's first positive root
located at the bracket `[lo, hi]` at the clearing `cc`, its origin
part withdrawn at the least occupied degree `k`
(`contactcell.extentRead`), and every further member keeping its
side from the free end to the bracket's top at a pivot cover of its
own order-one pencil (`cellcount.coverRead`), so the joined root
list's first positive member is the designated member's
(`listExtent_off`).  `freeRead` is the certificate's read at a
window pencil and the free end's level: the cell from the free end,
the cap read, the head bound beyond the upper level, the extent, the
bracket inside the cell's segment (the cell covering every ray at
or below the extent), and the floor pair `[kn : kd]` under the
cell's gap at the level (`gappos.gapsAt`), and the ground's count
one at the lower line (`thm:SO`'s multiplicity over the cell attached
to the free end); the window pencil is one fiber, the box window's,
its momentum section the whole read; `freeRead_pos` is the extent's
positivity, the free end's interiority read, the bracket's foot above
the sum's unit. The two levels are the `Cell`'s balance pairs in
the supplied pencil's units. The ground-relative level identity
of `def:pencil` reads an offset `a` at the absolute level `ε₀ + a`,
with `ε₀` the supplied window's designated ground. The sum is a
located-stage read; `freePMat` represents the raw pencil at its
stated absolute level. A `freeRead` proof certifies its supplied
window and its stated range.
-/

namespace freecell
open ground poly elim inertia

/-- The supplied scalar dominance record's comparison family at the
`α = 1` representative: two linear reads in the magnetic weight, cleared
at the member floor: the read at the head bound `hb` against the
upper level `⟨tx : ty⟩`, `fl (hb + ty − tx) − τ² 2 dL pv hb`, and the
leading side in the content, `fl − τ² 2 dL pv`
(`lem:freecell`'s scalar dominance instance at the supplied row-cap
coefficient `2 dL pv` against the floor `fl`). -/
def domDiv (hb dL pv fl tx ty : Pos) : List Poly :=
  [[BPair.ofPos fl * (BPair.ofPos hb + BPair.ofPos ty + (BPair.ofPos tx).swap),
    BPair.unit, (BPair.ofPos (2 * dL * pv * hb)).swap],
   [BPair.ofPos fl, BPair.unit, (BPair.ofPos (2 * dL * pv)).swap]]

/-- The supplied window's row-cap read: every stated tower row's
electric diagonal entry sits at or beyond the head bound, and its
full off-row magnetic magnitude fold satisfies
`fl · fold ≤ 2 dL pv · E_ii` (`lem:freecell`'s scalar dominance
instance). The fold includes every other column of the supplied
matrix; the per-vertex count is the direction count's read
(`lattice.vertexPlaq`). -/
def capRead (E M : Mat) (tw : List Nat) (hb dL pv fl : Pos) : Prop :=
  (tw.all (fun i =>
    decide (BPair.ofPos hb ≤ getAt BPair.unit (getAt [] E i) i)
    && decide (BPair.ofPos fl * decimation.offFold i (getAt [] M i)
        ≤ BPair.ofPos (2 * dL * pv) * getAt BPair.unit (getAt [] E i) i))) = true

instance instFreecell1 (E M : Mat) (tw : List Nat) (hb dL pv fl : Pos) :
    Decidable (capRead E M tw hb dL pv fl) :=
  inferInstanceAs (Decidable (_ = _))

/-- The further members' read, one walk over the list with its
covers: every member off the designated place `j` keeps its side from
the free end to the bracket's top at its own cover, the walk counting
the places from `s`. -/
def othersOff (j : Nat) (hi : BPair) (cc : Pos) :
    Nat → List Poly → List cellcount.Cover → Bool
  | _, [], _ => true
  | _, _ :: _, [] => false
  | s, p :: ps, c :: cs =>
      ((s == j) || decide (cellcount.coverRead [[p]] 1 0 stage.unitC ⟨hi, cc⟩ c))
      && othersOff j hi cc (s + 1) ps cs

/-- The extent read at a list of polynomials in the root coordinate:
the designated member `j`'s first positive root located at the
bracket `[lo, hi]` at the clearing `cc`, its origin part withdrawn at
the least occupied degree `k` (`contactcell.extentRead`), and every
further member keeping its side from the free end to the bracket's
top at a pivot cover of its own order-one pencil, one cover per
member (`cellcount.coverRead`), so the joined root list's first
positive member is the designated member's. -/
def listExtent {o1 o2 o3 o4 : Nat} (L : List Poly) (j k : Nat)
    (ct : cellcount.DivCert) (lo hi : BPair) (cc : Pos)
    (spH1 : Split o1) (spB1 : Split o2) (spH2 : Split o3) (spB2 : Split o4)
    (covs : List cellcount.Cover) : Prop :=
  j < L.length
  ∧ covs.length = L.length
  ∧ contactcell.extentRead (getAt [] L j) k ct lo hi cc spH1 spB1 spH2 spB2
  ∧ othersOff j hi cc 0 L covs = true

instance instFreecell2 {o1 o2 o3 o4 : Nat} (L : List Poly) (j k : Nat)
    (ct : cellcount.DivCert) (lo hi : BPair) (cc : Pos)
    (spH1 : Split o1) (spB1 : Split o2) (spH2 : Split o3) (spB2 : Split o4)
    (covs : List cellcount.Cover) :
    Decidable (listExtent L j k ct lo hi cc spH1 spB1 spH2 spB2 covs) :=
  inferInstanceAs (Decidable (_ ∧ _ = _ ∧ _ ∧ _ = _))

/-- A pivot cover of an order-one pencil keeps the entry off the
sum's unit at every point of an occupied segment: each piece's entry
keeps its side, the pieces chained to the top. -/
private theorem cover1_off : ∀ (cov : cellcount.Cover) (p : Poly) (K : Nat)
    (lo hi : CPair), cellcount.coverRead [[p]] 1 K lo hi cov → lo < hi →
    ∀ x : CPair, lo ≤ x → x ≤ hi → ¬ (stage.evalC p x).oneValue stage.unitC
  | .done, _, _, _, _, h, hlt => (CPair.not_lt_of_one h hlt).elim
  | .nought, _, _, _, _, h, _ => Bool.noConfusion h
  | .one b i up N D _ rest, p, K, lo, hi, h, _ => by
    have hi0 : i < 1 := ground.bltLt (ground.andSplitB h.1.1).1
    have hi1 : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi0)
    subst hi1
    have hs : (if up = true then stage.keepUpper p lo b N D
        else stage.keepLower p lo b N D) := h.2.1
    refine cellcount.seg_split (fun y => ¬ (stage.evalC p y).oneValue stage.unitC)
      lo b hi ?_ (fun hlt' => cover1_off rest p K b hi h.2.2.2 hlt')
    intro y hly hyb hov
    match up, hs with
    | true, hs =>
      exact CPair.not_lt_of_one (CPair.oneValue_symm hov)
        (stage.keepUpper_all p lo b N D hs y hly hyb)
    | false, hs =>
      exact CPair.not_lt_of_one hov (stage.keepLower_all p lo b N D hs y hly hyb)
  | .mixed _ i j _ _ _ _, _, _, _, _, h, _ => by
    have hs1 := ground.andSplitB h.1.1
    have hs2 := ground.andSplitB hs1.2
    have hi1 : i = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (ground.bltLt hs1.1))
    have hj1 : j = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (ground.bltLt hs2.1))
    subst hi1
    subst hj1
    exact absurd (h.1.2 0 (List.Mem.head _)) (by decide)
  | .twoUp _ i j _ _ _ _ _ _ _, _, _, _, _, h, _ => by
    have hs1 := ground.andSplitB h.1.1
    have hs2 := ground.andSplitB hs1.2
    have hi1 : i = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (ground.bltLt hs1.1))
    have hj1 : j = 0 :=
      Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (ground.bltLt hs2.1))
    subst hi1
    subst hj1
    exact absurd (h.1.2 0 (List.Mem.head _)) (by decide)
  | .diag b i up N D _ rest, p, K, lo, hi, h, _ => by
    have hi0 : i < 1 := ground.bltLt (ground.andSplitB h.1.1).1
    have hi1 : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi0)
    subst hi1
    have hs : (if up = true then stage.keepUpper p lo b N D
        else stage.keepLower p lo b N D) := h.2.1
    refine cellcount.seg_split (fun y => ¬ (stage.evalC p y).oneValue stage.unitC)
      lo b hi ?_ (fun hlt' => cover1_off rest p K b hi h.2.2.2.2 hlt')
    intro y hly hyb hov
    match up, hs with
    | true, hs =>
      exact CPair.not_lt_of_one (CPair.oneValue_symm hov)
        (stage.keepUpper_all p lo b N D hs y hly hyb)
    | false, hs =>
      exact CPair.not_lt_of_one hov (stage.keepLower_all p lo b N D hs y hly hyb)

/-- The walk's read at a place: the member there off the designated
place keeps its side at its own cover. -/
private theorem othersOff_read (j : Nat) (hi : BPair) (cc : Pos) :
    ∀ (s : Nat) (L : List Poly) (covs : List cellcount.Cover),
    othersOff j hi cc s L covs = true → covs.length = L.length →
    ∀ i, i < L.length → ¬ (s + i = j) →
    cellcount.coverRead [[getAt [] L i]] 1 0 stage.unitC ⟨hi, cc⟩
      (getAt cellcount.Cover.done covs i)
  | _, [], _, _, _, i, hi', _ => absurd hi' (Nat.not_lt_zero i)
  | _, _ :: _, [], _, hl, _, _, _ => Nat.noConfusion hl
  | s, p :: ps, c :: cs, h, hl, 0, _, hij => by
    have h1 := (ground.andSplitB h).1
    have hsj : (s == j) = false := by
      cases hb : (s == j) with
      | true => exact absurd (of_decide_eq_true hb) hij
      | false => rfl
    rw [hsj, Bool.false_or] at h1
    exact of_decide_eq_true h1
  | s, _ :: ps, _ :: cs, h, hl, i + 1, hi', hij =>
    othersOff_read j hi cc (s + 1) ps cs (ground.andSplitB h).2 (Nat.succ.inj hl) i
      (Nat.lt_of_succ_lt_succ hi')
      (fun he => hij (by rw [Nat.add_succ, ← Nat.succ_add]; exact he))

/-- Every member of the list off the designated one keeps its side
from the free end to the bracket's top, its root list vacant there:
the joined root list's first positive member is the designated
member's. -/
theorem listExtent_off {o1 o2 o3 o4 : Nat} (L : List Poly) (j k : Nat)
    (ct : cellcount.DivCert) (lo hi : BPair) (cc : Pos)
    (spH1 : Split o1) (spB1 : Split o2) (spH2 : Split o3) (spB2 : Split o4)
    (covs : List cellcount.Cover)
    (h : listExtent L j k ct lo hi cc spH1 spB1 spH2 spB2 covs)
    (hlt : stage.unitC < (⟨hi, cc⟩ : CPair))
    (i : Nat) (hiL : i < L.length) (hij : ¬ i = j)
    (x : CPair) (hx1 : stage.unitC ≤ x) (hx2 : x ≤ ⟨hi, cc⟩) :
    ¬ (stage.evalC (getAt [] L i) x).oneValue stage.unitC :=
  cover1_off _ _ 0 _ _
    (othersOff_read j hi cc 0 L covs h.2.2.2 h.2.1 i hiL
      (fun he => hij (by rw [Nat.zero_add] at he; exact he)))
    hlt x hx1 hx2

set_option genInjectivity false in
/-- The free cell's local certificate on a supplied window pencil:
the cell from the free end at its fixed absolute level pair, the
head bound `hb` with the per-term cap
`dL`, the direction count `d` (the per-vertex plaquette count its
read, `lattice.vertexPlaq`) and the member floor per link `fl` (the
dominance divisor's data), the stated further
families' polynomials in the root coordinate `fams` with one cover
per list member `covs`, the designated member `j`, the origin
multiplicity `k` with the squarefree witness past the origin and the
extent's located bracket `[lo, hi]` at the clearing `cc` with its four
splits at their orders (`lem:contactcell`'s bracket shape at the
withdrawn cofactor), and the floor pair `[kn : kd]`. -/
structure FreeCert (o : Nat) where
  cell : gappos.Cell o
  hb : Pos
  dL : Pos
  d : Nat
  fl : Pos
  fams : List Poly
  covs : List cellcount.Cover
  j : Nat
  k : Nat
  ct : cellcount.DivCert
  lo : BPair
  hi : BPair
  cc : Pos
  o1 : Nat
  o2 : Nat
  o3 : Nat
  o4 : Nat
  spH1 : Split o1
  spB1 : Split o2
  spH2 : Split o3
  spB2 : Split o4
  kn : Pos
  kd : Pos

/-- The boundary families' polynomials at the certificate past the
jump family: the dominance divisor at the head bound and the
certificate's upper level, and the stated further families. -/
def freeList {o : Nat} (fc : FreeCert o) : List Poly :=
  domDiv fc.hb fc.dL (lattice.vertexPlaq fc.d) fc.fl fc.cell.tx fc.cell.ty ++ fc.fams

/-- The local certificate's read at a supplied window and the free
end's level (`lem:freecell`): the cell read from the free end at its
stated absolute levels, the cap read at
the tower rows, the head bound beyond the upper level, the extent as
the list's first positive root, the bracket inside the cell's
segment, the floor pair under the cell's gap at the level, and the
ground's count one at the lower line (`lem:freecell`'s separation
clause, `thm:SO`'s multiplicity over the cell attached to the free
end). -/
def freeRead (E M G : Mat) (E0 : Pos) {o : Nat} (fc : FreeCert o) : Prop :=
  gappos.cellsRead E M G ⟨BPair.unit, 1⟩ [fc.cell]
  ∧ capRead E M fc.cell.tw fc.hb fc.dL (lattice.vertexPlaq fc.d) fc.fl
  ∧ fc.cell.tx < fc.hb + fc.cell.ty
  ∧ listExtent (freeList fc) fc.j fc.k fc.ct fc.lo fc.hi fc.cc
      fc.spH1 fc.spB1 fc.spH2 fc.spB2 fc.covs
  ∧ (⟨fc.hi, fc.cc⟩ : CPair) ≤ fc.cell.hi
  ∧ gappos.gapsAt E0 fc.kn fc.kd [fc.cell]
  ∧ fc.cell.g = 1

instance instFreecell3 (E M G : Mat) (E0 : Pos) {o : Nat} (fc : FreeCert o) :
    Decidable (freeRead E M G E0 fc) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ = _))

/-- The extent's positivity is the free end's interiority read: the
bracket's foot sits above the sum's unit
(`contactcell.extentRead_pos`). -/
theorem freeRead_pos (E M G : Mat) (E0 : Pos) {o : Nat} (fc : FreeCert o)
    (h : freeRead E M G E0 fc) : BPair.unit < fc.lo :=
  contactcell.extentRead_pos _ _ _ _ _ _ _ _ _ _ h.2.2.2.1.2.2.1

/-- The jump family's roots sit off the extent: at every point from
the free end to the bracket's top both level carriers' determinants
sit off the sum's unit, the cell's covers reading them so
(`gappos.cell_rootfree`, `lem:cellcount`'s root-freeness read at
`lem:freecell`'s jump family), the cell holding the bracket. -/
theorem freeRead_jump (E M G : Mat) (E0 : Pos) {o : Nat} (fc : FreeCert o)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o)
    (hEs : symmRead E) (hMs : symmRead M) (hGs : symmRead G)
    (h : freeRead E M G E0 fc) (hlt : stage.unitC < (⟨fc.hi, fc.cc⟩ : CPair))
    (zn : BPair) (zc : Pos)
    (hx1 : stage.unitC ≤ (⟨zn, zc⟩ : CPair)) (hx2 : (⟨zn, zc⟩ : CPair) ≤ ⟨fc.hi, fc.cc⟩) :
    ¬ (minor (cellcount.evalPC (freePMat E M G fc.cell.ax fc.cell.ay) zn zc 2)).oneValue
        BPair.unit
    ∧ ¬ (minor (cellcount.evalPC (freePMat E M G fc.cell.tx fc.cell.ty) zn zc 2)).oneValue
        BPair.unit := by
  have hc : gappos.cellRead E M G fc.cell := h.1.1
  have hlo : fc.cell.lo ≤ stage.unitC := h.1.2.1
  have hhi : (⟨fc.hi, fc.cc⟩ : CPair) ≤ fc.cell.hi := h.2.2.2.2.1
  exact gappos.cell_rootfree E M G hE hM hG hEs hMs hGs fc.cell hc
    (stage.leC_lt_trans hlo (stage.ltC_le_trans hlt hhi)) zn zc
    (CPair.le_trans hlo hx1) (CPair.le_trans hx2 hhi)

end freecell
