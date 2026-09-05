import MassGap.Cornerfloor
import MassGap.Momentfold
import MassGap.Cone
import MassGap.Gappos
/-!
`thm:continuum` — the continuum reads.  A continuum datum is a
finite list of supports, separations and Euclidean pairs at pair
coordinates against the chain's height (`Datum`), its observables
the algebra's at those supports; the datum's own read at a scale is
its site counts, one per support (`siteCount`, `siteCounts`:
`thm:groundreads`(vii)'s scale count at the pair coordinate, the
multiples of the chain's height at the scale at or below the
support's extent, cross-multiplied at the pair's two members, the
count's two comparisons its whole read, `siteCount_read` and
`siteCount_vac`).

Clause (i).  At every scale of the corner cell the datum's reads
sit in the stated brackets: a support's read is window-free within
the transport bracket (`groundreads.window_transport` at the support's
depth), a separation's connected read within the crossing
certificates' bracket (`groundreads.cluster_read` at the separating
slabs), and a Euclidean pair's read within the pair
bracket (`groundreads.euc_pair_price` at the pair `u`), two scales'
reads within the scale sandwich's priced bracket
(`groundreads.scale_read`).  On the corner disconjugacy certificate's
head, the walk's band-one head (`corner.headM`, `cornerpivot.wellMat`),
the floor locates the clearance at every tail scale
(`corner.cut_flat`, `corner.cut_flat_T` and `corner.cut_flat_S` at
every scale under the ceiling), the
ground-level sandwich sums to one cofactor read at the upper
family's rate (`ground.widthSum` at `corner.rate_close`'s rate), the
heights read two-sided at the certificate's rates
(`cornerpivot.witCount` from below, `cornerpivot.certCount` from
above), and a datum's scale reads close on the moment folds'
clearance cell (`momentfold.datum_close`).  The clause's own read at
the datum is the site counts' stabilization with the height's
brackets: the counts read one value at a scale bracket's two ends
(`countsStable`), and then one value at every scale between
(`counts_stable`, `groundreads.scaleCount_stable` and
`scaleCount_stable_vac` support by support).

Clause (ii).  Every finite Gram of bracketed reads is positive
semidefinite (`inertia.gram_psd`, the pairing's Gram at the reads'
vectors); reads at disjoint supports read one value at either order
and an ordering difference beyond the reach is the remainder's own
read (`groundreads.lead_tail_null`, `groundreads.prop_bracket`);
separated reads pair to their product within the crossing
certificates' brackets (`groundreads.cluster_read`); the certificate's
head's heights are two-sided located data at its positive located
floor (`corner.cut_flat`, `corner.cut_flat_T`, `corner.cut_flat_S`,
`corner.floor_pos`), and the chain's ground sits at or below the
head's line, the head its leading block
(`corner.ground_below_line` at `truncation.count_head_le`), so the
spectral data sit at the ground in the corner scale there: at a head pencil whose level gap ties to the
ground level (`def:pencil`'s `ε₀ G + Ẽ = H`), the count one at a
corner line reads the gap's count one at the line's gap level
through the site shift (`inertia.rev_exchange` at the shifted site,
the corner scale's own read), the located roots below the edge then
read one, the kernel root alone (`split.kernel_le_below`,
`split.rootsBelow_mono`), and the cut tie holds at every edge at or
below the line's gap level (`cell_cut` at
`flatstep.cutTie_of_edge`); the edge reaches the two lines' gap wherever
the ground sits at or below the lower line (`edge_floor`).  The
momentum reads are isotropic at degree two with the direction data
two degrees down (`cone.cone_read`), the multiplicities scale-free
(`restoration.deg4_indep`, `restoration.quartic_breaks`, stated at
every direction count with no scale datum).

Clause (iii).  The spacing is an output: the chain's height at a
scale is located between the ray's floor and its caps, one output
bracket per scale — the certificate's head's two-sided datum, its
floor's two members (`corner.floorN`, `corner.floorD`) positive by
their shape (`corner.floor_pos`), the count one at every cut
member's line (`corner.cut_flat`, `corner.cut_flat_T`,
`corner.cut_flat_S`, `corner.line_count`), the chain's ground at or
below the line (`corner.ground_below_line`) and its second root at
or below the head's (`truncation.count_head_le`,
`contactcell.count_bord_le`), and every probe's two moments' read
capping the chain's edge beside it (`attained.probe_cap`).
-/

namespace continuum
open ground elim inertia certconstruct

set_option genInjectivity false in
/-- The continuum datum: a finite list of supports, separations and
Euclidean pairs at pair coordinates against the chain's height, each
member a scalar pair `[sn : sd]` (`def:ground`) — the supports and
the separations at their extents, the Euclidean pairs at
`thm:groundreads`(v)'s pair `u`. -/
structure Datum where
  supports : List (Pos × Pos)
  seps : List (Pos × Pos)
  eucs : List (Pos × Pos)

/-- A member's site count against the chain's height at the scale,
`h = [hn : hd]`: the count of the height's multiples at or below the
member's extent `[sn : sd]`, the multiples `m` at `m·hn·sd ≤ sn·hd`
cross-multiplied (`thm:groundreads`(vii)'s scale count at the pair
coordinate). -/
def siteCount (s : Pos × Pos) (hn hd : Pos) : Option Pos :=
  groundreads.scaleCount s.1 (hn * s.2) hd

/-- The datum's site counts, one per support. -/
def siteCounts (D : Datum) (hn hd : Pos) : List (Option Pos) :=
  D.supports.map (fun s => siteCount s hn hd)

/-- An occupied site count is the stated one: the count `q` brackets
the cross-multiplied extent between `q` and `q + 1` multiples of the
cleared height, the two comparisons the count's whole read. -/
theorem siteCount_read (s : Pos × Pos) (hn hd q : Pos)
    (h : siteCount s hn hd = some q) :
    hn * s.2 * q ≤ s.1 * hd ∧ s.1 * hd < hn * s.2 * ground.succ q :=
  groundreads.scaleCount_read s.1 (hn * s.2) hd q h

/-- A vacant site count prices the extent below one step of the
cleared height. -/
theorem siteCount_vac (s : Pos × Pos) (hn hd : Pos)
    (h : siteCount s hn hd = none) : s.1 * hd < hn * s.2 :=
  groundreads.scaleCount_vac s.1 (hn * s.2) hd h

/-- The site counts read one value at a scale bracket's two ends,
support by support. -/
def countsStable (D : Datum) (ln ld un ud : Pos) : Prop :=
  (D.supports.all (fun s =>
    decide (siteCount s ln ld = siteCount s un ud))) = true

instance (D : Datum) (ln ld un ud : Pos) :
    Decidable (countsStable D ln ld un ud) :=
  inferInstanceAs (Decidable (_ = _))

/-- One support's count at a scale between the bracket's two ends
is the ends' one value: the vacant count carries through the low
end's step, and an occupied count through the high end's fit with
the low end's refusal of one further multiple
(`groundreads.scaleCount_stable`, `scaleCount_stable_vac`). -/
private theorem stableAt (ln ld un ud en ed : Pos)
    (hlo : ln * ed ≤ en * ld) (hhi : en * ud ≤ un * ed)
    (s : Pos × Pos) (hs : siteCount s ln ld = siteCount s un ud) :
    siteCount s en ed = siteCount s ln ld := by
  have hlo' : ln * s.2 * ed ≤ en * s.2 * ld := by
    rw [ground.mul_right_comm ln s.2 ed, ground.mul_right_comm en s.2 ld]
    exact ground.mul_le_mul_right s.2 hlo
  have hhi' : en * s.2 * ud ≤ un * s.2 * ed := by
    rw [ground.mul_right_comm en s.2 ud, ground.mul_right_comm un s.2 ed]
    exact ground.mul_le_mul_right s.2 hhi
  cases hA : siteCount s ln ld with
  | none =>
    exact groundreads.scaleCount_stable_vac s.1 (ln * s.2) ld (en * s.2) ed
      hlo' (siteCount_vac s ln ld hA)
  | some q =>
    rw [hA] at hs
    exact groundreads.scaleCount_stable s.1 (ln * s.2) ld (en * s.2) ed
      (un * s.2) ud q hlo' hhi' (siteCount_read s un ud q hs.symm).1
      (siteCount_read s ln ld q hA).2

/-- The stabilization walked along the support list. -/
private theorem stableGo (ln ld un ud en ed : Pos)
    (hlo : ln * ed ≤ en * ld) (hhi : en * ud ≤ un * ed) :
    ∀ l : List (Pos × Pos),
      (l.all (fun s =>
        decide (siteCount s ln ld = siteCount s un ud))) = true →
      l.map (fun s => siteCount s en ed)
        = l.map (fun s => siteCount s ln ld)
  | [], _ => rfl
  | s :: t, h => by
    have h2 := ground.andSplitB (show
      (decide (siteCount s ln ld = siteCount s un ud)
        && t.all (fun s =>
          decide (siteCount s ln ld = siteCount s un ud))) = true from h)
    show siteCount s en ed :: t.map (fun s => siteCount s en ed)
      = siteCount s ln ld :: t.map (fun s => siteCount s ln ld)
    rw [stableAt ln ld un ud en ed hlo hhi s (of_decide_eq_true h2.1),
      stableGo ln ld un ud en ed hlo hhi t h2.2]

/-- The site counts stabilize with the height's brackets: at a
height bracket whose two ends read the datum's counts at one value,
every height between reads them at that value, one integer per
support across the bracket (`thm:groundreads`(vii)'s scale count,
one integer across a scale bracket whose two ends read it). -/
theorem counts_stable (D : Datum) (ln ld un ud en ed : Pos)
    (hlo : ln * ed ≤ en * ld) (hhi : en * ud ≤ un * ed)
    (h : countsStable D ln ld un ud) :
    siteCounts D en ed = siteCounts D ln ld :=
  stableGo ln ld un ud en ed hlo hhi D.supports h

/-- The corner line's site at the head pencil is the level gap's site
at the line's gap level: at the ground level `⟨gx : gy⟩` tying the
gap to the pencil and the line `⟨tx : ty⟩` tying to its gap level
`tn` cross-added, the two site matrices read one value — the
difference site of the two levels the gap level's scalar copy
(`certconstruct.siteDiff_scalar`) withdrawn at the balanced double
of the gap's site. -/
private theorem site_shift {n : Nat} (H Et : Mat) (hH : sqAt H n)
    (hEsq : sqAt Et n) (gx gy tx ty tn : Pos)
    (hEt : matOneValue Et
      (siteDatum (matAdd H (matScale gy (idMat n))) (matScale gx (idMat n))))
    (htt : tn + (ty + gx) = tx + gy) :
    matOneValue
      (siteDatum (matAdd H (matScale ty (idMat n))) (matScale tx (idMat n)))
      (siteDatum (matScale Pos.one Et) (matScale tn (idMat n))) := by
  rw [matScale_one]
  have hI : sqAt (idMat n) n := sqAt_idMat n
  have hEg : sqAt (siteDatum (matAdd H (matScale gy (idMat n)))
      (matScale gx (idMat n))) n :=
    sqAt_siteDatum n _ _
      (sqAt_matAdd n H _ hH (sqAt_matScale n gy _ hI))
      (sqAt_matScale n gx _ hI)
  have hL : sqAt (siteDatum (matAdd H (matScale ty (idMat n)))
      (matScale tx (idMat n))) n :=
    sqAt_siteDatum n _ _
      (sqAt_matAdd n H _ hH (sqAt_matScale n ty _ hI))
      (sqAt_matScale n tx _ hI)
  have hN : sqAt (matAdd
      (siteDatum (matAdd H (matScale gy (idMat n))) (matScale gx (idMat n)))
      (matSwap (siteDatum (matAdd H (matScale gy (idMat n)))
        (matScale gx (idMat n))))) n :=
    sqAt_matAdd n _ _ hEg (sqAt_matSwap n _ hEg)
  have hS := siteDiff_scalar H (idMat n) hH hI gx gy tx ty tn
    (by rw [ground.add_comm (gx + ty) tn, ground.add_comm gx ty]; exact htt)
  have hS' := matSwap_congr hS
  rw [show siteDatum
      (siteDatum (matAdd H (matScale gy (idMat n))) (matScale gx (idMat n)))
      (siteDatum (matAdd H (matScale ty (idMat n))) (matScale tx (idMat n)))
    = matAdd
      (siteDatum (matAdd H (matScale gy (idMat n))) (matScale gx (idMat n)))
      (matSwap (siteDatum (matAdd H (matScale ty (idMat n)))
        (matScale tx (idMat n)))) from rfl,
    matSwap_matAdd, matSwap_matSwap] at hS'
  refine matOne_trans (matOne_symm (matAdd_nullL _ _
    (matNull_add_swap _)
    ((sqAt_len hN).trans (sqAt_len hL).symm)
    (rowsLen_of_sqAt hN) (rowsLen_of_sqAt hL))) ?_
  rw [matAdd_assoc]
  have hTn : sqAt (matSwap (matScale tn (idMat n))) n :=
    sqAt_matSwap n _ (sqAt_matScale n tn _ hI)
  refine matOne_trans ?_ (matAdd_cong2 n _ _ _ _
    (rowsLen_of_sqAt hEg) (rowsLen_of_sqAt hTn) (rowsLen_of_sqAt hEsq)
    (rowsLen_of_sqAt hTn) (matOne_symm hEt) (matOne_refl _))
  rw [matAdd_comm
    (siteDatum (matAdd H (matScale gy (idMat n))) (matScale gx (idMat n))),
    matAdd_comm
    (siteDatum (matAdd H (matScale gy (idMat n))) (matScale gx (idMat n)))]
  exact matAdd_cong2 n _ _ _ _
    (rowsLen_of_sqAt (sqAt_matAdd n _ _ (sqAt_matSwap n _ hEg) hL))
    (rowsLen_of_sqAt hEg) (rowsLen_of_sqAt hTn) (rowsLen_of_sqAt hEg)
    hS' (matOne_refl _)

/-- The cell's cut in the corner scale (`thm:continuum`(ii)): at a
head pencil over the unit gram whose level gap ties to the ground
level `⟨gx : gy⟩` (`def:pencil`'s `ε₀ G + Ẽ = H`), a corner line at
count one — the second root at or beyond the line, the ground its one
root below — reads the gap's count one at the line's gap level
through the site shift and the shared count
(`inertia.rev_exchange`), the count identity's certificate at that
level reads the located roots below it as one, the kernel root
alone (`split.kernel_le_below` from below, `split.rootsBelow_mono`
from above), and the cut tie holds at every edge at or below the
line's gap level (`flatstep.cutTie_of_edge`; `lem:speccut`'s
tie). -/
theorem cell_cut {n : Nat} (H Et : Mat) (gx gy : Pos)
    (hEt : matOneValue Et
      (siteDatum (matAdd H (matScale gy (idMat n))) (matScale gx (idMat n))))
    (T Tw : SqMat n) (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hker : split.rootsAtKernel (l.map (fun r => (r.1, r.2.1))) = 1)
    (tx ty tn : Pos) (spt spt' : Split n)
    (ht : countAtPair H (idMat n) tx ty 1 spt)
    (htt : tn + (ty + gx) = tx + gy)
    (hct : split.countRead Et (idMat n) (l.map (fun r => (r.1, r.2.1)))
      tn Pos.one spt')
    (E0 p q : Pos) (het : E0 * p * Pos.one ≤ tn * q) (sp : Split n)
    (hsp : splitRead (siteDatum (matScale q (matMul Et Et))
        (matScale (E0 * p) Et)) sp) :
    speccut.cutTie Et (l.map (fun r => (r.1, r.2.1))) E0 p q sp := by
  have hsite := site_shift H Et ht.1 hd.1 gx gy tx ty tn hEt htt
  have hsq' : sqAt (siteDatum (matScale Pos.one Et)
      (matScale tn (idMat n))) n :=
    sqAt_siteDatum n _ _ (sqAt_matScale n Pos.one Et hd.1)
      (sqAt_matScale n tn _ (sqAt_idMat n))
  have hspt : splitRead (siteDatum (matScale Pos.one Et)
      (matScale tn (idMat n))) spt :=
    splitRead_congr _ _ hsq' hsite spt ht.2.2.1
  have hrev : revAt spt' = 1 :=
    (rev_exchange _ spt' spt hct.2.2.2.2.1 hspt).trans ht.2.2.2
  have htop : split.rootsBelow (l.map (fun r => (r.1, r.2.1))) tn Pos.one
      = 1 :=
    hct.2.2.2.2.2.symm.trans hrev
  have hedge : split.rootsBelow (l.map (fun r => (r.1, r.2.1)))
      (E0 * p) q = 1 :=
    Nat.le_antisymm
      (Nat.le_trans (split.rootsBelow_mono _ (E0 * p) q tn Pos.one het)
        (Nat.le_of_eq htop))
      (Nat.le_trans (Nat.le_of_eq hker.symm)
        (split.kernel_le_below _ (E0 * p) q))
  exact flatstep.cutTie_of_edge Et T Tw l E0 p q 1 hd hker hedge sp hsp

/-- The edge reaches the floor's clearance: at the ground at or below
the lower line `⟨lx : ly⟩` and the top line `⟨tx : ty⟩` at its gap
level `tn`, the gap level clears the two lines' gap cross-added —
the edge of `cell_cut` at the line reaches the lines' gap, the
member line's height over the lower rate's line the cell's floor
(`lem:cornerpivot`(vi)). -/
theorem edge_floor (gx gy lx ly tx ty tn : Pos)
    (htt : tn + (ty + gx) = tx + gy) (hlow : gx + ly ≤ lx + gy) :
    tx + ly ≤ tn + (ty + lx) := by
  have key : ∀ g : Pos, gx + ly + g = lx + gy →
      tx + ly + g = tn + (ty + lx) := by
    intro g hg
    apply ground.add_right_cancel (c := gy)
    rw [ground.add_right_comm (tx + ly) g gy, ground.add_right_comm tx ly gy,
      ← htt, ground.add_assoc (tn + (ty + gx)) ly g,
      ground.add_assoc tn (ty + gx) (ly + g), ground.add_assoc ty gx (ly + g),
      ← ground.add_assoc gx ly g, hg, ← ground.add_assoc ty lx gy,
      ← ground.add_assoc tn (ty + lx) gy]
  match hlow with
  | Or.inl he =>
    exact Or.inl (by
      apply ground.add_right_cancel (c := gy)
      rw [ground.add_right_comm tx ly gy, ← htt,
        ground.add_assoc tn (ty + gx) ly, ground.add_assoc ty gx ly, he,
        ← ground.add_assoc ty lx gy, ← ground.add_assoc tn (ty + lx) gy])
  | Or.inr ⟨g, hg⟩ => exact Or.inr ⟨g, key g hg⟩

end continuum
