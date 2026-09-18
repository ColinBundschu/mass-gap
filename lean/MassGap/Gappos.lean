import MassGap.Flatstep
import MassGap.Cellcount
import MassGap.Truncation
import MassGap.Decimation
import MassGap.Freecell
/-!
`thm:gappos` clause (v) — the counting sandwich at a cell's two
couplings.

At couplings `v, v'` of one cell whose pencils' site datum `S` at
`H = H' + S` is capped two-sidedly at `ρG` — `ρG − S ⪰ 0` and
`ρG + S ⪰ 0`, the cap's two splits (`inertia.capAt`) — every count
obeys `count_v⟨a : ρ⟩ ≤ count_{v'}(a) ≤ count_v(a + ρ)`:
`sandwich_lo` reads the level's second member cross-added by the
width and `sandwich_hi` the first member's, each a monotone read of
`lem:inertia` at one of the cap's two splits, the difference datum
the cap's own carried across an entrywise tie (the balanced copies
`P + P̌` at the memberwise swap sitting at the sum's unit).

`flat_transport` travels a jump bracket between the two couplings at
that width: a flat window of `thm:flatstep` at the coupling `v`
whose margin exceeds twice the width — `hx + ρ + (ty + ρ) < tx + hy`
— transports to a flat window at `v'` at the crossed anchor and the
crossed top.  The margin names the crossed pair's own distance,
its difference read the stated split, and the two crossed counts
are squeezed onto the window's count between the two sandwich
comparisons and the monotone read along that distance
(`certconstruct.countAtPair_cross`,
`certconstruct.countAtPair_mono`).

The cell tier carries clause (iv)'s per-cell reads at
`lem:freecell`'s carrier on the decimated head.  A `Cell` is one
located segment of the root coordinate with its fixed level pair
`⟨ax : ay⟩ < ⟨tx : ty⟩` at the gap witness `gp`, the tower places
`tw` with the dominance read's bound `[dN : dD]`, the two level
carriers' pivot covers over the segment at the decimated head
(`decimation.towerHead`, the tower block's deflation cleared once at the
head's order `o − k` and the clearing `(k + 1)·2`, the carrier itself
at a vacant tower), and one sample point at the ground count
`g ≥ 1` on both deflated carriers with its two splits; `cellRead` is
the cell's decidable read, the covers and counts joined to the tower
places' frame and both carriers' dominance reads over the segment
(`decimation.domRead`), and `cellsRead` the list's from a stated
point, each cell's segment containing the running point and the next
cell read from its top, so two consecutive segments overlap and the
list's closed union is the segments' union (`cellsTop` the last top,
`locateCell` the point's cell, the first whose top is at or beyond
it).  On a cell the flat window holds at every root-coordinate point
of the segment (`cell_flat`): at the point `[n : c]` the ray
`[c² : n²]`'s pencil `pencil.rayH` reads count `g` at both levels
scaled by the clearing `c²`, each count the sample's read through
the tower's decimation, the tower block positive definite at the
point by the dominance read (`decimation.dom_segment`,
`decimation.dom_pd`), the count the deflated head's
(`inertia.rev_placesP` at `cellcount.evalPC_pdeflP`) and the head's
count one integer over the segment (`cellcount.cellCountP`,
`freecell.freePMat_eval` the bridge), and the level order keeps.
`locate_read` places every point from the list's foot to its top
in its located cell's segment, the fold locating the point by the
composite order's totality, and `point_flat` is the root
coordinate's rays' direct read (clause (v)): the located cell's
flat window at the ray's pencil.  The pair `κ = [kn : kd]` enters
against every cell's level gap at the module count as `gapsAt`, the
list's decidable fold read at a member by `gapsAt_mem`.

The ray tier reads clause (v)'s further pair rays.  A ray `[α : β]`
off the root coordinate reads its window at the root-coordinate
ray `[q² : p²]`: `rayP` is the least natural at the squared
comparison `βq² ≤ (p+1)²α`, one decidable read over the keys at or
below the weight `βq²` (`rayPred` at the key's successor, `rayK` the
least key, `ground.firstAt`; `rayKD` its fast read, the halving
search `ground.bisectFrom` at the comparison stepping up the keys, one
key with the walk by `rayKD_eq`), so `p²α < βq² ≤ (p+1)²α`; `rayGap` is
the weights' gap `βq²` against `p²α`, the margin read
(`BPair.marginPos`, `def:ground`'s difference), at or below
`(2p+1)α`; `rayRho` the sandwich's width, the gap's multiple of the
magnetic member's cap `W` (`thm:truncation`'s cap at the unit
magnetic weight); `rayCell` the neighbor `[p : q]`'s cell in the
list; and `rayGp` the transported window's level gap, the cell's gap
at the scale `αq²` less twice the width.  `ray_core` is the
transport at any scale `q` beyond `α` and at or beyond
`4W(2τ* + 1)`, `τ*` a natural at or beyond the list's top: the two
pencils' site datum `αH([q² : p²]) − q²H([α : β])` is the gap's
multiple of the magnetic member, capped two-sidedly at `ρ = rayGap·W`
against the gram (`inertia.capAt_scale` at the member's cap), the
cell's window at `[p : q]` scaled by `α` (`flatstep.vacFlat_scale`)
has its margin beyond twice the width, the width sitting at or below
a quarter of the cell's gap at that scale, and `flat_transport`
carries the window to the ray's pencil at the scale `q²` at the
levels shifted by `ρ`, the transported gap `rayGp` at or beyond half
the cell's, so at a pair `κ` doubled under the cells' gaps (`gapsAt`
at `2 kn`) the ray's cut holds `ακ` at its representative,
`E₀ ακ ≤ rayGp` at the scale `q²`; `ray_flat` is its instance at the
stated scale `rayQ = (α + 1)·4W(2τ* + 1)`.

The cutoff's price closes at the cut (clause (iii)): at
`thm:truncation`'s cap and polarization tie, a window whose
compression reads the cut at the level raised by the cofactor width
reads the cut itself at the level — the counting comparison of
`truncation.count_shift_le` at the compression's vacant count, the
removed block's vacancy derived at the admissible cutoff's data
(`truncCut`), the bracket display
`E₀ς𝒦_(Λ,C) ≤ E₀ς𝒦reg_Λ(v) + β²#p²d_L²` at the fixed region
and the stated simple-ground cutoff tail.
The flat window itself transports across the truncation at the
priced width (`flat_shift`): the head's flat window from the anchor
to the top reads at the whole window at the anchor and at the top
lowered by the shift cap, the anchor's count squeezed between the
compression side and the shift side at the anchor raised by the cap
(the head flat there by the monotone read), the lowered top's between
the shift side at the crossed top and the anchor's own, the removed
block vacant at both levels at its floor, and the level order kept at
the width beyond the cap; and it compresses the other way
(`flat_compress`), the whole window's flat window reading at the head
from the anchor raised by the cap to the top, the tex's two cuts'
values bracketing each other at the priced width.

The window reaches the cut (clauses (iii) and (v), `thm:flatstep`'s
identification at `lem:speccut`): at one located root list read
both ways — the count identity's factorization and the
diagonalizing congruence, `lem:split`'s one list — a flat window
whose two counts read the list's ground multiplicity brackets the
edge between its ends, the below count squeezed by the level
monotonicity, and the spectral read closes the cut at any stated
split of the cut's site datum (`windowCut`, landing
`speccut.cutTie` whole through `flatstep.flat_spec` and
`speccut.spec_to_cut`).

The priced cap tier reads (v)'s cap at the identity gram per
decimated head: `magCap`, the entrywise magnitude cap as a
decidable read, and `capId_lo`/`capId_hi`, the site datum of the
scaled identity against an entrywise-capped symmetric datum and
their sum, every split positive semidefinite at the count's
clearing `o·e ≤ ρ` — the dominance comparison priced by the cap
over the peeled rows (`decimation.dom_unit` at the joined row's
fold, the cap rejoined at the diagonal key) with `lem:inertia`'s
witness refused.
-/

namespace gappos
open ground elim inertia certconstruct flatstep

/-- The entrywise sum's congruence at one order, the four row frames
the square reads' own. -/
private theorem addCongS {o : Nat} (A B A' B' : Mat) (hA : sqAt A o)
    (hB : sqAt B o) (hA' : sqAt A' o) (hB' : sqAt B' o)
    (h1 : matOneValue A A') (h2 : matOneValue B B') :
    matOneValue (matAdd A B) (matAdd A' B') :=
  elim.matAdd_cong2 o A B A' B' (elim.rowsLen_of_sqAt hA)
    (elim.rowsLen_of_sqAt hB) (elim.rowsLen_of_sqAt hA')
    (elim.rowsLen_of_sqAt hB') h1 h2

/-- The two-level site difference: the first pencil's datum at its
level against the second's at its own, rearranged to the pencils'
difference beside the levels' four gram copies. -/
private theorem genSite (A B G : Mat) (x y x' y' : Pos) :
    siteDatum
        (siteDatum (matAdd A (matScale y G)) (matScale x G))
        (siteDatum (matAdd B (matScale y' G)) (matScale x' G))
      = matAdd
          (matAdd (matAdd A (matSwap B))
            (matAdd (matScale y G) (matSwap (matScale y' G))))
          (matAdd (matSwap (matScale x G)) (matScale x' G)) := by
  show matAdd (matAdd (matAdd A (matScale y G)) (matSwap (matScale x G)))
      (matSwap (matAdd (matAdd B (matScale y' G))
        (matSwap (matScale x' G))))
    = matAdd
        (matAdd (matAdd A (matSwap B))
          (matAdd (matScale y G) (matSwap (matScale y' G))))
        (matAdd (matSwap (matScale x G)) (matScale x' G))
  rw [elim.matSwap_matAdd (matAdd B (matScale y' G))
      (matSwap (matScale x' G)),
    elim.matSwap_matAdd B (matScale y' G),
    elim.matSwap_matSwap (matScale x' G),
    elim.matAdd_shuffle (matAdd A (matScale y G)) (matSwap (matScale x G))
      (matAdd (matSwap B) (matSwap (matScale y' G))) (matScale x' G),
    elim.matAdd_shuffle A (matScale y G) (matSwap B)
      (matSwap (matScale y' G))]

/-- The lower comparison's difference datum: the `v`-datum at the
level's second member raised by the width against the `v'`-datum at
the level itself, the pencils' difference and the width's gram
copy standing beside the level's and the first member's balanced
copies. -/
private theorem loSite (H H' G : Mat) (rho x y : Pos) :
    siteDatum
        (siteDatum (matAdd H (matScale (y + rho) G)) (matScale x G))
        (siteDatum (matAdd H' (matScale y G)) (matScale x G))
      = matAdd
          (matAdd
            (matAdd (matAdd H (matSwap H')) (matScale rho G))
            (matAdd (matScale y G) (matSwap (matScale y G))))
          (matAdd (matSwap (matScale x G)) (matScale x G)) := by
  rw [genSite H H' G x (y + rho) x y, matScale_addW y rho G,
    elim.matAdd_assoc (matScale y G) (matScale rho G)
      (matSwap (matScale y G)),
    elim.matAdd_comm (matScale rho G) (matSwap (matScale y G)),
    ← elim.matAdd_assoc (matScale y G) (matSwap (matScale y G))
      (matScale rho G),
    ← elim.matAdd_assoc (matAdd H (matSwap H'))
      (matAdd (matScale y G) (matSwap (matScale y G))) (matScale rho G),
    elim.matAdd_right_comm (matAdd H (matSwap H'))
      (matAdd (matScale y G) (matSwap (matScale y G))) (matScale rho G)]

/-- The upper comparison's difference datum: the `v'`-datum against
the `v`-datum at the level's first member raised by the width, the
pencils' difference and the width's gram copy standing beside the
level's and the first member's balanced copies. -/
private theorem hiSite (H H' G : Mat) (rho x y : Pos) :
    siteDatum
        (siteDatum (matAdd H' (matScale y G)) (matScale x G))
        (siteDatum (matAdd H (matScale y G)) (matScale (x + rho) G))
      = matAdd
          (matAdd (matAdd H' (matSwap H))
            (matAdd (matScale y G) (matSwap (matScale y G))))
          (matAdd (matAdd (matSwap (matScale x G)) (matScale x G))
            (matScale rho G)) := by
  rw [genSite H' H G x y (x + rho) y, matScale_addW x rho G,
    ← elim.matAdd_assoc (matSwap (matScale x G)) (matScale x G)
      (matScale rho G)]

/-- The pencils' difference at the coupling `v`'s own side: at
`H = H' + S` the first pencil against the second's swap reads the
site datum. -/
private theorem tieLo {o : Nat} (H H' S : Mat) (hH : sqAt H o)
    (hH' : sqAt H' o) (hS : sqAt S o)
    (hHe : matOneValue H (matAdd H' S)) :
    matOneValue (matAdd H (matSwap H')) S := by
  have hsw : sqAt (matSwap H') o := elim.sqAt_matSwap o H' hH'
  have hbal : sqAt (matAdd H' (matSwap H')) o :=
    elim.sqAt_matAdd o H' (matSwap H') hH' hsw
  have hs1 : matOneValue (matAdd H (matSwap H'))
      (matAdd (matAdd H' S) (matSwap H')) :=
    addCongS H (matSwap H') (matAdd H' S) (matSwap H') hH hsw
      (elim.sqAt_matAdd o H' S hH' hS) hsw hHe
      (elim.matOne_refl (matSwap H'))
  rw [elim.matAdd_right_comm H' S (matSwap H')] at hs1
  exact elim.matOne_trans hs1
    (elim.matAdd_nullL (matAdd H' (matSwap H')) S
      (elim.matNull_add_swap H')
      ((elim.sqAt_len hbal).trans (elim.sqAt_len hS).symm)
      (elim.rowsLen_of_sqAt hbal) (elim.rowsLen_of_sqAt hS))

/-- The pencils' difference at the coupling `v'`'s own side, the
`v`-side read under the memberwise swap. -/
private theorem tieHi {H H' S : Mat}
    (h : matOneValue (matAdd H (matSwap H')) S) :
    matOneValue (matAdd H' (matSwap H)) (matSwap S) := by
  have hs := elim.matSwap_congr h
  rw [elim.matSwap_matAdd H (matSwap H'), elim.matSwap_matSwap H',
    elim.matAdd_comm (matSwap H) H'] at hs
  exact hs

/-- The entrywise magnitude cap (`thm:gappos`(v)'s cap pricing):
every entry's magnitude at or below the stated bound. -/
def magCap (e : BPair) (S : Mat) : Prop :=
  (S.all (fun r => r.all (fun x => decide (windowsep.mag x ≤ e)))) = true

instance instGappos1 (e : BPair) (S : Mat) : Decidable (magCap e S) :=
  inferInstanceAs (Decidable (_ = _))

/-- The cap's entry read at stated keys. -/
private theorem magCap_entry {e : BPair} {S : Mat}
    (hcap : magCap e S) (i j : Nat) (hi : i < S.length)
    (hj : j < (ground.getAt ([] : List BPair) S i).length) :
    windowsep.mag (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) S i) j) ≤ e :=
  of_decide_eq_true
    (ground.all_getAt BPair.unit _
      (ground.all_getAt ([] : List BPair) _ hcap i hi) j hj)

/-- The magnitude's swapped floor: the memberwise swap of a
magnitude sits at or below the datum. -/
private theorem swapMag_le (z : BPair) :
    (windowsep.mag z).swap ≤ z := by
  have h := ground.leB_swap (windowsep.swap_le_mag z)
  rw [ground.BPair.swap_swap] at h
  exact h

/-- The magnitudes' fold at a unit-valued companion row: the joined
row's fold prices at the count against the cap, key by key. -/
private theorem magSum_cap (e : BPair) : ∀ (r1 r2 : List BPair),
    r1.length = r2.length →
    (∀ j, j < r1.length →
      (ground.getAt BPair.unit r1 j).oneValue BPair.unit) →
    (∀ j, j < r2.length →
      windowsep.mag (ground.getAt BPair.unit r2 j) ≤ e) →
    decimation.magSum (elim.vecAdd r1 r2) ≤ BPair.ofNat r2.length * e
  | [], [], _, _, _ => Or.inl (BPair.oneValue_symm (BPair.unit_mul e))
  | [], _ :: _, hl, _, _ => nomatch hl
  | _ :: _, [], hl, _, _ => nomatch hl
  | x1 :: t1, x2 :: t2, hl, h1, h2 => by
    have hx1 : x1.oneValue BPair.unit :=
      h1 0 (Nat.succ_le_succ (Nat.zero_le t1.length))
    have hx2 : windowsep.mag x2 ≤ e :=
      h2 0 (Nat.succ_le_succ (Nat.zero_le t2.length))
    have hrec := magSum_cap e t1 t2 (Nat.succ.inj hl)
      (fun j hj => h1 (j + 1) (Nat.succ_le_succ hj))
      (fun j hj => h2 (j + 1) (Nat.succ_le_succ hj))
    have hm : (windowsep.mag (x1 + x2)).oneValue (windowsep.mag x2) :=
      windowsep.mag_congr (BPair.oneValue_trans
        (BPair.add_congr hx1 (BPair.oneValue_refl x2))
        (BPair.unit_add x2))
    show windowsep.mag (x1 + x2)
        + decimation.magSum (elim.vecAdd t1 t2)
      ≤ BPair.ofNat (t2.length + 1) * e
    refine ground.leB_congr_right
      (BPair.oneValue_symm (ground.ofNat_succ_mul t2.length e)) ?_
    rw [BPair.add_comm (windowsep.mag (x1 + x2))
      (decimation.magSum (elim.vecAdd t1 t2))]
    exact ground.leB_add hrec (ground.leB_congr_left
      (BPair.oneValue_symm hm) hx2)

/-- The off-row fold at a unit-off-key first row against a capped
second: the joined row's fold with the cap rejoined prices at the
count against the cap, the diagonal key's own budget the join's. -/
private theorem offFold_cap (e : BPair) : ∀ (i : Nat)
    (r1 r2 : List BPair), r1.length = r2.length →
    i < r1.length →
    (∀ j, j < r1.length → ¬ j = i →
      (ground.getAt BPair.unit r1 j).oneValue BPair.unit) →
    (∀ j, j < r2.length →
      windowsep.mag (ground.getAt BPair.unit r2 j) ≤ e) →
    decimation.offFold i (elim.vecAdd r1 r2) + e
      ≤ BPair.ofNat r2.length * e
  | i, [], [], _, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | _, [], _ :: _, hl, _, _, _ => nomatch hl
  | _, _ :: _, [], hl, _, _, _ => nomatch hl
  | 0, _ :: t1, _ :: t2, hl, _, h1, h2 => by
    show decimation.magSum (elim.vecAdd t1 t2) + e
      ≤ BPair.ofNat (t2.length + 1) * e
    refine ground.leB_congr_right
      (BPair.oneValue_symm (ground.ofNat_succ_mul t2.length e)) ?_
    exact ground.leB_add
      (magSum_cap e t1 t2 (Nat.succ.inj hl)
        (fun j hj => h1 (j + 1) (Nat.succ_le_succ hj)
          (fun hh => Nat.noConfusion hh))
        (fun j hj => h2 (j + 1) (Nat.succ_le_succ hj)))
      (ground.leB_refl e)
  | i + 1, x1 :: t1, x2 :: t2, hl, hi, h1, h2 => by
    have hx1 : x1.oneValue BPair.unit :=
      h1 0 (Nat.succ_le_succ (Nat.zero_le t1.length))
        (fun hh => Nat.noConfusion hh)
    have hx2 : windowsep.mag x2 ≤ e :=
      h2 0 (Nat.succ_le_succ (Nat.zero_le t2.length))
    have hm : (windowsep.mag (x1 + x2)).oneValue (windowsep.mag x2) :=
      windowsep.mag_congr (BPair.oneValue_trans
        (BPair.add_congr hx1 (BPair.oneValue_refl x2))
        (BPair.unit_add x2))
    have hrec := offFold_cap e i t1 t2 (Nat.succ.inj hl)
      (Nat.lt_of_succ_lt_succ hi)
      (fun j hj hne => h1 (j + 1) (Nat.succ_le_succ hj)
        (fun hh => hne (Nat.succ.inj hh)))
      (fun j hj => h2 (j + 1) (Nat.succ_le_succ hj))
    show windowsep.mag (x1 + x2)
        + decimation.offFold i (elim.vecAdd t1 t2) + e
      ≤ BPair.ofNat (t2.length + 1) * e
    refine ground.leB_congr_right
      (BPair.oneValue_symm (ground.ofNat_succ_mul t2.length e)) ?_
    have hasm : decimation.offFold i (elim.vecAdd t1 t2) + e
        + windowsep.mag (x1 + x2)
      ≤ BPair.ofNat t2.length * e + e :=
      ground.leB_add hrec
        (ground.leB_congr_left (BPair.oneValue_symm hm) hx2)
    have heq : decimation.offFold i (elim.vecAdd t1 t2) + e
          + windowsep.mag (x1 + x2)
        = windowsep.mag (x1 + x2)
          + decimation.offFold i (elim.vecAdd t1 t2) + e := by
      rw [BPair.add_comm (decimation.offFold i (elim.vecAdd t1 t2) + e)
        (windowsep.mag (x1 + x2)),
        BPair.add_assoc (windowsep.mag (x1 + x2))
          (decimation.offFold i (elim.vecAdd t1 t2)) e]
    exact ground.leB_congr_left (BPair.oneValue_of_eq heq) hasm

/-- The scaled identity's entry at stated keys, the indicator's
own scale. -/
private theorem entry_scaleId (o : Nat) (rho : ground.Pos)
    (i j : Nat) (hi : i < o) (hj : j < o) :
    ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (matScale rho (idMat o)) i) j
      = (if j = i then BPair.ofNat 1 else BPair.unit).scale rho := by
  have hil : i < (idMat o).length := by
    rw [show (idMat o).length = o from
      ground.length_mapRange (elim.idRow o) o]
    exact hi
  have hjl : j < (ground.getAt ([] : List BPair) (idMat o) i).length := by
    rw [elim.idMat_row o i hi, elim.length_idRow o i]
    exact hj
  show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
      ((idMat o).map (fun r => r.map (fun x => x.scale rho))) i) j
    = (if j = i then BPair.ofNat 1 else BPair.unit).scale rho
  rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
      (fun r => r.map (fun x => x.scale rho)) (idMat o) i hil,
    ground.getAt_map BPair.unit BPair.unit
      (fun x => x.scale rho) _ j hjl,
    elim.getAt_idMat o i j hi hj]

/-- The scaled identity keeps the stated order. -/
private theorem sqAt_scaleId (o : Nat) (rho : ground.Pos) :
    sqAt (matScale rho (idMat o)) o :=
  inertia.sqAt_matScale o rho (idMat o)
    (elim.sqAt_idMat o)

/-- The joined pencil at the scaled identity keeps the entrywise
symmetry: both summands keep their own and the sum keeps theirs. -/
private theorem symAdd (o : Nat) (S : Mat) (rho : ground.Pos)
    (hS : sqAt S o) (hsym : symmRead S) :
    symmRead (matAdd (matScale rho (idMat o)) S) := by
  have hsI : matOneValue (transposeM (matScale rho (idMat o)))
      (matScale rho (idMat o)) :=
    elim.matOne_trans
      (inertia.transposeM_matScale rho o (idMat o)
        (elim.rowsLen_of_sqAt (elim.sqAt_idMat o)))
      (inertia.matScale_matOne rho
        (by rw [elim.transposeM_idMat o]; exact elim.matOne_refl _))
  exact elim.matOne_symm
    (elim.transposeM_matAdd_sym (matScale rho (idMat o)) S
      (sqAt_scaleId o rho) hS hsI (elim.matOne_symm hsym))

/-- The priced cap's quadratic floor at the scaled identity: the
joined datum's form clears the vacant fold at every stated vector,
the dominance comparison priced by the cap. -/
private theorem capQuad (o : Nat) (S : Mat) (e : BPair)
    (rho : ground.Pos)
    (hS : sqAt S o) (hsym : symmRead S)
    (hcap : magCap e S)
    (hcl : BPair.ofNat o * e ≤ BPair.ofPos rho)
    (u : List BPair) (hu : u.length = o) :
    elim.dotN (List.replicate o BPair.unit)
        (List.zipWith (· * ·) u u)
      ≤ elim.dotN u (elim.matVec
        (matAdd (matScale rho (idMat o)) S) u) := by
  have hIsq := sqAt_scaleId o rho
  have hSl : S.length = o := elim.sqAt_len hS
  have hIl : (matScale rho (idMat o)).length = o := elim.sqAt_len hIsq
  have hdom : ∀ i, i < o →
      decimation.offFold i (ground.getAt ([] : List BPair)
          (matAdd (matScale rho (idMat o)) S) i)
      ≤ ground.getAt BPair.unit (ground.getAt ([] : List BPair)
          (matAdd (matScale rho (idMat o)) S) i) i := by
    intro i hi
    have hrow := elim.getAt_matAdd (matScale rho (idMat o)) S i
      (by rw [hIl]; exact hi) (by rw [hSl]; exact hi)
    have hrXl : (ground.getAt ([] : List BPair)
        (matScale rho (idMat o)) i).length = o :=
      elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hIsq)
        (by rw [hIl]; exact hi)
    have hrSl : (ground.getAt ([] : List BPair) S i).length = o :=
      elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hS)
        (by rw [hSl]; exact hi)
    rw [hrow,
      elim.getAt_vecAdd _ _ i (by rw [hrXl]; exact hi)
        (by rw [hrSl]; exact hi),
      entry_scaleId o rho i i hi hi, if_pos rfl]
    have hcapRow : ∀ j, j < (ground.getAt ([] : List BPair)
          S i).length →
        windowsep.mag (ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) S i) j) ≤ e :=
      fun j hj => magCap_entry hcap i j (by rw [hSl]; exact hi) hj
    have hoff := offFold_cap e i _ _ (hrXl.trans hrSl.symm)
      (by rw [hrXl]; exact hi)
      (fun j hj hne => by
        rw [entry_scaleId o rho i j hi
          (by rw [hrXl] at hj; exact hj), if_neg hne]
        exact BPair.oneValue_symm (ground.unitScale rho))
      hcapRow
    rw [hrSl] at hoff
    have hoffr := ground.leB_trans hoff hcl
    have hmv : decimation.offFold i (elim.vecAdd
          (ground.getAt ([] : List BPair) (matScale rho (idMat o)) i)
          (ground.getAt ([] : List BPair) S i))
        ≤ BPair.ofPos rho + e.swap := by
      refine ground.leB_congr_left ?_
        (ground.leB_add hoffr (ground.leB_refl e.swap))
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_assoc _ e e.swap)) ?_
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_swap_null e))
        (BPair.add_unit _)
    have hswapii : e.swap ≤ ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) S i) i :=
      ground.leB_trans
        (ground.leB_swap (hcapRow i (by rw [hrSl]; exact hi)))
        (swapMag_le _)
    have hscale1 : (BPair.ofPos rho).oneValue
        ((BPair.ofNat 1).scale rho) := by
      show rho + Pos.one + Pos.one * rho
        = (Pos.one + Pos.one) * rho + Pos.one
      rw [ground.right_distrib Pos.one Pos.one rho,
        ground.one_mul rho, ground.add_assoc rho Pos.one rho,
        ground.add_comm Pos.one rho,
        ← ground.add_assoc rho rho Pos.one]
    exact ground.leB_trans hmv
      (ground.leB_add (Or.inl hscale1) hswapii)
  have hDsq : sqAt (matAdd (matScale rho (idMat o)) S) o :=
    elim.sqAt_matAdd o _ S hIsq hS
  refine ground.leB_congr_left
    (BPair.oneValue_symm (elim.dotN_nullL (List.replicate o BPair.unit)
      (List.zipWith (· * ·) u u) (poly.unitTail_replicate o))) ?_
  exact decimation.dom_unit (matAdd (matScale rho (idMat o)) S) hDsq
    (symAdd o S rho hS hsym)
    (decimation.domAt_of_rows (n := o) _ (elim.sqAt_len hDsq) hdom) u hu

/-- The entrywise cap at the memberwise swap, the magnitudes
swap-blind. -/
private theorem magCap_swap {e : BPair} {S : Mat} (h : magCap e S) :
    magCap e (elim.matSwap S) := by
  refine ground.all_of_getAt ([] : List BPair) _ (elim.matSwap S)
    (fun i hi => ?_)
  have hil : i < S.length := by
    rw [← elim.length_matSwap S]
    exact hi
  show (ground.getAt ([] : List BPair)
      (S.map (fun r => r.map BPair.swap)) i).all
      (fun x => decide (windowsep.mag x ≤ e)) = true
  rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
    (fun r => r.map BPair.swap) S i hil]
  refine ground.all_of_getAt BPair.unit _ _ (fun j hj => ?_)
  have hjl : j < (ground.getAt ([] : List BPair) S i).length := by
    rw [← ground.length_map BPair.swap
      (ground.getAt ([] : List BPair) S i)]
    exact hj
  rw [ground.getAt_map BPair.unit BPair.unit BPair.swap _ j hjl,
    windowsep.mag_swap]
  exact ground.all_getAt BPair.unit _
    (ground.all_getAt ([] : List BPair) _ h i hil) j hjl

/-- (`thm:gappos`(v)'s priced cap, the upper side at the identity
gram): the scaled identity joined to an entrywise-capped symmetric
datum reads every split positive semidefinite at the count's
clearing. -/
theorem capId_hi (o : Nat) (S : Mat) (e : BPair)
    (rho : ground.Pos) (sp : Split o)
    (hS : sqAt S o) (hsym : symmRead S)
    (hcap : magCap e S)
    (hcl : BPair.ofNat o * e ≤ BPair.ofPos rho)
    (h : splitRead (matAdd (matScale rho (idMat o)) S) sp) :
    psdAt sp := by
  cases Nat.eq_zero_or_pos (revAt sp) with
  | inl h0 => exact h0
  | inr hpos =>
    obtain ⟨u, hu, hlt⟩ := rev_witness _ sp h hpos
    exact absurd hlt (ground.leB_not_lt
      (ground.leB_congr_left
        (elim.dotN_nullL (List.replicate o BPair.unit)
          (List.zipWith (· * ·) u u) (poly.unitTail_replicate o))
        (capQuad o S e rho hS hsym hcap hcl u hu)))

/-- (`thm:gappos`(v)'s priced cap, the lower side at the identity
gram): the site datum of the scaled identity against an
entrywise-capped symmetric datum reads every split positive
semidefinite at the count's clearing. -/
theorem capId_lo (o : Nat) (S : Mat) (e : BPair)
    (rho : ground.Pos) (sp : Split o)
    (hS : sqAt S o) (hsym : symmRead S)
    (hcap : magCap e S)
    (hcl : BPair.ofNat o * e ≤ BPair.ofPos rho)
    (h : splitRead (siteDatum (matScale rho (idMat o)) S) sp) :
    psdAt sp :=
  capId_hi o (elim.matSwap S) e rho sp
    (elim.sqAt_matSwap o S hS) (elim.symmRead_matSwap S hsym)
    (magCap_swap hcap) hcl h

/-- The sandwich's lower comparison (`thm:gappos`(v)): at couplings
of one cell whose site datum `S` at `H = H' + S` is capped
two-sidedly at `ρG`, the count at `v` of the level with its second
member raised by the width sits at or below the count at `v'` of the
level itself — `count_v⟨a : ρ⟩ ≤ count_{v'}(a)`, the monotone read
of `lem:inertia` at the cap's lower split. -/
theorem sandwich_lo {o : Nat} (H H' S G : Mat) (rho x y : Pos)
    (n n' : Nat) (sp sp' spU spL : Split o)
    (hHe : matOneValue H (matAdd H' S))
    (hcap : capAt S (matScale rho G) spU spL)
    (h : countAtPair H G x (y + rho) n sp)
    (h' : countAtPair H' G x y n' sp') :
    n ≤ n' := by
  have hS : sqAt S o := hcap.1
  have hRG : sqAt (matScale rho G) o := hcap.2.1
  have hG : sqAt G o := h.2.1
  have hGy : sqAt (matScale y G) o := sqAt_matScale o y G hG
  have hGx : sqAt (matScale x G) o := sqAt_matScale o x G hG
  have hZy : sqAt (matAdd (matScale y G) (matSwap (matScale y G))) o :=
    elim.sqAt_matAdd o _ _ hGy (elim.sqAt_matSwap o (matScale y G) hGy)
  have hZx : sqAt (matAdd (matSwap (matScale x G)) (matScale x G)) o :=
    elim.sqAt_matAdd o _ _ (elim.sqAt_matSwap o (matScale x G) hGx) hGx
  have hP : sqAt (matAdd H (matSwap H')) o :=
    elim.sqAt_matAdd o H (matSwap H') h.1 (elim.sqAt_matSwap o H' h'.1)
  have hW : sqAt (matAdd (matAdd H (matSwap H')) (matScale rho G)) o :=
    elim.sqAt_matAdd o _ _ hP hRG
  have hWy : sqAt (matAdd
      (matAdd (matAdd H (matSwap H')) (matScale rho G))
      (matAdd (matScale y G) (matSwap (matScale y G)))) o :=
    elim.sqAt_matAdd o _ _ hW hZy
  have hDiff : sqAt (siteDatum
      (siteDatum (matAdd H (matScale (y + rho) G)) (matScale x G))
      (siteDatum (matAdd H' (matScale y G)) (matScale x G))) o :=
    sqAt_siteDatum o _ _ h.2.2.1.1 h'.2.2.1.1
  have hfull : matOneValue (siteDatum
      (siteDatum (matAdd H (matScale (y + rho) G)) (matScale x G))
      (siteDatum (matAdd H' (matScale y G)) (matScale x G)))
      (matAdd (matScale rho G) S) := by
    rw [loSite H H' G rho x y, elim.matAdd_comm (matScale rho G) S]
    exact elim.matOne_trans
      (elim.matOne_trans
        (elim.matAdd_nullR _ _ hWy hZx
          (elim.matNull_swap_add (elim.matOne_refl (matScale x G))))
        (elim.matAdd_nullR _ _ hW hZy
          (elim.matNull_add_swap (matScale y G))))
      (addCongS (matAdd H (matSwap H')) (matScale rho G) S
        (matScale rho G) hP hRG hS hRG
        (tieLo H H' S h.1 h'.1 hS hHe) (elim.matOne_refl _))
  have hspL : splitRead (siteDatum
      (siteDatum (matAdd H (matScale (y + rho) G)) (matScale x G))
      (siteDatum (matAdd H' (matScale y G)) (matScale x G))) spL :=
    inertia.splitRead_congr _ _ hDiff (elim.matOne_symm hfull) spL
      hcap.2.2.2.1
  exact countAtPair_mono H H' G x (y + rho) x y n n' sp sp' spL
    hspL hcap.2.2.2.2 h h'

/-- The sandwich's upper comparison (`thm:gappos`(v)): at the same
cap the count at `v'` of a level sits at or below the count at `v`
of the level with its first member raised by the width —
`count_{v'}(a) ≤ count_v(a + ρ)`, `lem:inertia`'s monotone read at
the cap's upper split. -/
theorem sandwich_hi {o : Nat} (H H' S G : Mat) (rho x y : Pos)
    (n n' : Nat) (sp sp' spU spL : Split o)
    (hHe : matOneValue H (matAdd H' S))
    (hcap : capAt S (matScale rho G) spU spL)
    (h' : countAtPair H' G x y n' sp')
    (h : countAtPair H G (x + rho) y n sp) :
    n' ≤ n := by
  have hS : sqAt S o := hcap.1
  have hRG : sqAt (matScale rho G) o := hcap.2.1
  have hG : sqAt G o := h.2.1
  have hGy : sqAt (matScale y G) o := sqAt_matScale o y G hG
  have hGx : sqAt (matScale x G) o := sqAt_matScale o x G hG
  have hZy : sqAt (matAdd (matScale y G) (matSwap (matScale y G))) o :=
    elim.sqAt_matAdd o _ _ hGy (elim.sqAt_matSwap o (matScale y G) hGy)
  have hZx : sqAt (matAdd (matSwap (matScale x G)) (matScale x G)) o :=
    elim.sqAt_matAdd o _ _ (elim.sqAt_matSwap o (matScale x G) hGx) hGx
  have hP : sqAt (matAdd H' (matSwap H)) o :=
    elim.sqAt_matAdd o H' (matSwap H) h'.1 (elim.sqAt_matSwap o H h.1)
  have hDiff : sqAt (siteDatum
      (siteDatum (matAdd H' (matScale y G)) (matScale x G))
      (siteDatum (matAdd H (matScale y G)) (matScale (x + rho) G))) o :=
    sqAt_siteDatum o _ _ h'.2.2.1.1 h.2.2.1.1
  have hfull : matOneValue (siteDatum
      (siteDatum (matAdd H' (matScale y G)) (matScale x G))
      (siteDatum (matAdd H (matScale y G)) (matScale (x + rho) G)))
      (matAdd (matScale rho G) (matSwap S)) := by
    rw [hiSite H H' G rho x y,
      elim.matAdd_comm (matScale rho G) (matSwap S)]
    exact addCongS (matAdd (matAdd H' (matSwap H))
        (matAdd (matScale y G) (matSwap (matScale y G))))
      (matAdd (matAdd (matSwap (matScale x G)) (matScale x G))
        (matScale rho G))
      (matSwap S) (matScale rho G)
      (elim.sqAt_matAdd o _ _ hP hZy)
      (elim.sqAt_matAdd o _ _ hZx hRG)
      (elim.sqAt_matSwap o S hS) hRG
      (elim.matOne_trans (elim.matAdd_nullR _ _ hP hZy
          (elim.matNull_add_swap (matScale y G)))
        (tieHi (tieLo H H' S h.1 h'.1 hS hHe)))
      (elim.matAdd_nullL _ _
        (elim.matNull_swap_add (elim.matOne_refl (matScale x G)))
        ((elim.sqAt_len hZx).trans (elim.sqAt_len hRG).symm)
        (elim.rowsLen_of_sqAt hZx) (elim.rowsLen_of_sqAt hRG))
  have hspU : splitRead (siteDatum
      (siteDatum (matAdd H' (matScale y G)) (matScale x G))
      (siteDatum (matAdd H (matScale y G)) (matScale (x + rho) G))) spU :=
    inertia.splitRead_congr _ _ hDiff (elim.matOne_symm hfull) spU
      hcap.2.2.1.1
  exact countAtPair_mono H' H G x y (x + rho) y n' n sp' sp spU
    hspU hcap.2.2.1.2 h' h

/-- The jump bracket travels between the couplings at the width
(`thm:gappos`(v)): a flat window of `thm:flatstep` at the coupling
`v` whose margin absorbs the sandwich width twice over transports to
a flat window at `v'`, the anchor's level crossed in its first
member and the top's in its second.  The margin names the crossed
pair's own distance, its difference read the stated split, and each
transported count is squeezed onto the window's own: the sandwich
brackets it against the window's crossed ends and the monotone read
along the crossed pair closes the squeeze. -/
theorem flat_transport {o : Nat} (H H' S G : Mat)
    (rho hx hy tx ty : Pos) (g na nt : Nat)
    (spa spt spa' spt' spd spU spL : Split o)
    (hHe : matOneValue H (matAdd H' S))
    (hcap : capAt S (matScale rho G) spU spL)
    (hw : vacFlat H G hx hy tx ty g spa spt)
    (hmargin : hx + rho + (ty + rho) < tx + hy)
    (hd : splitRead (siteDatum
      (siteDatum (matAdd H' (matScale hy G)) (matScale (hx + rho) G))
      (siteDatum (matAdd H' (matScale (ty + rho) G)) (matScale tx G))) spd)
    (hpd : psdAt spd)
    (ha' : countAtPair H' G (hx + rho) hy na spa')
    (ht' : countAtPair H' G tx (ty + rho) nt spt') :
    vacFlat H' G (hx + rho) hy tx (ty + rho) g spa' spt' := by
  have hga : g ≤ na :=
    sandwich_lo H H' S G rho (hx + rho) hy g na spa spa' spU spL
      hHe hcap (countAtPair_cross H G rho hx hy g spa hw.1) ha'
  have hant : na ≤ nt :=
    countAtPair_mono H' H' G (hx + rho) hy tx (ty + rho) na nt
      spa' spt' spd hd hpd ha' ht'
  have htg : nt ≤ g :=
    sandwich_hi H H' S G rho tx (ty + rho) g nt spt spt' spU spL
      hHe hcap ht' (countAtPair_cross H G rho tx ty g spt hw.2.1)
  have hna : na = g := Nat.le_antisymm (Nat.le_trans hant htg) hga
  have hnt : nt = g := Nat.le_antisymm htg (Nat.le_trans hga hant)
  exact ⟨hna ▸ ha', hnt ▸ ht', hw.2.2.1, hmargin⟩

set_option genInjectivity false in
/-- One cell of the flat window's list read at its data
(`thm:gappos`(ii), (iv)): the cell's located segment `[lo, hi]` in
the root coordinate, its level pair `⟨ax : ay⟩ < ⟨tx : ty⟩` with the
gap witness, the tower places `tw` with the dominance read's bound
`[dN : dD]` (`thm:decimation`(ii)'s tower block, `lem:freecell`'s
dominance family), the two level carriers' pivot covers over the
segment at the cleared tower deflation, one sample point with its
count at both deflated carriers, and the two sample splits at the
head's order. -/
structure Cell (o : Nat) where
  lo : CPair
  hi : CPair
  ax : Pos
  ay : Pos
  tx : Pos
  ty : Pos
  gp : Pos
  tw : List Nat
  dN : BPair
  dD : BPair
  covA : cellcount.Cover
  covT : cellcount.Cover
  sn : BPair
  sc : Pos
  g : Nat
  spA : Split (cellcount.compl tw o).length
  spT : Split (cellcount.compl tw o).length

/-- The cell's read: both level carriers' tower deflations, cleared
once, covered over the segment at the head's order, the complement
places' count, and the clearing `(k + 1)·2` (`lem:cellcount`'s
pivot cover at `lem:freecell`'s carrier deflated at the tower
places, `cellcount.pdeflP`), the sample
inside the segment at the ground count `g ≥ 1` on both, the level
pair's gap, the tower places inside the order and distinct, and both
carriers' tower blocks dominant over the segment at the stated bound
(`decimation.domRead`, `thm:decimation`(ii)'s comparison as one read
in the root coordinate); at a vacant tower the decimated head is the
carrier itself at the window's order (`decimation.towerHead`); and the
segment sits at or
beyond the sum's unit in the root coordinate, the free end its
foot (`thm:gappos`(ii)'s free cell at the free end, the root
coordinate's segment from the free end in `thm:main`(i)'s
proof). -/
def cellRead {o : Nat} (E M G : Mat) (c : Cell o) : Prop :=
  cellcount.coverRead
    (decimation.towerHead c.tw o (freecell.freePMat E M G c.ax c.ay))
    (cellcount.compl c.tw o).length ((c.tw.length + 1) * 2) c.lo c.hi c.covA
  ∧ cellcount.coverRead
    (decimation.towerHead c.tw o (freecell.freePMat E M G c.tx c.ty))
    (cellcount.compl c.tw o).length ((c.tw.length + 1) * 2) c.lo c.hi c.covT
  ∧ c.lo ≤ (⟨c.sn, c.sc⟩ : CPair)
  ∧ (⟨c.sn, c.sc⟩ : CPair) ≤ c.hi
  ∧ cellcount.countAt
    (decimation.towerHead c.tw o (freecell.freePMat E M G c.ax c.ay))
    ((c.tw.length + 1) * 2) c.sn c.sc c.g c.spA
  ∧ cellcount.countAt
    (decimation.towerHead c.tw o (freecell.freePMat E M G c.tx c.ty))
    ((c.tw.length + 1) * 2) c.sn c.sc c.g c.spT
  ∧ 1 ≤ c.g
  ∧ c.ax + c.ty + c.gp = c.tx + c.ay
  ∧ cellcount.pieceRead o c.tw
  ∧ decimation.domRead (split.pselM c.tw c.tw (freecell.freePMat E M G c.ax c.ay))
      c.lo c.hi c.dN c.dD
  ∧ decimation.domRead (split.pselM c.tw c.tw (freecell.freePMat E M G c.tx c.ty))
      c.lo c.hi c.dN c.dD
  ∧ stage.unitC ≤ c.lo

instance instGappos2 {o : Nat} (E M G : Mat) (c : Cell o) : Decidable (cellRead E M G c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ = _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The cell list from a stated point: each cell's read, its segment
containing the running covered point, and the next cell from its
top — two consecutive cells' segments overlapping at the running
point (`thm:gappos`(iv), the cells' closed union the segments'
union). -/
def cellsRead {o : Nat} (E M G : Mat) : CPair → List (Cell o) → Prop
  | _, [] => True
  | cur, c :: rest =>
      cellRead E M G c ∧ c.lo ≤ cur ∧ cur ≤ c.hi ∧ cellsRead E M G c.hi rest

def decCellsRead {o : Nat} (E M G : Mat) :
    ∀ (cur : CPair) (l : List (Cell o)), Decidable (cellsRead E M G cur l)
  | _, [] => isTrue trivial
  | _, c :: rest =>
    have : Decidable (cellsRead E M G c.hi rest) := decCellsRead E M G c.hi rest
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance instGappos3 {o : Nat} (E M G : Mat) (cur : CPair) (l : List (Cell o)) :
    Decidable (cellsRead E M G cur l) := decCellsRead E M G cur l

/-- The list's top: the last cell's own. -/
def cellsTop {o : Nat} (cur : CPair) : List (Cell o) → CPair
  | [] => cur
  | c :: rest => cellsTop c.hi rest

/-- The cell of a point: the first cell whose top is at or beyond
the point, the last cell past every top. -/
def locateCell {o : Nat} (c0 : Cell o) : List (Cell o) → CPair → Cell o
  | [], _ => c0
  | c1 :: rest, v => if v ≤ c0.hi then c0 else locateCell c1 rest v

/-- The pair `κ = [kn : kd]` against every cell's level gap at the
module count: `E₀ κ ≤ gp` per cell (`thm:gappos`(iv)'s pair within
the flat window). -/
def gapsAt {o : Nat} (E0 kn kd : Pos) (cells : List (Cell o)) : Prop :=
  (cells.all (fun c => decide (E0 * kn ≤ kd * c.gp))) = true

instance instGappos4 {o : Nat} (E0 kn kd : Pos) (cells : List (Cell o)) :
    Decidable (gapsAt E0 kn kd cells) :=
  inferInstanceAs (Decidable (_ = _))

/-- The pair read at a member cell, the fold's own elimination. -/
theorem gapsAt_mem {o : Nat} {E0 kn kd : Pos} {cells : List (Cell o)}
    (h : gapsAt E0 kn kd cells) {c : Cell o} (hc : c ∈ cells) :
    E0 * kn ≤ kd * c.gp :=
  of_decide_eq_true (ground.all_of_mem _ cells h c hc)

/-- One level carrier's count at a point of the cell's segment is the
sample's (`thm:gappos`(iv) at the decimated head): the tower block
evaluates positive definite at every point of the segment, the
dominance read along it (`decimation.dom_segment`,
`decimation.dom_pd`) with its determinant on its upper side
(`inertia.minor_pos_of_pd`), so the carrier's count is its tower
deflation's, cleared once, at the further places
(`inertia.rev_placesP` at `cellcount.evalPC_pdeflP`, the solve
`cellcount.pdeflW_solve`), and the deflated head's count is one
integer over the segment (`cellcount.cellCountP` at
`cellcount.evalPC_pdeflP_symm`, the deflation symmetric at every
segment point where the pivot sits off the unit); at a vacant tower
the deflation is the carrier itself. -/
private theorem headCount {o : Nat} (E M G : Mat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o)
    (hEs : symmRead E) (hMs : symmRead M) (hGs : symmRead G)
    (x y : Pos) (tw : List Nat) (dN dD : BPair) (lo hi : CPair)
    (cov : cellcount.Cover) (sn : BPair) (sc : Pos) (g : Nat)
    (sp : Split (cellcount.compl tw o).length)
    (hcov : cellcount.coverRead
      (decimation.towerHead tw o (freecell.freePMat E M G x y))
      (cellcount.compl tw o).length ((tw.length + 1) * 2) lo hi cov)
    (hls : lo ≤ (⟨sn, sc⟩ : CPair)) (hsu : (⟨sn, sc⟩ : CPair) ≤ hi)
    (hcnt : cellcount.countAt
      (decimation.towerHead tw o (freecell.freePMat E M G x y))
      ((tw.length + 1) * 2) sn sc g sp)
    (hpiece : cellcount.pieceRead o tw)
    (hdom : decimation.domRead
      (split.pselM tw tw (freecell.freePMat E M G x y)) lo hi dN dD)
    (hfoot : stage.unitC ≤ lo)
    (n cc : Pos)
    (hlo : lo ≤ (⟨BPair.ofPos n, cc⟩ : CPair))
    (hhi : (⟨BPair.ofPos n, cc⟩ : CPair) ≤ hi)
    (spx : Split o)
    (hx : splitRead (cellcount.evalPC (freecell.freePMat E M G x y)
      (BPair.ofPos n) cc 2) spx) :
    revAt spx = g := by
  have hsh := freecell.pShapeAt_freePMat E M G x y o hE hM hG
  have hsymP := freecell.freePMat_sym E M G x y o hE hM hG hEs hMs hGs
  have hsymE : ∀ (zn : BPair) (zc : Pos),
      matOneValue
        (transposeM (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))
        (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2) :=
    fun zn zc => matOne_symm (cellcount.evalPC_symAt _ o 2 zn zc
      (cellcount.pShape_len hsh) (cellcount.pShape_rows hsh) hsymP)
  match tw, sp, hcov, hcnt, hpiece, hdom with
  | [], sp, hcov, hcnt, hpiece, _ =>
    have hL : (cellcount.compl [] o).length = o :=
      (Nat.zero_add _).symm.trans
        (cellcount.compl_length (o := o) (idx := []) hpiece.2 hpiece.1)
    revert hx
    revert spx
    rw [← hL]
    intro spx hx
    exact cellcount.cellCountP _ 2 g lo hi cov hcov (fun zn zc _ _ => hsymE zn zc)
      sn sc hls hsu sp hcnt (BPair.ofPos n) cc hlo hhi spx hx
  | i :: t, sp, hcov, hcnt, hpiece, hdom =>
    have hk0 : 0 < (i :: t).length := Nat.succ_pos _
    have hidx : ((i :: t).all (fun k => Nat.blt k o)) = true := hpiece.1
    have hrest : ((cellcount.compl (i :: t) o).all (fun j => Nat.blt j o)) = true :=
      cellcount.all_compl (i :: t) o
    have hTsq : ∀ (zn : BPair) (zc : Pos), sqAt (selM (i :: t) (i :: t)
        (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))
        (i :: t).length :=
      fun _ _ => sqAt_of (length_selM _ _ _) (rowsLen_selM (i :: t) _ (i :: t))
    have hTsym : ∀ (zn : BPair) (zc : Pos), matOneValue
        (transposeM (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2)))
        (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2)) :=
      fun zn zc => transposeM_selM (i :: t) (i :: t) _ o
        (cellcount.evalPC_sqAt hsh zn zc) (hsymE zn zc) hk0 hidx hidx
    have hT : ∀ (zn : BPair) (zc : Pos), splitRead
        (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))
        (mkSplit (i :: t).length (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))) :=
      fun zn zc => mkSplit_read _ _ (hTsq zn zc) (hTsym zn zc)
    have hpdAt : ∀ (zn : BPair) (zc : Pos), lo ≤ (⟨zn, zc⟩ : CPair) →
        (⟨zn, zc⟩ : CPair) ≤ hi →
        pdAt (mkSplit (i :: t).length (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))) := by
      intro zn zc hlz hzh
      have hgp : decimation.gapPos (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2)) := by
        rw [cellcount.selM_evalPC zn zc 2 _ (i :: t) (i :: t)]
        exact decimation.dom_segment _ 2 lo hi dN dD hdom
          (cellcount.deg_pselM _ 2 (cellcount.ent_ble hsh) (i :: t) (i :: t))
          zn (stage.unitC_le_fst (CPair.le_trans hfoot hlz)) zc hlz hzh
      exact decimation.dom_pd _ hgp _ (hT zn zc)
    have hPposAt : ∀ (zn : BPair) (zc : Pos), lo ≤ (⟨zn, zc⟩ : CPair) →
        (⟨zn, zc⟩ : CPair) ≤ hi →
        BPair.unit < minor (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2)) :=
      fun zn zc hlz hzh => minor_pos_of_pd _ _ (hT zn zc) (hpdAt zn zc hlz hzh)
    have hshD := cellcount.pShape_pdeflP (freecell.freePMat E M G x y) o 2 (i :: t)
      (cellcount.compl (i :: t) o) hsh
    have hDsq := cellcount.evalPC_sqAt hshD (BPair.ofPos n) cc
    have hDsym : ∀ (zn : BPair) (zc : Pos), lo ≤ (⟨zn, zc⟩ : CPair) →
        (⟨zn, zc⟩ : CPair) ≤ hi →
        matOneValue
          (transposeM (cellcount.evalPC (cellcount.pdeflP (i :: t)
            (cellcount.compl (i :: t) o) (freecell.freePMat E M G x y)) zn zc
              (((i :: t).length + 1) * 2)))
          (cellcount.evalPC (cellcount.pdeflP (i :: t)
            (cellcount.compl (i :: t) o) (freecell.freePMat E M G x y)) zn zc
              (((i :: t).length + 1) * 2)) :=
      fun zn zc hlz hzh => cellcount.evalPC_pdeflP_symm (o := o) _ 2 (i :: t) _ zn zc hsh
        (hsymE zn zc) hk0 hidx hrest (ground.offOfUnitLt (hPposAt zn zc hlz hzh))
    have hD := mkSplit_read _ _ hDsq (hDsym (BPair.ofPos n) cc hlo hhi)
    have hgD := cellcount.cellCountP _ _ g lo hi cov hcov hDsym sn sc hls hsu sp hcnt
      (BPair.ofPos n) cc hlo hhi _ hD
    have hdefl := cellcount.evalPC_pdeflP (o := o) _ 2 (i :: t) (cellcount.compl (i :: t) o)
      (BPair.ofPos n) cc hsh (hsymE (BPair.ofPos n) cc) hk0 hidx hrest
    have hPw := cellcount.pdeflW_solve _ 2 (i :: t) (cellcount.compl (i :: t) o)
      (BPair.ofPos n) cc (cellcount.ent_ble hsh) hk0
    have hCwl : (cellcount.evalPC (cellcount.pdeflW (i :: t) (cellcount.compl (i :: t) o)
        (freecell.freePMat E M G x y)) (BPair.ofPos n) cc ((i :: t).length * 2)).length
        = (i :: t).length :=
      (cellcount.length_evalPC _ _ _ _).trans (cellcount.length_pdeflW _ _ _)
    have hCwr : rowsLen (cellcount.compl (i :: t) o).length
        (cellcount.evalPC (cellcount.pdeflW (i :: t) (cellcount.compl (i :: t) o)
          (freecell.freePMat E M G x y)) (BPair.ofPos n) cc ((i :: t).length * 2)) :=
      cellcount.rowsLen_evalPC _ _ _ _ _ (cellcount.rowsLen_pdeflW (i :: t) _ _ hk0)
    have hBel : (selM (i :: t) (cellcount.compl (i :: t) o)
        (cellcount.evalPC (freecell.freePMat E M G x y) (BPair.ofPos n) cc 2)).length
        = (i :: t).length :=
      length_selM _ _ _
    have hDefSq := sqAt_deflMatP
      (selM (i :: t) (i :: t)
        (cellcount.evalPC (freecell.freePMat E M G x y) (BPair.ofPos n) cc 2))
      (selM (i :: t) (cellcount.compl (i :: t) o)
        (cellcount.evalPC (freecell.freePMat E M G x y) (BPair.ofPos n) cc 2))
      (selM (cellcount.compl (i :: t) o) (cellcount.compl (i :: t) o)
        (cellcount.evalPC (freecell.freePMat E M G x y) (BPair.ofPos n) cc 2))
      (cellcount.evalPC (cellcount.pdeflW (i :: t) (cellcount.compl (i :: t) o)
        (freecell.freePMat E M G x y)) (BPair.ofPos n) cc ((i :: t).length * 2))
      (cellcount.compl (i :: t) o).length
      (length_transposeM _ (rowsLen_selM _ _ _) (by rw [hBel]; exact hk0))
      (length_transposeM _ hCwr (by rw [hCwl]; exact hk0))
      (length_selM _ _ _) (rowsLen_selM _ _ _)
    have hD' := splitRead_congr _ _ hDefSq hdefl _ hD
    have hlen : ((i :: t) ++ cellcount.compl (i :: t) o).length = o := by
      rw [ground.length_append]
      exact cellcount.compl_length hpiece.2 hidx
    have hb : (((i :: t) ++ cellcount.compl (i :: t) o).all (fun k => Nat.blt k o)) = true := by
      rw [ground.all_append, hidx, hrest]
      rfl
    have hMsq : sqAt (cellcount.evalPC (freecell.freePMat E M G x y)
        (BPair.ofPos n) cc 2) o :=
      cellcount.evalPC_sqAt hsh _ _
    have h := rev_placesP _ (i :: t) (cellcount.compl (i :: t) o) hk0 hMsq
      (hsymE (BPair.ofPos n) cc) hlen
      (cellcount.distinct_append_compl (o := o) hpiece.2) hb _ hCwl hCwr hPw
      (minor_pos_of_pd _ _ (hT (BPair.ofPos n) cc) (hpdAt (BPair.ofPos n) cc hlo hhi))
      spx hx _ (hT (BPair.ofPos n) cc) _ hD'
    rw [h, (hpdAt (BPair.ofPos n) cc hlo hhi).1, Nat.zero_add]
    exact hgD

/-- A cell's flat window at every root-coordinate point of its
segment (`thm:gappos`(iv)): at the point `[n : c]` the ray
`[c² : n²]`'s pencil reads count `g` at both levels scaled by the
clearing, each count the cell's sample read at the point through the
tower's decimation (`headCount`, `freecell.freePMat_eval` the bridge
to the carrier's cleared evaluation), and the level order keeps. -/
theorem cell_flat {o : Nat} (E M G : Mat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o)
    (hEs : symmRead E) (hMs : symmRead M) (hGs : symmRead G)
    (c : Cell o) (hc : cellRead E M G c) (n cc : Pos)
    (hlo : c.lo ≤ (⟨BPair.ofPos n, cc⟩ : CPair))
    (hhi : (⟨BPair.ofPos n, cc⟩ : CPair) ≤ c.hi)
    (spa spt : Split o)
    (ha : splitRead (siteDatum (matAdd (pencil.rayH E M (cc * cc) (n * n))
      (matScale (cc * cc * c.ay) G)) (matScale (cc * cc * c.ax) G)) spa)
    (ht : splitRead (siteDatum (matAdd (pencil.rayH E M (cc * cc) (n * n))
      (matScale (cc * cc * c.ty) G)) (matScale (cc * cc * c.tx) G)) spt) :
    vacFlat (pencil.rayH E M (cc * cc) (n * n)) G
      (cc * cc * c.ax) (cc * cc * c.ay) (cc * cc * c.tx) (cc * cc * c.ty)
      c.g spa spt := by
  have hP : sqAt (pencil.rayH E M (cc * cc) (n * n)) o :=
    pencil.sqAt_rayH E M o hE hM (cc * cc) (n * n)
  have hshA := freecell.pShapeAt_freePMat E M G c.ax c.ay o hE hM hG
  have hshT := freecell.pShapeAt_freePMat E M G c.tx c.ty o hE hM hG
  have ha' : splitRead (cellcount.evalPC (freecell.freePMat E M G c.ax c.ay)
      (BPair.ofPos n) cc 2) spa :=
    splitRead_congr _ _ (cellcount.evalPC_sqAt hshA _ _)
      (matOne_symm (freecell.freePMat_eval E M G c.ax c.ay o hE hM hG n cc))
      spa ha
  have ht' : splitRead (cellcount.evalPC (freecell.freePMat E M G c.tx c.ty)
      (BPair.ofPos n) cc 2) spt :=
    splitRead_congr _ _ (cellcount.evalPC_sqAt hshT _ _)
      (matOne_symm (freecell.freePMat_eval E M G c.tx c.ty o hE hM hG n cc))
      spt ht
  obtain ⟨hcA, hcT, hls, hsu, hnA, hnT, hg1, hgap, hpiece, hdA, hdT, hfoot⟩ := hc
  have hga : revAt spa = c.g :=
    headCount E M G hE hM hG hEs hMs hGs c.ax c.ay c.tw c.dN c.dD c.lo c.hi
      c.covA c.sn c.sc c.g c.spA hcA hls hsu hnA hpiece hdA hfoot n cc hlo hhi spa ha'
  have hgt : revAt spt = c.g :=
    headCount E M G hE hM hG hEs hMs hGs c.tx c.ty c.tw c.dN c.dD c.lo c.hi
      c.covT c.sn c.sc c.g c.spT hcT hls hsu hnT hpiece hdT hfoot n cc hlo hhi spt ht'
  refine ⟨⟨hP, hG, ha, hga⟩, ⟨hP, hG, ht, hgt⟩, hg1, ?_⟩
  have hlt : (c.ax + c.ty) * (cc * cc) < (c.tx + c.ay) * (cc * cc) :=
    ground.mul_lt_mul_right (cc * cc) ⟨c.gp, hgap⟩
  rw [ground.right_distrib, ground.right_distrib, ground.mul_comm c.ax (cc * cc),
    ground.mul_comm c.ty (cc * cc), ground.mul_comm c.tx (cc * cc),
    ground.mul_comm c.ay (cc * cc)] at hlt
  exact hlt


/-- One level carrier's determinant off the sum's unit at every
point of a covered segment: at the tower places the carrier's block
is positive definite by the dominance read
(`inertia.minor_pos_of_pd`) and its once-cleared deflation is covered
(`cellcount.cover_rootfreeP`), so the carrier's determinant is off
the unit (`cellcount.pdeflP_rootfree`); at a vacant tower the head is
the carrier itself and the cover reads it. -/
private theorem carrierRootfree {o : Nat} (E M G : Mat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o)
    (hEs : symmRead E) (hMs : symmRead M) (hGs : symmRead G)
    (x y : Pos) (tw : List Nat) (dN dD : BPair) (lo hi : CPair)
    (cov : cellcount.Cover)
    (hcov : cellcount.coverRead
      (decimation.towerHead tw o (freecell.freePMat E M G x y))
      (cellcount.compl tw o).length ((tw.length + 1) * 2) lo hi cov)
    (hpiece : cellcount.pieceRead o tw)
    (hdom : decimation.domRead
      (split.pselM tw tw (freecell.freePMat E M G x y)) lo hi dN dD)
    (hfoot : stage.unitC ≤ lo) (hlt : lo < hi)
    (zn : BPair) (zc : Pos)
    (hlz : lo ≤ (⟨zn, zc⟩ : CPair)) (hzh : (⟨zn, zc⟩ : CPair) ≤ hi) :
    ¬ (minor (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2)).oneValue
      BPair.unit := by
  have hsh := freecell.pShapeAt_freePMat E M G x y o hE hM hG
  have hsymP := freecell.freePMat_sym E M G x y o hE hM hG hEs hMs hGs
  have hsymE : ∀ (zn : BPair) (zc : Pos),
      matOneValue
        (transposeM (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))
        (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2) :=
    fun zn zc => matOne_symm (cellcount.evalPC_symAt _ o 2 zn zc
      (cellcount.pShape_len hsh) (cellcount.pShape_rows hsh) hsymP)
  match tw, hcov, hpiece, hdom with
  | [], hcov, hpiece, _ =>
    have hL : (cellcount.compl [] o).length = o :=
      (Nat.zero_add _).symm.trans
        (cellcount.compl_length (o := o) (idx := []) hpiece.2 hpiece.1)
    have hshS : cellcount.pShapeAt (decimation.towerHead [] o
        (freecell.freePMat E M G x y)) (cellcount.compl [] o).length 2 := by
      rw [hL]
      exact hsh
    exact cellcount.cover_rootfreeP cov _ _ 2 lo hi hcov hshS
      (fun zn zc _ _ => hsymE zn zc) hlt zn zc hlz hzh
  | i :: t, hcov, hpiece, hdom =>
    have hk0 : 0 < (i :: t).length := Nat.succ_pos _
    have hidx : ((i :: t).all (fun k => Nat.blt k o)) = true := hpiece.1
    have hrest : ((cellcount.compl (i :: t) o).all (fun j => Nat.blt j o)) = true :=
      cellcount.all_compl (i :: t) o
    have hTsq : ∀ (zn : BPair) (zc : Pos), sqAt (selM (i :: t) (i :: t)
        (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))
        (i :: t).length :=
      fun _ _ => sqAt_of (length_selM _ _ _) (rowsLen_selM (i :: t) _ (i :: t))
    have hTsym : ∀ (zn : BPair) (zc : Pos), matOneValue
        (transposeM (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2)))
        (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2)) :=
      fun zn zc => transposeM_selM (i :: t) (i :: t) _ o
        (cellcount.evalPC_sqAt hsh zn zc) (hsymE zn zc) hk0 hidx hidx
    have hT : ∀ (zn : BPair) (zc : Pos), splitRead
        (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))
        (mkSplit (i :: t).length (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))) :=
      fun zn zc => mkSplit_read _ _ (hTsq zn zc) (hTsym zn zc)
    have hpdAt : ∀ (zn : BPair) (zc : Pos), lo ≤ (⟨zn, zc⟩ : CPair) →
        (⟨zn, zc⟩ : CPair) ≤ hi →
        pdAt (mkSplit (i :: t).length (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2))) := by
      intro zn zc hlz hzh
      have hgp : decimation.gapPos (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2)) := by
        rw [cellcount.selM_evalPC zn zc 2 _ (i :: t) (i :: t)]
        exact decimation.dom_segment _ 2 lo hi dN dD hdom
          (cellcount.deg_pselM _ 2 (cellcount.ent_ble hsh) (i :: t) (i :: t))
          zn (stage.unitC_le_fst (CPair.le_trans hfoot hlz)) zc hlz hzh
      exact decimation.dom_pd _ hgp _ (hT zn zc)
    have hPposAt : ∀ (zn : BPair) (zc : Pos), lo ≤ (⟨zn, zc⟩ : CPair) →
        (⟨zn, zc⟩ : CPair) ≤ hi →
        BPair.unit < minor (selM (i :: t) (i :: t)
          (cellcount.evalPC (freecell.freePMat E M G x y) zn zc 2)) :=
      fun zn zc hlz hzh => minor_pos_of_pd _ _ (hT zn zc) (hpdAt zn zc hlz hzh)
    have hshD := cellcount.pShape_pdeflP (freecell.freePMat E M G x y) o 2 (i :: t)
      (cellcount.compl (i :: t) o) hsh
    have hDsym : ∀ (zn : BPair) (zc : Pos), lo ≤ (⟨zn, zc⟩ : CPair) →
        (⟨zn, zc⟩ : CPair) ≤ hi →
        matOneValue
          (transposeM (cellcount.evalPC (cellcount.pdeflP (i :: t)
            (cellcount.compl (i :: t) o) (freecell.freePMat E M G x y)) zn zc
              (((i :: t).length + 1) * 2)))
          (cellcount.evalPC (cellcount.pdeflP (i :: t)
            (cellcount.compl (i :: t) o) (freecell.freePMat E M G x y)) zn zc
              (((i :: t).length + 1) * 2)) :=
      fun zn zc hlz hzh => cellcount.evalPC_pdeflP_symm (o := o) _ 2 (i :: t) _ zn zc hsh
        (hsymE zn zc) hk0 hidx hrest (ground.offOfUnitLt (hPposAt zn zc hlz hzh))
    have hD := cellcount.cover_rootfreeP cov _ _ _ lo hi hcov hshD hDsym hlt zn zc hlz hzh
    exact cellcount.pdeflP_rootfree _ 2 (i :: t) hpiece hsh hk0 zn zc (hsymE zn zc)
      (ground.offOfUnitLt (hPposAt zn zc hlz hzh)) hD

/-- The cell's covers read both level carriers' determinants off the
sum's unit at every point of the cell's segment (`lem:cellcount`'s
root-freeness read at `lem:freecell`'s jump family, the pencil
determinant's roots at the certificate's fixed pair): the tower's
dominance and the covers beneath it (`carrierRootfree`). -/
theorem cell_rootfree {o : Nat} (E M G : Mat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o)
    (hEs : symmRead E) (hMs : symmRead M) (hGs : symmRead G)
    (c : Cell o) (hc : cellRead E M G c) (hlt : c.lo < c.hi)
    (zn : BPair) (zc : Pos)
    (hlz : c.lo ≤ (⟨zn, zc⟩ : CPair)) (hzh : (⟨zn, zc⟩ : CPair) ≤ c.hi) :
    ¬ (minor (cellcount.evalPC (freecell.freePMat E M G c.ax c.ay) zn zc 2)).oneValue
        BPair.unit
    ∧ ¬ (minor (cellcount.evalPC (freecell.freePMat E M G c.tx c.ty) zn zc 2)).oneValue
        BPair.unit :=
  ⟨carrierRootfree E M G hE hM hG hEs hMs hGs c.ax c.ay c.tw c.dN c.dD c.lo c.hi
    c.covA hc.1 hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.1
    hc.2.2.2.2.2.2.2.2.2.2.2 hlt zn zc hlz hzh,
   carrierRootfree E M G hE hM hG hEs hMs hGs c.tx c.ty c.tw c.dN c.dD c.lo c.hi
    c.covT hc.2.1 hc.2.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.2.2.1
    hc.2.2.2.2.2.2.2.2.2.2.2 hlt zn zc hlz hzh⟩

/-- Every point from the list's foot to its top sits in the segment
of its located cell, a member of the list at its read
(`thm:gappos`(iv): the cells' closed union is the segments' union),
the fold locating the point by the composite order's totality. -/
theorem locate_read {o : Nat} (E M G : Mat) :
    ∀ (cur : CPair) (c0 : Cell o) (cells : List (Cell o)),
      cellsRead E M G cur (c0 :: cells) →
      ∀ v : CPair, cur ≤ v → v ≤ cellsTop cur (c0 :: cells) →
      locateCell c0 cells v ∈ c0 :: cells
        ∧ cellRead E M G (locateCell c0 cells v)
        ∧ (locateCell c0 cells v).lo ≤ v ∧ v ≤ (locateCell c0 cells v).hi
  | _, c0, [], h, _, h1, h2 =>
    ⟨List.Mem.head [], h.1, CPair.le_trans h.2.1 h1, h2⟩
  | _, c0, c1 :: rest, h, v, h1, h2 =>
    if hv : v ≤ c0.hi then by
      have e : locateCell c0 (c1 :: rest) v = c0 := if_pos hv
      rw [e]
      exact ⟨List.Mem.head _, h.1, CPair.le_trans h.2.1 h1, hv⟩
    else by
      have e : locateCell c0 (c1 :: rest) v = locateCell c1 rest v := if_neg hv
      rw [e]
      have hv' : c0.hi ≤ v :=
        match CPair.le_total v c0.hi with
        | Or.inl h' => absurd h' hv
        | Or.inr h' => h'
      have ih := locate_read E M G c0.hi c1 rest h.2.2.2 v hv' h2
      exact ⟨List.Mem.tail c0 ih.1, ih.2.1, ih.2.2.1, ih.2.2.2⟩

/-- The root coordinate's rays read their cells directly
(`thm:gappos`(v)): at every point `[n : c]` from the list's foot to
its top the located cell's flat window holds at the ray
`[c² : n²]`'s pencil, the members' symmetry reads
`lem:cellcount`'s symmetric-pencil hypothesis at the carrier. -/
theorem point_flat {o : Nat} (E M G : Mat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o)
    (hEs : symmRead E) (hMs : symmRead M) (hGs : symmRead G)
    (cur : CPair) (c0 : Cell o) (cells : List (Cell o))
    (hcells : cellsRead E M G cur (c0 :: cells))
    (n cc : Pos) (h1 : cur ≤ (⟨BPair.ofPos n, cc⟩ : CPair))
    (h2 : (⟨BPair.ofPos n, cc⟩ : CPair) ≤ cellsTop cur (c0 :: cells))
    (spa spt : Split o)
    (ha : splitRead (siteDatum (matAdd (pencil.rayH E M (cc * cc) (n * n))
      (matScale (cc * cc * (locateCell c0 cells ⟨BPair.ofPos n, cc⟩).ay) G))
      (matScale (cc * cc * (locateCell c0 cells ⟨BPair.ofPos n, cc⟩).ax) G)) spa)
    (ht : splitRead (siteDatum (matAdd (pencil.rayH E M (cc * cc) (n * n))
      (matScale (cc * cc * (locateCell c0 cells ⟨BPair.ofPos n, cc⟩).ty) G))
      (matScale (cc * cc * (locateCell c0 cells ⟨BPair.ofPos n, cc⟩).tx) G)) spt) :
    vacFlat (pencil.rayH E M (cc * cc) (n * n)) G
      (cc * cc * (locateCell c0 cells ⟨BPair.ofPos n, cc⟩).ax)
      (cc * cc * (locateCell c0 cells ⟨BPair.ofPos n, cc⟩).ay)
      (cc * cc * (locateCell c0 cells ⟨BPair.ofPos n, cc⟩).tx)
      (cc * cc * (locateCell c0 cells ⟨BPair.ofPos n, cc⟩).ty)
      (locateCell c0 cells ⟨BPair.ofPos n, cc⟩).g spa spt :=
  have hl := locate_read E M G cur c0 cells hcells _ h1 h2
  cell_flat E M G hE hM hG hEs hMs hGs _ hl.2.1 n cc hl.2.2.1 hl.2.2.2 spa spt
    ha ht

/-! The further pair rays (`thm:gappos`(v)): a ray `[α : β]` off the
root coordinate reads its window at the root-coordinate ray
`[q² : p²]`, `p` the least natural at the squared comparison and `q`
the stated scale, the two pencils' site datum the weights' gap
against the magnetic member capped at that gap's multiple of the
magnetic cap, and the sandwich transporting the window at half the
cell's level gap. -/

/-- The scale `q` at a ray: beyond `α`, and at or beyond
`4W(2τ* + 1)` at a natural `τ*` at or beyond the list's top. -/
def rayQ (al W tn : Pos) : Pos := (al + 1) * (4 * W * (2 * tn + 1))

/-- The squared comparison at the key `k`: `βq² ≤ (k+1)²α`. -/
def rayPred (al be q : Pos) (k : Nat) : Prop :=
  be * (q * q) ≤ posOfSucc (k + 1) * posOfSucc (k + 1) * al

instance instGappos5 (al be q : Pos) : DecidablePred (rayPred al be q) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- The least key at the squared comparison, the search over the keys
at or below the weight's own value. -/
def rayK (al be q : Pos) : Nat :=
  firstAt (rayPred al be q) 0 (posVal (be * (q * q)))

/-- The root-coordinate neighbor's first member `p`, the least natural
at the squared comparison: the least key's successor,
`p²α < βq² ≤ (p+1)²α`. -/
def rayP (al be q : Pos) : Pos := posOfSucc (rayK al be q)

/-- The least key's fast read: the halving search at the squared
comparison from the origin over the keys at or below the weight's own
value (`ground.bisectFrom`), one key with the walk (`rayKD_eq`). -/
def rayKD (al be q : Pos) : Nat :=
  bisectFrom (rayPred al be q) 0 (posVal (be * (q * q)))

/-- The weights' gap, `βq²` against `p²α`: the margin read
(`def:ground`'s difference at the balance pair). -/
def rayGap (al be q : Pos) : Pos :=
  BPair.marginPos ⟨be * (q * q), rayP al be q * rayP al be q * al⟩

/-- The sandwich's width, the gap's multiple of the magnetic member's
cap. -/
def rayRho (al be q W : Pos) : Pos := rayGap al be q * W

/-- The ray's cell: the neighbor `[p : q]`'s own in the list. -/
def rayCell {o : Nat} (al be q : Pos) (c0 : Cell o) (cells : List (Cell o)) :
    Cell o :=
  locateCell c0 cells ⟨BPair.ofPos (rayP al be q), q⟩

/-- The transported window's level gap: the cell's gap at the scale
`αq²` less twice the width, the margin read. -/
def rayGp {o : Nat} (al be q W : Pos) (c0 : Cell o) (cells : List (Cell o)) :
    Pos :=
  BPair.marginPos ⟨al * (q * q * (rayCell al be q c0 cells).gp),
    rayRho al be q W + rayRho al be q W⟩

private theorem leMulR (a b : Pos) : a ≤ a * b := by
  have h := ground.mul_le_mul_right a (posOneLe b)
  rw [ground.one_mul, ground.mul_comm b a] at h
  exact h

private theorem ltOfNotLe {a b : Pos} (h : ¬ b ≤ a) : a < b :=
  match ground.trich a b with
  | .lt g hg => ⟨g, hg⟩
  | .eq e => absurd (Or.inl e.symm) h
  | .gt g hg => absurd (Or.inr ⟨g, hg⟩) h

/-- The comparison holds at the weight's own key. -/
private theorem rayPred_bound (al be q : Pos) :
    rayPred al be q (posVal (be * (q * q))) := by
  show be * (q * q) ≤ (be * (q * q) + Pos.one + Pos.one)
    * (be * (q * q) + Pos.one + Pos.one) * al
  exact ground.le_trans (posLeSelfAdd _ _) (ground.le_trans (posLeSelfAdd _ _)
    (ground.le_trans (leMulR _ _) (leMulR _ _)))

/-- The search hits at the weight's own key. -/
private theorem rayK_hit (al be q : Pos) : rayPred al be q (rayK al be q) :=
  firstAt_hit (rayPred al be q) (posVal (be * (q * q))) 0
    (by rw [Nat.zero_add]; exact rayPred_bound al be q)

/-- The comparison steps up the keys, the successor's square at or
beyond the key's. -/
private theorem rayPred_step (al be q : Pos) (k : Nat) (h : rayPred al be q k) :
    rayPred al be q (k + 1) := by
  have hs : posOfSucc (k + 1) ≤ posOfSucc (k + 1 + 1) :=
    posLeSelfAdd (posOfSucc (k + 1)) Pos.one
  exact ground.le_trans h (ground.mul_le_mul_right al (posSqMono hs))

/-- The fast read is the walk's key: the least held key at the
comparison stepping up the keys. -/
theorem rayKD_eq (al be q : Pos) : rayKD al be q = rayK al be q :=
  bisectFrom_eq_firstAt _ (rayPred_step al be q) 0 _

/-- The neighbor's two reads at a ray beyond `α`: `p²α < βq² ≤ (p+1)²α`. -/
private theorem rayP_read (al be q : Pos) (h : al < be * (q * q)) :
    rayP al be q * rayP al be q * al < be * (q * q)
    ∧ be * (q * q) ≤ (rayP al be q + Pos.one) * (rayP al be q + Pos.one) * al := by
  constructor
  · show posOfSucc (rayK al be q) * posOfSucc (rayK al be q) * al < be * (q * q)
    match hk : rayK al be q with
    | 0 =>
      show Pos.one * Pos.one * al < be * (q * q)
      rw [ground.one_mul, ground.one_mul]
      exact h
    | k + 1 =>
      have hb := firstAt_below (rayPred al be q) (posVal (be * (q * q))) 0 k
        (Nat.zero_le k) (by show k < rayK al be q; rw [hk]; exact Nat.lt_succ_self k)
      exact ltOfNotLe hb
  · show be * (q * q) ≤ posOfSucc (rayK al be q + 1) * posOfSucc (rayK al be q + 1) * al
    exact rayK_hit al be q

/-- The free end sits at or below every root-coordinate point. -/
private theorem unit_le_point (p q : Pos) :
    (⟨BPair.unit, Pos.one⟩ : CPair) ≤ ⟨BPair.ofPos p, q⟩ := by
  refine Or.inr ⟨p, ?_⟩
  show Pos.one * q + Pos.one * Pos.one + p = (p + Pos.one) * Pos.one + Pos.one * q
  rw [ground.one_mul, ground.one_mul, ground.mul_one,
    ground.add_comm (q + Pos.one) p, ground.add_comm q Pos.one,
    ground.add_assoc]

/-- A root-coordinate point sits at or below a second one exactly at
the cross-multiplied read. -/
private theorem point_le (p q tn td : Pos) (h : p * td ≤ tn * q) :
    (⟨BPair.ofPos p, q⟩ : CPair) ≤ ⟨BPair.ofPos tn, td⟩ := by
  have e1 : (p + Pos.one) * td + Pos.one * q = p * td + (td + q) := by
    rw [ground.right_distrib, ground.one_mul, ground.one_mul, ground.add_assoc]
  have e2 : (tn + Pos.one) * q + Pos.one * td = tn * q + (td + q) := by
    rw [ground.right_distrib, ground.one_mul, ground.one_mul, ground.add_assoc,
      ground.add_comm q td]
  match h with
  | Or.inl e =>
    refine Or.inl ?_
    show (p + Pos.one) * td + Pos.one * q = (tn + Pos.one) * q + Pos.one * td
    rw [e1, e2, e]
  | Or.inr ⟨g, hg⟩ =>
    refine Or.inr ⟨g, ?_⟩
    show (p + Pos.one) * td + Pos.one * q + g = (tn + Pos.one) * q + Pos.one * td
    rw [e1, e2, ← hg, ground.add_right_comm]

/-- The point's window carried to the ray at the stated scale
(`thm:gappos`(v)): at a list from the free end whose top is
`[τ* : td]`, a ray `[α : β]` at or below the top's square, a scale
`q` beyond `α` and at or beyond `4W(2τ* + 1)`, and the pair `κ`
doubled under every cell's level gap at `E₀`, the ray's pencil at
the scale `q²` reads a flat window at the ray's cell's levels
scaled by `αq²` and shifted by the width `ρ`, its level gap the
cell's gap at that scale less twice the width, `E₀ κ` under it at
the scale `αq²`. -/
theorem ray_core {o : Nat} (E M G : Mat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o)
    (hEs : symmRead E) (hMs : symmRead M) (hGs : symmRead G)
    (spG : Split o) (hGr : splitRead G spG) (hGp : psdAt spG)
    (W : Pos) (spU spL : Split o) (hcap : capAt M (matScale W G) spU spL)
    (c0 : Cell o) (cells : List (Cell o))
    (hcells : cellsRead E M G ⟨BPair.unit, Pos.one⟩ (c0 :: cells))
    (E0 kn kd : Pos) (hgaps : gapsAt E0 (2 * kn) kd (c0 :: cells))
    (tn td : Pos)
    (htop : cellsTop (⟨BPair.unit, Pos.one⟩ : CPair) (c0 :: cells)
      = ⟨BPair.ofPos tn, td⟩)
    (al be q : Pos) (hray : be * (td * td) ≤ tn * tn * al)
    (hqa : al < q) (hqW : 4 * W * (2 * tn + 1) ≤ q) :
    (al * (q * q * (rayCell al be q c0 cells).ax) + rayRho al be q W)
      + (al * (q * q * (rayCell al be q c0 cells).ty) + rayRho al be q W)
      + rayGp al be q W c0 cells
      = al * (q * q * (rayCell al be q c0 cells).tx)
        + al * (q * q * (rayCell al be q c0 cells).ay)
    ∧ E0 * (al * kn) * (q * q) ≤ kd * rayGp al be q W c0 cells
    ∧ ∀ spa spt : Split o,
      splitRead (siteDatum (matAdd (matScale (q * q) (pencil.rayH E M al be))
        (matScale (al * (q * q * (rayCell al be q c0 cells).ay)) G))
        (matScale (al * (q * q * (rayCell al be q c0 cells).ax) + rayRho al be q W) G))
        spa →
      splitRead (siteDatum (matAdd (matScale (q * q) (pencil.rayH E M al be))
        (matScale (al * (q * q * (rayCell al be q c0 cells).ty) + rayRho al be q W) G))
        (matScale (al * (q * q * (rayCell al be q c0 cells).tx)) G)) spt →
      vacFlat (matScale (q * q) (pencil.rayH E M al be)) G
        (al * (q * q * (rayCell al be q c0 cells).ax) + rayRho al be q W)
        (al * (q * q * (rayCell al be q c0 cells).ay))
        (al * (q * q * (rayCell al be q c0 cells).tx))
        (al * (q * q * (rayCell al be q c0 cells).ty) + rayRho al be q W)
        (rayCell al be q c0 cells).g spa spt := by
  unfold rayGp rayRho rayCell rayGap
  -- the neighbor's data
  have hqq : q ≤ q * q := leMulR q q
  have hbq : q * q ≤ be * (q * q) := by
    have h := ground.mul_le_mul_right (q * q) (posOneLe be)
    rw [ground.one_mul] at h
    exact h
  have hlt : al < be * (q * q) := ground.lt_of_lt_of_le hqa (ground.le_trans hqq hbq)
  obtain ⟨hp1, hp2⟩ := rayP_read al be q hlt
  generalize rayP al be q = p at hp1 hp2 ⊢
  have hkk : p * p * al + BPair.marginPos ⟨be * (q * q), p * p * al⟩ = be * (q * q) :=
    BPair.marginPos_join hp1
  generalize BPair.marginPos ⟨be * (q * q), p * p * al⟩ = kk at hkk ⊢
  -- the neighbor sits in the list's range
  have hptd : p * td ≤ tn * q := by
    have s1 : p * p * al * (td * td) < be * (q * q) * (td * td) :=
      ground.mul_lt_mul_right (td * td) ⟨kk, hkk⟩
    have s2 : be * (q * q) * (td * td) = be * (td * td) * (q * q) :=
      ground.mul_right_comm be (q * q) (td * td)
    have s3 : be * (td * td) * (q * q) ≤ tn * tn * al * (q * q) :=
      ground.mul_le_mul_right (q * q) hray
    rw [s2] at s1
    have s4 : p * p * al * (td * td) < tn * tn * al * (q * q) := ground.lt_of_lt_of_le s1 s3
    have e1 : p * p * al * (td * td) = p * td * (p * td) * al := by
      rw [ground.mul_right_comm (p * p) al (td * td),
        ground.mul_mul_mul_comm p p td td]
    have e2 : tn * tn * al * (q * q) = tn * q * (tn * q) * al := by
      rw [ground.mul_right_comm (tn * tn) al (q * q),
        ground.mul_mul_mul_comm tn tn q q]
    rw [e1, e2] at s4
    exact posSqLe (Or.inr (ground.lt_of_mul_lt s4))
  have hpt_lo : (⟨BPair.unit, Pos.one⟩ : CPair) ≤ ⟨BPair.ofPos p, q⟩ :=
    unit_le_point p q
  have hpt_hi : (⟨BPair.ofPos p, q⟩ : CPair)
      ≤ cellsTop (⟨BPair.unit, Pos.one⟩ : CPair) (c0 :: cells) := by
    rw [htop]
    exact point_le p q tn td hptd
  have hl := locate_read E M G _ c0 cells hcells _ hpt_lo hpt_hi
  have hk2 : E0 * (2 * kn) ≤ kd * (locateCell c0 cells ⟨BPair.ofPos p, q⟩).gp :=
    gapsAt_mem hgaps hl.1
  generalize locateCell c0 cells ⟨BPair.ofPos p, q⟩ = c at hl hk2 ⊢
  obtain ⟨_, hc, hlo, hhi⟩ := hl
  have htie := hc.2.2.2.2.2.2.2.1
  rw [ground.mul_comm 2 kn, ← ground.mul_assoc E0 kn 2] at hk2
  -- the gap of the weights and its bound
  have hkk_le : kk ≤ (2 * p + 1) * al := by
    have e : (p + Pos.one) * (p + Pos.one) * al = p * p * al + (2 * p + 1) * al := by
      rw [← ground.right_distrib]
      refine congrArg (fun z => z * al) ?_
      rw [ground.right_distrib, ground.left_distrib, ground.left_distrib,
        ground.mul_one, ground.mul_one, ground.one_mul, ground.two_mul,
        ground.add_assoc, ground.add_assoc]
      rfl
    rw [e, ← hkk, ground.add_comm (p * p * al) kk,
      ground.add_comm (p * p * al) ((2 * p + 1) * al)] at hp2
    exact posLeCancelR hp2
  have hp_le : p ≤ tn * q := ground.le_trans (leMulR p td) hptd
  have h2p : 2 * p + 1 ≤ (2 * tn + 1) * q := by
    have h1 : 2 * p ≤ 2 * (tn * q) := by
      have h := ground.mul_le_mul_right 2 hp_le
      rw [ground.mul_comm p 2, ground.mul_comm (tn * q) 2] at h
      exact h
    have h2 : 2 * p + 1 ≤ 2 * (tn * q) + 1 := posLeAdd h1 (Or.inl rfl)
    have h3 : 2 * (tn * q) + 1 ≤ 2 * (tn * q) + q := posLeAdd (Or.inl rfl) (posOneLe q)
    have e : (2 * tn + 1) * q = 2 * (tn * q) + q := by
      rw [ground.right_distrib]
      show 2 * tn * q + Pos.one * q = _
      rw [ground.one_mul, ground.mul_assoc]
    rw [e]
    exact ground.le_trans h2 h3
  -- the width and its quarter read
  have hW4 : kk * W + kk * W + (kk * W + kk * W) ≤ al * (q * q * c.gp) := by
    have b1 : kk * W ≤ (2 * tn + 1) * q * al * W := by
      refine ground.mul_le_mul_right W ?_
      refine ground.le_trans hkk_le ?_
      exact ground.mul_le_mul_right al h2p
    have b2 : kk * W + kk * W + (kk * W + kk * W)
        ≤ (2 * tn + 1) * q * al * W + (2 * tn + 1) * q * al * W
          + ((2 * tn + 1) * q * al * W + (2 * tn + 1) * q * al * W) :=
      posLeAdd (posLeAdd b1 b1) (posLeAdd b1 b1)
    have e4 : (2 * tn + 1) * q * al * W + (2 * tn + 1) * q * al * W
        + ((2 * tn + 1) * q * al * W + (2 * tn + 1) * q * al * W)
        = 4 * W * (2 * tn + 1) * q * al := by
      rw [← ground.two_mul, ← ground.two_mul,
        show (2 : Pos) * (2 * ((2 * tn + 1) * q * al * W))
          = 4 * ((2 * tn + 1) * q * al * W) from
          (ground.mul_assoc 2 2 _).symm,
        ground.mul_comm ((2 * tn + 1) * q * al) W, ← ground.mul_assoc 4 W _,
        ← ground.mul_assoc (4 * W) ((2 * tn + 1) * q) al,
        ← ground.mul_assoc (4 * W) (2 * tn + 1) q]
    have b3 : 4 * W * (2 * tn + 1) * q * al ≤ q * q * al :=
      ground.mul_le_mul_right al (ground.mul_le_mul_right q hqW)
    have b4 : q * q * al ≤ al * (q * q * c.gp) := by
      rw [ground.mul_comm al (q * q * c.gp), ground.mul_assoc (q * q) c.gp al,
        ground.mul_comm c.gp al, ← ground.mul_assoc (q * q) al c.gp]
      exact leMulR _ _
    exact ground.le_trans b2 (by rw [e4]; exact ground.le_trans b3 b4)
  -- the point window's splits at the carrier
  have hshA := freecell.pShapeAt_freePMat E M G c.ax c.ay o hE hM hG
  have hshT := freecell.pShapeAt_freePMat E M G c.tx c.ty o hE hM hG
  have hsymA := freecell.freePMat_sym E M G c.ax c.ay o hE hM hG hEs hMs hGs
  have hsymT := freecell.freePMat_sym E M G c.tx c.ty o hE hM hG hEs hMs hGs
  have hP : sqAt (pencil.rayH E M (q * q) (p * p)) o :=
    pencil.sqAt_rayH E M o hE hM (q * q) (p * p)
  have siteSq : ∀ (X : Mat) (u v : Pos), sqAt X o →
      sqAt (siteDatum (matAdd X (matScale u G)) (matScale v G)) o :=
    fun X u v hX => sqAt_siteDatum o _ _
      (sqAt_matAdd o X _ hX (sqAt_matScale o u G hG)) (sqAt_matScale o v G hG)
  have mkAt : ∀ (x y : Pos), split.pSymAt (freecell.freePMat E M G x y) o →
      cellcount.pShapeAt (freecell.freePMat E M G x y) o 2 →
      splitRead (siteDatum (matAdd (pencil.rayH E M (q * q) (p * p))
        (matScale (q * q * y) G)) (matScale (q * q * x) G))
        (mkSplit o (cellcount.evalPC (freecell.freePMat E M G x y)
          (BPair.ofPos p) q 2)) := by
    intro x y hsym hsh
    have hr := mkSplit_read o _ (cellcount.evalPC_sqAt hsh (BPair.ofPos p) q)
      (matOne_symm (cellcount.evalPC_symAt _ o 2 (BPair.ofPos p) q
        (cellcount.pShape_len hsh) (cellcount.pShape_rows hsh) hsym))
    exact splitRead_congr _ _ (siteSq _ _ _ hP)
      (freecell.freePMat_eval E M G x y o hE hM hG p q) _ hr
  have hw0 := cell_flat E M G hE hM hG hEs hMs hGs c hc p q hlo hhi _ _
    (mkAt c.ax c.ay hsymA hshA) (mkAt c.tx c.ty hsymT hshT)
  -- the window scaled by α
  have scaleSite : ∀ (u v : Pos),
      matScale al (siteDatum (matAdd (pencil.rayH E M (q * q) (p * p))
        (matScale u G)) (matScale v G))
      = siteDatum (matAdd (matScale al (pencil.rayH E M (q * q) (p * p)))
        (matScale (al * u) G)) (matScale (al * v) G) := by
    intro u v
    show matScale al (matAdd (matAdd _ (matScale u G)) (matSwap (matScale v G)))
      = matAdd (matAdd _ (matScale (al * u) G)) (matSwap (matScale (al * v) G))
    rw [matScale_matAdd, matScale_matAdd, matScale_matSwap,
      matScale_matScale u al G, matScale_matScale v al G]
  have hoff : ¬ (BPair.ofPos al).oneValue BPair.unit :=
    ground.offOfUnitLt (ground.unitLtOfPos al)
  have scaledRead : ∀ (u v : Pos) (sp : Split o),
      splitRead (siteDatum (matAdd (pencil.rayH E M (q * q) (p * p))
        (matScale u G)) (matScale v G)) sp →
      splitRead (siteDatum (matAdd (matScale al (pencil.rayH E M (q * q) (p * p)))
        (matScale (al * u) G)) (matScale (al * v) G))
        (scaleSplit (BPair.ofPos al) sp) := by
    intro u v sp hs
    have h1 := scaleSplit_read (BPair.ofPos al) hoff _ sp hs
    refine splitRead_congr _ _ (siteSq _ _ _ (sqAt_matScale o al _ hP)) ?_ _ h1
    rw [← scaleSite u v]
    exact matOne_symm (matScale_scaleB al _)
  have hw1 := vacFlat_scale al (pencil.rayH E M (q * q) (p * p)) G
    (q * q * c.ax) (q * q * c.ay) (q * q * c.tx) (q * q * c.ty) c.g _ _ _ _ hw0
    (scaledRead _ _ _ (mkAt c.ax c.ay hsymA hshA))
    (scaledRead _ _ _ (mkAt c.tx c.ty hsymT hshT))
  -- the tie between the two pencils and the cap
  have hHe : matOneValue (matScale al (pencil.rayH E M (q * q) (p * p)))
      (matAdd (matScale (q * q) (pencil.rayH E M al be)) (matScale kk M)) := by
    unfold pencil.rayH siteDatum
    rw [matScale_matAdd (q * q) (matScale al E),
      matScale_matSwap (q * q) (matScale be M)]
    rw [matScale_matAdd, matScale_matSwap, matScale_matScale (q * q) al E,
      matScale_matScale (p * p) al M, matScale_matScale al (q * q) E,
      matScale_matScale be (q * q) M, ground.mul_comm (q * q) be, ← hkk,
      matScale_addW (p * p * al) kk M, matSwap_matAdd,
      ground.mul_comm al (q * q), ground.mul_comm al (p * p),
      matAdd_assoc (matScale (q * q * al) E)
        (matAdd (matSwap (matScale (p * p * al) M)) (matSwap (matScale kk M)))
        (matScale kk M),
      matAdd_assoc (matSwap (matScale (p * p * al) M)) (matSwap (matScale kk M))
        (matScale kk M),
      ← matAdd_assoc (matScale (q * q * al) E) (matSwap (matScale (p * p * al) M))
        (matAdd (matSwap (matScale kk M)) (matScale kk M))]
    refine matOne_symm (matAdd_nullR (o := o) _ _ ?_ ?_ (matNull_swap_add (matOne_refl _)))
    · exact sqAt_matAdd o _ _ (sqAt_matScale o _ E hE)
        (sqAt_matSwap o _ (sqAt_matScale o _ M hM))
    · exact sqAt_matAdd o _ _ (sqAt_matSwap o _ (sqAt_matScale o kk M hM))
        (sqAt_matScale o kk M hM)
  have hcapS : capAt (matScale kk M) (matScale (kk * W) G)
      (scaleSplit (BPair.ofPos kk) spU) (scaleSplit (BPair.ofPos kk) spL) := by
    have h := capAt_scale M (matScale W G) kk spU spL hcap
    rw [matScale_matScale W kk G] at h
    exact h
  -- the margin and the half gap
  have hsum : al * (q * q * c.tx) + al * (q * q * c.ay)
      = al * (q * q * c.ax) + al * (q * q * c.ty) + al * (q * q * c.gp) := by
    rw [← ground.left_distrib, ← ground.left_distrib, ← ground.left_distrib,
      ← ground.left_distrib, ← ground.left_distrib, ← ground.left_distrib, ← htie]
  have hrho2 : kk * W + kk * W < al * (q * q * c.gp) :=
    ground.lt_of_lt_of_le (posLtSelfAdd _ _) hW4
  have hgp' : kk * W + kk * W + BPair.marginPos ⟨al * (q * q * c.gp), kk * W + kk * W⟩
      = al * (q * q * c.gp) := BPair.marginPos_join hrho2
  generalize BPair.marginPos ⟨al * (q * q * c.gp), kk * W + kk * W⟩ = gp' at hgp' ⊢
  have hhalf : al * (q * q * c.gp) ≤ gp' + gp' := by
    have h1 : al * (q * q * c.gp) + al * (q * q * c.gp)
        = kk * W + kk * W + (kk * W + kk * W) + (gp' + gp') := by
      rw [← hgp', ground.add_add_comm]
    have h2 : kk * W + kk * W + (kk * W + kk * W) + (gp' + gp')
        ≤ al * (q * q * c.gp) + (gp' + gp') := posLeAdd hW4 (Or.inl rfl)
    rw [← h1, ground.add_comm (al * (q * q * c.gp)) (gp' + gp')] at h2
    exact posLeCancelR h2
  have hmargin : al * (q * q * c.ax) + kk * W + (al * (q * q * c.ty) + kk * W)
      < al * (q * q * c.tx) + al * (q * q * c.ay) := by
    rw [hsum, ground.add_add_comm]
    match hrho2 with
    | ⟨g, hg⟩ => exact ⟨g, by rw [ground.add_assoc, hg]⟩
  have hgap : al * (q * q * c.ax) + kk * W + (al * (q * q * c.ty) + kk * W) + gp'
      = al * (q * q * c.tx) + al * (q * q * c.ay) := by
    rw [hsum, ground.add_add_comm, ground.add_assoc, hgp']
  refine ⟨hgap, ?_, ?_⟩
  · -- the pair's read at the ray
    have h1 : E0 * kn * 2 * (al * (q * q)) ≤ kd * c.gp * (al * (q * q)) :=
      ground.mul_le_mul_right (al * (q * q)) hk2
    have e1 : E0 * kn * 2 * (al * (q * q)) = E0 * (al * kn) * (q * q) * 2 := by
      rw [ground.mul_right_comm (E0 * kn) 2 (al * (q * q)),
        ground.mul_assoc E0 kn (al * (q * q)), ← ground.mul_assoc kn al (q * q),
        ground.mul_comm kn al, ← ground.mul_assoc E0 (al * kn) (q * q)]
    have e2 : kd * c.gp * (al * (q * q)) = kd * (al * (q * q * c.gp)) := by
      rw [ground.mul_assoc, ground.mul_comm c.gp (al * (q * q)),
        ground.mul_assoc al (q * q) c.gp]
    rw [e1, e2] at h1
    have h2 : kd * (al * (q * q * c.gp)) ≤ kd * gp' * 2 := by
      rw [ground.mul_comm (kd * gp') 2, ground.two_mul, ← ground.left_distrib]
      rw [ground.mul_comm kd (al * (q * q * c.gp)), ground.mul_comm kd (gp' + gp')]
      exact ground.mul_le_mul_right kd hhalf
    exact ground.le_of_mul_le (ground.le_trans h1 h2)
  · intro spa spt ha ht
    have hH' : sqAt (matScale (q * q) (pencil.rayH E M al be)) o :=
      sqAt_matScale o _ _ (pencil.sqAt_rayH E M o hE hM al be)
    -- the two levels' difference site at the target, the gram's scalar copy
    have hsplit := levelDiff_split (matScale (q * q) (pencil.rayH E M al be)) G hH' hG
      spG hGr hGp (al * (q * q * c.ax) + kk * W) (al * (q * q * c.ay))
      (al * (q * q * c.tx)) (al * (q * q * c.ty) + kk * W) gp' hgap
    have hspd := hsplit.1
    have hpd := hsplit.2
    exact flat_transport (matScale al (pencil.rayH E M (q * q) (p * p)))
      (matScale (q * q) (pencil.rayH E M al be)) (matScale kk M) G (kk * W)
      (al * (q * q * c.ax)) (al * (q * q * c.ay)) (al * (q * q * c.tx))
      (al * (q * q * c.ty)) c.g (revAt spa) (revAt spt) _ _ spa spt _ _ _
      hHe hcapS hw1 hmargin hspd hpd ⟨hH', hG, ha, rfl⟩ ⟨hH', hG, ht, rfl⟩

/-- The stated scale's two reads: beyond `α`, and at or beyond
`4W(2τ* + 1)`. -/
private theorem rayQ_reads (al W tn : Pos) :
    al < rayQ al W tn ∧ 4 * W * (2 * tn + 1) ≤ rayQ al W tn :=
  ⟨ground.lt_of_lt_of_le (posLtSelfAdd al 1) (leMulR _ _),
   by
    have h := ground.mul_le_mul_right (4 * W * (2 * tn + 1)) (posOneLe (al + 1))
    rw [ground.one_mul] at h
    exact h⟩

/-- The further pair rays' window (`thm:gappos`(v)), `ray_core` at
the stated scale `q = (α + 1)·4W(2τ* + 1)`. -/
theorem ray_flat {o : Nat} (E M G : Mat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o)
    (hEs : symmRead E) (hMs : symmRead M) (hGs : symmRead G)
    (spG : Split o) (hGr : splitRead G spG) (hGp : psdAt spG)
    (W : Pos) (spU spL : Split o) (hcap : capAt M (matScale W G) spU spL)
    (c0 : Cell o) (cells : List (Cell o))
    (hcells : cellsRead E M G ⟨BPair.unit, Pos.one⟩ (c0 :: cells))
    (E0 kn kd : Pos) (hgaps : gapsAt E0 (2 * kn) kd (c0 :: cells))
    (tn td : Pos)
    (htop : cellsTop (⟨BPair.unit, Pos.one⟩ : CPair) (c0 :: cells)
      = ⟨BPair.ofPos tn, td⟩)
    (al be : Pos) (hray : be * (td * td) ≤ tn * tn * al) :
    (al * (rayQ al W tn * rayQ al W tn * (rayCell al be (rayQ al W tn) c0 cells).ax)
        + rayRho al be (rayQ al W tn) W)
      + (al * (rayQ al W tn * rayQ al W tn * (rayCell al be (rayQ al W tn) c0 cells).ty)
        + rayRho al be (rayQ al W tn) W)
      + rayGp al be (rayQ al W tn) W c0 cells
      = al * (rayQ al W tn * rayQ al W tn * (rayCell al be (rayQ al W tn) c0 cells).tx)
        + al * (rayQ al W tn * rayQ al W tn * (rayCell al be (rayQ al W tn) c0 cells).ay)
    ∧ E0 * (al * kn) * (rayQ al W tn * rayQ al W tn)
        ≤ kd * rayGp al be (rayQ al W tn) W c0 cells
    ∧ ∀ spa spt : Split o,
      splitRead (siteDatum (matAdd (matScale (rayQ al W tn * rayQ al W tn)
          (pencil.rayH E M al be))
        (matScale (al * (rayQ al W tn * rayQ al W tn
          * (rayCell al be (rayQ al W tn) c0 cells).ay)) G))
        (matScale (al * (rayQ al W tn * rayQ al W tn
          * (rayCell al be (rayQ al W tn) c0 cells).ax) + rayRho al be (rayQ al W tn) W) G))
        spa →
      splitRead (siteDatum (matAdd (matScale (rayQ al W tn * rayQ al W tn)
          (pencil.rayH E M al be))
        (matScale (al * (rayQ al W tn * rayQ al W tn
          * (rayCell al be (rayQ al W tn) c0 cells).ty) + rayRho al be (rayQ al W tn) W) G))
        (matScale (al * (rayQ al W tn * rayQ al W tn
          * (rayCell al be (rayQ al W tn) c0 cells).tx)) G)) spt →
      vacFlat (matScale (rayQ al W tn * rayQ al W tn) (pencil.rayH E M al be)) G
        (al * (rayQ al W tn * rayQ al W tn * (rayCell al be (rayQ al W tn) c0 cells).ax)
          + rayRho al be (rayQ al W tn) W)
        (al * (rayQ al W tn * rayQ al W tn * (rayCell al be (rayQ al W tn) c0 cells).ay))
        (al * (rayQ al W tn * rayQ al W tn * (rayCell al be (rayQ al W tn) c0 cells).tx))
        (al * (rayQ al W tn * rayQ al W tn * (rayCell al be (rayQ al W tn) c0 cells).ty)
          + rayRho al be (rayQ al W tn) W)
        (rayCell al be (rayQ al W tn) c0 cells).g spa spt :=
  ray_core E M G hE hM hG hEs hMs hGs spG hGr hGp W spU spL hcap c0 cells hcells
    E0 kn kd hgaps tn td htop al be (rayQ al W tn) hray
    (rayQ_reads al W tn).1 (rayQ_reads al W tn).2


/-- The cutoff's price closes at the cut (`thm:gappos`(iii)): at the
magnetic cap and the polarization tie of `thm:truncation`, a window
whose compression reads the cut at the level raised by the cofactor
width reads the cut itself at the level — the removed block's
vacancy derived at the admissible cutoff's own data, the electric
diagonal at or above the cutoff with the block's magnetic cap and
the floor tie `x + ς + W ≤ c + y`
(`truncation.removed_psd`), and the window cuts transported to
`𝒦(v)` within the priced modulus (`truncation.count_shift_le` at
the vacant counts). -/
theorem truncCut {k m : Nat} (H G M M1 M2 P G1 Q De G2 B : Mat)
    (x y cw W s c : Pos)
    (spU spL spF spD spd : Split (k + m))
    (spH : Split k) (spR spDi spG spB : Split m)
    (hcap : capAt M (matScale W G) spU spL)
    (hMt : matOneValue M (blockJoin M1 B M2))
    (hGt : matOneValue G (blockJoin G1 (elim.nullMat k m) G2))
    (hM1 : sqAt M1 k) (hM2l : M2.length = m)
    (hG1 : sqAt G1 k) (hG2 : sqAt G2 m)
    (hB : B.length = k) (hBr : rowsLen m B)
    (htieD : matOneValue (matScale s (siteDatum
        (siteDatum (matAdd H (matScale y G)) (matScale x G))
        (blockJoin
          (siteDatum (matAdd P (matScale y G1)) (matScale (x + cw) G1))
          (elim.nullMat k m)
          (siteDatum (matAdd Q (matScale y G2)) (matScale (x + s) G2)))))
      (truncation.shiftSite W s B G1 G2))
    (hH : sqAt H (k + m)) (hG : sqAt G (k + m)) (hQ : sqAt Q m)
    (hsF : splitRead
      (siteDatum (matAdd H (matScale y G)) (matScale x G)) spF)
    (hh : countAtPair P G1 (x + cw) y 0 spH)
    (hQt : matOneValue Q (matAdd De M2))
    (hdi : splitRead (siteDatum De (matScale c G2)) spDi)
    (hpdi : psdAt spDi)
    (hgB : splitRead G2 spG) (hpg : psdAt spG)
    (hL : splitRead (matAdd (matScale W G2) M2) spB)
    (hpL : psdAt spB)
    (hlev : x + s + W ≤ c + y)
    (hsR : splitRead
      (siteDatum (matAdd Q (matScale y G2)) (matScale (x + s) G2)) spR)
    (hD : splitRead (blockJoin
      (siteDatum (matAdd P (matScale y G1)) (matScale (x + cw) G1))
      (elim.nullMat k m)
      (siteDatum (matAdd Q (matScale y G2)) (matScale (x + s) G2))) spD)
    (hd : splitRead (siteDatum
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd P (matScale y G1)) (matScale (x + cw) G1))
        (elim.nullMat k m)
        (siteDatum (matAdd Q (matScale y G2)) (matScale (x + s) G2))))
      spd) :
    psdAt spF := by
  have hrPsd : psdAt spR :=
    truncation.removed_psd Q De M2 G2 c W (x + s) y spDi spG spB spR
      hQt hdi hpdi hgB hpg hL hpL hlev hsR
  have hr : countAtPair Q G2 (x + s) y 0 spR := ⟨hQ, hG2, hsR, hrPsd⟩
  have hf : countAtPair H G x y (revAt spF) spF := ⟨hH, hG, hsF, rfl⟩
  have hle := truncation.count_shift_le H G M M1 M2 P G1 Q G2 B
    x y cw W s (revAt spF) 0 spU spL spF spD spd spH spR hcap hMt hGt
    hM1 hM2l hG1 hG2 hB hBr htieD hf hh hr hD hd
  show revAt spF = 0
  exact Nat.le_antisymm hle (Nat.zero_le _)

/-- The window reaches the cut (`thm:gappos`(iii), (v);
`thm:flatstep`'s identification at `lem:speccut`): at one located
root list read both ways — the count identity's factorization in
the window's top count certificate and the diagonalizing
congruence, `lem:split`'s one list — a flat window at the ground
multiplicity holds the edge below its top, the below count squeezed
from above by the level monotonicity and from below by the kernel
roots, every kernel root below every edge, and the spectral read
closes the cut at any stated split of the cut's site datum, the cut
tie landed whole (`flatstep.cutTie_of_edge`). -/
theorem windowCut {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos) (g : Nat)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hker : split.rootsAtKernel (l.map (fun r => (r.1, r.2.1))) = g)
    (tx ty : Pos) (spt : Split n)
    (hct : split.countRead Et (idMat n)
      (l.map (fun r => (r.1, r.2.1))) tx ty spt)
    (hgt : revAt spt = g) (het : E0 * p * ty ≤ tx * q)
    (sp : Split n)
    (hsp : splitRead (siteDatum (matScale q (matMul Et Et))
        (matScale (E0 * p) Et)) sp) :
    speccut.cutTie Et (l.map (fun r => (r.1, r.2.1))) E0 p q sp :=
  flatstep.cutTie_of_edge Et T Tw l E0 p q g hd hker
    (Nat.le_antisymm
      (Nat.le_trans (split.rootsBelow_mono _ (E0 * p) q tx ty het)
        (Nat.le_of_eq (hct.2.2.2.2.2.symm.trans hgt)))
      (Nat.le_trans (Nat.le_of_eq hker.symm)
        (split.kernel_le_below _ (E0 * p) q)))
    sp hsp

/-! The flat window across the truncation (`thm:truncation`; `thm:gappos`(iii)):
a compression lowers each count and each level's downward shift is at most
the shift cap, so the two cuts' values bracket each other at the priced
width, the flat window carried each way with one end moved by the cap. -/

/-- The removed block's floor tie at a level below the top: the top's
tie `tx + ς + W ≤ c + ty` descends to the anchor `⟨ax : ay⟩` sitting
below the lowered top by the margin. -/
private theorem tieBelow (ax ay tx ty s W c cw mg : Pos)
    (hlev : tx + s + W ≤ c + ty) (hmg : ax + (ty + cw) + mg = tx + ay) :
    ax + s + W ≤ c + ay := by
  have e : ax + s + W + (cw + mg) + ty = tx + s + W + ay := by
    rw [ground.add_assoc ax s W, ground.add_right_comm ax (s + W) (cw + mg),
      ground.add_right_comm (ax + (cw + mg)) (s + W) ty,
      ground.add_assoc ax (cw + mg) ty, ground.add_right_comm cw mg ty,
      ground.add_comm cw ty, ← ground.add_assoc ax (ty + cw) mg, hmg,
      ground.add_right_comm (tx + s) W ay, ground.add_right_comm tx s ay,
      ground.add_assoc (tx + ay) s W]
  have h1 : tx + s + W + ay ≤ c + ty + ay := ground.posLeAdd hlev (Or.inl rfl)
  rw [← e, ground.add_right_comm c ty ay] at h1
  exact ground.le_trans (ground.posLeSelfAdd (ax + s + W) (cw + mg))
    (ground.posLeCancelR h1)

/-- The top's tie lowered by the shift cap: `tx + ς + W ≤ c + (ty + c_W)`. -/
private theorem tieLowered (tx ty s W c cw : Pos)
    (hlev : tx + s + W ≤ c + ty) :
    tx + s + W ≤ c + (ty + cw) := by
  rw [← ground.add_assoc c ty cw]
  exact ground.le_trans hlev (ground.posLeSelfAdd (c + ty) cw)

/-- The flat window transports across the truncation at the priced
width (`thm:truncation`: a compression lowers each count, each
level's downward shift is at most `c_W`, so the two cuts' values
bracket each other at the priced width; `thm:gappos`(iii)): at the
magnetic cap, the polarization tie at the two levels and the removed
block's floor at the top's tie, the head's flat window from the
anchor `⟨ax : ay⟩` to the top `⟨tx : ty⟩` at the count `n` reads at
the whole window at the anchor and at the top lowered by the shift
cap, `⟨tx : ty + c_W⟩` — the anchor's count squeezed between the
compression side (`truncation.count_head_le`) and the shift side at
the anchor raised by `c_W` (`truncation.count_shift_le`, the head
flat there by the monotone read), the lowered top's between the
shift side at the crossed top (`certconstruct.countAtPair_cross`)
and the anchor's own (`certconstruct.countAtPair_mono`), the
removed block vacant at both levels at its floor
(`truncation.removed_psd`), and the level order kept at the width
beyond `c_W`. -/
theorem flat_shift {k m : Nat} (H G M M1 M2 P G1 Q De G2 B : Mat)
    (ax ay tx ty cw W s c : Pos) (n na nt nm : Nat)
    (spU spL : Split (k + m))
    (spHa spHt spHm spG1 : Split k)
    (spRa spRt spDi spG spB : Split m)
    (spDa spda spDt spdt spA spT spGf : Split (k + m))
    (hcap : capAt M (matScale W G) spU spL)
    (hMt : matOneValue M (blockJoin M1 B M2))
    (hGt : matOneValue G (blockJoin G1 (elim.nullMat k m) G2))
    (hM1 : sqAt M1 k) (hM2l : M2.length = m)
    (hG1 : sqAt G1 k) (hG2 : sqAt G2 m)
    (hB : B.length = k) (hBr : rowsLen m B)
    (hH : sqAt H (k + m)) (hG : sqAt G (k + m)) (hQ : sqAt Q m)
    (hG1r : splitRead G1 spG1) (hG1p : psdAt spG1)
    (hGr : splitRead G spGf) (hGp : psdAt spGf)
    (hw : vacFlat P G1 ax ay tx ty n spHa spHt)
    (hhm : countAtPair P G1 (ax + cw) ay nm spHm)
    (hQt : matOneValue Q (matAdd De M2))
    (hdi : splitRead (siteDatum De (matScale c G2)) spDi) (hpdi : psdAt spDi)
    (hgB : splitRead G2 spG) (hpg : psdAt spG)
    (hL : splitRead (matAdd (matScale W G2) M2) spB) (hpL : psdAt spB)
    (hlev : tx + s + W ≤ c + ty)
    (hsRa : splitRead (levelDatum Q G2 (ax + s) ay) spRa)
    (hsRt : splitRead (levelDatum Q G2 (tx + s) (ty + cw)) spRt)
    (htieA : matOneValue (levelDatum H G ax ay)
      (blockJoin (levelDatum P G1 ax ay) B (levelDatum Q G2 ax ay)))
    (htieDA : matOneValue (matScale s (siteDatum (levelDatum H G ax ay)
        (blockJoin (levelDatum P G1 (ax + cw) ay) (elim.nullMat k m)
          (levelDatum Q G2 (ax + s) ay))))
      (truncation.shiftSite W s B G1 G2))
    (hDa : splitRead (blockJoin (levelDatum P G1 (ax + cw) ay) (elim.nullMat k m)
      (levelDatum Q G2 (ax + s) ay)) spDa)
    (hda : splitRead (siteDatum (levelDatum H G ax ay)
      (blockJoin (levelDatum P G1 (ax + cw) ay) (elim.nullMat k m)
        (levelDatum Q G2 (ax + s) ay))) spda)
    (htieDT : matOneValue (matScale s (siteDatum (levelDatum H G tx (ty + cw))
        (blockJoin (levelDatum P G1 (tx + cw) (ty + cw)) (elim.nullMat k m)
          (levelDatum Q G2 (tx + s) (ty + cw)))))
      (truncation.shiftSite W s B G1 G2))
    (hDt : splitRead (blockJoin (levelDatum P G1 (tx + cw) (ty + cw)) (elim.nullMat k m)
      (levelDatum Q G2 (tx + s) (ty + cw))) spDt)
    (hdt : splitRead (siteDatum (levelDatum H G tx (ty + cw))
      (blockJoin (levelDatum P G1 (tx + cw) (ty + cw)) (elim.nullMat k m)
        (levelDatum Q G2 (tx + s) (ty + cw)))) spdt)
    (hA : countAtPair H G ax ay na spA)
    (hT : countAtPair H G tx (ty + cw) nt spT)
    (hmargin : ax + (ty + cw) < tx + ay) :
    vacFlat H G ax ay tx (ty + cw) n spA spT := by
  obtain ⟨mg, hmg⟩ := hmargin
  have hP : sqAt P k := hw.1.1
  -- the removed block vacant at the two levels
  have hrA : countAtPair Q G2 (ax + s) ay 0 spRa :=
    ⟨hQ, hG2, hsRa, truncation.removed_psd Q De M2 G2 c W (ax + s) ay
      spDi spG spB spRa hQt hdi hpdi hgB hpg hL hpL
      (tieBelow ax ay tx ty s W c cw mg hlev hmg) hsRa⟩
  have hrT : countAtPair Q G2 (tx + s) (ty + cw) 0 spRt :=
    ⟨hQ, hG2, hsRt, truncation.removed_psd Q De M2 G2 c W (tx + s) (ty + cw)
      spDi spG spB spRt hQt hdi hpdi hgB hpg hL hpL
      (tieLowered tx ty s W c cw hlev) hsRt⟩
  -- the anchor: the compression side and the shift side
  have h1 : n ≤ na :=
    truncation.count_head_le H G P G1 B Q G2 ax ay n na spHa spA hB htieA hw.1 hA
  have h2 : na ≤ nm :=
    truncation.count_shift_le H G M M1 M2 P G1 Q G2 B ax ay cw W s na nm
      spU spL spA spDa spda spHm spRa hcap hMt hGt hM1 hM2l hG1 hG2 hB hBr
      htieDA hA hhm hrA hDa hda
  have hmH := levelDiff_split P G1 hP hG1 spG1 hG1r hG1p (ax + cw) ay tx ty mg
    (by rw [ground.add_assoc ax cw ty, ground.add_comm cw ty]; exact hmg)
  have h3 : nm ≤ n :=
    countAtPair_mono P P G1 (ax + cw) ay tx ty nm n spHm spHt _ hmH.1 hmH.2 hhm hw.2.1
  -- the lowered top: the shift side at the crossed top and the anchor's read
  have h4 : nt ≤ n :=
    truncation.count_shift_le H G M M1 M2 P G1 Q G2 B tx (ty + cw) cw W s nt n
      spU spL spT spDt spdt spHt spRt hcap hMt hGt hM1 hM2l hG1 hG2 hB hBr
      htieDT hT (countAtPair_cross P G1 cw tx ty n spHt hw.2.1) hrT hDt hdt
  have hmF := levelDiff_split H G hH hG spGf hGr hGp ax ay tx (ty + cw) mg hmg
  have h5 : na ≤ nt :=
    countAtPair_mono H H G ax ay tx (ty + cw) na nt spA spT _ hmF.1 hmF.2 hA hT
  have hna : na = n := Nat.le_antisymm (Nat.le_trans h2 h3) h1
  have hnt : nt = n := Nat.le_antisymm h4 (Nat.le_trans (Nat.le_of_eq hna.symm) h5)
  exact ⟨hna ▸ hA, hnt ▸ hT, hw.2.2.1, ⟨mg, hmg⟩⟩

/-- The flat window compresses across the truncation at the priced
width (`thm:truncation`'s bracket read the other way; `lem:dualtrunc`):
the whole window's flat window from the anchor `⟨ax : ay⟩` to the
top `⟨tx : ty⟩` at the count `n` reads at the head at the anchor
raised by the shift cap, `⟨ax + c_W : ay⟩`, and at the top — the
raised anchor's count at or beyond the whole's anchor count by the
shift side (`truncation.count_shift_le`), the top's at or below the
whole's by the compression side (`truncation.count_head_le`), the
two squeezed by the head's monotone read, the removed block vacant
at the anchor's level at its floor (`truncation.removed_psd`), and
the level order kept at the width beyond `c_W`. -/
theorem flat_compress {k m : Nat} (H G M M1 M2 P G1 Q De G2 B : Mat)
    (ax ay tx ty cw W s c : Pos) (n na nt : Nat)
    (spU spL : Split (k + m))
    (spHa spHt spG1 : Split k)
    (spRa spDi spG spB : Split m)
    (spDa spda spA spT : Split (k + m))
    (hcap : capAt M (matScale W G) spU spL)
    (hMt : matOneValue M (blockJoin M1 B M2))
    (hGt : matOneValue G (blockJoin G1 (elim.nullMat k m) G2))
    (hM1 : sqAt M1 k) (hM2l : M2.length = m)
    (hG1 : sqAt G1 k) (hG2 : sqAt G2 m)
    (hB : B.length = k) (hBr : rowsLen m B)
    (hQ : sqAt Q m)
    (hG1r : splitRead G1 spG1) (hG1p : psdAt spG1)
    (hw : vacFlat H G ax ay tx ty n spA spT)
    (hha : countAtPair P G1 (ax + cw) ay na spHa)
    (hht : countAtPair P G1 tx ty nt spHt)
    (hQt : matOneValue Q (matAdd De M2))
    (hdi : splitRead (siteDatum De (matScale c G2)) spDi) (hpdi : psdAt spDi)
    (hgB : splitRead G2 spG) (hpg : psdAt spG)
    (hL : splitRead (matAdd (matScale W G2) M2) spB) (hpL : psdAt spB)
    (hlev : tx + s + W ≤ c + ty)
    (hsRa : splitRead (levelDatum Q G2 (ax + s) ay) spRa)
    (htieT : matOneValue (levelDatum H G tx ty)
      (blockJoin (levelDatum P G1 tx ty) B (levelDatum Q G2 tx ty)))
    (htieDA : matOneValue (matScale s (siteDatum (levelDatum H G ax ay)
        (blockJoin (levelDatum P G1 (ax + cw) ay) (elim.nullMat k m)
          (levelDatum Q G2 (ax + s) ay))))
      (truncation.shiftSite W s B G1 G2))
    (hDa : splitRead (blockJoin (levelDatum P G1 (ax + cw) ay) (elim.nullMat k m)
      (levelDatum Q G2 (ax + s) ay)) spDa)
    (hda : splitRead (siteDatum (levelDatum H G ax ay)
      (blockJoin (levelDatum P G1 (ax + cw) ay) (elim.nullMat k m)
        (levelDatum Q G2 (ax + s) ay))) spda)
    (hmargin : ax + cw + ty < tx + ay) :
    vacFlat P G1 (ax + cw) ay tx ty n spHa spHt := by
  obtain ⟨mg, hmg⟩ := hmargin
  have hP : sqAt P k := hha.1
  have hmg' : ax + (ty + cw) + mg = tx + ay := by
    rw [← ground.add_assoc ax ty cw, ground.add_right_comm ax ty cw]
    exact hmg
  have hrA : countAtPair Q G2 (ax + s) ay 0 spRa :=
    ⟨hQ, hG2, hsRa, truncation.removed_psd Q De M2 G2 c W (ax + s) ay
      spDi spG spB spRa hQt hdi hpdi hgB hpg hL hpL
      (tieBelow ax ay tx ty s W c cw mg hlev hmg') hsRa⟩
  have h1 : n ≤ na :=
    truncation.count_shift_le H G M M1 M2 P G1 Q G2 B ax ay cw W s n na
      spU spL spA spDa spda spHa spRa hcap hMt hGt hM1 hM2l hG1 hG2 hB hBr
      htieDA hw.1 hha hrA hDa hda
  have h2 : nt ≤ n :=
    truncation.count_head_le H G P G1 B Q G2 tx ty nt n spHt spT hB htieT hht hw.2.1
  have hmH := levelDiff_split P G1 hP hG1 spG1 hG1r hG1p (ax + cw) ay tx ty mg hmg
  have h3 : na ≤ nt :=
    countAtPair_mono P P G1 (ax + cw) ay tx ty na nt spHa spHt _ hmH.1 hmH.2 hha hht
  have hna : na = n := Nat.le_antisymm (Nat.le_trans h3 h2) h1
  have hnt : nt = n := Nat.le_antisymm h2 (Nat.le_trans h1 h3)
  exact ⟨hna ▸ hha, hnt ▸ hht, hw.2.2.1, ⟨mg, hmg⟩⟩

end gappos
