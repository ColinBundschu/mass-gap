import MassGap.Flatstep
import MassGap.Cellcount
import MassGap.Truncation
import MassGap.Decimation
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
`lem:cellcount`'s carrier: on a cell certified at the window's two
level carriers each counting function is a cell function read once,
so the sampled flat window's count holds at every point
(`cellWindow`, `cellcount.cover_const` at the two carriers), and on
a cell certified at one carrier a sampled positive-semidefinite
read holds at every point (`cellPsd`), the cut's per-cell coverage
read.  One root-free chain of located cells carries the count
whole (clause (ii)'s located cells at clause (iv)'s count read):
a chain of cells at shared endpoints, each with its cover and its
sample at the stated count (`chainRead`), reads that count at
every point from the chain's foot to its top (`chainCount`, the
positive-semidefinite instance `chainPsd`), the fold locating the
point by the composite order's totality.

The cutoff's price closes at the cut (clause (iii)): at
`thm:truncation`'s cap and polarization tie, a window whose
compression reads the cut at the level raised by the cofactor width
reads the cut itself at the level — the counting comparison of
`truncation.count_shift_le` at the compression's vacant count, the
removed block's vacancy derived at the admissible cutoff's data
(`truncCut`), the bracket display
`E₀ς𝒦_Λ ≤ E₀ς𝒦(v) + β²#p²d_θ²` realized at that one comparison.

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

The priced cap tier reads (v)'s cap at the identity gram: `magCap`
and `foldCap`, the entrywise magnitude cap and the pencil's
derivative-fold cap as decidable reads, and `capId_lo`/`capId_hi`,
the site datum of the scaled identity against an entrywise-capped
symmetric datum and their sum, every split positive semidefinite at
the count's clearing `o·e ≤ ρ` — the dominance comparison priced by
the cap over the peeled rows (`decimation.dom_quad` at the joined
row's fold, the cap rejoined at the diagonal key) with
`lem:inertia`'s witness refused.

The closed-union tier reads (ii)'s boundary clause at the chain's
carrier: `Piece`, a segment's root-free cell chain or a junction — a
located boundary point at its own split with the priced tie into a
flanking positive-semidefinite sample — with `startsAt` the anchored
head, `closedRead` the union's decidable read, `closedHi` its top,
`closedGaps` the committed boundaries' open gaps, and `closedPsd`
the walk: at an anchored occupied list every point from the foot to
the top reads positive semidefinite at any stated split, the
pieces' own reads with the gap hypothesis the consumer's, the
vacant order outright and the covers' brackets keeping their order
at an occupied width.

The gap tier reads (v)'s counting sandwich at a committed gap: an
anchored margin certificate at one flank — the scaled identity's
site datum against the anchor's evaluation, positive semidefinite —
absorbs the width the entry price sets, and every split at every
pair point strictly inside the gap reads positive semidefinite
(`gapPsd_lo` at the lower flank, `gapPsd_hi` at the upper through
the segment's magnitude read `stage.cmag_seg` and the swap-blind
magnitude).  Per entry the two-point price `stage.evalC_gap_le`
prices the value gap by the derivative fold against the committed
width, the power absorbed at the strict fold base, and the
common-clearing representatives read the priced value gap as the
width-denominator-scaled site datum's entry over the joint clearing
power — the committed comparison `o·(F·W)·c^K ≤ ρ·d_W` pricing the
fold against the width with the margin absorbing it, the roaming
factor riding both sides of the descended cap.

The interior's whole read composes the tiers at one window's
carrier ((ii) and (v) at one statement): `GapCert` a gap's
certificate with `gapRead`/`gapsRead` the committed gaps' decidable
reads, and `interiorPsd`: at an anchored occupied piece list whose
gaps past the anchored head each hold their certificate, every pair
point from the foot to the top reads every split of its evaluation
positive semidefinite — the head gap its own vacancy at the start
read, the point binder the consumer's own ray.
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

instance (e : BPair) (S : Mat) : Decidable (magCap e S) :=
  inferInstanceAs (Decidable (_ = _))

/-- The pencil's fold cap (`thm:gappos`(v)'s cap pricing): every
entry's derivative coefficient fold at the stated bound sits at or
below the one committed read. -/
def foldCap (S : split.PMat) (N D F : BPair) : Prop :=
  (S.all (fun r => r.all (fun p => decide
    (windowsep.magFold (poly.deriv p) N D ≤ F)))) = true

instance (S : split.PMat) (N D F : BPair) :
    Decidable (foldCap S N D F) :=
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

/-- A member joined to its memberwise swap reads the sum's unit. -/
private theorem addSwapB (x : BPair) :
    (x + x.swap).oneValue BPair.unit := by
  show x.fst + x.snd + Pos.one = Pos.one + (x.snd + x.fst)
  rw [ground.add_comm x.fst x.snd,
    ground.add_comm (x.snd + x.fst) Pos.one]

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
    rw [inertia.idMat_row o i hi, elim.length_idRow o i]
    exact hj
  show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
      ((idMat o).map (fun r => r.map (fun x => x.scale rho))) i) j
    = (if j = i then BPair.ofNat 1 else BPair.unit).scale rho
  rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
      (fun r => r.map (fun x => x.scale rho)) (idMat o) i hil,
    ground.getAt_map BPair.unit BPair.unit
      (fun x => x.scale rho) _ j hjl,
    inertia.getAt_idMat o i j hi hj]

/-- The scaled identity keeps the stated order. -/
private theorem sqAt_scaleId (o : Nat) (rho : ground.Pos) :
    sqAt (matScale rho (idMat o)) o :=
  inertia.sqAt_matScale o rho (idMat o)
    (inertia.sqAt_idMat o)

/-- The symmetric datum's entry exchange at stated keys. -/
private theorem entSym (o : Nat) (S : Mat) (hS : sqAt S o)
    (hsym : matOneValue S (transposeM S)) (i j : Nat)
    (hi : i < o) (hj : j < o) :
    (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) S i) j).oneValue
      (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) S j) i) := by
  have e := poly.oneValue_getAt j
    (elim.matOne_entries S (transposeM S) hsym i
      (by rw [elim.sqAt_len hS]; exact hi))
  rw [elim.getAt_transposeM BPair.unit S
    (elim.rowsLen_of_sqAt hS) i j hi
    (by rw [elim.sqAt_len hS]; exact hj)] at e
  exact e

/-- The joined pencil at the scaled identity keeps the entrywise
symmetry: both summands keep their own and the sum keeps theirs. -/
private theorem symAdd (o : Nat) (S : Mat) (rho : ground.Pos)
    (hS : sqAt S o) (hsym : matOneValue S (transposeM S)) :
    matOneValue (matAdd (matScale rho (idMat o)) S)
      (transposeM (matAdd (matScale rho (idMat o)) S)) := by
  have hsI : matOneValue (transposeM (matScale rho (idMat o)))
      (matScale rho (idMat o)) :=
    elim.matOne_trans
      (inertia.transposeM_matScale rho o (idMat o)
        (elim.rowsLen_of_sqAt (inertia.sqAt_idMat o)))
      (inertia.matScale_matOne rho
        (by rw [inertia.transposeM_idMat o]; exact elim.matOne_refl _))
  exact elim.matOne_symm
    (elim.transposeM_matAdd_sym (matScale rho (idMat o)) S
      (sqAt_scaleId o rho) hS hsI (elim.matOne_symm hsym))

/-- The priced cap's quadratic floor at the scaled identity: the
joined datum's form clears the vacant fold at every stated vector,
the dominance comparison priced by the cap. -/
private theorem capQuad (o : Nat) (S : Mat) (e : BPair)
    (rho : ground.Pos)
    (hS : sqAt S o) (hsym : matOneValue S (transposeM S))
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
        + ground.getAt BPair.unit (List.replicate o BPair.unit) i
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
    rw [hrow, ground.getAt_replicate_self BPair.unit o i,
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
        (BPair.add_congr (BPair.oneValue_refl _) (addSwapB e))
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
    refine ground.leB_congr_left
      (BPair.oneValue_symm (BPair.add_unit _)) ?_
    exact ground.leB_trans hmv
      (ground.leB_add (Or.inl hscale1) hswapii)
  have hDsq : sqAt (matAdd (matScale rho (idMat o)) S) o :=
    elim.sqAt_matAdd o _ S hIsq hS
  exact decimation.dom_quad
    (matAdd (matScale rho (idMat o)) S) o
    (List.replicate o BPair.unit) hDsq
    (ground.length_replicate BPair.unit o)
    (symAdd o S rho hS hsym) hdom u hu

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

/-- The memberwise swap keeps the entrywise symmetry. -/
private theorem swapSym (o : Nat) (S : Mat) (hS : sqAt S o)
    (hsym : matOneValue S (transposeM S)) :
    matOneValue (elim.matSwap S) (transposeM (elim.matSwap S)) := by
  have hSsq := elim.sqAt_matSwap o S hS
  have hDl := elim.sqAt_len hSsq
  have hDr := elim.rowsLen_of_sqAt hSsq
  have hTl : (transposeM (elim.matSwap S)).length = o :=
    elim.transposeLen _ hDr hDl
  have hTr : elim.rowsLen o (transposeM (elim.matSwap S)) := by
    have h0 := elim.rowsLen_transposeM (elim.matSwap S)
    rw [hDl] at h0
    exact h0
  refine elim.matOne_of_entries _ _ o hDl hDr hTl hTr ?_
  intro i j hi hj
  have hent : ∀ a b : Nat, a < o → b < o →
      ground.getAt BPair.unit (ground.getAt ([] : List BPair)
          (elim.matSwap S) a) b
        = (ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) S a) b).swap := by
    intro a b ha hb
    have hal : a < S.length := by
      rw [elim.sqAt_len hS]
      exact ha
    have hbl : b < (ground.getAt ([] : List BPair) S a).length := by
      rw [elim.rowsLen_getAt _ a (elim.rowsLen_of_sqAt hS) hal]
      exact hb
    show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (S.map (fun r => r.map BPair.swap)) a) b = _
    rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
        (fun r => r.map BPair.swap) S a hal,
      ground.getAt_map BPair.unit BPair.unit BPair.swap _ b hbl]
  rw [elim.getAt_transposeM BPair.unit _ hDr i j hi
      (by rw [hDl]; exact hj),
    hent i j hi hj, hent j i hj hi]
  exact ground.swap_congr (entSym o S hS hsym i j hi hj)

/-- (`thm:gappos`(v)'s priced cap, the upper side at the identity
gram): the scaled identity joined to an entrywise-capped symmetric
datum reads every split positive semidefinite at the count's
clearing. -/
theorem capId_hi (o : Nat) (S : Mat) (e : BPair)
    (rho : ground.Pos) (sp : Split o)
    (hS : sqAt S o) (hsym : matOneValue S (transposeM S))
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

/-! The gap tier (`thm:gappos`(v)'s counting sandwich at a committed
gap): the arithmetic privates, the quadratic-form reads, the
entrywise price at the common clearing, and the two anchored gap
theorems. -/

/-- (`thm:gappos`(v)'s priced cap, the lower side at the identity
gram): the site datum of the scaled identity against an
entrywise-capped symmetric datum reads every split positive
semidefinite at the count's clearing. -/
theorem capId_lo (o : Nat) (S : Mat) (e : BPair)
    (rho : ground.Pos) (sp : Split o)
    (hS : sqAt S o) (hsym : matOneValue S (transposeM S))
    (hcap : magCap e S)
    (hcl : BPair.ofNat o * e ≤ BPair.ofPos rho)
    (h : splitRead (siteDatum (matScale rho (idMat o)) S) sp) :
    psdAt sp :=
  capId_hi o (elim.matSwap S) e rho sp
    (elim.sqAt_matSwap o S hS) (swapSym o S hS hsym)
    (magCap_swap hcap) hcl h

/-- The natural one keeps under every power of a datum at or
beyond it. -/
private theorem oneLe_bpow {D : BPair} (h : BPair.ofNat 1 ≤ D) :
    ∀ L : Nat, BPair.ofNat 1 ≤ ground.bpow D L
  | 0 => ground.leB_refl _
  | L + 1 => by
    refine ground.leB_congr_right
      (BPair.oneValue_symm (BPair.norm_oneValue (D * ground.bpow D L)))
      ?_
    refine ground.leB_trans h ?_
    refine ground.leB_congr_left (BPair.mul_one_read D) ?_
    exact ground.leB_mulR
      (ground.leB_trans (ground.leB_of_lt (ground.unitLtOfPos _)) h)
      (oneLe_bpow h L)

/-- A summand keeping under its own join reads the further summand
at or above the sum's unit. -/
private theorem unitLe_of_le_add {a x : BPair} (h : a ≤ a + x) :
    BPair.unit ≤ x := by
  have h0 : a.fst + (a.snd + x.snd) ≤ a.fst + x.fst + a.snd := h
  rw [← ground.add_assoc a.fst a.snd x.snd] at h0
  rw [ground.add_comm (a.fst + a.snd) x.snd] at h0
  rw [ground.add_comm a.fst x.fst, ground.add_assoc x.fst a.fst a.snd]
    at h0
  have h2 : x.snd ≤ x.fst := ground.posLeCancelR h0
  show Pos.one + x.snd ≤ x.fst + Pos.one
  rw [ground.add_comm Pos.one x.snd]
  exact ground.posLeAdd h2 (Or.inl rfl)

/-- A nonnegative composite keeps under its product with a datum at
or beyond the natural one. -/
private theorem cleAbsorbC {x : ground.CPair} {c : BPair}
    (hx : stage.unitC ≤ x) (hc : BPair.ofNat 1 ≤ c) :
    x ≤ x * stage.ofB c := by
  obtain ⟨a, b⟩ := x
  have ha : BPair.unit ≤ a := stage.unitC_le_fst hx
  have h1 : a * BPair.ofNat 1 ≤ a * c := ground.leB_mulR ha hc
  show a.scale (b * Pos.one) ≤ (a * c).scale b
  refine ground.leB_congr ?_ (BPair.oneValue_refl ((a * c).scale b))
    (ground.leB_scale (ground.leB_congr_left
      (BPair.mul_one_read a) h1) b)
  refine BPair.oneValue_of_eq ?_
  rw [ground.mul_one b]

/-- The width from a covered point up to a further one sits at or
above the composite unit. -/
private theorem cleUnitAdd {u v : ground.CPair} (h : v ≤ u) :
    stage.unitC ≤ u + ground.CPair.swap v := by
  obtain ⟨un, uc⟩ := u
  obtain ⟨vn, vc⟩ := v
  have h0 : vn.scale uc ≤ un.scale vc := h
  have h1 : BPair.unit ≤ un.scale vc + (vn.swap).scale uc := by
    refine ground.leB_unit_add (V := (vn.swap).scale uc) ?_
    show vn.scale uc ≤ un.scale vc
    exact h0
  show BPair.unit.scale (uc * vc)
    ≤ (un.scale vc + (vn.swap).scale uc).scale Pos.one
  refine ground.leB_congr ?_
    (BPair.oneValue_of_eq
      (BPair.scale_one (un.scale vc + (vn.swap).scale uc)).symm) h1
  show Pos.one + Pos.one * (uc * vc) = Pos.one * (uc * vc) + Pos.one
  exact ground.add_comm Pos.one (Pos.one * (uc * vc))

/-- The composite sum keeps a second-summand comparison. -/
private theorem cleAddR {x y y' : ground.CPair} (h : y ≤ y') :
    x + y ≤ x + y' := 
  ground.CPair.le_add (ground.CPair.le_refl x) h

/-- The composite magnitude is blind to the memberwise swap. -/
private theorem cmagSwapC (z : ground.CPair) :
    (stage.cmag (ground.CPair.swap z)).oneValue (stage.cmag z) := by
  obtain ⟨n, d⟩ := z
  refine ground.CPair.oneValue_trans (stage.cmag_num n.swap d) ?_
  refine ground.CPair.oneValue_trans ?_
    (ground.CPair.oneValue_symm (stage.cmag_num n d))
  rw [windowsep.mag_swap n]
  exact ground.CPair.oneValue_refl _

/-- The reversed gap is the gap's own memberwise swap. -/
private theorem flipEq (x y : ground.CPair) :
    y + ground.CPair.swap x
      = ground.CPair.swap (x + ground.CPair.swap y) := by
  obtain ⟨xn, xc⟩ := x
  obtain ⟨yn, yc⟩ := y
  show CPair.mk (yn.scale xc + (xn.swap).scale yc) (yc * xc)
    = CPair.mk ((xn.scale yc + (yn.swap).scale xc).swap) (xc * yc)
  rw [show (xn.scale yc + (yn.swap).scale xc).swap
      = ((xn.scale yc).swap + ((yn.swap).scale xc).swap) from
      (BPair.swap_add (xn.scale yc) ((yn.swap).scale xc)).symm,
    show ((yn.swap).scale xc).swap = yn.scale xc from rfl,
    show (xn.scale yc).swap = (xn.swap).scale yc from rfl,
    BPair.add_comm ((xn.swap).scale yc) (yn.scale xc),
    ground.mul_comm yc xc]

/-- The positive rescaling keeps the entrywise symmetry. -/
private theorem symScale (w : ground.Pos) {o : Nat} (M : Mat)
    (hM : sqAt M o) (hsym : matOneValue M (transposeM M)) :
    matOneValue (matScale w M) (transposeM (matScale w M)) := by
  have hL := inertia.sqAt_matScale o w M hM
  have hLl := elim.sqAt_len hL
  have hLr := elim.rowsLen_of_sqAt hL
  have hTl : (transposeM (matScale w M)).length = o :=
    elim.transposeLen _ hLr hLl
  have hTr : elim.rowsLen o (transposeM (matScale w M)) := by
    have h0 := elim.rowsLen_transposeM (matScale w M)
    rw [hLl] at h0
    exact h0
  have hent : ∀ a b : Nat, a < o → b < o →
      ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (matScale w M) a) b
      = (ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) M a) b).scale w := by
    intro a b hao hbo
    have haM : a < M.length := by
      rw [elim.sqAt_len hM]; exact hao
    have hbM : b < (ground.getAt ([] : List BPair) M a).length := by
      rw [elim.rowsLen_getAt _ a (elim.rowsLen_of_sqAt hM) haM]
      exact hbo
    rw [show ground.getAt ([] : List BPair) (matScale w M) a
        = (ground.getAt ([] : List BPair) M a).map
          (fun x => x.scale w) from
        ground.getAt_map ([] : List BPair) ([] : List BPair)
          _ M a haM,
      ground.getAt_map BPair.unit BPair.unit _ _ b hbM]
  refine elim.matOne_of_entries _ _ o hLl hLr hTl hTr ?_
  intro i j hi hj
  rw [elim.getAt_transposeM BPair.unit _ hLr i j hi
      (by rw [hLl]; exact hj),
    hent i j hi hj, hent j i hj hi]
  exact BPair.scale_congr w (entSym o M hM hsym i j hi hj)

/-- The composite lift keeps the at-or-below read. -/
private theorem ofBLe {z z' : BPair} (h : z ≤ z') :
    stage.ofB z ≤ stage.ofB z' := by
  show z.scale Pos.one ≤ z'.scale Pos.one
  exact ground.leB_scale h Pos.one

/-- The fold cap's entry read. -/
private theorem foldCap_entry {S : split.PMat} {N D F : BPair}
    (h : foldCap S N D F) (i j : Nat) (hi : i < S.length)
    (hj : j < (ground.getAt ([] : List poly.Poly) S i).length) :
    windowsep.magFold (poly.deriv (ground.getAt ([] : poly.Poly)
      (ground.getAt ([] : List poly.Poly) S i) j)) N D ≤ F :=
  of_decide_eq_true
    (ground.all_getAt ([] : poly.Poly) _
      (ground.all_getAt ([] : List poly.Poly) _ h i hi) j hj)

/-- The common-clearing representative reads the composite
evaluation: the cleared value at the scaled point over the joint
clearing power is the evaluation at the point itself. -/
private theorem repRead (p : poly.Poly) {K : Nat} (hp : p.length ≤ K + 1)
    (an : BPair) (ac w : ground.Pos) :
    (⟨poly.evalClear p (an * BPair.ofPos w) (ac * w) K,
        ground.Pos.pow (ac * w) K⟩ : ground.CPair).oneValue
      (stage.evalC p ⟨an, ac⟩) := by
  refine ground.CPair.oneValue_trans
    (ground.CPair.num_oneValue
      (BPair.oneValue_symm
        (poly.eval_clearVar p (ac * w) K (an * BPair.ofPos w)))
      (ground.Pos.pow (ac * w) K)) ?_
  refine ground.CPair.oneValue_trans
    (ground.CPair.oneValue_symm
      (stage.evalC_read p K hp (an * BPair.ofPos w) (ac * w))) ?_
  refine ground.CPair.oneValue_trans
    (stage.evalC_point_congr p (ground.CPair.num_oneValue
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm an (BPair.ofPos w)))
        (BPair.ofPos_scale w an)) (ac * w))) ?_
  exact stage.evalC_point_congr p
    (ground.CPair.scale_oneValue an ac w)

/-- The entry price at the common clearing (`thm:gappos`(v)'s cap
sentence per entry): the cleared gap between the roaming point's
value and the anchor's sits within the derivative fold's cap
against the committed width, at the joint clearing power. -/
private theorem capEntry (p : poly.Poly) {K : Nat} (hp : p.length ≤ K + 1)
    (gln : BPair) (glc : ground.Pos) (grn : BPair) (grc : ground.Pos)
    (vn : BPair) (vc : ground.Pos) (N D F : BPair)
    (hD : BPair.unit < D)
    (ha : stage.cmag ⟨gln, glc⟩ * stage.ofB D ≤ stage.ofB N)
    (hb : stage.cmag ⟨grn, grc⟩ * stage.ofB D ≤ stage.ofB N)
    (hFp : windowsep.magFold (poly.deriv p) N D ≤ F)
    (hlv : (⟨gln, glc⟩ : ground.CPair) ≤ ⟨vn, vc⟩)
    (hvr : (⟨vn, vc⟩ : ground.CPair) ≤ ⟨grn, grc⟩) :
    BPair.scale (windowsep.mag
        (poly.evalClear p (vn * BPair.ofPos glc) (vc * glc) K
          + (poly.evalClear p (gln * BPair.ofPos vc)
            (glc * vc) K).swap)) (grc * glc)
      ≤ (F * (grn.scale glc + (gln.swap).scale grc)).scale
        (ground.Pos.pow (vc * glc) K) := by
  have hW : stage.unitC ≤ (⟨grn, grc⟩ : ground.CPair)
      + ground.CPair.swap ⟨gln, glc⟩ :=
    cleUnitAdd (ground.CPair.le_trans hlv hvr)
  have hgap := stage.evalC_gap_le p ⟨gln, glc⟩ ⟨grn, grc⟩ ⟨vn, vc⟩
    N D (ground.leB_of_lt hD) ha hb hlv hvr
  have habs : stage.cmag (stage.evalC p ⟨vn, vc⟩
      + ground.CPair.swap (stage.evalC p ⟨gln, glc⟩))
      ≤ stage.ofB (windowsep.magFold (poly.deriv p) N D)
        * ((⟨grn, grc⟩ : ground.CPair)
          + ground.CPair.swap ⟨gln, glc⟩) :=
    ground.CPair.le_trans
      (cleAbsorbC (stage.unitC_le_cmag _)
        (oneLe_bpow (ground.oneLeOfUnitLt hD)
          ((poly.vnorm (poly.deriv p)).length - 1))) hgap
  have hF2 : stage.ofB (windowsep.magFold (poly.deriv p) N D)
      * ((⟨grn, grc⟩ : ground.CPair) + ground.CPair.swap ⟨gln, glc⟩)
      ≤ stage.ofB F * ((⟨grn, grc⟩ : ground.CPair)
        + ground.CPair.swap ⟨gln, glc⟩) := by
    rw [CPair.mul_comm (stage.ofB (windowsep.magFold (poly.deriv p) N D))
        ((⟨grn, grc⟩ : ground.CPair) + ground.CPair.swap ⟨gln, glc⟩),
      CPair.mul_comm (stage.ofB F)
        ((⟨grn, grc⟩ : ground.CPair) + ground.CPair.swap ⟨gln, glc⟩)]
    exact stage.mulC_le_left hW (ofBLe hFp)
  have hpriced := ground.CPair.le_trans habs hF2
  have hE : (⟨poly.evalClear p (vn * BPair.ofPos glc) (vc * glc) K
      + (poly.evalClear p (gln * BPair.ofPos vc) (glc * vc) K).swap,
      ground.Pos.pow (vc * glc) K⟩ : ground.CPair).oneValue
      (stage.evalC p ⟨vn, vc⟩
        + ground.CPair.swap (stage.evalC p ⟨gln, glc⟩)) := by
    refine ground.CPair.oneValue_trans
      (ground.CPair.oneValue_symm (ground.CPair.add_same
        (poly.evalClear p (vn * BPair.ofPos glc) (vc * glc) K)
        ((poly.evalClear p (gln * BPair.ofPos vc) (glc * vc) K).swap)
        (ground.Pos.pow (vc * glc) K))) ?_
    refine ground.CPair.add_congr (repRead p hp vn vc glc) ?_
    refine ground.CPair.oneValue_trans
      (ground.CPair.den_congr (show ground.Pos.pow (vc * glc) K
        = ground.Pos.pow (glc * vc) K from by
        rw [ground.mul_comm vc glc])) ?_
    exact ground.CPair.swap_congr (repRead p hp gln glc vc)
  have hcm : stage.cmag (⟨poly.evalClear p (vn * BPair.ofPos glc)
      (vc * glc) K
      + (poly.evalClear p (gln * BPair.ofPos vc) (glc * vc) K).swap,
      ground.Pos.pow (vc * glc) K⟩ : ground.CPair)
      ≤ stage.ofB F * ((⟨grn, grc⟩ : ground.CPair)
        + ground.CPair.swap ⟨gln, glc⟩) :=
    ground.CPair.le_congr
      (stage.cmag_congr (ground.CPair.oneValue_symm hE))
      (ground.CPair.oneValue_refl _) hpriced
  have hnum : (⟨windowsep.mag (poly.evalClear p (vn * BPair.ofPos glc)
      (vc * glc) K
      + (poly.evalClear p (gln * BPair.ofPos vc) (glc * vc) K).swap),
      ground.Pos.pow (vc * glc) K⟩ : ground.CPair)
      ≤ stage.ofB F * ((⟨grn, grc⟩ : ground.CPair)
        + ground.CPair.swap ⟨gln, glc⟩) :=
    ground.CPair.le_congr (stage.cmag_num _ _)
      (ground.CPair.oneValue_refl _) hcm
  have h5 : BPair.scale (windowsep.mag
        (poly.evalClear p (vn * BPair.ofPos glc) (vc * glc) K
          + (poly.evalClear p (gln * BPair.ofPos vc)
            (glc * vc) K).swap))
        (Pos.one * (grc * glc))
      ≤ (F * (grn.scale glc + (gln.swap).scale grc)).scale
        (ground.Pos.pow (vc * glc) K) := hnum
  rw [ground.one_mul (grc * glc)] at h5
  exact h5

/-- The site datum of two entrywise-symmetric data keeps the
entrywise symmetry: the swapped summand keeps its own and the sum
keeps theirs. -/
private theorem symSite {o : Nat} (X Y : Mat)
    (hX : sqAt X o) (hY : sqAt Y o)
    (hsX : matOneValue X (transposeM X))
    (hsY : matOneValue Y (transposeM Y)) :
    matOneValue (matAdd X (elim.matSwap Y))
      (transposeM (matAdd X (elim.matSwap Y))) := by
  have hsw : matOneValue (transposeM (elim.matSwap Y))
      (elim.matSwap Y) := by
    rw [elim.transposeM_swap]
    exact elim.matSwap_congr (elim.matOne_symm hsY)
  exact elim.matOne_symm
    (elim.transposeM_matAdd_sym X (elim.matSwap Y) hX
      (elim.sqAt_matSwap o Y hY) (elim.matOne_symm hsX) hsw)

/-- The rescaled datum's entrywise cap at the entries' own scaled
magnitudes. -/
private theorem magCap_scaleOf {o : Nat} (w : ground.Pos)
    (S : Mat) (e : BPair) (hS : sqAt S o)
    (h : ∀ i j : Nat, i < o → j < o →
      BPair.scale (windowsep.mag (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) S i) j)) w ≤ e) :
    magCap e (matScale w S) := by
  refine ground.all_of_getAt ([] : List BPair) _ _ (fun i hi => ?_)
  have hiS : i < S.length := by
    rw [← ground.length_map (fun r => r.map
      (fun x => BPair.scale x w)) S]
    exact hi
  have hio : i < o := by
    rw [← elim.sqAt_len hS]
    exact hiS
  refine ground.all_of_getAt BPair.unit _ _ (fun j hj => ?_)
  have hjS : j < (ground.getAt ([] : List BPair) S i).length := by
    rw [← ground.length_map (fun x => BPair.scale x w)
      (ground.getAt ([] : List BPair) S i)]
    have he : ground.getAt ([] : List BPair) (matScale w S) i
        = (ground.getAt ([] : List BPair) S i).map
          (fun x => BPair.scale x w) :=
      ground.getAt_map ([] : List BPair) ([] : List BPair) _ S i hiS
    rw [← he]
    exact hj
  have hjo : j < o := by
    rw [← elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hS) hiS]
    exact hjS
  rw [show ground.getAt ([] : List BPair) (matScale w S) i
      = (ground.getAt ([] : List BPair) S i).map
        (fun x => BPair.scale x w) from
      ground.getAt_map ([] : List BPair) ([] : List BPair) _ S i hiS,
    ground.getAt_map BPair.unit BPair.unit _ _ j hjS]
  show decide (windowsep.mag ((ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) S i) j).scale w) ≤ e) = true
  rw [windowsep.mag_scale]
  exact decide_eq_true (h i j hio hjo)

/-- The gap's site datum at the common clearing is entrywise capped
at the priced width (`thm:gappos`(v)'s cap sentence at the record's
fold cap). -/
private theorem gapCap {o K : Nat} (S : split.PMat)
    (hsh : cellcount.pShapeAt S o K)
    (gln : BPair) (glc : ground.Pos) (grn : BPair) (grc : ground.Pos)
    (vn : BPair) (vc : ground.Pos) (N D F : BPair)
    (hD : BPair.unit < D)
    (ha : stage.cmag ⟨gln, glc⟩ * stage.ofB D ≤ stage.ofB N)
    (hb : stage.cmag ⟨grn, grc⟩ * stage.ofB D ≤ stage.ofB N)
    (hF : foldCap S N D F)
    (hlv : (⟨gln, glc⟩ : ground.CPair) ≤ ⟨vn, vc⟩)
    (hvr : (⟨vn, vc⟩ : ground.CPair) ≤ ⟨grn, grc⟩) :
    magCap ((F * (grn.scale glc + (gln.swap).scale grc)).scale
        (ground.Pos.pow (vc * glc) K))
      (matScale (grc * glc)
        (matAdd (cellcount.evalPC S (vn * BPair.ofPos glc)
            (vc * glc) K)
          (elim.matSwap (cellcount.evalPC S (gln * BPair.ofPos vc)
            (glc * vc) K)))) := by
  have hXsq := cellcount.evalPC_sqAt hsh (vn * BPair.ofPos glc)
    (vc * glc)
  have hYsq := cellcount.evalPC_sqAt hsh (gln * BPair.ofPos vc)
    (glc * vc)
  refine magCap_scaleOf (grc * glc) _ _
    (elim.sqAt_matAdd o _ _ hXsq (elim.sqAt_matSwap o _ hYsq))
    (fun i j hio hjo => ?_)
  have hiX : i < (cellcount.evalPC S (vn * BPair.ofPos glc)
      (vc * glc) K).length := by
    rw [elim.sqAt_len hXsq]; exact hio
  have hiY : i < (cellcount.evalPC S (gln * BPair.ofPos vc)
      (glc * vc) K).length := by
    rw [elim.sqAt_len hYsq]; exact hio
  have hiS : i < (elim.matSwap (cellcount.evalPC S
      (gln * BPair.ofPos vc) (glc * vc) K)).length := by
    rw [elim.length_matSwap]; exact hiY
  have hiP : i < S.length := by
    rw [cellcount.pShape_len hsh]; exact hio
  have hjX : j < (ground.getAt ([] : List BPair)
      (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K)
        i).length := by
    rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hXsq) hiX]
    exact hjo
  have hjY : j < (ground.getAt ([] : List BPair)
      (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K)
        i).length := by
    rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hYsq) hiY]
    exact hjo
  have hjS : j < (ground.getAt ([] : List BPair)
      (elim.matSwap (cellcount.evalPC S (gln * BPair.ofPos vc)
        (glc * vc) K)) i).length := by
    rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt
      (elim.sqAt_matSwap o _ hYsq)) hiS]
    exact hjo
  rw [elim.getAt_matAdd _ _ i hiX hiS,
    elim.getAt_vecAdd _ _ j hjX hjS,
    show ground.getAt ([] : List BPair)
        (elim.matSwap (cellcount.evalPC S (gln * BPair.ofPos vc)
          (glc * vc) K)) i
      = (ground.getAt ([] : List BPair)
          (cellcount.evalPC S (gln * BPair.ofPos vc)
            (glc * vc) K) i).map BPair.swap from
      ground.getAt_map ([] : List BPair) ([] : List BPair) _ _ i hiY,
    ground.getAt_map BPair.unit BPair.unit BPair.swap _ j hjY,
    cellcount.getAt_evalPC (vn * BPair.ofPos glc) (vc * glc) K S i j,
    cellcount.getAt_evalPC (gln * BPair.ofPos vc) (glc * vc) K S i j]
  exact capEntry (ground.getAt ([] : poly.Poly)
      (ground.getAt ([] : List poly.Poly) S i) j)
    (cellcount.ent_ble hsh i j) gln glc grn grc vn vc N D F hD
    ha hb
    (foldCap_entry hF i j hiP (by
      rw [elim.rowsLen_getAt _ i (cellcount.pShape_rows hsh) hiP]
      exact hjo))
    hlv hvr

/-- The gap's read at the lower anchor (`thm:gappos`(v)'s counting
sandwich at a committed gap): at a gap whose lower endpoint holds
the scaled identity's margin certificate, whose endpoints hold the
committed magnitude bounds, whose entries hold the committed fold
cap, and whose clearing comparison prices the width below the
margin, every split at every pair point strictly inside the gap
reads positive semidefinite — the level's margin absorbing the
sandwich's width. -/
theorem gapPsd_lo {o K : Nat} (S : split.PMat)
    (gln : BPair) (glc : ground.Pos) (grn : BPair) (grc : ground.Pos)
    (N D F : BPair) (rhoM : ground.Pos) (spM : Split o)
    (hsh : cellcount.pShapeAt S o K)
    (hsym : split.pSymAt S o)
    (hD : BPair.unit < D)
    (ha : stage.cmag ⟨gln, glc⟩ * stage.ofB D ≤ stage.ofB N)
    (hb : stage.cmag ⟨grn, grc⟩ * stage.ofB D ≤ stage.ofB N)
    (hF : foldCap S N D F)
    (hM : splitRead (siteDatum (cellcount.evalPC S gln glc K)
      (matScale rhoM (idMat o))) spM)
    (hMp : psdAt spM)
    (hcl : BPair.ofNat o
        * ((F * (grn.scale glc + (gln.swap).scale grc)).scale
          (ground.Pos.pow glc K))
      ≤ (BPair.ofPos rhoM).scale (grc * glc)) :
    ∀ (vn : BPair) (vc : ground.Pos),
    (⟨gln, glc⟩ : ground.CPair) < ⟨vn, vc⟩ →
    (⟨vn, vc⟩ : ground.CPair) < ⟨grn, grc⟩ →
    ∀ sp : Split o,
    splitRead (cellcount.evalPC S vn vc K) sp → psdAt sp := by
  intro vn vc hlv hvr sp hsp
  cases Nat.eq_zero_or_pos (revAt sp) with
  | inl h0 => exact h0
  | inr hpos =>
  obtain ⟨u, hu, hlt⟩ := rev_witness _ sp hsp hpos
  have hlt' : quadForm (cellcount.evalPC S vn vc K) u < BPair.unit := hlt
  have hXsq := cellcount.evalPC_sqAt hsh (vn * BPair.ofPos glc)
    (vc * glc)
  have hYsq := cellcount.evalPC_sqAt hsh (gln * BPair.ofPos vc)
    (glc * vc)
  have hGsq := cellcount.evalPC_sqAt (K := K) hsh gln glc
  have hqX : (quadForm (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K) u).oneValue
      (ground.bpow (BPair.ofPos glc) K * quadForm (cellcount.evalPC S vn vc K) u) :=
    BPair.oneValue_trans
      (elim.dotN_matVec_congrM _ _ u u
        (cellcount.evalPC_scalePoint S o K vn vc glc hsh))
      (inertia.quadForm_scaleB (ground.bpow (BPair.ofPos glc) K) _ u)
  have hqY : (quadForm (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K) u).oneValue
      (ground.bpow (BPair.ofPos vc) K * quadForm (cellcount.evalPC S gln glc K) u) :=
    BPair.oneValue_trans
      (elim.dotN_matVec_congrM _ _ u u
        (cellcount.evalPC_scalePoint S o K gln glc vc hsh))
      (inertia.quadForm_scaleB (ground.bpow (BPair.ofPos vc) K) _ u)
  have hmarg : quadForm (matScale rhoM (idMat o)) u
      ≤ quadForm (cellcount.evalPC S gln glc K) u := by
    have hnl := inertia.psd_all _ spM hM hMp u hu
    have hge : BPair.unit ≤ quadForm (siteDatum (cellcount.evalPC S gln glc K)
        (matScale rhoM (idMat o))) u :=
      ground.leB_of_not_lt hnl
    have hge2 : BPair.unit ≤ quadForm (cellcount.evalPC S gln glc K) u
        + (quadForm (matScale rhoM (idMat o)) u).swap :=
      ground.leB_congr_right
        (inertia.quadForm_site_sq hGsq (sqAt_scaleId o rhoM) hu) hge
    have h3 := ground.leB_of_unit_add hge2
    rw [BPair.swap_swap] at h3
    exact h3
  have hcap := gapCap S hsh gln glc grn grc vn vc N D F hD ha hb hF
    (Or.inr hlv) (Or.inr hvr)
  have hclv : BPair.ofNat o
      * ((F * (grn.scale glc + (gln.swap).scale grc)).scale
        (ground.Pos.pow (vc * glc) K))
      ≤ BPair.ofPos (rhoM * ((grc * glc) * ground.Pos.pow vc K)) := by
    have h1 := ground.leB_scale hcl (ground.Pos.pow vc K)
    refine ground.leB_congr ?_ ?_ h1
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_scale (BPair.ofNat o) _ (ground.Pos.pow glc K),
        BPair.scale_scale,
        BPair.mul_scale (BPair.ofNat o) _
          (ground.Pos.pow (vc * glc) K),
        ground.Pos.pow_mul vc glc K,
        ground.mul_comm (ground.Pos.pow glc K) (ground.Pos.pow vc K)]
    · refine BPair.oneValue_trans (BPair.oneValue_of_eq
        (BPair.scale_scale (BPair.ofPos rhoM) (grc * glc)
          (ground.Pos.pow vc K))) ?_
      refine BPair.oneValue_trans (BPair.oneValue_symm
        (BPair.ofPos_scale ((grc * glc) * ground.Pos.pow vc K)
          (BPair.ofPos rhoM))) ?_
      refine BPair.oneValue_trans (BPair.oneValue_of_eq
        (BPair.mul_comm
          (BPair.ofPos ((grc * glc) * ground.Pos.pow vc K))
          (BPair.ofPos rhoM))) ?_
      exact BPair.ofPos_mul rhoM ((grc * glc) * ground.Pos.pow vc K)
  have hquad := capQuad o
    (matScale (grc * glc) (matAdd (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K) (elim.matSwap (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K))))
    ((F * (grn.scale glc + (gln.swap).scale grc)).scale
      (ground.Pos.pow (vc * glc) K))
    (rhoM * ((grc * glc) * ground.Pos.pow vc K))
    (inertia.sqAt_matScale o (grc * glc) _
      (elim.sqAt_matAdd o _ _ hXsq (elim.sqAt_matSwap o _ hYsq)))
    (symScale (grc * glc) _
      (elim.sqAt_matAdd o _ _ hXsq (elim.sqAt_matSwap o _ hYsq))
      (symSite _ _ hXsq hYsq
        (cellcount.evalPC_symAt S o K (vn * BPair.ofPos glc)
          (vc * glc) hsh hsym)
        (cellcount.evalPC_symAt S o K (gln * BPair.ofPos vc)
          (glc * vc) hsh hsym)))
    hcap hclv u hu
  have h6 : BPair.unit ≤ quadForm
      (matAdd (matScale (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o))
        (matScale (grc * glc) (matAdd (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K) (elim.matSwap (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K))))) u :=
    ground.leB_congr_left
      (elim.dotN_nullL (List.replicate o BPair.unit)
        (List.zipWith (· * ·) u u) (poly.unitTail_replicate o))
      hquad
  have h7 : BPair.unit
      ≤ (quadForm (matScale (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o)) u
        + BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K) u)
        + (BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K) u).swap := by
    refine ground.leB_congr_right ?_ h6
    have hinner : (quadForm (matAdd (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K)
        (elim.matSwap (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K))) u).oneValue
        (quadForm (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K) u + (quadForm (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K) u).swap) :=
      inertia.quadForm_site_sq hXsq hYsq hu
    have hws : (quadForm (matScale (grc * glc)
        (matAdd (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K) (elim.matSwap (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K)))) u).oneValue
        (BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K) u
          + (BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K) u).swap) := by
      refine BPair.oneValue_trans
        (inertia.quadForm_ofPos (grc * glc) _ u) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos (grc * glc)))
          hinner) ?_
      refine BPair.oneValue_of_eq ?_
      rw [BPair.left_distrib, BPair.mul_swap]
    refine BPair.oneValue_trans
      (inertia.quadForm_add_sq (sqAt_scaleId o (rhoM * ((grc * glc) * ground.Pos.pow vc K)))
        (inertia.sqAt_matScale o (grc * glc) _
          (elim.sqAt_matAdd o _ _ hXsq (elim.sqAt_matSwap o _ hYsq)))
        hu) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) hws) ?_
    exact BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm
  have hCle := ground.leB_of_unit_add h7
  rw [BPair.swap_swap] at hCle
  have hqI : (quadForm (matScale (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o)) u).oneValue
      (BPair.ofPos ((grc * glc) * ground.Pos.pow vc K)
        * quadForm (matScale rhoM (idMat o)) u) := by
    refine BPair.oneValue_trans
      (inertia.quadForm_ofPos (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o) u) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_symm
        (BPair.ofPos_mul rhoM ((grc * glc) * ground.Pos.pow vc K)))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (by
      rw [BPair.mul_comm (BPair.ofPos rhoM)
          (BPair.ofPos ((grc * glc) * ground.Pos.pow vc K)),
        BPair.mul_assoc])) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (inertia.quadForm_ofPos rhoM (idMat o) u))
  have hAC : quadForm (matScale (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o)) u
      ≤ BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (gln * BPair.ofPos vc) (glc * vc) K) u := by
    have h8 : BPair.ofPos ((grc * glc) * ground.Pos.pow vc K)
        * quadForm (matScale rhoM (idMat o)) u
        ≤ BPair.ofPos ((grc * glc) * ground.Pos.pow vc K)
          * quadForm (cellcount.evalPC S gln glc K) u :=
      ground.leB_mulR
        (ground.leB_of_lt (ground.unitLtOfPos _)) hmarg
    refine ground.leB_congr (BPair.oneValue_symm hqI) ?_ h8
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_symm
          (BPair.ofPos_mul (grc * glc) (ground.Pos.pow vc K)))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc
        (BPair.ofPos (grc * glc)) (BPair.ofPos (ground.Pos.pow vc K)) _)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (ground.ofPos_pow vc K)
        (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_symm hqY
  have hAB := ground.leB_trans hAC hCle
  have hB : BPair.unit
      ≤ BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K) u :=
    unitLe_of_le_add hAB
  have hBlt : BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (vn * BPair.ofPos glc) (vc * glc) K) u
      < BPair.unit := by
    have h1 := ground.ltB_mulPos hlt'
      (ground.unitLtOfPos ((grc * glc) * ground.Pos.pow glc K))
    refine BPair.lt_congr ?_ ?_ h1
    · refine BPair.oneValue_trans (BPair.oneValue_of_eq
        (BPair.mul_comm (quadForm (cellcount.evalPC S vn vc K) u)
          (BPair.ofPos ((grc * glc) * ground.Pos.pow glc K)))) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_symm
            (BPair.ofPos_mul (grc * glc) (ground.Pos.pow glc K)))
          (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_assoc
          (BPair.ofPos (grc * glc))
          (BPair.ofPos (ground.Pos.pow glc K)) _)) ?_
      refine BPair.mul_congr (BPair.oneValue_refl _) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (ground.ofPos_pow glc K)
          (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_symm hqX
    · exact BPair.unit_mul
        (BPair.ofPos ((grc * glc) * ground.Pos.pow glc K))
  exact absurd hBlt (ground.leB_not_lt hB)

/-- The entry price at the common clearing, the anchor at the gap's
upper endpoint: the roaming point's magnitude bound is the
endpoints' own through the segment read, and the width prices at
the committed gap through the swap-blind magnitude. -/
private theorem capEntryHi (p : poly.Poly) {K : Nat}
    (hp : p.length ≤ K + 1)
    (gln : BPair) (glc : ground.Pos) (grn : BPair) (grc : ground.Pos)
    (vn : BPair) (vc : ground.Pos) (N D F : BPair)
    (hD : BPair.unit < D)
    (ha : stage.cmag ⟨gln, glc⟩ * stage.ofB D ≤ stage.ofB N)
    (hb : stage.cmag ⟨grn, grc⟩ * stage.ofB D ≤ stage.ofB N)
    (hFp : windowsep.magFold (poly.deriv p) N D ≤ F)
    (hlv : (⟨gln, glc⟩ : ground.CPair) ≤ ⟨vn, vc⟩)
    (hvr : (⟨vn, vc⟩ : ground.CPair) ≤ ⟨grn, grc⟩) :
    BPair.scale (windowsep.mag
        (poly.evalClear p (vn * BPair.ofPos grc) (vc * grc) K
          + (poly.evalClear p (grn * BPair.ofPos vc)
            (grc * vc) K).swap)) (grc * glc)
      ≤ (F * (grn.scale glc + (gln.swap).scale grc)).scale
        (ground.Pos.pow (vc * grc) K) := by
  have hv : stage.cmag ⟨vn, vc⟩ * stage.ofB D ≤ stage.ofB N :=
    stage.cmag_seg (ground.leB_of_lt hD) ha hb hlv hvr
  have hgap := stage.evalC_gap_le p ⟨vn, vc⟩ ⟨grn, grc⟩ ⟨grn, grc⟩
    N D (ground.leB_of_lt hD) hv hb hvr (ground.CPair.le_refl _)
  have habs : stage.cmag (stage.evalC p ⟨grn, grc⟩
      + ground.CPair.swap (stage.evalC p ⟨vn, vc⟩))
      ≤ stage.ofB (windowsep.magFold (poly.deriv p) N D)
        * ((⟨grn, grc⟩ : ground.CPair)
          + ground.CPair.swap ⟨vn, vc⟩) :=
    ground.CPair.le_trans
      (cleAbsorbC (stage.unitC_le_cmag _)
        (oneLe_bpow (ground.oneLeOfUnitLt hD)
          ((poly.vnorm (poly.deriv p)).length - 1))) hgap
  have hNpos : BPair.unit ≤ N :=
    stage.unitC_le_fst (ground.CPair.le_trans
      (stage.unitC_le_mul (stage.unitC_le_cmag ⟨gln, glc⟩) (by
        show BPair.unit.scale Pos.one ≤ D.scale Pos.one
        exact ground.leB_scale (ground.leB_of_lt hD) Pos.one)) ha)
  have hFC : stage.unitC ≤ stage.ofB F := by
    show BPair.unit.scale Pos.one ≤ F.scale Pos.one
    exact ground.leB_scale
      (ground.leB_trans (windowsep.unitLe_magFold (poly.deriv p)
        hNpos (ground.leB_of_lt hD)) hFp) Pos.one
  have hF2 : stage.ofB (windowsep.magFold (poly.deriv p) N D)
      * ((⟨grn, grc⟩ : ground.CPair) + ground.CPair.swap ⟨vn, vc⟩)
      ≤ stage.ofB F * ((⟨grn, grc⟩ : ground.CPair)
        + ground.CPair.swap ⟨vn, vc⟩) := by
    rw [CPair.mul_comm (stage.ofB (windowsep.magFold (poly.deriv p) N D))
        ((⟨grn, grc⟩ : ground.CPair) + ground.CPair.swap ⟨vn, vc⟩),
      CPair.mul_comm (stage.ofB F)
        ((⟨grn, grc⟩ : ground.CPair) + ground.CPair.swap ⟨vn, vc⟩)]
    exact stage.mulC_le_left (cleUnitAdd hvr) (ofBLe hFp)
  have hWm : stage.ofB F * ((⟨grn, grc⟩ : ground.CPair)
      + ground.CPair.swap ⟨vn, vc⟩)
      ≤ stage.ofB F * ((⟨grn, grc⟩ : ground.CPair)
        + ground.CPair.swap ⟨gln, glc⟩) :=
    stage.mulC_le_left hFC (cleAddR (ground.CPair.le_swap hlv))
  have hpriced := ground.CPair.le_trans habs
    (ground.CPair.le_trans hF2 hWm)
  have hE : (⟨poly.evalClear p (vn * BPair.ofPos grc) (vc * grc) K
      + (poly.evalClear p (grn * BPair.ofPos vc) (grc * vc) K).swap,
      ground.Pos.pow (vc * grc) K⟩ : ground.CPair).oneValue
      (stage.evalC p ⟨vn, vc⟩
        + ground.CPair.swap (stage.evalC p ⟨grn, grc⟩)) := by
    refine ground.CPair.oneValue_trans
      (ground.CPair.oneValue_symm (ground.CPair.add_same
        (poly.evalClear p (vn * BPair.ofPos grc) (vc * grc) K)
        ((poly.evalClear p (grn * BPair.ofPos vc) (grc * vc) K).swap)
        (ground.Pos.pow (vc * grc) K))) ?_
    refine ground.CPair.add_congr (repRead p hp vn vc grc) ?_
    refine ground.CPair.oneValue_trans
      (ground.CPair.den_congr (show ground.Pos.pow (vc * grc) K
        = ground.Pos.pow (grc * vc) K from by
        rw [ground.mul_comm vc grc])) ?_
    exact ground.CPair.swap_congr (repRead p hp grn grc vc)
  have hflip : (stage.cmag (stage.evalC p ⟨vn, vc⟩
      + ground.CPair.swap (stage.evalC p ⟨grn, grc⟩))).oneValue
      (stage.cmag (stage.evalC p ⟨grn, grc⟩
        + ground.CPair.swap (stage.evalC p ⟨vn, vc⟩))) := by
    rw [flipEq (stage.evalC p ⟨grn, grc⟩) (stage.evalC p ⟨vn, vc⟩)]
    exact cmagSwapC _
  have hcm : stage.cmag (⟨poly.evalClear p (vn * BPair.ofPos grc)
      (vc * grc) K
      + (poly.evalClear p (grn * BPair.ofPos vc) (grc * vc) K).swap,
      ground.Pos.pow (vc * grc) K⟩ : ground.CPair)
      ≤ stage.ofB F * ((⟨grn, grc⟩ : ground.CPair)
        + ground.CPair.swap ⟨gln, glc⟩) :=
    ground.CPair.le_congr
      (ground.CPair.oneValue_symm (ground.CPair.oneValue_trans
        (stage.cmag_congr hE) hflip))
      (ground.CPair.oneValue_refl _) hpriced
  have hnum : (⟨windowsep.mag (poly.evalClear p (vn * BPair.ofPos grc)
      (vc * grc) K
      + (poly.evalClear p (grn * BPair.ofPos vc) (grc * vc) K).swap),
      ground.Pos.pow (vc * grc) K⟩ : ground.CPair)
      ≤ stage.ofB F * ((⟨grn, grc⟩ : ground.CPair)
        + ground.CPair.swap ⟨gln, glc⟩) :=
    ground.CPair.le_congr (stage.cmag_num _ _)
      (ground.CPair.oneValue_refl _) hcm
  have h5 : BPair.scale (windowsep.mag
        (poly.evalClear p (vn * BPair.ofPos grc) (vc * grc) K
          + (poly.evalClear p (grn * BPair.ofPos vc)
            (grc * vc) K).swap))
        (Pos.one * (grc * glc))
      ≤ (F * (grn.scale glc + (gln.swap).scale grc)).scale
        (ground.Pos.pow (vc * grc) K) := hnum
  rw [ground.one_mul (grc * glc)] at h5
  exact h5

/-- The gap's site datum at the common clearing, the anchor at the
upper endpoint, is entrywise capped at the priced width. -/
private theorem gapCapHi {o K : Nat} (S : split.PMat)
    (hsh : cellcount.pShapeAt S o K)
    (gln : BPair) (glc : ground.Pos) (grn : BPair) (grc : ground.Pos)
    (vn : BPair) (vc : ground.Pos) (N D F : BPair)
    (hD : BPair.unit < D)
    (ha : stage.cmag ⟨gln, glc⟩ * stage.ofB D ≤ stage.ofB N)
    (hb : stage.cmag ⟨grn, grc⟩ * stage.ofB D ≤ stage.ofB N)
    (hF : foldCap S N D F)
    (hlv : (⟨gln, glc⟩ : ground.CPair) ≤ ⟨vn, vc⟩)
    (hvr : (⟨vn, vc⟩ : ground.CPair) ≤ ⟨grn, grc⟩) :
    magCap ((F * (grn.scale glc + (gln.swap).scale grc)).scale
        (ground.Pos.pow (vc * grc) K))
      (matScale (grc * glc)
        (matAdd (cellcount.evalPC S (vn * BPair.ofPos grc)
            (vc * grc) K)
          (elim.matSwap (cellcount.evalPC S (grn * BPair.ofPos vc)
            (grc * vc) K)))) := by
  have hXsq := cellcount.evalPC_sqAt hsh (vn * BPair.ofPos grc)
    (vc * grc)
  have hYsq := cellcount.evalPC_sqAt hsh (grn * BPair.ofPos vc)
    (grc * vc)
  refine magCap_scaleOf (grc * glc) _ _
    (elim.sqAt_matAdd o _ _ hXsq (elim.sqAt_matSwap o _ hYsq))
    (fun i j hio hjo => ?_)
  have hiX : i < (cellcount.evalPC S (vn * BPair.ofPos grc)
      (vc * grc) K).length := by
    rw [elim.sqAt_len hXsq]; exact hio
  have hiY : i < (cellcount.evalPC S (grn * BPair.ofPos vc)
      (grc * vc) K).length := by
    rw [elim.sqAt_len hYsq]; exact hio
  have hiS : i < (elim.matSwap (cellcount.evalPC S
      (grn * BPair.ofPos vc) (grc * vc) K)).length := by
    rw [elim.length_matSwap]; exact hiY
  have hiP : i < S.length := by
    rw [cellcount.pShape_len hsh]; exact hio
  have hjX : j < (ground.getAt ([] : List BPair)
      (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K)
        i).length := by
    rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hXsq) hiX]
    exact hjo
  have hjY : j < (ground.getAt ([] : List BPair)
      (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K)
        i).length := by
    rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hYsq) hiY]
    exact hjo
  have hjS : j < (ground.getAt ([] : List BPair)
      (elim.matSwap (cellcount.evalPC S (grn * BPair.ofPos vc)
        (grc * vc) K)) i).length := by
    rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt
      (elim.sqAt_matSwap o _ hYsq)) hiS]
    exact hjo
  rw [elim.getAt_matAdd _ _ i hiX hiS,
    elim.getAt_vecAdd _ _ j hjX hjS,
    show ground.getAt ([] : List BPair)
        (elim.matSwap (cellcount.evalPC S (grn * BPair.ofPos vc)
          (grc * vc) K)) i
      = (ground.getAt ([] : List BPair)
          (cellcount.evalPC S (grn * BPair.ofPos vc)
            (grc * vc) K) i).map BPair.swap from
      ground.getAt_map ([] : List BPair) ([] : List BPair) _ _ i hiY,
    ground.getAt_map BPair.unit BPair.unit BPair.swap _ j hjY,
    cellcount.getAt_evalPC (vn * BPair.ofPos grc) (vc * grc) K S i j,
    cellcount.getAt_evalPC (grn * BPair.ofPos vc) (grc * vc) K S i j]
  exact capEntryHi (ground.getAt ([] : poly.Poly)
      (ground.getAt ([] : List poly.Poly) S i) j)
    (cellcount.ent_ble hsh i j) gln glc grn grc vn vc N D F hD
    ha hb
    (foldCap_entry hF i j hiP (by
      rw [elim.rowsLen_getAt _ i (cellcount.pShape_rows hsh) hiP]
      exact hjo))
    hlv hvr

/-- The gap's read at the upper anchor (`thm:gappos`(v)'s counting
sandwich at a committed gap, the flanking sample above): at a gap
whose upper endpoint holds the scaled identity's margin
certificate, whose endpoints hold the committed magnitude bounds,
whose entries hold the committed fold cap, and whose clearing
comparison prices the width below the margin, every split at every
pair point strictly inside the gap reads positive semidefinite. -/
theorem gapPsd_hi {o K : Nat} (S : split.PMat)
    (gln : BPair) (glc : ground.Pos) (grn : BPair) (grc : ground.Pos)
    (N D F : BPair) (rhoM : ground.Pos) (spM : Split o)
    (hsh : cellcount.pShapeAt S o K)
    (hsym : split.pSymAt S o)
    (hD : BPair.unit < D)
    (ha : stage.cmag ⟨gln, glc⟩ * stage.ofB D ≤ stage.ofB N)
    (hb : stage.cmag ⟨grn, grc⟩ * stage.ofB D ≤ stage.ofB N)
    (hF : foldCap S N D F)
    (hM : splitRead (siteDatum (cellcount.evalPC S grn grc K)
      (matScale rhoM (idMat o))) spM)
    (hMp : psdAt spM)
    (hcl : BPair.ofNat o
        * ((F * (grn.scale glc + (gln.swap).scale grc)).scale
          (ground.Pos.pow grc K))
      ≤ (BPair.ofPos rhoM).scale (grc * glc)) :
    ∀ (vn : BPair) (vc : ground.Pos),
    (⟨gln, glc⟩ : ground.CPair) < ⟨vn, vc⟩ →
    (⟨vn, vc⟩ : ground.CPair) < ⟨grn, grc⟩ →
    ∀ sp : Split o,
    splitRead (cellcount.evalPC S vn vc K) sp → psdAt sp := by
  intro vn vc hlv hvr sp hsp
  cases Nat.eq_zero_or_pos (revAt sp) with
  | inl h0 => exact h0
  | inr hpos =>
  obtain ⟨u, hu, hlt⟩ := rev_witness _ sp hsp hpos
  have hlt' : quadForm (cellcount.evalPC S vn vc K) u < BPair.unit := hlt
  have hXsq := cellcount.evalPC_sqAt hsh (vn * BPair.ofPos grc)
    (vc * grc)
  have hYsq := cellcount.evalPC_sqAt hsh (grn * BPair.ofPos vc)
    (grc * vc)
  have hGsq := cellcount.evalPC_sqAt (K := K) hsh grn grc
  have hqX : (quadForm (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K) u).oneValue
      (ground.bpow (BPair.ofPos grc) K * quadForm (cellcount.evalPC S vn vc K) u) :=
    BPair.oneValue_trans
      (elim.dotN_matVec_congrM _ _ u u
        (cellcount.evalPC_scalePoint S o K vn vc grc hsh))
      (inertia.quadForm_scaleB (ground.bpow (BPair.ofPos grc) K) _ u)
  have hqY : (quadForm (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K) u).oneValue
      (ground.bpow (BPair.ofPos vc) K * quadForm (cellcount.evalPC S grn grc K) u) :=
    BPair.oneValue_trans
      (elim.dotN_matVec_congrM _ _ u u
        (cellcount.evalPC_scalePoint S o K grn grc vc hsh))
      (inertia.quadForm_scaleB (ground.bpow (BPair.ofPos vc) K) _ u)
  have hmarg : quadForm (matScale rhoM (idMat o)) u
      ≤ quadForm (cellcount.evalPC S grn grc K) u := by
    have hnl := inertia.psd_all _ spM hM hMp u hu
    have hge : BPair.unit ≤ quadForm (siteDatum (cellcount.evalPC S grn grc K)
        (matScale rhoM (idMat o))) u :=
      ground.leB_of_not_lt hnl
    have hge2 : BPair.unit ≤ quadForm (cellcount.evalPC S grn grc K) u
        + (quadForm (matScale rhoM (idMat o)) u).swap :=
      ground.leB_congr_right
        (inertia.quadForm_site_sq hGsq (sqAt_scaleId o rhoM) hu) hge
    have h3 := ground.leB_of_unit_add hge2
    rw [BPair.swap_swap] at h3
    exact h3
  have hcap := gapCapHi S hsh gln glc grn grc vn vc N D F hD ha hb hF
    (Or.inr hlv) (Or.inr hvr)
  have hclv : BPair.ofNat o
      * ((F * (grn.scale glc + (gln.swap).scale grc)).scale
        (ground.Pos.pow (vc * grc) K))
      ≤ BPair.ofPos (rhoM * ((grc * glc) * ground.Pos.pow vc K)) := by
    have h1 := ground.leB_scale hcl (ground.Pos.pow vc K)
    refine ground.leB_congr ?_ ?_ h1
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_scale (BPair.ofNat o) _ (ground.Pos.pow grc K),
        BPair.scale_scale,
        BPair.mul_scale (BPair.ofNat o) _
          (ground.Pos.pow (vc * grc) K),
        ground.Pos.pow_mul vc grc K,
        ground.mul_comm (ground.Pos.pow grc K) (ground.Pos.pow vc K)]
    · refine BPair.oneValue_trans (BPair.oneValue_of_eq
        (BPair.scale_scale (BPair.ofPos rhoM) (grc * glc)
          (ground.Pos.pow vc K))) ?_
      refine BPair.oneValue_trans (BPair.oneValue_symm
        (BPair.ofPos_scale ((grc * glc) * ground.Pos.pow vc K)
          (BPair.ofPos rhoM))) ?_
      refine BPair.oneValue_trans (BPair.oneValue_of_eq
        (BPair.mul_comm
          (BPair.ofPos ((grc * glc) * ground.Pos.pow vc K))
          (BPair.ofPos rhoM))) ?_
      exact BPair.ofPos_mul rhoM ((grc * glc) * ground.Pos.pow vc K)
  have hquad := capQuad o
    (matScale (grc * glc) (matAdd (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K) (elim.matSwap (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K))))
    ((F * (grn.scale glc + (gln.swap).scale grc)).scale
      (ground.Pos.pow (vc * grc) K))
    (rhoM * ((grc * glc) * ground.Pos.pow vc K))
    (inertia.sqAt_matScale o (grc * glc) _
      (elim.sqAt_matAdd o _ _ hXsq (elim.sqAt_matSwap o _ hYsq)))
    (symScale (grc * glc) _
      (elim.sqAt_matAdd o _ _ hXsq (elim.sqAt_matSwap o _ hYsq))
      (symSite _ _ hXsq hYsq
        (cellcount.evalPC_symAt S o K (vn * BPair.ofPos grc)
          (vc * grc) hsh hsym)
        (cellcount.evalPC_symAt S o K (grn * BPair.ofPos vc)
          (grc * vc) hsh hsym)))
    hcap hclv u hu
  have h6 : BPair.unit ≤ quadForm
      (matAdd (matScale (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o))
        (matScale (grc * glc) (matAdd (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K) (elim.matSwap (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K))))) u :=
    ground.leB_congr_left
      (elim.dotN_nullL (List.replicate o BPair.unit)
        (List.zipWith (· * ·) u u) (poly.unitTail_replicate o))
      hquad
  have h7 : BPair.unit
      ≤ (quadForm (matScale (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o)) u
        + BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K) u)
        + (BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K) u).swap := by
    refine ground.leB_congr_right ?_ h6
    have hinner : (quadForm (matAdd (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K)
        (elim.matSwap (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K))) u).oneValue
        (quadForm (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K) u + (quadForm (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K) u).swap) :=
      inertia.quadForm_site_sq hXsq hYsq hu
    have hws : (quadForm (matScale (grc * glc)
        (matAdd (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K) (elim.matSwap (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K)))) u).oneValue
        (BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K) u
          + (BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K) u).swap) := by
      refine BPair.oneValue_trans
        (inertia.quadForm_ofPos (grc * glc) _ u) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos (grc * glc)))
          hinner) ?_
      refine BPair.oneValue_of_eq ?_
      rw [BPair.left_distrib, BPair.mul_swap]
    refine BPair.oneValue_trans
      (inertia.quadForm_add_sq (sqAt_scaleId o (rhoM * ((grc * glc) * ground.Pos.pow vc K)))
        (inertia.sqAt_matScale o (grc * glc) _
          (elim.sqAt_matAdd o _ _ hXsq (elim.sqAt_matSwap o _ hYsq)))
        hu) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) hws) ?_
    exact BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm
  have hCle := ground.leB_of_unit_add h7
  rw [BPair.swap_swap] at hCle
  have hqI : (quadForm (matScale (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o)) u).oneValue
      (BPair.ofPos ((grc * glc) * ground.Pos.pow vc K)
        * quadForm (matScale rhoM (idMat o)) u) := by
    refine BPair.oneValue_trans
      (inertia.quadForm_ofPos (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o) u) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_symm
        (BPair.ofPos_mul rhoM ((grc * glc) * ground.Pos.pow vc K)))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (by
      rw [BPair.mul_comm (BPair.ofPos rhoM)
          (BPair.ofPos ((grc * glc) * ground.Pos.pow vc K)),
        BPair.mul_assoc])) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (inertia.quadForm_ofPos rhoM (idMat o) u))
  have hAC : quadForm (matScale (rhoM * ((grc * glc) * ground.Pos.pow vc K)) (idMat o)) u
      ≤ BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (grn * BPair.ofPos vc) (grc * vc) K) u := by
    have h8 : BPair.ofPos ((grc * glc) * ground.Pos.pow vc K)
        * quadForm (matScale rhoM (idMat o)) u
        ≤ BPair.ofPos ((grc * glc) * ground.Pos.pow vc K)
          * quadForm (cellcount.evalPC S grn grc K) u :=
      ground.leB_mulR
        (ground.leB_of_lt (ground.unitLtOfPos _)) hmarg
    refine ground.leB_congr (BPair.oneValue_symm hqI) ?_ h8
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_symm
          (BPair.ofPos_mul (grc * glc) (ground.Pos.pow vc K)))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc
        (BPair.ofPos (grc * glc)) (BPair.ofPos (ground.Pos.pow vc K)) _)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (ground.ofPos_pow vc K)
        (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_symm hqY
  have hAB := ground.leB_trans hAC hCle
  have hB : BPair.unit
      ≤ BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K) u :=
    unitLe_of_le_add hAB
  have hBlt : BPair.ofPos (grc * glc) * quadForm (cellcount.evalPC S (vn * BPair.ofPos grc) (vc * grc) K) u
      < BPair.unit := by
    have h1 := ground.ltB_mulPos hlt'
      (ground.unitLtOfPos ((grc * glc) * ground.Pos.pow grc K))
    refine BPair.lt_congr ?_ ?_ h1
    · refine BPair.oneValue_trans (BPair.oneValue_of_eq
        (BPair.mul_comm (quadForm (cellcount.evalPC S vn vc K) u)
          (BPair.ofPos ((grc * glc) * ground.Pos.pow grc K)))) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_symm
            (BPair.ofPos_mul (grc * glc) (ground.Pos.pow grc K)))
          (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_assoc
          (BPair.ofPos (grc * glc))
          (BPair.ofPos (ground.Pos.pow grc K)) _)) ?_
      refine BPair.mul_congr (BPair.oneValue_refl _) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (ground.ofPos_pow grc K)
          (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_symm hqX
    · exact BPair.unit_mul
        (BPair.ofPos ((grc * glc) * ground.Pos.pow grc K))
  exact absurd hBlt (ground.leB_not_lt hB)

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

/-- The cut's per-cell coverage (`thm:gappos`(iv)): on a cell
certified at one carrier a sampled positive-semidefinite read holds
at every point — `E₀ 𝒦(v) ≥ κ` on the whole cell, located point by
located point, the count a cell function at the vacant value
(`cellcount.cellCount`, the one transport). -/
theorem cellPsd {o : Nat} (S : split.PMat) (K : Nat)
    (lo hi : CPair) (cov : cellcount.Cover)
    (hc : cellcount.coverRead S o K lo hi cov)
    (sn : BPair) (sc : Pos)
    (hls : lo ≤ (⟨sn, sc⟩ : CPair)) (hsh : (⟨sn, sc⟩ : CPair) ≤ hi)
    (sps : Split o)
    (hs : cellcount.countAt S K sn sc 0 sps)
    (tn : BPair) (tc : Pos)
    (hlt : lo ≤ (⟨tn, tc⟩ : CPair)) (hth : (⟨tn, tc⟩ : CPair) ≤ hi)
    (spt : Split o)
    (ht : splitRead (cellcount.evalPC S tn tc K) spt) :
    psdAt spt :=
  cellcount.cellCount S K 0 lo hi cov hc sn sc hls hsh sps hs
    tn tc hlt hth spt ht

/-- One chain of cells at shared endpoints: from a stated foot, each
cell carries its top, its pivot cover and one sample at the stated
count, the next cell's foot the top itself (`thm:gappos`(ii), the
located cells' chain). -/
def chainRead {o : Nat} (S : split.PMat) (K n : Nat) : CPair →
    List (CPair × cellcount.Cover × (BPair × Pos) × Split o) → Prop
  | _, [] => True
  | lo, (hi, cov, (sn, sc), sp) :: rest =>
      cellcount.coverRead S o K lo hi cov
      ∧ lo ≤ (⟨sn, sc⟩ : CPair) ∧ (⟨sn, sc⟩ : CPair) ≤ hi
      ∧ cellcount.countAt S K sn sc n sp
      ∧ chainRead S K n hi rest

def decChainRead {o : Nat} (S : split.PMat) (K n : Nat) : ∀ (lo : CPair)
    (l : List (CPair × cellcount.Cover × (BPair × Pos) × Split o)),
    Decidable (chainRead S K n lo l)
  | _, [] => isTrue trivial
  | _, (hi, _, (_, _), _) :: rest =>
    have : Decidable (chainRead S K n hi rest) := decChainRead S K n hi rest
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

instance {o : Nat} (S : split.PMat) (K n : Nat) (lo : CPair)
    (l : List (CPair × cellcount.Cover × (BPair × Pos) × Split o)) :
    Decidable (chainRead S K n lo l) := decChainRead S K n lo l

/-- The chain's top: the last cell's own. -/
def chainHi {o : Nat} (lo : CPair) :
    List (CPair × cellcount.Cover × (BPair × Pos) × Split o) → CPair
  | [] => lo
  | (hi, _, _, _) :: rest => chainHi hi rest

/-- One root-free chain of located cells carries the count whole
(`thm:gappos`(ii), clause (iv)'s count a cell function read once
over the cells): at a chain of cells each with its cover and its
sample at the stated count, every point from the chain's foot to
its top reads that count at any stated split — the fold locating
the point in its cell by the composite order's totality. -/
theorem chainCount {o : Nat} (S : split.PMat) (K n : Nat) :
    ∀ (lo : CPair)
      (c : CPair × cellcount.Cover × (BPair × Pos) × Split o)
      (l : List (CPair × cellcount.Cover × (BPair × Pos) × Split o)),
      chainRead S K n lo (c :: l) →
      ∀ (tn : BPair) (tc : Pos), lo ≤ (⟨tn, tc⟩ : CPair) →
      (⟨tn, tc⟩ : CPair) ≤ chainHi lo (c :: l) →
      ∀ spt : Split o,
      splitRead (cellcount.evalPC S tn tc K) spt → revAt spt = n
  | lo, (hi, cov, (sn, sc), sp), [], h, tn, tc, hlt, hth, spt, ht =>
      cellcount.cellCount S K n lo hi cov h.1 sn sc h.2.1 h.2.2.1
        sp h.2.2.2.1 tn tc hlt hth spt ht
  | lo, (hi, cov, (sn, sc), sp), c' :: l', h, tn, tc, hlt, hth,
      spt, ht =>
    match CPair.le_total (⟨tn, tc⟩ : CPair) hi with
    | Or.inl h1 =>
        cellcount.cellCount S K n lo hi cov h.1 sn sc h.2.1 h.2.2.1
          sp h.2.2.2.1 tn tc hlt h1 spt ht
    | Or.inr h2 =>
        chainCount S K n hi c' l' h.2.2.2.2 tn tc h2 hth spt ht

/-- The chain's positive-semidefinite read, `chainCount` at the
vacant count — the cut carried across one root-free chain of
located cells. -/
theorem chainPsd {o : Nat} (S : split.PMat) (K : Nat) (lo : CPair)
    (c : CPair × cellcount.Cover × (BPair × Pos) × Split o)
    (l : List (CPair × cellcount.Cover × (BPair × Pos) × Split o))
    (h : chainRead S K 0 lo (c :: l))
    (tn : BPair) (tc : Pos) (hlt : lo ≤ (⟨tn, tc⟩ : CPair))
    (hth : (⟨tn, tc⟩ : CPair) ≤ chainHi lo (c :: l))
    (spt : Split o)
    (ht : splitRead (cellcount.evalPC S tn tc K) spt) : psdAt spt :=
  chainCount S K 0 lo c l h tn tc hlt hth spt ht

set_option genInjectivity false in
/-- The closed union's pieces (`thm:gappos`(ii), (v)): a segment,
one root-free cell chain at its foot, or a junction, a located
boundary point of the divisor at its own split with the priced tie
into a flanking positive-semidefinite sample — the boundary clause
of `lem:cellcount` at the chain's carrier, the chain's end
junctions `lem:freecell`'s and `lem:contactcell`'s
endpoint-extension clauses. -/
inductive Piece (o : Nat) where
  | seg (foot : ground.CPair)
      (cells : List (ground.CPair × cellcount.Cover
        × (BPair × ground.Pos) × Split o))
  | junc (bn : BPair) (bc : ground.Pos) (spb : Split o)
      (tn : BPair) (tc : ground.Pos) (spt : Split o)
      (side : Bool) (N D : BPair)

/-- The anchored start: the head piece's own point reads the stated
foot. -/
def startsAt {o : Nat} (lo : ground.CPair) : List (Piece o) → Prop
  | [] => True
  | .seg foot _ :: _ => foot.oneValue lo
  | .junc bn bc _ _ _ _ _ _ _ :: _ =>
      (⟨bn, bc⟩ : ground.CPair).oneValue lo

instance {o : Nat} (lo : ground.CPair) (l : List (Piece o)) :
    Decidable (startsAt lo l) :=
  match l with
  | [] => isTrue trivial
  | .seg _ _ :: _ =>
      inferInstanceAs (Decidable (ground.CPair.oneValue _ _))
  | .junc _ _ _ _ _ _ _ _ _ :: _ =>
      inferInstanceAs (Decidable (ground.CPair.oneValue _ _))

/-- The closed union's read (`thm:gappos`(v): the pair reads across
the cells' closed union at `lem:cellcount`'s boundary clause): per
segment the ordering with the chain's read at the vacant count, per
junction the ordering, the point's and the flanking sample's splits
with the sample positive semidefinite, and the priced tie on the
stated side — `stage.keepLower` from the point into the sample,
`stage.keepLowerTop` from the sample up to the point. -/
def closedRead {o : Nat} (S : split.PMat) (K : Nat) :
    ground.CPair → List (Piece o) → Prop
  | _, [] => True
  | _, .seg _ [] :: _ => False
  | lo, .seg foot (c :: cs) :: rest =>
      lo ≤ foot
      ∧ chainRead S K 0 foot (c :: cs)
      ∧ closedRead S K (chainHi foot (c :: cs)) rest
  | lo, .junc bn bc spb tn tc spt side N D :: rest =>
      lo ≤ (⟨bn, bc⟩ : ground.CPair)
      ∧ splitRead (cellcount.evalPC S bn bc K) spb
      ∧ splitRead (cellcount.evalPC S tn tc K) spt
      ∧ psdAt spt
      ∧ (if side then
          ((lowerList spb).all (fun u => decide
            (stage.keepLower (cellcount.quadP S u) ⟨bn, bc⟩
              ⟨tn, tc⟩ N D))) = true
        else
          ((lowerList spb).all (fun u => decide
            (stage.keepLowerTop (cellcount.quadP S u) ⟨tn, tc⟩
              ⟨bn, bc⟩ N D))) = true)
      ∧ closedRead S K ⟨bn, bc⟩ rest

/-- The closed read's decision, one arm per piece. -/
def decClosedRead {o : Nat} (S : split.PMat) (K : Nat) :
    ∀ (lo : ground.CPair) (l : List (Piece o)),
    Decidable (closedRead S K lo l)
  | _, [] => isTrue trivial
  | _, .seg _ [] :: _ => isFalse (fun h => h)
  | _, .seg foot (c :: cs) :: rest =>
    have : Decidable (closedRead S K (chainHi foot (c :: cs)) rest) :=
      decClosedRead S K _ rest
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | _, .junc bn bc _ _ _ _ _ _ _ :: rest =>
    have : Decidable (closedRead S K ⟨bn, bc⟩ rest) :=
      decClosedRead S K ⟨bn, bc⟩ rest
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

instance {o : Nat} (S : split.PMat) (K : Nat) (lo : ground.CPair)
    (l : List (Piece o)) : Decidable (closedRead S K lo l) :=
  decClosedRead S K lo l

/-- The closed union's top: the last piece's own point. -/
def closedHi {o : Nat} (lo : ground.CPair) :
    List (Piece o) → ground.CPair
  | [] => lo
  | .seg foot cells :: rest => closedHi (chainHi foot cells) rest
  | .junc bn bc _ _ _ _ _ _ _ :: rest => closedHi ⟨bn, bc⟩ rest

/-- The committed boundaries' open gaps, one pair per piece: the
running covered point against the next piece's own. -/
def closedGaps {o : Nat} (lo : ground.CPair) :
    List (Piece o) → List (ground.CPair × ground.CPair)
  | [] => []
  | .seg foot cells :: rest =>
      (lo, foot) :: closedGaps (chainHi foot cells) rest
  | .junc bn bc _ _ _ _ _ _ _ :: rest =>
      (lo, ⟨bn, bc⟩) :: closedGaps ⟨bn, bc⟩ rest

/-- The width's fold clears its seed. -/
private theorem widthOf_ge : ∀ (bs : List SBlock) (k : Nat),
    k ≤ widthOf bs k
  | [], k => Nat.le_refl k
  | b :: bs, k =>
    Nat.le_trans (Nat.le_add_right k b.order)
      (widthOf_ge bs (k + b.order))

/-- Every split at the vacant order reads positive semidefinite:
the width tie forces the block list vacant. -/
private theorem psdZero (sp : Split 0) : psdAt sp := by
  obtain ⟨T, Tw, blocks, kern, hw⟩ := sp
  match blocks, hw with
  | [], _ => rfl
  | b :: bs, hw =>
    have h0 : widthOf (b :: bs) kern = 0 := Nat.eq_of_beq_eq_true hw
    have hpos : 0 < widthOf (b :: bs) kern := by
      refine Nat.lt_of_lt_of_le ?_ (widthOf_ge bs (kern + b.order))
      match b with
      | .one _ =>
        exact Nat.lt_of_lt_of_le (Nat.succ_le_succ (Nat.zero_le kern))
          (Nat.le_refl (kern + 1))
      | .two _ _ _ =>
        exact Nat.lt_of_lt_of_le (Nat.succ_le_succ (Nat.zero_le kern))
          (Nat.le_add_right (kern + 1) 1)
    exact absurd (h0 ▸ hpos) (Nat.lt_irrefl 0)

/-- A cover's bracket keeps its order at an occupied width: the
occupied arms' priced side reads state the strict step and the tie
arm the one value, the vacant-width arm refused. -/
private theorem cover_le {m K : Nat} {S : split.PMat} :
    ∀ (cov : cellcount.Cover) (lo hi : ground.CPair),
    cellcount.coverRead S (m + 1) K lo hi cov → lo ≤ hi
  | .done, _, _, h => Or.inl h.2
  | .nought, _, _, h =>
    absurd (Nat.eq_of_beq_eq_true h) (fun hh => Nat.noConfusion hh)
  | .one b _ up _ _ _ rest, lo, hi, h => by
    have hlb : lo < b := by
      match up, h.2.1 with
      | true, hk => exact hk.2.1
      | false, hk => exact hk.2.1
    exact ground.CPair.le_trans (Or.inr hlb)
      (cover_le rest b hi h.2.2.2)
  | .mixed b _ _ _ _ _ rest, lo, hi, h =>
    ground.CPair.le_trans (Or.inr h.2.1.2.1)
      (cover_le rest b hi h.2.2.2)
  | .twoUp b _ _ _ _ _ _ _ _ rest, lo, hi, h =>
    ground.CPair.le_trans (Or.inr h.2.1.2.1)
      (cover_le rest b hi h.2.2.2.2)

/-- A chain's top keeps the foot's side at an occupied width, the
covers' brackets composing. -/
private theorem chain_le {m K n : Nat} (S : split.PMat) :
    ∀ (foot : ground.CPair)
      (cells : List (ground.CPair × cellcount.Cover
        × (BPair × ground.Pos) × Split (m + 1))),
    chainRead S K n foot cells → foot ≤ chainHi foot cells
  | _, [], _ => ground.CPair.le_refl _
  | foot, (hi, cov, _, _) :: rest, h =>
    ground.CPair.le_trans (cover_le cov foot hi h.1)
      (chain_le S hi rest h.2.2.2.2)

/-- The junction's own read: `lem:cellcount`'s boundary clause at
the committed side. -/
private theorem juncPsd {o K : Nat} (S : split.PMat)
    (bn : BPair) (bc : ground.Pos) (spb : Split o) (tn : BPair)
    (tc : ground.Pos) (spt : Split o) (side : Bool) (N D : BPair)
    (hsh : cellcount.pShapeAt S o K)
    (hspb : splitRead (cellcount.evalPC S bn bc K) spb)
    (hspt : splitRead (cellcount.evalPC S tn tc K) spt)
    (hpsdt : psdAt spt)
    (htie : if side then
        ((lowerList spb).all (fun u => decide
          (stage.keepLower (cellcount.quadP S u) ⟨bn, bc⟩
            ⟨tn, tc⟩ N D))) = true
      else
        ((lowerList spb).all (fun u => decide
          (stage.keepLowerTop (cellcount.quadP S u) ⟨tn, tc⟩
            ⟨bn, bc⟩ N D))) = true) :
    psdAt spb := by
  match side, htie with
  | true, htie =>
    exact cellcount.boundary_psd_lo S K bn bc tn tc N D spb spt
      hsh hspb hspt hpsdt htie
  | false, htie =>
    exact cellcount.boundary_psd_hi S K bn bc tn tc N D spb spt
      hsh hspb hspt hpsdt htie

/-- The closed union's walk at an occupied width, the running foot
covered: each point of the range reads its piece — a chain point the
chain's own (`chainPsd`), a junction point the boundary clause's
(`juncPsd` at the representative transport), a gap point the stated
gap read — with the covered foot passing to each piece's own top. -/
private theorem closedGo {m K : Nat} (S : split.PMat)
    (hsh : cellcount.pShapeAt S (m + 1) K) :
    ∀ (lo : ground.CPair) (l : List (Piece (m + 1))),
    (∀ (vn : BPair) (vc : ground.Pos),
      (⟨vn, vc⟩ : ground.CPair).oneValue lo →
      ∀ sp : Split (m + 1),
      splitRead (cellcount.evalPC S vn vc K) sp → psdAt sp) →
    closedRead S K lo l →
    (∀ gl gr : ground.CPair, (gl, gr) ∈ closedGaps lo l →
      ∀ (vn : BPair) (vc : ground.Pos),
      gl < (⟨vn, vc⟩ : ground.CPair) →
      (⟨vn, vc⟩ : ground.CPair) < gr →
      ∀ sp : Split (m + 1),
      splitRead (cellcount.evalPC S vn vc K) sp → psdAt sp) →
    ∀ (vn : BPair) (vc : ground.Pos),
    lo ≤ (⟨vn, vc⟩ : ground.CPair) →
    (⟨vn, vc⟩ : ground.CPair) ≤ closedHi lo l →
    ∀ sp : Split (m + 1),
    splitRead (cellcount.evalPC S vn vc K) sp → psdAt sp
  | lo, [], hcov, _, _, vn, vc, hlv, hvh, sp, hsp => by
    match hvh with
    | Or.inl e => exact hcov vn vc e sp hsp
    | Or.inr hvl =>
      match hlv with
      | Or.inl e =>
        exact hcov vn vc (ground.CPair.oneValue_symm e) sp hsp
      | Or.inr hlt => exact (ground.lt_asymm hlt hvl).elim
  | lo, .seg foot cells :: rest, hcov, hcr, hgap, vn, vc, hlv, hvh,
      sp, hsp => by
    match cells, hcr with
    | [], hcr => exact hcr.elim
    | c :: cs, hcr =>
      obtain ⟨_, hchain, hrest⟩ := hcr
      match ground.CPair.le_total (⟨vn, vc⟩ : ground.CPair)
          (chainHi foot (c :: cs)) with
      | Or.inl hvtop =>
        match ground.CPair.le_total foot ⟨vn, vc⟩ with
        | Or.inl hfv =>
          exact chainPsd S K foot c cs hchain vn vc hfv hvtop sp hsp
        | Or.inr hvf =>
          match hvf with
          | Or.inl e =>
            exact chainPsd S K foot c cs hchain vn vc
              (Or.inl (ground.CPair.oneValue_symm e)) hvtop sp hsp
          | Or.inr hvltf =>
            match hlv with
            | Or.inl e =>
              exact hcov vn vc (ground.CPair.oneValue_symm e) sp hsp
            | Or.inr hlov =>
              exact hgap lo foot (List.Mem.head _) vn vc hlov hvltf
                sp hsp
      | Or.inr htopv =>
        refine closedGo S hsh (chainHi foot (c :: cs)) rest ?_ hrest
          (fun gl gr hm => hgap gl gr (List.Mem.tail _ hm))
          vn vc htopv hvh sp hsp
        intro wn wc hw spw hspw
        have hfw : foot ≤ (⟨wn, wc⟩ : ground.CPair) := by
          match chain_le S foot (c :: cs) hchain with
          | Or.inl e =>
            exact Or.inl (ground.CPair.oneValue_trans e
              (ground.CPair.oneValue_symm hw))
          | Or.inr hlt =>
            exact Or.inr (ground.CPair.lt_congr
              (ground.CPair.oneValue_refl foot)
              (ground.CPair.oneValue_symm hw) hlt)
        exact chainPsd S K foot c cs hchain wn wc hfw
          (Or.inl hw) spw hspw
  | lo, .junc bn bc spb tn tc spt side N D :: rest, hcov, hcr, hgap,
      vn, vc, hlv, hvh, sp, hsp => by
    obtain ⟨_, hspb, hspt, hpsdt, htie, hrest⟩ := hcr
    have hbpsd : psdAt spb :=
      juncPsd S bn bc spb tn tc spt side N D hsh hspb hspt hpsdt htie
    match ground.CPair.le_total (⟨vn, vc⟩ : ground.CPair)
        ⟨bn, bc⟩ with
    | Or.inl hvb =>
      match hvb with
      | Or.inl e =>
        exact (cellcount.evalPC_pointCongr S K vn bn vc bc
          sp spb hsh e hsp hspb).trans hbpsd
      | Or.inr hvltb =>
        match hlv with
        | Or.inl e =>
          exact hcov vn vc (ground.CPair.oneValue_symm e) sp hsp
        | Or.inr hlov =>
          exact hgap lo ⟨bn, bc⟩ (List.Mem.head _) vn vc hlov hvltb
            sp hsp
    | Or.inr hbv =>
      refine closedGo S hsh ⟨bn, bc⟩ rest ?_ hrest
        (fun gl gr hm => hgap gl gr (List.Mem.tail _ hm))
        vn vc hbv hvh sp hsp
      intro wn wc hw spw hspw
      exact (cellcount.evalPC_pointCongr S K wn bn wc bc
        spw spb hsh hw hspw hspb).trans hbpsd

/-- The closed union's read at every point (`thm:gappos`(ii), (v):
the pair reads hold across the cells' closed union by
`lem:cellcount`'s boundary clause, the gaps the stated reads): at an
anchored occupied list, every point from the foot to the top reads
positive semidefinite at any stated split — the pieces' own reads
with the gap hypothesis the consumer's, and the vacant order outright. -/
theorem closedPsd {o K : Nat} (S : split.PMat) (lo : ground.CPair)
    (p : Piece o) (l : List (Piece o))
    (hsh : cellcount.pShapeAt S o K)
    (hst : startsAt lo (p :: l))
    (hcr : closedRead S K lo (p :: l))
    (hgap : ∀ gl gr : ground.CPair, (gl, gr) ∈ closedGaps lo (p :: l) →
      ∀ (vn : BPair) (vc : ground.Pos),
      gl < (⟨vn, vc⟩ : ground.CPair) →
      (⟨vn, vc⟩ : ground.CPair) < gr →
      ∀ sp : Split o,
      splitRead (cellcount.evalPC S vn vc K) sp → psdAt sp) :
    ∀ (vn : BPair) (vc : ground.Pos),
    lo ≤ (⟨vn, vc⟩ : ground.CPair) →
    (⟨vn, vc⟩ : ground.CPair) ≤ closedHi lo (p :: l) →
    ∀ sp : Split o,
    splitRead (cellcount.evalPC S vn vc K) sp → psdAt sp := by
  match o, p, l, hsh, hst, hcr, hgap with
  | 0, _, _, _, _, _, _ =>
    intro _ _ _ _ sp _
    exact psdZero sp
  | m + 1, p, l, hsh, hst, hcr, hgap =>
    refine closedGo S hsh lo (p :: l) ?_ hcr hgap
    intro wn wc hw spw hspw
    match p, hst, hcr with
    | .seg foot cells, hst, hcr =>
      match cells, hcr with
      | [], hcr => exact hcr.elim
      | c :: cs, hcr =>
        obtain ⟨_, hchain, _⟩ := hcr
        have hfw : foot.oneValue ⟨wn, wc⟩ :=
          ground.CPair.oneValue_trans hst
            (ground.CPair.oneValue_symm hw)
        have hwtop : (⟨wn, wc⟩ : ground.CPair)
            ≤ chainHi foot (c :: cs) := by
          match chain_le S foot (c :: cs) hchain with
          | Or.inl e =>
            exact Or.inl (ground.CPair.oneValue_trans
              (ground.CPair.oneValue_symm hfw) e)
          | Or.inr hlt =>
            exact Or.inr (ground.CPair.lt_congr hfw
              (ground.CPair.oneValue_refl _) hlt)
        exact chainPsd S K foot c cs hchain wn wc
          (Or.inl hfw) hwtop spw hspw
    | .junc bn bc spb tn tc spt side N D, hst, hcr =>
      obtain ⟨_, hspb, hspt, hpsdt, htie, _⟩ := hcr
      have hbpsd : psdAt spb :=
        juncPsd S bn bc spb tn tc spt side N D hsh hspb hspt hpsdt
          htie
      have hwb : (⟨wn, wc⟩ : ground.CPair).oneValue ⟨bn, bc⟩ :=
        ground.CPair.oneValue_trans hw
          (ground.CPair.oneValue_symm hst)
      exact (cellcount.evalPC_pointCongr S K wn bn wc bc
        spw spb hsh hwb hspw hspb).trans hbpsd

set_option genInjectivity false in
/-- A gap's certificate (`thm:gappos`(v)'s counting sandwich data):
the committed magnitude bound pair, the fold cap, the anchored
margin certificate with its side — the lower flank at `true`, the
upper at `false` — and the clearing weight the width comparison
prices against. -/
structure GapCert (o : Nat) where
  bN : BPair
  bD : BPair
  bF : BPair
  rho : ground.Pos
  spM : Split o
  side : Bool

/-- One gap's committed reads (`thm:gappos`(v)): the strict fold
base, the endpoints' magnitude bounds, the entries' fold cap, the
anchored margin certificate positive semidefinite, and the clearing
comparison pricing the width below the margin at the anchor's own
clearing power. -/
def gapRead {o : Nat} (S : split.PMat) (K : Nat) :
    ground.CPair → ground.CPair → GapCert o → Prop
  | ⟨gln, glc⟩, ⟨grn, grc⟩, c =>
      BPair.unit < c.bD
      ∧ stage.cmag ⟨gln, glc⟩ * stage.ofB c.bD ≤ stage.ofB c.bN
      ∧ stage.cmag ⟨grn, grc⟩ * stage.ofB c.bD ≤ stage.ofB c.bN
      ∧ foldCap S c.bN c.bD c.bF
      ∧ (if c.side then
          splitRead (siteDatum (cellcount.evalPC S gln glc K)
            (matScale c.rho (idMat o))) c.spM
        else
          splitRead (siteDatum (cellcount.evalPC S grn grc K)
            (matScale c.rho (idMat o))) c.spM)
      ∧ psdAt c.spM
      ∧ (if c.side then
          BPair.ofNat o
            * ((c.bF * (grn.scale glc + (gln.swap).scale grc)).scale
              (ground.Pos.pow glc K))
            ≤ (BPair.ofPos c.rho).scale (grc * glc)
        else
          BPair.ofNat o
            * ((c.bF * (grn.scale glc + (gln.swap).scale grc)).scale
              (ground.Pos.pow grc K))
            ≤ (BPair.ofPos c.rho).scale (grc * glc))

instance {o : Nat} (S : split.PMat) (K : Nat)
    (gl gr : ground.CPair) (c : GapCert o) :
    Decidable (gapRead S K gl gr c) :=
  match gl, gr with
  | ⟨_, _⟩, ⟨_, _⟩ =>
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The committed gaps' reads, one certificate per gap. -/
def gapsRead {o : Nat} (S : split.PMat) (K : Nat) :
    List (ground.CPair × ground.CPair) → List (GapCert o) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | (gl, gr) :: gs, c :: cs =>
      gapRead S K gl gr c ∧ gapsRead S K gs cs

def decGapsRead {o : Nat} (S : split.PMat) (K : Nat) :
    ∀ (gs : List (ground.CPair × ground.CPair))
      (cs : List (GapCert o)),
    Decidable (gapsRead S K gs cs)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | (_, _) :: gs, _ :: cs =>
    have : Decidable (gapsRead S K gs cs) := decGapsRead S K gs cs
    inferInstanceAs (Decidable (_ ∧ _))

instance {o : Nat} (S : split.PMat) (K : Nat)
    (gs : List (ground.CPair × ground.CPair))
    (cs : List (GapCert o)) : Decidable (gapsRead S K gs cs) :=
  decGapsRead S K gs cs

/-- Every certified gap reads its interior points positive
semidefinite, the anchored sandwich at each gap's own side. -/
private theorem gapsPsd {o K : Nat} (S : split.PMat)
    (hsh : cellcount.pShapeAt S o K) (hsym : split.pSymAt S o) :
    ∀ (gs : List (ground.CPair × ground.CPair))
      (cs : List (GapCert o)),
    gapsRead S K gs cs →
    ∀ gl gr : ground.CPair, (gl, gr) ∈ gs →
    ∀ (vn : BPair) (vc : ground.Pos),
    gl < (⟨vn, vc⟩ : ground.CPair) →
    (⟨vn, vc⟩ : ground.CPair) < gr →
    ∀ sp : Split o,
    splitRead (cellcount.evalPC S vn vc K) sp → psdAt sp
  | [], _, _, _, _, hm, _, _, _, _, _, _ => nomatch hm
  | _ :: _, [], hr, _, _, _, _, _, _, _, _, _ => hr.elim
  | (⟨gln, glc⟩, ⟨grn, grc⟩) :: _, c :: _, hr, _, _, .head _,
      vn, vc, hlv, hvr, sp, hsp => by
    obtain ⟨hD, ha, hb, hF, hM, hMp, hcl⟩ := hr.1
    match hside : c.side with
    | true =>
      rw [hside] at hM hcl
      rw [if_pos rfl] at hM hcl
      exact gapPsd_lo S gln glc grn grc c.bN c.bD c.bF c.rho c.spM
        hsh hsym hD ha hb hF hM hMp hcl vn vc hlv hvr sp hsp
    | false =>
      rw [hside] at hM hcl
      rw [if_neg (fun h => Bool.noConfusion h)] at hM hcl
      exact gapPsd_hi S gln glc grn grc c.bN c.bD c.bF c.rho c.spM
        hsh hsym hD ha hb hF hM hMp hcl vn vc hlv hvr sp hsp
  | _ :: gs, _ :: cs, hr, gl, gr, .tail _ hm',
      vn, vc, hlv, hvr, sp, hsp =>
    gapsPsd S hsh hsym gs cs hr.2 gl gr hm' vn vc hlv hvr sp hsp

/-- The interior's whole read at one window's carrier
(`thm:gappos`(ii), (v): the pair reads hold across the cells' closed
union at `lem:cellcount`'s boundary clause, with every committed gap
handed its cut by the counting sandwich's anchored margin): at an
anchored occupied piece list whose gaps past the anchored head each
hold their certificate, every pair point from the foot to the top
reads every split of its evaluation positive semidefinite — the
anchored head gap its own vacancy at the start read, the point
binder the consumer's own ray. -/
theorem interiorPsd {o K : Nat} (S : split.PMat) (lo : ground.CPair)
    (p : Piece o) (l : List (Piece o)) (cs : List (GapCert o))
    (hsh : cellcount.pShapeAt S o K)
    (hsym : split.pSymAt S o)
    (hst : startsAt lo (p :: l))
    (hcr : closedRead S K lo (p :: l))
    (hgr : gapsRead S K (closedGaps (closedHi lo [p]) l) cs) :
    ∀ (vn : BPair) (vc : ground.Pos),
    lo ≤ (⟨vn, vc⟩ : ground.CPair) →
    (⟨vn, vc⟩ : ground.CPair) ≤ closedHi lo (p :: l) →
    ∀ sp : Split o,
    splitRead (cellcount.evalPC S vn vc K) sp → psdAt sp := by
  refine closedPsd S lo p l hsh hst hcr ?_
  match p, hst, hgr with
  | .seg foot cells, hst, hgr =>
    intro gl gr hm vn vc h1 h2 sp hsp
    cases hm with
    | head =>
      exact (ground.lt_asymm h1 (ground.CPair.lt_congr
        (ground.CPair.oneValue_refl _) hst h2)).elim
    | tail _ hm' =>
      exact gapsPsd S hsh hsym _ cs hgr gl gr hm' vn vc h1 h2 sp hsp
  | .junc bn bc spb tn tc spt side N D, hst, hgr =>
    intro gl gr hm vn vc h1 h2 sp hsp
    cases hm with
    | head =>
      exact (ground.lt_asymm h1 (ground.CPair.lt_congr
        (ground.CPair.oneValue_refl _) hst h2)).elim
    | tail _ hm' =>
      exact gapsPsd S hsh hsym _ cs hgr gl gr hm' vn vc h1 h2 sp hsp

/-- The cutoff's price closes at the cut (`thm:gappos`(iii)): at the
magnetic cap and the polarization tie of `thm:truncation`, a window
whose compression reads the cut at the level raised by the cofactor
width reads the cut itself at the level — the removed block's
vacancy derived at the admissible cutoff's own data, the electric
diagonal at or above the cutoff with the block's magnetic cap and
the floor tie `x + ς + W + g = c + y`
(`truncation.removed_psd`), and the window cuts transported to
`𝒦(v)` within the priced modulus (`truncation.count_shift_le` at
the vacant counts). -/
theorem truncCut {k m : Nat} (H G M M1 M2 P G1 Q De G2 B : Mat)
    (x y cw W s c g : Pos)
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
    (hlev : x + s + W + g = c + y)
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
    truncation.removed_psd Q De M2 G2 c W (x + s) y g spDi spG spB spR
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

end gappos
