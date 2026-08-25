import MassGap.Flatstep
import MassGap.Cellcount
import MassGap.Truncation
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
-/

namespace gappos
open ground elim inertia certconstruct flatstep

/-- The three-term sum's last two members exchange. -/
private theorem addLR (A B C : Mat) :
    matAdd (matAdd A B) C = matAdd (matAdd A C) B := by
  rw [elim.matAdd_assoc A B C, elim.matAdd_comm B C,
    elim.matAdd_assoc A C B]

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
    addLR (matAdd H (matSwap H'))
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
  rw [addLR H' S (matSwap H')] at hs1
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
      hcap.2.2.2.2.1
  exact countAtPair_mono H H' G x (y + rho) x y n n' sp sp' spL
    hspL hcap.2.2.2.2.2 h h'

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
      hcap.2.2.1
  exact countAtPair_mono H' H G x y (x + rho) y n' n sp' sp spU
    hspU hcap.2.2.2.1 h' h

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
the two window counts' certificates and the diagonalizing
congruence, `lem:split`'s one list — a flat window at the ground
multiplicity brackets the edge between its ends, the below count
squeezed by the level monotonicity, and the spectral read closes
the cut at any stated split of the cut's site datum, the cut tie
landed whole. -/
theorem windowCut {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair)) (E0 p q : Pos) (g : Nat)
    (hsym : matOneValue (transposeM Et) Et)
    (hd : split.diagRead Et (idMat n) T Tw l)
    (hker : split.rootsAtKernel (l.map (fun r => (r.1, r.2.1))) = g)
    (ax ay tx ty : Pos) (spa spt : Split n)
    (hca : split.countRead Et (idMat n)
      (l.map (fun r => (r.1, r.2.1))) ax ay spa)
    (hct : split.countRead Et (idMat n)
      (l.map (fun r => (r.1, r.2.1))) tx ty spt)
    (hga : revAt spa = g) (hgt : revAt spt = g)
    (hae : ax * q ≤ E0 * p * ay) (het : E0 * p * ty ≤ tx * q)
    (hEE : sqAt (matMul Et Et) n) (sp : Split n)
    (hsp : splitRead (siteDatum (matScale q (matMul Et Et))
        (matScale (E0 * p) Et)) sp) :
    speccut.cutTie Et (l.map (fun r => (r.1, r.2.1))) E0 p q sp := by
  have hedge : split.rootsBelow (l.map (fun r => (r.1, r.2.1)))
      (E0 * p) q = g :=
    Nat.le_antisymm
      ((hct.2.2.2.2.2.symm.trans hgt) ▸
        split.rootsBelow_mono (l.map (fun r => (r.1, r.2.1)))
          (E0 * p) q tx ty het)
      ((hca.2.2.2.2.2.symm.trans hga) ▸
        split.rootsBelow_mono (l.map (fun r => (r.1, r.2.1)))
          ax ay (E0 * p) q hae)
  have hspec : speccut.specRead (l.map (fun r => (r.1, r.2.1)))
      E0 p q :=
    flatstep.flat_spec (l.map (fun r => (r.1, r.2.1))) E0 p q g
      hedge hker
  refine ⟨?_, hspec,
    hEE, hd.1, hsp, speccut.spec_to_cut Et T Tw l E0 p q hsym hd
      hspec sp hsp⟩
  rw [show Et.length = n from elim.sqAt_len hd.1]
  exact hca.2.2.1

end gappos
