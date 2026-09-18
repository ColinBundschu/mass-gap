import MassGap.Decimation
import MassGap.Gradingindex
/-!
`thm:decimation` at a member window.  The window's positions read the
grading (`lem:grading`; `grading.gradedIdx`): the tower places are the
positions whose configuration reads the tower read, the head places the
positions at the head read, and the far places the positions at the
slab read off the tower (`pairpencil.placesAt`, `towerPlaces`,
`headPlaces`, `farPlaces`, a class in both ranges the tower's), the three a
partition of the window's order at the window list (`places_length`,
`places_distinct`, `places_bounded`).  The
window's level datum is the pencil's site datum at the ray joined to
the level pair's gram copies (`certconstruct.levelDatum`,
`thm:certconstruct`'s count at a balance-pair level).
The decimated symbol at the window (`window_count`) is
`decimated_count` at those places: the level datum decimates onto the
head places at the tower block's dominance comparison and the far
slabs' deck pivot, the head shell the head places' own and the far
shells stated data with the chain's off-band read deciding their
shape, the decimated head the head shell's pivot at the head's order.
Clause (i) at the window (`window_chain`): the members' positions are
the window list's, the unit line at position nought (`memberPos`), the
vacuum class the chain's boundary shell, and
the level datum reads off band across two unjoined members, the gram
and the electric form block diagonal over the index
(`pairpencil.gramBlockRead`, `pairpencil.formE`) and the magnetic
member the terms' sum, a term's entry off the sum's unit the join
itself (`depthchain.joinedAt`), so the count splits over the window's
depth chain (`site_cross` at `chain_count`), the window's labels at a
stated domain with one spelling per label (`con:labels`;
`carrier.eqConf_eq`).
-/

namespace decimation
open ground elim inertia greenprod lattice fusion

/-! ### The places at the grading's reads -/

/-- The tower places: the positions at the tower read. -/
def towerPlaces {L : Type} (F : Data L) (R : Region) (lamH : Nat)
    (ix : List (List L)) (n : Nat) : List Nat :=
  pairpencil.placesAt F R ix n (grading.towerAt F R lamH)

/-- The head places: the positions at the head read, every component's
content below the bound and every pair within the band. -/
def headPlaces {L : Type} (F : Data L) (R : Region) (lamH : Nat)
    (ix : List (List L)) (n : Nat) : List Nat :=
  pairpencil.placesAt F R ix n (fun a => !(grading.towerAt F R lamH a || grading.slabAt F R a))

/-- The far places: the positions at the slab read off the tower, a
class in both ranges the tower block's. -/
def farPlaces {L : Type} (F : Data L) (R : Region) (lamH : Nat)
    (ix : List (List L)) (n : Nat) : List Nat :=
  pairpencil.placesAt F R ix n (fun a => !(grading.towerAt F R lamH a) && grading.slabAt F R a)

/-- The three places lists' count is the window's order. -/
theorem places_length {L : Type} (F : Data L) (R : Region) (lamH : Nat)
    (ix : List (List L)) (n : Nat) :
    (towerPlaces F R lamH ix n
      ++ (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n)).length = n := by
  rw [length_append, length_append]
  have h := length_filter_three
    (fun i => grading.towerAt F R lamH (pairpencil.posConf F R ix i))
    (fun i => grading.slabAt F R (pairpencil.posConf F R ix i)) (List.range n)
  rw [length_range] at h
  exact h

/-- The three places lists are distinct at their join: each list
distinct at the range's, and the reads disjoint. -/
theorem places_distinct {L : Type} (F : Data L) (R : Region) (lamH : Nat)
    (ix : List (List L)) (n : Nat) :
    distinctList (towerPlaces F R lamH ix n
      ++ (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n)) := by
  refine distinctList_append_disjoint _ _
    (distinctList_filter _ _ (distinctList_range n))
    (distinctList_append_disjoint _ _
      (distinctList_filter _ _ (distinctList_range n))
      (distinctList_filter _ _ (distinctList_range n)) ?_) ?_
  · intro i hh hf
    have h1 : (!(grading.towerAt F R lamH (pairpencil.posConf F R ix i)
        || grading.slabAt F R (pairpencil.posConf F R ix i))) = true :=
      (mem_filter_of _ _ i hh).2
    have h2 : (!(grading.towerAt F R lamH (pairpencil.posConf F R ix i))
        && grading.slabAt F R (pairpencil.posConf F R ix i)) = true :=
      (mem_filter_of _ _ i hf).2
    cases hT : grading.towerAt F R lamH (pairpencil.posConf F R ix i) with
    | true => rw [hT] at h2; exact Bool.noConfusion h2
    | false =>
      cases hQ : grading.slabAt F R (pairpencil.posConf F R ix i) with
      | true => rw [hT, hQ] at h1; exact Bool.noConfusion h1
      | false => rw [hT, hQ] at h2; exact Bool.noConfusion h2
  · intro i ht hr
    have h1 : grading.towerAt F R lamH (pairpencil.posConf F R ix i) = true :=
      (mem_filter_of _ _ i ht).2
    cases mem_append_of _ _ hr with
    | inl hh =>
      have h2 : (!(grading.towerAt F R lamH (pairpencil.posConf F R ix i)
          || grading.slabAt F R (pairpencil.posConf F R ix i))) = true :=
        (mem_filter_of _ _ i hh).2
      rw [h1] at h2
      exact Bool.noConfusion h2
    | inr hf =>
      have h2 : (!(grading.towerAt F R lamH (pairpencil.posConf F R ix i))
          && grading.slabAt F R (pairpencil.posConf F R ix i)) = true :=
        (mem_filter_of _ _ i hf).2
      rw [h1] at h2
      exact Bool.noConfusion h2

/-- Every place sits below the window's order. -/
theorem places_bounded {L : Type} (F : Data L) (R : Region) (lamH : Nat)
    (ix : List (List L)) (n : Nat) :
    ((towerPlaces F R lamH ix n
      ++ (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n)).all
        (fun i => Nat.blt i n)) = true := by
  refine all_of_mem_intro _ _ (fun i hi => ltBlt (ltOfMemRange ?_))
  cases mem_append_of _ _ hi with
  | inl h => exact (mem_filter_of _ _ i h).1
  | inr h =>
    cases mem_append_of _ _ h with
    | inl h' => exact (mem_filter_of _ _ i h').1
    | inr h' => exact (mem_filter_of _ _ i h').1

/-! ### The decimated symbol at the window -/

/-- The decimated symbol at a member window: at the tower places'
dominance comparison and the far slabs inside the deck pivot's ball,
the level datum's count is the head shell's pivot's, the head shell
the head places' own and the far shells stated over the further
places (`decimated_count` at the grading's places). -/
theorem window_count {L : Type} {o : Nat} (F : Data L) (R : Region) (lamH : Nat)
    (ix : List (List L)) (n : Nat) (H G : Mat) (x y : Pos)
    (hS : sqAt (certconstruct.levelDatum H G x y) n)
    (hsym : matOneValue (transposeM (certconstruct.levelDatum H G x y)) (certconstruct.levelDatum H G x y))
    (hk0 : 0 < (towerPlaces F R lamH ix n).length)
    (spT : Split (towerPlaces F R lamH ix n).length)
    (hT : splitRead (selM (towerPlaces F R lamH ix n) (towerPlaces F R lamH ix n)
      (certconstruct.levelDatum H G x y)) spT)
    (hdom : gapPos (selM (towerPlaces F R lamH ix n) (towerPlaces F R lamH ix n)
      (certconstruct.levelDatum H G x y)))
    (spS : Split n) (hS' : splitRead (certconstruct.levelDatum H G x y) spS)
    (spD : Split (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n).length)
    (hD : splitRead (towerDefl (certconstruct.levelDatum H G x y) (towerPlaces F R lamH ix n)
      (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n)) spD)
    (farSh : List (List Nat))
    (hshl : ((List.range (headPlaces F R lamH ix n).length :: farSh).flatMap
      (fun s => s)).length
      = (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n).length)
    (hshd : distinctList ((List.range (headPlaces F R lamH ix n).length :: farSh).flatMap
      (fun s => s)))
    (hshb : (((List.range (headPlaces F R lamH ix n).length :: farSh).flatMap
      (fun s => s)).all (fun i =>
        Nat.blt i (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n).length)) = true)
    (hocc : ∀ s, s ∈ (List.range (headPlaces F R lamH ix n).length :: farSh) → 0 < s.length)
    (hoff : depthchain.offBandB (towerDefl (certconstruct.levelDatum H G x y) (towerPlaces F R lamH ix n)
      (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n))
      (List.range (headPlaces F R lamH ix n).length :: farSh) = true)
    (X1 : MatQ) (Xs Rs : List MatQ) (ns : List Nat)
    (s1 : (k : Nat) × Split k) (sps : List ((k : Nat) × Split k))
    (ht : tailRead
      (depthchain.slabDiag (towerDefl (certconstruct.levelDatum H G x y) (towerPlaces F R lamH ix n)
        (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n))
        (List.range (headPlaces F R lamH ix n).length :: farSh))
      (depthchain.slabOff (towerDefl (certconstruct.levelDatum H G x y) (towerPlaces F R lamH ix n)
        (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n))
        (List.range (headPlaces F R lamH ix n).length :: farSh)) (X1 :: Xs) Rs ns)
    (hl : revListRead (X1 :: Xs) (s1 :: sps))
    (spC : Split (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n).length)
    (hC : splitRead (assemble
      (depthchain.slabDiag (towerDefl (certconstruct.levelDatum H G x y) (towerPlaces F R lamH ix n)
        (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n))
        (List.range (headPlaces F R lamH ix n).length :: farSh))
      (depthchain.slabOff (towerDefl (certconstruct.levelDatum H G x y) (towerPlaces F R lamH ix n)
        (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n))
        (List.range (headPlaces F R lamH ix n).length :: farSh))) spC)
    (Y : MatQ) (Gb : Mat) (y0n y0d rn rd : Pos) (spF : Split o)
    (bsps : List (Split o × Split o))
    (hYc : sqAt Y.1 o) (hF : spectator.floorRead Y Gb y0n y0d rn rd spF)
    (hball : spectator.ballList Y Gb rn rd Xs bsps) :
    revAt spS = revAt s1.2 :=
  decimated_count (certconstruct.levelDatum H G x y) (towerPlaces F R lamH ix n)
    (headPlaces F R lamH ix n ++ farPlaces F R lamH ix n) hk0 hS hsym
    (places_length F R lamH ix n) (places_distinct F R lamH ix n)
    (places_bounded F R lamH ix n) spT hT hdom spS hS' spD hD
    (List.range (headPlaces F R lamH ix n).length :: farSh) hshl hshd hshb hocc hoff
    X1 Xs Rs ns s1 sps ht hl spC hC Y Gb y0n y0d rn rd spF bsps hYc hF hball

/-! ### Clause (i) at the window: the depth chain -/

/-- The members' positions at the window list: the unit line at
position nought, then per index member the positions past it whose
configuration is the member. -/
def memberPos {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (n : Nat) : List (List Nat) :=
  [0] :: ix.map (fun a => (List.range n).filter (fun i =>
    decide (0 < i) && decide (pairpencil.posConf F R ix i = a)))

/-- A member's positions past nought read the member. -/
private theorem memberPos_read {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (n : Nat) (k i : Nat)
    (hi : i ∈ getAt [] (memberPos F R ix n) (k + 1)) :
    k < ix.length ∧ 0 < i ∧ i < n
      ∧ pairpencil.posConf F R ix i = getAt [] ix k := by
  have hi' : i ∈ getAt [] (ix.map (fun a => (List.range n).filter (fun i =>
      decide (0 < i) && decide (pairpencil.posConf F R ix i = a)))) k := hi
  cases Nat.lt_or_ge k ix.length with
  | inl hk =>
    rw [getAt_map [] [] _ ix k hk] at hi'
    obtain ⟨hr, hp⟩ := mem_filter_of _ _ i hi'
    obtain ⟨h0, he⟩ := andSplitB hp
    exact ⟨hk, of_decide_eq_true h0, ltOfMemRange hr, of_decide_eq_true he⟩
  | inr hk =>
    rw [getAt_over [] _ k (by rw [length_map]; exact hk)] at hi'
    exact nomatch hi'

/-- Every listed position sits below the order. -/
private theorem memberPos_lt {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (n : Nat) (hn : 0 < n) (a i : Nat)
    (hi : i ∈ getAt [] (memberPos F R ix n) a) : i < n := by
  cases a with
  | zero =>
    rw [eq_of_mem_single hi]
    exact hn
  | succ k => exact (memberPos_read F R ix n k i hi).2.2.1

/-- A rescaled unit read is the unit read. -/
private theorem scale_unit_read {z : BPair} (w : Pos)
    (h : z.oneValue BPair.unit) : (z.scale w).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.scale_congr w h) (BPair.unit_scale w)

/-- The level datum's entry at a position pair whose gram and magnetic
entries read the sum's unit reads the sum's unit: the electric form's
entry is the content against the gram's, and every summand of the
site datum is a unit read rescaled or swapped. -/
private theorem site_entry_unit (diag : List Nat) (n : Nat) (hdl : diag.length = n)
    (G M : Mat) (hG : sqAt G n) (hM : sqAt M n) (al be x y : Pos)
    (i j : Nat) (hi : i < n) (hj : j < n)
    (hG0 : (getAt BPair.unit (getAt [] G i) j).oneValue BPair.unit)
    (hM0 : (getAt BPair.unit (getAt [] M i) j).oneValue BPair.unit) :
    (getAt BPair.unit
      (getAt [] (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y) i) j).oneValue
        BPair.unit := by
  have hGl : G.length = n := sqAt_len hG
  have hGr : rowsLen n G := rowsLen_of_sqAt hG
  have hMl : M.length = n := sqAt_len hM
  have hMr : rowsLen n M := rowsLen_of_sqAt hM
  have hE : sqAt (pairpencil.formE diag G) n := pairpencil.sqAt_formE diag G n hdl
  have hH : sqAt (pairpencil.pencilH al be diag G M) n :=
    pencil.sqAt_rayH _ M n hE hM al be
  have hAE : sqAt (matScale al (pairpencil.formE diag G)) n := sqAt_matScale n al _ hE
  have hBM : sqAt (matScale be M) n := sqAt_matScale n be M hM
  have hYG : sqAt (matScale y G) n := sqAt_matScale n y G hG
  have hXG : sqAt (matScale x G) n := sqAt_matScale n x G hG
  have hAdd : sqAt (matAdd (pairpencil.pencilH al be diag G M) (matScale y G)) n :=
    sqAt_matAdd n _ _ hH hYG
  show (getAt BPair.unit (getAt []
    (siteDatum (matAdd (pairpencil.pencilH al be diag G M) (matScale y G))
      (matScale x G)) i) j).oneValue BPair.unit
  rw [siteDatum_entry _ _ n (rowsLen_of_sqAt hAdd) (rowsLen_of_sqAt hXG) i j
      (by rw [sqAt_len hAdd]; exact hi) (by rw [sqAt_len hXG]; exact hi) hj,
    entry_matAdd _ _ n (rowsLen_of_sqAt hH) (rowsLen_of_sqAt hYG) i j
      (by rw [sqAt_len hH]; exact hi) (by rw [sqAt_len hYG]; exact hi) hj,
    matScale_entry y G i j (by rw [hGl]; exact hi)
      (by rw [rowsLen_getAt G i hGr (by rw [hGl]; exact hi)]; exact hj),
    matScale_entry x G i j (by rw [hGl]; exact hi)
      (by rw [rowsLen_getAt G i hGr (by rw [hGl]; exact hi)]; exact hj)]
  have hHe : (getAt BPair.unit (getAt [] (pairpencil.pencilH al be diag G M) i) j).oneValue
      BPair.unit := by
    show (getAt BPair.unit (getAt []
      (siteDatum (matScale al (pairpencil.formE diag G)) (matScale be M)) i) j).oneValue
        BPair.unit
    rw [siteDatum_entry _ _ n (rowsLen_of_sqAt hAE) (rowsLen_of_sqAt hBM) i j
        (by rw [sqAt_len hAE]; exact hi) (by rw [sqAt_len hBM]; exact hi) hj,
      matScale_entry al _ i j (by rw [sqAt_len hE]; exact hi)
        (by rw [rowsLen_getAt _ i (rowsLen_of_sqAt hE) (by rw [sqAt_len hE]; exact hi)]
            exact hj),
      matScale_entry be M i j (by rw [hMl]; exact hi)
        (by rw [rowsLen_getAt M i hMr (by rw [hMl]; exact hi)]; exact hj)]
    exact BPair.add_units
      (scale_unit_read al (pairpencil.formE_entry_unit diag G i j (by rw [hdl]; exact hi)
        (by rw [hdl]; exact hj) hG0))
      (swap_congr (scale_unit_read be hM0))
  exact BPair.add_units (BPair.add_units hHe (scale_unit_read y hG0))
    (swap_congr (scale_unit_read x hG0))

/-- The level datum reads off band across two unjoined members: at
two positions of distinct members the gram's entry reads the sum's
unit at the block read, and at unjoined members every term's entry
does, so the magnetic member's sum entry does with them. -/
private theorem site_cross {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (n : Nat) (hn : 0 < n)
    (P : L → Bool) (hunitP : P F.unit = true)
    (hix : ∀ a, a ∈ ix → a.all P = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y)
    (hoff : ∀ a, a ∈ ix → (a.any (fun l => !(F.eqL l F.unit))) = true)
    (hdist : distinctList ix)
    (diag : List Nat) (hdl : diag.length = n) (G M : Mat) (c : Pos) (al be x y : Pos)
    (terms : List Mat) (hT : ∀ T, T ∈ terms → sqAt T n)
    (hG : sqAt G n) (hM : sqAt M n)
    (hgram : pairpencil.gramBlockRead F R n ix c G)
    (hMsum : matOneValue M (msum n (getAt [] terms) (List.range terms.length))) :
    depthchain.crossB terms (memberPos F R ix n)
      (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y) = true := by
  refine all_range_intro _ (fun a ha => all_range_intro _ (fun b hb => ?_))
  cases hab : (a == b) with
  | true => rfl
  | false =>
    cases hjn : depthchain.joined terms (memberPos F R ix n) a b with
    | true => rfl
    | false =>
      show (false || false || ((getAt [] (memberPos F R ix n) a).all (fun i =>
        (getAt [] (memberPos F R ix n) b).all (fun j =>
          decide ((getAt BPair.unit (getAt []
            (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y) i) j).oneValue
              BPair.unit))))) = true
      refine all_of_mem_intro _ _ (fun i hi => all_of_mem_intro _ _ (fun j hj =>
        decide_eq_true ?_))
      have hi' : i < n := memberPos_lt F R ix n hn a i hi
      have hj' : j < n := memberPos_lt F R ix n hn b j hj
      have hne : ¬ a = b := of_decide_eq_false hab
      -- the terms' entries read the unit at the unjoined pair
      have hterm : ∀ T, T ∈ terms →
          (getAt BPair.unit (getAt [] T i) j).oneValue BPair.unit := by
        intro T hTm
        have h1 := all_of_mem _ _ (all_not_of_any_false _ _ hjn) i hi
        have h2 : (getAt [] (memberPos F R ix n) b).any
            (fun j => depthchain.joinedAt terms i j) = false := by
          cases h2' : (getAt [] (memberPos F R ix n) b).any
              (fun j => depthchain.joinedAt terms i j) with
          | false => rfl
          | true => rw [h2'] at h1; exact Bool.noConfusion h1
        have h3 := all_of_mem _ _ (all_not_of_any_false _ _ h2) j hj
        have h4 : depthchain.joinedAt terms i j = false := by
          cases h4' : depthchain.joinedAt terms i j with
          | false => rfl
          | true => rw [h4'] at h3; exact Bool.noConfusion h3
        have h5 := all_of_mem _ _ (all_not_of_any_false _ _ h4) T hTm
        cases h6 : decide ((getAt BPair.unit (getAt [] T i) j).oneValue BPair.unit) with
        | true => exact of_decide_eq_true h6
        | false => rw [h6] at h5; exact Bool.noConfusion h5
      -- the magnetic member's entry at the pair
      have hM0 : (getAt BPair.unit (getAt [] M i) j).oneValue BPair.unit := by
        refine BPair.oneValue_trans (matOne_entry hMsum i j (by rw [sqAt_len hM]; exact hi')) ?_
        rw [entry_msum n (getAt [] terms) i j hi' hj' (List.range terms.length)
          (fun k hk => by
            have hkm := mem_getAt [] terms k (ltOfMemRange hk)
            exact ⟨rowsLen_of_sqAt (hT _ hkm), sqAt_len (hT _ hkm)⟩)]
        refine famFold_unit_ov bpairFoldLaws _ (fun k => ?_) _
        cases Nat.lt_or_ge k terms.length with
        | inl hk => exact hterm _ (mem_getAt [] terms k hk)
        | inr hk =>
          rw [getAt_over [] terms k hk]
          show (getAt BPair.unit ([] : List BPair) j).oneValue BPair.unit
          exact BPair.oneValue_refl _
      -- the gram's entry at the pair: the two positions' configurations differ
      have hG0 : (getAt BPair.unit (getAt [] G i) j).oneValue BPair.unit := by
        have h1 : (List.range n).all (fun j =>
            carrier.eqConf F (pairpencil.posConf F R ix i) (pairpencil.posConf F R ix j)
              || decide ((getAt BPair.unit (getAt [] G i) j).oneValue BPair.unit)) = true :=
          all_range_read n hgram.2.1 i hi'
        have h2 : (carrier.eqConf F (pairpencil.posConf F R ix i) (pairpencil.posConf F R ix j)
            || decide ((getAt BPair.unit (getAt [] G i) j).oneValue BPair.unit)) = true :=
          all_range_read n h1 j hj'
        cases orSplitB h2 with
        | inr h => exact of_decide_eq_true h
        | inl he =>
          exfalso
          have heq : pairpencil.posConf F R ix i = pairpencil.posConf F R ix j :=
            carrier.eqConf_eq F P hred _ _ (pairpencil.posConf_labels F R ix P hunitP hix i)
              (pairpencil.posConf_labels F R ix P hunitP hix j) he
          -- the unit configuration holds no nonunit label
          have hunit : ∀ a, a ∈ ix → ¬ (carrier.unitConf F R = a) := by
            intro a ha hu
            obtain ⟨l, hl, hne⟩ := mem_of_any _ _ (hoff a ha)
            rw [← hu] at hl
            rw [mem_replicate_eq F.unit R.links l hl, F.eqLRefl] at hne
            exact Bool.noConfusion hne
          cases a with
          | zero =>
            cases b with
            | zero => exact hne rfl
            | succ kb =>
              obtain ⟨hkb, _, _, hpb⟩ := memberPos_read F R ix n kb j hj
              rw [eq_of_mem_single hi] at heq
              exact hunit _ (mem_getAt [] ix kb hkb) (heq.trans hpb)
          | succ ka =>
            obtain ⟨hka, _, _, hpa⟩ := memberPos_read F R ix n ka i hi
            cases b with
            | zero =>
              rw [eq_of_mem_single hj] at heq
              exact hunit _ (mem_getAt [] ix ka hka) (heq.symm.trans hpa)
            | succ kb =>
              obtain ⟨hkb, _, _, hpb⟩ := memberPos_read F R ix n kb j hj
              have hk : ka = kb :=
                getAt_inj_distinct [] ix hdist ka kb hka hkb (hpa.symm.trans (heq.trans hpb))
              exact hne (congrArg Nat.succ hk)
      exact site_entry_unit diag n hdl G M hG hM al be x y i j hi' hj' hG0 hM0

/-- Clause (i) at the window: the count at every level splits over the
window's depth chain.  The level datum reads off band across unjoined
members (`site_cross`), so at a depth order listing every position
once its split reads the chain's own count, the pivots' fold
(`chain_count`). -/
theorem window_chain {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (ix : List (List L)) (n : Nat) (hn : 0 < n)
    (P : L → Bool) (hunitP : P F.unit = true)
    (hix : ∀ a, a ∈ ix → a.all P = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y)
    (hoff : ∀ a, a ∈ ix → (a.any (fun l => !(F.eqL l F.unit))) = true)
    (hdist : distinctList ix)
    (diag : List Nat) (hdl : diag.length = n) (G M : Mat) (c : Pos) (al be x y : Pos)
    (terms : List Mat)
    (hT : ∀ T, T ∈ terms → sqAt T n ∧ matOneValue (transposeM T) T)
    (hG : sqAt G n) (hM : sqAt M n)
    (hgram : pairpencil.gramBlockRead F R n ix c G)
    (hMsum : matOneValue M (msum n (getAt [] terms) (List.range terms.length)))
    (hocc : ∀ a, a < (memberPos F R ix n).length →
      0 < (getAt [] (memberPos F R ix n) a).length)
    (hS : sqAt (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y) n)
    (hsym : matOneValue (transposeM (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y))
      (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y))
    (hlen : (depthchain.depthOrder terms (memberPos F R ix n)
      (memberPos F R ix n).length [0]).length = n)
    (hdist' : distinctList (depthchain.depthOrder terms (memberPos F R ix n)
      (memberPos F R ix n).length [0]))
    (Xs Rs : List MatQ) (ns : List Nat)
    (sps : List ((k : Nat) × Split k))
    (ht : tailRead
      (depthchain.slabDiag (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y)
        (depthchain.posShells terms (memberPos F R ix n) (memberPos F R ix n).length [0]))
      (depthchain.slabOff (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y)
        (depthchain.posShells terms (memberPos F R ix n) (memberPos F R ix n).length [0]))
      Xs Rs ns)
    (hl : revListRead Xs sps)
    (spM : Split n) (hspM : splitRead (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y) spM)
    (spC : Split n)
    (hspC : splitRead (assemble
      (depthchain.slabDiag (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y)
        (depthchain.posShells terms (memberPos F R ix n) (memberPos F R ix n).length [0]))
      (depthchain.slabOff (certconstruct.levelDatum (pairpencil.pencilH al be diag G M) G x y)
        (depthchain.posShells terms (memberPos F R ix n) (memberPos F R ix n).length [0])))
      spC) :
    revAt spM = revFold sps :=
  chain_count terms (memberPos F R ix n) (memberPos F R ix n).length [0] n hT
    (fun s hs i hi => by
      obtain ⟨a, ha, hsa⟩ := getAt_of_mem [] hs
      rw [← hsa] at hi
      exact memberPos_lt F R ix n hn a i hi)
    hocc rfl _ hS hsym
    (site_cross F R ix n hn P hunitP hix hred hoff hdist diag hdl G M c al be x y terms
      (fun T hTm => (hT T hTm).1) hG hM hgram hMsum)
    hlen hdist'
    (all_of_mem_intro _ _ (fun i hi => by
      obtain ⟨s, hs, his⟩ := mem_flatMap_of _ _ i hi
      obtain ⟨sm, _, hsm⟩ := mem_map_of _ _ s hs
      rw [← hsm] at his
      obtain ⟨a, _, hia⟩ := mem_flatMap_of _ _ i his
      exact ltBlt (memberPos_lt F R ix n hn a i hia)))
    Xs Rs ns sps ht hl spM hspM spC hspC

end decimation
