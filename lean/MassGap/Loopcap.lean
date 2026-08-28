import MassGap.Coeff
import MassGap.Fpcap
import MassGap.Pairpencil
/-!
`lem:loopcap` — the loop window's form cap at the label index.  At a
loop window the magnetic matrix is the fusion form's own at the
self-dual `θ` over the unit-headed label list (`pairpencil.loopMag`,
the two spellings one datum), so the shifted term reads the
character's two-sided cap: unit width below and `r (r + 2)` above.
The upper side is `lem:fpcap`'s cap at `θ`'s instance
(`shiftUpper`), the interface's window reads its hypotheses — the
tex's own bare derivation is the cut tier below, the coefficient
carrier's; the lower side is the Gram
route (`shiftLower`) —
the squared fundamental's composition read `Σ_c N^c_{f x} N^c_{f y}
= N^x_{θ y} + δ_{xy}` at the window (`fpcap.compRead`) turns the
shifted form's double fold into the fundamental's window block
against the vector, the block's own squares summed over the
intermediate labels, at or above the sum's unit by the pairing's
one-sided read (`elim.dotN_self_side`).  The window's labels enter
pairwise distinct at the index's equality (`hdist`, `fpcap`'s
`distinctAt` — the decided fold whose pointwise decode converts the
label equality to the positional one), which is where the
composition read's `δ` becomes the identity the shifted term's
first summand carries.

The loop-cut tier reads the coefficient carrier's pairing
(`con:coeff`).  `cutSq` is the display: at joined slot coordinates
whose two self-pairings read the count against the two grams — the
evaluation identity's contractions — the squared Cauchy–Schwarz
over the joined list (`coeff.dotP_sq_le`) prices the pairing's
square at or below the count's square against the grams' product.
`cutCap` reads the order back at the image: the cut datum's own
pairing reads the image's gram, and the count cancels off the
comparison (`ground.leB_unscale`) to leave the image's gram at or
below the squared count against the vector's, the vacant arm
closing at the pairing's definiteness (`elim.dotP_self_null`,
where the absent count forces the pairing to the sum's unit).
`cutForm` reads the term two-sided: one further squared
Cauchy–Schwarz at a window vector against its image, the squared
comparison reading back at the trichotomy (`ground.leB_of_sq_le`),
so the form and its memberwise swap each sit at or below the count
against the gram.  `prop:wg`'s presentation Gram is the recorded
site; `thm:truncation`'s member cap is the consumer.
-/

namespace loopcap
open ground fusion elim

/-- The shifted term's upper side at a loop window: the `θ`-cap's
own instance, `r (r+2)` above at the interface's dimension
(`lem:loopcap`; `lem:fpcap`'s cap at the self-dual `θ`). -/
theorem shiftUpper {L : Type} (F : fusion.Data L) (ls : List L)
    (hsym : fpcap.symAt F F.theta (F.unit :: ls))
    (hrow : fpcap.rowCap F F.theta (F.unit :: ls))
    (hdim : fpcap.dimPos F (F.unit :: ls))
    (u : List ground.BPair) (hu : u.length = ls.length + 1) :
    ¬ (ground.BPair.ofNat (F.dim F.theta) * elim.dotN u u
        < inertia.quadForm (pairpencil.loopMag F ls) u) :=
  fpcap.capUpper F F.theta (F.unit :: ls) hsym hrow hdim u hu

/-! The equality diagonal: at pairwise-distinct labels the window's
squares collect from the positional delta's double fold, over
`def:ground`'s delta pick (`bsum_pick`, a key occupied once in an
index family read off the delta family's fold). -/

/-- The equality diagonal as the delta double fold: at a positional
delta the window's squares collect from the double fold. -/
private theorem deltaFold (n : Nat) (dl : Nat → Nat → Nat)
    (uu : Nat → BPair)
    (hdl : ∀ i j, i < n → j < n →
      dl i j = if i = j then 1 else 0) :
    (bsum (fun i => uu i * uu i) (List.range n)).oneValue
      (bsum (fun i => bsum (fun j =>
        BPair.ofNat (dl i j) * (uu i * uu j)) (List.range n))
        (List.range n)) := by
  refine foldB_congr_members _ _ (List.range n) (fun i hi => ?_)
  have hin : i < n := ground.ltOfMem hi
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (foldB_congr_members _ (fun j => if i = j then uu i * uu j
      else BPair.unit) (List.range n) (fun j hj => ?_))
    (bsum_pick (fun j => uu i * uu j) (List.range n) i ?_))
  · have hjn : j < n := ground.ltOfMem hj
    rw [hdl i j hin hjn]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij,
        BPair.mul_comm (BPair.ofNat 1) (uu i * uu j)]
      exact BPair.mul_ofNat_one _
    · rw [if_neg hij, if_neg hij]
      exact BPair.unit_mul _
  · rw [ground.countOf_range_one hin]

/-- The two folds merge at the composition's count: the window's
squares against the shifted form collect to the composed count's own
double fold. -/
private theorem sumFold (n : Nat) (dl NN CC : Nat → Nat → Nat)
    (uu : Nat → BPair)
    (hdl : ∀ i j, i < n → j < n →
      dl i j = if i = j then 1 else 0)
    (hC : ∀ i j, i < n → j < n → CC i j = NN i j + dl i j) :
    (bsum (fun i => uu i * uu i) (List.range n)
      + bsum (fun i => bsum (fun j => BPair.ofNat (NN i j)
          * (uu i * uu j)) (List.range n)) (List.range n)).oneValue
      (bsum (fun i => bsum (fun j => BPair.ofNat (CC i j)
        * (uu i * uu j)) (List.range n)) (List.range n)) := by
  refine BPair.oneValue_trans
    (BPair.add_congr (deltaFold n dl uu hdl) (BPair.oneValue_refl _))
    ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (foldB_add
      (fun i => bsum (fun j => BPair.ofNat (dl i j) * (uu i * uu j))
        (List.range n))
      (fun i => bsum (fun j => BPair.ofNat (NN i j) * (uu i * uu j))
        (List.range n)) (List.range n))) ?_
  refine foldB_congr_members _ _ (List.range n) (fun i hi => ?_)
  have hin : i < n := ground.ltOfMem hi
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (foldB_add (fun j => BPair.ofNat (dl i j) * (uu i * uu j))
      (fun j => BPair.ofNat (NN i j) * (uu i * uu j))
      (List.range n))) ?_
  refine foldB_congr_members _ _ (List.range n) (fun j hj => ?_)
  have hjn : j < n := ground.ltOfMem hj
  show (BPair.ofNat (dl i j) * (uu i * uu j)
      + BPair.ofNat (NN i j) * (uu i * uu j)).oneValue
    (BPair.ofNat (CC i j) * (uu i * uu j))
  rw [← BPair.right_distrib]
  refine BPair.mul_congr_left ?_
  rw [hC i j hin hjn]
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.ofNat_add (NN i j) (dl i j)) ?_)
  exact BPair.oneValue_of_eq (BPair.add_comm _ _)

/-- The composition's Gram collection: a double index fold whose
count is the further fold of a family's products collects to the
squares of that family's weighted folds — the tex's
`Σ_c (Σ_i N^c_{f x_i} u_i)²` at the cleared exchange. -/
private theorem gramFold (n m : Nat) (A : Nat → Nat → Nat)
    (uu : Nat → BPair) :
    (bsum (fun i => bsum (fun j =>
        BPair.ofNat (ground.famFold Nat.add 0
            (fun c => A c i * A c j) (List.range m))
          * (uu i * uu j)) (List.range n)) (List.range n)).oneValue
      (bsum (fun c =>
        bsum (fun i => BPair.ofNat (A c i) * uu i) (List.range n)
          * bsum (fun i => BPair.ofNat (A c i) * uu i)
            (List.range n)) (List.range m)) := by
  have hsplit : (bsum (fun i => bsum (fun j =>
        BPair.ofNat (ground.famFold Nat.add 0
            (fun c => A c i * A c j) (List.range m))
          * (uu i * uu j)) (List.range n)) (List.range n)).oneValue
      (bsum (fun i => bsum (fun j => bsum (fun c =>
        BPair.ofNat (A c i * A c j) * (uu i * uu j))
        (List.range m)) (List.range n)) (List.range n)) :=
    foldB_congr_members _ _ (List.range n) (fun i _ =>
      foldB_congr_members _ _ (List.range n) (fun j _ =>
        BPair.oneValue_symm (bsum_scalar (fun c => A c i * A c j)
          (uu i * uu j) (List.range m))))
  have hswapIn : (bsum (fun i => bsum (fun j => bsum (fun c =>
        BPair.ofNat (A c i * A c j) * (uu i * uu j))
        (List.range m)) (List.range n)) (List.range n)).oneValue
      (bsum (fun i => bsum (fun c => bsum (fun j =>
        BPair.ofNat (A c i * A c j) * (uu i * uu j))
        (List.range n)) (List.range m)) (List.range n)) :=
    foldB_congr_members _ _ (List.range n) (fun i _ =>
      bsum_swap (fun j c => BPair.ofNat (A c i * A c j)
        * (uu i * uu j)) (List.range n) (List.range m))
  have hswapOut := bsum_swap (fun i c => bsum (fun j =>
      BPair.ofNat (A c i * A c j) * (uu i * uu j)) (List.range n))
    (List.range n) (List.range m)
  have hcollect : (bsum (fun c => bsum (fun i => bsum (fun j =>
        BPair.ofNat (A c i * A c j) * (uu i * uu j))
        (List.range n)) (List.range n)) (List.range m)).oneValue
      (bsum (fun c =>
        bsum (fun i => BPair.ofNat (A c i) * uu i) (List.range n)
          * bsum (fun i => BPair.ofNat (A c i) * uu i)
            (List.range n)) (List.range m)) := by
    refine foldB_congr_members _ _ (List.range m) (fun c _ => ?_)
    refine BPair.oneValue_trans
      (foldB_congr_members _ (fun i => (BPair.ofNat (A c i) * uu i)
        * bsum (fun j => BPair.ofNat (A c j) * uu j)
          (List.range n)) (List.range n) (fun i _ => ?_)) ?_
    · refine BPair.oneValue_trans
        (foldB_congr_members _ (fun j => (BPair.ofNat (A c i) * uu i)
          * (BPair.ofNat (A c j) * uu j)) (List.range n)
          (fun j _ => BPair.oneValue_symm
            (mulPairNat (A c i) (A c j) (uu i) (uu j)))) ?_
      exact foldB_mul_left
        (BPair.ofNat (A c i) * uu i)
        (fun j => BPair.ofNat (A c j) * uu j) (List.range n)
    · refine BPair.oneValue_trans
        (foldB_congr_members _ (fun i =>
          bsum (fun j => BPair.ofNat (A c j) * uu j) (List.range n)
            * (BPair.ofNat (A c i) * uu i)) (List.range n)
          (fun i _ => BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_
      exact foldB_mul_left
        (bsum (fun j => BPair.ofNat (A c j) * uu j) (List.range n))
        (fun i => BPair.ofNat (A c i) * uu i) (List.range n)
  exact BPair.oneValue_trans hsplit (BPair.oneValue_trans hswapIn
    (BPair.oneValue_trans hswapOut hcollect))

/-- The lower side at the abstract families: a form reading the
window's squares against a double fold whose count is the
composition's own sits at or above the sum's unit, the block's
squares the carrier. -/
private theorem lowerAt (n m : Nat) (NN dl A : Nat → Nat → Nat)
    (uu : Nat → BPair) (V : List BPair) (hV : V.length = m)
    (hdl : ∀ i j, i < n → j < n →
      dl i j = if i = j then 1 else 0)
    (hC : ∀ i j, i < n → j < n →
      ground.famFold Nat.add 0 (fun c => A c i * A c j)
          (List.range m)
        = NN i j + dl i j)
    (hVc : ∀ c, c < m → (ground.getAt BPair.unit V c).oneValue
      (bsum (fun i => BPair.ofNat (A c i) * uu i) (List.range n)))
    (X : BPair)
    (hX : X.oneValue (bsum (fun i => uu i * uu i) (List.range n)
      + bsum (fun i => bsum (fun j => BPair.ofNat (NN i j)
        * (uu i * uu j)) (List.range n)) (List.range n))) :
    ¬ (X < BPair.unit) := by
  intro hlt
  refine elim.dotN_self_side V
    (BPair.lt_congr ?_ (BPair.oneValue_refl BPair.unit) hlt)
  refine BPair.oneValue_trans hX (BPair.oneValue_trans
    (sumFold n dl NN (fun i j => ground.famFold Nat.add 0
      (fun c => A c i * A c j) (List.range m)) uu hdl hC) ?_)
  refine BPair.oneValue_trans (gramFold n m A uu) ?_
  exact BPair.oneValue_trans
    (foldB_congr_members _ _ (List.range m) (fun c hc =>
      BPair.mul_congr (BPair.oneValue_symm (hVc c (ground.ltOfMem hc)))
        (BPair.oneValue_symm (hVc c (ground.ltOfMem hc)))))
    (BPair.oneValue_symm (selfFold V m hV))

/-! The fundamental's window block: the composition read's
intermediate labels the rows, the window the columns, entry
`(c, x) = N^c_{f x}`. -/

/-- The fundamental's window block at a composition's intermediate
list. -/
private def crossMat {L : Type} (F : fusion.Data L) (fl : L)
    (ls cs : List L) : Mat :=
  cs.map (fun c => (F.unit :: ls).map (fun x =>
    BPair.ofNat (F.count fl x c)))

/-- The block against the window's vector: at a stated intermediate
key the entry is the fundamental's weighted fold over the
window. -/
private theorem crossVec {L : Type} (F : fusion.Data L) (fl : L)
    (ls cs : List L) (u : List BPair)
    (hu : u.length = ls.length + 1) (c : Nat) (hc : c < cs.length) :
    (ground.getAt BPair.unit
        (elim.matVec (crossMat F fl ls cs) u) c).oneValue
      (bsum (fun i => BPair.ofNat (F.count fl
          (ground.getAt F.unit (F.unit :: ls) i)
          (ground.getAt F.unit cs c)) * ground.getAt BPair.unit u i)
        (List.range (ls.length + 1))) := by
  have hrow : ∀ y : L, ((F.unit :: ls).map (fun x =>
      BPair.ofNat (F.count fl x y))).length = ls.length + 1 :=
    fun y => ground.length_map _ (F.unit :: ls)
  have hmap : elim.matVec (crossMat F fl ls cs) u
      = cs.map (fun y => elim.dotN ((F.unit :: ls).map
        (fun x => BPair.ofNat (F.count fl x y))) u) :=
    ground.map_map _ _ cs
  rw [hmap, ground.getAt_map F.unit BPair.unit _ cs c hc]
  refine BPair.oneValue_trans (elim.dotN_read _ u) ?_
  rw [dotP_fold (ls.length + 1) _ u (hrow _) hu]
  refine foldB_congr_members _ _ (List.range (ls.length + 1))
    (fun i hi => ?_)
  rw [ground.getAt_map F.unit BPair.unit
    (fun x => BPair.ofNat
      (F.count fl x (ground.getAt F.unit cs c)))
    (F.unit :: ls) i (ground.ltOfMem hi)]
  exact BPair.oneValue_refl _

/-- The index read's pointwise decode: at a window key pair the
label equality reads the key equality, both ways. -/
private theorem distRead {L : Type} {F : fusion.Data L}
    {ls : List L} (h : fpcap.distinctAt F ls) (i j : Nat)
    (hi : i < ls.length) (hj : j < ls.length) :
    (F.eqL (ground.getAt F.unit ls i)
        (ground.getAt F.unit ls j) = true
      ↔ i = j) := by
  have hb : F.eqL (ground.getAt F.unit ls i)
      (ground.getAt F.unit ls j) = (i == j) :=
    ground.beqEqOf (ground.all_range_read ls.length
      (ground.all_range_read ls.length h i hi) j hj)
  rw [hb]
  exact ⟨fun he => ground.beqEqOf he, fun he => ground.eqBeqOf he⟩

/-- The shifted term's lower side at a loop window: the form with
the gram at or above the sum's unit — `χ_θ + 1` the squared
fundamental's Gram at the composition read, the window's labels
pairwise distinct at the index's equality (`lem:loopcap`). -/
theorem shiftLower {L : Type} (F : fusion.Data L) (fl : L)
    (ls cs : List L)
    (hcomp : fpcap.compRead F fl (F.unit :: ls) cs)
    (hdist : fpcap.distinctAt F (F.unit :: ls))
    (u : List ground.BPair) (hu : u.length = ls.length + 1) :
    ¬ (elim.dotN u u
          + inertia.quadForm (pairpencil.loopMag F ls) u
        < ground.BPair.unit) := by
  have hV : (elim.matVec (crossMat F fl ls cs) u).length
      = cs.length :=
    (ground.length_map _ (crossMat F fl ls cs)).trans
      (ground.length_map _ cs)
  have hq : (inertia.quadForm (pairpencil.loopMag F ls)
        u).oneValue
      (bsum (fun i => bsum (fun j =>
        BPair.ofNat (F.count F.theta
            (ground.getAt F.unit (F.unit :: ls) j)
            (ground.getAt F.unit (F.unit :: ls) i))
          * (ground.getAt BPair.unit u i
            * ground.getAt BPair.unit u j))
        (List.range (ls.length + 1)))
        (List.range (ls.length + 1))) := by
    exact fpcap.quadFold F F.theta (F.unit :: ls) u hu
  refine lowerAt (ls.length + 1) cs.length
    (fun i j => F.count F.theta
      (ground.getAt F.unit (F.unit :: ls) j)
      (ground.getAt F.unit (F.unit :: ls) i))
    (fun i j => if F.eqL (ground.getAt F.unit (F.unit :: ls) i)
      (ground.getAt F.unit (F.unit :: ls) j) then 1 else 0)
    (fun c i => F.count fl (ground.getAt F.unit (F.unit :: ls) i)
      (ground.getAt F.unit cs c))
    (fun i => ground.getAt BPair.unit u i)
    (elim.matVec (crossMat F fl ls cs) u) hV ?_ ?_
    (fun c hc => crossVec F fl ls cs u hu c hc) _
    (BPair.add_congr (selfFold u (ls.length + 1) hu) hq)
  · intro i j hi hj
    by_cases hij : i = j
    · rw [if_pos ((distRead hdist i j hi hj).mpr hij), if_pos hij]
    · rw [if_neg (fun he => hij ((distRead hdist i j hi hj).mp he)),
        if_neg hij]
  · intro i j hi hj
    have h0 := ground.beqEqOf
      (ground.all_range_read (F.unit :: ls).length
        (ground.all_range_read (F.unit :: ls).length hcomp i hi) j hj)
    rw [foldlSum (fun c =>
        F.count fl (ground.getAt F.unit (F.unit :: ls) i) c
          * F.count fl (ground.getAt F.unit (F.unit :: ls) j) c)
        cs 0,
      Nat.zero_add,
      ← ground.famFold_getAt Nat.add 0 _ F.unit cs cs.length rfl]
      at h0
    exact h0

/-! The loop-cut tier: the joined slot coordinates' pairing at the
squared Cauchy--Schwarz (`con:coeff`), the count cancelled off the
comparison, and the window vector's form read two-sided at the
count against the gram. -/

/-- The loop-cut display (`lem:loopcap`): at joined slot coordinates
whose two self-pairings read the count against the two grams, the
evaluation identity's contractions, the pairing's square sits at or
below the count's square against the grams' product, the squared
Cauchy--Schwarz at the joined list (`con:coeff`). -/
theorem cutSq (ya xb : List BPair) (hlen : ya.length = xb.length)
    (D : Nat) (Gy Gx : BPair)
    (hy : (elim.dotP ya ya).oneValue (BPair.ofNat D * Gy))
    (hx : (elim.dotP xb xb).oneValue (BPair.ofNat D * Gx)) :
    ¬ (BPair.ofNat D * Gy * (BPair.ofNat D * Gx)
        < elim.dotP ya xb * elim.dotP ya xb) :=
  fun hlt => coeff.dotP_sq_le ya xb hlen
    (BPair.lt_congr
      (BPair.mul_congr (BPair.oneValue_symm hy)
        (BPair.oneValue_symm hx))
      (BPair.oneValue_refl _) hlt)

/-- The order's read back at the image (`lem:loopcap`): at the cut
datum whose pairing reads the image's own gram, the image's gram
sits at or below the squared count against the vector's, the
comparison at the occupied factor with the vacant arm at the
pairing's definiteness. -/
theorem cutCap (ya xb : List BPair) (hlen : ya.length = xb.length)
    (D : Nat) (N Gx : BPair)
    (hP : (elim.dotP ya xb).oneValue N)
    (hy : (elim.dotP ya ya).oneValue (BPair.ofNat D * N))
    (hx : (elim.dotP xb xb).oneValue (BPair.ofNat D * Gx)) :
    ¬ (BPair.ofNat (D * D) * Gx < N) := by
  match D with
  | 0 =>
    have hself : (elim.dotP ya ya).oneValue BPair.unit :=
      BPair.oneValue_trans hy (BPair.unit_mul N)
    have hcross : (elim.dotP ya xb).oneValue BPair.unit :=
      elim.dotP_null_or ya xb hlen (fun i _ => Or.inl
        (poly.getAt_unitTail (elim.dotP_self_null ya hself) i))
    have hNu : N.oneValue BPair.unit :=
      BPair.oneValue_trans (BPair.oneValue_symm hP) hcross
    intro hlt
    exact leB_not_lt (leB_refl BPair.unit)
      (BPair.lt_congr (BPair.unit_mul Gx) hNu hlt)
  | D' + 1 =>
    have hD1 : BPair.unit < BPair.ofNat (D' + 1) := unitLtOfNat D'
    have hsq := cutSq ya xb hlen (D' + 1) N Gx hy hx
    have hNN : N * N
        ≤ BPair.ofNat ((D' + 1) * (D' + 1)) * Gx * N := by
      refine leB_congr (BPair.mul_congr hP hP) ?_
        (leB_of_not_lt hsq)
      rw [BPair.mul_mul_mul_comm (BPair.ofNat (D' + 1)) N
          (BPair.ofNat (D' + 1)) Gx,
        BPair.mul_comm N Gx, ← BPair.mul_assoc]
      exact BPair.mul_congr_left (BPair.mul_congr_left
        (BPair.oneValue_symm (BPair.ofNat_mul (D' + 1) (D' + 1))))
    have hN1 : BPair.unit ≤ N :=
      unitLeUnscale hD1 (leB_congr_right hy
        (unitLeOfSide (elim.dotP_self_side ya)))
    if hc : BPair.unit < N then
      exact leB_not_lt (leB_unscale hc hNN)
    else
      have hNu : BPair.unit.oneValue N :=
        leB_antisymm hN1 (leB_of_not_lt hc)
      have hGx1 : BPair.unit ≤ Gx :=
        unitLeUnscale hD1 (leB_congr_right hx
          (unitLeOfSide (elim.dotP_self_side xb)))
      exact leB_not_lt (leB_congr_left hNu
        (leB_unit_mul ((D' + 1) * (D' + 1)) hGx1))

/-- The two-sided form read (`lem:loopcap`): one further squared
Cauchy--Schwarz at a window vector against its image, the squared
comparison reading back at the trichotomy, the form and its
memberwise swap each at or below the count against the gram. -/
theorem cutForm (xc mxc : List BPair) (hlen : xc.length = mxc.length)
    (D : Nat) (Gx Q : BPair)
    (hGc : (elim.dotP xc xc).oneValue Gx)
    (hQ : Q.oneValue (elim.dotP xc mxc))
    (hcap : ¬ (BPair.ofNat (D * D) * Gx < elim.dotP mxc mxc)) :
    Q ≤ BPair.ofNat D * Gx ∧ Q.swap ≤ BPair.ofNat D * Gx := by
  have hside : BPair.unit ≤ Gx :=
    leB_congr_right hGc (unitLeOfSide (elim.dotP_self_side xc))
  have hb : BPair.unit ≤ BPair.ofNat D * Gx := leB_unit_mul D hside
  have h1 : ¬ (elim.dotP xc xc * elim.dotP mxc mxc < Q * Q) :=
    fun hlt => coeff.dotP_sq_le xc mxc hlen
      (BPair.lt_congr (BPair.oneValue_refl _)
        (BPair.mul_congr hQ hQ) hlt)
  have h3 : Gx * elim.dotP mxc mxc
      ≤ Gx * (BPair.ofNat (D * D) * Gx) :=
    leB_mulR hside (leB_of_not_lt hcap)
  have h4 : (Gx * (BPair.ofNat (D * D) * Gx)).oneValue
      (BPair.ofNat D * Gx * (BPair.ofNat D * Gx)) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl Gx)
        (BPair.mul_congr_left (BPair.ofNat_mul D D))) ?_
    rw [BPair.mul_left_comm Gx (BPair.ofNat D * BPair.ofNat D) Gx,
      BPair.mul_mul_mul_comm (BPair.ofNat D) Gx (BPair.ofNat D) Gx]
    exact BPair.oneValue_refl _
  have hsq : ¬ (BPair.ofNat D * Gx * (BPair.ofNat D * Gx) < Q * Q) :=
    leB_not_lt (leB_congr_right h4
      (leB_trans (leB_congr_right (BPair.mul_congr_left hGc)
        (leB_of_not_lt h1)) h3))
  refine ⟨leB_of_sq_le hb hsq, leB_of_sq_le hb ?_⟩
  rw [BPair.swap_sq]
  exact hsq

end loopcap
