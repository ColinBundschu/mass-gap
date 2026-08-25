import MassGap.Steinberg
import MassGap.Casimir
import MassGap.Strings
import MassGap.Lowerspan
/-!
`cor:weyldim` — the dimension is the Weyl product:
`d_λ · Π_{j<k} g_{jk} = Π_{j<k} g^λ_{jk}`, the unit set's member
gaps against the shape's, read off the sorted displays.  The
computation `dimOf` is the displays' gap products' exact cofactor,
and the corollary's display is the stated decidable read `read`,
the cross-multiplied naming identity — per instance it is the
cofactor's whole verification, the division's exactness
certificate.

The A-series general half stands at the substituted carrier: the
graded sums land as one-variable signed folds (`altT`) with the
span's content sum (`chTL`) beside them, the transport
(`chT_transport`) reads `thm:weylchar`'s identity per degree over
the occupied-key cover, the one-variable assembly (`altT_eq`, the
tex's subset fold at the taken counts, the exchange at tied counts
and the assignments at distinct ones) collects each graded sum to
its full monomial against the pair product, the unit-gap powers
withdraw at the monic cancellation, and the evaluation at the
natural one closes the count identity: `spanProd` (the span's
count against the unit display's gap product is the shape's own),
`dimOf_spanLen` (the computing read is the span's count), and
`readAll` (the display at every shape), the check module's pins
the instances with the coherence face beside them.  The dimension
is one value at the label's class: the full-column key's occupancy
moves every display entry together and the gap product reads the
gaps alone (`dimOf_snoc`).  Beneath the
naming sits the display's run tier: the gap product peels its head
against the head's own gap fold (`gapProd_cons`), a descending run
(`descRun`) carries that fold's factorial at its floor
(`gapHead_descRun`), a run over a stated tail reads the run's
product against the tail's with one tail fold per run entry
(`gapProd_descRun_app`), the unit display is the run at the unit
floor (`unitDisp_descRun`), and the display is the rows against it
entry by entry (`weylchar.display_zip`).

The member half stands at the abstract data beneath it
(`memberRead`): at `con:sertables`' orbit data for `ρ` and for the
shifted key, `thm:memberchar`'s multiplicity family, and the
crossed count read exchanging the two displays, the member count
against the positive list's `ρ`-gaps is the list's gaps at `λ+ρ`.
Its tier — the gap product at a weight, the two principal folds and
their degree data, the assembly instance, the convolution transfer,
the exchange and the gap comparison — is enumerated at its own
section below.
-/

namespace weyldim
open ground places

/-- The head's gap fold at a display tail, one factor per
member. -/
def gapHead (x : Nat) (t : List Nat) : Nat :=
  ground.prodOver (fun y => x - y) t

/-- The pair-gap product over a sorted display, each pair's gap one
factor. -/
def gapProd : List Nat → Nat
  | [] => 1
  | x :: t => gapHead x t * gapProd t

/-- The dimension read: the shape's display gap product against the
unit set's, the exact cofactor. -/
def dimOf (s : Shape) : Nat :=
  gapProd (display s)
    / gapProd (display (List.replicate s.length 0))

/-- `cor:weyldim`'s display as the cross-multiplied naming read,
the cofactor's whole verification. -/
def read (s : Shape) : Prop :=
  dimOf s * gapProd (display (List.replicate s.length 0))
    = gapProd (display s)

instance (s : Shape) : Decidable (read s) :=
  inferInstanceAs (Decidable (_ = _))

/-! The A-series telescope tier (`cor:weyldim`'s first paragraph):
the substitution `x_j := t^{u_j}` at the unit display maps the
graded sums to one-variable polynomials at the display dots, the
one-variable assembly reads each as a full monomial against the
pair products (`thm:assembly`'s subset fold at the powers' gaps,
the taken-count keys, the exchange at repeated counts, the
distinct-count families the assignments' own), the shared monic
words withdraw, and the evaluation at the natural one lands the
dimension display at the span's count. -/

/-- The substituted graded sum at a display: the signed fold over
the place permutations at the display's dots against the unit
display. -/
private def altT (b : List Nat) : poly.Poly :=
  ground.famFold poly.add []
    (fun p => poly.smono (parity p)
      (dotNat (unitDisp b.length) (places.expo b p)))
    (places.perms b.length)

/-- The substituted content sum over a stated content list. -/
private def chTL (d : Nat) (L : List (List Nat)) : poly.Poly :=
  ground.famFold poly.add []
    (fun nu => poly.mono (dotNat (unitDisp d) nu)) L

/-- The substituted pair product at a display, one factor per
place pair. -/
private def vprod (b : List Nat) : poly.Poly :=
  ground.famFold poly.mul poly.one
    (fun q => poly.add (poly.mono (ground.getAt 0 b q.1))
      (poly.neg (poly.mono (ground.getAt 0 b q.2))))
    (pairsOf b.length)

/-- The unit display descends strictly. -/
private theorem unitDisp_desc (d : Nat) :
    ∀ i, i + 1 < (unitDisp d).length →
      ground.getAt 0 (unitDisp d) (i + 1)
        < ground.getAt 0 (unitDisp d) i := by
  intro i hi
  have hi' : i + 1 < (display (List.replicate d 0)).length := hi
  rw [places.length_display] at hi'
  exact places.display_desc (List.replicate d 0) i hi'

/-- The pair's display gap at the two places' reads. -/
private def gapP (b : List Nat) (q : Nat × Nat) : Nat :=
  ground.getAt 0 b q.1 - ground.getAt 0 b q.2

/-- The second reads' fold over the place pairs. -/
private def sndSum (b : List Nat) : Nat :=
  ground.famFold Nat.add 0 (fun q => ground.getAt 0 b q.2)
    (pairsOf b.length)

/-- The gap pairs' product over the place pairs. -/
private def tfold (b : List Nat) : poly.Poly :=
  ground.famFold poly.mul poly.one
    (fun q => poly.tpair (gapP b q)) (pairsOf b.length)

/-- The product fold reads member-congruent factors at one
value. -/
private theorem mulFold_congr_members {α : Type} [DecidableEq α]
    (l : List α) {f g : α → poly.Poly}
    (h : ∀ x, 0 < ground.countOf x l → poly.oneValue (f x) (g x)) :
    poly.oneValue (ground.famFold poly.mul poly.one f l)
      (ground.famFold poly.mul poly.one g l) :=
  ground.famFold_congr_members_ov poly.oneValue poly.mul poly.one
    poly.oneValue_refl
    (fun hx hy => poly.oneValue_trans
      (poly.mul_congr_left hx _) (poly.mul_congr _ hy))
    f g l h

/-- The pair product splits at the lower powers: the second reads'
monomial collects against the gap pairs' product. -/
private theorem vprod_split {b : List Nat}
    (hd : ∀ i, i + 1 < b.length →
      ground.getAt 0 b (i + 1) < ground.getAt 0 b i) :
    poly.oneValue (vprod b)
      (poly.mul (poly.mono (sndSum b)) (tfold b)) := by
  refine poly.oneValue_trans
    (mulFold_congr_members (pairsOf b.length)
      (f := fun q => poly.add (poly.mono (ground.getAt 0 b q.1))
        (poly.neg (poly.mono (ground.getAt 0 b q.2))))
      (g := fun q => poly.mul (poly.mono (ground.getAt 0 b q.2))
        (poly.tpair (gapP b q)))
      (fun q hq => ?_)) ?_
  · match pairs_mem b.length q hq with
    | ⟨h1, h2⟩ =>
      exact poly.factor_split
        (ground.natAddSubCancel
          (Nat.le_of_lt (desc_lt hd q.2 q.1 h1 h2)))
  · exact poly.mulFold_collect
      (fun q => ground.getAt 0 b q.2)
      (fun q => poly.tpair (gapP b q)) (pairsOf b.length)

/-- A pair's taken place at an occupancy family: the second at a
member, the first off it. -/
private def takenAt (S : List (Nat × Nat)) (q : Nat × Nat) : Nat :=
  if 0 < ground.countOf q S then q.2 else q.1

/-- The taken counts: per place the count of its pairs taken
there. -/
private def takeAt (d : Nat) (S : List (Nat × Nat)) (v : Nat) :
    Nat :=
  ground.countOf v ((pairsOf d).map (takenAt S))

/-- The family's key: the display's fold against the taken counts'
successors. -/
private def keyAt (b : List Nat) (S : List (Nat × Nat)) : Nat :=
  ground.famFold Nat.add 0
    (fun v => (1 + takeAt b.length S v) * ground.getAt 0 b v)
    (List.range b.length)

/-- The expanded term's degree collects at the taken counts: the
display's sum with the second reads and the off-family gaps joins
to the family's key. -/
private theorem key_take {b : List Nat}
    (hd : ∀ i, i + 1 < b.length →
      ground.getAt 0 b (i + 1) < ground.getAt 0 b i)
    (S : List (Nat × Nat)) :
    ground.sumNat b + sndSum b
      + ground.famFold Nat.add 0
        (fun q => if 0 < ground.countOf q S then 0 else gapP b q)
        (pairsOf b.length)
    = keyAt b S := by
  rw [Nat.add_assoc]
  have h1 : sndSum b
      + ground.famFold Nat.add 0
        (fun q => if 0 < ground.countOf q S then 0 else gapP b q)
        (pairsOf b.length)
      = ground.famFold Nat.add 0
        (fun q => ground.getAt 0 b (takenAt S q))
        (pairsOf b.length) := by
    show ground.famFold Nat.add 0
        (fun q => ground.getAt 0 b q.2) (pairsOf b.length)
      + ground.famFold Nat.add 0
        (fun q => if 0 < ground.countOf q S then 0 else gapP b q)
        (pairsOf b.length)
      = _
    rw [← ground.famFold_add_split
      (fun q => ground.getAt 0 b q.2)
      (fun q => if 0 < ground.countOf q S then 0 else gapP b q)
      (pairsOf b.length)]
    refine ground.famFold_congr_members Nat.add 0 _ _
      (pairsOf b.length) (fun q hq => ?_)
    show ground.getAt 0 b q.2
        + (if 0 < ground.countOf q S then 0 else gapP b q)
      = ground.getAt 0 b
        (if 0 < ground.countOf q S then q.2 else q.1)
    by_cases hs : 0 < ground.countOf q S
    · rw [if_pos hs, if_pos hs]
      rfl
    · rw [if_neg hs, if_neg hs]
      exact ground.natAddSubCancel (Nat.le_of_lt
        (desc_lt hd q.2 q.1 (pairs_mem b.length q hq).1
          (pairs_mem b.length q hq).2))
  rw [h1]
  have h2 : ground.famFold Nat.add 0
      (fun q => ground.getAt 0 b (takenAt S q)) (pairsOf b.length)
      = ground.famFold Nat.add 0
        (fun v => takeAt b.length S v * ground.getAt 0 b v)
        (List.range b.length) := by
    rw [← ground.famFold_map Nat.add 0 (ground.getAt 0 b)
      (takenAt S) (pairsOf b.length)]
    exact ground.famFold_partition (ground.getAt 0 b)
      ((pairsOf b.length).map (takenAt S)) (List.range b.length)
      (ground.distinctList_range b.length)
      (fun x hx =>
        match ground.mem_map_of (takenAt S) (pairsOf b.length)
            x hx with
        | ⟨q, hq, hqe⟩ => by
          have hm := pairs_mem b.length q
            (ground.countOf_pos_of_mem hq)
          rw [← hqe]
          show (if 0 < ground.countOf q S then q.2 else q.1)
            ∈ List.range b.length
          by_cases hs : 0 < ground.countOf q S
          · rw [if_pos hs]
            exact ground.memRange hm.2
          · rw [if_neg hs]
            exact ground.memRange (Nat.lt_trans hm.1 hm.2))
  rw [h2, ← ground.sumIndex b, ← ground.famFold_add_split
    (fun k => ground.getAt 0 b k)
    (fun v => takeAt b.length S v * ground.getAt 0 b v)
    (List.range b.length)]
  exact ground.famFold_congr_all Nat.add 0 _ _
    (fun v => by
      rw [ground.mulAddR 1 (takeAt b.length S v)
        (ground.getAt 0 b v), Nat.one_mul])
    (List.range b.length)

/-- The exchange's flipped classes: the shared pair with the two
middle families. -/
private def flipC (v w : Nat) (q : Nat × Nat) : Bool :=
  if q = (v, w) then true
  else if q.1 = v ∧ q.2 < w then true
  else if q.2 = w ∧ v < q.1 then true
  else false

/-- The exchange's partner pair: the shared pair fixed, each pair
meeting one place read to its partner at the other. -/
private def sigmaP (v w : Nat) (q : Nat × Nat) : Nat × Nat :=
  if q = (v, w) then q
  else if q.2 = v then (q.1, w)
  else if q.2 = w then (if q.1 < v then (q.1, v) else (v, q.1))
  else if q.1 = v then (if q.2 < w then (q.2, w) else (w, q.2))
  else if q.1 = w then (v, q.2)
  else q

/-- A member pair sits in exactly one of the exchange's eight
classes. -/
private theorem sigma_cases {d v w : Nat}
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    q = (v, w)
    ∨ (q.2 = v ∧ q.1 < v)
    ∨ (q.2 = w ∧ q.1 < v)
    ∨ (q.2 = w ∧ v < q.1 ∧ q.1 < w)
    ∨ (q.1 = v ∧ v < q.2 ∧ q.2 < w)
    ∨ (q.1 = v ∧ w < q.2)
    ∨ (q.1 = w ∧ w < q.2)
    ∨ (¬ q.1 = v ∧ ¬ q.1 = w ∧ ¬ q.2 = v ∧ ¬ q.2 = w) := by
  have h12 := (pairs_mem d q hq).1
  by_cases h2v : q.2 = v
  · exact Or.inr (Or.inl ⟨h2v, h2v ▸ h12⟩)
  by_cases h2w : q.2 = w
  · by_cases h1v : q.1 = v
    · refine Or.inl ?_
      show q = (v, w)
      match q with
      | (a, b) => rw [show a = v from h1v, show b = w from h2w]
    · match Nat.lt_or_ge q.1 v with
      | .inl hlt => exact Or.inr (Or.inr (Or.inl ⟨h2w, hlt⟩))
      | .inr hge =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2w,
          Nat.lt_of_le_of_ne hge (fun e => h1v e.symm),
          h2w ▸ h12⟩)))
  by_cases h1v : q.1 = v
  · match Nat.lt_or_ge q.2 w with
    | .inl hlt =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h1v, h1v ▸ h12, hlt⟩))))
    | .inr hge =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h1v, Nat.lt_of_le_of_ne hge (fun e => h2w e.symm)⟩)))))
  by_cases h1w : q.1 = w
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h1w, h1w ▸ h12⟩))))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨h1v, h1w, h2v, h2w⟩))))))

/-- The shared pair's own reads. -/
private theorem sigmaP_A (v w : Nat) :
    sigmaP v w (v, w) = (v, w) := by
  show (if ((v, w) : Nat × Nat) = (v, w) then (v, w) else _) = _
  rw [if_pos rfl]

private theorem flipC_A (v w : Nat) : flipC v w (v, w) = true := by
  show (if ((v, w) : Nat × Nat) = (v, w) then true else _) = _
  rw [if_pos rfl]

/-- The below-both pair at the lower place: its partner at the
upper, the class unflipped. -/
private theorem sigmaP_B {v w : Nat} (hvw : v < w) {q : Nat × Nat}
    (h2 : q.2 = v) : sigmaP v w q = (q.1, w) := by
  show (if q = (v, w) then q
    else if q.2 = v then (q.1, w) else _) = _
  rw [if_neg (fun he => by
      rw [he] at h2
      have hwv : w = v := h2
      exact Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq hwv))),
    if_pos h2]

private theorem flipC_B {v w : Nat} (hvw : v < w) {q : Nat × Nat}
    (h12 : q.1 < q.2) (h2 : q.2 = v) : flipC v w q = false := by
  show (if q = (v, w) then true
    else if q.1 = v ∧ q.2 < w then true
    else if q.2 = w ∧ v < q.1 then true else false) = false
  rw [if_neg (fun he => by
      rw [he] at h2
      have hwv : w = v := h2
      exact Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq hwv))),
    if_neg (fun hc : q.1 = v ∧ q.2 < w => by
      rw [hc.1, h2] at h12
      exact Nat.lt_irrefl v h12),
    if_neg (fun hc : q.2 = w ∧ v < q.1 => by
      rw [h2] at hc
      exact Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq hc.1.symm)))]

private theorem sigmaP_C {v w : Nat} (hvw : v < w) {q : Nat × Nat}
    (h2 : q.2 = w) (h1 : q.1 < v) :
    sigmaP v w q = (q.1, v) := by
  show (if q = (v, w) then q
    else if q.2 = v then (q.1, w)
    else if q.2 = w then (if q.1 < v then (q.1, v) else (v, q.1))
    else _) = _
  rw [if_neg (fun he => by
      rw [he] at h1
      exact Nat.lt_irrefl v h1),
    if_neg (fun hc : q.2 = v => by
      rw [hc] at h2
      exact Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq h2.symm))),
    if_pos h2, if_pos h1]

private theorem flipC_C {v w : Nat} {q : Nat × Nat}
    (h1 : q.1 < v) : flipC v w q = false := by
  show (if q = (v, w) then true
    else if q.1 = v ∧ q.2 < w then true
    else if q.2 = w ∧ v < q.1 then true else false) = false
  rw [if_neg (fun he => by
      rw [he] at h1
      exact Nat.lt_irrefl v h1),
    if_neg (fun hc : q.1 = v ∧ q.2 < w => by
      rw [hc.1] at h1
      exact Nat.lt_irrefl v h1),
    if_neg (fun hc : q.2 = w ∧ v < q.1 =>
      Nat.lt_irrefl v (Nat.lt_trans hc.2 h1))]

private theorem sigmaP_E {v w : Nat} (hvw : v < w) {q : Nat × Nat}
    (h2 : q.2 = w) (h1 : v < q.1) :
    sigmaP v w q = (v, q.1) := by
  show (if q = (v, w) then q
    else if q.2 = v then (q.1, w)
    else if q.2 = w then (if q.1 < v then (q.1, v) else (v, q.1))
    else _) = _
  rw [if_neg (fun he => by
      rw [he] at h1
      exact Nat.lt_irrefl v h1),
    if_neg (fun hc : q.2 = v => by
      rw [hc] at h2
      exact Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq h2.symm))),
    if_pos h2,
    if_neg (fun hc : q.1 < v => Nat.lt_irrefl v
      (Nat.lt_trans h1 hc))]

private theorem flipC_E {v w : Nat} {q : Nat × Nat}
    (h2 : q.2 = w) (h1 : v < q.1) : flipC v w q = true := by
  show (if q = (v, w) then true
    else if q.1 = v ∧ q.2 < w then true
    else if q.2 = w ∧ v < q.1 then true else false) = true
  rw [if_neg (fun he => by
      rw [he] at h1
      exact Nat.lt_irrefl v h1),
    if_neg (fun hc : q.1 = v ∧ q.2 < w => by
      rw [hc.1] at h1
      exact Nat.lt_irrefl v h1),
    if_pos ⟨h2, h1⟩]

private theorem sigmaP_F {v w : Nat} {q : Nat × Nat}
    (h12 : q.1 < q.2) (h1 : q.1 = v) (h2 : q.2 < w) :
    sigmaP v w q = (q.2, w) := by
  show (if q = (v, w) then q
    else if q.2 = v then (q.1, w)
    else if q.2 = w then _
    else if q.1 = v then (if q.2 < w then (q.2, w) else (w, q.2))
    else _) = _
  rw [if_neg (fun he => by
      rw [he] at h2
      exact Nat.lt_irrefl w h2),
    if_neg (fun hc : q.2 = v => by
      rw [hc, ← h1] at h12
      exact Nat.lt_irrefl q.1 h12),
    if_neg (fun hc : q.2 = w => by
      rw [hc] at h2
      exact Nat.lt_irrefl w h2),
    if_pos h1, if_pos h2]

private theorem flipC_F {v w : Nat} {q : Nat × Nat}
    (h1 : q.1 = v) (h2 : q.2 < w) : flipC v w q = true := by
  show (if q = (v, w) then true
    else if q.1 = v ∧ q.2 < w then true
    else if q.2 = w ∧ v < q.1 then true else false) = true
  rw [if_neg (fun he => by
      rw [he] at h2
      exact Nat.lt_irrefl w h2),
    if_pos ⟨h1, h2⟩]

private theorem sigmaP_G {v w : Nat} (hvw : v < w) {q : Nat × Nat}
    (h1 : q.1 = v) (h2 : w < q.2) :
    sigmaP v w q = (w, q.2) := by
  show (if q = (v, w) then q
    else if q.2 = v then (q.1, w)
    else if q.2 = w then _
    else if q.1 = v then (if q.2 < w then (q.2, w) else (w, q.2))
    else _) = _
  rw [if_neg (fun he => by
      rw [he] at h2
      exact Nat.lt_irrefl w h2),
    if_neg (fun hc : q.2 = v => by
      rw [hc] at h2
      exact Nat.lt_irrefl w (Nat.lt_trans h2 hvw)),
    if_neg (fun hc : q.2 = w => by
      rw [hc] at h2
      exact Nat.lt_irrefl w h2),
    if_pos h1,
    if_neg (fun hc : q.2 < w => Nat.lt_irrefl w
      (Nat.lt_trans h2 hc))]

private theorem flipC_G {v w : Nat} {q : Nat × Nat}
    (h2 : w < q.2) : flipC v w q = false := by
  show (if q = (v, w) then true
    else if q.1 = v ∧ q.2 < w then true
    else if q.2 = w ∧ v < q.1 then true else false) = false
  rw [if_neg (fun he => by
      rw [he] at h2
      exact Nat.lt_irrefl w h2),
    if_neg (fun hc : q.1 = v ∧ q.2 < w => Nat.lt_irrefl w
      (Nat.lt_trans h2 hc.2)),
    if_neg (fun hc : q.2 = w ∧ v < q.1 => by
      rw [hc.1] at h2
      exact Nat.lt_irrefl w h2)]

private theorem sigmaP_H {v w : Nat} (hvw : v < w) {q : Nat × Nat}
    (h1 : q.1 = w) (h2 : w < q.2) :
    sigmaP v w q = (v, q.2) := by
  show (if q = (v, w) then q
    else if q.2 = v then (q.1, w)
    else if q.2 = w then _
    else if q.1 = v then _
    else if q.1 = w then (v, q.2)
    else q) = _
  rw [if_neg (fun he => by
      rw [he] at h1
      have hvw2 : v = w := h1
      exact Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq hvw2.symm))),
    if_neg (fun hc : q.2 = v => by
      rw [hc] at h2
      exact Nat.lt_irrefl w (Nat.lt_trans h2 hvw)),
    if_neg (fun hc : q.2 = w => by
      rw [hc] at h2
      exact Nat.lt_irrefl w h2),
    if_neg (fun hc : q.1 = v => by
      rw [hc] at h1
      exact Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq h1.symm))),
    if_pos h1]

private theorem flipC_H {v w : Nat} (hvw : v < w) {q : Nat × Nat}
    (h1 : q.1 = w) (h2 : w < q.2) : flipC v w q = false := by
  show (if q = (v, w) then true
    else if q.1 = v ∧ q.2 < w then true
    else if q.2 = w ∧ v < q.1 then true else false) = false
  rw [if_neg (fun he => by
      rw [he] at h1
      have hvw2 : v = w := h1
      exact Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq hvw2.symm))),
    if_neg (fun hc : q.1 = v ∧ q.2 < w => by
      rw [hc.1] at h1
      exact Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq h1.symm))),
    if_neg (fun hc : q.2 = w ∧ v < q.1 => by
      rw [hc.1] at h2
      exact Nat.lt_irrefl w h2)]

private theorem sigmaP_I {v w : Nat} {q : Nat × Nat}
    (h1v : ¬ q.1 = v) (h1w : ¬ q.1 = w)
    (h2v : ¬ q.2 = v) (h2w : ¬ q.2 = w) :
    sigmaP v w q = q := by
  show (if q = (v, w) then q
    else if q.2 = v then (q.1, w)
    else if q.2 = w then _
    else if q.1 = v then _
    else if q.1 = w then (v, q.2)
    else q) = _
  rw [if_neg (fun he => h1v (by rw [he])),
    if_neg h2v, if_neg h2w, if_neg h1v, if_neg h1w]

private theorem flipC_I {v w : Nat} {q : Nat × Nat}
    (h1v : ¬ q.1 = v) (h2w : ¬ q.2 = w) : flipC v w q = false := by
  show (if q = (v, w) then true
    else if q.1 = v ∧ q.2 < w then true
    else if q.2 = w ∧ v < q.1 then true else false) = false
  rw [if_neg (fun he => h1v (by rw [he])),
    if_neg (fun hc : q.1 = v ∧ q.2 < w => h1v hc.1),
    if_neg (fun hc : q.2 = w ∧ v < q.1 => h2w hc.1)]

/-- The partner pair joins the family. -/
private theorem sigmaP_mem {d v w : Nat} (hvw : v < w) (hwd : w < d)
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    0 < ground.countOf (sigmaP v w q) (pairsOf d) := by
  have hvd : v < d := Nat.lt_trans hvw hwd
  have h12 := (pairs_mem d q hq).1
  have h2d := (pairs_mem d q hq).2
  match sigma_cases (v := v) (w := w) hq with
  | .inl hA =>
    rw [hA, sigmaP_A]
    rw [hA] at hq
    exact hq
  | .inr (.inl ⟨h2, h1⟩) =>
    rw [sigmaP_B hvw h2]
    exact pairs_complete d (Nat.lt_trans h1 hvw) hwd
  | .inr (.inr (.inl ⟨h2, h1⟩)) =>
    rw [sigmaP_C hvw h2 h1]
    exact pairs_complete d h1 hvd
  | .inr (.inr (.inr (.inl ⟨h2, h1, h1w⟩))) =>
    rw [sigmaP_E hvw h2 h1]
    exact pairs_complete d h1 (Nat.lt_trans h1w hwd)
  | .inr (.inr (.inr (.inr (.inl ⟨h1, _hv2, h2w⟩)))) =>
    rw [sigmaP_F h12 h1 h2w]
    exact pairs_complete d h2w hwd
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩))))) =>
    rw [sigmaP_G hvw h1 hw2]
    exact pairs_complete d hw2 h2d
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩)))))) =>
    rw [sigmaP_H hvw h1 hw2]
    exact pairs_complete d (Nat.lt_trans hvw hw2) h2d
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨h1v, h1w, h2v, h2w⟩)))))) =>
    rw [sigmaP_I h1v h1w h2v h2w]
    exact hq

/-- The partner map is its own inverse at the family. -/
private theorem sigmaP_invol {d v w : Nat} (hvw : v < w)
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    sigmaP v w (sigmaP v w q) = q := by
  have h12 := (pairs_mem d q hq).1
  match sigma_cases (v := v) (w := w) hq with
  | .inl hA => rw [hA, sigmaP_A, sigmaP_A]
  | .inr (.inl ⟨h2, h1⟩) =>
    rw [sigmaP_B hvw h2, sigmaP_C (q := (q.1, w)) hvw rfl h1, ← h2]
  | .inr (.inr (.inl ⟨h2, h1⟩)) =>
    rw [sigmaP_C hvw h2 h1, sigmaP_B (q := (q.1, v)) hvw rfl, ← h2]
  | .inr (.inr (.inr (.inl ⟨h2, h1, h1w⟩))) =>
    rw [sigmaP_E hvw h2 h1, sigmaP_F (q := (v, q.1)) h1 rfl h1w,
      ← h2]
  | .inr (.inr (.inr (.inr (.inl ⟨h1, hv2, h2w⟩)))) =>
    rw [sigmaP_F h12 h1 h2w, sigmaP_E (q := (q.2, w)) hvw rfl hv2,
      ← h1]
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩))))) =>
    rw [sigmaP_G hvw h1 hw2, sigmaP_H (q := (w, q.2)) hvw rfl hw2,
      ← h1]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩)))))) =>
    rw [sigmaP_H hvw h1 hw2, sigmaP_G (q := (v, q.2)) hvw rfl hw2,
      ← h1]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨h1v, h1w, h2v, h2w⟩)))))) =>
    rw [sigmaP_I h1v h1w h2v h2w, sigmaP_I h1v h1w h2v h2w]

/-- The partner map keeps the flipped classes. -/
private theorem flipC_sigmaP {d v w : Nat} (hvw : v < w)
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    flipC v w (sigmaP v w q) = flipC v w q := by
  have h12 := (pairs_mem d q hq).1
  match sigma_cases (v := v) (w := w) hq with
  | .inl hA => rw [hA, sigmaP_A]
  | .inr (.inl ⟨h2, h1⟩) =>
    rw [sigmaP_B hvw h2, flipC_C (q := (q.1, w)) h1,
      flipC_B hvw h12 h2]
  | .inr (.inr (.inl ⟨h2, h1⟩)) =>
    rw [sigmaP_C hvw h2 h1, flipC_B (q := (q.1, v)) hvw h1 rfl,
      flipC_C h1]
  | .inr (.inr (.inr (.inl ⟨h2, h1, h1w⟩))) =>
    rw [sigmaP_E hvw h2 h1, flipC_F (q := (v, q.1)) rfl h1w,
      flipC_E h2 h1]
  | .inr (.inr (.inr (.inr (.inl ⟨h1, hv2, h2w⟩)))) =>
    rw [sigmaP_F h12 h1 h2w, flipC_E (q := (q.2, w)) rfl hv2,
      flipC_F h1 h2w]
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩))))) =>
    rw [sigmaP_G hvw h1 hw2, flipC_H (q := (w, q.2)) hvw rfl hw2,
      flipC_G hw2]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩)))))) =>
    rw [sigmaP_H hvw h1 hw2, flipC_G (q := (v, q.2)) hw2,
      flipC_H hvw h1 hw2]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨h1v, h1w, h2v, h2w⟩)))))) =>
    rw [sigmaP_I h1v h1w h2v h2w]

/-- The exchange's membership read: the partner's, flipped on the
shared pair and the middle families. -/
private def exMem (S : List (Nat × Nat)) (v w : Nat)
    (q : Nat × Nat) : Bool :=
  xor (flipC v w q) (ground.containsB S (sigmaP v w q))

/-- The exchange: the family at the exchanged membership read. -/
private def exchAt (d : Nat) (S : List (Nat × Nat)) (v w : Nat) :
    List (Nat × Nat) :=
  List.filter (exMem S v w) (pairsOf d)

/-- A member's count in the exchange: one at the membership read. -/
private theorem countOf_exchAt {d : Nat} (S : List (Nat × Nat))
    (v w : Nat) {q : Nat × Nat}
    (hq : 0 < ground.countOf q (pairsOf d)) :
    ground.countOf q (exchAt d S v w)
      = if exMem S v w q = true then 1 else 0 := by
  show ground.countOf q (List.filter (exMem S v w) (pairsOf d))
    = _
  rw [ground.countOf_filter (exMem S v w) q (pairsOf d),
    Nat.le_antisymm (pairs_distinct d q) hq]

/-- The exchange's taken places: the partner's at the letter
swap. -/
private theorem takenAt_exchAt {d v w : Nat} (hvw : v < w)
    (S : List (Nat × Nat)) {q : Nat × Nat}
    (hq : 0 < ground.countOf q (pairsOf d)) :
    takenAt (exchAt d S v w) q
      = swapIx v w (takenAt S (sigmaP v w q)) := by
  have h12 := (pairs_mem d q hq).1
  have hkey : takenAt (exchAt d S v w) q
      = (if exMem S v w q = true then q.2 else q.1) := by
    show (if 0 < ground.countOf q (exchAt d S v w)
      then q.2 else q.1) = _
    rw [countOf_exchAt S v w hq]
    cases hm : exMem S v w q with
    | true =>
      rw [if_pos rfl, if_pos (Nat.succ_pos 0), if_pos rfl]
    | false =>
      rw [if_neg (ground.boolNe rfl), if_neg (Nat.lt_irrefl 0),
        if_neg (ground.boolNe rfl)]
  rw [hkey]
  show (if xor (flipC v w q)
      (ground.containsB S (sigmaP v w q)) = true
    then q.2 else q.1)
    = swapIx v w (if 0 < ground.countOf (sigmaP v w q) S
      then (sigmaP v w q).2 else (sigmaP v w q).1)
  match sigma_cases (v := v) (w := w) hq with
  | .inl hA =>
    rw [hA, sigmaP_A, flipC_A]
    cases hcb : ground.containsB S ((v, w) : Nat × Nat) with
    | true =>
      rw [if_neg (ground.boolNe
          (show (true ^^ true) = false from rfl)),
        if_pos (of_decide_eq_true hcb)]
      show v = swapIx v w w
      rw [swapIx_snd (Nat.ne_of_gt hvw)]
    | false =>
      rw [if_pos (show (true ^^ false) = true from rfl),
        if_neg (fun hp => ground.boolNe hcb (decide_eq_true hp))]
      show w = swapIx v w v
      rw [swapIx_fst]
  | .inr (.inl ⟨h2, h1⟩) =>
    rw [sigmaP_B hvw h2, flipC_B hvw h12 h2]
    cases hcb : ground.containsB S ((q.1, w) : Nat × Nat) with
    | true =>
      rw [if_pos (show (false ^^ true) = true from rfl),
        if_pos (of_decide_eq_true hcb)]
      show q.2 = swapIx v w w
      rw [swapIx_snd (Nat.ne_of_gt hvw), h2]
    | false =>
      rw [if_neg (ground.boolNe
          (show (false ^^ false) = false from rfl)),
        if_neg (fun hp => ground.boolNe hcb (decide_eq_true hp))]
      show q.1 = swapIx v w q.1
      rw [swapIx_off (t := q.1)
        (fun e => Nat.lt_irrefl v
          (Nat.lt_of_le_of_lt (Nat.le_of_eq e.symm) h1))
        (fun e => Nat.lt_irrefl w
          (Nat.lt_of_le_of_lt (Nat.le_of_eq e.symm)
            (Nat.lt_trans h1 hvw)))]
  | .inr (.inr (.inl ⟨h2, h1⟩)) =>
    rw [sigmaP_C hvw h2 h1, flipC_C h1]
    cases hcb : ground.containsB S ((q.1, v) : Nat × Nat) with
    | true =>
      rw [if_pos (show (false ^^ true) = true from rfl),
        if_pos (of_decide_eq_true hcb)]
      show q.2 = swapIx v w v
      rw [swapIx_fst, h2]
    | false =>
      rw [if_neg (ground.boolNe
          (show (false ^^ false) = false from rfl)),
        if_neg (fun hp => ground.boolNe hcb (decide_eq_true hp))]
      show q.1 = swapIx v w q.1
      rw [swapIx_off (t := q.1)
        (fun e => Nat.lt_irrefl v
          (Nat.lt_of_le_of_lt (Nat.le_of_eq e.symm) h1))
        (fun e => Nat.lt_irrefl w
          (Nat.lt_of_le_of_lt (Nat.le_of_eq e.symm)
            (Nat.lt_trans h1 hvw)))]
  | .inr (.inr (.inr (.inl ⟨h2, h1, h1w⟩))) =>
    rw [sigmaP_E hvw h2 h1, flipC_E h2 h1]
    cases hcb : ground.containsB S ((v, q.1) : Nat × Nat) with
    | true =>
      rw [if_neg (ground.boolNe
          (show (true ^^ true) = false from rfl)),
        if_pos (of_decide_eq_true hcb)]
      show q.1 = swapIx v w q.1
      rw [swapIx_off (t := q.1)
        (fun e => Nat.lt_irrefl v
          (Nat.lt_of_lt_of_le h1 (Nat.le_of_eq e)))
        (fun e => Nat.lt_irrefl w
          (Nat.lt_of_le_of_lt (Nat.le_of_eq e.symm) h1w))]
    | false =>
      rw [if_pos (show (true ^^ false) = true from rfl),
        if_neg (fun hp => ground.boolNe hcb (decide_eq_true hp))]
      show q.2 = swapIx v w v
      rw [swapIx_fst, h2]
  | .inr (.inr (.inr (.inr (.inl ⟨h1, hv2, h2w⟩)))) =>
    rw [sigmaP_F h12 h1 h2w, flipC_F h1 h2w]
    cases hcb : ground.containsB S ((q.2, w) : Nat × Nat) with
    | true =>
      rw [if_neg (ground.boolNe
          (show (true ^^ true) = false from rfl)),
        if_pos (of_decide_eq_true hcb)]
      show q.1 = swapIx v w w
      rw [swapIx_snd (Nat.ne_of_gt hvw), h1]
    | false =>
      rw [if_pos (show (true ^^ false) = true from rfl),
        if_neg (fun hp => ground.boolNe hcb (decide_eq_true hp))]
      show q.2 = swapIx v w q.2
      rw [swapIx_off (t := q.2)
        (fun e => Nat.lt_irrefl v
          (Nat.lt_of_lt_of_le hv2 (Nat.le_of_eq e)))
        (fun e => Nat.lt_irrefl w
          (Nat.lt_of_le_of_lt (Nat.le_of_eq e.symm) h2w))]
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩))))) =>
    rw [sigmaP_G hvw h1 hw2, flipC_G hw2]
    cases hcb : ground.containsB S ((w, q.2) : Nat × Nat) with
    | true =>
      rw [if_pos (show (false ^^ true) = true from rfl),
        if_pos (of_decide_eq_true hcb)]
      show q.2 = swapIx v w q.2
      rw [swapIx_off (t := q.2)
        (fun e => Nat.lt_irrefl v
          (Nat.lt_of_lt_of_le (Nat.lt_trans hvw hw2)
            (Nat.le_of_eq e)))
        (fun e => Nat.lt_irrefl w
          (Nat.lt_of_lt_of_le hw2 (Nat.le_of_eq e)))]
    | false =>
      rw [if_neg (ground.boolNe
          (show (false ^^ false) = false from rfl)),
        if_neg (fun hp => ground.boolNe hcb (decide_eq_true hp))]
      show q.1 = swapIx v w w
      rw [swapIx_snd (Nat.ne_of_gt hvw), h1]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩)))))) =>
    rw [sigmaP_H hvw h1 hw2, flipC_H hvw h1 hw2]
    cases hcb : ground.containsB S ((v, q.2) : Nat × Nat) with
    | true =>
      rw [if_pos (show (false ^^ true) = true from rfl),
        if_pos (of_decide_eq_true hcb)]
      show q.2 = swapIx v w q.2
      rw [swapIx_off (t := q.2)
        (fun e => Nat.lt_irrefl v
          (Nat.lt_of_lt_of_le (Nat.lt_trans hvw hw2)
            (Nat.le_of_eq e)))
        (fun e => Nat.lt_irrefl w
          (Nat.lt_of_lt_of_le hw2 (Nat.le_of_eq e)))]
    | false =>
      rw [if_neg (ground.boolNe
          (show (false ^^ false) = false from rfl)),
        if_neg (fun hp => ground.boolNe hcb (decide_eq_true hp))]
      show q.1 = swapIx v w v
      rw [swapIx_fst, h1]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨h1v, h1w, h2v, h2w⟩)))))) =>
    rw [sigmaP_I h1v h1w h2v h2w, flipC_I h1v h2w]
    cases hcb : ground.containsB S q with
    | true =>
      rw [if_pos (show (false ^^ true) = true from rfl),
        if_pos (of_decide_eq_true hcb)]
      show q.2 = swapIx v w q.2
      rw [swapIx_off h2v h2w]
    | false =>
      rw [if_neg (ground.boolNe
          (show (false ^^ false) = false from rfl)),
        if_neg (fun hp => ground.boolNe hcb (decide_eq_true hp))]
      show q.1 = swapIx v w q.1
      rw [swapIx_off h1v h1w]

/-- The exchange's taken counts: the family's own at the letter
swap. -/
private theorem takeAt_exchAt {d v w : Nat} (hvw : v < w)
    (hwd : w < d) (S : List (Nat × Nat)) (u : Nat) :
    takeAt d (exchAt d S v w) u = takeAt d S (swapIx v w u) := by
  show ground.countOf u
      ((pairsOf d).map (takenAt (exchAt d S v w)))
    = ground.countOf (swapIx v w u) ((pairsOf d).map (takenAt S))
  rw [ground.countOf_fold u
      ((pairsOf d).map (takenAt (exchAt d S v w))),
    ground.countOf_fold (swapIx v w u)
      ((pairsOf d).map (takenAt S)),
    ground.famFold_map Nat.add 0
      (fun x => if u = x then (1 : Nat) else 0)
      (takenAt (exchAt d S v w)) (pairsOf d),
    ground.famFold_map Nat.add 0
      (fun x => if swapIx v w u = x then (1 : Nat) else 0)
      (takenAt S) (pairsOf d)]
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun q => if swapIx v w u = takenAt S (sigmaP v w q)
      then (1 : Nat) else 0)
    (pairsOf d) (fun q hq => ?_)) ?_
  · rw [takenAt_exchAt hvw S hq]
    by_cases he : swapIx v w u = takenAt S (sigmaP v w q)
    · rw [if_pos (by rw [← he, swapIx_invol v w u]), if_pos he]
    · rw [if_neg (fun hc : u = swapIx v w
          (takenAt S (sigmaP v w q)) => he (by
        rw [hc, swapIx_invol v w (takenAt S (sigmaP v w q))])),
        if_neg he]
  · exact (ground.famFold_reindex Nat.add 0 Nat.add_comm
      Nat.add_assoc
      (fun q => if swapIx v w u = takenAt S q
        then (1 : Nat) else 0)
      (l := pairsOf d) (g := sigmaP v w) (h := sigmaP v w)
      (fun x _ => pairs_distinct d x)
      (fun x hx => sigmaP_invol hvw hx)
      (fun x hx => sigmaP_invol hvw hx)
      (fun x hx => sigmaP_mem hvw hwd hx)
      (fun x hx => sigmaP_mem hvw hwd hx)).symm

/-- A filter's length is the membership indicator's fold. -/
private theorem filter_length {α : Type} (P : α → Bool) :
    ∀ l : List α, (List.filter P l).length
      = ground.famFold Nat.add 0
        (fun x => if P x = true then (1 : Nat) else 0) l
  | [] => rfl
  | a :: l => by
    cases hp : P a with
    | true =>
      rw [ground.filter_cons_true hp]
      show (List.filter P l).length + 1
        = Nat.add (if P a = true then (1 : Nat) else 0)
          (ground.famFold Nat.add 0
            (fun x => if P x = true then (1 : Nat) else 0) l)
      rw [hp, if_pos rfl, filter_length P l]
      exact Nat.add_comm _ 1
    | false =>
      rw [ground.filter_cons_false hp]
      show (List.filter P l).length
        = Nat.add (if P a = true then (1 : Nat) else 0)
          (ground.famFold Nat.add 0
            (fun x => if P x = true then (1 : Nat) else 0) l)
      rw [hp, if_neg (ground.boolNe rfl), filter_length P l]
      exact (Nat.zero_add _).symm

/-- The exclusive read's count against the joint's: the two
members' own counts. -/
private theorem xorCount (f c : Bool) :
    (if (f ^^ c) = true then (1 : Nat) else 0)
      + 2 * (if (f && c) = true then (1 : Nat) else 0)
    = (if f = true then (1 : Nat) else 0)
      + (if c = true then (1 : Nat) else 0) := by
  cases f with
  | true =>
    cases c with
    | true => rfl
    | false => rfl
  | false =>
    cases c with
    | true => rfl
    | false => rfl

/-- The lower middle family: the exchange's flipped pairs at the
first place. -/
private def midV (v w : Nat) (q : Nat × Nat) : Bool :=
  if ¬ q = (v, w) ∧ q.1 = v ∧ q.2 < w then true else false

/-- The upper middle family: the exchange's flipped pairs at the
second place. -/
private def midW (v w : Nat) (q : Nat × Nat) : Bool :=
  if ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w) ∧ q.2 = w ∧ v < q.1
  then true else false

/-- The flipped classes' indicator splits at the three disjoint
families. -/
private theorem flip_split (v w : Nat) (q : Nat × Nat) :
    (if flipC v w q = true then (1 : Nat) else 0)
    = (if ((v, w) : Nat × Nat) = q then (1 : Nat) else 0)
      + ((if midV v w q = true then (1 : Nat) else 0)
        + (if midW v w q = true then (1 : Nat) else 0)) := by
  show (if (if q = (v, w) then true
      else if q.1 = v ∧ q.2 < w then true
      else if q.2 = w ∧ v < q.1 then true else false) = true
      then (1 : Nat) else 0)
    = (if ((v, w) : Nat × Nat) = q then (1 : Nat) else 0)
      + ((if (if ¬ q = (v, w) ∧ q.1 = v ∧ q.2 < w
          then true else false) = true then (1 : Nat) else 0)
        + (if (if ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
            ∧ q.2 = w ∧ v < q.1
          then true else false) = true then (1 : Nat) else 0))
  by_cases hs : q = (v, w)
  · rw [if_pos hs, if_pos hs.symm,
      if_neg (fun hc : ¬ q = (v, w) ∧ q.1 = v ∧ q.2 < w =>
        hc.1 hs),
      if_neg (fun hc : ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
        ∧ q.2 = w ∧ v < q.1 => hc.1 hs),
      if_pos rfl, if_neg (ground.boolNe rfl)]
  · rw [if_neg hs, if_neg (fun e : ((v, w) : Nat × Nat) = q =>
      hs e.symm)]
    by_cases hb2 : q.1 = v ∧ q.2 < w
    · rw [if_pos hb2,
        if_pos ((⟨hs, hb2.1, hb2.2⟩ :
          ¬ q = (v, w) ∧ q.1 = v ∧ q.2 < w)),
        if_neg (fun hc : ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1 => hc.2.1 hb2),
        if_pos rfl, if_neg (ground.boolNe rfl)]
    · rw [if_neg hb2,
        if_neg (fun hc : ¬ q = (v, w) ∧ q.1 = v ∧ q.2 < w =>
          hb2 hc.2)]
      by_cases hb3 : q.2 = w ∧ v < q.1
      · rw [if_pos hb3,
          if_pos ((⟨hs, hb2, hb3.1, hb3.2⟩ :
            ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
              ∧ q.2 = w ∧ v < q.1)),
          if_pos rfl, if_neg (ground.boolNe rfl)]
      · rw [if_neg hb3,
          if_neg (fun hc : ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
            ∧ q.2 = w ∧ v < q.1 => hb3 ⟨hc.2.2.1, hc.2.2.2⟩),
          if_neg (ground.boolNe rfl)]

/-- The partner map carries the upper middle family onto the
lower. -/
private theorem midV_sigmaP {d v w : Nat} (hvw : v < w)
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    midV v w (sigmaP v w q) = midW v w q := by
  have h12 := (pairs_mem d q hq).1
  match sigma_cases (v := v) (w := w) hq with
  | .inl hA =>
    rw [hA, sigmaP_A]
    show (if ¬ ((v, w) : Nat × Nat) = (v, w) ∧ v = v ∧ w < w
        then true else false)
      = (if ¬ ((v, w) : Nat × Nat) = (v, w)
          ∧ ¬ (v = v ∧ w < w) ∧ w = w ∧ v < v
        then true else false)
    rw [if_neg (fun hc : ¬ ((v, w) : Nat × Nat) = (v, w) ∧ _ =>
        hc.1 rfl),
      if_neg (fun hc : ¬ ((v, w) : Nat × Nat) = (v, w) ∧ _ =>
        hc.1 rfl)]
  | .inr (.inl ⟨h2, h1⟩) =>
    rw [sigmaP_B hvw h2]
    show (if ¬ ((q.1, w) : Nat × Nat) = (v, w) ∧ q.1 = v ∧ w < w
        then true else false)
      = (if ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1
        then true else false)
    rw [if_neg (fun hc : ¬ ((q.1, w) : Nat × Nat) = (v, w)
          ∧ q.1 = v ∧ w < w => Nat.lt_irrefl w hc.2.2),
      if_neg (fun hc : ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1 => Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw
          (Nat.le_of_eq (h2.symm.trans hc.2.2.1).symm)))]
  | .inr (.inr (.inl ⟨h2, h1⟩)) =>
    rw [sigmaP_C hvw h2 h1]
    show (if ¬ ((q.1, v) : Nat × Nat) = (v, w) ∧ q.1 = v ∧ v < w
        then true else false)
      = (if ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1
        then true else false)
    rw [if_neg (fun hc : ¬ ((q.1, v) : Nat × Nat) = (v, w)
          ∧ q.1 = v ∧ v < w => Nat.lt_irrefl v
        (Nat.lt_of_le_of_lt (Nat.le_of_eq hc.2.1.symm) h1)),
      if_neg (fun hc : ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1 => Nat.lt_irrefl v
        (Nat.lt_trans hc.2.2.2 h1))]
  | .inr (.inr (.inr (.inl ⟨h2, h1, h1w⟩))) =>
    rw [sigmaP_E hvw h2 h1]
    show (if ¬ ((v, q.1) : Nat × Nat) = (v, w) ∧ v = v ∧ q.1 < w
        then true else false)
      = (if ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1
        then true else false)
    rw [if_pos ((⟨fun e => Nat.lt_irrefl w
          (Nat.lt_of_le_of_lt (Nat.le_of_eq
            (show w = q.1 from
              (show q.1 = w from congrArg Prod.snd e).symm)) h1w),
        rfl, h1w⟩ :
        ¬ ((v, q.1) : Nat × Nat) = (v, w) ∧ v = v ∧ q.1 < w)),
      if_pos ((⟨fun e => Nat.lt_irrefl v
          (Nat.lt_of_lt_of_le h1 (Nat.le_of_eq
            (show q.1 = v from congrArg Prod.fst e))),
        fun hc => Nat.lt_irrefl v
          (Nat.lt_of_lt_of_le h1 (Nat.le_of_eq hc.1)),
        h2, h1⟩ :
        ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1))]
  | .inr (.inr (.inr (.inr (.inl ⟨h1, hv2, h2w⟩)))) =>
    rw [sigmaP_F h12 h1 h2w]
    show (if ¬ ((q.2, w) : Nat × Nat) = (v, w) ∧ q.2 = v ∧ w < w
        then true else false)
      = (if ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1
        then true else false)
    rw [if_neg (fun hc : ¬ ((q.2, w) : Nat × Nat) = (v, w)
          ∧ q.2 = v ∧ w < w => Nat.lt_irrefl w hc.2.2),
      if_neg (fun hc : ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1 => hc.2.1 ⟨h1, h2w⟩)]
  | .inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩))))) =>
    rw [sigmaP_G hvw h1 hw2]
    show (if ¬ ((w, q.2) : Nat × Nat) = (v, w) ∧ w = v ∧ q.2 < w
        then true else false)
      = (if ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1
        then true else false)
    rw [if_neg (fun hc : ¬ ((w, q.2) : Nat × Nat) = (v, w)
          ∧ w = v ∧ q.2 < w => Nat.lt_irrefl v
        (Nat.lt_of_lt_of_le hvw (Nat.le_of_eq hc.2.1))),
      if_neg (fun hc : ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1 => Nat.lt_irrefl w
        (Nat.lt_of_lt_of_le hw2 (Nat.le_of_eq hc.2.2.1)))]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨h1, hw2⟩)))))) =>
    rw [sigmaP_H hvw h1 hw2]
    show (if ¬ ((v, q.2) : Nat × Nat) = (v, w) ∧ v = v ∧ q.2 < w
        then true else false)
      = (if ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1
        then true else false)
    rw [if_neg (fun hc : ¬ ((v, q.2) : Nat × Nat) = (v, w)
          ∧ v = v ∧ q.2 < w => Nat.lt_irrefl w
        (Nat.lt_trans hw2 hc.2.2)),
      if_neg (fun hc : ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1 => Nat.lt_irrefl w
        (Nat.lt_of_lt_of_le hw2 (Nat.le_of_eq hc.2.2.1)))]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨h1v, h1w, h2v, h2w⟩)))))) =>
    rw [sigmaP_I h1v h1w h2v h2w]
    show (if ¬ q = (v, w) ∧ q.1 = v ∧ q.2 < w
        then true else false)
      = (if ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1
        then true else false)
    rw [if_neg (fun hc : ¬ q = (v, w) ∧ q.1 = v ∧ q.2 < w =>
        h1v hc.2.1),
      if_neg (fun hc : ¬ q = (v, w) ∧ ¬ (q.1 = v ∧ q.2 < w)
          ∧ q.2 = w ∧ v < q.1 => h2w hc.2.2.1)]

/-- A leading successor crosses a sum, the hand-rolled read. -/
private theorem addFlip (a b : Nat) : (1 + a) + b = (b + 1) + a := by
  rw [Nat.add_comm (1 + a) b, ← Nat.add_assoc b 1 a]

/-- The exchange flips the side: the flipped classes count odd. -/
private theorem sideOf_exchAt {d v w : Nat} (hvw : v < w)
    (hwd : w < d) {S : List (Nat × Nat)}
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (pairsOf d))) :
    places.sideOf (exchAt d S v w) = ! places.sideOf S := by
  have hSlen : S.length
      = ground.famFold Nat.add 0
        (fun x => if ground.containsB S x = true then (1 : Nat)
          else 0) (pairsOf d) := by
    have h := congrArg List.length
      (ground.sublists_char (pairsOf d)
        (fun x => pairs_distinct d x) S hS)
    rw [filter_length (ground.containsB S) (pairsOf d)] at h
    exact h
  have hxor : ground.famFold Nat.add 0
        (fun x => if exMem S v w x = true then (1 : Nat) else 0)
        (pairsOf d)
      + 2 * ground.famFold Nat.add 0
        (fun x => if (flipC v w x
            && ground.containsB S (sigmaP v w x)) = true
          then (1 : Nat) else 0) (pairsOf d)
    = ground.famFold Nat.add 0
        (fun x => if flipC v w x = true then (1 : Nat) else 0)
        (pairsOf d)
      + ground.famFold Nat.add 0
        (fun x => if ground.containsB S (sigmaP v w x) = true
          then (1 : Nat) else 0) (pairsOf d) := by
    rw [ground.famFold_mul 2
        (fun x => if (flipC v w x
            && ground.containsB S (sigmaP v w x)) = true
          then (1 : Nat) else 0) (pairsOf d),
      ← ground.famFold_add_split
        (fun x => if exMem S v w x = true then (1 : Nat) else 0)
        (fun x => 2 * (if (flipC v w x
            && ground.containsB S (sigmaP v w x)) = true
          then (1 : Nat) else 0)) (pairsOf d),
      ← ground.famFold_add_split
        (fun x => if flipC v w x = true then (1 : Nat) else 0)
        (fun x => if ground.containsB S (sigmaP v w x) = true
          then (1 : Nat) else 0) (pairsOf d)]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun x => xorCount (flipC v w x)
        (ground.containsB S (sigmaP v w x))) (pairsOf d)
  have hcs : ground.famFold Nat.add 0
      (fun x => if ground.containsB S (sigmaP v w x) = true
        then (1 : Nat) else 0) (pairsOf d)
    = ground.famFold Nat.add 0
      (fun x => if ground.containsB S x = true then (1 : Nat)
        else 0) (pairsOf d) :=
    (ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun x => if ground.containsB S x = true then (1 : Nat)
        else 0)
      (l := pairsOf d) (g := sigmaP v w) (h := sigmaP v w)
      (fun x _ => pairs_distinct d x)
      (fun x hx => sigmaP_invol hvw hx)
      (fun x hx => sigmaP_invol hvw hx)
      (fun x hx => sigmaP_mem hvw hwd hx)
      (fun x hx => sigmaP_mem hvw hwd hx)).symm
  have hmw : ground.famFold Nat.add 0
      (fun x => if midW v w x = true then (1 : Nat) else 0)
      (pairsOf d)
    = ground.famFold Nat.add 0
      (fun x => if midV v w x = true then (1 : Nat) else 0)
      (pairsOf d) := by
    refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
      (fun x => if midV v w (sigmaP v w x) = true then (1 : Nat)
        else 0) (pairsOf d) (fun x hx => ?_)) ?_
    · rw [midV_sigmaP hvw hx]
    · exact (ground.famFold_reindex Nat.add 0 Nat.add_comm
        Nat.add_assoc
        (fun x => if midV v w x = true then (1 : Nat) else 0)
        (l := pairsOf d) (g := sigmaP v w) (h := sigmaP v w)
        (fun x _ => pairs_distinct d x)
        (fun x hx => sigmaP_invol hvw hx)
        (fun x hx => sigmaP_invol hvw hx)
        (fun x hx => sigmaP_mem hvw hwd hx)
        (fun x hx => sigmaP_mem hvw hwd hx)).symm
  have hflip : ground.famFold Nat.add 0
      (fun x => if flipC v w x = true then (1 : Nat) else 0)
      (pairsOf d)
    = 1 + 2 * ground.famFold Nat.add 0
      (fun x => if midV v w x = true then (1 : Nat) else 0)
      (pairsOf d) := by
    rw [ground.famFold_congr_all Nat.add 0 _ _
        (flip_split v w) (pairsOf d),
      ground.famFold_add_split
        (fun x => if ((v, w) : Nat × Nat) = x then (1 : Nat)
          else 0)
        (fun x => (if midV v w x = true then (1 : Nat) else 0)
          + (if midW v w x = true then (1 : Nat) else 0))
        (pairsOf d),
      ground.famFold_add_split
        (fun x => if midV v w x = true then (1 : Nat) else 0)
        (fun x => if midW v w x = true then (1 : Nat) else 0)
        (pairsOf d),
      ← ground.countOf_fold ((v, w) : Nat × Nat) (pairsOf d),
      Nat.le_antisymm (pairs_distinct d ((v, w) : Nat × Nat))
        (pairs_complete d hvw hwd),
      hmw, show (2 : Nat) = 1 + 1 from rfl,
      ground.mulAddR 1 1 (ground.famFold Nat.add 0
        (fun x => if midV v w x = true then (1 : Nat) else 0)
        (pairsOf d)),
      Nat.one_mul]
  have hkey : (exchAt d S v w).length
        + 2 * ground.famFold Nat.add 0
          (fun x => if (flipC v w x
              && ground.containsB S (sigmaP v w x)) = true
            then (1 : Nat) else 0) (pairsOf d)
      = (S.length + 1)
        + 2 * ground.famFold Nat.add 0
          (fun x => if midV v w x = true then (1 : Nat) else 0)
          (pairsOf d) := by
    rw [show (exchAt d S v w).length
        = (List.filter (exMem S v w) (pairsOf d)).length
        from rfl,
      filter_length (exMem S v w) (pairsOf d),
      hxor, hcs, hflip, ← hSlen]
    exact addFlip _ S.length
  show places.parityOf (exchAt d S v w).length
    = ! places.parityOf S.length
  rw [← places.parityOf_add_two_mul (exchAt d S v w).length
      (ground.famFold Nat.add 0
        (fun x => if (flipC v w x
            && ground.containsB S (sigmaP v w x)) = true
          then (1 : Nat) else 0) (pairsOf d)),
    hkey,
    places.parityOf_add_two_mul (S.length + 1)
      (ground.famFold Nat.add 0
        (fun x => if midV v w x = true then (1 : Nat) else 0)
        (pairsOf d))]
  rfl

/-- The exchange's membership test reads the exchanged read. -/
private theorem containsB_exchAt {d : Nat} (S : List (Nat × Nat))
    (v w : Nat) {q : Nat × Nat}
    (hq : 0 < ground.countOf q (pairsOf d)) :
    ground.containsB (exchAt d S v w) q = exMem S v w q := by
  show decide (0 < ground.countOf q (exchAt d S v w)) = _
  rw [countOf_exchAt S v w hq]
  cases hm : exMem S v w q with
  | true =>
    rw [if_pos rfl]
    rfl
  | false =>
    rw [if_neg (ground.boolNe rfl)]
    rfl

/-- The exchanged exchange's membership read is the family's
own. -/
private theorem exMem_exchAt {d v w : Nat} (hvw : v < w)
    (hwd : w < d) (S : List (Nat × Nat)) {q : Nat × Nat}
    (hq : 0 < ground.countOf q (pairsOf d)) :
    exMem (exchAt d S v w) v w q = ground.containsB S q := by
  show xor (flipC v w q)
      (ground.containsB (exchAt d S v w) (sigmaP v w q))
    = ground.containsB S q
  rw [containsB_exchAt S v w (sigmaP_mem hvw hwd hq),
    show exMem S v w (sigmaP v w q)
        = xor (flipC v w (sigmaP v w q))
          (ground.containsB S (sigmaP v w (sigmaP v w q)))
      from rfl,
    flipC_sigmaP hvw hq, sigmaP_invol hvw hq]
  cases flipC v w q with
  | true =>
    cases ground.containsB S q with
    | true => rfl
    | false => rfl
  | false =>
    cases ground.containsB S q with
    | true => rfl
    | false => rfl

/-- The exchange joins the enumeration. -/
private theorem exchAt_memS (d : Nat) (S : List (Nat × Nat))
    (v w : Nat) :
    0 < ground.countOf (exchAt d S v w)
      (ground.sublistsOf (pairsOf d)) :=
  ground.filter_member (exMem S v w) (pairsOf d)

/-- The exchange is its own inverse on the enumeration. -/
private theorem exchAt_invol {d v w : Nat} (hvw : v < w)
    (hwd : w < d) {S : List (Nat × Nat)}
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (pairsOf d))) :
    exchAt d (exchAt d S v w) v w = S := by
  show List.filter (exMem (exchAt d S v w) v w) (pairsOf d)
    = S
  rw [ground.filter_congr_mem (exMem (exchAt d S v w) v w)
    (ground.containsB S) (pairsOf d)
    (fun x hx => exMem_exchAt hvw hwd S hx)]
  exact (ground.sublists_char (pairsOf d)
    (fun x => pairs_distinct d x) S hS).symm

/-- At a tied pair the exchange keeps every taken count. -/
private theorem takeAt_exchAt_tie {d v w : Nat} (hvw : v < w)
    (hwd : w < d) (S : List (Nat × Nat))
    (htie : takeAt d S v = takeAt d S w) (u : Nat) :
    takeAt d (exchAt d S v w) u = takeAt d S u := by
  rw [takeAt_exchAt hvw hwd S u]
  by_cases huv : u = v
  · rw [huv, swapIx_fst, ← htie]
  · by_cases huw : u = w
    · rw [huw, swapIx_snd (Nat.ne_of_gt hvw), htie]
    · rw [swapIx_off huv huw]

/-- At a tied pair the exchange keeps the family's key. -/
private theorem keyAt_exchAt {b : List Nat} {v w : Nat}
    (hvw : v < w) (hwd : w < b.length) (S : List (Nat × Nat))
    (htie : takeAt b.length S v = takeAt b.length S w) :
    keyAt b (exchAt b.length S v w) = keyAt b S :=
  ground.famFold_congr_all Nat.add 0 _ _
    (fun u => by rw [takeAt_exchAt_tie hvw hwd S htie u])
    (List.range b.length)

/-- A filtered member passes the test inside the seed. -/
private theorem filter_pos {α : Type} [DecidableEq α]
    (P : α → Bool) (x : α) (l : List α)
    (h : 0 < ground.countOf x (List.filter P l)) :
    P x = true ∧ 0 < ground.countOf x l := by
  rw [ground.countOf_filter P x l] at h
  cases hp : P x with
  | true =>
    rw [hp, if_pos rfl] at h
    exact ⟨rfl, h⟩
  | false =>
    rw [hp, if_neg (ground.boolNe rfl)] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- The tied test: a pair's two taken counts at one value. -/
private def tiedP (d : Nat) (S : List (Nat × Nat))
    (q : Nat × Nat) : Bool :=
  decide (takeAt d S q.1 = takeAt d S q.2)

/-- The tied pairs, the family's own list. -/
private def tiedList (d : Nat) (S : List (Nat × Nat)) :
    List (Nat × Nat) :=
  List.filter (tiedP d S) (pairsOf d)

/-- The selected exchange pair: the tied list's first read. -/
private def xiP (d : Nat) (S : List (Nat × Nat)) : Nat × Nat :=
  ground.getAt (0, 0) (tiedList d S) 0

/-- The conditioned exchange: the selected pair's at a tied
family, the family kept off ties. -/
private def xiEx (d : Nat) (S : List (Nat × Nat)) :
    List (Nat × Nat) :=
  if 0 < (tiedList d S).length
  then exchAt d S (xiP d S).1 (xiP d S).2
  else S

/-- At a tied pair the exchange keeps the tied list. -/
private theorem tiedList_exchAt {d v w : Nat} (hvw : v < w)
    (hwd : w < d) (S : List (Nat × Nat))
    (htie : takeAt d S v = takeAt d S w) :
    tiedList d (exchAt d S v w) = tiedList d S := by
  show List.filter (tiedP d (exchAt d S v w)) (pairsOf d)
    = List.filter (tiedP d S) (pairsOf d)
  refine ground.filter_congr_mem _ _ (pairsOf d)
    (fun x _ => ?_)
  show decide (takeAt d (exchAt d S v w) x.1
      = takeAt d (exchAt d S v w) x.2)
    = decide (takeAt d S x.1 = takeAt d S x.2)
  rw [takeAt_exchAt_tie hvw hwd S htie x.1,
    takeAt_exchAt_tie hvw hwd S htie x.2]

/-- The conditioned exchange joins the enumeration. -/
private theorem xiEx_memS {d : Nat} {S : List (Nat × Nat)}
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (pairsOf d))) :
    0 < ground.countOf (xiEx d S)
      (ground.sublistsOf (pairsOf d)) := by
  by_cases hT : 0 < (tiedList d S).length
  · rw [show xiEx d S = exchAt d S (xiP d S).1 (xiP d S).2
      from if_pos hT]
    exact exchAt_memS d S _ _
  · rw [show xiEx d S = S from if_neg hT]
    exact hS

/-- The conditioned exchange is its own inverse on the
enumeration. -/
private theorem xiEx_invol {d : Nat} {S : List (Nat × Nat)}
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (pairsOf d))) :
    xiEx d (xiEx d S) = S := by
  by_cases hT : 0 < (tiedList d S).length
  · have hmem := filter_pos (tiedP d S) (xiP d S) (pairsOf d)
      (ground.countOf_getAt_pos (0, 0) (tiedList d S) 0 hT)
    have hvw := (pairs_mem d _ hmem.2).1
    have hwd := (pairs_mem d _ hmem.2).2
    have htie : takeAt d S (xiP d S).1 = takeAt d S (xiP d S).2 :=
      of_decide_eq_true hmem.1
    rw [show xiEx d S = exchAt d S (xiP d S).1 (xiP d S).2
      from if_pos hT]
    show (if 0 < (tiedList d
        (exchAt d S (xiP d S).1 (xiP d S).2)).length
      then exchAt d (exchAt d S (xiP d S).1 (xiP d S).2)
        (xiP d (exchAt d S (xiP d S).1 (xiP d S).2)).1
        (xiP d (exchAt d S (xiP d S).1 (xiP d S).2)).2
      else exchAt d S (xiP d S).1 (xiP d S).2) = S
    rw [show xiP d (exchAt d S (xiP d S).1 (xiP d S).2)
        = ground.getAt (0, 0)
          (tiedList d (exchAt d S (xiP d S).1 (xiP d S).2)) 0
      from rfl,
      tiedList_exchAt hvw hwd S htie, if_pos hT]
    exact exchAt_invol hvw hwd hS
  · rw [show xiEx d S = S from if_neg hT]
    exact if_neg hT

/-- The tied families' graded counts read one value at every key:
each joins its exchange at the flipped side. -/
private theorem tied_balance (b : List Nat) (k : Nat) :
    ground.famFold Nat.add 0
      (fun S => if 0 < (tiedList b.length S).length
          ∧ ((k, true) : Nat × Bool)
            = (keyAt b S, places.sideOf S)
        then (1 : Nat) else 0)
      (ground.sublistsOf (pairsOf b.length))
  = ground.famFold Nat.add 0
      (fun S => if 0 < (tiedList b.length S).length
          ∧ ((k, false) : Nat × Bool)
            = (keyAt b S, places.sideOf S)
        then (1 : Nat) else 0)
      (ground.sublistsOf (pairsOf b.length)) := by
  refine Eq.trans (ground.famFold_reindex Nat.add 0 Nat.add_comm
    Nat.add_assoc
    (fun S => if 0 < (tiedList b.length S).length
        ∧ ((k, true) : Nat × Bool)
          = (keyAt b S, places.sideOf S)
      then (1 : Nat) else 0)
    (l := ground.sublistsOf (pairsOf b.length))
    (g := xiEx b.length) (h := xiEx b.length)
    (fun x _ => ground.sublists_count_le (pairsOf b.length)
      (fun t => pairs_distinct b.length t) x)
    (fun x hx => xiEx_invol hx)
    (fun x hx => xiEx_invol hx)
    (fun x hx => xiEx_memS hx)
    (fun x hx => xiEx_memS hx)) ?_
  refine ground.famFold_congr_members Nat.add 0 _ _
    (ground.sublistsOf (pairsOf b.length)) (fun S hS => ?_)
  by_cases hT : 0 < (tiedList b.length S).length
  · have hmem := filter_pos (tiedP b.length S) (xiP b.length S)
      (pairsOf b.length)
      (ground.countOf_getAt_pos (0, 0) (tiedList b.length S) 0 hT)
    have hvw := (pairs_mem b.length _ hmem.2).1
    have hwd := (pairs_mem b.length _ hmem.2).2
    have htie : takeAt b.length S (xiP b.length S).1
        = takeAt b.length S (xiP b.length S).2 :=
      of_decide_eq_true hmem.1
    rw [show xiEx b.length S
        = exchAt b.length S (xiP b.length S).1 (xiP b.length S).2
      from if_pos hT,
      tiedList_exchAt hvw hwd S htie,
      keyAt_exchAt hvw hwd S htie,
      sideOf_exchAt hvw hwd hS]
    cases hside : places.sideOf S with
    | true =>
      rw [if_neg (fun hc : _ ∧ ((k, true) : Nat × Bool) = _ =>
          Bool.noConfusion (congrArg Prod.snd hc.2)),
        if_neg (fun hc : _ ∧ ((k, false) : Nat × Bool) = _ =>
          Bool.noConfusion (congrArg Prod.snd hc.2))]
    | false =>
      by_cases hk : k = keyAt b S
      · rw [if_pos ⟨hT,
            (show ((k, true) : Nat × Bool) = (keyAt b S, !false)
              from by rw [hk]; rfl)⟩,
          if_pos ⟨hT,
            (show ((k, false) : Nat × Bool) = (keyAt b S, false)
              from by rw [hk])⟩]
      · rw [if_neg (fun hc : _ ∧ ((k, true) : Nat × Bool) = _ =>
            hk (congrArg Prod.fst hc.2)),
          if_neg (fun hc : _ ∧ ((k, false) : Nat × Bool) = _ =>
            hk (congrArg Prod.fst hc.2))]
  · rw [show xiEx b.length S = S from if_neg hT,
      if_neg (fun hc : (0 < (tiedList b.length S).length) ∧ _ =>
        hT hc.1),
      if_neg (fun hc : (0 < (tiedList b.length S).length) ∧ _ =>
        hT hc.1)]

/-- The assignment's family: the pairs whose later letter sits at
the earlier position. -/
private def psiP (d : Nat) (p : List Nat) : List (Nat × Nat) :=
  List.filter
    (fun q => decide (places.posOf q.2 p < places.posOf q.1 p))
    (pairsOf d)

/-- An assignment's three reads: the width, the letters' counts,
and the entries' bound. -/
private theorem perm_reads {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d)) :
    p.length = d ∧ (∀ v, v < d → ground.countOf v p = 1)
      ∧ (∀ x, 0 < ground.countOf x p → x < d) := by
  have hc := places.member_conditions
    (show 0 < ground.countOf p
      (places.monomialsAt (List.replicate d 1)) from hp)
  have hlen : p.length = d := by
    rw [hc.1, ground.sumNat_replicate_one d]
  have hcontent := hc.2
  rw [ground.length_replicate 1 d] at hcontent
  refine ⟨hlen, fun v hv => ?_, fun x hx => ?_⟩
  · have h := places.getAt_contentAt d p v hv
    rw [hcontent, ground.getAt_replicate 0 1 d v hv] at h
    exact h.symm
  · exact places.mem_lt_of_content d p
      (by rw [hcontent, ground.sumNat_replicate_one d, hlen]) x hx

/-- The assignment family's taken places: each pair at its
earlier-positioned letter. -/
private theorem takenAt_psiP {d : Nat} (p : List Nat)
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    takenAt (psiP d p) q
      = if places.posOf q.2 p < places.posOf q.1 p
        then q.2 else q.1 := by
  show (if 0 < ground.countOf q (psiP d p) then q.2 else q.1) = _
  rw [show ground.countOf q (psiP d p)
      = if (decide (places.posOf q.2 p < places.posOf q.1 p))
          = true then ground.countOf q (pairsOf d) else 0
    from ground.countOf_filter _ q (pairsOf d)]
  by_cases hpos : places.posOf q.2 p < places.posOf q.1 p
  · rw [if_pos (decide_eq_true hpos), if_pos hq, if_pos hpos]
  · rw [if_neg (fun h : (decide (places.posOf q.2 p
          < places.posOf q.1 p)) = true =>
        hpos (of_decide_eq_true h)),
      if_neg (Nat.lt_irrefl 0), if_neg hpos]

/-- The strictly-beyond count on a range: the width less the
letter's successor. -/
private theorem countAbove_range (d c : Nat) (h : c < d) :
    ground.famFold Nat.add 0
      (fun i => if c < i then (1 : Nat) else 0) (List.range d)
    = d - (c + 1) := by
  rw [show d = c + 1 + (d - (c + 1)) from
      (ground.natAddSubCancel h).symm,
    ground.aboveRun c 1 (d - (c + 1)), Nat.one_mul,
    ground.natAddSubCancel h]

/-- The taken-place count collects over the places: per pair the
earlier-positioned letter, per place its later-positioned
partners. -/
private theorem take_psiP_go (p : List Nat) (v : Nat) :
    ∀ d : Nat, (∀ u, u < d → 0 < ground.countOf u p) →
    ground.famFold Nat.add 0
      (fun q => if (if places.posOf q.2 p < places.posOf q.1 p
          then q.2 else q.1) = v then (1 : Nat) else 0)
      (pairsOf d)
    = (if v < d then
        ground.famFold Nat.add 0
          (fun u => if ¬ u = v
              ∧ places.posOf v p < places.posOf u p
            then (1 : Nat) else 0)
          (List.range d)
      else 0)
  | 0, _ => by
    rw [if_neg (Nat.not_lt_zero v)]
    rfl
  | d + 1, hcnt => by
    have hcnt' : ∀ u, u < d → 0 < ground.countOf u p :=
      fun u hu => hcnt u (Nat.lt_succ_of_lt hu)
    rw [show pairsOf (d + 1)
        = pairsOf d ++ (List.range d).map (fun j => (j, d))
        from rfl,
      ground.famFold_append Nat.add 0
        (fun x y z => Nat.add_assoc x y z)
        (fun x => Nat.zero_add x) _
        (pairsOf d) ((List.range d).map (fun j => (j, d))),
      take_psiP_go p v d hcnt']
    match Nat.lt_or_ge v (d + 1) with
    | .inr hge =>
      have hz : ground.famFold Nat.add 0
          (fun q => if (if places.posOf q.2 p
              < places.posOf q.1 p
            then q.2 else q.1) = v then (1 : Nat) else 0)
          ((List.range d).map (fun j => (j, d))) = 0 := by
        rw [ground.famFold_map Nat.add 0 _ (fun j => (j, d))
          (List.range d)]
        refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
          (fun _ => (0 : Nat)) (List.range d) (fun j hj => ?_))
          (ground.famFold_zero (fun _ => (0 : Nat))
            (fun _ => rfl) _)
        show (if (if places.posOf d p < places.posOf j p
            then d else j) = v then (1 : Nat) else 0) = 0
        by_cases hdj : places.posOf d p < places.posOf j p
        · rw [if_pos hdj, if_neg (fun he : d = v =>
            Nat.lt_irrefl v (he ▸ hge))]
        · rw [if_neg hdj, if_neg (fun he : j = v =>
            Nat.lt_irrefl v (Nat.lt_of_le_of_lt
              (Nat.le_of_eq he.symm)
              (Nat.lt_trans (ground.ltOfMem hj) hge)))]
      rw [hz,
        if_neg (fun hc : v < d =>
          Nat.lt_irrefl v (Nat.lt_trans hc hge)),
        if_neg (fun hc : v < d + 1 =>
          Nat.lt_irrefl v (Nat.lt_of_lt_of_le hc hge))]
    | .inl hv1 =>
      match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hv1) with
      | .inr hvd =>
        have hstep : ground.famFold Nat.add 0
            (fun q => if (if places.posOf q.2 p
                < places.posOf q.1 p
              then q.2 else q.1) = v then (1 : Nat) else 0)
            ((List.range d).map (fun j => (j, d)))
          = (if places.posOf v p < places.posOf d p
            then (1 : Nat) else 0) := by
          rw [ground.famFold_map Nat.add 0 _ (fun j => (j, d))
            (List.range d)]
          refine Eq.trans (ground.famFold_congr_members Nat.add 0
            _ (fun j => if j = v
              then (if places.posOf v p < places.posOf d p
                then (1 : Nat) else 0) else 0)
            (List.range d) (fun j hj => ?_))
            (ground.famFold_pick
              (fun _ => if places.posOf v p < places.posOf d p
                then (1 : Nat) else 0) v (List.range d)
              (by rw [ground.countOf_range v d, if_pos hvd]))
          show (if (if places.posOf d p < places.posOf j p
              then d else j) = v then (1 : Nat) else 0)
            = (if j = v
              then (if places.posOf v p < places.posOf d p
                then (1 : Nat) else 0) else 0)
          by_cases hjv : j = v
          · rw [if_pos hjv, hjv]
            have hne : ¬ places.posOf d p = places.posOf v p :=
              posOf_inj (hcnt d (Nat.lt_succ_self d))
                (hcnt v hv1)
                (fun he : d = v => Nat.lt_irrefl v (he ▸ hvd))
            by_cases hdv : places.posOf d p < places.posOf v p
            · rw [if_pos hdv,
                if_neg (fun he : d = v =>
                  Nat.lt_irrefl v (he ▸ hvd)),
                if_neg (fun hc : places.posOf v p
                    < places.posOf d p =>
                  Nat.lt_irrefl (places.posOf v p)
                    (Nat.lt_trans hc hdv))]
            · have hvd2 : places.posOf v p < places.posOf d p :=
                match Nat.lt_or_ge (places.posOf d p)
                    (places.posOf v p) with
                | .inl h => absurd h hdv
                | .inr hge2 => Nat.lt_of_le_of_ne hge2
                    (fun he => hne he.symm)
              rw [if_neg hdv, if_pos rfl, if_pos hvd2]
          · rw [if_neg hjv]
            by_cases hdj : places.posOf d p < places.posOf j p
            · rw [if_pos hdj, if_neg (fun he : d = v =>
                Nat.lt_irrefl v (he ▸ hvd))]
            · rw [if_neg hdj, if_neg hjv]
        rw [hstep, if_pos hvd, if_pos hv1,
          ground.endSplit (fun u => if ¬ u = v
              ∧ places.posOf v p < places.posOf u p
            then (1 : Nat) else 0) d]
        by_cases hpd : places.posOf v p < places.posOf d p
        · rw [if_pos hpd, if_pos (show ¬ d = v
              ∧ places.posOf v p < places.posOf d p from
            ⟨fun he : d = v => Nat.lt_irrefl v (he ▸ hvd),
              hpd⟩)]
        · rw [if_neg hpd, if_neg (fun hc : ¬ d = v
              ∧ places.posOf v p < places.posOf d p =>
            hpd hc.2)]
      | .inl he =>
        rw [← he,
          if_neg (Nat.lt_irrefl v),
          if_pos (Nat.lt_succ_self v)]
        refine (Nat.zero_add _).trans ?_
        rw [ground.endSplit (fun u => if ¬ u = v
              ∧ places.posOf v p < places.posOf u p
            then (1 : Nat) else 0) v,
          if_neg (fun hc : ¬ v = v ∧ _ => hc.1 rfl),
          Nat.add_zero,
          ground.famFold_map Nat.add 0 _ (fun j => (j, v))
            (List.range v)]
        refine ground.famFold_congr_members Nat.add 0 _ _
          (List.range v) (fun j hj => ?_)
        show (if (if places.posOf v p < places.posOf j p
            then v else j) = v then (1 : Nat) else 0)
          = (if ¬ j = v ∧ places.posOf v p < places.posOf j p
            then (1 : Nat) else 0)
        have hjlt : j < v := ground.ltOfMem hj
        have hjv : ¬ j = v := fun hejv =>
          Nat.lt_irrefl v (hejv ▸ hjlt)
        by_cases hvj : places.posOf v p < places.posOf j p
        · rw [if_pos hvj, if_pos rfl,
            if_pos (show ¬ j = v
                ∧ places.posOf v p < places.posOf j p from
              ⟨hjv, hvj⟩)]
        · rw [if_neg hvj, if_neg hjv,
            if_neg (fun hc : ¬ j = v
                ∧ places.posOf v p < places.posOf j p =>
              hvj hc.2)]

/-- The assignment family's taken counts: the positions'
complements. -/
private theorem takeAt_psiP_eq {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d)) {v : Nat}
    (hv : v < d) :
    takeAt d (psiP d p) v = d - (places.posOf v p + 1) := by
  have hread := perm_reads hp
  have hlen := hread.1
  have hcnt := hread.2.1
  have hbound := hread.2.2
  have hcnt' : ∀ u, u < d → 0 < ground.countOf u p :=
    fun u hu => by
      rw [hcnt u hu]
      exact Nat.succ_pos 0
  have hdist : ∀ z, ground.countOf z p ≤ 1 := fun z => by
    by_cases hz : z < d
    · rw [hcnt z hz]
      exact Nat.le_refl 1
    · match Nat.eq_zero_or_pos (ground.countOf z p) with
      | .inl h0 =>
        rw [h0]
        exact Nat.zero_le 1
      | .inr hpos => exact absurd (hbound z hpos) hz
  have hposlt : places.posOf v p < d := by
    have h := places.posOf_lt v p (hcnt' v hv)
    rw [hlen] at h
    exact h
  show ground.countOf v ((pairsOf d).map (takenAt (psiP d p))) = _
  rw [ground.countOf_fold v
      ((pairsOf d).map (takenAt (psiP d p))),
    ground.famFold_map Nat.add 0
      (fun x => if v = x then (1 : Nat) else 0)
      (takenAt (psiP d p)) (pairsOf d),
    ground.famFold_congr_members Nat.add 0 _
      (fun q => if (if places.posOf q.2 p < places.posOf q.1 p
          then q.2 else q.1) = v then (1 : Nat) else 0)
      (pairsOf d) (fun q hq => by
        rw [takenAt_psiP p hq]
        by_cases he : (if places.posOf q.2 p
            < places.posOf q.1 p then q.2 else q.1) = v
        · rw [if_pos he.symm, if_pos he]
        · rw [if_neg (fun hc : v = _ => he hc.symm), if_neg he]),
    take_psiP_go p v d hcnt', if_pos hv,
    ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun u => if ¬ u = v ∧ places.posOf v p < places.posOf u p
        then (1 : Nat) else 0)
      (l := List.range d) (g := fun i => ground.getAt 0 p i)
      (h := fun u => places.posOf u p)
      (ground.distinctList_range d)
      (fun x hx => places.posOf_getAt hdist x
        (by rw [hlen]; exact ground.ltOfMem hx))
      (fun u hu => places.getAt_posOf u p
        (hcnt' u (ground.ltOfMem hu)))
      (fun x hx => ground.countOf_pos_of_mem (ground.memRange
        (hbound _ (ground.countOf_getAt_pos 0 p x
          (by rw [hlen]; exact ground.ltOfMem hx)))))
      (fun u hu => ground.countOf_pos_of_mem (ground.memRange (by
        have h2 := places.posOf_lt u p
          (hcnt' u (ground.ltOfMem hu))
        rw [hlen] at h2
        exact h2)))]
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun i => if places.posOf v p < i then (1 : Nat) else 0)
    (List.range d) (fun i hi => ?_))
    (countAbove_range d (places.posOf v p) hposlt)
  have hilt : i < d := ground.ltOfMem hi
  have hpos_i : places.posOf (ground.getAt 0 p i) p = i :=
    places.posOf_getAt hdist i (by rw [hlen]; exact hilt)
  show (if ¬ ground.getAt 0 p i = v
      ∧ places.posOf v p < places.posOf (ground.getAt 0 p i) p
    then (1 : Nat) else 0)
    = (if places.posOf v p < i then (1 : Nat) else 0)
  rw [hpos_i]
  by_cases hlt : places.posOf v p < i
  · rw [if_pos (show ¬ ground.getAt 0 p i = v
        ∧ places.posOf v p < i from
      ⟨fun heq => by
        rw [heq] at hpos_i
        rw [hpos_i] at hlt
        exact Nat.lt_irrefl i hlt, hlt⟩),
      if_pos hlt]
  · rw [if_neg (fun hc : ¬ ground.getAt 0 p i = v
        ∧ places.posOf v p < i => hlt hc.2),
      if_neg hlt]

/-- The assignment family's key is the display's dot against the
permuted exponents. -/
private theorem keyAt_psiP {b p : List Nat}
    (hp : 0 < ground.countOf p (places.perms b.length)) :
    keyAt b (psiP b.length p)
      = ground.dotNat (unitDisp b.length) (places.expo b p) := by
  have hread := perm_reads hp
  have hlen := hread.1
  have hcnt := hread.2.1
  have hbound := hread.2.2
  have hcnt' : ∀ u, u < b.length → 0 < ground.countOf u p :=
    fun u hu => by
      rw [hcnt u hu]
      exact Nat.succ_pos 0
  have hdist : ∀ z, ground.countOf z p ≤ 1 := fun z => by
    by_cases hz : z < b.length
    · rw [hcnt z hz]
      exact Nat.le_refl 1
    · match Nat.eq_zero_or_pos (ground.countOf z p) with
      | .inl h0 =>
        rw [h0]
        exact Nat.zero_le 1
      | .inr hpos => exact absurd (hbound z hpos) hz
  have hlenU : (unitDisp b.length).length = b.length := by
    show (display (List.replicate b.length 0)).length = b.length
    rw [places.length_display, ground.length_replicate]
  rw [ground.dotNat_index (unitDisp b.length) (places.expo b p)
      (by
        show (p.map (ground.getAt 0 b)).length = _
        rw [ground.length_map, hlen, hlenU]),
    hlenU]
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun v => (b.length - places.posOf v p)
      * ground.getAt 0 b v) (List.range b.length)
    (fun v hv => ?_)) (Eq.trans
      (ground.famFold_reindex Nat.add 0 Nat.add_comm
        Nat.add_assoc
        (fun v => (b.length - places.posOf v p)
          * ground.getAt 0 b v)
        (l := List.range b.length)
        (g := fun i => ground.getAt 0 p i)
        (h := fun u => places.posOf u p)
        (ground.distinctList_range b.length)
        (fun x hx => places.posOf_getAt hdist x
          (by rw [hlen]; exact ground.ltOfMem hx))
        (fun u hu => places.getAt_posOf u p
          (hcnt' u (ground.ltOfMem hu)))
        (fun x hx => ground.countOf_pos_of_mem (ground.memRange
          (hbound _ (ground.countOf_getAt_pos 0 p x
            (by rw [hlen]; exact ground.ltOfMem hx)))))
        (fun u hu => ground.countOf_pos_of_mem
          (ground.memRange (by
            have h2 := places.posOf_lt u p
              (hcnt' u (ground.ltOfMem hu))
            rw [hlen] at h2
            exact h2))))
      (ground.famFold_congr_members Nat.add 0 _ _
        (List.range b.length) (fun i hi => ?_)))
  · -- (1 + takeAt) * b_v = (d - pos_v) * b_v at member v
    have hvd : v < b.length := ground.ltOfMem hv
    rw [takeAt_psiP_eq hp hvd]
    have hple : places.posOf v p + 1 ≤ b.length := by
      have h2 := places.posOf_lt v p (hcnt' v hvd)
      rw [hlen] at h2
      exact h2
    have h1 : (places.posOf v p + 1)
        + (b.length - (places.posOf v p + 1)) = b.length :=
      ground.natAddSubCancel hple
    have h2 : places.posOf v p
        + (b.length - places.posOf v p) = b.length :=
      ground.natAddSubCancel (Nat.le_of_lt hple)
    have h3 : places.posOf v p
        + (1 + (b.length - (places.posOf v p + 1)))
        = b.length := by
      rw [← Nat.add_assoc]
      exact h1
    rw [ground.addCancelL (places.posOf v p)
      (h3.trans h2.symm)]
  · -- (d - posOf (p_i)) * b_{p_i} = uD_i * (expo b p)_i at member i
    have hid : i < b.length := ground.ltOfMem hi
    have hpos_i : places.posOf (ground.getAt 0 p i) p = i :=
      places.posOf_getAt hdist i (by rw [hlen]; exact hid)
    rw [hpos_i,
      show ground.getAt 0 (places.expo b p) i
        = ground.getAt 0 b (ground.getAt 0 p i) from
        ground.getAt_map 0 0 (ground.getAt 0 b) p i
          (by rw [hlen]; exact hid),
      weylchar.getAt_unitDisp b.length i hid]

/-- The assignment reads bundled: the width, the letters' counts,
the distinctness, and the entries' bound. -/
private theorem perm_kit {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d)) :
    p.length = d ∧ (∀ u, u < d → 0 < ground.countOf u p)
      ∧ (∀ z, ground.countOf z p ≤ 1)
      ∧ (∀ x, 0 < ground.countOf x p → x < d) := by
  match places.perm_member_reads hp with
  | ⟨hlen, hle, hlt, hpos⟩ => exact ⟨hlen, hpos, hle, hlt⟩

/-- The letter pair's positions, sorted. -/
private def pmap (p : List Nat) (q : Nat × Nat) : Nat × Nat :=
  if places.posOf q.1 p < places.posOf q.2 p
  then (places.posOf q.1 p, places.posOf q.2 p)
  else (places.posOf q.2 p, places.posOf q.1 p)

/-- The position pair's letters, sorted. -/
private def vmap (p : List Nat) (r : Nat × Nat) : Nat × Nat :=
  if ground.getAt 0 p r.1 < ground.getAt 0 p r.2
  then (ground.getAt 0 p r.1, ground.getAt 0 p r.2)
  else (ground.getAt 0 p r.2, ground.getAt 0 p r.1)

/-- The positions map joins the pairs. -/
private theorem pmap_mem {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d))
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    0 < ground.countOf (pmap p q) (pairsOf d) := by
  have hk := perm_kit hp
  have h12 := (pairs_mem d q hq).1
  have h2d := (pairs_mem d q hq).2
  have hpos1 : places.posOf q.1 p < d := by
    have h := places.posOf_lt q.1 p
      (hk.2.1 q.1 (Nat.lt_trans h12 h2d))
    rw [hk.1] at h
    exact h
  have hpos2 : places.posOf q.2 p < d := by
    have h := places.posOf_lt q.2 p (hk.2.1 q.2 h2d)
    rw [hk.1] at h
    exact h
  show 0 < ground.countOf
    (if places.posOf q.1 p < places.posOf q.2 p
      then (places.posOf q.1 p, places.posOf q.2 p)
      else (places.posOf q.2 p, places.posOf q.1 p)) (pairsOf d)
  by_cases hlt : places.posOf q.1 p < places.posOf q.2 p
  · rw [if_pos hlt]
    exact pairs_complete d hlt hpos2
  · rw [if_neg hlt]
    have hne : ¬ places.posOf q.1 p = places.posOf q.2 p :=
      posOf_inj (hk.2.1 q.1 (Nat.lt_trans h12 h2d))
        (hk.2.1 q.2 h2d)
        (fun he => Nat.lt_irrefl q.2
          (Nat.lt_of_le_of_lt (Nat.le_of_eq he.symm) h12))
    have hgt : places.posOf q.2 p < places.posOf q.1 p :=
      match Nat.lt_or_ge (places.posOf q.2 p)
          (places.posOf q.1 p) with
      | .inl h => h
      | .inr hge => absurd (Nat.lt_of_le_of_ne hge hne) hlt
    exact pairs_complete d hgt hpos1

/-- The letters map joins the pairs. -/
private theorem vmap_mem {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d))
    {r : Nat × Nat} (hr : 0 < ground.countOf r (pairsOf d)) :
    0 < ground.countOf (vmap p r) (pairsOf d) := by
  have hk := perm_kit hp
  have h12 := (pairs_mem d r hr).1
  have h2d := (pairs_mem d r hr).2
  have he1 : ground.getAt 0 p r.1 < d :=
    hk.2.2.2 _ (ground.countOf_getAt_pos 0 p r.1
      (by rw [hk.1]; exact Nat.lt_trans h12 h2d))
  have he2 : ground.getAt 0 p r.2 < d :=
    hk.2.2.2 _ (ground.countOf_getAt_pos 0 p r.2
      (by rw [hk.1]; exact h2d))
  have hne : ¬ ground.getAt 0 p r.1 = ground.getAt 0 p r.2 :=
    fun he => by
      have e1p := places.posOf_getAt hk.2.2.1 r.1
        (by rw [hk.1]; exact Nat.lt_trans h12 h2d)
      have e2p := places.posOf_getAt hk.2.2.1 r.2
        (by rw [hk.1]; exact h2d)
      rw [he] at e1p
      exact Nat.lt_irrefl r.2 (Nat.lt_of_le_of_lt
        (Nat.le_of_eq (e1p.symm.trans e2p).symm) h12)
  show 0 < ground.countOf
    (if ground.getAt 0 p r.1 < ground.getAt 0 p r.2
      then (ground.getAt 0 p r.1, ground.getAt 0 p r.2)
      else (ground.getAt 0 p r.2, ground.getAt 0 p r.1))
    (pairsOf d)
  by_cases hlt : ground.getAt 0 p r.1 < ground.getAt 0 p r.2
  · rw [if_pos hlt]
    exact pairs_complete d hlt he2
  · rw [if_neg hlt]
    have hgt : ground.getAt 0 p r.2 < ground.getAt 0 p r.1 :=
      match Nat.lt_or_ge (ground.getAt 0 p r.2)
          (ground.getAt 0 p r.1) with
      | .inl h => h
      | .inr hge => absurd (Nat.lt_of_le_of_ne hge hne) hlt
    exact pairs_complete d hgt he1

/-- The letters of the positions read the pair back. -/
private theorem vmap_pmap {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d))
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    vmap p (pmap p q) = q := by
  have hk := perm_kit hp
  have h12 := (pairs_mem d q hq).1
  have h2d := (pairs_mem d q hq).2
  have hg1 : ground.getAt 0 p (places.posOf q.1 p) = q.1 :=
    places.getAt_posOf q.1 p
      (hk.2.1 q.1 (Nat.lt_trans h12 h2d))
  have hg2 : ground.getAt 0 p (places.posOf q.2 p) = q.2 :=
    places.getAt_posOf q.2 p (hk.2.1 q.2 h2d)
  show vmap p (if places.posOf q.1 p < places.posOf q.2 p
    then (places.posOf q.1 p, places.posOf q.2 p)
    else (places.posOf q.2 p, places.posOf q.1 p)) = q
  by_cases hlt : places.posOf q.1 p < places.posOf q.2 p
  · rw [if_pos hlt]
    show (if ground.getAt 0 p (places.posOf q.1 p)
        < ground.getAt 0 p (places.posOf q.2 p)
      then (ground.getAt 0 p (places.posOf q.1 p),
        ground.getAt 0 p (places.posOf q.2 p))
      else (ground.getAt 0 p (places.posOf q.2 p),
        ground.getAt 0 p (places.posOf q.1 p))) = q
    rw [hg1, hg2, if_pos h12]
  · rw [if_neg hlt]
    show (if ground.getAt 0 p (places.posOf q.2 p)
        < ground.getAt 0 p (places.posOf q.1 p)
      then (ground.getAt 0 p (places.posOf q.2 p),
        ground.getAt 0 p (places.posOf q.1 p))
      else (ground.getAt 0 p (places.posOf q.1 p),
        ground.getAt 0 p (places.posOf q.2 p))) = q
    rw [hg1, hg2,
      if_neg (fun hc : q.2 < q.1 => Nat.lt_irrefl q.2
        (Nat.lt_trans hc h12))]

/-- The positions of the letters read the pair back. -/
private theorem pmap_vmap {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d))
    {r : Nat × Nat} (hr : 0 < ground.countOf r (pairsOf d)) :
    pmap p (vmap p r) = r := by
  have hk := perm_kit hp
  have h12 := (pairs_mem d r hr).1
  have h2d := (pairs_mem d r hr).2
  have hp1 : places.posOf (ground.getAt 0 p r.1) p = r.1 :=
    places.posOf_getAt hk.2.2.1 r.1
      (by rw [hk.1]; exact Nat.lt_trans h12 h2d)
  have hp2 : places.posOf (ground.getAt 0 p r.2) p = r.2 :=
    places.posOf_getAt hk.2.2.1 r.2
      (by rw [hk.1]; exact h2d)
  show pmap p (if ground.getAt 0 p r.1 < ground.getAt 0 p r.2
    then (ground.getAt 0 p r.1, ground.getAt 0 p r.2)
    else (ground.getAt 0 p r.2, ground.getAt 0 p r.1)) = r
  by_cases hlt : ground.getAt 0 p r.1 < ground.getAt 0 p r.2
  · rw [if_pos hlt]
    show (if places.posOf (ground.getAt 0 p r.1) p
        < places.posOf (ground.getAt 0 p r.2) p
      then (places.posOf (ground.getAt 0 p r.1) p,
        places.posOf (ground.getAt 0 p r.2) p)
      else (places.posOf (ground.getAt 0 p r.2) p,
        places.posOf (ground.getAt 0 p r.1) p)) = r
    rw [hp1, hp2, if_pos h12]
  · rw [if_neg hlt]
    show (if places.posOf (ground.getAt 0 p r.2) p
        < places.posOf (ground.getAt 0 p r.1) p
      then (places.posOf (ground.getAt 0 p r.2) p,
        places.posOf (ground.getAt 0 p r.1) p)
      else (places.posOf (ground.getAt 0 p r.1) p,
        places.posOf (ground.getAt 0 p r.2) p)) = r
    rw [hp1, hp2,
      if_neg (fun hc : r.2 < r.1 => Nat.lt_irrefl r.2
        (Nat.lt_trans hc h12))]

/-- The reversed-position test transports across the position
map. -/
private theorem psiInd_pmap {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d))
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    (if ground.getAt 0 p (pmap p q).2
        < ground.getAt 0 p (pmap p q).1 then (1 : Nat) else 0)
    = (if places.posOf q.2 p < places.posOf q.1 p
      then (1 : Nat) else 0) := by
  have hk := perm_kit hp
  have h12 := (pairs_mem d q hq).1
  have h2d := (pairs_mem d q hq).2
  have hg1 : ground.getAt 0 p (places.posOf q.1 p) = q.1 :=
    places.getAt_posOf q.1 p
      (hk.2.1 q.1 (Nat.lt_trans h12 h2d))
  have hg2 : ground.getAt 0 p (places.posOf q.2 p) = q.2 :=
    places.getAt_posOf q.2 p (hk.2.1 q.2 h2d)
  have hne : ¬ places.posOf q.1 p = places.posOf q.2 p :=
    posOf_inj (hk.2.1 q.1 (Nat.lt_trans h12 h2d))
      (hk.2.1 q.2 h2d)
      (fun he => Nat.lt_irrefl q.2
        (Nat.lt_of_le_of_lt (Nat.le_of_eq he.symm) h12))
  show (if ground.getAt 0 p
      ((if places.posOf q.1 p < places.posOf q.2 p
        then (places.posOf q.1 p, places.posOf q.2 p)
        else (places.posOf q.2 p, places.posOf q.1 p))
        : Nat × Nat).2
      < ground.getAt 0 p
      ((if places.posOf q.1 p < places.posOf q.2 p
        then (places.posOf q.1 p, places.posOf q.2 p)
        else (places.posOf q.2 p, places.posOf q.1 p))
        : Nat × Nat).1
    then (1 : Nat) else 0) = _
  by_cases hlt : places.posOf q.1 p < places.posOf q.2 p
  · rw [if_pos hlt]
    show (if ground.getAt 0 p (places.posOf q.2 p)
        < ground.getAt 0 p (places.posOf q.1 p)
      then (1 : Nat) else 0) = _
    rw [hg1, hg2,
      if_neg (fun hc : q.2 < q.1 => Nat.lt_irrefl q.2
        (Nat.lt_trans hc h12)),
      if_neg (fun hc => Nat.lt_irrefl (places.posOf q.1 p)
        (Nat.lt_trans hlt hc))]
  · have hgt : places.posOf q.2 p < places.posOf q.1 p :=
      match Nat.lt_or_ge (places.posOf q.2 p)
          (places.posOf q.1 p) with
      | .inl h => h
      | .inr hge => absurd (Nat.lt_of_le_of_ne hge hne) hlt
    rw [if_neg hlt]
    show (if ground.getAt 0 p (places.posOf q.1 p)
        < ground.getAt 0 p (places.posOf q.2 p)
      then (1 : Nat) else 0) = _
    rw [hg1, hg2, if_pos h12, if_pos hgt]

/-- The assignment family's side is the assignment's own
grading. -/
private theorem sideOf_psiP {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d)) :
    places.sideOf (psiP d p) = places.parity p := by
  have hk := perm_kit hp
  show places.parityOf (psiP d p).length
    = places.parityOf (places.inversions p)
  refine congrArg places.parityOf ?_
  refine Eq.trans (filter_length _ (pairsOf d)) ?_
  rw [places.inversions_pairs p, hk.1]
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun q => if places.posOf q.2 p < places.posOf q.1 p
      then (1 : Nat) else 0) (pairsOf d) (fun q hq => ?_)) ?_
  · by_cases hc : places.posOf q.2 p < places.posOf q.1 p
    · rw [if_pos (decide_eq_true hc), if_pos hc]
    · rw [if_neg (fun h => hc (of_decide_eq_true h)), if_neg hc]
  · refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
      (fun q => if ground.getAt 0 p (pmap p q).2
          < ground.getAt 0 p (pmap p q).1 then (1 : Nat) else 0)
      (pairsOf d) (fun q hq => (psiInd_pmap hp hq).symm)) ?_
    exact (ground.famFold_reindex Nat.add 0 Nat.add_comm
      Nat.add_assoc
      (fun r => if ground.getAt 0 p r.2 < ground.getAt 0 p r.1
        then (1 : Nat) else 0)
      (l := pairsOf d) (g := pmap p) (h := vmap p)
      (fun x _ => pairs_distinct d x)
      (fun x hx => vmap_pmap hp hx)
      (fun x hx => pmap_vmap hp hx)
      (fun x hx => pmap_mem hp hx)
      (fun x hx => vmap_mem hp hx)).symm

/-- The fold compares at member comparisons. -/
private theorem famFold_le_members {α : Type} [DecidableEq α]
    {F G : α → Nat} : ∀ l : List α,
    (∀ x, 0 < ground.countOf x l → F x ≤ G x) →
    ground.famFold Nat.add 0 F l ≤ ground.famFold Nat.add 0 G l
  | [], _ => Nat.le_refl 0
  | a :: t, h => by
    show F a + ground.famFold Nat.add 0 F t
      ≤ G a + ground.famFold Nat.add 0 G t
    exact Nat.add_le_add
      (h a (by rw [ground.countOf_head]; exact Nat.succ_pos _))
      (famFold_le_members t
        (fun x hx => h x (ground.countOf_cons_pos hx)))

/-- Equal folds at member comparisons read equal members. -/
private theorem fold_squeeze {α : Type} [DecidableEq α]
    {F G : α → Nat} : ∀ l : List α,
    (∀ x, 0 < ground.countOf x l → F x ≤ G x) →
    ground.famFold Nat.add 0 F l = ground.famFold Nat.add 0 G l →
    ∀ x, 0 < ground.countOf x l → F x = G x
  | [], _, _, x, hx => absurd hx (Nat.lt_irrefl 0)
  | a :: t, hle, he, x, hx => by
    have hleT : ∀ y, 0 < ground.countOf y t → F y ≤ G y :=
      fun y hy => hle y (ground.countOf_cons_pos hy)
    have ha : F a ≤ G a :=
      hle a (by rw [ground.countOf_head]; exact Nat.succ_pos _)
    have ht := famFold_le_members t hleT
    have heC : F a + ground.famFold Nat.add 0 F t
        = G a + ground.famFold Nat.add 0 G t := he
    have hGa : G a ≤ F a := by
      refine leCancelR (ground.famFold Nat.add 0 G t) ?_
      rw [← heC]
      exact Nat.add_le_add (Nat.le_refl (F a)) ht
    have haE : F a = G a := Nat.le_antisymm ha hGa
    have htE : ground.famFold Nat.add 0 F t
        = ground.famFold Nat.add 0 G t := by
      refine ground.addCancelL (F a) ?_
      rw [heC, haE]
    by_cases hxa : x = a
    · rw [hxa, haE]
    · refine fold_squeeze t hleT htE x ?_
      rw [← ground.countOf_head_ne hxa t]
      exact hx

/-- A place's pair reads collect over its partners. -/
private theorem pairsAt_place (v : Nat) (W : Nat → Nat) :
    ∀ d : Nat,
    ground.famFold Nat.add 0
      (fun q => if q.1 = v then W q.2
        else if q.2 = v then W q.1 else 0)
      (pairsOf d)
    = (if v < d then
        ground.famFold Nat.add 0
          (fun u => if u = v then 0 else W u) (List.range d)
      else 0)
  | 0 => by
    rw [if_neg (Nat.not_lt_zero v)]
    rfl
  | d + 1 => by
    rw [show pairsOf (d + 1)
        = pairsOf d ++ (List.range d).map (fun j => (j, d))
        from rfl,
      ground.famFold_append Nat.add 0
        (fun x y z => Nat.add_assoc x y z)
        (fun x => Nat.zero_add x) _
        (pairsOf d) ((List.range d).map (fun j => (j, d))),
      pairsAt_place v W d]
    match Nat.lt_or_ge v (d + 1) with
    | .inr hge =>
      have hz : ground.famFold Nat.add 0
          (fun q => if q.1 = v then W q.2
            else if q.2 = v then W q.1 else 0)
          ((List.range d).map (fun j => (j, d))) = 0 := by
        rw [ground.famFold_map Nat.add 0 _ (fun j => (j, d))
          (List.range d)]
        refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
          (fun _ => (0 : Nat)) (List.range d) (fun j hj => ?_))
          (ground.famFold_zero (fun _ => (0 : Nat))
            (fun _ => rfl) _)
        show (if j = v then W d
          else if d = v then W j else 0) = 0
        rw [if_neg (fun he : j = v => Nat.lt_irrefl v
            (Nat.lt_of_le_of_lt (Nat.le_of_eq he.symm)
              (Nat.lt_trans (ground.ltOfMem hj) hge))),
          if_neg (fun he : d = v => Nat.lt_irrefl v
            (Nat.lt_of_le_of_lt (Nat.le_of_eq he.symm) hge))]
      rw [hz,
        if_neg (fun hc : v < d =>
          Nat.lt_irrefl v (Nat.lt_trans hc hge)),
        if_neg (fun hc : v < d + 1 =>
          Nat.lt_irrefl v (Nat.lt_of_lt_of_le hc hge))]
    | .inl hv1 =>
      match Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hv1) with
      | .inr hvd =>
        have hstep : ground.famFold Nat.add 0
            (fun q => if q.1 = v then W q.2
              else if q.2 = v then W q.1 else 0)
            ((List.range d).map (fun j => (j, d))) = W d := by
          rw [ground.famFold_map Nat.add 0 _ (fun j => (j, d))
            (List.range d)]
          refine Eq.trans (ground.famFold_congr_members Nat.add 0
            _ (fun j => if j = v then W d else 0)
            (List.range d) (fun j hj => ?_))
            (ground.famFold_pick (fun _ => W d) v (List.range d)
              (by rw [ground.countOf_range v d, if_pos hvd]))
          show (if j = v then W d
            else if d = v then W j else 0)
            = (if j = v then W d else 0)
          by_cases hjv : j = v
          · rw [if_pos hjv, if_pos hjv]
          · rw [if_neg hjv, if_neg hjv,
              if_neg (fun he : d = v =>
                Nat.lt_irrefl v (he ▸ hvd))]
        rw [hstep, if_pos hvd, if_pos hv1,
          ground.endSplit (fun u => if u = v then 0 else W u) d,
          if_neg (fun he : d = v =>
            Nat.lt_irrefl v (he ▸ hvd))]
        rfl
      | .inl he =>
        rw [← he, if_neg (Nat.lt_irrefl v),
          if_pos (Nat.lt_succ_self v)]
        refine (Nat.zero_add _).trans ?_
        rw [ground.endSplit (fun u => if u = v then 0 else W u) v,
          if_pos rfl, Nat.add_zero,
          ground.famFold_map Nat.add 0 _ (fun j => (j, v))
            (List.range v)]
        refine ground.famFold_congr_members Nat.add 0 _ _
          (List.range v) (fun j hj => ?_)
        have hjlt : j < v := ground.ltOfMem hj
        show (if j = v then W v
          else if v = v then W j else 0)
          = (if j = v then 0 else W j)
        rw [if_neg (fun hejv : j = v =>
            Nat.lt_irrefl v (hejv ▸ hjlt)),
          if_neg (fun hejv : j = v =>
            Nat.lt_irrefl v (hejv ▸ hjlt)),
          if_pos rfl]

/-- The taken count as the pairs' own fold. -/
private theorem takeAt_fold {d : Nat} (S : List (Nat × Nat))
    (v : Nat) :
    takeAt d S v = ground.famFold Nat.add 0
      (fun q => if v = takenAt S q then (1 : Nat) else 0)
      (pairsOf d) := by
  show ground.countOf v ((pairsOf d).map (takenAt S)) = _
  rw [ground.countOf_fold v ((pairsOf d).map (takenAt S)),
    ground.famFold_map Nat.add 0
      (fun x => if v = x then (1 : Nat) else 0)
      (takenAt S) (pairsOf d)]

/-- The off-place indicator's fold joins the place to the width. -/
private theorem offPick_fold {d v : Nat} (hv : v < d) :
    ground.famFold Nat.add 0
      (fun u => if u = v then 0 else 1) (List.range d) + 1 = d := by
  have hsplit := ground.famFold_add_split
    (fun u => if u = v then 0 else 1)
    (fun u => if u = v then (1 : Nat) else 0) (List.range d)
  have hpt : ground.famFold Nat.add 0
      (fun u => (if u = v then 0 else 1)
        + (if u = v then (1 : Nat) else 0)) (List.range d)
      = ground.famFold Nat.add 0 (fun _ => (1 : Nat))
        (List.range d) :=
    ground.famFold_congr_all Nat.add 0 _ _ (fun u => by
      by_cases hu : u = v
      · rw [if_pos hu, if_pos hu]
      · rw [if_neg hu, if_neg hu]) (List.range d)
  have hpick := ground.famFold_pick (fun _ => (1 : Nat)) v
    (List.range d)
    (by rw [ground.countOf_range v d, if_pos hv])
  have hsum : ground.famFold Nat.add 0
      (fun u => if u = v then 0 else 1) (List.range d)
      + ground.famFold Nat.add 0
        (fun u => if u = v then (1 : Nat) else 0)
        (List.range d) = d := by
    rw [← hsplit, hpt, ground.famFold_length (List.range d),
      ground.length_range d]
  rw [hpick] at hsum
  exact hsum

/-- A pair's taken read enters its own membership read. -/
private theorem taken_le_member (S : List (Nat × Nat)) (v : Nat)
    (q : Nat × Nat) :
    (if v = takenAt S q then (1 : Nat) else 0)
      ≤ (if q.1 = v then 1 else if q.2 = v then 1 else 0) := by
  by_cases hvt : v = takenAt S q
  · rw [if_pos hvt]
    by_cases hm : 0 < ground.countOf q S
    · have ht2 : takenAt S q = q.2 := if_pos hm
      rw [ht2] at hvt
      by_cases h1v : q.1 = v
      · rw [if_pos h1v]
        exact Nat.le_refl 1
      · rw [if_neg h1v, if_pos hvt.symm]
        exact Nat.le_refl 1
    · have ht1 : takenAt S q = q.1 := if_neg hm
      rw [ht1] at hvt
      rw [if_pos hvt.symm]
      exact Nat.le_refl 1
  · rw [if_neg hvt]
    exact Nat.zero_le _

/-- A taken count sits below the width. -/
private theorem takeAt_lt {d : Nat} (S : List (Nat × Nat))
    {v : Nat} (hv : v < d) : takeAt d S v < d := by
  have h1 : takeAt d S v ≤ ground.famFold Nat.add 0
      (fun q => if q.1 = v then 1
        else if q.2 = v then 1 else 0) (pairsOf d) := by
    rw [takeAt_fold S v]
    exact famFold_le_members (pairsOf d)
      (fun q _ => taken_le_member S v q)
  rw [pairsAt_place v (fun _ => 1) d, if_pos hv] at h1
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le h1)
    (Nat.le_of_eq (offPick_fold hv))

/-- Off ties every two places' taken counts differ. -/
private theorem untied_ne {d : Nat} {S : List (Nat × Nat)}
    (hUT : ¬ 0 < (tiedList d S).length) :
    ∀ {u w : Nat}, u < w → w < d →
    ¬ takeAt d S u = takeAt d S w := fun {u w} huw hwd he =>
  hUT (ground.length_pos_of_countOf (by
    show 0 < ground.countOf ((u, w) : Nat × Nat)
      (List.filter (tiedP d S) (pairsOf d))
    rw [ground.countOf_filter (tiedP d S)
        ((u, w) : Nat × Nat) (pairsOf d),
      if_pos (show tiedP d S ((u, w) : Nat × Nat) = true from
        decide_eq_true he)]
    exact pairs_complete d huw hwd))

/-- A member-injective map keeps a distinct family distinct. -/
private theorem map_distinct {α β : Type} [DecidableEq α]
    [DecidableEq β] {f : α → β} {l : List α}
    (hdist : ∀ x, ground.countOf x l ≤ 1)
    (hinj : ∀ a, 0 < ground.countOf a l →
      ∀ b, 0 < ground.countOf b l → f a = f b → a = b) :
    ∀ y, ground.countOf y (l.map f) ≤ 1 := fun y => by
  match Nat.eq_zero_or_pos (ground.countOf y (l.map f)) with
  | .inl h0 =>
    rw [h0]
    exact Nat.zero_le 1
  | .inr hpos =>
    match ground.mem_map_of f l y
        (ground.mem_of_countOf_pos y _ hpos) with
    | ⟨a, ha, hay⟩ =>
      rw [← hay, ground.countOf_map_inj f a l
        (fun x hx he => hinj x hx a
          (ground.countOf_pos_of_mem ha) he)]
      exact hdist a

/-- The takes list is distinct at an untied family. -/
private theorem takesDist {d : Nat} {S : List (Nat × Nat)}
    (hUT : ¬ 0 < (tiedList d S).length) :
    ∀ y, ground.countOf y ((List.range d).map (takeAt d S)) ≤ 1 :=
  map_distinct (fun x => by
    rw [ground.countOf_range x d]
    by_cases hx : x < d
    · rw [if_pos hx]
      exact Nat.le_refl 1
    · rw [if_neg hx]
      exact Nat.zero_le 1)
    (fun a ha b hb he => by
      match Nat.lt_or_ge a b with
      | .inl hab =>
        exact absurd he (untied_ne hUT hab (ground.ltOfMem hb))
      | .inr hge =>
        match Nat.eq_or_lt_of_le hge with
        | .inl heq => exact heq.symm
        | .inr hba =>
          exact absurd he.symm
            (untied_ne hUT hba (ground.ltOfMem ha)))

/-- Off ties the taken counts cover the degrees below the width,
one place each. -/
private theorem takes_cover {d : Nat} {S : List (Nat × Nat)}
    (hUT : ¬ 0 < (tiedList d S).length) :
    ∀ c, c < d → ground.countOf c
      ((List.range d).map (takeAt d S)) = 1 := by
  have hdistT : ∀ y, ground.countOf y
      ((List.range d).map (takeAt d S)) ≤ 1 := takesDist hUT
  have hsum : ground.famFold Nat.add 0
      (fun x => ground.countOf x
        ((List.range d).map (takeAt d S)))
      (List.range d)
      = ((List.range d).map (takeAt d S)).length :=
    ground.countOf_partition ((List.range d).map (takeAt d S))
      (List.range d) (ground.distinctList_range d)
      (fun x hx =>
        match ground.mem_map_of (takeAt d S) (List.range d)
            x hx with
        | ⟨v, hv, hvx⟩ => by
          rw [← hvx]
          exact ground.memRange
            (takeAt_lt S (ground.ltOfMemRange hv)))
  intro c hc
  refine fold_squeeze
    (F := fun x => ground.countOf x
      ((List.range d).map (takeAt d S)))
    (G := fun _ => (1 : Nat)) (List.range d)
    (fun x _ => hdistT x)
    (by rw [hsum, ground.length_mapRange,
      ground.famFold_length (List.range d),
      ground.length_range d])
    c (ground.countOf_pos_of_mem (ground.memRange hc))

/-- The strictly-below test's fold on a range. -/
private theorem countBelowRange (d c : Nat) (h : c ≤ d) :
    ground.famFold Nat.add 0
      (fun i => if i < c then (1 : Nat) else 0) (List.range d)
    = c := by
  rw [show d = c + (d - c) from (ground.natAddSubCancel h).symm,
    places.belowRun c 1 (d - c), Nat.one_mul]

/-- Off ties the below-take places count the level itself. -/
private theorem takesBelow {d : Nat} {S : List (Nat × Nat)}
    (hUT : ¬ 0 < (tiedList d S).length) {c : Nat} (hc : c ≤ d) :
    ground.famFold Nat.add 0
      (fun u => if takeAt d S u < c then (1 : Nat) else 0)
      (List.range d) = c := by
  rw [← ground.famFold_map Nat.add 0
      (fun x => if x < c then (1 : Nat) else 0)
      (takeAt d S) (List.range d),
    ground.famFold_partition
      (fun x => if x < c then (1 : Nat) else 0)
      ((List.range d).map (takeAt d S)) (List.range d)
      (ground.distinctList_range d)
      (fun x hx =>
        match ground.mem_map_of (takeAt d S) (List.range d)
            x hx with
        | ⟨v, hv, hvx⟩ => by
          rw [← hvx]
          exact ground.memRange
            (takeAt_lt S (ground.ltOfMemRange hv)))]
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun x => if x < c then (1 : Nat) else 0) (List.range d)
    (fun x hx => by
      rw [takes_cover hUT x (ground.ltOfMem hx), Nat.one_mul]))
    (countBelowRange d c hc)

/-- A pair at a stated place reads its other end's bounds. -/
private theorem pair_other {d v u : Nat} {q : Nat × Nat}
    (hq : 0 < ground.countOf q (pairsOf d))
    (hqu : q = (u, v) ∨ q = (v, u)) :
    ¬ u = v ∧ u < d ∧ v < d := by
  match hqu with
  | .inl he =>
    have h12 := (pairs_mem d q hq).1
    have h2d := (pairs_mem d q hq).2
    rw [he] at h12 h2d
    exact ⟨fun hc => Nat.lt_irrefl v
      (Nat.lt_of_le_of_lt (Nat.le_of_eq hc.symm) h12),
      Nat.lt_trans h12 h2d, h2d⟩
  | .inr he =>
    have h12 := (pairs_mem d q hq).1
    have h2d := (pairs_mem d q hq).2
    rw [he] at h12 h2d
    exact ⟨fun hc => Nat.lt_irrefl v
      (Nat.lt_of_lt_of_le h12 (Nat.le_of_eq hc)), h2d,
      Nat.lt_trans h12 h2d⟩

/-- Off ties every pair reads its taken place at the larger taken
count, level by level from the top. -/
private theorem tourn_go {d : Nat} {S : List (Nat × Nat)}
    (hUT : ¬ 0 < (tiedList d S).length) :
    ∀ (k v : Nat), v < d → d ≤ takeAt d S v + (k + 1) →
    ∀ q : Nat × Nat, 0 < ground.countOf q (pairsOf d) →
    ∀ u : Nat, q = (u, v) ∨ q = (v, u) →
    (takenAt S q = v ↔ takeAt d S u < takeAt d S v)
  | 0, v, hv, hbound, q, hq, u, hqu => by
    have hmax : takeAt d S v + 1 = d :=
      Nat.le_antisymm (takeAt_lt S hv) hbound
    have hune := pair_other hq hqu
    have hRHS : takeAt d S u < takeAt d S v := by
      have hlt : takeAt d S u < takeAt d S v + 1 :=
        Nat.lt_of_lt_of_le (takeAt_lt S hune.2.1)
          (Nat.le_of_eq hmax.symm)
      have hne : ¬ takeAt d S u = takeAt d S v := by
        match Nat.lt_or_ge u v with
        | .inl huv => exact untied_ne hUT huv hv
        | .inr hge =>
          have hvu : v < u := Nat.lt_of_le_of_ne hge
            (fun he2 => hune.1 he2.symm)
          exact fun he2 => untied_ne hUT hvu hune.2.1 he2.symm
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) hne
    have hsq := fold_squeeze
      (F := fun q' => if v = takenAt S q' then (1 : Nat) else 0)
      (G := fun q' => if q'.1 = v then 1
        else if q'.2 = v then 1 else 0)
      (pairsOf d)
      (fun q' _ => taken_le_member S v q')
      (by
        rw [← takeAt_fold S v, pairsAt_place v (fun _ => 1) d,
          if_pos hv]
        exact Nat.succ.inj (hmax.trans (offPick_fold hv).symm))
      q hq
    refine ⟨fun _ => hRHS, fun _ => ?_⟩
    match hqu with
    | .inl he =>
      rw [he] at hsq
      have hsq2 : (if v = takenAt S ((u, v) : Nat × Nat)
          then (1 : Nat) else 0)
          = (if u = v then 1 else if v = v then 1 else 0) := hsq
      rw [if_neg hune.1, if_pos rfl] at hsq2
      rw [he]
      exact (ground.ind_one hsq2).symm
    | .inr he =>
      rw [he] at hsq
      have hsq2 : (if v = takenAt S ((v, u) : Nat × Nat)
          then (1 : Nat) else 0)
          = (if v = v then 1 else if u = v then 1 else 0) := hsq
      rw [if_pos rfl] at hsq2
      rw [he]
      exact (ground.ind_one hsq2).symm
  | k + 1, v, hv, hbound, q, hq, u, hqu => by
    by_cases hk : d ≤ takeAt d S v + (k + 1)
    · exact tourn_go hUT k v hv hk q hq u hqu
    · have hune := pair_other hq hqu
      have hlev : takeAt d S v + (k + 2) = d := by
        refine Nat.le_antisymm ?_ hbound
        exact match Nat.lt_or_ge (takeAt d S v + (k + 1)) d with
        | .inl h => h
        | .inr hge => absurd hge hk
      have hstep1 : (takeAt d S v + 1) + (k + 1)
          = takeAt d S v + (k + 2) := by
        rw [Nat.add_assoc, Nat.add_comm 1 (k + 1)]
      have hple : ∀ q', 0 < ground.countOf q' (pairsOf d) →
          (if v = takenAt S q' then (1 : Nat) else 0)
          ≤ (if q'.1 = v
              then (if takeAt d S q'.2 < takeAt d S v
                then (1 : Nat) else 0)
              else if q'.2 = v
              then (if takeAt d S q'.1 < takeAt d S v
                then (1 : Nat) else 0)
              else 0) := by
        intro q' hq'
        have h12 := (pairs_mem d q' hq').1
        have h2d := (pairs_mem d q' hq').2
        by_cases hvt : v = takenAt S q'
        · rw [if_pos hvt]
          by_cases h1v : q'.1 = v
          · rw [if_pos h1v]
            have hwv : v < q'.2 := by
              rw [← h1v]
              exact h12
            have hw : ¬ takeAt d S q'.2 = takeAt d S v :=
              fun he2 => untied_ne hUT hwv h2d he2.symm
            match Nat.lt_or_ge (takeAt d S q'.2)
                (takeAt d S v) with
            | .inl hlt =>
              rw [if_pos hlt]
              exact Nat.le_refl 1
            | .inr hge =>
              have hgt : takeAt d S v < takeAt d S q'.2 :=
                Nat.lt_of_le_of_ne hge (fun he2 => hw he2.symm)
              have hbw : d ≤ takeAt d S q'.2 + (k + 1) :=
                Nat.le_trans
                  (Nat.le_of_eq (hlev.symm.trans hstep1.symm))
                  (Nat.add_le_add hgt (Nat.le_refl (k + 1)))
              have hIH := tourn_go hUT k q'.2 h2d hbw q' hq' v
                (Or.inl (by rw [← h1v]))
              have htk : takenAt S q' = q'.2 := hIH.mpr hgt
              rw [htk] at hvt
              exact absurd hvt (fun he2 => Nat.lt_irrefl q'.2
                (Nat.lt_of_le_of_lt (Nat.le_of_eq he2.symm) hwv))
          · by_cases h2v : q'.2 = v
            · rw [if_neg h1v, if_pos h2v]
              have hwv : q'.1 < v := by
                rw [← h2v]
                exact h12
              have hw : ¬ takeAt d S q'.1 = takeAt d S v :=
                untied_ne hUT hwv (by
                  rw [← h2v]
                  exact h2d)
              match Nat.lt_or_ge (takeAt d S q'.1)
                  (takeAt d S v) with
              | .inl hlt =>
                rw [if_pos hlt]
                exact Nat.le_refl 1
              | .inr hge =>
                have hgt : takeAt d S v < takeAt d S q'.1 :=
                  Nat.lt_of_le_of_ne hge (fun he2 => hw he2.symm)
                have hbw : d ≤ takeAt d S q'.1 + (k + 1) :=
                  Nat.le_trans
                    (Nat.le_of_eq (hlev.symm.trans hstep1.symm))
                    (Nat.add_le_add hgt (Nat.le_refl (k + 1)))
                have hIH := tourn_go hUT k q'.1
                  (Nat.lt_trans h12 h2d) hbw q' hq' v
                  (Or.inr (by rw [← h2v]))
                have htk : takenAt S q' = q'.1 := hIH.mpr hgt
                rw [htk] at hvt
                exact absurd hvt (fun he2 => Nat.lt_irrefl v
                  (Nat.lt_of_le_of_lt (Nat.le_of_eq he2) hwv))
            · -- v off the pair: taken is an end, both off v
              exfalso
              by_cases hm : 0 < ground.countOf q' S
              · have ht2 : takenAt S q' = q'.2 := if_pos hm
                rw [ht2] at hvt
                exact h2v hvt.symm
              · have ht1 : takenAt S q' = q'.1 := if_neg hm
                rw [ht1] at hvt
                exact h1v hvt.symm
        · rw [if_neg hvt]
          exact Nat.zero_le _
      have hsums : ground.famFold Nat.add 0
          (fun q' => if v = takenAt S q' then (1 : Nat) else 0)
          (pairsOf d)
          = ground.famFold Nat.add 0
            (fun q' => if q'.1 = v
              then (if takeAt d S q'.2 < takeAt d S v
                then (1 : Nat) else 0)
              else if q'.2 = v
              then (if takeAt d S q'.1 < takeAt d S v
                then (1 : Nat) else 0)
              else 0) (pairsOf d) := by
        rw [← takeAt_fold S v,
          pairsAt_place v
            (fun w => if takeAt d S w < takeAt d S v
              then (1 : Nat) else 0) d,
          if_pos hv,
          ground.famFold_congr_all Nat.add 0 _
            (fun w => if takeAt d S w < takeAt d S v
              then (1 : Nat) else 0)
            (fun w => by
              by_cases hw : w = v
              · rw [if_pos hw, hw,
                  if_neg (Nat.lt_irrefl (takeAt d S v))]
              · rw [if_neg hw]) (List.range d),
          takesBelow hUT (Nat.le_of_lt (takeAt_lt S hv))]
      have hsq := fold_squeeze
        (F := fun q' => if v = takenAt S q' then (1 : Nat) else 0)
        (G := fun q' => if q'.1 = v
          then (if takeAt d S q'.2 < takeAt d S v
            then (1 : Nat) else 0)
          else if q'.2 = v
          then (if takeAt d S q'.1 < takeAt d S v
            then (1 : Nat) else 0)
          else 0)
        (pairsOf d) hple hsums q hq
      match hqu with
      | .inl he =>
        rw [he] at hsq
        have hsq2 : (if v = takenAt S ((u, v) : Nat × Nat)
            then (1 : Nat) else 0)
            = (if u = v
              then (if takeAt d S v < takeAt d S v
                then (1 : Nat) else 0)
              else if v = v
              then (if takeAt d S u < takeAt d S v
                then (1 : Nat) else 0)
              else 0) := hsq
        rw [if_neg hune.1, if_pos rfl] at hsq2
        rw [he]
        refine ⟨fun hT => ground.ind_one (by
            rw [← hsq2, if_pos hT.symm]), fun hR => ?_⟩
        have hF : (if v = takenAt S ((u, v) : Nat × Nat)
            then (1 : Nat) else 0) = 1 := by
          rw [hsq2, if_pos hR]
        exact (ground.ind_one hF).symm
      | .inr he =>
        rw [he] at hsq
        have hsq2 : (if v = takenAt S ((v, u) : Nat × Nat)
            then (1 : Nat) else 0)
            = (if v = v
              then (if takeAt d S u < takeAt d S v
                then (1 : Nat) else 0)
              else if u = v
              then (if takeAt d S v < takeAt d S v
                then (1 : Nat) else 0)
              else 0) := hsq
        rw [if_pos rfl] at hsq2
        rw [he]
        refine ⟨fun hT => ground.ind_one (by
            rw [← hsq2, if_pos hT.symm]), fun hR => ?_⟩
        have hF : (if v = takenAt S ((v, u) : Nat × Nat)
            then (1 : Nat) else 0) = 1 := by
          rw [hsq2, if_pos hR]
        exact (ground.ind_one hF).symm

/-- The ranking assignment: per position the place at the
complementary taken count. -/
private def rankP (d : Nat) (S : List (Nat × Nat)) : List Nat :=
  (List.range d).map (fun i =>
    places.posOf (d - (i + 1)) ((List.range d).map (takeAt d S)))

/-- The complement's complement reads the level back. -/
private theorem subCompl {d c : Nat} (hc : c < d) :
    d - ((d - (c + 1)) + 1) = c := by
  have h1 : c + ((d - (c + 1)) + 1) = d := by
    rw [Nat.add_comm (d - (c + 1)) 1, ← Nat.add_assoc c 1 _]
    exact ground.natAddSubCancel hc
  rw [ground.addCancelL c (h1.trans
      (ground.natAddSubCancel (Nat.le_of_lt hc)).symm)]
  exact ground.natSubSubCancel d c (Nat.le_of_lt hc)

/-- The ranking's letter counts read one below the width. -/
private theorem rankP_count {d : Nat} {S : List (Nat × Nat)}
    (hUT : ¬ 0 < (tiedList d S).length) :
    ∀ v, v < d → ground.countOf v (rankP d S) = 1 := by
  intro v hv
  have htlen : ((List.range d).map (takeAt d S)).length = d :=
    ground.length_mapRange _ d
  have hdistT : ∀ y, ground.countOf y
      ((List.range d).map (takeAt d S)) ≤ 1 := takesDist hUT
  have hgetTl : ∀ u, u < d →
      ground.getAt 0 ((List.range d).map (takeAt d S)) u
        = takeAt d S u := fun u hu => by
    rw [ground.getAt_map 0 0 (takeAt d S) (List.range d) u
        (by rw [ground.length_range]; exact hu),
      ground.getAt_range d u hu]
  have hgv : places.posOf
      (d - ((d - (takeAt d S v + 1)) + 1))
      ((List.range d).map (takeAt d S)) = v := by
    rw [subCompl (takeAt_lt S hv)]
    have h := places.posOf_getAt hdistT v
      (by rw [htlen]; exact hv)
    rw [hgetTl v hv] at h
    exact h
  have ha : d - (takeAt d S v + 1) < d := Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _)
      (takeAt_lt S hv)) (Nat.succ_pos _)
  have hinj : ∀ x, 0 < ground.countOf x (List.range d) →
      places.posOf (d - (x + 1))
          ((List.range d).map (takeAt d S))
        = places.posOf (d - ((d - (takeAt d S v + 1)) + 1))
          ((List.range d).map (takeAt d S)) →
      x = d - (takeAt d S v + 1) := by
    intro x hx he
    have hxd : x < d := ground.ltOfMem hx
    have hpos : 0 < ground.countOf (d - (x + 1))
        ((List.range d).map (takeAt d S)) := by
      rw [takes_cover hUT (d - (x + 1)) (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hxd)
        (Nat.succ_pos _))]
      exact Nat.succ_pos 0
    have h1 := places.getAt_posOf (d - (x + 1))
      ((List.range d).map (takeAt d S)) hpos
    rw [he, hgv] at h1
    rw [hgetTl v hv] at h1
    have c1 : (x + 1) + (d - (x + 1)) = d :=
      ground.natAddSubCancel hxd
    rw [← h1] at c1
    have c2 : (takeAt d S v + 1) + (d - (takeAt d S v + 1)) = d :=
      ground.natAddSubCancel (takeAt_lt S hv)
    have c3 : (takeAt d S v + 1) + x = d := by
      rw [Nat.add_assoc (takeAt d S v) 1 x, Nat.add_comm 1 x,
        Nat.add_comm (takeAt d S v) (x + 1)]
      exact c1
    exact ground.addCancelL (takeAt d S v + 1) (c3.trans c2.symm)
  have hcnt := ground.countOf_map_inj
    (fun i => places.posOf (d - (i + 1))
      ((List.range d).map (takeAt d S)))
    (d - (takeAt d S v + 1)) (List.range d) hinj
  show ground.countOf v ((List.range d).map
    (fun i => places.posOf (d - (i + 1))
      ((List.range d).map (takeAt d S)))) = 1
  rw [← hgv, hcnt, ground.countOf_range, if_pos ha]

/-- The complements reverse the comparison. -/
private theorem subAnti {d a b : Nat} (ha : a < d) (hb : b < d) :
    (d - (b + 1) < d - (a + 1)) ↔ a < b := by
  have c1 : (a + 1) + (d - (a + 1)) = d :=
    ground.natAddSubCancel ha
  have c2 : (b + 1) + (d - (b + 1)) = d :=
    ground.natAddSubCancel hb
  constructor
  · intro h
    match Nat.lt_or_ge a b with
    | .inl h2 => exact h2
    | .inr hge =>
      have hle : (b + 1) + (d - (a + 1))
          ≤ (a + 1) + (d - (a + 1)) :=
        Nat.add_le_add (Nat.succ_le_succ hge) (Nat.le_refl _)
      have hle2 : (b + 1) + (d - (a + 1))
          ≤ (b + 1) + (d - (b + 1)) :=
        Nat.le_trans hle (Nat.le_trans (Nat.le_of_eq c1)
          (Nat.le_of_eq c2.symm))
      have hXY : d - (a + 1) ≤ d - (b + 1) :=
        leCancelL (b + 1) hle2
      exact absurd (Nat.lt_of_lt_of_le h hXY)
        (Nat.lt_irrefl (d - (b + 1)))
  · intro h
    have h1 : ((a + 1) + 1) + (d - (b + 1))
        ≤ (b + 1) + (d - (b + 1)) :=
      Nat.add_le_add (Nat.succ_le_succ h) (Nat.le_refl _)
    have h2 : (a + 1) + (1 + (d - (b + 1)))
        ≤ (a + 1) + (d - (a + 1)) := by
      rw [← Nat.add_assoc]
      exact Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq c2)
        (Nat.le_of_eq c1.symm))
    have h3 : 1 + (d - (b + 1)) ≤ d - (a + 1) :=
      leCancelL (a + 1) h2
    have h4 : (d - (b + 1)) + 1 ≤ d - (a + 1) := by
      rw [Nat.add_comm]
      exact h3
    exact h4

/-- A pair's second-place take is its membership read. -/
private theorem taken_snd_iff {d : Nat} (S : List (Nat × Nat))
    {q : Nat × Nat} (hq : 0 < ground.countOf q (pairsOf d)) :
    takenAt S q = q.2 ↔ 0 < ground.countOf q S := by
  have h12 := (pairs_mem d q hq).1
  constructor
  · intro hT
    by_cases hm : 0 < ground.countOf q S
    · exact hm
    · have ht1 : takenAt S q = q.1 := if_neg hm
      rw [ht1] at hT
      exact absurd hT (fun he => Nat.lt_irrefl q.2
        (Nat.lt_of_le_of_lt (Nat.le_of_eq he.symm) h12))
  · intro hm
    exact if_pos hm

/-- The ranking reads distinct entries. -/
private theorem rankP_dist {d : Nat} {S : List (Nat × Nat)}
    (hUT : ¬ 0 < (tiedList d S).length) :
    ∀ z, ground.countOf z (rankP d S) ≤ 1 := fun z => by
  by_cases hz : z < d
  · rw [rankP_count hUT z hz]
    exact Nat.le_refl 1
  · match Nat.eq_zero_or_pos (ground.countOf z (rankP d S)) with
    | .inl h0 =>
      rw [h0]
      exact Nat.zero_le 1
    | .inr hpos =>
      exfalso
      match ground.mem_map_of
          (fun i => places.posOf (d - (i + 1))
            ((List.range d).map (takeAt d S)))
          (List.range d) z
          (ground.mem_of_countOf_pos z _ hpos) with
      | ⟨i, hi, hie⟩ =>
        refine hz ?_
        rw [← hie]
        have hpos2 : 0 < ground.countOf
            (d - (i + 1)) ((List.range d).map (takeAt d S)) := by
          rw [takes_cover hUT (d - (i + 1))
            (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _)
                (ground.ltOfMemRange hi))
              (Nat.succ_pos _))]
          exact Nat.succ_pos 0
        have h := places.posOf_lt (d - (i + 1))
          ((List.range d).map (takeAt d S)) hpos2
        rw [ground.length_mapRange] at h
        exact h

/-- A place's position in the ranking is its taken count's
complement. -/
private theorem posOf_rankP {d : Nat} {S : List (Nat × Nat)}
    (hUT : ¬ 0 < (tiedList d S).length) {v : Nat} (hv : v < d) :
    places.posOf v (rankP d S) = d - (takeAt d S v + 1) := by
  have htlen : ((List.range d).map (takeAt d S)).length = d :=
    ground.length_mapRange _ d
  have hdistT : ∀ y, ground.countOf y
      ((List.range d).map (takeAt d S)) ≤ 1 := takesDist hUT
  have ha : d - (takeAt d S v + 1) < d := Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le _)
      (takeAt_lt S hv)) (Nat.succ_pos _)
  have hrlen : (rankP d S).length = d :=
    ground.length_mapRange _ d
  have hentry : ground.getAt 0 (rankP d S)
      (d - (takeAt d S v + 1)) = v := by
    show ground.getAt 0 ((List.range d).map
      (fun i => places.posOf (d - (i + 1))
        ((List.range d).map (takeAt d S))))
      (d - (takeAt d S v + 1)) = v
    rw [ground.getAt_map 0 0 _ (List.range d) _
        (by rw [ground.length_range]; exact ha),
      ground.getAt_range d _ ha, subCompl (takeAt_lt S hv)]
    have h := places.posOf_getAt hdistT v
      (by rw [htlen]; exact hv)
    rw [ground.getAt_map 0 0 (takeAt d S) (List.range d) v
        (by rw [ground.length_range]; exact hv),
      ground.getAt_range d v hv] at h
    exact h
  have h := places.posOf_getAt (rankP_dist hUT)
    (d - (takeAt d S v + 1)) (by rw [hrlen]; exact ha)
  rw [hentry] at h
  exact h

/-- The ranking joins the assignments. -/
private theorem rankP_perm {d : Nat} {S : List (Nat × Nat)}
    (hUT : ¬ 0 < (tiedList d S).length) :
    0 < ground.countOf (rankP d S) (places.perms d) := by
  show 0 < ground.countOf (rankP d S)
    (places.monomialsAt (List.replicate d 1))
  rw [places.countOf_monomialsAt (List.replicate d 1)
    (rankP d S)]
  have hlen : (rankP d S).length
      = ground.sumNat (List.replicate d 1) := by
    show ((List.range d).map _).length = _
    rw [ground.length_mapRange,
      ground.sumNat_replicate_one d]
  have hcont : places.content (List.replicate d 1).length
      (rankP d S) = List.replicate d 1 := by
    rw [ground.length_replicate 1 d]
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · rw [places.content_length, ground.length_replicate]
    · intro i hi
      have hid : i < d := by
        rw [places.content_length] at hi
        exact hi
      rw [places.getAt_contentAt d (rankP d S) i hid,
        rankP_count hUT i hid,
        ground.getAt_replicate 0 1 d i hid]
  rw [if_pos ⟨hlen, hcont⟩]
  exact Nat.succ_pos 0

/-- Off ties the family is its ranking's own. -/
private theorem untied_eq_psiP {d : Nat} {S : List (Nat × Nat)}
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (pairsOf d)))
    (hUT : ¬ 0 < (tiedList d S).length) :
    S = psiP d (rankP d S) := by
  refine Eq.trans (ground.sublists_char (pairsOf d)
    (fun x => pairs_distinct d x) S hS) ?_
  refine ground.filter_congr_mem _ _ (pairsOf d)
    (fun q hq => ?_)
  have h12 := (pairs_mem d q hq).1
  have h2d := (pairs_mem d q hq).2
  have h1d : q.1 < d := Nat.lt_trans h12 h2d
  have ht1 := takeAt_lt S h1d
  have ht2 := takeAt_lt S h2d
  have hbound : d ≤ takeAt d S q.2 + (d + 1) :=
    Nat.le_trans (Nat.le_add_left d (takeAt d S q.2))
      (Nat.add_le_add (Nat.le_refl _)
        (Nat.le_of_lt (Nat.lt_succ_self d)))
  have htour := tourn_go hUT d q.2 h2d hbound q hq q.1
    (Or.inl rfl)
  have hchain : 0 < ground.countOf q S
      ↔ places.posOf q.2 (rankP d S)
        < places.posOf q.1 (rankP d S) := by
    rw [posOf_rankP hUT h2d, posOf_rankP hUT h1d]
    exact Iff.trans (Iff.trans
      (taken_snd_iff S hq).symm htour)
      (subAnti ht1 ht2).symm
  cases hL : ground.containsB S q with
  | true =>
    cases hR : (decide (places.posOf q.2 (rankP d S)
        < places.posOf q.1 (rankP d S)) : Bool) with
    | true => rfl
    | false =>
      exact absurd (decide_eq_true
        (hchain.mp (of_decide_eq_true hL)))
        (ground.boolNe hR)
  | false =>
    cases hR : (decide (places.posOf q.2 (rankP d S)
        < places.posOf q.1 (rankP d S)) : Bool) with
    | true =>
      exact absurd (decide_eq_true
        (hchain.mpr (of_decide_eq_true hR)))
        (ground.boolNe hL)
    | false => rfl

/-- The assignment family is off ties. -/
private theorem psiP_untied {d : Nat} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms d)) :
    ¬ 0 < (tiedList d (psiP d p)).length := by
  intro hT
  have hmem := filter_pos (tiedP d (psiP d p)) (xiP d (psiP d p))
    (pairsOf d) (ground.countOf_getAt_pos (0, 0) (tiedList d (psiP d p)) 0 hT)
  have h12 := (pairs_mem d _ hmem.2).1
  have h2d := (pairs_mem d _ hmem.2).2
  have h1d := Nat.lt_trans h12 h2d
  have htie : takeAt d (psiP d p) (xiP d (psiP d p)).1
      = takeAt d (psiP d p) (xiP d (psiP d p)).2 :=
    of_decide_eq_true hmem.1
  rw [takeAt_psiP_eq hp h1d, takeAt_psiP_eq hp h2d] at htie
  have hk := perm_kit hp
  have hpos1lt : places.posOf (xiP d (psiP d p)).1 p < d := by
    have h := places.posOf_lt _ p (hk.2.1 _ h1d)
    rw [hk.1] at h
    exact h
  have hpos2lt : places.posOf (xiP d (psiP d p)).2 p < d := by
    have h := places.posOf_lt _ p (hk.2.1 _ h2d)
    rw [hk.1] at h
    exact h
  have c1 := ground.natAddSubCancel hpos1lt
  have c2 := ground.natAddSubCancel hpos2lt
  rw [htie] at c1
  have heq : places.posOf (xiP d (psiP d p)).1 p
      = places.posOf (xiP d (psiP d p)).2 p :=
    Nat.succ.inj (ground.addCancelR _ (c1.trans c2.symm))
  exact posOf_inj (hk.2.1 _ h1d) (hk.2.1 _ h2d)
    (fun he => Nat.lt_irrefl (xiP d (psiP d p)).2
      (Nat.lt_of_le_of_lt (Nat.le_of_eq he.symm) h12)) heq

/-- Two assignments at one family are one assignment. -/
private theorem psiP_inj {d : Nat} {p p' : List Nat}
    (hp : 0 < ground.countOf p (places.perms d))
    (hp' : 0 < ground.countOf p' (places.perms d))
    (he : psiP d p = psiP d p') : p = p' := by
  have hk := perm_kit hp
  have hk' := perm_kit hp'
  have hpos : ∀ v, v < d →
      places.posOf v p = places.posOf v p' := by
    intro v hv
    have h1 := takeAt_psiP_eq hp hv
    have h2 := takeAt_psiP_eq hp' hv
    rw [he] at h1
    have h3 : d - (places.posOf v p + 1)
        = d - (places.posOf v p' + 1) := h1.symm.trans h2
    have hl : places.posOf v p < d := by
      have h := places.posOf_lt v p (hk.2.1 v hv)
      rw [hk.1] at h
      exact h
    have hl' : places.posOf v p' < d := by
      have h := places.posOf_lt v p' (hk'.2.1 v hv)
      rw [hk'.1] at h
      exact h
    have c1 := ground.natAddSubCancel hl
    have c2 := ground.natAddSubCancel hl'
    rw [h3] at c1
    exact Nat.succ.inj (ground.addCancelR _ (c1.trans c2.symm))
  refine ground.getAt_ext 0 p p' (by rw [hk.1, hk'.1]) ?_
  intro i hi
  have hx : ground.getAt 0 p i < d :=
    hk.2.2.2 _ (ground.countOf_getAt_pos 0 p i hi)
  have hpx : places.posOf (ground.getAt 0 p i) p = i :=
    places.posOf_getAt hk.2.2.1 i hi
  have hpx' : places.posOf (ground.getAt 0 p i) p' = i := by
    rw [← hpos _ hx]
    exact hpx
  have h := places.getAt_posOf (ground.getAt 0 p i) p'
    (hk'.2.1 _ hx)
  rw [hpx'] at h
  exact h.symm

/-- The off-tie families' graded counts read the assignments'
own. -/
private theorem untied_transport (b : List Nat) (k : Nat)
    (s : Bool) :
    ground.famFold Nat.add 0
      (fun S => if ¬ 0 < (tiedList b.length S).length
          ∧ ((k, s) : Nat × Bool)
            = (keyAt b S, places.sideOf S)
        then (1 : Nat) else 0)
      (ground.sublistsOf (pairsOf b.length))
    = ground.countOf ((k, s) : Nat × Bool)
      ((places.perms b.length).map (fun p =>
        (ground.dotNat (unitDisp b.length) (places.expo b p),
          places.parity p))) := by
  have hsubdist : ∀ x, ground.countOf x
      (ground.sublistsOf (pairsOf b.length)) ≤ 1 :=
    fun x => ground.sublists_count_le (pairsOf b.length)
      (fun t => pairs_distinct b.length t) x
  have hperm_dist : ∀ x, ground.countOf x
      (places.perms b.length) ≤ 1 := fun x => by
    match Nat.eq_zero_or_pos (ground.countOf x
        (places.perms b.length)) with
    | .inl h0 =>
      rw [h0]
      exact Nat.zero_le 1
    | .inr hpos =>
      exact places.monomialsAt_distinct
        (List.replicate b.length 1) x
        (ground.mem_of_countOf_pos x _ hpos)
  have hM1 : ∀ x, 0 < ground.countOf x
        (ground.sublistsOf (pairsOf b.length)) →
      ¬ 0 < (tiedList b.length x).length →
      ground.countOf x ((places.perms b.length).map
        (psiP b.length)) = 1 := by
    intro x hx hUTx
    rw [untied_eq_psiP hx hUTx,
      ground.countOf_map_inj (psiP b.length)
        (rankP b.length x) (places.perms b.length)
        (fun y hy he2 => psiP_inj hy (rankP_perm hUTx) he2)]
    exact Nat.le_antisymm (hperm_dist _) (rankP_perm hUTx)
  have hM0 : ∀ x, 0 < (tiedList b.length x).length →
      ground.countOf x ((places.perms b.length).map
        (psiP b.length)) = 0 := by
    intro x hTx
    refine ground.countOf_map_none (psiP b.length) x
      (places.perms b.length) (fun p hp he2 => ?_)
    refine psiP_untied hp ?_
    rw [he2]
    exact hTx
  rw [ground.countOf_fold ((k, s) : Nat × Bool)
      ((places.perms b.length).map (fun p =>
        (ground.dotNat (unitDisp b.length) (places.expo b p),
          places.parity p))),
    ground.famFold_map Nat.add 0
      (fun x => if ((k, s) : Nat × Bool) = x
        then (1 : Nat) else 0)
      (fun p => (ground.dotNat (unitDisp b.length)
        (places.expo b p), places.parity p))
      (places.perms b.length)]
  refine Eq.trans (ground.famFold_partition _
    (ground.sublistsOf (pairsOf b.length))
    (ground.sublistsOf (pairsOf b.length))
    (fun x _ => hsubdist x) (fun x hx => hx)) ?_
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun x => ground.countOf x ((places.perms b.length).map
        (psiP b.length))
      * (if ¬ 0 < (tiedList b.length x).length
          ∧ ((k, s) : Nat × Bool)
            = (keyAt b x, places.sideOf x)
        then (1 : Nat) else 0))
    (ground.sublistsOf (pairsOf b.length))
    (fun x hx => ?_)) ?_
  · by_cases hT : 0 < (tiedList b.length x).length
    · rw [if_neg (fun hc : (¬ 0 < (tiedList b.length x).length)
          ∧ _ => hc.1 hT),
        Nat.mul_zero, Nat.mul_zero]
    · rw [Nat.le_antisymm (hsubdist x) hx, hM1 x hx hT,
        Nat.one_mul]
  · refine Eq.trans (ground.famFold_partition _
      ((places.perms b.length).map (psiP b.length))
      (ground.sublistsOf (pairsOf b.length))
      (fun x _ => hsubdist x)
      (fun x hx => ?_)).symm ?_
    · match ground.mem_map_of (psiP b.length)
          (places.perms b.length) x hx with
      | ⟨p, hpm, hpe⟩ =>
        rw [← hpe]
        exact ground.mem_of_countOf_pos _ _
          (ground.filter_member _ (pairsOf b.length))
    · rw [ground.famFold_map Nat.add 0 _ (psiP b.length)
        (places.perms b.length)]
      refine ground.famFold_congr_members Nat.add 0 _ _
        (places.perms b.length) (fun p hp2 => ?_)
      show (if ¬ 0 < (tiedList b.length (psiP b.length p)).length
          ∧ ((k, s) : Nat × Bool)
            = (keyAt b (psiP b.length p),
              places.sideOf (psiP b.length p))
        then (1 : Nat) else 0)
        = (if ((k, s) : Nat × Bool)
            = (ground.dotNat (unitDisp b.length)
                (places.expo b p), places.parity p)
          then (1 : Nat) else 0)
      rw [keyAt_psiP hp2, sideOf_psiP hp2]
      by_cases hc : ((k, s) : Nat × Bool)
          = (ground.dotNat (unitDisp b.length)
              (places.expo b p), places.parity p)
      · rw [if_pos (show
            (¬ 0 < (tiedList b.length
              (psiP b.length p)).length)
            ∧ ((k, s) : Nat × Bool)
              = (ground.dotNat (unitDisp b.length)
                  (places.expo b p), places.parity p)
          from ⟨psiP_untied hp2, hc⟩), if_pos hc]
      · rw [if_neg (fun h2 : _ ∧ ((k, s) : Nat × Bool) = _ =>
          hc h2.2), if_neg hc]

/-- The graded counts balance at every key: the tied families
join their exchanges and the off-tie families read the
assignments' own. -/
private theorem key_balance (b : List Nat) (kk : Nat) :
    ground.countOf ((kk, false) : Nat × Bool)
      ((ground.sublistsOf (pairsOf b.length)).map
        (fun S => (keyAt b S, places.sideOf S)))
    + ground.countOf ((kk, true) : Nat × Bool)
      ((places.perms b.length).map (fun p =>
        (ground.dotNat (unitDisp b.length) (places.expo b p),
          places.parity p)))
    = ground.countOf ((kk, true) : Nat × Bool)
      ((ground.sublistsOf (pairsOf b.length)).map
        (fun S => (keyAt b S, places.sideOf S)))
    + ground.countOf ((kk, false) : Nat × Bool)
      ((places.perms b.length).map (fun p =>
        (ground.dotNat (unitDisp b.length) (places.expo b p),
          places.parity p))) := by
  have hsplit : ∀ s : Bool,
      ground.countOf ((kk, s) : Nat × Bool)
        ((ground.sublistsOf (pairsOf b.length)).map
          (fun S => (keyAt b S, places.sideOf S)))
      = ground.famFold Nat.add 0
        (fun S => if 0 < (tiedList b.length S).length
            ∧ ((kk, s) : Nat × Bool)
              = (keyAt b S, places.sideOf S)
          then (1 : Nat) else 0)
        (ground.sublistsOf (pairsOf b.length))
      + ground.famFold Nat.add 0
        (fun S => if ¬ 0 < (tiedList b.length S).length
            ∧ ((kk, s) : Nat × Bool)
              = (keyAt b S, places.sideOf S)
          then (1 : Nat) else 0)
        (ground.sublistsOf (pairsOf b.length)) := by
    intro s
    rw [ground.countOf_fold ((kk, s) : Nat × Bool)
        ((ground.sublistsOf (pairsOf b.length)).map
          (fun S => (keyAt b S, places.sideOf S))),
      ground.famFold_map Nat.add 0
        (fun x => if ((kk, s) : Nat × Bool) = x
          then (1 : Nat) else 0)
        (fun S => (keyAt b S, places.sideOf S))
        (ground.sublistsOf (pairsOf b.length)),
      ← ground.famFold_add_split
        (fun S => if 0 < (tiedList b.length S).length
            ∧ ((kk, s) : Nat × Bool)
              = (keyAt b S, places.sideOf S)
          then (1 : Nat) else 0)
        (fun S => if ¬ 0 < (tiedList b.length S).length
            ∧ ((kk, s) : Nat × Bool)
              = (keyAt b S, places.sideOf S)
          then (1 : Nat) else 0)
        (ground.sublistsOf (pairsOf b.length))]
    refine ground.famFold_congr_all Nat.add 0 _ _ (fun S => ?_)
      (ground.sublistsOf (pairsOf b.length))
    by_cases hT : 0 < (tiedList b.length S).length
    · by_cases hc : ((kk, s) : Nat × Bool)
          = (keyAt b S, places.sideOf S)
      · rw [if_pos hc,
          if_pos (show 0 < (tiedList b.length S).length
              ∧ ((kk, s) : Nat × Bool)
                = (keyAt b S, places.sideOf S)
            from ⟨hT, hc⟩),
          if_neg (fun h2 : (¬ 0 < (tiedList b.length S).length)
              ∧ _ => h2.1 hT)]
      · rw [if_neg hc,
          if_neg (fun h2 : (0 < (tiedList b.length S).length)
              ∧ ((kk, s) : Nat × Bool) = _ => hc h2.2),
          if_neg (fun h2 : (¬ 0 < (tiedList b.length S).length)
              ∧ ((kk, s) : Nat × Bool) = _ => hc h2.2)]
    · by_cases hc : ((kk, s) : Nat × Bool)
          = (keyAt b S, places.sideOf S)
      · rw [if_pos hc,
          if_neg (fun h2 : (0 < (tiedList b.length S).length)
              ∧ _ => hT h2.1),
          if_pos (show (¬ 0 < (tiedList b.length S).length)
              ∧ ((kk, s) : Nat × Bool)
                = (keyAt b S, places.sideOf S)
            from ⟨hT, hc⟩)]
      · rw [if_neg hc,
          if_neg (fun h2 : (0 < (tiedList b.length S).length)
              ∧ ((kk, s) : Nat × Bool) = _ => hc h2.2),
          if_neg (fun h2 : (¬ 0 < (tiedList b.length S).length)
              ∧ ((kk, s) : Nat × Bool) = _ => hc h2.2)]
  rw [hsplit false, hsplit true, tied_balance b kk,
    untied_transport b kk false, untied_transport b kk true,
    Nat.add_assoc, Nat.add_assoc,
    Nat.add_comm (ground.countOf ((kk, false) : Nat × Bool)
      ((places.perms b.length).map (fun p =>
        (ground.dotNat (unitDisp b.length) (places.expo b p),
          places.parity p))))
      (ground.countOf ((kk, true) : Nat × Bool)
        ((places.perms b.length).map (fun p =>
          (ground.dotNat (unitDisp b.length)
            (places.expo b p), places.parity p))))]

/-- The substituted graded sum collects the full monomial against
the pair product: `cor:weyldim`'s one-variable read at a strictly
descending display. -/
private theorem altT_eq {b : List Nat}
    (hd : ∀ i, i + 1 < b.length →
      ground.getAt 0 b (i + 1) < ground.getAt 0 b i) :
    poly.oneValue (altT b)
      (poly.mul (poly.mono (ground.sumNat b)) (vprod b)) := by
  refine poly.oneValue_symm (poly.oneValue_trans
    (poly.mul_congr (poly.mono (ground.sumNat b))
      (vprod_split hd)) ?_)
  refine poly.oneValue_trans (poly.oneValue_symm
    (poly.mul_assoc (poly.mono (ground.sumNat b))
      (poly.mono (sndSum b)) (tfold b))) ?_
  refine poly.oneValue_trans (poly.mul_congr_left
    (poly.mono_mul (ground.sumNat b) (sndSum b)) (tfold b)) ?_
  refine poly.oneValue_trans (poly.mul_congr
    (poly.mono (ground.sumNat b + sndSum b))
    (elim.tpairFold_subsets (gapP b) (pairsOf b.length)
      (fun j => pairs_distinct b.length j))) ?_
  refine poly.oneValue_trans (poly.mul_comm
    (poly.mono (ground.sumNat b + sndSum b))
    (ground.famFold poly.add []
      (fun S => poly.smono (places.sideOf S)
        (ground.famFold Nat.add 0
          (fun j => if 0 < ground.countOf j S then 0
            else gapP b j) (pairsOf b.length)))
      (ground.sublistsOf (pairsOf b.length)))) ?_
  refine poly.oneValue_trans (poly.mul_famFold
    (fun S => poly.smono (places.sideOf S)
      (ground.famFold Nat.add 0
        (fun j => if 0 < ground.countOf j S then 0
          else gapP b j) (pairsOf b.length)))
    (ground.sublistsOf (pairsOf b.length))
    (poly.mono (ground.sumNat b + sndSum b))) ?_
  refine poly.oneValue_trans (poly.foldP_congr_members
    (E := fun S => poly.mul
      (poly.smono (places.sideOf S)
        (ground.famFold Nat.add 0
          (fun j => if 0 < ground.countOf j S then 0
            else gapP b j) (pairsOf b.length)))
      (poly.mono (ground.sumNat b + sndSum b)))
    (E' := fun S => poly.smono (places.sideOf S)
      (keyAt b S))
    (ground.sublistsOf (pairsOf b.length))
    (fun S _ => ?_)) ?_
  · -- per-family: smono(side)(offkey) * mono T ~ smono(side)(keyAt)
    refine poly.oneValue_trans (poly.mul_comm _ _) ?_
    refine poly.oneValue_trans (poly.mono_mul_left
      (ground.sumNat b + sndSum b) _) ?_
    rw [show poly.shiftUp (ground.sumNat b + sndSum b)
        (poly.smono (places.sideOf S)
          (ground.famFold Nat.add 0
            (fun j => if 0 < ground.countOf j S then 0
              else gapP b j) (pairsOf b.length)))
      = poly.smono (places.sideOf S) (keyAt b S) from ?_]
    · exact poly.oneValue_refl _
    · show poly.shiftUp (ground.sumNat b + sndSum b)
        (poly.shiftUp (ground.famFold Nat.add 0
          (fun j => if 0 < ground.countOf j S then 0
            else gapP b j) (pairsOf b.length))
          [ground.signedAt (places.sideOf S)
            (BPair.ofPos .one)]) = _
      rw [poly.shiftUp_shiftUp, key_take hd S]
      rfl
  · -- monoFold_ov at the balance
    exact poly.monoFold_ov (keyAt b) places.sideOf
      (fun p => ground.dotNat (unitDisp b.length)
        (places.expo b p))
      places.parity
      (ground.sublistsOf (pairsOf b.length))
      (places.perms b.length)
      (fun kk => key_balance b kk)

/-- A span content's width is the shape's. -/
private theorem span_content_len {s : Shape} {nu : List Nat}
    (hnu : 0 < ground.countOf nu
      ((blockcount.blockSpan s).map blockcount.HVec.content)) :
    nu.length = s.length := by
  match ground.mem_map_of blockcount.HVec.content (blockcount.blockSpan s)
      nu (ground.mem_of_countOf_pos nu _ hnu) with
  | ⟨v, hv, hve⟩ =>
    rw [← hve]
    exact blockcount.blockSpan_width s v hv

/-- The joint member's key: the content's componentwise join with
the permuted unit display. -/
private def keyJ (s : Shape) (x : List Nat × List Nat) :
    List Nat :=
  List.zipWith (fun a b => a + b) x.2
    (places.expo (unitDisp s.length) x.1)

/-- The permuted unit display's width. -/
private theorem expoU_len {s : Shape} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms s.length)) :
    (places.expo (unitDisp s.length) p).length = s.length := by
  show (p.map _).length = _
  rw [ground.length_map, (perm_kit hp).1]

/-- The joint key's width. -/
private theorem keyJ_len {s : Shape} {p nu : List Nat}
    (hp : 0 < ground.countOf p (places.perms s.length))
    (hnu : nu.length = s.length) :
    (keyJ s (p, nu)).length = s.length := by
  show (List.zipWith (fun a b => a + b) nu
    (places.expo (unitDisp s.length) p)).length = s.length
  exact ground.length_zipWith (fun a b => a + b) nu
    (places.expo (unitDisp s.length) p) s.length hnu
    (expoU_len hp)

/-- The joint key ties back to its content. -/
private theorem tie_keyJ {s : Shape} {p nu : List Nat}
    (hp : 0 < ground.countOf p (places.perms s.length))
    (hnu : nu.length = s.length) :
    ground.tieGap (keyJ s (p, nu))
      (places.expo (unitDisp s.length) p) = some nu := by
  have hly := keyJ_len hp hnu
  refine ground.tieGap_make _ _ _ (by rw [hly, hnu])
    (by rw [hly, expoU_len hp]) ?_
  intro i hi
  have his : i < s.length := by
    rw [← hly]
    exact hi
  show ground.getAt 0 nu i
      + ground.getAt 0 (places.expo (unitDisp s.length) p) i
    = ground.getAt 0 (List.zipWith (fun a b => a + b) nu
        (places.expo (unitDisp s.length) p)) i
  rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) nu
    (places.expo (unitDisp s.length) p) i
    (by rw [hnu]; exact his)
    (by rw [expoU_len hp]; exact his)]

/-- A tied key is the joint key. -/
private theorem keyJ_of_tie {s : Shape} {p nu y : List Nat}
    (hp : 0 < ground.countOf p (places.perms s.length))
    (hnu : nu.length = s.length)
    (ht : ground.tieGap y
      (places.expo (unitDisp s.length) p) = some nu) :
    y = keyJ s (p, nu) := by
  have hr := ground.tieGap_reads y
    (places.expo (unitDisp s.length) p) nu ht
  have hys : y.length = s.length := by
    rw [← hnu, hr.1]
  refine ground.getAt_ext 0 y (keyJ s (p, nu))
    (by rw [hys, keyJ_len hp hnu]) ?_
  intro i hi
  have his : i < s.length := by
    rw [← hys]
    exact hi
  show ground.getAt 0 y i
    = ground.getAt 0 (List.zipWith (fun a b => a + b) nu
        (places.expo (unitDisp s.length) p)) i
  rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) nu
    (places.expo (unitDisp s.length) p) i
    (by rw [hnu]; exact his)
    (by rw [expoU_len hp]; exact his)]
  exact (hr.2.2 i hi).symm

/-- The joint key's degree splits at the two reads. -/
private theorem dot_keyJ {s : Shape} {p nu : List Nat}
    (hp : 0 < ground.countOf p (places.perms s.length))
    (hnu : nu.length = s.length) :
    ground.dotNat (unitDisp s.length) (keyJ s (p, nu))
      = ground.dotNat (unitDisp s.length) nu
        + ground.dotNat (unitDisp s.length)
          (places.expo (unitDisp s.length) p) := by
  have hlU : (unitDisp s.length).length = s.length :=
    places.length_unitDisp s.length
  exact places.dotNat_zipAdd (unitDisp s.length) nu
    (places.expo (unitDisp s.length) p)
    (by rw [hnu, hlU]) (by rw [expoU_len hp, hlU])

/-- The span's content list. -/
private def spanL (s : Shape) : List (List Nat) :=
  (blockcount.blockSpan s).map blockcount.HVec.content

/-- The product's joint carrier: the assignments against the
span's contents. -/
private def prodCar (s : Shape) : List (List Nat × List Nat) :=
  (places.perms s.length).flatMap (fun p =>
    (spanL s).map (fun nu => (p, nu)))

/-- The occupied keys' cover: the joint keys with the shifted
alternant's own, deduplicated. -/
private def keyList (s : Shape) : List (List Nat) :=
  ground.dedupL (((prodCar s).map (keyJ s))
    ++ ((places.perms s.length).map
      (places.expo (display s))))

/-- The keys' distinct cover reads each once. -/
private theorem keyList_dist (s : Shape) :
    ∀ y, ground.countOf y (keyList s) ≤ 1 :=
  fun y => ground.countOf_dedupL_le y _

/-- A joint member's key joins the cover once. -/
private theorem keyJ_in_KL {s : Shape} {x : List Nat × List Nat}
    (hx : 0 < ground.countOf x (prodCar s)) :
    ground.countOf (keyJ s x) (keyList s) = 1 := by
  refine Nat.le_antisymm (keyList_dist s _) ?_
  refine ground.countOf_pos_of_mem (ground.mem_dedupL ?_)
  refine ground.mem_of_countOf_pos _ _ ?_
  rw [ground.countOf_append]
  refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
  exact ground.countOf_pos_of_mem (ground.mem_map_to (keyJ s)
    (ground.mem_of_countOf_pos x _ hx))

/-- A shifted key joins the cover once. -/
private theorem expoD_in_KL {s : Shape} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms s.length)) :
    ground.countOf (places.expo (display s) p) (keyList s)
      = 1 := by
  refine Nat.le_antisymm (keyList_dist s _) ?_
  refine ground.countOf_pos_of_mem (ground.mem_dedupL ?_)
  refine ground.mem_of_countOf_pos _ _ ?_
  rw [ground.countOf_append]
  refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _ _)
  exact ground.countOf_pos_of_mem (ground.mem_map_to
    (places.expo (display s))
    (ground.mem_of_countOf_pos p _ hp))

/-- The per-assignment content fold reads the tie's multiplicity
under the degree and grading guards. -/
private theorem innerL_read {s : Shape} {p : List Nat}
    (hp : 0 < ground.countOf p (places.perms s.length))
    (y : List Nat) (n : Nat) (s2 : Bool) :
    ground.famFold Nat.add 0
      (fun nu => if y = keyJ s (p, nu)
        then (if ((n, s2) : Nat × Bool)
          = (ground.dotNat (unitDisp s.length) nu
            + ground.dotNat (unitDisp s.length)
              (places.expo (unitDisp s.length) p),
            places.parity p)
          then (1 : Nat) else 0)
        else 0)
      (spanL s)
    = (if ground.dotNat (unitDisp s.length) y = n
      then (if places.parity p = s2
        then weylchar.multAtGap
          (fun chi => ground.countOf chi (spanL s)) y
          (places.expo (unitDisp s.length) p)
        else 0)
      else 0) := by
  by_cases hpar : places.parity p = s2
  · by_cases hdot : ground.dotNat (unitDisp s.length) y = n
    · rw [if_pos hdot, if_pos hpar]
      cases htie : ground.tieGap y
          (places.expo (unitDisp s.length) p) with
      | some nu0 =>
        have hmm : weylchar.multAtGap
            (fun chi => ground.countOf chi (spanL s)) y
            (places.expo (unitDisp s.length) p)
            = ground.countOf nu0 (spanL s) := by
          show (match ground.tieGap y
              (places.expo (unitDisp s.length) p) with
            | some nu => ground.countOf nu (spanL s)
            | none => 0) = _
          rw [htie]
        rw [hmm, ground.countOf_fold nu0 (spanL s)]
        refine ground.famFold_congr_members Nat.add 0 _ _
          (spanL s) (fun nu hnu => ?_)
        by_cases hk : y = keyJ s (p, nu)
        · have ht := tie_keyJ hp (span_content_len hnu)
          rw [← hk] at ht
          have hnn : nu = nu0 := Option.some.inj
            (ht.symm.trans htie)
          rw [if_pos hk,
            if_pos (show ((n, s2) : Nat × Bool)
                = (ground.dotNat (unitDisp s.length) nu
                  + ground.dotNat (unitDisp s.length)
                    (places.expo (unitDisp s.length) p),
                  places.parity p) from by
              rw [← hdot, ← hpar, hk,
                dot_keyJ hp (span_content_len hnu)]),
            if_pos (hnn.symm)]
        · rw [if_neg hk,
            if_neg (fun he : nu0 = nu => hk (by
              have h2 := keyJ_of_tie hp
                (by rw [he]; exact span_content_len hnu) htie
              rw [he] at h2
              exact h2))]
      | none =>
        have hmm : weylchar.multAtGap
            (fun chi => ground.countOf chi (spanL s)) y
            (places.expo (unitDisp s.length) p) = 0 := by
          show (match ground.tieGap y
              (places.expo (unitDisp s.length) p) with
            | some nu => ground.countOf nu (spanL s)
            | none => 0) = _
          rw [htie]
        rw [hmm]
        refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
          (fun _ => (0 : Nat)) (spanL s) (fun nu hnu => ?_))
          (ground.famFold_zero (fun _ => (0 : Nat))
            (fun _ => rfl) _)
        rw [if_neg (fun hk : y = keyJ s (p, nu) => by
          have ht := tie_keyJ hp (span_content_len hnu)
          rw [← hk, htie] at ht
          exact nomatch ht)]
    · rw [if_neg hdot]
      refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
        (fun _ => (0 : Nat)) (spanL s) (fun nu hnu => ?_))
        (ground.famFold_zero (fun _ => (0 : Nat))
          (fun _ => rfl) _)
      by_cases hk : y = keyJ s (p, nu)
      · rw [if_pos hk,
          if_neg (fun hc : ((n, s2) : Nat × Bool) = _ => hdot (by
            have h1 : n = ground.dotNat (unitDisp s.length) nu
                + ground.dotNat (unitDisp s.length)
                  (places.expo (unitDisp s.length) p) :=
              congrArg Prod.fst hc
            rw [hk, dot_keyJ hp (span_content_len hnu)]
            exact h1.symm))]
      · rw [if_neg hk]
  · have hz : ∀ nu : List Nat,
        (if y = keyJ s (p, nu)
          then (if ((n, s2) : Nat × Bool)
            = (ground.dotNat (unitDisp s.length) nu
              + ground.dotNat (unitDisp s.length)
                (places.expo (unitDisp s.length) p),
              places.parity p)
            then (1 : Nat) else 0)
          else 0) = 0 := by
      intro nu
      by_cases hk : y = keyJ s (p, nu)
      · rw [if_pos hk,
          if_neg (fun hc : ((n, s2) : Nat × Bool) = _ =>
            hpar (congrArg Prod.snd hc).symm)]
      · rw [if_neg hk]
    rw [ground.famFold_congr_all Nat.add 0 _ (fun _ => (0 : Nat))
        hz (spanL s),
      ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) _]
    by_cases hdot : ground.dotNat (unitDisp s.length) y = n
    · rw [if_pos hdot, if_neg hpar]
    · rw [if_neg hdot]

/-- The joint carrier's graded count regroups over the key
cover. -/
private theorem cntJ_regroup (s : Shape) (n : Nat) (s2 : Bool) :
    ground.countOf ((n, s2) : Nat × Bool)
      ((prodCar s).map (fun x =>
        (ground.dotNat (unitDisp s.length) x.2
          + ground.dotNat (unitDisp s.length)
            (places.expo (unitDisp s.length) x.1),
          places.parity x.1)))
    = ground.famFold Nat.add 0
      (fun y => if ground.dotNat (unitDisp s.length) y = n
        then weylchar.prodCount
          (fun chi => ground.countOf chi (spanL s))
          s.length y s2
        else 0)
      (keyList s) := by
  rw [ground.countOf_fold ((n, s2) : Nat × Bool)
      ((prodCar s).map (fun x =>
        (ground.dotNat (unitDisp s.length) x.2
          + ground.dotNat (unitDisp s.length)
            (places.expo (unitDisp s.length) x.1),
          places.parity x.1))),
    ground.famFold_map Nat.add 0
      (fun z => if ((n, s2) : Nat × Bool) = z
        then (1 : Nat) else 0)
      (fun x => (ground.dotNat (unitDisp s.length) x.2
        + ground.dotNat (unitDisp s.length)
          (places.expo (unitDisp s.length) x.1),
        places.parity x.1))
      (prodCar s),
    ground.famFold_congr_members Nat.add 0 _
      (fun x => ground.famFold Nat.add 0
        (fun y => if y = keyJ s x
          then (if ((n, s2) : Nat × Bool)
            = (ground.dotNat (unitDisp s.length) x.2
              + ground.dotNat (unitDisp s.length)
                (places.expo (unitDisp s.length) x.1),
              places.parity x.1)
            then (1 : Nat) else 0)
          else 0)
        (keyList s))
      (prodCar s)
      (fun x hx => (ground.famFold_pick
        (fun _ => if ((n, s2) : Nat × Bool)
          = (ground.dotNat (unitDisp s.length) x.2
            + ground.dotNat (unitDisp s.length)
              (places.expo (unitDisp s.length) x.1),
            places.parity x.1)
          then (1 : Nat) else 0)
        (keyJ s x) (keyList s) (keyJ_in_KL hx)).symm),
    ground.famFold_swap
      (fun x y => if y = keyJ s x
        then (if ((n, s2) : Nat × Bool)
          = (ground.dotNat (unitDisp s.length) x.2
            + ground.dotNat (unitDisp s.length)
              (places.expo (unitDisp s.length) x.1),
            places.parity x.1)
          then (1 : Nat) else 0)
        else 0)
      (prodCar s) (keyList s)]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (keyList s) (fun y hy => ?_)
  rw [show prodCar s = (places.perms s.length).flatMap
      (fun p => (spanL s).map (fun nu => (p, nu))) from rfl,
    ground.famFold_flatMap _
      (fun p => (spanL s).map (fun nu => (p, nu)))
      (places.perms s.length)]
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun p => if ground.dotNat (unitDisp s.length) y = n
      then (if places.parity p = s2
        then weylchar.multAtGap
          (fun chi => ground.countOf chi (spanL s)) y
          (places.expo (unitDisp s.length) p)
        else 0)
      else 0)
    (places.perms s.length) (fun p hp2 => ?_)) ?_
  · rw [ground.famFold_map Nat.add 0 _ (fun nu => (p, nu))
      (spanL s)]
    exact innerL_read hp2 y n s2
  · by_cases hdot : ground.dotNat (unitDisp s.length) y = n
    · rw [if_pos hdot]
      refine Eq.trans (ground.famFold_congr_all Nat.add 0 _
        (fun p => if places.parity p = s2
          then weylchar.multAtGap
            (fun chi => ground.countOf chi (spanL s)) y
            (places.expo (unitDisp s.length) p)
          else 0)
        (fun p => by rw [if_pos hdot])
        (places.perms s.length)) ?_
      rfl
    · rw [if_neg hdot]
      refine Eq.trans (ground.famFold_congr_all Nat.add 0 _
        (fun _ => (0 : Nat))
        (fun p => by rw [if_neg hdot])
        (places.perms s.length)) ?_
      exact ground.famFold_zero (fun _ => (0 : Nat))
        (fun _ => rfl) _

/-- The shifted alternant's graded count regroups over the key
cover. -/
private theorem cntL_regroup (s : Shape) (n : Nat) (s2 : Bool) :
    ground.countOf ((n, s2) : Nat × Bool)
      ((places.perms s.length).map (fun p =>
        (ground.dotNat (unitDisp s.length)
          (places.expo (display s) p), places.parity p)))
    = ground.famFold Nat.add 0
      (fun y => if ground.dotNat (unitDisp s.length) y = n
        then weylchar.sideCount s.length (display s) y s2
        else 0)
      (keyList s) := by
  rw [ground.countOf_fold ((n, s2) : Nat × Bool)
      ((places.perms s.length).map (fun p =>
        (ground.dotNat (unitDisp s.length)
          (places.expo (display s) p), places.parity p))),
    ground.famFold_map Nat.add 0
      (fun z => if ((n, s2) : Nat × Bool) = z
        then (1 : Nat) else 0)
      (fun p => (ground.dotNat (unitDisp s.length)
        (places.expo (display s) p), places.parity p))
      (places.perms s.length),
    ground.famFold_congr_members Nat.add 0 _
      (fun p => ground.famFold Nat.add 0
        (fun y => if y = places.expo (display s) p
          then (if ((n, s2) : Nat × Bool)
            = (ground.dotNat (unitDisp s.length)
                (places.expo (display s) p), places.parity p)
            then (1 : Nat) else 0)
          else 0)
        (keyList s))
      (places.perms s.length)
      (fun p hp => (ground.famFold_pick
        (fun _ => if ((n, s2) : Nat × Bool)
          = (ground.dotNat (unitDisp s.length)
              (places.expo (display s) p), places.parity p)
          then (1 : Nat) else 0)
        (places.expo (display s) p) (keyList s)
        (expoD_in_KL hp)).symm),
    ground.famFold_swap
      (fun p y => if y = places.expo (display s) p
        then (if ((n, s2) : Nat × Bool)
          = (ground.dotNat (unitDisp s.length)
              (places.expo (display s) p), places.parity p)
          then (1 : Nat) else 0)
        else 0)
      (places.perms s.length) (keyList s)]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (keyList s) (fun y hy => ?_)
  by_cases hdot : ground.dotNat (unitDisp s.length) y = n
  · rw [if_pos hdot]
    refine Eq.trans (ground.famFold_congr_all Nat.add 0 _
      (fun p => if places.parity p = s2
        then (if places.expo (display s) p = y
          then (1 : Nat) else 0)
        else 0)
      (fun p => ?_) (places.perms s.length)) ?_
    · by_cases hk : y = places.expo (display s) p
      · rw [if_pos hk]
        by_cases hpar : places.parity p = s2
        · rw [if_pos (show ((n, s2) : Nat × Bool)
              = (ground.dotNat (unitDisp s.length)
                  (places.expo (display s) p),
                places.parity p) from by
              rw [← hk, hdot, ← hpar]),
            if_pos hpar, if_pos hk.symm]
        · rw [if_neg (fun hc : ((n, s2) : Nat × Bool) = _ =>
              hpar (congrArg Prod.snd hc).symm),
            if_neg hpar]
      · rw [if_neg hk]
        by_cases hpar : places.parity p = s2
        · rw [if_pos hpar,
            if_neg (fun he : places.expo (display s) p = y =>
              hk he.symm)]
        · rw [if_neg hpar]
    · rfl
  · rw [if_neg hdot]
    refine Eq.trans (ground.famFold_congr_all Nat.add 0 _
      (fun _ => (0 : Nat)) (fun p => ?_)
      (places.perms s.length)) ?_
    · by_cases hk : y = places.expo (display s) p
      · rw [if_pos hk,
          if_neg (fun hc : ((n, s2) : Nat × Bool) = _ => hdot (by
            have h1 : n = ground.dotNat (unitDisp s.length)
                (places.expo (display s) p) :=
              congrArg Prod.fst hc
            rw [hk]
            exact h1.symm))]
      · rw [if_neg hk]
    · exact ground.famFold_zero (fun _ => (0 : Nat))
        (fun _ => rfl) _

/-- The identity's balance transports to the degree reads. -/
private theorem transported_balance (s : Shape) (n : Nat) :
    ground.countOf ((n, false) : Nat × Bool)
      ((prodCar s).map (fun x =>
        (ground.dotNat (unitDisp s.length) x.2
          + ground.dotNat (unitDisp s.length)
            (places.expo (unitDisp s.length) x.1),
          places.parity x.1)))
    + ground.countOf ((n, true) : Nat × Bool)
      ((places.perms s.length).map (fun p =>
        (ground.dotNat (unitDisp s.length)
          (places.expo (display s) p), places.parity p)))
    = ground.countOf ((n, true) : Nat × Bool)
      ((prodCar s).map (fun x =>
        (ground.dotNat (unitDisp s.length) x.2
          + ground.dotNat (unitDisp s.length)
            (places.expo (unitDisp s.length) x.1),
          places.parity x.1)))
    + ground.countOf ((n, false) : Nat × Bool)
      ((places.perms s.length).map (fun p =>
        (ground.dotNat (unitDisp s.length)
          (places.expo (display s) p), places.parity p))) := by
  rw [cntJ_regroup s n false, cntJ_regroup s n true,
    cntL_regroup s n true, cntL_regroup s n false,
    ← ground.famFold_add_split
      (fun y => if ground.dotNat (unitDisp s.length) y = n
        then weylchar.prodCount
          (fun chi => ground.countOf chi (spanL s))
          s.length y false
        else 0)
      (fun y => if ground.dotNat (unitDisp s.length) y = n
        then weylchar.sideCount s.length (display s) y true
        else 0)
      (keyList s),
    ← ground.famFold_add_split
      (fun y => if ground.dotNat (unitDisp s.length) y = n
        then weylchar.prodCount
          (fun chi => ground.countOf chi (spanL s))
          s.length y true
        else 0)
      (fun y => if ground.dotNat (unitDisp s.length) y = n
        then weylchar.sideCount s.length (display s) y false
        else 0)
      (keyList s)]
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun y => ?_)
    (keyList s)
  have hid := weylchar.identityRead s (spanL s)
    (casimir.recRead_def s) (strings.symRead_def s)
    (lowerspan.supportRead_def s) (lowerspan.topRead_def s) y
  by_cases hdot : ground.dotNat (unitDisp s.length) y = n
  · rw [if_pos hdot, if_pos hdot, if_pos hdot, if_pos hdot]
    exact hid
  · rw [if_neg hdot, if_neg hdot, if_neg hdot, if_neg hdot]

/-- The character's transport: the unit alternant's product with
the span's content sum reads the shifted alternant. -/
private theorem chT_transport (s : Shape) :
    poly.oneValue
      (poly.mul (altT (unitDisp s.length))
        (chTL s.length (spanL s)))
      (altT (display s)) := by
  have hlU : (unitDisp s.length).length = s.length :=
    places.length_unitDisp s.length
  have haU : altT (unitDisp s.length)
      = ground.famFold poly.add []
        (fun p => poly.smono (places.parity p)
          (ground.dotNat (unitDisp s.length)
            (places.expo (unitDisp s.length) p)))
        (places.perms s.length) := by
    show ground.famFold poly.add []
      (fun p => poly.smono (places.parity p)
        (ground.dotNat (unitDisp (unitDisp s.length).length)
          (places.expo (unitDisp s.length) p)))
      (places.perms (unitDisp s.length).length) = _
    rw [hlU]
  have haD : altT (display s)
      = ground.famFold poly.add []
        (fun p => poly.smono (places.parity p)
          (ground.dotNat (unitDisp s.length)
            (places.expo (display s) p)))
        (places.perms s.length) := by
    show ground.famFold poly.add []
      (fun p => poly.smono (places.parity p)
        (ground.dotNat (unitDisp (display s).length)
          (places.expo (display s) p)))
      (places.perms (display s).length) = _
    rw [places.length_display]
  rw [haU, haD]
  refine poly.oneValue_trans (poly.mul_famFold
    (fun p => poly.smono (places.parity p)
      (ground.dotNat (unitDisp s.length)
        (places.expo (unitDisp s.length) p)))
    (places.perms s.length)
    (chTL s.length (spanL s))) ?_
  refine poly.oneValue_trans (poly.foldP_congr_members
    (E := fun p => poly.mul
      (poly.smono (places.parity p)
        (ground.dotNat (unitDisp s.length)
          (places.expo (unitDisp s.length) p)))
      (chTL s.length (spanL s)))
    (E' := fun p => ground.famFold poly.add []
      (fun x : List Nat × List Nat =>
        poly.smono (places.parity x.1)
          (ground.dotNat (unitDisp s.length) x.2
            + ground.dotNat (unitDisp s.length)
              (places.expo (unitDisp s.length) x.1)))
      ((spanL s).map (fun nu => (p, nu))))
    (places.perms s.length)
    (fun p _ => ?_)) ?_
  · refine poly.oneValue_trans (poly.mul_comm _ _) ?_
    refine poly.oneValue_trans (poly.mul_famFold
      (fun nu => poly.mono
        (ground.dotNat (unitDisp s.length) nu))
      (spanL s)
      (poly.smono (places.parity p)
        (ground.dotNat (unitDisp s.length)
          (places.expo (unitDisp s.length) p)))) ?_
    rw [ground.famFold_map poly.add []
      (fun x : List Nat × List Nat =>
        poly.smono (places.parity x.1)
          (ground.dotNat (unitDisp s.length) x.2
            + ground.dotNat (unitDisp s.length)
              (places.expo (unitDisp s.length) x.1)))
      (fun nu => (p, nu)) (spanL s)]
    refine poly.foldP_congr_members _ _ (spanL s) (fun nu _ => ?_)
    refine poly.oneValue_trans (poly.mono_mul_left
      (ground.dotNat (unitDisp s.length) nu)
      (poly.smono (places.parity p)
        (ground.dotNat (unitDisp s.length)
          (places.expo (unitDisp s.length) p)))) ?_
    rw [show poly.shiftUp
        (ground.dotNat (unitDisp s.length) nu)
        (poly.smono (places.parity p)
          (ground.dotNat (unitDisp s.length)
            (places.expo (unitDisp s.length) p)))
      = poly.smono (places.parity p)
        (ground.dotNat (unitDisp s.length) nu
          + ground.dotNat (unitDisp s.length)
            (places.expo (unitDisp s.length) p)) from by
      show poly.shiftUp _ (poly.shiftUp _ _) = _
      rw [poly.shiftUp_shiftUp]
      rfl]
    exact poly.oneValue_refl _
  · refine poly.oneValue_trans (poly.oneValue_symm
      (poly.foldP_flatMap
        (fun x : List Nat × List Nat =>
          poly.smono (places.parity x.1)
            (ground.dotNat (unitDisp s.length) x.2
              + ground.dotNat (unitDisp s.length)
                (places.expo (unitDisp s.length) x.1)))
        (fun p => (spanL s).map (fun nu => (p, nu)))
        (places.perms s.length))) ?_
    exact poly.monoFold_ov
      (fun x : List Nat × List Nat =>
        ground.dotNat (unitDisp s.length) x.2
          + ground.dotNat (unitDisp s.length)
            (places.expo (unitDisp s.length) x.1))
      (fun x => places.parity x.1)
      (fun p => ground.dotNat (unitDisp s.length)
        (places.expo (display s) p))
      places.parity
      (prodCar s) (places.perms s.length)
      (fun n => transported_balance s n)

/-- An occupied place pair's display gap is positive at a strictly
descending display. -/
private theorem gapP_pos {b : List Nat}
    (hd : ∀ i, i + 1 < b.length →
      ground.getAt 0 b (i + 1) < ground.getAt 0 b i)
    {q : Nat × Nat}
    (hq : 0 < ground.countOf q (pairsOf b.length)) :
    0 < gapP b q := by
  match pairs_mem b.length q hq with
  | ⟨h1, h2⟩ =>
    have hlt : ground.getAt 0 b q.2 < ground.getAt 0 b q.1 :=
      desc_lt hd q.2 q.1 h1 h2
    match Nat.eq_zero_or_pos (gapP b q) with
    | .inr hp => exact hp
    | .inl h0 =>
      have hc : ground.getAt 0 b q.2 + gapP b q
          = ground.getAt 0 b q.1 :=
        ground.natAddSubCancel (Nat.le_of_lt hlt)
      rw [h0, Nat.add_zero] at hc
      exact absurd hlt (by rw [hc]; exact Nat.lt_irrefl _)

/-- The display gap product collects over the place pairs. -/
private theorem gapProd_pairs : ∀ b : List Nat,
    gapProd b
      = ground.famFold Nat.mul 1 (gapP b) (pairsOf b.length)
  | [] => rfl
  | x :: t => by
    show ground.famFold Nat.mul 1 (fun y => x - y) t * gapProd t
      = ground.famFold Nat.mul 1 (gapP (x :: t))
        (pairsOf (t.length + 1))
    rw [ground.famFold_relist Nat.mul 1 Nat.mul_comm ground.mulAssoc
        (gapP (x :: t)) (pairsOf (t.length + 1))
        ((List.range t.length).map
            (fun k => ((0, k + 1) : Nat × Nat))
          ++ (pairsOf t.length).map
            (fun r => ((r.1 + 1, r.2 + 1) : Nat × Nat)))
        (places.countOf_pairs_split t.length),
      ground.famFold_append Nat.mul 1 ground.mulAssoc Nat.one_mul
        (gapP (x :: t)) _ _,
      ground.famFold_map Nat.mul 1 (gapP (x :: t))
        (fun k => ((0, k + 1) : Nat × Nat)) (List.range t.length),
      ground.famFold_map Nat.mul 1 (gapP (x :: t))
        (fun r => ((r.1 + 1, r.2 + 1) : Nat × Nat))
        (pairsOf t.length),
      show ground.famFold Nat.mul 1
          (fun k => gapP (x :: t) ((0, k + 1) : Nat × Nat))
          (List.range t.length)
        = ground.famFold Nat.mul 1
          (fun k => x - ground.getAt 0 t k)
          (List.range t.length) from rfl,
      show ground.famFold Nat.mul 1
          (fun r => gapP (x :: t) ((r.1 + 1, r.2 + 1) : Nat × Nat))
          (pairsOf t.length)
        = ground.famFold Nat.mul 1 (gapP t) (pairsOf t.length)
        from rfl,
      ground.famFold_getAt Nat.mul 1 (fun y => x - y) 0 t
        t.length rfl,
      gapProd_pairs t]
    rfl

/-- A product fold at positive entries is positive. -/
private theorem mulFold_pos {α : Type} [DecidableEq α]
    (g : α → Nat) :
    ∀ l : List α, (∀ x, 0 < ground.countOf x l → 0 < g x) →
      0 < ground.famFold Nat.mul 1 g l
  | [], _ => Nat.lt_succ_self 0
  | a :: t, h => by
    show 0 < g a * ground.famFold Nat.mul 1 g t
    exact Nat.mul_pos
      (h a (by rw [ground.countOf_head]; exact Nat.succ_pos _))
      (mulFold_pos g t (fun x hx => h x (ground.countOf_cons_pos hx)))

/-- The unit display's gap product is positive: the display's
gaps are occupied at every place pair of the unit shape. -/
theorem gapProdU_pos (s : Shape) :
    0 < gapProd (display (List.replicate s.length 0)) := by
  have hpos : 0 < ground.famFold Nat.mul 1
      (gapP (unitDisp s.length))
      (pairsOf (unitDisp s.length).length) :=
    mulFold_pos (gapP (unitDisp s.length))
      (pairsOf (unitDisp s.length).length)
      (fun q hq => gapP_pos (unitDisp_desc s.length) hq)
  rw [← gapProd_pairs (unitDisp s.length)] at hpos
  exact hpos

/-- The graded sum splits at the unit-gap powers: the signed fold
reads the monic power against the joined monomial and the
geometric words. -/
private theorem altT_gsplit {b : List Nat}
    (hd : ∀ i, i + 1 < b.length →
      ground.getAt 0 b (i + 1) < ground.getAt 0 b i) :
    poly.oneValue (altT b)
      (poly.mul (poly.powOf (poly.tpair 1) (pairsOf b.length).length)
        (poly.mul (poly.mono (ground.sumNat b + sndSum b))
          (ground.famFold poly.mul poly.one
            (fun q => poly.gword (gapP b q))
            (pairsOf b.length)))) := by
  refine poly.oneValue_trans (altT_eq hd) ?_
  refine poly.oneValue_trans
    (poly.mul_congr (poly.mono (ground.sumNat b))
      (vprod_split hd)) ?_
  refine poly.oneValue_trans (poly.oneValue_symm
    (poly.mul_assoc (poly.mono (ground.sumNat b))
      (poly.mono (sndSum b)) (tfold b))) ?_
  refine poly.oneValue_trans (poly.mul_congr_left
    (poly.mono_mul (ground.sumNat b) (sndSum b)) (tfold b)) ?_
  refine poly.oneValue_trans
    (poly.mul_congr (poly.mono (ground.sumNat b + sndSum b))
      (poly.tpairFold_split (gapP b) (pairsOf b.length)
        (fun q hq => gapP_pos hd hq))) ?_
  refine poly.oneValue_trans (poly.oneValue_symm
    (poly.mul_assoc (poly.mono (ground.sumNat b + sndSum b))
      (poly.powOf (poly.tpair 1) (pairsOf b.length).length)
      (ground.famFold poly.mul poly.one
        (fun q => poly.gword (gapP b q)) (pairsOf b.length)))) ?_
  refine poly.oneValue_trans (poly.mul_congr_left
    (poly.mul_comm (poly.mono (ground.sumNat b + sndSum b))
      (poly.powOf (poly.tpair 1) (pairsOf b.length).length))
    (ground.famFold poly.mul poly.one
      (fun q => poly.gword (gapP b q)) (pairsOf b.length))) ?_
  exact poly.mul_assoc _ _ _

/-- The substituted content sum reads the span's count at the
natural one. -/
private theorem eval_chTL_one (d : Nat) : ∀ L : List (List Nat),
    (poly.eval (chTL d L) (BPair.ofNat 1)).oneValue
      (BPair.ofNat L.length)
  | [] => BPair.oneValue_refl _
  | nu :: L => by
    show (poly.eval
        (poly.add (poly.mono (dotNat (unitDisp d) nu)) (chTL d L))
        (BPair.ofNat 1)).oneValue
      (BPair.ofNat (L.length + 1))
    refine BPair.oneValue_trans
      (poly.eval_add (poly.mono (dotNat (unitDisp d) nu)) (chTL d L)
        (BPair.ofNat 1)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (poly.eval_mono_one (dotNat (unitDisp d) nu))
        (eval_chTL_one d L)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq
      (BPair.add_comm (BPair.ofNat 1) (BPair.ofNat L.length))) ?_
    exact BPair.oneValue_symm (BPair.ofNat_succ L.length)

/-- The transport collects to the count identity: the unit
display's pair-gap product against the span's count reads the
shape's own. -/
private theorem span_count (s : Shape) :
    ground.famFold Nat.mul 1 (gapP (unitDisp s.length))
        (pairsOf s.length)
      * (spanL s).length
    = ground.famFold Nat.mul 1 (gapP (display s))
        (pairsOf s.length) := by
  have hdD : ∀ i, i + 1 < (display s).length →
      ground.getAt 0 (display s) (i + 1)
        < ground.getAt 0 (display s) i := by
    intro i hi
    rw [places.length_display] at hi
    exact places.display_desc s i hi
  have hU := altT_gsplit (unitDisp_desc s.length)
  have hD := altT_gsplit hdD
  rw [places.length_unitDisp s.length] at hU
  rw [places.length_display] at hD
  have h1 := poly.oneValue_trans
    (poly.mul_congr_left (poly.oneValue_symm hU)
      (chTL s.length (spanL s)))
    (poly.oneValue_trans (chT_transport s) hD)
  have h2 := poly.oneValue_trans
    (poly.oneValue_symm (poly.mul_assoc _ _ _)) h1
  have hmon := poly.powOf_congr poly.tpair_monic
    (pairsOf s.length).length
  have hcanc : poly.oneValue
      (poly.mul
        (poly.mul (poly.mono (ground.sumNat (unitDisp s.length)
            + sndSum (unitDisp s.length)))
          (ground.famFold poly.mul poly.one
            (fun q => poly.gword (gapP (unitDisp s.length) q))
            (pairsOf s.length)))
        (chTL s.length (spanL s)))
      (poly.mul (poly.mono (ground.sumNat (display s)
          + sndSum (display s)))
        (ground.famFold poly.mul poly.one
          (fun q => poly.gword (gapP (display s) q))
          (pairsOf s.length))) := by
    refine poly.powOf_cancel_monic [BPair.swap (BPair.ofPos .one)]
      (pairsOf s.length).length ?_
    refine poly.oneValue_trans
      (poly.mul_congr _ (poly.oneValue_symm hmon)) ?_
    refine poly.oneValue_trans (poly.mul_comm _ _) ?_
    refine poly.oneValue_trans h2 ?_
    refine poly.oneValue_trans (poly.mul_comm _ _) ?_
    exact poly.mul_congr _ hmon
  have heval := poly.eval_congr hcanc (BPair.ofNat 1)
  have hRU : (poly.eval
      (poly.mul (poly.mono (ground.sumNat (unitDisp s.length)
          + sndSum (unitDisp s.length)))
        (ground.famFold poly.mul poly.one
          (fun q => poly.gword (gapP (unitDisp s.length) q))
          (pairsOf s.length)))
      (BPair.ofNat 1)).oneValue
      (BPair.ofNat (ground.famFold Nat.mul 1
        (gapP (unitDisp s.length)) (pairsOf s.length))) := by
    refine BPair.oneValue_trans
      (poly.eval_mul _ _ (BPair.ofNat 1)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (poly.eval_mono_one _)
        (poly.eval_gwordFold_one (gapP (unitDisp s.length))
          (pairsOf s.length))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
    exact BPair.mul_ofNat_one _
  have hRD : (poly.eval
      (poly.mul (poly.mono (ground.sumNat (display s)
          + sndSum (display s)))
        (ground.famFold poly.mul poly.one
          (fun q => poly.gword (gapP (display s) q))
          (pairsOf s.length)))
      (BPair.ofNat 1)).oneValue
      (BPair.ofNat (ground.famFold Nat.mul 1
        (gapP (display s)) (pairsOf s.length))) := by
    refine BPair.oneValue_trans
      (poly.eval_mul _ _ (BPair.ofNat 1)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (poly.eval_mono_one _)
        (poly.eval_gwordFold_one (gapP (display s))
          (pairsOf s.length))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
    exact BPair.mul_ofNat_one _
  have hL : (poly.eval
      (poly.mul
        (poly.mul (poly.mono (ground.sumNat (unitDisp s.length)
            + sndSum (unitDisp s.length)))
          (ground.famFold poly.mul poly.one
            (fun q => poly.gword (gapP (unitDisp s.length) q))
            (pairsOf s.length)))
        (chTL s.length (spanL s)))
      (BPair.ofNat 1)).oneValue
      (BPair.ofNat (ground.famFold Nat.mul 1
          (gapP (unitDisp s.length)) (pairsOf s.length)
        * (spanL s).length)) := by
    refine BPair.oneValue_trans
      (poly.eval_mul _ _ (BPair.ofNat 1)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr hRU (eval_chTL_one s.length (spanL s))) ?_
    exact BPair.oneValue_symm (BPair.ofNat_mul _ _)
  have hnat : (BPair.ofNat (ground.famFold Nat.mul 1
      (gapP (unitDisp s.length)) (pairsOf s.length)
      * (spanL s).length)).oneValue
      (BPair.ofNat (ground.famFold Nat.mul 1
        (gapP (display s)) (pairsOf s.length))) :=
    BPair.oneValue_trans (BPair.oneValue_symm hL)
      (BPair.oneValue_trans heval hRD)
  exact BPair.ofNat_inj hnat

/-- `cor:weyldim`'s A-series count identity: the span's count
against the unit display's gap product is the shape's own gap
product. -/
theorem spanProd (s : Shape) :
    (blockcount.blockSpan s).length
      * gapProd (display (List.replicate s.length 0))
    = gapProd (display s) := by
  have hgU : gapProd (display (List.replicate s.length 0))
      = ground.famFold Nat.mul 1 (gapP (unitDisp s.length))
        (pairsOf s.length) := by
    have h0 := gapProd_pairs (unitDisp s.length)
    rw [places.length_unitDisp s.length] at h0
    exact h0
  have hgD : gapProd (display s)
      = ground.famFold Nat.mul 1 (gapP (display s))
        (pairsOf s.length) := by
    have h0 := gapProd_pairs (display s)
    rw [places.length_display] at h0
    exact h0
  have hlen : (spanL s).length
      = (blockcount.blockSpan s).length :=
    ground.length_map blockcount.HVec.content
      (blockcount.blockSpan s)
  rw [Nat.mul_comm ((blockcount.blockSpan s).length)
      (gapProd (display (List.replicate s.length 0))),
    hgU, hgD, ← hlen]
  exact span_count s

/-- The computing read equals the span's count, the exact
division's read at the count identity. -/
theorem dimOf_spanLen (s : Shape) :
    dimOf s = (blockcount.blockSpan s).length := by
  show gapProd (display s)
      / gapProd (display (List.replicate s.length 0))
    = (blockcount.blockSpan s).length
  rw [← spanProd s]
  exact ground.divMulSelf ((blockcount.blockSpan s).length)
    (gapProd (display (List.replicate s.length 0)))
    (gapProdU_pos s)

/-- `cor:weyldim`'s display holds at every shape: the exact
division's certificate off the count identity. -/
theorem readAll (s : Shape) : read s := by
  show dimOf s
      * gapProd (display (List.replicate s.length 0))
    = gapProd (display s)
  rw [dimOf_spanLen s]
  exact spanProd s

/-- The row list at a shifted last occupancy: the appended count
moves every row together, one per key. -/
private theorem rowList_snoc_shift : ∀ (s : Shape) (j : Nat),
    rowList (s ++ [j]) = (rowList (s ++ [0])).map (fun x => x + j)
  | [], j => by
    show [j + 0] = [0 + 0 + j]
    rw [Nat.add_zero j, Nat.add_zero 0, Nat.zero_add j]
  | a :: t, j => by
    show (a + sumNat (t ++ [j])) :: rowList (t ++ [j])
      = (a + sumNat (t ++ [0]) + j) :: (rowList (t ++ [0])).map (fun x => x + j)
    rw [rowList_snoc_shift t j, ground.sumNat_append t [j],
      ground.sumNat_append t [0]]
    show (a + (sumNat t + (j + 0))) :: _
      = (a + (sumNat t + (0 + 0)) + j) :: _
    rw [Nat.add_zero j, Nat.add_zero 0, Nat.add_zero (sumNat t),
      Nat.add_assoc a (sumNat t) j]

/-- A shifted first family passes the shift through the
componentwise sum. -/
private theorem zipWith_shift : ∀ (l u : List Nat) (j : Nat),
    List.zipWith (fun x y => x + y) (l.map (fun x => x + j)) u
      = (List.zipWith (fun x y => x + y) l u).map (fun x => x + j)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | a :: l, b :: u, j => by
    show (a + j + b) :: List.zipWith (fun x y => x + y)
        (l.map (fun x => x + j)) u
      = (a + b + j) :: (List.zipWith (fun x y => x + y) l u).map
        (fun x => x + j)
    rw [zipWith_shift l u j, Nat.add_right_comm a j b]

/-- The display at a shifted last occupancy: the appended count
moves every display entry together. -/
private theorem display_snoc_shift (s : Shape) (j : Nat) :
    display (s ++ [j]) = (display (s ++ [0])).map (fun x => x + j) := by
  have hl : (s ++ [j]).length = (s ++ [0]).length := by
    rw [ground.length_append s [j], ground.length_append s [0]]
    exact rfl
  show List.zipWith (fun l u => l + u) (rowList (s ++ [j]))
      ((List.range (s ++ [j]).length).map
        (fun i => (s ++ [j]).length - i))
    = (List.zipWith (fun l u => l + u) (rowList (s ++ [0]))
        ((List.range (s ++ [0]).length).map
          (fun i => (s ++ [0]).length - i))).map (fun x => x + j)
  rw [hl, rowList_snoc_shift s j]
  exact zipWith_shift (rowList (s ++ [0])) _ j

/-- The gap product is blind to a shared shift: every pair gap is
the shifted pair's own. -/
private theorem gapProd_shift : ∀ (l : List Nat) (j : Nat),
    gapProd (l.map (fun x => x + j)) = gapProd l
  | [], _ => rfl
  | x :: t, j => by
    show gapHead (x + j) (t.map (fun y => y + j))
        * gapProd (t.map (fun y => y + j))
      = gapHead x t * gapProd t
    rw [gapProd_shift t j]
    show ground.famFold Nat.mul 1 (fun y => x + j - y)
          (t.map (fun y => y + j)) * gapProd t
      = ground.famFold Nat.mul 1 (fun y => x - y) t * gapProd t
    rw [ground.famFold_map Nat.mul 1 (fun y => x + j - y)
        (fun y => y + j) t,
      ground.famFold_congr_all Nat.mul 1 (fun y => x + j - (y + j))
        (fun y => x - y) (fun y => ground.addSubAddR x y j) t]

/-- The dimension is one value at the class: the full-column key's
occupancy moves every display entry together and the gap product
reads the gaps alone. -/
theorem dimOf_snoc (s : List Nat) (a : Nat) :
    dimOf (s ++ [a]) = dimOf (s ++ [0]) := by
  have hl : (s ++ [a]).length = (s ++ [0]).length := by
    rw [ground.length_append s [a], ground.length_append s [0]]
    exact rfl
  show gapProd (display (s ++ [a]))
      / gapProd (display (List.replicate (s ++ [a]).length 0))
    = gapProd (display (s ++ [0]))
      / gapProd (display (List.replicate (s ++ [0]).length 0))
  rw [hl, display_snoc_shift s a, gapProd_shift (display (s ++ [0])) a]

/-! The display's run tier: a display's gap product peels its head
against the head's own gap fold (`gapProd_cons`), a descending run
carries the fold's factorial at its floor (`gapHead_descRun`), and
a run over a stated tail reads the run's product against the tail's
with one tail fold per run entry (`gapProd_descRun_app`) — the unit
display the run at the unit floor (`unitDisp_descRun`), and the
display the rows against it entry by entry (`weylchar.display_zip`). -/

/-- The descending run: `k` entries at a stated floor, `a + k - 1`
down to `a`. -/
def descRun (a : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => (k + a) :: descRun a k

/-- The tail's gap folds over a run's members, one factor per run
entry. -/
def gapRun (post : List Nat) (a : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => gapRun post a k * gapHead (k + a) post

/-- The run's length is its count. -/
theorem length_descRun (a : Nat) : ∀ k : Nat, (descRun a k).length = k
  | 0 => rfl
  | k + 1 => congrArg Nat.succ (length_descRun a k)

/-- The display's gap product peels its head: the head's gap fold
against the tail's own product. -/
theorem gapProd_cons (x : Nat) (t : List Nat) :
    gapProd (x :: t) = gapHead x t * gapProd t := rfl

/-- The head's gap fold peels its member: the member's own gap
against the fold beneath it. -/
theorem gapHead_cons (x y : Nat) (t : List Nat) :
    gapHead x (y :: t) = (x - y) * gapHead x t := rfl

/-- The head's gap fold splits over a join. -/
theorem gapHead_append (x : Nat) (l m : List Nat) :
    gapHead x (l ++ m) = gapHead x l * gapHead x m :=
  ground.famFold_append Nat.mul 1 ground.mulAssoc Nat.one_mul
    (fun y => x - y) l m

/-- The run grows at its floor: the raised run over the floor's own
entry. -/
theorem descRun_snoc (a : Nat) : ∀ k : Nat,
    descRun a (k + 1) = descRun (a + 1) k ++ [a]
  | 0 => by
    show (0 + a) :: descRun a 0 = descRun (a + 1) 0 ++ [a]
    rw [Nat.zero_add]
    rfl
  | k + 1 => by
    show (k + 1 + a) :: descRun a (k + 1)
      = (k + (a + 1)) :: (descRun (a + 1) k ++ [a])
    rw [descRun_snoc a k, Nat.add_assoc k 1 a, Nat.add_comm 1 a]

/-- A raised run is the run at the raised floor. -/
theorem map_descRun (w c : Nat) : ∀ k : Nat,
    (descRun c k).map (fun x => w + x) = descRun (w + c) k
  | 0 => rfl
  | k + 1 => by
    show (w + (k + c)) :: (descRun c k).map (fun x => w + x)
      = (k + (w + c)) :: descRun (w + c) k
    rw [map_descRun w c k, Nat.add_left_comm w k c]

/-- A run raised by a constant family is the run at the raised
floor, the raise's zipWith spelling. -/
theorem zipWith_descRun (c a : Nat) : ∀ k : Nat,
    List.zipWith (fun l u => l + u) (List.replicate k c) (descRun a k)
      = descRun (a + c) k
  | 0 => rfl
  | k + 1 => by
    show (c + (k + a)) :: List.zipWith (fun l u => l + u)
        (List.replicate k c) (descRun a k)
      = (k + (a + c)) :: descRun (a + c) k
    rw [zipWith_descRun c a k, Nat.add_comm c (k + a),
      Nat.add_assoc k a c]

/-- The run's head gap fold against the factorial: the falling
product at the run's own floor. -/
theorem gapHead_descRun (a : Nat) : ∀ (k m : Nat),
    gapHead (k + m + a) (descRun a k) * ground.factorial m
      = ground.factorial (k + m)
  | 0, m => by
    show 1 * ground.factorial m = ground.factorial (0 + m)
    rw [Nat.one_mul, Nat.zero_add]
  | k + 1, m => by
    have hx : k + 1 + m + a = k + (m + 1) + a := by
      rw [Nat.add_right_comm k 1 m, Nat.add_assoc k m 1]
    have hs : k + (m + 1) + a - (k + a) = m + 1 := by
      rw [show k + (m + 1) + a = k + a + (m + 1) from by
        rw [Nat.add_right_comm k (m + 1) a], ground.addSubSelfL]
    show gapHead (k + 1 + m + a) ((k + a) :: descRun a k)
        * ground.factorial m = ground.factorial (k + 1 + m)
    rw [hx]
    show (k + (m + 1) + a - (k + a))
        * gapHead (k + (m + 1) + a) (descRun a k)
        * ground.factorial m = ground.factorial (k + 1 + m)
    rw [hs, Nat.mul_comm (m + 1)
        (gapHead (k + (m + 1) + a) (descRun a k)), ground.mulAssoc]
    show gapHead (k + (m + 1) + a) (descRun a k)
        * ground.factorial (m + 1) = ground.factorial (k + 1 + m)
    rw [gapHead_descRun a k (m + 1),
      show k + (m + 1) = k + 1 + m from by
        rw [Nat.add_right_comm k 1 m, ← Nat.add_assoc k m 1]]

/-- The run's head gap fold at the floor above it is the
factorial. -/
private theorem gapHead_descRun_zero (a k : Nat) :
    gapHead (k + a) (descRun a k) = ground.factorial k := by
  have h0 := gapHead_descRun a k 0
  show gapHead (k + 0 + a) (descRun a k) = ground.factorial (k + 0)
  rw [← h0]
  show gapHead (k + 0 + a) (descRun a k)
    = gapHead (k + 0 + a) (descRun a k) * 1
  rw [Nat.mul_one]

/-- The five-factor product's shuffle. -/
private theorem mulShuffle (F H G P R : Nat) :
    F * H * (G * (P * R)) = F * G * (P * (R * H)) := by
  rw [ground.mulAssoc F H (G * (P * R)),
    Nat.mul_comm H (G * (P * R)), ground.mulAssoc G (P * R) H,
    ground.mulAssoc P R H, ← ground.mulAssoc F G (P * (R * H))]

/-- The run's gap product grows by the factorial: the new floor's
gaps over the run beneath it. -/
theorem gapProd_descRun_succ (a k : Nat) :
    gapProd (descRun a (k + 1))
      = ground.factorial k * gapProd (descRun a k) := by
  show gapProd ((k + a) :: descRun a k)
    = ground.factorial k * gapProd (descRun a k)
  rw [gapProd_cons (k + a) (descRun a k), gapHead_descRun_zero a k]

/-- The run's gap product is its count's own: the display's gaps
read the run's steps alone, at any floor. -/
theorem gapProd_descRun (a b : Nat) : ∀ k : Nat,
    gapProd (descRun a k) = gapProd (descRun b k)
  | 0 => rfl
  | k + 1 => by
    rw [gapProd_descRun_succ a k, gapProd_descRun_succ b k,
      gapProd_descRun a b k]

/-- The run over a stated tail: the run's own product against the
tail's, with one tail fold per run entry. -/
theorem gapProd_descRun_app (post : List Nat) (a : Nat) : ∀ k : Nat,
    gapProd (descRun a k ++ post)
      = gapProd (descRun a k) * (gapProd post * gapRun post a k)
  | 0 => by
    show gapProd post = 1 * (gapProd post * 1)
    rw [Nat.mul_one, Nat.one_mul]
  | k + 1 => by
    show gapProd ((k + a) :: (descRun a k ++ post))
      = gapProd (descRun a (k + 1))
        * (gapProd post * (gapRun post a k * gapHead (k + a) post))
    rw [gapProd_cons (k + a) (descRun a k ++ post),
      gapHead_append (k + a) (descRun a k) post,
      gapProd_descRun_app post a k, gapProd_descRun_succ a k,
      gapHead_descRun_zero a k]
    exact mulShuffle (ground.factorial k) (gapHead (k + a) post)
      (gapProd (descRun a k)) (gapProd post) (gapRun post a k)

/-- The run's entry read: the key joins the entry to the run's
top. -/
theorem getAt_descRun (a : Nat) : ∀ (k i : Nat), i < k →
    i + ground.getAt 0 (descRun a k) i + 1 = k + a
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, 0, _ => by
    show 0 + (k + a) + 1 = k + 1 + a
    rw [Nat.zero_add, Nat.add_right_comm k a 1]
  | k + 1, j + 1, h => by
    have hj : j < k := Nat.lt_of_succ_lt_succ h
    show j + 1 + ground.getAt 0 (descRun a k) j + 1 = k + 1 + a
    rw [Nat.add_right_comm j 1 (ground.getAt 0 (descRun a k) j),
      getAt_descRun a k j hj, Nat.add_right_comm k a 1]

/-- The unit display is the run at the unit floor. -/
theorem unitDisp_descRun (d : Nat) : unitDisp d = descRun 1 d := by
  refine ground.getAt_ext 0 (unitDisp d) (descRun 1 d)
    (by rw [places.length_unitDisp d, length_descRun 1 d]) ?_
  intro i hi
  rw [places.length_unitDisp d] at hi
  have h2 : i + ground.getAt 0 (descRun 1 d) i = d :=
    ground.addCancelR 1 (getAt_descRun 1 d i hi)
  have h4 : i + ground.getAt 0 (descRun 1 d) i - i
      = ground.getAt 0 (descRun 1 d) i :=
    ground.addSubSelfL i (ground.getAt 0 (descRun 1 d) i)
  rw [h2] at h4
  rw [weylchar.getAt_unitDisp d i hi, h4]

/-! The member tier: `cor:weyldim`'s dimension identity at the
member data, `d_λ Π_α g_α = Π_α g^λ_α` over the positive list's
dots against `ρ` and `λ+ρ`.  The gap product at a weight expands
over `thm:assembly`'s occupancy families — one signed monomial per
family at the complement-guarded gap fold, whose degree the shifted
key's margin solves — and the identity's per-key balance carries it
onto the `ρ`-orbit's principal fold (`prodPos_pfold`).  The
convolution transfer takes the product of that fold with the
multiplicity family's own onto the shifted orbit's fold, key by key
at `thm:memberchar`'s balance (`pfold_conv`); the exchange carries
the shifted orbit's fold at `ρ` onto the `ρ`-orbit's fold at `λ+ρ`
at the stated crossed count read (`pfold_exchange`); and the two
weights' expansions meet at the shared unit-gap power, cancelled at
the monic, with the geometric words' Horner reads at the natural one
the two products and the multiplicity family's own count
(`eval_lfold_one`, `poly.eval_gwordFold_one`).  The comparison
beside it prices every member's gap at `λ+ρ` at or beyond its gap at
`ρ` (`memberGap_le`), the dominant top's own dots the margin. -/

open sertables assembly memberchar

/-- The shifted key against `λ+ρ`, the member weight of
`cor:weyldim`'s right-hand product. -/
def lamrho (t : gentable.Table) (lamV : List BPair) : List BPair :=
  poly.pnorm (elim.vecAdd lamV (rhoV t))

/-- The shifted principal fold of a signed family at a weight: one
signed monomial per member at the shifted dot's margin
(`cor:weyldim`'s graded display of `con:sertables`' orbit data). -/
def pfold (F : FundData) (kap : List BPair) (sig : BPair)
    (W : List (List BPair × Bool)) : poly.Poly :=
  ground.famFold poly.add []
    (fun vp => poly.smono vp.2
      (BPair.marginN (BPair.add sig (dotB F vp.1 kap)))) W

/-- The unsigned principal fold of a multiplicity family, its
members all at the even side (`thm:memberchar`'s `ch` at
`cor:weyldim`'s grading). -/
def lfold (F : FundData) (kap : List BPair) (sig : BPair)
    (L : List (List BPair)) : poly.Poly :=
  ground.famFold poly.add []
    (fun nu => poly.smono false
      (BPair.marginN (BPair.add sig (dotB F nu kap)))) L

/-- The gap product over the positive list at a weight, one pair per
member (`cor:weyldim`'s member product). -/
def prodPos (t : gentable.Table) (F : FundData)
    (kap : List BPair) : poly.Poly :=
  ground.famFold poly.mul poly.one
    (fun j => poly.tpair (gapsAt t F kap j))
    (List.range t.posFolds.length)

/-- The degree data of a signed family at a weight and a shift: the
shifted dot's margin per member, the side kept. -/
def dmap (F : FundData) (sig : BPair) (kap : List BPair)
    (W : List (List BPair × Bool)) : List (Nat × Bool) :=
  W.map (fun vp =>
    (BPair.marginN (BPair.add sig (dotB F vp.1 kap)), vp.2))

/-- The graded count of a signed family reads the guarded fold over
its members. -/
private theorem wCountFold (y : List BPair) (s : Bool) :
    ∀ W : List (List BPair × Bool),
    ground.countOf (y, s) W
      = ground.famFold Nat.add 0
          (fun vp => if vp.2 = s then
            (if vp.1 = y then 1 else 0) else 0) W
  | [] => rfl
  | vp :: W => by
    show ground.countOf (y, s) (vp :: W)
      = (if vp.2 = s then (if vp.1 = y then 1 else 0) else 0)
        + ground.famFold Nat.add 0
            (fun vp => if vp.2 = s then
              (if vp.1 = y then 1 else 0) else 0) W
    rw [ground.countOf_cons, wCountFold y s W]
    refine congrArg (fun n => n + _) ?_
    by_cases h2 : vp.2 = s
    · by_cases h1 : vp.1 = y
      · rw [if_pos h2, if_pos h1,
          if_pos (show ((y, s) : List BPair × Bool) = vp from by
            rw [← h1, ← h2])]
      · rw [if_pos h2, if_neg h1,
          if_neg (fun he : ((y, s) : List BPair × Bool) = vp =>
            h1 (congrArg Prod.fst he).symm)]
    · rw [if_neg h2,
        if_neg (fun he : ((y, s) : List BPair × Bool) = vp =>
          h2 (congrArg Prod.snd he).symm)]

/-- The degree fibres: a graded family's count at a degree collects
the per-key graded counts at that degree, the keys read off a
distinct index the family's own keys reach. -/
private theorem fiberCount {α K : Type} [DecidableEq α]
    [DecidableEq K] (key : α → K) (sd : α → Bool) (dg : α → Nat)
    (deg : K → Nat) (D : List K)
    (hD : ∀ y, ground.countOf y D ≤ 1) (k : Nat) (s : Bool) :
    ∀ l : List α,
    (∀ x, 0 < ground.countOf x l → 0 < ground.countOf (key x) D) →
    (∀ x, 0 < ground.countOf x l → dg x = deg (key x)) →
    ground.countOf (k, s) (l.map (fun x => (dg x, sd x)))
      = ground.famFold Nat.add 0
          (fun y => if deg y = k then
            ground.famFold Nat.add 0
              (fun x => if sd x = s then
                (if key x = y then 1 else 0) else 0) l
            else 0) D
  | [], _, _ => by
    show 0 = ground.famFold Nat.add 0
      (fun y => if deg y = k then 0 else 0) D
    rw [ground.famFold_zero (fun y => if deg y = k then 0 else 0)
      (fun _ => ite_self 0) D]
  | a :: l, hcov, hdeg => by
    have hal : ∀ x, 0 < ground.countOf x l →
        0 < ground.countOf x (a :: l) := fun x hx =>
      Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _)
    have hahead : 0 < ground.countOf a (a :: l) := by
      rw [ground.countOf_head]
      exact Nat.succ_pos _
    have hcnt : ground.countOf (key a) D = 1 :=
      Nat.le_antisymm (hD (key a)) (hcov a hahead)
    have hda : dg a = deg (key a) := hdeg a hahead
    have hsplit : ground.famFold Nat.add 0
        (fun y => if deg y = k then
          ((if sd a = s then (if key a = y then 1 else 0) else 0)
            + ground.famFold Nat.add 0
                (fun x => if sd x = s then
                  (if key x = y then 1 else 0) else 0) l)
          else 0) D
      = ground.famFold Nat.add 0
          (fun y => if deg y = k then
            (if sd a = s then (if key a = y then 1 else 0) else 0)
            else 0) D
        + ground.famFold Nat.add 0
            (fun y => if deg y = k then
              ground.famFold Nat.add 0
                (fun x => if sd x = s then
                  (if key x = y then 1 else 0) else 0) l
              else 0) D := by
      rw [← ground.famFold_add_split]
      refine ground.famFold_congr_all Nat.add 0 _ _ (fun y => ?_) D
      by_cases hy : deg y = k
      · rw [if_pos hy, if_pos hy, if_pos hy]
      · rw [if_neg hy, if_neg hy, if_neg hy]
    have hfirst : ground.famFold Nat.add 0
        (fun y => if deg y = k then
          (if sd a = s then (if key a = y then 1 else 0) else 0)
          else 0) D
      = (if ((k, s) : Nat × Bool) = (dg a, sd a) then 1 else 0) := by
      rw [ground.famFold_pick_of _ (key a) D hcnt (fun y _ hy => by
        by_cases h1 : deg y = k
        · rw [if_pos h1]
          by_cases h2 : sd a = s
          · rw [if_pos h2, if_neg (fun he : key a = y => hy he.symm)]
          · rw [if_neg h2]
        · rw [if_neg h1]), if_pos rfl]
      by_cases h1 : deg (key a) = k
      · rw [if_pos h1]
        by_cases h2 : sd a = s
        · rw [if_pos h2,
            if_pos (show ((k, s) : Nat × Bool) = (dg a, sd a) from by
              rw [hda, h1, h2])]
        · rw [if_neg h2,
            if_neg (fun he : ((k, s) : Nat × Bool) = (dg a, sd a) =>
              h2 (congrArg Prod.snd he).symm)]
      · rw [if_neg h1,
          if_neg (fun he : ((k, s) : Nat × Bool) = (dg a, sd a) =>
            h1 (hda.symm.trans (congrArg Prod.fst he).symm))]
    show ground.countOf (k, s)
        ((dg a, sd a) :: l.map (fun x => (dg x, sd x)))
      = ground.famFold Nat.add 0
          (fun y => if deg y = k then
            ((if sd a = s then (if key a = y then 1 else 0) else 0)
              + ground.famFold Nat.add 0
                  (fun x => if sd x = s then
                    (if key x = y then 1 else 0) else 0) l)
            else 0) D
    rw [ground.countOf_cons, hsplit, hfirst,
      fiberCount key sd dg deg D hD k s l
        (fun x hx => hcov x (hal x hx)) (fun x hx => hdeg x (hal x hx))]

/-- The guarded per-key balance folds to the per-degree balance. -/
private theorem foldGuard_balance {K : Type} [DecidableEq K]
    (deg : K → Nat) (k : Nat) (a b c d : K → Nat) (D : List K)
    (h : ∀ y, 0 < ground.countOf y D → a y + b y = c y + d y) :
    ground.famFold Nat.add 0 (fun y => if deg y = k then a y else 0) D
      + ground.famFold Nat.add 0
          (fun y => if deg y = k then b y else 0) D
    = ground.famFold Nat.add 0
        (fun y => if deg y = k then c y else 0) D
      + ground.famFold Nat.add 0
          (fun y => if deg y = k then d y else 0) D := by
  rw [← ground.famFold_add_split, ← ground.famFold_add_split]
  refine ground.famFold_congr_members Nat.add 0 _ _ D (fun y hy => ?_)
  by_cases hg : deg y = k
  · rw [if_pos hg, if_pos hg, if_pos hg, if_pos hg]
    exact h y hy
  · rw [if_neg hg, if_neg hg, if_neg hg, if_neg hg]

/-- `cor:weyldim`'s exchange: at the stated crossed count read the
shifted orbit's fold at `ρ` is the `ρ`-orbit's fold at `λ+ρ`, the
two displays' degrees matched side by side. -/
theorem pfold_exchange (t : gentable.Table) (F : FundData)
    (W W' : List (List BPair × Bool)) (lamV : List BPair)
    (hexch : ∀ k : Nat,
      ground.countOf (k, false) (W'.map (fun vp =>
        (BPair.marginN (BPair.add
          (dotB F (lamrho t lamV) (rhoV t))
          (dotB F vp.1 (rhoV t))), vp.2)))
        + ground.countOf (k, true) (W.map (fun vp =>
        (BPair.marginN (BPair.add
          (dotB F (rhoV t) (lamrho t lamV))
          (dotB F vp.1 (lamrho t lamV))), vp.2)))
      = ground.countOf (k, true) (W'.map (fun vp =>
        (BPair.marginN (BPair.add
          (dotB F (lamrho t lamV) (rhoV t))
          (dotB F vp.1 (rhoV t))), vp.2)))
        + ground.countOf (k, false) (W.map (fun vp =>
        (BPair.marginN (BPair.add
          (dotB F (rhoV t) (lamrho t lamV))
          (dotB F vp.1 (lamrho t lamV))), vp.2)))) :
    poly.oneValue
      (pfold F (rhoV t) (dotB F (lamrho t lamV) (rhoV t)) W')
      (pfold F (lamrho t lamV)
        (dotB F (rhoV t) (lamrho t lamV)) W) :=
  poly.monoFold_ov
    (fun vp : List BPair × Bool => BPair.marginN (BPair.add
      (dotB F (lamrho t lamV) (rhoV t)) (dotB F vp.1 (rhoV t))))
    (fun vp : List BPair × Bool => vp.2)
    (fun vp : List BPair × Bool => BPair.marginN (BPair.add
      (dotB F (rhoV t) (lamrho t lamV))
      (dotB F vp.1 (lamrho t lamV))))
    (fun vp : List BPair × Bool => vp.2) W' W hexch

/-- `cor:weyldim`'s assembly instance: the gap product at a weight
whose positive dots sit at or beyond the sum's unit is the shifted
principal fold of the `ρ`-orbit's data.  The product expands over
the occupancy families at `thm:assembly`'s subset fold, each
family's degree the shifted key's own margin, and the identity's
per-key balance carries the families' graded counts onto the orbit's
at every degree. -/
theorem prodPos_pfold (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hwsh : wShapeRead t W)
    (hclose : wCloseRead t W) (hdom : wDomRead t W wits)
    (htop : wTopRead t W)
    (kap : List BPair)
    (hnn : ∀ j, j < t.posFolds.length →
      BPair.unit ≤ dotB F (posCorootV t j) kap) :
    poly.oneValue (prodPos t F kap)
      (pfold F kap (dotB F (rhoV t) kap) W) := by
  have hdist : ∀ j,
      ground.countOf j (List.range t.posFolds.length) ≤ 1 := by
    intro j
    rw [ground.countOf_range j t.posFolds.length]
    by_cases h : j < t.posFolds.length
    · rw [if_pos h]
      exact Nat.le_refl 1
    · rw [if_neg h]
      exact Nat.zero_le 1
  refine poly.oneValue_trans
    (elim.tpairFold_subsets (gapsAt t F kap)
      (List.range t.posFolds.length) hdist) ?_
  have hD : ∀ y, ground.countOf y (ground.dedupL
      ((sublistsOf (List.range t.posFolds.length)).map (eKey t)
        ++ W.map Prod.fst)) ≤ 1 := fun y =>
    ground.countOf_dedupL_le y _
  have hframe : ∀ y, 0 < ground.countOf y (ground.dedupL
      ((sublistsOf (List.range t.posFolds.length)).map (eKey t)
        ++ W.map Prod.fst)) →
      y.length = t.rank ∧ poly.pnorm y = y := by
    intro y hy
    have hmem := ground.mem_of_dedupL (ground.mem_of_countOf_pos y _ hy)
    cases ground.mem_append_of _ _ hmem with
    | inl hin =>
      obtain ⟨S, _, hS⟩ := ground.mem_map_of (eKey t) _ y hin
      rw [← hS]
      exact ⟨eKey_length t S, eKey_norm t S⟩
    | inr hin =>
      obtain ⟨vp, hvp, hv⟩ := ground.mem_map_of Prod.fst W y hin
      have hsh := hwsh vp hvp
      rw [hv] at hsh
      exact hsh
  have hcovS : ∀ S, 0 < ground.countOf S
      (sublistsOf (List.range t.posFolds.length)) →
      0 < ground.countOf (eKey t S) (ground.dedupL
        ((sublistsOf (List.range t.posFolds.length)).map (eKey t)
          ++ W.map Prod.fst)) := fun S hS =>
    ground.countOf_pos_of_mem (ground.mem_dedupL
      (ground.mem_append_left _ (ground.mem_map_to (eKey t)
        (ground.mem_of_countOf_pos S _ hS))))
  have hcovW : ∀ vp, 0 < ground.countOf vp W →
      0 < ground.countOf vp.1 (ground.dedupL
        ((sublistsOf (List.range t.posFolds.length)).map (eKey t)
          ++ W.map Prod.fst)) := fun vp hvp =>
    ground.countOf_pos_of_mem (ground.mem_dedupL
      (ground.mem_append_right _ (ground.mem_map_to Prod.fst
        (ground.mem_of_countOf_pos vp W hvp))))
  have hdegS : ∀ S, 0 < ground.countOf S
      (sublistsOf (List.range t.posFolds.length)) →
      ground.famFold Nat.add 0
        (fun j => if 0 < ground.countOf j S then 0
          else gapsAt t F kap j)
        (List.range t.posFolds.length)
      = BPair.marginN (BPair.add
          (dotB F (rhoV t) kap) (dotB F (eKey t S) kap)) := fun S hS =>
    gapFold_eKey t F hshape hsp hpsq hpi hrd kap hnn S hS
  refine poly.monoFold_ov _ _ _ _ _ W (fun k => ?_)
  rw [fiberCount (eKey t) sideOf
      (fun S => ground.famFold Nat.add 0
        (fun j => if 0 < ground.countOf j S then 0
          else gapsAt t F kap j)
        (List.range t.posFolds.length))
      (fun y => BPair.marginN (BPair.add
        (dotB F (rhoV t) kap) (dotB F y kap))) _ hD k false _
      hcovS hdegS,
    fiberCount (eKey t) sideOf
      (fun S => ground.famFold Nat.add 0
        (fun j => if 0 < ground.countOf j S then 0
          else gapsAt t F kap j)
        (List.range t.posFolds.length))
      (fun y => BPair.marginN (BPair.add
        (dotB F (rhoV t) kap) (dotB F y kap))) _ hD k true _
      hcovS hdegS,
    fiberCount Prod.fst Prod.snd
      (fun vp => BPair.marginN (BPair.add
        (dotB F (rhoV t) kap) (dotB F vp.1 kap)))
      (fun y => BPair.marginN (BPair.add
        (dotB F (rhoV t) kap) (dotB F y kap))) _ hD k true W
      hcovW (fun _ _ => rfl),
    fiberCount Prod.fst Prod.snd
      (fun vp => BPair.marginN (BPair.add
        (dotB F (rhoV t) kap) (dotB F vp.1 kap)))
      (fun y => BPair.marginN (BPair.add
        (dotB F (rhoV t) kap) (dotB F y kap))) _ hD k false W
      hcovW (fun _ _ => rfl)]
  refine foldGuard_balance _ k _ _ _ _ _ (fun y hy => ?_)
  obtain ⟨hy1, hy2⟩ := hframe y hy
  have hbal := assembly.balanceRead t F W wits hshape hgram hgsym
    hsp hsq hpsq hpi hrd hclose hdom htop y hy1 hy2
  rw [← wCountFold y true W, ← wCountFold y false W]
  exact hbal

/-- `cor:weyldim`'s convolution transfer: the product of the
`ρ`-orbit's principal fold with the multiplicity family's own is
the shifted orbit's principal fold, both read at the `ρ` weight.
The product's members are the orbit's members joined to the
family's, each pair's degree the two shifted margins' sum at the
joined key's own, and `thm:memberchar`'s per-key balance carries the
pair counts onto the shifted orbit's counts at every degree. -/
theorem pfold_conv (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair)) (witsL : List (List Nat))
    (lamV : List BPair)
    (W' : List (List BPair × Bool)) (wits' : List (List Nat))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hform : reflFormRead t F)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (hdom : wDomRead t W wits) (htop : wTopRead t W)
    (hmsh : mShapeRead t L) (hsym : symRead t L)
    (hsupp : supportRead t L witsL lamV)
    (htopL : topRead L lamV) (hlam : lamRead t lamV)
    (hwsh' : wShapeRead t W') (hclose' : wCloseRead t W')
    (hdom' : wDomAt t W' wits' (lamrho t lamV))
    (htop' : wTopAt W' (lamrho t lamV))
    (hreg' : wRegRead t W' (lamrho t lamV))
    (hrec : recRead t F W L lamV)
    (hnw : ∀ vp ∈ W, BPair.unit ≤ BPair.add
      (dotB F (rhoV t) (rhoV t)) (dotB F vp.1 (rhoV t)))
    (hnl : ∀ nu ∈ L, BPair.unit ≤ BPair.add
      (dotB F lamV (rhoV t)) (dotB F nu (rhoV t))) :
    poly.oneValue
      (poly.mul (pfold F (rhoV t) (dotB F (rhoV t) (rhoV t)) W)
        (lfold F (rhoV t) (dotB F lamV (rhoV t)) L))
      (pfold F (rhoV t)
        (dotB F (lamrho t lamV) (rhoV t)) W') := by
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  -- the pair members: each orbit member joined to each family member
  have hpair : ∀ p : (List BPair × Bool) × List BPair,
      0 < ground.countOf p
        (W.flatMap (fun vp => L.map (fun nu => (vp, nu)))) →
      0 < ground.countOf p.1 W ∧ 0 < ground.countOf p.2 L := by
    intro p hp
    obtain ⟨vp, hvp, hin⟩ := ground.mem_flatMap_of _ _ p
      (ground.mem_of_countOf_pos p _ hp)
    obtain ⟨nu, hnu, he⟩ := ground.mem_map_of _ L p hin
    rw [← he]
    exact ⟨ground.countOf_pos_of_mem hvp, ground.countOf_pos_of_mem hnu⟩
  -- the product as the pair family's own fold
  have hstep : ∀ vp : List BPair × Bool,
      poly.oneValue
        (poly.mul (poly.smono vp.2 (BPair.marginN (BPair.add
            (dotB F (rhoV t) (rhoV t)) (dotB F vp.1 (rhoV t)))))
          (lfold F (rhoV t) (dotB F lamV (rhoV t)) L))
        (ground.famFold poly.add []
          (fun nu => poly.smono vp.2
            (BPair.marginN (BPair.add (dotB F (rhoV t) (rhoV t))
              (dotB F vp.1 (rhoV t)))
              + BPair.marginN (BPair.add (dotB F lamV (rhoV t))
                (dotB F nu (rhoV t))))) L) := by
    intro vp
    refine poly.oneValue_trans (poly.mul_comm _ _) ?_
    refine poly.oneValue_trans
      (poly.mul_famFold _ L (poly.smono vp.2 (BPair.marginN
        (BPair.add (dotB F (rhoV t) (rhoV t))
          (dotB F vp.1 (rhoV t)))))) ?_
    refine poly.foldP_congr_members _ _ L (fun nu _ => ?_)
    refine poly.oneValue_trans (poly.mul_comm _ _) ?_
    exact poly.smono_mul_mono vp.2 _ _
  have hflat : ground.famFold poly.add []
      (fun vp : List BPair × Bool => ground.famFold poly.add []
        (fun nu => poly.smono vp.2
          (BPair.marginN (BPair.add (dotB F (rhoV t) (rhoV t))
            (dotB F vp.1 (rhoV t)))
            + BPair.marginN (BPair.add (dotB F lamV (rhoV t))
              (dotB F nu (rhoV t))))) L) W
    = ground.famFold poly.add []
        (fun vp : List BPair × Bool => ground.famFold poly.add []
          (fun p : (List BPair × Bool) × List BPair =>
            poly.smono p.1.2
              (BPair.marginN (BPair.add (dotB F (rhoV t) (rhoV t))
                (dotB F p.1.1 (rhoV t)))
                + BPair.marginN (BPair.add (dotB F lamV (rhoV t))
                  (dotB F p.2 (rhoV t)))))
          (L.map (fun nu => (vp, nu)))) W := by
    refine ground.famFold_congr_all poly.add [] _ _ (fun vp => ?_) W
    rw [ground.famFold_map poly.add []
      (fun p : (List BPair × Bool) × List BPair =>
        poly.smono p.1.2
          (BPair.marginN (BPair.add (dotB F (rhoV t) (rhoV t))
            (dotB F p.1.1 (rhoV t)))
            + BPair.marginN (BPair.add (dotB F lamV (rhoV t))
              (dotB F p.2 (rhoV t)))))
      (fun nu => (vp, nu)) L]
  refine poly.oneValue_trans
    (poly.mul_famFold _ W (lfold F (rhoV t) (dotB F lamV (rhoV t)) L)) ?_
  refine poly.oneValue_trans
    (poly.foldP_congr_members _ _ W (fun vp _ => hstep vp)) ?_
  rw [hflat]
  refine poly.oneValue_trans
    (poly.oneValue_symm (poly.foldP_flatMap _
      (fun vp => L.map (fun nu => (vp, nu))) W)) ?_
  -- the crossed degree balance at the joined keys
  have hD : ∀ y, ground.countOf y (ground.dedupL
      ((W.flatMap (fun vp => L.map (fun nu => (vp, nu)))).map
        (fun p => poly.pnorm (elim.vecAdd p.1.1 p.2))
        ++ W'.map Prod.fst)) ≤ 1 := fun y =>
    ground.countOf_dedupL_le y _
  have hcovP : ∀ p, 0 < ground.countOf p
      (W.flatMap (fun vp => L.map (fun nu => (vp, nu)))) →
      0 < ground.countOf (poly.pnorm (elim.vecAdd p.1.1 p.2))
        (ground.dedupL
          ((W.flatMap (fun vp => L.map (fun nu => (vp, nu)))).map
            (fun p => poly.pnorm (elim.vecAdd p.1.1 p.2))
            ++ W'.map Prod.fst)) := fun p hp =>
    ground.countOf_pos_of_mem (ground.mem_dedupL
      (ground.mem_append_left _ (ground.mem_map_to _
        (ground.mem_of_countOf_pos p _ hp))))
  have hcovW' : ∀ vp, 0 < ground.countOf vp W' →
      0 < ground.countOf vp.1 (ground.dedupL
        ((W.flatMap (fun vp => L.map (fun nu => (vp, nu)))).map
          (fun p => poly.pnorm (elim.vecAdd p.1.1 p.2))
          ++ W'.map Prod.fst)) := fun vp hvp =>
    ground.countOf_pos_of_mem (ground.mem_dedupL
      (ground.mem_append_right _ (ground.mem_map_to Prod.fst
        (ground.mem_of_countOf_pos vp W' hvp))))
  have hdegP : ∀ p, 0 < ground.countOf p
      (W.flatMap (fun vp => L.map (fun nu => (vp, nu)))) →
      BPair.marginN (BPair.add (dotB F (rhoV t) (rhoV t))
          (dotB F p.1.1 (rhoV t)))
        + BPair.marginN (BPair.add (dotB F lamV (rhoV t))
            (dotB F p.2 (rhoV t)))
      = BPair.marginN (BPair.add (dotB F (lamrho t lamV) (rhoV t))
          (dotB F (poly.pnorm (elim.vecAdd p.1.1 p.2)) (rhoV t))) := by
    intro p hp
    obtain ⟨hpW, hpL⟩ := hpair p hp
    have hvl : p.1.1.length = t.rank :=
      (hwsh p.1 (ground.mem_of_countOf_pos p.1 W hpW)).1
    have hnl' : p.2.length = t.rank :=
      (hmsh p.2 (ground.mem_of_countOf_pos p.2 L hpL)).1
    rw [← BPair.marginN_add
      (hnw p.1 (ground.mem_of_countOf_pos p.1 W hpW))
      (hnl p.2 (ground.mem_of_countOf_pos p.2 L hpL))]
    refine BPair.marginN_congr ?_
    have hlr : (dotB F (lamrho t lamV) (rhoV t)).oneValue
        (BPair.add (dotB F lamV (rhoV t)) (dotB F (rhoV t) (rhoV t))) :=
      BPair.oneValue_trans
        (dotB_congrL F (lamrho t lamV) (elim.vecAdd lamV (rhoV t))
          (rhoV t) (poly.pnorm_oneValue _))
        (dotB_addL t F hshape lamV (rhoV t) (rhoV t) hlam.1 hrl)
    have hkr : (dotB F (poly.pnorm (elim.vecAdd p.1.1 p.2))
        (rhoV t)).oneValue
        (BPair.add (dotB F p.1.1 (rhoV t)) (dotB F p.2 (rhoV t))) :=
      BPair.oneValue_trans
        (dotB_congrL F _ (elim.vecAdd p.1.1 p.2) (rhoV t)
          (poly.pnorm_oneValue _))
        (dotB_addL t F hshape p.1.1 p.2 (rhoV t) hvl hnl')
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr hlr hkr) (BPair.oneValue_of_eq ?_))
    show dotB F lamV (rhoV t) + dotB F (rhoV t) (rhoV t)
        + (dotB F p.1.1 (rhoV t) + dotB F p.2 (rhoV t))
      = dotB F (rhoV t) (rhoV t) + dotB F p.1.1 (rhoV t)
        + (dotB F lamV (rhoV t) + dotB F p.2 (rhoV t))
    rw [BPair.add_add_comm (dotB F (rhoV t) (rhoV t))
        (dotB F p.1.1 (rhoV t)) (dotB F lamV (rhoV t))
        (dotB F p.2 (rhoV t)),
      BPair.add_comm (dotB F (rhoV t) (rhoV t))
        (dotB F lamV (rhoV t))]
  have hconv : ∀ (y : List BPair) (s : Bool),
      ground.famFold Nat.add 0
        (fun p : (List BPair × Bool) × List BPair =>
          if p.1.2 = s then
            (if poly.pnorm (elim.vecAdd p.1.1 p.2) = y then 1 else 0)
          else 0)
        (W.flatMap (fun vp => L.map (fun nu => (vp, nu))))
      = convCount W L y s := by
    intro y s
    rw [ground.famFold_flatMap _ (fun vp => L.map (fun nu => (vp, nu))) W]
    refine ground.famFold_congr_all Nat.add 0 _ _ (fun vp => ?_) W
    rw [ground.famFold_map Nat.add 0
      (fun p : (List BPair × Bool) × List BPair =>
        if p.1.2 = s then
          (if poly.pnorm (elim.vecAdd p.1.1 p.2) = y then 1 else 0)
        else 0)
      (fun nu => (vp, nu)) L]
    by_cases hs : vp.2 = s
    · rw [if_pos hs]
      refine ground.famFold_congr_all Nat.add 0 _ _ (fun nu => ?_) L
      rw [if_pos hs]
    · rw [if_neg hs,
        ground.famFold_congr_all Nat.add 0 _ (fun _ => (0 : Nat))
          (fun nu => by rw [if_neg hs]) L,
        ground.famFold_zero (fun _ : List BPair => (0 : Nat))
          (fun _ => rfl) L]
  refine poly.monoFold_ov _ _ _ _ _ W' (fun k => ?_)
  rw [fiberCount (fun p : (List BPair × Bool) × List BPair =>
        poly.pnorm (elim.vecAdd p.1.1 p.2))
      (fun p : (List BPair × Bool) × List BPair => p.1.2)
      (fun p : (List BPair × Bool) × List BPair =>
        BPair.marginN (BPair.add (dotB F (rhoV t) (rhoV t))
            (dotB F p.1.1 (rhoV t)))
          + BPair.marginN (BPair.add (dotB F lamV (rhoV t))
              (dotB F p.2 (rhoV t))))
      (fun y => BPair.marginN (BPair.add
        (dotB F (lamrho t lamV) (rhoV t)) (dotB F y (rhoV t))))
      _ hD k false _ hcovP hdegP,
    fiberCount (fun p : (List BPair × Bool) × List BPair =>
        poly.pnorm (elim.vecAdd p.1.1 p.2))
      (fun p : (List BPair × Bool) × List BPair => p.1.2)
      (fun p : (List BPair × Bool) × List BPair =>
        BPair.marginN (BPair.add (dotB F (rhoV t) (rhoV t))
            (dotB F p.1.1 (rhoV t)))
          + BPair.marginN (BPair.add (dotB F lamV (rhoV t))
              (dotB F p.2 (rhoV t))))
      (fun y => BPair.marginN (BPair.add
        (dotB F (lamrho t lamV) (rhoV t)) (dotB F y (rhoV t))))
      _ hD k true _ hcovP hdegP,
    fiberCount Prod.fst Prod.snd
      (fun vp => BPair.marginN (BPair.add
        (dotB F (lamrho t lamV) (rhoV t)) (dotB F vp.1 (rhoV t))))
      (fun y => BPair.marginN (BPair.add
        (dotB F (lamrho t lamV) (rhoV t)) (dotB F y (rhoV t))))
      _ hD k true W' hcovW' (fun _ _ => rfl),
    fiberCount Prod.fst Prod.snd
      (fun vp => BPair.marginN (BPair.add
        (dotB F (lamrho t lamV) (rhoV t)) (dotB F vp.1 (rhoV t))))
      (fun y => BPair.marginN (BPair.add
        (dotB F (lamrho t lamV) (rhoV t)) (dotB F y (rhoV t))))
      _ hD k false W' hcovW' (fun _ _ => rfl)]
  refine foldGuard_balance _ k _ _ _ _ _ (fun y _ => ?_)
  have hid := identityRead t F W wits L witsL lamV W' wits'
    hshape hgram hgsym hsp hsq hpsq hpi hrd hform hwsh hclose hdom
    htop hmsh hsym hsupp htopL hlam hwsh' hclose' hdom' htop' hreg'
    hrec y
  rw [hconv y false, hconv y true,
    ← wCountFold y true W', ← wCountFold y false W']
  exact hid

/-- The multiplicity family's fold reads its member count at the
natural one: every member enters at the even side, one letter
each. -/
theorem eval_lfold_one (F : FundData) (kap : List BPair)
    (sig : BPair) : ∀ L : List (List BPair),
    (poly.eval (lfold F kap sig L) (BPair.ofNat 1)).oneValue
      (BPair.ofNat L.length)
  | [] => BPair.oneValue_refl _
  | nu :: L => by
    show (poly.eval (poly.add
        (poly.smono false
          (BPair.marginN (BPair.add sig (dotB F nu kap))))
        (lfold F kap sig L)) (BPair.ofNat 1)).oneValue
      (BPair.ofNat (L.length + 1))
    refine BPair.oneValue_trans
      (poly.eval_add _ (lfold F kap sig L) (BPair.ofNat 1)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (poly.eval_mono_one
          (BPair.marginN (BPair.add sig (dotB F nu kap))))
        (eval_lfold_one F kap sig L)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.add_comm (BPair.ofNat 1) (BPair.ofNat L.length))) ?_
    exact BPair.oneValue_symm (BPair.ofNat_succ L.length)

/-- `cor:weyldim`'s comparison: every positive member's gap at
`λ+ρ` sits at or beyond its gap at `ρ`, the dominant top's own dot
the margin between them. -/
theorem memberGap_le (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (lamV : List BPair) (hlam : lamRead t lamV) :
    ∀ j, j < t.posFolds.length →
      BPair.marginN (dotB F (posCorootV t j) (rhoV t))
        ≤ BPair.marginN
            (dotB F (posCorootV t j) (lamrho t lamV)) := by
  intro j _
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hnnLam : BPair.unit ≤ dotB F (posCorootV t j) lamV :=
    assembly.dotB_pos_nonneg t F hshape hgram lamV hlam.1
      (fun k hk => hlam.2.2 k hk) j
  have hnnRho : BPair.unit ≤ dotB F (posCorootV t j) (rhoV t) :=
    assembly.dotB_pos_nonneg t F hshape hgram (rhoV t) hrl
      (fun k hk => by
        show BPair.unit ≤ ground.getAt BPair.unit
          (List.replicate t.rank (BPair.ofNat 1)) k
        rw [ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank k hk]
        exact ground.unitLeOfNat 1) j
  have hsplit : (dotB F (posCorootV t j) (lamrho t lamV)).oneValue
      (dotB F (posCorootV t j) lamV
        + dotB F (posCorootV t j) (rhoV t)) :=
    BPair.oneValue_trans
      (dotB_congrR F (posCorootV t j) _ (elim.vecAdd lamV (rhoV t))
        (poly.pnorm_oneValue _))
      (dotB_addR t F hshape (posCorootV t j) lamV (rhoV t)
        (posCorootV_length t j) hlam.1 hrl)
  have hadd : BPair.marginN (dotB F (posCorootV t j) lamV
        + dotB F (posCorootV t j) (rhoV t))
      = BPair.marginN (dotB F (posCorootV t j) lamV)
        + BPair.marginN (dotB F (posCorootV t j) (rhoV t)) :=
    BPair.marginN_add hnnLam hnnRho
  rw [BPair.marginN_congr hsplit, hadd, Nat.add_comm]
  exact Nat.le_add_right _ _

/-- `cor:weyldim`'s member half: the dimension is the gap product,
`d_λ Π_α g_α = Π_α g^λ_α` at the margins of the positive list's dots
against `ρ` and `λ+ρ`.  The two weights' gap products expand over the
occupancy families onto their orbits' principal folds, the
convolution transfer carries the `ρ`-product against the
multiplicity family onto the shifted orbit's fold, the stated
crossed counts exchange it onto the `ρ`-orbit's fold at `λ+ρ`, and
the two expansions meet at the shared unit-gap power — cancelled at
the monic, the geometric words' Horner reads at the natural one the
two products against the family's member count. -/
theorem memberRead (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair)) (witsL : List (List Nat))
    (lamV : List BPair)
    (W' : List (List BPair × Bool)) (wits' : List (List Nat))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hform : reflFormRead t F)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (hdom : wDomRead t W wits) (htop : wTopRead t W)
    (hmsh : mShapeRead t L) (hsym : symRead t L)
    (hsupp : supportRead t L witsL lamV)
    (htopL : topRead L lamV) (hlam : lamRead t lamV)
    (hwsh' : wShapeRead t W') (hclose' : wCloseRead t W')
    (hdom' : wDomAt t W' wits' (lamrho t lamV))
    (htop' : wTopAt W' (lamrho t lamV))
    (hreg' : wRegRead t W' (lamrho t lamV))
    (hrec : recRead t F W L lamV)
    (hnnW : ∀ vp ∈ W, BPair.unit ≤ BPair.add
      (dotB F (rhoV t) (rhoV t)) (dotB F vp.1 (rhoV t)))
    (hnnL : ∀ nu ∈ L, BPair.unit ≤ BPair.add
      (dotB F lamV (rhoV t)) (dotB F nu (rhoV t)))
    (hexch1 : ∀ p ∈ dmap F (dotB F (lamrho t lamV) (rhoV t))
        (rhoV t) W',
      ground.countOf p (dmap F (dotB F (lamrho t lamV) (rhoV t))
          (rhoV t) W')
        = ground.countOf p (dmap F (dotB F (rhoV t) (lamrho t lamV))
            (lamrho t lamV) W))
    (hexch2 : ∀ p ∈ dmap F (dotB F (rhoV t) (lamrho t lamV))
        (lamrho t lamV) W,
      ground.countOf p (dmap F (dotB F (lamrho t lamV) (rhoV t))
          (rhoV t) W')
        = ground.countOf p (dmap F (dotB F (rhoV t) (lamrho t lamV))
            (lamrho t lamV) W)) :
    L.length * ground.famFold Nat.mul 1
      (fun j => BPair.marginN
        (dotB F (posCorootV t j) (rhoV t)))
      (List.range t.posFolds.length)
    = ground.famFold Nat.mul 1
      (fun j => BPair.marginN
        (dotB F (posCorootV t j) (lamrho t lamV)))
      (List.range t.posFolds.length) := by
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hlrl : (lamrho t lamV).length = t.rank :=
    (poly.pnorm_length _).trans
      (elim.length_vecAdd lamV (rhoV t) t.rank hlam.1 hrl)
  have hjlt : ∀ j, 0 < ground.countOf j (List.range t.posFolds.length) →
      j < t.posFolds.length := by
    intro j hj
    rw [ground.countOf_range j t.posFolds.length] at hj
    by_cases hlt : j < t.posFolds.length
    · exact hlt
    · rw [if_neg hlt] at hj
      exact absurd hj (Nat.lt_irrefl 0)
  -- the two weights' positive-dot reads
  have hnnRho : ∀ j, j < t.posFolds.length →
      BPair.unit ≤ dotB F (posCorootV t j) (rhoV t) :=
    fun j hj => ground.leB_of_lt (hrd j hj)
  have hnnLamRho : ∀ j, j < t.posFolds.length →
      BPair.unit ≤ dotB F (posCorootV t j) (lamrho t lamV) :=
    fun j _ => assembly.dotB_pos_nonneg t F hshape hgram
      (lamrho t lamV) hlrl
      (fun k hk => ground.leB_of_lt (shifted_reg t lamV hlam k hk)) j
  -- the assembly instances at both weights, the transfer, the exchange
  have h3rho := prodPos_pfold t F W wits hshape hgram hgsym hsp hsq
    hpsq hpi hrd hwsh hclose hdom htop (rhoV t) hnnRho
  have h3lam := prodPos_pfold t F W wits hshape hgram hgsym hsp hsq
    hpsq hpi hrd hwsh hclose hdom htop (lamrho t lamV) hnnLamRho
  have h4 := pfold_conv t F W wits L witsL lamV W' wits' hshape hgram
    hgsym hsp hsq hpsq hpi hrd hform hwsh hclose hdom htop hmsh hsym
    hsupp htopL hlam hwsh' hclose' hdom' htop' hreg' hrec
    hnnW hnnL
  have hcount : ∀ p : Nat × Bool,
      ground.countOf p (dmap F (dotB F (lamrho t lamV) (rhoV t))
          (rhoV t) W')
        = ground.countOf p (dmap F (dotB F (rhoV t) (lamrho t lamV))
            (lamrho t lamV) W) := by
    intro p
    match Nat.eq_zero_or_pos (ground.countOf p
        (dmap F (dotB F (lamrho t lamV) (rhoV t)) (rhoV t) W')) with
    | Or.inr hp =>
      exact hexch1 p (ground.mem_of_countOf_pos p _ hp)
    | Or.inl h1 =>
      match Nat.eq_zero_or_pos (ground.countOf p
          (dmap F (dotB F (rhoV t) (lamrho t lamV))
            (lamrho t lamV) W)) with
      | Or.inr hp => exact hexch2 p (ground.mem_of_countOf_pos p _ hp)
      | Or.inl h2 => rw [h1, h2]
  have h5 := pfold_exchange t F W W' lamV (fun k => by
    show ground.countOf (k, false)
        (dmap F (dotB F (lamrho t lamV) (rhoV t)) (rhoV t) W')
        + ground.countOf (k, true)
          (dmap F (dotB F (rhoV t) (lamrho t lamV))
            (lamrho t lamV) W)
      = ground.countOf (k, true)
          (dmap F (dotB F (lamrho t lamV) (rhoV t)) (rhoV t) W')
        + ground.countOf (k, false)
          (dmap F (dotB F (rhoV t) (lamrho t lamV))
            (lamrho t lamV) W)
    rw [hcount (k, false), hcount (k, true)]
    exact Nat.add_comm _ _)
  -- the shifted product against the `ρ`-product and the family
  have hA : poly.oneValue (prodPos t F (lamrho t lamV))
      (poly.mul (prodPos t F (rhoV t))
        (lfold F (rhoV t) (dotB F lamV (rhoV t)) L)) :=
    poly.oneValue_trans h3lam
      (poly.oneValue_trans (poly.oneValue_symm h5)
        (poly.oneValue_trans (poly.oneValue_symm h4)
          (poly.mul_congr_left (poly.oneValue_symm h3rho) _)))
  -- the unit-gap powers on both sides
  have hposRho : ∀ j, 0 < ground.countOf j
      (List.range t.posFolds.length) → 0 < gapsAt t F (rhoV t) j :=
    fun j hj => BPair.marginN_pos (hrd j (hjlt j hj))
  have hposLam : ∀ j, 0 < ground.countOf j
      (List.range t.posFolds.length) →
      0 < gapsAt t F (lamrho t lamV) j := fun j hj =>
    Nat.lt_of_lt_of_le (hposRho j hj)
      (memberGap_le t F hshape hgram lamV hlam j (hjlt j hj))
  have h6rho := poly.tpairFold_split (gapsAt t F (rhoV t))
    (List.range t.posFolds.length) hposRho
  have h6lam := poly.tpairFold_split (gapsAt t F (lamrho t lamV))
    (List.range t.posFolds.length) hposLam
  have hbig : poly.oneValue
      (poly.mul (poly.powOf (poly.tpair 1)
          (List.range t.posFolds.length).length)
        (ground.famFold poly.mul poly.one
          (fun j => poly.gword (gapsAt t F (lamrho t lamV) j))
          (List.range t.posFolds.length)))
      (poly.mul (poly.powOf (poly.tpair 1)
          (List.range t.posFolds.length).length)
        (poly.mul (ground.famFold poly.mul poly.one
            (fun j => poly.gword (gapsAt t F (rhoV t) j))
            (List.range t.posFolds.length))
          (lfold F (rhoV t) (dotB F lamV (rhoV t)) L))) :=
    poly.oneValue_trans (poly.oneValue_symm h6lam)
      (poly.oneValue_trans hA
        (poly.oneValue_trans (poly.mul_congr_left h6rho _)
          (poly.mul_assoc _ _ _)))
  have hmon : poly.oneValue
      (poly.powOf (poly.tpair 1)
        (List.range t.posFolds.length).length)
      (poly.powOf (poly.monic [BPair.swap (BPair.ofPos .one)])
        (List.range t.posFolds.length).length) :=
    poly.powOf_congr poly.tpair_monic _
  have hcancel := poly.powOf_cancel_monic
    [BPair.swap (BPair.ofPos .one)]
    (List.range t.posFolds.length).length
    (poly.oneValue_trans
      (poly.mul_congr _ (poly.oneValue_symm hmon))
      (poly.oneValue_trans (poly.mul_comm _ _)
        (poly.oneValue_trans hbig
          (poly.oneValue_trans (poly.mul_comm _ _)
            (poly.mul_congr _ hmon)))))
  -- the Horner reads at the natural one
  have heval := poly.eval_congr hcancel (BPair.ofNat 1)
  have hleft : (poly.eval (ground.famFold poly.mul poly.one
      (fun j => poly.gword (gapsAt t F (lamrho t lamV) j))
      (List.range t.posFolds.length)) (BPair.ofNat 1)).oneValue
      (BPair.ofNat (ground.famFold Nat.mul 1
        (gapsAt t F (lamrho t lamV))
        (List.range t.posFolds.length))) :=
    poly.eval_gwordFold_one (gapsAt t F (lamrho t lamV))
      (List.range t.posFolds.length)
  have hright : (poly.eval (poly.mul (ground.famFold poly.mul poly.one
        (fun j => poly.gword (gapsAt t F (rhoV t) j))
        (List.range t.posFolds.length))
      (lfold F (rhoV t) (dotB F lamV (rhoV t)) L))
      (BPair.ofNat 1)).oneValue
      (BPair.ofNat (ground.famFold Nat.mul 1 (gapsAt t F (rhoV t))
        (List.range t.posFolds.length) * L.length)) :=
    BPair.oneValue_trans
      (poly.eval_mul _ (lfold F (rhoV t) (dotB F lamV (rhoV t)) L)
        (BPair.ofNat 1))
      (BPair.oneValue_trans
        (BPair.mul_congr
          (poly.eval_gwordFold_one (gapsAt t F (rhoV t))
            (List.range t.posFolds.length))
          (eval_lfold_one F (rhoV t) (dotB F lamV (rhoV t)) L))
        (BPair.oneValue_symm (BPair.ofNat_mul _ L.length)))
  have hnat := BPair.ofNat_inj
    (BPair.oneValue_trans (BPair.oneValue_symm hleft)
      (BPair.oneValue_trans heval hright))
  show L.length * ground.famFold Nat.mul 1 (gapsAt t F (rhoV t))
      (List.range t.posFolds.length)
    = ground.famFold Nat.mul 1 (gapsAt t F (lamrho t lamV))
      (List.range t.posFolds.length)
  rw [hnat, Nat.mul_comm]

end weyldim
