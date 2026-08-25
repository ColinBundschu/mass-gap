import MassGap.Weylchar
import MassGap.Blockcount
/-!
`lem:lowerspan` — the span's structural reads at the definitional
multiplicity, `def:blockcount`'s span occupancy: every span member
is the exhibit or an occupied lowering image, a lowering moves the
content one letter-pair step with the height fold dropping by
exactly one (`ht`, the entries against the descending place gaps)
and the dominance walk kept toward the top (`domGo_moveDn` at
`weylchar.domGo`'s slack recursion), so the occupied contents sit
at or below the top with the top's content at the head's line
alone.  The two discharge theorems instantiate
`blockcount.blockSpan_reads` at the invariant conjunction:
`supportRead_def` — `weylchar.supportRead` at the span occupancy —
and `topRead_def` — `weylchar.topRead` there, the exhibit's content
the row list (`blockcount.content_exhibit`) with every further
member's height strictly below.  The fixpoint semantics and the
independence tier are proven (`spanReads`, the height fold the
measure with the exhibit's off-unit family the seed), the
two-list exchange read sits at its owner (`elim.span_count_le`,
`elim.span_count_eq`), and the closure is landed at every distinct
letter pair (`act_closed_def`, `act_span_def` — the parametric
`blockcount.act_closed`/`act_span` at `spanReads`' own
conjunction); the pairs' string exhaustion with the dimension
identification are the string decomposition's arrivals
(`lem:strings`), with the eigen-recursion's discharge at
`lem:casimir`; the span's trace read is stated at the tex (the
projection fold, the crossed fold, the one-value collection at two
orthogonal spanning lists) with its Lean carrier the trace tier's
arrival, the strings' members its instantiating list.  The
occupancy's own reads sit at their owner
(`blockcount.occ`, `occupancyAt_eq_occ`, `groupAt_occupancy`,
`groupAt_rows`); this module keeps only the absent content's
vanishing count beside the discharge.
-/

namespace lowerspan
open ground places blockcount

/-- The height fold: the entries against the descending place
gaps, one occupied lowering dropping it by exactly one. -/
def ht : List Nat → Nat
  | [] => 0
  | a :: t => t.length * a + ht t

/-- The occupied lowering drops the height fold by exactly one. -/
theorem ht_moveDn : ∀ (j : Nat) (nu : List Nat),
    j + 1 < nu.length → 0 < ground.getAt 0 nu j →
    ht (units.moveDn j nu) + 1 = ht nu
  | _, [], hj, _ => absurd hj (Nat.not_lt_zero _)
  | 0, [_], hj, _ =>
    absurd hj (fun hs => Nat.not_lt_zero 0
      (Nat.lt_of_succ_lt_succ hs))
  | 0, a :: b :: t, _, ha => by
    match a, ha with
    | c + 1, _ =>
      show ((t.length + 1) * c + (t.length * (b + 1) + ht t)) + 1
        = (t.length + 1) * (c + 1) + (t.length * b + ht t)
      have h1 : (t.length + 1) * (c + 1)
          = (t.length + 1) * c + (t.length + 1) := Nat.mul_succ _ _
      have h2 : t.length * (b + 1) = t.length * b + t.length :=
        Nat.mul_succ _ _
      rw [h1, h2, Nat.add_right_comm (t.length * b) t.length (ht t),
        ← Nat.add_assoc ((t.length + 1) * c)
          (t.length * b + ht t) t.length,
        Nat.add_assoc ((t.length + 1) * c + (t.length * b + ht t))
          t.length 1,
        Nat.add_right_comm ((t.length + 1) * c) (t.length + 1)
          (t.length * b + ht t)]
  | j + 1, a :: t, hj, ha => by
    show (units.moveDn j t).length * a + ht (units.moveDn j t) + 1
      = t.length * a + ht t
    rw [units.length_moveDn j t, Nat.add_assoc,
      ht_moveDn j t (Nat.lt_of_succ_lt_succ hj) ha]

/-- The dominance walk at a list against itself, the slack kept at
the unit. -/
theorem domGo_refl : ∀ nu : List Nat,
    weylchar.domGo 0 nu nu = true
  | [] => rfl
  | a :: t => by
    show (if a ≤ 0 + a then weylchar.domGo (0 + a - a) t t
      else false) = true
    rw [Nat.zero_add, if_pos (Nat.le_refl a), Nat.sub_self]
    exact domGo_refl t

private theorem domGo_shift (sl b : Nat) (t mt : List Nat) :
    weylchar.domGo (sl + 1) ((b + 1) :: t) mt
      = weylchar.domGo sl (b :: t) mt := by
  cases mt with
  | nil => rfl
  | cons m mr =>
    show (if b + 1 ≤ sl + 1 + m
        then weylchar.domGo (sl + 1 + m - (b + 1)) t mr else false)
      = (if b ≤ sl + m
        then weylchar.domGo (sl + m - b) t mr else false)
    have he : sl + 1 + m = (sl + m) + 1 := Nat.add_right_comm sl 1 m
    have hsub : (sl + m) + 1 - (b + 1) = (sl + m) - b :=
      Nat.succ_sub_succ _ _
    rw [he, hsub]
    by_cases hb : b ≤ sl + m
    · rw [if_pos hb, if_pos (Nat.succ_le_succ hb)]
    · rw [if_neg hb,
        if_neg (fun hs => hb (Nat.le_of_succ_le_succ hs))]

/-- The occupied lowering keeps the dominance walk toward the same
top: the moved prefix drops by one with the slack absorbing it. -/
theorem domGo_moveDn : ∀ (j sl : Nat) (nu mu : List Nat),
    j + 1 < nu.length → 0 < ground.getAt 0 nu j →
    weylchar.domGo sl nu mu = true →
    weylchar.domGo sl (units.moveDn j nu) mu = true
  | _, _, [], _, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | 0, _, [_], _, hj, _, _ =>
    absurd hj (fun hs => Nat.not_lt_zero 0
      (Nat.lt_of_succ_lt_succ hs))
  | 0, sl, a :: b :: t, [], _, _, h => Bool.noConfusion h
  | 0, sl, a :: b :: t, m :: mr, _, ha, h => by
    have h' : (if a ≤ sl + m
        then weylchar.domGo (sl + m - a) (b :: t) mr
        else false) = true := h
    by_cases hc : a ≤ sl + m
    · rw [if_pos hc] at h'
      show (if a - 1 ≤ sl + m
          then weylchar.domGo (sl + m - (a - 1)) ((b + 1) :: t) mr
          else false) = true
      rw [if_pos (Nat.le_trans (Nat.sub_le a 1) hc)]
      match a, ha with
      | c + 1, _ =>
        have hsl : sl + m - c = (sl + m - (c + 1)) + 1 := by
          have h1 : sl + m - (c + 1) = (sl + m - c) - 1 :=
            Nat.sub_succ (sl + m) c
          have h2 : 0 < sl + m - c :=
            ground.subPos (Nat.lt_of_succ_le hc)
          rw [h1]
          exact (Nat.succ_pred_eq_of_pos h2).symm
        show weylchar.domGo (sl + m - c) ((b + 1) :: t) mr = true
        rw [hsl, domGo_shift (sl + m - (c + 1)) b t mr]
        exact h'
    · rw [if_neg hc] at h'
      exact Bool.noConfusion h'
  | j + 1, sl, a :: t, [], hj, ha, h => Bool.noConfusion h
  | j + 1, sl, a :: t, m :: mr, hj, ha, h => by
    have h' : (if a ≤ sl + m
        then weylchar.domGo (sl + m - a) t mr
        else false) = true := h
    show (if a ≤ sl + m
        then weylchar.domGo (sl + m - a) (units.moveDn j t) mr
        else false) = true
    by_cases hc : a ≤ sl + m
    · rw [if_pos hc] at h'
      rw [if_pos hc]
      exact domGo_moveDn j (sl + m - a) t mr
        (Nat.lt_of_succ_lt_succ hj) ha h'
    · rw [if_neg hc] at h'
      exact Bool.noConfusion h'

/-! The occupancy's member read: a positive occupancy names a
member at the content through the group's own rows
(`blockcount.groupAt_occupancy`), and the absent content's count
vanishes. -/

/-! The discharge: the span's invariant conjunction through the
bridge, and the two hypothesis displays at the span occupancy. -/

private def inv (lam : Shape) (v : HVec) : Prop :=
  v.content.length = lam.length
    ∧ weylchar.domGo 0 v.content (rowList lam) = true
    ∧ ht v.content ≤ ht (rowList lam)

private theorem inv_step (lam : Shape) :
    ∀ (v w : HVec) (j : Nat), j + 1 < lam.length → inv lam v →
      lowerH j v = some w →
      inv lam w ∧ ht w.content < ht (rowList lam) := by
  intro v w j hj hv hw
  obtain ⟨hg, hwc⟩ := lowerH_reads hw
  have hjb : j + 1 < v.content.length := by
    rw [hv.1]
    exact hj
  have hlt : ht w.content < ht (rowList lam) := by
    rw [hwc]
    exact Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.le_of_eq (ht_moveDn j v.content hjb hg)))
      hv.2.2
  refine ⟨⟨?_, ?_, Nat.le_of_lt hlt⟩, hlt⟩
  · rw [hwc, units.length_moveDn]
    exact hv.1
  · rw [hwc]
    exact domGo_moveDn j 0 v.content (rowList lam) hjb hg hv.2.1

private theorem span_reads (lam : Shape) :
    ∃ tail, blockSpan lam = exhibit lam :: tail
      ∧ ∀ v ∈ tail, inv lam v
          ∧ ht v.content < ht (rowList lam) :=
  blockSpan_reads lam (inv lam)
    (fun v => ht v.content < ht (rowList lam))
    ⟨by rw [content_exhibit]; exact places.length_rowList lam,
     by rw [content_exhibit]; exact domGo_refl (rowList lam),
     by rw [content_exhibit]; exact Nat.le_refl _⟩
    (inv_step lam)

/-- The support clause discharged at the span's occupancy family:
every member content of the span sits at or below the top in the
dominance order (`weylchar.supportRead` at `def:blockcount`'s
span contents). -/
theorem supportRead_def (lam : Shape) :
    weylchar.supportRead lam ((blockSpan lam).map HVec.content) := by
  have hall : ∀ v ∈ blockSpan lam, inv lam v :=
    blockSpan_all lam (inv lam)
      ⟨by rw [content_exhibit]; exact places.length_rowList lam,
       by rw [content_exhibit]; exact domGo_refl (rowList lam),
       by rw [content_exhibit]; exact Nat.le_refl _⟩
      (fun v w j hj hv hw => (inv_step lam v w j hj hv hw).1)
  intro y hy
  obtain ⟨v, hv, hvy⟩ :=
    ground.mem_map_of HVec.content (blockSpan lam) y hy
  exact hvy ▸ (hall v hv).2.1

/-- The top clause discharged at the span's occupancy family: the
top content's count is one, the exhibit's line alone
(`weylchar.topRead` at `def:blockcount`'s span contents). -/
theorem topRead_def (lam : Shape) :
    weylchar.topRead lam ((blockSpan lam).map HVec.content) := by
  show countOf (rowList lam) ((blockSpan lam).map HVec.content) = 1
  rw [← occ_eq_countOf]
  obtain ⟨tail, hbs, hqr⟩ := span_reads lam
  rw [hbs]
  show (if (exhibit lam).content = rowList lam then 1 else 0)
      + occ (rowList lam) tail = 1
  rw [if_pos (content_exhibit lam),
    blockcount.occ_off tail (fun v hv hc => absurd (hqr v hv).2
      (by rw [hc]; exact Nat.lt_irrefl _))]

/-! The joined-collection clause's instantiation: the height fold is the
closure's measure — dropping by one per interior occupied lowering,
move-free at its floor, and capped by the degree against the letter
count — so the span's semantic reads land at `ht`
(`blockSpan_sem`), the exhibit's off-unit coordinate family
(`exhibit_off_unit`) the seed. -/

private theorem ht_zero_entries : ∀ nu : List Nat, ht nu = 0 →
    ∀ i, i + 1 < nu.length → ground.getAt 0 nu i = 0
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | a :: t, h, 0, hi => by
    have hta : t.length * a = 0 :=
      Nat.eq_zero_of_add_eq_zero_right h
    match ht2 : t.length, Nat.lt_of_succ_lt_succ hi with
    | m + 1, _ =>
      rw [ht2, Nat.succ_mul] at hta
      exact Nat.eq_zero_of_add_eq_zero_left hta
  | a :: t, h, i + 1, hi =>
    ht_zero_entries t (Nat.eq_zero_of_add_eq_zero_left h) i
      (Nat.lt_of_succ_lt_succ hi)

private theorem ht_le : ∀ nu : List Nat,
    ht nu ≤ sumNat nu * nu.length
  | [] => Nat.le_refl 0
  | a :: t => by
    show t.length * a + ht t
      ≤ (a + sumNat t) * (t.length + 1)
    rw [Nat.mul_succ (a + sumNat t) t.length,
      Nat.mul_comm (a + sumNat t) t.length,
      Nat.mul_add t.length a (sumNat t)]
    refine Nat.le_trans (Nat.add_le_add
      (Nat.le_refl (t.length * a))
      (Nat.le_trans (ht_le t) (Nat.le_of_eq
        (Nat.mul_comm (sumNat t) t.length)))) ?_
    exact Nat.le_add_right _ _

/-- The height measure is move-free at its floor: a content whose
height fold reads the sum's unit holds every interior letter
unoccupied, and each lowering's guard refuses. -/
theorem ht_nomove (d : Nat) : ∀ v : HVec,
    v.content.length = d → ht v.content = 0 →
    ∀ j : Nat, j < d - 1 → lowerH j v = none := by
  intro v hlen h0 j hj
  show (if 0 < ground.getAt 0 v.content j then _ else none) = none
  rw [ht_zero_entries v.content h0 j
    (by
      rw [hlen]
      exact ground.succ_lt_of_lt_pred hj)]
  exact if_neg (Nat.lt_irrefl 0)

/-- The height measure drops by exactly one per occupied interior
lowering, `ht_moveDn` at the lowering's own reads. -/
theorem ht_drop (d : Nat) : ∀ (j : Nat) (v w : HVec),
    j < d - 1 → lowerH j v = some w → v.content.length = d →
    ht w.content + 1 = ht v.content := by
  intro j v w hj heq hlen
  match blockcount.lowerH_reads heq with
  | ⟨hocc, hcont⟩ =>
    rw [hcont]
    exact ht_moveDn j v.content
      (by
        rw [hlen]
        exact ground.succ_lt_of_lt_pred hj) hocc

/-- The exhibit's height sits inside the closure's fuel, the degree
against the letter count. -/
theorem ht_exh (s : Shape) :
    ht (rowList s) ≤ degree s * s.length := by
  show ht (rowList s) ≤ sumNat (rowList s) * s.length
  rw [← places.length_rowList s]
  exact ht_le (rowList s)

/-- The span's semantic reads at the height measure
(`lem:lowerspan`'s joined-collection clause): every member sized, the content
groups independent, and every member's occupied interior lowering
image inside its group's span — the exhibit's off-unit coordinate
family the stated seed. -/
theorem spanReads (s : Shape) :
    (∀ v ∈ blockSpan s, blockcount.sized v)
      ∧ blockcount.indepAll (blockSpan s)
      ∧ blockcount.closedAt (blockSpan s) s.length :=
  blockcount.blockSpan_sem s ht (ht_nomove s.length)
    (ht_drop s.length) (ht_exh s)
    (blockcount.exhibit_sized s) (blockcount.exhibit_off_unit s)

/-- The closure instantiated at the span's proven semantic reads:
every distinct letter pair's action sends every span member to a
settled vector (`lem:lowerspan`'s word induction at the height
measure's reads). -/
theorem act_closed_def (s : Shape) (i j : Nat) (hi : i < s.length)
    (hj : j < s.length) (hij : ¬ i = j) :
    ∀ v ∈ blockcount.blockSpan s,
      blockcount.settledAt (blockcount.blockSpan s)
        (blockcount.act i j v) :=
  blockcount.act_closed s (spanReads s).1 (spanReads s).2.2
    i j hi hj hij

/-- The span-level transport instantiated at the proven reads. -/
theorem act_span_def (s : Shape) (i j : Nat) (hi : i < s.length)
    (hj : j < s.length) (hij : ¬ i = j) (mu : List Nat)
    (x : List BPair)
    (hx : x.length = (places.monomialsAt mu).length)
    (hsp : elim.spanRel (places.monomialsAt mu).length
      (blockcount.groupAt (blockcount.blockSpan s) mu) x) :
    elim.spanRel
      (places.monomialsAt (blockcount.moveAt i j mu)).length
      (blockcount.groupAt (blockcount.blockSpan s)
        (blockcount.moveAt i j mu))
      (elim.matVec
        (units.matUnitAt (blockcount.moveAt i j mu) mu i j) x) :=
  blockcount.act_span s (spanReads s).1 (spanReads s).2.2
    i j hi hj hij mu x hx hsp

/-! The raise's height read: a raising at a key grows the fold by
the letter gap, its lowering partner drops it by the gap of its
own, and an unoccupied key's lowering leaves the family whole — the
general move's strict raise the join of the two gaps. -/

private theorem ht_editAt (f : Nat → Nat) :
    ∀ (i g : Nat) (nu : List Nat), i + (g + 1) = nu.length →
      ht (ground.editAt f i nu) + ground.getAt 0 nu i * g
        = ht nu + f (ground.getAt 0 nu i) * g
  | _, _, [], h => Nat.noConfusion h
  | 0, g, a :: t, h => by
    have hg : g = t.length :=
      Nat.succ.inj ((Nat.zero_add (g + 1)).symm.trans h)
    show t.length * f a + ht t + a * g = t.length * a + ht t + f a * g
    rw [← hg, Nat.mul_comm g (f a), Nat.mul_comm g a]
    exact ground.addSwapEnds (f a * g) (ht t) (a * g)
  | i + 1, g, a :: t, h => by
    have h' : i + (g + 1) = t.length :=
      Nat.succ.inj ((Nat.succ_add i (g + 1)).symm.trans h)
    show (ground.editAt f i t).length * a + ht (ground.editAt f i t)
        + ground.getAt 0 t i * g
      = t.length * a + ht t + f (ground.getAt 0 t i) * g
    rw [ground.length_editAt f i t,
      Nat.add_assoc (t.length * a) (ht (ground.editAt f i t))
        (ground.getAt 0 t i * g),
      ht_editAt f i g t h', Nat.add_assoc]

private theorem ht_bumpAt : ∀ (i g : Nat) (nu : List Nat),
    i + (g + 1) = nu.length →
    ht (ground.bumpAt i nu) = ht nu + g
  := fun i g nu h => by
    refine ground.addCancelR (ground.getAt 0 nu i * g) ?_
    refine (ht_editAt (fun x => x + 1) i g nu h).trans ?_
    rw [Nat.succ_mul (ground.getAt 0 nu i) g,
      ← Nat.add_assoc (ht nu) (ground.getAt 0 nu i * g) g,
      Nat.add_right_comm (ht nu) (ground.getAt 0 nu i * g) g]

private theorem ht_dipAt : ∀ (j g : Nat) (nu : List Nat),
    j + (g + 1) = nu.length → 0 < ground.getAt 0 nu j →
    ht nu = ht (ground.dipAt j nu) + g
  := fun j g nu h hocc => by
    have hb : ground.getAt 0 nu j - 1 + 1 = ground.getAt 0 nu j :=
      ground.subAdd hocc
    have hgen := ht_editAt (fun x => x - 1) j g nu h
    rw [(congrArg (fun z => z * g) hb).symm.trans
        (Nat.succ_mul (ground.getAt 0 nu j - 1) g),
      ← Nat.add_assoc (ht (ground.editAt (fun x => x - 1) j nu))
        ((ground.getAt 0 nu j - 1) * g) g] at hgen
    refine (ground.addCancelR ((ground.getAt 0 nu j - 1) * g) ?_).symm
    rw [Nat.add_right_comm (ht (ground.dipAt j nu)) g
        ((ground.getAt 0 nu j - 1) * g)]
    exact hgen

private theorem lt_add_succ (a m : Nat) : a < a + (m + 1) := by
  show a + 1 ≤ a + (m + 1)
  rw [Nat.add_comm m 1, ← Nat.add_assoc]
  exact Nat.le_add_right (a + 1) m

private theorem add_shuffle (i k g : Nat) :
    i + (k + (g + 1) + 1) = i + 1 + k + (g + 1) := by
  show i + (k + g) + 1 + 1 = i + 1 + k + g + 1
  rw [Nat.add_right_comm i 1 k, ← Nat.add_assoc i k g,
    Nat.add_assoc (i + k) 1 g, Nat.add_comm 1 g,
    ← Nat.add_assoc (i + k) g 1]

private theorem add_regroup (d g k : Nat) :
    d + (k + (g + 1)) = d + g + (k + 1) := by
  show d + (k + g) + 1 = d + g + k + 1
  rw [← Nat.add_assoc d k g, Nat.add_right_comm d k g]

/-- A raising strictly raises the height fold — the moved box's
weight grows by the letter gap, `ht_moveDn`'s mirror at the general
move; the exhaustion producer's pick reads it (the height-maximal
member's raised contents are unoccupied). -/
theorem ht_moveAt_raise (i j : Nat) (mu : List Nat)
    (hij : i < j) (hj : j < mu.length) :
    ht mu < ht (moveAt i j mu) := by
  obtain ⟨gj, hgj⟩ := Nat.le.dest hj
  obtain ⟨k, hk⟩ := Nat.le.dest hij
  have hgjs : j + (gj + 1) = mu.length :=
    (Nat.succ_add j gj).symm.trans hgj
  have hgis : i + (k + (gj + 1) + 1) = mu.length := by
    rw [add_shuffle i k gj, hk]
    exact hgjs
  show ht mu < ht (ground.bumpAt i (ground.dipAt j mu))
  match Nat.eq_zero_or_pos (ground.getAt 0 mu j) with
  | Or.inl hz =>
    rw [ground.dipAt_of_zero j mu hz, ht_bumpAt i (k + (gj + 1)) mu hgis]
    exact lt_add_succ (ht mu) (k + gj)
  | Or.inr hp =>
    rw [ht_bumpAt i (k + (gj + 1)) (ground.dipAt j mu)
        (by rw [ground.length_dipAt j mu]; exact hgis),
      ht_dipAt j gj mu hgjs hp,
      add_regroup (ht (ground.dipAt j mu)) gj k]
    exact lt_add_succ (ht (ground.dipAt j mu) + gj) k

/-- An off-unit sized seed at the letter width closes to a pool at
the stated data, the seed machinery assembled once: the closure's
sizes, widths, head-cons provenance and group independence are
`seedSpan_sem`'s and `seedSpan_prov`'s at the height measure, and
the pool is closed under every letter-pair action at the seed's
adjacent top reads (`pool_act_closed`). -/
theorem seed_closed (d fuel : Nat) (w : blockcount.HVec)
    (hsz : blockcount.sized w) (hwd : w.content.length = d)
    (hoff : ¬ poly.unitTail w.coords)
    (htop : ∀ jr, jr + 1 < d →
      poly.unitTail (blockcount.act jr (jr + 1) w).coords)
    (hfuel : ht w.content ≤ fuel) :
    ∃ t, blockcount.closeSpan d fuel [w] [w] = w :: t
      ∧ (∀ x ∈ w :: t, blockcount.sized x)
      ∧ (∀ x ∈ w :: t, x.content.length = d)
      ∧ (∀ k, k < t.length → ∃ i, i ≤ k ∧ ∃ j, j + 1 < d ∧
          blockcount.lowerH j
              (ground.getAt (⟨[], []⟩ : blockcount.HVec) (w :: t) i)
            = some (ground.getAt (⟨[], []⟩ : blockcount.HVec) t k))
      ∧ blockcount.indepAll (w :: t)
      ∧ (∀ x ∈ w :: t, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
          blockcount.settledAt (w :: t) (blockcount.act i j x)) := by
  have hsem := blockcount.seedSpan_sem d fuel ht w
    (ht_nomove d) (ht_drop d) hsz hwd hoff hfuel
  match blockcount.seedSpan_prov d fuel w with
  | ⟨t, htl, hprov⟩ =>
    rw [htl] at hsem
    obtain ⟨hszv, hwidv, hindv, hclv⟩ := hsem
    refine ⟨t, htl, hszv, hwidv, hprov, hindv, ?_⟩
    intro x hx i hi j hj hij
    exact blockcount.pool_act_closed d w t hszv hwidv hprov hclv
      htop i j hi hj hij x hx

end lowerspan
