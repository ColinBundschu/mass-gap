import MassGap.Fusion
/-!
`thm:drift` — the uniform drift at the label calculus: the
dimension-weighted adjoint row's Casimir fold reads
`Σ_c N^c_{Rθ} d_c d_f Q(c) = d_R d_θ (d_f Q(R) + 2 d_f²)` at every
shape of the width, `fusion.driftLaw`'s `dataA` instance at every
label.  The derivation sums `thm:weylchar`'s trace recursion over
the block's occupancy family (`casimir.recRead_def`): the moved
folds reindex at the move's round trip to the target's own reads,
the swap symmetry (`strings.symRead_def`) reads the moment folds
place-free, the fused carrier's family splits over the channels at
the exhaustion's content refinement
(`blockcount.gradedDim_countAt`) and over the factors at the
contents' addition, and the square identity (`c2hat.squareAll`)
with the dimension display (`blockcount.fusionCount_dim`) closes
the display at the shared degree with `d_f Q(θ) = 2 d_f²`.  The
strictness read is `cor:weyldim`'s factor comparison: a nonunit
reduced shape's consecutive gap factor clears the unit display's.

The support tier stands here.  The recursion display's reindexed
place-pair weights are `wCross` and `wSqP`, the place products'
and place squares' folds over the width's pairs.  The moment folds
over a pool (`mom1`, `mom1At`, `mom2At`, `mom11`) read place-free
at the span: the span's content family is transposition-invariant,
so a weight's fold is blind to a letter swap
(`fold_swap_invariant`) and every place reads the first's
(`mom1At_free`, `pairFold_free`); the pair folds then collapse to
one moment against the pair count (`wCross_fold`, `wSqP_fold`) and
the first moment reads the degree against the span's count
(`mom1_deg`).  The fused pool's family splits over its two factors
at the tensor's componentwise content (`fold_fusedAt`).  The
display conversion `qconv` reads the shape's display square
against the row list's cleared read at the unit display's own —
`c2hat.squareAll` on the squares, and the sorted rows' gap fold
against the unit display's dot, `2 ⟨λ, u⟩ = ⟨λ, 2ρ⟩ + (d_f + 1) k`
(`crossRead`) — with the adjoint's own value `d_f Q(θ) = 2 d_f²`
(`dfQ_theta`, `prop:anchor`'s tower at index one).

The theorem's own tier stands above it.  The fused pool's content
family refines over the exhaustion's channels (`fold_channels`),
each channel weighted by its own fusion count at the tops' row
lists and read on its shape's block — a channel's occupied block
content is a pool content wherever the channel's count is
occupied, so the pool's distinct contents index both reads — and
every channel carries the two factors' joined degree
(`exhaust_degree`).  The summed recursion reads at the moments
(`momRec`): the shifted squares split at the display's join into
the span's square moment against the width, its first moment
against the unit display's total, and the unit display's own
square against the span's count, every place of the width reading
the first place's.  The fused pool's moments split over its two
factors at the contents' componentwise addition (`momT1`, `momT2`,
`momT11`), the mixed terms the two factors' first moments at the
shared width.  The channel recursion (`foldRec`) then meets the
two factors' own at those splits, the shared cross weight
withdraws (`assembleC`), and the display conversion closes at the
channels' one raised degree (`assembleFinal`) with the first
moments the degrees' (`mom1_deg`) — `driftFold`, the row's fold in
closed form.  The row read (`readAll`) bridges the label
calculus's guarded enumeration to that index: each survivor reads
at its own reduced label with the count at the matched-degree lift
and the dimension and cleared Casimir one value at the class, the
fast count is the block count (`cor:steinberg`), each channel is
listed once at its own degree, and every off-channel shape's count
is vacant.  The strictness read (`strict`) is `cor:weyldim`'s
factor comparison: the rows descend weakly from an occupied head
to the withdrawn full column's vacant last row, so some adjacent
pair drops strictly; every display gap dominates the unit
display's at the rows' own monotonicity (`gapProd_le`), and the
dropping pair's factor doubles it (`gapProd_double`).
-/

namespace drift
open ground places blockcount

/-- The place products' pair fold at a content, the recursion
display's reindexed cross weight. -/
def wCross (mu : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun ab => ground.getAt 0 mu ab.1 * ground.getAt 0 mu ab.2)
    (places.pairsOf mu.length)

/-- The place squares' pair fold at a content, the reindexed
square weight. -/
def wSqP (mu : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun ab => ground.getAt 0 mu ab.1 * ground.getAt 0 mu ab.1)
    (places.pairsOf mu.length)

/-! The moment folds over a pool: the first place's occupancy, a
stated place's occupancy and its square, and the first two places'
product, each summed over the pool's members. -/

/-- The pool's first-place moment. -/
private def mom1 (P : List HVec) : Nat :=
  ground.famFold Nat.add 0 (fun v => ground.getAt 0 v.content 0) P

/-- The pool's moment at a stated place. -/
private def mom1At (p : Nat) (P : List HVec) : Nat :=
  ground.famFold Nat.add 0 (fun v => ground.getAt 0 v.content p) P

/-- The pool's square moment at a stated place. -/
private def mom2At (p : Nat) (P : List HVec) : Nat :=
  ground.famFold Nat.add 0
    (fun v => ground.getAt 0 v.content p * ground.getAt 0 v.content p) P

/-- The pool's cross moment at the first two places. -/
private def mom11 (P : List HVec) : Nat :=
  ground.famFold Nat.add 0
    (fun v => ground.getAt 0 v.content 0 * ground.getAt 0 v.content 1) P

/-! The swap transport: the block span's content family is
invariant under every letter transposition
(`strings.symRead_def`), so a weight's fold over the span reads
the transposed places' fold, and every place of the width reads
the first place's. -/

/-- A weight's fold over the span is blind to a letter
transposition: the contents' multiplicities are the transposed
contents' own, read on the distinct index both ways. -/
private theorem fold_swap_invariant (lam : Shape) (F : List Nat → Nat)
    (i j : Nat) (hi : i < lam.length) (hj : j < lam.length) :
    ground.famFold Nat.add 0
        (fun v => F (places.swapPair i j v.content)) (blockSpan lam)
      = ground.famFold Nat.add 0 (fun v => F v.content)
        (blockSpan lam) := by
  have hsym := strings.symRead_def lam
  have hmem : ∀ x : List Nat,
      0 < ground.countOf x ((blockSpan lam).map HVec.content) →
      ground.countOf x
          (ground.dedupL ((blockSpan lam).map HVec.content)) = 1 :=
    fun x hx => ground.countOf_dedupL_one (ground.mem_of_countOf_pos x _ hx)
  have hswapCnt : ∀ x : List Nat,
      ground.countOf x
          ((ground.dedupL ((blockSpan lam).map HVec.content)).map
            (places.swapPair i j))
        = ground.countOf (places.swapPair i j x)
          (ground.dedupL ((blockSpan lam).map HVec.content)) :=
    fun x => ground.countOf_map_iff (places.swapPair i j) _ x
      (places.swapPair i j x)
      (fun v _ => ⟨fun hxv => by
          rw [hxv, places.swapPair_swapPair i j v],
        fun hvx => by
          rw [← hvx, places.swapPair_swapPair i j x]⟩)
  have hmem' : ∀ x : List Nat,
      0 < ground.countOf x ((blockSpan lam).map HVec.content) →
      ground.countOf x
          ((ground.dedupL ((blockSpan lam).map HVec.content)).map
            (places.swapPair i j)) = 1 := by
    intro x hx
    rw [hswapCnt x]
    refine hmem (places.swapPair i j x) ?_
    rw [hsym x (ground.mem_of_countOf_pos x _ hx) i hi j hj]
    exact hx
  have e2 := ground.famFold_countCollect F
    ((blockSpan lam).map HVec.content)
    ((ground.dedupL ((blockSpan lam).map HVec.content)).map
      (places.swapPair i j)) hmem'
  have e3 := ground.famFold_map Nat.add 0
    (fun m => ground.countOf m ((blockSpan lam).map HVec.content) * F m)
    (places.swapPair i j)
    (ground.dedupL ((blockSpan lam).map HVec.content))
  have e4 : ground.famFold Nat.add 0
        (fun m => ground.countOf (places.swapPair i j m)
            ((blockSpan lam).map HVec.content)
          * F (places.swapPair i j m))
        (ground.dedupL ((blockSpan lam).map HVec.content))
      = ground.famFold Nat.add 0
        (fun m => ground.countOf m ((blockSpan lam).map HVec.content)
          * F (places.swapPair i j m))
        (ground.dedupL ((blockSpan lam).map HVec.content)) :=
    ground.famFold_congr_members Nat.add 0 _ _ _
      (fun m hm => by
        rw [hsym m (ground.mem_of_dedupL
          (ground.mem_of_countOf_pos m _ hm)) i hi j hj])
  have e5 := ground.famFold_countCollect
    (fun mu => F (places.swapPair i j mu))
    ((blockSpan lam).map HVec.content)
    (ground.dedupL ((blockSpan lam).map HVec.content)) hmem
  rw [← ground.famFold_map Nat.add 0
      (fun mu => F (places.swapPair i j mu)) HVec.content (blockSpan lam),
    ← ground.famFold_map Nat.add 0 F HVec.content (blockSpan lam),
    e5, ← e4, ← e3]
  exact e2.symm

/-- A two-place weight's fold over the span at transposed read
places: the transposition's entry reads carry the fold across. -/
private theorem pair_swap (lam : Shape) (G : Nat → Nat → Nat)
    (i j x y px py : Nat) (hi : i < lam.length) (hj : j < lam.length)
    (hpx : ∀ mu : List Nat, mu.length = lam.length →
      ground.getAt 0 (places.swapPair i j mu) x = ground.getAt 0 mu px)
    (hpy : ∀ mu : List Nat, mu.length = lam.length →
      ground.getAt 0 (places.swapPair i j mu) y = ground.getAt 0 mu py) :
    ground.famFold Nat.add 0
        (fun v => G (ground.getAt 0 v.content px)
          (ground.getAt 0 v.content py)) (blockSpan lam)
      = ground.famFold Nat.add 0
        (fun v => G (ground.getAt 0 v.content x)
          (ground.getAt 0 v.content y)) (blockSpan lam) := by
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _ _
      (blockSpan lam) (fun v hv => ?_))
    (fold_swap_invariant lam
      (fun mu => G (ground.getAt 0 mu x) (ground.getAt 0 mu y)) i j hi hj)
  have hw : v.content.length = lam.length :=
    blockcount.blockSpan_width lam v (ground.mem_of_countOf_pos v _ hv)
  rw [hpx v.content hw, hpy v.content hw]

/-- The span's moment at an interior place is the first place's:
the transposition of the two places carries the fold. -/
private theorem mom1At_free (lam : Shape) (p : Nat)
    (hp : p < lam.length) :
    mom1At p (blockSpan lam) = mom1 (blockSpan lam) := by
  cases p with
  | zero => rfl
  | succ q =>
    have h0 : 0 < lam.length :=
      Nat.lt_of_lt_of_le (Nat.succ_pos q) (Nat.le_of_lt hp)
    have hne : ¬ (0 = q + 1) := fun h => Nat.noConfusion h
    exact pair_swap lam (fun a _ => a) 0 (q + 1) 0 0 (q + 1) (q + 1)
      h0 hp
      (fun mu hmu => places.getAt_swapPair_fst mu hne
        (by rw [hmu]; exact h0) (by rw [hmu]; exact hp))
      (fun mu hmu => places.getAt_swapPair_fst mu hne
        (by rw [hmu]; exact h0) (by rw [hmu]; exact hp))

/-- The span's two-place fold at an ordered pair of the width is
the first two places' own: the deeper place moves to the second by
one transposition and the shallower to the first by another. -/
private theorem pairFold_free (lam : Shape) (G : Nat → Nat → Nat)
    (a b : Nat) (hab : a < b) (hb : b < lam.length) :
    ground.famFold Nat.add 0
        (fun v => G (ground.getAt 0 v.content a)
          (ground.getAt 0 v.content b)) (blockSpan lam)
      = ground.famFold Nat.add 0
        (fun v => G (ground.getAt 0 v.content 0)
          (ground.getAt 0 v.content 1)) (blockSpan lam) := by
  have h0 : 0 < lam.length := Nat.lt_of_le_of_lt (Nat.zero_le b) hb
  have hbpos : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le a) hab
  have halam : a < lam.length := Nat.lt_trans hab hb
  by_cases hb1 : b = 1
  · rw [hb1] at hab
    rw [hb1, Nat.le_antisymm (Nat.le_of_succ_le_succ hab) (Nat.zero_le a)]
  · have h1b : 1 < b := Nat.lt_of_le_of_ne hbpos (fun h => hb1 h.symm)
    have h1lam : 1 < lam.length := Nat.lt_trans h1b hb
    have hb0 : ¬ ((0 : Nat) = b) := by
      intro h
      rw [← h] at hbpos
      exact absurd hbpos (Nat.lt_irrefl 0)
    have hb0' : ¬ (b = 0) := fun h => hb0 h.symm
    have hba : ¬ (b = a) := by
      intro h
      rw [h] at hab
      exact absurd hab (Nat.lt_irrefl a)
    have step2 : ground.famFold Nat.add 0
          (fun v => G (ground.getAt 0 v.content 0)
            (ground.getAt 0 v.content b)) (blockSpan lam)
        = ground.famFold Nat.add 0
          (fun v => G (ground.getAt 0 v.content 0)
            (ground.getAt 0 v.content 1)) (blockSpan lam) :=
      pair_swap lam G 1 b 0 1 0 b h1lam hb
        (fun mu hmu => places.getAt_swapPair_ne mu
          (by rw [hmu]; exact h1lam) (by rw [hmu]; exact hb)
          (fun h => Nat.noConfusion h) hb0)
        (fun mu hmu => places.getAt_swapPair_fst mu
          (fun h => hb1 h.symm)
          (by rw [hmu]; exact h1lam) (by rw [hmu]; exact hb))
    by_cases ha0 : a = 0
    · rw [ha0]
      exact step2
    · refine Eq.trans ?_ step2
      exact pair_swap lam G 0 a 0 b a b h0 halam
        (fun mu hmu => places.getAt_swapPair_fst mu
          (fun h => ha0 h.symm)
          (by rw [hmu]; exact h0) (by rw [hmu]; exact halam))
        (fun mu hmu => places.getAt_swapPair_ne mu
          (by rw [hmu]; exact h0) (by rw [hmu]; exact halam)
          hb0' hba)

/-! The pair-fold collapse: the width's pair count against one
moment, the span's places all reading alike. -/

/-- The cross weight's fold over the span: the width's pair count
against the span's cross moment. -/
private theorem wCross_fold (lam : Shape) :
    ground.famFold Nat.add 0 (fun v => wCross v.content) (blockSpan lam)
      = (places.pairsOf lam.length).length * mom11 (blockSpan lam) := by
  have hc : ground.famFold Nat.add 0 (fun v => wCross v.content)
        (blockSpan lam)
      = ground.famFold Nat.add 0
        (fun v => ground.famFold Nat.add 0
          (fun ab => ground.getAt 0 v.content ab.1
            * ground.getAt 0 v.content ab.2)
          (places.pairsOf lam.length)) (blockSpan lam) :=
    ground.famFold_congr_members Nat.add 0 _ _ (blockSpan lam)
      (fun v hv => by
        show ground.famFold Nat.add 0
            (fun ab => ground.getAt 0 v.content ab.1
              * ground.getAt 0 v.content ab.2)
            (places.pairsOf v.content.length)
          = ground.famFold Nat.add 0
            (fun ab => ground.getAt 0 v.content ab.1
              * ground.getAt 0 v.content ab.2)
            (places.pairsOf lam.length)
        rw [blockcount.blockSpan_width lam v
          (ground.mem_of_countOf_pos v _ hv)])
  have hpair : ground.famFold Nat.add 0
        (fun ab => ground.famFold Nat.add 0
          (fun v => ground.getAt 0 v.content ab.1
            * ground.getAt 0 v.content ab.2) (blockSpan lam))
        (places.pairsOf lam.length)
      = ground.famFold Nat.add 0
        (fun _ => mom11 (blockSpan lam)) (places.pairsOf lam.length) :=
    ground.famFold_congr_members Nat.add 0 _ _
      (places.pairsOf lam.length)
      (fun ab hab =>
        pairFold_free lam (fun p q => p * q) ab.1 ab.2
          (places.pairs_mem lam.length ab hab).1
          (places.pairs_mem lam.length ab hab).2)
  rw [hc, ground.famFold_swap
      (fun (v : HVec) (ab : Nat × Nat) =>
        ground.getAt 0 v.content ab.1 * ground.getAt 0 v.content ab.2)
      (blockSpan lam) (places.pairsOf lam.length),
    hpair, ground.famFold_const (mom11 (blockSpan lam))
      (places.pairsOf lam.length)]

/-- The square weight's fold over the span: the width's pair count
against the span's first-place square moment. -/
private theorem wSqP_fold (lam : Shape) :
    ground.famFold Nat.add 0 (fun v => wSqP v.content) (blockSpan lam)
      = (places.pairsOf lam.length).length
        * mom2At 0 (blockSpan lam) := by
  have hc : ground.famFold Nat.add 0 (fun v => wSqP v.content)
        (blockSpan lam)
      = ground.famFold Nat.add 0
        (fun v => ground.famFold Nat.add 0
          (fun ab => ground.getAt 0 v.content ab.1
            * ground.getAt 0 v.content ab.1)
          (places.pairsOf lam.length)) (blockSpan lam) :=
    ground.famFold_congr_members Nat.add 0 _ _ (blockSpan lam)
      (fun v hv => by
        show ground.famFold Nat.add 0
            (fun ab => ground.getAt 0 v.content ab.1
              * ground.getAt 0 v.content ab.1)
            (places.pairsOf v.content.length)
          = ground.famFold Nat.add 0
            (fun ab => ground.getAt 0 v.content ab.1
              * ground.getAt 0 v.content ab.1)
            (places.pairsOf lam.length)
        rw [blockcount.blockSpan_width lam v
          (ground.mem_of_countOf_pos v _ hv)])
  have hpair : ground.famFold Nat.add 0
        (fun ab => ground.famFold Nat.add 0
          (fun v => ground.getAt 0 v.content ab.1
            * ground.getAt 0 v.content ab.1) (blockSpan lam))
        (places.pairsOf lam.length)
      = ground.famFold Nat.add 0
        (fun _ => mom2At 0 (blockSpan lam))
        (places.pairsOf lam.length) :=
    ground.famFold_congr_members Nat.add 0 _ _
      (places.pairsOf lam.length)
      (fun ab hab =>
        pairFold_free lam (fun p _ => p * p) ab.1 ab.2
          (places.pairs_mem lam.length ab hab).1
          (places.pairs_mem lam.length ab hab).2)
  rw [hc, ground.famFold_swap
      (fun (v : HVec) (ab : Nat × Nat) =>
        ground.getAt 0 v.content ab.1 * ground.getAt 0 v.content ab.1)
      (blockSpan lam) (places.pairsOf lam.length),
    hpair, ground.famFold_const (mom2At 0 (blockSpan lam))
      (places.pairsOf lam.length)]

/-- The span's first moment against the width reads the shape's
box total against the span's count: every member's content sums to
the degree, and the places' moments are one value. -/
private theorem mom1_deg (lam : Shape) :
    lam.length * mom1 (blockSpan lam)
      = places.degree lam * (blockSpan lam).length := by
  have hdeg : ground.famFold Nat.add 0
        (fun v => ground.sumNat v.content) (blockSpan lam)
      = (blockSpan lam).length * places.degree lam := by
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun _ => places.degree lam) (blockSpan lam)
        (fun v hv => blockcount.blockSpan_degree lam v
          (ground.mem_of_countOf_pos v _ hv)),
      ground.famFold_const (places.degree lam) (blockSpan lam)]
  have hidx : ground.famFold Nat.add 0
        (fun v => ground.sumNat v.content) (blockSpan lam)
      = ground.famFold Nat.add 0
        (fun v => ground.famFold Nat.add 0
          (fun k => ground.getAt 0 v.content k)
          (List.range lam.length)) (blockSpan lam) :=
    ground.famFold_congr_members Nat.add 0 _ _ (blockSpan lam)
      (fun v hv => by
        rw [← ground.sumIndex v.content,
          blockcount.blockSpan_width lam v
            (ground.mem_of_countOf_pos v _ hv)])
  have hfree : ground.famFold Nat.add 0
        (fun k => ground.famFold Nat.add 0
          (fun v => ground.getAt 0 v.content k) (blockSpan lam))
        (List.range lam.length)
      = lam.length * mom1 (blockSpan lam) := by
    rw [ground.famFold_congr_members Nat.add 0
        (fun k => ground.famFold Nat.add 0
          (fun (v : HVec) => ground.getAt 0 v.content k) (blockSpan lam))
        (fun _ => mom1 (blockSpan lam)) (List.range lam.length)
        (fun k hk => mom1At_free lam k (ground.ltOfMem hk)),
      ground.famFold_const (mom1 (blockSpan lam))
        (List.range lam.length), ground.length_range lam.length]
  rw [← hfree, ← ground.famFold_swap
      (fun (v : HVec) (k : Nat) => ground.getAt 0 v.content k)
      (blockSpan lam) (List.range lam.length),
    ← hidx, hdeg, Nat.mul_comm (blockSpan lam).length
      (places.degree lam)]

/-- The fused pool's family splits over the two factors: each
member's content is the factors' componentwise sum. -/
private theorem fold_fusedAt (A B : List HVec) (W : List Nat → Nat) :
    ground.famFold Nat.add 0 (fun v => W v.content)
        (blockcount.fusedAt A B)
      = ground.famFold Nat.add 0
        (fun x => ground.famFold Nat.add 0
          (fun y => W (List.zipWith (fun p q => p + q)
            x.content y.content)) B) A := by
  show ground.famFold Nat.add 0 (fun v => W v.content)
      (A.flatMap (fun v => B.map (blockcount.tensorH v))) = _
  rw [ground.famFold_flatMap (fun v : HVec => W v.content)
    (fun v => B.map (blockcount.tensorH v)) A]
  exact ground.famFold_congr_all Nat.add 0 _ _
    (fun x => ground.famFold_map Nat.add 0
      (fun v : HVec => W v.content) (blockcount.tensorH x) B) A

/-! The display conversion: the shape's display square against the
row list's cleared read.  The display is the rows against the unit
display entry by entry, the square splits at the join
(`weylchar.sqSplit`), the squares' half is `def:c2hat`'s square
identity, and the dot's half is the sorted rows' gap fold. -/

/-- The unit display peels its head: the width at the first place
with the shortened unit display beneath. -/
private theorem unitDisp_cons (m : Nat) :
    places.unitDisp (m + 1) = (m + 1) :: places.unitDisp m := by
  rw [weylchar.unitDisp_eq (m + 1), weylchar.unitDisp_eq m,
    ground.range_cons m]
  show (m + 1) :: ((List.range m).map (fun j => j + 1)).map
      (fun i => m + 1 - i)
    = (m + 1) :: (List.range m).map (fun i => m - i)
  rw [ground.map_map (fun j => j + 1) (fun i => m + 1 - i)
      (List.range m),
    ground.map_congr_all (fun j => m + 1 - (j + 1)) (fun i => m - i)
      (fun j => Nat.succ_sub_succ m j) (List.range m)]

/-- The head step's regrouping at the gap join: the head's doubled
weight against the raised width's. -/
private theorem crossRing (x m s r f : Nat) (hj : f + s = m * x) :
    2 * (x * (m + 1)) + (r + (m + 1) * s)
      = f + r + (m + 1 + 1) * (x + s) := by
  refine ground.addCancelR s ?_
  have hR : f + r + (m + 1 + 1) * (x + s) + s
      = f + s + (r + (m + 1 + 1) * (x + s)) := by
    rw [Nat.add_assoc f r ((m + 1 + 1) * (x + s)),
      Nat.add_right_comm f (r + (m + 1 + 1) * (x + s)) s]
  have hL : 2 * (x * (m + 1)) + (r + (m + 1) * s) + s
      = 2 * (x * (m + 1)) + (r + (m + 1 + 1) * s) := by
    rw [Nat.add_assoc (2 * (x * (m + 1))) (r + (m + 1) * s) s,
      Nat.add_assoc r ((m + 1) * s) s,
      ground.mulAddR (m + 1) 1 s, Nat.one_mul s]
  have hx : 2 * (x * (m + 1)) = m * x + (m + 1 + 1) * x := by
    rw [Nat.mul_succ x m, Nat.left_distrib 2 (x * m) x,
      ground.mulAddR (m + 1) 1 x, Nat.one_mul x,
      ground.mulAddR m 1 x, Nat.one_mul x,
      Nat.mul_comm x m, Nat.two_mul (m * x), Nat.two_mul x,
      Nat.add_assoc (m * x) (m * x) (x + x), Nat.add_assoc (m * x) x x]
  rw [hR, hL, hj, hx, Nat.left_distrib (m + 1 + 1) x s,
    Nat.add_assoc (m * x) ((m + 1 + 1) * x)
      (r + (m + 1 + 1) * s),
    Nat.add_left_comm ((m + 1 + 1) * x) r ((m + 1 + 1) * s)]

/-- The sorted rows' dot against the unit display, doubled: the
pair-gap fold with the raised width against the box total,
`2 ⟨λ, u⟩ = ⟨λ, 2ρ⟩ + (d_f + 1) k`. -/
private theorem crossRead : ∀ l : List Nat,
    (∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) →
    2 * ground.dotNat l (places.unitDisp l.length)
      = c2hat.rho2 l + (l.length + 1) * ground.sumNat l
  | [], _ => rfl
  | x :: t, hdesc => by
    have hih := crossRead t
      (fun p hp => hdesc (p + 1) (Nat.succ_lt_succ hp))
    have hj := ground.gapFold_total x t
      (fun q hq => ground.descLe (x :: t) 0 (q + 1) hdesc
        (Nat.zero_le (q + 1)) (Nat.succ_lt_succ hq))
    show 2 * ground.dotNat (x :: t) (places.unitDisp (t.length + 1))
      = t.foldl (fun acc y => acc + (x - y)) 0 + c2hat.rho2 t
        + (t.length + 1 + 1) * (x + ground.sumNat t)
    rw [unitDisp_cons t.length]
    show 2 * (x * (t.length + 1)
        + ground.dotNat t (places.unitDisp t.length)) = _
    rw [Nat.left_distrib 2 (x * (t.length + 1))
        (ground.dotNat t (places.unitDisp t.length)), hih]
    exact crossRing x t.length (ground.sumNat t) (c2hat.rho2 t)
      (t.foldl (fun acc y => acc + (x - y)) 0) hj

/-- The display square and the rows' square fold are one read. -/
private theorem stdSq_sumSq : ∀ z : List Nat,
    weylchar.stdSq z = c2hat.sumSq z
  | [] => rfl
  | a :: z => by
    show a * a + weylchar.stdSq z = a * a + c2hat.sumSq z
    rw [stdSq_sumSq z]

/-- The conversion's regrouping at the four collected terms. -/
private theorem qRing (kk g nr p c : Nat) :
    kk + g + (nr + p) + c = g + nr + kk + p + c := by
  rw [Nat.add_assoc kk g (nr + p), ← Nat.add_assoc g nr p,
    ← Nat.add_assoc kk (g + nr) p, Nat.add_comm kk (g + nr)]

/-- The display conversion: the shape's display square at the
width reads the cleared traceless value against the box total's
square, the raised width's box weight, and the unit display's own
square. -/
private theorem qconv (s : Shape) :
    s.length * weylchar.stdSq (places.display s)
      = c2hat.dfQ s + places.degree s * places.degree s
        + s.length * (s.length + 1) * places.degree s
        + s.length * weylchar.stdSq (places.unitDisp s.length) := by
  have hlen : (places.rowList s).length = s.length :=
    places.length_rowList s
  have hsplit : weylchar.stdSq (places.display s)
      = weylchar.stdSq (places.rowList s)
        + 2 * ground.dotNat (places.rowList s)
            (places.unitDisp s.length)
        + weylchar.stdSq (places.unitDisp s.length) := by
    rw [weylchar.display_zip s]
    exact weylchar.sqSplit (places.rowList s) (places.unitDisp s.length)
      (by rw [hlen, places.length_unitDisp s.length])
  have hsq : s.length * weylchar.stdSq (places.rowList s)
      = places.degree s * places.degree s
        + c2hat.sqGaps (places.rowList s) := by
    rw [stdSq_sumSq (places.rowList s)]
    exact c2hat.squareAll s
  have hcross : 2 * ground.dotNat (places.rowList s)
        (places.unitDisp s.length)
      = c2hat.rho2 (places.rowList s)
        + (s.length + 1) * places.degree s := by
    have h := crossRead (places.rowList s)
      (fun p hp => places.rowList_le s p (by rw [← hlen]; exact hp))
    rw [hlen] at h
    exact h
  show s.length * weylchar.stdSq (places.display s)
    = c2hat.sqGaps (places.rowList s)
        + s.length * c2hat.rho2 (places.rowList s)
      + places.degree s * places.degree s
      + s.length * (s.length + 1) * places.degree s
      + s.length * weylchar.stdSq (places.unitDisp s.length)
  rw [hsplit,
    Nat.left_distrib s.length
      (weylchar.stdSq (places.rowList s)
        + 2 * ground.dotNat (places.rowList s)
            (places.unitDisp s.length))
      (weylchar.stdSq (places.unitDisp s.length)),
    Nat.left_distrib s.length (weylchar.stdSq (places.rowList s))
      (2 * ground.dotNat (places.rowList s)
        (places.unitDisp s.length)),
    hsq, hcross,
    Nat.left_distrib s.length (c2hat.rho2 (places.rowList s))
      ((s.length + 1) * places.degree s),
    ← ground.mulAssoc s.length (s.length + 1) (places.degree s)]
  exact qRing (places.degree s * places.degree s)
    (c2hat.sqGaps (places.rowList s))
    (s.length * c2hat.rho2 (places.rowList s))
    (s.length * (s.length + 1) * places.degree s)
    (s.length * weylchar.stdSq (places.unitDisp s.length))

/-- The adjoint's cleared read, `d_f Q(θ) = 2 d_f²`
(`prop:anchor`'s tower at index one). -/
private theorem dfQ_theta (d : Nat) (hd : 2 ≤ d) :
    c2hat.dfQ (adjchar.theta d) = 2 * d * d := by
  have h := anchor.tower_dfQ d 1 hd
  rw [anchor.towerShape_one d] at h
  have hd1 : 1 + (d - 1) = d := by
    rw [Nat.add_comm 1 (d - 1)]
    exact ground.subAdd (Nat.le_trans (Nat.le_succ 1) hd)
  rw [h, Nat.one_mul (1 + (d - 1)), hd1]

/-! The summed trace recursion: `thm:weylchar`'s display read at
every key of the recursion family and summed.  The moved folds
reindex at the pair move's exact inverse — a target's occupied
source is the reversed move at the raised letter's own shift, the
shift determined by that letter's count — so the family's fold of a
moved weight reads the occupancy family's own fold at the sources'
values (`moved_reindex`, `exch_at` one letter pair at a time).  The
reindexed weights split at the shift fold's constant offset
(`inner_split`): the second letter's read is the cross weight
against the shared shift total, the first letter's the square
weight against the same total, and the shared summand cancels. -/

/-- A scalar against a key's indicator reads the guarded scalar. -/
private theorem mulIf (c : Nat) {P : Prop} [Decidable P] :
    c * (if P then 1 else 0) = if P then c else 0 := by
  by_cases h : P
  · rw [if_pos h, if_pos h, Nat.mul_one]
  · rw [if_neg h, if_neg h, Nat.mul_zero]

/-- A shift family's member is a positive shift within the
count. -/
private theorem shift_mem {M l : Nat}
    (h : 0 < ground.countOf l
      ((List.range M).map (fun k => k + 1))) :
    ∃ j, j < M ∧ l = j + 1 := by
  obtain ⟨j, hj, hjl⟩ := ground.mem_map_of (fun k => k + 1)
    (List.range M) l (ground.mem_of_countOf_pos l _ h)
  exact ⟨j, ground.ltOfMemRange hj, hjl.symm⟩

/-- A shift within the count is counted once in the shift
family. -/
private theorem shift_count {M j : Nat} (h : j < M) :
    ground.countOf (j + 1)
      ((List.range M).map (fun k => k + 1)) = 1 :=
  Eq.trans (ground.countOf_shiftRange (j + 1) M)
    (if_pos ⟨Nat.succ_le_succ (Nat.zero_le j),
      Nat.succ_le_of_lt h⟩)

/-- A shift within the count joins the shift family. -/
private theorem shift_to {M j : Nat} (h : j < M) :
    j + 1 ∈ (List.range M).map (fun k => k + 1) :=
  ground.mem_map_to (fun k => k + 1) (ground.memRange h)

/-- A gap against its subtrahend doubled reads the top raised by
the subtrahend. -/
private theorem gapTwice {m l : Nat} (h : l ≤ m) :
    m - l + 2 * l = m + l := by
  rw [Nat.two_mul l, ← Nat.add_assoc (m - l) l l, ground.subAdd h]

/-- Every key of the recursion family carries the width: the
occupancy contents at the join's first side and the pair moves'
sources beyond it, the move keeping the width. -/
private theorem recKeys_len (d : Nat) (L : List (List Nat))
    (hL : ∀ mu, mu ∈ L → mu.length = d) :
    ∀ nu, nu ∈ weylchar.recKeys d L → nu.length = d := by
  intro nu hnu
  have hnu' : nu ∈ L ++ L.flatMap (fun mu =>
      (places.pairsOf d).flatMap (fun ab =>
        ((List.range (ground.getAt 0 mu ab.1)).map
          (fun l => l + 1)).map
          (fun l => weylchar.moveBy ab.2 ab.1 l mu))) := hnu
  match ground.mem_append_of L _ hnu' with
  | .inl h => exact hL nu h
  | .inr h =>
    obtain ⟨mu, hmu, hin⟩ := ground.mem_flatMap_of _ L nu h
    obtain ⟨_, _, hin2⟩ := ground.mem_flatMap_of _
      (places.pairsOf d) nu hin
    obtain ⟨l, _, hl⟩ := ground.mem_map_of _ _ nu hin2
    rw [← hl, weylchar.length_moveBy]
    exact hL mu hmu

/-- A pair move's source at a family member joins the recursion's
key family. -/
private theorem srcs_mem (d : Nat) (L : List (List Nat))
    {mu : List Nat} (hmu : mu ∈ L) {a b : Nat}
    (hab : (a, b) ∈ places.pairsOf d) {l : Nat}
    (hl : l ∈ (List.range (ground.getAt 0 mu a)).map
      (fun k => k + 1)) :
    weylchar.moveBy b a l mu ∈ weylchar.recKeys d L := by
  refine ground.mem_append_right L ?_
  refine ground.mem_flatMap_to _ hmu ?_
  refine ground.mem_flatMap_to _ hab ?_
  exact ground.mem_map_to (fun k => weylchar.moveBy b a k mu) hl

/-- The pair's source family at a content: the reversed move at
each shift within the first letter's count. -/
private def srcsOf (a b : Nat) (kap : List Nat) : List (List Nat) :=
  ((List.range (ground.getAt 0 kap a)).map (fun l => l + 1)).map
    (fun l => weylchar.moveBy b a l kap)

/-- A weight's fold over the source family reads the shift
family's fold at the sources. -/
private theorem famFold_srcs (a b : Nat) (kap : List Nat)
    (F : List Nat → Nat) :
    ground.famFold Nat.add 0 F (srcsOf a b kap)
      = ground.famFold Nat.add 0
        (fun l => F (weylchar.moveBy b a l kap))
        ((List.range (ground.getAt 0 kap a)).map (fun l => l + 1)) :=
  ground.famFold_map Nat.add 0 F
    (fun l => weylchar.moveBy b a l kap) _

/-- A pair move's weighted multiplicity fold reads the occupancy
family's guarded weights: the count is the indicator's fold over
the family and the weight passes the guard. -/
private theorem g_indicator (L : List (List Nat)) (nu : List Nat)
    (a b : Nat) (W : Nat → Nat) :
    ground.famFold Nat.add 0
        (fun l => W l
          * ground.countOf (weylchar.moveBy a b l nu) L)
        ((List.range (ground.getAt 0 nu b)).map (fun l => l + 1))
      = ground.famFold Nat.add 0
        (fun kap => ground.famFold Nat.add 0
          (fun l => if weylchar.moveBy a b l nu = kap
            then W l else 0)
          ((List.range (ground.getAt 0 nu b)).map
            (fun l => l + 1))) L := by
  rw [← ground.famFold_swap
    (fun (l : Nat) (kap : List Nat) =>
      if weylchar.moveBy a b l nu = kap then W l else 0)
    ((List.range (ground.getAt 0 nu b)).map (fun l => l + 1)) L]
  refine ground.famFold_congr_all Nat.add 0 _ _ ?_ _
  intro l
  rw [ground.countOf_fold (weylchar.moveBy a b l nu) L,
    ground.famFold_mul (W l)
      (fun kap => if weylchar.moveBy a b l nu = kap
        then (1 : Nat) else 0) L]
  exact ground.famFold_congr_all Nat.add 0 _ _
    (fun _ => mulIf (W l)) L

/-- The exchange at one letter pair: the recursion family's fold of
a pair move's guarded weights at a stated content reads that
content's own source fold.  A holding guard names the source
through the move's exact inverse, the shift is determined by the
raised letter's count, and the sources are distinct at that
letter. -/
private theorem exch_at (d : Nat) (L K : List (List Nat))
    (hKlen : ∀ nu, nu ∈ K → nu.length = d)
    (hK1 : ∀ x, x ∈ weylchar.recKeys d L → ground.countOf x K = 1)
    {a b : Nat} (hab : a < b) (hbd : b < d)
    {kap : List Nat} (hkap : kap ∈ L) (hklen : kap.length = d)
    (W : List Nat → Nat → Nat) (V : Nat → Nat)
    (hval : ∀ j, j < ground.getAt 0 kap a →
      W (weylchar.moveBy b a (j + 1) kap) (j + 1) = V (j + 1)) :
    ground.famFold Nat.add 0
        (fun nu => ground.famFold Nat.add 0
          (fun l => if weylchar.moveBy a b l nu = kap
            then W nu l else 0)
          ((List.range (ground.getAt 0 nu b)).map
            (fun l => l + 1))) K
      = ground.famFold Nat.add 0 V
        ((List.range (ground.getAt 0 kap a)).map
          (fun l => l + 1)) := by
  have hne : a ≠ b := Nat.ne_of_lt hab
  have hen : b ≠ a := fun h => hne h.symm
  have had : a < d := Nat.lt_trans hab hbd
  have hak : a < kap.length := by rw [hklen]; exact had
  have hbk : b < kap.length := by rw [hklen]; exact hbd
  have hpair : (a, b) ∈ places.pairsOf d :=
    ground.mem_of_countOf_pos _ _ (places.pairs_complete d hab hbd)
  have hsrcK : ∀ x, 0 < ground.countOf x (srcsOf a b kap) →
      ground.countOf x K = 1 := by
    intro x hx
    have hxm : x ∈ ((List.range (ground.getAt 0 kap a)).map
        (fun l => l + 1)).map
        (fun l => weylchar.moveBy b a l kap) :=
      ground.mem_of_countOf_pos x _ hx
    obtain ⟨l, hl, hlx⟩ := ground.mem_map_of
      (fun l => weylchar.moveBy b a l kap) _ x hxm
    rw [← hlx]
    exact hK1 _ (srcs_mem d L hkap hpair hl)
  have hsrcs1 : ∀ x, 0 < ground.countOf x (srcsOf a b kap) →
      ground.countOf x (srcsOf a b kap) = 1 := by
    intro x hx
    have hxm : x ∈ ((List.range (ground.getAt 0 kap a)).map
        (fun l => l + 1)).map
        (fun l => weylchar.moveBy b a l kap) :=
      ground.mem_of_countOf_pos x _ hx
    obtain ⟨l0, hl0, hl0x⟩ := ground.mem_map_of
      (fun l => weylchar.moveBy b a l kap) _ x hxm
    obtain ⟨j0, hj0, hj0e⟩ :=
      shift_mem (ground.countOf_pos_of_mem hl0)
    have hinj : ∀ y, 0 < ground.countOf y
        ((List.range (ground.getAt 0 kap a)).map
          (fun l => l + 1)) →
        weylchar.moveBy b a y kap = weylchar.moveBy b a l0 kap →
        y = l0 := by
      intro y hy hyeq
      obtain ⟨i, hi, hie⟩ := shift_mem hy
      have hyle : y ≤ ground.getAt 0 kap a := by
        rw [hie]; exact hi
      have hl0le : l0 ≤ ground.getAt 0 kap a := by
        rw [hj0e]; exact hj0
      refine ground.subInj hyle hl0le ?_
      rw [← weylchar.getAt_moveBy_snd b hen y kap hak,
        ← weylchar.getAt_moveBy_snd b hen l0 kap hak, hyeq]
    show ground.countOf x
      (((List.range (ground.getAt 0 kap a)).map (fun l => l + 1)).map
        (fun l => weylchar.moveBy b a l kap)) = 1
    rw [← hl0x]
    refine Eq.trans (ground.countOf_map_inj
      (fun l => weylchar.moveBy b a l kap) l0 _ hinj) ?_
    rw [hj0e]
    exact shift_count hj0
  have hGsrc : ∀ j, j < ground.getAt 0 kap a →
      ground.famFold Nat.add 0
        (fun l => if weylchar.moveBy a b l
            (weylchar.moveBy b a (j + 1) kap) = kap
          then W (weylchar.moveBy b a (j + 1) kap) l else 0)
        ((List.range (ground.getAt 0
          (weylchar.moveBy b a (j + 1) kap) b)).map
          (fun l => l + 1))
      = V (j + 1) := by
    intro j hj
    have hjle : j + 1 ≤ ground.getAt 0 kap a := hj
    have hnub : ground.getAt 0
        (weylchar.moveBy b a (j + 1) kap) b
        = ground.getAt 0 kap b + (j + 1) :=
      weylchar.getAt_moveBy_fst hen (j + 1) kap hbk
    have hnua : ground.getAt 0
        (weylchar.moveBy b a (j + 1) kap) a
        = ground.getAt 0 kap a - (j + 1) :=
      weylchar.getAt_moveBy_snd b hen (j + 1) kap hak
    have hnulen : (weylchar.moveBy b a (j + 1) kap).length = d := by
      rw [weylchar.length_moveBy]
      exact hklen
    have hrt : weylchar.moveBy a b (j + 1)
        (weylchar.moveBy b a (j + 1) kap) = kap :=
      weylchar.moveBy_moveBy hen (j + 1) kap hbk hak hjle
    have hcount : ground.countOf (j + 1)
        ((List.range (ground.getAt 0
          (weylchar.moveBy b a (j + 1) kap) b)).map
          (fun l => l + 1)) = 1 := by
      rw [hnub]
      exact shift_count (Nat.lt_of_lt_of_le (Nat.lt_succ_self j)
        (Nat.le_add_left (j + 1) (ground.getAt 0 kap b)))
    have hcongr : ∀ l, 0 < ground.countOf l
        ((List.range (ground.getAt 0
          (weylchar.moveBy b a (j + 1) kap) b)).map
          (fun l => l + 1)) →
        (if weylchar.moveBy a b l
            (weylchar.moveBy b a (j + 1) kap) = kap
          then W (weylchar.moveBy b a (j + 1) kap) l else 0)
          = (if l = j + 1
            then W (weylchar.moveBy b a (j + 1) kap) l else 0) := by
      intro l _
      by_cases hg : weylchar.moveBy a b l
          (weylchar.moveBy b a (j + 1) kap) = kap
      · have hla : ground.getAt 0
              (weylchar.moveBy a b l
                (weylchar.moveBy b a (j + 1) kap)) a
            = ground.getAt 0
                (weylchar.moveBy b a (j + 1) kap) a + l :=
          weylchar.getAt_moveBy_fst hne l _
            (by rw [hnulen]; exact had)
        rw [hg] at hla
        have hlj : l = j + 1 := by
          refine ground.addCancelL
            (ground.getAt 0 kap a - (j + 1)) ?_
          rw [ground.subAdd hjle, ← hnua]
          exact hla.symm
        rw [if_pos hg, if_pos hlj]
      · have hnl : ¬ l = j + 1 := by
          intro he
          rw [he] at hg
          exact hg hrt
        rw [if_neg hg, if_neg hnl]
    rw [ground.famFold_congr_members Nat.add 0 _ _ _ hcongr,
      ground.famFold_pick
        (fun l => W (weylchar.moveBy b a (j + 1) kap) l) (j + 1)
        _ hcount]
    exact hval j hj
  have hGoff : ∀ nu, nu ∈ K →
      ground.countOf nu (srcsOf a b kap) = 0 →
      ground.famFold Nat.add 0
        (fun l => if weylchar.moveBy a b l nu = kap
          then W nu l else 0)
        ((List.range (ground.getAt 0 nu b)).map
          (fun l => l + 1)) = 0 := by
    intro nu hnu hz
    have hnulen : nu.length = d := hKlen nu hnu
    have han : a < nu.length := by rw [hnulen]; exact had
    have hbn : b < nu.length := by rw [hnulen]; exact hbd
    refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
      (fun _ => (0 : Nat)) _ ?_)
      (ground.famFold_zero (fun _ : Nat => (0 : Nat))
        (fun _ => rfl) _)
    intro l hl
    obtain ⟨i, hi, hli⟩ := shift_mem hl
    have hlle : l ≤ ground.getAt 0 nu b := by
      rw [hli]
      exact hi
    refine if_neg ?_
    intro hg
    have hrt : weylchar.moveBy b a l kap = nu := by
      rw [← hg]
      exact weylchar.moveBy_moveBy hne l nu han hbn hlle
    have hfa : ground.getAt 0 kap a
        = ground.getAt 0 nu a + l := by
      rw [← hg]
      exact weylchar.getAt_moveBy_fst hne l nu han
    have him : i < ground.getAt 0 kap a := by
      rw [hfa, hli]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i)
        (Nat.le_add_left (i + 1) (ground.getAt 0 nu a))
    have hmem : nu ∈ srcsOf a b kap := by
      show nu ∈ ((List.range (ground.getAt 0 kap a)).map
        (fun l => l + 1)).map
        (fun l => weylchar.moveBy b a l kap)
      rw [← hrt, hli]
      exact ground.mem_map_to
        (fun k => weylchar.moveBy b a k kap) (shift_to him)
    have hcp := ground.countOf_pos_of_mem hmem
    rw [hz] at hcp
    exact absurd hcp (Nat.lt_irrefl 0)
  have hcc := ground.famFold_countCollect
    (fun nu => ground.famFold Nat.add 0
      (fun l => if weylchar.moveBy a b l nu = kap
        then W nu l else 0)
      ((List.range (ground.getAt 0 nu b)).map (fun l => l + 1)))
    (srcsOf a b kap) K hsrcK
  have hstep : ground.famFold Nat.add 0
      (fun x => ground.countOf x (srcsOf a b kap)
        * ground.famFold Nat.add 0
          (fun l => if weylchar.moveBy a b l x = kap
            then W x l else 0)
          ((List.range (ground.getAt 0 x b)).map
            (fun l => l + 1))) K
    = ground.famFold Nat.add 0
      (fun x => ground.famFold Nat.add 0
        (fun l => if weylchar.moveBy a b l x = kap
          then W x l else 0)
        ((List.range (ground.getAt 0 x b)).map
          (fun l => l + 1))) K := by
    refine ground.famFold_congr_members Nat.add 0 _ _ K ?_
    intro x hx
    match Nat.eq_zero_or_pos
        (ground.countOf x (srcsOf a b kap)) with
    | .inl hzero =>
      rw [hzero, Nat.zero_mul,
        hGoff x (ground.mem_of_countOf_pos x K hx) hzero]
    | .inr hposn =>
      rw [hsrcs1 x hposn, Nat.one_mul]
  rw [← hstep, ← hcc, famFold_srcs a b kap]
  refine ground.famFold_congr_members Nat.add 0 _ _ _ ?_
  intro l0 hl0
  obtain ⟨j, hj, hje⟩ := shift_mem hl0
  rw [hje]
  exact hGsrc j hj

/-- The moved folds' reindexing: the recursion family's fold of a
weighted pair move reads the occupancy family's own fold at the
sources' values, one letter pair at a time. -/
private theorem moved_reindex (lam : Shape) (L K : List (List Nat))
    (hL : ∀ mu, mu ∈ L → mu.length = lam.length)
    (hKrec : ∀ nu, nu ∈ K → nu ∈ weylchar.recKeys lam.length L)
    (hK1 : ∀ x, x ∈ weylchar.recKeys lam.length L →
      ground.countOf x K = 1)
    (W V : Nat → Nat → List Nat → Nat → Nat)
    (hval : ∀ a b : Nat, a < b → b < lam.length →
      ∀ kap : List Nat, kap ∈ L →
      ∀ j, j < ground.getAt 0 kap a →
        W a b (weylchar.moveBy b a (j + 1) kap) (j + 1)
          = V a b kap (j + 1)) :
    ground.famFold Nat.add 0
        (fun nu => ground.famFold Nat.add 0
          (fun ab => ground.famFold Nat.add 0
            (fun l => W ab.1 ab.2 nu l
              * ground.countOf
                (weylchar.moveBy ab.1 ab.2 l nu) L)
            ((List.range (ground.getAt 0 nu ab.2)).map
              (fun l => l + 1)))
          (places.pairsOf lam.length)) K
      = ground.famFold Nat.add 0
        (fun kap => ground.famFold Nat.add 0
          (fun ab => ground.famFold Nat.add 0
            (fun l => V ab.1 ab.2 kap l)
            ((List.range (ground.getAt 0 kap ab.1)).map
              (fun l => l + 1)))
          (places.pairsOf lam.length)) L := by
  have hKlen : ∀ nu, nu ∈ K → nu.length = lam.length :=
    fun nu h => recKeys_len lam.length L hL nu (hKrec nu h)
  rw [ground.famFold_swap
      (fun (nu : List Nat) (ab : Nat × Nat) =>
        ground.famFold Nat.add 0
          (fun l => W ab.1 ab.2 nu l
            * ground.countOf
              (weylchar.moveBy ab.1 ab.2 l nu) L)
          ((List.range (ground.getAt 0 nu ab.2)).map
            (fun l => l + 1)))
      K (places.pairsOf lam.length),
    ground.famFold_swap
      (fun (kap : List Nat) (ab : Nat × Nat) =>
        ground.famFold Nat.add 0 (fun l => V ab.1 ab.2 kap l)
          ((List.range (ground.getAt 0 kap ab.1)).map
            (fun l => l + 1)))
      L (places.pairsOf lam.length)]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (places.pairsOf lam.length) ?_
  intro ab hab
  have hpr := places.pairs_mem lam.length ab hab
  have hgi : ground.famFold Nat.add 0
      (fun nu => ground.famFold Nat.add 0
        (fun l => W ab.1 ab.2 nu l
          * ground.countOf
            (weylchar.moveBy ab.1 ab.2 l nu) L)
        ((List.range (ground.getAt 0 nu ab.2)).map
          (fun l => l + 1))) K
    = ground.famFold Nat.add 0
      (fun nu => ground.famFold Nat.add 0
        (fun kap => ground.famFold Nat.add 0
          (fun l => if weylchar.moveBy ab.1 ab.2 l nu = kap
            then W ab.1 ab.2 nu l else 0)
          ((List.range (ground.getAt 0 nu ab.2)).map
            (fun l => l + 1))) L) K :=
    ground.famFold_congr_all Nat.add 0 _ _
      (fun nu => g_indicator L nu ab.1 ab.2 (W ab.1 ab.2 nu)) K
  rw [hgi, ground.famFold_swap
    (fun (nu : List Nat) (kap : List Nat) =>
      ground.famFold Nat.add 0
        (fun l => if weylchar.moveBy ab.1 ab.2 l nu = kap
          then W ab.1 ab.2 nu l else 0)
        ((List.range (ground.getAt 0 nu ab.2)).map
          (fun l => l + 1)))
    K L]
  refine ground.famFold_congr_members Nat.add 0 _ _ L ?_
  intro kap hkap
  exact exch_at lam.length L K hKlen hK1 hpr.1 hpr.2
    (ground.mem_of_countOf_pos kap L hkap)
    (hL kap (ground.mem_of_countOf_pos kap L hkap))
    (W ab.1 ab.2) (fun l => V ab.1 ab.2 kap l)
    (fun j hj => hval ab.1 ab.2 hpr.1 hpr.2 kap
      (ground.mem_of_countOf_pos kap L hkap) j hj)

/-- The shifts' own total at a content, the weight shared by the
two reindexed reads. -/
private def wT (mu : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun ab => ground.famFold Nat.add 0 (fun l => l)
      ((List.range (ground.getAt 0 mu ab.1)).map (fun l => l + 1)))
    (places.pairsOf mu.length)

/-- The reindexed second-letter weight at a content: at each pair
the first letter's shifts against the second letter's count. -/
private def wSndR (mu : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun ab => ground.famFold Nat.add 0
      (fun l => ground.getAt 0 mu ab.2 + l)
      ((List.range (ground.getAt 0 mu ab.1)).map (fun l => l + 1)))
    (places.pairsOf mu.length)

/-- The reindexed first-letter weight at a content. -/
private def wFstR (mu : List Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun ab => ground.famFold Nat.add 0
      (fun l => ground.getAt 0 mu ab.1 + l)
      ((List.range (ground.getAt 0 mu ab.1)).map (fun l => l + 1)))
    (places.pairsOf mu.length)

/-- A shift fold at a constant offset splits into the count's
product and the shifts' own total. -/
private theorem inner_split (mu : List Nat) (p q : Nat) :
    ground.famFold Nat.add 0 (fun l => ground.getAt 0 mu q + l)
      ((List.range (ground.getAt 0 mu p)).map (fun l => l + 1))
    = ground.getAt 0 mu p * ground.getAt 0 mu q
      + ground.famFold Nat.add 0 (fun l => l)
        ((List.range (ground.getAt 0 mu p)).map
          (fun l => l + 1)) := by
  rw [ground.famFold_add_split
      (fun _ => ground.getAt 0 mu q) (fun l => l)
      ((List.range (ground.getAt 0 mu p)).map (fun l => l + 1)),
    ground.famFold_const (ground.getAt 0 mu q)
      ((List.range (ground.getAt 0 mu p)).map (fun l => l + 1)),
    ground.length_map (fun l => l + 1)
      (List.range (ground.getAt 0 mu p)),
    ground.length_range (ground.getAt 0 mu p)]

/-- The reindexed second-letter weight is the cross weight against
the shared shift total. -/
private theorem wSndR_split (mu : List Nat) :
    wSndR mu = wCross mu + wT mu := by
  show ground.famFold Nat.add 0
      (fun ab => ground.famFold Nat.add 0
        (fun l => ground.getAt 0 mu ab.2 + l)
        ((List.range (ground.getAt 0 mu ab.1)).map
          (fun l => l + 1)))
      (places.pairsOf mu.length)
    = ground.famFold Nat.add 0
        (fun ab => ground.getAt 0 mu ab.1 * ground.getAt 0 mu ab.2)
        (places.pairsOf mu.length)
      + ground.famFold Nat.add 0
        (fun ab => ground.famFold Nat.add 0 (fun l => l)
          ((List.range (ground.getAt 0 mu ab.1)).map
            (fun l => l + 1)))
        (places.pairsOf mu.length)
  rw [ground.famFold_congr_all Nat.add 0 _
      (fun ab : Nat × Nat =>
        ground.getAt 0 mu ab.1 * ground.getAt 0 mu ab.2
        + ground.famFold Nat.add 0 (fun l => l)
          ((List.range (ground.getAt 0 mu ab.1)).map
            (fun l => l + 1)))
      (fun ab => inner_split mu ab.1 ab.2)
      (places.pairsOf mu.length),
    ground.famFold_add_split
      (fun ab : Nat × Nat =>
        ground.getAt 0 mu ab.1 * ground.getAt 0 mu ab.2)
      (fun ab : Nat × Nat => ground.famFold Nat.add 0 (fun l => l)
        ((List.range (ground.getAt 0 mu ab.1)).map
          (fun l => l + 1)))
      (places.pairsOf mu.length)]

/-- The reindexed first-letter weight is the square weight against
the shared shift total. -/
private theorem wFstR_split (mu : List Nat) :
    wFstR mu = wSqP mu + wT mu := by
  show ground.famFold Nat.add 0
      (fun ab => ground.famFold Nat.add 0
        (fun l => ground.getAt 0 mu ab.1 + l)
        ((List.range (ground.getAt 0 mu ab.1)).map
          (fun l => l + 1)))
      (places.pairsOf mu.length)
    = ground.famFold Nat.add 0
        (fun ab => ground.getAt 0 mu ab.1 * ground.getAt 0 mu ab.1)
        (places.pairsOf mu.length)
      + ground.famFold Nat.add 0
        (fun ab => ground.famFold Nat.add 0 (fun l => l)
          ((List.range (ground.getAt 0 mu ab.1)).map
            (fun l => l + 1)))
        (places.pairsOf mu.length)
  rw [ground.famFold_congr_all Nat.add 0 _
      (fun ab : Nat × Nat =>
        ground.getAt 0 mu ab.1 * ground.getAt 0 mu ab.1
        + ground.famFold Nat.add 0 (fun l => l)
          ((List.range (ground.getAt 0 mu ab.1)).map
            (fun l => l + 1)))
      (fun ab => inner_split mu ab.1 ab.1)
      (places.pairsOf mu.length),
    ground.famFold_add_split
      (fun ab : Nat × Nat =>
        ground.getAt 0 mu ab.1 * ground.getAt 0 mu ab.1)
      (fun ab : Nat × Nat => ground.famFold Nat.add 0 (fun l => l)
        ((List.range (ground.getAt 0 mu ab.1)).map
          (fun l => l + 1)))
      (places.pairsOf mu.length)]

/-- The trace recursion summed over the recursion family at a
stated occupancy family: the display's square collects against the
family's count, the shifted squares collect at the family's own
contents, and the moved folds reindex to the pair weights with
their shared shift total cancelling. -/
private theorem sumRec_gen (lam : Shape) (L K : List (List Nat))
    (hL : ∀ mu, mu ∈ L → mu.length = lam.length)
    (hKrec : ∀ nu, nu ∈ K → nu ∈ weylchar.recKeys lam.length L)
    (hK1 : ∀ x, x ∈ weylchar.recKeys lam.length L →
      ground.countOf x K = 1)
    (hrec : weylchar.recRead lam L) :
    weylchar.stdSq (places.display lam) * L.length
      + 2 * ground.famFold Nat.add 0 (fun kap => wCross kap) L
    = ground.famFold Nat.add 0
        (fun kap => weylchar.stdSq (List.zipWith (fun a b => a + b)
          kap (places.unitDisp lam.length))) L
      + 2 * ground.famFold Nat.add 0 (fun kap => wSqP kap) L := by
  have hKlen : ∀ nu, nu ∈ K → nu.length = lam.length :=
    fun nu h => recKeys_len lam.length L hL nu (hKrec nu h)
  have hcov : ∀ x, 0 < ground.countOf x L →
      ground.countOf x K = 1 := by
    intro x hx
    refine hK1 x ?_
    show x ∈ L ++ L.flatMap (fun mu =>
      (places.pairsOf lam.length).flatMap (fun ab =>
        ((List.range (ground.getAt 0 mu ab.1)).map
          (fun l => l + 1)).map
          (fun l => weylchar.moveBy ab.2 ab.1 l mu)))
    exact ground.mem_append_left _
      (ground.mem_of_countOf_pos x L hx)
  have hA : ground.famFold Nat.add 0
      (fun nu => weylchar.stdSq (places.display lam)
          * ground.countOf nu L
        + 2 * weylchar.movedSnd
          (fun chi => ground.countOf chi L) nu) K
    = ground.famFold Nat.add 0
      (fun nu => weylchar.stdSq (List.zipWith (fun a b => a + b) nu
          (places.unitDisp lam.length)) * ground.countOf nu L
        + 2 * weylchar.movedFst
          (fun chi => ground.countOf chi L) nu) K :=
    ground.famFold_congr_members Nat.add 0 _ _ K
      (fun nu hnu =>
        hrec nu (hKrec nu (ground.mem_of_countOf_pos nu K hnu))
          (hKlen nu (ground.mem_of_countOf_pos nu K hnu)))
  have hB1 : ground.famFold Nat.add 0
      (fun nu => ground.countOf nu L) K = L.length := by
    have h := ground.famFold_countCollect
      (fun _ : List Nat => (1 : Nat)) L K hcov
    rw [ground.famFold_length L] at h
    rw [h]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun m => (Nat.mul_one (ground.countOf m L)).symm) K
  have hB2 : ground.famFold Nat.add 0
      (fun nu => weylchar.stdSq (List.zipWith (fun a b => a + b) nu
        (places.unitDisp lam.length)) * ground.countOf nu L) K
    = ground.famFold Nat.add 0
      (fun kap => weylchar.stdSq (List.zipWith (fun a b => a + b)
        kap (places.unitDisp lam.length))) L := by
    have h := ground.famFold_countCollect
      (fun kap => weylchar.stdSq (List.zipWith (fun a b => a + b)
        kap (places.unitDisp lam.length))) L K hcov
    rw [h]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun m => Nat.mul_comm _ _) K
  have hB3 : ground.famFold Nat.add 0
      (fun nu => weylchar.movedSnd
        (fun chi => ground.countOf chi L) nu) K
    = ground.famFold Nat.add 0 (fun kap => wSndR kap) L := by
    have h1 : ground.famFold Nat.add 0
        (fun nu => weylchar.movedSnd
          (fun chi => ground.countOf chi L) nu) K
      = ground.famFold Nat.add 0
        (fun nu => ground.famFold Nat.add 0
          (fun ab => ground.famFold Nat.add 0
            (fun l => ground.getAt 0 nu ab.2
              * ground.countOf
                (weylchar.moveBy ab.1 ab.2 l nu) L)
            ((List.range (ground.getAt 0 nu ab.2)).map
              (fun l => l + 1)))
          (places.pairsOf lam.length)) K := by
      refine ground.famFold_congr_members Nat.add 0 _ _ K ?_
      intro nu hnu
      show ground.famFold Nat.add 0
          (fun ab => weylchar.gSnd
            (fun chi => ground.countOf chi L) nu ab.1 ab.2)
          (places.pairsOf nu.length) = _
      rw [hKlen nu (ground.mem_of_countOf_pos nu K hnu)]
      rfl
    rw [h1, moved_reindex lam L K hL hKrec hK1
      (fun _ b nu _ => ground.getAt 0 nu b)
      (fun _ b kap l => ground.getAt 0 kap b + l)
      (fun a b hab hbd kap hkap j _ =>
        weylchar.getAt_moveBy_fst
          (fun h => Nat.ne_of_lt hab h.symm) (j + 1) kap
          (by rw [hL kap hkap]; exact hbd))]
    refine ground.famFold_congr_members Nat.add 0 _ _ L ?_
    intro kap hkap
    show _ = ground.famFold Nat.add 0
        (fun ab => ground.famFold Nat.add 0
          (fun l => ground.getAt 0 kap ab.2 + l)
          ((List.range (ground.getAt 0 kap ab.1)).map
            (fun l => l + 1)))
        (places.pairsOf kap.length)
    rw [hL kap (ground.mem_of_countOf_pos kap L hkap)]
  have hB4 : ground.famFold Nat.add 0
      (fun nu => weylchar.movedFst
        (fun chi => ground.countOf chi L) nu) K
    = ground.famFold Nat.add 0 (fun kap => wFstR kap) L := by
    have h1 : ground.famFold Nat.add 0
        (fun nu => weylchar.movedFst
          (fun chi => ground.countOf chi L) nu) K
      = ground.famFold Nat.add 0
        (fun nu => ground.famFold Nat.add 0
          (fun ab => ground.famFold Nat.add 0
            (fun l => (ground.getAt 0 nu ab.1 + 2 * l)
              * ground.countOf
                (weylchar.moveBy ab.1 ab.2 l nu) L)
            ((List.range (ground.getAt 0 nu ab.2)).map
              (fun l => l + 1)))
          (places.pairsOf lam.length)) K := by
      refine ground.famFold_congr_members Nat.add 0 _ _ K ?_
      intro nu hnu
      show ground.famFold Nat.add 0
          (fun ab => weylchar.gFst
            (fun chi => ground.countOf chi L) nu ab.1 ab.2)
          (places.pairsOf nu.length) = _
      rw [hKlen nu (ground.mem_of_countOf_pos nu K hnu)]
      rfl
    rw [h1, moved_reindex lam L K hL hKrec hK1
      (fun a _ nu l => ground.getAt 0 nu a + 2 * l)
      (fun a _ kap l => ground.getAt 0 kap a + l)
      (fun a b hab hbd kap hkap j hj => by
        show ground.getAt 0 (weylchar.moveBy b a (j + 1) kap) a
            + 2 * (j + 1)
          = ground.getAt 0 kap a + (j + 1)
        rw [weylchar.getAt_moveBy_snd b
          (fun h => Nat.ne_of_lt hab h.symm) (j + 1) kap
          (by rw [hL kap hkap]; exact Nat.lt_trans hab hbd)]
        exact gapTwice hj)]
    refine ground.famFold_congr_members Nat.add 0 _ _ L ?_
    intro kap hkap
    show _ = ground.famFold Nat.add 0
        (fun ab => ground.famFold Nat.add 0
          (fun l => ground.getAt 0 kap ab.1 + l)
          ((List.range (ground.getAt 0 kap ab.1)).map
            (fun l => l + 1)))
        (places.pairsOf kap.length)
    rw [hL kap (ground.mem_of_countOf_pos kap L hkap)]
  have hSnd : ground.famFold Nat.add 0 (fun kap => wSndR kap) L
    = ground.famFold Nat.add 0 (fun kap => wCross kap) L
      + ground.famFold Nat.add 0 (fun kap => wT kap) L := by
    rw [← ground.famFold_add_split (fun kap => wCross kap)
      (fun kap => wT kap) L]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun kap => wSndR_split kap) L
  have hFst : ground.famFold Nat.add 0 (fun kap => wFstR kap) L
    = ground.famFold Nat.add 0 (fun kap => wSqP kap) L
      + ground.famFold Nat.add 0 (fun kap => wT kap) L := by
    rw [← ground.famFold_add_split (fun kap => wSqP kap)
      (fun kap => wT kap) L]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun kap => wFstR_split kap) L
  rw [ground.famFold_add_split
      (fun nu => weylchar.stdSq (places.display lam)
        * ground.countOf nu L)
      (fun nu => 2 * weylchar.movedSnd
        (fun chi => ground.countOf chi L) nu) K,
    ground.famFold_add_split
      (fun nu => weylchar.stdSq (List.zipWith (fun a b => a + b) nu
        (places.unitDisp lam.length)) * ground.countOf nu L)
      (fun nu => 2 * weylchar.movedFst
        (fun chi => ground.countOf chi L) nu) K,
    ← ground.famFold_mul (weylchar.stdSq (places.display lam))
      (fun nu => ground.countOf nu L) K,
    ← ground.famFold_mul 2
      (fun nu => weylchar.movedSnd
        (fun chi => ground.countOf chi L) nu) K,
    ← ground.famFold_mul 2
      (fun nu => weylchar.movedFst
        (fun chi => ground.countOf chi L) nu) K,
    hB1, hB2, hB3, hB4, hSnd, hFst] at hA
  refine ground.addCancelR (2 * ground.famFold Nat.add 0
    (fun kap => wT kap) L) ?_
  rw [Nat.add_assoc (weylchar.stdSq (places.display lam) * L.length)
      (2 * ground.famFold Nat.add 0 (fun kap => wCross kap) L)
      (2 * ground.famFold Nat.add 0 (fun kap => wT kap) L),
    Nat.add_assoc (ground.famFold Nat.add 0
        (fun kap => weylchar.stdSq (List.zipWith (fun a b => a + b)
          kap (places.unitDisp lam.length))) L)
      (2 * ground.famFold Nat.add 0 (fun kap => wSqP kap) L)
      (2 * ground.famFold Nat.add 0 (fun kap => wT kap) L),
    ← Nat.left_distrib 2
      (ground.famFold Nat.add 0 (fun kap => wCross kap) L)
      (ground.famFold Nat.add 0 (fun kap => wT kap) L),
    ← Nat.left_distrib 2
      (ground.famFold Nat.add 0 (fun kap => wSqP kap) L)
      (ground.famFold Nat.add 0 (fun kap => wT kap) L)]
  exact hA

/-- The trace recursion summed over the block's occupancy family
(`casimir.recRead_def` at every key of the recursion family): the
moved folds reindex at the move's round trip to the target's own
reads, the shared shift folds a summand on both members, and the
display collects to the top's square against the span's shifted
squares with the pair folds' cross and square weights. -/
theorem sumRec (lam : Shape) :
    weylchar.stdSq (places.display lam) * (blockSpan lam).length
      + 2 * ground.famFold Nat.add 0 (fun v => wCross v.content)
          (blockSpan lam)
    = ground.famFold Nat.add 0
        (fun v => weylchar.stdSq (List.zipWith (fun a b => a + b)
          v.content (places.unitDisp lam.length)))
        (blockSpan lam)
      + 2 * ground.famFold Nat.add 0 (fun v => wSqP v.content)
          (blockSpan lam) := by
  have hL : ∀ mu, mu ∈ (blockSpan lam).map HVec.content →
      mu.length = lam.length := by
    intro mu hmu
    obtain ⟨v, hv, hvc⟩ := ground.mem_map_of HVec.content
      (blockSpan lam) mu hmu
    rw [← hvc]
    exact blockcount.blockSpan_width lam v hv
  have hbase := sumRec_gen lam ((blockSpan lam).map HVec.content)
    (ground.dedupL (weylchar.recKeys lam.length
      ((blockSpan lam).map HVec.content)))
    hL (fun _ h => ground.mem_of_dedupL h)
    (fun x hx => ground.countOf_dedupL_one hx)
    (casimir.recRead_def lam)
  rw [ground.famFold_map Nat.add 0 (fun kap => wCross kap)
      HVec.content (blockSpan lam),
    ground.famFold_map Nat.add 0 (fun kap => wSqP kap)
      HVec.content (blockSpan lam),
    ground.famFold_map Nat.add 0
      (fun kap => weylchar.stdSq (List.zipWith (fun a b => a + b)
        kap (places.unitDisp lam.length)))
      HVec.content (blockSpan lam),
    ground.length_map HVec.content (blockSpan lam)] at hbase
  exact hbase

/-! The channel split: the fused pool's content family refines
over the exhaustion's channels (`blockcount.gradedDim_countAt`),
each channel weighted by its own fusion count
(`blockcount.fusionCount_countAt` at the tops' row lists) and read
on its shape's block.  A channel's occupied block content is
occupied in the pool wherever the channel's count is, so the
pool's own distinct contents index both reads. -/

/-- A content weight's fold over the fused pool splits over the
channels: the channel's fusion count against the channel shape's
own block fold. -/
private theorem fold_channels (a b : Shape) (hba : b.length = a.length)
    (W : List Nat → Nat) :
    ground.famFold Nat.add 0 (fun v => W v.content)
      (fusedAt (blockSpan a) (blockSpan b))
    = ground.famFold Nat.add 0
        (fun mu => fusionCount a b (places.shapeOf mu)
          * ground.famFold Nat.add 0 (fun v => W v.content)
              (blockSpan (places.shapeOf mu)))
        (ground.dedupL
          ((exhaust a.length
            (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)) := by
  obtain ⟨hszP, hwidP, hclP, hiP⟩ := fusedSpan_pack a b hba
  have hrl := exhaust_rowList_shapeOf a.length
    (fusedAt (blockSpan a) (blockSpan b)) hszP hwidP hclP
  have hD : ∀ x : List Nat,
      0 < ground.countOf x
        ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content) →
      ground.countOf x (ground.dedupL
        ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)) = 1 :=
    fun x hx => ground.countOf_dedupL_one (ground.mem_of_countOf_pos x _ hx)
  have hposF := channel_content a b hba
  have hstep : ∀ m : List Nat,
      ground.countOf m
          ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content) * W m
      = ground.famFold Nat.add 0
          (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
            * (occ m (blockSpan (places.shapeOf nu)) * W m))
          (ground.dedupL ((exhaust a.length
            (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)) := by
    intro m
    rw [← occ_eq_countOf m (fusedAt (blockSpan a) (blockSpan b)),
      ← dimAt_occ (fusedAt (blockSpan a) (blockSpan b)) hiP m,
      gradedDim_countAt a.length (fusedAt (blockSpan a) (blockSpan b))
        hszP hwidP hclP m,
      ← ground.famFold_mulR (W m)
        (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * occ m (blockSpan (places.shapeOf nu)))
        (ground.dedupL ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun nu => ground.mulAssoc _ _ _)
      (ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
  rw [← ground.famFold_map Nat.add 0 W HVec.content
      (fusedAt (blockSpan a) (blockSpan b)),
    ground.famFold_countCollect W
      ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)
      (ground.dedupL
        ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)) hD,
    ground.famFold_congr_all Nat.add 0 _ _ hstep
      (ground.dedupL
        ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)),
    ground.famFold_swap
      (fun (m : List Nat) (nu : List Nat) =>
        countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * (occ m (blockSpan (places.shapeOf nu)) * W m))
      (ground.dedupL
        ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content))
      (ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))]
  refine ground.famFold_congr_members Nat.add 0 _ _ _ ?_
  intro nu hnu
  have hnuE : nu ∈ ground.dedupL ((exhaust a.length
      (fusedAt (blockSpan a) (blockSpan b))).map HVec.content) :=
    ground.mem_of_countOf_pos nu _ hnu
  have hfc : fusionCount a b (places.shapeOf nu)
      = countAt (fusedAt (blockSpan a) (blockSpan b)) nu := by
    rw [fusionCount_countAt a b (places.shapeOf nu) hba,
      hrl nu (ground.mem_of_dedupL hnuE)]
  rw [hfc]
  match Nat.eq_zero_or_pos
      (countAt (fusedAt (blockSpan a) (blockSpan b)) nu) with
  | .inl hz =>
    rw [hz, Nat.zero_mul]
    exact Eq.trans (ground.famFold_congr_all Nat.add 0 _
        (fun _ => (0 : Nat))
        (fun m => Nat.zero_mul _) _)
      (ground.famFold_zero (fun _ : List Nat => (0 : Nat))
        (fun _ => rfl) _)
  | .inr hp =>
    have hcover : ∀ x : List Nat,
        0 < ground.countOf x
          ((blockSpan (places.shapeOf nu)).map HVec.content) →
        ground.countOf x (ground.dedupL
          ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)) = 1 := by
      intro x hx
      refine hD x (hposF nu hnuE hp x ?_)
      rw [occ_eq_countOf]
      exact hx
    rw [← ground.famFold_mul
        (countAt (fusedAt (blockSpan a) (blockSpan b)) nu)
        (fun m => occ m (blockSpan (places.shapeOf nu)) * W m)
        (ground.dedupL
          ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)),
      ground.famFold_congr_all Nat.add 0
        (fun m => occ m (blockSpan (places.shapeOf nu)) * W m)
        (fun m => ground.countOf m
          ((blockSpan (places.shapeOf nu)).map HVec.content) * W m)
        (fun m => by rw [occ_eq_countOf])
        (ground.dedupL
          ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)),
      ← ground.famFold_countCollect W
        ((blockSpan (places.shapeOf nu)).map HVec.content)
        (ground.dedupL
          ((fusedAt (blockSpan a) (blockSpan b)).map HVec.content)) hcover,
      ground.famFold_map Nat.add 0 W HVec.content
        (blockSpan (places.shapeOf nu))]

/-! The moment reductions: `sumRec`'s shifted-square fold splits at
the display's join (`weylchar.sqSplit`) into the span's own square
moment, its first moment against the unit display's dot, and the
unit display's square against the span's count — every place of the
width reading the first place's moment. -/

/-- The span's square moment at an interior place is the first
place's: the transposition of the two places carries the fold. -/
private theorem mom2At_free (lam : Shape) (p : Nat)
    (hp : p < lam.length) :
    mom2At p (blockSpan lam) = mom2At 0 (blockSpan lam) := by
  cases p with
  | zero => rfl
  | succ q =>
    have h0 : 0 < lam.length :=
      Nat.lt_of_lt_of_le (Nat.succ_pos q) (Nat.le_of_lt hp)
    have hne : ¬ (0 = q + 1) := fun h => Nat.noConfusion h
    exact pair_swap lam (fun a _ => a * a) 0 (q + 1) 0 0
      (q + 1) (q + 1) h0 hp
      (fun mu hmu => places.getAt_swapPair_fst mu hne
        (by rw [hmu]; exact h0) (by rw [hmu]; exact hp))
      (fun mu hmu => places.getAt_swapPair_fst mu hne
        (by rw [hmu]; exact h0) (by rw [hmu]; exact hp))

/-- The summed recursion at the moments: the span's shifted
squares read the square moment against the width, the first moment
against the unit display's total, and the unit display's own
square against the span's count. -/
private theorem momRec (d : Nat) (x : Shape) (hx : x.length = d) :
    weylchar.stdSq (places.display x) * (blockSpan x).length
      + 2 * ((places.pairsOf d).length * mom11 (blockSpan x))
    = d * mom2At 0 (blockSpan x)
      + 2 * (mom1 (blockSpan x) * ground.sumNat (places.unitDisp d))
      + (blockSpan x).length * weylchar.stdSq (places.unitDisp d)
      + 2 * ((places.pairsOf d).length * mom2At 0 (blockSpan x)) := by
  have hwid : ∀ v : HVec, 0 < ground.countOf v (blockSpan x) →
      v.content.length = d := by
    intro v hv
    rw [blockcount.blockSpan_width x v
      (ground.mem_of_countOf_pos v _ hv), hx]
  have hA : ground.famFold Nat.add 0
        (fun v => weylchar.stdSq v.content) (blockSpan x)
      = d * mom2At 0 (blockSpan x) := by
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun v => ground.famFold Nat.add 0
          (fun k => ground.getAt 0 v.content k
            * ground.getAt 0 v.content k)
          (List.range d)) (blockSpan x)
        (fun v hv => by rw [weylchar.stdSq_index v.content, hwid v hv]),
      ground.famFold_swap
        (fun (v : HVec) (k : Nat) => ground.getAt 0 v.content k
          * ground.getAt 0 v.content k)
        (blockSpan x) (List.range d),
      ground.famFold_congr_members Nat.add 0
        (fun k : Nat => ground.famFold Nat.add 0
          (fun v : HVec => ground.getAt 0 v.content k
            * ground.getAt 0 v.content k) (blockSpan x))
        (fun _ => mom2At 0 (blockSpan x)) (List.range d)
        (fun k hk => mom2At_free x k
          (by rw [hx]; exact ground.ltOfMem hk)),
      ground.famFold_const (mom2At 0 (blockSpan x)) (List.range d),
      ground.length_range d]
  have hB : ground.famFold Nat.add 0
        (fun v => ground.dotNat v.content (places.unitDisp d))
        (blockSpan x)
      = mom1 (blockSpan x) * ground.sumNat (places.unitDisp d) := by
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun v => ground.famFold Nat.add 0
          (fun i => ground.getAt 0 v.content i
            * ground.getAt 0 (places.unitDisp d) i)
          (List.range d)) (blockSpan x)
        (fun v hv => by
          rw [ground.dotNat_index v.content (places.unitDisp d)
            (by rw [places.length_unitDisp d, hwid v hv]),
            hwid v hv]),
      ground.famFold_swap
        (fun (v : HVec) (i : Nat) => ground.getAt 0 v.content i
          * ground.getAt 0 (places.unitDisp d) i)
        (blockSpan x) (List.range d),
      ground.famFold_congr_members Nat.add 0 _
        (fun i => mom1 (blockSpan x)
          * ground.getAt 0 (places.unitDisp d) i)
        (List.range d)
        (fun i hi => by
          rw [ground.famFold_mulR
            (ground.getAt 0 (places.unitDisp d) i)
            (fun v : HVec => ground.getAt 0 v.content i)
            (blockSpan x)]
          show mom1At i (blockSpan x)
              * ground.getAt 0 (places.unitDisp d) i
            = mom1 (blockSpan x)
              * ground.getAt 0 (places.unitDisp d) i
          rw [mom1At_free x i (by rw [hx]; exact ground.ltOfMem hi)]),
      ← ground.famFold_mul (mom1 (blockSpan x))
        (fun i => ground.getAt 0 (places.unitDisp d) i)
        (List.range d),
      show List.range d
          = List.range (places.unitDisp d).length from by
        rw [places.length_unitDisp d],
      ground.sumIndex (places.unitDisp d)]
  have hsplit : ground.famFold Nat.add 0
      (fun v => weylchar.stdSq (List.zipWith (fun a b => a + b)
        v.content (places.unitDisp d))) (blockSpan x)
    = d * mom2At 0 (blockSpan x)
      + 2 * (mom1 (blockSpan x) * ground.sumNat (places.unitDisp d))
      + (blockSpan x).length * weylchar.stdSq (places.unitDisp d) := by
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun v => weylchar.stdSq v.content
          + 2 * ground.dotNat v.content (places.unitDisp d)
          + weylchar.stdSq (places.unitDisp d)) (blockSpan x)
        (fun v hv => weylchar.sqSplit v.content (places.unitDisp d)
          (by rw [hwid v hv, places.length_unitDisp d])),
      ground.famFold_add_split
        (fun v : HVec => weylchar.stdSq v.content
          + 2 * ground.dotNat v.content (places.unitDisp d))
        (fun _ : HVec => weylchar.stdSq (places.unitDisp d))
        (blockSpan x),
      ground.famFold_add_split
        (fun v : HVec => weylchar.stdSq v.content)
        (fun v : HVec => 2
          * ground.dotNat v.content (places.unitDisp d))
        (blockSpan x),
      ← ground.famFold_mul 2
        (fun v : HVec => ground.dotNat v.content
          (places.unitDisp d)) (blockSpan x),
      hA, hB,
      ground.famFold_const (weylchar.stdSq (places.unitDisp d))
        (blockSpan x)]
  have hsum := sumRec x
  rw [wCross_fold x, wSqP_fold x, hx, hsplit] at hsum
  exact hsum

/-! The tensor splits: the fused pool's moments over the two
factors' own, each member's content the factors' componentwise sum
(`fold_fusedAt`) with the entry reads the walk's
(`ground.getAt_zipWith`). -/

/-- The two joins' product at the four cross terms. -/
private theorem prodExpand (a c b e : Nat) :
    (a + b) * (c + e) = a * c + (a * e + b * c) + b * e := by
  rw [Nat.left_distrib (a + b) c e, ground.mulAddR a b c,
    ground.mulAddR a b e,
    Nat.add_assoc (a * c) (b * c) (a * e + b * e),
    ← Nat.add_assoc (b * c) (a * e) (b * e),
    Nat.add_comm (b * c) (a * e),
    ← Nat.add_assoc (a * c) (a * e + b * c) (b * e)]

/-- The two blocks' members carry the shapes' widths. -/
private theorem span_pos (s : Shape) (k : Nat) (hs : k < s.length) :
    ∀ v : HVec, 0 < ground.countOf v (blockSpan s) →
      k < v.content.length := by
  intro v hv
  rw [blockcount.blockSpan_width s v
    (ground.mem_of_countOf_pos v _ hv)]
  exact hs

/-- The fused pool's first moment splits over the two factors. -/
private theorem momT1 (s t : Shape) (hs : 0 < s.length)
    (ht : 0 < t.length) :
    mom1 (fusedAt (blockSpan s) (blockSpan t))
      = (blockSpan t).length * mom1 (blockSpan s)
        + (blockSpan s).length * mom1 (blockSpan t) := by
  refine Eq.trans (fold_fusedAt (blockSpan s) (blockSpan t)
    (fun mu => ground.getAt 0 mu 0)) ?_
  rw [ground.famFold_congr_members Nat.add 0 _
      (fun x : HVec => ground.famFold Nat.add 0
        (fun y : HVec => ground.getAt 0 x.content 0
          + ground.getAt 0 y.content 0) (blockSpan t)) (blockSpan s)
      (fun x hx => ground.famFold_congr_members Nat.add 0 _ _
        (blockSpan t)
        (fun y hy => ground.getAt_zipWith 0 0 0 (fun p q => p + q)
          x.content y.content 0 (span_pos s 0 hs x hx)
          (span_pos t 0 ht y hy))),
    ground.famFold_congr_all Nat.add 0 _
      (fun x : HVec => (blockSpan t).length
        * ground.getAt 0 x.content 0 + mom1 (blockSpan t))
      (fun x => by
        rw [ground.famFold_add_split
            (fun _ : HVec => ground.getAt 0 x.content 0)
            (fun y : HVec => ground.getAt 0 y.content 0)
            (blockSpan t),
          ground.famFold_const (ground.getAt 0 x.content 0)
            (blockSpan t)]
        rfl)
      (blockSpan s),
    ground.famFold_add_split
      (fun x : HVec => (blockSpan t).length
        * ground.getAt 0 x.content 0)
      (fun _ : HVec => mom1 (blockSpan t)) (blockSpan s),
    ← ground.famFold_mul (blockSpan t).length
      (fun x : HVec => ground.getAt 0 x.content 0) (blockSpan s),
    ground.famFold_const (mom1 (blockSpan t)) (blockSpan s)]
  rfl

/-- The fused pool's square moment splits over the two factors,
the join's square at the cross term. -/
private theorem momT2 (s t : Shape) (hs : 0 < s.length)
    (ht : 0 < t.length) :
    mom2At 0 (fusedAt (blockSpan s) (blockSpan t))
      = (blockSpan t).length * mom2At 0 (blockSpan s)
        + 2 * (mom1 (blockSpan s) * mom1 (blockSpan t))
        + (blockSpan s).length * mom2At 0 (blockSpan t) := by
  refine Eq.trans (fold_fusedAt (blockSpan s) (blockSpan t)
    (fun mu => ground.getAt 0 mu 0 * ground.getAt 0 mu 0)) ?_
  rw [ground.famFold_congr_members Nat.add 0 _
      (fun x : HVec => ground.famFold Nat.add 0
        (fun y : HVec => ground.getAt 0 x.content 0
            * ground.getAt 0 x.content 0
          + 2 * (ground.getAt 0 x.content 0
            * ground.getAt 0 y.content 0)
          + ground.getAt 0 y.content 0 * ground.getAt 0 y.content 0)
        (blockSpan t)) (blockSpan s)
      (fun x hx => ground.famFold_congr_members Nat.add 0 _ _
        (blockSpan t)
        (fun y hy => by
          rw [ground.getAt_zipWith 0 0 0 (fun p q => p + q)
            x.content y.content 0 (span_pos s 0 hs x hx)
            (span_pos t 0 ht y hy)]
          exact ground.sqAdd (ground.getAt 0 x.content 0)
            (ground.getAt 0 y.content 0))),
    ground.famFold_congr_all Nat.add 0 _
      (fun x : HVec => (blockSpan t).length
          * (ground.getAt 0 x.content 0 * ground.getAt 0 x.content 0)
        + 2 * (ground.getAt 0 x.content 0 * mom1 (blockSpan t))
        + mom2At 0 (blockSpan t))
      (fun x => by
        rw [ground.famFold_add_split
            (fun y : HVec => ground.getAt 0 x.content 0
                * ground.getAt 0 x.content 0
              + 2 * (ground.getAt 0 x.content 0
                * ground.getAt 0 y.content 0))
            (fun y : HVec => ground.getAt 0 y.content 0
              * ground.getAt 0 y.content 0) (blockSpan t),
          ground.famFold_add_split
            (fun _ : HVec => ground.getAt 0 x.content 0
              * ground.getAt 0 x.content 0)
            (fun y : HVec => 2 * (ground.getAt 0 x.content 0
              * ground.getAt 0 y.content 0)) (blockSpan t),
          ground.famFold_const (ground.getAt 0 x.content 0
            * ground.getAt 0 x.content 0) (blockSpan t),
          ← ground.famFold_mul 2
            (fun y : HVec => ground.getAt 0 x.content 0
              * ground.getAt 0 y.content 0) (blockSpan t),
          ← ground.famFold_mul (ground.getAt 0 x.content 0)
            (fun y : HVec => ground.getAt 0 y.content 0)
            (blockSpan t)]
        rfl)
      (blockSpan s),
    ground.famFold_add_split
      (fun x : HVec => (blockSpan t).length
          * (ground.getAt 0 x.content 0 * ground.getAt 0 x.content 0)
        + 2 * (ground.getAt 0 x.content 0 * mom1 (blockSpan t)))
      (fun _ : HVec => mom2At 0 (blockSpan t)) (blockSpan s),
    ground.famFold_add_split
      (fun x : HVec => (blockSpan t).length
        * (ground.getAt 0 x.content 0 * ground.getAt 0 x.content 0))
      (fun x : HVec => 2 * (ground.getAt 0 x.content 0
        * mom1 (blockSpan t))) (blockSpan s),
    ← ground.famFold_mul (blockSpan t).length
      (fun x : HVec => ground.getAt 0 x.content 0
        * ground.getAt 0 x.content 0) (blockSpan s),
    ← ground.famFold_mul 2
      (fun x : HVec => ground.getAt 0 x.content 0
        * mom1 (blockSpan t)) (blockSpan s),
    ground.famFold_mulR (mom1 (blockSpan t))
      (fun x : HVec => ground.getAt 0 x.content 0) (blockSpan s),
    ground.famFold_const (mom2At 0 (blockSpan t)) (blockSpan s)]
  rfl

/-- The fused pool's cross moment splits over the two factors, the
mixed terms the two factors' first moments at the shared width. -/
private theorem momT11 (s t : Shape) (hs : 1 < s.length)
    (ht : 1 < t.length) :
    mom11 (fusedAt (blockSpan s) (blockSpan t))
      = (blockSpan t).length * mom11 (blockSpan s)
        + 2 * (mom1 (blockSpan s) * mom1 (blockSpan t))
        + (blockSpan s).length * mom11 (blockSpan t) := by
  have hs0 : 0 < s.length := Nat.lt_trans Nat.zero_lt_one hs
  have ht0 : 0 < t.length := Nat.lt_trans Nat.zero_lt_one ht
  have hA1 : mom1At 1 (blockSpan s) = mom1 (blockSpan s) :=
    mom1At_free s 1 hs
  have hB1 : mom1At 1 (blockSpan t) = mom1 (blockSpan t) :=
    mom1At_free t 1 ht
  refine Eq.trans (fold_fusedAt (blockSpan s) (blockSpan t)
    (fun mu => ground.getAt 0 mu 0 * ground.getAt 0 mu 1)) ?_
  rw [ground.famFold_congr_members Nat.add 0 _
      (fun x : HVec => ground.famFold Nat.add 0
        (fun y : HVec => ground.getAt 0 x.content 0
            * ground.getAt 0 x.content 1
          + (ground.getAt 0 x.content 0 * ground.getAt 0 y.content 1
            + ground.getAt 0 y.content 0
              * ground.getAt 0 x.content 1)
          + ground.getAt 0 y.content 0 * ground.getAt 0 y.content 1)
        (blockSpan t)) (blockSpan s)
      (fun x hx => ground.famFold_congr_members Nat.add 0 _ _
        (blockSpan t)
        (fun y hy => by
          rw [ground.getAt_zipWith 0 0 0 (fun p q => p + q)
              x.content y.content 0 (span_pos s 0 hs0 x hx)
              (span_pos t 0 ht0 y hy),
            ground.getAt_zipWith 0 0 0 (fun p q => p + q)
              x.content y.content 1 (span_pos s 1 hs x hx)
              (span_pos t 1 ht y hy)]
          exact prodExpand (ground.getAt 0 x.content 0)
            (ground.getAt 0 x.content 1)
            (ground.getAt 0 y.content 0)
            (ground.getAt 0 y.content 1))),
    ground.famFold_congr_all Nat.add 0 _
      (fun x : HVec => (blockSpan t).length
          * (ground.getAt 0 x.content 0 * ground.getAt 0 x.content 1)
        + (ground.getAt 0 x.content 0 * mom1 (blockSpan t)
          + mom1 (blockSpan t) * ground.getAt 0 x.content 1)
        + mom11 (blockSpan t))
      (fun x => by
        rw [ground.famFold_add_split
            (fun y : HVec => ground.getAt 0 x.content 0
                * ground.getAt 0 x.content 1
              + (ground.getAt 0 x.content 0
                  * ground.getAt 0 y.content 1
                + ground.getAt 0 y.content 0
                  * ground.getAt 0 x.content 1))
            (fun y : HVec => ground.getAt 0 y.content 0
              * ground.getAt 0 y.content 1) (blockSpan t),
          ground.famFold_add_split
            (fun _ : HVec => ground.getAt 0 x.content 0
              * ground.getAt 0 x.content 1)
            (fun y : HVec => ground.getAt 0 x.content 0
                * ground.getAt 0 y.content 1
              + ground.getAt 0 y.content 0
                * ground.getAt 0 x.content 1) (blockSpan t),
          ground.famFold_add_split
            (fun y : HVec => ground.getAt 0 x.content 0
              * ground.getAt 0 y.content 1)
            (fun y : HVec => ground.getAt 0 y.content 0
              * ground.getAt 0 x.content 1) (blockSpan t),
          ground.famFold_const (ground.getAt 0 x.content 0
            * ground.getAt 0 x.content 1) (blockSpan t),
          ← ground.famFold_mul (ground.getAt 0 x.content 0)
            (fun y : HVec => ground.getAt 0 y.content 1)
            (blockSpan t),
          ground.famFold_mulR (ground.getAt 0 x.content 1)
            (fun y : HVec => ground.getAt 0 y.content 0)
            (blockSpan t)]
        show (blockSpan t).length * _
            + (ground.getAt 0 x.content 0 * mom1At 1 (blockSpan t)
              + mom1 (blockSpan t) * ground.getAt 0 x.content 1)
            + mom11 (blockSpan t) = _
        rw [hB1])
      (blockSpan s),
    ground.famFold_add_split
      (fun x : HVec => (blockSpan t).length
          * (ground.getAt 0 x.content 0 * ground.getAt 0 x.content 1)
        + (ground.getAt 0 x.content 0 * mom1 (blockSpan t)
          + mom1 (blockSpan t) * ground.getAt 0 x.content 1))
      (fun _ : HVec => mom11 (blockSpan t)) (blockSpan s),
    ground.famFold_add_split
      (fun x : HVec => (blockSpan t).length
        * (ground.getAt 0 x.content 0 * ground.getAt 0 x.content 1))
      (fun x : HVec => ground.getAt 0 x.content 0
          * mom1 (blockSpan t)
        + mom1 (blockSpan t) * ground.getAt 0 x.content 1)
      (blockSpan s),
    ground.famFold_add_split
      (fun x : HVec => ground.getAt 0 x.content 0
        * mom1 (blockSpan t))
      (fun x : HVec => mom1 (blockSpan t)
        * ground.getAt 0 x.content 1) (blockSpan s),
    ← ground.famFold_mul (blockSpan t).length
      (fun x : HVec => ground.getAt 0 x.content 0
        * ground.getAt 0 x.content 1) (blockSpan s),
    ground.famFold_mulR (mom1 (blockSpan t))
      (fun x : HVec => ground.getAt 0 x.content 0) (blockSpan s),
    ← ground.famFold_mul (mom1 (blockSpan t))
      (fun x : HVec => ground.getAt 0 x.content 1) (blockSpan s),
    ground.famFold_const (mom11 (blockSpan t)) (blockSpan s)]
  show (blockSpan t).length * mom11 (blockSpan s)
      + (mom1 (blockSpan s) * mom1 (blockSpan t)
        + mom1 (blockSpan t) * mom1At 1 (blockSpan s))
      + (blockSpan s).length * mom11 (blockSpan t) = _
  rw [hA1, Nat.mul_comm (mom1 (blockSpan t)) (mom1 (blockSpan s)),
    ← Nat.two_mul (mom1 (blockSpan s) * mom1 (blockSpan t))]

/-! The assembly's arithmetic: the products' reassociations, the
four-term right distribution, and the two regroupings that carry
the channel fold and the two factors' recursions onto the one
cancellation. -/

/-- A scalar against a three-term sum. -/
private theorem mulTri (c u v w : Nat) :
    c * (u + v + w) = c * u + c * v + c * w := by
  rw [Nat.left_distrib c (u + v) w, Nat.left_distrib c u v]

/-- A two-factor product's second factor moves to the right. -/
private theorem swap3 (a c e : Nat) : a * (c * e) = a * e * c := by
  rw [← ground.mulAssoc a c e]
  exact ground.mulRightComm a c e

/-- A three-factor product's third factor moves to the right. -/
private theorem swap4 (a b c e : Nat) :
    a * (b * (c * e)) = a * (b * e) * c := by
  rw [← ground.mulAssoc b c e, ground.mulRightComm b c e,
    ← ground.mulAssoc a (b * e) c]

/-- A leading scalar passes two factors. -/
private theorem pull4 (n a b m : Nat) :
    n * (a * (b * m)) = a * (b * (n * m)) := by
  rw [ground.mulLeftComm n a (b * m), ground.mulLeftComm n b m]

/-- A leading scalar joins an inner left factor. -/
private theorem pullMid (n a m u : Nat) :
    n * (a * (m * u)) = a * (n * m * u) := by
  rw [ground.mulLeftComm n a (m * u), ← ground.mulAssoc n m u]

/-- A four-term sum's right distribution. -/
private theorem quadR (a b c e f : Nat) :
    (a + b + c + e) * f = a * f + b * f + c * f + e * f := by
  rw [ground.mulAddR (a + b + c) e f, ground.mulAddR (a + b) c f,
    ground.mulAddR a b f]

/-- The cancellation joining the channel fold to the two factors'
recursions: the shared shift and the shared common part withdraw
and the two displays stand. -/
private theorem cancelJoin (SQ G u v w q p : Nat)
    (hA : SQ + u + p = v + w + q + p)
    (hG : G + u = v + (q + q)) : SQ + q = G + w := by
  have h1 : SQ + u = v + w + q := ground.addCancelR p hA
  refine ground.addCancelR u ?_
  rw [Nat.add_right_comm SQ q u, h1, Nat.add_right_comm G w u, hG,
    Nat.add_assoc (v + w) q q, Nat.add_assoc v w (q + q),
    Nat.add_comm w (q + q), ← Nat.add_assoc v (q + q) w]

/-- The channel fold's regrouping: the two factors' parts collect
against the shared cross term, the shared shift, and the unit
display's own weight. -/
private theorem regroupA (v1 w v2 e1 e2 q g1 p g2 : Nat) :
    v1 + w + v2 + (e1 + e2) + q + (g1 + p + g2)
      = v1 + v2 + (e1 + e2) + (g1 + g2) + w + q + p := by
  rw [Nat.add_right_comm g1 p g2,
    ← Nat.add_assoc (v1 + w + v2 + (e1 + e2) + q) (g1 + g2) p,
    Nat.add_right_comm v1 w v2,
    Nat.add_right_comm (v1 + v2) w (e1 + e2),
    Nat.add_right_comm (v1 + v2 + (e1 + e2)) w q,
    Nat.add_right_comm (v1 + v2 + (e1 + e2) + q) w (g1 + g2),
    Nat.add_right_comm (v1 + v2 + (e1 + e2)) q (g1 + g2),
    Nat.add_right_comm (v1 + v2 + (e1 + e2) + (g1 + g2)) q w]

/-! The channel recursion: the summed recursion at every channel
shape, folded against the channels' fusion counts — the moment
folds collecting to the fused pool's own
(`fold_channels`) and the channel dimensions to the two blocks'
count product (`blockcount.fusionCount_dim`). -/

/-- The summed recursion folded over the channels: the channels'
display squares against the fused pool's moments. -/
private theorem foldRec (d : Nat) (s t : Shape)
    (hsd : s.length = d) (hts : t.length = s.length) :
    ground.famFold Nat.add 0
        (fun mu => fusionCount s t (places.shapeOf mu)
          * (weylchar.stdSq (places.display (places.shapeOf mu))
            * (blockSpan (places.shapeOf mu)).length))
        (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content))
      + 2 * ((places.pairsOf d).length * mom11 (fusedAt (blockSpan s) (blockSpan t)))
    = d * mom2At 0 (fusedAt (blockSpan s) (blockSpan t))
      + 2 * (mom1 (fusedAt (blockSpan s) (blockSpan t)) * ground.sumNat (places.unitDisp d))
      + (blockSpan s).length * (blockSpan t).length * weylchar.stdSq (places.unitDisp d)
      + 2 * ((places.pairsOf d).length * mom2At 0 (fusedAt (blockSpan s) (blockSpan t))) := by
  obtain ⟨hszP, hwidP, hclP, hiP⟩ := fusedSpan_pack s t hts
  have hwd : ∀ mu : List Nat, 0 < ground.countOf mu
      (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)) → mu.length = d := by
    intro mu hmu
    rw [exhaust_width s.length
      (fusedAt (blockSpan s) (blockSpan t)) hszP hwidP hclP mu
      (ground.mem_of_dedupL (ground.mem_of_countOf_pos mu _ hmu))]
    exact hsd
  have hc1 : ground.famFold Nat.add 0
      (fun mu => fusionCount s t (places.shapeOf mu) * mom1 (blockSpan
        (places.shapeOf mu))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content))
    = mom1 (fusedAt (blockSpan s) (blockSpan t)) :=
    (fold_channels s t hts (fun mu => ground.getAt 0 mu 0)).symm
  have hc2 : ground.famFold Nat.add 0
      (fun mu => fusionCount s t (places.shapeOf mu) * mom2At 0 (blockSpan
        (places.shapeOf mu))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content))
    = mom2At 0 (fusedAt (blockSpan s) (blockSpan t)) :=
    (fold_channels s t hts
      (fun mu => ground.getAt 0 mu 0 * ground.getAt 0 mu 0)).symm
  have hc11 : ground.famFold Nat.add 0
      (fun mu => fusionCount s t (places.shapeOf mu) * mom11 (blockSpan
        (places.shapeOf mu))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content))
    = mom11 (fusedAt (blockSpan s) (blockSpan t)) :=
    (fold_channels s t hts
      (fun mu => ground.getAt 0 mu 0 * ground.getAt 0 mu 1)).symm
  have hdim := blockcount.fusionCount_dim s t hts
  have step1 : ground.famFold Nat.add 0
      (fun mu => fusionCount s t (places.shapeOf mu)
        * (weylchar.stdSq (places.display (places.shapeOf mu))
            * (blockSpan (places.shapeOf mu)).length
          + 2 * ((places.pairsOf d).length * mom11 (blockSpan (places.shapeOf
            mu))))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content))
    = ground.famFold Nat.add 0
        (fun mu => fusionCount s t (places.shapeOf mu)
          * (weylchar.stdSq (places.display (places.shapeOf mu))
            * (blockSpan (places.shapeOf mu)).length)) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content))
      + 2 * ((places.pairsOf d).length * mom11 (fusedAt (blockSpan s) (blockSpan t))) := by
    rw [ground.famFold_congr_all Nat.add 0 _
        (fun mu => fusionCount s t (places.shapeOf mu)
            * (weylchar.stdSq (places.display (places.shapeOf mu))
              * (blockSpan (places.shapeOf mu)).length)
          + 2 * ((places.pairsOf d).length
            * (fusionCount s t (places.shapeOf mu) * mom11 (blockSpan (places.shapeOf mu)))))
        (fun mu => by
          rw [Nat.left_distrib (fusionCount s t (places.shapeOf mu))
              (weylchar.stdSq (places.display (places.shapeOf mu))
                * (blockSpan (places.shapeOf mu)).length)
              (2 * ((places.pairsOf d).length * mom11 (blockSpan (places.shapeOf mu)))),
            pull4 (fusionCount s t (places.shapeOf mu)) 2 ((places.pairsOf d).length)
              (mom11 (blockSpan (places.shapeOf mu)))]) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ground.famFold_add_split
        (fun mu => fusionCount s t (places.shapeOf mu)
          * (weylchar.stdSq (places.display (places.shapeOf mu))
            * (blockSpan (places.shapeOf mu)).length))
        (fun mu => 2 * ((places.pairsOf d).length
          * (fusionCount s t (places.shapeOf mu) * mom11 (blockSpan
            (places.shapeOf mu))))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ← ground.famFold_mul 2
        (fun mu => (places.pairsOf d).length
          * (fusionCount s t (places.shapeOf mu) * mom11 (blockSpan
            (places.shapeOf mu)))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ← ground.famFold_mul ((places.pairsOf d).length)
        (fun mu => fusionCount s t (places.shapeOf mu) * mom11 (blockSpan
          (places.shapeOf mu))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      hc11]
  have step2 : ground.famFold Nat.add 0
      (fun mu => fusionCount s t (places.shapeOf mu)
        * (d * mom2At 0 (blockSpan (places.shapeOf mu))
          + 2 * (mom1 (blockSpan (places.shapeOf mu)) * ground.sumNat (places.unitDisp d))
          + (blockSpan (places.shapeOf mu)).length * weylchar.stdSq (places.unitDisp d)
          + 2 * ((places.pairsOf d).length * mom2At 0 (blockSpan
            (places.shapeOf mu))))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content))
    = d * mom2At 0 (fusedAt (blockSpan s) (blockSpan t))
      + 2 * (mom1 (fusedAt (blockSpan s) (blockSpan t)) * ground.sumNat (places.unitDisp d))
      + (blockSpan s).length * (blockSpan t).length * weylchar.stdSq (places.unitDisp d)
      + 2 * ((places.pairsOf d).length * mom2At 0 (fusedAt (blockSpan s) (blockSpan t))) := by
    rw [ground.famFold_congr_all Nat.add 0 _
        (fun mu => d * (fusionCount s t (places.shapeOf mu) * mom2At 0
          (blockSpan (places.shapeOf mu)))
          + 2 * (fusionCount s t (places.shapeOf mu) * mom1 (blockSpan
            (places.shapeOf mu)) * ground.sumNat (places.unitDisp d))
          + fusionCount s t (places.shapeOf mu) * (blockSpan (places.shapeOf
            mu)).length * weylchar.stdSq (places.unitDisp d)
          + 2 * ((places.pairsOf d).length
            * (fusionCount s t (places.shapeOf mu) * mom2At 0 (blockSpan (places.shapeOf mu)))))
        (fun mu => by
          rw [mulTri (fusionCount s t (places.shapeOf mu))
              (d * mom2At 0 (blockSpan (places.shapeOf mu))
                + 2 * (mom1 (blockSpan (places.shapeOf mu)) * ground.sumNat (places.unitDisp d)))
              ((blockSpan (places.shapeOf mu)).length * weylchar.stdSq (places.unitDisp d))
              (2 * ((places.pairsOf d).length * mom2At 0 (blockSpan (places.shapeOf mu)))),
            Nat.left_distrib (fusionCount s t (places.shapeOf mu))
              (d * mom2At 0 (blockSpan (places.shapeOf mu)))
              (2 * (mom1 (blockSpan (places.shapeOf mu)) * ground.sumNat (places.unitDisp d))),
            ground.mulLeftComm (fusionCount s t (places.shapeOf mu)) d (mom2At
              0 (blockSpan (places.shapeOf mu))),
            pullMid (fusionCount s t (places.shapeOf mu)) 2 (mom1 (blockSpan
              (places.shapeOf mu))) (ground.sumNat (places.unitDisp d)),
            ← ground.mulAssoc (fusionCount s t (places.shapeOf mu))
              ((blockSpan (places.shapeOf mu)).length) (weylchar.stdSq (places.unitDisp d)),
            pull4 (fusionCount s t (places.shapeOf mu)) 2 ((places.pairsOf d).length)
              (mom2At 0 (blockSpan (places.shapeOf mu)))]) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ground.famFold_add_split
        (fun mu => d * (fusionCount s t (places.shapeOf mu) * mom2At 0
          (blockSpan (places.shapeOf mu)))
          + 2 * (fusionCount s t (places.shapeOf mu) * mom1 (blockSpan
            (places.shapeOf mu)) * ground.sumNat (places.unitDisp d))
          + fusionCount s t (places.shapeOf mu) * (blockSpan (places.shapeOf
            mu)).length * weylchar.stdSq (places.unitDisp d))
        (fun mu => 2 * ((places.pairsOf d).length
          * (fusionCount s t (places.shapeOf mu) * mom2At 0 (blockSpan
            (places.shapeOf mu))))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ground.famFold_add_split
        (fun mu => d * (fusionCount s t (places.shapeOf mu) * mom2At 0
          (blockSpan (places.shapeOf mu)))
          + 2 * (fusionCount s t (places.shapeOf mu) * mom1 (blockSpan
            (places.shapeOf mu)) * ground.sumNat (places.unitDisp d)))
        (fun mu => fusionCount s t (places.shapeOf mu) * (blockSpan
          (places.shapeOf mu)).length * weylchar.stdSq (places.unitDisp d))
          (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ground.famFold_add_split
        (fun mu => d * (fusionCount s t (places.shapeOf mu) * mom2At 0
          (blockSpan (places.shapeOf mu))))
        (fun mu => 2 * (fusionCount s t (places.shapeOf mu) * mom1 (blockSpan
          (places.shapeOf mu)) * ground.sumNat (places.unitDisp d)))
          (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ← ground.famFold_mul d
        (fun mu => fusionCount s t (places.shapeOf mu) * mom2At 0 (blockSpan
          (places.shapeOf mu))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ← ground.famFold_mul 2
        (fun mu => fusionCount s t (places.shapeOf mu) * mom1 (blockSpan
          (places.shapeOf mu)) * ground.sumNat (places.unitDisp d))
          (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ground.famFold_mulR (ground.sumNat (places.unitDisp d))
        (fun mu => fusionCount s t (places.shapeOf mu) * mom1 (blockSpan
          (places.shapeOf mu))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ground.famFold_mulR (weylchar.stdSq (places.unitDisp d))
        (fun mu => fusionCount s t (places.shapeOf mu) * (blockSpan
          (places.shapeOf mu)).length) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ← ground.famFold_mul 2
        (fun mu => (places.pairsOf d).length
          * (fusionCount s t (places.shapeOf mu) * mom2At 0 (blockSpan
            (places.shapeOf mu)))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      ← ground.famFold_mul ((places.pairsOf d).length)
        (fun mu => fusionCount s t (places.shapeOf mu) * mom2At 0 (blockSpan
          (places.shapeOf mu))) (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)),
      hc1, hc2, hdim]
  rw [← step1, ← step2]
  refine ground.famFold_congr_members Nat.add 0 _ _ (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan t))).map HVec.content)) ?_
  intro mu hmu
  exact congrArg (fun z => fusionCount s t (places.shapeOf mu) * z)
    (momRec d (places.shapeOf mu)
      ((places.length_shapeOf mu).trans (hwd mu hmu)))

/-- A scalar against a scaled three-term sum. -/
private theorem mulTri2 (a b u v w : Nat) :
    a * (b * (u + v + w)) = a * (b * u) + a * (b * v) + a * (b * w) := by
  rw [mulTri b u v w, mulTri a (b * u) (b * v) (b * w)]

/-- The unit display's weight against the two counts, read from
the second factor's side. -/
private theorem quSwapR (a c b : Nat) : b * c * a = c * (a * b) := by
  rw [ground.mulAssoc b c a, ground.mulLeftComm b c a,
    Nat.mul_comm b a]

/-- The channel fold against the two factors' recursions: the
common part and the shared cross weight withdraw, leaving the two
displays against the count product and the width's own cross
term. -/
private theorem assembleC (SQ P d U1 qu Qs Qt Ds Dt
    M1s M1t M2s M2t M11s M11t : Nat)
    (hA : SQ + 2 * (P * (Dt * M11s + 2 * (M1s * M1t) + Ds * M11t))
        = d * (Dt * M2s + 2 * (M1s * M1t) + Ds * M2t)
          + 2 * ((Dt * M1s + Ds * M1t) * U1)
          + Ds * Dt * qu
          + 2 * (P * (Dt * M2s + 2 * (M1s * M1t) + Ds * M2t)))
    (hs : Qs * Ds + 2 * (P * M11s)
        = d * M2s + 2 * (M1s * U1) + Ds * qu + 2 * (P * M2s))
    (ht : Qt * Dt + 2 * (P * M11t)
        = d * M2t + 2 * (M1t * U1) + Dt * qu + 2 * (P * M2t)) :
    SQ + qu * (Ds * Dt)
      = Qs * Ds * Dt + Qt * Dt * Ds + 2 * (d * (M1s * M1t)) := by
  have hs' : Qs * Ds * Dt + 2 * (P * M11s) * Dt
      = d * M2s * Dt + 2 * (M1s * U1) * Dt + 2 * (P * M2s) * Dt
        + qu * (Ds * Dt) := by
    have h : (Qs * Ds + 2 * (P * M11s)) * Dt
        = (d * M2s + 2 * (M1s * U1) + Ds * qu + 2 * (P * M2s)) * Dt :=
      congrArg (fun z => z * Dt) hs
    rw [ground.mulAddR (Qs * Ds) (2 * (P * M11s)) Dt,
      quadR (d * M2s) (2 * (M1s * U1)) (Ds * qu) (2 * (P * M2s)) Dt,
      Nat.add_right_comm (d * M2s * Dt + 2 * (M1s * U1) * Dt)
        (Ds * qu * Dt) (2 * (P * M2s) * Dt),
      ← ground.mulHeadComm qu Ds Dt] at h
    exact h
  have ht' : Qt * Dt * Ds + 2 * (P * M11t) * Ds
      = d * M2t * Ds + 2 * (M1t * U1) * Ds + 2 * (P * M2t) * Ds
        + qu * (Ds * Dt) := by
    have h : (Qt * Dt + 2 * (P * M11t)) * Ds
        = (d * M2t + 2 * (M1t * U1) + Dt * qu + 2 * (P * M2t)) * Ds :=
      congrArg (fun z => z * Ds) ht
    rw [ground.mulAddR (Qt * Dt) (2 * (P * M11t)) Ds,
      quadR (d * M2t) (2 * (M1t * U1)) (Dt * qu) (2 * (P * M2t)) Ds,
      Nat.add_right_comm (d * M2t * Ds + 2 * (M1t * U1) * Ds)
        (Dt * qu * Ds) (2 * (P * M2t) * Ds),
      quSwapR Ds qu Dt] at h
    exact h
  have hG : Qs * Ds * Dt + Qt * Dt * Ds
        + (2 * (P * M11s) * Dt + 2 * (P * M11t) * Ds)
      = d * M2s * Dt + d * M2t * Ds
          + (2 * (M1s * U1) * Dt + 2 * (M1t * U1) * Ds)
          + (2 * (P * M2s) * Dt + 2 * (P * M2t) * Ds)
        + (qu * (Ds * Dt) + qu * (Ds * Dt)) := by
    rw [← Nat.add_add_add_comm (Qs * Ds * Dt) (2 * (P * M11s) * Dt)
        (Qt * Dt * Ds) (2 * (P * M11t) * Ds),
      hs', ht',
      Nat.add_add_add_comm
        (d * M2s * Dt + 2 * (M1s * U1) * Dt + 2 * (P * M2s) * Dt)
        (qu * (Ds * Dt))
        (d * M2t * Ds + 2 * (M1t * U1) * Ds + 2 * (P * M2t) * Ds)
        (qu * (Ds * Dt)),
      Nat.add_add_add_comm
        (d * M2s * Dt + 2 * (M1s * U1) * Dt) (2 * (P * M2s) * Dt)
        (d * M2t * Ds + 2 * (M1t * U1) * Ds) (2 * (P * M2t) * Ds),
      Nat.add_add_add_comm (d * M2s * Dt) (2 * (M1s * U1) * Dt)
        (d * M2t * Ds) (2 * (M1t * U1) * Ds)]
  have hA' : SQ + (2 * (P * M11s) * Dt + 2 * (P * M11t) * Ds)
        + 2 * (P * (2 * (M1s * M1t)))
      = d * M2s * Dt + d * M2t * Ds
          + (2 * (M1s * U1) * Dt + 2 * (M1t * U1) * Ds)
          + (2 * (P * M2s) * Dt + 2 * (P * M2t) * Ds)
        + 2 * (d * (M1s * M1t)) + qu * (Ds * Dt)
        + 2 * (P * (2 * (M1s * M1t))) := by
    rw [mulTri2 2 P (Dt * M11s) (2 * (M1s * M1t)) (Ds * M11t),
      swap4 2 P Dt M11s, swap4 2 P Ds M11t,
      mulTri d (Dt * M2s) (2 * (M1s * M1t)) (Ds * M2t),
      swap3 d Dt M2s, swap3 d Ds M2t, ground.mulLeftComm d 2 (M1s * M1t),
      ground.mulAddR (Dt * M1s) (Ds * M1t) U1,
      Nat.left_distrib 2 (Dt * M1s * U1) (Ds * M1t * U1),
      ground.mulAssoc Dt M1s U1, ground.mulAssoc Ds M1t U1,
      swap3 2 Dt (M1s * U1), swap3 2 Ds (M1t * U1),
      Nat.mul_comm (Ds * Dt) qu,
      mulTri2 2 P (Dt * M2s) (2 * (M1s * M1t)) (Ds * M2t),
      swap4 2 P Dt M2s, swap4 2 P Ds M2t,
      Nat.add_right_comm (2 * (P * M11s) * Dt)
        (2 * (P * (2 * (M1s * M1t)))) (2 * (P * M11t) * Ds),
      ← Nat.add_assoc SQ
        (2 * (P * M11s) * Dt + 2 * (P * M11t) * Ds)
        (2 * (P * (2 * (M1s * M1t)))),
      regroupA (d * M2s * Dt) (2 * (d * (M1s * M1t)))
        (d * M2t * Ds) (2 * (M1s * U1) * Dt) (2 * (M1t * U1) * Ds)
        (qu * (Ds * Dt)) (2 * (P * M2s) * Dt)
        (2 * (P * (2 * (M1s * M1t)))) (2 * (P * M2t) * Ds)] at hA
    exact hA
  exact cancelJoin SQ (Qs * Ds * Dt + Qt * Dt * Ds)
    (2 * (P * M11s) * Dt + 2 * (P * M11t) * Ds)
    (d * M2s * Dt + d * M2t * Ds
      + (2 * (M1s * U1) * Dt + 2 * (M1t * U1) * Ds)
      + (2 * (P * M2s) * Dt + 2 * (P * M2t) * Ds))
    (2 * (d * (M1s * M1t))) (qu * (Ds * Dt))
    (2 * (P * (2 * (M1s * M1t)))) hA' hG

/-- The converted display's regrouping: the channel's raised
degree expands against the two factors' own and the shared unit
weights pair off. -/
private theorem regroupF (qs a b q e f g h : Nat) :
    qs + a + b + q + (e + f + g + q) + h
      = qs + e + (a + h + f + (b + g) + q + q) := by
  rw [← Nat.add_assoc (qs + a + b + q) (e + f + g) q,
    ← Nat.add_assoc (qs + a + b + q) (e + f) g,
    ← Nat.add_assoc (qs + a + b + q) e f,
    Nat.add_right_comm (qs + a + b) q e,
    Nat.add_right_comm (qs + a + b + e) q f,
    Nat.add_right_comm (qs + a + b + e + f) q g,
    Nat.add_right_comm (qs + a + b + e + f + g + q) q h,
    Nat.add_right_comm (qs + a + b + e + f + g) q h,
    ← Nat.add_assoc (qs + e) (a + h + f + (b + g) + q) q,
    ← Nat.add_assoc (qs + e) (a + h + f + (b + g)) q,
    ← Nat.add_assoc (qs + e) (a + h + f) (b + g),
    ← Nat.add_assoc (qs + e + (a + h + f)) b g,
    ← Nat.add_assoc (qs + e) (a + h) f,
    ← Nat.add_assoc (qs + e) a h,
    Nat.add_right_comm qs e a,
    Nat.add_right_comm (qs + a + e + h) f b,
    Nat.add_right_comm (qs + a + e) h b,
    Nat.add_right_comm (qs + a) e b,
    Nat.add_right_comm (qs + a + b + e) h f,
    Nat.add_right_comm (qs + a + b + e + f) h g]

/-- The display conversion's close: the channels' raised degree
withdraws against the two factors' converted displays and the
width's cross term, leaving the drift fold at the count product
against the shape's own cleared read and the adjoint's. -/
private theorem assembleFinal (X Ds Dt ks d qu qs : Nat)
    (h : X + ((ks + d) * (ks + d) + d * (d + 1) * (ks + d) + d * qu)
          * (Ds * Dt)
        + d * (qu * (Ds * Dt))
      = (qs + ks * ks + d * (d + 1) * ks + d * qu) * Ds * Dt
        + (2 * d * d + d * d + d * (d + 1) * d + d * qu) * Dt * Ds
        + 2 * (ks * Ds * (d * Dt))) :
    X = Ds * Dt * (qs + 2 * d * d) := by
  rw [ground.sqAdd ks d, Nat.left_distrib (d * (d + 1)) ks d,
    ← ground.mulAssoc d qu (Ds * Dt),
    Nat.add_assoc X
      ((ks * ks + 2 * (ks * d) + d * d
        + (d * (d + 1) * ks + d * (d + 1) * d) + d * qu) * (Ds * Dt))
      (d * qu * (Ds * Dt)),
    ← ground.mulAddR
      (ks * ks + 2 * (ks * d) + d * d
        + (d * (d + 1) * ks + d * (d + 1) * d) + d * qu)
      (d * qu) (Ds * Dt),
    ground.mulAssoc (qs + ks * ks + d * (d + 1) * ks + d * qu) Ds Dt,
    ground.mulAssoc (2 * d * d + d * d + d * (d + 1) * d + d * qu)
      Dt Ds,
    Nat.mul_comm Dt Ds,
    ground.mulMulMulComm ks Ds d Dt,
    ← ground.mulAssoc 2 (ks * d) (Ds * Dt),
    ← ground.mulAddR (qs + ks * ks + d * (d + 1) * ks + d * qu)
      (2 * d * d + d * d + d * (d + 1) * d + d * qu) (Ds * Dt),
    ← ground.mulAddR
      (qs + ks * ks + d * (d + 1) * ks + d * qu
        + (2 * d * d + d * d + d * (d + 1) * d + d * qu))
      (2 * (ks * d)) (Ds * Dt),
    regroupF qs (ks * ks) (d * (d + 1) * ks) (d * qu) (2 * d * d)
      (d * d) (d * (d + 1) * d) (2 * (ks * d)),
    ground.mulAddR (qs + 2 * d * d)
      (ks * ks + 2 * (ks * d) + d * d
        + (d * (d + 1) * ks + d * (d + 1) * d) + d * qu + d * qu)
      (Ds * Dt)] at h
  rw [ground.addCancelR _ h]
  exact Nat.mul_comm (qs + 2 * d * d) (Ds * Dt)

/-- The two factors' square pair at a shared scalar. -/
private theorem sqPair (a b c : Nat) :
    a * (a * (b * c)) = a * b * (a * c) := by
  rw [← ground.mulAssoc a a (b * c), ← ground.mulMulMulComm a b a c]

/-- `thm:drift`'s fold at the label calculus: the channels'
dimension-weighted Casimir fold reads the two blocks' count
product against the shape's cleared read and the adjoint's own
`2 d_f²`.  The channel recursion (`foldRec`) meets the two
factors' recursions (`momRec`) at the tensor splits, the shared
cross weight withdraws (`assembleC`), and the display conversion
(`qconv`) closes at the channels' one raised degree
(`assembleFinal`) with the first moments the degrees'
(`mom1_deg`). -/
private theorem driftFold (d : Nat) (hd : 2 ≤ d) (s : Shape)
    (hsd : s.length = d) :
    ground.famFold Nat.add 0
        (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
          * (blockSpan (places.shapeOf mu)).length * c2hat.dfQ (places.shapeOf mu))
        (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content))
      = (blockSpan s).length * (blockSpan (adjchar.theta d)).length
        * (c2hat.dfQ s + 2 * d * d) := by
  have hd1 : 1 < d := hd
  have hts : (adjchar.theta d).length = s.length := by
    rw [adjchar.length_theta d, hsd]
  have htd : (adjchar.theta d).length = d := adjchar.length_theta d
  obtain ⟨hszP, hwidP, hclP, hiP⟩ := fusedSpan_pack s (adjchar.theta d) hts
  have hwd : ∀ mu : List Nat, 0 < ground.countOf mu
      (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
            HVec.content)) → mu.length = d := by
    intro mu hmu
    rw [exhaust_width s.length
      (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))
      hszP hwidP hclP mu
      (ground.mem_of_dedupL (ground.mem_of_countOf_pos mu _ hmu))]
    exact hsd
  have hrl := exhaust_rowList_shapeOf s.length (fusedAt (blockSpan s)
    (blockSpan (adjchar.theta d))) hszP hwidP hclP
  have hdeg : ∀ mu : List Nat, 0 < ground.countOf mu
      (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
            HVec.content)) → places.degree (places.shapeOf mu) = places.degree s + d := by
    intro mu hmu
    show ground.sumNat (places.rowList (places.shapeOf mu)) = _
    rw [hrl mu (ground.mem_of_dedupL
        (ground.mem_of_countOf_pos mu _ hmu)),
      exhaust_degree s (adjchar.theta d) hts mu
        (ground.mem_of_dedupL
          (ground.mem_of_countOf_pos mu _ hmu)),
      adjchar.degree_theta d hd]
  have hdim := blockcount.fusionCount_dim s (adjchar.theta d) hts
  -- the channel recursion at the two factors' tensor splits
  have hA := foldRec d s (adjchar.theta d) hsd hts
  rw [momT11 s (adjchar.theta d) (by rw [hsd]; exact hd1) (by rw [htd]; exact hd1),
    momT2 s (adjchar.theta d) (by rw [hsd]; exact Nat.lt_trans Nat.zero_lt_one hd1)
      (by rw [htd]; exact Nat.lt_trans Nat.zero_lt_one hd1),
    momT1 s (adjchar.theta d) (by rw [hsd]; exact Nat.lt_trans Nat.zero_lt_one hd1)
      (by rw [htd]; exact Nat.lt_trans Nat.zero_lt_one hd1)] at hA
  have hC := assembleC
    (ground.famFold Nat.add 0
      (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
        * (weylchar.stdSq (places.display (places.shapeOf mu))
          * (blockSpan (places.shapeOf mu)).length))
      (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content)))
    (places.pairsOf d).length d (ground.sumNat (places.unitDisp d))
    (weylchar.stdSq (places.unitDisp d))
    (weylchar.stdSq (places.display s))
    (weylchar.stdSq (places.display (adjchar.theta d)))
    (blockSpan s).length (blockSpan (adjchar.theta d)).length
    (mom1 (blockSpan s)) (mom1 (blockSpan (adjchar.theta d)))
    (mom2At 0 (blockSpan s)) (mom2At 0 (blockSpan (adjchar.theta d)))
    (mom11 (blockSpan s)) (mom11 (blockSpan (adjchar.theta d)))
    hA (momRec d s hsd) (momRec d (adjchar.theta d) htd)
  -- the display conversion at each channel and at the two factors
  have hqs : d * weylchar.stdSq (places.display s)
      = c2hat.dfQ s + places.degree s * places.degree s
        + d * (d + 1) * places.degree s
        + d * weylchar.stdSq (places.unitDisp d) := by
    have h := qconv s
    rw [hsd] at h
    exact h
  have hqt : d * weylchar.stdSq (places.display (adjchar.theta d))
      = 2 * d * d + d * d + d * (d + 1) * d
        + d * weylchar.stdSq (places.unitDisp d) := by
    have h := qconv (adjchar.theta d)
    rw [htd, adjchar.degree_theta d hd, dfQ_theta d hd] at h
    exact h
  have hm1s : d * mom1 (blockSpan s) = places.degree s * (blockSpan s).length := by
    have h := mom1_deg s
    rw [hsd] at h
    exact h
  have hm1t : d * mom1 (blockSpan (adjchar.theta d)) = d * (blockSpan
    (adjchar.theta d)).length := by
    have h := mom1_deg (adjchar.theta d)
    rw [htd, adjchar.degree_theta d hd] at h
    exact h
  -- the fold's conversion at the channels' one raised degree
  have hdS : d * ground.famFold Nat.add 0
        (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
          * (weylchar.stdSq (places.display (places.shapeOf mu))
            * (blockSpan (places.shapeOf mu)).length))
        (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content))
      = ground.famFold Nat.add 0
          (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
            * (blockSpan (places.shapeOf mu)).length * c2hat.dfQ (places.shapeOf mu))
          (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content))
        + (((places.degree s + d) * (places.degree s + d)
      + d * (d + 1) * (places.degree s + d) + d * weylchar.stdSq
        (places.unitDisp d))) * ((blockSpan s).length * (blockSpan (adjchar.theta d)).length) := by
    rw [ground.famFold_mul d
        (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
          * (weylchar.stdSq (places.display (places.shapeOf mu))
            * (blockSpan (places.shapeOf mu)).length))
        (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content)),
      ground.famFold_congr_members Nat.add 0 _
        (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
            * (blockSpan (places.shapeOf mu)).length * c2hat.dfQ (places.shapeOf mu)
          + (((places.degree s + d) * (places.degree s + d)
      + d * (d + 1) * (places.degree s + d) + d * weylchar.stdSq (places.unitDisp d)))
            * (fusionCount s (adjchar.theta d) (places.shapeOf mu) *
              (blockSpan (places.shapeOf mu)).length))
        (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content))
        (fun mu hmu => by
          have hq : d * weylchar.stdSq (places.display (places.shapeOf mu))
              = c2hat.dfQ (places.shapeOf mu) + (((places.degree s + d) * (places.degree s + d)
      + d * (d + 1) * (places.degree s + d) + d * weylchar.stdSq (places.unitDisp d))) := by
            have h := qconv (places.shapeOf mu)
            rw [(places.length_shapeOf mu).trans (hwd mu hmu),
              hdeg mu hmu] at h
            rw [h, Nat.add_assoc (c2hat.dfQ (places.shapeOf mu))
                ((places.degree s + d) * (places.degree s + d))
                (d * (d + 1) * (places.degree s + d)),
              Nat.add_assoc (c2hat.dfQ (places.shapeOf mu))
                ((places.degree s + d) * (places.degree s + d)
                  + d * (d + 1) * (places.degree s + d)) (d * weylchar.stdSq (places.unitDisp d))]
          rw [pullMid d (fusionCount s (adjchar.theta d) (places.shapeOf mu))
              (weylchar.stdSq (places.display (places.shapeOf mu)))
              ((blockSpan (places.shapeOf mu)).length),
            hq,
            ground.mulAddR (c2hat.dfQ (places.shapeOf mu)) ((((places.degree s
              + d) * (places.degree s + d)
      + d * (d + 1) * (places.degree s + d) + d * weylchar.stdSq (places.unitDisp d))))
              ((blockSpan (places.shapeOf mu)).length),
            Nat.left_distrib (fusionCount s (adjchar.theta d) (places.shapeOf mu))
              (c2hat.dfQ (places.shapeOf mu) * (blockSpan (places.shapeOf mu)).length)
              ((((places.degree s + d) * (places.degree s + d)
      + d * (d + 1) * (places.degree s + d) + d * weylchar.stdSq
        (places.unitDisp d))) * (blockSpan (places.shapeOf mu)).length),
            swap3 (fusionCount s (adjchar.theta d) (places.shapeOf mu))
              (c2hat.dfQ (places.shapeOf mu))
              ((blockSpan (places.shapeOf mu)).length),
            ground.mulLeftComm (fusionCount s (adjchar.theta d)
              (places.shapeOf mu)) ((((places.degree s + d) * (places.degree s + d)
      + d * (d + 1) * (places.degree s + d) + d * weylchar.stdSq (places.unitDisp d))))
              ((blockSpan (places.shapeOf mu)).length)]),
      ground.famFold_add_split
        (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
          * (blockSpan (places.shapeOf mu)).length * c2hat.dfQ (places.shapeOf mu))
        (fun mu => (((places.degree s + d) * (places.degree s + d)
      + d * (d + 1) * (places.degree s + d) + d * weylchar.stdSq (places.unitDisp d)))
          * (fusionCount s (adjchar.theta d) (places.shapeOf mu) * (blockSpan
            (places.shapeOf mu)).length))
        (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content)),
      ← ground.famFold_mul ((((places.degree s + d) * (places.degree s + d)
      + d * (d + 1) * (places.degree s + d) + d * weylchar.stdSq (places.unitDisp d))))
        (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu) *
          (blockSpan (places.shapeOf mu)).length)
        (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content)),
      hdim]
  -- the converted display at the two factors and the cross term
  have hfin := congrArg (fun z => d * z) hC
  show ground.famFold Nat.add 0
      (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
        * (blockSpan (places.shapeOf mu)).length * c2hat.dfQ (places.shapeOf mu))
      (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content))
    = _
  refine assembleFinal
    (ground.famFold Nat.add 0
      (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
        * (blockSpan (places.shapeOf mu)).length * c2hat.dfQ (places.shapeOf mu))
      (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content)))
    (blockSpan s).length (blockSpan (adjchar.theta d)).length
    (places.degree s) d
    (weylchar.stdSq (places.unitDisp d)) (c2hat.dfQ s) ?_
  show _ = _
  rw [← hdS]
  rw [← Nat.left_distrib d
      (ground.famFold Nat.add 0
        (fun mu => fusionCount s (adjchar.theta d) (places.shapeOf mu)
          * (weylchar.stdSq (places.display (places.shapeOf mu))
            * (blockSpan (places.shapeOf mu)).length))
        (ground.dedupL ((exhaust s.length
          (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content)))
      (weylchar.stdSq (places.unitDisp d) * ((blockSpan s).length * (blockSpan
        (adjchar.theta d)).length)),
    hC, mulTri d
      (weylchar.stdSq (places.display s) * (blockSpan s).length
        * (blockSpan (adjchar.theta d)).length)
      (weylchar.stdSq (places.display (adjchar.theta d)) * (blockSpan (adjchar.theta d)).length
        * (blockSpan s).length)
      (2 * (d * (mom1 (blockSpan s) * mom1 (blockSpan (adjchar.theta d))))),
    ← ground.mulAssoc d
      (weylchar.stdSq (places.display s) * (blockSpan s).length)
      ((blockSpan (adjchar.theta d)).length),
    ← ground.mulAssoc d (weylchar.stdSq (places.display s))
      ((blockSpan s).length),
    ← ground.mulAssoc d
      (weylchar.stdSq (places.display (adjchar.theta d)) * (blockSpan (adjchar.theta d)).length)
      ((blockSpan s).length),
    ← ground.mulAssoc d (weylchar.stdSq (places.display (adjchar.theta d)))
      ((blockSpan (adjchar.theta d)).length),
    hqs, hqt,
    ground.mulLeftComm d 2 (d * (mom1 (blockSpan s) * mom1 (blockSpan (adjchar.theta d)))),
    sqPair d (mom1 (blockSpan s)) (mom1 (blockSpan (adjchar.theta d))),
    hm1s, hm1t]

/-! The row read: the adjoint row's fold at the label calculus's
own data — the guarded enumeration's survivors, the label count at
the reduced target, and the enumeration's bridge to the channels'
index. -/

/-- The dimension is one value at the class: the withdrawn full
column moves the display together. -/
private theorem dimOf_reduce (c : Shape) (hc : 0 < c.length) :
    weyldim.dimOf (labels.reduce c) = weyldim.dimOf c := by
  cases c with
  | nil => exact absurd hc (Nat.lt_irrefl 0)
  | cons x t =>
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', j, hs, _⟩ =>
      rw [hs, labels.reduce_snoc s' j, weyldim.dimOf_snoc s' j]

/-- `thm:drift`'s display at the label calculus: the
dimension-weighted adjoint row's Casimir fold reads
`d_R d_θ (d_f Q(R) + 2 d_f²)` at every shape of the width.  The
row's guarded enumeration reads each survivor at its own reduced
label — the count at the matched-degree lift
(`labels.countL_reduce`) with the dimension and the cleared
Casimir one value at the class (`weyldim.dimOf_snoc`,
`labels.c2Class_all`) — the fast count is the block count
(`cor:steinberg`), and the enumeration bridges to the channels'
index, each channel listed once at its own degree and every
off-channel shape's count vacant.  The fold then closes at
`driftFold`: the summed recursion (`sumRec`) at each channel
against the two factors', the fused family split over the channels
(`blockcount.gradedDim_countAt`) and over the factors, the moments
at the degree folds, and the square identity closing at the shared
channel degree with the dimension display
(`blockcount.fusionCount_dim`) and `d_f Q(θ) = 2 d_f²`. -/
theorem readAll (d : Nat) (hd : 2 ≤ d) (s : Shape)
    (hs : s.length = d) : fusion.driftLaw (fusion.dataA d) s := by
  have hd0 : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_two hd
  have hts : (adjchar.theta d).length = s.length := by
    rw [adjchar.length_theta d, hs]
  have htd : (adjchar.theta d).length = d := adjchar.length_theta d
  obtain ⟨hszP, hwidP, hclP, hiP⟩ := fusedSpan_pack s (adjchar.theta d) hts
  have hrl := exhaust_rowList_shapeOf s.length (fusedAt (blockSpan s)
    (blockSpan (adjchar.theta d))) hszP hwidP hclP
  have hwd : ∀ mu : List Nat, 0 < ground.countOf mu
      (ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)) → mu.length = d := by
    intro mu hmu
    rw [exhaust_width s.length
      (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))
      hszP hwidP hclP mu
      (ground.mem_of_dedupL (ground.mem_of_countOf_pos mu _ hmu))]
    exact hs
  have hdeg : ∀ mu : List Nat, 0 < ground.countOf mu
      (ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)) → places.degree (places.shapeOf mu) = (places.degree
          s + places.degree (adjchar.theta d)) := by
    intro mu hmu
    show ground.sumNat (places.rowList (places.shapeOf mu)) = _
    rw [hrl mu (ground.mem_of_dedupL
        (ground.mem_of_countOf_pos mu _ hmu)),
      exhaust_degree s (adjchar.theta d) hts mu
        (ground.mem_of_dedupL
          (ground.mem_of_countOf_pos mu _ hmu))]
  -- the image of the channels' index sits once in the enumeration
  have hES1 : ∀ c : Shape, 0 < ground.countOf c ((ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)).map places.shapeOf) →
      ground.countOf c ((ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)).map places.shapeOf) = 1 := by
    intro c hc
    obtain ⟨mu, hmu, hmuc⟩ := ground.mem_map_of places.shapeOf
      (ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)) c (ground.mem_of_countOf_pos c _ hc)
    rw [← hmuc,
      ground.countOf_map_inj places.shapeOf mu (ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content))
        (fun y hy hyc => by
          rw [← hrl y (ground.mem_of_dedupL
              (ground.mem_of_countOf_pos y _ hy)),
            ← hrl mu (ground.mem_of_dedupL
              (ground.mem_of_countOf_pos mu _
                (ground.countOf_pos_of_mem hmu))),
            hyc])]
    exact Nat.le_antisymm (ground.countOf_dedupL_le mu _)
      (ground.countOf_pos_of_mem hmu)
  have hEScov : ∀ c : Shape, 0 < ground.countOf c ((ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)).map places.shapeOf) →
      ground.countOf c (places.allShapes d (places.degree s + places.degree
        (adjchar.theta d))) = 1 := by
    intro c hc
    obtain ⟨mu, hmu, hmuc⟩ := ground.mem_map_of places.shapeOf
      (ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)) c (ground.mem_of_countOf_pos c _ hc)
    have hmuP : 0 < ground.countOf mu (ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content)) :=
      ground.countOf_pos_of_mem hmu
    have hlen : c.length = d := by
      rw [← hmuc, places.length_shapeOf mu]
      exact hwd mu hmuP
    have hdc : places.degree c = (places.degree s + places.degree (adjchar.theta d)) := by
      rw [← hmuc]
      exact hdeg mu hmuP
    refine Nat.le_antisymm (places.countOf_allShapes_le d (places.degree s +
      places.degree (adjchar.theta d)) c) ?_
    refine ground.countOf_pos_of_mem ?_
    rw [← hdc]
    exact places.mem_allShapes d c hlen
  -- an off-image shape of the enumeration carries no fusion
  have hoff : ∀ c : Shape,
      0 < ground.countOf c (places.allShapes d (places.degree s +
        places.degree (adjchar.theta d))) →
      ground.countOf c ((ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)).map places.shapeOf) = 0 →
      blockcount.fusionCount s (adjchar.theta d) c = 0 := by
    intro c hc hz
    have hcs : c.length = s.length := by
      rw [(places.allShapes_sound d (places.degree s + places.degree (adjchar.theta d)) c
        (ground.mem_of_countOf_pos c _ hc)).1, hs]
    rw [blockcount.fusionCount_countOf s (adjchar.theta d) c hts]
    match Nat.eq_zero_or_pos (ground.countOf (places.rowList c)
      ((exhaust s.length (fusedAt (blockSpan s) (blockSpan (adjchar.theta
        d)))).map HVec.content)) with
    | .inl h0 => exact h0
    | .inr hp =>
      exfalso
      have hmem : c ∈ ((ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)).map places.shapeOf) := by
        rw [← places.shapeOf_rowList c]
        exact ground.mem_map_to places.shapeOf
          (ground.mem_dedupL (ground.mem_of_countOf_pos _ _ hp))
      have := ground.countOf_pos_of_mem hmem
      rw [hz] at this
      exact absurd this (Nat.lt_irrefl 0)
  -- the row's guarded values at the reduced labels
  have hterm : ∀ c : Shape,
      0 < ground.countOf c (places.allShapes d (places.degree s +
        places.degree (adjchar.theta d))) →
      ground.optVal
        (fun c' => labels.countL s (adjchar.theta d) c' * weyldim.dimOf c'
          * c2hat.dfQ c')
        (if 0 < steinberg.count s (adjchar.theta d) c
          then some (labels.reduce c) else none)
      = blockcount.fusionCount s (adjchar.theta d) c * weyldim.dimOf c
        * c2hat.dfQ c := by
    intro c hc
    obtain ⟨hcl, hck⟩ := places.allShapes_sound d (places.degree s +
      places.degree (adjchar.theta d)) c
      (ground.mem_of_countOf_pos c _ hc)
    have hcs : c.length = s.length := by rw [hcl, hs]
    have hcpos : 0 < c.length := by rw [hcl]; exact hd0
    by_cases hg : 0 < steinberg.count s (adjchar.theta d) c
    · rw [if_pos hg]
      show labels.countL s (adjchar.theta d) (labels.reduce c)
          * weyldim.dimOf (labels.reduce c)
          * c2hat.dfQ (labels.reduce c) = _
      rw [labels.countL_reduce s (adjchar.theta d) c hcs hck,
        dimOf_reduce c hcpos, ← labels.c2Class_all c,
        steinberg.count_fusion s (adjchar.theta d) c hts hcs]
    · rw [if_neg hg]
      show (0 : Nat) = _
      match Nat.eq_zero_or_pos (steinberg.count s (adjchar.theta d) c) with
      | .inl h0 =>
        rw [← steinberg.count_fusion s (adjchar.theta d) c hts hcs, h0,
          Nat.zero_mul, Nat.zero_mul]
      | .inr hp => exact absurd hp hg
  -- the enumeration bridges to the channels' index
  have hbridge : ground.famFold Nat.add 0
      (fun c => blockcount.fusionCount s (adjchar.theta d) c * weyldim.dimOf c
        * c2hat.dfQ c) (places.allShapes d (places.degree s + places.degree (adjchar.theta d)))
    = ground.famFold Nat.add 0
      (fun mu => blockcount.fusionCount s (adjchar.theta d) (places.shapeOf mu)
        * (blockSpan (places.shapeOf mu)).length
        * c2hat.dfQ (places.shapeOf mu)) (ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content)) := by
    rw [ground.famFold_congr_members Nat.add 0
        (fun c => blockcount.fusionCount s (adjchar.theta d) c * weyldim.dimOf c
        * c2hat.dfQ c)
        (fun c => ground.countOf c ((ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)).map places.shapeOf)
          * (blockcount.fusionCount s (adjchar.theta d) c
            * weyldim.dimOf c * c2hat.dfQ c))
        (places.allShapes d (places.degree s + places.degree (adjchar.theta d)))
        (fun c hc => by
          match Nat.eq_zero_or_pos (ground.countOf c ((ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)).map places.shapeOf)) with
          | .inl h0 =>
            rw [h0, Nat.zero_mul, hoff c hc h0, Nat.zero_mul,
              Nat.zero_mul]
          | .inr hp => rw [hES1 c hp, Nat.one_mul]),
      ← ground.famFold_countCollect
        (fun c => blockcount.fusionCount s (adjchar.theta d) c * weyldim.dimOf c
        * c2hat.dfQ c)
        ((ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map
          HVec.content)).map places.shapeOf) (places.allShapes d
          (places.degree s + places.degree (adjchar.theta d))) hEScov,
      ground.famFold_map Nat.add 0
        (fun c => blockcount.fusionCount s (adjchar.theta d) c * weyldim.dimOf c
        * c2hat.dfQ c)
        places.shapeOf (ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content))]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun mu => by rw [weyldim.dimOf_spanLen (places.shapeOf mu)])
      (ground.dedupL ((exhaust s.length
        (fusedAt (blockSpan s) (blockSpan (adjchar.theta d)))).map HVec.content))
  show ((places.allShapes d (places.degree s + places.degree (adjchar.theta d))).filterMap
      (fun c => if 0 < steinberg.count s (adjchar.theta d) c
        then some (labels.reduce c) else none)).foldl
      (fun acc c => acc + labels.countL s (adjchar.theta d) c * weyldim.dimOf c
        * c2hat.dfQ c) 0
    = weyldim.dimOf s * weyldim.dimOf (adjchar.theta d)
      * (c2hat.dfQ s + 2 * d * d)
  rw [ground.foldlSum
      (fun c => labels.countL s (adjchar.theta d) c * weyldim.dimOf c
        * c2hat.dfQ c) _ 0,
    Nat.zero_add,
    ground.famFold_filterMap
      (fun c => if 0 < steinberg.count s (adjchar.theta d) c
        then some (labels.reduce c) else none)
      (fun c => labels.countL s (adjchar.theta d) c * weyldim.dimOf c
        * c2hat.dfQ c)
      (places.allShapes d (places.degree s + places.degree (adjchar.theta d))),
    ground.famFold_congr_members Nat.add 0 _
      (fun c => blockcount.fusionCount s (adjchar.theta d) c * weyldim.dimOf c
        * c2hat.dfQ c) (places.allShapes d (places.degree s + places.degree
          (adjchar.theta d))) hterm,
    hbridge, driftFold d hd s hs,
    weyldim.dimOf_spanLen s, weyldim.dimOf_spanLen (adjchar.theta d)]

/-! The strictness read (`cor:weyldim`'s factor comparison): a
nonunit reduced shape's display gaps dominate the unit display's
factor by factor, and the shape's own strict row drop doubles one
factor, so the dimension clears two. -/

/-- A gap below a sum's second summand at a stated join. -/
private theorem leSubOf {a b c : Nat} (h : b + c ≤ a) : c ≤ a - b := by
  match Nat.le.dest h with
  | ⟨e, he⟩ =>
    rw [← he, Nat.add_assoc b c e, ground.addSubSelfL b (c + e)]
    exact Nat.le_add_right c e

/-- A weakly descending family with an occupied head and a vacant
last entry drops strictly at some adjacent key pair. -/
private theorem descDrop : ∀ (l : List Nat) (r : Nat),
    l.length = r + 1 →
    (∀ k, k + 1 < l.length →
      ground.getAt 0 l (k + 1) ≤ ground.getAt 0 l k) →
    0 < ground.getAt 0 l 0 → ground.getAt 0 l r = 0 →
    ∃ p, p + 1 < l.length
      ∧ ground.getAt 0 l (p + 1) < ground.getAt 0 l p
  | [], _, h, _, _, _ => Nat.noConfusion h
  | a :: t, 0, _, _, hp, hz => by
    have ha : a = 0 := hz
    rw [ha] at hp
    exact absurd hp (Nat.lt_irrefl 0)
  | a :: t, r + 1, h, hd, hp, hz => by
    cases t with
    | nil => exact Nat.noConfusion (Nat.succ.inj h)
    | cons b t' =>
      by_cases hba : b < a
      · exact ⟨0, Nat.succ_lt_succ (Nat.succ_pos t'.length), hba⟩
      · have hab : a ≤ b := Nat.le_of_not_lt hba
        have hba' : b ≤ a := hd 0 (Nat.succ_lt_succ (Nat.succ_pos _))
        have hbpos : 0 < ground.getAt 0 (b :: t') 0 := by
          show 0 < b
          exact Nat.lt_of_lt_of_le hp hab
        obtain ⟨p, hp1, hp2⟩ := descDrop (b :: t') r
          (Nat.succ.inj h)
          (fun k hk => hd (k + 1) (Nat.succ_lt_succ hk))
          hbpos hz
        exact ⟨p + 1, Nat.succ_lt_succ hp1, hp2⟩

/-- A head gap fold dominates factor by factor. -/
private theorem gapHead_le (x u : Nat) : ∀ (X U : List Nat),
    X.length = U.length →
    (∀ j, j < U.length →
      u - ground.getAt 0 U j ≤ x - ground.getAt 0 X j) →
    weyldim.gapHead u U ≤ weyldim.gapHead x X
  | [], [], _, _ => Nat.le_refl 1
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | a :: X, b :: U, h, hle => by
    show (u - b) * weyldim.gapHead u U
      ≤ (x - a) * weyldim.gapHead x X
    exact Nat.mul_le_mul (hle 0 (Nat.succ_pos U.length))
      (gapHead_le x u X U (Nat.succ.inj h)
        (fun j hj => hle (j + 1) (Nat.succ_lt_succ hj)))

/-- A head gap fold doubles at a doubled first factor. -/
private theorem gapHead_double (x u : Nat) (X U : List Nat)
    (h : X.length = U.length) (hU : 0 < U.length)
    (hle : ∀ j, j < U.length →
      u - ground.getAt 0 U j ≤ x - ground.getAt 0 X j)
    (h2 : 2 * (u - ground.getAt 0 U 0)
      ≤ x - ground.getAt 0 X 0) :
    2 * weyldim.gapHead u U ≤ weyldim.gapHead x X := by
  cases U with
  | nil => exact absurd hU (Nat.lt_irrefl 0)
  | cons b U' =>
    cases X with
    | nil => exact Nat.noConfusion h
    | cons a X' =>
      show 2 * ((u - b) * weyldim.gapHead u U')
        ≤ (x - a) * weyldim.gapHead x X'
      rw [← ground.mulAssoc 2 (u - b) (weyldim.gapHead u U')]
      exact Nat.mul_le_mul h2
        (gapHead_le x u X' U' (Nat.succ.inj h)
          (fun j hj => hle (j + 1) (Nat.succ_lt_succ hj)))

/-- A gap product dominates at pairwise dominating gaps. -/
private theorem gapProd_le : ∀ (X U : List Nat),
    X.length = U.length →
    (∀ i j, i < j → j < U.length →
      ground.getAt 0 U i - ground.getAt 0 U j
        ≤ ground.getAt 0 X i - ground.getAt 0 X j) →
    weyldim.gapProd U ≤ weyldim.gapProd X
  | [], [], _, _ => Nat.le_refl 1
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | a :: X, b :: U, h, hle => by
    show weyldim.gapHead b U * weyldim.gapProd U
      ≤ weyldim.gapHead a X * weyldim.gapProd X
    exact Nat.mul_le_mul
      (gapHead_le a b X U (Nat.succ.inj h)
        (fun j hj => hle 0 (j + 1) (Nat.succ_pos j)
          (Nat.succ_lt_succ hj)))
      (gapProd_le X U (Nat.succ.inj h)
        (fun i j hij hj => hle (i + 1) (j + 1)
          (Nat.succ_lt_succ hij) (Nat.succ_lt_succ hj)))

/-- A gap product doubles at one doubled adjacent gap. -/
private theorem gapProd_double : ∀ (X U : List Nat) (p : Nat),
    X.length = U.length →
    (∀ i j, i < j → j < U.length →
      ground.getAt 0 U i - ground.getAt 0 U j
        ≤ ground.getAt 0 X i - ground.getAt 0 X j) →
    p + 1 < U.length →
    2 * (ground.getAt 0 U p - ground.getAt 0 U (p + 1))
      ≤ ground.getAt 0 X p - ground.getAt 0 X (p + 1) →
    2 * weyldim.gapProd U ≤ weyldim.gapProd X
  | _, [], p, _, _, hp, _ => absurd hp (Nat.not_lt_zero _)
  | [], _ :: _, _, h, _, _, _ => Nat.noConfusion h
  | a :: X, b :: U, 0, h, hle, hp, h2 => by
    show 2 * (weyldim.gapHead b U * weyldim.gapProd U)
      ≤ weyldim.gapHead a X * weyldim.gapProd X
    rw [← ground.mulAssoc 2 (weyldim.gapHead b U)
      (weyldim.gapProd U)]
    refine Nat.mul_le_mul ?_
      (gapProd_le X U (Nat.succ.inj h)
        (fun i j hij hj => hle (i + 1) (j + 1)
          (Nat.succ_lt_succ hij) (Nat.succ_lt_succ hj)))
    exact gapHead_double a b X U (Nat.succ.inj h)
      (Nat.lt_of_succ_lt_succ hp)
      (fun j hj => hle 0 (j + 1) (Nat.succ_pos j)
        (Nat.succ_lt_succ hj)) h2
  | a :: X, b :: U, q + 1, h, hle, hp, h2 => by
    show 2 * (weyldim.gapHead b U * weyldim.gapProd U)
      ≤ weyldim.gapHead a X * weyldim.gapProd X
    rw [ground.mulLeftComm 2 (weyldim.gapHead b U) (weyldim.gapProd U)]
    exact Nat.mul_le_mul
      (gapHead_le a b X U (Nat.succ.inj h)
        (fun j hj => hle 0 (j + 1) (Nat.succ_pos j)
          (Nat.succ_lt_succ hj)))
      (gapProd_double X U q (Nat.succ.inj h)
        (fun i j hij hj => hle (i + 1) (j + 1)
          (Nat.succ_lt_succ hij) (Nat.succ_lt_succ hj))
        (Nat.lt_of_succ_lt_succ hp) h2)

/-- A joined pair's gap dominates the second summands' own at
weakly descending summands. -/
private theorem gapDom {la lb ua ub : Nat} (hl : lb ≤ la)
    (hu : ub ≤ ua) : ua - ub ≤ (la + ua) - (lb + ub) := by
  refine leSubOf ?_
  rw [Nat.add_assoc lb ub (ua - ub), Nat.add_comm ub (ua - ub),
    ground.subAdd hu]
  exact Nat.add_le_add hl (Nat.le_refl ua)

/-- A joined pair's gap clears two at two strict summand drops. -/
private theorem gapTwo {la lb ua ub : Nat} (hl : lb + 1 ≤ la)
    (hu : ub + 1 ≤ ua) : 2 ≤ (la + ua) - (lb + ub) := by
  refine leSubOf ?_
  show lb + ub + (1 + 1) ≤ la + ua
  rw [Nat.add_add_add_comm lb ub 1 1]
  exact Nat.add_le_add hl hu

/-- The raised key's join at a stated gap. -/
private theorem shiftAddL (p e : Nat) : p + 1 + 1 + e = p + (e + 2) := by
  rw [Nat.add_right_comm (p + 1) 1 e, Nat.add_right_comm p 1 e]
  exact Nat.add_assoc p e 2

/-- The raised key's join at the shortened gap. -/
private theorem shiftAddR (p e : Nat) :
    p + 1 + 1 + e = p + 1 + (e + 1) := by
  rw [Nat.add_right_comm (p + 1) 1 e]
  exact Nat.add_assoc (p + 1) e 1

/-- `thm:drift`'s strictness clause: a nonunit reduced shape's
dimension clears two, `cor:weyldim`'s display at the consecutive
gap factor against the unit display's.  The rows descend weakly
from an occupied head to the withdrawn full column's vacant last
row, so some adjacent pair drops strictly; every display gap
dominates the unit display's at the rows' own monotonicity, and
the dropping pair's factor doubles it. -/
theorem strict (s : Shape) (hred : labels.reduce s = s)
    (hpos : 0 < places.degree s) : 2 ≤ weyldim.dimOf s := by
  have hsl : 0 < s.length := by
    match s, hpos with
    | [], h => exact absurd h (Nat.lt_irrefl 0)
    | _ :: t, _ => exact Nat.succ_pos t.length
  obtain ⟨r, hr⟩ : ∃ r, s.length = r + 1 :=
    ⟨s.length - 1, (ground.subAdd hsl).symm⟩
  have hdescL : ∀ k, k + 1 < (places.rowList s).length →
      ground.getAt 0 (places.rowList s) (k + 1)
        ≤ ground.getAt 0 (places.rowList s) k := by
    intro k hk
    rw [places.length_rowList s] at hk
    exact places.rowList_le s k hk
  have hdescU : ∀ k, k + 1 < (places.unitDisp s.length).length →
      ground.getAt 0 (places.unitDisp s.length) (k + 1)
        ≤ ground.getAt 0 (places.unitDisp s.length) k := by
    intro k hk
    rw [places.length_unitDisp s.length] at hk
    exact Nat.le_of_lt (weylchar.unitDisp_strict s.length k hk)
  -- the last row is the withdrawn full column's vacancy
  have hlast : ground.getAt 0 (places.rowList s) r = 0 := by
    obtain ⟨s', j, hsj, hs'len⟩ := ground.snoc_split r s hr
    have hre : s' ++ [0] = s := by
      rw [← hred, hsj, labels.reduce_snoc s' j]
    rw [places.rowList_last s r hr, ← hre,
      ground.getAt_append 0 s' [0] r,
      if_neg (by rw [hs'len]; exact Nat.lt_irrefl r), hs'len,
      Nat.sub_self r]
    rfl
  -- the head row is occupied
  have hhead : 0 < ground.getAt 0 (places.rowList s) 0 := by
    have hsum : 0 < ground.famFold Nat.add 0
        (fun k => ground.getAt 0 (places.rowList s) k)
        (List.range (places.rowList s).length) := by
      rw [ground.sumIndex (places.rowList s)]
      exact hpos
    obtain ⟨k, hk, hkp⟩ := ground.famFold_pos_mem
      (fun k => ground.getAt 0 (places.rowList s) k)
      (List.range (places.rowList s).length) hsum
    exact Nat.lt_of_lt_of_le hkp
      (ground.descLe (places.rowList s) 0 k hdescL (Nat.zero_le k)
        (ground.ltOfMemRange hk))
  obtain ⟨p, hp1, hp2⟩ := descDrop (places.rowList s) r
    ((places.length_rowList s).trans hr) hdescL hhead hlast
  rw [places.length_rowList s] at hp1
  have hpd : p < s.length := Nat.lt_of_succ_lt hp1
  -- the unit display's adjacent gap is one
  obtain ⟨e, he⟩ := Nat.le.dest hp1
  have hUp : s.length - p = e + 2 := by
    rw [show s.length = p + (e + 2) from by
      rw [← he]; exact shiftAddL p e, ground.addSubSelfL p (e + 2)]
  have hUp1 : s.length - (p + 1) = e + 1 := by
    rw [show s.length = p + 1 + (e + 1) from by
      rw [← he]; exact shiftAddR p e,
      ground.addSubSelfL (p + 1) (e + 1)]
  -- the display gaps dominate the unit display's
  have hdom : ∀ i j, i < j → j < (places.unitDisp s.length).length →
      ground.getAt 0 (places.unitDisp s.length) i
          - ground.getAt 0 (places.unitDisp s.length) j
        ≤ ground.getAt 0 (places.display s) i
          - ground.getAt 0 (places.display s) j := by
    intro i j hij hj
    have hj' : j < s.length := by
      rw [places.length_unitDisp s.length] at hj
      exact hj
    have hi : i < s.length := Nat.lt_trans hij hj'
    have hu : s.length - j ≤ s.length - i := by
      have h := ground.descLe (places.unitDisp s.length) i j hdescU
        (Nat.le_of_lt hij)
        (by rw [places.length_unitDisp s.length]; exact hj')
      rw [weylchar.getAt_unitDisp s.length i hi,
        weylchar.getAt_unitDisp s.length j hj'] at h
      exact h
    rw [places.getAt_display s i hi, places.getAt_display s j hj',
      weylchar.getAt_unitDisp s.length i hi,
      weylchar.getAt_unitDisp s.length j hj']
    exact gapDom
      (ground.descLe (places.rowList s) i j hdescL (Nat.le_of_lt hij)
        (by rw [places.length_rowList s]; exact hj'))
      hu
  -- the dropping pair's factor doubles
  have hdbl : 2 * (ground.getAt 0 (places.unitDisp s.length) p
        - ground.getAt 0 (places.unitDisp s.length) (p + 1))
      ≤ ground.getAt 0 (places.display s) p
        - ground.getAt 0 (places.display s) (p + 1) := by
    have hgap : ground.getAt 0 (places.unitDisp s.length) p
        - ground.getAt 0 (places.unitDisp s.length) (p + 1) = 1 := by
      rw [weylchar.getAt_unitDisp s.length p hpd,
        weylchar.getAt_unitDisp s.length (p + 1) hp1, hUp, hUp1]
      exact ground.addSubSelfL (e + 1) 1
    have hu2 : s.length - (p + 1) + 1 ≤ s.length - p := by
      rw [hUp, hUp1]
      exact Nat.le_refl (e + 2)
    rw [hgap, Nat.mul_one,
      places.getAt_display s p hpd,
      places.getAt_display s (p + 1) hp1]
    exact gapTwo hp2 hu2
  have hmain : 2 * weyldim.gapProd (places.unitDisp s.length)
      ≤ weyldim.gapProd (places.display s) :=
    gapProd_double (places.display s) (places.unitDisp s.length) p
      (by rw [places.length_display s, places.length_unitDisp s.length])
      hdom (by rw [places.length_unitDisp s.length]; exact hp1) hdbl
  have hU : weyldim.dimOf s
      * weyldim.gapProd (places.display (List.replicate s.length 0))
    = weyldim.gapProd (places.display s) := weyldim.readAll s
  refine Nat.le_of_mul_le_mul_right ?_ (weyldim.gapProdU_pos s)
  rw [hU]
  exact hmain

end drift
