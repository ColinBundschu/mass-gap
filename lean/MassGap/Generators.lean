import MassGap.Stagesplit
import MassGap.Certconstruct
/-!
`def:generators` — the displayed generator list at the formal-`i`
carrier, the remainder lists at `z² + 1` (`stagesplit.iList` with
`poly.remMul`): the swap, `i`-sum and diagonal combinations with
the count join `2·binom(d_f, 2) + r + 1 = d_f²` (`genList`,
`genList_length`); each member anti-Hermitian by its shape — the
`re` component antisymmetric at the memberwise swap, the `im`
symmetric (`antiH`, `antiHAll_holds`, the place-pair frame the
enumeration's own); the Hermitian companions at `X = i T`
entrywise (`tOf`, `tList`, `iT_entry`, `iTRead`); the trace-pairing
Gram with its realness read (`traceMul`, `gramReal`, `gramR`) and
the metric-dual data at the Gram's adjugate against its
determinant with the adjugate identity's coherence and the
independence read at the determinant off the sum's unit (`detG`,
`adjG`, `gramSolve`, `gramIndep`); and the Fierz read cleared of
the form point — the ξ-orthonormal display's rescaling withdraws
at the metric dual (`prop:form`'s one-value read), leaving
`d·δ_ps·δ_rq·det G = δ_pq·δ_rs·det G + d·S` at the
adjugate-weighted sum `S` (`dl`, `fierzS`, `fierzRead`).  The
statement's further sentences execute at their sites: the display
`Δ = Σ X†X` at the cleared traceless bracket (`def:c2hat`'s join
with `prop:lap`'s insertion identity the action's own read); the
trace pairing `tr(X_aX_b) + ξδ_ab` at the sum's unit is the
orthonormal spelling's, executed at the cleared Fierz read; and
the companions' `ξ` read is the Gram exchange, the companion
pairing the displayed pairing's memberwise swap, the check
module's decided read.  The two general theorems
(`genList_length`, `antiHAll_holds`) and `iT_entry` hold at every
width; the decided Props read at the check module's pinned
widths.
-/

namespace generators
open ground

/-- The formal `i`, the linear monomial's class at `z² + 1`. -/
def entryI : poly.Poly := [BPair.unit, BPair.ofNat 1]

/-- The formal `i`'s balance partner. -/
def entryInegP : poly.Poly := [BPair.unit, (BPair.ofNat 1).swap]

/-- The scalar one entry. -/
def entryOne : poly.Poly := [BPair.ofNat 1]

/-- The scalar one's balance partner. -/
def entryNegOne : poly.Poly := [(BPair.ofNat 1).swap]

/-- The swap combination at a place pair: one at `(p, q)` with its
balance partner at `(q, p)`. -/
def swapX (d p q : Nat) : List (List poly.Poly) :=
  ground.matOf d d (fun i j =>
    if i == p && j == q then entryOne
    else if i == q && j == p then entryNegOne else [])

/-- The `i`-weighted sum at a place pair: `i` at both places. -/
def isumX (d p q : Nat) : List (List poly.Poly) :=
  ground.matOf d d (fun i j =>
    if (i == p && j == q) || (i == q && j == p) then entryI else [])

/-- The diagonal combination at a consecutive place pair: `i` at
the place's diagonal with `i`'s balance partner at the
successor's. -/
def diagX (d p : Nat) : List (List poly.Poly) :=
  ground.matOf d d (fun i j =>
    if i == p && j == p then entryI
    else if (i == p + 1) && (j == p + 1) then entryInegP else [])

/-- The displayed generator list: the swap and `i`-sum combinations
over the place pairs `p < q` with the diagonal combinations over
the consecutive places. -/
def genList (d : Nat) : List (List (List poly.Poly)) :=
  ((List.range d).flatMap (fun q =>
    (List.range q).map (fun p => swapX d p q)))
  ++ ((List.range d).flatMap (fun q =>
    (List.range q).map (fun p => isumX d p q)))
  ++ (List.range (d - 1)).map (fun p => diagX d p)

/-- The place-pair enumeration's triangle count. -/
private def tri : Nat → Nat
  | 0 => 0
  | dd + 1 => tri dd + dd

/-- The flattened place-pair family's count is the triangle's. -/
private theorem triFlatLen (g : Nat → Nat → List (List poly.Poly)) :
    ∀ dd : Nat,
      ((List.range dd).flatMap (fun q =>
        (List.range q).map (fun p => g p q))).length = tri dd
  | 0 => rfl
  | dd + 1 => by
    rw [range_succ dd,
      flatMap_append (fun q => (List.range q).map (fun p => g p q))
        (List.range dd) [dd],
      ground.length_append, triFlatLen g dd]
    show tri dd + ((List.range dd).map (fun p => g p dd) ++ []).length
      = tri dd + dd
    rw [ground.length_append, ground.length_mapRange]
    rfl

/-- Twice the triangle with the width reads the width's square. -/
private theorem triSquare : ∀ dd : Nat, 2 * tri dd + dd = dd * dd
  | 0 => rfl
  | dd + 1 => by
    show 2 * (tri dd + dd) + (dd + 1) = (dd + 1) * (dd + 1)
    rw [Nat.mul_add 2 (tri dd) dd, Nat.succ_mul dd (dd + 1),
      Nat.mul_succ dd dd, Nat.two_mul dd,
      Nat.add_assoc (2 * tri dd) (dd + dd) (dd + 1),
      Nat.add_assoc dd dd (dd + 1),
      ← Nat.add_assoc (2 * tri dd) dd (dd + (dd + 1)),
      triSquare dd,
      ← Nat.add_assoc (dd * dd) dd (dd + 1),
      ← Nat.add_assoc (dd * dd + dd) dd 1]

/-- The count join, `2·binom(d_f, 2) + r + 1 = d_f²`: the displayed
list's count with one is the fundamental count's square.  The bound
`hd` is LOAD-BEARING: at the vacant width the list is vacant and the
join refuses — the check module's pinned refusal. -/
theorem genList_length (d : Nat) (hd : 1 ≤ d) :
    (genList d).length + 1 = d * d := by
  match Nat.le.dest hd with
  | ⟨e, he⟩ =>
    have hde : d = e + 1 := by rw [← he, Nat.add_comm]
    subst hde
    unfold genList
    rw [ground.length_append, ground.length_append,
      ground.length_mapRange,
      triFlatLen (fun p q => swapX (e + 1) p q) (e + 1),
      triFlatLen (fun p q => isumX (e + 1) p q) (e + 1)]
    show tri (e + 1) + tri (e + 1) + e + 1 = (e + 1) * (e + 1)
    rw [Nat.add_assoc (tri (e + 1) + tri (e + 1)) e 1,
      ← Nat.two_mul (tri (e + 1))]
    exact triSquare (e + 1)

/-- The anti-Hermitian read at a width: entry against transposed
entry, the `re` component antisymmetric at the memberwise swap and
the `im` symmetric — "each anti-Hermitian by its shape". -/
def antiH (d : Nat) (X : List (List poly.Poly)) : Prop :=
  ((List.range d).all (fun i => (List.range d).all (fun j =>
    let e := ground.getAt [] (ground.getAt [] X i) j
    let f := ground.getAt [] (ground.getAt [] X j) i
    decide (BPair.oneValue (ground.getAt BPair.unit f 0)
        ((ground.getAt BPair.unit e 0).swap))
      && decide (BPair.oneValue (ground.getAt BPair.unit f 1)
        (ground.getAt BPair.unit e 1))))) = true

instance (d : Nat) (X : List (List poly.Poly)) :
    Decidable (antiH d X) :=
  inferInstanceAs (Decidable (_ = _))

/-- The anti-Hermitian read at an entry family, the pointwise pair
reads folded over the range. -/
private theorem antiH_matOf (d : Nat) (f : Nat → Nat → poly.Poly)
    (h : ∀ i j : Nat, i < d → j < d →
      (decide (BPair.oneValue (ground.getAt BPair.unit (f j i) 0)
          ((ground.getAt BPair.unit (f i j) 0).swap))
        && decide (BPair.oneValue (ground.getAt BPair.unit (f j i) 1)
          (ground.getAt BPair.unit (f i j) 1))) = true) :
    antiH d (ground.matOf d d f) := by
  show ((List.range d).all _) = true
  refine all_range_intro d (fun i hi => ?_)
  refine all_range_intro d (fun j hj => ?_)
  show (decide (BPair.oneValue
      (ground.getAt BPair.unit
        (ground.getAt [] (ground.getAt [] (ground.matOf d d f) j) i) 0)
      ((ground.getAt BPair.unit
        (ground.getAt [] (ground.getAt [] (ground.matOf d d f) i) j) 0).swap))
    && decide (BPair.oneValue
      (ground.getAt BPair.unit
        (ground.getAt [] (ground.getAt [] (ground.matOf d d f) j) i) 1)
      (ground.getAt BPair.unit
        (ground.getAt [] (ground.getAt [] (ground.matOf d d f) i) j) 1))) = true
  rw [ground.matOf_entry _ _ d d f i j hi hj,
    ground.matOf_entry _ _ d d f j i hj hi]
  exact h i j hi hj

/-- The swap combination is anti-Hermitian at distinct places, the
displayed family's own index space with the collision refused. -/
private theorem antiH_swapX (d p q : Nat) (hpq : p ≠ q) :
    antiH d (swapX d p q) := by
  refine antiH_matOf d _ (fun i j hi hj => ?_)
  cases h1 : i == p with
  | true =>
    cases h3 : i == q with
    | true =>
      exact absurd ((ground.beqEqOf h1).symm.trans (ground.beqEqOf h3))
        hpq
    | false =>
      cases h2 : j == q with
      | true =>
        cases h4 : j == p with
        | true =>
          exact absurd
            ((ground.beqEqOf h4).symm.trans (ground.beqEqOf h2)) hpq
        | false => rfl
      | false => cases h4 : j == p <;> rfl
  | false =>
    cases h2 : j == q <;> cases h3 : i == q <;> cases h4 : j == p <;>
      rfl

/-- The `i`-sum combination is anti-Hermitian at every place
pair. -/
private theorem antiH_isumX (d p q : Nat) : antiH d (isumX d p q) := by
  refine antiH_matOf d _ (fun i j hi hj => ?_)
  cases h1 : i == p <;> cases h2 : j == q <;> cases h3 : i == q <;>
    cases h4 : j == p <;> rfl

/-- The diagonal combination is anti-Hermitian at every place. -/
private theorem antiH_diagX (d p : Nat) : antiH d (diagX d p) := by
  refine antiH_matOf d _ (fun i j hi hj => ?_)
  cases h1 : i == p <;> cases h2 : j == p <;> cases h3 : i == p + 1 <;>
    cases h4 : j == p + 1 <;> rfl

/-- The whole displayed list's anti-Hermitian read, the fold. -/
def antiHAll (d : Nat) : Prop :=
  ((genList d).all (fun X => decide (antiH d X))) = true

instance (d : Nat) : Decidable (antiHAll d) :=
  inferInstanceAs (Decidable (_ = _))

/-- Every displayed generator is anti-Hermitian, the three families
folded over the enumeration. -/
theorem antiHAll_holds (d : Nat) : antiHAll d := by
  show ((genList d).all (fun X => decide (antiH d X))) = true
  unfold genList
  rw [all_append, all_append]
  refine andIntroB (andIntroB ?_ ?_) ?_
  · rw [all_flatMap]
    refine all_range_intro d (fun q hq => ?_)
    show (((List.range q).map (fun p => swapX d p q)).all _) = true
    rw [all_map]
    exact all_range_intro q (fun p hp =>
      decide_eq_true (antiH_swapX d p q (Nat.ne_of_lt hp)))
  · rw [all_flatMap]
    refine all_range_intro d (fun q hq => ?_)
    show (((List.range q).map (fun p => isumX d p q)).all _) = true
    rw [all_map]
    exact all_range_intro q (fun p hp =>
      decide_eq_true (antiH_isumX d p q))
  · rw [all_map]
    exact all_range_intro (d - 1) (fun p hp =>
      decide_eq_true (antiH_diagX d p))


/-- The Hermitian companion entrywise, `T = -i·X`: the `re` the
`im` and the `im` the `re`'s balance partner. -/
def tOf (X : List (List poly.Poly)) : List (List poly.Poly) :=
  X.map (fun r => r.map (fun e =>
    [ground.getAt BPair.unit e 1, (ground.getAt BPair.unit e 0).swap]))

/-- The Hermitian companions of the displayed list. -/
def tList (d : Nat) : List (List (List poly.Poly)) :=
  (genList d).map tOf

/-- The companion's entry read, `X = i T`: the formal `i` against
the companion entry reads the entry back, one remainder product at
`z² + 1`. -/
theorem iT_entry (a b : BPair) :
    poly.oneValue
      (poly.remMul stagesplit.iList entryI
        [b, a.swap]) [a, b] := by
  show poly.oneValue
    [(BPair.unit * b + BPair.unit)
       + ((BPair.ofNat 1 * a.swap) * (BPair.ofPos .one)).swap,
     (BPair.unit * a.swap + (BPair.ofNat 1 * b + BPair.unit))
       + ((BPair.ofNat 1 * a.swap) * BPair.unit).swap] [a, b]
  have hone : ∀ x : BPair, (BPair.ofNat 1 * x).oneValue x := by
    intro x
    rw [BPair.mul_comm (BPair.ofNat 1) x]
    exact BPair.mul_one_read x
  refine ⟨?_, ?_, trivial⟩
  · refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.unit_mul b)
            (BPair.oneValue_refl BPair.unit))
          (BPair.add_unit BPair.unit))
        (ground.swap_congr
          (BPair.oneValue_trans (BPair.mul_one_read _) (hone a.swap))))
      (BPair.unit_add a)
  · refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.unit_mul a.swap)
            (BPair.oneValue_trans
              (BPair.add_congr (hone b) (BPair.oneValue_refl BPair.unit))
              (BPair.add_unit b)))
          (BPair.unit_add b))
        (ground.swap_congr (BPair.mul_unit _)))
      (BPair.add_unit b)

/-- The list-level companion read, `X = i T` at every entry of
every member. -/
def iTRead (d : Nat) : Prop :=
  (((genList d).zip (tList d)).all (fun XT =>
    (List.range d).all (fun i => (List.range d).all (fun j =>
      decide (poly.oneValue
        (poly.remMul stagesplit.iList entryI
          (ground.getAt [] (ground.getAt [] XT.2 i) j))
        (ground.getAt [] (ground.getAt [] XT.1 i) j)))))) = true

instance (d : Nat) : Decidable (iTRead d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The trace of a product at the formal-`i` carrier, the row
against column fold. -/
def traceMul (d : Nat) (X Y : List (List poly.Poly)) : poly.Poly :=
  ground.famFold poly.add [] (fun i =>
    ground.famFold poly.add [] (fun j =>
      poly.remMul stagesplit.iList
        (ground.getAt [] (ground.getAt [] X i) j)
        (ground.getAt [] (ground.getAt [] Y j) i)) (List.range d))
    (List.range d)

/-- The trace pairing's realness read: every Gram entry's `im`
component reads the sum's unit, the `re` projection's coherence,
decided at the pinned widths. -/
def gramReal (d : Nat) : Prop :=
  ((genList d).all (fun X => (genList d).all (fun Y =>
    decide (BPair.oneValue
      (ground.getAt BPair.unit (traceMul d X Y) 1) BPair.unit)))) = true

instance (d : Nat) : Decidable (gramReal d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The trace-pairing Gram at the `re` components, the projection
whose coherence is `gramReal`'s decided read. -/
def gramR (d : Nat) : elim.Mat :=
  (genList d).map (fun X => (genList d).map (fun Y =>
    ground.getAt BPair.unit (traceMul d X Y) 0))

/-- The Gram's determinant, the pivot-descent read. -/
def detG (d : Nat) : BPair := elim.detD (gramR d)

/-- The Gram's adjugate at the pivot-descent determinant. -/
def adjG (d : Nat) : elim.Mat :=
  elim.adjO elim.detD BPair.swap (gramR d)

/-- The metric dual's data verified at the adjugate identity,
`G · adj G = det G · 1`: the identity's read at the computed
adjugate and determinant, the pair data's own coherence. -/
def gramSolve (d : Nat) : Prop :=
  let gm := gramR d
  elim.matOneValue (elim.matMul gm (elim.adjO elim.detD BPair.swap gm))
    (inertia.matScaleB (elim.detD gm) (inertia.idMat gm.length))

/-- The displayed list's independence read: the trace-pairing
Gram's determinant off the sum's unit, the solve's warrant
(`lem:genericlift`(ii)'s off-equal-members read at the pinned
widths). -/
def gramIndep (d : Nat) : Prop :=
  ¬ (detG d).oneValue BPair.unit

instance (d : Nat) : Decidable (gramIndep d) :=
  inferInstanceAs (Decidable (¬ _))

instance (d : Nat) : Decidable (gramSolve d) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The Kronecker read at two keys. -/
def dl (i j : Nat) : BPair :=
  if i == j then BPair.ofNat 1 else BPair.unit

/-- The adjugate-weighted Fierz sum at stated list and adjugate
data, the width's objects bound once. -/
private def fierzSAt (gs : List (List (List poly.Poly)))
    (ag : elim.Mat) (p q r s : Nat) : poly.Poly :=
  ground.famFold poly.add [] (fun a =>
    ground.famFold poly.add [] (fun b =>
      poly.scaleP
        (ground.getAt BPair.unit (ground.getAt [] ag a) b)
        (poly.remMul stagesplit.iList
          (ground.getAt [] (ground.getAt []
            (ground.getAt [] gs a) p) q)
          (ground.getAt [] (ground.getAt []
            (ground.getAt [] gs b) r) s))) (List.range gs.length))
    (List.range gs.length)

/-- The adjugate-weighted Fierz sum,
`S_pqrs = Σ_{a,b} adj(G)_{ab} (X_a)_pq (X_b)_rs`. -/
def fierzS (d p q r s : Nat) : poly.Poly :=
  fierzSAt (genList d) (adjG d) p q r s

/-- The Fierz read cleared of the form point: the ξ-orthonormal
display's rescaling withdraws at the metric dual (`prop:form`'s
one-value read), leaving
`d·δ_ps·δ_rq·det G = δ_pq·δ_rs·det G + d·S` over every index
tuple of the width. -/
def fierzRead (d : Nat) : Prop :=
  let gs := genList d
  let gm := gramR d
  let ag := elim.adjO elim.detD BPair.swap gm
  let dg := [elim.detD gm]
  ((List.range d).all (fun p => (List.range d).all (fun q =>
    (List.range d).all (fun r => (List.range d).all (fun s =>
      decide (poly.oneValue
        (poly.scaleP (dl p s * dl r q * BPair.ofNat d) dg)
        (poly.add (poly.scaleP (dl p q * dl r s) dg)
          (poly.scaleP (BPair.ofNat d)
            (fierzSAt gs ag p q r s))))))))) = true

instance (d : Nat) : Decidable (fierzRead d) :=
  inferInstanceAs (Decidable (_ = _))


end generators
