import MassGap.Elim
/-!
`thm:windowsep` — the separation arithmetic: the magnitude carrier
(`mag`, the members' larger against smaller, the sorted pair's value
at the order read, with its arithmetic laws — the sum's cap
`mag_add_le`, the product's identity `mag_mul`, and the power's
`mag_bpow` with the capped read `mag_bpow_le` at a bound on the
datum's own magnitude), the coefficient fold capping a polynomial's
evaluations over a bound (`magFold`, cleared at the bound's second
member's powers, its Horner pass reading the monomial fold
`Σ_i |s_i| n^i d^(k-i)` over the occupancy family's keys at
`magFold_read`, with the reads at or above the sum's unit
`unitLe_height`, `unitLe_radiusN`, `unitLe_radiusD`,
`unitLe_magFold`, the swap's blindness `magFold_neg` and the
cleared list's read `magFold_clearVar` — the bound's first member
taking the clearing and the fold the clearing's whole power —
beside it),
the height and the radius pair `B = [c + H : c]`
(`height`, `radiusN`/`radiusD`; the leading-term bound is the
theorem tier's own, `lead_upper` and `lead_lower`: beyond the radius
the tail's magnitude sits below the leading term's at the geometric
telescope, so the evaluation reads the term's side; the bound's
cleared reads beside them, the leading margin at the radius
`leadMargin` with its display `leadMargin_read` and its positivity
`unitLt_leadMargin` at an occupied top, the leading term's
magnitude at a natural clearing the radius against the margin
`leadTerm_ge`, an evaluation's magnitude under the coefficient fold
at the bound one against the point's power `magEval_le` with that
fold's read `magFold_one_read`, and the leading magnitude's
positivity `unitLt_radiusD`), the
curvature fold `Λ` at the splitting count `(i choose 2)`
(`curvFold`, cleared), and the separation's width read (`sepRead`):
a width sits at or below the display `2 max{Λ V, 1} δ = 1`'s `δ`
exactly at the two cleared comparisons, the Bézout cofactor's fold
`V` clearing at the resultant (`elim.bezout_all`'s adjugate solve at
`(S, S')`), the squarefree site the resultant's own read.  Every read here enters at the value's
representative (`poly.vnorm`): the radius reads the top key's
coefficient at the degree's own read and the folds run over the
occupancy family, so each read is a function of the one-value
class alone (`sepRead_congr` with the per-read equalities), and a
consumer decides the certificate at the representative its own
route computes.  The division descent's greatest common
divisor at general inputs — the squarefree part with the iterated
Bézout witnesses — is `lem:stagesplit`'s certificate tier
(`gcdRead`, `sqfreeRead`, `multAt`); at this tier every input
enters squarefree at the resultant's read, `poly.divRead`,
`poly.div_unique` and `poly.hornerRead` riding the stage's remainder
arithmetic (`lem:stage`).  That tier's producer is this module's
(`GcdData`, `gcdD`): the extended primitive pseudo-remainder walk at
the integer representatives, one row per remainder at the invariant
`u P + v Q = m r` — the row's two multipliers riding each
pseudo-division and the row's own clearing `m` absorbing both the
step's leading power and the content stripped off the remainder at
the coefficients' margins (`BPair.marginN` folded at the counts'
greatest common divisor), so every row stays on the integer
carrier.  The walk seeds at the two inputs ordered by degree and
stops at the first cleared remainder, the answer the prior row; that
row's remainder is then carried to a positive top (its clearing
taking the side exchange with it) and stripped of its own content,
and the divisor enters `lem:stagesplit`'s spelling as the below-top
list with the stated top.  The two cofactors are the inputs'
pseudo-divisions by that divisor, each exact, their clearings the
leading power `ℓ^k` the division accumulated; the Bézout witness is
the answer row's own pair at its clearing.  `stagesplit.gcdRead`
verifies the tuple whole — the produced data is decided, never
trusted — and `genericlift.pReduce` is the recorded consumer, a pair
moving to its reduced representative exactly where the certificate
decides.  The separation theorem itself — distinct
roots at `Λ V G ≥ 1` — is the general tier at its recorded
consumers (`lem:stage`'s isolating brackets, `lem:split`'s
designations), the arithmetic below its stated data.
-/

namespace windowsep
open ground poly elim

/-- The magnitude: the members' larger against smaller, the sorted
pair's value at the order read. -/
def mag (x : BPair) : BPair := if x < x.swap then x.swap else x

/-- The height: the largest coefficient magnitude, the fold's
trichotomy at each member of the value's representative
(`poly.vnorm`). -/
def height (P : Poly) : BPair :=
  (poly.vnorm P).foldl (fun h c => if h < mag c then mag c else h)
    BPair.unit

/-- The radius pair's first member `c + H`, at `c` the leading
coefficient's magnitude and `H` the height: every located root sits in
the radius segment between `B`'s balance partner and `B` at
`B = [c + H : c]`, the leading-term bound. -/
def radiusN (P : Poly) : BPair :=
  (mag (top (poly.vnorm P)) + height P).norm

/-- The radius pair's second member, the leading coefficient's
magnitude — the top key's coefficient at the value's
representative, the degree's own read. -/
def radiusD (P : Poly) : BPair := mag (top (poly.vnorm P))

/-- The two-base monomial fold of a coefficient list, `Σ_i l_i n^i
d^(k-i)` at `k` the list's top key: one pass at two running
accumulators, the powers shared, every intermediate at its
canonical representative. -/
def foldPow (l : List BPair) (n d : BPair) : BPair :=
  (l.reverse.foldl (fun s c =>
    (((s.1 * n).norm + (c * s.2).norm).norm, (s.2 * d).norm))
    (BPair.unit, BPair.ofPos .one)).1

/-- The coefficient fold at a bound `[n : d]`, cleared at the second
member's powers: `Σ_i |s_i| n^i d^(k-i)` at `k` the top key, the
evaluations' cap over the bound against `d^k` — one pass at two
running accumulators, the powers shared. -/
def magFold (P : Poly) (n d : BPair) : BPair :=
  foldPow ((poly.vnorm P).map mag) n d

/-- The curvature fold `Λ` at a bound `[n : d]`, cleared at the
second member: `Σ_{i≥2} (i choose 2) |s_i| n^(i-2) d^(k-i)` against
`d^(k-2)`, the splitting count `Σ_{a+b+2=i}(a+1) = (i choose 2)`
the display's, the pass `magFold`'s at the weighted shift. -/
def curvFold (P : Poly) (n d : BPair) : BPair :=
  foldPow ((List.range ((poly.vnorm P).length - 2)).map (fun j =>
    BPair.ofNat ((j + 2) * (j + 1) / 2)
      * mag (ground.getAt BPair.unit (poly.vnorm P) (j + 2)))) n d

/-- The separation's width read at a squarefree `S`: the width
`[wn : wd]` — a gap, positive by its carrier — sits at or below
the `δ` of `2 max{Λ V, 1} δ = 1` exactly at the two cleared
comparisons, `Λ` the curvature fold at the radius, `V` the Bézout
cofactor's fold clearing at the resultant (the adjugate solve at
`(S, S')`), and `δ` at most `[1 : 2]`; the squarefree site is the
resultant's own read. -/
def sepRead (S : Poly) (wn wd : Pos) : Prop :=
  (resultant (poly.vnorm S) (deriv (poly.vnorm S))).offUnit
  ∧ (BPair.ofNat 2 * BPair.ofPos wn
        * (curvFold S (radiusN S) (radiusD S)
          * magFold (bezoutB (poly.vnorm S) (deriv (poly.vnorm S)))
              (radiusN S) (radiusD S)))
      ≤ (BPair.ofPos wd
        * (mag (resultant (poly.vnorm S) (deriv (poly.vnorm S)))
          * bpow (radiusD S)
              ((poly.vnorm S).length - 3
               + ((poly.vnorm (bezoutB (poly.vnorm S)
                    (deriv (poly.vnorm S)))).length - 1))))
  ∧ BPair.ofNat 2 * BPair.ofPos wn ≤ BPair.ofPos wd

/-! The reads are functions of the one-value class alone: each
enters at the value's representative, so a representative exchange
moves each read by `poly.vnorm_congr`'s equality. -/

/-- The height at every representative of one value. -/
theorem height_congr {P Q : Poly} (h : poly.oneValue P Q) :
    height P = height Q := by
  unfold height
  rw [poly.vnorm_congr h]

/-- The radius pair's first member at every representative. -/
theorem radiusN_congr {P Q : Poly} (h : poly.oneValue P Q) :
    radiusN P = radiusN Q := by
  unfold radiusN
  rw [poly.vnorm_congr h, height_congr h]

/-- The radius pair's second member at every representative. -/
theorem radiusD_congr {P Q : Poly} (h : poly.oneValue P Q) :
    radiusD P = radiusD Q := by
  unfold radiusD
  rw [poly.vnorm_congr h]

/-- The curvature fold at every representative. -/
theorem curvFold_congr {P Q : Poly} (h : poly.oneValue P Q)
    (n d : BPair) : curvFold P n d = curvFold Q n d := by
  unfold curvFold
  rw [poly.vnorm_congr h]

/-- The separation's width read at every representative of one
value: the certificate reads the polynomial, so a consumer decides
it at the representative its own route computes — the descent's
read at a square frame among them. -/
theorem sepRead_congr {S S' : Poly} (h : poly.oneValue S S')
    (wn wd : Pos) : sepRead S wn wd ↔ sepRead S' wn wd := by
  unfold sepRead
  rw [poly.vnorm_congr h, radiusN_congr h, radiusD_congr h,
      curvFold_congr h]

/-! The width read decides at the descent: the resultant is the
shift frame's walk and the Bezout row the erased frames' walks
(`elim.detD_eq` with `elim.minor_detL`, `elim.bezoutBD_eq`), the
comparisons moved across the values' reads. -/

/-- The magnitude at every representative of one value. -/
theorem mag_congr {x y : BPair} (h : x.oneValue y) :
    (mag x).oneValue (mag y) := by
  unfold mag
  cases hx : decide (x < x.swap) with
  | true =>
    rw [if_pos (of_decide_eq_true hx)]
    cases hy : decide (y < y.swap) with
    | true =>
      rw [if_pos (of_decide_eq_true hy)]
      exact ground.swap_congr h
    | false =>
      exact absurd
        ((decide_eq_true (BPair.lt_congr h (ground.swap_congr h)
          (of_decide_eq_true hx))).symm.trans hy)
        (fun hcl => Bool.noConfusion hcl)
  | false =>
    cases hy : decide (y < y.swap) with
    | true =>
      exact absurd
        ((decide_eq_true (BPair.lt_congr (BPair.oneValue_symm h)
          (ground.swap_congr (BPair.oneValue_symm h))
          (of_decide_eq_true hy))).symm.trans hx)
        (fun hcl => Bool.noConfusion hcl)
    | false =>
      rw [if_neg (fun hlt => Bool.noConfusion
          ((decide_eq_true hlt).symm.trans hx)),
        if_neg (fun hlt => Bool.noConfusion
          ((decide_eq_true hlt).symm.trans hy))]
      exact h

/-- The datum sits at or below its own magnitude. -/
theorem le_mag (z : BPair) : z ≤ mag z := by
  unfold mag
  cases hz : decide (z < z.swap) with
  | true =>
    rw [if_pos (of_decide_eq_true hz)]
    exact ground.leB_of_lt (of_decide_eq_true hz)
  | false =>
    rw [if_neg (fun hlt => Bool.noConfusion
      ((decide_eq_true hlt).symm.trans hz))]
    exact ground.leB_refl z

/-- The datum's balance partner sits at or below its magnitude:
the carrier's two-sided read, the magnitude the larger member. -/
theorem swap_le_mag (z : BPair) : z.swap ≤ mag z := by
  unfold mag
  cases hz : decide (z < z.swap) with
  | true =>
    rw [if_pos (of_decide_eq_true hz)]
    exact ground.leB_refl z.swap
  | false =>
    have hn : ¬ (z < z.swap) := fun hlt =>
      Bool.noConfusion ((decide_eq_true hlt).symm.trans hz)
    rw [if_neg hn]
    exact ground.leB_of_not_lt hn

/-- The magnitude sits at or above the sum's unit, the two-sided
read's own consequence. -/
theorem unitLe_mag (z : BPair) : BPair.unit ≤ mag z :=
  ground.leB_of_not_lt (fun h =>
    have hb : BPair.unit.swap < z.swap :=
      ground.ltB_swap (ground.leB_ltB_trans (le_mag z) h)
    ground.leB_not_lt (ground.leB_of_lt hb)
      (ground.leB_ltB_trans (swap_le_mag z) h))

/-- A datum at or above the sum's unit is its own magnitude. -/
theorem mag_unitLe {z : BPair} (h : BPair.unit ≤ z) : mag z = z :=
  if_neg (fun hlt =>
    have hb : (z.swap).swap < BPair.unit.swap :=
      ground.ltB_swap (ground.leB_ltB_trans h hlt)
    ground.leB_not_lt h hb)

/-- An equal-membered pair is its own balance partner. -/
private theorem swap_eq_of_eqMem : ∀ {z : BPair}, z.fst = z.snd →
    z.swap = z
  | ⟨a, b⟩, h => by
    show BPair.mk b a = BPair.mk a b
    rw [show a = b from h]

/-- The magnitude reads through the memberwise swap: the two
members' larger is the same either way. -/
theorem mag_swap (z : BPair) : mag (z.swap) = mag z := by
  unfold mag
  rw [BPair.swap_swap]
  match ground.trich z.fst z.snd with
  | Trich.lt g hg =>
    have hlt : z < z.swap := ⟨g + g, by
      show z.fst + z.fst + (g + g) = z.snd + z.snd
      rw [ground.add_add_comm z.fst z.fst g g, hg]⟩
    rw [if_pos hlt,
      if_neg (ground.leB_not_lt (ground.leB_of_lt hlt))]
  | Trich.eq he => rw [swap_eq_of_eqMem he]
  | Trich.gt g hg =>
    have hgt : z.swap < z := ⟨g + g, by
      show z.snd + z.snd + (g + g) = z.fst + z.fst
      rw [ground.add_add_comm z.snd z.snd g g, hg]⟩
    rw [if_pos hgt,
      if_neg (ground.leB_not_lt (ground.leB_of_lt hgt))]


/-- The magnitude of a rescaled datum is the magnitude's own
rescaling, the sort blind to the shared positive factor. -/
theorem mag_scale (z : BPair) (w : Pos) :
    mag (z.scale w) = (mag z).scale w := by
  by_cases h : z < z.swap
  · have h' : z.scale w < (z.scale w).swap := BPair.scale_lt w h
    show (if z.scale w < (z.scale w).swap then (z.scale w).swap
        else z.scale w)
      = (if z < z.swap then z.swap else z).scale w
    rw [if_pos h', if_pos h]
    rfl
  · have h' : ¬ (z.scale w < (z.scale w).swap) := fun hh =>
      h (BPair.lt_of_scale_lt hh)
    show (if z.scale w < (z.scale w).swap then (z.scale w).swap
        else z.scale w)
      = (if z < z.swap then z.swap else z).scale w
    rw [if_neg h', if_neg h]
/-- The height's running maximum prices its seed and every member's
magnitude, one trichotomy per step. -/
private theorem heightGo : ∀ (l : Poly) (acc : BPair),
    acc ≤ l.foldl (fun h c => if h < mag c then mag c else h) acc
      ∧ ∀ z ∈ l, mag z
          ≤ l.foldl (fun h c => if h < mag c then mag c else h) acc
  | [], acc => ⟨ground.leB_refl acc, fun _ h => nomatch h⟩
  | c :: t, acc => by
    have hs : acc ≤ (if acc < mag c then mag c else acc)
        ∧ mag c ≤ (if acc < mag c then mag c else acc) := by
      cases hd : decide (acc < mag c) with
      | true =>
        rw [if_pos (of_decide_eq_true hd)]
        exact ⟨ground.leB_of_lt (of_decide_eq_true hd),
          ground.leB_refl _⟩
      | false =>
        have hn : ¬ (acc < mag c) := fun hlt =>
          Bool.noConfusion ((decide_eq_true hlt).symm.trans hd)
        rw [if_neg hn]
        exact ⟨ground.leB_refl _, ground.leB_of_not_lt hn⟩
    have ih := heightGo t (if acc < mag c then mag c else acc)
    refine ⟨ground.leB_trans hs.1 ih.1, fun z hz => ?_⟩
    cases hz with
    | head => exact ground.leB_trans hs.2 ih.1
    | tail _ hz' => exact ih.2 z hz'

/-- The height sits at or above every coefficient's magnitude at
the value's representative. -/
theorem mag_le_height {P : Poly} {z : BPair}
    (h : z ∈ poly.vnorm P) : mag z ≤ height P :=
  (heightGo (poly.vnorm P) BPair.unit).2 z h


/-! The magnitude's arithmetic laws, `thm:windowsep`'s clause: the
sum's magnitude sits at or below the magnitudes' sum, the product's
is the magnitudes' product, and the power's is the magnitude's
power; the coefficient fold's Horner pass reads the monomial fold
over the occupancy family's keys. -/

/-- The magnitude is one of the pair's two members, the order
read's two arms. -/
private theorem mag_cases (z : BPair) : mag z = z ∨ mag z = z.swap := by
  cases h : decide (z < z.swap) with
  | true => exact Or.inr (if_pos (of_decide_eq_true h))
  | false =>
    exact Or.inl (if_neg (fun hlt =>
      Bool.noConfusion ((decide_eq_true hlt).symm.trans h)))

/-- The magnitude's comparison at a common factor: a bound holding at
the datum and at its balance partner holds at the magnitude. -/
theorem mag_mul_le {z M k : BPair} (h1 : k * z ≤ M)
    (h2 : k * z.swap ≤ M) : k * mag z ≤ M := by
  cases mag_cases z with
  | inl h => rw [h]; exact h1
  | inr h => rw [h]; exact h2

/-- A datum at or above the sum's unit at both members reads its
own balance partner: both sit at the unit. -/
private theorem eq_swap_of_unitLe {z : BPair} (h1 : BPair.unit ≤ z)
    (h2 : BPair.unit ≤ z.swap) : z.oneValue z.swap :=
  BPair.oneValue_trans
    (BPair.oneValue_symm (ground.leB_antisymm h1 (ground.leUnitOfSwap h2)))
    (ground.swap_congr (ground.leB_antisymm h1 (ground.leUnitOfSwap h2)))

/-- The magnitude is the one member at or above the sum's unit: a
datum at or above the unit among the pair's two members reads the
magnitude. -/
private theorem magUniq {z w : BPair} (hw : BPair.unit ≤ w)
    (h : w = z ∨ w = z.swap) : (mag z).oneValue w := by
  have hm : BPair.unit ≤ mag z := unitLe_mag z
  cases mag_cases z with
  | inl hz =>
    rw [hz] at hm
    cases h with
    | inl hw' => rw [hz, hw']; exact BPair.oneValue_refl _
    | inr hw' =>
      rw [hw'] at hw
      rw [hz, hw']
      exact eq_swap_of_unitLe hm hw
  | inr hz =>
    rw [hz] at hm
    cases h with
    | inl hw' =>
      rw [hw'] at hw
      rw [hz, hw']
      exact BPair.oneValue_symm (eq_swap_of_unitLe hw hm)
    | inr hw' => rw [hz, hw']; exact BPair.oneValue_refl _

/-- A magnitude at the sum's unit reads its datum there. -/
theorem unit_of_mag {z : BPair} (h : (mag z).oneValue BPair.unit) :
    z.oneValue BPair.unit := by
  cases mag_cases z with
  | inl hz => rw [hz] at h; exact h
  | inr hz =>
    rw [hz] at h
    exact ground.swap_congr h

/-- The sum's magnitude sits at or below the magnitudes' sum. -/
theorem mag_add_le (x y : BPair) : mag (x + y) ≤ mag x + mag y := by
  cases mag_cases (x + y) with
  | inl h =>
    rw [h]
    exact ground.leB_add (le_mag x) (le_mag y)
  | inr h =>
    rw [h, ← BPair.swap_add]
    exact ground.leB_add (swap_le_mag x) (swap_le_mag y)

/-- The fold's magnitude sits at or below the magnitudes' fold. -/
theorem mag_famFold_le {α : Type} (f : α → BPair) : ∀ l : List α,
    mag (ground.famFold BPair.add BPair.unit f l)
      ≤ ground.famFold BPair.add BPair.unit
          (fun i => mag (f i)) l
  | [] => by
    show mag BPair.unit ≤ BPair.unit
    rw [mag_unitLe (ground.leB_refl BPair.unit)]
    exact ground.leB_refl _
  | a :: t =>
    ground.leB_trans
      (mag_add_le (f a)
        (ground.famFold BPair.add BPair.unit f t))
      (ground.leB_add (ground.leB_refl _) (mag_famFold_le f t))

/-- The product's magnitude is the magnitudes' product. -/
theorem mag_mul (x y : BPair) :
    (mag (x * y)).oneValue (mag x * mag y) := by
  refine magUniq (ground.unitLeMul (unitLe_mag x) (unitLe_mag y)) ?_
  cases mag_cases x with
  | inl hx =>
    cases mag_cases y with
    | inl hy => exact Or.inl (by rw [hx, hy])
    | inr hy => exact Or.inr (by rw [hx, hy, BPair.mul_swap])
  | inr hx =>
    cases mag_cases y with
    | inl hy => exact Or.inr (by rw [hx, hy, BPair.swap_mul])
    | inr hy => exact Or.inl (by rw [hx, hy, BPair.swap_mul_swap])

/-! The power's magnitude at the balance carrier: the power's
magnitude is the magnitude's power, and it caps at the cap's
power. -/

/-- The power's magnitude is the magnitude's power. -/
theorem mag_bpow (x : BPair) : ∀ k : Nat,
    (mag (ground.bpow x k)).oneValue (ground.bpow (mag x) k)
  | 0 =>
    BPair.oneValue_of_eq
      (mag_unitLe (ground.leB_of_lt (ground.unitLtOfPos Pos.one)))
  | k + 1 => by
    refine BPair.oneValue_trans
      (mag_congr (BPair.norm_oneValue (x * ground.bpow x k))) ?_
    refine BPair.oneValue_trans (mag_mul x (ground.bpow x k)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (mag x)) (mag_bpow x k)) ?_
    exact BPair.oneValue_symm (BPair.norm_oneValue _)

/-- The power's magnitude under a cap on the datum's. -/
theorem mag_bpow_le {x R : BPair} (h : mag x ≤ R) (k : Nat) :
    mag (ground.bpow x k) ≤ ground.bpow R k :=
  ground.leB_congr_left (BPair.oneValue_symm (mag_bpow x k))
    (ground.bpow_mono (unitLe_mag x) h k)

/-! The coefficient fold's Horner pass at its own recursion: the
pass's two accumulators read the running power and the collected
monomial fold. -/

/-- The Horner pass's recursion: the value and the running power at
the list's own descent. -/
private def powGo (n d : BPair) : List BPair → BPair × BPair
  | [] => (BPair.unit, BPair.ofPos .one)
  | c :: t =>
    (((((powGo n d t).1 * n).norm + (c * (powGo n d t).2).norm).norm),
      (((powGo n d t).2 * d).norm))

private theorem foldPow_powGo (n d : BPair) : ∀ l : List BPair,
    l.reverse.foldl (fun s c =>
        (((s.1 * n).norm + (c * s.2).norm).norm, (s.2 * d).norm))
        (BPair.unit, BPair.ofPos .one)
      = powGo n d l
  | [] => rfl
  | c :: t => by
    rw [ground.reverse_cons c t,
      ground.foldl_append (fun s c =>
        (((s.1 * n).norm + (c * s.2).norm).norm, (s.2 * d).norm))
        t.reverse [c] (BPair.unit, BPair.ofPos .one),
      foldPow_powGo n d t]
    rfl

private theorem foldPow_eq (n d : BPair) (l : List BPair) :
    foldPow l n d = (powGo n d l).1 :=
  congrArg Prod.fst (foldPow_powGo n d l)

/-- The pass's running power at the list's count. -/
private theorem powGo_snd (n d : BPair) : ∀ l : List BPair,
    ((powGo n d l).2).oneValue (ground.bpow d l.length)
  | [] => BPair.oneValue_refl _
  | _ :: t => by
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (powGo_snd n d t) (BPair.oneValue_refl d)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm (ground.bpow d t.length) d)) ?_
    exact BPair.oneValue_symm (BPair.norm_oneValue _)

private theorem mul_shuffle (a b c e : BPair) :
    a * (e * b) * c = e * (a * b * c) := by
  rw [BPair.mul_comm e b, ← BPair.mul_assoc a b e,
    BPair.mul_assoc (a * b) e c, BPair.mul_comm e c,
    ← BPair.mul_assoc (a * b) c e, BPair.mul_comm (a * b * c) e]

/-- The pass's value at the monomial fold over the list's keys. -/
private theorem powGo_fst (n d : BPair) : ∀ l : List BPair,
    ((powGo n d l).1).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun i => ground.getAt BPair.unit l i * ground.bpow n i
          * ground.bpow d (l.length - 1 - i))
        (List.range l.length))
  | [] => BPair.oneValue_refl _
  | c :: t => by
    rw [show (c :: t).length = t.length + 1 from rfl,
      ground.foldB_range_cons
        (fun i => ground.getAt BPair.unit (c :: t) i * ground.bpow n i
          * ground.bpow d (t.length + 1 - 1 - i)) t.length]
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.norm_oneValue _) (BPair.norm_oneValue _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.add_comm ((powGo n d t).1 * n) (c * (powGo n d t).2))) ?_
    refine BPair.add_congr ?_ ?_
    · refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.mul_one_read c) (BPair.oneValue_refl _)) ?_
      exact BPair.mul_congr (BPair.oneValue_refl c)
        (BPair.oneValue_symm (powGo_snd n d t))
    · refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans ?_
        (BPair.oneValue_of_eq (BPair.mul_comm n (powGo n d t).1))
      refine BPair.oneValue_trans ?_
        (BPair.mul_congr (BPair.oneValue_refl n)
          (BPair.oneValue_symm (powGo_fst n d t)))
      refine BPair.oneValue_trans ?_
        (ground.foldB_mul_left n
          (fun j => ground.getAt BPair.unit t j * ground.bpow n j
            * ground.bpow d (t.length - 1 - j))
          (List.range t.length))
      refine ground.foldB_congr_members _ _ (List.range t.length)
        (fun j _ => ?_)
      show (ground.getAt BPair.unit t j * ground.bpow n (j + 1)
          * ground.bpow d (t.length - (j + 1))).oneValue
        (n * (ground.getAt BPair.unit t j * ground.bpow n j
          * ground.bpow d (t.length - 1 - j)))
      rw [show t.length - (j + 1) = t.length - 1 - j from by
        rw [ground.subSub t.length 1 j, Nat.add_comm 1 j]]
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.norm_oneValue (n * ground.bpow n j)))
          (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_of_eq
        (mul_shuffle (ground.getAt BPair.unit t j) (ground.bpow n j)
          (ground.bpow d (t.length - 1 - j)) n)

/-- The pass's value at the monomial fold over the list's keys, the
fold's own read. -/
theorem foldPow_read (l : List BPair) (n d : BPair) :
    (foldPow l n d).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun i => ground.getAt BPair.unit l i * ground.bpow n i
          * ground.bpow d (l.length - 1 - i))
        (List.range l.length)) :=
  BPair.oneValue_trans (BPair.oneValue_of_eq (foldPow_eq n d l))
    (powGo_fst n d l)

/-- The magnitude read through a mapped list's entry. -/
theorem getAt_map_mag : ∀ (l : Poly) (i : Nat),
    ground.getAt BPair.unit (l.map mag) i
      = mag (ground.getAt BPair.unit l i)
  | [], _ => (mag_unitLe (ground.leB_refl BPair.unit)).symm
  | _ :: _, 0 => rfl
  | _ :: t, i + 1 => getAt_map_mag t i

/-- The coefficient fold reads the monomial fold at the value's
representative: the coefficients' magnitudes against the bound's
first member's powers, cleared at the second member's. -/
theorem magFold_read (P : Poly) (n d : BPair) :
    (magFold P n d).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun i => mag (ground.getAt BPair.unit (poly.vnorm P) i)
          * ground.bpow n i
          * ground.bpow d ((poly.vnorm P).length - 1 - i))
        (List.range (poly.vnorm P).length)) := by
  have h := powGo_fst n d ((poly.vnorm P).map mag)
  rw [ground.length_map mag (poly.vnorm P)] at h
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (foldPow_eq n d ((poly.vnorm P).map mag))) ?_
  refine BPair.oneValue_trans h ?_
  exact BPair.oneValue_of_eq
    (ground.famFold_congr_all BPair.add BPair.unit _ _
      (fun i => by rw [getAt_map_mag (poly.vnorm P) i])
      (List.range (poly.vnorm P).length))

/-! The reads at or above the sum's unit: the height, the radius
pair's two members and the coefficient fold each sit there. -/

/-- The height sits at or above the sum's unit. -/
theorem unitLe_height (P : Poly) : BPair.unit ≤ height P :=
  (heightGo (poly.vnorm P) BPair.unit).1

/-- The radius pair's second member sits at or above the sum's
unit. -/
theorem unitLe_radiusD (P : Poly) : BPair.unit ≤ radiusD P :=
  unitLe_mag _

/-- The radius pair's first member sits at or above the sum's
unit. -/
theorem unitLe_radiusN (P : Poly) : BPair.unit ≤ radiusN P :=
  ground.leB_congr_right
    (BPair.oneValue_symm (BPair.norm_oneValue _))
    (ground.unitLeAdd (unitLe_mag _) (unitLe_height P))

/-- The coefficient fold at a bound whose members sit at or above
the sum's unit sits there. -/
theorem unitLe_magFold (P : Poly) {n d : BPair}
    (hn : BPair.unit ≤ n) (hd : BPair.unit ≤ d) :
    BPair.unit ≤ magFold P n d :=
  ground.leB_congr_right
    (BPair.oneValue_symm (magFold_read P n d))
    (ground.foldB_nonneg _ (List.range (poly.vnorm P).length)
      (fun i _ => ground.unitLeMul
        (ground.unitLeMul (unitLe_mag _) (ground.unitLeBpow hn i))
        (ground.unitLeBpow hd _)))

/-- The coefficient fold at the bound one is the coefficients'
magnitudes' fold, every power of the bound the unit's. -/
theorem magFold_one_read (P : Poly) :
    (magFold P (BPair.ofPos .one) (BPair.ofPos .one)).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun i => mag (ground.getAt BPair.unit (poly.vnorm P) i))
        (List.range (poly.vnorm P).length)) := by
  refine BPair.oneValue_trans (magFold_read P _ _) ?_
  refine ground.foldB_congr_members _ _ _ (fun i _ => ?_)
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.mul_congr (BPair.oneValue_refl _) (ground.bpow_one i))
      (ground.bpow_one _)) ?_
  exact BPair.oneValue_trans (BPair.mul_congr_left (BPair.mul_one_read _))
    (BPair.mul_one_read _)

/-- A comparison at every counted key folds to the folds'
comparison over a range. -/
theorem leB_famFold_range (l : List Nat) {f g : Nat → BPair}
    (h : ∀ x, 0 < countOf x l → f x ≤ g x) :
    ground.famFold BPair.add BPair.unit f l
      ≤ ground.famFold BPair.add BPair.unit g l := by
  induction l with
  | nil => exact leB_refl _
  | cons a t ih =>
    refine leB_add (h a ?_) (ih (fun x hx => h x ?_))
    · rw [countOf_cons, if_pos rfl]; exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _)
    · exact Nat.lt_of_lt_of_le hx (countOf_cons_le x a t)

/-- The radius' second member at an occupied polynomial sits
strictly above the sum's unit, the leading magnitude's read. -/
theorem unitLt_radiusD (P : Poly) (h : ¬ poly.unitTail P) :
    BPair.unit < radiusD P :=
  ground.ltOfLeOff (unitLe_mag _)
    (fun hu => poly.vnorm_top h (unit_of_mag hu))

/-- The reverse triangle at the magnitude carrier: a sum's magnitude
sits at or beyond the first summand's less the second's. -/
private theorem mag_add_ge (u v : BPair) :
    mag u + (mag v).swap ≤ mag (u + v) := by
  have h0 : (u + v + v.swap).oneValue u := by
    rw [BPair.add_right_comm]
    exact BPair.add_swap_self u v
  have h1 : mag u ≤ mag (u + v) + mag v := by
    refine ground.leB_congr_left (mag_congr h0) ?_
    refine ground.leB_trans (mag_add_le (u + v) v.swap) ?_
    rw [mag_swap]
    exact ground.leB_refl _
  refine ground.leB_congr_right ?_ (ground.leB_add h1 (ground.leB_refl _))
  rw [BPair.add_right_comm]
  exact BPair.add_swap_self _ _

/-- The geometric telescope at the pair carrier: at `x ≡ y + H`,
`H Σ_{i<d} x^i y^{d-i} + y^{d+1} ≡ y x^d`. -/
private theorem geo_telescope (x y H : BPair) (hx : x.oneValue (y + H)) : ∀ d : Nat,
    (H * ground.famFold BPair.add BPair.unit
        (fun i => ground.bpow x i * ground.bpow y (d - i)) (List.range d)
      + ground.bpow y (d + 1)).oneValue (y * ground.bpow x d)
  | 0 =>
    BPair.oneValue_trans (BPair.add_congr (BPair.mul_unit H) (ground.bpow_one_read y))
      (BPair.oneValue_trans (BPair.unit_add y) (BPair.oneValue_symm (BPair.mul_one_read y)))
  | d + 1 => by
    have hG : (ground.famFold BPair.add BPair.unit
        (fun i => ground.bpow x i * ground.bpow y (d + 1 - i)) (List.range (d + 1))).oneValue
        (y * ground.famFold BPair.add BPair.unit
          (fun i => ground.bpow x i * ground.bpow y (d - i)) (List.range d)
          + ground.bpow x d * y) := by
      refine BPair.oneValue_trans (ground.foldB_range_snoc _ d) ?_
      refine BPair.add_congr ?_ ?_
      · refine BPair.oneValue_trans
          (ground.foldB_congr_members _ (fun i => y * (ground.bpow x i * ground.bpow y (d - i))) _
            (fun i hi => ?_)) (ground.foldB_mul_left y _ _)
        have hid : d + 1 - i = d - i + 1 := by
          have h := ground.subSuccAdd (k := i) (n := d + 1)
            (Nat.succ_le_succ (Nat.le_of_lt (ground.ltOfCountRange hi)))
          rw [Nat.succ_sub_succ] at h
          exact h.symm
        rw [hid]
        refine BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) (ground.bpow_succ_read y (d - i))) ?_
        exact BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)
      · rw [ground.addSubSelfL d 1]
        exact BPair.mul_congr (BPair.oneValue_refl _) (ground.bpow_one_read y)
    have ih := geo_telescope x y H hx d
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl H) hG)
        (ground.bpow_succ_read y (d + 1))) ?_
    generalize ground.famFold BPair.add BPair.unit
      (fun i => ground.bpow x i * ground.bpow y (d - i)) (List.range d) = G at ih ⊢
    generalize hC : ground.bpow x d = C at ih ⊢
    generalize ground.bpow y (d + 1) = B at ih ⊢
    refine BPair.oneValue_trans (ground.polEqB [H, y, G, C, B]
      (Pol.add (Pol.mul (Pol.mon (Mon.var 0))
          (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2)))
            (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 1)))))
        (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 4))))
      (Pol.add (Pol.mul (Pol.mon (Mon.var 1))
          (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 4))))
        (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 1)))))
      (by decide +kernel)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl y) ih) (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (ground.polEqB [H, y, C]
      (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))))
        (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 1)))))
      (Pol.mul (Pol.mon (Mon.var 1))
        (Pol.mul (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))))
      (by decide +kernel)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl y) ?_
    rw [← hC]
    exact BPair.oneValue_trans (BPair.mul_congr_left (BPair.oneValue_symm hx))
      (BPair.oneValue_symm (ground.bpow_succ_read x d))

/-- The leading margin at the radius, cleared at the radius' second
member's power: the leading term's magnitude at the radius against
the further terms' magnitudes' fold there, `|a_d| rN^d` against
`Σ_{i<d} |a_i| rN^i rD^{d-i}` at the radius `[rN : rD]` and the top
key `d`, the further terms' fold the coefficient fold's pass at
the below-top magnitudes with one further second-member factor. -/
def leadMargin (P : Poly) : BPair :=
  radiusD P * ground.bpow (radiusN P) ((poly.vnorm P).length - 1)
  + (radiusD P * foldPow (((poly.vnorm P).map mag).take ((poly.vnorm P).length - 1))
      (radiusN P) (radiusD P)).swap

/-- The index identity of the further terms' fold: one second-member
factor joined to the pass's power reads the display's. -/
private theorem subPredIdx {d i : Nat} (h : i < d) : d - 1 - i + 1 = d - i := by
  rw [ground.subSub d 1 i, Nat.add_comm 1 i]
  exact ground.subSuccAdd h

/-- The leading margin reads its display: the leading magnitude's
power against the further terms' magnitudes at the radius' powers. -/
theorem leadMargin_read (P : Poly) :
    (leadMargin P).oneValue
      (radiusD P * ground.bpow (radiusN P) ((poly.vnorm P).length - 1)
      + (ground.famFold BPair.add BPair.unit
          (fun i => mag (ground.getAt BPair.unit (poly.vnorm P) i)
            * ground.bpow (radiusN P) i
            * ground.bpow (radiusD P) ((poly.vnorm P).length - 1 - i))
          (List.range ((poly.vnorm P).length - 1))).swap) := by
  refine BPair.add_congr (BPair.oneValue_refl _) ?_
  refine ground.swap_congr ?_
  have hlen : (((poly.vnorm P).map mag).take ((poly.vnorm P).length - 1)).length
      = (poly.vnorm P).length - 1 := by
    rw [ground.length_take _ _ (by rw [ground.length_map]; exact Nat.sub_le _ _)]
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (foldPow_read _ _ _)) ?_
  rw [hlen]
  refine BPair.oneValue_trans (BPair.oneValue_symm (ground.foldB_mul_left _ _ _)) ?_
  refine ground.foldB_congr_members _ _ _ (fun i hi => ?_)
  have hi' : i < (poly.vnorm P).length - 1 := ground.ltOfCountRange hi
  rw [ground.getAt_take BPair.unit _ _ i hi', getAt_map_mag, ← subPredIdx hi']
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _) (ground.bpow_succ_read _ _)) ?_
  exact BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)

/-- The margin is a margin: at an occupied polynomial the leading
term's magnitude at the radius exceeds the further terms' fold
there, the leading term dominating at every point of margin at or
beyond the radius (the geometric telescope at the radius' two
members). -/
theorem unitLt_leadMargin (P : Poly) (h : ¬ poly.unitTail P) :
    BPair.unit < leadMargin P := by
  have hy : BPair.unit < radiusD P := unitLt_radiusD P h
  have hx : (radiusN P).oneValue (radiusD P + height P) := BPair.norm_oneValue _
  have hS : ground.famFold BPair.add BPair.unit
      (fun i => mag (ground.getAt BPair.unit (poly.vnorm P) i)
        * ground.bpow (radiusN P) i
        * ground.bpow (radiusD P) ((poly.vnorm P).length - 1 - i))
      (List.range ((poly.vnorm P).length - 1))
    ≤ height P * ground.famFold BPair.add BPair.unit
      (fun i => ground.bpow (radiusN P) i
        * ground.bpow (radiusD P) ((poly.vnorm P).length - 1 - i))
      (List.range ((poly.vnorm P).length - 1)) := by
    refine ground.leB_congr_right (ground.foldB_mul_left (height P)
      (fun i => ground.bpow (radiusN P) i
        * ground.bpow (radiusD P) ((poly.vnorm P).length - 1 - i))
      (List.range ((poly.vnorm P).length - 1))) ?_
    refine leB_famFold_range _ (fun i hi => ?_)
    have hi' : i < (poly.vnorm P).length :=
      Nat.lt_of_lt_of_le (ground.ltOfCountRange hi) (Nat.sub_le _ _)
    have hH : mag (ground.getAt BPair.unit (poly.vnorm P) i) ≤ height P :=
      mag_le_height (ground.mem_getAt BPair.unit _ i hi')
    refine ground.leB_congr_right (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) ?_
    exact ground.leB_mulL (ground.unitLeBpow (unitLe_radiusD P) _)
      (ground.leB_mulL (ground.unitLeBpow (unitLe_radiusN P) i) hH)
  have ht := geo_telescope (radiusN P) (radiusD P) (height P) hx ((poly.vnorm P).length - 1)
  refine BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (leadMargin_read P)) ?_
  generalize ground.famFold BPair.add BPair.unit
      (fun i => ground.bpow (radiusN P) i
        * ground.bpow (radiusD P) ((poly.vnorm P).length - 1 - i))
      (List.range ((poly.vnorm P).length - 1)) = G at hS ht
  generalize ground.famFold BPair.add BPair.unit
      (fun i => mag (ground.getAt BPair.unit (poly.vnorm P) i)
        * ground.bpow (radiusN P) i
        * ground.bpow (radiusD P) ((poly.vnorm P).length - 1 - i))
      (List.range ((poly.vnorm P).length - 1)) = S at hS ⊢
  generalize (poly.vnorm P).length - 1 = d at ht ⊢
  generalize radiusD P = y at hy ht hS ⊢
  generalize radiusN P = x at ht ⊢
  generalize height P = H at ht hS ⊢
  have hval : (y * ground.bpow x d + (H * G).swap).oneValue (ground.bpow y (d + 1)) := by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_symm ht) (BPair.oneValue_refl _)) ?_
    rw [BPair.add_comm (H * G) (ground.bpow y (d + 1)), BPair.add_right_comm]
    exact BPair.add_swap_self _ _
  have hpos : BPair.unit < ground.bpow y (d + 1) := ground.unitLtBpow hy _
  refine ground.ltB_trans_le (BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm hval) hpos) ?_
  exact ground.leB_add (ground.leB_refl _) (ground.leB_swap hS)

/-- A polynomial's evaluation's magnitude sits at or below its
coefficients' magnitudes' fold against the point's magnitude's power
at any key at or beyond its top, the point at or beyond one. -/
theorem magEval_le (p : Poly) (x : BPair) (m : Nat)
    (hm : (poly.vnorm p).length ≤ m + 1) (hx : BPair.ofPos .one ≤ mag x) :
    mag (poly.eval p x)
      ≤ magFold p (BPair.ofPos .one) (BPair.ofPos .one) * ground.bpow (mag x) m := by
  have hq : (poly.eval p x).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit (poly.vnorm p) k * ground.bpow x k)
        (List.range (poly.vnorm p).length)) :=
    BPair.oneValue_trans (poly.eval_congr (poly.oneValue_symm (poly.vnorm_ov p)) x)
      (poly.eval_famFold _ x)
  refine ground.leB_congr_left (BPair.oneValue_symm (mag_congr hq)) ?_
  refine ground.leB_trans (mag_famFold_le _ _) ?_
  refine ground.leB_congr_right (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.mul_congr_left (magFold_one_read p))
    (ground.foldB_mul_right _ _ _))) ?_
  refine leB_famFold_range _ (fun i hi => ?_)
  have him : i ≤ m := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (ground.ltOfCountRange hi) hm)
  refine ground.leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
    (mag_mul _ _)
    (BPair.mul_congr (BPair.oneValue_refl _) (mag_bpow x i)))) ?_
  exact ground.leB_mulR (unitLe_mag _) (ground.bpow_le_exp hx him)

/-- The leading term's magnitude at a natural at or beyond the
radius, cleared at the radius' first member's power: at or beyond the
leading margin against the natural's power at the top key, the tail
priced at the radius' powers. -/
theorem leadTerm_ge (P : Poly) (hP : ¬ poly.unitTail P) (l : Nat)
    (hcl : radiusN P ≤ BPair.ofNat l * radiusD P) :
    leadMargin P * ground.bpow (BPair.ofNat l) ((poly.vnorm P).length - 1)
      ≤ mag (poly.eval P (BPair.ofNat l))
        * ground.bpow (radiusN P) ((poly.vnorm P).length - 1) := by
  have hlen := poly.len_of_top_off (poly.vnorm_top hP)
  have hlu : BPair.unit ≤ BPair.ofNat l := ground.unitLeOfNat l
  have hmagl : mag (BPair.ofNat l) = BPair.ofNat l := mag_unitLe hlu
  refine ground.leB_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (leadMargin_read P))) ?_
  generalize hd : (poly.vnorm P).length - 1 = d at hlen ⊢
  have hgetd : ground.getAt BPair.unit (poly.vnorm P) d = poly.top (poly.vnorm P) :=
    (poly.topO_getAt ground.bpairOps _ d hlen).symm
  have hq : (poly.eval P (BPair.ofNat l)).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit (poly.vnorm P) k * ground.bpow (BPair.ofNat l) k)
        (List.range d)
      + poly.top (poly.vnorm P) * ground.bpow (BPair.ofNat l) d) := by
    refine BPair.oneValue_trans (poly.eval_congr (poly.oneValue_symm (poly.vnorm_ov P)) _) ?_
    have hf := poly.eval_famFold (poly.vnorm P) (BPair.ofNat l)
    rw [hlen] at hf
    refine BPair.oneValue_trans hf ?_
    rw [← hgetd]
    exact ground.foldB_range_snoc _ d
  have hTcap : mag (ground.famFold BPair.add BPair.unit
      (fun k => ground.getAt BPair.unit (poly.vnorm P) k * ground.bpow (BPair.ofNat l) k)
      (List.range d)) ≤ ground.famFold BPair.add BPair.unit
      (fun k => mag (ground.getAt BPair.unit (poly.vnorm P) k) * ground.bpow (BPair.ofNat l) k)
      (List.range d) := by
    refine ground.leB_trans (mag_famFold_le _ _) ?_
    refine leB_famFold_range _ (fun i _ => ?_)
    refine ground.leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
      (mag_mul _ _)
      (BPair.mul_congr (BPair.oneValue_refl _) (mag_bpow _ i)))) ?_
    rw [hmagl]
    exact ground.leB_refl _
  have htop : (mag (poly.top (poly.vnorm P) * ground.bpow (BPair.ofNat l) d)).oneValue
      (radiusD P * ground.bpow (BPair.ofNat l) d) := by
    refine BPair.oneValue_trans (mag_mul _ _) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans (mag_bpow _ d) ?_
    rw [hmagl]
    exact BPair.oneValue_refl _
  have hrev : radiusD P * ground.bpow (BPair.ofNat l) d
      + (ground.famFold BPair.add BPair.unit
        (fun k => mag (ground.getAt BPair.unit (poly.vnorm P) k)
          * ground.bpow (BPair.ofNat l) k) (List.range d)).swap
      ≤ mag (poly.eval P (BPair.ofNat l)) := by
    refine ground.leB_congr_right (mag_congr (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _)) (BPair.oneValue_symm hq))) ?_
    refine ground.leB_trans ?_ (mag_add_ge _ _)
    exact ground.leB_add (ground.leB_congr_left htop (ground.leB_refl _)) (ground.leB_swap hTcap)
  have hterm : ∀ i, i < d →
      mag (ground.getAt BPair.unit (poly.vnorm P) i) * ground.bpow (BPair.ofNat l) i
          * ground.bpow (radiusN P) d
        ≤ mag (ground.getAt BPair.unit (poly.vnorm P) i)
          * ground.bpow (radiusN P) i * ground.bpow (radiusD P) (d - i)
          * ground.bpow (BPair.ofNat l) d := by
    intro i hi
    have hid : i + (d - i) = d := by
      rw [Nat.add_comm]
      exact ground.subAdd (Nat.le_of_lt hi)
    have hxd : (ground.bpow (radiusN P) (i + (d - i))).oneValue
        (ground.bpow (radiusN P) d) := by
      rw [hid]
      exact BPair.oneValue_refl _
    have hli : (ground.bpow (BPair.ofNat l) i * ground.bpow (BPair.ofNat l) (d - i)).oneValue
        (ground.bpow (BPair.ofNat l) d) := by
      have h := ground.bpow_add (BPair.ofNat l) i (d - i)
      rw [hid] at h
      exact BPair.oneValue_symm h
    have hxN : ground.bpow (radiusN P) d ≤ ground.bpow (radiusN P) i
        * (ground.bpow (BPair.ofNat l) (d - i) * ground.bpow (radiusD P) (d - i)) := by
      refine ground.leB_congr_left hxd ?_
      refine ground.leB_congr_left (BPair.oneValue_symm (ground.bpow_add (radiusN P) i (d - i))) ?_
      refine ground.leB_mulR (ground.unitLeBpow (unitLe_radiusN P) i) ?_
      refine ground.leB_congr_right (ground.bpow_mul (BPair.ofNat l) (radiusD P) (d - i)) ?_
      exact ground.bpow_mono (unitLe_radiusN P) hcl (d - i)
    have hA : BPair.unit ≤ mag (ground.getAt BPair.unit (poly.vnorm P) i) := unitLe_mag _
    have hLi : BPair.unit ≤ ground.bpow (BPair.ofNat l) i := ground.unitLeBpow hlu i
    generalize mag (ground.getAt BPair.unit (poly.vnorm P) i) = A at hA ⊢
    generalize ground.bpow (BPair.ofNat l) i = Li at hLi hli ⊢
    generalize ground.bpow (radiusN P) d = Xd at hxN ⊢
    generalize ground.bpow (radiusN P) i = Xi at hxN ⊢
    generalize ground.bpow (BPair.ofNat l) (d - i) = Lr at hxN hli ⊢
    generalize ground.bpow (radiusD P) (d - i) = Yr at hxN ⊢
    generalize ground.bpow (BPair.ofNat l) d = Ld at hli ⊢
    refine ground.leB_trans (ground.leB_mulR (ground.unitLeMul hA hLi) hxN) ?_
    refine ground.leB_congr_left (BPair.oneValue_symm (ground.polEqB [A, Li, Xi, Lr, Yr]
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))
          (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 4)))))
        (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 4)))
          (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 3))))
        (by decide +kernel))) ?_
    exact ground.leB_congr_right (BPair.mul_congr (BPair.oneValue_refl _) hli) (ground.leB_refl _)
  have hSS : ground.famFold BPair.add BPair.unit
      (fun k => mag (ground.getAt BPair.unit (poly.vnorm P) k)
        * ground.bpow (BPair.ofNat l) k) (List.range d) * ground.bpow (radiusN P) d
    ≤ ground.famFold BPair.add BPair.unit
      (fun i => mag (ground.getAt BPair.unit (poly.vnorm P) i)
        * ground.bpow (radiusN P) i
        * ground.bpow (radiusD P) (d - i)) (List.range d) * ground.bpow (BPair.ofNat l) d := by
    refine ground.leB_congr (BPair.oneValue_symm (ground.foldB_mul_right (ground.bpow (radiusN P) d)
        (fun k => mag (ground.getAt BPair.unit (poly.vnorm P) k)
          * ground.bpow (BPair.ofNat l) k) (List.range d)))
      (BPair.oneValue_symm (ground.foldB_mul_right (ground.bpow (BPair.ofNat l) d)
        (fun i => mag (ground.getAt BPair.unit (poly.vnorm P) i)
          * ground.bpow (radiusN P) i
          * ground.bpow (radiusD P) (d - i)) (List.range d))) ?_
    exact leB_famFold_range (List.range d)
      (fun i hi => hterm i (ground.ltOfCountRange hi))
  refine ground.leB_trans ?_ (ground.leB_mulL (ground.unitLeBpow (unitLe_radiusN P) d) hrev)
  generalize ground.famFold BPair.add BPair.unit
      (fun k => mag (ground.getAt BPair.unit (poly.vnorm P) k)
        * ground.bpow (BPair.ofNat l) k) (List.range d) = Sl at hSS ⊢
  generalize ground.famFold BPair.add BPair.unit
      (fun i => mag (ground.getAt BPair.unit (poly.vnorm P) i)
        * ground.bpow (radiusN P) i
        * ground.bpow (radiusD P) (d - i)) (List.range d) = Sx at hSS ⊢
  generalize radiusD P = A
  generalize ground.bpow (BPair.ofNat l) d = Ld at hSS ⊢
  generalize ground.bpow (radiusN P) d = Xd at hSS ⊢
  refine ground.leB_congr (BPair.oneValue_symm (BPair.oneValue_of_eq (BPair.right_distrib _ _ _)))
    (BPair.oneValue_symm (BPair.oneValue_of_eq (BPair.right_distrib _ _ _))) ?_
  refine ground.leB_add (ground.leB_congr_left (BPair.oneValue_of_eq (BPair.mul_right_comm A Ld Xd))
    (ground.leB_refl _)) ?_
  rw [BPair.swap_mul, BPair.swap_mul]
  exact ground.leB_swap hSS

/-- The coefficient fold at the memberwise swap, the magnitudes
unchanged. -/
private theorem map_neg_mag : ∀ l : Poly,
    (poly.neg l).map mag = l.map mag
  | [] => rfl
  | c :: t => by
    show mag c.swap :: (poly.neg t).map mag = mag c :: t.map mag
    rw [mag_swap c, map_neg_mag t]

/-- The coefficient fold at the memberwise swap. -/
theorem magFold_neg (P : Poly) (n d : BPair) :
    magFold (poly.neg P) n d = magFold P n d := by
  unfold magFold
  rw [poly.vnorm_neg P, map_neg_mag (poly.vnorm P)]

/-- The coefficient fold at the cleared list: the bound's first
member takes the clearing and the fold takes the clearing's whole
power, `Σ |p_k c^(K−k)| (Nc)^k D^(K−k) = c^K Σ |p_k| N^k D^(K−k)`
at `K` the representative's top key. -/
theorem magFold_clearVar (p : Poly) (c : Pos) (N D : BPair) :
    (magFold (poly.clearVar (poly.vnorm p) c ((poly.vnorm p).length - 1))
        (N * BPair.ofPos c) D).oneValue
      (ground.bpow (BPair.ofPos c) ((poly.vnorm p).length - 1)
        * magFold p N D) := by
  have hmagc : mag (BPair.ofPos c) = BPair.ofPos c :=
    mag_unitLe (ground.leB_of_lt (ground.unitLtOfPos c))
  refine BPair.oneValue_trans
    (magFold_read
      (poly.clearVar (poly.vnorm p) c ((poly.vnorm p).length - 1))
      (N * BPair.ofPos c) D) ?_
  rw [poly.vnorm_clearVar p c ((poly.vnorm p).length - 1),
    poly.length_clearVar (poly.vnorm p) c ((poly.vnorm p).length - 1)]
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_trans
      (ground.foldB_mul_left
        (ground.bpow (BPair.ofPos c) ((poly.vnorm p).length - 1))
        (fun i => mag (ground.getAt BPair.unit (poly.vnorm p) i)
          * ground.bpow N i
          * ground.bpow D ((poly.vnorm p).length - 1 - i))
        (List.range (poly.vnorm p).length))
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (magFold_read p N D))))
  refine ground.foldB_congr_members _ _
    (List.range (poly.vnorm p).length) ?_
  intro i hi
  have hik : i ≤ (poly.vnorm p).length - 1 :=
    Nat.sub_le_sub_right (ground.ltOfMem hi) 1
  have hm : (mag (ground.getAt BPair.unit
      (poly.clearVar (poly.vnorm p) c
        ((poly.vnorm p).length - 1)) i)).oneValue
      (mag (ground.getAt BPair.unit (poly.vnorm p) i)
        * ground.bpow (BPair.ofPos c)
          ((poly.vnorm p).length - 1 - i)) :=
    BPair.oneValue_trans
      (mag_congr (poly.getAt_clearVar (poly.vnorm p) c
        ((poly.vnorm p).length - 1) i))
      (BPair.oneValue_trans (mag_congr (BPair.norm_oneValue _))
        (BPair.oneValue_trans
          (mag_mul (ground.getAt BPair.unit (poly.vnorm p) i)
            (ground.bpow (BPair.ofPos c)
              ((poly.vnorm p).length - 1 - i)))
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_trans
              (mag_bpow (BPair.ofPos c)
                ((poly.vnorm p).length - 1 - i))
              (BPair.oneValue_of_eq
                (congrArg (fun z => ground.bpow z
                  ((poly.vnorm p).length - 1 - i)) hmagc))))))
  have hC : (ground.bpow (BPair.ofPos c)
      ((poly.vnorm p).length - 1)).oneValue
      (ground.bpow (BPair.ofPos c) ((poly.vnorm p).length - 1 - i)
        * ground.bpow (BPair.ofPos c) i) :=
    BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (congrArg (ground.bpow (BPair.ofPos c))
          (ground.subAdd hik).symm))
      (ground.bpow_add (BPair.ofPos c)
        ((poly.vnorm p).length - 1 - i) i)
  have hEq : mag (ground.getAt BPair.unit (poly.vnorm p) i)
        * ground.bpow (BPair.ofPos c) ((poly.vnorm p).length - 1 - i)
        * (ground.bpow N i * ground.bpow (BPair.ofPos c) i)
        * ground.bpow D ((poly.vnorm p).length - 1 - i)
      = ground.bpow (BPair.ofPos c) ((poly.vnorm p).length - 1 - i)
        * ground.bpow (BPair.ofPos c) i
        * (mag (ground.getAt BPair.unit (poly.vnorm p) i)
          * ground.bpow N i
          * ground.bpow D ((poly.vnorm p).length - 1 - i)) := by
    rw [BPair.mul_mul_mul_comm
        (mag (ground.getAt BPair.unit (poly.vnorm p) i))
        (ground.bpow (BPair.ofPos c) ((poly.vnorm p).length - 1 - i))
        (ground.bpow N i) (ground.bpow (BPair.ofPos c) i),
      BPair.mul_assoc
        (mag (ground.getAt BPair.unit (poly.vnorm p) i)
          * ground.bpow N i)
        (ground.bpow (BPair.ofPos c) ((poly.vnorm p).length - 1 - i)
          * ground.bpow (BPair.ofPos c) i)
        (ground.bpow D ((poly.vnorm p).length - 1 - i)),
      BPair.mul_left_comm
        (mag (ground.getAt BPair.unit (poly.vnorm p) i)
          * ground.bpow N i)
        (ground.bpow (BPair.ofPos c) ((poly.vnorm p).length - 1 - i)
          * ground.bpow (BPair.ofPos c) i)
        (ground.bpow D ((poly.vnorm p).length - 1 - i))]
  refine BPair.oneValue_trans
    (BPair.mul_congr
      (BPair.mul_congr hm (ground.bpow_mul N (BPair.ofPos c) i))
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq hEq) ?_
  exact BPair.mul_congr (BPair.oneValue_symm hC) (BPair.oneValue_refl _)

/-- The height's fold reads through the memberwise swap, one
magnitude per step. -/
private theorem heightGo_neg : ∀ (l : Poly) (acc : BPair),
    (poly.neg l).foldl
        (fun h c => if h < mag c then mag c else h) acc
      = l.foldl (fun h c => if h < mag c then mag c else h) acc
  | [], _ => rfl
  | c :: t, acc => by
    show (poly.neg t).foldl
        (fun h c => if h < mag c then mag c else h)
        (if acc < mag c.swap then mag c.swap else acc)
      = t.foldl (fun h c => if h < mag c then mag c else h)
        (if acc < mag c then mag c else acc)
    rw [mag_swap c, heightGo_neg t]

/-- The height at the memberwise swap, the magnitudes unchanged. -/
theorem height_neg (P : Poly) : height (poly.neg P) = height P := by
  unfold height
  rw [poly.vnorm_neg P, heightGo_neg (poly.vnorm P)]

/-- The radius pair's second member at the memberwise swap. -/
theorem radiusD_neg (P : Poly) : radiusD (poly.neg P) = radiusD P := by
  unfold radiusD
  rw [poly.vnorm_neg P, poly.top_neg (poly.vnorm P), mag_swap]

/-- The radius pair's first member at the memberwise swap. -/
theorem radiusN_neg (P : Poly) : radiusN (poly.neg P) = radiusN P := by
  unfold radiusN
  rw [poly.vnorm_neg P, poly.top_neg (poly.vnorm P), mag_swap,
    height_neg P]

/-! `thm:windowsep`'s leading-term clause: beyond the radius the
leading term dominates.  At a point `x` of magnitude `y` at or
beyond the radius pair `B = [c + H : c]` — `c` the leading
coefficient's magnitude, `H` the height — the geometric telescope
`(y - 1) Σ_{i<k} y^i + 1 = y^k` at the top key `k` prices the tail's
cap `H Σ_{i<k} y^i` below `c y^k` at the radius' read
`c (y - 1) ≥ H`, so the tail joins the leading term at a magnitude
below the term's and the evaluation reads the term's own side. -/

/-- A leading term off the sum's unit carries a top off it. -/
private theorem top_off_of_lead {q : Poly} {x : BPair} {n : Nat}
    (hl : BPair.unit < top q * ground.bpow x n) :
    ¬ (top q).oneValue BPair.unit := fun h =>
  ground.leB_not_lt (ground.leB_refl BPair.unit)
    (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      ((BPair.mul_unit_iff (top q) (ground.bpow x n)).mpr (Or.inl h)) hl)

/-- The telescope's price at the balance carrier: with the scale's
product against the leading magnitude at or above that magnitude
joined to the height, and the telescope `1 + y S ≍ S + P` at the
key range's fold `S` and the top key's power `P`, the height's fold
sits below the leading magnitude's power, the leading magnitude
itself the joined margin. -/
private theorem lead_arith {c H y S P : BPair}
    (hSu : BPair.unit ≤ S) (hcu : BPair.unit ≤ c)
    (hyu : BPair.unit ≤ y)
    (hgeo : (BPair.ofPos Pos.one + y * S).oneValue (S + P))
    (hrad : c + H ≤ y * c) : c + H * S ≤ c * P := by
  have hmulS : (c + H) * S ≤ (y * c) * S :=
    ground.leB_mul_mono hSu (ground.unitLeMul hyu hcu) hrad
      (ground.leB_refl S)
  have hdist : c * S + H * S ≤ c * (y * S) := by
    rw [← BPair.right_distrib]
    refine ground.leB_congr_right ?_ hmulS
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_comm y c, BPair.mul_assoc]
  have hgeoc : (c * BPair.ofPos Pos.one + c * (y * S)).oneValue
      (c * S + c * P) := by
    rw [← BPair.left_distrib, ← BPair.left_distrib]
    exact BPair.mul_congr (BPair.oneValue_refl c) hgeo
  have hadd : c * BPair.ofPos Pos.one + (c * S + H * S)
      ≤ c * BPair.ofPos Pos.one + c * (y * S) :=
    ground.leB_add (ground.leB_refl _) hdist
  have hstep : c * S + (c * BPair.ofPos Pos.one + H * S)
      ≤ c * S + c * P := by
    refine ground.leB_congr ?_ hgeoc hadd
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.add_assoc, ← BPair.add_assoc,
      BPair.add_comm (c * BPair.ofPos Pos.one) (c * S)]
  refine ground.leB_congr_left ?_ (ground.leB_cancelL hstep)
  exact BPair.add_congr (BPair.mul_one_read c) (BPair.oneValue_refl (H * S))

/-- The leading term's side at a carrier whose length reads its top
key's successor: the tail's magnitude sits below the leading term,
so the evaluation joins the term above the sum's unit. -/
private theorem lead_core (q : Poly) (x H : BPair) (n : Nat)
    (hq : q.length = n + 1) (hHu : BPair.unit ≤ H)
    (hH : ∀ z ∈ q, mag z ≤ H)
    (hx : (mag (top q) + H).norm ≤ mag x * mag (top q))
    (hl : BPair.unit < top q * ground.bpow x n) :
    BPair.unit < poly.eval q x := by
  have hyu : BPair.unit ≤ mag x := unitLe_mag x
  have hcu : BPair.unit ≤ mag (top q) := unitLe_mag (top q)
  have hSu : BPair.unit ≤ ground.famFold BPair.add BPair.unit
      (fun i => ground.bpow (mag x) i) (List.range n) :=
    ground.foldB_nonneg _ (List.range n) (fun i _ => ground.unitLeBpow hyu i)
  have hgetn : ground.getAt BPair.unit q n = top q :=
    (poly.topO_getAt ground.bpairOps q n hq).symm
  have heval : (poly.eval q x).oneValue
      (ground.famFold BPair.add BPair.unit
          (fun k => ground.getAt BPair.unit q k * ground.bpow x k)
          (List.range n)
        + top q * ground.bpow x n) := by
    have hfam := poly.eval_famFold q x
    rw [hq] at hfam
    refine BPair.oneValue_trans hfam ?_
    rw [← hgetn]
    exact ground.foldB_range_snoc
      (fun k => ground.getAt BPair.unit q k * ground.bpow x k) n
  have hcap : ground.famFold BPair.add BPair.unit
      (fun i => mag (ground.getAt BPair.unit q i * ground.bpow x i))
      (List.range n)
    ≤ ground.famFold BPair.add BPair.unit
      (fun i => H * ground.bpow (mag x) i) (List.range n) := by
    refine ground.bsum_le _ _ (List.range n) (fun i hi => ?_)
    have hin : i < n := ground.ltOfMem hi
    have hmem : ground.getAt BPair.unit q i ∈ q :=
      ground.mem_getAt BPair.unit q i
        (by rw [hq]; exact Nat.lt_succ_of_lt hin)
    refine ground.leB_congr_left
      (BPair.oneValue_symm (BPair.oneValue_trans
        (mag_mul (ground.getAt BPair.unit q i) (ground.bpow x i))
        (BPair.mul_congr (BPair.oneValue_refl _) (mag_bpow x i)))) ?_
    exact ground.leB_mul_mono (ground.unitLeBpow hyu i) hHu (hH _ hmem)
      (ground.leB_refl _)
  have hTmag : mag (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit q k * ground.bpow x k)
        (List.range n))
      ≤ H * ground.famFold BPair.add BPair.unit
          (fun i => ground.bpow (mag x) i) (List.range n) :=
    ground.leB_congr_right
      (ground.foldB_mul_left H (fun i => ground.bpow (mag x) i)
        (List.range n))
      (ground.leB_trans
        (mag_famFold_le
          (fun k => ground.getAt BPair.unit q k * ground.bpow x k)
          (List.range n))
        hcap)
  have hshift : (ground.famFold BPair.add BPair.unit
      (fun j => ground.bpow (mag x) (j + 1)) (List.range n)).oneValue
      (mag x * ground.famFold BPair.add BPair.unit
        (fun i => ground.bpow (mag x) i) (List.range n)) :=
    BPair.oneValue_trans
      (ground.foldB_congr_members
        (fun j => ground.bpow (mag x) (j + 1))
        (fun j => mag x * ground.bpow (mag x) j) (List.range n)
        (fun _ _ => BPair.norm_oneValue _))
      (ground.foldB_mul_left (mag x) (fun j => ground.bpow (mag x) j)
        (List.range n))
  have hgeo : (BPair.ofPos Pos.one
      + mag x * ground.famFold BPair.add BPair.unit
          (fun i => ground.bpow (mag x) i) (List.range n)).oneValue
      (ground.famFold BPair.add BPair.unit
          (fun i => ground.bpow (mag x) i) (List.range n)
        + ground.bpow (mag x) n) :=
    BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (BPair.ofPos Pos.one))
        (BPair.oneValue_symm hshift))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (ground.foldB_range_cons
            (fun i => ground.bpow (mag x) i) n).symm)
        (ground.foldB_range_snoc (fun i => ground.bpow (mag x) i) n))
  have hprice : mag (top q)
      + H * ground.famFold BPair.add BPair.unit
          (fun i => ground.bpow (mag x) i) (List.range n)
      ≤ mag (top q) * ground.bpow (mag x) n :=
    lead_arith hSu hcu hyu hgeo
      (ground.leB_congr_left (BPair.norm_oneValue (mag (top q) + H)) hx)
  have hLeq : mag (top q * ground.bpow x n) = top q * ground.bpow x n :=
    mag_unitLe (ground.leB_of_lt hl)
  have hLc : (mag (top q) * ground.bpow (mag x) n).oneValue
      (top q * ground.bpow x n) := by
    rw [← hLeq]
    exact BPair.oneValue_symm
      (BPair.oneValue_trans (mag_mul (top q) (ground.bpow x n))
        (BPair.mul_congr (BPair.oneValue_refl (mag (top q)))
          (mag_bpow x n)))
  have hTL : mag (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit q k * ground.bpow x k)
        (List.range n))
      + mag (top q) ≤ top q * ground.bpow x n :=
    ground.leB_congr_right hLc
      (ground.leB_trans
        (ground.leB_congr_right
          (BPair.oneValue_of_eq
            (BPair.add_comm
              (H * ground.famFold BPair.add BPair.unit
                (fun i => ground.bpow (mag x) i) (List.range n))
              (mag (top q))))
          (ground.leB_add hTmag (ground.leB_refl (mag (top q)))))
        hprice)
  have hcpos : BPair.unit < mag (top q) :=
    ground.ltOfLeOff hcu (fun h => top_off_of_lead hl (unit_of_mag h))
  exact BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm
      (BPair.oneValue_trans heval
        (BPair.oneValue_of_eq
          (BPair.add_comm
            (ground.famFold BPair.add BPair.unit
              (fun k => ground.getAt BPair.unit q k * ground.bpow x k)
              (List.range n))
            (top q * ground.bpow x n)))))
    (ground.unitLt_of_swap_lt
      (ground.leB_ltB_trans (swap_le_mag _)
        (ground.ltB_trans_le (ground.ltB_addPos hcpos) hTL)))

/-- Beyond the radius the leading term dominates, on its upper side: at a point whose magnitude
clears the radius pair, a leading term above the sum's unit puts the evaluation above it, the tail
joined at a magnitude below the term's. -/
theorem lead_upper (p : Poly) (x : BPair)
    (hx : radiusN p ≤ mag x * radiusD p)
    (hl : BPair.unit < top (poly.vnorm p) * ground.bpow x ((poly.vnorm p).length - 1)) :
    BPair.unit < poly.eval p x :=
  BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (poly.eval_congr (poly.vnorm_ov p) x)
    (lead_core (poly.vnorm p) x (height p) ((poly.vnorm p).length - 1)
      (poly.len_of_top_off (top_off_of_lead hl)) (unitLe_height p)
      (fun _ hz => mag_le_height hz) hx hl)

/-- The lower side's read, the memberwise swap's. -/
theorem lead_lower (p : Poly) (x : BPair)
    (hx : radiusN p ≤ mag x * radiusD p)
    (hl : top (poly.vnorm p) * ground.bpow x ((poly.vnorm p).length - 1) < BPair.unit) :
    poly.eval p x < BPair.unit := by
  have hxn : radiusN (poly.neg p) ≤ mag x * radiusD (poly.neg p) := by
    rw [radiusN_neg, radiusD_neg]
    exact hx
  have hln : BPair.unit < top (poly.vnorm (poly.neg p))
      * ground.bpow x ((poly.vnorm (poly.neg p)).length - 1) := by
    rw [poly.vnorm_neg, poly.top_neg, poly.length_neg, BPair.swap_mul]
    exact ground.ltB_swap hl
  have hup := lead_upper (poly.neg p) x hxn hln
  rw [poly.eval_neg] at hup
  exact ground.ltB_swap hup

/-- The coefficient fold at every representative. -/
theorem magFold_congr {P Q : Poly} (h : poly.oneValue P Q)
    (n d : BPair) : magFold P n d = magFold Q n d := by
  unfold magFold
  rw [poly.vnorm_congr h]

/-- The width read against its descent spelling at a square shift
frame: the resultant at the walk with the Bezout row's entries the
erased frames' walks, each comparison moved across the value. -/
private theorem sepRead_walk (S : Poly) (wn wd : Pos)
    (hsq : elim.rowsLen
      (elim.shiftMat (poly.vnorm S) (deriv (poly.vnorm S))).length
      (elim.shiftMat (poly.vnorm S) (deriv (poly.vnorm S)))) :
    sepRead S wn wd ↔
    ((elim.detD (elim.shiftMat (poly.vnorm S)
        (deriv (poly.vnorm S)))).offUnit
     ∧ (BPair.ofNat 2 * BPair.ofPos wn
           * (curvFold S (radiusN S) (radiusD S)
             * magFold (elim.bezoutBD (poly.vnorm S)
                 (deriv (poly.vnorm S)))
                 (radiusN S) (radiusD S)))
         ≤ (BPair.ofPos wd
           * (mag (elim.detD (elim.shiftMat (poly.vnorm S)
                (deriv (poly.vnorm S))))
             * bpow (radiusD S)
                 ((poly.vnorm S).length - 3
                  + ((poly.vnorm (elim.bezoutBD (poly.vnorm S)
                       (deriv (poly.vnorm S)))).length - 1))))
     ∧ BPair.ofNat 2 * BPair.ofPos wn ≤ BPair.ofPos wd) := by
  have hR : (elim.detD (elim.shiftMat (poly.vnorm S)
        (deriv (poly.vnorm S)))).oneValue
      (resultant (poly.vnorm S) (deriv (poly.vnorm S))) :=
    BPair.oneValue_refl _
  have hB : poly.oneValue
      (elim.bezoutBD (poly.vnorm S) (deriv (poly.vnorm S)))
      (elim.bezoutB (poly.vnorm S) (deriv (poly.vnorm S))) :=
    elim.bezoutBD_eq _ _ hsq
  have e1 : magFold (elim.bezoutB (poly.vnorm S) (deriv (poly.vnorm S)))
      (radiusN S) (radiusD S)
      = magFold (elim.bezoutBD (poly.vnorm S) (deriv (poly.vnorm S)))
        (radiusN S) (radiusD S) :=
    magFold_congr (poly.oneValue_symm hB) _ _
  have e2 : (poly.vnorm (elim.bezoutB (poly.vnorm S)
        (deriv (poly.vnorm S)))).length
      = (poly.vnorm (elim.bezoutBD (poly.vnorm S)
        (deriv (poly.vnorm S)))).length :=
    congrArg List.length (poly.vnorm_congr (poly.oneValue_symm hB))
  constructor
  · intro x
    refine ⟨fun hu => x.1 (BPair.oneValue_trans
        (BPair.oneValue_symm hR) hu), ?_, x.2.2⟩
    have x2 := x.2.1
    rw [e1, e2] at x2
    exact ground.leB_congr_right
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_symm (mag_congr hR))
          (BPair.oneValue_refl _))) x2
  · intro x
    refine ⟨fun hu => x.1 (BPair.oneValue_trans hR hu), ?_, x.2.2⟩
    have x2 := x.2.1
    rw [e1, e2]
    exact ground.leB_congr_right
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (mag_congr hR) (BPair.oneValue_refl _))) x2

instance instWindowsep1 (S : Poly) (wn wd : Pos) : Decidable (sepRead S wn wd) :=
  let T := poly.vnorm S
  let M := elim.shiftMat T (deriv T)
  match elim.decRowsLen M.length M with
  | isTrue hsq =>
    let W := elim.detD M
    let B := elim.bezoutBD T (deriv T)
    decidable_of_iff
      (W.offUnit
       ∧ (BPair.ofNat 2 * BPair.ofPos wn
             * (curvFold S (radiusN S) (radiusD S)
               * magFold B (radiusN S) (radiusD S)))
           ≤ (BPair.ofPos wd
             * (mag W * bpow (radiusD S)
                 (T.length - 3 + ((poly.vnorm B).length - 1))))
       ∧ BPair.ofNat 2 * BPair.ofPos wn ≤ BPair.ofPos wd)
      (sepRead_walk S wn wd hsq).symm
  | isFalse _ => inferInstanceAs (Decidable (¬ _ ∧ _ ∧ _))

/-! The division descent, `lem:stagesplit`'s certificate tier's
producer: the extended primitive pseudo-remainder walk and the
cofactors' exact pseudo-divisions. -/

set_option genInjectivity false in
/-- The descent's produced data: the divisor at its cleared
below-top list with the stated positive top, the two cofactors at
their clearing multipliers, and the Bézout witness — the tuple
`stagesplit.gcdRead` reads whole. -/
structure GcdData where
  g : Poly
  top : Pos
  A : Poly
  B : Poly
  u : Poly
  v : Poly
  cA : Pos
  cB : Pos
  c : BPair

/-! The descent's own kit: the constant scaling and key shift, the
content at the coefficients' margins with its exact division
(`ground.BPair.listContent`, `BPair.listPrim`), the count's power,
and the pseudo-division's accumulating descent, the inputs at the
value's representative (`poly.vnorm`). -/


private def pdivGo : Nat → Poly → Poly → Poly → Nat →
    Poly × Poly × Nat
  | 0, _, r, q, k => (q, r, k)
  | fuel + 1, D, r, q, k =>
    if r.length < D.length then (q, r, k)
    else
      let c := poly.top r
      let j := r.length - D.length
      pdivGo fuel D
        (poly.vnorm (poly.add (poly.scaleP (poly.top D) r)
          (poly.neg (poly.scaleP c (poly.shiftUp j D)))))
        (poly.pnorm (poly.add (poly.scaleP (poly.top D) q)
          (poly.shiftUp j [c])))
        (k + 1)

private def pdiv (D P : Poly) : Poly × Poly × Nat :=
  pdivGo (P.length + 1) D (poly.vnorm P) [] 0

set_option genInjectivity false in
/-- One walk row: the remainder, the two multipliers riding it, and
the row's own clearing, at `u P + v Q = m r`. -/
private structure Row where
  r : Poly
  u : Poly
  v : Poly
  m : BPair

private def walkGo : Nat → Row → Row → Row
  | 0, R0, _ => R0
  | fuel + 1, R0, R1 =>
    match R1.r with
    | [] => R0
    | c1 :: t1 =>
      let dv := pdiv (c1 :: t1) R0.r
      let em := (bpow (poly.top (c1 :: t1)) dv.2.2 * R1.m).norm
      let mm := (R0.m * R1.m).norm
      let kap := BPair.listContent dv.2.1
      walkGo fuel R1
        ⟨BPair.listPrim kap dv.2.1,
         poly.pnorm (poly.add (poly.scaleP em R0.u)
           (poly.neg (poly.scaleP R0.m (poly.mul dv.1 R1.u)))),
         poly.pnorm (poly.add (poly.scaleP em R0.v)
           (poly.neg (poly.scaleP R0.m (poly.mul dv.1 R1.v)))),
         if kap == 0 then mm else (mm * BPair.ofNat kap).norm⟩

private def signFix (R : Row) : Row :=
  if decide (poly.top R.r < BPair.unit)
  then ⟨poly.neg R.r, R.u, R.v, R.m.swap⟩
  else R

private def contentFix (R : Row) : Row :=
  let k := BPair.listContent R.r
  if k == 0 then R
  else ⟨BPair.listPrim k R.r, R.u, R.v, (R.m * BPair.ofNat k).norm⟩

/-- The division descent at the integer representatives: the
extended primitive pseudo-remainder walk, the contents stripped
per step at the coefficients' margins, the Bézout rows riding the
walk at their own multipliers, the output the certificate's
tuple. -/
def gcdD (P Q : Poly) : GcdData :=
  let p0 := poly.vnorm P
  let q0 := poly.vnorm Q
  let fuel := p0.length + q0.length + 2
  let ans := contentFix (signFix
    (if q0.length ≤ p0.length
     then walkGo fuel ⟨p0, poly.one, [], BPair.ofPos .one⟩
       ⟨q0, [], poly.one, BPair.ofPos .one⟩
     else walkGo fuel ⟨q0, [], poly.one, BPair.ofPos .one⟩
       ⟨p0, poly.one, [], BPair.ofPos .one⟩))
  let tp := posOfSucc (BPair.marginN (poly.top ans.r) - 1)
  let g := ans.r.dropLast
  let dA := pdiv (poly.topped g tp) P
  let dB := pdiv (poly.topped g tp) Q
  ⟨g, tp, dA.1, dB.1, ans.u, ans.v,
   Pos.powC tp dA.2.2, Pos.powC tp dB.2.2, ans.m⟩

/-! The coefficient fold at a stated power: `Σ_{i≤K} |p_i| n^i d^(K-i)`,
the magnitudes at every key through the power with the vacant keys
at the sum's unit, cleared at `d^K` (`foldK`, its family instance
`foldAt`); it recurs on the power (`foldAt_succ`), reads the
coefficient fold at the polynomial's own top with the further
powers' clearing (`foldK_magFold`, `magFold` at `Σ_i |s_i| n^i
d^(k-i)`, the fold's read at a further power its computing form),
and caps a cleared evaluation at a point inside the bound at the
bound's read (`foldK_cap`, the evaluations-at-magnitude-below-a-bound
clause), with the sum's and the rescaling's reads and the
congruence. -/

/-- The fold's step, the running pair at one coefficient: the first
member's bound multiple joined to the coefficient's multiple of the
second, and the second's clearing multiple. -/
private def stepAt (n d : BPair) (s : BPair × BPair) (c : BPair) :
    BPair × BPair :=
  (((s.1 * n).norm + (c * s.2).norm).norm, (s.2 * d).norm)

/-- The running pair's regrouping, one collected display at seven
pairs. -/
private theorem lin_shuffle (a n c b d N F : BPair) :
    (a * (n * N) + b * (c * N + d * F)).oneValue
      ((a * n + c * b) * N + b * d * F) :=
  polEqB [a, n, c, b, d, N, F]
    (Pol.add (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1) (Mon.var 5))))
      (Pol.mul (Pol.mon (Mon.var 3))
        (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 5)))
          (Pol.mon (Mon.mul (Mon.var 4) (Mon.var 6))))))
    (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 1)))
        (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 3)))) (Pol.mon (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 4)) (Mon.var 6))))
    (by decide +kernel)

/-- A sum's multiple joined to a multiple of a sum, regrouped at the
two summands' own pairs. -/
private theorem distrib_shuffle (x y N d u v : BPair) :
    ((x + y) * N + d * (u + v)).oneValue (x * N + d * u + (y * N + d * v)) :=
  polEqB [x, y, N, d, u, v]
    (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))
        (Pol.mon (Mon.var 2)))
      (Pol.mul (Pol.mon (Mon.var 3))
        (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.var 5)))))
    (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 2)))
        (Pol.mon (Mon.mul (Mon.var 3) (Mon.var 4))))
      (Pol.add (Pol.mon (Mon.mul (Mon.var 1) (Mon.var 2)))
        (Pol.mon (Mon.mul (Mon.var 3) (Mon.var 5)))))
    (by decide +kernel)

/-- A scale across the recursion's two summands. -/
private theorem scale_shuffle (c x N d F : BPair) :
    (c * x * N + d * (c * F)).oneValue (c * (x * N + d * F)) :=
  polEqB [c, x, N, d, F]
    (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.var 3) (Mon.mul (Mon.var 0) (Mon.var 4)))))
    (Pol.mul (Pol.mon (Mon.var 0))
      (Pol.add (Pol.mon (Mon.mul (Mon.var 1) (Mon.var 2)))
        (Pol.mon (Mon.mul (Mon.var 3) (Mon.var 4)))))
    (by decide +kernel)

/-- The fold from a stated running pair is linear in it: the first
member's power multiple joined to the second member's multiple of
the fold from the units. -/
private theorem foldFrom_lin (n d : BPair) : ∀ (m : List BPair) (a b : BPair),
    ((m.foldl (stepAt n d) (a, b)).1).oneValue
      (a * bpow n m.length
        + b * (m.foldl (stepAt n d) (BPair.unit, BPair.ofPos .one)).1)
  | [], a, b => by
    show a.oneValue (a * BPair.ofPos .one + b * BPair.unit)
    exact BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_one_read a) (BPair.mul_unit b))
      (BPair.add_unit a))
  | c :: m, a, b => by
    show ((m.foldl (stepAt n d) (stepAt n d (a, b) c)).1).oneValue
      (a * bpow n (m.length + 1)
        + b * (m.foldl (stepAt n d) (stepAt n d (BPair.unit, BPair.ofPos .one) c)).1)
    have hA : (((a * n).norm + (c * b).norm).norm).oneValue (a * n + c * b) :=
      BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.add_congr (BPair.norm_oneValue _) (BPair.norm_oneValue _))
    have hB : ((b * d).norm).oneValue (b * d) := BPair.norm_oneValue _
    have hA0 : (((BPair.unit * n).norm + (c * BPair.ofPos .one).norm).norm).oneValue c :=
      BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_trans
          (BPair.add_congr
            (BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.unit_mul n))
            (BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_one_read c)))
          (BPair.unit_add c))
    have hB0 : ((BPair.ofPos .one * d).norm).oneValue d :=
      BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ d))
          (BPair.mul_one_read d))
    refine BPair.oneValue_trans (foldFrom_lin n d m _ _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_congr_left hA)
        (BPair.mul_congr_left hB)) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl a) (bpow_succ_read n m.length))
        (BPair.mul_congr (BPair.oneValue_refl b)
          (BPair.oneValue_trans (foldFrom_lin n d m _ _)
            (BPair.add_congr (BPair.mul_congr_left hA0)
              (BPair.mul_congr_left hB0))))) ?_
    exact lin_shuffle a n c b d _ _

/-- A list grown by one member at its top folds to the member's power
joined to the bound's second datum's multiple of the fold below. -/
private theorem foldPow_snoc (l : List BPair) (x n d : BPair) :
    (foldPow (l ++ [x]) n d).oneValue (x * bpow n l.length + d * foldPow l n d) := by
  show ((((l ++ [x]).reverse).foldl (stepAt n d) (BPair.unit, BPair.ofPos .one)).1).oneValue
    (x * bpow n l.length + d * ((l.reverse.foldl (stepAt n d) (BPair.unit, BPair.ofPos .one)).1))
  rw [reverse_append l [x]]
  show ((l.reverse.foldl (stepAt n d) (stepAt n d (BPair.unit, BPair.ofPos .one) x)).1).oneValue _
  refine BPair.oneValue_trans (foldFrom_lin n d l.reverse _ _) ?_
  rw [length_reverse l]
  refine BPair.add_congr (BPair.mul_congr_left ?_) (BPair.mul_congr_left ?_)
  · exact BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.unit_mul n))
          (BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_one_read x)))
        (BPair.unit_add x))
  · exact BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ d))
        (BPair.mul_one_read d))

/-- A coefficient family's fold at a stated power: `Σ_{i≤K} f_i n^i d^(K-i)`,
the family's reads at every key through the power, cleared at
`d^K`. -/
def foldAt (f : Nat → BPair) (n d : BPair) (K : Nat) : BPair :=
  foldPow ((List.range (K + 1)).map f) n d

/-- The fold at the power nought is the family's read at the
constant key. -/
theorem foldAt_zero (f : Nat → BPair) (n d : BPair) :
    (foldAt f n d 0).oneValue (f 0) := by
  show ((([f 0]).reverse.foldl (stepAt n d)
      (BPair.unit, BPair.ofPos .one)).1).oneValue _
  show ((((BPair.unit * n).norm + (f 0 * BPair.ofPos .one).norm).norm)).oneValue _
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.unit_mul n))
        (BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_one_read _)))
      (BPair.unit_add _))

/-- The fold recurs on the power: the top key's read at the bound's
power joined to the second datum's multiple of the fold below. -/
theorem foldAt_succ (f : Nat → BPair) (n d : BPair) (K : Nat) :
    (foldAt f n d (K + 1)).oneValue
      (f (K + 1) * bpow n (K + 1) + d * foldAt f n d K) := by
  show (foldPow ((List.range (K + 1 + 1)).map f) n d).oneValue _
  rw [range_succ (K + 1), map_append]
  refine BPair.oneValue_trans (foldPow_snoc _ _ n d) ?_
  rw [length_map, length_range]
  exact BPair.oneValue_refl _

/-- The fold's family read: the family's reads at the powers over the
keys through the power, `thm:windowsep`'s coefficient fold at a
stated family. -/
theorem foldAt_read (f : Nat → BPair) (n d : BPair) (K : Nat) :
    (foldAt f n d K).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun i => f i * bpow n i * bpow d (K - i)) (List.range (K + 1))) := by
  refine BPair.oneValue_trans (foldPow_read _ n d) ?_
  rw [length_map, length_range]
  refine ground.famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit
    BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2) _ _
    (List.range (K + 1)) (fun i hi => ?_)
  have hlt : i < K + 1 := by
    have h := countOf_range i (K + 1)
    cases hd : decide (i < K + 1) with
    | true => exact of_decide_eq_true hd
    | false =>
      rw [if_neg (of_decide_eq_false hd)] at h
      rw [h] at hi
      exact absurd hi (Nat.lt_irrefl 0)
  rw [getAt_map_range BPair.unit f (K + 1) i, if_pos hlt]
  exact BPair.oneValue_refl _

/-- The fold passes a pointwise one-value read of the family. -/
theorem foldAt_congr {f g : Nat → BPair} (h : ∀ i, (f i).oneValue (g i))
    (n d : BPair) : ∀ K : Nat, (foldAt f n d K).oneValue (foldAt g n d K)
  | 0 => BPair.oneValue_trans (foldAt_zero f n d)
      (BPair.oneValue_trans (h 0) (BPair.oneValue_symm (foldAt_zero g n d)))
  | K + 1 => BPair.oneValue_trans (foldAt_succ f n d K)
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.mul_congr_left (h (K + 1)))
          (BPair.mul_congr (BPair.oneValue_refl d) (foldAt_congr h n d K)))
        (BPair.oneValue_symm (foldAt_succ g n d K)))

/-- The fold sits at or beyond the sum's unit at a family and bounds
at or beyond it. -/
theorem unitLe_foldAt {f : Nat → BPair} (hf : ∀ i, BPair.unit ≤ f i)
    {n d : BPair} (hn : BPair.unit ≤ n) (hd : BPair.unit ≤ d) :
    ∀ K : Nat, BPair.unit ≤ foldAt f n d K
  | 0 => leB_congr_right (BPair.oneValue_symm (foldAt_zero f n d)) (hf 0)
  | K + 1 => leB_congr_right (BPair.oneValue_symm (foldAt_succ f n d K))
      (unitLeAdd (unitLeMul (hf _) (unitLeBpow hn (K + 1)))
        (unitLeMul hd (unitLe_foldAt hf hn hd K)))

/-- The fold of a family's sum sits at or below the folds' sum at
bounds at or beyond the sum's unit. -/
theorem foldAt_add_le {f g h : Nat → BPair} {n d : BPair}
    (hn : BPair.unit ≤ n) (hd : BPair.unit ≤ d)
    (hle : ∀ i, h i ≤ f i + g i) :
    ∀ K : Nat, foldAt h n d K ≤ foldAt f n d K + foldAt g n d K
  | 0 => leB_congr (BPair.oneValue_symm (foldAt_zero h n d))
      (BPair.oneValue_symm (BPair.add_congr (foldAt_zero f n d) (foldAt_zero g n d)))
      (hle 0)
  | K + 1 => by
    refine leB_congr (BPair.oneValue_symm (foldAt_succ h n d K))
      (BPair.oneValue_symm (BPair.add_congr (foldAt_succ f n d K) (foldAt_succ g n d K))) ?_
    refine leB_trans (leB_add
      (leB_mulL (unitLeBpow hn (K + 1)) (hle (K + 1)))
      (leB_mulR hd (foldAt_add_le hn hd hle K))) ?_
    exact Or.inl (distrib_shuffle (f (K + 1)) (g (K + 1)) (bpow n (K + 1)) d
      (foldAt f n d K) (foldAt g n d K))

/-- A scaled family folds at the scale's multiple. -/
theorem foldAt_scale (c : BPair) (f : Nat → BPair) (n d : BPair) :
    ∀ K : Nat, (foldAt (fun i => c * f i) n d K).oneValue (c * foldAt f n d K)
  | 0 => BPair.oneValue_trans (foldAt_zero _ n d)
      (BPair.mul_congr (BPair.oneValue_refl c) (BPair.oneValue_symm (foldAt_zero f n d)))
  | K + 1 => by
    refine BPair.oneValue_trans (foldAt_succ _ n d K) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl d) (foldAt_scale c f n d K))) ?_
    refine BPair.oneValue_trans (scale_shuffle c (f (K + 1)) (bpow n (K + 1)) d (foldAt f n d K)) ?_
    exact BPair.mul_congr (BPair.oneValue_refl c) (BPair.oneValue_symm (foldAt_succ f n d K))

/-- The coefficient fold at a stated power: `Σ_{i≤K} |p_i| n^i d^(K-i)`,
the magnitudes at every key through the power with the vacant keys
at the sum's unit, cleared at `d^K`. -/
def foldK (p : poly.Poly) (n d : BPair) (K : Nat) : BPair :=
  foldAt (fun i => mag (ground.getAt BPair.unit p i)) n d K

/-- The fold at the power nought is the constant key's magnitude. -/
theorem foldK_zero (p : poly.Poly) (n d : BPair) :
    (foldK p n d 0).oneValue (mag (ground.getAt BPair.unit p 0)) :=
  foldAt_zero _ n d

/-- The fold recurs on the power: the top key's magnitude at the
bound's power joined to the second datum's multiple of the fold
below. -/
theorem foldK_succ (p : poly.Poly) (n d : BPair) (K : Nat) :
    (foldK p n d (K + 1)).oneValue
      (mag (ground.getAt BPair.unit p (K + 1)) * bpow n (K + 1)
        + d * foldK p n d K) :=
  foldAt_succ _ n d K

/-- The vacant list's fold is the sum's unit at every power. -/
theorem foldK_nil (n d : BPair) : ∀ K : Nat,
    (foldK [] n d K).oneValue BPair.unit
  | 0 => BPair.oneValue_trans (foldK_zero [] n d)
      (BPair.oneValue_of_eq (mag_unitLe (leB_refl _)))
  | K + 1 => by
    refine BPair.oneValue_trans (foldK_succ [] n d K) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr_left (BPair.oneValue_of_eq (mag_unitLe (leB_refl _))))
        (BPair.mul_congr (BPair.oneValue_refl d) (foldK_nil n d K))) ?_
    exact BPair.oneValue_trans (BPair.add_congr (BPair.unit_mul _) (BPair.mul_unit d))
      (BPair.unit_add _)

/-- The fold passes the one-value read. -/
theorem foldK_congr {p q : poly.Poly} (h : poly.oneValue p q) (n d : BPair)
    (K : Nat) : (foldK p n d K).oneValue (foldK q n d K) :=
  foldAt_congr (fun i => mag_congr (poly.oneValue_getAt i h)) n d K

/-- The fold sits at or beyond the sum's unit at bounds at or beyond
it. -/
theorem unitLe_foldK (p : poly.Poly) {n d : BPair}
    (hn : BPair.unit ≤ n) (hd : BPair.unit ≤ d) (K : Nat) :
    BPair.unit ≤ foldK p n d K :=
  unitLe_foldAt (fun _ => unitLe_mag _) hn hd K

/-- The sum's fold sits at or below the folds' sum. -/
theorem foldK_add_le (p q : poly.Poly) {n d : BPair}
    (hn : BPair.unit ≤ n) (hd : BPair.unit ≤ d) (K : Nat) :
    foldK (poly.add p q) n d K ≤ foldK p n d K + foldK q n d K :=
  foldAt_add_le hn hd (fun i =>
    leB_congr_left (BPair.oneValue_symm (mag_congr (poly.getAt_add p q i)))
      (mag_add_le _ _)) K

/-- A rescaled polynomial's fold is the scale's magnitude against
the fold. -/
theorem foldK_scaleP (c : BPair) (p : poly.Poly) (n d : BPair) (K : Nat) :
    (foldK (poly.scaleP c p) n d K).oneValue (mag c * foldK p n d K) :=
  BPair.oneValue_trans
    (foldAt_congr (fun i =>
      BPair.oneValue_trans (mag_congr (poly.getAt_scaleP c p i)) (mag_mul c _)) n d K)
    (foldAt_scale (mag c) _ n d K)

/-- The fold at the polynomial's own top's predecessor joined to a
further power is that power's clearing of the coefficient fold:
`thm:windowsep`'s `magFold` at `Σ_i |s_i| n^i d^(k-i)` with the
further keys' magnitudes at the sum's unit. -/
theorem foldK_magFold (p : poly.Poly) (n d : BPair) : ∀ g : Nat,
    (foldK p n d ((poly.vnorm p).length - 1 + g)).oneValue
      (bpow d g * magFold p n d)
  | 0 => by
    match hv : poly.vnorm p with
    | [] =>
      have hp : poly.oneValue p [] := by
        rw [← hv]; exact poly.oneValue_symm (poly.vnorm_ov p)
      show (foldK p n d 0).oneValue (bpow d 0 * magFold p n d)
      refine BPair.oneValue_trans (foldK_congr hp n d 0) ?_
      refine BPair.oneValue_trans (foldK_nil n d 0) ?_
      rw [show magFold p n d = foldPow ((poly.vnorm p).map mag) n d from rfl, hv]
      exact BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm _ _)) (BPair.mul_one_read _))
    | c :: cs =>
      show (foldK p n d ((c :: cs).length - 1 + 0)).oneValue (bpow d 0 * magFold p n d)
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
          (BPair.mul_one_read _)) ?_
      show (foldPow ((poly.vnorm p).map mag) n d).oneValue (foldK p n d (cs.length + 0))
      refine BPair.oneValue_trans (foldPow_read _ n d) ?_
      refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (foldAt_read _ n d _))
      rw [hv, length_map]
      show (ground.famFold BPair.add BPair.unit
        (fun i => ground.getAt BPair.unit ((c :: cs).map mag) i * bpow n i
          * bpow d (cs.length - i)) (List.range (cs.length + 1))).oneValue
        (ground.famFold BPair.add BPair.unit
          (fun i => mag (ground.getAt BPair.unit p i) * bpow n i
            * bpow d (cs.length - i)) (List.range (cs.length + 1)))
      refine ground.famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit
        BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2) _ _
        (List.range (cs.length + 1)) (fun i _ => ?_)
      rw [getAt_mapT BPair.unit BPair.unit mag (mag_unitLe (leB_refl _))]
      refine BPair.mul_congr_left (BPair.mul_congr_left ?_)
      have h1 : (ground.getAt BPair.unit (c :: cs) i).oneValue
          (ground.getAt BPair.unit p i) := by
        rw [← hv]; exact poly.oneValue_getAt i (poly.vnorm_ov p)
      exact mag_congr h1
  | g + 1 => by
    have hge : (poly.vnorm p).length ≤ (poly.vnorm p).length - 1 + g + 1 := by
      match hv : (poly.vnorm p).length with
      | 0 => exact Nat.zero_le _
      | m + 1 => exact Nat.add_le_add_right (Nat.le_add_right m g) 1
    have hbeyond : (ground.getAt BPair.unit p ((poly.vnorm p).length - 1 + g + 1)).oneValue
        BPair.unit := by
      refine BPair.oneValue_trans
        (BPair.oneValue_symm (poly.oneValue_getAt _ (poly.vnorm_ov p))) ?_
      rw [getAt_over BPair.unit (poly.vnorm p) _ hge]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans (foldK_succ p n d _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr_left (BPair.oneValue_trans (mag_congr hbeyond)
          (BPair.oneValue_of_eq (mag_unitLe (leB_refl _)))))
        (BPair.mul_congr (BPair.oneValue_refl d) (foldK_magFold p n d g))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul _) (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.unit_add _) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc d _ _).symm) ?_
    exact BPair.mul_congr_left (BPair.oneValue_symm (bpow_succ_read d g))

/-- The cap's term: a coefficient against the point's power against
the clearing's power, its magnitude against the bound's clearing
power, regrouped at the point's cleared power. -/
private theorem capL_shuffle (m M C dk dg : BPair) :
    (m * M * C * (dk * dg)).oneValue (m * C * dg * (M * dk)) :=
  polEqB [m, M, C, dk, dg]
    (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
      (Mon.mul (Mon.var 3) (Mon.var 4))))
    (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 2)) (Mon.var 4))
      (Mon.mul (Mon.var 1) (Mon.var 3))))
    (by decide +kernel)

/-- The cap's term on the bound's side, regrouped at the bound's
cleared power. -/
private theorem capR_shuffle (m nk dg C ck : BPair) :
    (m * nk * dg * (ck * C)).oneValue (m * C * dg * (nk * ck)) :=
  polEqB [m, nk, dg, C, ck]
    (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
      (Mon.mul (Mon.var 4) (Mon.var 3))))
    (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 3)) (Mon.var 2))
      (Mon.mul (Mon.var 1) (Mon.var 4))))
    (by decide +kernel)

/-- The cap's one term: a coefficient's cleared monomial at a point
inside the bound, its magnitude at the bound's clearing power, sits
at or below the coefficient's magnitude at the bound's monomial at
the point's clearing power. -/
private theorem cap_term (p : poly.Poly) (tn : BPair) (tc : Pos) (n d : BPair)
    (K k : Nat) (hd : BPair.unit ≤ d)
    (ht : mag tn * d ≤ n * BPair.ofPos tc) (hk : k ≤ K) :
    mag (ground.getAt BPair.unit p k * bpow tn k * bpow (BPair.ofPos tc) (K - k))
        * bpow d K
      ≤ mag (ground.getAt BPair.unit p k) * bpow n k * bpow d (K - k)
        * bpow (BPair.ofPos tc) K := by
  have hcU : BPair.unit ≤ BPair.ofPos tc := leB_of_lt (unitLtOfPos tc)
  have hsplit : k + (K - k) = K := natAddSubCancel hk
  have hdK : (bpow d K).oneValue (bpow d k * bpow d (K - k)) := by
    have h := bpow_add d k (K - k)
    rw [hsplit] at h
    exact h
  have hcK : (bpow (BPair.ofPos tc) K).oneValue
      (bpow (BPair.ofPos tc) k * bpow (BPair.ofPos tc) (K - k)) := by
    have h := bpow_add (BPair.ofPos tc) k (K - k)
    rw [hsplit] at h
    exact h
  have hmag : (mag (ground.getAt BPair.unit p k * bpow tn k * bpow (BPair.ofPos tc) (K - k))).oneValue
      (mag (ground.getAt BPair.unit p k) * bpow (mag tn) k * bpow (BPair.ofPos tc) (K - k)) :=
    BPair.oneValue_trans (mag_mul _ _)
      (BPair.mul_congr
        (BPair.oneValue_trans (mag_mul _ _)
          (BPair.mul_congr (BPair.oneValue_refl _) (mag_bpow tn k)))
        (BPair.oneValue_of_eq (mag_unitLe (unitLeBpow hcU (K - k)))))
  have hpow : bpow (mag tn) k * bpow d k ≤ bpow n k * bpow (BPair.ofPos tc) k :=
    leB_congr (bpow_mul (mag tn) d k) (bpow_mul n (BPair.ofPos tc) k)
      (bpow_mono (unitLeMul (unitLe_mag tn) hd) ht k)
  have hL : (mag (ground.getAt BPair.unit p k * bpow tn k * bpow (BPair.ofPos tc) (K - k))
        * bpow d K).oneValue
      (mag (ground.getAt BPair.unit p k) * bpow (BPair.ofPos tc) (K - k) * bpow d (K - k)
        * (bpow (mag tn) k * bpow d k)) :=
    BPair.oneValue_trans (BPair.mul_congr hmag hdK)
      (capL_shuffle (mag (ground.getAt BPair.unit p k)) (bpow (mag tn) k)
        (bpow (BPair.ofPos tc) (K - k)) (bpow d k) (bpow d (K - k)))
  have hR : (mag (ground.getAt BPair.unit p k) * bpow n k * bpow d (K - k)
        * bpow (BPair.ofPos tc) K).oneValue
      (mag (ground.getAt BPair.unit p k) * bpow (BPair.ofPos tc) (K - k) * bpow d (K - k)
        * (bpow n k * bpow (BPair.ofPos tc) k)) :=
    BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hcK)
      (capR_shuffle (mag (ground.getAt BPair.unit p k)) (bpow n k)
        (bpow d (K - k)) (bpow (BPair.ofPos tc) (K - k)) (bpow (BPair.ofPos tc) k))
  exact leB_congr (BPair.oneValue_symm hL) (BPair.oneValue_symm hR)
    (leB_mulR
      (unitLeMul (unitLeMul (unitLe_mag _) (unitLeBpow hcU (K - k))) (unitLeBpow hd (K - k)))
      hpow)

/-- The cap: a cleared evaluation at a point inside the bound, its
magnitude at the bound's clearing power, sits at or below the fold
at the point's clearing power, `thm:windowsep`'s evaluations capped
by the coefficient fold. -/
theorem foldK_cap (p : poly.Poly) (tn : BPair) (tc : Pos) (n d : BPair) (K : Nat)
    (hd : BPair.unit ≤ d) (hp : p.length ≤ K + 1)
    (ht : mag tn * d ≤ n * BPair.ofPos tc) :
    mag (poly.evalClear p tn tc K) * bpow d K
      ≤ foldK p n d K * bpow (BPair.ofPos tc) K := by
  have hext : (ground.famFold BPair.add BPair.unit
      (fun k => ground.getAt BPair.unit p k * bpow tn k
        * bpow (BPair.ofPos tc) (K - k)) (List.range (K + 1))).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit p k * bpow tn k
          * bpow (BPair.ofPos tc) (K - k)) (List.range p.length)) := by
    refine foldRange_le _ p.length (K + 1) hp (fun j hj => ?_)
    rw [getAt_over BPair.unit p j hj]
    exact BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
          (BPair.mul_unit _))) (BPair.mul_unit _))
  have hval : (poly.evalClear p tn tc K).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit p k * bpow tn k
          * bpow (BPair.ofPos tc) (K - k)) (List.range (K + 1))) :=
    BPair.oneValue_trans (poly.evalClear_read p tn tc K) (BPair.oneValue_symm hext)
  refine leB_congr_left
    (BPair.oneValue_symm (BPair.mul_congr_left (mag_congr hval))) ?_
  refine leB_trans (leB_mulL (unitLeBpow hd K) (mag_famFold_le _ _)) ?_
  refine leB_congr (BPair.oneValue_symm (foldB_mul_right _ _ _))
    (BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.mul_congr_left (foldAt_read _ n d K)) (foldB_mul_right _ _ _))) ?_
  refine leB_famFold_range (List.range (K + 1)) (fun k hk => ?_)
  exact cap_term p tn tc n d K k hd ht
    (Nat.le_of_lt_succ (ground.ltOfCountRange hk))

/-- The unit's domination by a list: every coefficient at or beyond
the sum's unit, the walk past the left list's end. -/
def unitDomB : Poly → Bool
  | [] => true
  | y :: q => decide (BPair.unit ≤ y) && unitDomB q

/-- Coefficientwise magnitude domination, the two lists walked
together: at every shared key the left's magnitude sits at or below
the right, a key past the right list reading the left's magnitude
against the sum's unit and a key past the left list the unit
against the right's coefficient (`thm:windowsep`'s carrier at the
coefficient lists). -/
def magDomB : Poly → Poly → Bool
  | [], q => unitDomB q
  | x :: p, [] => decide (mag x ≤ BPair.unit) && magDomB p []
  | x :: p, y :: q => decide (mag x ≤ y) && magDomB p q

/-- The domination read. -/
def magDom (p q : Poly) : Prop := magDomB p q = true

instance instWindowsep2 (p q : Poly) : Decidable (magDom p q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The unit's domination at every key: the walk's member at a key
of the list and the unit against unit beyond it. -/
private theorem unitDomB_at : ∀ (q : Poly) (j : Nat), unitDomB q = true →
    mag (ground.getAt BPair.unit ([] : Poly) j) ≤ ground.getAt BPair.unit q j
  | [], _, _ => by
    show mag BPair.unit ≤ BPair.unit
    rw [mag_unitLe (ground.leB_refl BPair.unit)]
    exact ground.leB_refl _
  | y :: q, 0, h => by
    have h' : (decide (BPair.unit ≤ y) && unitDomB q) = true := h
    show mag BPair.unit ≤ y
    rw [mag_unitLe (ground.leB_refl BPair.unit)]
    exact of_decide_eq_true (ground.andSplitB h').1
  | y :: q, j + 1, h => by
    have h' : (decide (BPair.unit ≤ y) && unitDomB q) = true := h
    exact unitDomB_at q j (ground.andSplitB h').2

/-- The domination read at every key, the walk's own member at a
key of either list and the unit against unit beyond both. -/
private theorem magDomB_at : ∀ (p q : Poly) (j : Nat), magDomB p q = true →
    mag (ground.getAt BPair.unit p j) ≤ ground.getAt BPair.unit q j
  | [], q, j, h => unitDomB_at q j h
  | x :: p, [], 0, h => by
    have h' : (decide (mag x ≤ BPair.unit) && magDomB p []) = true := h
    exact of_decide_eq_true (ground.andSplitB h').1
  | x :: p, [], j + 1, h => by
    have h' : (decide (mag x ≤ BPair.unit) && magDomB p []) = true := h
    exact magDomB_at p [] j (ground.andSplitB h').2
  | x :: p, y :: q, 0, h => by
    have h' : (decide (mag x ≤ y) && magDomB p q) = true := h
    exact of_decide_eq_true (ground.andSplitB h').1
  | x :: p, y :: q, j + 1, h => by
    have h' : (decide (mag x ≤ y) && magDomB p q) = true := h
    exact magDomB_at p q j (ground.andSplitB h').2

private theorem magDom_at {p q : Poly} (h : magDom p q) (j : Nat) :
    mag (ground.getAt BPair.unit p j) ≤ ground.getAt BPair.unit q j :=
  magDomB_at p q j h

/-- The unit's domination from every key's read. -/
private theorem unitDomB_of : ∀ (q : Poly),
    (∀ j, mag (ground.getAt BPair.unit ([] : Poly) j) ≤ ground.getAt BPair.unit q j) →
    unitDomB q = true
  | [], _ => rfl
  | y :: q, h => by
    show (decide (BPair.unit ≤ y) && unitDomB q) = true
    have h0 : mag BPair.unit ≤ y := h 0
    rw [mag_unitLe (ground.leB_refl BPair.unit)] at h0
    rw [decide_eq_true h0, unitDomB_of q (fun j => h (j + 1))]
    rfl

/-- The walk from every key's read. -/
private theorem magDomB_of : ∀ (p q : Poly),
    (∀ j, mag (ground.getAt BPair.unit p j) ≤ ground.getAt BPair.unit q j) →
    magDomB p q = true
  | [], q, h => unitDomB_of q h
  | x :: p, [], h => by
    show (decide (mag x ≤ BPair.unit) && magDomB p []) = true
    have h0 : mag x ≤ BPair.unit := h 0
    rw [decide_eq_true h0, magDomB_of p [] (fun j => h (j + 1))]
    rfl
  | x :: p, y :: q, h => by
    show (decide (mag x ≤ y) && magDomB p q) = true
    have h0 : mag x ≤ y := h 0
    rw [decide_eq_true h0, magDomB_of p q (fun j => h (j + 1))]
    rfl

/-- The domination read from every key. -/
theorem magDom_of {p q : Poly}
    (h : ∀ j, mag (ground.getAt BPair.unit p j) ≤ ground.getAt BPair.unit q j) :
    magDom p q :=
  magDomB_of p q h

/-- The magnitude map dominates its own source. -/
theorem magDom_map (p : Poly) : magDom p (p.map mag) :=
  magDom_of (fun j => by
    rw [getAt_map_mag p j]
    exact ground.leB_refl _)

/-- Domination sums, the magnitudes' own sum law. -/
theorem magDom_add {p1 q1 p2 q2 : Poly}
    (h1 : magDom p1 q1) (h2 : magDom p2 q2) :
    magDom (poly.add p1 p2) (poly.add q1 q2) :=
  magDom_of (fun j => by
    refine ground.leB_congr_left
      (mag_congr (BPair.oneValue_symm (poly.getAt_add p1 p2 j))) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_symm (poly.getAt_add q1 q2 j)) ?_
    exact ground.leB_trans (mag_add_le _ _)
      (ground.leB_add (magDom_at h1 j) (magDom_at h2 j)))

/-- Domination rides the key shift, the shifted keys vacant on both
sides below the shift. -/
theorem magDom_shiftUp (b : Nat) {p q : Poly}
    (h : magDom p q) :
    magDom (poly.shiftUp b p) (poly.shiftUp b q) :=
  magDom_of (fun j =>
    match Nat.lt_or_ge j b with
    | Or.inl hlt => by
      rw [poly.getAt_shiftUp_lt b p j hlt, poly.getAt_shiftUp_lt b q j hlt,
        mag_unitLe (ground.leB_refl BPair.unit)]
      exact ground.leB_refl _
    | Or.inr hge => by
      obtain ⟨k, hk⟩ := Nat.le.dest hge
      rw [← hk, poly.getAt_shiftUp_add b p k, poly.getAt_shiftUp_add b q k]
      exact magDom_at h k)

/-- Domination rides a rescaling at its own magnitude. -/
theorem magDom_scaleP {a : BPair} (ha : mag a = a)
    {p q : Poly} (h : magDom p q) :
    magDom (poly.scaleP a p) (poly.scaleP a q) := by
  have hau : BPair.unit ≤ a := by
    rw [← ha]
    exact unitLe_mag a
  refine magDom_of (fun j => ?_)
  refine ground.leB_congr_left
    (mag_congr
      (BPair.oneValue_symm (poly.getAt_scaleP a p j))) ?_
  refine ground.leB_congr_right
    (BPair.oneValue_symm (poly.getAt_scaleP a q j)) ?_
  refine ground.leB_congr_left
    (BPair.oneValue_symm
      (mag_mul a (ground.getAt BPair.unit p j))) ?_
  rw [ha]
  exact ground.leB_mulR hau (magDom_at h j)

/-- A dominated coefficient against two factors at or beyond the
sum's unit keeps the domination at the product. -/
private theorem magTerm_le {A B : BPair} (hA : mag A ≤ B)
    (x y : BPair) (hx : BPair.unit ≤ x) (hy : BPair.unit ≤ y) :
    mag (A * x * y) ≤ B * x * y := by
  have hB : BPair.unit ≤ B := ground.leB_trans (unitLe_mag A) hA
  refine ground.leB_congr_left
    (BPair.oneValue_symm
      (BPair.oneValue_trans (mag_mul (A * x) y)
        (BPair.mul_congr (mag_mul A x)
          (BPair.oneValue_refl _)))) ?_
  rw [mag_unitLe hx, mag_unitLe hy]
  exact ground.leB_mul_mono hy (ground.unitLeMul hB hx)
    (ground.leB_mul_mono hx hB hA (ground.leB_refl x))
    (ground.leB_refl y)

/-- Coefficientwise domination prices the cleared evaluation at a
point at or beyond the sum's unit: the evaluation's magnitude sits at or below the
dominating list's own, both folds extended to the shared key
range. -/
theorem evalClear_magDom {p q : Poly} (zn : BPair) (hzn : BPair.unit ≤ zn)
    (ed : Pos) (K : Nat) (h : magDom p q) :
    mag (poly.evalClear p zn ed K) ≤ poly.evalClear q zn ed K := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hoff : ∀ (l : Poly) (j : Nat), l.length ≤ j →
      (ground.getAt BPair.unit l j * ground.bpow zn j
        * ground.bpow (BPair.ofPos ed) (K - j)).oneValue BPair.unit := by
    intro l j hj
    rw [ground.getAt_over BPair.unit l j hj]
    exact BPair.oneValue_trans (BPair.mul_congr_left (BPair.unit_mul _))
      (BPair.unit_mul _)
  have hP : (poly.evalClear p zn ed K).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit p k
          * ground.bpow zn k
          * ground.bpow (BPair.ofPos ed) (K - k))
        (List.range (p.length + q.length))) :=
    BPair.oneValue_trans (poly.evalClear_read p zn ed K)
      (BPair.oneValue_symm
        (ground.foldRange_le _ p.length (p.length + q.length)
          (Nat.le_add_right _ _) (hoff p)))
  have hQ : (poly.evalClear q zn ed K).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit q k
          * ground.bpow zn k
          * ground.bpow (BPair.ofPos ed) (K - k))
        (List.range (p.length + q.length))) :=
    BPair.oneValue_trans (poly.evalClear_read q zn ed K)
      (BPair.oneValue_symm
        (ground.foldRange_le _ q.length (p.length + q.length)
          (Nat.le_add_left _ _) (hoff q)))
  refine ground.leB_congr_left
    (mag_congr (BPair.oneValue_symm hP)) ?_
  refine ground.leB_congr_right (BPair.oneValue_symm hQ) ?_
  refine ground.leB_trans (mag_famFold_le _ _) ?_
  exact ground.bsum_le _ _ (List.range (p.length + q.length))
    (fun i _ => magTerm_le (magDom_at h i) _ _ (ground.unitLeBpow hzn i)
      (ground.unitLeBpow hEd (K - i)))


end windowsep
