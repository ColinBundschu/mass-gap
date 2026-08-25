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
telescope, so the evaluation reads the term's side), the
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
real roots at `Λ V G ≥ 1` — is the general tier at its recorded
consumers (`lem:stage`'s isolating brackets, `lem:split`'s
designations), the arithmetic below its stated data.

The subresultant walk is refuted at this producer, the measured dead
end: at every swept input (390,625 grid pairs with a six-rung
magnitude ladder at margins to `10^6`, at the exactness guard silent
throughout) the subresultant and primitive walks produce the
identical certified tuple, so the interior is gauge at the output;
the primitive walk's coefficients sit entrywise at or below the
subresultant's among fraction-free walks (the subresultant's
classical framing priced against 1970s bignum arithmetic, where the
kernel's `Nat.gcd` is GMP-accelerated); and the subresultant
spelling's landing price is Collins' exactness theorem derived
standalone in the tex.  The walk as landed is the minimal
fraction-free spelling, the decided object.
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
coefficient's magnitude and `H` the height: every real root sits in
the radius segment between `B`'s balance partner and `B` at
`B = [c + H : c]`, the leading-term bound. -/
def radiusN (P : Poly) : BPair :=
  (mag (top (poly.vnorm P)) + height P).norm

/-- The radius pair's second member, the leading coefficient's
magnitude — the top key's coefficient at the value's
representative, the degree's own read. -/
def radiusD (P : Poly) : BPair := mag (top (poly.vnorm P))

private def foldPow (l : List BPair) (n d : BPair) : BPair :=
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

/-! The power's order kit at the balance carrier: a power of a
datum at or above the sum's unit sits there, a power of one strictly
above it sits strictly above, powers compare at comparing bases, and
powers pass the product. -/

/-- A power of a datum at or above the sum's unit sits there. -/
theorem unitLe_bpow {a : BPair} (h : BPair.unit ≤ a) :
    ∀ k : Nat, BPair.unit ≤ ground.bpow a k
  | 0 => ground.leB_of_lt (ground.unitLtOfPos Pos.one)
  | k + 1 =>
    ground.leB_congr_right
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (ground.unitLeMul h (unitLe_bpow h k))

/-- A power of a datum strictly above the sum's unit sits strictly
above it. -/
theorem unitLt_bpow {a : BPair} (h : BPair.unit < a) :
    ∀ k : Nat, BPair.unit < ground.bpow a k
  | 0 => ground.unitLtOfPos Pos.one
  | k + 1 =>
    BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (ground.unitLtMul h (unitLt_bpow h k))

/-- The powers compare at comparing bases from the sum's unit. -/
theorem bpow_mono {a b : BPair} (ha : BPair.unit ≤ a) (h : a ≤ b) :
    ∀ k : Nat, ground.bpow a k ≤ ground.bpow b k
  | 0 => ground.leB_refl _
  | k + 1 => by
    have hb : BPair.unit ≤ b := ground.leB_trans ha h
    have hstep : a * ground.bpow a k ≤ b * ground.bpow b k :=
      ground.leB_trans (ground.leB_mulR ha (bpow_mono ha h k))
        (ground.leB_congr
          (BPair.oneValue_of_eq (BPair.mul_comm (ground.bpow b k) a))
          (BPair.oneValue_of_eq (BPair.mul_comm (ground.bpow b k) b))
          (ground.leB_mulR (unitLe_bpow hb k) h))
    exact ground.leB_congr
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (BPair.oneValue_symm (BPair.norm_oneValue _)) hstep

/-- The power passes the product. -/
theorem bpow_mul (a b : BPair) : ∀ k : Nat,
    (ground.bpow (a * b) k).oneValue
      (ground.bpow a k * ground.bpow b k)
  | 0 => BPair.oneValue_symm (BPair.mul_one_read _)
  | k + 1 => by
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (a * b)) (bpow_mul a b k)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_mul_mul_comm a b (ground.bpow a k) (ground.bpow b k))) ?_
    exact BPair.mul_congr
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (BPair.oneValue_symm (BPair.norm_oneValue _))

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
    (bpow_mono (unitLe_mag x) h k)

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

/-- The magnitude read through a mapped list's entry. -/
private theorem getAt_map_mag : ∀ (l : Poly) (i : Nat),
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
        (ground.unitLeMul (unitLe_mag _) (unitLe_bpow hn i))
        (unitLe_bpow hd _)))

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
      (BPair.mul_congr hm (bpow_mul N (BPair.ofPos c) i))
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

/-- A top off the sum's unit puts the carrier's length at the top
key's successor. -/
private theorem len_of_top_off : ∀ {q : Poly},
    ¬ (top q).oneValue BPair.unit → q.length = (q.length - 1) + 1
  | [], h => absurd (BPair.oneValue_refl BPair.unit) h
  | _ :: _, _ => rfl

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
    ground.foldB_nonneg _ (List.range n) (fun i _ => unitLe_bpow hyu i)
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
    exact ground.leB_mul_mono (unitLe_bpow hyu i) hHu (hH _ hmem)
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
      (len_of_top_off (top_off_of_lead hl)) (unitLe_height p)
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

instance (S : Poly) (wn wd : Pos) : Decidable (sepRead S wn wd) :=
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
content at the coefficients' margins with its exact division, the
count's power, and the pseudo-division's accumulating descent, the
inputs at the value's representative (`poly.vnorm`). -/

private def contentN (P : Poly) : Nat :=
  P.foldl (fun k x => Nat.gcd k (BPair.marginN x)) 0

private def primDiv (n : Nat) (P : Poly) : Poly :=
  P.map (fun x =>
    if n == 0 then x
    else if BPair.marginN x % n == 0 then
      match x.side with
      | .lt _ _ => ⟨.one, posOfSucc (BPair.marginN x / n)⟩
      | .eq _ => BPair.unit
      | .gt _ _ => ⟨posOfSucc (BPair.marginN x / n), .one⟩
    else x)

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
      let kap := contentN dv.2.1
      walkGo fuel R1
        ⟨primDiv kap dv.2.1,
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
  let k := contentN R.r
  if k == 0 then R
  else ⟨primDiv k R.r, R.u, R.v, (R.m * BPair.ofNat k).norm⟩

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

end windowsep
