import MassGap.Steinberg
/-!
`prop:row` — the X-tower matrix's member reads at the tables: the
diagonal's value is θ's occupied coroot support, the count of
simple keys at an occupied coroot pair (`supportCount`), one at
every member off the `A`-series and two at the `A`-series at
`r ≥ 2` with one at its first member — the `c₁` the statement's
prefix and the channel divisor read; the dimension is the content
list's own fold, twice the positive count with the coordinate
count (`dTheta`); and the unit content's fold data enter at the
member join `Σ_α ⟨α,α⟩ = ℓ (r + 1)` over the positive list, the
cleared length fold (`lenFoldAll`).  The `A`-series' fusion route
is pinned against this read at the shared instances in the check
module, the fast count of `cor:steinberg` at the matched-degree
shapes.

The content tier states the tie analysis's own data: θ's coroot
vector `thetaV` and the tower key `kappaV` at `mθ + ρ`, both
normed; the vacant coroot support `zCount`, `supportCount`'s
complement at the coordinate count (`supportCount_zCount`); the θ
content list's reads `thetaFamRead` — the unit content at the
coordinate count, the root list with its balance partners at one
each, and the members those alone, with `thetaCount` the read's
own count function, every vector's count in the list read off the
table and the vector alone (`countOf_theta`); the tie's kept square
`sqAtRead`, the form's square carried across the graded image
list; and the ρ-length read `rhoLenRead`, every positive member's
square at or beyond the unit and at or below its doubled ρ-dot,
the doubled dot's equality at the simples alone.

The diagonal theorem itself is the tie analysis over that data.  A
tie `ν_w + wκ = κ` keeps the form's square, so the withdrawn key's
square reads its doubled pairing with `κ`; at the unit content the
member is the key itself, at a positive member the ρ-length read's
cap forces the scaled θ-dot to the sum's unit and its equality
names the member a simple, and at a balance partner the square's
own nonnegativity refutes.  The qualifying simples' keys are the
letters' images of `κ`, one each on the odd side and none on the
even by the closure read at the top, and their coroot vectors part
at the Gram's defining diagonal — so `balanceValues` reads the two
convolution counts as the coordinate count and `zCount` at every
`m ≥ 1`, `defectValues` reads both at the coordinate count at the
vacuum (`prop:row`'s defect, the Kronecker delta at two labels),
and `diagRead` closes the display at a stated exhaustion:
`N^{mθ}_{θ,mθ} = supportCount`, θ's occupied coroot support.
-/

namespace row
open ground gentable sertables assembly memberchar

/-- θ's occupied coroot support: the count of simple keys at a
coroot pair off equal members, the diagonal's value
(`prop:row`). -/
def supportCount (t : Table) : Nat :=
  (List.range t.rank).foldl (fun acc j =>
    if (corootAt t t.thetaFold j).oneValue BPair.unit then acc
    else acc + 1) 0

/-- The adjoint dimension, the content list's own fold: twice the
positive count with the coordinate count (`prop:row`'s dimension
fold). -/
def dTheta (t : Table) : Nat := 2 * posCount t + t.rank

/-- The positive list's length fold `Σ_α ⟨α,α⟩`, cleared at
`2 lenDen`: the member join's read, `formNum`'s fold over the
root list. -/
def lenFoldAll (t : Table) : BPair :=
  BPair.sum (t.posFolds.map (fun f => formNum t f f))

/-- The member join `Σ_α ⟨α,α⟩ = ℓ (r + 1)` over the positive
list, the unit content's fold display at the cleared second
member. -/
def lenFoldRead (t : Table) (v : Nat) : Prop :=
  (lenFoldAll t).oneValue (BPair.ofNat (2 * t.lenDen * v))

instance (t : Table) (v : Nat) : Decidable (lenFoldRead t v) :=
  inferInstanceAs (Decidable (_ = _))

/-! The tie analysis's content data (`prop:row`'s member ties):
θ's own coroot vector and the tower key at `mθ + ρ`, the vacant
coroot support beside `supportCount`, and the three reads the tie
consumes — the θ content list's, the kept square's and the
ρ-length's. -/

/-- θ's coroot vector, `posCorootV`'s spelling at the θ fold,
normed (`prop:row`'s member ties at `κ = mθ + ρ`). -/
def thetaV (t : Table) : List BPair :=
  poly.pnorm ((List.range t.rank).map (gentable.corootAt t t.thetaFold))

/-- The tower key `mθ + ρ`, normed (`prop:row`'s tie at
`ν_w + wκ = κ`). -/
def kappaV (t : Table) (m : Nat) : List BPair :=
  poly.pnorm (elim.vecAdd (elim.vecScale (BPair.ofNat m) (thetaV t))
    (rhoV t))

/-- θ's vacant coroot support, `supportCount`'s complement: the
count of simple keys at θ's coroot pair of equal members
(`prop:row`'s `z`). -/
def zCount (t : Table) : Nat :=
  (List.range t.rank).foldl (fun acc j =>
    if (corootAt t t.thetaFold j).oneValue BPair.unit then acc + 1
    else acc) 0

/-- The θ content list's reads: the unit content at the coordinate
count, the root list with its balance partners at one each, and the
members those alone (`prop:row`'s member `θ` content list). -/
def thetaFamRead (t : Table) (L : List (List BPair)) : Prop :=
  ground.countOf (List.replicate t.rank BPair.unit) L = t.rank
  ∧ (∀ j, j < t.posFolds.length →
      ground.countOf (poly.pnorm (posCorootV t j)) L = 1
      ∧ ground.countOf (poly.pnorm (poly.neg (posCorootV t j))) L = 1)
  ∧ (∀ nu ∈ L, nu = List.replicate t.rank BPair.unit
      ∨ ∃ j, j + 1 < t.posFolds.length + 1
          ∧ (nu = poly.pnorm (posCorootV t j)
             ∨ nu = poly.pnorm (poly.neg (posCorootV t j))))

instance (t : Table) (L : List (List BPair)) :
    Decidable (thetaFamRead t L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The θ content list's count at a vector, the characterization's
own function: the unit content reads the coordinate count, a
positive fold's coroot vector or its balance partner reads one,
and every further vector reads the vacant count. -/
def thetaCount (t : Table) (x : List BPair) : Nat :=
  if x = List.replicate t.rank BPair.unit then t.rank
  else if ∃ j, j + 1 < t.posFolds.length + 1
      ∧ (x = poly.pnorm (posCorootV t j)
         ∨ x = poly.pnorm (poly.neg (posCorootV t j))) then 1
  else 0

/-- The θ content list's count is the characterization's own
function: under `thetaFamRead` every vector's count in the list is
read off the table and the vector alone. -/
theorem countOf_theta (t : Table) (L : List (List BPair))
    (h : thetaFamRead t L) (x : List BPair) :
    ground.countOf x L = thetaCount t x := by
  show ground.countOf x L
    = if x = List.replicate t.rank BPair.unit then t.rank
      else if ∃ j, j + 1 < t.posFolds.length + 1
          ∧ (x = poly.pnorm (posCorootV t j)
             ∨ x = poly.pnorm (poly.neg (posCorootV t j))) then 1
      else 0
  by_cases hu : x = List.replicate t.rank BPair.unit
  · rw [if_pos hu, hu]
    exact h.1
  · rw [if_neg hu]
    by_cases hs : ∃ j, j + 1 < t.posFolds.length + 1
        ∧ (x = poly.pnorm (posCorootV t j)
           ∨ x = poly.pnorm (poly.neg (posCorootV t j)))
    · rw [if_pos hs]
      obtain ⟨j, hj, hor⟩ := hs
      have hjl : j < t.posFolds.length := Nat.lt_of_succ_lt_succ hj
      match hor with
      | .inl he => rw [he]; exact (h.2.1 j hjl).1
      | .inr he => rw [he]; exact (h.2.1 j hjl).2
    · rw [if_neg hs]
      match Nat.eq_zero_or_pos (ground.countOf x L) with
      | .inl hz => exact hz
      | .inr hpos =>
        match h.2.2 x (ground.mem_of_countOf_pos x L hpos) with
        | .inl hxu => exact absurd hxu hu
        | .inr hex => exact absurd hex hs

/-- The tie's kept square, the family's own read: every member of
the graded image list carries the stated key's form square
(`prop:row`: a tie keeps the form's square). -/
def sqAtRead (F : FundData) (W : List (List BPair × Bool))
    (v : List BPair) : Prop :=
  ∀ vp ∈ W, (dotB F vp.1 vp.1).oneValue (dotB F v v)

instance (F : FundData) (W : List (List BPair × Bool))
    (v : List BPair) : Decidable (sqAtRead F W v) :=
  inferInstanceAs (Decidable (∀ vp ∈ W, _))

/-- The ρ-length read: every positive member's square beyond the
unit and at or below its doubled ρ-dot, the doubled dot's equality
at the simples alone (`con:sertables`' positive square at the
family's displayed length; `prop:row`'s root fold's pair two at
the simples and beyond two at every further positive member). -/
def rhoLenRead (t : Table) (F : FundData) : Prop :=
  ∀ j, j < t.posFolds.length →
    BPair.unit < dotB F (posCorootV t j) (posCorootV t j)
    ∧ dotB F (posCorootV t j) (posCorootV t j)
      ≤ dotB F (posCorootV t j) (rhoV t)
        + dotB F (posCorootV t j) (rhoV t)
    ∧ ((dotB F (posCorootV t j) (rhoV t)
          + dotB F (posCorootV t j) (rhoV t)).oneValue
        (dotB F (posCorootV t j) (posCorootV t j))
      → ∃ i, i + 1 < t.rank + 1
          ∧ j = ground.getAt 0 F.simplePos i)

instance (t : Table) (F : FundData) : Decidable (rhoLenRead t F) :=
  inferInstanceAs (Decidable (∀ j, j < t.posFolds.length → _ ∧ _ ∧ _))

/-! The complement join: the two guarded walks over one key list
read the list's own length, each key counted on exactly one of the
two sides. -/

/-- The accumulator's shift at the qualifying side. -/
private theorem shiftQual (a b n : Nat) :
    a + (b + 1) + n = a + b + (n + 1) := by
  rw [Nat.add_assoc a (b + 1) n, Nat.add_assoc b 1 n,
    Nat.add_comm 1 n, ← Nat.add_assoc a b (n + 1)]

/-- The accumulator's shift at the refusing side. -/
private theorem shiftOff (a b n : Nat) :
    a + 1 + b + n = a + b + (n + 1) := by
  rw [Nat.add_assoc a 1 b, Nat.add_comm 1 b, ← Nat.add_assoc a b 1,
    Nat.add_assoc (a + b) 1 n, Nat.add_comm 1 n]

/-- The guarded walks' complementary split: counting a key list's
refusals beside its qualifications reads the list's own length,
both seeds carried. -/
private theorem countSplit (P : Nat → Prop) [DecidablePred P] :
    ∀ (l : List Nat) (a b : Nat),
      l.foldl (fun acc j => if P j then acc else acc + 1) a
        + l.foldl (fun acc j => if P j then acc + 1 else acc) b
      = a + b + l.length
  | [], _, _ => rfl
  | j :: l, a, b => by
    show (l.foldl (fun acc j => if P j then acc else acc + 1)
          (if P j then a else a + 1))
        + (l.foldl (fun acc j => if P j then acc + 1 else acc)
          (if P j then b + 1 else b))
      = a + b + (l.length + 1)
    by_cases hj : P j
    · rw [if_pos hj, if_pos hj, countSplit P l a (b + 1)]
      exact shiftQual a b l.length
    · rw [if_neg hj, if_neg hj, countSplit P l (a + 1) b]
      exact shiftOff a b l.length

/-- The support count's complement join: θ's occupied coroot
support and its vacant support read the coordinate count
(`prop:row`'s `N^{mθ}_{θ,mθ} + z = ℓ` at the diagonal's value). -/
theorem supportCount_zCount (t : Table) :
    supportCount t + zCount t = t.rank := by
  have h := countSplit
    (fun j => (corootAt t t.thetaFold j).oneValue BPair.unit)
    (List.range t.rank) 0 0
  rw [ground.length_range t.rank, Nat.add_zero, Nat.zero_add] at h
  exact h

/-! The tower key's own frame: the order, the representative and the
coordinate read `κ_k = m θ_k + 1`, the vacant key's two reads, and
the reflection's shift — at a coordinate reading the natural one the
letter's image is the key less the simple's own coroot vector, the
reflection join read at that coordinate. -/

/-- θ's coroot vector sits at the rank's order. -/
private theorem thetaV_length (t : Table) : (thetaV t).length = t.rank := by
  show (((List.range t.rank).map
    (gentable.corootAt t t.thetaFold)).map BPair.norm).length = t.rank
  rw [ground.length_map, ground.length_mapRange]

/-- The tower key sits at the rank's order. -/
private theorem kappa_length (t : Table) (m : Nat) :
    (kappaV t m).length = t.rank := by
  have hS : (elim.vecScale (BPair.ofNat m) (thetaV t)).length = t.rank :=
    (elim.length_vecScale _ _).trans (thetaV_length t)
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  show (poly.pnorm (elim.vecAdd
    (elim.vecScale (BPair.ofNat m) (thetaV t)) (rhoV t))).length = t.rank
  rw [poly.pnorm_length,
    elim.length_vecAdd (elim.vecScale (BPair.ofNat m) (thetaV t))
      (rhoV t) t.rank hS hrl]

/-- The tower key is its own representative. -/
private theorem kappa_norm (t : Table) (m : Nat) :
    poly.pnorm (kappaV t m) = kappaV t m :=
  poly.pnorm_pnorm _

/-- The tower key's coordinate read: `m θ_k` joined to the natural
one, `ρ`'s own entry. -/
private theorem kappa_entry (t : Table) (m : Nat)
    {k : Nat} (hk : k < t.rank) :
    (ground.getAt BPair.unit (kappaV t m) k).oneValue
      (BPair.ofNat m * ground.getAt BPair.unit (thetaV t) k
        + BPair.ofNat 1) := by
  have hS : (elim.vecScale (BPair.ofNat m) (thetaV t)).length = t.rank :=
    (elim.length_vecScale _ _).trans (thetaV_length t)
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hA : (elim.vecAdd (elim.vecScale (BPair.ofNat m) (thetaV t))
      (rhoV t)).length = t.rank :=
    elim.length_vecAdd (elim.vecScale (BPair.ofNat m) (thetaV t))
      (rhoV t) t.rank hS hrl
  have hrho : ground.getAt BPair.unit (rhoV t) k = BPair.ofNat 1 :=
    ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank k hk
  show (ground.getAt BPair.unit ((elim.vecAdd
    (elim.vecScale (BPair.ofNat m) (thetaV t)) (rhoV t)).map
      BPair.norm) k).oneValue _
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ k
      (by rw [hA]; exact hk),
    elim.getAt_vecAdd _ _ k (by rw [hS]; exact hk)
      (by rw [hrl]; exact hk),
    elim.getAt_vecScale _ _ k (by rw [thetaV_length t]; exact hk), hrho]
  exact BPair.norm_oneValue _

/-- The reflection's shift at a unit coordinate: the letter's image
of a key reading the natural one at its own coordinate is the key
less the simple's coroot vector (`con:gentable`'s reflection join
`μ = s_i μ + μ(α_i^∨) α_i` at `μ(α_i^∨) = 1`, the shifted key read
at the Cartan row bridged to the simple's coroot vector). -/
private theorem reflShift (t : Table) (F : FundData)
    (hsp : simplePosRead t F) {i : Nat} (hi : i < t.rank)
    (y : List BPair) (hy : y.length = t.rank)
    (hyi : (ground.getAt BPair.unit y i).oneValue (BPair.ofNat 1)) :
    reflAt t i y
      = poly.pnorm (elim.vecAdd y
          (poly.neg (poly.pnorm
            (posCorootV t (ground.getAt 0 F.simplePos i))))) := by
  rw [assembly.reflAt_shift t i hi y hy hyi, assembly.simpleRow t F hsp hi]
  have hcl : (assembly.cartRowV t i).length = t.rank :=
    assembly.cartRowV_length t i
  have hpl : (poly.pnorm (assembly.cartRowV t i)).length = t.rank :=
    (poly.pnorm_length _).trans hcl
  have h1 : (poly.neg (assembly.cartRowV t i)).length = t.rank :=
    (ground.length_map _ _).trans hcl
  have h2 : (poly.neg (poly.pnorm (assembly.cartRowV t i))).length
      = t.rank :=
    (ground.length_map _ _).trans hpl
  refine poly.pnorm_congr _ _ ?_ ?_
  · rw [elim.length_vecAdd y _ t.rank hy h1,
      elim.length_vecAdd y _ t.rank hy h2]
  · rw [elim.vecAdd_comm y (poly.neg (assembly.cartRowV t i)),
      elim.vecAdd_comm y (poly.neg (poly.pnorm
        (assembly.cartRowV t i)))]
    refine elim.vecAdd_congr _ _ y (h1.trans h2.symm) ?_
    exact poly.swapMap_oneValue
      (poly.oneValue_symm (poly.pnorm_oneValue _))

/-! The form's reads at the tie: the balance partner at the first
slot, the simple's own pairing through the Gram's defining
diagonal, the tower key's expansion at `mθ + ρ`, the joined key's
square, and the tie equation itself — a graded member at the key's
own withdrawal carries the withdrawn key's square against its
doubled pairing with the tower key. -/

/-- The tower key's expansion at the second slot: the scaled θ-dot
joined to the ρ-dot. -/
private theorem dotB_kappa (t : Table) (F : FundData)
    (hshape : fundShape t F) (m : Nat)
    (v : List BPair) (hv : v.length = t.rank) :
    (dotB F v (kappaV t m)).oneValue
      (BPair.ofNat m * dotB F v (thetaV t) + dotB F v (rhoV t)) := by
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hS : (elim.vecScale (BPair.ofNat m) (thetaV t)).length = t.rank :=
    (elim.length_vecScale _ _).trans (thetaV_length t)
  refine BPair.oneValue_trans
    (dotB_congrR F v _ _ (poly.pnorm_oneValue _)) ?_
  refine BPair.oneValue_trans
    (dotB_addR t F hshape v _ _ hv hS hrl) ?_
  exact BPair.add_congr
    (dotB_scaleR F (BPair.ofNat m) v (thetaV t))
    (BPair.oneValue_refl _)

/-- The tie equation (`prop:row`: a tie keeps the form's square):
a graded member sitting at the tower key's withdrawal of a key
carries that key's square joined to its doubled pairing with the
tower key, read on the pairing's lower side, at the sum's unit. -/
private theorem tieUnit (t : Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (W : List (List BPair × Bool)) (m : Nat)
    (hksq : sqAtRead F W (kappaV t m))
    (nu : List BPair) (hnu : nu.length = t.rank) (s : Bool)
    (hmem : (poly.pnorm (elim.vecAdd (kappaV t m) (poly.neg nu)), s)
      ∈ W) :
    (dotB F nu nu
      + ((dotB F nu (kappaV t m)).swap
        + (dotB F nu (kappaV t m)).swap)).oneValue BPair.unit := by
  have hy : (kappaV t m).length = t.rank := kappa_length t m
  have hng : (poly.neg nu).length = t.rank :=
    (ground.length_map BPair.swap nu).trans hnu
  have hsq := hksq _ hmem
  rw [elim.vecAdd_comm (kappaV t m) (poly.neg nu)] at hsq
  have hsp2 := dotB_sq_split t F hshape hgsym (poly.neg nu) (kappaV t m)
    hng hy
  -- the withdrawn key's own square and its cross pairing
  have hQ : (dotB F (poly.neg nu) (poly.neg nu)).oneValue
      (dotB F nu nu) := BPair.oneValue_of_eq (sertables.dotB_negSq F nu)
  have hS : dotB F (poly.neg nu) (kappaV t m)
      = (dotB F nu (kappaV t m)).swap :=
    elim.dotP_swap_left nu (elim.matVec F.gram (kappaV t m))
  refine BPair.oneValue_symm (BPair.add_cancel
    (c := dotB F (kappaV t m) (kappaV t m)) ?_)
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm hsq) ?_
  refine BPair.oneValue_trans hsp2 ?_
  rw [hS]
  exact BPair.add_congr (BPair.add_congr hQ (BPair.oneValue_refl _))
    (BPair.oneValue_refl _)


/-! The tie's arithmetic at the carrier: a balance pair and its own
partner join at the sum's unit, the positive member's case forces
the scaled θ-dot to the unit and the square to the doubled ρ-dot,
and the balance partner's case refutes outright. -/

/-- The positive member's tie: the square reads the doubled pairing,
so the scaled θ-dot sits at the sum's unit and the square at the
doubled ρ-dot (`prop:row`'s `κ(β^∨) = 1`). -/
private theorem tieSimple {Q R Mt : BPair}
    (h0 : (Q + ((Mt + R).swap + (Mt + R).swap)).oneValue BPair.unit)
    (hQle : Q ≤ R + R) (hmT : BPair.unit ≤ Mt) :
    Mt.oneValue BPair.unit ∧ (R + R).oneValue Q := by
  have hQD : Q.oneValue ((Mt + R) + (Mt + R)) := by
    refine BPair.add_cancel (c := (Mt + R).swap + (Mt + R).swap) ?_
    refine BPair.oneValue_trans h0 (BPair.oneValue_symm ?_)
    rw [BPair.add_add_comm (Mt + R) (Mt + R) (Mt + R).swap (Mt + R).swap]
    exact BPair.oneValue_trans
      (BPair.add_congr (ground.unitOfOne (BPair.oneValue_refl (Mt + R))) (ground.unitOfOne (BPair.oneValue_refl (Mt + R))))
      (BPair.add_unit BPair.unit)
  have hle : Mt + Mt ≤ BPair.unit := by
    have h1 : (Mt + Mt) + (R + R) ≤ R + R :=
      ground.leB_congr_left
        (BPair.oneValue_of_eq (BPair.add_add_comm Mt R Mt R))
        (ground.leB_congr_left hQD hQle)
    refine ground.leB_cancelL (x := R + R) ?_
    exact ground.leB_congr (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.oneValue_symm (BPair.add_unit (R + R))) h1
  have hmTu : Mt.oneValue BPair.unit :=
    ground.leB_antisymm
      (ground.leB_trans (ground.leB_congr_left (BPair.add_unit Mt)
        (ground.leB_add (ground.leB_refl Mt) hmT)) hle) hmT
  refine ⟨hmTu, BPair.oneValue_symm (BPair.oneValue_trans hQD ?_)⟩
  exact BPair.add_congr
    (BPair.oneValue_trans (BPair.add_congr hmTu (BPair.oneValue_refl R))
      (BPair.unit_add R))
    (BPair.oneValue_trans (BPair.add_congr hmTu (BPair.oneValue_refl R))
      (BPair.unit_add R))

/-- The balance partner's tie refutes: the square at or beyond the
unit joined to the doubled pairing on its own side sits strictly
above the sum's unit, the ρ-dot's strict read (`prop:row`: a
partner's case reads the doubled pairing on its lower side against
the square). -/
private theorem tieNeg {Q R Mt : BPair}
    (h0 : (Q + ((Mt + R) + (Mt + R))).oneValue BPair.unit)
    (hQnn : BPair.unit ≤ Q) (hmT : BPair.unit ≤ Mt)
    (hR : BPair.unit < R) : False := by
  have hMR : BPair.unit < Mt + R :=
    BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (BPair.oneValue_of_eq (BPair.add_comm R Mt))
      (ground.unitLtAdd hR hmT)
  have hE : BPair.unit < (Mt + R) + (Mt + R) :=
    ground.unitLtAdd hMR (ground.leB_of_lt hMR)
  have hfin : BPair.unit < Q + ((Mt + R) + (Mt + R)) :=
    BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (ground.unitLtAdd hE hQnn)
  exact absurd (BPair.lt_congr (BPair.oneValue_refl BPair.unit) h0 hfin)
    (by decide +kernel)

/-- The simple's scaled length sits off the sum's unit. -/
private theorem scaleLen_offUnit (t : Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hsp : simplePosRead t F) (hrd : rhoDotRead t F)
    {i : Nat} (hi : i < t.rank) :
    ¬ (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)).oneValue
        BPair.unit :=
  BPair.ofNat_off_unit _ (Nat.mul_pos hshape.2.2.1
    (memberchar.lenNums_pos t F hshape hsp hrd hgram hi))

/-! The letter's image of the tower key: the graded image list holds
it once on the flipped side and never on the key's own, the closure
read at the top and the letter's involution beneath it. -/

/-- The letter's image of the tower key sits in the graded list once
at the odd side and off it at the even. -/
private theorem topRefl (t : Table) (W : List (List BPair × Bool))
    (hsq : reflSquareRead t) (hclose : wCloseRead t W) (m : Nat)
    (htop : wTopAt W (kappaV t m)) {i : Nat} (hi : i < t.rank) :
    ground.countOf (reflAt t i (kappaV t m), true) W = 1
    ∧ ground.countOf (reflAt t i (kappaV t m), false) W = 0 :=
  ⟨(assembly.wCount_refl t W hclose hsq i hi (kappaV t m)
      (kappa_length t m) (kappa_norm t m) true).trans htop.1,
   (assembly.wCount_refl t W hclose hsq i hi (kappaV t m)
      (kappa_length t m) (kappa_norm t m) false).trans htop.2⟩

/-- The simples' coroot vectors part: two keys reading one normed
coroot vector are the same key, the Gram's defining diagonal read at
a coordinate probe. -/
private theorem distinctSimple (t : Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hsp : simplePosRead t F) (hrd : rhoDotRead t F)
    {i i' : Nat} (hi : i < t.rank) (hi' : i' < t.rank)
    (he : poly.pnorm (posCorootV t (ground.getAt 0 F.simplePos i))
      = poly.pnorm (posCorootV t (ground.getAt 0 F.simplePos i'))) :
    i = i' := by
  by_cases hii : i = i'
  · exact hii
  · exfalso
    have hz : ((List.range t.rank).map (fun k =>
        if k == i then BPair.ofNat 1 else BPair.unit)).length = t.rank :=
      ground.length_mapRange _ t.rank
    have hzr : ∀ q, q < t.rank → ground.getAt BPair.unit
        ((List.range t.rank).map (fun k =>
          if k == i then BPair.ofNat 1 else BPair.unit)) q
        = if q == i then BPair.ofNat 1 else BPair.unit := fun q hq => by
      rw [ground.getAt_map 0 BPair.unit _ (List.range t.rank) q
          (by rw [ground.length_range]; exact hq),
        ground.getAt_range t.rank q hq]
    have hone : poly.oneValue
        (posCorootV t (ground.getAt 0 F.simplePos i))
        (posCorootV t (ground.getAt 0 F.simplePos i')) := by
      refine poly.oneValue_trans
        (poly.oneValue_symm (poly.pnorm_oneValue _)) ?_
      rw [he]
      exact poly.pnorm_oneValue _
    have hcong := dotB_congrL F _ _ ((List.range t.rank).map (fun k =>
      if k == i then BPair.ofNat 1 else BPair.unit)) hone
    have hL := assembly.dotB_simple t F hshape hgram hsp hi _ hz
    have hR := assembly.dotB_simple t F hshape hgram hsp hi' _ hz
    rw [hzr i hi, if_pos (ground.eqBeqOf rfl)] at hL
    rw [hzr i' hi', if_neg (fun hb : (i' == i) = true =>
      hii (ground.beqEqOf hb).symm)] at hR
    refine scaleLen_offUnit t F hshape hgram hsp hrd hi ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.mul_ofNat_one _)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm hL) ?_
    exact BPair.oneValue_trans hcong
      (BPair.oneValue_trans hR (BPair.mul_unit _))

/-- The qualifying letter's key: at a coordinate whose scaled θ-dot
sits at the sum's unit the tower key's withdrawal of the simple's
normed coroot vector is the letter's own image. -/
private theorem qualKey (t : Table) (F : FundData)
    (hsp : simplePosRead t F) (m : Nat)
    {i : Nat} (hi : i < t.rank)
    (hq : (BPair.ofNat m
      * ground.getAt BPair.unit (thetaV t) i).oneValue BPair.unit) :
    poly.pnorm (elim.vecAdd (kappaV t m)
        (poly.neg (poly.pnorm
          (posCorootV t (ground.getAt 0 F.simplePos i)))))
      = reflAt t i (kappaV t m) :=
  (reflShift t F hsp hi (kappaV t m) (kappa_length t m)
    (BPair.oneValue_trans (kappa_entry t m hi)
      (BPair.oneValue_trans
        (BPair.add_congr hq (BPair.oneValue_refl (BPair.ofNat 1)))
        (BPair.unit_add (BPair.ofNat 1))))).symm


/-! The tie's two occupied cases at the θ content list: a positive
member's withdrawal names a simple at θ's coroot pair of equal
members, and a balance partner's withdrawal refuses. -/

/-- The positive member's occupied withdrawal: the tie names a
simple key whose scaled θ-dot sits at the sum's unit, the member the
simple's own (`prop:row`'s `κ(β^∨) = 1` at `β` simple). -/
private theorem keyOcc (t : Table) (F : FundData)
    (W : List (List BPair × Bool)) (m : Nat)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F) (hrho : rhoLenRead t F)
    (hdth : ∀ k, k < t.rank →
      BPair.unit ≤ ground.getAt BPair.unit (thetaV t) k)
    (hksq : sqAtRead F W (kappaV t m))
    {j : Nat} (hj : j < t.posFolds.length) (s : Bool)
    (hmem : (poly.pnorm (elim.vecAdd (kappaV t m)
        (poly.neg (poly.pnorm (posCorootV t j)))), s) ∈ W) :
    ∃ i, i < t.rank
      ∧ (BPair.ofNat m
          * ground.getAt BPair.unit (thetaV t) i).oneValue BPair.unit
      ∧ j = ground.getAt 0 F.simplePos i := by
  have hB : (posCorootV t j).length = t.rank := posCorootV_length t j
  have hnul : (poly.pnorm (posCorootV t j)).length = t.rank :=
    (poly.pnorm_length _).trans hB
  have htie := tieUnit t F hshape hgsym W m hksq
    (poly.pnorm (posCorootV t j)) hnul s hmem
  have hQ : (dotB F (poly.pnorm (posCorootV t j))
        (poly.pnorm (posCorootV t j))).oneValue
      (dotB F (posCorootV t j) (posCorootV t j)) :=
    BPair.oneValue_trans
      (dotB_congrL F _ _ _ (poly.pnorm_oneValue _))
      (dotB_congrR F _ _ _ (poly.pnorm_oneValue _))
  have hD : (dotB F (poly.pnorm (posCorootV t j)) (kappaV t m)).oneValue
      (BPair.ofNat m * dotB F (posCorootV t j) (thetaV t)
        + dotB F (posCorootV t j) (rhoV t)) :=
    BPair.oneValue_trans
      (dotB_congrL F _ _ _ (poly.pnorm_oneValue _))
      (dotB_kappa t F hshape m (posCorootV t j) hB)
  have h0 := BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.add_congr hQ
      (BPair.add_congr (ground.swap_congr hD) (ground.swap_congr hD))))
    htie
  obtain ⟨hmTu, hQRR⟩ := tieSimple h0 (hrho j hj).2.1
    (ground.leB_unit_mul m
      (assembly.dotB_pos_nonneg t F hshape hgram (thetaV t)
        (thetaV_length t) hdth j))
  obtain ⟨i, hi1, hji⟩ := (hrho j hj).2.2 hQRR
  have hi : i < t.rank := Nat.lt_of_succ_lt_succ hi1
  refine ⟨i, hi, ?_, hji⟩
  rw [hji] at hmTu
  have hTi := assembly.dotB_simple t F hshape hgram hsp hi (thetaV t) (thetaV_length t)
  have hmTu2 : (BPair.ofNat m
      * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
        * ground.getAt BPair.unit (thetaV t) i)).oneValue
      BPair.unit :=
    BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat m)) hTi))
      hmTu
  refine ground.mulCancel
    (scaleLen_offUnit t F hshape hgram hsp hrd hi) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm (BPair.mul_unit _))
  refine BPair.oneValue_trans (BPair.oneValue_of_eq ?_) hmTu2
  rw [← BPair.mul_assoc, ← BPair.mul_assoc,
    BPair.mul_comm (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i))
      (BPair.ofNat m)]

/-- The balance partner's occupied withdrawal refuses: the tie's
equation sits strictly above the sum's unit (`prop:row`: a partner's
case reads the doubled pairing on its lower side against the
square). -/
private theorem negRefute (t : Table) (F : FundData)
    (W : List (List BPair × Bool)) (m : Nat)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hrd : rhoDotRead t F)
    (hrho : rhoLenRead t F)
    (hdth : ∀ k, k < t.rank →
      BPair.unit ≤ ground.getAt BPair.unit (thetaV t) k)
    (hksq : sqAtRead F W (kappaV t m))
    {j : Nat} (hj : j < t.posFolds.length) (s : Bool)
    (hmem : (poly.pnorm (elim.vecAdd (kappaV t m)
        (poly.neg (poly.pnorm (poly.neg (posCorootV t j))))), s) ∈ W) :
    False := by
  have hB : (posCorootV t j).length = t.rank := posCorootV_length t j
  have hng : (poly.neg (posCorootV t j)).length = t.rank :=
    (ground.length_map BPair.swap _).trans hB
  have hnul : (poly.pnorm (poly.neg (posCorootV t j))).length
      = t.rank := (poly.pnorm_length _).trans hng
  have htie := tieUnit t F hshape hgsym W m hksq
    (poly.pnorm (poly.neg (posCorootV t j))) hnul s hmem
  have hQ : (dotB F (poly.pnorm (poly.neg (posCorootV t j)))
        (poly.pnorm (poly.neg (posCorootV t j)))).oneValue
      (dotB F (posCorootV t j) (posCorootV t j)) :=
    BPair.oneValue_trans
      (BPair.oneValue_trans
        (dotB_congrL F _ _ _ (poly.pnorm_oneValue _))
        (dotB_congrR F _ _ _ (poly.pnorm_oneValue _)))
      (BPair.oneValue_of_eq (sertables.dotB_negSq F (posCorootV t j)))
  have hD : (dotB F (poly.pnorm (poly.neg (posCorootV t j)))
        (kappaV t m)).oneValue
      ((BPair.ofNat m * dotB F (posCorootV t j) (thetaV t)
        + dotB F (posCorootV t j) (rhoV t)).swap) := by
    refine BPair.oneValue_trans
      (dotB_congrL F _ _ _ (poly.pnorm_oneValue _)) ?_
    rw [show dotB F (poly.neg (posCorootV t j)) (kappaV t m)
        = (dotB F (posCorootV t j) (kappaV t m)).swap from
      elim.dotP_swap_left (posCorootV t j)
        (elim.matVec F.gram (kappaV t m))]
    exact ground.swap_congr
      (dotB_kappa t F hshape m (posCorootV t j) hB)
  have hDs : (dotB F (poly.pnorm (poly.neg (posCorootV t j)))
      (kappaV t m)).swap.oneValue
      (BPair.ofNat m * dotB F (posCorootV t j) (thetaV t)
        + dotB F (posCorootV t j) (rhoV t)) := by
    have h := ground.swap_congr hD
    rw [BPair.swap_swap] at h
    exact h
  have h0 := BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.add_congr hQ
      (BPair.add_congr hDs hDs))) htie
  exact tieNeg h0 (ground.leB_of_lt (hrho j hj).1)
    (ground.leB_unit_mul m
      (assembly.dotB_pos_nonneg t F hshape hgram (thetaV t)
        (thetaV_length t) hdth j))
    (hrd j hj)

/-! The convolution read at the content list: the graded fold's own
exchange carries the product's side count onto the θ content list,
each member weighted by the graded image list's count at the tower
key's withdrawal of it. -/

/-! The two convolution counts at the tower key: the even side is
the coordinate count, the unit content's own, and the odd side
collects the qualifying simples, one each at the letter's image of
the key. -/

/-- The tower key's vacant withdrawal is the key itself. -/
private theorem kappaVacant (t : Table) (m : Nat) :
    poly.pnorm (elim.vecAdd (kappaV t m)
        (poly.neg (List.replicate t.rank BPair.unit))) = kappaV t m := by
  have hy : (kappaV t m).length = t.rank := kappa_length t m
  rw [poly.neg_repl t.rank]
  refine Eq.trans (poly.pnorm_congr _ (kappaV t m) ?_ ?_)
    (kappa_norm t m)
  · rw [elim.length_vecAdd (kappaV t m) _ t.rank hy
      (ground.length_replicate BPair.unit t.rank), hy]
  · exact elim.vecAdd_null_right (kappaV t m)
      (List.replicate t.rank BPair.unit)
      (hy.trans (ground.length_replicate BPair.unit t.rank).symm)
      (poly.unitTail_replicate t.rank)

/-- The even side reads the coordinate count: the unit content is
the one member whose withdrawal is the tower key itself, and the
key sits in the graded list once at the even side. -/
private theorem convFalse (t : Table) (F : FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair)) (m : Nat)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsq : reflSquareRead t)
    (hsp : simplePosRead t F) (hrd : rhoDotRead t F)
    (hrho : rhoLenRead t F)
    (hdth : ∀ k, k < t.rank →
      BPair.unit ≤ ground.getAt BPair.unit (thetaV t) k)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (htop : wTopAt W (kappaV t m))
    (hksq : sqAtRead F W (kappaV t m))
    (hmsh : memberchar.mShapeRead t L) (hfam : thetaFamRead t L) :
    memberchar.convCount W L (kappaV t m) false = t.rank := by
  have hy : (kappaV t m).length = t.rank := kappa_length t m
  have hyn : poly.pnorm (kappaV t m) = kappaV t m := kappa_norm t m
  rw [memberchar.convCount_wFold t W L hwsh hmsh (kappaV t m) hy hyn false]
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun nu => if List.replicate t.rank BPair.unit = nu then 1 else 0)
    L (fun nu hnu => ?_)) ?_
  · by_cases hz : List.replicate t.rank BPair.unit = nu
    · rw [if_pos hz, ← hz, kappaVacant t m]
      exact htop.1
    · rw [if_neg hz]
      match Nat.eq_zero_or_pos (ground.countOf
          (poly.pnorm (elim.vecAdd (kappaV t m) (poly.neg nu)),
            false) W) with
      | Or.inl h => exact h
      | Or.inr hpos =>
        exfalso
        have hmemW := ground.mem_of_countOf_pos _ W hpos
        match hfam.2.2 nu (ground.mem_of_countOf_pos nu L hnu) with
        | Or.inl he => exact hz he.symm
        | Or.inr ⟨j, hj1, hshapes⟩ =>
          have hj : j < t.posFolds.length := Nat.lt_of_succ_lt_succ hj1
          match hshapes with
          | Or.inl hpb =>
            rw [hpb] at hmemW
            obtain ⟨i, hi, hq, hji⟩ := keyOcc t F W m hshape hgram
              hgsym hsp hrd hrho hdth hksq hj false hmemW
            rw [hpb, hji, qualKey t F hsp m hi hq,
              (topRefl t W hsq hclose m htop hi).2] at hpos
            exact absurd hpos (Nat.lt_irrefl 0)
          | Or.inr hnb =>
            rw [hnb] at hmemW
            exact negRefute t F W m hshape hgram hgsym hrd hrho hdth
              hksq hj false hmemW
  · rw [← ground.countOf_fold (List.replicate t.rank BPair.unit) L]
    exact hfam.1

/-- The odd side collects the qualifying simples: each key at θ's
coroot pair of equal members contributes its content's single count
at the letter's image of the tower key. -/
private theorem convTrue (t : Table) (F : FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair)) (m : Nat)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsq : reflSquareRead t)
    (hsp : simplePosRead t F) (hrd : rhoDotRead t F)
    (hrho : rhoLenRead t F)
    (hdth : ∀ k, k < t.rank →
      BPair.unit ≤ ground.getAt BPair.unit (thetaV t) k)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (htop : wTopAt W (kappaV t m))
    (hksq : sqAtRead F W (kappaV t m))
    (hmsh : memberchar.mShapeRead t L) (hfam : thetaFamRead t L) :
    memberchar.convCount W L (kappaV t m) true
      = ground.famFold Nat.add 0 (fun i =>
          if (BPair.ofNat m
            * ground.getAt BPair.unit (thetaV t) i).oneValue BPair.unit
          then 1 else 0) (List.range t.rank) := by
  have hy : (kappaV t m).length = t.rank := kappa_length t m
  have hyn : poly.pnorm (kappaV t m) = kappaV t m := kappa_norm t m
  rw [memberchar.convCount_wFold t W L hwsh hmsh (kappaV t m) hy hyn true]
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun nu => ground.famFold Nat.add 0 (fun i =>
      (if (BPair.ofNat m
        * ground.getAt BPair.unit (thetaV t) i).oneValue BPair.unit
        then 1 else 0)
      * (if poly.pnorm (posCorootV t (ground.getAt 0 F.simplePos i))
          = nu then 1 else 0)) (List.range t.rank))
    L (fun nu hnu => ?_)) ?_
  · match Nat.eq_zero_or_pos (ground.countOf
        (poly.pnorm (elim.vecAdd (kappaV t m) (poly.neg nu)),
          true) W) with
    | Or.inr hpos =>
      have hmemW := ground.mem_of_countOf_pos _ W hpos
      match hfam.2.2 nu (ground.mem_of_countOf_pos nu L hnu) with
      | Or.inl he =>
        exfalso
        rw [he, kappaVacant t m, htop.2] at hpos
        exact absurd hpos (Nat.lt_irrefl 0)
      | Or.inr ⟨j, hj1, hshapes⟩ =>
        have hj : j < t.posFolds.length := Nat.lt_of_succ_lt_succ hj1
        match hshapes with
        | Or.inr hnb =>
          exact absurd hpos (fun _ => negRefute t F W m hshape hgram
            hgsym hrd hrho hdth hksq hj true (hnb ▸ hmemW))
        | Or.inl hpb =>
          rw [hpb] at hmemW
          obtain ⟨i0, hi0, hq0, hji0⟩ := keyOcc t F W m hshape hgram
            hgsym hsp hrd hrho hdth hksq hj true hmemW
          rw [hpb, hji0, qualKey t F hsp m hi0 hq0,
            (topRefl t W hsq hclose m htop hi0).1]
          refine Eq.symm (Eq.trans
            (ground.famFold_congr_members Nat.add 0 _
              (fun i => if i0 = i then 1 else 0) (List.range t.rank)
              (fun i hi => ?_)) ?_)
          · have hir : i < t.rank :=
              ground.ltOfMem hi
            by_cases hii : i0 = i
            · rw [if_pos hii, ← hii, if_pos hq0, if_pos rfl]
            · rw [if_neg hii]
              by_cases hE : poly.pnorm
                  (posCorootV t (ground.getAt 0 F.simplePos i))
                = poly.pnorm
                  (posCorootV t (ground.getAt 0 F.simplePos i0))
              · exact absurd (distinctSimple t F hshape hgram hsp hrd
                  hir hi0 hE).symm hii
              · rw [if_neg hE, Nat.mul_zero]
          · rw [← ground.countOf_fold i0 (List.range t.rank),
              ground.countOf_range i0 t.rank, if_pos hi0]
    | Or.inl h0 =>
      rw [h0]
      refine Eq.symm (Eq.trans (ground.famFold_congr_members Nat.add 0 _
        (fun _ => 0) (List.range t.rank) (fun i hi => ?_))
        (ground.famFold_zero (fun _ : Nat => (0 : Nat)) (fun _ => rfl)
          (List.range t.rank)))
      have hir : i < t.rank :=
        ground.ltOfMem hi
      by_cases hq : (BPair.ofNat m
          * ground.getAt BPair.unit (thetaV t) i).oneValue BPair.unit
      · by_cases hE : poly.pnorm
            (posCorootV t (ground.getAt 0 F.simplePos i)) = nu
        · exfalso
          rw [← hE, qualKey t F hsp m hir hq,
            (topRefl t W hsq hclose m htop hir).1] at h0
          exact Nat.noConfusion h0
        · rw [if_neg hE, Nat.mul_zero]
      · rw [if_neg hq, Nat.zero_mul]
  · rw [ground.famFold_swap (fun (nu : List BPair) (i : Nat) =>
      (if (BPair.ofNat m
        * ground.getAt BPair.unit (thetaV t) i).oneValue BPair.unit
        then 1 else 0)
      * (if poly.pnorm (posCorootV t (ground.getAt 0 F.simplePos i))
          = nu then 1 else 0)) L (List.range t.rank)]
    refine ground.famFold_congr_members Nat.add 0 _ _
      (List.range t.rank) (fun i hi => ?_)
    have hir : i < t.rank :=
      ground.ltOfMem hi
    rw [← ground.famFold_mul _ (fun nu =>
        if poly.pnorm (posCorootV t (ground.getAt 0 F.simplePos i))
          = nu then 1 else 0) L,
      ← ground.countOf_fold _ L,
      (hfam.2.1 (ground.getAt 0 F.simplePos i)
        (assembly.simplePos_lt t F hshape hir)).1,
      Nat.mul_one]


/-! The qualifying count at the two regimes: beyond the vacuum the
guard is θ's own coroot pair of equal members, `zCount`'s walk, and
at the vacuum every coordinate qualifies. -/

/-- θ's vacant coroot support as a guarded fold. -/
private theorem zCount_famFold (t : Table) :
    ground.famFold Nat.add 0 (fun j =>
      if (gentable.corootAt t t.thetaFold j).oneValue BPair.unit
      then 1 else 0) (List.range t.rank) = zCount t := by
  show _ = (List.range t.rank).foldl _ 0
  rw [ground.foldl_congr
      (fun acc j => if (gentable.corootAt t t.thetaFold j).oneValue
        BPair.unit then acc + 1 else acc)
      (fun acc j => acc + (if (gentable.corootAt t
        t.thetaFold j).oneValue BPair.unit then 1 else 0))
      (fun acc j => by
        by_cases h : (gentable.corootAt t t.thetaFold j).oneValue
          BPair.unit
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
          exact (Nat.add_zero acc).symm)
      (List.range t.rank) 0,
    ground.foldlSum _ (List.range t.rank) 0, Nat.zero_add]

/-- θ's coordinate read: the normed vector's entry is the fold's own
coroot pair at that key. -/
private theorem theta_entry (t : Table) {i : Nat} (hi : i < t.rank) :
    (ground.getAt BPair.unit (thetaV t) i).oneValue
      (gentable.corootAt t t.thetaFold i) := by
  show (ground.getAt BPair.unit
    (((List.range t.rank).map (gentable.corootAt t t.thetaFold)).map
      BPair.norm) i).oneValue _
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ i
      (by rw [ground.length_mapRange]; exact hi),
    ground.getAt_map_range BPair.unit _ t.rank i, if_pos hi]
  exact BPair.norm_oneValue _

/-- Beyond the vacuum the qualifying count is θ's vacant coroot
support: the scaled coordinate reads the sum's unit exactly where
the coordinate itself does. -/
private theorem qualCount_pos (t : Table) (m : Nat) (hm : 1 ≤ m) :
    ground.famFold Nat.add 0 (fun i =>
      if (BPair.ofNat m
        * ground.getAt BPair.unit (thetaV t) i).oneValue BPair.unit
      then 1 else 0) (List.range t.rank) = zCount t := by
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun j => if (gentable.corootAt t t.thetaFold j).oneValue BPair.unit
      then 1 else 0) (List.range t.rank) (fun i hi => ?_))
    (zCount_famFold t)
  have hir : i < t.rank := ground.ltOfMem hi
  by_cases hA : (BPair.ofNat m
      * ground.getAt BPair.unit (thetaV t) i).oneValue BPair.unit
  · refine Eq.trans (if_pos hA) (Eq.symm (if_pos ?_))
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (theta_entry t hir)) ?_
    refine ground.mulCancel (c := BPair.ofNat m)
      (BPair.ofNat_off_unit m hm) ?_
    exact BPair.oneValue_trans hA
      (BPair.oneValue_symm (BPair.mul_unit (BPair.ofNat m)))
  · refine Eq.trans (if_neg hA) (Eq.symm (if_neg (fun hB => hA ?_)))
    refine BPair.oneValue_trans (BPair.mul_congr
      (BPair.oneValue_refl (BPair.ofNat m))
      (BPair.oneValue_trans (theta_entry t hir) hB)) ?_
    exact BPair.mul_unit (BPair.ofNat m)

/-- At the vacuum every coordinate qualifies, the count the
coordinate count. -/
private theorem qualCount_zero (t : Table) :
    ground.famFold Nat.add 0 (fun i =>
      if (BPair.ofNat 0
        * ground.getAt BPair.unit (thetaV t) i).oneValue BPair.unit
      then 1 else 0) (List.range t.rank) = t.rank := by
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun _ => (1 : Nat)) (List.range t.rank) (fun i _ => ?_)) ?_
  · refine if_pos ?_
    exact BPair.oneValue_trans
      (BPair.mul_congr (by decide +kernel : (BPair.ofNat 0).oneValue BPair.unit)
        (BPair.oneValue_refl _))
      (BPair.unit_mul _)
  · rw [ground.famFold_length (List.range t.rank),
      ground.length_range t.rank]

/-! `prop:row`'s diagonal theorem: the tie analysis's two counts at
the tower key, the vacuum's defect beside them, and the display
corollary at a stated exhaustion. -/

/-- The core: at a tower key beyond the vacuum the two convolution
counts are the coordinate count on the even side and θ's vacant
coroot support on the odd (`prop:row`'s
`N^{mθ}_{θ,mθ} + z = ℓ` at every `m ≥ 1`). -/
theorem balanceValues (t : Table) (F : FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair)) (m : Nat)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsq : reflSquareRead t)
    (hsp : simplePosRead t F) (hrd : rhoDotRead t F)
    (hrho : rhoLenRead t F)
    (hdth : ∀ k, k < t.rank →
      BPair.unit ≤ ground.getAt BPair.unit (thetaV t) k)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (htop : wTopAt W (kappaV t m))
    (hksq : sqAtRead F W (kappaV t m))
    (hmsh : memberchar.mShapeRead t L)
    (hfam : thetaFamRead t L)
    (hm : 1 ≤ m) :
    memberchar.convCount W L (kappaV t m) false = t.rank
      ∧ memberchar.convCount W L (kappaV t m) true = zCount t :=
  ⟨convFalse t F W L m hshape hgram hgsym hsq hsp hrd hrho hdth hwsh
      hclose htop hksq hmsh hfam,
   Eq.trans (convTrue t F W L m hshape hgram hgsym hsq hsp hrd hrho hdth
      hwsh hclose htop hksq hmsh hfam) (qualCount_pos t m hm)⟩

/-- The vacuum: both counts read the coordinate count, the tie's
every simple at the pair one — `prop:row`'s defect, the Kronecker
delta at two labels. -/
theorem defectValues (t : Table) (F : FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsq : reflSquareRead t)
    (hsp : simplePosRead t F) (hrd : rhoDotRead t F)
    (hrho : rhoLenRead t F)
    (hdth : ∀ k, k < t.rank →
      BPair.unit ≤ ground.getAt BPair.unit (thetaV t) k)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (htop : wTopAt W (kappaV t 0))
    (hksq : sqAtRead F W (kappaV t 0))
    (hmsh : memberchar.mShapeRead t L)
    (hfam : thetaFamRead t L) :
    memberchar.convCount W L (kappaV t 0) false = t.rank
      ∧ memberchar.convCount W L (kappaV t 0) true = t.rank :=
  ⟨convFalse t F W L 0 hshape hgram hgsym hsq hsp hrd hrho hdth hwsh
      hclose htop hksq hmsh hfam,
   Eq.trans (convTrue t F W L 0 hshape hgram hgsym hsq hsp hrd hrho hdth
      hwsh hclose htop hksq hmsh hfam) (qualCount_zero t)⟩

/-- The display corollary at a stated exhaustion: the diagonal's
value is θ's occupied coroot support (`prop:row`'s
`N^{mθ}_{θ,mθ} = ℓ − z`). -/
theorem diagRead (t : Table) (F : FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (cVs : List (List BPair)) (m : Nat)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsq : reflSquareRead t)
    (hsp : simplePosRead t F) (hrd : rhoDotRead t F)
    (hrho : rhoLenRead t F)
    (hdth : ∀ k, k < t.rank →
      BPair.unit ≤ ground.getAt BPair.unit (thetaV t) k)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (htop : wTopAt W (kappaV t m))
    (hksq : sqAtRead F W (kappaV t m))
    (hmsh : memberchar.mShapeRead t L)
    (hfam : thetaFamRead t L)
    (hm : 1 ≤ m)
    (hmem : steinberg.memberAt t W L cVs
      (poly.pnorm (elim.vecScale (BPair.ofNat m) (thetaV t)))) :
    ground.countOf
        (poly.pnorm (elim.vecScale (BPair.ofNat m) (thetaV t)))
        cVs = supportCount t := by
  have hkey : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecScale (BPair.ofNat m) (thetaV t)))
      (rhoV t)) = kappaV t m :=
    elim.pnorm_vecAdd_left (elim.vecScale (BPair.ofNat m) (thetaV t))
      (rhoV t)
      (((elim.length_vecScale _ _).trans (thetaV_length t)).trans
        (ground.length_replicate (BPair.ofNat 1) t.rank).symm)
  obtain ⟨hfalse, htrue⟩ := balanceValues t F W L m hshape hgram hgsym
    hsq hsp hrd hrho hdth hwsh hclose htop hksq hmsh hfam hm
  have hmem' : ground.countOf
      (poly.pnorm (elim.vecScale (BPair.ofNat m) (thetaV t))) cVs
      + memberchar.convCount W L (kappaV t m) true
    = memberchar.convCount W L (kappaV t m) false := by
    rw [← hkey]
    exact hmem
  rw [hfalse, htrue] at hmem'
  exact ground.addCancelR (zCount t)
    (hmem'.trans (supportCount_zCount t).symm)


/-- The vacuum's display at a stated exhaustion: the vacant
weight's channel count is the sum's own seed, the Kronecker defect
at the tower's foot (`prop:row`: the vacuum's ties read every
simple at the pair one, the count the Kronecker delta at two
labels). -/
theorem defectRead (t : Table) (F : FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (cVs : List (List BPair))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsq : reflSquareRead t)
    (hsp : simplePosRead t F) (hrd : rhoDotRead t F)
    (hrho : rhoLenRead t F)
    (hdth : ∀ k, k < t.rank →
      BPair.unit ≤ ground.getAt BPair.unit (thetaV t) k)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (htop : wTopAt W (kappaV t 0))
    (hksq : sqAtRead F W (kappaV t 0))
    (hmsh : memberchar.mShapeRead t L)
    (hfam : thetaFamRead t L)
    (hmem : steinberg.memberAt t W L cVs
      (poly.pnorm (elim.vecScale (BPair.ofNat 0) (thetaV t)))) :
    ground.countOf
        (poly.pnorm (elim.vecScale (BPair.ofNat 0) (thetaV t)))
        cVs = 0 := by
  have hkey : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecScale (BPair.ofNat 0) (thetaV t)))
      (rhoV t)) = kappaV t 0 :=
    elim.pnorm_vecAdd_left (elim.vecScale (BPair.ofNat 0) (thetaV t))
      (rhoV t)
      (((elim.length_vecScale _ _).trans (thetaV_length t)).trans
        (ground.length_replicate (BPair.ofNat 1) t.rank).symm)
  obtain ⟨hfalse, htrue⟩ := defectValues t F W L hshape hgram hgsym
    hsq hsp hrd hrho hdth hwsh hclose htop hksq hmsh hfam
  have hmem' : ground.countOf
      (poly.pnorm (elim.vecScale (BPair.ofNat 0) (thetaV t))) cVs
      + memberchar.convCount W L (kappaV t 0) true
    = memberchar.convCount W L (kappaV t 0) false := by
    rw [← hkey]
    exact hmem
  rw [hfalse, htrue] at hmem'
  exact ground.addCancelR t.rank
    (hmem'.trans (Nat.zero_add t.rank).symm)

end row
