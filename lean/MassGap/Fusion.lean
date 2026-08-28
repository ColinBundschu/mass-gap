import MassGap.Repring
import MassGap.Adjchar
import MassGap.Xfusion
/-!
`con:fusion` — the fusion interface: the calculus's outputs the
chain reads are one interface, its fields the structure a member
instantiation fills.  The fields carried here are the ones the
carrier layer reads (`def:carrier`, `prop:windowfinite`,
`def:pencil`'s consumers): the label data — the equality read with
each label equal to itself (`eqLRefl`), the
unit, the involution, the composition and the self-dual `θ`; the
fusion count with the row's support list; the dimension; the
weight-free Casimir at the cleared pair (`c2N` over the one second
member `c2D`); the base `c₁`; the below-cutoff enumeration
(`below`, the nonunit labels at the cleared Casimir at or below a
stated natural, the window index's finiteness datum); and the
class data (`lem:chargedcell`'s charged layer) — the class code
per label (`cls`, the `d_f`-ality at the label calculus), the
class group's sum (`clsAdd`) and the winding floor per class
(`clsFloorN`, the endpoint's numerator at the one second member
`c2D`).  The count laws, the dimension identity, the Casimir's
positivity at nonunit labels, the Cartan strictness, the drift
identity and the class laws — the row's additivity, the dual's
join to the unit class and `θ`'s unit class — are
the stated reads over the structure; the commutativity and the
unit law hold at the label instantiation as theorems
(`commLaw_dataA` at `labels.countL_comm`, `unitLaw_dataA` at
`repring.unitRead_all`), the further laws each an
instantiation's pin.
The remaining interface fields land with their consumers: the
channel list at the sector's own reads
(`con:xfusion`, `thm:xdata` — `θ`'s content list standing at
`adjchar.multRead`), the Casimir's floor at its consumers
(`lem:casfloor`'s descent, `lem:freeend`), its dominance growth
along a row at `prop:fusionfinite`'s layer, the form caps at
`lem:fpcap` — the two-sided dimension cap at the eigen-identity's
rows, with the loop windows' reads and the loop-cut tier at
`lem:loopcap` (`con:coeff`'s pairing), `thm:truncation` the
consumer — the evaluation identity and the
presentation at the pairing's layer (`prop:wg`), and the series
tier's polynomial-pair reads at the rank-stability layer
(`lem:rankstable`; `lem:serstable`).  The label calculus
instantiates every carried field (`dataA`), each instantiating
read the field's own derivation at its module; the member and
series instantiations at the weight tables read at `Memberdata`
(`con:fusion`'s member clause at `lem:memberdata`'s count and
involution constructions).
-/

namespace fusion
open ground places

set_option genInjectivity false in
/-- The fusion interface's carried fields over a label type: the
label data, the count with its row support, the dimension, the
cleared Casimir, the base, and the below-cutoff enumeration. -/
structure Data (L : Type) where
  eqL : L → L → Bool
  eqLRefl : ∀ l, eqL l l = true
  unit : L
  dual : L → L
  add : L → L → L
  theta : L
  count : L → L → L → Nat
  row : L → L → List L
  dim : L → Nat
  c2N : L → Nat
  c2D : Nat
  c1 : Nat
  below : Nat → List L
  cls : L → Nat
  clsAdd : Nat → Nat → Nat
  clsFloorN : Nat → Nat

/-- The unit read `N^𝟏_{ab} = δ_{a b̄}` at the interface. -/
def unitLaw {L : Type} (F : Data L) (a b : L) : Prop :=
  F.count a b F.unit = (if F.eqL a (F.dual b) then 1 else 0)

instance {L : Type} (F : Data L) (a b : L) :
    Decidable (unitLaw F a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The commutativity read at the interface. -/
def commLaw {L : Type} (F : Data L) (a b c : L) : Prop :=
  F.count a b c = F.count b a c

instance {L : Type} (F : Data L) (a b c : L) :
    Decidable (commLaw F a b c) :=
  inferInstanceAs (Decidable (_ = _))

/-- The row-is-support law at the interface: a label is a
constituent exactly where it sits on the row, the row reading it
once — the row the occupied constituent set
(`prop:fusionfinite`'s row, `prop:algebra`'s displayed sums its
folds). -/
def rowLaw {L : Type} [DecidableEq L] (F : Data L) (a b c : L) :
    Prop :=
  (0 < F.count a b c ↔ 0 < ground.countOf c (F.row a b))
  ∧ ground.countOf c (F.row a b) ≤ 1

instance {L : Type} [DecidableEq L] (F : Data L) (a b c : L) :
    Decidable (rowLaw F a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The Cartan strictness read `N^{a+b}_{ab} = 1` at the
interface's composition. -/
def cartanLaw {L : Type} (F : Data L) (a b : L) : Prop :=
  F.count a b (F.add a b) = 1

instance {L : Type} (F : Data L) (a b : L) :
    Decidable (cartanLaw F a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The associativity read at the interface, the folds over the
two rows. -/
def assocLaw {L : Type} (F : Data L) (a b c dd : L) : Prop :=
  ((F.row a b).foldl (fun acc e =>
      acc + F.count a b e * F.count e c dd) 0)
    = ((F.row b c).foldl (fun acc f =>
      acc + F.count b c f * F.count a f dd) 0)

instance {L : Type} (F : Data L) (a b c dd : L) :
    Decidable (assocLaw F a b c dd) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dimension identity `Σ_c N^c_{ab} d_c = d_a d_b` over the
row's support. -/
def dimLaw {L : Type} (F : Data L) (a b : L) : Prop :=
  ((F.row a b).foldl (fun acc c =>
      acc + F.count a b c * F.dim c) 0)
    = F.dim a * F.dim b

instance {L : Type} (F : Data L) (a b : L) :
    Decidable (dimLaw F a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The weight-free Casimir's positivity at a nonunit label. -/
def casPos {L : Type} (F : Data L) (l : L) : Prop :=
  (F.eqL l F.unit || decide (0 < F.c2N l)) = true

instance {L : Type} (F : Data L) (l : L) : Decidable (casPos F l) :=
  inferInstanceAs (Decidable (_ = _))

/-- The unit's one spelling over a stated list: each member off the
unit's class or the unit label itself — a label list reading
`def:carrier`'s data (the support's labels nonunit, the vacant key
the unit) at the one reduced spelling per label. -/
def oneUnit {L : Type} [DecidableEq L] (F : Data L)
    (l : List L) : Prop :=
  (l.all (fun m => (!(F.eqL m F.unit)) || (m == F.unit))) = true

instance {L : Type} [DecidableEq L] (F : Data L) (l : List L) :
    Decidable (oneUnit F l) :=
  inferInstanceAs (Decidable (_ = _))

/-- The unit spelling's member read: an occupied member at the
unit's class is the unit label. -/
theorem oneUnit_read {L : Type} [DecidableEq L] (F : Data L)
    (cov : List L) (h : oneUnit F cov) (x : L)
    (hx : 0 < ground.countOf x cov)
    (hq : F.eqL x F.unit = true) : x = F.unit := by
  have hb := ground.all_of_mem _ cov h x
    (ground.mem_of_countOf_pos x cov hx)
  cases ground.orSplitB hb with
  | inl h1 =>
    rw [hq] at h1
    exact Bool.noConfusion h1
  | inr h2 => exact ground.beqEqOf h2

/-- The drift identity, uniform in the label (`thm:drift`),
cleared at the one second member:
`Σ_k m_k d_k ĉ₂(k) = d_R d_θ (ĉ₂(R) + 1)` over the label's
adjoint row, the adjoint square's read its `θ` instance. -/
def driftLaw {L : Type} (F : Data L) (r : L) : Prop :=
  ((F.row r F.theta).foldl (fun acc c =>
      acc + F.count r F.theta c * F.dim c * F.c2N c) 0)
    = F.dim r * F.dim F.theta * (F.c2N r + F.c2D)

instance {L : Type} (F : Data L) (r : L) :
    Decidable (driftLaw F r) :=
  inferInstanceAs (Decidable (_ = _))

/-- The adjoint square's occupied channels over a label list: each
label of positive count against the adjoint pair at its weight
numerator `m d` and its Casimir numerator, a vacant label
skipped. -/
def adjRow {L : Type} (F : Data L) : List L → List (Nat × Nat)
  | [] => []
  | k :: ks =>
    match F.count F.theta F.theta k * F.dim k with
    | 0 => adjRow F ks
    | m + 1 => (m + 1, F.c2N k) :: adjRow F ks

/-- The `θ`-square channel list at its occupied data, the adjoint
row's channels at their weight numerators and Casimir numerators. -/
def adjChannels {L : Type} (F : Data L) : List (Nat × Nat) :=
  adjRow F (F.row F.theta F.theta)

/-- The class additivity read over a row: every occupied fusion
target's class is the factors' classes' sum, the class data's
vertex-law carrier. -/
def clsLaw {L : Type} (F : Data L) (a b : L) : Prop :=
  ((F.row a b).all (fun c =>
    Nat.beq (F.cls c) (F.clsAdd (F.cls a) (F.cls b)))) = true

instance {L : Type} (F : Data L) (a b : L) :
    Decidable (clsLaw F a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dual's class joins its label's to the unit class. -/
def clsDualLaw {L : Type} (F : Data L) (a : L) : Prop :=
  F.clsAdd (F.cls (F.dual a)) (F.cls a) = F.cls F.unit

instance {L : Type} (F : Data L) (a : L) :
    Decidable (clsDualLaw F a) :=
  inferInstanceAs (Decidable (_ = _))

/-- `θ`'s class the unit class, the magnetic member's own read. -/
def clsThetaLaw {L : Type} (F : Data L) : Prop :=
  F.cls F.theta = F.cls F.unit

instance {L : Type} (F : Data L) : Decidable (clsThetaLaw F) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dual label's Casimir is its label's own (`def:c2hat`'s
one-value read at the interface): the electric fold is blind to an
orientation reversal (`thm:restoration`). -/
def casDualLaw {L : Type} (F : Data L) (a : L) : Prop :=
  F.c2N (F.dual a) = F.c2N a

instance {L : Type} (F : Data L) (a : L) :
    Decidable (casDualLaw F a) :=
  inferInstanceAs (Decidable (_ = _))

/-- The self-dual theta (`con:fusion`'s field), the magnetic fold's
own blindness at a reversed boundary word (`thm:restoration`). -/
def thetaSelfDual {L : Type} (F : Data L) : Prop :=
  F.eqL (F.dual F.theta) F.theta = true

instance {L : Type} (F : Data L) : Decidable (thetaSelfDual F) :=
  inferInstanceAs (Decidable (_ = _))

/-- The below-cutoff enumeration's soundness: every member reads
its cleared Casimir at or below the stated natural. -/
def belowSound {L : Type} (F : Data L) (k : Nat) : Prop :=
  ((F.below k).all (fun l => F.c2N l ≤ k)) = true

instance {L : Type} (F : Data L) (k : Nat) :
    Decidable (belowSound F k) :=
  inferInstanceAs (Decidable (_ = _))

/-- The keyed lookup at a stated equality read, the stored lists'
one scan. -/
def lookupBy {L : Type} {α : Type} (eq : L → L → Bool)
    (k : L) : List (L × α) → Option α
  | [] => none
  | p :: t => if eq p.1 k then some p.2 else lookupBy eq k t

/-- The interface tabulated below a cutoff, the window
enumerations' lookup route: the counts and rows stored once over
the below-cutoff labels with the unit, the reads the stored
lists' scans — a read off the stored keys at any position falls
back to the interface — one value with the interface at every
read, the coherence the check module's pin. -/
def tabulate {L : Type} (F : Data L) (K : Nat) : Data L :=
  let ls := F.unit :: F.below K
  let tab := ls.map (fun a => (a, ls.map (fun b =>
    (b, (F.row a b).map (fun c => (c, F.count a b c))))))
  { F with
    count := fun a b c =>
      match lookupBy F.eqL a tab with
      | none => F.count a b c
      | some rowA =>
        match lookupBy F.eqL b rowA with
        | none => F.count a b c
        | some r =>
          match lookupBy F.eqL c r with
          | none => F.count a b c
          | some n => n
    row := fun a b =>
      match lookupBy F.eqL a tab with
      | none => F.row a b
      | some rowA =>
        match lookupBy F.eqL b rowA with
        | none => F.row a b
        | some r => r.map (fun p => p.1) }

/-- The label calculus's instantiation at a fundamental count: the
reduced shapes with `con:labels`' data, the fast fold's count at
the matched-degree lift, the row's support over the matched-degree
shapes reduced, `cor:weyldim`'s dimension, `def:c2hat`'s cleared
pair, `con:xfusion`'s base, the enumeration over the degree
window at the Casimir filter, and the class data at the box
count's remainder — the `d_f`-ality — with the endpoint floor's
numerator `j g_j (r+2)` at the complement gap. -/
def dataA (d : Nat) : Data Shape :=
  ⟨(fun a b => labels.reduce a == labels.reduce b),
   (fun l => ground.listEqBeq (labels.reduce l)),
   labels.unitL d, labels.dualL, places.addS,
   adjchar.theta d, labels.countL,
   (fun a b => (allShapes d (degree a + degree b)).filterMap
     (fun c => if 0 < steinberg.count a b c then
        some (labels.reduce c) else none)),
   weyldim.dimOf, c2hat.dfQ, 2 * d * d, xfusion.c1 d,
   (fun k => (List.range (k + 1)).flatMap (fun j =>
     (allShapes (d - 1) j).filterMap (fun s =>
       if 0 < j && c2hat.dfQ (s ++ [0]) ≤ k then some (s ++ [0])
       else none))),
   (fun s => places.degree s % d), (fun x y => (x + y) % d),
   (fun j => j * (d - j) * (d + 1))⟩

/-- The commutativity law holds at the `A`-series data outright:
the interface's count is the label count, whose exchange is
`labels.countL_comm` — `prop:repring`'s read discharged as a
theorem at every label triple of one width. -/
theorem commLaw_dataA (d : Nat) (a b c : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length) :
    commLaw (dataA d) a b c :=
  labels.countL_comm a b c hba hca

/-- The unit law at the label instantiation: the unit label's
count in the product is one exactly at the dual label,
`repring.unitRead_all`'s read at the involution's representative
(`labels.reduce_dualL`). -/
theorem unitLaw_dataA (d : Nat) (a b : Shape)
    (hba : b.length = a.length) (hd : a.length = d) :
    unitLaw (dataA d) a b := by
  have h := repring.unitRead_all a b hba
  show labels.countL a b (labels.unitL d)
    = (if (labels.reduce a == labels.reduce (labels.dualL b))
       then 1 else 0)
  rw [← hd, labels.reduce_dualL b, h]
  cases hq : (labels.reduce a == labels.dualL b) with
  | true =>
    rw [if_pos (ground.listBeqEq hq)]
    rfl
  | false =>
    rw [if_neg (fun he => by
      rw [he] at hq
      exact Bool.noConfusion
        ((ground.listEqBeq (labels.dualL b)).symm.trans hq))]
    rfl


/-- The label count is one value at the class in the first
argument: the reduced representative differs from the label by the
lift's own full columns (`labels.countL_addFullsA`). -/
private theorem countL_reduceL (x y z : Shape)
    (hyx : y.length = x.length) (hzx : z.length = x.length) :
    labels.countL (labels.reduce x) y z = labels.countL x y z := by
  cases x with
  | nil => rfl
  | cons p t =>
    match ground.snoc_split t.length (p :: t) rfl with
    | ⟨s', j, hs, _⟩ =>
      have hsl : (s' ++ [0] : Shape).length = (p :: t : Shape).length := by
        rw [ground.length_append s' [0], hs,
          ground.length_append s' [j]]
        rfl
      have h1 : labels.addFulls j (s' ++ [0]) = s' ++ [j] := by
        rw [labels.addFulls_snoc j s' 0, Nat.zero_add]
      rw [hs, labels.reduce_snoc s' j, ← h1]
      exact (labels.countL_addFullsA j (s' ++ [0]) y z
        (hyx.trans hsl.symm) (hzx.trans hsl.symm)).symm

/-- The row's fold at the interface reads the matched-degree
enumeration's own: the row lists the enumeration's occupied
members reduced, each contributing its own count against the
weight, and the refused members contribute the sum's unit — the
reduced member's count is the shape's (`labels.countL_reduce`) and
the weight reads one value along the class. -/
private theorem rowFold (x y : Shape) (W : Shape → Nat)
    (hW : ∀ v : Shape, v.length = x.length →
      W (labels.reduce v) = W v) :
    ground.famFold Nat.add 0
      (fun v => optVal (fun e => labels.countL x y e * W e)
        (if 0 < steinberg.count x y v then some (labels.reduce v)
         else none))
      (allShapes x.length (degree x + degree y))
    = ground.famFold Nat.add 0
      (fun e => steinberg.count x y e * W e)
      (allShapes x.length (degree x + degree y)) := by
  refine ground.famFold_congr_members Nat.add 0 _ _
    (allShapes x.length (degree x + degree y)) ?_
  intro v hv
  obtain ⟨hvl, hvd⟩ := allShapes_sound x.length (degree x + degree y) v
    (ground.mem_of_countOf_pos v _ hv)
  show optVal (fun e => labels.countL x y e * W e)
      (if 0 < steinberg.count x y v then some (labels.reduce v)
       else none)
    = steinberg.count x y v * W v
  cases Nat.eq_zero_or_pos (steinberg.count x y v) with
  | inl hz =>
    rw [if_neg (by rw [hz]; exact Nat.lt_irrefl 0), hz, Nat.zero_mul]
    rfl
  | inr hp =>
    rw [if_pos hp]
    show labels.countL x y (labels.reduce v) * W (labels.reduce v)
      = steinberg.count x y v * W v
    rw [labels.countL_reduce x y v hvl hvd, hW v hvl]

/-- The associativity law at the label instantiation: the two
pairings' folds over the interface's rows read one value,
`repring.assocRead_all`'s display carried onto the rows — the row
lists the matched-degree enumeration's occupied members reduced,
each reduced member's count the shape's own
(`labels.countL_reduce`) and each weight one value along the class
(`labels.countL_addFullsA`, `labels.countL_comm`).  The width tie
`hd` reads the row's own carrier. -/
theorem assocLaw_dataA (d : Nat) (a b c dd : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hdd : dd.length = a.length) (hd : a.length = d) :
    assocLaw (dataA d) a b c dd := by
  have hcb : c.length = b.length := hca.trans hba.symm
  have hWL : ∀ v : Shape, v.length = a.length →
      labels.countL (labels.reduce v) c dd
        = labels.countL v c dd :=
    fun v hvl => countL_reduceL v c dd (hca.trans hvl.symm)
      (hdd.trans hvl.symm)
  have hWR : ∀ v : Shape, v.length = b.length →
      labels.countL a (labels.reduce v) dd
        = labels.countL a v dd := by
    intro v hvl
    have hva : v.length = a.length := hvl.trans hba
    have hrl : (labels.reduce v).length = a.length :=
      (labels.length_reduce v).trans hva
    rw [labels.countL_comm a (labels.reduce v) dd hrl hdd,
      labels.countL_comm a v dd hva hdd]
    exact countL_reduceL v a dd hva.symm (hdd.trans hva.symm)
  have hrowR := rowFold b c (fun f => labels.countL a f dd) hWR
  rw [hba] at hrowR
  show (((allShapes d (degree a + degree b)).filterMap
      (fun c' => if 0 < steinberg.count a b c' then
        some (labels.reduce c') else none)).foldl
      (fun acc e => acc + labels.countL a b e * labels.countL e c dd) 0)
    = (((allShapes d (degree b + degree c)).filterMap
      (fun c' => if 0 < steinberg.count b c c' then
        some (labels.reduce c') else none)).foldl
      (fun acc f => acc + labels.countL b c f * labels.countL a f dd) 0)
  rw [← hd,
    ground.foldlSum
      (fun e => labels.countL a b e * labels.countL e c dd)
      ((allShapes a.length (degree a + degree b)).filterMap
        (fun c' => if 0 < steinberg.count a b c' then
          some (labels.reduce c') else none)) 0,
    ground.foldlSum
      (fun f => labels.countL b c f * labels.countL a f dd)
      ((allShapes a.length (degree b + degree c)).filterMap
        (fun c' => if 0 < steinberg.count b c c' then
          some (labels.reduce c') else none)) 0,
    ground.famFold_filterMap
      (fun c' => if 0 < steinberg.count a b c' then
        some (labels.reduce c') else none)
      (fun e => labels.countL a b e * labels.countL e c dd)
      (allShapes a.length (degree a + degree b)),
    ground.famFold_filterMap
      (fun c' => if 0 < steinberg.count b c c' then
        some (labels.reduce c') else none)
      (fun f => labels.countL b c f * labels.countL a f dd)
      (allShapes a.length (degree b + degree c)),
    rowFold a b (fun e => labels.countL e c dd) hWL, hrowR,
    labels.countL_assoc a b c dd hba hca hdd]

end fusion
