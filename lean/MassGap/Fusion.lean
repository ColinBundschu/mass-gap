import MassGap.Repring
import MassGap.Adjchar
import MassGap.Xfusion
import MassGap.Fiber
import MassGap.Fusiondata
import MassGap.Form
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
stated natural, the window index's finiteness datum, nested across
cutoffs as the larger enumeration's filter at the smaller cutoff
(`belowNest`) and listing nonunit labels alone (`belowNonunit`),
both laws theorems at the `A`-series, `belowNest_dataA` and
`belowNonunit_dataA`); and the
class data (`lem:chargedcell`'s charged layer) — the class code
per label (`cls`, the `d_f`-ality at the label calculus), the
class group's sum (`clsAdd`) and the winding floor per class
(`clsFloorN`, the endpoint's numerator at the one second member
`c2D`); and the presentation field: at a vertex's incident ends,
the labels with their orientations, the fiber's vertex list in the
ends' slot power at the member's generating table (`pres`,
`fiber.Pres`: the table, the vertex list, the link list, the
boundary factor's word with its coevaluation and the unit's term
read; the label calculus's own at `fiber.presA` and a member's at
`fiber.presT` over `con:memtable`'s tables), the Gram the derived
read `vertGramOf`, the list's own `fiber.listGram` where the list
is stated and the two-end coevaluation's count at the label data
off it (`fiber.twoEndGram`, `lem:dualread`(i), vacant at a further
vertex).
The count laws, the dimension identity, the Casimir's
positivity at nonunit labels, the Cartan strictness, the drift
identity and the class laws — the row's additivity, the dual's
join to the unit class and `θ`'s unit class — are
the stated reads over the structure; the commutativity, the
unit, the associativity, the dimension and the row-is-support laws
hold at the label instantiation as theorems (`commLaw_dataA` at
`labels.countL_comm`, `unitLaw_dataA` at `repring.unitRead_all`,
`assocLaw_dataA` at `labels.countL_assoc`, `dimLaw_dataA` at
`repring.dimRead_all` through `labels.rowFold`, `unitRowLaw_dataA`
at the unit's first factor on the enumerated row, `rowLaw_dataA` at the
lift's reads and the enumeration's), each over the width-`d`
labels, the reduced shapes of the stated width (`labelA`, the
domain the rows and the involution keep). Casimir positivity is
`casPos_dataA` at the degree floor, the cutoff bound is
`belowSound_dataA` at the filter, and the involution preserves the
Casimir and dimension by `labels.casDual_all` and
`labels.dimDual_all`; `thetaSelfDual_dataA` reads the adjoint's
complement at `form.dualL_theta`.
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
cleared Casimir, the base, the derived residue, and the below-cutoff
enumeration. -/
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
  residue : Nat
  below : Nat → List L
  cls : L → Nat
  clsAdd : Nat → Nat → Nat
  clsFloorN : Nat → Nat
  pres : fiber.Pres L

/-- The vertex Gram at the interface: the vertex list's own where
the list is stated, and off it the two-end coevaluation's count at
the label data (`con:fiber`: a vertex of two ends reads its block's
coevaluation, self-paired at the block's count). -/
def vertGramOf {L : Type} (F : Data L) (es : List (L × Bool)) :
    Option (elim.Mat × Pos) :=
  match F.pres.vertList es with
  | some l => some (fiber.listGram l)
  | none => fiber.twoEndGram F.eqL F.dual F.dim es

/-- The window's floor read: every below-cutoff label's Casimir at
or beyond the floor, `lem:casfloor`'s read at the window's own
labels. -/
def belowFloor {L : Type} (F : Data L) (K f : Nat) : Prop :=
  ((F.below K).all (fun l => f ≤ F.c2N l)) = true

instance instFusion18 {L : Type} (F : Data L) (K f : Nat) :
    Decidable (belowFloor F K f) :=
  inferInstanceAs (Decidable (_ = _))

/-- The unit read `N^𝟏_{ab} = δ_{a b̄}` at the interface. -/
def unitLaw {L : Type} (F : Data L) (a b : L) : Prop :=
  F.count a b F.unit = (if F.eqL a (F.dual b) then 1 else 0)

instance instFusion1 {L : Type} (F : Data L) (a b : L) :
    Decidable (unitLaw F a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The commutativity read at the interface. -/
def commLaw {L : Type} (F : Data L) (a b c : L) : Prop :=
  F.count a b c = F.count b a c

instance instFusion2 {L : Type} (F : Data L) (a b c : L) :
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

instance instFusion3 {L : Type} [DecidableEq L] (F : Data L) (a b c : L) :
    Decidable (rowLaw F a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The unit's row at the interface: the unit label's fusion row at
a label is that label alone, the count law `N^c_{1b} = δ_{cb}` read
on the row (`prop:algebra`'s unit identity at `prop:fusionfinite`'s
row). -/
def unitRowLaw {L : Type} [DecidableEq L] (F : Data L) (b : L) : Prop :=
  F.row F.unit b = [b]

instance instFusion17 {L : Type} [DecidableEq L] (F : Data L) (b : L) :
    Decidable (unitRowLaw F b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The Cartan strictness read `N^{a+b}_{ab} = 1` at the
interface's composition. -/
def cartanLaw {L : Type} (F : Data L) (a b : L) : Prop :=
  F.count a b (F.add a b) = 1

instance instFusion4 {L : Type} (F : Data L) (a b : L) :
    Decidable (cartanLaw F a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The associativity read at the interface, the folds over the
two rows. -/
def assocLaw {L : Type} (F : Data L) (a b c dd : L) : Prop :=
  ((F.row a b).foldl (fun acc e =>
      acc + F.count a b e * F.count e c dd) 0)
    = ((F.row b c).foldl (fun acc f =>
      acc + F.count b c f * F.count a f dd) 0)

instance instFusion5 {L : Type} (F : Data L) (a b c dd : L) :
    Decidable (assocLaw F a b c dd) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dimension identity `Σ_c N^c_{ab} d_c = d_a d_b` over the
row's support. -/
def dimLaw {L : Type} (F : Data L) (a b : L) : Prop :=
  ((F.row a b).foldl (fun acc c =>
      acc + F.count a b c * F.dim c) 0)
    = F.dim a * F.dim b

instance instFusion6 {L : Type} (F : Data L) (a b : L) :
    Decidable (dimLaw F a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The weight-free Casimir's positivity at a nonunit label. -/
def casPos {L : Type} (F : Data L) (l : L) : Prop :=
  (F.eqL l F.unit || decide (0 < F.c2N l)) = true

instance instFusion7 {L : Type} (F : Data L) (l : L) : Decidable (casPos F l) :=
  inferInstanceAs (Decidable (_ = _))

/-- The unit's one spelling over a stated list: each member off the
unit's class or the unit label itself — a label list reading
`def:carrier`'s data (the support's labels nonunit, the vacant key
the unit) at the one reduced spelling per label. -/
def oneUnit {L : Type} [DecidableEq L] (F : Data L)
    (l : List L) : Prop :=
  (l.all (fun m => (!(F.eqL m F.unit)) || (m == F.unit))) = true

instance instFusion8 {L : Type} [DecidableEq L] (F : Data L) (l : List L) :
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

instance instFusion9 {L : Type} (F : Data L) (r : L) :
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

instance instFusion10 {L : Type} (F : Data L) (a b : L) :
    Decidable (clsLaw F a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dual's class joins its label's to the unit class. -/
def clsDualLaw {L : Type} (F : Data L) (a : L) : Prop :=
  F.clsAdd (F.cls (F.dual a)) (F.cls a) = F.cls F.unit

instance instFusion11 {L : Type} (F : Data L) (a : L) :
    Decidable (clsDualLaw F a) :=
  inferInstanceAs (Decidable (_ = _))

/-- `θ`'s class the unit class, the magnetic member's own read. -/
def clsThetaLaw {L : Type} (F : Data L) : Prop :=
  F.cls F.theta = F.cls F.unit

instance instFusion12 {L : Type} (F : Data L) : Decidable (clsThetaLaw F) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dual label's Casimir is its label's own (`def:c2hat`'s
one-value read at the interface): the electric fold is blind to an
orientation reversal (`thm:restoration`). -/
def casDualLaw {L : Type} (F : Data L) (a : L) : Prop :=
  F.c2N (F.dual a) = F.c2N a

instance instFusion13 {L : Type} (F : Data L) (a : L) :
    Decidable (casDualLaw F a) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dual label's dimension is its label's own
(`lem:dualread`(ii): the dual block's count the block's, the
complement shape's block at the full-column line). -/
def dimDualLaw {L : Type} (F : Data L) (a : L) : Prop :=
  F.dim (F.dual a) = F.dim a

instance instFusion16 {L : Type} (F : Data L) (a : L) :
    Decidable (dimDualLaw F a) :=
  inferInstanceAs (Decidable (_ = _))

/-- The self-dual theta (`con:fusion`'s field), the magnetic fold's
own blindness at a reversed boundary word (`thm:restoration`). -/
def thetaSelfDual {L : Type} (F : Data L) : Prop :=
  F.eqL (F.dual F.theta) F.theta = true

instance instFusion14 {L : Type} (F : Data L) : Decidable (thetaSelfDual F) :=
  inferInstanceAs (Decidable (_ = _))

/-- The below-cutoff enumeration's soundness: every member reads
its cleared Casimir at or below the stated natural. -/
def belowSound {L : Type} (F : Data L) (k : Nat) : Prop :=
  ((F.below k).all (fun l => F.c2N l ≤ k)) = true

instance instFusion15 {L : Type} (F : Data L) (k : Nat) :
    Decidable (belowSound F k) :=
  inferInstanceAs (Decidable (_ = _))

/-- The below-cutoff enumeration nested (`prop:windowfinite`: the
enumeration reads two cutoffs as one list): the enumeration at a
cutoff is the enumeration at a larger cutoff filtered at the cleared
Casimir at or below the cutoff, one list in the larger enumeration's
order. -/
def belowNest {L : Type} [DecidableEq L] (F : Data L) (C C' : Nat) : Prop :=
  F.below C = (F.below C').filter (fun l => decide (F.c2N l ≤ C))

instance instFusion19 {L : Type} [DecidableEq L] (F : Data L) (C C' : Nat) :
    Decidable (belowNest F C C') :=
  inferInstanceAs (Decidable (_ = _))

/-- The below-cutoff enumeration lists nonunit labels alone
(`prop:windowfinite`'s enumeration, the nonunit labels at content
at or below a cutoff). -/
def belowNonunit {L : Type} (F : Data L) (C : Nat) : Prop :=
  ((F.below C).all (fun l => !(F.eqL l F.unit))) = true

instance instFusion20 {L : Type} (F : Data L) (C : Nat) :
    Decidable (belowNonunit F C) :=
  inferInstanceAs (Decidable (_ = _))

/-- The keyed lookup at a stated equality read, the stored lists'
one scan. -/
def lookupBy {L : Type} {α : Type} (eq : L → L → Bool)
    (k : L) : List (L × α) → Option α
  | [] => none
  | p :: t => if eq p.1 k then some p.2 else lookupBy eq k t

/-- A natural-valued table with distinct keys reads its lookup
as the guarded value fold. The equality read is the keys' own. -/
theorem lookupBy_sum {L : Type} [DecidableEq L] (eq : L → L → Bool)
    (hread : ∀ a b, eq a b = decide (a = b)) (k : L) : ∀ ps : List (L × Nat),
    ground.distinctList (ps.map Prod.fst) →
    (lookupBy eq k ps).getD 0
      = ground.famFold Nat.add 0 (fun p => if p.1 = k then p.2 else 0) ps
  | [], _ => rfl
  | (a, n) :: ps, hd => by
    have ht : ground.distinctList (ps.map Prod.fst) := ground.distinct_tail hd
    change (if eq a k then some n else lookupBy eq k ps).getD 0 =
      (if a = k then n else 0) + ground.famFold Nat.add 0 (fun p => if p.1 = k then p.2 else 0) ps
    rw [hread]
    by_cases he : a = k
    · rw [if_pos (decide_eq_true he), if_pos he]
      have hc : ground.countOf k (ps.map Prod.fst) = 0 := by
        have h := hd a (List.Mem.head _)
        change ground.countOf a (a :: ps.map Prod.fst) ≤ 1 at h
        rw [ground.countOf_head, he] at h
        exact Nat.le_antisymm (Nat.le_of_succ_le_succ h) (Nat.zero_le _)
      have hz : ground.famFold Nat.add 0 (fun p : L × Nat => if p.1 = k then p.2 else 0) ps = 0 := by
        apply ground.famFold_null_ov ground.natFoldLaws
        intro p hp
        apply if_neg
        intro hpk
        have h := ground.countOf_pos_of_mem
          (ground.mem_map_to Prod.fst (ground.mem_of_countOf_pos p ps hp))
        rw [hpk, hc] at h
        exact absurd h (Nat.lt_irrefl 0)
      rw [hz, Nat.add_zero]
      rfl
    · rw [if_neg (fun h => he (of_decide_eq_true h)), if_neg he, Nat.zero_add]
      exact lookupBy_sum eq hread k ps ht

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
pair, `con:xfusion`'s base, the enumeration over the degrees at
or below the cutoff's quotient at the count
(`prop:windowfinite`'s window, `c2hat.degree_le_dfQ`) at the
Casimir filter, and the class data at the box
count's remainder — the `d_f`-ality — with the endpoint floor's
numerator `j g_j (r+2)` at the complement gap. -/
def dataA (d : Nat) : Data Shape :=
  ⟨(fun a b => labels.reduce a == labels.reduce b),
   (fun l => ground.listEqBeq (labels.reduce l)),
   labels.unitL d, labels.dualL, places.addS,
   adjchar.theta d, labels.countL,
   labels.rowL d,
   weyldim.dimOf, c2hat.dfQ, 2 * d * d, xfusion.c1 d, d - 1,
   (fun k => (List.range (k / d + 1)).flatMap (fun j =>
     (allShapes (d - 1) j).filterMap (fun s =>
       if 0 < j && c2hat.dfQ (s ++ [0]) ≤ k then some (s ++ [0])
       else none))),
   (fun s => places.degree s % d), (fun x y => (x + y) % d),
   (fun j => j * (d - j) * (d + 1)),
   fiber.presA d⟩

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
  have hrowR := labels.rowFold b c (fun f => labels.countL a f dd) hWR
  rw [hba] at hrowR
  show (((allShapes d (degree a + degree b)).filterMap
      (labels.emit a b)).foldl
      (fun acc e => acc + labels.countL a b e * labels.countL e c dd) 0)
    = (((allShapes d (degree b + degree c)).filterMap
      (labels.emit b c)).foldl
      (fun acc f => acc + labels.countL b c f * labels.countL a f dd) 0)
  rw [← hd,
    ground.foldlSum
      (fun e => labels.countL a b e * labels.countL e c dd)
      ((allShapes a.length (degree a + degree b)).filterMap
        (labels.emit a b)) 0,
    ground.foldlSum
      (fun f => labels.countL b c f * labels.countL a f dd)
      ((allShapes a.length (degree b + degree c)).filterMap
        (labels.emit b c)) 0,
    ground.famFold_filterMap (labels.emit a b)
      (fun e => labels.countL a b e * labels.countL e c dd)
      (allShapes a.length (degree a + degree b)),
    ground.famFold_filterMap (labels.emit b c)
      (fun f => labels.countL b c f * labels.countL a f dd)
      (allShapes a.length (degree b + degree c)),
    labels.rowFold a b (fun e => labels.countL e c dd) hWL, hrowR,
    labels.countL_assoc a b c dd hba hca hdd]

/-- The dimension identity at the A-series interface for every
pair on its letter list (`con:fusion`; `lem:blockcount`(iii)).
The row's fold reads the matched-degree enumeration through
`labels.rowFold`, with the dimension fixed by label reduction
(`labels.dimOf_class`), and the enumeration's identity is
`repring.dimRead_all`. The width ties name the two factors' common
letter list and the row enumeration at that list. -/
theorem dimLaw_dataA (d : Nat) (a b : Shape)
    (hba : b.length = a.length) (hd : a.length = d) :
    dimLaw (dataA d) a b := by
  have hdim := repring.dimRead_all a b hba
  show (((allShapes d (degree a + degree b)).filterMap
      (labels.emit a b)).foldl
      (fun acc c => acc + labels.countL a b c * weyldim.dimOf c) 0)
    = weyldim.dimOf a * weyldim.dimOf b
  rw [← hd,
    ground.foldlSum (fun c => labels.countL a b c * weyldim.dimOf c) _ 0,
    ground.famFold_filterMap (labels.emit a b)
      (fun c => labels.countL a b c * weyldim.dimOf c),
    labels.rowFold a b weyldim.dimOf
      (fun c _ => (labels.dimOf_class c).symm)]
  exact (ground.foldlSum
    (fun c => steinberg.count a b c * weyldim.dimOf c) _ 0).symm.trans hdim

/-- The row-is-support law at the label instantiation, at a
reduced target of the stated width: an occupied count at or below
the pairing's degree puts the target's lift at the matched degree
on the enumeration, so its reduction sits on the row
(`labels.countL_geRead`, `places.mem_allShapes`), and a target
beyond the pairing's degree is vacant outright, the lifted first
shape's full columns refusing a reduced target
(`labels.countL_ltRead`, `labels.fusionCount_colOff`); a row member
reads its own positive count (`labels.countL_reduce`); and the row
lists the target at most once, the enumeration listing each shape
once and the reduction injective at one degree
(`places.countOf_allShapes_le`, `labels.reduce_inj`).  The width
ties are the frame; the reduced read is load-bearing with its
committed refusal. -/
theorem rowLaw_dataA (d : Nat) (a b c : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length)
    (hd : a.length = d) (hred : labels.reduce c = c) :
    rowLaw (dataA d) a b c := by
  match Nat.eq_zero_or_pos a.length with
  | Or.inl h0 =>
    have hd0 : d = 0 := hd.symm.trans h0
    rw [hd0, ground.nil_of_length_zero a h0,
      ground.nil_of_length_zero b (hba.trans h0),
      ground.nil_of_length_zero c (hca.trans h0)]
    decide +kernel
  | Or.inr hL =>
    rw [← hd]
    have hpred : a.length - 1 + 1 = a.length := ground.subAdd hL
    have hle : ground.countOf c
        ((allShapes a.length (degree a + degree b)).filterMap (labels.emit a b))
        ≤ 1 := labels.rowL_count_le a.length a b c
    have hback : 0 < ground.countOf c
        ((allShapes a.length (degree a + degree b)).filterMap (labels.emit a b))
        → 0 < labels.countL a b c :=
      fun hp => labels.rowL_count_pos a.length a b c rfl
        (ground.mem_of_countOf_pos c _ hp)
    have hfwd : 0 < labels.countL a b c → 0 < ground.countOf c
        ((allShapes a.length (degree a + degree b)).filterMap
          (labels.emit a b)) := by
      intro hpos
      cases Nat.lt_or_ge (degree a + degree b) (degree c) with
      | inl hlt =>
        have hmod : (degree c - (degree a + degree b)) % a.length = 0 := by
          by_cases hm : (degree c - (degree a + degree b)) % a.length = 0
          · exact hm
          · rw [labels.countL_ltVac a b c hlt hm] at hpos
            exact absurd hpos (Nat.lt_irrefl 0)
        rw [labels.countL_ltRead a b c hba hca hlt hmod] at hpos
        have hq : 0 < (degree c - (degree a + degree b)) / a.length := by
          have hn := (ground.natDivRead (degree c - (degree a + degree b))
            a.length hL).1
          rw [hmod, Nat.add_zero] at hn
          cases hz : (degree c - (degree a + degree b)) / a.length with
          | zero =>
            rw [hz, Nat.mul_zero] at hn
            have hk := ground.natAddSubCancel (Nat.le_of_lt hlt)
            rw [← hn, Nat.add_zero] at hk
            rw [hk] at hlt
            exact absurd hlt (Nat.lt_irrefl _)
          | succ m => exact Nat.succ_pos m
        have hlast : ground.getAt 0 (places.rowList c) (a.length - 1)
            = 0 := by
          rw [places.rowList_last c (a.length - 1) (hca.trans hpred.symm)]
          obtain ⟨s, x, hs, hsl⟩ :=
            ground.snoc_split (a.length - 1) c (hca.trans hpred.symm)
          have hx : x = 0 := by
            rw [hs, labels.reduce_snoc s x] at hred
            exact (List.cons.inj
              (ground.append_inj_len s s [0] [x] rfl hred).2).1.symm
          rw [hs, ← hsl]
          show ground.getAt 0 (s ++ [x]) (s.length + 0) = 0
          rw [ground.getAt_append_add 0 s [x] 0]
          exact hx
        rw [labels.fusionCount_colOff _ a b c hba hca
          (by rw [hlast]; exact hq) hL] at hpos
        exact absurd hpos (Nat.lt_irrefl 0)
      | inr hge =>
        have hnlt : ¬ degree a + degree b < degree c :=
          fun hlt => Nat.not_succ_le_self (degree a + degree b)
            (Nat.le_trans hlt hge)
        have hmod : (degree a + degree b - degree c) % a.length = 0 := by
          by_cases hm : (degree a + degree b - degree c) % a.length = 0
          · exact hm
          · rw [labels.countL_geVac a b c hnlt hm] at hpos
            exact absurd hpos (Nat.lt_irrefl 0)
        rw [labels.countL_geRead a b c hba hca hge hmod] at hpos
        have hcl : (labels.addFulls ((degree a + degree b - degree c)
            / a.length) c).length = a.length :=
          (labels.length_addFulls _ c).trans hca
        have hcd : degree (labels.addFulls ((degree a + degree b - degree c)
            / a.length) c) = degree a + degree b := by
          rw [labels.degree_addFulls _ c, hca]
          have hn := (ground.natDivRead (degree a + degree b - degree c)
            a.length hL).1
          rw [hmod, Nat.add_zero, Nat.mul_comm] at hn
          rw [hn]
          exact ground.natAddSubCancel hge
        have hmem : labels.addFulls ((degree a + degree b - degree c)
            / a.length) c ∈ allShapes a.length (degree a + degree b) := by
          have h := mem_allShapes a.length _ hcl
          rw [hcd] at h
          exact h
        have hemit : labels.emit a b (labels.addFulls
            ((degree a + degree b - degree c) / a.length) c) = some c := by
          show (if 0 < steinberg.count a b (labels.addFulls
              ((degree a + degree b - degree c) / a.length) c)
            then some (labels.reduce (labels.addFulls
              ((degree a + degree b - degree c) / a.length) c))
            else none) = some c
          rw [if_pos (by
              rw [steinberg.count_fusion a b _ hba hcl]
              exact hpos),
            labels.reduce_addFulls _ c, hred]
        exact ground.countOf_pos_of_mem
          (ground.mem_filterMap_to (labels.emit a b) hmem hemit)
    exact ⟨⟨hfwd, hback⟩, hle⟩

/-- The unit's row at the label calculus: the row of the unit label
at a reduced label of the stated width is that label alone, the row
listing the matched-degree enumeration's occupied members reduced
(`labels.rowL`), the count at the unit's first factor the Kronecker
delta at the label (`blockcount.fusionCount_unit` through the
factors' exchange and `steinberg.count_fusion`), and the enumeration
listing the label once (`places.mem_allShapes`,
`places.countOf_allShapes_le`). -/
theorem unitRowLaw_dataA (d : Nat) (b : Shape) (hbd : b.length = d)
    (hred : labels.reduce b = b) : unitRowLaw (dataA d) b := by
  show (allShapes d (degree (labels.unitL d) + degree b)).filterMap
    (labels.emit (labels.unitL d) b) = [b]
  have hdeg : degree (labels.unitL d) + degree b = degree b := by
    show degree (List.replicate d 0) + degree b = degree b
    rw [degree_replicate_zero d, Nat.zero_add]
  rw [hdeg]
  have hul : (labels.unitL d).length = d := ground.length_replicate 0 d
  have hu : labels.unitL d = List.replicate b.length 0 := by
    rw [hbd]
    rfl
  have hcongr : (allShapes d (degree b)).filterMap (labels.emit (labels.unitL d) b)
      = (allShapes d (degree b)).filterMap (fun c => if c = b then some b else none) := by
    refine filterMap_congr_members _ _ _ (fun c hc => ?_)
    obtain ⟨hcl, _⟩ := allShapes_sound d (degree b) c (mem_of_countOf_pos c _ hc)
    have hcount : steinberg.count (labels.unitL d) b c = if c = b then 1 else 0 := by
      rw [steinberg.count_fusion (labels.unitL d) b c (hbd.trans hul.symm) (hcl.trans hul.symm),
        blockcount.fusionCount_comm (labels.unitL d) b c (hbd.trans hul.symm), hu,
        blockcount.fusionCount_unit b c (hcl.trans hbd.symm)]
    show (if 0 < steinberg.count (labels.unitL d) b c then some (labels.reduce c) else none)
      = if c = b then some b else none
    rw [hcount]
    by_cases hcb : c = b
    · rw [if_pos hcb, if_pos hcb, if_pos (Nat.succ_pos 0), hcb, hred]
    · rw [if_neg hcb, if_neg hcb, if_neg (Nat.lt_irrefl 0)]
  rw [hcongr]
  refine filterMap_key_once b b _ (Nat.le_antisymm (countOf_allShapes_le d (degree b) b) ?_)
  exact countOf_pos_of_mem (mem_allShapes d b hbd)

/-- The label read at a fundamental count: a reduced shape of the
stated width, `con:labels`' one representative per label — the
domain the count laws hold over at the instantiation, the unit
label a member, the involution and the rows keeping it. -/
def labelA (d : Nat) (s : Shape) : Bool :=
  (s.length == d) && (labels.reduce s == s)

/-- A label's width. -/
theorem labelA_len (d : Nat) (s : Shape) (h : labelA d s = true) :
    s.length = d :=
  ground.beqEqOf (ground.andSplitB h).1

/-- A label is reduced. -/
theorem labelA_red (d : Nat) (s : Shape) (h : labelA d s = true) :
    labels.reduce s = s :=
  ground.listBeqEq (ground.andSplitB h).2

/-- At the label calculus the equality read is structural on the
width-`d` labels: two labels reading equal are one reduced spelling. -/
theorem eqL_labelA (d : Nat) (x y : places.Shape) (hx : labelA d x = true)
    (hy : labelA d y = true) (he : (dataA d).eqL x y = true) : x = y := by
  have h : labels.reduce x = labels.reduce y :=
    ground.listBeqEq (show (labels.reduce x == labels.reduce y) = true from he)
  rw [labelA_red d x hx, labelA_red d y hy] at h
  exact h

/-- A reduced shape of the stated width is a label. -/
theorem labelA_of (d : Nat) (s : Shape) (hl : s.length = d)
    (hr : labels.reduce s = s) : labelA d s = true := by
  show ((s.length == d) && (labels.reduce s == s)) = true
  rw [ground.eqBeqOf hl, hr, ground.listEqBeq s]
  rfl

/-- The unit label is a label: the unit shape's last key sits at the
unit occupancy. -/
theorem labelA_unit (d : Nat) : labelA d (dataA d).unit = true := by
  exact labelA_of d _ (ground.length_replicate 0 d) (labels.reduce_unit d)

/-- The involution keeps the labels: the dual is reduced at the
width (`labels.reduce_dualL`). -/
theorem labelA_dual (d : Nat) (s : Shape) (h : labelA d s = true) :
    labelA d ((dataA d).dual s) = true :=
  labelA_of d _ ((labels.length_dualL s).trans (labelA_len d s h))
    (labels.reduce_dualL s)

/-- The rows keep the labels: every row member is the enumeration's
shape reduced, at the stated width and reduced again to itself. -/
theorem labelA_row (d : Nat) (a b : Shape) :
    (((dataA d).row a b).all (labelA d)) = true := by
  refine ground.all_filterMap_mem _ _ _ (fun c hc y hy => ?_)
  have hcs := allShapes_sound d (degree a + degree b) c hc
  obtain ⟨_, hyv⟩ := labels.emit_reads hy
  rw [← hyv]
  exact labelA_of d _ ((labels.length_reduce c).trans hcs.1)
    (labels.reduce_reduce c)

/-- The window index's label carrier at the label calculus is inside
the labels: the unit label and every below-cutoff member, the
enumeration's shapes at the withdrawn last key. -/
theorem labelA_below (d C : Nat) :
    (((dataA d).unit :: (dataA d).below C).all (labelA d)) = true := by
  show (labelA d (dataA d).unit && ((dataA d).below C).all (labelA d)) = true
  rw [labelA_unit d]
  show ((dataA d).below C).all (labelA d) = true
  refine ground.all_of_mem_intro _ _ (fun x hx => ?_)
  obtain ⟨j, _, hxj⟩ := ground.mem_flatMap_of _ _ x hx
  obtain ⟨s, hs, hsx⟩ := ground.mem_filterMap_of _ _ x hxj
  have hsx' : (if 0 < j && c2hat.dfQ (s ++ [0]) ≤ C then some (s ++ [0])
      else none) = some x := hsx
  by_cases hc : (0 < j && c2hat.dfQ (s ++ [0]) ≤ C) = true
  · rw [if_pos hc] at hsx'
    obtain ⟨hsl, hsd⟩ := allShapes_sound (d - 1) j s hs
    rw [← Option.some.inj hsx']
    cases d with
    | zero =>
      have hj : 0 < j := of_decide_eq_true (ground.andSplitB hc).1
      rw [ground.nil_of_length_zero s hsl] at hsd
      rw [← hsd] at hj
      exact absurd hj (Nat.lt_irrefl 0)
    | succ n =>
      have hsl' : s.length = n := hsl
      refine labelA_of (n + 1) (s ++ [0]) ?_ (labels.reduce_snoc s 0)
      rw [ground.length_append s [0], hsl']
      rfl
  · rw [if_neg hc] at hsx'
    exact nomatch hsx'

/-- The window index's label carrier at the label calculus is
distinct: the unit label is off the below-cutoff list, whose members
are occupied, and the list itself lists each shape once, one block
per degree with the emission injective. -/
theorem below_distinct_dataA (d C : Nat) :
    ground.distinctList ((dataA d).unit :: (dataA d).below C) := by
  intro x _
  have hbel : ∀ y, y ∈ (dataA d).below C →
      ∃ s j, s ∈ allShapes (d - 1) j ∧ 0 < j ∧ y = s ++ [0] := by
    intro y hy
    obtain ⟨j, _, hyj⟩ := ground.mem_flatMap_of _ _ y hy
    obtain ⟨s, hs, hsy⟩ := ground.mem_filterMap_of _ _ y hyj
    have hsy' : (if 0 < j && c2hat.dfQ (s ++ [0]) ≤ C then some (s ++ [0])
        else none) = some y := hsy
    by_cases hc : (0 < j && c2hat.dfQ (s ++ [0]) ≤ C) = true
    · rw [if_pos hc] at hsy'
      exact ⟨s, j, hs, of_decide_eq_true (ground.andSplitB hc).1,
        (Option.some.inj hsy').symm⟩
    · rw [if_neg hc] at hsy'
      exact nomatch hsy'
  rw [ground.countOf_cons]
  by_cases hxu : x = (dataA d).unit
  · rw [if_pos hxu]
    have hz : ground.countOf x ((dataA d).below C) = 0 := by
      cases Nat.eq_zero_or_pos (ground.countOf x ((dataA d).below C)) with
      | inl h0 => exact h0
      | inr hp =>
        obtain ⟨s, j, hs, hj, hxs⟩ :=
          hbel x (ground.mem_of_countOf_pos x _ hp)
        obtain ⟨_, hsd⟩ := allShapes_sound (d - 1) j s hs
        have hdeg : degree x = j := by
          rw [hxs, degree_snoc s 0, Nat.zero_mul, Nat.add_zero, hsd]
        rw [hxu] at hdeg
        have h0 : degree (List.replicate d 0) = j := hdeg
        rw [degree_replicate_zero d] at h0
        rw [← h0] at hj
        exact absurd hj (Nat.lt_irrefl 0)
    rw [hz]
    exact Nat.le_refl 1
  · rw [if_neg hxu, Nat.zero_add]
    show ground.countOf x ((List.range (C / d + 1)).flatMap (fun j =>
      (allShapes (d - 1) j).filterMap (fun s =>
        if 0 < j && c2hat.dfQ (s ++ [0]) ≤ C then some (s ++ [0])
        else none))) ≤ 1
    rw [ground.countOf_flatMap]
    refine ground.famFold_le_one_at _ (degree x) (List.range (C / d + 1)) ?_ ?_ ?_
    · intro j _ hjx
      cases Nat.eq_zero_or_pos (ground.countOf x
          ((allShapes (d - 1) j).filterMap (fun s =>
            if 0 < j && c2hat.dfQ (s ++ [0]) ≤ C then some (s ++ [0])
            else none))) with
      | inl h0 => exact h0
      | inr hp =>
        obtain ⟨s, hs, hsx⟩ := ground.filterMap_pre _ _ x hp
        have hsx' : (if 0 < j && c2hat.dfQ (s ++ [0]) ≤ C then some (s ++ [0])
            else none) = some x := hsx
        by_cases hc : (0 < j && c2hat.dfQ (s ++ [0]) ≤ C) = true
        · rw [if_pos hc] at hsx'
          obtain ⟨_, hsd⟩ := allShapes_sound (d - 1) j s
            (ground.mem_of_countOf_pos s _ hs)
          have hdeg : degree x = j := by
            rw [← Option.some.inj hsx', degree_snoc s 0, Nat.zero_mul,
              Nat.add_zero, hsd]
          exact absurd hdeg.symm hjx
        · rw [if_neg hc] at hsx'
          exact nomatch hsx'
    · refine ground.countOf_filterMap_le_one _ x _
        (fun s => countOf_allShapes_le (d - 1) _ s) ?_
      intro s s' _ _ hfs hfs'
      have hfs2 : (if 0 < degree x && c2hat.dfQ (s ++ [0]) ≤ C
          then some (s ++ [0]) else none) = some x := hfs
      have hfs2' : (if 0 < degree x && c2hat.dfQ (s' ++ [0]) ≤ C
          then some (s' ++ [0]) else none) = some x := hfs'
      by_cases hc : (0 < degree x && c2hat.dfQ (s ++ [0]) ≤ C) = true
      · rw [if_pos hc] at hfs2
        by_cases hc' : (0 < degree x && c2hat.dfQ (s' ++ [0]) ≤ C) = true
        · rw [if_pos hc'] at hfs2'
          exact ground.snoc_inj s s' 0
            ((Option.some.inj hfs2).trans (Option.some.inj hfs2').symm)
        · rw [if_neg hc'] at hfs2'
          exact nomatch hfs2'
      · rw [if_neg hc] at hfs2
        exact nomatch hfs2
    · rw [ground.countOf_range]
      by_cases hlt : degree x < C / d + 1
      · rw [if_pos hlt]
        exact Nat.le_refl 1
      · rw [if_neg hlt]
        exact Nat.zero_le 1

/-- The enumeration's shape at the `A`-series: one block per degree
up to the cutoff's quotient at the count, the degree's shapes kept at
the cleared Casimir at or below the cutoff and the vacant degree
refused, each shape grown by its vacant last row. -/
private theorem below_dataA_eq (d C : Nat) :
    (dataA d).below C
      = (List.range (C / d + 1)).flatMap (fun j =>
          ((allShapes (d - 1) j).filter (fun s =>
            0 < j && c2hat.dfQ (s ++ [0]) ≤ C)).map (fun s => s ++ [0])) := by
  show (List.range (C / d + 1)).flatMap (fun j =>
      (allShapes (d - 1) j).filterMap (fun s =>
        if 0 < j && c2hat.dfQ (s ++ [0]) ≤ C then some (s ++ [0])
        else none)) = _
  exact ground.flatMap_congr_all _ _ (fun j => ground.filterMap_ite _ _ _) _

/-- A degree block beyond the cutoff's quotient is vacant: a shape
of degree `j` at `d j > C` reads its cleared Casimir beyond the
cutoff (`c2hat.degree_le_dfQ`), and at the vacant count the
positive degree holds no shape. -/
private theorem below_block_vacant (d C j : Nat) (hj : C / d + 1 ≤ j) :
    (allShapes (d - 1) j).filter (fun s =>
      0 < j && c2hat.dfQ (s ++ [0]) ≤ C) = [] := by
  refine ground.filter_false _ _ (fun s hs => ?_)
  obtain ⟨hsl, hsd⟩ := allShapes_sound (d - 1) j s hs
  have hj0 : 0 < j := Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) hj
  cases d with
  | zero =>
    have hsn : s = [] := by
      cases s with
      | nil => rfl
      | cons a t => exact Nat.noConfusion hsl
    rw [hsn] at hsd
    have h0 : (0 : Nat) = j := hsd
    rw [← h0] at hj0
    exact absurd hj0 (Nat.lt_irrefl 0)
  | succ e =>
    have hdeg : degree (s ++ [0]) = j := by
      rw [degree_snoc s 0, Nat.zero_mul, Nat.add_zero, hsd]
    have hsl' : s.length = e := by rw [hsl]; exact Nat.succ_sub_one e
    have hlen : (s ++ [0]).length = e + 1 := by
      rw [ground.length_append, hsl']
      rfl
    have hlast : ground.getAt 0 (s ++ [0]) e = 0 := by
      rw [ground.getAt_append, if_neg (by rw [hsl']; exact Nat.lt_irrefl e), hsl',
        Nat.sub_self]
      rfl
    have h1 : (e + 1) * j ≤ c2hat.dfQ (s ++ [0]) := by
      have h := c2hat.degree_le_dfQ (s ++ [0]) e hlen hlast
      rw [hlen, hdeg] at h
      exact h
    have h2 : C < (e + 1) * j := by
      obtain ⟨hdiv, hmod⟩ := ground.natDivRead C (e + 1) (Nat.zero_lt_succ e)
      have h3 : (e + 1) * (C / (e + 1) + 1) ≤ (e + 1) * j :=
        Nat.mul_le_mul_left (e + 1) hj
      rw [Nat.mul_succ] at h3
      have h4 : (e + 1) * (C / (e + 1)) + C % (e + 1)
          < (e + 1) * (C / (e + 1)) + (e + 1) :=
        Nat.add_lt_add_left hmod _
      rw [hdiv] at h4
      exact Nat.lt_of_lt_of_le h4 h3
    show (decide (0 < j) && decide (c2hat.dfQ (s ++ [0]) ≤ C)) = false
    rw [decide_eq_false (Nat.not_le.mpr (Nat.lt_of_lt_of_le h2 h1)), Bool.and_false]

/-- The `A`-series' enumeration is nested (`belowNest` at every
ordered cutoff pair): the larger cutoff's enumeration filtered at
the smaller cutoff keeps, block by block, exactly the smaller
cutoff's shapes, and the degree blocks beyond the smaller quotient
are vacant, so the two enumerations are one list in the blocks'
order. -/
theorem belowNest_dataA (d C C' : Nat) (h : C ≤ C') : belowNest (dataA d) C C' := by
  show (dataA d).below C
    = ((dataA d).below C').filter (fun l => decide (c2hat.dfQ l ≤ C))
  rw [below_dataA_eq d C, below_dataA_eq d C', ground.filter_flatMap]
  have hq : C / d ≤ C' / d := ground.divMono C C' d h
  obtain ⟨g, hg⟩ := Nat.le.dest hq
  rw [show C' / d + 1 = (C / d + 1) + g by rw [← hg, Nat.add_right_comm],
    ground.range_split (C / d + 1) g, ground.flatMap_append,
    ground.flatMap_nil _ ((List.range g).map (fun c => C / d + 1 + c)) (fun j hj => by
      obtain ⟨c, _, hcj⟩ := ground.mem_map_of _ _ j hj
      rw [← hcj, ground.filter_map, ground.filter_filter,
        ground.filter_congr (fun s => ((0 < C / d + 1 + c
              && c2hat.dfQ (s ++ [0]) ≤ C') && c2hat.dfQ (s ++ [0]) ≤ C))
          (fun s => (0 < C / d + 1 + c && c2hat.dfQ (s ++ [0]) ≤ C))
          (fun s => by
            cases hc : decide (c2hat.dfQ (s ++ [0]) ≤ C) with
            | false => rw [Bool.and_false, Bool.and_false]
            | true =>
              rw [Bool.and_true, Bool.and_true,
                decide_eq_true (Nat.le_trans (of_decide_eq_true hc) h), Bool.and_true]),
        below_block_vacant d C (C / d + 1 + c) (Nat.le_add_right _ _)]
      rfl),
    ground.append_nil]
  refine ground.flatMap_congr_all _ _ (fun j => ?_) _
  rw [ground.filter_map, ground.filter_filter]
  refine congrArg (List.map (fun s => s ++ [0])) (ground.filter_congr _ _ (fun s => ?_) _)
  cases hc : decide (c2hat.dfQ (s ++ [0]) ≤ C) with
  | false => rw [Bool.and_false, Bool.and_false]
  | true =>
    rw [Bool.and_true, Bool.and_true, decide_eq_true (Nat.le_trans (of_decide_eq_true hc) h),
      Bool.and_true]

/-- The `A`-series' enumeration lists nonunit labels alone: every
member is a shape of positive degree, off the unit shape at its
degree (`eqL_labelA`'s equality read at two labels). -/
theorem belowNonunit_dataA (d C : Nat) : belowNonunit (dataA d) C := by
  refine ground.all_of_mem_intro _ _ (fun x hx => ?_)
  have hlab : labelA d x = true :=
    ground.all_of_mem _ _ (labelA_below d C) x (List.Mem.tail _ hx)
  obtain ⟨j, _, hxj⟩ := ground.mem_flatMap_of _ _ x hx
  obtain ⟨s, hs, hsx⟩ := ground.mem_filterMap_of _ _ x hxj
  have hsx' : (if 0 < j && c2hat.dfQ (s ++ [0]) ≤ C then some (s ++ [0])
      else none) = some x := hsx
  by_cases hc : (0 < j && c2hat.dfQ (s ++ [0]) ≤ C) = true
  · rw [if_pos hc] at hsx'
    obtain ⟨_, hsd⟩ := allShapes_sound (d - 1) j s hs
    have hj : 0 < j := of_decide_eq_true (ground.andSplitB hc).1
    have hdeg : degree x = j := by
      rw [← Option.some.inj hsx', degree_snoc s 0, Nat.zero_mul, Nat.add_zero, hsd]
    show (!(dataA d).eqL x (dataA d).unit) = true
    cases he : (dataA d).eqL x (dataA d).unit with
    | false => rfl
    | true =>
      have hxu : x = (dataA d).unit := eqL_labelA d x _ hlab (labelA_unit d) he
      rw [hxu] at hdeg
      have h0 : degree (List.replicate d 0) = j := hdeg
      rw [degree_replicate_zero d] at h0
      rw [← h0] at hj
      exact absurd hj (Nat.lt_irrefl 0)
  · rw [if_neg hc] at hsx'
    exact nomatch hsx'

/-- Every label on the stated letter list is the unit label or
has positive cleared Casimir (`con:fusion`; `def:c2hat`). At the
reduced shape the degree floor bounds the box count, and a vacant
box count reads the unit shape. -/
theorem casPos_dataA (d : Nat) (s : Shape) (hlen : s.length = d) :
    casPos (dataA d) s := by
  cases d with
  | zero =>
    rw [ground.nil_of_length_zero s hlen]
    rfl
  | succ r =>
    have hrl : (labels.reduce s).length = r + 1 :=
      (labels.length_reduce s).trans hlen
    have hred : getAt 0 (labels.reduce s) r = 0 := by
      obtain ⟨t, a, hs, ht⟩ := ground.snoc_split r s hlen
      rw [hs, labels.reduce_snoc t a, ← ht]
      exact ground.getAt_append_add 0 t [0] 0
    cases Nat.eq_zero_or_pos (degree (labels.reduce s)) with
    | inl h0 =>
      have hunit : labels.reduce s = labels.unitL (r + 1) := by
        have he := places.eq_unit_of_degree_zero (labels.reduce s) h0
        rw [hrl] at he
        exact he
      show ((labels.reduce s == labels.reduce (labels.unitL (r + 1)))
        || decide (0 < c2hat.dfQ s)) = true
      rw [hunit, labels.reduce_unit, ground.listEqBeq]
      rfl
    | inr hp =>
      have hf := c2hat.degree_le_dfQ (labels.reduce s) r hrl hred
      rw [hrl, ← labels.c2Class_all s] at hf
      have hpos := Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.succ_pos r) hp) hf
      show ((dataA (r + 1)).eqL s (dataA (r + 1)).unit
        || decide (0 < c2hat.dfQ s)) = true
      rw [decide_eq_true hpos]
      exact Bool.or_true _

/-- The A-series cutoff list satisfies its bound at every cutoff
(`prop:windowfinite`; `con:fusion`), the Casimir comparison in the
list's defining filter. -/
theorem belowSound_dataA (d k : Nat) : belowSound (dataA d) k := by
  refine ground.all_of_mem_intro _ _ (fun x hx => ?_)
  obtain ⟨j, _, hxj⟩ := ground.mem_flatMap_of _ _ x hx
  obtain ⟨s, _, hsx⟩ := ground.mem_filterMap_of _ _ x hxj
  have hsx' : (if 0 < j && c2hat.dfQ (s ++ [0]) ≤ k then some (s ++ [0])
      else none) = some x := hsx
  by_cases hc : (0 < j && c2hat.dfQ (s ++ [0]) ≤ k) = true
  · rw [if_pos hc] at hsx'
    rw [← Option.some.inj hsx']
    exact (ground.andSplitB hc).2
  · rw [if_neg hc] at hsx'
    exact nomatch hsx'

/-- The self-dual theta at the label calculus: the complement
arithmetic reads the adjoint back (`prop:form`'s `dualL_theta`),
the interface law at every fundamental count from two. -/
theorem thetaSelfDual_dataA (d : Nat) (hd : 2 ≤ d) :
    fusion.thetaSelfDual (fusion.dataA d) := by
  show (fusion.dataA d).eqL
    ((fusion.dataA d).dual (fusion.dataA d).theta)
    (fusion.dataA d).theta = true
  rw [show (fusion.dataA d).dual (fusion.dataA d).theta
      = (fusion.dataA d).theta from form.dualL_theta d hd]
  exact (fusion.dataA d).eqLRefl _

end fusion
