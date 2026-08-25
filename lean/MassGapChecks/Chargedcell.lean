import MassGap.Chargedcell
/-!
The check module for `lem:chargedcell`'s class tier: the ality
reads at the label calculus — `θ` at the unit class, the
fundamentals at their indices, the dual at the complement, the
reduction's one value through the theorem route — the class laws
at stated factor pairs with the general theorems' own instances,
the winding floor per class against `lem:casfloor`'s endpoint
display, and the refusals at forged class data: the unit's code
moved, the sum without its remainder, the code at the raw
degree.  Clause (i)'s vertex law rides beside them: the class
fold's unit read at a positive invariant count over the label
calculus, at the dual pair and at the pair with the unit adjoined,
the theorem route beside the kernel's own, with the refusals
isolating each hypothesis binder — the positivity and the width at
the label calculus, and the interface binders at forged fusion data
over the naturals, one refusal per binder.  The flux tier closes
the module at the torus instance: the transverse-cut reads per
direction, the winding configuration's flux at every cut with the
charge family, the conservation through its own theorem route, and
one isolating refusal per binder of that theorem — and above it the
translation clause, the two directions' translations carrying the
winding string to the next row and onto itself with the charge
family standing at both, the permutation binder refused at a
collapsed witness that moves both components, and the two grade
transports refused at their swapped maps.  The class
tier's own reads close the module above it: `θ`'s row at the
source's class with the fused configuration's charge fixed against
the unit fusion's refusal, the per-class floor at a nonfundamental
class-one shape read strictly above the endpoint display, and the
winding floor at the torus attained at the winding strings — the
region binders at their own pins, the configuration binders
refusing in place — with the two-string union sharing one vertex
at the summed floor, the side-five string at the family's own
side, and the self-loop's two-ended incidence read at the one-loop
region.  The tie and merge tier rides beside the per-class floor:
the two endpoints' floors tied at the dual pair and parted by the
crossed gaps on the two strict sides of the sum's trichotomy, the
join binder refused off the pair, the merge's strict gap at all
three branches with the beyond branch attaining it, and the
merge's four class binders forged one at a time.  The price tier
closes the module: the unit class's least nonunit read attained at
`θ`'s own shape with the class, unit and width binders forged in
turn; the merge's strict gap at a two-member crossing family,
attained at the fundamental pair and read below its content on the
side-five family, with the count and width binders refused; the
netted family's two members at their classes' floors, attained at
the same pair, with the net and count binders refused; the crossing
counts at the landed winding configurations where the price rides
at the count's unit; and the two-string configuration at `d_f = 2`
attaining the priced floor exactly — three extra-crossed cuts at
two nonunit crossings each, the floor at the count's unit, the
price refused one cut higher, and the occupancy and width binders
undercutting the priced display in place.  The exactness, identity
and warrant tier closes the module: the tie's exactness at the dual
pair with the tie identities' join binders refused one at a time,
the merge's three cost identities at their theorem routes, the two
clearing comparisons with the residue binder refused at one, the
netted family's width binder refused at two short labels, and the
joint attainment — two direction-0 strings beside a direction-1
string at `d_f = 3` — reading the priced display at the content
exactly with both summands occupied.  The dressing fold and the
tension close the module at the composite pair: the interface reads
the fold consumes at both widths — a fundamental's row against `θ`,
its members' content gaps over the source at the cleared Casimir
units, the vertex gap at the vacuum and the class's endpoint floor,
at `d_f = 2` and at `d_f = 3` — then the charge-one stencil's own
tension, the free end reading the winding-floor pair alone, the far
plaquette joined to both members leaving the value standing and
joined to one member alone moving it, the committed stencil reading
its upper side with an inflated string entry carrying it to the
lower, the head atom splitting off the fold at one committed atom,
and the side at the seam's tie — one ray's two representatives
reading one side, with the tie binder isolated at two pairs off the
tie whose sides part.  Clause (iv)'s charged decimation closes the
module: the charge grouping at the one-dimensional torus with the
vacuum and the fundamental winding string at their own keys and the
swapped keys refusing; the plaquette row's charge preservation at
the two-dimensional torus's first plaquette, the theorem's route
beside the kernel's own read over the row's sixteen targets; the
charge blocking at a two-sector instance with the swapped keys and
a forged pencil refusing at their own conjuncts; the count split at
the assembled block diagonal, the head sector's certificate against
the joined rest with the reversal counts' sum; the charged head's
shift transport at the side length times the class's endpoint
floor, both directions with the unshifted level refusing; the
tension's located root bracketed at two term counts, the members
equal at nine string atoms and the lower side read at ten; and the
charged record at the one head pencil — the two sectors'
site-datum family with the charged diagonal the vacuum's shifted
by the side length's multiple of the floor, the divisor's witness,
and the level list, the multiplicities and the block structure the
reads of that head pencil, pinned per cell at one committed
instance. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground places chargedcell

/-! The ality reads at `d = 3`. -/

example : (fusion.dataA 3).cls (adjchar.theta 3) = 0 := by decide +kernel
example : (fusion.dataA 3).cls (casfloor.fundShape 1 2) = 1 := by
  decide +kernel
example : (fusion.dataA 3).cls (casfloor.fundShape 2 1) = 2 := by
  decide +kernel
example : (fusion.dataA 3).cls
    (labels.dualL (casfloor.fundShape 1 2)) = 2 := by decide +kernel
example : (fusion.dataA 3).cls (labels.reduce [2, 1, 4])
    = (fusion.dataA 3).cls [2, 1, 4] :=
  ality_reduce 3 [2, 1, 4] rfl
example : (fusion.dataA 3).cls [2, 1, 4] = 1 := by decide +kernel

/-! The class laws at stated pairs, the general theorems' own
instances beside the kernel reads. -/

example : fusion.clsLaw (fusion.dataA 3) (casfloor.fundShape 1 2)
    (casfloor.fundShape 2 1) := clsLaw_all 3 _ _
example : fusion.clsLaw (fusion.dataA 3) (adjchar.theta 3)
    (adjchar.theta 3) := by decide +kernel
example : fusion.clsDualLaw (fusion.dataA 3)
    (casfloor.fundShape 1 2) := clsDualLaw_all 3 _ rfl
example : fusion.clsDualLaw (fusion.dataA 2) (adjchar.theta 2) := by
  decide +kernel
example : (fusion.dataA 3).cls (fusion.dataA 3).unit = 0 :=
  ality_unit 3
example : fusion.clsThetaLaw (fusion.dataA 3) := clsThetaLaw_all 3
example : fusion.clsThetaLaw (fusion.dataA 2) := by decide +kernel

/-! The winding floor per class against the endpoint display,
`clsFloorN j = d_f Q(ω_j)` at the complement gap. -/

example : (fusion.dataA 3).clsFloorN 1
    = c2hat.dfQ (casfloor.fundShape 1 2) := by decide +kernel
example : (fusion.dataA 3).clsFloorN 2
    = c2hat.dfQ (casfloor.fundShape 2 1) := by decide +kernel
example : (fusion.dataA 4).clsFloorN 1
    = c2hat.dfQ (casfloor.fundShape 1 3) := by decide +kernel
example : (fusion.dataA 3).clsFloorN 0 = 0 := by decide +kernel

/-! The forged class data refuse, one conjunct each. -/

example : ¬ (({ fusion.dataA 3 with cls := fun _ => 1 }
    : fusion.Data places.Shape).cls (fusion.dataA 3).unit = 0) := by
  decide +kernel
example : ¬ fusion.clsLaw
    { fusion.dataA 3 with clsAdd := fun x y => x + y }
    (casfloor.fundShape 1 2) (casfloor.fundShape 2 1) := by decide +kernel
example : ¬ fusion.clsDualLaw
    { fusion.dataA 3 with clsAdd := fun x y => x + y }
    (casfloor.fundShape 1 2) := by decide +kernel
example : ¬ fusion.clsThetaLaw
    { fusion.dataA 3 with cls := fun s => places.degree s } := by
  decide +kernel

/-! The vertex law at the fusion interface: the class fold's unit
read at a positive invariant count, the kernel's own reads beside
the theorem route at the label calculus. -/

example : 0 < carrier.invCount (fusion.dataA 3)
    [casfloor.fundShape 1 2, labels.dualL (casfloor.fundShape 1 2)] := by
  decide +kernel
example : clsFold (fusion.dataA 3)
    [casfloor.fundShape 1 2, labels.dualL (casfloor.fundShape 1 2)]
    = (fusion.dataA 3).cls (labels.unitL 3) := by decide +kernel
example : clsFold (fusion.dataA 3)
    [casfloor.fundShape 1 2, labels.dualL (casfloor.fundShape 1 2)]
    = (fusion.dataA 3).cls (fusion.dataA 3).unit :=
  vertexLaw_all 3 _ (by decide +kernel) (by decide +kernel)

example : 0 < carrier.invCount (fusion.dataA 3)
    [casfloor.fundShape 1 2, labels.dualL (casfloor.fundShape 1 2),
      labels.unitL 3] := by decide +kernel
example : clsFold (fusion.dataA 3)
    [casfloor.fundShape 1 2, labels.dualL (casfloor.fundShape 1 2),
      labels.unitL 3] = (fusion.dataA 3).cls (labels.unitL 3) := by
  decide +kernel
example : clsFold (fusion.dataA 3)
    [casfloor.fundShape 1 2, labels.dualL (casfloor.fundShape 1 2),
      labels.unitL 3]
    = (fusion.dataA 3).cls (fusion.dataA 3).unit :=
  vertexLaw_all 3 _ (by decide +kernel) (by decide +kernel)

/-! The positivity binder and the width binder, each refused at a
label list moving that binder alone. -/

example : carrier.invCount (fusion.dataA 3)
    [casfloor.fundShape 1 2] = 0 := by decide +kernel
example : ([casfloor.fundShape 1 2].all (fun s => s.length == 3))
    = true := by decide +kernel
example : ¬ (clsFold (fusion.dataA 3) [casfloor.fundShape 1 2]
    = (fusion.dataA 3).cls (fusion.dataA 3).unit) := by decide +kernel

example : 0 < carrier.invCount (fusion.dataA 3) [[1], [0]] := by decide +kernel
example : ([[1], [0]].all (fun s => s.length == 3)) = false := by decide +kernel
example : ¬ (clsFold (fusion.dataA 3) [[1], [0]]
    = (fusion.dataA 3).cls (fusion.dataA 3).unit) := by decide +kernel

/-! The interface binders at forged fusion data over the naturals,
one refusal per binder: the label domain is the whole carrier where
the forgery needs no scope (`pAll`), and a stated finite domain
where it does. -/

private def pAll : Nat → Bool := fun _ => true

private def fHinv : fusion.Data Nat :=
  ⟨(fun a b => a % 2 == b % 2), (fun _ => ground.eqBeqOf rfl),
   0, id, (fun a b => a + b), 0, (fun _ _ _ => 0), (fun _ _ => []),
   (fun _ => 1), (fun _ => 0), 1, 1, (fun _ => []),
   id, (fun _ _ => 0), id⟩

example : ∀ a b : Nat, pAll a = true → pAll b = true →
    ((fHinv.row a b).all pAll) = true := fun _ _ _ _ => rfl
example : ∀ a b : Nat, pAll a = true → pAll b = true →
    fusion.clsLaw fHinv a b := fun _ _ _ _ => rfl
example : ∀ a : Nat, pAll a = true → fusion.clsDualLaw fHinv a :=
  fun _ _ => rfl
example : pAll fHinv.unit = true := rfl
example : ∀ a : Nat, pAll a = true → pAll (fHinv.dual a) = true :=
  fun _ _ => rfl
example : ([2].all pAll) = true := rfl
example : 0 < carrier.invCount fHinv [2] := by decide +kernel
example : fHinv.eqL 2 0 = true := by decide +kernel
example : ¬ (fHinv.cls 2 = fHinv.cls 0) := by decide +kernel
example : ¬ (clsFold fHinv [2] = fHinv.cls fHinv.unit) := by decide +kernel

private def fHdual : fusion.Data Nat :=
  ⟨(fun a b => a == b), (fun _ => ground.eqBeqOf rfl),
   0, id, (fun a b => a + b), 0, (fun _ _ _ => 0), (fun _ _ => []),
   (fun _ => 1), (fun _ => 0), 1, 1, (fun _ => []),
   id, (fun x _ => x), id⟩

example : ∀ a b : Nat, pAll a = true → pAll b = true →
    ((fHdual.row a b).all pAll) = true := fun _ _ _ _ => rfl
example : ∀ a b : Nat, pAll a = true → pAll b = true →
    fusion.clsLaw fHdual a b := fun _ _ _ _ => rfl
example : ∀ a b : Nat, pAll a = true → pAll b = true →
    fHdual.eqL a b = true → fHdual.cls a = fHdual.cls b :=
  fun _ _ _ _ h => ground.beqEqOf h
example : pAll fHdual.unit = true := rfl
example : ∀ a : Nat, pAll a = true → pAll (fHdual.dual a) = true :=
  fun _ _ => rfl
example : ([1, 1].all pAll) = true := rfl
example : 0 < carrier.invCount fHdual [1, 1] := by decide +kernel
example : ¬ fusion.clsDualLaw fHdual 1 := by decide +kernel
example : ¬ (clsFold fHdual [1, 1] = fHdual.cls fHdual.unit) := by decide +kernel

private def fHlaw : fusion.Data Nat :=
  ⟨(fun a b => a == b), (fun _ => ground.eqBeqOf rfl),
   0, id, (fun a b => a + b), 0, (fun _ _ _ => 1), (fun _ _ => [5]),
   (fun _ => 1), (fun _ => 0), 1, 1, (fun _ => []),
   (fun a => if a == 0 then 0 else 1), (fun x y => (x + y) % 2), id⟩

example : ∀ a b : Nat, pAll a = true → pAll b = true →
    ((fHlaw.row a b).all pAll) = true := fun _ _ _ _ => rfl
example : ∀ a b : Nat, pAll a = true → pAll b = true →
    fHlaw.eqL a b = true → fHlaw.cls a = fHlaw.cls b :=
  fun _ _ _ _ h => congrArg fHlaw.cls (ground.beqEqOf h)
example : ∀ a : Nat, pAll a = true → fusion.clsDualLaw fHlaw a := by
  intro a _
  show ((if a == 0 then 0 else 1) + (if a == 0 then 0 else 1)) % 2
    = (if (0 : Nat) == 0 then 0 else 1)
  cases h : (a == 0) with
  | true => exact rfl
  | false => exact rfl
example : pAll fHlaw.unit = true := rfl
example : ∀ a : Nat, pAll a = true → pAll (fHlaw.dual a) = true :=
  fun _ _ => rfl
example : ([1, 1, 5].all pAll) = true := rfl
example : 0 < carrier.invCount fHlaw [1, 1, 5] := by decide +kernel
example : ¬ fusion.clsLaw fHlaw 1 1 := by decide +kernel
example : ¬ (clsFold fHlaw [1, 1, 5] = fHlaw.cls fHlaw.unit) := by
  decide +kernel

private def pHunit : Nat → Bool := fun a => a == 2

private def fHunit : fusion.Data Nat :=
  ⟨(fun a b => a % 2 == b % 2), (fun _ => ground.eqBeqOf rfl),
   0, id, (fun a b => a + b), 0, (fun _ _ _ => 0), (fun _ _ => []),
   (fun _ => 1), (fun _ => 0), 1, 1, (fun _ => []),
   id, (fun _ _ => 0), id⟩

example : ∀ a b : Nat, pHunit a = true → pHunit b = true →
    ((fHunit.row a b).all pHunit) = true := fun _ _ _ _ => rfl
example : ∀ a b : Nat, pHunit a = true → pHunit b = true →
    fusion.clsLaw fHunit a b := fun _ _ _ _ => rfl
example : ∀ a : Nat, pHunit a = true → fusion.clsDualLaw fHunit a :=
  fun _ _ => rfl
example : ∀ a b : Nat, pHunit a = true → pHunit b = true →
    fHunit.eqL a b = true → fHunit.cls a = fHunit.cls b := by
  intro a b ha hb _
  rw [ground.beqEqOf (show (a == 2) = true from ha),
    ground.beqEqOf (show (b == 2) = true from hb)]
example : ∀ a : Nat, pHunit a = true → pHunit (fHunit.dual a) = true :=
  fun _ ha => ha
example : ([2].all pHunit) = true := rfl
example : 0 < carrier.invCount fHunit [2] := by decide +kernel
example : pHunit fHunit.unit = false := by decide +kernel
example : ¬ (clsFold fHunit [2] = fHunit.cls fHunit.unit) := by decide +kernel

private def pHdualP : Nat → Bool := fun a => a == 1 || a == 0

private theorem p2_cases (a : Nat) (h : pHdualP a = true) :
    a = 1 ∨ a = 0 := by
  cases ground.orSplitB (show ((a == 1) || (a == 0)) = true from h) with
  | inl h1 => exact Or.inl (ground.beqEqOf h1)
  | inr h0 => exact Or.inr (ground.beqEqOf h0)

private def fHdualP : fusion.Data Nat :=
  ⟨(fun a b => a % 2 == b % 2), (fun _ => ground.eqBeqOf rfl),
   0, (fun a => 2 * a), (fun a b => a + b), 0, (fun _ _ _ => 0),
   (fun _ _ => []), (fun _ => 1), (fun _ => 0), 1, 1, (fun _ => []),
   (fun a => a % 3), (fun x y => (x + y) % 3), id⟩

example : ∀ a b : Nat, pHdualP a = true → pHdualP b = true →
    ((fHdualP.row a b).all pHdualP) = true := fun _ _ _ _ => rfl
example : ∀ a b : Nat, pHdualP a = true → pHdualP b = true →
    fusion.clsLaw fHdualP a b := fun _ _ _ _ => rfl
example : ∀ a : Nat, pHdualP a = true → fusion.clsDualLaw fHdualP a := by
  intro a ha
  cases p2_cases a ha with
  | inl h => subst h; decide +kernel
  | inr h => subst h; decide +kernel
example : ∀ a b : Nat, pHdualP a = true → pHdualP b = true →
    fHdualP.eqL a b = true → fHdualP.cls a = fHdualP.cls b := by
  intro a b ha hb he
  cases p2_cases a ha with
  | inl h =>
    subst h
    cases p2_cases b hb with
    | inl k => subst k; rfl
    | inr k => subst k; exact absurd he (by decide +kernel)
  | inr h =>
    subst h
    cases p2_cases b hb with
    | inl k => subst k; exact absurd he (by decide +kernel)
    | inr k => subst k; rfl
example : pHdualP fHdualP.unit = true := by decide +kernel
example : ([0, 1].all pHdualP) = true := by decide +kernel
example : 0 < carrier.invCount fHdualP [0, 1] := by decide +kernel
example : pHdualP 1 = true := by decide +kernel
example : pHdualP (fHdualP.dual 1) = false := by decide +kernel
example : ¬ (clsFold fHdualP [0, 1] = fHdualP.cls fHdualP.unit) := by
  decide +kernel

private def pHrow : Nat → Bool := fun a => a == 0 || a == 1 || a == 2

private theorem p3_cases (a : Nat) (h : pHrow a = true) :
    a = 0 ∨ a = 1 ∨ a = 2 := by
  cases ground.orSplitB
      (show (((a == 0) || (a == 1)) || (a == 2)) = true from h) with
  | inl hl =>
    cases ground.orSplitB hl with
    | inl h0 => exact Or.inl (ground.beqEqOf h0)
    | inr h1 => exact Or.inr (Or.inl (ground.beqEqOf h1))
  | inr h2 => exact Or.inr (Or.inr (ground.beqEqOf h2))

private def fHrow : fusion.Data Nat :=
  ⟨(fun a b => (a == b) || (a == 5 && b == 1) || (a == 1 && b == 5)),
   (fun _ => by rw [ground.eqBeqOf rfl]; exact rfl),
   0, (fun a => if a == 0 then 0 else 3 - a), (fun a b => a + b), 0,
   (fun _ _ _ => 1), (fun a b => if a == 1 && b == 1 then [5] else []),
   (fun _ => 1), (fun _ => 0), 1, 1, (fun _ => []),
   (fun a => a % 3), (fun x y => (x + y) % 3), id⟩

example : ∀ a b : Nat, pHrow a = true → pHrow b = true →
    fusion.clsLaw fHrow a b := by
  intro a b _ _
  show ((if a == 1 && b == 1 then [5] else []).all
      (fun c => Nat.beq (fHrow.cls c)
        (fHrow.clsAdd (fHrow.cls a) (fHrow.cls b)))) = true
  cases h : (a == 1 && b == 1) with
  | false => exact rfl
  | true =>
    rw [ground.beqEqOf (ground.andSplitB h).1,
      ground.beqEqOf (ground.andSplitB h).2]
    decide +kernel
example : ∀ a : Nat, pHrow a = true → fusion.clsDualLaw fHrow a := by
  intro a ha
  cases p3_cases a ha with
  | inl h => subst h; decide +kernel
  | inr hr =>
    cases hr with
    | inl h => subst h; decide +kernel
    | inr h => subst h; decide +kernel
example : ∀ a b : Nat, pHrow a = true → pHrow b = true →
    fHrow.eqL a b = true → fHrow.cls a = fHrow.cls b := by
  intro a b ha hb he
  cases ground.orSplitB
      (show (((a == b) || (a == 5 && b == 1)) || (a == 1 && b == 5))
        = true from he) with
  | inl hl =>
    cases ground.orSplitB hl with
    | inl h => exact congrArg fHrow.cls (ground.beqEqOf h)
    | inr h =>
      rw [ground.beqEqOf (ground.andSplitB h).1] at ha
      exact absurd ha (by decide +kernel)
  | inr h =>
    rw [ground.beqEqOf (ground.andSplitB h).2] at hb
    exact absurd hb (by decide +kernel)
example : pHrow fHrow.unit = true := by decide +kernel
example : ∀ a : Nat, pHrow a = true → pHrow (fHrow.dual a) = true := by
  intro a ha
  cases p3_cases a ha with
  | inl h => subst h; decide +kernel
  | inr hr =>
    cases hr with
    | inl h => subst h; decide +kernel
    | inr h => subst h; decide +kernel
example : ([1, 1, 2].all pHrow) = true := by decide +kernel
example : 0 < carrier.invCount fHrow [1, 1, 2] := by decide +kernel
example : pHrow 1 = true := by decide +kernel
example : ((fHrow.row 1 1).all pHrow) = false := by decide +kernel
example : ¬ (clsFold fHrow [1, 1, 2] = fHrow.cls fHrow.unit) := by
  decide +kernel

/-! The flux tier at the torus instance `d = 2`, `L = 3`, `n = 3`:
the transverse-cut family at each direction's positional digit, the
winding configuration's flux at every cut of both directions with
the charge family beside it, the theorem's own route against the
kernel's values, and one isolating refusal per binder — the cut
count moved, the winding opened at one link, the grading forged off
its cyclic successor, the labels' width moved at a region where
every other read holds, and an endpoint beyond the vertex
count. -/

private def fundA : Shape := casfloor.fundShape 1 2
private def dualA : Shape := labels.dualL fundA
private def unitA : Shape := labels.unitL 3
private def torus23 : lattice.Region := fiberdec.torusRegion 2 3
private def cut0 : Nat → Nat := fun s => fiberdec.digitAt 3 0 s
private def cut1 : Nat → Nat := fun s => fiberdec.digitAt 3 1 s

/-- The winding configuration: the straight fundamental cycle along
the first direction, every further key unoccupied. -/
private def wind : List Shape :=
  [fundA, fundA, fundA] ++ List.replicate 15 unitA

example : transCutRead torus23 cut0 3 := by decide +kernel
example : transCutRead torus23 cut1 3 := by decide +kernel
example : ¬ transCutRead torus23 cut0 2 := by decide +kernel

example : carrier.occupied (fusion.dataA 3) torus23 wind = true := by
  decide +kernel
example : (wind.all (fun s => s.length == 3)) = true := by decide +kernel

example : fluxAt 3 torus23 cut0 0 wind = 1 := by decide +kernel
example : fluxAt 3 torus23 cut0 1 wind = 1 := by decide +kernel
example : fluxAt 3 torus23 cut0 2 wind = 1 := by decide +kernel
example : fluxAt 3 torus23 cut1 0 wind = 0 := by decide +kernel
example : chargeT 3 2 3 wind = [1, 0] := by decide +kernel

example : fluxAt 3 torus23 cut0 2 wind % 3
    = fluxAt 3 torus23 cut0 0 wind % 3 :=
  fluxConserve 3 torus23 cut0 3 wind (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 2 (by decide +kernel)

/-! The grade binder: beyond the cut count the flux reads no
crossing at all and the conclusion refuses. -/

example : fluxAt 3 torus23 cut0 3 wind = 0 := by decide +kernel
example : ¬ (fluxAt 3 torus23 cut0 3 wind % 3
    = fluxAt 3 torus23 cut0 0 wind % 3) := by decide +kernel

/-! The occupancy binder: one open fundamental link, every other
read holding at the same region and grading. -/

private def open1 : List Shape := [fundA] ++ List.replicate 17 unitA

example : carrier.occupied (fusion.dataA 3) torus23 open1 = false := by
  decide +kernel
example : (open1.all (fun s => s.length == 3)) = true := by decide +kernel
example : 0 < fluxAt 3 torus23 cut0 0 open1 := by decide +kernel
example : fluxAt 3 torus23 cut0 1 open1 = 0 := by decide +kernel
example : ¬ (fluxAt 3 torus23 cut0 1 open1 % 3
    = fluxAt 3 torus23 cut0 0 open1 % 3) := by decide +kernel

/-! The cut binder: one site's grade moved off its link's cyclic
successor, at the winding configuration where every other read
holds. -/

private def cutBad : Nat → Nat :=
  fun s => if s == 1 then 2 else fiberdec.digitAt 3 0 s

example : ¬ transCutRead torus23 cutBad 3 := by decide +kernel
example : ¬ (fluxAt 3 torus23 cutBad 1 wind % 3
    = fluxAt 3 torus23 cutBad 0 wind % 3) := by decide +kernel

/-! The width binder at the three-site cycle: the labels read a
width off the residue, so the dual's join no longer clears the
class and the two cuts part, every further read holding. -/

private def tri : lattice.Region :=
  { links := 3, verts := 3, tail := [0, 1, 2], head := [1, 2, 0],
    plaqs := [], color := [false, true, false] , tailLen := rfl, headLen := rfl }
private def thin : List Shape := [[1], [2], [1]]

example : lattice.wellRead tri := by decide +kernel
example : transCutRead tri id 3 := by decide +kernel
example : carrier.occupied (fusion.dataA 3) tri thin = true := by decide +kernel
example : (thin.all (fun s => s.length == 3)) = false := by decide +kernel
example : ¬ (fluxAt 3 tri id 1 thin % 3
    = fluxAt 3 tri id 0 thin % 3) := by decide +kernel

/-! The self-loop's two-ended incidence: a link at both ends reads
its vertex once per end, the label beside its dual — the one-loop
configuration occupied at the dual's own join and the loop
crossing no cut, its class withdrawn from every flux. -/

private def loop1 : lattice.Region :=
  { links := 1, verts := 1, tail := [0], head := [0], plaqs := [],
    color := [false] , tailLen := rfl, headLen := rfl }

example : carrier.incidentLabels (fusion.dataA 3) loop1 [fundA] 0
    = [fundA, dualA] := by decide +kernel
example : carrier.occupied (fusion.dataA 3) loop1 [fundA] = true := by
  decide +kernel
example : 0 < carrier.vmult (fusion.dataA 3) loop1 [fundA] 0 := by
  decide +kernel
example : fluxAt 3 loop1 (fun _ => 0) 0 [fundA] = 0 := by decide +kernel

/-! The shape binder: two link ends beyond the vertex count, whose
vertex laws the occupancy read never reaches, so a class enters the
cut family off the accounting. -/

private def outside : lattice.Region :=
  { links := 4, verts := 2, tail := [0, 1, 2, 3], head := [1, 2, 3, 0],
    plaqs := [], color := [false, true] , tailLen := rfl, headLen := rfl }
private def outConf : List Shape :=
  [fundA, fundA, adjchar.theta 3, fundA]

example : ¬ lattice.wellRead outside := by decide +kernel
example : transCutRead outside id 4 := by decide +kernel
example : carrier.occupied (fusion.dataA 3) outside outConf = true := by
  decide +kernel
example : (outConf.all (fun s => s.length == 3)) = true := by decide +kernel
example : ¬ (fluxAt 3 outside id 2 outConf % 3
    = fluxAt 3 outside id 0 outConf % 3) := by decide +kernel


/-! The translation clause at the same torus instance: a
translation permutes the link index at one charge and the relabeled
configuration's charge family is the source's own.  The
direction-one translation carries the winding string from its row
to the next — the relabeled configuration off the source, both
charge families at the winding's own read — and the direction-zero
translation carries the string onto itself, the second direction's
coverage.  The theorem's reads stand at their own pins: the
permutation read at the translation and its witness, the cut family
per direction, and per direction the grade map's transport, its
injectivity below the side, and the base cut's located pre-image —
the moved direction at the cyclic successor with pre-image two, the
fixed direction at the identity with pre-image the base cut itself.
The refusals: the witness map collapsed to one key refuses the
permutation read alone — every cut read, every grade transport and
every frame read of the theorem names the translation only, so the
forged witness passes all of them — and the relabeled
configuration's charge family parts from the source's at both
components; the all-identity grade map refuses the transport at the
moved direction while its injectivity and pre-image reads hold; the
pre-image forged to one refuses its own read at the moved direction
while the transport and injectivity hold; and the constant grade
map refuses the injectivity with the transport refusing beside it,
the two reads' joint tie — at this window the transport pins the
grade map at every occurring grade, so a map refusing injectivity
below the side refuses the transport with it.  The frame binders:
the occupancy and width reads enter through `fluxConserve` alone,
their isolating refusals the conservation's own above (the opened
link, the labels off the residue width); the region's shape read
and the cut family feed `fluxAt_move`'s own grade bounds as well
(the endpoint-beyond-the-vertex-count refusal above the
conservation's), the shape read the endpoint bounds' source. -/

private def tr0 : Nat → Nat := fiberdec.torusTransl 2 3 0
private def trI0 : Nat → Nat := fiberdec.torusTranslInv 2 3 0
private def tr1 : Nat → Nat := fiberdec.torusTransl 2 3 1
private def trI1 : Nat → Nat := fiberdec.torusTranslInv 2 3 1

/-- The direction-one translation's grade maps: the moved direction
at the cyclic successor, the fixed at the identity. -/
private def mv1 : Nat → Nat → Nat :=
  fun e x => if e == 1 then (x + 1) % 3 else x
/-- The base cut's pre-images at the direction-one translation. -/
private def pre1 : Nat → Nat := fun e => if e == 1 then 2 else 0
/-- The direction-zero translation's grade maps. -/
private def mv0 : Nat → Nat → Nat :=
  fun e x => if e == 0 then (x + 1) % 3 else x
/-- The base cut's pre-images at the direction-zero translation. -/
private def pre0 : Nat → Nat := fun e => if e == 0 then 2 else 0

example : lattice.wellRead torus23 := by decide +kernel
example : fiberdec.permRead torus23 tr1 trI1 := by decide +kernel
example : ∀ e, e < 2 → transCutRead torus23
    (fun v => fiberdec.digitAt 3 e v) 3 := by decide +kernel
example : ∀ e, e < 2 → cutMoveRead torus23 tr1
    (fun v => fiberdec.digitAt 3 e v) (mv1 e) := by decide +kernel
example : ∀ e, e < 2 → ∀ u, u < 3 → ∀ v, v < 3 →
    mv1 e u = mv1 e v → u = v := by decide +kernel
example : ∀ e, e < 2 → pre1 e < 3 ∧ mv1 e (pre1 e) = 0 := by decide +kernel

example : ¬ (fiberdec.permConf (fusion.dataA 3) trI1
    (fiberdec.torusRegion 2 3).links wind = wind) := by decide +kernel
example : chargeT 3 2 3 (fiberdec.permConf (fusion.dataA 3) trI1
    (fiberdec.torusRegion 2 3).links wind) = [1, 0] := by decide +kernel

example : chargeT 3 2 3 (fiberdec.permConf (fusion.dataA 3) trI1
      (fiberdec.torusRegion 2 3).links wind)
    = chargeT 3 2 3 wind :=
  chargeT_perm 3 2 3 wind tr1 trI1 mv1 pre1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The winding direction's own translation: the string is carried
onto itself and the charge family stands. -/

example : fiberdec.permConf (fusion.dataA 3) trI0
    (fiberdec.torusRegion 2 3).links wind = wind := by decide +kernel

example : chargeT 3 2 3 (fiberdec.permConf (fusion.dataA 3) trI0
      (fiberdec.torusRegion 2 3).links wind)
    = chargeT 3 2 3 wind :=
  chargeT_perm 3 2 3 wind tr0 trI0 mv0 pre0 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The permutation binder: the witness map collapsed to one key,
the translation and every read stated at it kept — the relabeled
configuration reads that key's label at every link and both charge
components move. -/

example : ¬ fiberdec.permRead torus23 tr1 (fun _ => 0) := by decide +kernel
example : chargeT 3 2 3 (fiberdec.permConf (fusion.dataA 3)
    (fun _ => 0) (fiberdec.torusRegion 2 3).links wind) = [0, 0] := by
  decide +kernel
example : ¬ (chargeT 3 2 3 (fiberdec.permConf (fusion.dataA 3)
      (fun _ => 0) (fiberdec.torusRegion 2 3).links wind)
    = chargeT 3 2 3 wind) := by decide +kernel

/-! The grade-map binders at the direction-one translation.  The
transport: the all-identity map refuses at the moved direction
while its injectivity and pre-image reads hold.  The pre-image:
forged to one at the moved direction, its own read refuses while
the transport and injectivity hold.  The injectivity: the constant
map refuses it with the transport refusing beside it, the joint
tie's two reads. -/

example : ¬ (∀ e, e < 2 → cutMoveRead torus23 tr1
    (fun v => fiberdec.digitAt 3 e v) ((fun _ x => x) e)) := by decide +kernel
example : ∀ e, e < 2 → ∀ u, u < 3 → ∀ v, v < 3 →
    (fun (_ x : Nat) => x) e u = (fun (_ x : Nat) => x) e v → u = v := by
  decide +kernel
example : ∀ e, e < 2 → (fun _ => (0 : Nat)) e < 3
    ∧ (fun (_ x : Nat) => x) e ((fun _ => (0 : Nat)) e) = 0 := by decide +kernel

example : ¬ (∀ e, e < 2 → (fun _ => (1 : Nat)) e < 3
    ∧ mv1 e ((fun _ => (1 : Nat)) e) = 0) := by decide +kernel
example : ∀ e, e < 2 → cutMoveRead torus23 tr1
    (fun v => fiberdec.digitAt 3 e v) (mv1 e) := by decide +kernel

example : ¬ (∀ e, e < 2 → ∀ u, u < 3 → ∀ v, v < 3 →
    (fun (_ _ : Nat) => (0 : Nat)) e u = (fun (_ _ : Nat) => (0 : Nat)) e v
      → u = v) := by decide +kernel
example : ¬ (∀ e, e < 2 → cutMoveRead torus23 tr1
    (fun v => fiberdec.digitAt 3 e v)
    ((fun (_ _ : Nat) => (0 : Nat)) e)) := by decide +kernel

/-! The `θ`-row class read at `d = 3`: every member of `θ`'s row
over the first fundamental reads that fundamental's class, the
theorem route beside the kernel's own fold, with a named row
member off the source label and the winding configuration's charge
fixed by that fusion — against the refusal at a fusion to the unit,
which moves the charge. -/

/-- A member of `θ`'s row over the first fundamental, off the
fundamental itself. -/
private def rowMem : Shape := [0, 2, 0]

example : (((fusion.dataA 3).row (adjchar.theta 3) fundA).all (fun c =>
    Nat.beq ((fusion.dataA 3).cls c) ((fusion.dataA 3).cls fundA)))
    = true :=
  clsRow_theta 3 fundA
example : (((fusion.dataA 3).row (adjchar.theta 3) fundA).all (fun c =>
    Nat.beq ((fusion.dataA 3).cls c) ((fusion.dataA 3).cls fundA)))
    = true := by decide +kernel

example : 0 < ground.countOf rowMem
    ((fusion.dataA 3).row (adjchar.theta 3) fundA) := by decide +kernel
example : (fusion.dataA 3).cls rowMem = 1 := by decide +kernel
example : ¬ ((fusion.dataA 3).eqL rowMem fundA = true) := by decide +kernel

example : chargeT 3 2 3
    ([rowMem, fundA, fundA] ++ List.replicate 15 unitA) = [1, 0] := by
  decide +kernel
example : chargeT 3 2 3
    ([unitA, fundA, fundA] ++ List.replicate 15 unitA) = [0, 0] := by
  decide +kernel
example : ¬ (chargeT 3 2 3
    ([unitA, fundA, fundA] ++ List.replicate 15 unitA) = [1, 0]) := by
  decide +kernel

/-! The per-class floor at a nonfundamental class-one shape: the
theorem route reads the endpoint display `1 · 2 · 4` at or below
the shape's own cleared Casimir, strictly so — the floor's
attainment sits at the fundamentals alone. -/

example : (fusion.dataA 3).clsFloorN 1 = 8 := by decide +kernel
example : 1 * (2 + 1 - 1) * (2 + 2) ≤ c2hat.dfQ rowMem :=
  casfloor.classFloor 2 1 rowMem rfl rfl rfl
example : (fusion.dataA 3).clsFloorN 1 ≤ (fusion.dataA 3).clsFloorN 2 :=
  casfloor.classFloor_fund 2 2 (by decide +kernel) (by decide +kernel)
example : (2 : Nat) * (2 + 1 - 2) * (2 + 2) = 8 := by decide +kernel
example : (8 : Nat) ≤ c2hat.dfQ rowMem := by decide +kernel
example : ¬ (c2hat.dfQ rowMem = 8) := by decide +kernel

/-! The tie tier at `n = 4`: the two endpoints' floors tie exactly
at the dual pair, and part by the crossed gaps on the two strict
sides of the sum's trichotomy — the theorem routes beside the
kernel's own values, with the join binder refused off the pair. -/

example : (fusion.dataA 4).clsFloorN 1 = 15 := by decide +kernel
example : (fusion.dataA 4).clsFloorN 2 = 20 := by decide +kernel
example : (fusion.dataA 4).clsFloorN 3 = 15 := by decide +kernel

example : (fusion.dataA 4).clsFloorN 1
    = (fusion.dataA 4).clsFloorN 3 :=
  tieDual 4 1 3 rfl
example : (fusion.dataA 4).clsFloorN 1
    = (fusion.dataA 4).clsFloorN 3 := by decide +kernel

example : (fusion.dataA 4).clsFloorN 1 + 1 * 1 * (4 + 1)
    = (fusion.dataA 4).clsFloorN 2 :=
  tieBelow 4 2 1 1 1 rfl rfl
example : (fusion.dataA 4).clsFloorN 1 + 1 * 1 * (4 + 1)
    = (fusion.dataA 4).clsFloorN 2 := by decide +kernel

example : (fusion.dataA 4).clsFloorN 3 + 1 * 1 * (4 + 1)
    = (fusion.dataA 4).clsFloorN 2 :=
  tieBeyond 4 3 2 1 1 1 rfl rfl rfl
example : (fusion.dataA 4).clsFloorN 3 + 1 * 1 * (4 + 1)
    = (fusion.dataA 4).clsFloorN 2 := by decide +kernel

example : ¬ ((fusion.dataA 4).clsFloorN 1
    = (fusion.dataA 4).clsFloorN 2) := by decide +kernel

/-! The merge's strict gap at the three branches of the sum's
trichotomy — below the residue at `n = 5`, at it at `n = 4`, and
beyond it at `n = 3`, the last attaining the gap exactly. -/

example : (fusion.dataA 5).clsFloorN ((1 + 2) % 5) + 2 * (5 + 1)
    ≤ (fusion.dataA 5).clsFloorN 1 + (fusion.dataA 5).clsFloorN 2 :=
  mergeGap 5 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : (fusion.dataA 5).clsFloorN ((1 + 2) % 5) + 2 * (5 + 1)
    ≤ (fusion.dataA 5).clsFloorN 1
      + (fusion.dataA 5).clsFloorN 2 := by decide +kernel

example : (fusion.dataA 4).clsFloorN ((1 + 3) % 4) + 2 * (4 + 1)
    ≤ (fusion.dataA 4).clsFloorN 1 + (fusion.dataA 4).clsFloorN 3 :=
  mergeGap 4 1 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : (fusion.dataA 4).clsFloorN ((1 + 3) % 4) + 2 * (4 + 1)
    ≤ (fusion.dataA 4).clsFloorN 1
      + (fusion.dataA 4).clsFloorN 3 := by decide +kernel

example : (fusion.dataA 3).clsFloorN ((2 + 2) % 3) + 2 * (3 + 1)
    ≤ (fusion.dataA 3).clsFloorN 2 + (fusion.dataA 3).clsFloorN 2 :=
  mergeGap 3 2 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : (fusion.dataA 3).clsFloorN ((2 + 2) % 3) + 2 * (3 + 1)
    = (fusion.dataA 3).clsFloorN 2
      + (fusion.dataA 3).clsFloorN 2 := by decide +kernel

/-! The merge's four class binders at `n = 2`, each forged in turn
with the other three standing: the first class vacant, the first
class at the residue, the second class vacant, the second class at
the residue.  Each forgery moves the conclusion. -/

example : ¬ ((fusion.dataA 2).clsFloorN ((0 + 1) % 2) + 2 * (2 + 1)
    ≤ (fusion.dataA 2).clsFloorN 0
      + (fusion.dataA 2).clsFloorN 1) := by decide +kernel
example : ¬ ((fusion.dataA 2).clsFloorN ((2 + 1) % 2) + 2 * (2 + 1)
    ≤ (fusion.dataA 2).clsFloorN 2
      + (fusion.dataA 2).clsFloorN 1) := by decide +kernel
example : ¬ ((fusion.dataA 2).clsFloorN ((1 + 0) % 2) + 2 * (2 + 1)
    ≤ (fusion.dataA 2).clsFloorN 1
      + (fusion.dataA 2).clsFloorN 0) := by decide +kernel
example : ¬ ((fusion.dataA 2).clsFloorN ((1 + 2) % 2) + 2 * (2 + 1)
    ≤ (fusion.dataA 2).clsFloorN 1
      + (fusion.dataA 2).clsFloorN 2) := by decide +kernel

/-! The winding floor at the torus instance `d = 2`, `L = 3`,
`n = 3`: the per-link cut disjointness, then the theorem route at
the winding configuration against the kernel's two values — the
content and the side length times the per-direction floor sum both
`24`, the floor attained at the strings.  The region binders
(`hwell`, `hcuts`, `hdisj`) stand at their pins at the stated
instances, the statement pinned at `torusRegion`; the
configuration binders refuse in place — an open winding line,
occupied nowhere, undercuts the floor sum at its own content, and
a thin-label configuration, occupied at every site, reads content
nowhere while its cuts still carry the class. -/

example : cutDisjRead 2 3 := by decide +kernel

example : carrier.contentN (fusion.dataA 3) wind = 24 := by decide +kernel
example : 3 * famFold Nat.add 0 (fun e =>
    (fusion.dataA 3).clsFloorN
      (fluxAt 3 (fiberdec.torusRegion 2 3)
        (fun s => fiberdec.digitAt 3 e s) 0 wind % 3))
    (List.range 2) = 24 := by decide +kernel

example : 3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 3).clsFloorN
        (fluxAt 3 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 wind % 3))
      (List.range 2)
    ≤ carrier.contentN (fusion.dataA 3) wind :=
  windFloor 3 2 3 wind (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : carrier.contentN (fusion.dataA 3) open1 = 8 := by decide +kernel
example : 3 * famFold Nat.add 0 (fun e =>
    (fusion.dataA 3).clsFloorN
      (fluxAt 3 (fiberdec.torusRegion 2 3)
        (fun s => fiberdec.digitAt 3 e s) 0 open1 % 3))
    (List.range 2) = 24 := by decide +kernel
example : ¬ (3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 3).clsFloorN
        (fluxAt 3 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 open1 % 3))
      (List.range 2)
    ≤ carrier.contentN (fusion.dataA 3) open1) := by decide +kernel

/-- The thin winding line: the labels read a width off the
residue, every site still occupied. -/
private def thin3 : List Shape :=
  [[1], [1], [1]] ++ List.replicate 15 unitA

example : carrier.occupied (fusion.dataA 3) torus23 thin3 = true := by
  decide +kernel
example : (thin3.all (fun s => s.length == 3)) = false := by decide +kernel
example : carrier.contentN (fusion.dataA 3) thin3 = 0 := by decide +kernel
example : ¬ (3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 3).clsFloorN
        (fluxAt 3 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 thin3 % 3))
      (List.range 2)
    ≤ carrier.contentN (fusion.dataA 3) thin3) := by decide +kernel

/-! The two-string attainment: one straight fundamental cycle per
direction, the strings sharing one vertex at a positive invariant
count, the charge occupied at both directions and the content the
summed floor exactly. -/

private def wind2 : List Shape :=
  [fundA, fundA, fundA, unitA, unitA, unitA, unitA, unitA, unitA,
   fundA, unitA, unitA, fundA, unitA, unitA, fundA, unitA, unitA]

example : chargeT 3 2 3 wind2 = [1, 1] := by decide +kernel
example : carrier.occupied (fusion.dataA 3) torus23 wind2 = true := by
  decide +kernel
example : (carrier.incidentLabels (fusion.dataA 3) torus23
    wind2 0).length = 4 := by decide +kernel
example : 0 < carrier.vmult (fusion.dataA 3) torus23 wind2 0 := by
  decide +kernel
example : carrier.contentN (fusion.dataA 3) wind2 = 48 := by decide +kernel
example : 3 * famFold Nat.add 0 (fun e =>
    (fusion.dataA 3).clsFloorN
      (fluxAt 3 (fiberdec.torusRegion 2 3)
        (fun s => fiberdec.digitAt 3 e s) 0 wind2 % 3))
    (List.range 2) = 48 := by decide +kernel
example : 3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 3).clsFloorN
        (fluxAt 3 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 wind2 % 3))
      (List.range 2)
    ≤ carrier.contentN (fusion.dataA 3) wind2 :=
  windFloor 3 2 3 wind2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The attainment at the family's own side: the straight winding
string on the side-five torus, the content the summed floor
exactly. -/

private def wind5 : List Shape :=
  [fundA, fundA, fundA, fundA, fundA] ++ List.replicate 45 unitA

example : chargeT 3 2 5 wind5 = [1, 0] := by decide +kernel
example : carrier.occupied (fusion.dataA 3)
    (fiberdec.torusRegion 2 5) wind5 = true := by decide +kernel
example : carrier.contentN (fusion.dataA 3) wind5 = 40 := by decide +kernel
example : 5 * famFold Nat.add 0 (fun e =>
    (fusion.dataA 3).clsFloorN
      (fluxAt 3 (fiberdec.torusRegion 2 5)
        (fun s => fiberdec.digitAt 5 e s) 0 wind5 % 3))
    (List.range 2) = 40 := by decide +kernel
example : 5 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 3).clsFloorN
        (fluxAt 3 (fiberdec.torusRegion 2 5)
          (fun s => fiberdec.digitAt 5 e s) 0 wind5 % 3))
      (List.range 2)
    ≤ carrier.contentN (fusion.dataA 3) wind5 :=
  windFloor 3 2 5 wind5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The unit class's least nonunit read at `d_f = 2`: a label off
the unit whose class is the unit's clears `2 d_f²`, attained at
`θ`'s own shape — the class binder, the unit binder and the width
binder each forged in turn, every forgery moving the conclusion. -/

example : adjchar.theta 2 = [2, 0] := by decide +kernel
example : (fusion.dataA 2).cls (adjchar.theta 2) = 0 := by decide +kernel
example : (fusion.dataA 2).eqL (adjchar.theta 2)
    (fusion.dataA 2).unit = false := by decide +kernel
example : c2hat.dfQ (adjchar.theta 2) = 8 := by decide +kernel
example : 2 * (2 * 2) ≤ c2hat.dfQ (adjchar.theta 2) :=
  unitCrossFloor 2 (adjchar.theta 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : 2 * (2 * 2) ≤ c2hat.dfQ (adjchar.theta 2) := by decide +kernel

example : (([1, 0] : Shape).length == 2) = true := by decide +kernel
example : ¬ ((fusion.dataA 2).cls [1, 0] = 0) := by decide +kernel
example : (fusion.dataA 2).eqL [1, 0] (fusion.dataA 2).unit
    = false := by decide +kernel
example : ¬ (2 * (2 * 2) ≤ c2hat.dfQ [1, 0]) := by decide +kernel

example : (((fusion.dataA 2).unit.length == 2)) = true := by decide +kernel
example : (fusion.dataA 2).cls (fusion.dataA 2).unit = 0 := by decide +kernel
example : (fusion.dataA 2).eqL (fusion.dataA 2).unit
    (fusion.dataA 2).unit = true := by decide +kernel
example : ¬ (2 * (2 * 2) ≤ c2hat.dfQ (fusion.dataA 2).unit) := by
  decide +kernel

example : (([0] : Shape).length == 2) = false := by decide +kernel
example : (fusion.dataA 2).cls [0] = 0 := by decide +kernel
example : (fusion.dataA 2).eqL [0] (fusion.dataA 2).unit = false := by
  decide +kernel
example : ¬ (2 * (2 * 2) ≤ c2hat.dfQ [0]) := by decide +kernel

/-! The merge's strict gap at a crossing family with two nonunit
classes: the fundamental pair at `d_f = 2` nets the unit class and
attains the gap exactly, and the pair at classes one and two on the
side-five family reads it below its own content — with the count
binder refused at a lone nonunit member and the width binder at a
family off the residue. -/

example : famFold Nat.add 0 (fun s =>
    if (fusion.dataA 2).cls s == 0 then 0 else 1)
    [[1, 0], [1, 0]] = 2 := by decide +kernel
example : (fusion.dataA 2).clsFloorN
    (famFold Nat.add 0 (fun s => (fusion.dataA 2).cls s)
      [[1, 0], [1, 0]] % 2) = 0 := by decide +kernel
example : famFold Nat.add 0 (fun s => c2hat.dfQ s)
    [[1, 0], [1, 0]] = 6 := by decide +kernel
example : (fusion.dataA 2).clsFloorN
      (famFold Nat.add 0 (fun s => (fusion.dataA 2).cls s)
        [[1, 0], [1, 0]] % 2) + 2 * (2 + 1)
    = famFold Nat.add 0 (fun s => c2hat.dfQ s) [[1, 0], [1, 0]] := by
  decide +kernel
example : (fusion.dataA 2).clsFloorN
      (famFold Nat.add 0 (fun s => (fusion.dataA 2).cls s)
        [[1, 0], [1, 0]] % 2) + 2 * (2 + 1)
    ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) [[1, 0], [1, 0]] :=
  famSubStrict 2 (by decide +kernel) [[1, 0], [1, 0]] (by decide +kernel) (by decide +kernel)

example : famFold Nat.add 0 (fun s => (fusion.dataA 5).cls s)
    [casfloor.fundShape 1 4, casfloor.fundShape 2 3] % 5 = 3 := by
  decide +kernel
example : famFold Nat.add 0 (fun s => c2hat.dfQ s)
    [casfloor.fundShape 1 4, casfloor.fundShape 2 3] = 60 := by decide +kernel
example : (fusion.dataA 5).clsFloorN
      (famFold Nat.add 0 (fun s => (fusion.dataA 5).cls s)
        [casfloor.fundShape 1 4, casfloor.fundShape 2 3] % 5)
      + 2 * (5 + 1)
    ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s)
      [casfloor.fundShape 1 4, casfloor.fundShape 2 3] :=
  famSubStrict 5 (by decide +kernel)
    [casfloor.fundShape 1 4, casfloor.fundShape 2 3] (by decide +kernel)
    (by decide +kernel)
example : (fusion.dataA 5).clsFloorN
      (famFold Nat.add 0 (fun s => (fusion.dataA 5).cls s)
        [casfloor.fundShape 1 4, casfloor.fundShape 2 3] % 5)
      + 2 * (5 + 1)
    ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s)
      [casfloor.fundShape 1 4, casfloor.fundShape 2 3] := by decide +kernel

example : famFold Nat.add 0 (fun s =>
    if (fusion.dataA 2).cls s == 0 then 0 else 1) [[1, 0]] = 1 := by
  decide +kernel
example : ¬ ((fusion.dataA 2).clsFloorN
      (famFold Nat.add 0 (fun s => (fusion.dataA 2).cls s)
        [[1, 0]] % 2) + 2 * (2 + 1)
    ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) [[1, 0]]) := by decide +kernel

example : (([[1], [1]] : List Shape).all (fun s => s.length == 2))
    = false := by decide +kernel
example : famFold Nat.add 0 (fun s =>
    if (fusion.dataA 2).cls s == 0 then 0 else 1) [[1], [1]] = 2 := by
  decide +kernel
example : ¬ ((fusion.dataA 2).clsFloorN
      (famFold Nat.add 0 (fun s => (fusion.dataA 2).cls s)
        [[1], [1]] % 2) + 2 * (2 + 1)
    ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) [[1], [1]]) := by decide +kernel

/-! The netted family's two members at their classes' floors: the
fundamental pair at `d_f = 2` nets the unit class and attains twice
the least nonunit floor, with the net binder refused at a lone
nonunit member and the count binder at the all-unit family. -/

example : 2 * ((2 - 1) * (2 + 1))
    ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) [[1, 0], [1, 0]] :=
  famNetUnit 2 (by decide +kernel) [[1, 0], [1, 0]] (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
example : 2 * ((2 - 1) * (2 + 1))
    = famFold Nat.add 0 (fun s => c2hat.dfQ s) [[1, 0], [1, 0]] := by
  decide +kernel

example : famFold Nat.add 0 (fun s => (fusion.dataA 2).cls s)
    [[1, 0]] % 2 = 1 := by decide +kernel
example : 1 ≤ famFold Nat.add 0 (fun s =>
    if (fusion.dataA 2).cls s == 0 then 0 else 1) [[1, 0]] := by decide +kernel
example : ¬ (2 * ((2 - 1) * (2 + 1))
    ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) [[1, 0]]) := by decide +kernel

example : famFold Nat.add 0 (fun s => (fusion.dataA 2).cls s)
    [[0, 0]] % 2 = 0 := by decide +kernel
example : famFold Nat.add 0 (fun s =>
    if (fusion.dataA 2).cls s == 0 then 0 else 1) [[0, 0]] = 0 := by
  decide +kernel
example : ¬ (2 * ((2 - 1) * (2 + 1))
    ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) [[0, 0]]) := by decide +kernel

/-! The crossing count at the landed winding configurations: the
straight string crosses each of its own direction's cuts once and
the transverse direction's not at all, so the price rides at the
count's unit and the priced floor reads the winding floor. -/

example : crossCountAt 3 (fiberdec.torusRegion 2 3)
    (fun s => fiberdec.digitAt 3 0 s) wind 0 = 1 := by decide +kernel
example : crossCountAt 3 (fiberdec.torusRegion 2 3)
    (fun s => fiberdec.digitAt 3 0 s) wind 1 = 1 := by decide +kernel
example : crossCountAt 3 (fiberdec.torusRegion 2 3)
    (fun s => fiberdec.digitAt 3 1 s) wind 0 = 0 := by decide +kernel
example : famFold Nat.add 0 (fun e =>
    famFold Nat.add 0 (fun x =>
      if 2 ≤ crossCountAt 3 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) wind x then 1 else 0)
      (List.range 3)) (List.range 2) = 0 := by decide +kernel
example : 3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 3).clsFloorN
        (fluxAt 3 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 wind % 3))
      (List.range 2)
    + 2 * (3 + 1) * famFold Nat.add 0 (fun e =>
        famFold Nat.add 0 (fun x =>
          if 2 ≤ crossCountAt 3 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) wind x then 1 else 0)
          (List.range 3)) (List.range 2)
    ≤ carrier.contentN (fusion.dataA 3) wind :=
  windFloorPriced 3 2 3 wind (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The two-string attainment at `d_f = 2`: two straight
fundamental cycles on neighbouring rows of the first direction, the
strings' classes netting the unit class at every cut of that
direction, each cut extra-crossed at two nonunit members, and the
priced floor attained exactly at the configuration's content — the
price at three extra-crossed cuts and the floor at the count's
unit. -/

/-- The fundamental label at `d_f = 2`. -/
private def fund2 : Shape := casfloor.fundShape 1 1

/-- The unit label at `d_f = 2`. -/
private def unit2 : Shape := labels.unitL 2

/-- The two-string configuration: one straight fundamental cycle
along the first direction on each of two rows, every further key
unoccupied. -/
private def twoRows : List Shape :=
  [fund2, fund2, fund2, fund2, fund2, fund2]
    ++ List.replicate 12 unit2

example : fund2 = [1, 0] := by decide +kernel
example : c2hat.dfQ fund2 = 3 := by decide +kernel
example : (fusion.dataA 2).cls fund2 = 1 := by decide +kernel

example : carrier.occupied (fusion.dataA 2) torus23 twoRows = true := by
  decide +kernel
example : (twoRows.all (fun s => s.length == 2)) = true := by decide +kernel
example : chargeT 2 2 3 twoRows = [0, 0] := by decide +kernel

example : crossCountAt 2 (fiberdec.torusRegion 2 3)
    (fun s => fiberdec.digitAt 3 0 s) twoRows 0 = 2 := by decide +kernel
example : crossCountAt 2 (fiberdec.torusRegion 2 3)
    (fun s => fiberdec.digitAt 3 0 s) twoRows 1 = 2 := by decide +kernel
example : crossCountAt 2 (fiberdec.torusRegion 2 3)
    (fun s => fiberdec.digitAt 3 0 s) twoRows 2 = 2 := by decide +kernel
example : crossCountAt 2 (fiberdec.torusRegion 2 3)
    (fun s => fiberdec.digitAt 3 1 s) twoRows 0 = 0 := by decide +kernel

example : fluxAt 2 torus23 cut0 0 twoRows % 2 = 0 := by decide +kernel
example : 3 * famFold Nat.add 0 (fun e =>
    (fusion.dataA 2).clsFloorN
      (fluxAt 2 (fiberdec.torusRegion 2 3)
        (fun s => fiberdec.digitAt 3 e s) 0 twoRows % 2))
    (List.range 2) = 0 := by decide +kernel
example : famFold Nat.add 0 (fun e =>
    famFold Nat.add 0 (fun x =>
      if 2 ≤ crossCountAt 2 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) twoRows x then 1 else 0)
      (List.range 3)) (List.range 2) = 3 := by decide +kernel
example : carrier.contentN (fusion.dataA 2) twoRows = 18 := by decide +kernel

example : 3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 2).clsFloorN
        (fluxAt 2 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 twoRows % 2))
      (List.range 2)
    + 2 * (2 + 1) * famFold Nat.add 0 (fun e =>
        famFold Nat.add 0 (fun x =>
          if 2 ≤ crossCountAt 2 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) twoRows x then 1 else 0)
          (List.range 3)) (List.range 2)
    = carrier.contentN (fusion.dataA 2) twoRows := by decide +kernel
example : 3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 2).clsFloorN
        (fluxAt 2 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 twoRows % 2))
      (List.range 2)
    + 2 * (2 + 1) * famFold Nat.add 0 (fun e =>
        famFold Nat.add 0 (fun x =>
          if 2 ≤ crossCountAt 2 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) twoRows x then 1 else 0)
          (List.range 3)) (List.range 2)
    ≤ carrier.contentN (fusion.dataA 2) twoRows :=
  windFloorPriced 2 2 3 twoRows (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The price is exact at the attainment: one further extra-crossed
cut moves the display past the configuration's own content. -/

example : ¬ (3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 2).clsFloorN
        (fluxAt 2 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 twoRows % 2))
      (List.range 2)
    + 2 * (2 + 1) * (famFold Nat.add 0 (fun e =>
        famFold Nat.add 0 (fun x =>
          if 2 ≤ crossCountAt 2 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) twoRows x then 1 else 0)
          (List.range 3)) (List.range 2) + 1)
    ≤ carrier.contentN (fusion.dataA 2) twoRows) := by decide +kernel

/-! The configuration binders at the priced display: the open
winding line, occupied nowhere, and the thin-label configuration,
reading a width off the residue, each undercut their own content
where the price rides at the count's unit. -/

example : famFold Nat.add 0 (fun e =>
    famFold Nat.add 0 (fun x =>
      if 2 ≤ crossCountAt 3 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) open1 x then 1 else 0)
      (List.range 3)) (List.range 2) = 0 := by decide +kernel
example : ¬ (3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 3).clsFloorN
        (fluxAt 3 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 open1 % 3))
      (List.range 2)
    + 2 * (3 + 1) * famFold Nat.add 0 (fun e =>
        famFold Nat.add 0 (fun x =>
          if 2 ≤ crossCountAt 3 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) open1 x then 1 else 0)
          (List.range 3)) (List.range 2)
    ≤ carrier.contentN (fusion.dataA 3) open1) := by decide +kernel

example : famFold Nat.add 0 (fun e =>
    famFold Nat.add 0 (fun x =>
      if 2 ≤ crossCountAt 3 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) thin3 x then 1 else 0)
      (List.range 3)) (List.range 2) = 0 := by decide +kernel
example : ¬ (3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 3).clsFloorN
        (fluxAt 3 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 thin3 % 3))
      (List.range 2)
    + 2 * (3 + 1) * famFold Nat.add 0 (fun e =>
        famFold Nat.add 0 (fun x =>
          if 2 ≤ crossCountAt 3 (fiberdec.torusRegion 2 3)
            (fun s => fiberdec.digitAt 3 e s) thin3 x then 1 else 0)
          (List.range 3)) (List.range 2)
    ≤ carrier.contentN (fusion.dataA 3) thin3) := by decide +kernel

/-! The tie's exactness, the merge's three cost identities and the
two clearing comparisons, each at its theorem route beside the
kernel's own value, with one isolating refusal per load-bearing
binder of the tie identities. -/

example : (3 : Nat) + 1 = 4 :=
  tieOnly 4 3 1 1 1 rfl rfl (by decide +kernel)
example : ¬ ((fusion.dataA 4).clsFloorN 1 + 1 * 2 * (4 + 1)
    = (fusion.dataA 4).clsFloorN 2) := by decide +kernel
example : ¬ ((fusion.dataA 5).clsFloorN 1 + 1 * 1 * (5 + 1)
    = (fusion.dataA 5).clsFloorN 3) := by decide +kernel
example : ¬ ((fusion.dataA 4).clsFloorN 3 + 1 * 2 * (4 + 1)
    = (fusion.dataA 4).clsFloorN 2) := by decide +kernel
example : ¬ ((fusion.dataA 2).clsFloorN 3 + 2 * 2 * (2 + 1)
    = (fusion.dataA 2).clsFloorN 1) := by decide +kernel

example : (fusion.dataA 5).clsFloorN 1 + (fusion.dataA 5).clsFloorN 2
    = (fusion.dataA 5).clsFloorN (1 + 2) + 2 * (1 * 2) * (5 + 1) :=
  mergeBelow 5 1 2 2 rfl
example : (fusion.dataA 5).clsFloorN 1 + (fusion.dataA 5).clsFloorN 2
    = (fusion.dataA 5).clsFloorN (1 + 2)
      + 2 * (1 * 2) * (5 + 1) := by decide +kernel
example : (fusion.dataA 4).clsFloorN 1 + (fusion.dataA 4).clsFloorN 3
    = 2 * (1 * 3) * (4 + 1) :=
  mergeDrop 4 1 3 rfl
example : (fusion.dataA 4).clsFloorN 1 + (fusion.dataA 4).clsFloorN 3
    = 2 * (1 * 3) * (4 + 1) := by decide +kernel
example : (fusion.dataA 3).clsFloorN 2 + (fusion.dataA 3).clsFloorN 2
    = (fusion.dataA 3).clsFloorN 1 + 2 * (1 * 1) * (3 + 1) :=
  mergeBeyond 3 2 2 1 1 1 rfl rfl rfl
example : (fusion.dataA 3).clsFloorN 2 + (fusion.dataA 3).clsFloorN 2
    = (fusion.dataA 3).clsFloorN 1 + 2 * (1 * 1) * (3 + 1) := by
  decide +kernel

example : 2 * (2 + 1) ≤ 2 * (2 * 2) := unitCrossClears 2 (by decide +kernel)
example : 2 * (5 + 1) ≤ 2 * (5 * 5) := unitCrossClears 5 (by decide +kernel)
example : ¬ (2 * (1 + 1) ≤ 2 * (1 * 1)) := by decide +kernel
example : 2 * (2 + 1) ≤ 2 * ((2 - 1) * (2 + 1)) :=
  netUnitClears 2 (by decide +kernel)
example : ¬ (2 * (1 + 1) ≤ 2 * ((1 - 1) * (1 + 1))) := by decide +kernel

/-! The netted family's width binder, refused at two short labels
netting the unit class with the count occupied. -/

example : famFold Nat.add 0
    (fun s => (fusion.dataA 2).cls s) [[1], [1]] % 2 = 0 := by decide +kernel
example : 1 ≤ famFold Nat.add 0 (fun s =>
    if (fusion.dataA 2).cls s == 0 then 0 else 1) [[1], [1]] := by
  decide +kernel
example : ¬ (2 * ((2 - 1) * (2 + 1))
    ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) [[1], [1]]) := by
  decide +kernel

/-! The priced floor with both summands occupied: two straight
direction-0 fundamental strings beside one direction-1 string at
`d_f = 3` on the torus of side three — the floor at 48, the price
at three extra-crossed cuts, and the display attained at the
content exactly. -/

private def joint3 : List places.Shape :=
  [casfloor.fundShape 1 2, casfloor.fundShape 1 2,
   casfloor.fundShape 1 2, casfloor.fundShape 1 2,
   casfloor.fundShape 1 2, casfloor.fundShape 1 2,
   labels.unitL 3, labels.unitL 3, labels.unitL 3,
   casfloor.fundShape 1 2, labels.unitL 3, labels.unitL 3,
   casfloor.fundShape 1 2, labels.unitL 3, labels.unitL 3,
   casfloor.fundShape 1 2, labels.unitL 3, labels.unitL 3]

example : carrier.occupied (fusion.dataA 3)
    (fiberdec.torusRegion 2 3) joint3 = true := by decide +kernel
example : (joint3.all (fun s => s.length == 3)) = true := by decide +kernel
example : crossCountAt 3 (fiberdec.torusRegion 2 3)
    (fun s => fiberdec.digitAt 3 0 s) joint3 0 = 2 := by decide +kernel
example : crossCountAt 3 (fiberdec.torusRegion 2 3)
    (fun s => fiberdec.digitAt 3 1 s) joint3 0 = 1 := by decide +kernel
example : famFold Nat.add 0 (fun e =>
    (fusion.dataA 3).clsFloorN
      (fluxAt 3 (fiberdec.torusRegion 2 3)
        (fun s => fiberdec.digitAt 3 e s) 0 joint3 % 3))
    (List.range 2) = 16 := by decide +kernel
example : famFold Nat.add 0 (fun e =>
    famFold Nat.add 0 (fun x =>
      if 2 ≤ crossCountAt 3 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) joint3 x
        then 1 else 0) (List.range 3)) (List.range 2) = 3 := by decide +kernel
example : carrier.contentN (fusion.dataA 3) joint3 = 72 := by decide +kernel
example : 3 * 16 + 2 * (3 + 1) * 3 = 72 := by decide +kernel
example : 3 * famFold Nat.add 0 (fun e =>
      (fusion.dataA 3).clsFloorN
        (fluxAt 3 (fiberdec.torusRegion 2 3)
          (fun s => fiberdec.digitAt 3 e s) 0 joint3 % 3))
    (List.range 2)
    + 2 * (3 + 1) * famFold Nat.add 0 (fun e =>
        famFold Nat.add 0 (fun x =>
          if 2 ≤ crossCountAt 3 (fiberdec.torusRegion 2 3)
              (fun s => fiberdec.digitAt 3 e s) joint3 x
            then 1 else 0) (List.range 3)) (List.range 2)
    ≤ carrier.contentN (fusion.dataA 3) joint3 :=
  windFloorPriced 3 2 3 joint3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The dressing fold's interface at `d_f = 2`: the fusion row of a
fundamental against `θ`, the three excited labels' content gaps
against the source's at the cleared Casimir units, and the class's
endpoint floor. -/

example : (fusion.dataA 2).row [1, 0] [2, 0] = [[3, 0], [1, 0]] := by
  decide +kernel
example : c2hat.dfQ [1, 0] + 36
    = 3 * (2 * 2 * 2) + c2hat.dfQ [3, 0] := by decide +kernel
example : c2hat.dfQ [1, 0] + 24
    = 3 * (2 * 2 * 2) + c2hat.dfQ [1, 0] := by decide +kernel
example : (fusion.dataA 2).clsFloorN 1 = 3 := by decide +kernel

/-! The same interface at `d_f = 3`: the row of a fundamental
against `θ` at the column-occupancy carrier, its three members'
content gaps over the source, the vertex gap at the vacuum, and the
class's endpoint floor. -/

example : (fusion.dataA 3).row [1, 0, 0] [1, 1, 0]
    = [[2, 1, 0], [0, 2, 0], [1, 0, 0]] := by decide +kernel
example : c2hat.dfQ [1, 0, 0] + 78
    = 3 * 18 + c2hat.dfQ [2, 1, 0] := by decide +kernel
example : c2hat.dfQ [1, 0, 0] + 66
    = 3 * 18 + c2hat.dfQ [0, 2, 0] := by decide +kernel
example : c2hat.dfQ [1, 0, 0] + 54
    = 3 * 18 + c2hat.dfQ [1, 0, 0] := by decide +kernel
example : 4 * (fusion.dataA 3).c2D = 72 := by decide +kernel
example : 4 * (fusion.dataA 2).c2D = 32 := by decide +kernel
example : (fusion.dataA 3).clsFloorN 1 = 8 := by decide +kernel

/-! The stencil at the charge-one instance: the vacuum's two atoms,
the string's four, one far plaquette, and the string with an
inflated changed-edge entry. -/

private def vacAtoms : List (Pos × Pos) := [(1, 32), (1, 32)]
private def strAtoms : List (Pos × Pos) :=
  [(1, 36), (1, 24), (1, 32), (1, 32)]
private def farAtoms : List (Pos × Pos) := [(1, 72)]
private def strInflated : List (Pos × Pos) :=
  [(1, 36), (5, 24), (1, 32), (1, 32)]

/-! The free end reads the winding-floor pair alone, the theorem
route beside the kernel's own. -/

example : (tension ⟨3, 8⟩ ⟨1, 1⟩ [] []).oneValue
    (CPair.ofPair ⟨3, 8⟩ .one) := tension_free ⟨3, 8⟩ ⟨1, 1⟩ []
example : (tension ⟨3, 8⟩ ⟨1, 1⟩ [] []).oneValue
    (CPair.ofPair ⟨3, 8⟩ .one) := by decide +kernel

/-! The far plaquette joined to both members leaves the value
standing; joined to the string's member alone it moves the
value. -/

example : (tension ⟨3, 8⟩ ⟨1, 1⟩ (vacAtoms ++ farAtoms)
      (strAtoms ++ farAtoms)).oneValue
    (tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms) :=
  tension_far ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms farAtoms
example : (tension ⟨3, 8⟩ ⟨1, 1⟩ (vacAtoms ++ farAtoms)
      (strAtoms ++ farAtoms)).oneValue
    (tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms) := by decide +kernel
example : ¬ (tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms
    (strAtoms ++ farAtoms)).oneValue
    (tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms) := by decide +kernel

/-! The committed instance's side at the unit magnetic weight: the
tension reads its upper side, and an inflated string entry carries
it to the lower. -/

example : ¬ (tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms
    < (tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms).swap) := by decide +kernel
example : tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strInflated
    < (tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strInflated).swap := by decide +kernel

/-! The head atom splits off the dressing fold at one committed
atom, the theorem route beside the kernel's own. -/

example : (dressFold ⟨1, 1⟩
      ((1, 36) :: [(1, 24), (1, 32), (1, 32)])).oneValue
    (CPair.ofPair (⟨1, 1⟩ * ⟨1 * 1, 36⟩) .one
      + dressFold ⟨1, 1⟩ [(1, 24), (1, 32), (1, 32)]) :=
  dressFold_cons ⟨1, 1⟩ (1, 36) [(1, 24), (1, 32), (1, 32)]
example : (dressFold ⟨1, 1⟩
      ((1, 36) :: [(1, 24), (1, 32), (1, 32)])).oneValue
    (CPair.ofPair (⟨1, 1⟩ * ⟨1 * 1, 36⟩) .one
      + dressFold ⟨1, 1⟩ [(1, 24), (1, 32), (1, 32)]) := by decide +kernel

/-! The tension's side at the seam's tie: two representatives of one
ray read one side, and off the tie the two sides part — the second
pair's fourth power carries the string's atom past the electric
member while the first pair's leaves it standing. -/

example : (tensionAt 1 2 3 8 vacAtoms strAtoms
      < (tensionAt 1 2 3 8 vacAtoms strAtoms).swap)
    ↔ (tensionAt 2 4 3 8 vacAtoms strAtoms
      < (tensionAt 2 4 3 8 vacAtoms strAtoms).swap) :=
  tension_ray 1 2 2 4 (by decide +kernel) 3 8 vacAtoms strAtoms
example : ¬ ((1 : Pos) * 1 = 9 * 2) := by decide +kernel
example : ¬ (tensionAt 1 2 3 8 vacAtoms strAtoms
    < (tensionAt 1 2 3 8 vacAtoms strAtoms).swap) := by decide +kernel
example : tensionAt 9 1 3 8 vacAtoms strAtoms
    < (tensionAt 9 1 3 8 vacAtoms strAtoms).swap := by decide +kernel
example : ¬ ((tensionAt 1 2 3 8 vacAtoms strAtoms
      < (tensionAt 1 2 3 8 vacAtoms strAtoms).swap)
    ↔ (tensionAt 9 1 3 8 vacAtoms strAtoms
      < (tensionAt 9 1 3 8 vacAtoms strAtoms).swap)) := by decide +kernel

/-! Clause (iv)'s charged decimation.  The charge grouping at the
`d = 1` torus: at `d_f = 2`, side five, the vacuum configuration
and the fundamental winding string sit at the charges `[0]` and
`[1]`, the string occupied, and the two one-member groups read
their own keys — the keys exchanged, the grouping refuses; at
`d_f = 3`, side nine, the same pair reads the same keys at the
record's own width. -/

private def u : BPair := BPair.unit

private def R15 : lattice.Region := fiberdec.torusRegion 1 5
private def cfV : List Shape :=
  (List.range R15.links).map (fun _ => [0, 0])
private def cfW : List Shape :=
  (List.range R15.links).map (fun _ => [1, 0])

example : chargeT 2 1 5 cfV = [0] := by decide +kernel
example : chargeT 2 1 5 cfW = [1] := by decide +kernel
example : carrier.occupied (fusion.dataA 2) R15 cfW = true := by decide +kernel
example : chargeGroupsAt 2 1 5 [[0], [1]] [[cfV], [cfW]] = true := by
  decide +kernel
example : ¬ (chargeGroupsAt 2 1 5 [[0], [1]] [[cfW], [cfV]]
    = true) := by decide +kernel

private def R19 : lattice.Region := fiberdec.torusRegion 1 9
private def cfV3 : List Shape :=
  (List.range R19.links).map (fun _ => [0, 0, 0])
private def cfW3 : List Shape :=
  (List.range R19.links).map (fun _ => [1, 0, 0])

example : chargeT 3 1 9 cfV3 = [0] := by decide +kernel
example : chargeT 3 1 9 cfW3 = [1] := by decide +kernel
example : carrier.occupied (fusion.dataA 3) R19 cfW3 = true := by decide +kernel

/-! The row's charge preservation at the `d = 2`, `L = 2` torus: the
first plaquette fuses four of the eight links by `θ`, the row's
sixteen occupied targets each reading the source's charge — the
theorem's route and the kernel's own read at the one instance. -/

private def R22 : lattice.Region := fiberdec.torusRegion 2 2
private def cf22 : List Shape :=
  (List.range R22.links).map (fun _ => [1, 0])
private def p22 : List (Nat × Bool) := getAt [] R22.plaqs 0

example : ((algebra.plaqRow (fusion.dataA 2) R22 p22 cf22).all
    (fun b => chargeT 2 2 2 b == chargeT 2 2 2 cf22)) = true :=
  chargeRow 2 2 2 p22 cf22
example : (algebra.plaqRow (fusion.dataA 2) R22 p22 cf22).length = 16
    ∧ ((algebra.plaqRow (fusion.dataA 2) R22 p22 cf22).all
      (fun b => chargeT 2 2 2 b == chargeT 2 2 2 cf22)) = true := by
  decide +kernel

/-! The charge blocking at the record's two sectors: the vacuum
sector's block at the pencil datum ten and the charge-one sector's
at eighteen, the pencil the assembled block diagonal at the vacant
coupling, one refusal per load-bearing conjunct — the index
reordered against the concatenation, the keys exchanged against
the groups, a duplicated key against the keys' distinctness with
its two side reads passing, a forged order list against the
groups' lengths, and a forged pencil entry against the assembled
read. -/

private def gsQ : List (List (List Shape)) := [[cfV3], [cfW3]]
private def ixQ : List (List Shape) := [cfV3, cfW3]
private def csQ : List (List Nat) := [[0], [1]]
private def diagQ : List elim.Mat := [[[⟨11, 1⟩]], [[⟨19, 1⟩]]]
private def hQ : elim.Mat :=
  greenprod.assemble diagQ (unitOffs [1, 1])
private def hF : elim.Mat := [[⟨11, 1⟩, u], [u, ⟨20, 1⟩]]

example : greenprod.assemble diagQ (unitOffs [1, 1])
    = [[⟨11, 1⟩, u], [u, ⟨19, 1⟩]] := by decide +kernel
example : chargeBlockRead 3 1 9 ixQ csQ gsQ hQ diagQ [1, 1] := by
  decide +kernel
example : ¬ chargeBlockRead 3 1 9 [cfW3, cfV3] csQ gsQ hQ diagQ
    [1, 1] := by decide +kernel
example : ¬ chargeBlockRead 3 1 9 ixQ [[1], [0]] gsQ hQ diagQ
    [1, 1] := by decide +kernel
example : decimation.confListEq (fusion.dataA 3)
    ([[cfV3], [cfV3]].flatMap (fun g => g)) [cfV3, cfV3] = true := by
  decide +kernel
example : chargeGroupsAt 3 1 9 [[0], [0]] [[cfV3], [cfV3]]
    = true := by decide +kernel
example : ¬ chargeBlockRead 3 1 9 [cfV3, cfV3] [[0], [0]]
    [[cfV3], [cfV3]] hQ diagQ [1, 1] := by decide +kernel
example : gsQ.map List.length = [1, 1] := by decide +kernel
example : ¬ chargeBlockRead 3 1 9 ixQ csQ gsQ hQ diagQ [2, 1] := by
  decide +kernel
example : ¬ elim.matOneValue hF
    (greenprod.assemble diagQ (unitOffs [1, 1])) := by decide +kernel
example : ¬ chargeBlockRead 3 1 9 ixQ csQ gsQ hF diagQ [1, 1] := by
  decide +kernel

/-! The counts split over the charge blocks at a committed level:
the two sectors' site data at level six, the vacuum sector one
reversal and the charged sector vacant, and the assembled block
diagonal at their sum — `lem:inertia`'s block-diagonal addition
read at the blocking's own assembled pencil, the assembled literal
the join's own. -/

private def dgL : List elim.Mat := [[[⟨1, 3⟩]], [[⟨7, 1⟩]]]
private def spA1 : inertia.Split 1 :=
  ⟨⟨inertia.idMat 1, rfl⟩, ⟨inertia.idMat 1, rfl⟩,
   [.one ⟨1, 3⟩], 0, rfl⟩
private def spB1 : inertia.Split 1 :=
  ⟨⟨inertia.idMat 1, rfl⟩, ⟨inertia.idMat 1, rfl⟩,
   [.one ⟨7, 1⟩], 0, rfl⟩
private def spS2 : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, rfl⟩, ⟨inertia.idMat 2, rfl⟩,
   [.one ⟨1, 3⟩, .one ⟨7, 1⟩], 0, rfl⟩

example : greenprod.assemble dgL (unitOffs [1, 1])
    = inertia.blockJoin [[⟨1, 3⟩]]
      (List.replicate 1 (List.replicate 1 BPair.unit))
      [[⟨7, 1⟩]] := by decide +kernel
example : inertia.splitRead
    (greenprod.assemble dgL (unitOffs [1, 1])) spS2 := by decide +kernel
example : inertia.revAt spS2
    = inertia.revAt spA1 + inertia.revAt spB1 :=
  inertia.rev_join [[⟨1, 3⟩]] [[⟨7, 1⟩]] spA1 (by decide +kernel) spB1
    (by decide +kernel) spS2 (by decide +kernel)
example : inertia.revAt spS2 = 1 := by decide +kernel

/-! The charged head's shift transport: the class-one endpoint
floor at `d_f = 3` is the pair of eight against eighteen, the side
length nine reading the shift four at the cross-multiplied
witness; the charged sector's datum is the vacuum's shifted by
four grams, and a charged count at a level is the vacuum sector's
count at the shift cross-added onto the level — both directions at
the theorem's own route, the unshifted level refusing beside
them. -/

private def secQ0 : elim.Mat := [[⟨11, 1⟩]]
private def gramQ1 : elim.Mat := [[⟨3, 1⟩]]

example : (fusion.dataA 3).clsFloorN 1 = 8 := by decide +kernel
example : (fusion.dataA 3).c2D = 18 := by decide +kernel
example : 9 * 8 = 4 * 18 := by decide +kernel
example : elim.matOneValue [[⟨19, 1⟩]]
    (elim.matAdd (inertia.matScale 4 gramQ1) secQ0) := by decide +kernel

private def spSh0 : inertia.Split 1 :=
  ⟨⟨inertia.idMat 1, rfl⟩, ⟨inertia.idMat 1, rfl⟩,
   [.one ⟨7, 1⟩], 0, rfl⟩
private def spSh1 : inertia.Split 1 :=
  ⟨⟨inertia.idMat 1, rfl⟩, ⟨inertia.idMat 1, rfl⟩,
   [.one ⟨1, 3⟩], 0, rfl⟩

example : certconstruct.countAtPair
    (elim.matAdd (inertia.matScale 4 gramQ1) secQ0) gramQ1 7 1 0
    spSh0 := by decide +kernel
example : certconstruct.countAtPair secQ0 gramQ1 7 (1 + 4) 0 spSh0 :=
  (certconstruct.countAtPair_shift secQ0 gramQ1 4 7 1 0 spSh0
    (by decide +kernel)).mp (by decide +kernel)
example : certconstruct.countAtPair
    (elim.matAdd (inertia.matScale 4 gramQ1) secQ0) gramQ1 11 1 1
    spSh1 :=
  (certconstruct.countAtPair_shift secQ0 gramQ1 4 11 1 1 spSh1
    (by decide +kernel)).mpr (by decide +kernel)
example : ¬ certconstruct.countAtPair secQ0 gramQ1 7 1 0 spSh0 := by
  decide +kernel

/-! The tension's first root located at the string's term count: at
the electric member `3/8` and the unit stencil pair the vacant
vacuum against nine string atoms reads equal members — neither side
strictly below the other — and one atom further the value reads its
lower side, the root bracketed between the two term counts. -/

private def strNine : List (Pos × Pos) :=
  List.replicate 9 ((1 : Pos), (24 : Pos))
private def strTen : List (Pos × Pos) :=
  List.replicate 10 ((1 : Pos), (24 : Pos))

example : ¬ (tension ⟨3, 8⟩ ⟨1, 1⟩ [] strNine
    < (tension ⟨3, 8⟩ ⟨1, 1⟩ [] strNine).swap) := by decide +kernel
example : ¬ ((tension ⟨3, 8⟩ ⟨1, 1⟩ [] strNine).swap
    < tension ⟨3, 8⟩ ⟨1, 1⟩ [] strNine) := by decide +kernel
example : tension ⟨3, 8⟩ ⟨1, 1⟩ [] strTen
    < (tension ⟨3, 8⟩ ⟨1, 1⟩ [] strTen).swap := by decide +kernel

/-! The least-length read extends: the per-length pair at the
length's one-member entry reads the per-cell side at every length,
the committed instance at side nine. -/

example : (CPair.ofPair (Pair.ofPos 9) .one
      * tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms
    < (CPair.ofPair (Pair.ofPos 9) .one
      * tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms).swap)
    ↔ (tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms
      < (tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms).swap) :=
  tension_length 9 ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms
example : ¬ (CPair.ofPair (Pair.ofPos 9) .one
    * tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms
    < (CPair.ofPair (Pair.ofPos 9) .one
      * tension ⟨3, 8⟩ ⟨1, 1⟩ vacAtoms strAtoms).swap) := by decide +kernel

/-! The matched stencil's free-end read: at one list on both
members the folds withdraw and the value is the winding-floor
pair, the vacant instance beside it above. -/

example : (tension ⟨3, 8⟩ ⟨1, 1⟩ strAtoms strAtoms).oneValue
    (CPair.ofPair ⟨3, 8⟩ .one) :=
  tension_free ⟨3, 8⟩ ⟨1, 1⟩ strAtoms
example : (tension ⟨3, 8⟩ ⟨1, 1⟩ strAtoms strAtoms).oneValue
    (CPair.ofPair ⟨3, 8⟩ .one) := by decide +kernel

/-! The atom's read discriminates the entry's square: one atom at
entry two reads four against its gap, the entry itself refused. -/

example : (dressFold ⟨1, 1⟩ [((2 : Pos), (24 : Pos))]).oneValue
    (CPair.ofPair ⟨4, 24⟩ .one) := by decide +kernel
example : ¬ (dressFold ⟨1, 1⟩ [((2 : Pos), (24 : Pos))]).oneValue
    (CPair.ofPair ⟨2, 24⟩ .one) := by decide +kernel

/-! The charged record at the one head pencil: the two sectors'
site-datum family `S(x) = [[10 - 2x, 0], [0, 18 - 2x]]` at the
clearing power one and the sample weight two, the charged sector's
diagonal the vacuum's shifted by the four grams; its divisor is
the determinant `4x² - 56x + 180`, squarefree at its own Bézout
combination, the three samples at `x = 4, 7, 10` with the counts
`0, 1, 2`, and the two jump boundaries straddling the cleared
roots `40` and `72`.  The blocking's read and the sample
evaluation are pinned at the same pencil — the evaluated head at
the first sample is the cleared site datum of the blocking's own
`H` against four grams — so the level list, the multiplicities
and the block structure are the reads of that head pencil, pinned
per cell. -/

private def spDg (a b : BPair) : inertia.Split 2 :=
  ⟨⟨inertia.idMat 2, rfl⟩, ⟨inertia.idMat 2, rfl⟩,
   [.one a, .one b], 0, rfl⟩
private def spUt (t tw a b : BPair) : inertia.Split 2 :=
  ⟨⟨[[⟨2, 1⟩, t], [u, ⟨2, 1⟩]], rfl⟩,
   ⟨[[⟨2, 1⟩, tw], [u, ⟨2, 1⟩]], rfl⟩,
   [.one a, .one b], 0, rfl⟩

private def sC : split.PMat :=
  [[[⟨11, 1⟩, ⟨1, 3⟩], [u]], [[u], [⟨19, 1⟩, ⟨1, 3⟩]]]

private def ctC : cellcount.DivCert :=
  ⟨[], [⟨181, 1⟩, ⟨1, 57⟩, ⟨5, 1⟩], [⟨1, 57⟩, ⟨9, 1⟩], [⟨5, 1⟩],
   [⟨15, 1⟩, ⟨1, 3⟩], [⟨181, 1⟩, ⟨1, 57⟩, ⟨5, 1⟩], [⟨5, 1⟩],
   [⟨15, 1⟩, ⟨1, 3⟩], 1, 1, 1, 1, ⟨1, 65⟩, ⟨1, 65⟩⟩

private def spHDC : inertia.Split 2 :=
  spUt ⟨1, 29⟩ ⟨29, 1⟩ ⟨3, 1⟩ ⟨129, 1⟩

private def cellsC : List (BPair × Nat × inertia.Split 2) :=
  [(⟨9, 1⟩, 0, spDg ⟨5, 1⟩ ⟨21, 1⟩),
   (⟨15, 1⟩, 1, spDg ⟨1, 9⟩ ⟨9, 1⟩),
   (⟨21, 1⟩, 2, spDg ⟨1, 21⟩ ⟨1, 5⟩)]

private def bndsC : List (decimation.Bound 2) :=
  [.jump (spUt ⟨1, 41⟩ ⟨41, 1⟩ ⟨513, 1⟩ ⟨1, 40961⟩),
   .jump (spUt ⟨1, 17⟩ ⟨17, 1⟩ ⟨513, 1⟩ ⟨1, 40961⟩)]

private def recC : decimation.DivRecord 2 2 :=
  ⟨sC, 1, 2, ctC, spHDC, cellsC, bndsC⟩

example : decimation.recordRead recC := by decide +kernel
example : recC.cells.map (fun x => x.1)
    = [⟨9, 1⟩, ⟨15, 1⟩, ⟨21, 1⟩] := by decide +kernel
example : recC.cells.map (fun x => x.2.1) = [0, 1, 2] := by decide +kernel
example : elim.matOneValue (cellcount.evalPC sC ⟨9, 1⟩ 2 1)
    (inertia.matScale 2 (inertia.siteDatum hQ
      (inertia.matScale 4 (greenprod.assemble
        [[[⟨3, 1⟩]], [[⟨3, 1⟩]]] (unitOffs [1, 1]))))) := by decide +kernel
example : decimation.recordRead recC
    ∧ chargeBlockRead 3 1 9 ixQ csQ gsQ hQ diagQ [1, 1] := by decide +kernel
