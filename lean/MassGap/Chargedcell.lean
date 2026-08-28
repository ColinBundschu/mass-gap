import MassGap.Fusion
import MassGap.Casfloor
import MassGap.Carrier
import MassGap.Fiberdec
import MassGap.Decimation
/-!
`lem:chargedcell` — the charged cells, clause (i)'s class tier at
the label calculus.  The `d_f`-ality of a label is the box count's
remainder at the fundamental count, the chain endpoint's index:
the reduction withdraws one full-column count so the ality is one
value at the class (`ality_reduce`), the dual's ality joins its
label's to the unit class at the complement's degree
(`ality_dual`), `θ`'s reads the unit class at the adjoint's degree
(`ality_theta`), and the class laws of `con:fusion` hold at the
label calculus over every factor pair — the row's additivity at
the enumeration's stated degree (`clsLaw_all`), the dual's join
(`clsDualLaw_all`), the unit label's ality (`ality_unit`) and
`θ`'s unit-class law (`clsThetaLaw_all`) — the vertex law, the
flux and the charge
tiers' reads at the interface's class data.  Clause (i)'s vertex
law lands at the fusion interface (`vertexLaw`): at a positive
invariant count of a label list, the list's class fold under the
class group's sum (`clsFold`) reads the unit's code, the class
laws entering relativized to a label domain — off the domain they
are false, so the relativization is the consumer's own scope —
with the label calculus discharging every hypothesis at the stated
width (`vertexLaw_all`).  The flux tier rides above it: a
transverse cut family enters as a stated site grading with its
decidable read (`transCutRead`), the flux through a cut is the
class fold over the crossing links (`fluxAt`), the vertex laws
summed over one slab withdraw the interior links' pairs at the
dual's join and read consecutive cuts at one class mod the
residue (`fluxConserve`), and the charge at the torus is the
per-direction flux family at the base cut (`chargeT`).  Clause
(i)'s translation clause closes that tier: a translation permutes
the index at one charge, the relabeled configuration's flux
through a cut its own through the moved cut — the moved cut
entering as the per-link transport of the endpoint grades
(`cutMoveRead`), one term per link along the permutation with the
directions kept — and the conservation reads the base cut's class
back, so the charge family stands at the relabeling
(`chargeT_perm`).  Above them
sit clause (i)'s `θ`-row read — a fusion by `θ` fixes every link's
`d_f`-ality, each member of a `θ`-row reading the source's class
(`clsRow_theta`) — and clause (ii)'s winding floor: every shape
reads its class's endpoint floor, the floors are subadditive at
the class merge, and an occupied configuration's content clears
the side length times the per-direction floor sum at the torus,
each direction's cuts netting the base cut's class and the
directions' crossing families disjoint per link (`windFloor`, at
`cutDisjRead`'s per-link read).  Clause (ii)'s tie sentence: two
distinct class codes' floors tie exactly at the dual pair
(`tieDual`, with `tieOnly` the exactness) and part by the crossed
gaps on the two strict sides of the pair sum's trichotomy against
`d_f` (`tieBelow`, `tieBeyond`); the merge's three cost identities
(`mergeBelow`, `mergeDrop`, `mergeBeyond`) join two classes' floors
at their net's with the crossed product doubled, and the merge of
two nonunit classes clears two residue counts below the two
classes' own (`mergeGap`).  Clause (iii)'s price tier reads beside
them: the cut's nonunit crossing count (`crossCountAt`), the unit
class's least nonunit read (`unitCrossFloor`) with the two clearing
comparisons (`unitCrossClears`, `netUnitClears`), the crossing
family's strict merge price (`famSubStrict`) and netted floor
(`famNetUnit`), and the priced winding floor (`windFloorPriced`),
every extra-crossed cut joining the merge's gap to the floor.  Clause (iii)'s prices ride above the floor: a label
off the unit label whose class is the unit's reads `θ`'s own
cleared Casimir (`unitCrossFloor`), a crossing family with two
nonunit classes prices its net class two residue counts below its
own content (`famSubStrict`) and one netting the unit class holds
two members at their classes' floors (`famNetUnit`), and the
winding floor gains its price at the cuts' nonunit crossing counts
(`crossCountAt`) — every cut crossed at two nonunit members joins
the merge's strict gap to the floor (`windFloorPriced`).  Clause
(iii)'s dressing fold and tension close the module at the composite
pair: the tower decimation's per-cell Schur read enters as one pair
`[e² : g]` per stencil atom at the changed-edge entry and the
content gap, summed at the squared magnetic weight (`dressFold`,
its head splitting off at `dressFold_cons`), and the tension is the
balance pair of the string's dressed per-cell floor against the
unit class's — the winding-floor pair at a one-member site, the
vacuum's fold on the first member and the string's on the second
through the memberwise swap (`tension`), read at the ray's factors
with `q²` at the electric member and `[p⁴ : q²]` at the two folds
(`tensionAt`).  Its three sentences: far plaquettes' folds enter
both members equally and the value stands (`tension_far`), at the
free end both folds read the end's one member and the value is the
winding-floor pair (`tension_free`), and the tension's side is a
ray datum at the seam's cross-multiplied tie (`tension_ray`).
-/

namespace chargedcell
open ground places




/-- The ality is one value at the class: the reduction withdraws
one full-column count from the degree, `lem:chargedcell`'s
chain-endpoint clause at the box count's remainder. -/
theorem ality_reduce (d : Nat) :
    ∀ s : Shape, s.length = d →
      degree (labels.reduce s) % d = degree s % d := by
  match d with
  | 0 =>
    intro s h
    match s, h with
    | [], _ => rfl
  | k + 1 =>
    intro s h
    match ground.snoc_split k s h with
    | ⟨s', a, hs, hl⟩ =>
      rw [hs, labels.reduce_snoc s' a, degree_snoc s' a, degree_snoc s' 0,
        Nat.zero_mul, Nat.add_zero, hl]
      exact (ground.modAddMul (degree s') a (k + 1)).symm

/-- The dual's ality joins its label's to the unit class: the
complement's degree joins the label's to the top row's full
columns. -/
theorem ality_dual (d : Nat) :
    ∀ s : Shape, s.length = d →
      (degree s % d + degree (labels.dualL s) % d) % d = 0 := by
  intro s h
  rw [ground.modAdd (degree s) (degree (labels.dualL s)) d,
    labels.degree_dualL_add s, h, Nat.mul_comm d (sumNat s)]
  exact ground.modMulSelf (sumNat s) d

/-- The class additivity holds at the label calculus over every
factor pair: a row member's reduced degree joins the factors'
degree fold to full columns, the enumeration's stated degree with
the reduction's withdrawal. -/
theorem clsLaw_all (d : Nat) (a b : Shape) :
    fusion.clsLaw (fusion.dataA d) a b := by
  refine ground.all_filterMap_mem _ _ _ (fun c hc y hy => ?_)
  have hcs := allShapes_sound d (degree a + degree b) c hc
  by_cases h0 : 0 < steinberg.count a b c
  · rw [if_pos h0] at hy
    have hyv : y = labels.reduce c := (Option.some.inj hy).symm
    rw [hyv]
    show Nat.beq (degree (labels.reduce c) % d)
        ((degree a % d + degree b % d) % d) = true
    rw [ality_reduce d c hcs.1, hcs.2, ground.modAdd]
    exact ground.beqRefl _
  · rw [if_neg h0] at hy
    exact nomatch hy

/-- The dual's class law at the label calculus. -/
theorem clsDualLaw_all (d : Nat) (a : Shape) (h : a.length = d) :
    fusion.clsDualLaw (fusion.dataA d) a := by
  show (degree (labels.dualL a) % d + degree a % d) % d
    = degree (labels.unitL d) % d
  rw [Nat.add_comm (degree (labels.dualL a) % d) (degree a % d),
    ality_dual d a h]
  rw [show degree (labels.unitL d) = 0 from by
    show sumNat (rowList (List.replicate d 0)) = 0
    rw [rowList_replicate_zero d, sumNat_replicate_zero d]]
  rw [ground.modZeroLeft d]

/-- The unit label's class code at the label calculus. -/
theorem ality_unit (d : Nat) :
    (fusion.dataA d).cls (fusion.dataA d).unit = 0 := by
  show degree (labels.unitL d) % d = 0
  rw [show degree (labels.unitL d) = 0 from by
    show sumNat (rowList (List.replicate d 0)) = 0
    rw [rowList_replicate_zero d, sumNat_replicate_zero d]]
  exact ground.modZeroLeft d


/-- `θ`'s class is the unit class: the adjoint's degree is the
fundamental count, one column of the residue's length beside the
one box. -/
theorem ality_theta : ∀ d : Nat,
    degree (adjchar.theta d) % d = 0
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | e + 2 => by
    have hrep : (List.replicate (e + 2) (0 : Nat)).length = e + 2 :=
      ground.length_replicate 0 (e + 2)
    have hlen : (ground.bumpAt e
        (List.replicate (e + 2) 0)).length = e + 2 :=
      (ground.length_bumpAt e (List.replicate (e + 2) 0)).trans hrep
    show degree (ground.bumpAt 0
      (ground.bumpAt e (List.replicate (e + 2) 0))) % (e + 2) = 0
    rw [places.degree_bumpAt 0 _ (by rw [hlen]; exact Nat.succ_pos (e + 1)),
      places.degree_bumpAt e _ (by
        rw [hrep]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self e)
          (Nat.le_succ (e + 1))),
      show degree (List.replicate (e + 2) (0 : Nat)) = 0 from by
        show sumNat (rowList (List.replicate (e + 2) 0)) = 0
        rw [rowList_replicate_zero (e + 2),
          sumNat_replicate_zero (e + 2)],
      Nat.zero_add]
    exact ground.modOf (Nat.succ_pos (e + 1))
      (by rw [Nat.mul_one, Nat.add_zero]) (Nat.succ_pos (e + 1))

/-- `θ`'s class law at the label calculus. -/
theorem clsThetaLaw_all (d : Nat) :
    fusion.clsThetaLaw (fusion.dataA d) := by
  show degree (adjchar.theta d) % d = degree (labels.unitL d) % d
  rw [ality_theta d]
  exact (ality_unit d).symm

/-! `lem:chargedcell`(i)'s vertex law at the fusion interface: the
class fold of a label list under the class group's sum, and its
unit read at a positive invariant count.  The class laws enter
relativized to a label domain `P`, the consumer's own scope — at
the label calculus `P` is the stated width, off which the laws are
false — and the induction runs on the list's length as its own
fuel, the row expansion absorbing the leading pair into one row
member whose class the additivity law reads back. -/

/-- The class fold of a label list: the vacant list at the unit's
code, a nonvacant one at the class group's sum over the members'
codes, the leading label the seed. -/
def clsFold {L : Type} (F : fusion.Data L) : List L → Nat
  | [] => F.cls F.unit
  | l :: t => t.foldl (fun acc x => F.clsAdd acc (F.cls x)) (F.cls l)

/-- A positive additive fold reads a positive member, the family
fold's own witness at the hoisted seed. -/
private theorem foldPos {α : Type} (f : α → Nat) (l : List α)
    (h : 0 < l.foldl (fun acc x => acc + f x) 0) :
    ∃ x, x ∈ l ∧ 0 < f x := by
  rw [ground.foldlSum f l 0, Nat.zero_add] at h
  exact ground.famFold_pos_mem f l h

/-- The vertex law's induction at the list's length as its own
fuel: the one-label read is the unit, the pair's read the duality,
and three labels or more absorb the leading pair into a row member
whose class the additivity law reads as the pair's sum. -/
private theorem vertexGo {L : Type} (F : fusion.Data L) (P : L → Bool)
    (hrow : ∀ a b : L, P a = true → P b = true →
      ((F.row a b).all P) = true)
    (hlaw : ∀ a b : L, P a = true → P b = true → fusion.clsLaw F a b)
    (hdual : ∀ a : L, P a = true → fusion.clsDualLaw F a)
    (hinv : ∀ a b : L, P a = true → P b = true →
      F.eqL a b = true → F.cls a = F.cls b)
    (hunit : P F.unit = true)
    (hdualP : ∀ a : L, P a = true → P (F.dual a) = true) :
    ∀ (n : Nat) (ls : List L), ls.length = n → ls.all P = true →
      0 < carrier.invCount F ls → clsFold F ls = F.cls F.unit
  | 0, [], _, _, _ => rfl
  | 0, _ :: _, hn, _, _ => Nat.noConfusion hn
  | _ + 1, [], _, _, _ => rfl
  | _ + 1, [l], _, hls, hpos => by
    have hPl : P l = true :=
      ground.all_of_mem P [l] hls l (List.Mem.head [])
    show F.cls l = F.cls F.unit
    exact hinv l F.unit hPl hunit
      (carrier.invCount_one_pos F l hpos)
  | _ + 1, [l1, l2], _, hls, hpos => by
    have hP1 : P l1 = true :=
      ground.all_of_mem P [l1, l2] hls l1 (List.Mem.head [l2])
    have hP2 : P l2 = true :=
      ground.all_of_mem P [l1, l2] hls l2
        (List.Mem.tail l1 (List.Mem.head []))
    have hcls : F.cls l1 = F.cls (F.dual l2) :=
      hinv l1 (F.dual l2) hP1 (hdualP l2 hP2)
        (carrier.invCount_pair_pos F l1 l2 hpos)
    show F.clsAdd (F.cls l1) (F.cls l2) = F.cls F.unit
    rw [hcls]
    exact hdual l2 hP2
  | n + 1, l1 :: l2 :: l3 :: rest, hn, hls, hpos => by
    have hP1 : P l1 = true :=
      ground.all_of_mem P (l1 :: l2 :: l3 :: rest) hls l1
        (List.Mem.head (l2 :: l3 :: rest))
    have hP2 : P l2 = true :=
      ground.all_of_mem P (l1 :: l2 :: l3 :: rest) hls l2
        (List.Mem.tail l1 (List.Mem.head (l3 :: rest)))
    have hls2 : (l2 :: l3 :: rest).all P = true :=
      (ground.andSplitB
        (show (P l1 && (l2 :: l3 :: rest).all P) = true from hls)).2
    have hls3 : (l3 :: rest).all P = true :=
      (ground.andSplitB
        (show (P l2 && (l3 :: rest).all P) = true from hls2)).2
    rw [carrier.invCount_cons] at hpos
    match foldPos
        (fun c => F.count l1 l2 c * carrier.invCount F (c :: l3 :: rest))
        (F.row l1 l2) hpos with
    | ⟨c, hc, hcpos⟩ =>
      have hposc : 0 < carrier.invCount F (c :: l3 :: rest) := by
        cases hv : carrier.invCount F (c :: l3 :: rest) with
        | zero =>
          rw [hv, Nat.mul_zero] at hcpos
          exact absurd hcpos (Nat.lt_irrefl 0)
        | succ k => exact Nat.succ_pos k
      have hPc : P c = true :=
        ground.all_of_mem P (F.row l1 l2) (hrow l1 l2 hP1 hP2) c hc
      have hclsc : F.cls c = F.clsAdd (F.cls l1) (F.cls l2) :=
        ground.beqEq _ _
          (ground.all_of_mem
            (fun x => Nat.beq (F.cls x) (F.clsAdd (F.cls l1) (F.cls l2)))
            (F.row l1 l2) (hlaw l1 l2 hP1 hP2) c hc)
      have hallc : (c :: l3 :: rest).all P = true := by
        show (P c && (l3 :: rest).all P) = true
        rw [hPc, hls3]
        exact rfl
      have hIH := vertexGo F P hrow hlaw hdual hinv hunit hdualP n
        (c :: l3 :: rest) (Nat.succ.inj hn) hallc hposc
      show (l3 :: rest).foldl (fun acc x => F.clsAdd acc (F.cls x))
          (F.clsAdd (F.cls l1) (F.cls l2)) = F.cls F.unit
      rw [← hclsc]
      exact hIH

/-- `lem:chargedcell`(i)'s vertex law at the fusion interface: at a
positive invariant count of a label list, the list's class fold
reads the unit's code — the class laws, the row's closure and the
label equality's class read taken over a stated label domain. -/
theorem vertexLaw {L : Type} (F : fusion.Data L) (P : L → Bool)
    (hrow : ∀ a b : L, P a = true → P b = true →
      ((F.row a b).all P) = true)
    (hlaw : ∀ a b : L, P a = true → P b = true → fusion.clsLaw F a b)
    (hdual : ∀ a : L, P a = true → fusion.clsDualLaw F a)
    (hinv : ∀ a b : L, P a = true → P b = true →
      F.eqL a b = true → F.cls a = F.cls b)
    (hunit : P F.unit = true)
    (hdualP : ∀ a : L, P a = true → P (F.dual a) = true)
    (ls : List L) (hls : ls.all P = true)
    (hpos : 0 < carrier.invCount F ls) :
    clsFold F ls = F.cls F.unit :=
  vertexGo F P hrow hlaw hdual hinv hunit hdualP ls.length ls rfl hls hpos


/-- The row's members all read the stated width at the label
calculus: a row member is a reduced shape of the enumeration at
that width. -/
private theorem lenP_row (d : Nat) : ∀ a b : Shape,
    (((fusion.dataA d).row a b).all (fun s => s.length == d)) = true := by
  intro a b
  refine ground.all_filterMap_mem _ _ _ (fun c hc y hy => ?_)
  have hcs := allShapes_sound d (degree a + degree b) c hc
  by_cases h0 : 0 < steinberg.count a b c
  · rw [if_pos h0] at hy
    have hyv : y = labels.reduce c := (Option.some.inj hy).symm
    rw [hyv]
    show ((labels.reduce c).length == d) = true
    exact ground.eqBeqOf ((labels.length_reduce c).trans hcs.1)
  · rw [if_neg h0] at hy
    exact nomatch hy

/-- The dual keeps the stated width: the occupancy reversal off the
full-column key. -/
private theorem lenP_dual (d : Nat) : ∀ a : Shape,
    (a.length == d) = true →
      ((labels.dualL a).length == d) = true :=
  fun a ha => ground.eqBeqOf
    ((labels.length_dualL a).trans (ground.beqEqOf ha))

/-- The label equality reads one class at the stated width: equal
labels reduce alike, and the ality is one value at the class. -/
private theorem lenP_inv (d : Nat) : ∀ a b : Shape,
    (a.length == d) = true → (b.length == d) = true →
      (fusion.dataA d).eqL a b = true →
      (fusion.dataA d).cls a = (fusion.dataA d).cls b := by
  intro a b ha hb heq
  have hre : labels.reduce a = labels.reduce b :=
    ground.listBeqEq
      (show (labels.reduce a == labels.reduce b) = true from heq)
  show degree a % d = degree b % d
  rw [← ality_reduce d a (ground.beqEqOf ha), hre,
    ality_reduce d b (ground.beqEqOf hb)]

/-- The vertex law at the label calculus: at a positive invariant
count of shapes of the stated width, the class fold reads the unit
label's ality, every hypothesis discharged by the calculus's own
class tier. -/
theorem vertexLaw_all (d : Nat) (ls : List Shape)
    (hls : (ls.all (fun s => s.length == d)) = true)
    (hpos : 0 < carrier.invCount (fusion.dataA d) ls) :
    clsFold (fusion.dataA d) ls
      = (fusion.dataA d).cls (fusion.dataA d).unit :=
  vertexLaw (fusion.dataA d) (fun s => s.length == d)
    (fun a b _ _ => lenP_row d a b)
    (fun a b _ _ => clsLaw_all d a b)
    (fun a ha => clsDualLaw_all d a (ground.beqEqOf ha))
    (fun a b ha hb h => lenP_inv d a b ha hb h)
    (ground.eqBeqOf (ground.length_replicate 0 d))
    (fun a ha => lenP_dual d a ha)
    ls hls hpos

/-! `lem:chargedcell`(i)'s flux tier at the label calculus: a
transverse cut family enters as a stated site grading, the flux
through a cut is the class fold over the crossing links, and the
vertex laws summed over one slab withdraw the interior links'
pairs at the dual's join, reading consecutive cuts at one class
mod `n`; the charge at the torus is the per-direction flux family
at the base cut. -/

/-- The transverse-cut family at a stated site grading: every
grade below the count, and every link's head grade its tail's or
the tail's cyclic successor — the links moving one grade the
crossings, the cut family's own. -/
def transCutRead (R : lattice.Region) (g : Nat → Nat) (c : Nat) :
    Prop :=
  (((List.range R.verts).all (fun v => g v < c))
    && ((R.tail.zip R.head).all (fun e =>
      (g e.2 == g e.1)
        || (g e.2 == (g e.1 + 1) % c)))) = true

instance (R : lattice.Region) (g : Nat → Nat) (c : Nat) :
    Decidable (transCutRead R g c) :=
  inferInstanceAs (Decidable (_ = _))

/-- The per-link fold along the link family: the tails and the
heads read together with the label list beside them, one stated
read per link, a label beyond its list at the stated default. -/
private def linkFold (dflt : Shape) (f : Nat → Nat → Shape → Nat) :
    List Nat → List Nat → List Shape → Nat
  | t :: ts, h :: hs, s :: as' => f t h s + linkFold dflt f ts hs as'
  | t :: ts, h :: hs, [] => f t h dflt + linkFold dflt f ts hs []
  | [], _, _ => 0
  | _ :: _, [], _ => 0

/-- The flux fold at a cut: the class codes of the links crossing
out of the stated grade, the cut's own class read. -/
def fluxAt (n : Nat) (R : lattice.Region) (g : Nat → Nat) (x : Nat)
    (a : List Shape) : Nat :=
  linkFold (fusion.dataA n).unit (fun t h s =>
    if (!(g h == g t)) && (g t == x)
      then (fusion.dataA n).cls s else 0) R.tail R.head a

/-- The moved cut's transport along a translation — every link's
endpoint grades at the image link read the stated grade map of its
own, the per-link term of the relabeled flux
(`lem:chargedcell`(i)'s translation clause at `con:lattice`'s
translation field). -/
def cutMoveRead (R : lattice.Region) (t : Nat → Nat)
    (g : Nat → Nat) (mv : Nat → Nat) : Prop :=
  ground.pairIdxAll (fun l tl hd =>
    (g (getAt 0 R.tail (t l)) == mv (g tl))
      && (g (getAt 0 R.head (t l)) == mv (g hd)))
    R.tail R.head 0 = true

instance (R : lattice.Region) (t : Nat → Nat) (g : Nat → Nat)
    (mv : Nat → Nat) : Decidable (cutMoveRead R t g mv) :=
  inferInstanceAs (Decidable (_ = _))

/-- The endpoint families' per-link read: a fold over the tails and
the heads together reads at every link key, the entry pair the two
endpoint reads' own. -/
private theorem zipRead {P : Nat × Nat → Bool} (R : lattice.Region)
    (hall : ((R.tail.zip R.head).all P) = true)
    (l : Nat) (hl : l < R.links) :
    P (getAt 0 R.tail l, getAt 0 R.head l) = true := by
  have hlen : (List.zipWith Prod.mk R.tail R.head).length = R.links :=
    ground.length_zipWith Prod.mk R.tail R.head R.links R.tailLen R.headLen
  have hk : P (getAt ((0 : Nat), (0 : Nat))
      (List.zipWith Prod.mk R.tail R.head) l) = true :=
    ground.all_getAt ((0 : Nat), (0 : Nat))
      (List.zipWith Prod.mk R.tail R.head) hall l
      (by rw [hlen]; exact hl)
  rw [ground.getAt_zipWith 0 0 ((0 : Nat), (0 : Nat)) Prod.mk
      R.tail R.head l (by rw [R.tailLen]; exact hl)
      (by rw [R.headLen]; exact hl)] at hk
  exact hk

/-- The cut family's per-link read: at every link key the head's
grade is the tail's own or its cyclic successor. -/
private theorem transCut_at (R : lattice.Region) (g : Nat → Nat)
    (c : Nat) (hcut : transCutRead R g c)
    (l : Nat) (hl : l < R.links) :
    ((g (getAt 0 R.head l) == g (getAt 0 R.tail l))
      || (g (getAt 0 R.head l)
          == (g (getAt 0 R.tail l) + 1) % c)) = true :=
  zipRead R (ground.andSplitB (show
      (((List.range R.verts).all (fun v => g v < c))
        && ((R.tail.zip R.head).all (fun e =>
          (g e.2 == g e.1)
            || (g e.2 == (g e.1 + 1) % c)))) = true from hcut)).2
    l hl

/-- The moved cut's per-link read: at every link key the image
link's endpoint grades are the stated grade map's values at the
link's own. -/
private theorem cutMove_at (R : lattice.Region) (t : Nat → Nat)
    (g : Nat → Nat) (mv : Nat → Nat) (hmv : cutMoveRead R t g mv)
    (l : Nat) (hl : l < R.links) :
    ((g (getAt 0 R.tail (t l)) == mv (g (getAt 0 R.tail l)))
      && (g (getAt 0 R.head (t l))
          == mv (g (getAt 0 R.head l)))) = true := by
  have h := ground.pairIdxAll_at (fun l' tl hd =>
      (g (getAt 0 R.tail (t l')) == mv (g tl))
        && (g (getAt 0 R.head (t l')) == mv (g hd)))
    R.tail R.head 0 hmv l
    (by rw [R.tailLen]; exact hl) (by rw [R.headLen]; exact hl)
  rw [Nat.zero_add] at h
  exact h

/-- The per-link fold reads at the link keys: at matched endpoint
lengths the walk's value is the key fold over the family. -/
private theorem linkFold_read (dflt : Shape)
    (f : Nat → Nat → Shape → Nat) :
    ∀ (t h : List Nat) (a : List Shape), h.length = t.length →
      linkFold dflt f t h a
        = famFold Nat.add 0 (fun l =>
            f (getAt 0 t l) (getAt 0 h l) (getAt dflt a l))
          (List.range t.length)
  | [], _, _, _ => rfl
  | _ :: _, [], _, hl => nomatch hl
  | t0 :: ts, h0 :: hs, a, hl => by
    have hlen : hs.length = ts.length := Nat.succ.inj hl
    have hIH := linkFold_read dflt f ts hs a.tail hlen
    have hstep : linkFold dflt f (t0 :: ts) (h0 :: hs) a
        = f t0 h0 (getAt dflt a 0) + linkFold dflt f ts hs a.tail := by
      cases a with
      | nil => rfl
      | cons _ _ => rfl
    have hfold : famFold Nat.add 0 (fun l =>
          f (getAt 0 (t0 :: ts) l) (getAt 0 (h0 :: hs) l)
            (getAt dflt a l)) (List.range (ts.length + 1))
        = f t0 h0 (getAt dflt a 0)
          + famFold Nat.add 0 (fun j =>
              f (getAt 0 ts j) (getAt 0 hs j) (getAt dflt a.tail j))
            (List.range ts.length) := by
      rw [ground.range_cons ts.length]
      show f t0 h0 (getAt dflt a 0)
          + famFold Nat.add 0 (fun l =>
              f (getAt 0 (t0 :: ts) l) (getAt 0 (h0 :: hs) l)
                (getAt dflt a l))
            ((List.range ts.length).map (fun j => j + 1))
        = _
      rw [ground.famFold_map Nat.add 0 (fun l =>
          f (getAt 0 (t0 :: ts) l) (getAt 0 (h0 :: hs) l)
            (getAt dflt a l)) (fun j => j + 1) (List.range ts.length)]
      refine congrArg (fun y => f t0 h0 (getAt dflt a 0) + y) ?_
      refine ground.famFold_congr_all Nat.add 0 _ _ (fun j => ?_)
        (List.range ts.length)
      show f (getAt 0 ts j) (getAt 0 hs j) (getAt dflt a (j + 1)) = _
      rw [ground.getAt_tail dflt a j]
    show linkFold dflt f (t0 :: ts) (h0 :: hs) a
      = famFold Nat.add 0 (fun l =>
          f (getAt 0 (t0 :: ts) l) (getAt 0 (h0 :: hs) l)
            (getAt dflt a l)) (List.range (ts.length + 1))
    rw [hfold, hstep, hIH]

/-- The flux at a cut reads the link keys: at the shape read's
endpoint lengths the walk's value is the key fold over the region's
links. -/
private theorem fluxAt_read (n : Nat) (R : lattice.Region)
    (g : Nat → Nat) (x : Nat) (a : List Shape)
    :
    fluxAt n R g x a
      = famFold Nat.add 0 (fun l =>
          if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
              && (g (getAt 0 R.tail l) == x)
            then (fusion.dataA n).cls
              (getAt (fusion.dataA n).unit a l)
            else 0) (List.range R.links) := by
  have h := linkFold_read (fusion.dataA n).unit
    (fun t h s => if (!(g h == g t)) && (g t == x)
      then (fusion.dataA n).cls s else 0)
    R.tail R.head a (R.headLen.trans R.tailLen.symm)
  rw [R.tailLen] at h
  exact h

/-- The cut family's grade read: every vertex of the region carries
a grade below the stated count. -/
private theorem cutGrade (R : lattice.Region) (g : Nat → Nat) (c : Nat)
    (hcut : transCutRead R g c) (v : Nat) (hv : v < R.verts) : g v < c :=
  of_decide_eq_true (ground.all_of_mem _ _
    (ground.andSplitB (show
      (((List.range R.verts).all (fun w => g w < c))
        && ((R.tail.zip R.head).all (fun e =>
          (g e.2 == g e.1)
            || (g e.2 == (g e.1 + 1) % c)))) = true from hcut)).1
    v (ground.memRange hv))

/-- The cyclic successor is injective below the count: two grades
below the count with one successor are one grade. -/
private theorem succModInj (c x y : Nat) (hx : x < c) (hy : y < c)
    (h : (x + 1) % c = (y + 1) % c) : x = y := by
  have htop : ∀ k : Nat, k + 1 = c → (k + 1) % c = 0 := by
    intro k he
    rw [he]
    have hm := ground.modMulSelf 1 c
    rw [Nat.one_mul] at hm
    exact hm
  cases Nat.eq_or_lt_of_le (show x + 1 ≤ c from hx) with
  | inl hxe =>
    cases Nat.eq_or_lt_of_le (show y + 1 ≤ c from hy) with
    | inl hye => exact Nat.succ.inj (hxe.trans hye.symm)
    | inr hylt =>
      rw [htop x hxe, ground.modOfLt (y + 1) c hylt] at h
      exact Nat.noConfusion h
  | inr hxlt =>
    cases Nat.eq_or_lt_of_le (show y + 1 ≤ c from hy) with
    | inl hye =>
      rw [htop y hye, ground.modOfLt (x + 1) c hxlt] at h
      exact Nat.noConfusion h
    | inr hylt =>
      rw [ground.modOfLt (x + 1) c hxlt, ground.modOfLt (y + 1) c hylt] at h
      exact Nat.succ.inj h






/-- A summand withdraws from the remainder at the divisor's own
multiple. -/
private theorem modAddZero (n p q : Nat) (hpq : (p + q) % n = 0)
    (hq : q % n = 0) : p % n = 0 := by
  rw [← ground.modAdd p q n, hq, Nat.add_zero, ground.modMod] at hpq
  exact hpq

/-- A shared summand cancels at the remainder: two sums reading the
divisor's multiple read their own summands at one residue. -/
private theorem modCancel (n p q r : Nat) (h1 : (p + q) % n = 0)
    (h2 : (r + q) % n = 0) : p % n = r % n := by
  have e1 : (p + (r + q)) % n = p % n := by
    rw [← ground.modAdd p (r + q) n, h2, Nat.add_zero, ground.modMod]
  have e2 : (r + (p + q)) % n = r % n := by
    rw [← ground.modAdd r (p + q) n, h1, Nat.add_zero, ground.modMod]
  have e3 : p + (r + q) = r + (p + q) := by
    rw [← Nat.add_assoc p r q, ← Nat.add_assoc r p q,
      Nat.add_comm p r]
  rw [← e1, e3, e2]



/-- The one-key fold reads its key's count: a family guarded at a
stated key folds to the value at the key's own count. -/
private theorem keyCollapse (A T : Nat) : ∀ K : List Nat,
    famFold Nat.add 0 (fun v => if T == v then A else 0) K
      = A * ground.countOf T K
  | [] => by
    show (0 : Nat) = A * 0
    rw [Nat.mul_zero]
  | v :: t => by
    have hIH := keyCollapse A T t
    rw [ground.countOf_cons]
    show (if T == v then A else 0)
        + famFold Nat.add 0 (fun u => if T == u then A else 0) t
      = A * ((if T = v then 1 else 0) + ground.countOf T t)
    cases hb : (T == v) with
    | true =>
      rw [if_pos rfl, if_pos (ground.beqEqOf hb), hIH,
        Nat.mul_add A 1 (ground.countOf T t), Nat.mul_one]
    | false =>
      rw [if_neg (fun h : (false = true) => Bool.noConfusion h),
        if_neg (fun he : T = v =>
          Bool.noConfusion (hb.symm.trans (ground.eqBeqOf he))),
        hIH, Nat.mul_add A 0 (ground.countOf T t), Nat.mul_zero]

/-- Every link's label reads the stated width: a key inside the
configuration reads a member, and beyond its top the unit label's
own width. -/
private theorem label_width (n : Nat) (a : List Shape)
    (hw : (a.all (fun s => s.length == n)) = true) (l : Nat) :
    ((getAt (fusion.dataA n).unit a l).length == n) = true := by
  cases Nat.lt_or_ge l a.length with
  | inl h =>
    exact ground.all_of_mem (fun s => s.length == n) a hw _
      (ground.mem_getAt (fusion.dataA n).unit a l h)
  | inr h =>
    rw [ground.getAt_over (fusion.dataA n).unit a l h]
    exact ground.eqBeqOf (ground.length_replicate 0 n)

/-- The incident labels all read the stated width: the outgoing
end its link's label, the incoming end that label's dual. -/
private theorem incident_width (n : Nat) (R : lattice.Region)
    (a : List Shape) (hw : (a.all (fun s => s.length == n)) = true)
    (v : Nat) :
    ((carrier.incidentLabels (fusion.dataA n) R a v).all
      (fun s => s.length == n)) = true := by
  refine ground.all_filterMap_mem _ _ _ (fun e _ y hy => ?_)
  have hy' : (if (fusion.dataA n).eqL
        (getAt (fusion.dataA n).unit a e.1) (fusion.dataA n).unit
      then none
      else if e.2 then some (getAt (fusion.dataA n).unit a e.1)
      else some (labels.dualL (getAt (fusion.dataA n).unit a e.1)))
      = some y := hy
  cases hq : (fusion.dataA n).eqL
      (getAt (fusion.dataA n).unit a e.1) (fusion.dataA n).unit with
  | true =>
    rw [hq] at hy'
    exact nomatch (show (none : Option Shape) = some y from hy')
  | false =>
    rw [hq] at hy'
    cases hb : e.2 with
    | true =>
      rw [hb] at hy'
      have hy2 : some (getAt (fusion.dataA n).unit a e.1) = some y := hy'
      rw [← Option.some.inj hy2]
      exact label_width n a hw e.1
    | false =>
      rw [hb] at hy'
      have hy2 : some (labels.dualL
        (getAt (fusion.dataA n).unit a e.1)) = some y := hy'
      rw [← Option.some.inj hy2]
      exact lenP_dual n _ (label_width n a hw e.1)

/-- A label reading the unit reads the unit's class code. -/
private theorem cls_of_unitEq (n : Nat) (s : Shape)
    (hs : (s.length == n) = true)
    (h : (fusion.dataA n).eqL s (fusion.dataA n).unit = true) :
    (fusion.dataA n).cls s = 0 :=
  (lenP_inv n s (fusion.dataA n).unit hs
      (ground.eqBeqOf (ground.length_replicate 0 n)) h).trans
    (show (fusion.dataA n).cls (fusion.dataA n).unit = 0
      from ality_unit n)

/-- The dual of a unit-class label reads the unit class: the pair's
join is the unit's code and the label's own withdraws. -/
private theorem clsDual_zero (n : Nat) (s : Shape)
    (hs : (s.length == n) = true)
    (hcls : (fusion.dataA n).cls s = 0) :
    (fusion.dataA n).cls (labels.dualL s) = 0 := by
  have hd : ((fusion.dataA n).cls (labels.dualL s)
      + (fusion.dataA n).cls s) % n
      = (fusion.dataA n).cls (fusion.dataA n).unit :=
    clsDualLaw_all n s (ground.beqEqOf hs)
  rw [hcls, Nat.add_zero,
    show (fusion.dataA n).cls (fusion.dataA n).unit = 0
      from ality_unit n] at hd
  exact (ground.modMod (places.degree (labels.dualL s)) n).symm.trans hd

/-- A class code is its own residue. -/
private theorem clsMod (n : Nat) (s : Shape) :
    (fusion.dataA n).cls s % n = (fusion.dataA n).cls s :=
  ground.modMod (places.degree s) n

/-- The class fold's accumulator invariant: the seed rides the fold
at the class group's own remainder. -/
private theorem clsAcc (n : Nat) : ∀ (t : List Shape) (A : Nat),
    t.foldl (fun acc x => (fusion.dataA n).clsAdd acc
        ((fusion.dataA n).cls x)) (A % n)
      = (A + famFold Nat.add 0 (fun s => (fusion.dataA n).cls s) t) % n
  | [], A => by
    show A % n = (A + 0) % n
    rw [Nat.add_zero]
  | x :: t, A => by
    have hseed : (A % n + (fusion.dataA n).cls x) % n
        = (A + (fusion.dataA n).cls x) % n := by
      have h1 := ground.modAdd A ((fusion.dataA n).cls x) n
      rw [clsMod n x] at h1
      exact h1
    show t.foldl (fun acc y => (fusion.dataA n).clsAdd acc
          ((fusion.dataA n).cls y))
        ((A % n + (fusion.dataA n).cls x) % n)
      = (A + ((fusion.dataA n).cls x
          + famFold Nat.add 0 (fun s => (fusion.dataA n).cls s) t)) % n
    rw [hseed, clsAcc n t (A + (fusion.dataA n).cls x),
      Nat.add_assoc A ((fusion.dataA n).cls x)
        (famFold Nat.add 0 (fun s => (fusion.dataA n).cls s) t)]

/-- The class fold reads the members' code sum at the class group's
remainder. -/
private theorem clsFold_famFold (n : Nat) : ∀ ls : List Shape,
    clsFold (fusion.dataA n) ls
      = famFold Nat.add 0 (fun s => (fusion.dataA n).cls s) ls % n
  | [] => by
    show (fusion.dataA n).cls (fusion.dataA n).unit = 0 % n
    rw [show (fusion.dataA n).cls (fusion.dataA n).unit = 0
        from ality_unit n]
    exact (ground.modZeroLeft n).symm
  | l :: t => by
    have h := clsAcc n t ((fusion.dataA n).cls l)
    rw [clsMod n l] at h
    exact h

/-- The vertex's incident labels fold at the region's link range:
the class fold over the incident list is the link-indexed fold at
the vertex's two ends, the incoming end's label dualized and the
unoccupied keys reading the sum's unit. -/
private theorem incidentFold (n : Nat) (R : lattice.Region)
    (a : List Shape) (hwidth : (a.all (fun s => s.length == n)) = true)
    (v : Nat) :
    famFold Nat.add 0 (fun l =>
      (if getAt 0 R.tail l == v
        then (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l)
        else 0)
      + (if getAt 0 R.head l == v
        then (fusion.dataA n).cls
          (labels.dualL (getAt (fusion.dataA n).unit a l))
        else 0)) (List.range R.links)
    = famFold Nat.add 0 (fun s => (fusion.dataA n).cls s)
        (carrier.incidentLabels (fusion.dataA n) R a v) := by
  have hunf : carrier.incidentLabels (fusion.dataA n) R a v
      = ((List.range R.links).flatMap (fun l : Nat =>
          (if getAt 0 R.tail l == v then [(l, true)] else [])
            ++ (if getAt 0 R.head l == v then [(l, false)]
                else []))).filterMap (fun e : Nat × Bool =>
          if (fusion.dataA n).eqL
              (getAt (fusion.dataA n).unit a e.1) (fusion.dataA n).unit
            then none
          else if e.2 then some (getAt (fusion.dataA n).unit a e.1)
          else some (labels.dualL (getAt (fusion.dataA n).unit a e.1))) := by
    show (lattice.incident R v).filterMap (fun e : Nat × Bool =>
        if (fusion.dataA n).eqL
            (getAt (fusion.dataA n).unit a e.1) (fusion.dataA n).unit
          then none
        else if e.2 then some (getAt (fusion.dataA n).unit a e.1)
        else some (labels.dualL (getAt (fusion.dataA n).unit a e.1)))
      = _
    rw [lattice.incident_read R v]
  rw [hunf]
  show famFold Nat.add 0 (fun l =>
      (if getAt 0 R.tail l == v
        then (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l)
        else 0)
      + (if getAt 0 R.head l == v
        then (fusion.dataA n).cls
          (labels.dualL (getAt (fusion.dataA n).unit a l))
        else 0)) (List.range R.links)
    = famFold Nat.add 0 (fun s => (fusion.dataA n).cls s)
        (((List.range R.links).flatMap (fun l : Nat =>
            (if getAt 0 R.tail l == v then [(l, true)] else [])
              ++ (if getAt 0 R.head l == v then [(l, false)]
                  else []))).filterMap (fun e : Nat × Bool =>
          if (fusion.dataA n).eqL
              (getAt (fusion.dataA n).unit a e.1) (fusion.dataA n).unit
            then none
          else if e.2 then some (getAt (fusion.dataA n).unit a e.1)
          else some (labels.dualL (getAt (fusion.dataA n).unit a e.1))))
  rw [ground.famFold_filterMap (fun e : Nat × Bool =>
        if (fusion.dataA n).eqL
            (getAt (fusion.dataA n).unit a e.1) (fusion.dataA n).unit
          then none
        else if e.2 then some (getAt (fusion.dataA n).unit a e.1)
        else some (labels.dualL (getAt (fusion.dataA n).unit a e.1)))
      (fun s => (fusion.dataA n).cls s)
      ((List.range R.links).flatMap (fun l : Nat =>
        (if getAt 0 R.tail l == v then [(l, true)] else [])
          ++ (if getAt 0 R.head l == v then [(l, false)] else []))),
    ground.famFold_flatMap
      (fun e : Nat × Bool =>
        ground.optVal (fun s => (fusion.dataA n).cls s)
          (if (fusion.dataA n).eqL
              (getAt (fusion.dataA n).unit a e.1) (fusion.dataA n).unit
            then none
          else if e.2 then some (getAt (fusion.dataA n).unit a e.1)
          else some (labels.dualL
            (getAt (fusion.dataA n).unit a e.1))))
      (fun l : Nat =>
        (if getAt 0 R.tail l == v then [(l, true)] else [])
          ++ (if getAt 0 R.head l == v then [(l, false)] else []))
      (List.range R.links)]
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun l => ?_)
    (List.range R.links)
  have harmA : ground.optVal (fun s => (fusion.dataA n).cls s)
      (if (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
          (fusion.dataA n).unit = true
        then none
        else some (getAt (fusion.dataA n).unit a l))
      = (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l) := by
    cases hq : (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
        (fusion.dataA n).unit with
    | true =>
      rw [if_pos rfl]
      exact (cls_of_unitEq n _ (label_width n a hwidth l) hq).symm
    | false =>
      rw [if_neg (fun hc : (false = true) => Bool.noConfusion hc)]
      exact rfl
  have harmB : ground.optVal (fun s => (fusion.dataA n).cls s)
      (if (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
          (fusion.dataA n).unit = true
        then none
        else some (labels.dualL (getAt (fusion.dataA n).unit a l)))
      = (fusion.dataA n).cls
          (labels.dualL (getAt (fusion.dataA n).unit a l)) := by
    cases hq : (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
        (fusion.dataA n).unit with
    | true =>
      rw [if_pos rfl]
      exact (clsDual_zero n _ (label_width n a hwidth l)
        (cls_of_unitEq n _ (label_width n a hwidth l) hq)).symm
    | false =>
      rw [if_neg (fun hc : (false = true) => Bool.noConfusion hc)]
      exact rfl
  cases ht : (getAt 0 R.tail l == v) with
  | true =>
    cases hh : (getAt 0 R.head l == v) with
    | true =>
      rw [if_pos rfl, if_pos rfl, if_pos rfl, if_pos rfl]
      show (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l)
          + (fusion.dataA n).cls
              (labels.dualL (getAt (fusion.dataA n).unit a l))
        = ground.optVal (fun s => (fusion.dataA n).cls s)
            (if (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
                (fusion.dataA n).unit = true
              then none
              else some (getAt (fusion.dataA n).unit a l))
          + (ground.optVal (fun s => (fusion.dataA n).cls s)
              (if (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
                  (fusion.dataA n).unit = true
                then none
                else some (labels.dualL
                  (getAt (fusion.dataA n).unit a l)))
            + 0)
      rw [harmA, harmB, Nat.add_zero]
    | false =>
      rw [if_pos rfl, if_pos rfl,
        if_neg (fun h : (false = true) => Bool.noConfusion h),
        if_neg (fun h : (false = true) => Bool.noConfusion h)]
      show (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l) + 0
        = ground.optVal (fun s => (fusion.dataA n).cls s)
            (if (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
                (fusion.dataA n).unit = true
              then none
              else some (getAt (fusion.dataA n).unit a l))
          + 0
      rw [harmA]
  | false =>
    cases hh : (getAt 0 R.head l == v) with
    | true =>
      rw [if_neg (fun h : (false = true) => Bool.noConfusion h),
        if_neg (fun h : (false = true) => Bool.noConfusion h),
        if_pos rfl, if_pos rfl]
      show 0 + (fusion.dataA n).cls
          (labels.dualL (getAt (fusion.dataA n).unit a l))
        = ground.optVal (fun s => (fusion.dataA n).cls s)
            (if (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
                (fusion.dataA n).unit = true
              then none
              else some (labels.dualL
                (getAt (fusion.dataA n).unit a l)))
          + 0
      rw [harmB, Nat.add_zero, Nat.zero_add]
    | false =>
      rw [if_neg (fun h : (false = true) => Bool.noConfusion h),
        if_neg (fun h : (false = true) => Bool.noConfusion h),
        if_neg (fun h : (false = true) => Bool.noConfusion h),
        if_neg (fun h : (false = true) => Bool.noConfusion h)]
      exact rfl

/-- The vertex law summed at one site: the incident labels' class
codes fold to the class group's unit, the outgoing ends reading
their labels and the incoming ends the duals. -/
private theorem vertexSum (n : Nat) (R : lattice.Region)
    (a : List Shape)
    (hocc : carrier.occupied (fusion.dataA n) R a = true)
    (hwidth : (a.all (fun s => s.length == n)) = true)
    (v : Nat) (hv : v < R.verts) :
    famFold Nat.add 0 (fun l =>
      (if getAt 0 R.tail l == v
        then (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l)
        else 0)
      + (if getAt 0 R.head l == v
        then (fusion.dataA n).cls
          (labels.dualL (getAt (fusion.dataA n).unit a l))
        else 0)) (List.range R.links) % n = 0 := by
  rw [incidentFold n R a hwidth v]
  cases hz : ((carrier.incidentLabels (fusion.dataA n) R a v).length
      == 0) with
  | true =>
    rw [ground.nil_of_length_zero _ (ground.beqEqOf hz)]
    exact ground.modZeroLeft n
  | false =>
    have hpos : 0 < carrier.invCount (fusion.dataA n)
        (carrier.incidentLabels (fusion.dataA n) R a v) :=
      carrier.vmult_pos (fusion.dataA n) R a v hv hocc
    have hvl := vertexLaw_all n
      (carrier.incidentLabels (fusion.dataA n) R a v)
      (incident_width n R a hwidth v) hpos
    rw [clsFold_famFold n
      (carrier.incidentLabels (fusion.dataA n) R a v)] at hvl
    rw [hvl]
    exact ality_unit n

/-- The slab collapse: the vertex laws summed over one slab read
the two cuts at one class.  The interior links, whose two ends
share the slab read, withdraw at the dual's join; the crossing
links' outgoing block is the slab's own flux and the incoming
block joins its duals, so the two crossing blocks read one
class. -/
private theorem slabConserve (n : Nat) (Lk K : List Nat)
    (T H w w' : Nat → Nat) (p q q' : Nat → Bool)
    (hcT : ∀ l, l ∈ Lk →
      ground.countOf (T l) K = if q l then 1 else 0)
    (hcH : ∀ l, l ∈ Lk →
      ground.countOf (H l) K = if q' l then 1 else 0)
    (hnc : ∀ l, l ∈ Lk → p l = false → q l = q' l)
    (hdual : ∀ l, l ∈ Lk → (w l + w' l) % n = 0)
    (hslab : famFold Nat.add 0 (fun v =>
        famFold Nat.add 0 (fun l =>
          (if T l == v then w l else 0)
            + (if H l == v then w' l else 0)) Lk) K % n = 0) :
    famFold Nat.add 0 (fun l => if p l && q l then w l else 0) Lk % n
      = famFold Nat.add 0
          (fun l => if p l && q' l then w l else 0) Lk % n := by
  have hper : famFold Nat.add 0 (fun l =>
        famFold Nat.add 0 (fun v =>
          (if T l == v then w l else 0)
            + (if H l == v then w' l else 0)) K) Lk
      = famFold Nat.add 0 (fun l =>
          (if q l then w l else 0) + (if q' l then w' l else 0)) Lk := by
    refine ground.famFold_congr_members Nat.add 0 _ _ Lk (fun l hl => ?_)
    have hlm := ground.mem_of_countOf_pos l Lk hl
    rw [ground.famFold_add_split (fun v => if T l == v then w l else 0)
        (fun v => if H l == v then w' l else 0) K,
      keyCollapse (w l) (T l) K, keyCollapse (w' l) (H l) K,
      hcT l hlm, hcH l hlm]
    cases hq : q l with
    | true =>
      cases hq' : q' l with
      | true =>
        show w l * 1 + w' l * 1 = w l + w' l
        rw [Nat.mul_one, Nat.mul_one]
      | false =>
        show w l * 1 + w' l * 0 = w l + 0
        rw [Nat.mul_one, Nat.mul_zero]
    | false =>
      cases hq' : q' l with
      | true =>
        show w l * 0 + w' l * 1 = 0 + w' l
        rw [Nat.mul_zero, Nat.mul_one]
      | false =>
        show w l * 0 + w' l * 0 = 0 + 0
        rw [Nat.mul_zero, Nat.mul_zero]
  have hS : famFold Nat.add 0 (fun l =>
      (if q l then w l else 0) + (if q' l then w' l else 0)) Lk % n
      = 0 := by
    rw [← hper, ← ground.famFold_swap (fun v l =>
      (if T l == v then w l else 0)
        + (if H l == v then w' l else 0)) K Lk]
    exact hslab
  rw [ground.famFold_add_split (fun l => if q l then w l else 0)
      (fun l => if q' l then w' l else 0) Lk,
    ground.splitGuard p q w Lk, ground.splitGuard p q' w' Lk,
    Nat.add_add_add_comm
      (famFold Nat.add 0 (fun l => if p l && q l then w l else 0) Lk)
      (famFold Nat.add 0
        (fun l => if !(p l) && q l then w l else 0) Lk)
      (famFold Nat.add 0 (fun l => if p l && q' l then w' l else 0) Lk)
      (famFold Nat.add 0
        (fun l => if !(p l) && q' l then w' l else 0) Lk),
    ← ground.famFold_add_split
      (fun l => if !(p l) && q l then w l else 0)
      (fun l => if !(p l) && q' l then w' l else 0) Lk] at hS
  have hNC : famFold Nat.add 0 (fun l =>
      (if !(p l) && q l then w l else 0)
        + (if !(p l) && q' l then w' l else 0)) Lk % n = 0 := by
    refine ground.foldMod n _ Lk (fun l hl => ?_)
    cases hp : p l with
    | true =>
      show ((0 : Nat) + 0) % n = 0
      exact ground.modZeroLeft n
    | false =>
      rw [hnc l hl hp]
      cases hq : q' l with
      | true => exact hdual l hl
      | false =>
        show ((0 : Nat) + 0) % n = 0
        exact ground.modZeroLeft n
  have hFCi := modAddZero n
    (famFold Nat.add 0 (fun l => if p l && q l then w l else 0) Lk
      + famFold Nat.add 0
          (fun l => if p l && q' l then w' l else 0) Lk)
    (famFold Nat.add 0 (fun l =>
      (if !(p l) && q l then w l else 0)
        + (if !(p l) && q' l then w' l else 0)) Lk) hS hNC
  have hCP : famFold Nat.add 0
      (fun l => if p l && q' l then w l + w' l else 0) Lk % n = 0 := by
    refine ground.foldMod n _ Lk (fun l hl => ?_)
    cases hg : (p l && q' l) with
    | true => exact hdual l hl
    | false => exact ground.modZeroLeft n
  rw [ground.pairSplit (fun l => p l && q' l) w w' Lk] at hCP
  exact modCancel n
    (famFold Nat.add 0 (fun l => if p l && q l then w l else 0) Lk)
    (famFold Nat.add 0 (fun l => if p l && q' l then w' l else 0) Lk)
    (famFold Nat.add 0 (fun l => if p l && q' l then w l else 0) Lk)
    hFCi hCP

/-- The conservation's one step: the flux at a cut reads the cut
beneath it at one class, the slab between them summed at the
vertex laws. -/
private theorem fluxStep (n : Nat) (R : lattice.Region)
    (g : Nat → Nat) (c : Nat) (a : List Shape)
    (hwell : lattice.wellRead R)
    (hcut : transCutRead R g c)
    (hocc : carrier.occupied (fusion.dataA n) R a = true)
    (hwidth : (a.all (fun s => s.length == n)) = true)
    (x : Nat) (hx : x + 1 < c) :
    fluxAt n R g (x + 1) a % n = fluxAt n R g x a % n := by
  rw [fluxAt_read n R g (x + 1) a, fluxAt_read n R g x a]
  have htlt : ∀ l : Nat, l ∈ List.range R.links →
      getAt 0 R.tail l < R.verts := fun l hl =>
    (lattice.endLt R hwell l (ground.ltOfMemRange hl)).1
  have hhlt : ∀ l : Nat, l ∈ List.range R.links →
      getAt 0 R.head l < R.verts := fun l hl =>
    (lattice.endLt R hwell l (ground.ltOfMemRange hl)).2
  have hglt : ∀ v : Nat, v < R.verts → g v < c := cutGrade R g c hcut
  have hcross : ∀ l : Nat, l ∈ List.range R.links →
      (g (getAt 0 R.head l) == g (getAt 0 R.tail l)) = false →
      g (getAt 0 R.head l) = (g (getAt 0 R.tail l) + 1) % c := by
    intro l hl hbf
    cases ground.orSplitB (transCut_at R g c hcut l
        (ground.ltOfMemRange hl)) with
    | inl h => exact absurd (h.symm.trans hbf) (by exact Bool.noConfusion)
    | inr h => exact ground.beqEqOf h
  have hslab := slabConserve n (List.range R.links)
    ((List.range R.verts).filter (fun v => g v == x + 1))
    (fun l => getAt 0 R.tail l) (fun l => getAt 0 R.head l)
    (fun l => (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l))
    (fun l => (fusion.dataA n).cls
      (labels.dualL (getAt (fusion.dataA n).unit a l)))
    (fun l => !(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
    (fun l => g (getAt 0 R.tail l) == x + 1)
    (fun l => g (getAt 0 R.head l) == x + 1)
    (fun l hl => by
      rw [ground.countOf_filter (fun v => g v == x + 1)
          (getAt 0 R.tail l) (List.range R.verts),
        countOf_range_one (htlt l hl)])
    (fun l hl => by
      rw [ground.countOf_filter (fun v => g v == x + 1)
          (getAt 0 R.head l) (List.range R.verts),
        countOf_range_one (hhlt l hl)])
    (fun l _ hp => by
      have heq : g (getAt 0 R.head l) = g (getAt 0 R.tail l) := by
        cases hb : (g (getAt 0 R.head l) == g (getAt 0 R.tail l)) with
        | true => exact ground.beqEqOf hb
        | false =>
          rw [hb] at hp
          exact Bool.noConfusion hp
      rw [heq])
    (fun l _ => ality_dual n (getAt (fusion.dataA n).unit a l)
      (ground.beqEqOf (label_width n a hwidth l)))
    (ground.foldMod n _ _ (fun v hv =>
      vertexSum n R a hocc hwidth v
        (ground.ltOfMemRange
          (ground.mem_filter_of (fun u => g u == x + 1)
            (List.range R.verts) v hv).1)))
  refine hslab.trans (congrArg (fun y => y % n) ?_)
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range R.links) (fun l hl => ?_)
  have hlm := ground.mem_of_countOf_pos l (List.range R.links) hl
  refine congrArg (fun b : Bool => if b then
      (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l)
    else 0) ?_
  cases hp : (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l))) with
  | false => exact rfl
  | true =>
    have hbf : (g (getAt 0 R.head l) == g (getAt 0 R.tail l)) = false := by
      cases hb : (g (getAt 0 R.head l) == g (getAt 0 R.tail l)) with
      | true =>
        rw [hb] at hp
        exact Bool.noConfusion hp
      | false => rfl
    have hgh := hcross l hlm hbf
    have hgt : g (getAt 0 R.tail l) < c := hglt _ (htlt l hlm)
    have hxc : x < c := Nat.lt_trans (Nat.lt_succ_self x) hx
    have hx1 : (x + 1) % c = x + 1 := ground.modOfLt (x + 1) c hx
    show (true && (g (getAt 0 R.head l) == x + 1))
      = (true && (g (getAt 0 R.tail l) == x))
    show (g (getAt 0 R.head l) == x + 1)
      = (g (getAt 0 R.tail l) == x)
    cases hb2 : (g (getAt 0 R.tail l) == x) with
    | true =>
      refine ground.eqBeqOf ?_
      rw [hgh, ground.beqEqOf hb2, hx1]
    | false =>
      cases hb3 : (g (getAt 0 R.head l) == x + 1) with
      | true =>
        have hsucc : (g (getAt 0 R.tail l) + 1) % c = (x + 1) % c := by
          rw [← hgh, ground.beqEqOf hb3, hx1]
        rw [ground.eqBeqOf (succModInj c (g (getAt 0 R.tail l)) x
          hgt hxc hsucc)] at hb2
        exact Bool.noConfusion hb2
      | false => exact rfl

/-- The conservation along the grades: the vertex laws summed over
one slab, the interior pairs withdrawing at the dual's join, and
the cuts read one class by the induction along the grades. -/
theorem fluxConserve (n : Nat) (R : lattice.Region)
    (g : Nat → Nat) (c : Nat) (a : List Shape)
    (hwell : lattice.wellRead R)
    (hcut : transCutRead R g c)
    (hocc : carrier.occupied (fusion.dataA n) R a = true)
    (hwidth : (a.all (fun s => s.length == n)) = true) :
    ∀ x : Nat, x < c → fluxAt n R g x a % n = fluxAt n R g 0 a % n
  | 0, _ => rfl
  | x + 1, hx =>
    (fluxStep n R g c a hwell hcut hocc hwidth x hx).trans
      (fluxConserve n R g c a hwell hcut hocc hwidth x
        (Nat.lt_trans (Nat.lt_succ_self x) hx))

/-- The charge at the torus: the per-direction flux family at the
base cut, each direction's site grading its own positional
digit. -/
def chargeT (n d L : Nat) (a : List Shape) : List Nat :=
  (List.range d).map (fun e =>
    fluxAt n (fiberdec.torusRegion d L)
      (fun s => fiberdec.digitAt L e s) 0 a % n)

/-- The relabeled configuration's flux through a cut is its own
through the moved cut: the translation permutes the link index, one
term per link along the permutation with the directions kept, the
image link's endpoint grades reading the stated grade map, and the
grade map injective below the count carries the cut's grade back to
its source. -/
private theorem fluxAt_move (n : Nat) (R : lattice.Region)
    (t s : Nat → Nat) (g : Nat → Nat) (mv : Nat → Nat) (c : Nat)
    (a : List Shape)
    (hperm : fiberdec.permRead R t s)
    (hmv : cutMoveRead R t g mv)
    (hinj : ∀ u v, u < c → v < c → mv u = mv v → u = v)
    (hg : ∀ v', v' < R.verts → g v' < c)
    (hwell : lattice.wellRead R)
    (x x0 : Nat) (hx0 : mv x0 = x) (hx0c : x0 < c) :
    fluxAt n R g x
        (fiberdec.permConf (fusion.dataA n) s R.links a)
      = fluxAt n R g x0 a := by
  rw [fluxAt_read n R g x (fiberdec.permConf (fusion.dataA n) s
      R.links a),
    fluxAt_read n R g x0 a]
  have hts : ∀ l : Nat, l < R.links →
      s (t l) = l ∧ t (s l) = l ∧ t l < R.links ∧ s l < R.links :=
    fun l hl => fiberdec.permRead_at R t s hperm l hl
  refine (ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc
    (fun l =>
      if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
          && (g (getAt 0 R.tail l) == x)
        then (fusion.dataA n).cls (getAt (fusion.dataA n).unit
          (fiberdec.permConf (fusion.dataA n) s R.links a) l)
        else 0)
    (ground.distinctList_range R.links)
    (fun y hy => (hts y (ground.ltOfMem hy)).1)
    (fun y hy => (hts y (ground.ltOfMem hy)).2.1)
    (fun y hy => ground.countOf_range_pos
      ((hts y (ground.ltOfMem hy)).2.2.1))
    (fun y hy => ground.countOf_range_pos
      ((hts y (ground.ltOfMem hy)).2.2.2))).trans ?_
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range R.links) (fun m hm => ?_)
  have hmr : m < R.links := ground.ltOfMem hm
  have hend := lattice.endLt R hwell m hmr
  have hs2 := ground.andSplitB
    (cutMove_at R t g mv hmv m hmr)
  have hT : g (getAt 0 R.tail (t m)) = mv (g (getAt 0 R.tail m)) :=
    ground.beqEqOf hs2.1
  have hH : g (getAt 0 R.head (t m)) = mv (g (getAt 0 R.head m)) :=
    ground.beqEqOf hs2.2
  have hAc : g (getAt 0 R.head m) < c := hg _ hend.2
  have hBc : g (getAt 0 R.tail m) < c := hg _ hend.1
  have hval : getAt (fusion.dataA n).unit
        (fiberdec.permConf (fusion.dataA n) s R.links a) (t m)
      = getAt (fusion.dataA n).unit a m := by
    show getAt (fusion.dataA n).unit
        ((List.range R.links).map
          (fun l => getAt (fusion.dataA n).unit a (s l))) (t m)
      = getAt (fusion.dataA n).unit a m
    rw [ground.getAt_map_range (fusion.dataA n).unit
        (fun l => getAt (fusion.dataA n).unit a (s l)) R.links (t m),
      if_pos (hts m hmr).2.2.1]
    show getAt (fusion.dataA n).unit a (s (t m))
      = getAt (fusion.dataA n).unit a m
    rw [(hts m hmr).1]
  have e1 : (mv (g (getAt 0 R.head m)) == mv (g (getAt 0 R.tail m)))
      = (g (getAt 0 R.head m) == g (getAt 0 R.tail m)) := by
    by_cases hab : g (getAt 0 R.head m) = g (getAt 0 R.tail m)
    · rw [hab]
      exact (ground.eqBeqOf rfl).trans (ground.eqBeqOf rfl).symm
    · rw [ground.neBeqOf (fun hc => hab (hinj _ _ hAc hBc hc)),
        ground.neBeqOf hab]
  have e2 : (mv (g (getAt 0 R.tail m)) == x)
      = (g (getAt 0 R.tail m) == x0) := by
    by_cases hbx : g (getAt 0 R.tail m) = x0
    · rw [hbx, hx0]
      exact (ground.eqBeqOf rfl).trans (ground.eqBeqOf rfl).symm
    · rw [ground.neBeqOf (fun hc => hbx
          (hinj _ _ hBc hx0c (hc.trans hx0.symm))),
        ground.neBeqOf hbx]
  show (if (!(g (getAt 0 R.head (t m)) == g (getAt 0 R.tail (t m))))
        && (g (getAt 0 R.tail (t m)) == x)
      then (fusion.dataA n).cls (getAt (fusion.dataA n).unit
        (fiberdec.permConf (fusion.dataA n) s R.links a) (t m))
      else 0)
    = (if (!(g (getAt 0 R.head m) == g (getAt 0 R.tail m)))
        && (g (getAt 0 R.tail m) == x0)
      then (fusion.dataA n).cls (getAt (fusion.dataA n).unit a m)
      else 0)
  rw [hT, hH, e1, e2, hval]

/-- A translation permutes the index at one charge: the relabeled
configuration's charge family is the source's — per direction the
endpoint grades read along the translation at the stated grade map,
the map injective below the side with the base cut's pre-image
located, and the conservation reads the base cut's class back
(`lem:chargedcell`(i)'s translation clause). -/
theorem chargeT_perm (n d L : Nat) (a : List Shape)
    (t s : Nat → Nat) (mv : Nat → Nat → Nat) (pre : Nat → Nat)
    (hperm : fiberdec.permRead (fiberdec.torusRegion d L) t s)
    (hcuts : ∀ e, e < d → transCutRead (fiberdec.torusRegion d L)
      (fun v => fiberdec.digitAt L e v) L)
    (hmove : ∀ e, e < d → cutMoveRead (fiberdec.torusRegion d L) t
      (fun v => fiberdec.digitAt L e v) (mv e))
    (hinj : ∀ e, e < d → ∀ u, u < L → ∀ v, v < L →
      mv e u = mv e v → u = v)
    (hpre : ∀ e, e < d → pre e < L ∧ mv e (pre e) = 0)
    (hwell : lattice.wellRead (fiberdec.torusRegion d L))
    (hocc : carrier.occupied (fusion.dataA n)
      (fiberdec.torusRegion d L) a = true)
    (hwidth : (a.all (fun sh => sh.length == n)) = true) :
    chargeT n d L (fiberdec.permConf (fusion.dataA n) s
        (fiberdec.torusRegion d L).links a)
      = chargeT n d L a := by
  refine ground.map_congr_members _ _ (List.range d) (fun e he => ?_)
  have hed : e < d := ground.ltOfMem he
  have hgl : ∀ v : Nat, v < (fiberdec.torusRegion d L).verts →
      fiberdec.digitAt L e v < L :=
    fun v hv => cutGrade (fiberdec.torusRegion d L)
      (fun w => fiberdec.digitAt L e w) L (hcuts e hed) v hv
  show fluxAt n (fiberdec.torusRegion d L)
      (fun v => fiberdec.digitAt L e v) 0
      (fiberdec.permConf (fusion.dataA n) s
        (fiberdec.torusRegion d L).links a) % n
    = fluxAt n (fiberdec.torusRegion d L)
      (fun v => fiberdec.digitAt L e v) 0 a % n
  rw [fluxAt_move n (fiberdec.torusRegion d L) t s
    (fun v => fiberdec.digitAt L e v) (mv e) L a hperm (hmove e hed)
    (fun u v hu hv => hinj e hed u hu v hv) hgl hwell 0 (pre e)
    (hpre e hed).2 (hpre e hed).1]
  exact fluxConserve n (fiberdec.torusRegion d L)
    (fun v => fiberdec.digitAt L e v) L a hwell (hcuts e hed) hocc
    hwidth (pre e) (hpre e hed).1

/-! `lem:chargedcell`(i)'s `θ`-row read: `M` fuses one link by `θ`
fixing every link's `d_f`-ality, the row additivity at `θ`'s unit
class. -/

/-- A row's every member reads one stated class code: the class
law's read at the factors' joined code. -/
theorem clsRow_of (n : Nat) (a b : Shape) (k : Nat)
    (hk : (fusion.dataA n).clsAdd ((fusion.dataA n).cls a)
      ((fusion.dataA n).cls b) = k) :
    (((fusion.dataA n).row a b).all (fun c =>
      Nat.beq ((fusion.dataA n).cls c) k)) = true := by
  have h : (((fusion.dataA n).row a b).all (fun c =>
      Nat.beq ((fusion.dataA n).cls c)
        ((fusion.dataA n).clsAdd ((fusion.dataA n).cls a)
          ((fusion.dataA n).cls b)))) = true := clsLaw_all n a b
  rw [hk] at h
  exact h

/-- Every member of a `θ`-row reads the source label's class: the
row's additivity at `θ`'s own unit class. -/
theorem clsRow_theta (n : Nat) (y : Shape) :
    (((fusion.dataA n).row (adjchar.theta n) y).all (fun c =>
      Nat.beq ((fusion.dataA n).cls c)
        ((fusion.dataA n).cls y))) = true :=
  clsRow_of n (adjchar.theta n) y ((fusion.dataA n).cls y) (by
    show (degree (adjchar.theta n) % n + degree y % n) % n
      = degree y % n
    rw [ality_theta n, Nat.zero_add]
    exact ground.modMod (degree y) n)

/-! `lem:chargedcell`(ii)'s winding floor at the torus: every shape
reads its class's endpoint floor, the merge of two classes is
subadditive at those floors, and an occupied configuration's
content clears `L` times the per-direction floor sum — each
direction's cuts netting the base cut's class by the conservation,
each cut's crossing family descending to its net class's own
floor, and the directions' crossing families disjoint per link. -/



/-- The reduction keeps the cleared read, `con:labels`' descent at
the withdrawn full columns. -/
private theorem dfQ_reduce (s : Shape) :
    c2hat.dfQ (labels.reduce s) = c2hat.dfQ s :=
  Eq.symm (labels.c2Class_all s)

/-- The reduced shape reads the unit occupancy at its full-column
key. -/
private theorem reduce_red (d : Nat) (s : Shape)
    (h : s.length = d + 1) :
    ground.getAt 0 (labels.reduce s) d = 0 := by
  match ground.snoc_split d s h with
  | ⟨s', a, hs, hl⟩ =>
    rw [hs, labels.reduce_snoc s' a, ← hl]
    exact ground.getAt_append_add 0 s' [0] 0

/-- A class code sits below the residue. -/
private theorem clsLt (n : Nat) (hn : 0 < n) (s : Shape) :
    (fusion.dataA n).cls s < n :=
  (ground.natDivRead (degree s) n hn).2

/-- The crossed pair's product identity: the two mixed products
join the shared member's own against the doubled cross term. -/
private theorem crossId (m u v : Nat) :
    u * (m + v) + v * (m + u) = m * (u + v) + 2 * (u * v) := by
  rw [Nat.left_distrib u m v, Nat.left_distrib v m u,
    Nat.mul_comm v u,
    Nat.add_add_add_comm (u * m) (u * v) (v * m) (u * v),
    ← ground.mulAddR u v m, Nat.mul_comm (u + v) m,
    Nat.two_mul (u * v)]

/-- The crossed identity at a named total. -/
private theorem crossTotal (m gm u v : Nat) (hgm : gm = u + v) :
    (m + v) * u + (m + u) * v = m * gm + 2 * (u * v) := by
  rw [hgm, Nat.mul_comm (m + v) u, Nat.mul_comm (m + u) v]
  exact crossId m u v

/-- Two distinct class codes' endpoint floors tie exactly at the
dual pair: at codes joining to the residue the two floors read one
value (`lem:chargedcell`(ii)). -/
theorem tieDual (n j j' : Nat) (h : j + j' = n) :
    (fusion.dataA n).clsFloorN j = (fusion.dataA n).clsFloorN j' := by
  have e1 : n - j = j' := by
    rw [← h]
    exact ground.addSubSelfL j j'
  have e2 : n - j' = j := by
    rw [← h]
    exact ground.addSubSelfR j j'
  show j * (n - j) * (n + 1) = j' * (n - j') * (n + 1)
  rw [e1, e2, Nat.mul_comm j j']

/-- Below the dual pair the two floors part by the crossed gaps:
at a pair whose sum falls short of the residue by `b` and whose
own gap is `a`, the lower code's floor joins `a b (n + 1)` to the
higher code's (`lem:chargedcell`(ii), the sum's trichotomy against
`d_f`). -/
theorem tieBelow (n j j' a b : Nat) (ha : j' + a = j)
    (hb : j + j' + b = n) :
    (fusion.dataA n).clsFloorN j' + a * b * (n + 1)
      = (fusion.dataA n).clsFloorN j := by
  have h1 : j' + (j + b) = n := by
    rw [← Nat.add_assoc j' j b, Nat.add_comm j' j]
    exact hb
  have h2 : j + (j' + b) = n := by
    rw [← Nat.add_assoc j j' b]
    exact hb
  have e1 : n - j' = j + b := by
    rw [← h1]
    exact ground.addSubSelfL j' (j + b)
  have e2 : n - j = j' + b := by
    rw [← h2]
    exact ground.addSubSelfL j (j' + b)
  show j' * (n - j') * (n + 1) + a * b * (n + 1)
    = j * (n - j) * (n + 1)
  rw [e1, e2, ← ground.mulAddR (j' * (j + b)) (a * b) (n + 1), ← ha,
    ground.crossMul j' a b]

/-- Beyond the dual pair the parting reverses: at a pair whose sum
clears the residue by `b`, with the higher code's gap to the
residue `m` and the pair's own gap `a`, the higher code's floor
joins `a b (n + 1)` to the lower code's (`lem:chargedcell`(ii),
the sum's trichotomy against `d_f`). -/
theorem tieBeyond (n j j' a b m : Nat) (ha : j' + a = j)
    (hm : j + m = n) (hb : j + j' = n + b) :
    (fusion.dataA n).clsFloorN j + a * b * (n + 1)
      = (fusion.dataA n).clsFloorN j' := by
  have e1 : n - j = m := by
    rw [← hm]
    exact ground.addSubSelfL j m
  have hj' : j' = m + b := by
    refine ground.addCancelL j ?_
    rw [← Nat.add_assoc j m b, hm]
    exact hb
  have h2 : j' + (m + a) = n := by
    rw [← Nat.add_assoc j' m a, Nat.add_right_comm j' m a, ha]
    exact hm
  have e2 : n - j' = m + a := by
    rw [← h2]
    exact ground.addSubSelfL j' (m + a)
  show j * (n - j) * (n + 1) + a * b * (n + 1)
    = j' * (n - j') * (n + 1)
  rw [e1, e2, ← ground.mulAddR (j * m) (a * b) (n + 1), ← ha, hj',
    Nat.mul_comm (m + b) (m + a), ← ground.crossMul m a b,
    Nat.mul_comm (m + b + a) m, Nat.add_right_comm m b a]

/-- The tie is exact: two distinct class codes within the residue
at one floor value join to the residue, the crossed gap's occupied
product refusing both strict sides (`lem:chargedcell`(ii)). -/
theorem tieOnly (n j j' a m : Nat) (ha : j' + (a + 1) = j)
    (hm : j + m = n)
    (heq : (fusion.dataA n).clsFloorN j
      = (fusion.dataA n).clsFloorN j') :
    j + j' = n := by
  cases Nat.lt_or_ge (j + j') n with
  | inl hlt =>
    exfalso
    match Nat.le.dest hlt with
    | ⟨b, hb⟩ =>
      have hb' : j + j' + (1 + b) = n := by
        rw [← Nat.add_assoc (j + j') 1 b]
        exact hb
      have ht := tieBelow n j j' (a + 1) (1 + b) ha hb'
      rw [heq] at ht
      have h0 : (a + 1) * (1 + b) * (n + 1) = 0 :=
        (ground.addCancelL ((fusion.dataA n).clsFloorN j')
          (ht.trans (Nat.add_zero _).symm)).symm.symm
      have hp : 0 < (a + 1) * (1 + b) * (n + 1) :=
        Nat.mul_pos (Nat.mul_pos (Nat.succ_pos a)
          (Nat.add_pos_left (Nat.succ_pos 0) b)) (Nat.succ_pos n)
      rw [h0] at hp
      exact absurd hp (Nat.lt_irrefl 0)
  | inr hge =>
    cases Nat.eq_or_lt_of_le hge with
    | inl heqn => exact heqn.symm
    | inr hlt =>
      exfalso
      match Nat.le.dest hlt with
      | ⟨b, hb⟩ =>
        have hb' : j + j' = n + (1 + b) := by
          rw [← Nat.add_assoc n 1 b]
          exact hb.symm
        have ht := tieBeyond n j j' (a + 1) (1 + b) m ha hm hb'
        rw [← heq] at ht
        have h0 : (a + 1) * (1 + b) * (n + 1) = 0 :=
          (ground.addCancelL ((fusion.dataA n).clsFloorN j)
            (ht.trans (Nat.add_zero _).symm)).symm.symm
        have hp : 0 < (a + 1) * (1 + b) * (n + 1) :=
          Nat.mul_pos (Nat.mul_pos (Nat.succ_pos a)
            (Nat.add_pos_left (Nat.succ_pos 0) b)) (Nat.succ_pos n)
        rw [h0] at hp
        exact absurd hp (Nat.lt_irrefl 0)

/-- The merge's cost identity below the residue: two classes'
floors join at their sum's floor with the crossed product's doubled
count (`lem:chargedcell`(ii)'s merge clause). -/
theorem mergeBelow (n a1 a2 m : Nat) (hm : a1 + a2 + m = n) :
    (fusion.dataA n).clsFloorN a1 + (fusion.dataA n).clsFloorN a2
      = (fusion.dataA n).clsFloorN (a1 + a2)
        + 2 * (a1 * a2) * (n + 1) := by
  have h1 : a1 + (m + a2) = n := by
    rw [Nat.add_comm m a2, ← Nat.add_assoc a1 a2 m]
    exact hm
  have h2 : a2 + (m + a1) = n := by
    rw [Nat.add_comm m a1, ← Nat.add_assoc a2 a1 m,
      Nat.add_comm a2 a1]
    exact hm
  have hs : a1 + a2 + m = n := hm
  have e1 : n - a1 = m + a2 := by
    rw [← h1]
    exact ground.addSubSelfL a1 (m + a2)
  have e2 : n - a2 = m + a1 := by
    rw [← h2]
    exact ground.addSubSelfL a2 (m + a1)
  have es : n - (a1 + a2) = m := by
    rw [← hs]
    exact ground.addSubSelfL (a1 + a2) m
  show a1 * (n - a1) * (n + 1) + a2 * (n - a2) * (n + 1)
    = (a1 + a2) * (n - (a1 + a2)) * (n + 1)
      + 2 * (a1 * a2) * (n + 1)
  rw [e1, e2, es, ← ground.mulAddR (a1 * (m + a2)) (a2 * (m + a1))
      (n + 1),
    ← ground.mulAddR ((a1 + a2) * m) (2 * (a1 * a2)) (n + 1),
    crossId m a1 a2, Nat.mul_comm (a1 + a2) m]

/-- The merge's drop at the residue: the pair withdraws whole, the
crossed product's doubled count the two floors' own join
(`lem:chargedcell`(ii)'s merge clause). -/
theorem mergeDrop (n a1 a2 : Nat) (h : a1 + a2 = n) :
    (fusion.dataA n).clsFloorN a1 + (fusion.dataA n).clsFloorN a2
      = 2 * (a1 * a2) * (n + 1) := by
  have e1 : n - a1 = a2 := by
    rw [← h]
    exact ground.addSubSelfL a1 a2
  have e2 : n - a2 = a1 := by
    rw [← h]
    exact ground.addSubSelfR a1 a2
  show a1 * (n - a1) * (n + 1) + a2 * (n - a2) * (n + 1)
    = 2 * (a1 * a2) * (n + 1)
  rw [e1, e2, ← ground.mulAddR (a1 * a2) (a2 * a1) (n + 1),
    Nat.mul_comm a2 a1, ← Nat.two_mul (a1 * a2)]

/-- The merge's cost identity beyond the residue: the two floors
join at the gap's floor with the complement gaps' crossed product
doubled (`lem:chargedcell`(ii)'s merge clause). -/
theorem mergeBeyond (n a1 a2 g g1 g2 : Nat)
    (hg : n + g = a1 + a2) (h1 : a1 + g1 = n) (h2 : a2 + g2 = n) :
    (fusion.dataA n).clsFloorN a1 + (fusion.dataA n).clsFloorN a2
      = (fusion.dataA n).clsFloorN g + 2 * (g1 * g2) * (n + 1) := by
  have hgm : g + (g1 + g2) = n := by
    refine ground.addCancelL n ?_
    rw [← Nat.add_assoc n g (g1 + g2), hg,
      Nat.add_add_add_comm a1 a2 g1 g2, h1, h2]
  have e1 : n - a1 = g1 := by
    rw [← h1]
    exact ground.addSubSelfL a1 g1
  have e2 : n - a2 = g2 := by
    rw [← h2]
    exact ground.addSubSelfL a2 g2
  have eg : n - g = g1 + g2 := by
    rw [← hgm]
    exact ground.addSubSelfL g (g1 + g2)
  have hc1 : a1 = g + g2 := by
    refine ground.addCancelR g1 ?_
    rw [h1, ← hgm, Nat.add_assoc g g2 g1, Nat.add_comm g2 g1]
  have hc2 : a2 = g + g1 := by
    refine ground.addCancelR g2 ?_
    rw [h2, ← hgm, Nat.add_assoc g g1 g2]
  show a1 * (n - a1) * (n + 1) + a2 * (n - a2) * (n + 1)
    = g * (n - g) * (n + 1) + 2 * (g1 * g2) * (n + 1)
  rw [e1, e2, eg,
    ← ground.mulAddR (a1 * g1) (a2 * g2) (n + 1),
    ← ground.mulAddR (g * (g1 + g2)) (2 * (g1 * g2)) (n + 1),
    hc1, hc2, crossTotal g (g1 + g2) g1 g2 rfl]

/-- The unit-class crossing's floor clears the merge read: the
square's growth prices the residue's successor
(`lem:chargedcell`(iii)'s warrant clause). -/
theorem unitCrossClears (n : Nat) (h : 2 ≤ n) :
    2 * (n + 1) ≤ 2 * (n * n) := by
  refine Nat.mul_le_mul_left 2 ?_
  refine Nat.le_trans ?_ (Nat.mul_le_mul_right n h)
  rw [Nat.two_mul n]
  exact Nat.add_le_add_left (Nat.le_trans (by decide +kernel) h) n

/-- The netted family's floor clears the merge read: the occupied
factor prices the pair's two least members
(`lem:chargedcell`(iii)'s warrant clause). -/
theorem netUnitClears (n : Nat) (h : 2 ≤ n) :
    2 * (n + 1) ≤ 2 * ((n - 1) * (n + 1)) := by
  refine Nat.mul_le_mul_left 2 ?_
  match Nat.le.dest h with
  | ⟨b, hb⟩ =>
    have h1 : 1 + (n - 1) = n :=
      ground.natAddSubCancel (Nat.le_trans (by decide +kernel) h)
    have hg : n - 1 = 1 + b := by
      refine ground.addCancelL 1 ?_
      rw [h1, ← hb, ← Nat.add_assoc 1 1 b]
    rw [hg, ground.mulAddR 1 b (n + 1), Nat.one_mul]
    exact Nat.le_add_right (n + 1) (b * (n + 1))

/-- The merge's strict gap at two nonunit classes: the merged
class's floor clears two residue counts below the two classes'
own, the three cost identities read at their occupied crossed
products (`lem:chargedcell`(ii)'s merge clause). -/
theorem mergeGap (n c1 c2 : Nat) (h1o : 0 < c1) (h1 : c1 < n)
    (h2o : 0 < c2) (h2 : c2 < n) :
    (fusion.dataA n).clsFloorN ((c1 + c2) % n) + 2 * (n + 1)
      ≤ (fusion.dataA n).clsFloorN c1
        + (fusion.dataA n).clsFloorN c2 := by
  have htwo : ∀ x y : Nat, 0 < x → 0 < y →
      2 * (n + 1) ≤ 2 * (x * y) * (n + 1) := by
    intro x y hx hy
    refine Nat.mul_le_mul_right (n + 1) ?_
    have h := Nat.mul_le_mul_left 2 (Nat.mul_pos hx hy)
    rw [Nat.mul_one] at h
    exact h
  cases Nat.lt_or_ge (c1 + c2) n with
  | inl hlt =>
    match Nat.le.dest hlt with
    | ⟨m, hm⟩ =>
      have hm' : c1 + c2 + (1 + m) = n := by
        rw [← Nat.add_assoc (c1 + c2) 1 m]
        exact hm
      rw [ground.modOfLt (c1 + c2) n hlt,
        mergeBelow n c1 c2 (1 + m) hm']
      exact Nat.add_le_add_left (htwo c1 c2 h1o h2o) _
  | inr hge =>
    cases Nat.eq_or_lt_of_le hge with
    | inl heq =>
      have h0 : (c1 + c2) % n = 0 := by
        have hmm := ground.modMulSelf 1 n
        rw [Nat.one_mul] at hmm
        rw [← heq]
        exact hmm
      have hz : (fusion.dataA n).clsFloorN 0 = 0 := by
        show 0 * (n - 0) * (n + 1) = 0
        rw [Nat.zero_mul, Nat.zero_mul]
      rw [h0, hz, Nat.zero_add, mergeDrop n c1 c2 heq.symm]
      exact htwo c1 c2 h1o h2o
    | inr hlt =>
      have hg1 : c1 + (n - c1) = n :=
        ground.natAddSubCancel (Nat.le_of_lt h1)
      have hg2 : c2 + (n - c2) = n :=
        ground.natAddSubCancel (Nat.le_of_lt h2)
      have hp1 : 0 < n - c1 := by
        cases hx : n - c1 with
        | zero =>
          exfalso
          rw [hx, Nat.add_zero] at hg1
          rw [hg1] at h1
          exact absurd h1 (Nat.lt_irrefl n)
        | succ k => exact Nat.succ_pos k
      have hp2 : 0 < n - c2 := by
        cases hx : n - c2 with
        | zero =>
          exfalso
          rw [hx, Nat.add_zero] at hg2
          rw [hg2] at h2
          exact absurd h2 (Nat.lt_irrefl n)
        | succ k => exact Nat.succ_pos k
      match Nat.le.dest (Nat.le_of_lt hlt) with
      | ⟨m, hnm⟩ =>
        have hmn : m < n := by
          have hsum : n + m < n + n := by
            rw [hnm]
            exact Nat.add_lt_add h1 h2
          exact Nat.lt_of_add_lt_add_left hsum
        have hmod : (c1 + c2) % n = m := by
          rw [← hnm, show n + m = m + 1 * n from by
            rw [Nat.one_mul, Nat.add_comm], ground.modAddMul m 1 n]
          exact ground.modOfLt m n hmn
        rw [hmod,
          mergeBeyond n c1 c2 m (n - c1) (n - c2) hnm hg1 hg2]
        exact Nat.add_le_add_left (htwo (n - c1) (n - c2) hp1 hp2) _

/-- The endpoint floors are subadditive at the class merge: the
merged class's floor sits at or below the two classes' own, the
occupied case the merge's strict gap withdrawn and a vacant class
reading its summand off the join (`lem:chargedcell`(ii)'s merge
clause). -/
private theorem floorSub (n : Nat) (c1 c2 : Nat)
    (h1 : c1 < n) (h2 : c2 < n) :
    (fusion.dataA n).clsFloorN ((c1 + c2) % n)
      ≤ (fusion.dataA n).clsFloorN c1
        + (fusion.dataA n).clsFloorN c2 := by
  cases c1 with
  | zero =>
    rw [Nat.zero_add, ground.modOfLt c2 n h2]
    show (fusion.dataA n).clsFloorN c2
      ≤ 0 * (n - 0) * (n + 1) + (fusion.dataA n).clsFloorN c2
    rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_add]
    exact Nat.le_refl _
  | succ a =>
    cases c2 with
    | zero =>
      rw [Nat.add_zero, ground.modOfLt (a + 1) n h1]
      show (fusion.dataA n).clsFloorN (a + 1)
        ≤ (fusion.dataA n).clsFloorN (a + 1) + 0 * (n - 0) * (n + 1)
      rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero]
      exact Nat.le_refl _
    | succ b =>
      exact Nat.le_trans
        (Nat.le_add_right ((fusion.dataA n).clsFloorN
          ((a + 1 + (b + 1)) % n)) (2 * (n + 1)))
        (mergeGap n (a + 1) (b + 1) (Nat.succ_pos a) h1
          (Nat.succ_pos b) h2)

/-- One label's class floor sits at or below its own cleared
Casimir: at the unit class the floor is the count's unit, and at a
nonunit class the reduced shape reads `lem:casfloor`'s per-class
descent, the reduction keeping both the class and the read. -/
private theorem famMember (n : Nat) (hn : 0 < n) (s : Shape)
    (hs : (s.length == n) = true) :
    (fusion.dataA n).clsFloorN ((fusion.dataA n).cls s)
      ≤ c2hat.dfQ s := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ n' =>
    have h := casfloor.classFloor n' ((fusion.dataA (n' + 1)).cls s)
      (labels.reduce s)
      ((labels.length_reduce s).trans (ground.beqEqOf hs))
      (reduce_red n' s (ground.beqEqOf hs))
      (ality_reduce (n' + 1) s (ground.beqEqOf hs))
    rw [dfQ_reduce s] at h
    exact h

/-- A label family's net class reads its floor at or below the
family's own content: the merge subadditivity walked one member at
a time, each member's class floor priced at its cleared
Casimir. -/
private theorem famSub (n : Nat) (hn : 0 < n) : ∀ ls : List Shape,
    (ls.all (fun s => s.length == n)) = true →
    (fusion.dataA n).clsFloorN
        (famFold Nat.add 0 (fun s => (fusion.dataA n).cls s) ls % n)
      ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) ls
  | [], _ => by
    show (fusion.dataA n).clsFloorN (0 % n) ≤ 0
    rw [ground.modZeroLeft n]
    show (0 : Nat) * (n - 0) * (n + 1) ≤ 0
    rw [Nat.zero_mul, Nat.zero_mul]
    exact Nat.le_refl 0
  | s :: t, hall => by
    have hsplit := ground.andSplitB
      (show ((s.length == n)
        && t.all (fun u => u.length == n)) = true from hall)
    have hstep : ((fusion.dataA n).cls s
        + famFold Nat.add 0 (fun u => (fusion.dataA n).cls u) t) % n
      = ((fusion.dataA n).cls s
        + famFold Nat.add 0 (fun u => (fusion.dataA n).cls u) t % n)
        % n := by
      have h := ground.modAdd ((fusion.dataA n).cls s)
        (famFold Nat.add 0 (fun u => (fusion.dataA n).cls u) t) n
      rw [clsMod n s] at h
      exact h.symm
    show (fusion.dataA n).clsFloorN
        (((fusion.dataA n).cls s
          + famFold Nat.add 0 (fun u => (fusion.dataA n).cls u) t) % n)
      ≤ c2hat.dfQ s + famFold Nat.add 0 (fun u => c2hat.dfQ u) t
    rw [hstep]
    refine Nat.le_trans (floorSub n ((fusion.dataA n).cls s) _
      (clsLt n hn s) ((ground.natDivRead _ n hn).2)) ?_
    exact Nat.add_le_add (famMember n hn s hsplit.1)
      (famSub n hn t hsplit.2)







/-- The content at the label calculus as a family fold: the unit
keys read the sum's unit, every further key its label's cleared
Casimir. -/
private theorem contentN_fam (n : Nat) (a : List Shape) :
    carrier.contentN (fusion.dataA n) a
      = famFold Nat.add 0 (fun s =>
          if (fusion.dataA n).eqL s (fusion.dataA n).unit then 0
          else c2hat.dfQ s) a := by
  have hstep : ∀ (acc : Nat) (l : Shape),
      (if (fusion.dataA n).eqL l (fusion.dataA n).unit then acc
        else acc + c2hat.dfQ l)
      = acc + (if (fusion.dataA n).eqL l (fusion.dataA n).unit then 0
        else c2hat.dfQ l) := by
    intro acc l
    cases (fusion.dataA n).eqL l (fusion.dataA n).unit with
    | true => exact (Nat.add_zero acc).symm
    | false => exact rfl
  show a.foldl (fun acc l =>
      if (fusion.dataA n).eqL l (fusion.dataA n).unit then acc
      else acc + c2hat.dfQ l) 0
    = famFold Nat.add 0 (fun s =>
        if (fusion.dataA n).eqL s (fusion.dataA n).unit then 0
        else c2hat.dfQ s) a
  rw [ground.foldl_congr _ (fun acc l => acc
      + (if (fusion.dataA n).eqL l (fusion.dataA n).unit then 0
        else c2hat.dfQ l)) hstep a 0,
    ground.foldlSum (fun s =>
      if (fusion.dataA n).eqL s (fusion.dataA n).unit then 0
      else c2hat.dfQ s) a 0, Nat.zero_add]

/-- The content at the key range: the configuration's fold read
key by key at the region's own link keys. -/
private theorem contentN_famFold (n : Nat) (a : List Shape) :
    carrier.contentN (fusion.dataA n) a
      = famFold Nat.add 0 (fun l =>
          if (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
              (fusion.dataA n).unit
            then 0
            else c2hat.dfQ (getAt (fusion.dataA n).unit a l))
        (List.range a.length) := by
  rw [contentN_fam n a,
    ← ground.famFold_getAt Nat.add 0 (fun s =>
        if (fusion.dataA n).eqL s (fusion.dataA n).unit then 0
        else c2hat.dfQ s) (fusion.dataA n).unit a a.length rfl]

/-- A label reading the unit reads the vacant Casimir: the
reduction is the unit's own and the vacant shape's read is
vacant. -/
private theorem dfQ_unitEq (n : Nat) (s : Shape)
    (h : (fusion.dataA n).eqL s (fusion.dataA n).unit = true) :
    c2hat.dfQ s = 0 := by
  have hre : labels.reduce s = labels.reduce (labels.unitL n) :=
    ground.listBeqEq
      (show (labels.reduce s == labels.reduce (labels.unitL n)) = true
        from h)
  rw [← dfQ_reduce s, hre, dfQ_reduce (labels.unitL n)]
  exact c2hat.dfQ_replicate_zero n

/-- A guarded keyed image's fold is the guarded fold at the source
keys, the refused keys reading the sum's unit. -/
private theorem famFold_guardSel {β : Type} (q : Nat → Bool)
    (v : Nat → β) (F : β → Nat) (K : List Nat) :
    famFold Nat.add 0 F
        (K.filterMap (fun l => if q l then some (v l) else none))
      = famFold Nat.add 0 (fun l => if q l then F (v l) else 0) K := by
  rw [ground.famFold_filterMap (fun l => if q l then some (v l) else none) F K]
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun l => ?_) K
  cases hq : q l with
  | true => exact rfl
  | false => exact rfl

/-- A guarded family of link labels reads the stated width at every
member. -/
private theorem all_guardSel (n : Nat) (q : Nat → Bool) (a : List Shape)
    (hwidth : (a.all (fun s => s.length == n)) = true) (K : List Nat) :
    ((K.filterMap (fun l =>
      if q l then some (getAt (fusion.dataA n).unit a l) else none)).all
      (fun s => s.length == n)) = true := by
  refine ground.all_filterMap_mem _ _ K (fun l _ y hy => ?_)
  cases hq : q l with
  | true =>
    rw [hq] at hy
    rw [← Option.some.inj
      (show some (getAt (fusion.dataA n).unit a l) = some y from hy)]
    exact label_width n a hwidth l
  | false =>
    rw [hq] at hy
    exact nomatch hy

/-- The cut's crossing family descends to its own class's floor:
the flux is the crossing labels' class fold and the guarded content
their cleared Casimirs, so the merge subadditivity prices the cut's
class at the crossing links' own content. -/
private theorem fluxFloor (n : Nat) (hn : 0 < n) (R : lattice.Region)
    (g : Nat → Nat) (a : List Shape)
    (hwidth : (a.all (fun s => s.length == n)) = true) (x : Nat) :
    (fusion.dataA n).clsFloorN (fluxAt n R g x a % n)
      ≤ famFold Nat.add 0 (fun l =>
          if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
              && (g (getAt 0 R.tail l) == x)
            then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
            else 0) (List.range R.links) := by
  rw [fluxAt_read n R g x a]
  have h := famSub n hn
    ((List.range R.links).filterMap (fun l =>
      if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
          && (g (getAt 0 R.tail l) == x)
        then some (getAt (fusion.dataA n).unit a l) else none))
    (all_guardSel n (fun l =>
      (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
        && (g (getAt 0 R.tail l) == x)) a hwidth (List.range R.links))
  rw [famFold_guardSel (fun l =>
      (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
        && (g (getAt 0 R.tail l) == x))
      (fun l => getAt (fusion.dataA n).unit a l)
      (fun s => (fusion.dataA n).cls s) (List.range R.links),
    famFold_guardSel (fun l =>
      (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
        && (g (getAt 0 R.tail l) == x))
      (fun l => getAt (fusion.dataA n).unit a l)
      (fun s => c2hat.dfQ s) (List.range R.links)] at h
  exact h

/-- The cuts' crossing families partition the direction's crossing
links: every crossing link is met at its tail's own grade, so the
cut family's folds collect the direction's crossing fold. -/
private theorem cutSplitFold (n : Nat) (R : lattice.Region)
    (g : Nat → Nat) (L : Nat) (a : List Shape)
    (hwell : lattice.wellRead R)
    (hcut : transCutRead R g L) :
    famFold Nat.add 0 (fun x => famFold Nat.add 0 (fun l =>
        if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
            && (g (getAt 0 R.tail l) == x)
          then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
          else 0) (List.range R.links)) (List.range L)
      = famFold Nat.add 0 (fun l =>
          if !(g (getAt 0 R.head l) == g (getAt 0 R.tail l))
            then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
            else 0) (List.range R.links) := by
  have htlt : ∀ l : Nat, l ∈ List.range R.links →
      getAt 0 R.tail l < R.verts := fun l hl =>
    (lattice.endLt R hwell l (ground.ltOfMemRange hl)).1
  have hglt : ∀ v : Nat, v < R.verts → g v < L := cutGrade R g L hcut
  have hswap := ground.famFold_swap (fun (x l : Nat) =>
      if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
          && (g (getAt 0 R.tail l) == x)
        then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
        else 0) (List.range L) (List.range R.links)
  have hcollapse : famFold Nat.add 0 (fun l =>
        famFold Nat.add 0 (fun x =>
          if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
              && (g (getAt 0 R.tail l) == x)
            then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
            else 0) (List.range L)) (List.range R.links)
      = famFold Nat.add 0 (fun l =>
          if !(g (getAt 0 R.head l) == g (getAt 0 R.tail l))
            then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
            else 0) (List.range R.links) := by
    refine ground.famFold_congr_members Nat.add 0 _ _
      (List.range R.links) (fun l hl => ?_)
    have hlm := ground.mem_of_countOf_pos l (List.range R.links) hl
    cases hc : (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l))) with
    | true =>
      exact ground.famFold_pickBeqRange (g (getAt 0 R.tail l))
        (c2hat.dfQ (getAt (fusion.dataA n).unit a l)) L
        (hglt _ (htlt l hlm))
    | false =>
      exact ground.famFold_zero _ (fun _ => rfl) (List.range L)
  exact hswap.trans hcollapse

/-- One direction's cuts sum to the direction's crossing content:
each cut nets the base cut's class by the conservation and reads
its own crossing family's floor, and the cuts' crossing families
partition the direction's crossing links at the tail's grade. -/
private theorem dirFloor (n : Nat) (hn : 0 < n) (R : lattice.Region)
    (g : Nat → Nat) (L : Nat) (a : List Shape)
    (hwell : lattice.wellRead R)
    (hcut : transCutRead R g L)
    (hocc : carrier.occupied (fusion.dataA n) R a = true)
    (hwidth : (a.all (fun s => s.length == n)) = true) :
    L * (fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n)
      ≤ famFold Nat.add 0 (fun l =>
          if !(g (getAt 0 R.head l) == g (getAt 0 R.tail l))
            then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
            else 0) (List.range R.links) := by
  have hconst : L * (fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n)
      = famFold Nat.add 0 (fun _ : Nat =>
          (fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n))
        (List.range L) := by
    rw [ground.famFold_const
        ((fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n))
        (List.range L), ground.length_range L]
  have hle1 : famFold Nat.add 0 (fun _ : Nat =>
        (fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n))
        (List.range L)
      ≤ famFold Nat.add 0 (fun x => famFold Nat.add 0 (fun l =>
          if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
              && (g (getAt 0 R.tail l) == x)
            then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
            else 0) (List.range R.links)) (List.range L) := by
    refine ground.famFold_le _ _ (List.range L) (fun x hx => ?_)
    rw [← fluxConserve n R g L a hwell hcut hocc hwidth x
      (ground.ltOfMemRange hx)]
    exact fluxFloor n hn R g a hwidth x
  rw [hconst]
  exact Nat.le_trans hle1
    (Nat.le_of_eq (cutSplitFold n R g L a hwell hcut))

/-- The directions' crossing folds sit within the configuration's
content: at most one direction's cut crosses a link, so the
crossing labels' cleared Casimirs are read once each at the
content's own key fold. -/
private theorem crossFloorContent (n d : Nat) (R : lattice.Region)
    (gf : Nat → Nat → Nat) (a : List Shape)
    (hdisj : ∀ l : Nat, l ∈ List.range R.links →
      ((List.range d).filter (fun e =>
        !(gf e (getAt 0 R.head l) == gf e (getAt 0 R.tail l)))).length
        ≤ 1) :
    famFold Nat.add 0 (fun e =>
        famFold Nat.add 0 (fun l =>
          if !(gf e (getAt 0 R.head l) == gf e (getAt 0 R.tail l))
            then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
            else 0) (List.range R.links)) (List.range d)
      ≤ carrier.contentN (fusion.dataA n) a := by
  rw [ground.famFold_swap (fun (e l : Nat) =>
    if !(gf e (getAt 0 R.head l) == gf e (getAt 0 R.tail l))
      then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
      else 0) (List.range d) (List.range R.links)]
  refine Nat.le_trans (ground.famFold_le _ (fun l =>
      if (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
          (fusion.dataA n).unit
        then 0
        else c2hat.dfQ (getAt (fusion.dataA n).unit a l))
      (List.range R.links) (fun l hl => ?_)) ?_
  · rw [ground.guardFold_count (fun e =>
      !(gf e (getAt 0 R.head l) == gf e (getAt 0 R.tail l)))
      (c2hat.dfQ (getAt (fusion.dataA n).unit a l)) (List.range d)]
    cases hq : (fusion.dataA n).eqL (getAt (fusion.dataA n).unit a l)
        (fusion.dataA n).unit with
    | true =>
      rw [dfQ_unitEq n (getAt (fusion.dataA n).unit a l) hq,
        Nat.zero_mul]
      exact Nat.zero_le _
    | false =>
      exact Nat.le_trans
        (Nat.mul_le_mul_left
          (c2hat.dfQ (getAt (fusion.dataA n).unit a l)) (hdisj l hl))
        (Nat.le_of_eq
          (Nat.mul_one (c2hat.dfQ (getAt (fusion.dataA n).unit a l))))
  · rw [contentN_famFold n a]
    refine ground.famFold_range_dom _ a.length R.links (fun l hl => ?_)
    rw [ground.getAt_over (fusion.dataA n).unit a l hl]
    exact if_pos ((fusion.dataA n).eqLRefl (fusion.dataA n).unit)

/-- The winding floor at a stated cut family: an occupied
configuration's content clears the side length times the
per-direction floor sum, the directions' crossing families disjoint
per link. -/
private theorem windFloorGen (n d L : Nat) (R : lattice.Region)
    (gf : Nat → Nat → Nat) (a : List Shape) (hn : 0 < n)
    (hwell : lattice.wellRead R)
    (hcuts : ∀ e : Nat, e < d → transCutRead R (gf e) L)
    (hdisj : ∀ l : Nat, l ∈ List.range R.links →
      ((List.range d).filter (fun e =>
        !(gf e (getAt 0 R.head l) == gf e (getAt 0 R.tail l)))).length
        ≤ 1)
    (hocc : carrier.occupied (fusion.dataA n) R a = true)
    (hwidth : (a.all (fun s => s.length == n)) = true) :
    L * famFold Nat.add 0 (fun e =>
        (fusion.dataA n).clsFloorN (fluxAt n R (gf e) 0 a % n))
      (List.range d)
      ≤ carrier.contentN (fusion.dataA n) a := by
  rw [ground.famFold_mul L (fun e =>
    (fusion.dataA n).clsFloorN (fluxAt n R (gf e) 0 a % n))
    (List.range d)]
  refine Nat.le_trans (ground.famFold_le _ (fun e =>
      famFold Nat.add 0 (fun l =>
        if !(gf e (getAt 0 R.head l) == gf e (getAt 0 R.tail l))
          then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
          else 0) (List.range R.links)) (List.range d)
    (fun e he => dirFloor n hn R (gf e) L a hwell
      (hcuts e (ground.ltOfMemRange he)) hocc hwidth)) ?_
  exact crossFloorContent n d R gf a hdisj

/-- The vacant residue's floors are vacant: at no class count every
endpoint display reads the count's unit. -/
private theorem clsFloor_zero (j : Nat) :
    (fusion.dataA 0).clsFloorN j = 0 := by
  show j * (0 - j) * (0 + 1) = 0
  rw [Nat.zero_sub j, Nat.mul_zero, Nat.zero_mul]

/-- The per-link cut disjointness: at most one direction's cut
crosses a link. -/
def cutDisjRead (d L : Nat) : Prop :=
  ((List.range (fiberdec.torusRegion d L).links).all (fun l =>
    ((List.range d).filter (fun e =>
      !(fiberdec.digitAt L e
          (getAt 0 (fiberdec.torusRegion d L).head l)
        == fiberdec.digitAt L e
          (getAt 0 (fiberdec.torusRegion d L).tail l)))).length
      ≤ 1)) = true

instance (d L : Nat) : Decidable (cutDisjRead d L) :=
  inferInstanceAs (Decidable (_ = _))

/-- The winding floor at the torus: an occupied configuration's
content clears the side length times the per-direction floor sum,
each direction's cuts netting the base cut's class by the
conservation, each cut's crossing family descending to its net
class's own floor, and the directions' crossing families disjoint
per link (`lem:chargedcell`(ii)). -/
theorem windFloor (n d L : Nat) (a : List Shape)
    (hwell : lattice.wellRead (fiberdec.torusRegion d L))
    (hcuts : ∀ e : Nat, e < d →
      transCutRead (fiberdec.torusRegion d L)
        (fun s => fiberdec.digitAt L e s) L)
    (hdisj : cutDisjRead d L)
    (hocc : carrier.occupied (fusion.dataA n)
      (fiberdec.torusRegion d L) a = true)
    (hwidth : (a.all (fun s => s.length == n)) = true) :
    L * famFold Nat.add 0 (fun e =>
        (fusion.dataA n).clsFloorN
          (fluxAt n (fiberdec.torusRegion d L)
            (fun s => fiberdec.digitAt L e s) 0 a % n))
      (List.range d)
      ≤ carrier.contentN (fusion.dataA n) a := by
  cases n with
  | zero =>
    rw [ground.famFold_zero (fun e =>
      (fusion.dataA 0).clsFloorN
        (fluxAt 0 (fiberdec.torusRegion d L)
          (fun s => fiberdec.digitAt L e s) 0 a % 0))
      (fun e => clsFloor_zero _) (List.range d), Nat.mul_zero]
    exact Nat.zero_le _
  | succ n' =>
    exact windFloorGen (n' + 1) d L (fiberdec.torusRegion d L)
      (fun e s => fiberdec.digitAt L e s) a (Nat.succ_pos n')
      hwell hcuts
      (fun l hl => of_decide_eq_true
        (ground.all_of_mem _ _
          (show ((List.range (fiberdec.torusRegion d L).links).all
            (fun l => decide
              (((List.range d).filter (fun e =>
                !(fiberdec.digitAt L e
                    (getAt 0 (fiberdec.torusRegion d L).head l)
                  == fiberdec.digitAt L e
                    (getAt 0 (fiberdec.torusRegion d L).tail l)))).length
                ≤ 1))) = true from hdisj) l hl))
      hocc hwidth

/-- The unit label's reduction is the label itself: the vacant
family already reads the unit occupancy at its full-column key. -/
private theorem reduce_unitL : ∀ n : Nat,
    labels.reduce (labels.unitL n) = labels.unitL n
  | 0 => rfl
  | k + 1 => by
    show labels.reduce (List.replicate (k + 1) 0)
      = List.replicate (k + 1) 0
    rw [← ground.replicate_snoc 0 k,
      labels.reduce_snoc (List.replicate k 0) 0]

/-- An extra crossing at the unit class prices its label at the
unit class's least nonunit read: a label of the stated width whose
class is the unit's and whose own read is off the unit label clears
`2 d_f²`, `θ`'s own cleared Casimir
(`lem:chargedcell`(iii)). -/
theorem unitCrossFloor (n : Nat) (s : Shape)
    (hs : (s.length == n) = true)
    (hcls : (fusion.dataA n).cls s = 0)
    (hne : (fusion.dataA n).eqL s (fusion.dataA n).unit = false) :
    2 * (n * n) ≤ c2hat.dfQ s := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n' =>
    have hlen : s.length = n' + 1 := ground.beqEqOf hs
    have hocc : 0 < ground.sumNat (labels.reduce s) := by
      cases hz : ground.sumNat (labels.reduce s) with
      | zero =>
        have hrep : labels.reduce s
            = List.replicate (labels.reduce s).length 0 :=
          ground.replicate_of_sum_zero (labels.reduce s) hz
        have hre : labels.reduce s
            = labels.reduce (labels.unitL (n' + 1)) := by
          rw [reduce_unitL (n' + 1)]
          show labels.reduce s = List.replicate (n' + 1) 0
          rw [hrep, (labels.length_reduce s).trans hlen]
        have htrue : (fusion.dataA (n' + 1)).eqL s
            (fusion.dataA (n' + 1)).unit = true := by
          show (labels.reduce s
            == labels.reduce (labels.unitL (n' + 1))) = true
          rw [hre]
          exact ground.listEqBeq _
        exact Bool.noConfusion (htrue.symm.trans hne)
      | succ k => exact Nat.succ_pos k
    have hc0 : places.degree s % (n' + 1) = 0 := hcls
    have h := casfloor.unitClassFloor n' (labels.reduce s)
      ((labels.length_reduce s).trans hlen)
      (reduce_red n' s hlen)
      ((ality_reduce (n' + 1) s hlen).trans hc0)
      hocc
    rw [dfQ_reduce s] at h
    exact h

/-- A refused unit-class read is a positive class code. -/
private theorem clsPos (n : Nat) (s : Shape)
    (hb : ((fusion.dataA n).cls s == 0) = false) :
    0 < (fusion.dataA n).cls s := by
  cases hcs : (fusion.dataA n).cls s with
  | zero =>
    rw [hcs] at hb
    exact Bool.noConfusion (show (true : Bool) = false from hb)
  | succ k => exact Nat.succ_pos k

/-- A crossing family carrying one nonunit member prices a nonunit
class merged onto its net: the merge's strict gap enters at the
walk's first nonunit member and rides to the family's own content
(`lem:chargedcell`(iii)). -/
private theorem famStrictHead (n : Nat) (hn : 0 < n) (c : Nat)
    (hc : 0 < c) (hcn : c < n) : ∀ ls : List Shape,
    (ls.all (fun s => s.length == n)) = true →
    1 ≤ famFold Nat.add 0 (fun s =>
        if (fusion.dataA n).cls s == 0 then 0 else 1) ls →
    (fusion.dataA n).clsFloorN
        ((c + famFold Nat.add 0
          (fun s => (fusion.dataA n).cls s) ls) % n)
      + 2 * (n + 1)
      ≤ (fusion.dataA n).clsFloorN c
        + famFold Nat.add 0 (fun s => c2hat.dfQ s) ls
  | [], _, hcount =>
    absurd (show 1 ≤ 0 from hcount) (Nat.not_succ_le_zero 0)
  | s :: t, hall, hcount => by
    have hsplit := ground.andSplitB
      (show ((s.length == n)
        && t.all (fun u => u.length == n)) = true from hall)
    have hc0 : (1 : Nat)
        ≤ (if ((fusion.dataA n).cls s == 0) = true then 0 else 1)
          + famFold Nat.add 0 (fun u =>
            if (fusion.dataA n).cls u == 0 then 0 else 1) t :=
      hcount
    cases hb : ((fusion.dataA n).cls s == 0) with
    | true =>
      rw [if_pos hb, Nat.zero_add] at hc0
      show (fusion.dataA n).clsFloorN
          ((c + ((fusion.dataA n).cls s
            + famFold Nat.add 0
              (fun u => (fusion.dataA n).cls u) t)) % n)
          + 2 * (n + 1)
        ≤ (fusion.dataA n).clsFloorN c
          + (c2hat.dfQ s
            + famFold Nat.add 0 (fun u => c2hat.dfQ u) t)
      rw [ground.beqEqOf hb, Nat.zero_add]
      exact Nat.le_trans (famStrictHead n hn c hc hcn t hsplit.2 hc0)
        (Nat.add_le_add_left
          (Nat.le_add_left
            (famFold Nat.add 0 (fun u => c2hat.dfQ u) t)
            (c2hat.dfQ s))
          ((fusion.dataA n).clsFloorN c))
    | false =>
      have hmod : (c + ((fusion.dataA n).cls s
            + famFold Nat.add 0
              (fun u => (fusion.dataA n).cls u) t)) % n
          = ((c + (fusion.dataA n).cls s) % n
            + famFold Nat.add 0
              (fun u => (fusion.dataA n).cls u) t % n) % n := by
        rw [ground.modAdd (c + (fusion.dataA n).cls s)
          (famFold Nat.add 0 (fun u => (fusion.dataA n).cls u) t) n,
          Nat.add_assoc]
      show (fusion.dataA n).clsFloorN
          ((c + ((fusion.dataA n).cls s
            + famFold Nat.add 0
              (fun u => (fusion.dataA n).cls u) t)) % n)
          + 2 * (n + 1)
        ≤ (fusion.dataA n).clsFloorN c
          + (c2hat.dfQ s
            + famFold Nat.add 0 (fun u => c2hat.dfQ u) t)
      rw [hmod]
      refine Nat.le_trans (Nat.add_le_add_right
        (floorSub n ((c + (fusion.dataA n).cls s) % n)
          (famFold Nat.add 0 (fun u => (fusion.dataA n).cls u) t % n)
          ((ground.natDivRead _ n hn).2)
          ((ground.natDivRead _ n hn).2)) (2 * (n + 1))) ?_
      rw [Nat.add_right_comm
          ((fusion.dataA n).clsFloorN ((c + (fusion.dataA n).cls s) % n))
          ((fusion.dataA n).clsFloorN
            (famFold Nat.add 0 (fun u => (fusion.dataA n).cls u) t % n))
          (2 * (n + 1)),
        ← Nat.add_assoc ((fusion.dataA n).clsFloorN c) (c2hat.dfQ s)
          (famFold Nat.add 0 (fun u => c2hat.dfQ u) t)]
      exact Nat.add_le_add
        (Nat.le_trans
          (mergeGap n c ((fusion.dataA n).cls s) hc hcn
            (clsPos n s hb) (clsLt n hn s))
          (Nat.add_le_add_left (famMember n hn s hsplit.1)
            ((fusion.dataA n).clsFloorN c)))
        (famSub n hn t hsplit.2)

/-- A crossing family carrying two nonunit members prices its net
class strictly: the merge's gap of two residue counts rides the
walk to the family's own content (`lem:chargedcell`(iii)). -/
theorem famSubStrict (n : Nat) (hn : 0 < n) : ∀ ls : List Shape,
    (ls.all (fun s => s.length == n)) = true →
    2 ≤ famFold Nat.add 0 (fun s =>
        if (fusion.dataA n).cls s == 0 then 0 else 1) ls →
    (fusion.dataA n).clsFloorN
        (famFold Nat.add 0 (fun s => (fusion.dataA n).cls s) ls % n)
      + 2 * (n + 1)
      ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) ls
  | [], _, hcount =>
    absurd (show 2 ≤ 0 from hcount) (Nat.not_succ_le_zero 1)
  | s :: t, hall, hcount => by
    have hsplit := ground.andSplitB
      (show ((s.length == n)
        && t.all (fun u => u.length == n)) = true from hall)
    have hc0 : (2 : Nat)
        ≤ (if ((fusion.dataA n).cls s == 0) = true then 0 else 1)
          + famFold Nat.add 0 (fun u =>
            if (fusion.dataA n).cls u == 0 then 0 else 1) t :=
      hcount
    cases hb : ((fusion.dataA n).cls s == 0) with
    | true =>
      rw [if_pos hb, Nat.zero_add] at hc0
      show (fusion.dataA n).clsFloorN
          (((fusion.dataA n).cls s
            + famFold Nat.add 0
              (fun u => (fusion.dataA n).cls u) t) % n)
          + 2 * (n + 1)
        ≤ c2hat.dfQ s + famFold Nat.add 0 (fun u => c2hat.dfQ u) t
      rw [ground.beqEqOf hb, Nat.zero_add]
      exact Nat.le_trans (famSubStrict n hn t hsplit.2 hc0)
        (Nat.le_add_left
          (famFold Nat.add 0 (fun u => c2hat.dfQ u) t)
          (c2hat.dfQ s))
    | false =>
      rw [if_neg (ground.boolNe hb)] at hc0
      have hcnt : 1 ≤ famFold Nat.add 0 (fun u =>
          if (fusion.dataA n).cls u == 0 then 0 else 1) t :=
        ground.leCancelL 1 hc0
      show (fusion.dataA n).clsFloorN
          (((fusion.dataA n).cls s
            + famFold Nat.add 0
              (fun u => (fusion.dataA n).cls u) t) % n)
          + 2 * (n + 1)
        ≤ c2hat.dfQ s + famFold Nat.add 0 (fun u => c2hat.dfQ u) t
      exact Nat.le_trans
        (famStrictHead n hn ((fusion.dataA n).cls s) (clsPos n s hb)
          (clsLt n hn s) t hsplit.2 hcnt)
        (Nat.add_le_add_right (famMember n hn s hsplit.1)
          (famFold Nat.add 0 (fun u => c2hat.dfQ u) t))

/-- A nonunit label's cleared Casimir clears the fundamental loop's
own read: the class floors' least nonunit value at the stated
width. -/
private theorem memberFloor (n : Nat) (hn : 0 < n) (s : Shape)
    (hs : (s.length == n) = true)
    (hb : ((fusion.dataA n).cls s == 0) = false) :
    (n - 1) * (n + 1) ≤ c2hat.dfQ s := by
  cases n with
  | zero => exact absurd hn (Nat.lt_irrefl 0)
  | succ n' =>
    have h := casfloor.classFloor_fund n'
      ((fusion.dataA (n' + 1)).cls s) (clsPos (n' + 1) s hb)
      (Nat.le_of_lt_succ (clsLt (n' + 1) hn s))
    rw [show n' + 1 - 1 = n' from ground.addSubSelfR n' 1]
    exact Nat.le_trans h (famMember (n' + 1) hn s hs)

/-- A crossing family clears its nonunit-member count's multiple of
the least nonunit floor at its own content
(`lem:chargedcell`(iii)). -/
private theorem famCountFloor (n : Nat) (hn : 0 < n) :
    ∀ (k : Nat) (ls : List Shape),
    (ls.all (fun s => s.length == n)) = true →
    k ≤ famFold Nat.add 0 (fun s =>
        if (fusion.dataA n).cls s == 0 then 0 else 1) ls →
    k * ((n - 1) * (n + 1))
      ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) ls
  | k, [], _, hcount => by
    cases k with
    | zero =>
      rw [Nat.zero_mul]
      exact Nat.le_refl 0
    | succ k' => exact absurd hcount (Nat.not_succ_le_zero k')
  | k, s :: t, hall, hcount => by
    have hsplit := ground.andSplitB
      (show ((s.length == n)
        && t.all (fun u => u.length == n)) = true from hall)
    have hc0 : k
        ≤ (if ((fusion.dataA n).cls s == 0) = true then 0 else 1)
          + famFold Nat.add 0 (fun u =>
            if (fusion.dataA n).cls u == 0 then 0 else 1) t :=
      hcount
    show k * ((n - 1) * (n + 1))
      ≤ c2hat.dfQ s + famFold Nat.add 0 (fun u => c2hat.dfQ u) t
    cases hb : ((fusion.dataA n).cls s == 0) with
    | true =>
      rw [if_pos hb, Nat.zero_add] at hc0
      exact Nat.le_trans (famCountFloor n hn k t hsplit.2 hc0)
        (Nat.le_add_left
          (famFold Nat.add 0 (fun u => c2hat.dfQ u) t)
          (c2hat.dfQ s))
    | false =>
      cases k with
      | zero =>
        rw [Nat.zero_mul]
        exact Nat.zero_le _
      | succ k' =>
        rw [if_neg (ground.boolNe hb), Nat.add_comm k' 1] at hc0
        rw [ground.mulAddR k' 1 ((n - 1) * (n + 1)),
          Nat.one_mul, Nat.add_comm (k' * ((n - 1) * (n + 1)))]
        exact Nat.add_le_add (memberFloor n hn s hsplit.1 hb)
          (famCountFloor n hn k' t hsplit.2
            (ground.leCancelL 1 hc0))

/-- An all-unit crossing family nets the unit class: every member's
code is the unit's and the fold's residue with it. -/
private theorem netAllUnit (n : Nat) : ∀ ls : List Shape,
    famFold Nat.add 0 (fun s =>
        if (fusion.dataA n).cls s == 0 then 0 else 1) ls = 0 →
    famFold Nat.add 0 (fun s => (fusion.dataA n).cls s) ls % n = 0
  | [], _ => ground.modZeroLeft n
  | s :: t, h0 => by
    have hsum : (if ((fusion.dataA n).cls s == 0) = true then 0 else 1)
        + famFold Nat.add 0 (fun u =>
          if (fusion.dataA n).cls u == 0 then 0 else 1) t = 0 := h0
    have hhead : (if ((fusion.dataA n).cls s == 0) = true
        then (0 : Nat) else 1) = 0 :=
      Nat.eq_zero_of_add_eq_zero_right hsum
    have hz : (fusion.dataA n).cls s = 0 := by
      cases hb : ((fusion.dataA n).cls s == 0) with
      | true => exact ground.beqEqOf hb
      | false =>
        rw [if_neg (ground.boolNe hb)] at hhead
        exact Nat.noConfusion hhead
    show ((fusion.dataA n).cls s
      + famFold Nat.add 0 (fun u => (fusion.dataA n).cls u) t) % n = 0
    rw [hz, Nat.zero_add]
    exact netAllUnit n t (Nat.eq_zero_of_add_eq_zero_left hsum)

/-- A crossing family netting the unit class at one nonunit member
carries a second: a lone nonunit code nets itself, off the unit
class below the residue. -/
private theorem netCountTwo (n : Nat) (hn : 0 < n) :
    ∀ ls : List Shape,
    famFold Nat.add 0 (fun s => (fusion.dataA n).cls s) ls % n = 0 →
    1 ≤ famFold Nat.add 0 (fun s =>
        if (fusion.dataA n).cls s == 0 then 0 else 1) ls →
    2 ≤ famFold Nat.add 0 (fun s =>
        if (fusion.dataA n).cls s == 0 then 0 else 1) ls
  | [], _, hcount =>
    absurd (show 1 ≤ 0 from hcount) (Nat.not_succ_le_zero 0)
  | s :: t, hnet, hcount => by
    have hn0 : ((fusion.dataA n).cls s
        + famFold Nat.add 0
          (fun u => (fusion.dataA n).cls u) t) % n = 0 := hnet
    have hc0 : (1 : Nat)
        ≤ (if ((fusion.dataA n).cls s == 0) = true then 0 else 1)
          + famFold Nat.add 0 (fun u =>
            if (fusion.dataA n).cls u == 0 then 0 else 1) t :=
      hcount
    show (2 : Nat)
      ≤ (if ((fusion.dataA n).cls s == 0) = true then 0 else 1)
        + famFold Nat.add 0 (fun u =>
          if (fusion.dataA n).cls u == 0 then 0 else 1) t
    cases hb : ((fusion.dataA n).cls s == 0) with
    | true =>
      rw [if_pos hb, Nat.zero_add] at hc0
      rw [ground.beqEqOf hb, Nat.zero_add] at hn0
      rw [if_pos rfl, Nat.zero_add]
      exact netCountTwo n hn t hn0 hc0
    | false =>
      rw [if_neg (fun h : (false = true) => Bool.noConfusion h)]
      have hcnt : 1 ≤ famFold Nat.add 0 (fun u =>
          if (fusion.dataA n).cls u == 0 then 0 else 1) t := by
        cases hct : famFold Nat.add 0 (fun u =>
            if (fusion.dataA n).cls u == 0 then 0 else 1) t with
        | zero =>
          rw [← ground.modAdd ((fusion.dataA n).cls s)
              (famFold Nat.add 0
                (fun u => (fusion.dataA n).cls u) t) n,
            netAllUnit n t hct, clsMod n s, Nat.add_zero,
            clsMod n s] at hn0
          rw [hn0] at hb
          exact Bool.noConfusion (show (true : Bool) = false from hb)
        | succ k => exact Nat.succ_pos k
      exact Nat.add_le_add_left hcnt 1

/-- A crossing family netting the unit class holds two members at
their classes' floors: the net's two nonunit members each clear the
least nonunit floor, twice it at the family's own content
(`lem:chargedcell`(iii)). -/
theorem famNetUnit (n : Nat) (hn : 0 < n) (ls : List Shape)
    (hw : (ls.all (fun s => s.length == n)) = true)
    (hnet : famFold Nat.add 0
        (fun s => (fusion.dataA n).cls s) ls % n = 0)
    (h1 : 1 ≤ famFold Nat.add 0 (fun s =>
        if (fusion.dataA n).cls s == 0 then 0 else 1) ls) :
    2 * ((n - 1) * (n + 1))
      ≤ famFold Nat.add 0 (fun s => c2hat.dfQ s) ls :=
  famCountFloor n hn 2 ls hw (netCountTwo n hn ls hnet h1)

/-- The transverse cut's crossing multiset at its nonunit-class
members: the count of the region's links crossing the cut at a
label off the unit class (`lem:chargedcell`(iii)'s crossing
count). -/
def crossCountAt (n : Nat) (R : lattice.Region)
    (g : Nat → Nat) (a : List Shape) (x : Nat) : Nat :=
  linkFold (fusion.dataA n).unit (fun t h s =>
    if (!(g h == g t)) && (g t == x)
        && !((fusion.dataA n).cls s == 0)
      then 1 else 0) R.tail R.head a

/-- The crossing count reads at the link keys, the per-link fold's
own key read. -/
private theorem crossCountAt_read (n : Nat) (R : lattice.Region)
    (g : Nat → Nat) (a : List Shape) (x : Nat) :
    crossCountAt n R g a x
      = famFold Nat.add 0 (fun l =>
          if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
              && (g (getAt 0 R.tail l) == x)
              && !((fusion.dataA n).cls
                (getAt (fusion.dataA n).unit a l) == 0)
            then 1 else 0) (List.range R.links) := by
  have h := linkFold_read (fusion.dataA n).unit
    (fun t h s => if (!(g h == g t)) && (g t == x)
        && !((fusion.dataA n).cls s == 0)
      then 1 else 0)
    R.tail R.head a (R.headLen.trans R.tailLen.symm)
  rw [R.tailLen] at h
  exact h

/-- The crossing count reads the cut family's nonunit-class count:
the guarded members' unit-class reads and the count's own guard
meet key by key. -/
private theorem crossCount_read (n : Nat) (R : lattice.Region)
    (g : Nat → Nat) (a : List Shape) (x : Nat) :
    famFold Nat.add 0 (fun l =>
        if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
            && (g (getAt 0 R.tail l) == x)
          then (if (fusion.dataA n).cls
            (getAt (fusion.dataA n).unit a l) == 0 then 0 else 1)
          else 0) (List.range R.links)
      = crossCountAt n R g a x := by
  refine Eq.trans ?_ (crossCountAt_read n R g a x).symm
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun l => ?_)
    (List.range R.links)
  cases hq : ((!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
      && (g (getAt 0 R.tail l) == x)) with
  | true =>
    cases hbc : ((fusion.dataA n).cls
        (getAt (fusion.dataA n).unit a l) == 0) with
    | true => rfl
    | false => rfl
  | false => rfl

/-- An extra-crossed cut descends to its class's floor strictly:
two nonunit crossings price the cut's class two residue counts
below the crossing links' own content
(`lem:chargedcell`(iii)). -/
private theorem fluxFloorStrict (n : Nat) (hn : 0 < n)
    (R : lattice.Region) (g : Nat → Nat) (a : List Shape)
    (hwidth : (a.all (fun s => s.length == n)) = true) (x : Nat)
    (hx : 2 ≤ crossCountAt n R g a x) :
    (fusion.dataA n).clsFloorN (fluxAt n R g x a % n) + 2 * (n + 1)
      ≤ famFold Nat.add 0 (fun l =>
          if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
              && (g (getAt 0 R.tail l) == x)
            then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
            else 0) (List.range R.links) := by
  rw [fluxAt_read n R g x a]
  have hg := famFold_guardSel (fun l =>
      (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
        && (g (getAt 0 R.tail l) == x))
    (fun l => getAt (fusion.dataA n).unit a l)
    (fun s => if (fusion.dataA n).cls s == 0 then 0 else 1)
    (List.range R.links)
  have hcount : 2 ≤ famFold Nat.add 0 (fun s =>
      if (fusion.dataA n).cls s == 0 then 0 else 1)
      ((List.range R.links).filterMap (fun l =>
        if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
            && (g (getAt 0 R.tail l) == x)
          then some (getAt (fusion.dataA n).unit a l) else none)) :=
    Nat.le_trans hx (Nat.le_of_eq
      ((crossCount_read n R g a x).symm.trans hg.symm))
  have h := famSubStrict n hn
    ((List.range R.links).filterMap (fun l =>
      if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
          && (g (getAt 0 R.tail l) == x)
        then some (getAt (fusion.dataA n).unit a l) else none))
    (all_guardSel n (fun l =>
      (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
        && (g (getAt 0 R.tail l) == x)) a hwidth (List.range R.links))
    hcount
  rw [famFold_guardSel (fun l =>
      (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
        && (g (getAt 0 R.tail l) == x))
      (fun l => getAt (fusion.dataA n).unit a l)
      (fun s => (fusion.dataA n).cls s) (List.range R.links),
    famFold_guardSel (fun l =>
      (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
        && (g (getAt 0 R.tail l) == x))
      (fun l => getAt (fusion.dataA n).unit a l)
      (fun s => c2hat.dfQ s) (List.range R.links)] at h
  exact h

/-- One direction's priced floor: every extra-crossed cut joins the
merge's strict gap to the direction's floor, the cuts' crossing
families partitioning the direction's crossing links
(`lem:chargedcell`(iii)). -/
private theorem dirFloorPriced (n : Nat) (hn : 0 < n)
    (R : lattice.Region) (g : Nat → Nat) (L : Nat) (a : List Shape)
    (hwell : lattice.wellRead R)
    (hcut : transCutRead R g L)
    (hocc : carrier.occupied (fusion.dataA n) R a = true)
    (hwidth : (a.all (fun s => s.length == n)) = true) :
    L * (fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n)
      + 2 * (n + 1) * famFold Nat.add 0 (fun x =>
          if 2 ≤ crossCountAt n R g a x then 1 else 0) (List.range L)
      ≤ famFold Nat.add 0 (fun l =>
          if !(g (getAt 0 R.head l) == g (getAt 0 R.tail l))
            then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
            else 0) (List.range R.links) := by
  have hconst : L * (fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n)
      = famFold Nat.add 0 (fun _ : Nat =>
          (fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n))
        (List.range L) := by
    rw [ground.famFold_const
        ((fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n))
        (List.range L), ground.length_range L]
  rw [hconst, ground.famFold_mul (2 * (n + 1)) (fun x =>
      if 2 ≤ crossCountAt n R g a x then 1 else 0) (List.range L),
    ← ground.famFold_add_split (fun _ : Nat =>
        (fusion.dataA n).clsFloorN (fluxAt n R g 0 a % n))
      (fun x => 2 * (n + 1)
        * (if 2 ≤ crossCountAt n R g a x then 1 else 0))
      (List.range L)]
  refine Nat.le_trans (ground.famFold_le _ (fun x =>
      famFold Nat.add 0 (fun l =>
        if (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
            && (g (getAt 0 R.tail l) == x)
          then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
          else 0) (List.range R.links)) (List.range L)
    (fun x hx => ?_)) (Nat.le_of_eq (cutSplitFold n R g L a hwell hcut))
  rw [← fluxConserve n R g L a hwell hcut hocc hwidth x
    (ground.ltOfMemRange hx)]
  by_cases hc : 2 ≤ crossCountAt n R g a x
  · rw [if_pos hc, Nat.mul_one]
    exact fluxFloorStrict n hn R g a hwidth x hc
  · rw [if_neg hc, Nat.mul_zero, Nat.add_zero]
    exact fluxFloor n hn R g a hwidth x

/-- The priced winding floor at a stated cut family: every
extra-crossed cut joins the merge's strict gap to the winding
floor, the directions' crossing families disjoint per link
(`lem:chargedcell`(iii)). -/
private theorem windPricedGen (n d L : Nat) (R : lattice.Region)
    (gf : Nat → Nat → Nat) (a : List Shape) (hn : 0 < n)
    (hwell : lattice.wellRead R)
    (hcuts : ∀ e : Nat, e < d → transCutRead R (gf e) L)
    (hdisj : ∀ l : Nat, l ∈ List.range R.links →
      ((List.range d).filter (fun e =>
        !(gf e (getAt 0 R.head l) == gf e (getAt 0 R.tail l)))).length
        ≤ 1)
    (hocc : carrier.occupied (fusion.dataA n) R a = true)
    (hwidth : (a.all (fun s => s.length == n)) = true) :
    L * famFold Nat.add 0 (fun e =>
        (fusion.dataA n).clsFloorN (fluxAt n R (gf e) 0 a % n))
      (List.range d)
      + 2 * (n + 1) * famFold Nat.add 0 (fun e =>
          famFold Nat.add 0 (fun x =>
            if 2 ≤ crossCountAt n R (gf e) a x then 1 else 0)
            (List.range L)) (List.range d)
      ≤ carrier.contentN (fusion.dataA n) a := by
  rw [ground.famFold_mul L (fun e =>
      (fusion.dataA n).clsFloorN (fluxAt n R (gf e) 0 a % n))
      (List.range d),
    ground.famFold_mul (2 * (n + 1)) (fun e =>
      famFold Nat.add 0 (fun x =>
        if 2 ≤ crossCountAt n R (gf e) a x then 1 else 0)
        (List.range L)) (List.range d),
    ← ground.famFold_add_split (fun e =>
        L * (fusion.dataA n).clsFloorN (fluxAt n R (gf e) 0 a % n))
      (fun e => 2 * (n + 1) * famFold Nat.add 0 (fun x =>
        if 2 ≤ crossCountAt n R (gf e) a x then 1 else 0)
        (List.range L)) (List.range d)]
  refine Nat.le_trans (ground.famFold_le _ (fun e =>
      famFold Nat.add 0 (fun l =>
        if !(gf e (getAt 0 R.head l) == gf e (getAt 0 R.tail l))
          then c2hat.dfQ (getAt (fusion.dataA n).unit a l)
          else 0) (List.range R.links)) (List.range d)
    (fun e he => dirFloorPriced n hn R (gf e) L a hwell
      (hcuts e (ground.ltOfMemRange he))
      hocc hwidth)) ?_
  exact crossFloorContent n d R gf a hdisj

/-- At the vacant residue every label reads the unit class: a
vacant width leaves the label calculus its own vacant shape. -/
private theorem clsZero_width (s : Shape) (h : s.length = 0) :
    (fusion.dataA 0).cls s = 0 := by
  cases s with
  | nil => rfl
  | cons y t => exact Nat.noConfusion (show t.length + 1 = 0 from h)

/-- At the vacant residue no crossing is counted: every label reads
the unit class, so the count's own guard refuses at every link. -/
private theorem crossCountAt_zero (R : lattice.Region)
    (g : Nat → Nat) (a : List Shape)
    (hwidth : (a.all (fun s => s.length == 0)) = true) (x : Nat) :
    crossCountAt 0 R g a x = 0 := by
  rw [crossCountAt_read 0 R g a x]
  refine ground.famFold_zero _ (fun l => ?_) (List.range R.links)
  have hcls : (fusion.dataA 0).cls (getAt (fusion.dataA 0).unit a l)
      = 0 :=
    clsZero_width (getAt (fusion.dataA 0).unit a l)
      (ground.beqEqOf (label_width 0 a hwidth l))
  rw [hcls]
  cases hg : (!(g (getAt 0 R.head l) == g (getAt 0 R.tail l)))
      && (g (getAt 0 R.tail l) == x) with
  | true => exact rfl
  | false => exact rfl

/-- The priced winding floor at the torus: every extra-crossed cut
joins the merge's strict gap to the winding floor, so an occupied
configuration's content clears the side length times the
per-direction floor sum together with two residue counts per
extra-crossed cut (`lem:chargedcell`(iii)). -/
theorem windFloorPriced (n d L : Nat) (a : List Shape)
    (hwell : lattice.wellRead (fiberdec.torusRegion d L))
    (hcuts : ∀ e : Nat, e < d →
      transCutRead (fiberdec.torusRegion d L)
        (fun s => fiberdec.digitAt L e s) L)
    (hdisj : cutDisjRead d L)
    (hocc : carrier.occupied (fusion.dataA n)
      (fiberdec.torusRegion d L) a = true)
    (hwidth : (a.all (fun s => s.length == n)) = true) :
    L * famFold Nat.add 0 (fun e =>
        (fusion.dataA n).clsFloorN
          (fluxAt n (fiberdec.torusRegion d L)
            (fun s => fiberdec.digitAt L e s) 0 a % n))
      (List.range d)
      + 2 * (n + 1) * famFold Nat.add 0 (fun e =>
          famFold Nat.add 0 (fun x =>
            if 2 ≤ crossCountAt n (fiberdec.torusRegion d L)
                (fun s => fiberdec.digitAt L e s) a x
              then 1 else 0)
            (List.range L)) (List.range d)
      ≤ carrier.contentN (fusion.dataA n) a := by
  cases n with
  | zero =>
    rw [ground.famFold_zero (fun e =>
        (fusion.dataA 0).clsFloorN
          (fluxAt 0 (fiberdec.torusRegion d L)
            (fun s => fiberdec.digitAt L e s) 0 a % 0))
        (fun e => clsFloor_zero _) (List.range d), Nat.mul_zero,
      Nat.zero_add,
      ground.famFold_zero (fun e =>
        famFold Nat.add 0 (fun x =>
          if 2 ≤ crossCountAt 0 (fiberdec.torusRegion d L)
              (fun s => fiberdec.digitAt L e s) a x
            then 1 else 0)
          (List.range L))
        (fun e => ground.famFold_zero (fun x =>
          if 2 ≤ crossCountAt 0 (fiberdec.torusRegion d L)
              (fun s => fiberdec.digitAt L e s) a x
            then 1 else 0)
          (fun x => by
            rw [crossCountAt_zero (fiberdec.torusRegion d L)
              (fun s => fiberdec.digitAt L e s) a hwidth x]
            exact if_neg (by decide +kernel)) (List.range L))
        (List.range d), Nat.mul_zero]
    exact Nat.zero_le _
  | succ n' =>
    exact windPricedGen (n' + 1) d L (fiberdec.torusRegion d L)
      (fun e s => fiberdec.digitAt L e s) a (Nat.succ_pos n')
      hwell hcuts
      (fun l hl => of_decide_eq_true
        (ground.all_of_mem _ _
          (show ((List.range (fiberdec.torusRegion d L).links).all
            (fun l => decide
              (((List.range d).filter (fun e =>
                !(fiberdec.digitAt L e
                    (getAt 0 (fiberdec.torusRegion d L).head l)
                  == fiberdec.digitAt L e
                    (getAt 0 (fiberdec.torusRegion d L).tail l)))).length
                ≤ 1))) = true from hdisj) l hl))
      hocc hwidth

/-- `lem:chargedcell`(iii)'s dressing fold, the tower decimation's
per-cell Schur read at the cell's stencil: one pair `[e² : g]` per
stencil atom at the changed-edge entry `e` and the content gap's
numerator `g` over the one second member, the fold at the squared
magnetic weight `w`. -/
def dressFold (w : Pair) (atoms : List (Pos × Pos)) : CPair :=
  CPair.ofPair w .one * CPair.sum (atoms.map (fun a =>
    CPair.ofPair ⟨a.1 * a.1, a.2⟩ .one))

/-- The balance pair of the string's dressed per-cell floor against
the unit class's — the winding-floor pair at a one-member site with
the vacuum's dressing fold, against the string's fold on the second
member. -/
def tension (vp w : Pair) (vac str : List (Pos × Pos)) : CPair :=
  CPair.ofPair vp .one + dressFold w vac + (dressFold w str).swap

/-- The tension at the ray's factors, `q²` at the electric member
and `[p⁴ : q²]` at the two folds, the seam identity's weights. -/
def tensionAt (p q vpN vpD : Pos)
    (vac str : List (Pos × Pos)) : CPair :=
  tension ⟨q * q * vpN, vpD⟩ ⟨p * p * (p * p), q * q⟩ vac str

/-- Both members linear in the term count, each further atom one
more summand. -/
theorem dressFold_cons (w : Pair) (a : Pos × Pos)
    (l : List (Pos × Pos)) :
    (dressFold w (a :: l)).oneValue
      (CPair.ofPair (w * ⟨a.1 * a.1, a.2⟩) .one + dressFold w l) := by
  refine CPair.oneValue_trans
    (CPair.mul_congr (CPair.oneValue_refl _) (CPair.sum_cons _ _)) ?_
  refine CPair.oneValue_trans (CPair.mul_add _ _ _) ?_
  refine CPair.add_congr (CPair.oneValue_symm
    (CPair.ofPair_mul w ⟨a.1 * a.1, a.2⟩ .one .one .one)) ?_
  exact CPair.oneValue_refl _

/-- A joined stencil's fold splits at the two parts' folds, the
weight standing across the join. -/
private theorem dressFold_append (w : Pair) (u v : List (Pos × Pos)) :
    (dressFold w (u ++ v)).oneValue (dressFold w u + dressFold w v) := by
  show (CPair.ofPair w .one * CPair.sum ((u ++ v).map (fun a =>
      CPair.ofPair ⟨a.1 * a.1, a.2⟩ .one))).oneValue
    (dressFold w u + dressFold w v)
  rw [ground.map_append]
  refine CPair.oneValue_trans
    (CPair.mul_congr (CPair.oneValue_refl _) (CPair.sum_append _ _)) ?_
  exact CPair.mul_add _ _ _

/-- The far plaquettes' folds enter both members equally, a summand
on both members fixing the value — the pair reads at the stencil
neighborhood alone. -/
theorem tension_far (vp w : Pair)
    (vac str far : List (Pos × Pos)) :
    (tension vp w (vac ++ far) (str ++ far)).oneValue
      (tension vp w vac str) := by
  have h1 : (tension vp w (vac ++ far) (str ++ far)).oneValue
      (CPair.ofPair vp .one + (dressFold w vac + dressFold w far)
        + ((dressFold w str).swap + (dressFold w far).swap)) :=
    CPair.add_congr
      (CPair.add_congr (CPair.oneValue_refl _) (dressFold_append w vac far))
      (CPair.swap_congr (dressFold_append w str far))
  have hEq : CPair.ofPair vp .one + (dressFold w vac + dressFold w far)
        + ((dressFold w str).swap + (dressFold w far).swap)
      = tension vp w vac str
        + (dressFold w far + (dressFold w far).swap) := by
    show CPair.ofPair vp .one + (dressFold w vac + dressFold w far)
        + ((dressFold w str).swap + (dressFold w far).swap)
      = CPair.ofPair vp .one + dressFold w vac + (dressFold w str).swap
        + (dressFold w far + (dressFold w far).swap)
    rw [← CPair.add_assoc (CPair.ofPair vp .one) (dressFold w vac)
        (dressFold w far),
      CPair.add_assoc (CPair.ofPair vp .one + dressFold w vac)
        (dressFold w far)
        ((dressFold w str).swap + (dressFold w far).swap),
      ← CPair.add_assoc (dressFold w far) ((dressFold w str).swap)
        ((dressFold w far).swap),
      CPair.add_comm (dressFold w far) ((dressFold w str).swap),
      CPair.add_assoc ((dressFold w str).swap) (dressFold w far)
        ((dressFold w far).swap),
      ← CPair.add_assoc (CPair.ofPair vp .one + dressFold w vac)
        ((dressFold w str).swap)
        (dressFold w far + (dressFold w far).swap)]
  refine CPair.oneValue_trans h1 ?_
  rw [hEq]
  exact CPair.add_swap_unit (dressFold w far) (tension vp w vac str)

/-- The free end reads the electric member alone, both folds at the
end's one-member read: at the matched stencil the folds enter both
members equally and the value is the summed winding floor. -/
theorem tension_free (vp w : Pair) (l : List (Pos × Pos)) :
    (tension vp w l l).oneValue (CPair.ofPair vp .one) := by
  refine CPair.oneValue_trans (tension_far vp w [] [] l) ?_
  show (CPair.ofPair vp .one + dressFold w [] + (dressFold w []).swap).oneValue
    (CPair.ofPair vp .one)
  rw [CPair.add_assoc]
  exact CPair.add_swap_unit (dressFold w []) (CPair.ofPair vp .one)

/-- The ray's factors scaled together carry one squared factor out
of the whole tension: the electric member and both dressing folds
gain the same one-member entry. -/
private theorem tensionAt_scale (s p q vpN vpD : Pos)
    (vac str : List (Pos × Pos)) :
    (tensionAt (s * p) (s * q) vpN vpD vac str).oneValue
      (CPair.ofPair ⟨s * s, .one⟩ .one
        * tensionAt p q vpN vpD vac str) := by
  have hvpEq : ((s * q) * (s * q) * vpN) * (Pos.one * vpD)
      = ((s * s) * (q * q * vpN)) * vpD := by
    rw [ground.one_mul vpD, ground.mul_mul_mul_comm s q s q,
      ground.mul_assoc (s * s) (q * q) vpN]
  have hwEq : ((s * p) * (s * p) * ((s * p) * (s * p)))
        * (Pos.one * (q * q))
      = ((s * s) * (p * p * (p * p))) * ((s * q) * (s * q)) := by
    rw [ground.one_mul (q * q), ground.mul_mul_mul_comm s p s p,
      ground.mul_mul_mul_comm s q s q,
      ground.mul_mul_mul_comm (s * s) (p * p) (s * s) (p * p),
      ground.mul_mul_mul_comm (s * s) (p * p * (p * p)) (s * s) (q * q),
      ground.mul_assoc (s * s * (s * s)) (p * p * (p * p)) (q * q)]
  have hvp : (CPair.ofPair ⟨(s * q) * (s * q) * vpN, vpD⟩ .one).oneValue
      (CPair.ofPair ⟨s * s, .one⟩ .one
        * CPair.ofPair ⟨q * q * vpN, vpD⟩ .one) :=
    CPair.oneValue_trans
      (CPair.ofPair_congr (p := ⟨(s * q) * (s * q) * vpN, vpD⟩)
        (q := ⟨(s * s) * (q * q * vpN), Pos.one * vpD⟩)
        hvpEq .one .one)
      (CPair.ofPair_mul ⟨s * s, .one⟩ ⟨q * q * vpN, vpD⟩ .one .one .one)
  have hw : (CPair.ofPair
        ⟨(s * p) * (s * p) * ((s * p) * (s * p)), (s * q) * (s * q)⟩
        .one).oneValue
      (CPair.ofPair ⟨s * s, .one⟩ .one
        * CPair.ofPair ⟨p * p * (p * p), q * q⟩ .one) :=
    CPair.oneValue_trans
      (CPair.ofPair_congr
        (p := ⟨(s * p) * (s * p) * ((s * p) * (s * p)), (s * q) * (s * q)⟩)
        (q := ⟨(s * s) * (p * p * (p * p)), Pos.one * (q * q)⟩)
        hwEq .one .one)
      (CPair.ofPair_mul ⟨s * s, .one⟩ ⟨p * p * (p * p), q * q⟩ .one .one .one)
  have hvac : (dressFold
        ⟨(s * p) * (s * p) * ((s * p) * (s * p)),
          (s * q) * (s * q)⟩ vac).oneValue
      (CPair.ofPair ⟨s * s, .one⟩ .one
        * dressFold ⟨p * p * (p * p), q * q⟩ vac) :=
    CPair.mul_left_congr hw _
  have hstr : (dressFold
        ⟨(s * p) * (s * p) * ((s * p) * (s * p)),
          (s * q) * (s * q)⟩ str).oneValue
      (CPair.ofPair ⟨s * s, .one⟩ .one
        * dressFold ⟨p * p * (p * p), q * q⟩ str) :=
    CPair.mul_left_congr hw _
  have hL : (tensionAt (s * p) (s * q) vpN vpD vac str).oneValue
      ((CPair.ofPair ⟨s * s, .one⟩ .one
            * CPair.ofPair ⟨q * q * vpN, vpD⟩ .one
          + CPair.ofPair ⟨s * s, .one⟩ .one
            * dressFold ⟨p * p * (p * p), q * q⟩ vac)
        + CPair.ofPair ⟨s * s, .one⟩ .one
            * (dressFold ⟨p * p * (p * p), q * q⟩ str).swap) :=
    CPair.add_congr (CPair.add_congr hvp hvac) (CPair.swap_congr hstr)
  have hR : (CPair.ofPair ⟨s * s, .one⟩ .one
        * tensionAt p q vpN vpD vac str).oneValue
      ((CPair.ofPair ⟨s * s, .one⟩ .one
            * CPair.ofPair ⟨q * q * vpN, vpD⟩ .one
          + CPair.ofPair ⟨s * s, .one⟩ .one
            * dressFold ⟨p * p * (p * p), q * q⟩ vac)
        + CPair.ofPair ⟨s * s, .one⟩ .one
            * (dressFold ⟨p * p * (p * p), q * q⟩ str).swap) :=
    CPair.oneValue_trans (CPair.mul_add _ _ _)
      (CPair.add_congr (CPair.mul_add _ _ _) (CPair.oneValue_refl _))
  exact CPair.oneValue_trans hL (CPair.oneValue_symm hR)

/-- The scaled ray reads the same side: the carried one-member
factor keeps the swap comparison. -/
private theorem tensionAt_scale_lt (s p q vpN vpD : Pos)
    (vac str : List (Pos × Pos)) :
    (tensionAt (s * p) (s * q) vpN vpD vac str
        < (tensionAt (s * p) (s * q) vpN vpD vac str).swap)
      ↔ (tensionAt p q vpN vpD vac str
        < (tensionAt p q vpN vpD vac str).swap) := by
  have hsc := tensionAt_scale s p q vpN vpD vac str
  constructor
  · intro hlt
    exact (CPair.mul_lt_swap ⟨s * s, .one⟩ .one
      (tensionAt p q vpN vpD vac str)).mp
      (CPair.lt_congr hsc (CPair.swap_congr hsc) hlt)
  · intro hlt
    exact CPair.lt_congr (CPair.oneValue_symm hsc)
      (CPair.swap_congr (CPair.oneValue_symm hsc))
      ((CPair.mul_lt_swap ⟨s * s, .one⟩ .one
        (tensionAt p q vpN vpD vac str)).mpr hlt)

/-- The tension's side is a ray datum — two representatives at the
seam's cross-multiplied tie read one side. -/
theorem tension_ray (p q p' q' : Pos) (h : p * q' = p' * q)
    (vpN vpD : Pos) (vac str : List (Pos × Pos)) :
    (tensionAt p q vpN vpD vac str
        < (tensionAt p q vpN vpD vac str).swap)
      ↔ (tensionAt p' q' vpN vpD vac str
        < (tensionAt p' q' vpN vpD vac str).swap) := by
  have e1 := tensionAt_scale_lt q' p q vpN vpD vac str
  have e2 := tensionAt_scale_lt q p' q' vpN vpD vac str
  have hp : q' * p = q * p' := by
    rw [ground.mul_comm q' p, h, ground.mul_comm p' q]
  have hq : q' * q = q * q' := ground.mul_comm q' q
  rw [hp, hq] at e1
  exact Iff.trans (Iff.symm e1) e2

/-- At tension off its lower side on the cell the least-length read
extends to every larger length: the per-length pair is the per-cell
tension at the length's one-member entry, so its side is the cell's
own at every length. -/
theorem tension_length (Lp : Pos) (vp w : Pair)
    (vac str : List (Pos × Pos)) :
    (CPair.ofPair (Pair.ofPos Lp) .one * tension vp w vac str
        < (CPair.ofPair (Pair.ofPos Lp) .one
          * tension vp w vac str).swap)
      ↔ (tension vp w vac str < (tension vp w vac str).swap) :=
  CPair.mul_lt_swap (Pair.ofPos Lp) .one (tension vp w vac str)

/-! `lem:chargedcell`(iv)'s charged decimation: the fiber pencil is
block diagonal over the charges — the plaquette rows keep the
charge at `θ`'s unit class with the electric diagonal reading each
index member at itself — and the counts split over the charge
blocks, `lem:inertia`'s block-diagonal addition at the vacant
couplings. -/

/-- The per-group charge reads, one structural pass — each group's
members at the group's own stated charge vector and pairwise
distinct at the interface equality. -/
def chargeGroupsAt (n d L : Nat) :
    List (List Nat) → List (List (List Shape)) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | c :: cs, g :: gs =>
    (g.all (fun a => chargeT n d L a == c))
      && decimation.distinctGo (fusion.dataA n) g
      && chargeGroupsAt n d L cs gs

/-- The sectors' vacant couplings at the stated orders, one
equal-membered block per consecutive pair. -/
def unitOffs : List Nat → List elim.Mat
  | [] => []
  | [_] => []
  | k :: k' :: t =>
    List.replicate k (List.replicate k' BPair.unit)
      :: unitOffs (k' :: t)

/-- The charge blocking — the stated index at the concatenated
charge groups, the group keys distinct, the orders the groups'
lengths with the sector blocks square at them, and the window
pencil at the assembled block diagonal over the charges, the
couplings vacant. -/
def chargeBlockRead (n d L : Nat) (ix : List (List Shape))
    (cs : List (List Nat)) (gs : List (List (List Shape)))
    (H : elim.Mat) (diag : List elim.Mat) (ns : List Nat) : Prop :=
  decimation.confListEq (fusion.dataA n) (gs.flatMap (fun g => g)) ix
      = true
  ∧ chargeGroupsAt n d L cs gs = true
  ∧ ground.distinctList cs
  ∧ ns = gs.map List.length
  ∧ greenprod.slabShape diag (unitOffs ns) ns
  ∧ elim.matOneValue H (greenprod.assemble diag (unitOffs ns))

instance (n d L : Nat) (ix : List (List Shape))
    (cs : List (List Nat)) (gs : List (List (List Shape)))
    (H : elim.Mat) (diag : List elim.Mat) (ns : List Nat) :
    Decidable (chargeBlockRead n d L ix cs gs H diag ns) :=
  inferInstanceAs (Decidable (_ = _ ∧ _ = _ ∧ _ ∧ _ = _ ∧ _ ∧ _))

/-- Every member of a row fused by `θ` on the right reads the source
label's class, the row's additivity at `θ`'s own unit class. -/
private theorem clsRow_theta_source (n : Nat) (y : Shape) :
    (((fusion.dataA n).row y (adjchar.theta n)).all (fun c =>
      Nat.beq ((fusion.dataA n).cls c)
        ((fusion.dataA n).cls y))) = true :=
  clsRow_of n y (adjchar.theta n) ((fusion.dataA n).cls y) (by
    show (degree y % n + degree (adjchar.theta n) % n) % n
      = degree y % n
    rw [ality_theta n, Nat.add_zero]
    exact ground.modMod (degree y) n)

/-- A plaquette row's target reads the source's class at every link:
on a boundary link the target sits in the `θ`-row of the source's
own label, off the boundary it is that label. -/
private theorem plaqRow_cls (n : Nat) (R : lattice.Region)
    (p : List (Nat × Bool)) (a b : List Shape)
    (hb : 0 < ground.countOf b
      (algebra.plaqRow (fusion.dataA n) R p a))
    (l : Nat) (hl : l < R.links) :
    (fusion.dataA n).cls (getAt (fusion.dataA n).unit b l)
      = (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l) := by
  have hk := algebra.plaqRow_target (fusion.dataA n) R p a b hb l hl
  by_cases hany : (p.any (fun e => e.1 == l)) = true
  · have hrow : algebra.linkTargets (fusion.dataA n) p a l
        = (fusion.dataA n).row (getAt (fusion.dataA n).unit a l)
          (fusion.dataA n).theta := by
      show (if p.any (fun e => e.1 == l)
          then (fusion.dataA n).row (getAt (fusion.dataA n).unit a l)
            (fusion.dataA n).theta
          else [getAt (fusion.dataA n).unit a l])
        = (fusion.dataA n).row (getAt (fusion.dataA n).unit a l)
          (fusion.dataA n).theta
      rw [if_pos hany]
    rw [hrow] at hk
    exact ground.beqEq _ _
      (ground.all_of_mem _ _
        (clsRow_theta_source n (getAt (fusion.dataA n).unit a l)) _
        (ground.mem_of_countOf_pos _ _ hk))
  · have hsing : algebra.linkTargets (fusion.dataA n) p a l
        = [getAt (fusion.dataA n).unit a l] := by
      show (if p.any (fun e => e.1 == l)
          then (fusion.dataA n).row (getAt (fusion.dataA n).unit a l)
            (fusion.dataA n).theta
          else [getAt (fusion.dataA n).unit a l])
        = [getAt (fusion.dataA n).unit a l]
      rw [if_neg hany]
    rw [hsing] at hk
    rw [ground.countOf_single hk]

/-- The flux fold reads the classes alone: two configurations at one
class per link read one flux at every cut. -/
private theorem fluxAt_cls (n : Nat) (R : lattice.Region)
    (g : Nat → Nat) (x : Nat) (a b : List Shape)
    (h : ∀ l, l < R.links →
      (fusion.dataA n).cls (getAt (fusion.dataA n).unit b l)
        = (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l)) :
    fluxAt n R g x b = fluxAt n R g x a := by
  have hlt : ∀ y : Nat, 0 < ground.countOf y (List.range R.links) →
      y < R.links := fun _ hy => ground.ltOfMem hy
  rw [fluxAt_read n R g x b, fluxAt_read n R g x a]
  refine ground.famFold_congr_members Nat.add 0 _ _
    (List.range R.links) ?_
  intro y hy
  rw [h y (hlt y hy)]

/-- The charge is the classes' read: two configurations at one class
per link carry one charge family at the torus. -/
private theorem chargeT_cls (n d L : Nat) (a b : List Shape)
    (h : ∀ l, l < (fiberdec.torusRegion d L).links →
      (fusion.dataA n).cls (getAt (fusion.dataA n).unit b l)
        = (fusion.dataA n).cls (getAt (fusion.dataA n).unit a l)) :
    chargeT n d L b = chargeT n d L a := by
  show (List.range d).map (fun e =>
      fluxAt n (fiberdec.torusRegion d L)
        (fun s => fiberdec.digitAt L e s) 0 b % n)
    = (List.range d).map (fun e =>
      fluxAt n (fiberdec.torusRegion d L)
        (fun s => fiberdec.digitAt L e s) 0 a % n)
  refine ground.map_congr_all _ _ ?_ (List.range d)
  intro e
  rw [fluxAt_cls n (fiberdec.torusRegion d L)
    (fun s => fiberdec.digitAt L e s) 0 a b h]

/-- Every plaquette row keeps the charge — the fusion by `θ` fixes
every link's class, and the flux folds read the classes alone. -/
theorem chargeRow (n d L : Nat) (p : List (Nat × Bool))
    (a : List Shape) :
    ((algebra.plaqRow (fusion.dataA n)
        (fiberdec.torusRegion d L) p a).all
      (fun b => chargeT n d L b == chargeT n d L a)) = true := by
  refine ground.all_of_getAt ([] : List Shape) _
    (algebra.plaqRow (fusion.dataA n)
      (fiberdec.torusRegion d L) p a) ?_
  intro k hk
  have hcnt := ground.countOf_getAt_pos ([] : List Shape)
    (algebra.plaqRow (fusion.dataA n)
      (fiberdec.torusRegion d L) p a) k hk
  have heq := chargeT_cls n d L a
    (getAt ([] : List Shape)
      (algebra.plaqRow (fusion.dataA n)
        (fiberdec.torusRegion d L) p a) k)
    (fun l hl => plaqRow_cls n (fiberdec.torusRegion d L) p a _
      hcnt l hl)
  show (chargeT n d L (getAt ([] : List Shape)
      (algebra.plaqRow (fusion.dataA n)
        (fiberdec.torusRegion d L) p a) k)
    == chargeT n d L a) = true
  rw [heq]
  exact ground.listEqBeq (chargeT n d L a)

end chargedcell
