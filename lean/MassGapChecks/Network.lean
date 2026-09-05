import MassGap.Network
/-!
The check module for `thm:network`: the theta region's four
lattice reads decided; the weight numerators, the resolvent
factors and the slot-two self-energy at the label calculus's
committed residues — the `r = 1` self-energy `[5 : 18]` at the
three-channel row — with the displayed weight list's shape; and
the recoupling tier's committed reads, the interpolant's
coefficient counts at the withdrawn nodes with the projected
states' collected key lists.  Above them: the weight displays'
and the middle values' theorem routes at each row's own floor
width, the committed list's own value representatives, the
interface ties at the two residues with the `θ` row refused at
the width two, the width three's dimension identity and
self-energy `[349 : 1344]`, the resolvent factor's composition at
the `θ` term, and the middle values' first three pairwise apart
at `r = 1`.  Below them the reduction's reads: the all-`θ` network occupied at the width two
with its content, its two three-valent multiplicities and a
path-broken configuration refused; the energy and multiplicity
theorems routed at the committed labels; the pair read and the
spread decided there with the spread's unit read, the evaluation's
split at the three labels; and the path reads and the determination
routed at a fusion datum over the counts, with one datum per
refused label read — the involution at the unit label, the
involution at one count, an equality joining two counts to the
unit label at each order, a chaining equality refusing the
transitive read alone, and an upward equality refusing the unit
labels' read alone, each held law swept at the exhibit's label
window — beside the three occupancy binders' own refusals.
-/
open ground fusion network

/-! The theta region's lattice reads. -/

example : lattice.wellRead lattice.thetaG := by decide +kernel
example : lattice.colorRead lattice.thetaG := by decide +kernel
example : lattice.simpleRead lattice.thetaG := by decide +kernel
example : lattice.plaqRead lattice.thetaG := by decide +kernel

/-! The weight numerators at the committed residues: the `r = 1`
row's `m_k d_k` at the three channels against `d_θ² = 9`
(`fusion.dimLaw` the completeness's read), and the `r = 2` `θ`
weight at the base `c₁ = 2`. -/

example : weightN (dataA 2) [0, 0] = 1 := by decide +kernel
example : weightN (dataA 2) [2, 0] = 3 := by decide +kernel
example : weightN (dataA 2) [4, 0] = 5 := by decide +kernel
example : dimLaw (dataA 2) (adjchar.theta 2) (adjchar.theta 2) := by
  decide +kernel
example : weightN (dataA 3) (adjchar.theta 3) = 16 := by decide +kernel

/-! The resolvent factors and the self-energy at `r = 1`: the
factors `[8 : 16 + dfQ]` at the three channels and the fold's
value `[5 : 18]`, the vacant interface's factor `none`. -/

example : (match resFactor (dataA 2) (adjchar.theta 2) with
    | some p => decide (p.oneValue
        (Pair.mk (posOfSucc 0) (posOfSucc 2)))
    | none => false) = true := by decide +kernel

example : (match selfEnergy (dataA 2) with
    | some p => decide (p.oneValue
        (Pair.mk (posOfSucc 4) (posOfSucc 17)))
    | none => false) = true := by decide +kernel

/-! The recoupling tier's committed reads: five nodes, the
interpolant at a withdrawn node one degree-four coefficient list,
and the projected states' sites. -/

example : network.nodes.length = 5 := by decide +kernel
example : (network.lagNum 0).length = 5 := by decide +kernel
example : (network.lagNum 1).length = 5 := by decide +kernel
example : network.siteQ12.length = 4 := by decide +kernel
example : (twoplaq.extSite 0 network.siteQ12).length = 6 := by
  decide +kernel

/-! The weight displays' theorem routes at each row's own floor
width, the label calculus's first residues. -/

example : ((poly.eval wUnit.1 (BPair.ofNat (0 + 1))).mul
      (BPair.ofNat
        (4 * (((0 + 2) * (0 + 2) - 1) * ((0 + 2) * (0 + 2) - 1))))).oneValue
    ((poly.eval wUnit.2 (BPair.ofNat (0 + 1))).mul
      (BPair.ofNat (1 * (4 * weyldim.dimOf (channels.rowUnit (0 + 2)))))) :=
  wUnit_read 0

example : ((poly.eval wTheta.1 (BPair.ofNat (0 + 2))).mul
      (BPair.ofNat
        (4 * (((0 + 3) * (0 + 3) - 1) * ((0 + 3) * (0 + 3) - 1))))).oneValue
    ((poly.eval wTheta.2 (BPair.ofNat (0 + 2))).mul
      (BPair.ofNat (2 * (4 * weyldim.dimOf (channels.rowTheta (0 + 3)))))) :=
  wTheta_read 0

example : ((poly.eval wTwoTheta.1 (BPair.ofNat (0 + 1))).mul
      (BPair.ofNat
        (4 * (((0 + 2) * (0 + 2) - 1) * ((0 + 2) * (0 + 2) - 1))))).oneValue
    ((poly.eval wTwoTheta.2 (BPair.ofNat (0 + 1))).mul
      (BPair.ofNat
        (1 * (4 * weyldim.dimOf (channels.rowTwoTheta (0 + 2)))))) :=
  wTwoTheta_read 0

example : ((poly.eval wDual.1 (BPair.ofNat (0 + 2))).mul
      (BPair.ofNat
        (4 * (((0 + 3) * (0 + 3) - 1) * ((0 + 3) * (0 + 3) - 1))))).oneValue
    ((poly.eval wDual.2 (BPair.ofNat (0 + 2))).mul
      (BPair.ofNat (1 * (4 * weyldim.dimOf (channels.rowDualA (0 + 3)))))) :=
  wDual_read 0

example : ((poly.eval wDual.1 (BPair.ofNat (0 + 2))).mul
      (BPair.ofNat
        (4 * (((0 + 3) * (0 + 3) - 1) * ((0 + 3) * (0 + 3) - 1))))).oneValue
    ((poly.eval wDual.2 (BPair.ofNat (0 + 2))).mul
      (BPair.ofNat (1 * (4 * weyldim.dimOf (channels.rowDualB (0 + 3)))))) :=
  wDualB_read 0

example : ((poly.eval wOmega.1 (BPair.ofNat (0 + 3))).mul
      (BPair.ofNat
        (4 * (((0 + 4) * (0 + 4) - 1) * ((0 + 4) * (0 + 4) - 1))))).oneValue
    ((poly.eval wOmega.2 (BPair.ofNat (0 + 3))).mul
      (BPair.ofNat (1 * (4 * weyldim.dimOf (channels.rowOmega (0 + 4)))))) :=
  wOmega_read 0

/-! The middle values' ties routed at their floors, with the ten
pairwise gaps' first reads off the bundled theorem. -/

example : ((poly.eval (ground.getAt poly.pZero nodes 1).1
      (BPair.ofNat (0 + 1))).mul (BPair.ofNat (2 * (0 + 2)))).oneValue
    ((poly.eval (ground.getAt poly.pZero nodes 1).2
      (BPair.ofNat (0 + 1))).mul
      (BPair.ofNat (c2hat.dfQ (channels.rowTheta (0 + 2))))) :=
  nodeTheta_read 0

example : ((poly.eval (ground.getAt poly.pZero nodes 3).1
      (BPair.ofNat (0 + 2))).mul (BPair.ofNat (2 * (0 + 3)))).oneValue
    ((poly.eval (ground.getAt poly.pZero nodes 3).2
      (BPair.ofNat (0 + 2))).mul
      (BPair.ofNat (c2hat.dfQ (channels.rowDualB (0 + 3))))) :=
  nodeDualB_read 0

example : ¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 0)
    (ground.getAt poly.pZero nodes 1) (BPair.ofNat (0 + 2)) :=
  (nodes_gap 0).1

/-! The committed list holds its six displayed pairs, each its own
value representative, so the degree and top reads run at the
stored coefficients. -/

example : wList.length = 6 := by decide +kernel
example : (wList.all (fun w =>
    decide (poly.vnorm w.1 = w.1) && decide (poly.vnorm w.2 = w.2)))
      = true := by decide +kernel

/-! The displays against the interface at `r = 1`: the unit and
`2θ` rows tie at `[m_k d_k : d_θ²]`, and the `θ` row is refused
there — the table's count at the width two is one at that row
against the display's two. -/

example : ((poly.eval wUnit.1 (BPair.ofNat 1)).mul
      (BPair.ofNat
        ((dataA 2).dim (adjchar.theta 2)
          * (dataA 2).dim (adjchar.theta 2)))).oneValue
    ((poly.eval wUnit.2 (BPair.ofNat 1)).mul
      (BPair.ofNat (weightN (dataA 2) (channels.rowUnit 2)))) := by decide +kernel

example : ((poly.eval wTwoTheta.1 (BPair.ofNat 1)).mul
      (BPair.ofNat
        ((dataA 2).dim (adjchar.theta 2)
          * (dataA 2).dim (adjchar.theta 2)))).oneValue
    ((poly.eval wTwoTheta.2 (BPair.ofNat 1)).mul
      (BPair.ofNat (weightN (dataA 2) (channels.rowTwoTheta 2)))) := by decide +kernel

example : ¬ ((poly.eval wTheta.1 (BPair.ofNat 1)).mul
      (BPair.ofNat
        ((dataA 2).dim (adjchar.theta 2)
          * (dataA 2).dim (adjchar.theta 2)))).oneValue
    ((poly.eval wTheta.2 (BPair.ofNat 1)).mul
      (BPair.ofNat (weightN (dataA 2) (channels.rowTheta 2)))) := by decide +kernel

/-! The displays against the interface at `r = 2`: the five rows of
the width three tie at `[m_k d_k : d_θ²]`, the dual pair's display
entering at each of its two rows. -/

example : ((poly.eval wUnit.1 (BPair.ofNat 2)).mul
      (BPair.ofNat
        ((dataA 3).dim (adjchar.theta 3)
          * (dataA 3).dim (adjchar.theta 3)))).oneValue
    ((poly.eval wUnit.2 (BPair.ofNat 2)).mul
      (BPair.ofNat (weightN (dataA 3) (channels.rowUnit 3)))) := by decide +kernel

example : ((poly.eval wTheta.1 (BPair.ofNat 2)).mul
      (BPair.ofNat
        ((dataA 3).dim (adjchar.theta 3)
          * (dataA 3).dim (adjchar.theta 3)))).oneValue
    ((poly.eval wTheta.2 (BPair.ofNat 2)).mul
      (BPair.ofNat (weightN (dataA 3) (adjchar.theta 3)))) := by decide +kernel

example : ((poly.eval wTwoTheta.1 (BPair.ofNat 2)).mul
      (BPair.ofNat
        ((dataA 3).dim (adjchar.theta 3)
          * (dataA 3).dim (adjchar.theta 3)))).oneValue
    ((poly.eval wTwoTheta.2 (BPair.ofNat 2)).mul
      (BPair.ofNat (weightN (dataA 3) (channels.rowTwoTheta 3)))) := by decide +kernel

example : ((poly.eval wDual.1 (BPair.ofNat 2)).mul
      (BPair.ofNat
        ((dataA 3).dim (adjchar.theta 3)
          * (dataA 3).dim (adjchar.theta 3)))).oneValue
    ((poly.eval wDual.2 (BPair.ofNat 2)).mul
      (BPair.ofNat (weightN (dataA 3) (channels.rowDualA 3)))) := by decide +kernel

example : ((poly.eval wDual.1 (BPair.ofNat 2)).mul
      (BPair.ofNat
        ((dataA 3).dim (adjchar.theta 3)
          * (dataA 3).dim (adjchar.theta 3)))).oneValue
    ((poly.eval wDual.2 (BPair.ofNat 2)).mul
      (BPair.ofNat (weightN (dataA 3) (channels.rowDualB 3)))) := by decide +kernel

/-! The width three's dimension identity and self-energy: the
interface's completeness at the adjoint square and the fold's value
`[349 : 1344]`. -/

example : dimLaw (dataA 3) (adjchar.theta 3) (adjchar.theta 3) := by decide +kernel

example : (match selfEnergy (dataA 3) with
    | some p => decide (p.oneValue
        (Pair.mk (posOfSucc 348) (posOfSucc 1343)))
    | none => false) = true := by decide +kernel

/-! The middle values at `r = 1`: the first three pairwise apart. -/

example : ¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 0)
    (ground.getAt poly.pZero nodes 1) (BPair.ofNat 1) := by decide +kernel

example : ¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 0)
    (ground.getAt poly.pZero nodes 2) (BPair.ofNat 1) := by decide +kernel

example : ¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 1)
    (ground.getAt poly.pZero nodes 2) (BPair.ofNat 1) := by decide +kernel

/-! The reduction (`thm:network`(i)) at the label calculus's width
two: the all-`θ` network's occupancy with its content `56` and its
two three-valent multiplicities, and a path-broken configuration
refused at the vertex where its two links read apart. -/

example : carrier.occupied (dataA 2) lattice.thetaG
    (netConf [2, 0] [2, 0] [2, 0]) = true := by decide +kernel

example : carrier.contentN (dataA 2) (netConf [2, 0] [2, 0] [2, 0])
    = 56 := by decide +kernel

example : carrier.vmult (dataA 2) lattice.thetaG
    (netConf [2, 0] [2, 0] [2, 0]) 0 = 1 := by decide +kernel

example : carrier.vmult (dataA 2) lattice.thetaG
    (netConf [2, 0] [2, 0] [2, 0]) 3 = 1 := by decide +kernel

example : carrier.occupied (dataA 2) lattice.thetaG
    [[2, 0], [2, 0], [4, 0], [2, 0], [2, 0], [2, 0], [2, 0]]
      = false := by decide +kernel

example : carrier.vmult (dataA 2) lattice.thetaG
    [[2, 0], [2, 0], [4, 0], [2, 0], [2, 0], [2, 0], [2, 0]] 2
      = 0 := by decide +kernel

/-! The energy and multiplicity theorems routed at the width two's
committed labels, the display's own count `56` beside the first. -/

example : carrier.contentN (dataA 2) (netConf [2, 0] [2, 0] [2, 0])
    = 3 * (if (dataA 2).eqL [2, 0] (dataA 2).unit then 0
        else (dataA 2).c2N [2, 0])
      + (if (dataA 2).eqL [2, 0] (dataA 2).unit then 0
        else (dataA 2).c2N [2, 0])
      + 3 * (if (dataA 2).eqL [2, 0] (dataA 2).unit then 0
        else (dataA 2).c2N [2, 0]) :=
  netConf_energy (dataA 2) [2, 0] [2, 0] [2, 0]

example : (3 * (if (dataA 2).eqL [2, 0] (dataA 2).unit then 0
      else (dataA 2).c2N [2, 0])
    + (if (dataA 2).eqL [2, 0] (dataA 2).unit then 0
      else (dataA 2).c2N [2, 0])
    + 3 * (if (dataA 2).eqL [2, 0] (dataA 2).unit then 0
      else (dataA 2).c2N [2, 0])) = 56 := by decide +kernel

example : carrier.vmult (dataA 2) lattice.thetaG
      (netConf [2, 0] [2, 0] [2, 0]) 0
      = carrier.invCount (dataA 2)
          [[2, 0], (dataA 2).dual [2, 0], (dataA 2).dual [2, 0]]
    ∧ carrier.vmult (dataA 2) lattice.thetaG
      (netConf [2, 0] [2, 0] [2, 0]) 3
      = carrier.invCount (dataA 2)
          [(dataA 2).dual [2, 0], [2, 0], [2, 0]] :=
  netConf_vmult (dataA 2) [2, 0] [2, 0] [2, 0] (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The two path reads and the reduction at the width two's all-`θ`
network, decided at the label calculus's own reads: the first
two-valent vertex's pair read, one of the four the network reads
at one label over its six path links, and the index at its own
spread. -/

example :
    (((dataA 2).eqL
          (ground.getAt (dataA 2).unit (netConf [2, 0] [2, 0] [2, 0]) 0)
          (dataA 2).unit = true
        ∧ (dataA 2).eqL
          (ground.getAt (dataA 2).unit (netConf [2, 0] [2, 0] [2, 0]) 1)
          (dataA 2).unit = true)
      ∨ ((dataA 2).eqL
          (ground.getAt (dataA 2).unit (netConf [2, 0] [2, 0] [2, 0]) 0)
          (dataA 2).unit = false
        ∧ (dataA 2).eqL
          (ground.getAt (dataA 2).unit (netConf [2, 0] [2, 0] [2, 0]) 1)
          (dataA 2).unit = false
        ∧ (dataA 2).eqL
          ((dataA 2).dual
            (ground.getAt (dataA 2).unit (netConf [2, 0] [2, 0] [2, 0]) 0))
          ((dataA 2).dual
            (ground.getAt (dataA 2).unit (netConf [2, 0] [2, 0] [2, 0]) 1))
          = true)) := by decide +kernel

example : carrier.eqConf (dataA 2) (netConf [2, 0] [2, 0] [2, 0])
    (netConf
      (ground.getAt (dataA 2).unit (netConf [2, 0] [2, 0] [2, 0]) 1)
      (ground.getAt (dataA 2).unit (netConf [2, 0] [2, 0] [2, 0]) 0)
      (ground.getAt (dataA 2).unit (netConf [2, 0] [2, 0] [2, 0]) 4))
      = true := by decide +kernel

/-! The spread's unit read: the all-`θ` network is occupied off the
unit coordinate, the all-unit spread reads it, and a mixed spread at
one unit label reads off — the evaluation's split at the three
labels, decided and through the theorem. -/

example : ((netConf [2, 0] [2, 0] [2, 0]).all
    (fun x => (dataA 2).eqL x (dataA 2).unit)) = false := by decide +kernel
example : ((netConf [0, 0] [0, 0] [0, 0]).all
    (fun x => (dataA 2).eqL x (dataA 2).unit)) = true := by decide +kernel
example : ((netConf [2, 0] [0, 0] [0, 0]).all
    (fun x => (dataA 2).eqL x (dataA 2).unit)) = false := by decide +kernel
example : ((netConf [2, 0] [0, 0] [4, 0]).all
    (fun x => (dataA 2).eqL x (dataA 2).unit))
    = ((dataA 2).eqL [0, 0] (dataA 2).unit && (dataA 2).eqL [2, 0] (dataA 2).unit
      && (dataA 2).eqL [4, 0] (dataA 2).unit) :=
  spreadUnit (dataA 2) [2, 0] [0, 0] [4, 0]

/-! The interface values the binder reads run at: a fusion datum
over the counts, its label equality and involution stated per read
with the counts, rows, dimensions and Casimirs at one value each. -/

private def trivF (e : Nat → Nat → Bool) (d : Nat → Nat)
    (hr : ∀ l, e l l = true) : fusion.Data Nat :=
  { eqL := e, eqLRefl := hr, unit := 0, dual := d,
    add := fun x y => x + y, theta := 1,
    count := fun _ _ _ => 1, row := fun _ _ => [0, 1],
    dim := fun _ => 1, c2N := fun _ => 1, c2D := 1, c1 := 1,
    below := fun _ => [], cls := fun _ => 0,
    clsAdd := fun x y => x + y, clsFloorN := fun _ => 0,
    vertList := fun _ => none }

/-- The label equality at the counts' own read. -/
private def eqBeq (x y : Nat) : Bool := x == y

/-- A label equality joining the counts `3` and `4` to the unit
label `0` at each order, the counts' own read beside those four. -/
private def eqJoin (x y : Nat) : Bool :=
  x == y || (x == 3 && y == 0) || (x == 0 && y == 3)
    || (x == 4 && y == 0) || (x == 0 && y == 4)

private theorem eqBeqRefl (l : Nat) : eqBeq l l = true :=
  ground.eqBeqOf rfl

private theorem eqJoinRefl (l : Nat) : eqJoin l l = true := by
  show ((l == l) || (l == 3 && l == 0) || (l == 0 && l == 3)
    || (l == 4 && l == 0) || (l == 0 && l == 4)) = true
  rw [show (l == l) = true from ground.eqBeqOf rfl]
  exact rfl

/-- The involution at the identity, the four label reads holding. -/
private def Fid : fusion.Data Nat := trivF eqBeq (fun x => x) eqBeqRefl

/-- The involution reading the count `1` at the unit label and the
count `2` at `1`, refusing `hdu`. -/
private def Fdu : fusion.Data Nat := trivF eqBeq (fun x => x - 1) eqBeqRefl

/-- The involution at the count `1`, refusing `hdc`. -/
private def Fdc : fusion.Data Nat := trivF eqBeq (fun _ => 1) eqBeqRefl

/-- The joining equality at the identity involution, refusing `huu`
and `htr`. -/
private def Fuu : fusion.Data Nat := trivF eqJoin (fun x => x) eqJoinRefl

/-- The involution's unit read at the identity involution. -/
private theorem hduF : ∀ x, Fid.eqL (Fid.dual x) Fid.unit = true →
    Fid.eqL x Fid.unit = true := fun _ h => h

/-- The two duals at one label give the two labels one read. -/
private theorem hdcF : ∀ x y,
    Fid.eqL (Fid.dual x) (Fid.dual y) = true → Fid.eqL y x = true :=
  fun x y h => by
    show (y == x) = true
    rw [ground.beqEqOf (show (x == y) = true from h)]
    exact ground.eqBeqOf rfl

/-- Two labels at the unit read one another. -/
private theorem huuF : ∀ x y, Fid.eqL x Fid.unit = true →
    Fid.eqL y Fid.unit = true → Fid.eqL y x = true :=
  fun x y hx hy => by
    show (y == x) = true
    rw [ground.beqEqOf (show (x == 0) = true from hx),
      ground.beqEqOf (show (y == 0) = true from hy)]
    exact ground.eqBeqOf rfl

/-- The label equality's transitive read. -/
private theorem htrF : ∀ x y z, Fid.eqL x y = true →
    Fid.eqL y z = true → Fid.eqL x z = true :=
  fun x y z h1 h2 => by
    show (x == z) = true
    rw [ground.beqEqOf (show (x == y) = true from h1)]
    exact h2

/-! The two theorems routed at the interface value holding the four
label reads: the network at the count `1` is occupied, its four
two-valent pair reads hold, and the index is its own spread. -/

example :
    ((Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 0) Fid.unit = true
        ∧ Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 1) Fid.unit = true)
      ∨ (Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 0) Fid.unit = false
        ∧ Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 1) Fid.unit = false
        ∧ Fid.eqL (Fid.dual (ground.getAt Fid.unit (netConf 1 1 1) 0))
            (Fid.dual (ground.getAt Fid.unit (netConf 1 1 1) 1)) = true))
  ∧ ((Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 1) Fid.unit = true
        ∧ Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 2) Fid.unit = true)
      ∨ (Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 1) Fid.unit = false
        ∧ Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 2) Fid.unit = false
        ∧ Fid.eqL (Fid.dual (ground.getAt Fid.unit (netConf 1 1 1) 1))
            (Fid.dual (ground.getAt Fid.unit (netConf 1 1 1) 2)) = true))
  ∧ ((Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 4) Fid.unit = true
        ∧ Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 5) Fid.unit = true)
      ∨ (Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 4) Fid.unit = false
        ∧ Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 5) Fid.unit = false
        ∧ Fid.eqL (Fid.dual (ground.getAt Fid.unit (netConf 1 1 1) 4))
            (Fid.dual (ground.getAt Fid.unit (netConf 1 1 1) 5)) = true))
  ∧ ((Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 5) Fid.unit = true
        ∧ Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 6) Fid.unit = true)
      ∨ (Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 5) Fid.unit = false
        ∧ Fid.eqL (ground.getAt Fid.unit (netConf 1 1 1) 6) Fid.unit = false
        ∧ Fid.eqL (Fid.dual (ground.getAt Fid.unit (netConf 1 1 1) 5))
            (Fid.dual (ground.getAt Fid.unit (netConf 1 1 1) 6)) = true)) :=
  pathReads Fid hduF (netConf 1 1 1) (by decide +kernel)

example : carrier.eqConf Fid (netConf 1 1 1)
    (netConf (ground.getAt Fid.unit (netConf 1 1 1) 0)
      (ground.getAt Fid.unit (netConf 1 1 1) 3)
      (ground.getAt Fid.unit (netConf 1 1 1) 4)) = true :=
  netConf_det Fid hduF hdcF huuF htrF (netConf 1 1 1) (by decide +kernel)
    (by decide +kernel)

/-! The binder refusals, one interface value per label read.  The
involution at the unit label refuses `hdu`, and the occupied
configuration `[1, 0, 0, 1, 2, 2, 2]` reads its first path's first
two links at one occupied link beside a link at the unit, the pair
read refused there. -/

example : Fdu.eqL (Fdu.dual 1) Fdu.unit = true := by decide +kernel
example : Fdu.eqL 1 Fdu.unit = false := by decide +kernel
example : carrier.occupied Fdu lattice.thetaG [1, 0, 0, 1, 2, 2, 2] = true := by
  decide +kernel

example : ¬
  ((Fdu.eqL
        (ground.getAt Fdu.unit [1, 0, 0, 1, 2, 2, 2] 0)
        Fdu.unit = true
      ∧ Fdu.eqL
        (ground.getAt Fdu.unit [1, 0, 0, 1, 2, 2, 2] 1)
        Fdu.unit = true)
    ∨ (Fdu.eqL
        (ground.getAt Fdu.unit [1, 0, 0, 1, 2, 2, 2] 0)
        Fdu.unit = false
      ∧ Fdu.eqL
        (ground.getAt Fdu.unit [1, 0, 0, 1, 2, 2, 2] 1)
        Fdu.unit = false
      ∧ Fdu.eqL
        (Fdu.dual
          (ground.getAt Fdu.unit [1, 0, 0, 1, 2, 2, 2] 0))
        (Fdu.dual
          (ground.getAt Fdu.unit [1, 0, 0, 1, 2, 2, 2] 1))
        = true)) := by decide +kernel

/-! The involution at the count `1` refuses `hdc`: the occupied
configuration `[1, 1, 2, 1, 1, 1, 1]` reads its third link at a
label apart from its second's, and the index refuses its own
spread. -/

example : Fdc.eqL (Fdc.dual 1) (Fdc.dual 2) = true := by decide +kernel
example : Fdc.eqL 2 1 = false := by decide +kernel
example : carrier.occupied Fdc lattice.thetaG [1, 1, 2, 1, 1, 1, 1] = true := by
  decide +kernel
example : carrier.eqConf Fdc [1, 1, 2, 1, 1, 1, 1]
    (netConf (ground.getAt Fdc.unit [1, 1, 2, 1, 1, 1, 1] 0)
      (ground.getAt Fdc.unit [1, 1, 2, 1, 1, 1, 1] 3)
      (ground.getAt Fdc.unit [1, 1, 2, 1, 1, 1, 1] 4))
      = false := by decide +kernel

/-! The joining equality refuses `huu` at the label pair `(3, 4)`
and `htr` at `(3, 0, 4)`: every link of `[3, 3, 4, 3, 3, 3, 3]`
reads at the unit label, so the incident lists are withdrawn at
every vertex and the configuration is occupied, while its third
link and its second read apart and the index refuses its own
spread. -/

example : Fuu.eqL 3 Fuu.unit = true := by decide +kernel
example : Fuu.eqL 4 Fuu.unit = true := by decide +kernel
example : Fuu.eqL 4 3 = false := by decide +kernel
example : Fuu.eqL 3 Fuu.unit = true ∧ Fuu.eqL Fuu.unit 4 = true
    ∧ Fuu.eqL 3 4 = false := by decide +kernel
example : carrier.occupied Fuu lattice.thetaG [3, 3, 4, 3, 3, 3, 3] = true := by
  decide +kernel
example : carrier.eqConf Fuu [3, 3, 4, 3, 3, 3, 3]
    (netConf (ground.getAt Fuu.unit [3, 3, 4, 3, 3, 3, 3] 0)
      (ground.getAt Fuu.unit [3, 3, 4, 3, 3, 3, 3] 3)
      (ground.getAt Fuu.unit [3, 3, 4, 3, 3, 3, 3] 4))
      = false := by decide +kernel

/-! The three occupancy binders of `netConf_vmult`: at the middle
label the unit both three-valent vertices read `0` while the
three-label counts read `1`, the unit label entering the count's own
row fold and withdrawn from the incident list. -/

example : Fid.eqL 0 Fid.unit = true := by decide +kernel
example : Fid.eqL 2 Fid.unit = false ∧ Fid.eqL 1 Fid.unit = false := by
  decide +kernel
example : carrier.vmult Fid lattice.thetaG (netConf 2 0 1) 0 = 0 := by decide +kernel
example : carrier.invCount Fid [2, Fid.dual 0, Fid.dual 1] = 1 := by decide +kernel
example : carrier.vmult Fid lattice.thetaG (netConf 2 0 1) 3 = 0 := by decide +kernel
example : carrier.invCount Fid [Fid.dual 2, 0, 1] = 1 := by decide +kernel

/-! The resolvent factor's composition at the `θ` channel of the
width two: the weight pair against the factor reads the
self-energy's own term, the products' display. -/

example : (match resFactor (dataA 2) (adjchar.theta 2) with
    | some f => decide ((Pair.mk (posOfSucc 2) (posOfSucc 8) * f).oneValue
        (Pair.mk (posOfSucc 23) (posOfSucc 215)))
    | none => false) = true := by decide +kernel

/-! The projected states compute at the collected key lists: each
state twenty-four wirings, the magnetic image forty-eight, and the
identity wiring's coefficient occupied. -/

example : (chanState 0).length = 24 := by decide +kernel

example : (chanState 1).length = 24 := by decide +kernel

example : (twoplaq.mulAdj (chanState 0)).length = 48 := by decide +kernel

example : genericlift.pairOcc
    (states.coeffAtW (chanState 1) [0, 1, 2, 3]) := by decide +kernel

/-! Two further label equalities, one per remaining law read.  The
chaining equality joins the counts `3, 4` and `4, 5` at both
orders over the identity involution: the involution reads and the
unit reads hold while the transitive read is refused at
`(3, 4, 5)`, and the occupied configuration `[3, 4, 5, 1, 1, 1, 1]`
refuses the determination. -/

private def eqChain (x y : Nat) : Bool :=
  x == y || (x == 3 && y == 4) || (x == 4 && y == 3)
    || (x == 4 && y == 5) || (x == 5 && y == 4)

private theorem eqChainRefl (l : Nat) : eqChain l l = true := by
  show ((l == l) || (l == 3 && l == 4) || (l == 4 && l == 3)
    || (l == 4 && l == 5) || (l == 5 && l == 4)) = true
  rw [show (l == l) = true from ground.eqBeqOf rfl]
  exact rfl

private def Fch : fusion.Data Nat := trivF eqChain (fun x => x) eqChainRefl

example : Fch.eqL 3 4 = true ∧ Fch.eqL 4 5 = true
    ∧ Fch.eqL 3 5 = false := by decide +kernel
example : ((List.range 7).all (fun x =>
    !(Fch.eqL (Fch.dual x) Fch.unit) || Fch.eqL x Fch.unit))
      = true := by decide +kernel
example : ((List.range 7).all (fun x => (List.range 7).all (fun y =>
    !(Fch.eqL (Fch.dual x) (Fch.dual y)) || Fch.eqL y x)))
      = true := by decide +kernel
example : ((List.range 7).all (fun x => (List.range 7).all (fun y =>
    !(Fch.eqL x Fch.unit) || (!(Fch.eqL y Fch.unit)
      || Fch.eqL y x)))) = true := by decide +kernel
example : carrier.occupied Fch lattice.thetaG [3, 4, 5, 1, 1, 1, 1] = true := by
  decide +kernel
example : carrier.eqConf Fch [3, 4, 5, 1, 1, 1, 1]
    (netConf (ground.getAt Fch.unit [3, 4, 5, 1, 1, 1, 1] 0)
      (ground.getAt Fch.unit [3, 4, 5, 1, 1, 1, 1] 3)
      (ground.getAt Fch.unit [3, 4, 5, 1, 1, 1, 1] 4))
      = false := by decide +kernel

/-! The upward equality joins the counts `3` and `4` to the unit
label at one order over the raised involution `x + 6`: the
involution reads and the transitive read hold while the unit
labels' read is refused at `(3, 4)`, and the occupied
configuration `[3, 3, 4, 3, 3, 3, 3]` refuses the
determination. -/

private def eqUp (x y : Nat) : Bool :=
  x == y || (x == 3 && y == 0) || (x == 4 && y == 0)

private theorem eqUpRefl (l : Nat) : eqUp l l = true := by
  show ((l == l) || (l == 3 && l == 0) || (l == 4 && l == 0)) = true
  rw [show (l == l) = true from ground.eqBeqOf rfl]
  exact rfl

private def Fup : fusion.Data Nat := trivF eqUp (fun x => x + 6) eqUpRefl

example : Fup.eqL 3 Fup.unit = true ∧ Fup.eqL 4 Fup.unit = true
    ∧ Fup.eqL 4 3 = false := by decide +kernel
example : ((List.range 17).all (fun x =>
    !(Fup.eqL (Fup.dual x) Fup.unit) || Fup.eqL x Fup.unit))
      = true := by decide +kernel
example : ((List.range 17).all (fun x => (List.range 17).all (fun y =>
    !(Fup.eqL (Fup.dual x) (Fup.dual y)) || Fup.eqL y x)))
      = true := by decide +kernel
example : ((List.range 7).all (fun x => (List.range 7).all (fun y =>
    (List.range 7).all (fun z =>
      !(Fup.eqL x y) || (!(Fup.eqL y z) || Fup.eqL x z)))))
      = true := by decide +kernel
example : carrier.occupied Fup lattice.thetaG [3, 3, 4, 3, 3, 3, 3] = true := by
  decide +kernel
example : carrier.eqConf Fup [3, 3, 4, 3, 3, 3, 3]
    (netConf (ground.getAt Fup.unit [3, 3, 4, 3, 3, 3, 3] 0)
      (ground.getAt Fup.unit [3, 3, 4, 3, 3, 3, 3] 3)
      (ground.getAt Fup.unit [3, 3, 4, 3, 3, 3, 3] 4))
      = false := by decide +kernel

/-! The multiplicity theorem's first and third occupied binders:
at a unit first or second path label the three-valent counts part
from the three-label reads, one exhibit each beside the middle
label's own above. -/

example : carrier.vmult Fid lattice.thetaG (netConf 0 2 1) 0 = 0 := by decide +kernel
example : carrier.invCount Fid [0, Fid.dual 2, Fid.dual 1] = 1 := by decide +kernel
example : carrier.vmult Fid lattice.thetaG (netConf 1 2 0) 0 = 0 := by decide +kernel
example : carrier.invCount Fid [1, Fid.dual 2, Fid.dual 0] = 1 := by decide +kernel
