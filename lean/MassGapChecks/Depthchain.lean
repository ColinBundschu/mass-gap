import MassGap.Depthchain
import MassGap.Network
/-!
`con:depthchain`'s batteries.  At a three-key walk of one term with
one position per member: the members joined along the walk, the
depths from the base `0` reading `0, 1, 2`, the shells one member
each, the depth order the walk's own and the matrix along it the
walk itself; the slab data the walk's own entries at the slab
shape, the off-band read holding, and the assembly read decided
beside its theorem route; the joined step's depth read beside its
theorem route, and the join binder isolated: the walk's two ends
are joined to neither, and the far end's depth exceeds the base's
successor.  The assembly's binders isolated: at a shell list off
the depth order the off-band read refuses and the assembled slabs
part from the matrix, and at an asymmetric matrix the bond's
exchange parts the assembly from the matrix at the off-band read
holding.  The walk's closure: every reached member's depth sits
below the count and every reached member sits in its listed shell,
the theorem routes beside the decided reads, and the cross read
refused at a matrix coupling two members the walk does not join.
The fusion walk's reach (`lem:cornerkey`'s near mass): at the window
`(𝟏, θ, (4, 0))` of `dataA 2` the walk reads the third key off the
sum's unit at two steps and the reach read holds there, decided and
through the theorem, while at one step the key sits at the unit and
the reach read refuses.
-/

namespace depthchain

namespace depthchainChecks
open ground elim

private def u : BPair := BPair.unit
private def w3 : Mat :=
  [[u, ⟨2, 1⟩, u], [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨3, 1⟩]]
private def p3 : List (List Nat) := [[0], [1], [2]]

theorem pin1 : joinedAt [w3] 0 1 = true := by decide +kernel
theorem pin2 : joined [w3] p3 0 1 = true := by decide +kernel
theorem pin3 : joined [w3] p3 1 2 = true := by decide +kernel
theorem pin4 : joined [w3] p3 0 2 = false := by decide +kernel
theorem pin5 : reach [w3] p3 3 [0] 1 = [0, 1] := by decide +kernel
theorem pin6 : reach [w3] p3 3 [0] 2 = [0, 1, 2] := by decide +kernel
theorem pin7 : depthOf [w3] p3 3 [0] 0 = 0 := by decide +kernel
theorem pin8 : depthOf [w3] p3 3 [0] 1 = 1 := by decide +kernel
theorem pin9 : depthOf [w3] p3 3 [0] 2 = 2 := by decide +kernel
theorem pin10 : shell [w3] p3 3 [0] 1 = [1] := by decide +kernel
theorem pin11 : shells [w3] p3 3 [0] = [[0], [1], [2]] := by decide +kernel
theorem pin12 : posShells [w3] p3 3 [0] = [[0], [1], [2]] := by decide +kernel
theorem pin13 : depthOrder [w3] p3 3 [0] = [0, 1, 2] := by decide +kernel
theorem pin14 : selM (depthOrder [w3] p3 3 [0]) (depthOrder [w3] p3 3 [0]) w3 = w3 := by
  decide +kernel

theorem pin15 : depthOf [w3] p3 3 [0] 2 ≤ depthOf [w3] p3 3 [0] 1 + 1 :=
  depth_step [w3] p3 3 [0] 2 1 (by decide) (by decide +kernel)
theorem pin16 : joined [w3] p3 0 1 = joined [w3] p3 1 0 :=
  joined_symm [w3] p3 3 (by decide +kernel) (by decide +kernel) 0 1

/-! The walk's closure at the three-key walk: every member's depth
below the count and every member in its listed shell, decided and
through the theorems; and a fourth member off the walk sits at the
budget's cap, off every listed shell. -/

theorem pin17 : depthOf [w3] p3 3 [0] 2 < 3 :=
  depth_lt [w3] p3 3 [0] (by decide +kernel) (by decide +kernel) (by decide)
    2 2 (by decide +kernel)
theorem pin18 : 2 ∈ ground.getAt [] (shells [w3] p3 3 [0]) (depthOf [w3] p3 3 [0] 2) :=
  mem_shells [w3] p3 3 [0] (by decide +kernel) (by decide +kernel) (by decide)
    2 2 (by decide) (by decide +kernel)
theorem pin19 : 0 < (shell [w3] p3 3 [0] 1).length :=
  shell_contiguous [w3] p3 3 [0] (by decide +kernel) 1 2 (by decide)
    (ground.mem_of_countOf_pos _ _ (by decide +kernel))

private def w4 : Mat :=
  [[u, ⟨2, 1⟩, u, u], [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, u], [u, ⟨2, 1⟩, ⟨3, 1⟩, u],
   [u, u, u, ⟨3, 1⟩]]
private def p4 : List (List Nat) := [[0], [1], [2], [3]]

theorem pin20 : depthOf [w4] p4 4 [0] 3 = 4 := by decide +kernel
theorem pin21 : shells [w4] p4 4 [0] = [[0], [1], [2]] := by decide +kernel
theorem pin22 : (List.range 4).all (fun k => !reachB [w4] p4 4 [0] k 3) = true := by
  decide +kernel

/-! The slab data along the walk's shells: the diagonal blocks the
walk's own entries, the bonds its unit bonds, the slab shape at the
orders one each, the off-band read holding, and the assembly read
decided beside its theorem route. -/

theorem pin23 : slabDiag w3 (posShells [w3] p3 3 [0]) = [[[u]], [[⟨3, 1⟩]], [[⟨3, 1⟩]]] := by
  decide +kernel
theorem pin24 : slabOff w3 (posShells [w3] p3 3 [0]) = [[[⟨2, 1⟩]], [[⟨2, 1⟩]]] := by
  decide +kernel
theorem pin25 : greenprod.slabShape (slabDiag w3 (posShells [w3] p3 3 [0]))
    (slabOff w3 (posShells [w3] p3 3 [0])) [1, 1, 1] := by decide +kernel
theorem pin26 : greenprod.slabShape (slabDiag w3 (posShells [w3] p3 3 [0]))
    (slabOff w3 (posShells [w3] p3 3 [0]))
    ((posShells [w3] p3 3 [0]).map List.length) :=
  slabs_shape w3 (posShells [w3] p3 3 [0]) (by decide +kernel) (by decide +kernel)
theorem pin27 : offBandB w3 (posShells [w3] p3 3 [0]) = true := by decide +kernel
theorem pin28 : crossB [w3] p3 w3 = true := by decide +kernel
theorem pin29 : matOneValue (selM (depthOrder [w3] p3 3 [0]) (depthOrder [w3] p3 3 [0]) w3)
    (greenprod.assemble (slabDiag w3 (posShells [w3] p3 3 [0]))
      (slabOff w3 (posShells [w3] p3 3 [0]))) := by decide +kernel
theorem pin30 : matOneValue (selM (depthOrder [w3] p3 3 [0]) (depthOrder [w3] p3 3 [0]) w3)
    (greenprod.assemble (slabDiag w3 (posShells [w3] p3 3 [0]))
      (slabOff w3 (posShells [w3] p3 3 [0]))) :=
  depth_assemble [w3] p3 3 [0] 3 (by decide +kernel) (by decide +kernel)
    (by decide) rfl w3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin31 : crossB [w3] p3 (msum 3 (ground.getAt [] [w3]) (List.range 1)) = true :=
  msum_cross [w3] p3 3 (by decide +kernel) (by decide +kernel)
theorem pin32 : crossB [w3] p3 (elim.idMat 3) = true :=
  memberDiag_cross [w3] p3 (elim.idMat 3) (by decide +kernel)

/-! The join binder isolated: the two ends of the walk are joined to
neither, and the far end's depth sits beyond the base's successor. -/

theorem pin33 : ¬ (depthOf [w3] p3 3 [0] 2 ≤ depthOf [w3] p3 3 [0] 0 + 1) := by
  decide +kernel

/-! The assembly's binders isolated.  At the shell list `[[0], [2], [1]]`,
off the depth order, the off-band read refuses (the walk's bond
`(0, 1)` sits two shells apart) and the assembled slabs part from
the matrix along the joined keys, the assembly theorem's own route
at the depth order beside it; at an asymmetric matrix at two shells,
the off-band read holding, the assembly's exchanged bond parts from
the matrix's own; and the cross read refuses at a matrix coupling
the walk's two ends, which the walk's terms do not join, the
assembly parting there. -/

theorem pin34 : offBandB w3 [[0], [2], [1]] = false := by decide +kernel
theorem pin35 : ¬ matOneValue (selM ([[0], [2], [1]].flatMap (fun s => s))
      ([[0], [2], [1]].flatMap (fun s => s)) w3)
    (greenprod.assemble (slabDiag w3 [[0], [2], [1]])
      (slabOff w3 [[0], [2], [1]])) := by decide +kernel
theorem pin36 : matOneValue (selM ([[0], [1], [2]].flatMap (fun s => s))
      ([[0], [1], [2]].flatMap (fun s => s)) w3)
    (greenprod.assemble (slabDiag w3 [[0], [1], [2]])
      (slabOff w3 [[0], [1], [2]])) :=
  chain_assemble w3 3 (by decide +kernel) (by decide +kernel) [[0], [1], [2]]
    (by decide) (by decide) (by decide +kernel)

private def wA : Mat := [[u, ⟨2, 1⟩], [⟨3, 1⟩, u]]

theorem pin37 : offBandB wA [[0], [1]] = true := by decide +kernel
theorem pin38 : ¬ matOneValue (transposeM wA) wA := by decide +kernel
theorem pin39 : ¬ matOneValue (selM ([[0], [1]].flatMap (fun s => s))
      ([[0], [1]].flatMap (fun s => s)) wA)
    (greenprod.assemble (slabDiag wA [[0], [1]])
      (slabOff wA [[0], [1]])) := by decide +kernel

private def wX : Mat :=
  [[u, ⟨2, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩]]

theorem pin40 : crossB [w3] p3 wX = false := by decide +kernel
theorem pin41 : ¬ matOneValue (selM (depthOrder [w3] p3 3 [0]) (depthOrder [w3] p3 3 [0]) wX)
    (greenprod.assemble (slabDiag wX (posShells [w3] p3 3 [0]))
      (slabOff wX (posShells [w3] p3 3 [0]))) := by decide +kernel

end depthchainChecks

/-! The one-plaquette window's unit sector at two letters: the index
at the cutoff `96` the two loops at the tower labels `θ` and `2θ`,
the depth chain's shells the labels at one fusion depth from the
unit label, and the walk's band-one head the chain itself at the
residue one, the diagonal `c₁ = 1` at every tower label with the
vacuum defect; at three letters the unit sector's depth-two shell
holds the two further channels beside `2θ`, and the walk's head is
the depth chain's compression to the tower powers, the diagonal
`c₁ = 2` there.  The three-letter loop member reads entry by entry
at the fusion counts, the vacuum column at the adjoint row of the
unit label through the row law (`fusion.rowLaw_dataA`, the
unit-column counts off the row). -/

namespace square
open ground elim lattice fusion carrier

private def u : BPair := BPair.unit
private def fS : Data places.Shape := tabulate (xData (dataA 2)) 96
private def sqIx : List (List places.Shape) :=
  [[[2, 0], [2, 0], [2, 0], [2, 0]], [[4, 0], [4, 0], [4, 0], [4, 0]]]

private theorem sqIxPin : idx fS lattice.square 96 = sqIx := by
  rw [← idxA_eq]; decide +kernel

theorem pin42 : pairpencil.slotDiag fS lattice.square (idx fS lattice.square 96)
    = [0, 32, 96] := by
  rw [sqIxPin]; decide +kernel

private def mSq : Mat := pairpencil.loopMag (dataA 2) [[2, 0], [4, 0]]
private def p3 : List (List Nat) := [[0], [1], [2]]

theorem pin43 : mSq = [[u, ⟨2, 1⟩, u], [⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨2, 1⟩]] := by
  decide +kernel
theorem pin44 : shells [mSq] p3 3 [0] = [[0], [1], [2]] := by decide +kernel
theorem pin45 : slabDiag mSq (posShells [mSq] p3 3 [0]) = [[[u]], [[⟨2, 1⟩]], [[⟨2, 1⟩]]] := by
  decide +kernel
theorem pin46 : slabOff mSq (posShells [mSq] p3 3 [0]) = [[[⟨2, 1⟩]], [[⟨2, 1⟩]]] := by
  decide +kernel
theorem pin47 : matOneValue (selM (depthOrder [mSq] p3 3 [0]) (depthOrder [mSq] p3 3 [0]) mSq)
    (greenprod.assemble (slabDiag mSq (posShells [mSq] p3 3 [0]))
      (slabOff mSq (posShells [mSq] p3 3 [0]))) :=
  depth_assemble [mSq] p3 3 [0] 3 (by decide +kernel) (by decide +kernel)
    (by decide) rfl mSq (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The three-letter loop member at the unit sector's labels through
the fusion depth two: the vacuum column read at the unit label's
adjoint row, `[θ]`, through the row law, and the further entries at
the fusion counts, each one read; the member assembled entry by
entry. -/

private def th3 : places.Shape := adjchar.theta 3
private def l2 : places.Shape := [2, 2, 0]
private def l3 : places.Shape := [3, 0, 0]
private def l4 : places.Shape := [0, 3, 0]
private def v0 : places.Shape := [0, 0, 0]

private theorem rowUnit : (dataA 3).row th3 v0 = [th3] := by decide +kernel

/-- A unit-column count off the adjoint row of the unit label reads
the sum's unit, the row law's read at the pinned row. -/
private theorem countUnitOff (x : places.Shape) (hx : x.length = 3)
    (hred : labels.reduce x = x) (hoff : countOf x [th3] = 0) :
    (dataA 3).count th3 v0 x = 0 := by
  have h := rowLaw_dataA 3 th3 v0 x rfl hx rfl hred
  cases Nat.eq_zero_or_pos ((dataA 3).count th3 v0 x) with
  | inl h0 => exact h0
  | inr hp =>
    have hc := h.1.mp hp
    rw [rowUnit, hoff] at hc
    exact absurd hc (Nat.lt_irrefl 0)

private theorem c02 : (dataA 3).count th3 v0 l2 = 0 :=
  countUnitOff l2 rfl (by decide +kernel) (by decide +kernel)
private theorem c04 : (dataA 3).count th3 v0 l4 = 0 :=
  countUnitOff l4 rfl (by decide +kernel) (by decide +kernel)

private def mSq3 : Mat := pairpencil.loopMag (dataA 3) [th3, l2, l3, l4]
private def mSq3L : Mat :=
  [[u, ⟨2, 1⟩, u, u, u],
   [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩],
   [u, ⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩],
   [u, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩, u],
   [u, ⟨2, 1⟩, ⟨2, 1⟩, u, ⟨2, 1⟩]]

private theorem mSq3Pin : mSq3 = mSq3L := by
  show [[BPair.ofNat ((dataA 3).count th3 v0 v0), BPair.ofNat ((dataA 3).count th3 th3 v0),
         BPair.ofNat ((dataA 3).count th3 l2 v0), BPair.ofNat ((dataA 3).count th3 l3 v0),
         BPair.ofNat ((dataA 3).count th3 l4 v0)],
        [BPair.ofNat ((dataA 3).count th3 v0 th3), BPair.ofNat ((dataA 3).count th3 th3 th3),
         BPair.ofNat ((dataA 3).count th3 l2 th3), BPair.ofNat ((dataA 3).count th3 l3 th3),
         BPair.ofNat ((dataA 3).count th3 l4 th3)],
        [BPair.ofNat ((dataA 3).count th3 v0 l2), BPair.ofNat ((dataA 3).count th3 th3 l2),
         BPair.ofNat ((dataA 3).count th3 l2 l2), BPair.ofNat ((dataA 3).count th3 l3 l2),
         BPair.ofNat ((dataA 3).count th3 l4 l2)],
        [BPair.ofNat ((dataA 3).count th3 v0 l3), BPair.ofNat ((dataA 3).count th3 th3 l3),
         BPair.ofNat ((dataA 3).count th3 l2 l3), BPair.ofNat ((dataA 3).count th3 l3 l3),
         BPair.ofNat ((dataA 3).count th3 l4 l3)],
        [BPair.ofNat ((dataA 3).count th3 v0 l4), BPair.ofNat ((dataA 3).count th3 th3 l4),
         BPair.ofNat ((dataA 3).count th3 l2 l4), BPair.ofNat ((dataA 3).count th3 l3 l4),
         BPair.ofNat ((dataA 3).count th3 l4 l4)]] = mSq3L
  rw [c02, c04]
  decide +kernel

theorem pin48 : (dataA 3).row th3 th3 = [l2, l4, l3, th3, v0] := by decide +kernel
theorem pin49 : shells [mSq3L] [[0], [1], [2], [3], [4]] 5 [0] = [[0], [1], [2, 3, 4]] := by
  decide +kernel
theorem pin50 : selM [0, 1, 2] [0, 1, 2] mSq3L
    = [[u, ⟨2, 1⟩, u], [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩], [u, ⟨2, 1⟩, ⟨3, 1⟩]] := by
  decide +kernel
theorem pin51 : slabOff mSq3L (posShells [mSq3L] [[0], [1], [2], [3], [4]] 5 [0])
    = [[[⟨2, 1⟩]], [[⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩]]] := by decide +kernel
theorem pin52 : matOneValue
    (selM (depthOrder [mSq3] [[0], [1], [2], [3], [4]] 5 [0])
      (depthOrder [mSq3] [[0], [1], [2], [3], [4]] 5 [0]) mSq3)
    (greenprod.assemble (slabDiag mSq3 (posShells [mSq3] [[0], [1], [2], [3], [4]] 5 [0]))
      (slabOff mSq3 (posShells [mSq3] [[0], [1], [2], [3], [4]] 5 [0]))) := by
  rw [mSq3Pin]
  exact depth_assemble [mSq3L] [[0], [1], [2], [3], [4]] 5 [0] 5 (by decide +kernel)
    (by decide +kernel) (by decide) rfl mSq3L (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end square

/-! The theta graph's `X`-sector at the residue one and the cutoff
`48`: the window index at the unit class's alphabet pinned at its
three occupied members (the two single plaquettes at the content
`32` and the two plaquettes at the unit shared link, the outer loop,
at `48`), the gram the identity at the clearing one, and the two
plaquette terms at the clearing three, the positions the index's
(the vacuum, the second plaquette, the outer loop, the first
plaquette), each term's support the changed-edge rows' and its
entries the loop reads at its own plaquette (the vacuum's bond one
and the diagonal `c₁ = 1`, the fusion count at the residue one),
the outer loop's diagonal the sum's unit (the shared link sits off
its own plaquette rows), and the other plaquette's bond to the outer
loop the presentation's pairing of the module pair against the
outer loop's adjoint character `χ_θ(UV)`, `[1 : r(r + 2)]` at every
residue and `[1 : 3]` at the residue one, the outer loop's
self-pairing one.  The depth chain from the unit's line: the two
single plaquettes at depth one and the outer loop at depth two, the
shells `[0], [1, 3], [2]`, the joined step's read beside its theorem
route; the magnetic member the terms' sum with its cross read the
terms' own; the gram and the electric member's form at the fibers'
orthogonal sum; the slab data at the three shells with the assembly
read beside its theorem route; and the pencil's site datum at the
dual representative `[1 : 12]` and the level one, cleared at twelve,
assembled from its slabs along the shells. -/

namespace theta
open ground elim lattice fusion carrier poly states twoplaq network
  genericlift

private def u : BPair := BPair.unit
private def fX : Data places.Shape := tabulate (xData (dataA 2)) 48
private def thIx : List (List places.Shape) :=
  [[[0, 0], [0, 0], [0, 0], [2, 0], [2, 0], [2, 0], [2, 0]],
   [[2, 0], [2, 0], [2, 0], [0, 0], [2, 0], [2, 0], [2, 0]],
   [[2, 0], [2, 0], [2, 0], [2, 0], [0, 0], [0, 0], [0, 0]]]
private def p4 : List (List Nat) := [[0], [1], [2], [3]]

private theorem thIxPin : idx fX lattice.thetaG 48 = thIx := by
  rw [← idxA_eq]; decide +kernel

theorem pin53 : pairpencil.slotDiag fX lattice.thetaG (idx fX lattice.thetaG 48)
    = [0, 32, 48, 32] := by
  rw [thIxPin]; decide +kernel
theorem pin54 : pairpencil.gramBlockRead fX lattice.thetaG 4 thIx 1 (elim.idMat 4) := by
  decide +kernel

/-! The terms' supports at the changed-edge rows, one term per
plaquette. -/

private def thSupp (p : List (Nat × Bool)) : Mat :=
  ground.matOf 4 4 (fun i j =>
    if carrier.confMem fX (pairpencil.posConf fX lattice.thetaG thIx j)
        (algebra.plaqRow fX lattice.thetaG p
          (pairpencil.posConf fX lattice.thetaG thIx i))
      || carrier.confMem fX (pairpencil.posConf fX lattice.thetaG thIx i)
        (algebra.plaqRow fX lattice.thetaG p
          (pairpencil.posConf fX lattice.thetaG thIx j))
    then ⟨2, 1⟩ else BPair.unit)
private def suppT : List Mat :=
  lattice.thetaG.plaqs.map thSupp

/-- The first plaquette's term at the clearing three: the vacuum's
bond and the diagonal at the first plaquette, the second plaquette's
bond to the outer loop. -/
private def t1 : Mat :=
  [[u, u, u, ⟨4, 1⟩],
   [u, u, ⟨2, 1⟩, u],
   [u, ⟨2, 1⟩, u, u],
   [⟨4, 1⟩, u, u, ⟨4, 1⟩]]

/-- The second plaquette's term at the clearing three. -/
private def t2 : Mat :=
  [[u, ⟨4, 1⟩, u, u],
   [⟨4, 1⟩, ⟨4, 1⟩, u, u],
   [u, u, u, ⟨2, 1⟩],
   [u, u, ⟨2, 1⟩, u]]

private def tTh : List Mat := [t1, t2]

theorem pin55 : ((List.range 4).all (fun i => (List.range 4).all (fun j =>
    joinedAt tTh i j == joinedAt suppT i j))) = true := by decide +kernel
theorem pin56 : ((List.range 2).all (fun q => (List.range 4).all (fun i =>
    (List.range 4).all (fun j =>
      joinedAt [ground.getAt [] tTh q] i j
        == joinedAt [ground.getAt [] suppT q] i j)))) = true := by decide +kernel

/-! The terms' entries.  The single plaquettes read the loop
window's fusion matrix at the residue one, and the outer loop's
bond and self-pairing read in the presentation: the outer loop's
adjoint character at the two-plaquette site, its self-pairing one
and its pairing against the module pair `[1 : r(r + 2)]`, read at
the residue one as `[1 : 3]`. -/

theorem pin57 : pairpencil.loopMag (dataA 2) [[2, 0]] = [[u, ⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]] := by
  decide +kernel

private def outC : Comb :=
  [([2, 3, 0, 1], pOne), ([1, 0, 3, 2], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩]))]
private def bondP : PPair := ([⟨2, 1⟩], [⟨1, 1⟩, ⟨3, 1⟩, ⟨2, 1⟩])

theorem pin58 : crossNull (fiber.pairP siteQ12 siteQ12 outC outC) pOne := by
  decide +kernel
theorem pin59 : crossNull (fiber.pairP siteQ12 siteQ12 outC q12) bondP := by
  decide +kernel
theorem pin60 : agreeAt bondP ([⟨2, 1⟩], [⟨4, 1⟩]) (BPair.ofNat 1) := by decide +kernel
theorem pin61 : ¬ agreeAt bondP ([⟨2, 1⟩], [⟨2, 1⟩]) (BPair.ofNat 1) := by decide +kernel

/-! The depth chain at the two terms. -/

private def mTh : Mat := msum 4 (ground.getAt [] tTh) (List.range 2)

theorem pin62 : matOneValue mTh [[u, ⟨4, 1⟩, u, ⟨4, 1⟩], [⟨4, 1⟩, ⟨4, 1⟩, ⟨2, 1⟩, u],
    [u, ⟨2, 1⟩, u, ⟨2, 1⟩], [⟨4, 1⟩, u, ⟨2, 1⟩, ⟨4, 1⟩]] := by decide +kernel
theorem pin63 : joined tTh p4 0 1 = true := by decide +kernel
theorem pin64 : joined tTh p4 0 3 = true := by decide +kernel
theorem pin65 : joined tTh p4 0 2 = false := by decide +kernel
theorem pin66 : joined tTh p4 1 2 = true := by decide +kernel
theorem pin67 : joined tTh p4 1 3 = false := by decide +kernel
theorem pin68 : joined tTh p4 2 2 = false := by decide +kernel
theorem pin69 : (List.range 4).map (fun a => depthOf tTh p4 4 [0] a) = [0, 1, 2, 1] := by
  decide +kernel
theorem pin70 : shells tTh p4 4 [0] = [[0], [1, 3], [2]] := by
  decide +kernel
theorem pin71 : depthOrder tTh p4 4 [0] = [0, 1, 3, 2] := by decide +kernel
theorem pin72 : depthOf tTh p4 4 [0] 1 ≤ depthOf tTh p4 4 [0] 0 + 1 :=
  depth_step tTh p4 4 [0] 1 0 (by decide) (by decide +kernel)

theorem pin73 : crossB tTh p4 mTh = true := by decide +kernel
theorem pin74 : crossB tTh p4 mTh = true :=
  msum_cross tTh p4 4 (by decide +kernel) (by decide +kernel)
theorem pin75 : matOneValue (ground.getAt [] (slabDiag mTh (posShells tTh p4 4 [0])) 0)
    [[u]] := by decide +kernel
theorem pin76 : matOneValue (ground.getAt [] (slabDiag mTh (posShells tTh p4 4 [0])) 1)
    [[⟨4, 1⟩, u], [u, ⟨4, 1⟩]] := by decide +kernel
theorem pin77 : matOneValue (ground.getAt [] (slabDiag mTh (posShells tTh p4 4 [0])) 2)
    [[u]] := by decide +kernel
theorem pin78 : matOneValue (ground.getAt [] (slabOff mTh (posShells tTh p4 4 [0])) 0)
    [[⟨4, 1⟩, ⟨4, 1⟩]] := by decide +kernel
theorem pin79 : matOneValue (ground.getAt [] (slabOff mTh (posShells tTh p4 4 [0])) 1)
    [[⟨2, 1⟩], [⟨2, 1⟩]] := by decide +kernel
theorem pin80 : greenprod.slabShape (slabDiag mTh (posShells tTh p4 4 [0]))
    (slabOff mTh (posShells tTh p4 4 [0])) [1, 2, 1] := by decide +kernel
theorem pin81 : matOneValue (selM (depthOrder tTh p4 4 [0]) (depthOrder tTh p4 4 [0]) mTh)
    (greenprod.assemble (slabDiag mTh (posShells tTh p4 4 [0]))
      (slabOff mTh (posShells tTh p4 4 [0]))) := by decide +kernel
theorem pin82 : matOneValue (selM (depthOrder tTh p4 4 [0]) (depthOrder tTh p4 4 [0]) mTh)
    (greenprod.assemble (slabDiag mTh (posShells tTh p4 4 [0]))
      (slabOff mTh (posShells tTh p4 4 [0]))) :=
  depth_assemble tTh p4 4 [0] 4 (by decide +kernel) (by decide +kernel)
    (by decide) rfl mTh (by decide +kernel) (by decide +kernel)
    (msum_cross tTh p4 4 (by decide +kernel) (by decide +kernel))

/-! The gram and the electric member's form at the fibers'
orthogonal sum, and the pencil's site datum at the dual
representative `[1 : 12]` and the level one, cleared at twelve: the
electric member's form at the window diagonal and the identity gram
joined to twelve times the gram, less four times the cleared
magnetic member; its slabs along the shells and the assembly
read. -/

private def eTh : Mat := pairpencil.formE [0, 32, 48, 32] (elim.idMat 4)
private def sTh : Mat :=
  inertia.siteDatum
    (matAdd eTh (inertia.matScaleB (BPair.ofNat 12) (elim.idMat 4)))
    (inertia.matScaleB (BPair.ofNat 4) mTh)

theorem pin83 : crossB tTh p4 (elim.idMat 4) = true :=
  memberDiag_cross tTh p4 (elim.idMat 4) (by decide +kernel)
theorem pin84 : crossB tTh p4 eTh = true :=
  memberDiag_cross tTh p4 eTh (by decide +kernel)
theorem pin85 : matOneValue (ground.getAt [] (slabDiag sTh (posShells tTh p4 4 [0])) 0)
    [[⟨13, 1⟩]] := by decide +kernel
theorem pin86 : matOneValue (ground.getAt [] (slabDiag sTh (posShells tTh p4 4 [0])) 1)
    [[⟨33, 1⟩, u], [u, ⟨33, 1⟩]] := by decide +kernel
theorem pin87 : matOneValue (ground.getAt [] (slabDiag sTh (posShells tTh p4 4 [0])) 2)
    [[⟨61, 1⟩]] := by decide +kernel
theorem pin88 : matOneValue (ground.getAt [] (slabOff sTh (posShells tTh p4 4 [0])) 0)
    [[⟨1, 13⟩, ⟨1, 13⟩]] := by decide +kernel
theorem pin89 : matOneValue (ground.getAt [] (slabOff sTh (posShells tTh p4 4 [0])) 1)
    [[⟨1, 5⟩], [⟨1, 5⟩]] := by decide +kernel
private theorem sThSq : sqAt sTh 4 := by decide +kernel
private theorem sThSym : matOneValue (transposeM sTh) sTh := by decide +kernel
private theorem sThCross : crossB tTh p4 sTh = true := by decide +kernel
theorem pin90 : matOneValue (selM (depthOrder tTh p4 4 [0]) (depthOrder tTh p4 4 [0]) sTh)
    (greenprod.assemble (slabDiag sTh (posShells tTh p4 4 [0]))
      (slabOff sTh (posShells tTh p4 4 [0]))) :=
  depth_assemble tTh p4 4 [0] 4 (by decide +kernel) (by decide +kernel)
    (by decide) rfl sTh sThSq sThSym sThCross

end theta

namespace walk
open ground elim fusion fpcap

private def F : Data (List Nat) := dataA 2
private def winW : List (List Nat) := [labels.unitL 2, adjchar.theta 2, [4, 0]]
private def pw : List (List Nat) := (List.range winW.length).map (fun j => [j])
private def seed : List Nat :=
  (List.range winW.length).filter (fun j => F.eqL (getAt F.unit winW j) F.unit)

theorem pin91 : seed = [0] := by decide +kernel
theorem pin92 : ¬ (getAt BPair.unit (walkVec F winW 2) 2).oneValue BPair.unit := by
  decide +kernel
theorem pin93 : reachB [fusionMat F F.theta winW] pw winW.length seed 2 2 = true := by
  decide +kernel
theorem pin94 : reachB [fusionMat F F.theta winW] pw winW.length seed 2 2 = true :=
  walk_reach F winW 2 2 (by decide) (by decide +kernel)
theorem pin95 : (getAt BPair.unit (walkVec F winW 1) 2).oneValue BPair.unit := by
  decide +kernel
theorem pin96 : reachB [fusionMat F F.theta winW] pw winW.length seed 1 2 = false := by
  decide +kernel

end walk

end depthchain
