import MassGap.Fiber
import MassGap.Adjchar
import MassGap.Xfusion
import MassGap.Carrier
import MassGap.Memberdata
/-!
The check module for `con:fiber`: the batteries re-read the fiber's
pairing by kernel `decide` at the presentation's own values —
`⟨tr U, tr U⟩ = 1` at the one-factor site, and at the adjoint site
`⟨χ_adj, χ_adj⟩ = 1` with `⟨1, χ_adj⟩` of equal members at
`χ_adj = |tr U|² - [1 : d_f] tr(U U†)`, `prop:wg`'s pinned
Weingarten values read through the fiber's own display; and the
carrier's vertex lists at the label calculus, the interpolant's
validity, the two-end coevaluation's display at the block's count
with the symbolic route's own read there, at the wiring and at the
star, the display's reduced representative one value with the
through pairing's projection at the adjoint over two and three
letters and with the dual pair's tensor projected at `B_2`'s
vector, and the (2, 2) shape's two tie columns over four letters at
the count twenty, the
three- and four-end adjoint Grams at both tags with the direct
tag's members at their primitive representatives in the slot
power's coordinates, one value at the orientation spellings of a
self-dual vertex, the direct route's scale at two ends beside the
coevaluation's, the coevaluation's weights graded at the members'
weights one value with the Gram's adjugate at the adjoint over two
and three letters with the orthogonality and leading-minor binders
refused, the two-end reads at every orientation, the
projection's eigen-read, the direct tag's kernel-list reads with
the routing at unmatched ends and at a bottom column's daggered
slot, the interpolant's refusals at labels occurring twice in
their mixed power, and the insertion's tie to `prop:lap`'s action
at the residue.  The module's kernel reads price the direct tag's
kernel solve at the four-end vertex, `elim.kernelList` on the
stacked raisings' rows over the nineteen-member fused span at each
of its two orientation spellings, and the (2, 1) shape's two-end
projection over four letters at its twenty-eight-member fused
span, the reads beyond the one-pin budget the module's own. -/

namespace fiber
set_option maxHeartbeats 4000000

open ground places poly genericlift states

private def fU : FList := [(0, false)]
private def fAdj : FList := [(0, false), (0, true)]

/-- The fundamental trace's presentation, `tr U`. -/
private def trU : Comb := [([0], pOne)]

/-- The unit's presentation, `[1 : d_f] tr(U U†)`. -/
private def unitC : Comb := [([1, 0], ([⟨2, 1⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

/-- The adjoint character's presentation,
`|tr U|² - [1 : d_f] tr(U U†)`. -/
private def adjC : Comb :=
  [([0, 1], pOne), ([1, 0], ([⟨1, 2⟩], [⟨2, 1⟩, ⟨2, 1⟩]))]

theorem pin1 : crossNull (pairP fU fU trU trU) pOne := by decide +kernel
theorem pin2 : crossNull (pairP fAdj fAdj adjC adjC) pOne := by decide +kernel
theorem pin3 : crossNull (pairP fAdj fAdj unitC adjC) pZero := by decide +kernel

/-! The vertex lists at the label calculus (`con:fiber`'s stated
list): the interpolant's validity at the adjoint and the
fundamental; the two-end coevaluation at the adjoint and the
fundamental, at two outgoing self-dual adjoints as well, the vacant
list at two outgoing fundamentals, beside the symbolic route's own
read there, the projected through-wiring's self-pairing the block's
count, and the star's at two outgoing adjoints over two letters,
two outgoing fundamentals there and the self-dual middle column
over four letters; the
three-end adjoint Gram at the counts three and four, the two
orientations one value, the order the base `c₁` and the
determinant positive; the eigen-read of the projection, the
cleared insertion at each link reading the adjoint's cleared
Casimir on every projected wiring; and the direct tag's reads —
three adjoints at the count two, four at the count two (the
kernel list's three members), and the fundamental's triple wedge at
the count three. -/

private def th (d : Nat) : Shape := adjchar.theta d
private def fd (d : Nat) : Shape := ground.bumpAt 0 (labels.unitL d)
private def fdb (d : Nat) : Shape := labels.dualL (fd d)

theorem pin4 : interpValid 2 (th 2) = true ∧ interpValid 3 (th 3) = true
    ∧ interpValid 3 (fd 3) = true ∧ interpValid 4 [1, 1, 0, 0] = false
    ∧ interpValid 4 [2, 1, 0, 0] = false ∧ interpValid 4 [0, 2, 0, 0] = false := by
  decide +kernel
theorem pin5 : interpNodes 3 (th 3) = [labels.unitL 3] := by decide +kernel

theorem pin6 : vertGramA 2 [(th 2, true), (th 2, false)] = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 3 [(fd 3, true), (fd 3, false)] = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 3 [(th 3, true), (th 3, true)] = ([[BPair.ofNat 8]], Pos.one)
    ∧ vertGramA 3 [(fd 3, true), (fd 3, true)] = ([], Pos.one)
    ∧ vertGramA 3 [] = ([[BPair.ofNat 1]], Pos.one) := by decide +kernel
theorem pin7 : listGram (vertListSym 3 [(th 3, true), (th 3, false)]) = ([[BPair.ofNat 8]], Pos.one)
    ∧ listGram (vertListSym 2 [(th 2, true), (th 2, false)]) = ([[BPair.ofNat 3]], Pos.one)
    ∧ listGram (vertListSym 3 [(fd 3, true), (fd 3, false)]) = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 3 [(th 3, true), (th 3, false)] = ([[BPair.ofNat 8]], Pos.one)
    ∧ vertGramA 2 [(th 2, true), (th 2, true)] = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 2 [(fd 2, true), (fd 2, true)] = ([[BPair.ofNat 2]], Pos.one)
    ∧ vertGramA 4 [([0, 1, 0, 0], true), ([0, 1, 0, 0], true)]
      = ([[BPair.ofNat 6]], Pos.one) := by
  decide +kernel

/-! The two-end reads at every orientation: two incoming adjoints,
the fundamental's dual against the fundamental both incoming, the
fundamental incoming against itself outgoing and outgoing against
its dual outgoing, each at the count; and the (2, 1) shape over
four letters against itself at the exchanged orientation, two
wiring columns at the block's twenty, the projection's solve at
the ends' weight lists' groups. -/

theorem pin8 : vertGramA 3 [(th 3, false), (th 3, false)] = ([[BPair.ofNat 8]], Pos.one)
    ∧ vertGramA 3 [(fdb 3, false), (fd 3, false)] = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 3 [(fd 3, false), (fd 3, true)] = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 3 [(fd 3, true), (fdb 3, true)] = ([[BPair.ofNat 3]], Pos.one) := by
  decide +kernel
theorem pin9 : vertGramA 4 [([1, 1, 0, 0], true), ([1, 1, 0, 0], false)]
    = ([[BPair.ofNat 20]], Pos.one) := by decide +kernel

/-! The symbolic members' Gram at the cycle counts is the members'
coordinate pairing, the fast read tied to the graded vectors at
the three-end adjoint vertex over three letters at both
orientations and at the two-end symbolic reads. -/

theorem pin10 : (vertListSym 3 [(th 3, true), (th 3, true), (th 3, false)]).members.gram
      = slotpower.gramT (memtable.lettersT 3)
        (vertListSym 3 [(th 3, true), (th 3, true), (th 3, false)]).members.list
    ∧ (vertListSym 3 [(th 3, true), (th 3, false), (th 3, false)]).members.gram
      = slotpower.gramT (memtable.lettersT 3)
        (vertListSym 3 [(th 3, true), (th 3, false), (th 3, false)]).members.list
    ∧ (vertListSym 2 [(th 2, true), (th 2, false)]).members.gram
      = slotpower.gramT (memtable.lettersT 2)
        (vertListSym 2 [(th 2, true), (th 2, false)]).members.list
    ∧ (vertListSym 3 [(fd 3, true), (fd 3, false)]).members.gram
      = slotpower.gramT (memtable.lettersT 3)
        (vertListSym 3 [(fd 3, true), (fd 3, false)]).members.list := by
  decide +kernel

/-! The direct route's scale at two ends beside the coevaluation's:
the kernel member at its primitive representative in the slot
power's coordinates self-pairs at twelve over two letters and at
seventy-two over three, where the coevaluation reads the counts
three and eight; and the coevaluation's clearing at the display's
primitive representative, three at the adjoint over three letters
and two at two outgoing adjoints over two letters. -/

theorem pin11 : posVal (twoEndList 3 (th 3, true) (th 3, false)).clear = 3
    ∧ posVal (twoEndList 2 (th 2, true) (th 2, true)).clear = 2 := by decide +kernel

theorem pin12 : listGram (vertListDirect 2 [(th 2, true), (th 2, true)])
      = ([[BPair.ofNat 12]], Pos.one)
    ∧ listGram (vertListDirect 3 [(th 3, true), (th 3, false)])
      = ([[BPair.ofNat 72]], Pos.one) := by decide +kernel

private def g3 : elim.Mat × Pos :=
  ([[BPair.ofNat 56, (BPair.ofNat 16).swap], [(BPair.ofNat 16).swap, BPair.ofNat 56]], 3)
private def g4 : elim.Mat × Pos :=
  ([[BPair.ofNat 105, (BPair.ofNat 15).swap], [(BPair.ofNat 15).swap, BPair.ofNat 105]], 2)

theorem pin13 : vertGramA 3 [(th 3, true), (th 3, true), (th 3, false)] = g3
    ∧ vertGramA 3 [(th 3, true), (th 3, false), (th 3, false)] = g3
    ∧ vertGramA 4 [(th 4, true), (th 4, true), (th 4, false)] = g4 := by decide +kernel
theorem pin14 : (vertGramA 3 [(th 3, true), (th 3, true), (th 3, false)]).1.length
      = xfusion.c1 3
    ∧ (elim.detD g3.1).oneValue (BPair.ofNat 2880) := by decide +kernel

/-- The eigen-read at a three-end adjoint vertex: every projected
wiring at every link's cleared insertion reads the adjoint's cleared
Casimir `dfQ θ` times itself. -/
private def eigenRead (d : Nat) (es : List (Shape × Bool)) : Bool :=
  let ends := linkEnds d es 0 0
  let k := ground.sumNat (ends.map (fun e => e.1.length))
  (places.perms k).all (fun σ =>
    let v := projVertex d es (slotpower.monV σ.length σ rfl)
    ends.all (fun e =>
      slotpower.oneValueV (linkCasC d e.1 e.2 v)
        (slotpower.scaleV (BPair.ofNat (c2hat.dfQ (th d))) v)))

theorem pin15 : eigenRead 3 [(th 3, true), (th 3, true), (th 3, false)] = true
    ∧ eigenRead 2 [(th 2, true), (th 2, false)] = true := by decide +kernel

/-- The four-end adjoint Gram over two letters at two incoming
ends, the members' signs the back solve's at that spelling. -/
private def m4 : elim.Mat :=
  [[BPair.ofNat 144, (BPair.ofNat 144).swap, BPair.ofNat 48],
   [(BPair.ofNat 144).swap, BPair.ofNat 336, (BPair.ofNat 144).swap],
   [BPair.ofNat 48, (BPair.ofNat 144).swap, BPair.ofNat 144]]

/-- The four-end adjoint Gram over two letters at every end
outgoing, the members' signs the back solve's there. -/
private def m4Out : elim.Mat :=
  [[BPair.ofNat 144, BPair.ofNat 144, BPair.ofNat 48],
   [BPair.ofNat 144, BPair.ofNat 336, BPair.ofNat 144],
   [BPair.ofNat 48, BPair.ofNat 144, BPair.ofNat 144]]

theorem pin16 : vertGramA 2 [(th 2, true), (th 2, true), (th 2, false)]
      = ([[BPair.ofNat 12]], Pos.one)
    ∧ vertGramA 2 [(th 2, true), (th 2, true), (th 2, true)]
      = ([[BPair.ofNat 12]], Pos.one)
    ∧ vertGramA 2 [(fd 2, true), (th 2, true), (fd 2, false)]
      = ([[BPair.ofNat 12]], Pos.one) := by decide +kernel
theorem pin17 : vertGramA 2 [(th 2, true), (th 2, true), (th 2, false), (th 2, false)]
      = (m4, Pos.one)
    ∧ vertGramA 2 [(th 2, true), (th 2, true), (th 2, true), (th 2, true)]
      = (m4Out, Pos.one) := by decide +kernel

/-! The routing at unmatched ends: three outgoing fundamentals over
three letters read the wedge at the direct tag through the vertex
Gram itself, three outgoing dual fundamentals the dual wedge at a
bottom column's daggered slots, three fundamentals with the
adjoint the two-member kernel Gram at the vertex's own
multiplicity, four outgoing fundamentals over two letters the
two-member kernel Gram there, and the self-dual middle column over
four letters reads its coevaluation at two ends. -/

theorem pin18 : vertGramA 3 [(fd 3, true), (fd 3, true), (fd 3, true)]
      = ([[BPair.ofNat 6]], Pos.one)
    ∧ vertGramA 3 [(fdb 3, true), (fdb 3, true), (fdb 3, true)]
      = ([[BPair.ofNat 6]], Pos.one)
    ∧ vertGramA 3 [(fd 3, true), (fd 3, true), (fd 3, true), (th 3, true)]
      = ([[BPair.ofNat 144, BPair.ofNat 72], [BPair.ofNat 72, BPair.ofNat 144]], Pos.one)
    ∧ carrier.invCount (fusion.dataA 3) [fd 3, fd 3, fd 3, th 3] = 2
    ∧ (vertGramA 2 [(fd 2, true), (fd 2, true), (fd 2, true), (fd 2, true)]).1.length
      = carrier.invCount (fusion.dataA 2) [fd 2, fd 2, fd 2, fd 2]
    ∧ carrier.invCount (fusion.dataA 2) [fd 2, fd 2, fd 2, fd 2] = 2
    ∧ vertGramA 4 [([0, 1, 0, 0], true), ([0, 1, 0, 0], false)]
      = ([[BPair.ofNat 6]], Pos.one) := by decide +kernel

/-! The insertion's tie to its owner: `linkCas` at a link's row and
column ends is `lap.lapAct` on the closed site of the ends,
evaluated at the residue and cleared by `2 d_f` — the site's factors
the row ends undaggered then the column ends daggered at the link's
key, a wiring the involution pairing each row end with its column
end, the action's images read back at their row ends, and each
key's coefficient the polynomial pair's Horner read at the residue
(`prop:lap`'s display at the residue's count). -/

/-- A polynomial pair read at the residue as a scalar pair, the
second member's read positive at the display. -/
private def atRes (r : Nat) (c : poly.PPair) : CPair :=
  ⟨poly.eval c.1 (BPair.ofNat r),
    ground.posOfSucc (BPair.marginN (poly.eval c.2 (BPair.ofNat r)) - 1)⟩

/-- The action's image at a wiring read back at the row ends, one
scalar pair per wiring key. -/
private def actAtRes (d k : Nat) (F : FList) (W : Nat) (σ : List Nat) :
    List (List Nat × CPair) :=
  let π := σ.map (fun j => j + k) ++ (List.range k).map (fun j => places.posOf j σ)
  (lap.lapAct F W π).foldl (fun acc e =>
    ground.joinBy (fun a b => a == b) (fun y x => y + x)
      ((e.1.take k).map (fun j => j - k)) (atRes (d - 1) e.2) acc) []

/-- The tie at one wiring: every key of either read at one value,
the cleared insertion against the action's read at `2 d_f`. -/
private def casTie (d k : Nat) (F : FList) (W : Nat) (rs cs : List Nat)
    (σ : List Nat) : Bool :=
  let l := fiber.linkCasC d rs cs (slotpower.monV σ.length σ rfl)
  let a := actAtRes d k F W σ
  ((l.val ++ a.map (fun e => (e.1, BPair.unit))).map Prod.fst).all (fun w =>
    let x := slotpower.coefAt w l
    let y := a.foldl (fun acc e => if e.1 == w then acc + e.2 else acc)
      (⟨BPair.unit, Pos.one⟩ : CPair)
    ((⟨BPair.ofNat (2 * d), Pos.one⟩ : CPair) * y).oneValue ⟨x, Pos.one⟩)

/-- Two ends of one link among two, and the four ends of one link
at a two-row two-column word. -/
private def fTwo : FList := [(0, false), (1, false), (1, true), (0, true)]
private def fFour : FList := [(0, false), (0, false), (0, true), (0, true)]

theorem pin19 : (places.perms 2).all (fun σ => casTie 2 2 fTwo 0 [0] [1] σ) = true
    ∧ (places.perms 2).all (fun σ => casTie 3 2 fTwo 0 [0] [1] σ) = true
    ∧ (places.perms 2).all (fun σ => casTie 3 2 fFour 0 [0, 1] [0, 1] σ) = true
    ∧ (places.perms 2).all (fun σ => casTie 4 2 fFour 0 [0, 1] [0, 1] σ) = true := by
  decide +kernel

/-! The letter count at the members: the wirings' stated count at
the symbolic three-end vertex, the coordinate families' width at
the direct-tag list and at the unit state's list. -/

theorem pin20 : (vertListSym 3 [(th 3, true), (th 3, true), (th 3, false)]).members.letters = 3
    ∧ (vertListDirect 2 [(th 2, true), (th 2, true), (th 2, false)]).members.letters = 2
    ∧ (vertListA 3 []).members.letters = 3 := by decide +kernel

/-! A link's invariant list at its combined slots (`con:fiber`'s
magnetic read): the adjoint loop's changed link over three letters,
three of each at the symbolic tag, six wirings at the cycle-count
Gram of determinant `119439360`, and over two letters the direct
tag at five kernel members, the Gram's determinant `5184`; the
fundamental's unchanged link, one wiring at the count; and the
coevaluation's
weights the adjugate against the determinant, the list against
the adjugate the determinant's diagonal at the two-wiring link. -/

theorem pin21 : (linkList 3 [true, false, false, true, false, true]).1.length = 6
    ∧ (linkList 3 [true, false, false, true, false, true]).2 = mixedinv.cycleGram 3 3
    ∧ (elim.detD (linkList 3 [true, false, false, true, false, true]).2).oneValue
        (BPair.ofNat 119439360)
    ∧ (linkList 2 [true, true, false, true, false, false]).1.length = 5
    ∧ (elim.detD (linkList 2 [true, true, false, true, false, false]).2).oneValue
        (BPair.ofNat 5184)
    ∧ (linkList 3 [true, false]).1.length = 1
    ∧ (linkList 3 [true, false]).2 = [[BPair.ofNat 3]] := by decide +kernel
theorem pin22 : (coevW [[BPair.ofNat 4, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 4]]).2.oneValue
      (BPair.ofNat 12)
    ∧ elim.matOneValue
        (elim.matMul [[BPair.ofNat 4, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 4]]
          (coevW [[BPair.ofNat 4, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 4]]).1)
        [[BPair.ofNat 12, BPair.unit], [BPair.unit, BPair.ofNat 12]] := by decide +kernel

/-! The presentation field at a member (`con:memtable`; `presT`):
`B_2`'s generating table, the defining table joined to the spinor's
at nine keys, the reach list the vector and the spinor among the
keys, `θ = 2ω_2` the spinor's top squared in degree two, the
fundamentals' involution the identity. The vertex lists: the
two-end reads the coevaluation's display at the blocks' counts, at
opposite orientations the spinor against its dual at four, the
vector at five and the adjoint at ten; at one orientation the
display read through the dual pair at every slot, the counts again
at either orientation and every member at the sum's unit under
every raising at the vertex's signature, and the vacant list at two labels off the
dual pair; the three-end spinor pair against the vector one member
(`N^v_{ss} = 1`) at the kernel's weighted read twenty (the paired
keys' weight two against the null key's one), refused at the
identity weight; the untouched vertex the scalar one and a one-end
vertex vacant; the boundary factor's word `(2, 0)` with its
coevaluation at twenty-eight monomials; the link list at the
spinor's boundary link one member and the spinor's own link the
block's count; the reach read's tops at their degrees with the
blocks' counts at `B_2`, `B_3`, `C_3`, `D_4` and `G_2`; and the
dual coherence, the dual pair carrying each fundamental's block
onto its dual's, at `B_2`, `C_3`, `D_4` and `D_5`'s spinor pair. -/

private def presB2 : Pres (List Nat) :=
  presT (memtable.genB 2) (fusion.reachB 2) (fun i => i) [0, 2]

private def vlAt (es : List (List Nat × Bool)) : Option (Nat × elim.Mat × Pos) :=
  (presB2.vertList es).map (fun l => (l.members.list.length, listGram l))

theorem pin23 : vlAt [([0, 1], true), ([0, 1], false)] = some (1, [[BPair.ofNat 4]], Pos.one) := by
  decide +kernel
theorem pin24 : vlAt [([1, 0], true), ([1, 0], false)] = some (1, [[BPair.ofNat 5]], Pos.one) := by
  decide +kernel
theorem pin25 : vlAt [([0, 1], true), ([0, 1], true), ([1, 0], false)]
    = some (1, [[BPair.ofNat 20]], Pos.one) := by decide +kernel
theorem pin26 : vlAt [([0, 2], true), ([0, 2], false)] = some (1, [[BPair.ofNat 10]], Pos.one) := by
  decide +kernel
theorem pin27 : vlAt [([1, 0], true), ([1, 0], true)] = some (1, [[BPair.ofNat 5]], Pos.one) := by
  decide +kernel
theorem pin28 : vlAt [([0, 1], true), ([0, 1], true)] = some (1, [[BPair.ofNat 4]], Pos.one) := by
  decide +kernel
theorem pin29 : vlAt [([0, 1], false), ([0, 1], false)] = some (1, [[BPair.ofNat 4]], Pos.one) := by
  decide +kernel
theorem pin30 : vlAt [([0, 2], true), ([0, 2], true)] = some (1, [[BPair.ofNat 10]], Pos.one) := by
  decide +kernel
theorem pin31 : vlAt [([1, 0], true), ([0, 1], true)] = some (0, [], Pos.one)
    ∧ vlAt [([1, 0], true), ([0, 1], false)] = some (0, [], Pos.one) := by decide +kernel
theorem pin32 : vlAt [] = some (1, [[BPair.ofNat 1]], Pos.one)
    ∧ vlAt [([0, 1], true)] = some (0, [], Pos.one)
    ∧ presB2.bdryWord = (2, 0)
    ∧ presB2.lessUnit = false
    ∧ (presB2.vertList []).map (fun l => l.members.letters) = some 9 := by decide +kernel
theorem pin33 : presB2.bdry.1.2.val.length = 28 ∧ presB2.bdry.1.1 = 4 := by decide +kernel
theorem pin34 : (presB2.linkList ([0, 1], some true, [0, 1])).1.2.length = 1
    ∧ (presB2.linkList ([0, 1], none, [0, 1])).2 = [[BPair.ofNat 4]] := by decide +kernel

/-- The `B_2` table at the identity in place of its dual pair, the
one-orientation read parting from the block's count. -/
private def presB2ident : Pres (List Nat) :=
  presT { memtable.genB 2 with dual := some (memtable.unitWt 9, Pos.one) }
    (fusion.reachB 2) (fun i => i) [0, 2]

theorem pin35 : ¬ ((presB2ident.vertList [([1, 0], true), ([1, 0], true)]).map
    (fun l => listGram l) = some ([[BPair.ofNat 5]], Pos.one)) := by decide +kernel

/-- The `B_2` table at the identity weight, the three-end Gram
parting from the weighted read. -/
private def presB2unit : Pres (List Nat) :=
  presT { memtable.genB 2 with wt := memtable.unitWt 9, wtInv := memtable.unitWt 9, wtDet := 1 }
    (fusion.reachB 2) (fun i => i) [0, 2]

theorem pin36 : (presB2unit.vertList [([0, 1], true), ([0, 1], true), ([1, 0], false)]).map
    (fun l => listGram l) = some ([[BPair.ofNat 12]], Pos.one) := by decide +kernel

/-! The reach read's tops with their degrees, and the blocks'
counts at the fundamentals and at `θ`. -/

private def topsB2 := fundTops (memtable.genB 2) (fusion.reachB 2)
private def topsB3 := fundTops (memtable.genB 3) (fusion.reachB 3)
private def topsC3 := fundTops (memtable.definingC 3) (fusion.reachC 3)
private def topsD4 := fundTops (memtable.genD 4) (fusion.reachD 4)
private def topsG2 := fundTops memtable.genG2 [none, some (0, 0)]

theorem pin37 : topsB2.map (fun t => t.map Sigma.fst) = [some 1, some 1]
    ∧ topsB3.map (fun t => t.map Sigma.fst) = [some 1, some 2, some 1]
    ∧ topsC3.map (fun t => t.map Sigma.fst) = [some 1, some 2, some 3]
    ∧ topsD4.map (fun t => t.map Sigma.fst) = [some 1, some 2, some 1, some 1]
    ∧ topsG2.map (fun t => t.map Sigma.fst) = [some 1, some 2] := by decide +kernel
theorem pin38 : (blockAt (memtable.genB 2) topsB2 [1, 0]).length = 5
    ∧ (blockAt (memtable.genB 2) topsB2 [0, 1]).length = 4
    ∧ (blockAt (memtable.genB 2) topsB2 [0, 2]).length = 10 := by decide +kernel
theorem pin39 : (blockAt (memtable.genB 3) topsB3 [0, 1, 0]).length = 21
    ∧ (blockAt (memtable.definingC 3) topsC3 [0, 0, 1]).length = 14
    ∧ (blockAt (memtable.genD 4) topsD4 [0, 1, 0, 0]).length = 28
    ∧ (blockAt memtable.genG2 topsG2 [0, 1]).length = 14 := by decide +kernel

theorem pin40 : dualCoherent (memtable.genB 2) topsB2 (fun i => i) [1, 0] = true
    ∧ dualCoherent (memtable.genB 2) topsB2 (fun i => i) [0, 1] = true
    ∧ dualCoherent (memtable.genB 2) topsB2 (fun i => i) [0, 2] = true
    ∧ dualCoherent (memtable.definingC 3) topsC3 (fun i => i) [0, 1, 0] = true
    ∧ dualCoherent (memtable.genD 4) topsD4 (fun i => i) [0, 0, 1, 0] = true := by
  decide +kernel
theorem pin41 : dualCoherent (memtable.genD 5) (fundTops (memtable.genD 5) (fusion.reachD 5))
    (fun i => if i == 3 then 4 else if i == 4 then 3 else i) [0, 0, 0, 1, 0] = true := by
  decide +kernel

/-! The two-end display against the through pairing's projection
(`con:slotpower`'s derived identity, the projection the block's
coevaluation): at the adjoint over three letters at opposite
orientations and over two letters at two outgoing ends, the star at
the tie column, the vertex list's member at its clearing and the
grouped projection at its own read one reduced representative,
display and clearing; and the (2, 2) shape's two tie columns over
four letters at the block's count twenty. -/

/-- A vertex list's one member with its clearing at the reduced
representative, the display and the clearing. -/
private def reducedAt (l : VList) : List (List Nat × BPair) × Nat :=
  match l.members with
  | .vecs _ w vs =>
    let r := slotpower.reduceV (ground.getAt (slotpower.emptyV w) vs 0, l.clear)
    (r.1.val, posVal r.2)
  | .wirings _ _ _ _ => ([], 0)

private def tp3 := slotpower.castV (slotpower.twoEnds_len 3 (th 3, true) (th 3, false))
  (slotpower.throughPair 3 (th 3, true) (th 3, false)).1
private def prG3 := slotpower.projectGroupsT (memtable.lettersT 3)
  (slotpower.fusedGroupsT (memtable.lettersT 3)
    (slotpower.endBlocks 3 [(th 3, true), (th 3, false)])) tp3
private def tp2 := slotpower.castV (slotpower.twoEnds_len 2 (th 2, true) (th 2, true))
  (slotpower.throughPair 2 (th 2, true) (th 2, true)).1
private def prG2 := slotpower.projectGroupsT (memtable.lettersT 2)
  (slotpower.fusedGroupsT (memtable.lettersT 2)
    (slotpower.endBlocks 2 [(th 2, true), (th 2, true)])) tp2

theorem pin42 : reducedAt (twoEndList 3 (th 3, true) (th 3, false))
      = ((slotpower.reduceV prG3).1.val, posVal (slotpower.reduceV prG3).2)
    ∧ reducedAt (twoEndList 2 (th 2, true) (th 2, true))
      = ((slotpower.reduceV prG2).1.val, posVal (slotpower.reduceV prG2).2) := by
  decide +kernel

theorem pin43 : vertGramA 4 [([0, 2, 0, 0], true), ([0, 2, 0, 0], true)]
    = ([[BPair.ofNat 20]], Pos.one) := by decide +kernel

/-- A vertex list's every member at the sum's unit under every
raising at the vertex's signature at a member table
(`slotpower.raisedUnit`, the identified coevaluation a top of the
unit label). -/
private def topsAt (es : List (List Nat × Bool)) : Bool :=
  let sig := es.flatMap (fun e => List.replicate (degOf topsB2 e.1) (!e.2))
  match presB2.vertList es with
  | some l =>
    match l.members with
    | .vecs T w vs =>
      if h : w = sig.length then
        vs.all (fun v => slotpower.raisedUnit T sig (slotpower.castV h v))
      else false
    | .wirings _ _ _ _ => false
  | none => false

/-! The display against the dual pair's tensor projected to the fused
span at a member (`con:fiber`'s one-orientation identity at
`con:memtable`'s pair): `B_2`'s vector at two outgoing ends, the
vertex list's member at its reduced representative one value with
`slotpower.dualThroughT`'s tensor projected group by group at the
tensor's clearing against the projection's. -/

private def endB2 (e : List Nat × Bool) : slotpower.EndBlock :=
  ⟨List.replicate (degOf topsB2 e.1) (!e.2), degOf topsB2 e.1,
    ground.length_replicate _ _, blockAt (memtable.genB 2) topsB2 e.1⟩
private def endsV : List slotpower.EndBlock := [endB2 ([1, 0], true), endB2 ([1, 0], true)]
private def pairsV : List (Nat × Nat) :=
  (slotpower.colMatch (fun i => i) true
    (slotpower.layoutOf 0 (factorsOf topsB2 [1, 0], []) 0)
    (slotpower.layoutOf 0 (factorsOf topsB2 [1, 0], []) (degOf topsB2 [1, 0]))).flatMap
    (fun p => List.zipWith (fun a b => (a, b)) p.1 p.2.1)
private def prV : Option (List (List Nat × BPair) × Nat) :=
  (slotpower.dualThroughT (memtable.genB 2) pairsV (slotpower.fusedSig endsV).length).map
    (fun tp =>
      let pr := slotpower.projectGroupsT (memtable.genB 2)
        (slotpower.fusedGroupsT (memtable.genB 2) endsV) tp.1
      let r := slotpower.reduceV (pr.1, tp.2 * pr.2)
      (r.1.val, posVal r.2))

theorem pin45 : (presB2.vertList [([1, 0], true), ([1, 0], true)]).map reducedAt = prV := by
  decide +kernel

theorem pin44 : topsAt [([1, 0], true), ([1, 0], true)] = true
    ∧ topsAt [([1, 0], false), ([1, 0], false)] = true
    ∧ topsAt [([0, 1], true), ([0, 1], true)] = true
    ∧ topsAt [([0, 1], false), ([0, 1], false)] = true
    ∧ topsAt [([1, 0], true), ([1, 0], false)] = true
    ∧ topsAt [([0, 2], true), ([0, 2], true)] = true := by decide +kernel

/-! The graded coevaluation weights at the block's weight grades
(`coevG` at `slotpower.blockGroupsAt`; `lem:dualread`(i)'s adjugate
collecting each weight grade's own at the further grades'
determinants): at the adjoint block over two letters, three members
at three weights, and over three letters, eight members with the unit
weight's grade of two, a grade's weight at two of its places is the
Gram's adjugate at those places, the adjugate reads the unit at two
places of distinct weights, and the clearing is the determinant,
decided at the two-letter block against the cofactor family and at
the three-letter block against the dense descent read (`coevW`, the
adjugate at one bordered descent), and read through `coevG_block` at
the two-letter block at the block's own grades with the weights'
orthogonality the one decided binder; the orthogonality binder
refused at a list whose two members at distinct weights pair off the
unit (the first member two monomials, its weight its head's), the
adjugate then off the unit at the cross places and the clearing off
the determinant; the leading minors' binder refused at a repeated
member, the one grade's Gram singular and its weight off the
adjugate. -/

private def gT2 := slotpower.blockSpanAt 2 (th 2)
private def gT3 := slotpower.blockSpanAt 3 (th 3)
private def gG2 := slotpower.blockGroupsAt 2 (th 2)
private def gG3 := slotpower.blockGroupsAt 3 (th 3)
private def gr2 : List (List Nat) := slotpower.weightPlaces (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) gT2
private def gr3 : List (List Nat) := slotpower.weightPlaces (memtable.lettersT 3) (slotpower.labelSig 3 (th 3)) gT3
private def dG2 : List (slotpower.SVec (slotpower.labelSig 2 (th 2)).length) × elim.Mat := ([], [])
private def dG3 : List (slotpower.SVec (slotpower.labelSig 3 (th 3)).length) × elim.Mat := ([], [])
private def vA : slotpower.SVec 1 :=
  slotpower.addV (slotpower.monV 1 [0] rfl) (slotpower.monV 1 [1] rfl)
private def vB : slotpower.SVec 1 := slotpower.monV 1 [1] rfl
private def gAB := slotpower.listGroupsT (memtable.lettersT 2) [false] [vA, vB]
private def gBB := slotpower.listGroupsT (memtable.lettersT 2) [false] [vB, vB]
private def dG1 : List (slotpower.SVec 1) × elim.Mat := ([], [])
private def top2 : slotpower.SVec (slotpower.labelSig 2 (th 2)).length :=
  slotpower.castV (by decide) (slotpower.ofH (slotpower.blockTop 2 (th 2)))

theorem pin46 : gG2.length = 3 ∧ gG3.length = 7 ∧ gr2 = [[0], [1], [2]]
    ∧ gr3 = [[0], [1], [2], [3, 4], [5], [6], [7]]
    ∧ (∀ i : Nat, i < 3 → ∀ p : Nat, p < (getAt [] gr2 i).length →
        ∀ q : Nat, q < (getAt [] gr2 i).length →
        (getAt BPair.unit (getAt [] (getAt dG2 (coevG gG2).1 i).2 p) q).oneValue
          (getAt BPair.unit (getAt [] (elim.adjM (slotpower.gramT (memtable.lettersT 2) gT2))
            (getAt 0 (getAt [] gr2 i) p)) (getAt 0 (getAt [] gr2 i) q)))
    ∧ (∀ j : Nat, j < 3 → ∀ j' : Nat, j' < 3 → ¬ elim.groupOf j gr2 = elim.groupOf j' gr2 →
        (getAt BPair.unit (getAt [] (elim.adjM (slotpower.gramT (memtable.lettersT 2) gT2)) j)
          j').oneValue BPair.unit)
    ∧ ((coevG gG2).2).oneValue (elim.detL (slotpower.gramT (memtable.lettersT 2) gT2))
    ∧ (∀ i : Nat, i < 7 → ∀ p : Nat, p < (getAt [] gr3 i).length →
        ∀ q : Nat, q < (getAt [] gr3 i).length →
        (getAt BPair.unit (getAt [] (getAt dG3 (coevG gG3).1 i).2 p) q).oneValue
          (getAt BPair.unit (getAt [] (coevW (slotpower.gramT (memtable.lettersT 3) gT3)).1
            (getAt 0 (getAt [] gr3 i) p)) (getAt 0 (getAt [] gr3 i) q)))
    ∧ (∀ j : Nat, j < 8 → ∀ j' : Nat, j' < 8 → ¬ elim.groupOf j gr3 = elim.groupOf j' gr3 →
        (getAt BPair.unit (getAt [] (coevW (slotpower.gramT (memtable.lettersT 3) gT3)).1 j)
          j').oneValue BPair.unit)
    ∧ ((coevG gG3).2).oneValue (coevW (slotpower.gramT (memtable.lettersT 3) gT3)).2 := by
  decide +kernel
theorem pin47 : gAB.length = 2 ∧ gBB.length = 1
    ∧ ¬ (getAt BPair.unit (getAt [] (elim.adjM (slotpower.gramT (memtable.lettersT 2) [vA, vB])) 0)
        1).oneValue BPair.unit
    ∧ ¬ ((coevG gAB).2).oneValue (elim.detL (slotpower.gramT (memtable.lettersT 2) [vA, vB]))
    ∧ ¬ (slotpower.pairT (memtable.lettersT 2) (slotpower.unitWtRead (memtable.lettersT 2))
        vA vB).oneValue BPair.unit
    ∧ ¬ slotpower.weightV (memtable.lettersT 2) [false] vA
        = slotpower.weightV (memtable.lettersT 2) [false] vB
    ∧ ¬ (∀ p : Nat, p < 2 → ∀ q : Nat, q < 2 →
        (getAt BPair.unit (getAt [] (getAt dG1 (coevG gBB).1 0).2 p) q).oneValue
          (getAt BPair.unit (getAt [] (elim.adjM (slotpower.gramT (memtable.lettersT 2) [vB, vB])) p) q))
    ∧ ¬ ((coevG gBB).2).oneValue (elim.detL (slotpower.gramT (memtable.lettersT 2) [vB, vB]))
    ∧ (elim.detL (slotpower.gramT (memtable.lettersT 2) [vB, vB])).oneValue BPair.unit := by
  decide +kernel
theorem pin48 : (∀ i, i < (slotpower.weightPlaces (memtable.lettersT 2) (slotpower.labelSig 2 (th 2))
        (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)).length →
      ∀ p, p < (getAt [] (slotpower.weightPlaces (memtable.lettersT 2) (slotpower.labelSig 2 (th 2))
        (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)) i).length →
      ∀ q, q < (getAt [] (slotpower.weightPlaces (memtable.lettersT 2) (slotpower.labelSig 2 (th 2))
        (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)) i).length →
        (getAt BPair.unit (getAt [] (getAt ([], [])
          (coevG (slotpower.blockGroupsT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)).1 i).2
          p) q).oneValue
        (getAt BPair.unit (getAt [] (elim.adjM (slotpower.gramT (memtable.lettersT 2)
            (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)))
          (getAt 0 (getAt [] (slotpower.weightPlaces (memtable.lettersT 2) (slotpower.labelSig 2 (th 2))
            (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)) i) p))
          (getAt 0 (getAt [] (slotpower.weightPlaces (memtable.lettersT 2) (slotpower.labelSig 2 (th 2))
            (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)) i) q)))
    ∧ (∀ j, j < (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2).length →
        ∀ j', j' < (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2).length →
        ¬ slotpower.weightV (memtable.lettersT 2) (slotpower.labelSig 2 (th 2))
            (getAt (slotpower.emptyV _)
              (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2) j)
          = slotpower.weightV (memtable.lettersT 2) (slotpower.labelSig 2 (th 2))
            (getAt (slotpower.emptyV _)
              (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2) j') →
        (getAt BPair.unit (getAt [] (elim.adjM (slotpower.gramT (memtable.lettersT 2)
          (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2))) j)
          j').oneValue BPair.unit)
    ∧ ((coevG (slotpower.blockGroupsT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)).2).oneValue
        (elim.detL (slotpower.gramT (memtable.lettersT 2)
          (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2))) :=
  coevG_block (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2 (memtable.lettersT_symm 2)
    (by decide +kernel)

/-! The coevaluation tensor as the display over every pair
(`coevOf`, `coevDisplay`; `lem:dualread`(i)'s `Σ A_{jk} y_j ⊗ y_k` at
the adjugate collecting each block's own): at the two-letter adjoint
block the grades' own pairs' tensor is the display at the whole
Gram's adjugate, decided and read through `coevOf_block`, and at the
two-member list whose members at distinct weights pair off the unit
the two tensors differ at the cross term. -/

theorem pin49 : (coevOf gG2).1 = coevDisplay gT2 gT2 (elim.adjM (slotpower.gramT (memtable.lettersT 2) gT2))
    ∧ ¬ (coevOf gAB).1 = coevDisplay [vA, vB] [vA, vB]
        (elim.adjM (slotpower.gramT (memtable.lettersT 2) [vA, vB])) := by
  decide +kernel
theorem pin50 : (coevOf (slotpower.blockGroupsT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)).1
      = coevDisplay (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)
          (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)
          (elim.adjM (slotpower.gramT (memtable.lettersT 2)
            (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)))
    ∧ ((coevOf (slotpower.blockGroupsT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2)).2).oneValue
        (elim.detL (slotpower.gramT (memtable.lettersT 2)
          (slotpower.blockSpanT (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2))) :=
  coevOf_block (memtable.lettersT 2) (slotpower.labelSig 2 (th 2)) top2 (memtable.lettersT_symm 2)
    (by decide +kernel)

/-- The actual G2 tensor top exists and is occupied at every
label of the member's width. -/
theorem pin51 (a : List Nat) (ha : a.length = 2) :
    ∃ v, topOf (fundTops memtable.genG2 [none, some (0, 0)]) a = some v ∧ v.2.val ≠ [] :=
  topOf_occupied_G2 a ha

theorem pin52 (tops : List (Option slotpower.WVec)) (a : List Nat) (v : slotpower.WVec)
    (hv : topOf tops a = some v) : v.1 = degOf tops a := topOf_degree tops a v hv

theorem pin53 (a : List Nat) (ha : a.length = 2) :
    ∀ w ∈ blockWeights memtable.genG2 (fundTops memtable.genG2 [none, some (0, 0)]) a,
      w.length = 2 ∧ poly.pnorm w = w := blockWeights_shape_G2 a ha

theorem pin54 : topOf [] [1] = none ∧ topOf [] [0] = some ⟨0, slotpower.unitV⟩ := by
  decide +kernel

theorem pin55 : (blockWeights memtable.genG2 topsG2 [0, 1]).length = 14 :=
  (blockWeights_length memtable.genG2 topsG2 [0, 1]).trans pin39.2.2.2

theorem pin56 (a : List Nat) (ha : a.length = 2) :
    ∃ t, topOf topsG2 a = some t ∧ slotpower.keysRead memtable.genG2.keys t.2
      ∧ slotpower.homogRead memtable.genG2 (List.replicate t.1 false) t.2 (a.map ground.BPair.ofNat) :=
  topOf_weight_G2 a ha

theorem pin57 (a : List Nat) (ha : a.length = 2) :
    a.map ground.BPair.ofNat ∈ blockWeights memtable.genG2 topsG2 a := blockWeights_top_G2 a ha

theorem pin58 (a : List Nat) (ha : a.length = 2) :
    0 < (blockWeights memtable.genG2 topsG2 a).length := blockWeights_pos_G2 a ha

/-- The constructed G2 top reads every simple raising at the unit
at every label of the member's width. -/
theorem pin59 (a : List Nat) (ha : a.length = 2) :
    ∃ v, topOf topsG2 a = some v
      ∧ slotpower.raisedUnit memtable.genG2 (List.replicate v.1 false)
        (slotpower.castV (ground.length_replicate false v.1).symm v.2) = true :=
  topOf_raisedUnit_G2 a ha

/-- An actual label block at extra fuel reads its original list. -/
theorem pin60 (a : List Nat) (t : slotpower.WVec) (ht : topOf topsG2 a = some t) (extra : Nat) :
    blockAt memtable.genG2 topsG2 a =
      ((slotpower.closeT memtable.genG2 (List.replicate t.1 false)
        ((List.replicate t.1 false).length * memtable.genG2.keys + 1 + extra)
        (slotpower.tryAddT memtable.genG2 (List.replicate t.1 false) []
          (slotpower.castV (ground.length_replicate false t.1).symm t.2))
        [slotpower.castV (ground.length_replicate false t.1).symm t.2]).map
        (slotpower.castV (ground.length_replicate false t.1))).map
          (slotpower.castV (topOf_degree topsG2 a t ht)) :=
  blockAt_fuel_G2 topsG2 a t ht extra

/-- Every label's constructed G2 block has an independent
coordinate list, with its actual computed degree. -/
theorem pin61 (a : List Nat) (ha : a.length = 2) :
    let ms := places.allMon memtable.genG2.keys (degOf topsG2 a)
    elim.indepRows ms.length ((blockAt memtable.genG2 topsG2 a).map (slotpower.coordsV ms)) :=
  blockAt_indep_G2 a ha

end fiber
