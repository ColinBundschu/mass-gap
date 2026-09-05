import MassGap.Fiber
import MassGap.Adjchar
import MassGap.Xfusion
import MassGap.Carrier
/-!
The check module for `con:fiber`: the batteries re-read the fiber's
pairing by kernel `decide` at the presentation's own values —
`⟨tr U, tr U⟩ = 1` at the one-factor site, and at the adjoint site
`⟨χ_adj, χ_adj⟩ = 1` with `⟨1, χ_adj⟩` of equal members at
`χ_adj = |tr U|² - [1 : d_f] tr(U U†)`, `prop:wg`'s pinned
Weingarten values read through the fiber's own display; and the
carrier's vertex lists at the label calculus, the interpolant's
validity, the two-end coevaluation at the block's count with the
symbolic route's own read there, at the wiring and at the star, the
three- and four-end adjoint Grams at both tags with the direct
tag's members at their primitive representatives in the slot
power's coordinates, one value at the orientation spellings of a
self-dual vertex, the direct route's scale at two ends beside the
coevaluation's, the two-end reads at every orientation, the
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
set_option maxHeartbeats 4000000

open ground places poly genericlift states fiber

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

example : crossNull (pairP fU fU trU trU) pOne := by decide +kernel
example : crossNull (pairP fAdj fAdj adjC adjC) pOne := by decide +kernel
example : crossNull (pairP fAdj fAdj unitC adjC) pZero := by decide +kernel

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

example : interpValid 2 (th 2) = true ∧ interpValid 3 (th 3) = true
    ∧ interpValid 3 (fd 3) = true ∧ interpValid 4 [1, 1, 0, 0] = false
    ∧ interpValid 4 [2, 1, 0, 0] = false ∧ interpValid 4 [0, 2, 0, 0] = false := by
  decide +kernel
example : interpNodes 3 (th 3) = [labels.unitL 3] := by decide +kernel

example : vertGramA 2 [(th 2, true), (th 2, false)] = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 3 [(fd 3, true), (fd 3, false)] = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 3 [(th 3, true), (th 3, true)] = ([[BPair.ofNat 8]], Pos.one)
    ∧ vertGramA 3 [(fd 3, true), (fd 3, true)] = ([], Pos.one)
    ∧ vertGramA 3 [] = ([[BPair.ofNat 1]], Pos.one) := by decide +kernel
example : listGram (vertListSym 3 [(th 3, true), (th 3, false)]) = ([[BPair.ofNat 8]], Pos.one)
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

example : vertGramA 3 [(th 3, false), (th 3, false)] = ([[BPair.ofNat 8]], Pos.one)
    ∧ vertGramA 3 [(fdb 3, false), (fd 3, false)] = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 3 [(fd 3, false), (fd 3, true)] = ([[BPair.ofNat 3]], Pos.one)
    ∧ vertGramA 3 [(fd 3, true), (fdb 3, true)] = ([[BPair.ofNat 3]], Pos.one) := by
  decide +kernel
example : vertGramA 4 [([1, 1, 0, 0], true), ([1, 1, 0, 0], false)]
    = ([[BPair.ofNat 20]], Pos.one) := by decide +kernel

/-! The symbolic members' Gram at the cycle counts is the members'
coordinate pairing, the fast read tied to the graded vectors at
the three-end adjoint vertex over three letters at both
orientations and at the two-end symbolic reads. -/

example : (vertListSym 3 [(th 3, true), (th 3, true), (th 3, false)]).members.gram
      = slotpower.gramOf
        (vertListSym 3 [(th 3, true), (th 3, true), (th 3, false)]).members.list
    ∧ (vertListSym 3 [(th 3, true), (th 3, false), (th 3, false)]).members.gram
      = slotpower.gramOf
        (vertListSym 3 [(th 3, true), (th 3, false), (th 3, false)]).members.list
    ∧ (vertListSym 2 [(th 2, true), (th 2, false)]).members.gram
      = slotpower.gramOf (vertListSym 2 [(th 2, true), (th 2, false)]).members.list
    ∧ (vertListSym 3 [(fd 3, true), (fd 3, false)]).members.gram
      = slotpower.gramOf (vertListSym 3 [(fd 3, true), (fd 3, false)]).members.list := by
  decide +kernel

/-! The direct route's scale at two ends beside the coevaluation's:
the kernel member at its primitive representative in the slot
power's coordinates self-pairs at twelve over two letters and at
seventy-two over three, where the coevaluation reads the counts
three and eight; and the coevaluation's clearing at the grouped
solve, three at the adjoint over three letters and two over two. -/

example : posVal (twoEndList 3 (th 3, true) (th 3, false)).clear = 3
    ∧ posVal (twoEndList 2 (th 2, true) (th 2, true)).clear = 2 := by decide +kernel

example : listGram (vertListDirect 2 [(th 2, true), (th 2, true)])
      = ([[BPair.ofNat 12]], Pos.one)
    ∧ listGram (vertListDirect 3 [(th 3, true), (th 3, false)])
      = ([[BPair.ofNat 72]], Pos.one) := by decide +kernel

private def g3 : elim.Mat × Pos :=
  ([[BPair.ofNat 56, (BPair.ofNat 16).swap], [(BPair.ofNat 16).swap, BPair.ofNat 56]], 3)
private def g4 : elim.Mat × Pos :=
  ([[BPair.ofNat 105, (BPair.ofNat 15).swap], [(BPair.ofNat 15).swap, BPair.ofNat 105]], 2)

example : vertGramA 3 [(th 3, true), (th 3, true), (th 3, false)] = g3
    ∧ vertGramA 3 [(th 3, true), (th 3, false), (th 3, false)] = g3
    ∧ vertGramA 4 [(th 4, true), (th 4, true), (th 4, false)] = g4 := by decide +kernel
example : (vertGramA 3 [(th 3, true), (th 3, true), (th 3, false)]).1.length
      = xfusion.c1 3
    ∧ (elim.detD g3.1).oneValue (BPair.ofNat 2880) := by decide +kernel

/-- The eigen-read at a three-end adjoint vertex: every projected
wiring at every link's cleared insertion reads the adjoint's cleared
Casimir `dfQ θ` times itself. -/
private def eigenRead (d : Nat) (es : List (Shape × Bool)) : Bool :=
  let ends := linkEnds d es 0 0
  let k := ground.sumNat (ends.map (fun e => e.1.length))
  (places.perms k).all (fun σ =>
    let v := projVertex d es [(σ, BPair.ofNat 1)]
    ends.all (fun e =>
      vOneValue (linkCasC d e.1 e.2 v)
        (v.map (fun t => (t.1, t.2 * BPair.ofNat (c2hat.dfQ (th d)))))))

example : eigenRead 3 [(th 3, true), (th 3, true), (th 3, false)] = true
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

example : vertGramA 2 [(th 2, true), (th 2, true), (th 2, false)]
      = ([[BPair.ofNat 12]], Pos.one)
    ∧ vertGramA 2 [(th 2, true), (th 2, true), (th 2, true)]
      = ([[BPair.ofNat 12]], Pos.one)
    ∧ vertGramA 2 [(fd 2, true), (th 2, true), (fd 2, false)]
      = ([[BPair.ofNat 12]], Pos.one) := by decide +kernel
example : vertGramA 2 [(th 2, true), (th 2, true), (th 2, false), (th 2, false)]
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

example : vertGramA 3 [(fd 3, true), (fd 3, true), (fd 3, true)]
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
  let l := fiber.linkCasC d rs cs [(σ, BPair.ofNat 1)]
  let a := actAtRes d k F W σ
  ((l ++ a.map (fun e => (e.1, BPair.unit))).map Prod.fst).all (fun w =>
    let x := fiber.coefAt w l
    let y := a.foldl (fun acc e => if e.1 == w then acc + e.2 else acc)
      (⟨BPair.unit, Pos.one⟩ : CPair)
    ((⟨BPair.ofNat (2 * d), Pos.one⟩ : CPair) * y).oneValue ⟨x, Pos.one⟩)

/-- Two ends of one link among two, and the four ends of one link
at a two-row two-column word. -/
private def fTwo : FList := [(0, false), (1, false), (1, true), (0, true)]
private def fFour : FList := [(0, false), (0, false), (0, true), (0, true)]

example : (places.perms 2).all (fun σ => casTie 2 2 fTwo 0 [0] [1] σ) = true
    ∧ (places.perms 2).all (fun σ => casTie 3 2 fTwo 0 [0] [1] σ) = true
    ∧ (places.perms 2).all (fun σ => casTie 3 2 fFour 0 [0, 1] [0, 1] σ) = true
    ∧ (places.perms 2).all (fun σ => casTie 4 2 fFour 0 [0, 1] [0, 1] σ) = true := by
  decide +kernel

/-! The letter count at the members: the wirings' stated count at
the symbolic three-end vertex, the coordinate families' width at
the direct-tag list and at the unit state's list. -/

example : (vertListSym 3 [(th 3, true), (th 3, true), (th 3, false)]).members.letters = 3
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

example : (linkList 3 [true, false, false, true, false, true]).1.length = 6
    ∧ (linkList 3 [true, false, false, true, false, true]).2 = mixedinv.cycleGram 3 3
    ∧ (elim.detD (linkList 3 [true, false, false, true, false, true]).2).oneValue
        (BPair.ofNat 119439360)
    ∧ (linkList 2 [true, true, false, true, false, false]).1.length = 5
    ∧ (elim.detD (linkList 2 [true, true, false, true, false, false]).2).oneValue
        (BPair.ofNat 5184)
    ∧ (linkList 3 [true, false]).1.length = 1
    ∧ (linkList 3 [true, false]).2 = [[BPair.ofNat 3]] := by decide +kernel
example : (coevW [[BPair.ofNat 4, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 4]]).2.oneValue
      (BPair.ofNat 12)
    ∧ elim.matOneValue
        (elim.matMul [[BPair.ofNat 4, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 4]]
          (coevW [[BPair.ofNat 4, BPair.ofNat 2], [BPair.ofNat 2, BPair.ofNat 4]]).1)
        [[BPair.ofNat 12, BPair.unit], [BPair.unit, BPair.ofNat 12]] := by decide +kernel
