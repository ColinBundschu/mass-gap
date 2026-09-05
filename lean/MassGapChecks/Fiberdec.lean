import MassGap.Fiberdec
/-!
The check module for `lem:fiberdec`: the batteries re-read the
fibering's carrier and its translation by kernel `decide`.  The two
region builders are read at three windows — the plaquette chain at
cycle lengths three and five, and the two-direction torus at side
three — the interface's shape, plaquette and simplicity reads
holding at each, with the coloring read taken at the even side,
where the two-coloring exists, and refused at the three odd-side
windows: the even-cycle read is the region family's field, a
winding cycle reads the side's parity, and the refusals beside the
readings are the two families' separation.  The
translation is read at all
three, both torus directions among them: the permutation with its
witness, the endpoints transported along the induced vertex
permutation with that vertex map itself read a permutation of the
vertex range, the plaquette list mapping into itself, and the
`L`-fold iterate the identity, each beside the refusal that
isolates it — a map paired with itself in place of its witness
fails the composition read, a wrong iterate count fails the cycle
read, and a transposition of a rung with a rail keeps the
permutation read while failing the plaquette read.  The index
action rides at the chain window over the label calculus at two
letters: the enumeration is pinned once at its five members (three
squares and the two rails), the content, the occupancy and the
index closure are fixed at the action, and the congruence
`Pmᵀ H Pm = H` holds at the free end's window matrix on the window
list — every fiber at its one slot there, the window list's
diagonal the index's contents — the same transposition, which moves
a rail loop off the index, failing the closure and the congruence
together; the place action's four binders refuse on its own
carrier, and a three-letter fixture with fibers of four slots reads
the congruence at the vertex witness and refuses it at the identity
in the witness's place.

The chord tier rides on the translation's own link permutation
(`permMatAt`), the cheapest faithful carrier for identities that
are matrix-level: the side-three bench at order nine and the
committed side-five chain at order fifteen.  The orthogonality is
discharged at both sides by `permRead_orth` rather than decided —
the permutation read the module already commits is its one
hypothesis — and the deck relation follows it, decided at side
three and discharged by `chord_deck` at side five.  The word
identity, the word's two fixed reads and the annihilation are read
at each side's own symbol (`m = 1` at side three, `m = 2` at side
five).  The word's two fixed reads are discharged rather
than decided — `fixedWord_perm` at the side-three window and
`fixedWord_of` at the free orbit, the word identity their one
further hypothesis — with the geometric word's own `T`-multiple
read (`wordSum_fixed`) and the witness's read
(`inertia.fixed_transpose`) discharged beside them at the orbit,
and the cycle read shown load-bearing by the transposition's
refusal.  The chord's
doubling on the fixed word is `chord_join`'s instance at the free
orbit, the translation restricted to the chain's rung range, order
five: the tex's own free orbit, where the base-rational splitting
runs whole — the unit fiber's one member with its fixed read, the
four-member spanning list of `P_L(S)`'s kernel, the concatenation's
congruence carrying the window datum `S - 1` to the two blocks'
join, and the count splitting at `lem:inertia`'s `rev_join`, four
against nought and four.  The sampled momenta are the two brackets
of `P_5 = w² + w - 1` at width one sixteenth, the separation's own
`δ` at half of it, with the chord `2` off the roots at the division
display `P_5(2) = 5`.

The refusals isolate each read.  The orthogonality and the deck
relation fail at the chord operator itself, a symmetric matrix off
the permutations — and they hold at the rung-and-rail
transposition, which is a permutation: the deck relation is the
orthogonality's own consequence (`chord_deck`), so what the
transposition breaks is the cycle, and the annihilation is where it
shows.  The annihilation refuses three ways besides: at that
transposition's order-two matrix, at the wrong side's symbol
(`P_3` against the side-five orbit), and at a symbol with one
coefficient moved.  The count split refuses at a congruence whose
first member leaves the unit fiber, the off-block no longer equal
members.

The permutation-matrix kit is discharged at the committed windows:
the composition read at the chain's translation against itself, the
identity map's matrix, the transpose as the witness's own matrix,
and the fifth power at the side-five chain read twice — once
against the iterate's matrix, once against the identity through
`cycleRead_pow`.  Its range clause is shown load-bearing by a
refusal, a map whose values leave the key range emptying its matrix
so that the composition read fails against the composite's own.

The residue tier rides at the side-five orbit.  The deck symbol's
monic display decides, the deck-family column reads the membership
`S u = x u` at the recursion closing cyclically, the doubling
datum's image is perpendicular to the column, the pair's Gram
determinant `300 + 100x` reads the occupied constant `50000`
against its Bézout cofactor `200 - 100x` modulo `P_5`, and the
count squeeze reads the orbit's two root blocks at `1 + 4 = 5`.
The refusals sit at the wrong side's symbol (the side-three residue
against the side-five orbit, where the wrap has period three), at
the column with two of its keys exchanged, at the chord operator in
place of the doubling datum for the perpendicularity, and at a
dependent pair for the independence.  One expected refusal is
instead a recorded reading: the `Q`-family column satisfies the
membership read too, the two families running the one recursion and
differing only at their seeds, so what the tex's own column carries
beyond `Q`'s is the seed `p₀ = 2` rather than the membership.  The
vector bridge closes the residue tier: two entrywise wrap
congruences at side five read one residue vector (`prow_redP`), and
the read refuses at an entry pair the symbol does not join.

The tier's theorem routes stand beside those kernel reads, each
discharged rather than decided.  The membership is
`colMember_wrap`'s at sides three, five and seven; the
perpendicularity is `perp_band`'s at every square datum — read here
at a forged three-by-three matrix off the permutations, where no
cyclic structure is available to the pairing — with `perp_wrap` its
instance at the wrap shift's matrix, sides five and seven; and the
self-pairing is `deckColumn_selfPair`'s at sides five and seven,
each beside its kernel twin and its wrong-constant refusal.  The
independence carries two witnesses at once: `orbCof`, the
witness-parametric read at the side-five orbit, and `gramCof`, the
tex's divided-cofactor witness — the deck symbol divided by the
chord's two linear factors — whose cleared constant is `4L³` at the
side's own parity member, read at sides five and seven.

The band tier's own instances close the module: the band root at a
rational bench chord — the located roots of `P_5` are irrational
and enter over `lem:stagesplit`'s quadratic extension, so the
ground-arithmetic reading is the chord `1` at the clearing `2`,
`4s² + t² = 4` giving `s² = 3/4` — and the band congruence at the
orbit's own two-member compression, the descent rescaling the image
column, with the image at the shape `lem:cellcount`'s counts
consume and the identity descent its refusal.

The magnetic member's transport reads at the side-three chain
window beside the electric member's congruence: the plaquette list
permuted by the translation as stated data, the plaquette terms
at the support's shape transported plaquette by plaquette, the
terms' sum moved along the action and commuting with the induced
permutation matrix, decided and routed through
`movedReadBy_termSum`, `commRead_slotM` and `commRead_slotM_dataA`,
and the pencil interface's read at the window with its magnetic
member commuting through `commRead_pencilM_dataA`, every binder
at its refusal; the fibers of four slots read the transport with
the vertex witness load-bearing at the magnetic member as at the
electric.

Budget exception: the window enumeration reads through the
content-pruned identity (`carrier.idxA_eq`), the pin's route
rather than its statement, and the module's cost is the `apply
perp_band` route at the forged three-by-three datum with the
index-action band at the side-nine window beside it (`commRead`
over `slotMat fA chW chIx` at the translation's two witnesses, with
`occFixed` / `contentFixed` / `idxFixed` at the link witness) and
the pencil interface's read at the chain window, whose six cap
splits at order six read through `inertia.splitRead` with
`psdAt` one kernel task per split read, the kernel keeping every
reduced subterm of one task until it closes, so a conjunction of
split reads decided at once costs the sum of their caches where
the reads decided one by one cost each its own.
-/
set_option maxHeartbeats 16000000

open ground lattice fusion elim carrier fiberdec

/-! The chain's boundary configurations, the tier's shared
fixtures: one builder at a stated label pair with the elementary
loop its fundamental instance. -/

namespace fiberdec

/-- A boundary configuration on one square of the chain: the
forward boundary entries at a stated label, the reversed at a
second, the further keys at the unit. -/
def loopConf (Lc i : Nat) (fwd bwd : places.Shape) :
    List places.Shape :=
  let R := chainRegion Lc
  let p := ground.getAt [] R.plaqs i
  (List.range R.links).map (fun l =>
    if p.any (fun e => e.1 == l && e.2) then fwd
    else if p.any (fun e => e.1 == l && !e.2) then bwd
    else [0, 0, 0])

/-- The elementary loop on one square of the chain: the forward
boundary entries at the fundamental label, the reversed at its
dual, the further keys at the unit. -/
def loopAt (Lc i : Nat) : List places.Shape :=
  loopConf Lc i [1, 0, 0] [0, 1, 0]

end fiberdec

/-! The two carriers' interface reads at the three windows. -/

private theorem chWell3 : wellRead (chainRegion 3) := by decide +kernel
example : wellRead (chainRegion 5) := by decide +kernel
example : wellRead (torusRegion 2 3) := by decide +kernel

example : plaqRead (chainRegion 3) := by decide +kernel
example : plaqRead (chainRegion 5) := by decide +kernel
example : plaqRead (torusRegion 2 3) := by decide +kernel

example : simpleRead (chainRegion 3) := by decide +kernel
example : simpleRead (chainRegion 5) := by decide +kernel
example : simpleRead (torusRegion 2 3) := by decide +kernel

/-! The shapes at their counts: the chain's `3L` links over `2L`
vertices with its `L` squares, and the torus's `d · L^d` links over
`L^d` sites with one square per site and direction pair. -/

example : (chainRegion 3).links = 9 ∧ (chainRegion 3).verts = 6
    ∧ (chainRegion 3).plaqs.length = 3 := by decide +kernel
example : (chainRegion 5).links = 15 ∧ (chainRegion 5).verts = 10
    ∧ (chainRegion 5).plaqs.length = 5 := by decide +kernel
example : (torusRegion 2 3).links = 18 ∧ (torusRegion 2 3).verts = 9
    ∧ (torusRegion 2 3).plaqs.length = 9 := by decide +kernel

/-! The two-coloring at the even side, where the vertices admit
one: the chain's rails and the torus's own cycles read their
length there. -/

example : colorRead (chainRegion 4) := by decide +kernel
example : colorRead (torusRegion 2 4) := by decide +kernel

/-! The two families' separation read (`con:lattice`): the
even-cycle read is the region family's field, and each refusal
below decides that field off the coloring these three windows
commit.  The tex's winding-parity sentence is the wider statement —
at odd side a winding cycle reads the side's parity, so every
coloring of such a window meets an odd cycle — and these committed
readings are its exhibits, the rest of the interface holding at
each. -/

example : ¬ colorRead (chainRegion 3) := by decide +kernel
example : ¬ colorRead (chainRegion 5) := by decide +kernel
example : ¬ colorRead (torusRegion 2 3) := by decide +kernel

/-! The translation's four reads at the three windows, both torus
directions among them. -/

private theorem chPerm3 :
    permRead (chainRegion 3) (chainTransl 3) (chainTranslInv 3) := by
  decide +kernel
private theorem chPerm5 :
    permRead (chainRegion 5) (chainTransl 5) (chainTranslInv 5) := by
  decide +kernel
example : permRead (torusRegion 2 3) (torusTransl 2 3 0)
    (torusTranslInv 2 3 0) := by decide +kernel
example : permRead (torusRegion 2 3) (torusTransl 2 3 1)
    (torusTranslInv 2 3 1) := by decide +kernel

/-! The composition clause (`con:lattice`): the two directions'
shifts compose to one map at either order, the read decided with
its key extraction and the matrices' commutation routed, and the
refusal at a pair off the clause — a direction's shift against the
region's own key involution fails the read at a moved key. -/

example : commutesRead (torusRegion 2 3) (torusTransl 2 3 0)
    (torusTransl 2 3 1) := by decide +kernel
example : commutesRead (torusRegion 2 3) (torusTransl 2 3 0)
    (torusTranslInv 2 3 0) := by decide +kernel
example : torusTransl 2 3 0 (torusTransl 2 3 1 4)
    = torusTransl 2 3 1 (torusTransl 2 3 0 4) :=
  commutesRead_at (torusRegion 2 3) (torusTransl 2 3 0)
    (torusTransl 2 3 1) (by decide +kernel) 4 (by decide +kernel)
example : matOneValue
    (matMul (permMatAt 18 (torusTransl 2 3 0))
      (permMatAt 18 (torusTransl 2 3 1)))
    (matMul (permMatAt 18 (torusTransl 2 3 1))
      (permMatAt 18 (torusTransl 2 3 0))) :=
  permMatAt_comm 18 (torusTransl 2 3 0) (torusTransl 2 3 1)
    (fun j hj => by revert j; decide +kernel)
    (fun j hj => by revert j; decide +kernel)
    (fun l hl => by revert l; decide +kernel)
example : ¬ commutesRead (torusRegion 2 3) (torusTransl 2 3 0)
    (fun l => 17 - l) := by decide +kernel

private theorem chEnds3 :
    endsRead (chainRegion 3) (chainTransl 3) (chainVert 3) := by
  decide +kernel
example : endsRead (chainRegion 5) (chainTransl 5) (chainVert 5) := by
  decide +kernel
example : endsRead (torusRegion 2 3) (torusTransl 2 3 0)
    (shiftSite 3 0) := by decide +kernel
example : endsRead (torusRegion 2 3) (torusTransl 2 3 1)
    (shiftSite 3 1) := by decide +kernel


private theorem chVert3 :
    vertPermRead (chainRegion 3) (chainVert 3) (chainVertInv 3) := by
  decide +kernel
example : vertPermRead (chainRegion 5) (chainVert 5) (chainVertInv 5) := by
  decide +kernel
example : vertPermRead (torusRegion 2 3) (shiftSite 3 0)
    (shiftSiteInv 3 0) := by decide +kernel
example : vertPermRead (torusRegion 2 3) (shiftSite 3 1)
    (shiftSiteInv 3 1) := by decide +kernel

example : plaqPermRead (chainRegion 3) (chainTransl 3) (fun _ => false)
    (fun q => ground.getAt 0 [1, 2, 0] q) (fun q => ground.getAt 0 [2, 0, 1] q) := by
  decide +kernel
example : plaqPermRead (chainRegion 5) (chainTransl 5) (fun _ => false)
    (fun q => ground.getAt 0 [1, 2, 3, 4, 0] q)
    (fun q => ground.getAt 0 [4, 0, 1, 2, 3] q) := by decide +kernel
example : plaqPermRead (torusRegion 2 3) (torusTransl 2 3 0) (fun _ => false)
    (fun q => ground.getAt 0 [1, 2, 0, 4, 5, 3, 7, 8, 6] q)
    (fun q => ground.getAt 0 [2, 0, 1, 5, 3, 4, 8, 6, 7] q) := by decide +kernel
example : plaqPermRead (torusRegion 2 3) (torusTransl 2 3 1) (fun _ => false)
    (fun q => ground.getAt 0 [3, 4, 5, 6, 7, 8, 0, 1, 2] q)
    (fun q => ground.getAt 0 [6, 7, 8, 0, 1, 2, 3, 4, 5] q) := by decide +kernel

example : cycleRead (chainRegion 3) (chainTransl 3) 3 := by decide +kernel
private theorem chCyc5 : cycleRead (chainRegion 5) (chainTransl 5) 5 := by
  decide +kernel
example : cycleRead (torusRegion 2 3) (torusTransl 2 3 0) 3 := by decide +kernel
example : cycleRead (torusRegion 2 3) (torusTransl 2 3 1) 3 := by decide +kernel

/-! The refusals isolating the reads: a map paired with itself in
place of its witness, and the iterate at a count below the side. -/

example : ¬ permRead (chainRegion 3) (chainTransl 3) (chainTransl 3) := by
  decide +kernel
example : ¬ permRead (torusRegion 2 3) (torusTransl 2 3 0)
    (torusTransl 2 3 0) := by decide +kernel
example : ¬ cycleRead (chainRegion 3) (chainTransl 3) 2 := by decide +kernel
example : ¬ cycleRead (torusRegion 2 3) (torusTransl 2 3 1) 2 := by decide +kernel

/-! The rung-and-rail transposition: a permutation of the link keys
that moves a square's boundary off the plaquette list at every
position, so the plaquette permutation read refuses at the
identity data and at every stated position. -/

private def swapRR : Nat → Nat :=
  fun l => if l == 0 then 3 else if l == 3 then 0 else l

example : permRead (chainRegion 3) swapRR swapRR := by decide +kernel
example : ¬ plaqPermRead (chainRegion 3) swapRR (fun _ => false) (fun q => q) (fun q => q)
    ∧ ((List.range 3).all (fun p =>
        !cycEq (moveWord swapRR (fun _ => false)
            (ground.getAt [] (chainRegion 3).plaqs 0))
          (ground.getAt [] (chainRegion 3).plaqs p))) = true := by
  decide +kernel

/-! The index action at the chain window over the label calculus at
two letters: the enumeration pinned once at its five members, the
two rail loops then the three squares. -/

private def fA : Data places.Shape := tabulate (dataA 2) 12
private def chW : Region := chainRegion 3
private def chIx : List (List places.Shape) :=
  [[[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [1, 0], [1, 0], [1, 0]],
   [[0, 0], [0, 0], [0, 0], [1, 0], [1, 0], [1, 0], [0, 0], [0, 0], [0, 0]],
   [[0, 0], [1, 0], [1, 0], [0, 0], [1, 0], [0, 0], [0, 0], [1, 0], [0, 0]],
   [[1, 0], [0, 0], [1, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0], [1, 0]],
   [[1, 0], [1, 0], [0, 0], [1, 0], [0, 0], [0, 0], [1, 0], [0, 0], [0, 0]]]
/-! The diagonal's two `9`s are the rail loops' winding content at
this window: a winding support of `L = 3` links, each at the member
floor `3`, against the plaquette level `4 · 3 = 12`.  At side three
the winding content sits below that level, and from side five it
reads at or beyond it (`5 · 3 = 15`) — the fibering's family
restriction at its own exhibit, and by design here, where the
window prices the carrier and the translation reads alone. -/

private def chDiag : List Nat := [0, 9, 9, 12, 12, 12]

/-! The one enumeration the module prices: the window index at its
five members.  Every read below runs on the pinned list, the
window list's diagonal among them — every fiber at one slot here,
the diagonal the index's contents with the unit line at its head,
so the pin carries it.  The pin's
statement is `def:carrier`'s own enumeration; its route is the
content-pruned read beside it (`carrier.idxA_eq`), ten times
cheaper at this window. -/

private theorem chIxPin : idx fA chW 12 = chIx := by
  rw [← idxA_eq]
  decide +kernel

example : pairpencil.slotDiag fA chW (idx fA chW 12) = chDiag := by
  rw [chIxPin]
  decide +kernel

/-! The three index reads at the action, the witness's own map the
relabeling: the content, the occupancy and the closure fixed. -/

example : contentFixed fA chW chIx (chainTranslInv 3) := by decide +kernel
example : occFixed fA chW chIx (chainTranslInv 3) := by decide +kernel
example : idxFixed fA chW chIx (chainTranslInv 3) := by decide +kernel

/-! The content and the occupancy fixed through the theorems at
the label calculus itself, the pinned index's members the width-two
labels at the window's link count: the content by the region's own
action (`contentN_perm`) and the occupancy by the transport at the
count laws discharged over the labels (`occupied_perm_dataA`), each
beside the decided read above. -/

private theorem chIxLabels :
    (chIx.all (fun a => a.all (labelA 2))) = true := by decide +kernel
private theorem chIxLen : (chIx.all (fun a => a.length == 9)) = true := by
  decide +kernel

example : contentFixed (dataA 2) chW chIx (chainTranslInv 3) :=
  contentFixed_of (dataA 2) chW chIx (chainTranslInv 3) (fun a ha =>
    contentN_perm (dataA 2) chW (chainTransl 3) (chainTranslInv 3) chPerm3 a
      (ground.beqEqOf (ground.all_of_mem _ _ chIxLen a ha)))
example : occFixed (dataA 2) chW chIx (chainTranslInv 3) :=
  occFixed_of (dataA 2) chW chIx (chainTranslInv 3) (fun a ha =>
    occupied_perm_dataA 2 chW chWell3 (chainTransl 3) (chainTranslInv 3)
      (chainVert 3) (chainVertInv 3) chPerm3 chEnds3 chVert3 a
      (ground.all_of_mem _ _ chIxLabels a ha))

/-! The closure through the theorem at the label calculus: the
enumeration itself at the untabulated interface reads the pinned
list, and the window index maps within itself at the translation
(`idxFixed_dataA`), the decided read above its companion. -/

private theorem chIxPinA : idx (dataA 2) chW 12 = chIx := by
  rw [← idxA_eq]
  decide +kernel

example : idxFixed (dataA 2) chW chIx (chainTranslInv 3) := by
  rw [← chIxPinA]
  exact idxFixed_dataA 2 chW 12 chWell3 (chainTransl 3) (chainTranslInv 3)
    (chainVert 3) (chainVertInv 3) chPerm3 chEnds3 chVert3

/-! The congruence's data at the pinned index, every fiber at its
one slot: the window list is the index with the vacant key per
member and its diagonal is the index's contents (`slotDiag_unit`'s
instance, decided beside the theorem), the window list meets each
member's image once, its equality read is structural on the image
pairs, and the electric member's entries move along the
translation — each decided and each the theorem's own at the label
calculus — with the congruence at the free end's window matrix
read through `commRead_slotE_dataA` beside the decided read.  The
transposition's refusal: the moved lower rail loop meets the window
list at no member. -/

private def chSlots : List (List places.Shape × List Nat) :=
  chIx.map (fun a => (a, List.replicate 6 0))
private def chAct : List places.Shape × List Nat → List places.Shape × List Nat :=
  slotAct (dataA 2) (chainTranslInv 3) (chainVertInv 3) 9 6

example : pairpencil.slotList (dataA 2) chW chIx = chSlots := by decide +kernel
private theorem chSlotDiag : pairpencil.slotDiag (dataA 2) chW chIx = chDiag := by
  decide +kernel
example : pairpencil.slotDiag (dataA 2) chW chIx = chDiag :=
  (pairpencil.slotDiag_unit (dataA 2) chW chIx (by decide +kernel)).trans
    (by decide +kernel)
example : imgOnceBy (slotEq (dataA 2)) chAct
    (pairpencil.slotList (dataA 2) chW chIx) := by decide +kernel
example : imgEqBy (slotEq (dataA 2)) chAct
    (pairpencil.slotList (dataA 2) chW chIx) := by decide +kernel
example : ground.distinctList (pairpencil.slotList (dataA 2) chW chIx) := by
  decide +kernel
example : movedReadBy (slotEq (dataA 2)) chAct
    (pairpencil.slotList (dataA 2) chW chIx) (pairpencil.pencilE chDiag) := by
  decide +kernel
private theorem chOnce : imgOnceBy (slotEq (dataA 2))
    (slotAct (dataA 2) (chainTranslInv 3) (chainVertInv 3) chW.links chW.verts)
    (pairpencil.slotList (dataA 2) chW chIx) := by
  rw [← chIxPinA]
  exact slotOnce_dataA 2 chW 12 chWell3 (chainTransl 3) (chainTranslInv 3)
    (chainVert 3) (chainVertInv 3) chPerm3 chEnds3 chVert3
example : imgEqBy (slotEq (dataA 2))
    (slotAct (dataA 2) (chainTranslInv 3) (chainVertInv 3) chW.links chW.verts)
    (pairpencil.slotList (dataA 2) chW chIx) := by
  rw [← chIxPinA]
  exact slotEq_dataA 2 chW 12 (chainTranslInv 3) (chainVertInv 3)
example : ground.distinctList (pairpencil.slotList (dataA 2) chW chIx) := by
  rw [← chIxPinA]
  exact pairpencil.slotList_distinct (dataA 2) chW _
    (idx_distinct (dataA 2) chW 12 (below_distinct_dataA 2 12))
example : ¬ imgOnceBy (slotEq (dataA 2))
    (slotAct (dataA 2) swapRR (fun v => v) 9 6)
    (pairpencil.slotList (dataA 2) chW chIx) := by decide +kernel

/-! The magnetic member's transport at the chain window.  The
translation permutes the plaquette list, the moved positions
`[1, 2, 0]` with the witness's `[2, 0, 1]` the action's plaquette
permutation as stated data (`plaqPermRead`, each image word the
moved position's own at the cyclic reading; the read at the
witness's map with the data exchanged, and refused at the data
crossed and at the map's own permutation for its witness).  The
plaquette terms enter as stated data at the support's shape: per
plaquette the matrix reading a pair at every position pair whose
configurations meet across the plaquette's changed edge
(`algebra.plaqRow`'s targets at the window positions), the unit
elsewhere.  The terms' transport is decided, the terms' sum's
moved read decided and routed through `movedReadBy_termSum`, and
the congruence at the sum decided and routed through
`commRead_slotM` at the pinned index with the window list met once
by the calculus's own read (`slotOnce_dataA` at the pinned
enumeration) and through `commRead_slotM_dataA` at the index tied
to the window's own.  The pencil interface's read at the chain
window closes the tier, `commRead_pencilM_dataA`'s route: the
electric member at the window list's diagonal, the identity gram
at its split, the three terms with their two cap splits at the
adjoint dimension three, and the magnetic member the terms' sum,
the induced permutation matrix commuting with the member through
the interface's own read.  The refusals, each isolating one binder
with its companions decided: the terms with one entry of the first
plaquette's term forged off its moved twin at two moved positions
part the terms' transport, the sum's moved read and the
congruence; an entry forged at two fixed positions, the rail
loops', parts the terms' transport alone, the sum's moved read
and the congruence holding, the sum blind to a term's own twin at
fixed positions; a fourth term beyond the plaquette count parts
the sum's moved read with the transport holding, the count tie; a
term with one row truncated parts the sum's moved read with the
transport holding, the order binder, the entrywise sum truncating
at the shorter operand; and a window list with one member listed
twice under the identity action refuses the once-met read with
the transport and the sum's moved read holding and the congruence
parting, `commRead_slotM`'s once-met binder off the sum lemma.
The plaquette read's one listing per plaquette refuses at a
plaquette listed twice and at a plaquette listed beside its
rotation, the second at the structural distinctness holding. -/

private def chPmT : Nat → Nat := fun q => ground.getAt 0 [1, 2, 0] q
private def chPmS : Nat → Nat := fun q => ground.getAt 0 [2, 0, 1] q

private theorem chPlaqT :
    plaqPermRead chW (chainTransl 3) (fun _ => false) chPmT chPmS := by
  decide +kernel
example : plaqPermRead chW (chainTranslInv 3) (fun _ => false) chPmS chPmT := by
  decide +kernel
example : ¬ plaqPermRead chW (chainTransl 3) (fun _ => false) chPmS chPmT
    ∧ ¬ plaqPermRead chW (chainTransl 3) (fun _ => false) chPmT chPmT := by
  decide +kernel

private def chTerm (p : List (Nat × Bool)) : Mat :=
  ground.matOf 6 6 (fun i j =>
    if carrier.confMem (dataA 2) (pairpencil.posConf (dataA 2) chW chIx j)
        (algebra.plaqRow (dataA 2) chW p (pairpencil.posConf (dataA 2) chW chIx i))
      || carrier.confMem (dataA 2) (pairpencil.posConf (dataA 2) chW chIx i)
        (algebra.plaqRow (dataA 2) chW p (pairpencil.posConf (dataA 2) chW chIx j))
    then ⟨2, 1⟩ else BPair.unit)
private def chTerms : List Mat := chW.plaqs.map chTerm
private def chSum : Mat := elim.msum 6 (ground.getAt [] chTerms) (List.range 3)

example : termsMoved (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3)
    chPmT chTerms := by decide +kernel
example : movedReadBy (slotEq (dataA 2)) chAct
    (pairpencil.slotList (dataA 2) chW chIx) chSum := by decide +kernel
example : commRead (slotMat (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3))
    chSum := by decide +kernel

private theorem chTermsSq : (List.range chTerms.length).all (fun q =>
    decide (sqAt (ground.getAt [] chTerms q)
      ((pairpencil.slotList (dataA 2) chW chIx).length + 1))) = true := by
  decide +kernel

example : movedReadBy (slotEq (dataA 2))
    (slotAct (dataA 2) (chainTranslInv 3) (chainVertInv 3) chW.links chW.verts)
    (pairpencil.slotList (dataA 2) chW chIx)
    (elim.msum ((pairpencil.slotList (dataA 2) chW chIx).length + 1)
      (ground.getAt [] chTerms) (List.range chTerms.length)) :=
  movedReadBy_termSum (dataA 2) chW chIx (chainTransl 3) (chainTranslInv 3)
    (chainVertInv 3) chPmT chPmS chPlaqT chTerms (by decide +kernel)
    (fun q hq => of_decide_eq_true (all_range_read _ chTermsSq q hq))
    (by decide +kernel)
example : commRead (slotMat (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3))
    (elim.msum ((pairpencil.slotList (dataA 2) chW chIx).length + 1)
      (ground.getAt [] chTerms) (List.range chTerms.length)) :=
  commRead_slotM (dataA 2) chW chIx (chainTransl 3) (chainTranslInv 3)
    (chainVertInv 3) chPmT chPmS chPlaqT chOnce chTerms (by decide +kernel)
    (fun q hq => of_decide_eq_true (all_range_read _ chTermsSq q hq))
    (by decide +kernel)
example : commRead (slotMat (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3))
    (elim.msum ((pairpencil.slotList (dataA 2) chW chIx).length + 1)
      (ground.getAt [] chTerms) (List.range chTerms.length)) :=
  commRead_slotM_dataA 2 chW 12 chIx chIxPinA chWell3 (chainTransl 3)
    (chainTranslInv 3) (chainVert 3) (chainVertInv 3) chPmT chPmS
    chPerm3 chEnds3 chVert3 chPlaqT chTerms (by decide +kernel)
    (fun q hq => of_decide_eq_true (all_range_read _ chTermsSq q hq))
    (by decide +kernel)

private def chG : Mat := inertia.idMat 6
private def chP (k : Nat) : List (Nat × Bool) := ground.getAt [] chW.plaqs k
private def chCap : Mat :=
  inertia.matScaleB (BPair.ofNat ((dataA 2).dim (dataA 2).theta)) chG

/-! The gram's split and the six cap splits at the adjoint
dimension three as stated data: the gram's own, and per plaquette
the upper split at the site datum and the lower at the sum, each the cleared congruence with its adjugate
witness at normalized representatives, the blocks and the kernel
order (`lem:inertia`'s certificate data; the read at the data is
`splitRead`'s, the descent's own output re-read rather than
re-run). -/

private def chSpG : inertia.Split 6 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩]], rfl⟩,
   ⟨[[⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩]], rfl⟩,
   [.one ⟨2, 1⟩, .one ⟨2, 1⟩, .one ⟨2, 1⟩, .one ⟨2, 1⟩, .one ⟨2, 1⟩, .one ⟨2, 1⟩],
   0, rfl⟩
private def chU0 : inertia.Split 6 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨82, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1594324⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨12157665459056928802, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 5391030899743293631239539488528815119194426882613553319204⟩]], rfl⟩,
   ⟨[[⟨1, 25392449348622130779763242573538520583474933800798398908000521914985712447677679339868⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨8464149782874043593254414191179506861158311266932799636000173971661904149225893113290, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 313487028995334947898311636710352105968826343219733319851858295246737190712070115308⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨15926791088519786003064148590679881418931379526481396121112548658575277686941530, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2088595827392656793085408064780643444068898148936888424953199350268⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4710128697246244834921603690, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨28, 1⟩,
    .one ⟨19684, 1⟩,
    .one ⟨7625597484988, 1⟩,
    .one ⟨443426488243037769948249630619149892804, 1⟩,
    .one ⟨58126428323973972135274047057240514464642714936487833390350146291993978062482293295650366604554455411194036817110419, 1⟩],
   0, rfl⟩
private def chL0 : inertia.Split 6 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨82, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1594324⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨12157665459056928802, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 5391030899743293631239539488528815119194426882613553319204⟩]], rfl⟩,
   ⟨[[⟨1, 25392449348622130779763242573538520583474933800798398908000521914985712447677679339868⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨8464149782874043593254414191179506861158311266932799636000173971661904149225893113290, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 313487028995334947898311636710352105968826343219733319851858295246737190712070115308⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨15926791088519786003064148590679881418931379526481396121112548658575277686941530, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2088595827392656793085408064780643444068898148936888424953199350268⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4710128697246244834921603690, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨28, 1⟩,
    .one ⟨19684, 1⟩,
    .one ⟨7625597484988, 1⟩,
    .one ⟨443426488243037769948249630619149892804, 1⟩,
    .one ⟨116252856647947944270548094114481028929285429872975666780700292583987956124964586591300733209108910822388073634220837, 1⟩],
   0, rfl⟩
private def chU1 : inertia.Split 6 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨82, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1594324⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨8105110306037952535, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1597342488812827742589493181786315590872422780033645427913⟩]], rfl⟩,
   ⟨[[⟨1, 5015792463925359166372986187365633695501221491515733117629732723947795051393121844913⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1671930821308453055457662062455211231833740497171911039209910907982598350464373948305, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 61923363752164927979913409720563378956805203598959668118885589184540679646828664753⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3146032807608846617889214536430593860529655215107436270837046648607462259148945, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 618843208116342753506787574749820279724117970055374348134281288969⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨3140085798164163223281069127, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨28, 1⟩,
    .one ⟨19684, 1⟩,
    .one ⟨5083731656659, 1⟩,
    .one ⟨197078439219127897754777613608511063469, 1⟩,
    .one ⟨7654509079700276165962014427290931945961180567767945137823887577546532090532647676793463915003055856618144766039233, 1⟩],
   0, rfl⟩
private def chL1 : inertia.Split 6 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨82, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1594324⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨16210220612075905069, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 12778739910502621940715945454290524726979382240269163423297⟩]], rfl⟩,
   ⟨[[⟨1, 80252679422805746661967778997850139128019543864251729882075723583164720822289949518593⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨26750893140935248887322592999283379709339847954750576627358574527721573607429983172865, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 990773820034638847678614555529014063308883257583354689902169426952650874349258636033⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨50336524921741545886227432582889501768474483441718980333392746377719396146383105, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 4950745664930742028054300597998562237792943760442994785074250311745⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨6280171596328326446562138253, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨28, 1⟩,
    .one ⟨19684, 1⟩,
    .one ⟨10167463313317, 1⟩,
    .one ⟨788313756876511591019110454434044253873, 1⟩,
    .one ⟨489888581100817674621568923346619644541515556337148488820728804962978053794089451314781690560195574823561265026510849, 1⟩],
   0, rfl⟩
private def chU2 : inertia.Split 6 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨82, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1594324⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨12157665459056928802, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 3594020599828862420826359659019210079462951255075702212803⟩]], rfl⟩,
   ⟨[[⟨1, 16928299565748087186508828382359013722316622533865599272000347943323808298451786226579⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨5642766521916029062169609460786337907438874177955199757333449314441269432817262075527, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 208991352663556631932207757806901403979217562146488879901238863497824793808046743539⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨10617860725679857335376099060453254279287586350987597414075032439050185124627687, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1392397218261771195390272043187095629379265432624592283302132900179⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4710128697246244834921603690, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨28, 1⟩,
    .one ⟨19684, 1⟩,
    .one ⟨7625597484988, 1⟩,
    .one ⟨295617658828691846632166420412766595203, 1⟩,
    .one ⟨38750952215982648090182698038160342976428476624325222260233430861329318708321528863766911069702970274129357878073613, 1⟩],
   0, rfl⟩
private def chL2 : inertia.Split 6 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 4⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨82, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1594324⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨12157665459056928802, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 7188041199657724841652719318038420158925902510151404425605⟩]], rfl⟩,
   ⟨[[⟨1, 33856599131496174373017656764718027444633245067731198544000695886647616596903572453157⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨11285533043832058124339218921572675814877748355910399514666898628882538865634524151053, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 417982705327113263864415515613802807958435124292977759802477726995649587616093487077⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨21235721451359714670752198120906508558575172701975194828150064878100370249255373, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2784794436523542390780544086374191258758530865249184566604265800357⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨4710128697246244834921603690, 1⟩]], rfl⟩,
   [.one ⟨4, 1⟩,
    .one ⟨28, 1⟩,
    .one ⟨19684, 1⟩,
    .one ⟨7625597484988, 1⟩,
    .one ⟨591235317657383693264332840825533190405, 1⟩,
    .one ⟨155003808863930592360730792152641371905713906497300889040933723445317274833286115455067644278811881096517431512294449, 1⟩],
   0, rfl⟩
private def chTermsP : List (Mat × inertia.Split 6 × inertia.Split 6) :=
  [(chTerm (chP 0), chU0, chL0), (chTerm (chP 1), chU1, chL1),
   (chTerm (chP 2), chU2, chL2)]
private theorem chPlaqs : chW.plaqs = [chP 0, chP 1, chP 2] := by decide +kernel
private theorem chDim : windowfinite.dimSect (dataA 2) chW 12 = 6 := by
  rw [windowfinite.dimSect, chIxPinA]
  decide +kernel

/-! The terms' reads one kernel task per split read: per plaquette
the term's symmetry, its shape with the cap's, the upper split at
the site datum with its positivity (`leAt`), the lower split at the
sum with its positivity, the support at the changed-edge targets
and the entries at the fibers' stated lists one task per position
row (the range fold's one-step introduction assembling them), each
decided on its own and the three terms assembled at
`termsRead`'s own conjunction over the pinned plaquette list.  The
cap is stated at the interface's own spelling (`chCap`, the
adjoint dimension read at the data), so the assembly matches
`termsRead`'s clause by unfolding alone, the dimension read left
to the kernel. -/

private theorem chCapSq : sqAt chCap 6 := by decide +kernel
private theorem chSym0 : pairpencil.symmRead (chTerm (chP 0)) := by decide +kernel
private theorem chSq0 : sqAt (chTerm (chP 0)) 6 := by decide +kernel
private theorem chLe0 : inertia.leAt (chTerm (chP 0)) chCap chU0 := by
  decide +kernel
private theorem chLo0 : inertia.splitRead (matAdd chCap (chTerm (chP 0))) chL0 := by
  decide +kernel
private theorem chPsd0 : inertia.psdAt chL0 := by decide +kernel
private theorem chSupp0 :
    pairpencil.termSupport (dataA 2) chW 6 chIx (chP 0) (chTerm (chP 0)) := by
  decide +kernel
private theorem chEnt0R0 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 0) 0 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 0)) (chP 0) 0 j) = true := by
  decide +kernel
private theorem chEnt0R1 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 0) 1 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 0)) (chP 0) 1 j) = true := by
  decide +kernel
private theorem chEnt0R2 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 0) 2 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 0)) (chP 0) 2 j) = true := by
  decide +kernel
private theorem chEnt0R3 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 0) 3 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 0)) (chP 0) 3 j) = true := by
  decide +kernel
private theorem chEnt0R4 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 0) 4 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 0)) (chP 0) 4 j) = true := by
  decide +kernel
private theorem chEnt0R5 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 0) 5 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 0)) (chP 0) 5 j) = true := by
  decide +kernel
private theorem chEnt0 : pairpencil.entriesRead (dataA 2) chW 6 chIx 1 chG (chP 0) (chTerm (chP 0)) :=
  (ground.all_range_succ_intro 5 (ground.all_range_succ_intro 4 (ground.all_range_succ_intro 3 (ground.all_range_succ_intro 2 (ground.all_range_succ_intro 1 (ground.all_range_succ_intro 0 rfl chEnt0R0) chEnt0R1) chEnt0R2) chEnt0R3) chEnt0R4) chEnt0R5)
private theorem chSym1 : pairpencil.symmRead (chTerm (chP 1)) := by decide +kernel
private theorem chSq1 : sqAt (chTerm (chP 1)) 6 := by decide +kernel
private theorem chLe1 : inertia.leAt (chTerm (chP 1)) chCap chU1 := by
  decide +kernel
private theorem chLo1 : inertia.splitRead (matAdd chCap (chTerm (chP 1))) chL1 := by
  decide +kernel
private theorem chPsd1 : inertia.psdAt chL1 := by decide +kernel
private theorem chSupp1 :
    pairpencil.termSupport (dataA 2) chW 6 chIx (chP 1) (chTerm (chP 1)) := by
  decide +kernel
private theorem chEnt1R0 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 1) 0 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 1)) (chP 1) 0 j) = true := by
  decide +kernel
private theorem chEnt1R1 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 1) 1 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 1)) (chP 1) 1 j) = true := by
  decide +kernel
private theorem chEnt1R2 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 1) 2 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 1)) (chP 1) 2 j) = true := by
  decide +kernel
private theorem chEnt1R3 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 1) 3 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 1)) (chP 1) 3 j) = true := by
  decide +kernel
private theorem chEnt1R4 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 1) 4 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 1)) (chP 1) 4 j) = true := by
  decide +kernel
private theorem chEnt1R5 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 1) 5 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 1)) (chP 1) 5 j) = true := by
  decide +kernel
private theorem chEnt1 : pairpencil.entriesRead (dataA 2) chW 6 chIx 1 chG (chP 1) (chTerm (chP 1)) :=
  (ground.all_range_succ_intro 5 (ground.all_range_succ_intro 4 (ground.all_range_succ_intro 3 (ground.all_range_succ_intro 2 (ground.all_range_succ_intro 1 (ground.all_range_succ_intro 0 rfl chEnt1R0) chEnt1R1) chEnt1R2) chEnt1R3) chEnt1R4) chEnt1R5)
private theorem chSym2 : pairpencil.symmRead (chTerm (chP 2)) := by decide +kernel
private theorem chSq2 : sqAt (chTerm (chP 2)) 6 := by decide +kernel
private theorem chLe2 : inertia.leAt (chTerm (chP 2)) chCap chU2 := by
  decide +kernel
private theorem chLo2 : inertia.splitRead (matAdd chCap (chTerm (chP 2))) chL2 := by
  decide +kernel
private theorem chPsd2 : inertia.psdAt chL2 := by decide +kernel
private theorem chSupp2 :
    pairpencil.termSupport (dataA 2) chW 6 chIx (chP 2) (chTerm (chP 2)) := by
  decide +kernel
private theorem chEnt2R0 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 2) 0 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 2)) (chP 2) 0 j) = true := by
  decide +kernel
private theorem chEnt2R1 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 2) 1 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 2)) (chP 2) 1 j) = true := by
  decide +kernel
private theorem chEnt2R2 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 2) 2 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 2)) (chP 2) 2 j) = true := by
  decide +kernel
private theorem chEnt2R3 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 2) 3 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 2)) (chP 2) 3 j) = true := by
  decide +kernel
private theorem chEnt2R4 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 2) 4 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 2)) (chP 2) 4 j) = true := by
  decide +kernel
private theorem chEnt2R5 : (List.range 6).all (fun j =>
    !pairpencil.rowPair (dataA 2) chW chIx (chP 2) 5 j
      || pairpencil.entryAt (dataA 2) chW chIx 1 chG (chTerm (chP 2)) (chP 2) 5 j) = true := by
  decide +kernel
private theorem chEnt2 : pairpencil.entriesRead (dataA 2) chW 6 chIx 1 chG (chP 2) (chTerm (chP 2)) :=
  (ground.all_range_succ_intro 5 (ground.all_range_succ_intro 4 (ground.all_range_succ_intro 3 (ground.all_range_succ_intro 2 (ground.all_range_succ_intro 1 (ground.all_range_succ_intro 0 rfl chEnt2R0) chEnt2R1) chEnt2R2) chEnt2R3) chEnt2R4) chEnt2R5)
private theorem chCapAt0 : inertia.capAt (chTerm (chP 0)) chCap chU0 chL0 :=
  ⟨chSq0, chCapSq, chLe0, chLo0, chPsd0⟩
private theorem chCapAt1 : inertia.capAt (chTerm (chP 1)) chCap chU1 chL1 :=
  ⟨chSq1, chCapSq, chLe1, chLo1, chPsd1⟩
private theorem chCapAt2 : inertia.capAt (chTerm (chP 2)) chCap chU2 chL2 :=
  ⟨chSq2, chCapSq, chLe2, chLo2, chPsd2⟩
private theorem chTermsRead :
    pairpencil.termsRead (dataA 2) chW 6 chIx 1 chG chW.plaqs chTermsP := by
  rw [chPlaqs]
  exact ⟨chSym0, chCapAt0, chSupp0, chEnt0, chSym1, chCapAt1, chSupp1, chEnt1,
    chSym2, chCapAt2, chSupp2, chEnt2, trivial⟩
private theorem chGramRead : pairpencil.gramBlockRead (dataA 2) chW 6 chIx 1 chG := by
  decide +kernel
private theorem chSpGRead : inertia.splitRead chG chSpG ∧ inertia.pdAt chSpG := by
  decide +kernel
private theorem chPencil : pairpencil.pencilRead (dataA 2) chW 12 6 chIx 1
    (pairpencil.pencilE chDiag) chG chSum chSpG chTermsP :=
  ⟨chIxPinA, chDim, by decide +kernel,
    by rw [chSlotDiag]; decide +kernel, chGramRead, chSpGRead.1, chSpGRead.2,
    chTermsRead, by decide +kernel, by decide +kernel⟩

example : commRead (slotMat (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3))
    chSum :=
  commRead_pencilM_dataA 2 chW 12 6 chIx 1 (pairpencil.pencilE chDiag) chG chSum
    chSpG chTermsP chPencil chWell3 (chainTransl 3) (chainTranslInv 3)
    (chainVert 3) (chainVertInv 3) chPmT chPmS chPerm3 chEnds3 chVert3 chPlaqT
    (by decide +kernel)

private def chTermBad : Mat :=
  ground.matOf 6 6 (fun i j =>
    if i == 3 && j == 4 then ⟨3, 1⟩
    else ground.getAt BPair.unit (ground.getAt [] (chTerm (chP 0)) i) j)
private def chTermsBad : List Mat := chTermBad :: chTerms.drop 1

example : ¬ termsMoved (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3)
    chPmT chTermsBad := by decide +kernel
example : ¬ movedReadBy (slotEq (dataA 2)) chAct
    (pairpencil.slotList (dataA 2) chW chIx)
    (elim.msum 6 (ground.getAt [] chTermsBad) (List.range 3)) := by decide +kernel
example : ¬ commRead (slotMat (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3))
    (elim.msum 6 (ground.getAt [] chTermsBad) (List.range 3)) := by decide +kernel

private def chTermRail : Mat :=
  ground.matOf 6 6 (fun i j =>
    if i == 1 && j == 2 then ⟨3, 1⟩
    else ground.getAt BPair.unit (ground.getAt [] (chTerm (chP 0)) i) j)
private def chTermsRail : List Mat := chTermRail :: chTerms.drop 1

example : ¬ termsMoved (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3)
      chPmT chTermsRail
    ∧ movedReadBy (slotEq (dataA 2)) chAct (pairpencil.slotList (dataA 2) chW chIx)
      (elim.msum 6 (ground.getAt [] chTermsRail) (List.range 3))
    ∧ commRead (slotMat (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3))
      (elim.msum 6 (ground.getAt [] chTermsRail) (List.range 3)) := by
  decide +kernel

private def chTermX : Mat :=
  ground.matOf 6 6 (fun i j => if i == 3 && j == 4 then ⟨3, 1⟩ else BPair.unit)

example : termsMoved (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3)
      chPmT (chTerms ++ [chTermX])
    ∧ ¬ movedReadBy (slotEq (dataA 2)) chAct (pairpencil.slotList (dataA 2) chW chIx)
      (elim.msum 6 (ground.getAt [] (chTerms ++ [chTermX])) (List.range 4)) := by
  decide +kernel

private def chTermRag : Mat :=
  (List.range 6).map (fun i =>
    if i == 3 then (ground.getAt [] (chTerm (chP 0)) 3).take 3
    else ground.getAt [] (chTerm (chP 0)) i)
private def chTermsRag : List Mat := chTermRag :: chTerms.drop 1

example : termsMoved (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3)
      chPmT chTermsRag
    ∧ ¬ sqAt chTermRag 6
    ∧ ¬ movedReadBy (slotEq (dataA 2)) chAct (pairpencil.slotList (dataA 2) chW chIx)
      (elim.msum 6 (ground.getAt [] chTermsRag) (List.range 3)) := by
  decide +kernel

private def chIxD : List (List places.Shape) :=
  [ground.getAt [] chIx 2, ground.getAt [] chIx 2]
private def chSD : Mat :=
  [[BPair.unit, BPair.unit, BPair.unit], [BPair.unit, ⟨2, 1⟩, ⟨2, 1⟩],
   [BPair.unit, ⟨2, 1⟩, ⟨2, 1⟩]]

example : plaqPermRead chW (fun l => l) (fun _ => false) (fun q => q) (fun q => q)
    ∧ ¬ imgOnceBy (slotEq (dataA 2)) (slotAct (dataA 2) (fun l => l) (fun v => v) 9 6)
      (pairpencil.slotList (dataA 2) chW chIxD)
    ∧ termsMoved (dataA 2) chW chIxD (fun l => l) (fun v => v) (fun q => q)
      [chSD, chSD, chSD]
    ∧ movedReadBy (slotEq (dataA 2)) (slotAct (dataA 2) (fun l => l) (fun v => v) 9 6)
      (pairpencil.slotList (dataA 2) chW chIxD)
      (elim.msum 3 (ground.getAt [] [chSD, chSD, chSD]) (List.range 3))
    ∧ ¬ commRead (slotMat (dataA 2) chW chIxD (fun l => l) (fun v => v))
      (elim.msum 3 (ground.getAt [] [chSD, chSD, chSD]) (List.range 3)) := by
  decide +kernel

private def chTwice : Region :=
  { chW with plaqs := [chP 0, chP 0, chP 1] }
private def chRot : Region :=
  { chW with plaqs := [chP 0, ground.rotAt 1 (chP 0), chP 1] }

example : ¬ plaqRead chTwice ∧ ¬ ground.distinctList chTwice.plaqs
    ∧ ¬ plaqRead chRot ∧ ground.distinctList chRot.plaqs := by decide +kernel

/-! The congruence's four load-bearing binders at their refusals
on the place action's own carrier, the standing conjuncts decided
beside each: the diagonal moved — two members exchanged under the
action at weights fourteen and nineteen; the action off
injectivity, a constant action folding two members onto one at one
weight; the equality read off the image pairs' structure, the
parity read meeting each image once at a member off the image with
the weights fixed; and the image off the list, the shift by five
at fixed weights. -/

private def swapTwo : Nat → Nat := fun a => if a = 0 then 1 else 0

example : imgOnceBy (fun a b : Nat => a == b) swapTwo [0, 1]
    ∧ imgEqBy (fun a b : Nat => a == b) swapTwo [0, 1]
    ∧ ground.distinctList [0, 1] := by decide +kernel
example : ¬ movedReadBy (fun a b : Nat => a == b) swapTwo [0, 1]
    (pairpencil.pencilE [0, 14, 19]) := by decide +kernel
example : ¬ commRead (permMatBy (fun a b : Nat => a == b) swapTwo [0, 1])
    (pairpencil.pencilE [0, 14, 19]) := by decide +kernel
example : imgOnceBy (fun a b : Nat => a == b) (fun _ => 0) [0, 1]
    ∧ imgEqBy (fun a b : Nat => a == b) (fun _ => 0) [0, 1] := by
  decide +kernel
example : ¬ movedReadBy (fun a b : Nat => a == b) (fun _ => 0) [0, 1]
    (pairpencil.pencilE [0, 5, 5]) := by decide +kernel
example : ¬ commRead (permMatBy (fun a b : Nat => a == b) (fun _ => 0) [0, 1])
    (pairpencil.pencilE [0, 5, 5]) := by decide +kernel

private def eqP : Nat → Nat → Bool := fun a b => a % 2 == b % 2
private def imgP : Nat → Nat := fun a => if a == 0 then 3 else 2
private def wP : Nat → Nat := fun a => if a == 0 || a == 3 then 5 else 9

example : imgOnceBy eqP imgP [0, 1]
    ∧ ([0, 1].all (fun a => [0, 1].all (fun b =>
        !(imgP a == imgP b) || (a == b)))) = true
    ∧ ([0, 1].all (fun a => wP (imgP a) == wP a)) = true := by decide +kernel
example : ¬ imgEqBy eqP imgP [0, 1] := by decide +kernel
example : ¬ movedReadBy eqP imgP [0, 1] (pairpencil.pencilE [0, 5, 9]) := by
  decide +kernel
example : ¬ commRead (permMatBy eqP imgP [0, 1])
    (pairpencil.pencilE [0, 5, 9]) := by decide +kernel

example : imgEqBy (fun a b : Nat => a == b) (fun a => a + 5) [0, 1] := by
  decide +kernel
example : ¬ imgOnceBy (fun a b : Nat => a == b) (fun a => a + 5) [0, 1] := by
  decide +kernel
example : ¬ commRead (permMatBy (fun a b : Nat => a == b) (fun a => a + 5) [0, 1])
    (pairpencil.pencilE [0, 4, 4]) := by decide +kernel

example : commRead (slotMat (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3))
    (pairpencil.pencilE chDiag) := by
  rw [← chSlotDiag]
  exact commRead_slotE_dataA 2 chW 12 chIx chIxPinA chWell3 (chainTransl 3)
    (chainTranslInv 3) (chainVert 3) (chainVertInv 3) chPerm3 chEnds3 chVert3
example : commRead (slotMat (dataA 2) chW chIx (chainTranslInv 3) (chainVertInv 3))
    (pairpencil.pencilE chDiag) := by
  decide +kernel

/-! The commuting read at the free end's window matrix
(`prop:segment`, the electric member alone at its own one-member
site, `pairpencil.pencilE`): the place action's matrix's congruence
fixes the diagonal at the tabulated interface as well, the three
squares' contents at one value and the two rails' at another. -/

example : commRead (slotMat fA chW chIx (chainTranslInv 3) (chainVertInv 3))
    (pairpencil.pencilE chDiag) := by
  decide +kernel

/-! The transposition biting at the index layer: it moves the lower
rail loop to a configuration whose rung end reads one label alone,
so the closure fails and the congruence with it. -/

example : ¬ idxFixed fA chW chIx swapRR := by decide +kernel
example : ¬ occFixed fA chW chIx swapRR := by decide +kernel
example : ¬ commRead (slotMat fA chW chIx swapRR (fun v => v))
    (pairpencil.pencilE chDiag) := by
  decide +kernel

/-! The window list at fibers of four slots: at three letters the
rails at the adjoint with one rung at the adjoint, the rung's two
ends at multiplicity two (`θ ⊗ θ ⊗ θ` holding the unit twice at
three letters), the three members the translation's one orbit,
twelve slots with the unit line.  The congruence holds at the
vertex witness and refuses at the identity in its place, the moved
key off the moved member's fiber: the vertex witness is
load-bearing at the window list, at the electric member and at the
magnetic — the terms' transport at a diagonal term reading each
slot key's digit fold moves at the vertex witness and refuses at
the identity in its place, the sum commuting at the witness. -/

private def th3 : places.Shape := adjchar.theta 3
private def u3 : places.Shape := [0, 0, 0]
private def ix3 : List (List places.Shape) :=
  [[th3, u3, u3, th3, th3, th3, th3, th3, th3],
   [u3, th3, u3, th3, th3, th3, th3, th3, th3],
   [u3, u3, th3, th3, th3, th3, th3, th3, th3]]
private def act3 : List places.Shape × List Nat → List places.Shape × List Nat :=
  slotAct (dataA 3) (chainTranslInv 3) (chainVertInv 3) 9 6

example : (ix3.all (fun a => occupied (dataA 3) chW a)) = true
    ∧ (ix3.all (fun a => windowfinite.fibProd (dataA 3) chW a == 4)) = true := by
  decide +kernel
example : pairpencil.slotKeys (dataA 3) chW (ground.getAt [] ix3 0)
    = [[0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0],
       [1, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0]] := by decide +kernel
example : (pairpencil.slotList (dataA 3) chW ix3).length = 12 := by
  decide +kernel
example : imgOnceBy (slotEq (dataA 3)) act3 (pairpencil.slotList (dataA 3) chW ix3)
    ∧ imgEqBy (slotEq (dataA 3)) act3 (pairpencil.slotList (dataA 3) chW ix3)
    ∧ ground.distinctList (pairpencil.slotList (dataA 3) chW ix3) := by
  decide +kernel
example : commRead (slotMat (dataA 3) chW ix3 (chainTranslInv 3) (chainVertInv 3))
    (pairpencil.pencilE (pairpencil.slotDiag (dataA 3) chW ix3)) := by
  decide +kernel
example : ¬ imgOnceBy (slotEq (dataA 3))
    (slotAct (dataA 3) (chainTranslInv 3) (fun v => v) 9 6)
    (pairpencil.slotList (dataA 3) chW ix3) := by decide +kernel
example : ¬ commRead (slotMat (dataA 3) chW ix3 (chainTranslInv 3) (fun v => v))
    (pairpencil.pencilE (pairpencil.slotDiag (dataA 3) chW ix3)) := by
  decide +kernel

private def slotDigits : Mat :=
  ground.matOf 13 13 (fun i j =>
    if i == j then
      (if i == 0 then BPair.unit
       else ⟨⟨ground.famFold Nat.add 0 (fun x => x)
          (ground.getAt ([], []) (pairpencil.slotList (dataA 3) chW ix3) (i - 1)).2⟩,
        Pos.one⟩)
    else BPair.unit)

example : termsMoved (dataA 3) chW ix3 (chainTranslInv 3) (chainVertInv 3) chPmT
    [slotDigits, slotDigits, slotDigits] := by decide +kernel
example : ¬ termsMoved (dataA 3) chW ix3 (chainTranslInv 3) (fun v => v) chPmT
    [slotDigits, slotDigits, slotDigits] := by decide +kernel
example : commRead (slotMat (dataA 3) chW ix3 (chainTranslInv 3) (chainVertInv 3))
    (elim.msum 13 (ground.getAt [] [slotDigits, slotDigits, slotDigits])
      (List.range 3)) := by decide +kernel

/-! The chord tier's carriers: the translation's link permutation at
the two sides, and the free orbit at side five — the translation
restricted to the chain's rung range, the tex's own free orbit. -/

private def chT3 : Mat := permMatAt 9 (chainTransl 3)
private def chT5 : Mat := permMatAt 15 (chainTransl 5)
private def orbT : Mat := permMatAt 5 (chainTransl 5)

/-! The orthogonality and the deck relation at both sides: the
relation at side five is `chord_deck`'s own instance, the general
theorem discharged at the window's shape reads. -/

example : orthRead chT3 9 :=
  permRead_orth (chainRegion 3) (chainTransl 3) (chainTranslInv 3) chPerm3
example : orthRead chT5 15 :=
  permRead_orth (chainRegion 5) (chainTransl 5) (chainTranslInv 5) chPerm5

example : deckOpRead chT3 9 := by decide +kernel
example : deckOpRead chT5 15 :=
  chord_deck 15 chT5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! The word identity, the word's two fixed reads and the
annihilation at each side's own symbol, `m = 1` at the side-three
bench with the side-five reads at the free orbit below.  The
committed window's whole-link-set instances (order fifteen, three
disjoint five-cycles) sit beyond the pin budget as kernel decides,
and the general theorems
discharge the same two reads at the permutation-level side
conditions alone — the multi-orbit direct sum pinned at the
window's own link set. -/

example : wordOpRead chT3 9 1 := by decide +kernel
example : annihRead chT3 9 1 := by decide +kernel

example : wordOpRead chT5 15 2 :=
  word_read 15 2 (chainTransl 5) (chainTranslInv 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : annihRead chT5 15 2 :=
  annih_of 15 2 (chainTransl 5) (chainTranslInv 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : fixedWordRead chT3 9 1 :=
  fixedWord_perm (chainRegion 3) (chainTransl 3) (chainTranslInv 3) 1
    (by decide +kernel) chPerm3 (by decide +kernel) (by decide +kernel)

/-! The same three at the free orbit, the tex's own carrier — the
translation restricted to the chain's rung range at side five — and
the chord's doubling on the fixed word there, `chord_join`'s
instance: the fixed read derived at the general theorem, the join
derived on it. -/

example : wordOpRead orbT 5 2 := by decide +kernel
example : annihRead orbT 5 2 := by decide +kernel

/-! The two reads discharged by their general theorems at the
orbit — `word_read` and `annih_of` at the cycle's own count, the
theorems' instances beside the kernel decides above. -/

example : wordOpRead orbT 5 2 :=
  word_read 5 2 (chainTransl 5) (chainTranslInv 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : annihRead orbT 5 2 :=
  annih_of 5 2 (chainTransl 5) (chainTranslInv 5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem orbFix : fixedWordRead orbT 5 2 :=
  fixedWord_of 5 2 orbT (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : matOneValue (matMul orbT (wordSum orbT 5 5))
    (wordSum orbT 5 5) :=
  wordSum_fixed 5 5 orbT (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : matOneValue (matMul (transposeM orbT) (chordWord orbT 5 2))
    (chordWord orbT 5 2) :=
  inertia.fixed_transpose 5 orbT (chordWord orbT 5 2) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    orbFix.1

example : matOneValue (matMul (chordOp orbT) (chordWord orbT 5 2))
    (inertia.matScaleB (BPair.ofNat 2) (chordWord orbT 5 2)) :=
  chord_join 5 orbT (chordWord orbT 5 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) orbFix.1 orbFix.2

/-! The base-rational splitting at the free orbit: the unit fiber's
one member, the four-member spanning list of `P_5(S)`'s kernel, and
the identification joining the kernel read to the fixed read. -/

private def orbS : Mat := chordOp orbT
private def orbD : Mat := inertia.siteDatum orbS (inertia.idMat 5)

private def orbLu : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1,
    BPair.ofNat 1]]

private def orbLk : Mat :=
  [[BPair.ofNat 1, (BPair.ofNat 1).swap, BPair.unit, BPair.unit,
    BPair.unit],
   [BPair.ofNat 3, BPair.ofNat 1, (BPair.ofNat 4).swap, BPair.unit,
    BPair.unit],
   [BPair.ofNat 5, BPair.ofNat 4, (BPair.ofNat 2).swap,
    (BPair.ofNat 7).swap, BPair.unit],
   [(BPair.ofNat 1).swap, BPair.ofNat 4, BPair.ofNat 4,
    (BPair.ofNat 1).swap, (BPair.ofNat 6).swap]]

example : identRead orbT 5 := by decide +kernel
example : unitFiberRead orbT 5 orbLu := by decide +kernel
example : rootBlockRead orbT 5 2 orbLk := by decide +kernel

/-! The splitting congruence and the count split: the concatenated
lists carry the window datum `S - 1` to the two blocks' join, and
`lem:inertia`'s `rev_join` prices the count at the blocks' sum. -/

private def orbP : Mat := [[BPair.ofNat 5]]

private def orbQ : Mat :=
  [[(BPair.ofNat 4).swap, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, (BPair.ofNat 28).swap, BPair.unit, BPair.unit],
   [BPair.unit, BPair.unit, (BPair.ofNat 42).swap, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, (BPair.ofNat 30).swap]]

example : baseSplitRead orbT orbD 5 2 orbLu orbLk orbP orbQ := by decide +kernel

private def orbSpP : inertia.Split 1 :=
  ⟨⟨inertia.idMat 1, by decide +kernel⟩, ⟨inertia.idMat 1, by decide +kernel⟩,
   [.one (BPair.ofNat 5)], 0, by decide +kernel⟩

private def orbSpQ : inertia.Split 4 :=
  ⟨⟨inertia.idMat 4, by decide +kernel⟩, ⟨inertia.idMat 4, by decide +kernel⟩,
   [.one ((BPair.ofNat 4).swap), .one ((BPair.ofNat 28).swap),
    .one ((BPair.ofNat 42).swap), .one ((BPair.ofNat 30).swap)],
   0, by decide +kernel⟩

private def orbSpS : inertia.Split 5 :=
  ⟨⟨inertia.idMat 5, by decide +kernel⟩, ⟨inertia.idMat 5, by decide +kernel⟩,
   [.one (BPair.ofNat 5), .one ((BPair.ofNat 4).swap),
    .one ((BPair.ofNat 28).swap), .one ((BPair.ofNat 42).swap),
    .one ((BPair.ofNat 30).swap)], 0, by decide +kernel⟩

example : inertia.revAt orbSpS = inertia.revAt orbSpP + inertia.revAt orbSpQ :=
  inertia.rev_join orbP orbQ orbSpP (by decide +kernel) orbSpQ (by decide +kernel)
    orbSpS (by decide +kernel)

example : inertia.revAt orbSpS = 4 ∧ inertia.revAt orbSpP = 0
    ∧ inertia.revAt orbSpQ = 4 := by decide +kernel

/-! The sampled momenta at side five: the two brackets of
`P_5 = w² + w - 1` at width one sixteenth, the separation's `δ` at
half of it, with the chord `2` off the roots. -/

private def mom5 : List stage.Ext :=
  [⟨[(BPair.ofNat 1).swap, BPair.ofNat 1], ⟨(BPair.ofNat 26).swap, 16⟩,
    ⟨(BPair.ofNat 25).swap, 16⟩⟩,
   ⟨[(BPair.ofNat 1).swap, BPair.ofNat 1], ⟨BPair.ofNat 9, 16⟩,
    ⟨BPair.ofNat 10, 16⟩⟩]

example : momentaRead 2 mom5 1 16 := by decide +kernel

/-! The split certificate at side five: `P_5 = w² + w - 1`
irreducible, its two roots the committed momenta brackets, and the
bridge rebuilding the momenta read from the certificate.  At side
nine the mixed instance: `P_9 = (w + 1)(w³ − 3w + 1)`, one rational
root beside an irreducible cubic, the width one two-hundred
fifty-sixth at the cubic's separation.  The refusals isolate the
product, a bracket off the root, the count, and the apartness, each
at every other conjunct held. -/

private def fs5 : List poly.Poly := [[(BPair.ofNat 1).swap, BPair.ofNat 1]]
private def rE5 : List (Nat × (CPair × CPair)) :=
  [(0, (⟨(BPair.ofNat 26).swap, 16⟩, ⟨(BPair.ofNat 25).swap, 16⟩)),
   (0, (⟨BPair.ofNat 9, 16⟩, ⟨BPair.ofNat 10, 16⟩))]

example : splitRead 2 fs5 rE5 1 16 := by decide +kernel

example : momentaRead 2 (rE5.map (extAt fs5)) 1 16 :=
  splitRead_momenta 2 fs5 rE5 1 16 (by decide +kernel)

private def fs9 : List poly.Poly :=
  [[BPair.ofNat 1],
   [BPair.ofNat 1, (BPair.ofNat 3).swap, BPair.unit]]
private def rE9 : List (Nat × (CPair × CPair)) :=
  [(1, (⟨(BPair.ofNat 482).swap, 256⟩, ⟨(BPair.ofNat 481).swap, 256⟩)),
   (0, (⟨(BPair.ofNat 513).swap, 512⟩, ⟨(BPair.ofNat 511).swap, 512⟩)),
   (1, (⟨BPair.ofNat 88, 256⟩, ⟨BPair.ofNat 89, 256⟩)),
   (1, (⟨BPair.ofNat 392, 256⟩, ⟨BPair.ofNat 393, 256⟩))]

example : splitRead 4 fs9 rE9 1 256 := by decide +kernel

private def fsF : List poly.Poly := [[BPair.unit], [BPair.ofNat 1]]
private def rEF : List (Nat × (CPair × CPair)) :=
  [(1, (⟨(BPair.ofNat 33).swap, 32⟩, ⟨(BPair.ofNat 31).swap, 32⟩)),
   (0, (⟨(BPair.ofNat 1).swap, 32⟩, ⟨BPair.ofNat 1, 32⟩))]
example : ¬ splitRead 2 fsF rEF 1 16 := by decide +kernel
example : rEF.length = 2
    ∧ (fsF.all (fun f =>
        decide (windowsep.sepRead (poly.monic f) (2 * 1) 16))) = true
    ∧ (rEF.all (fun jE =>
        decide (jE.1 < fsF.length)
        && decide (stage.bracketRead (extAt fsF jE))
        && decide ((jE.2.1 + ⟨BPair.ofPos 1, 16⟩).oneValue jE.2.2)))
        = true
    ∧ ((⟨(BPair.ofNat 31).swap, 32⟩ : CPair)
        < ⟨(BPair.ofNat 1).swap, 32⟩) := by
  decide +kernel

private def rE5b : List (Nat × (CPair × CPair)) :=
  [(0, (⟨(BPair.ofNat 26).swap, 16⟩, ⟨(BPair.ofNat 25).swap, 16⟩)),
   (0, (⟨BPair.ofNat 12, 16⟩, ⟨BPair.ofNat 13, 16⟩))]
example : ¬ splitRead 2 fs5 rE5b 1 16 := by decide +kernel

example : ¬ splitRead 2 fs5 [(0, (⟨BPair.ofNat 9, 16⟩,
    ⟨BPair.ofNat 10, 16⟩))] 1 16 := by decide +kernel

example : ¬ splitRead 2 fs5
    [(0, (⟨BPair.ofNat 9, 16⟩, ⟨BPair.ofNat 10, 16⟩)),
     (0, (⟨BPair.ofNat 9, 16⟩, ⟨BPair.ofNat 10, 16⟩))] 1 16 := by decide +kernel

/-! The per-root tower at the side-five factor: over `rootTower`
the depth-two arithmetic reads `w · (w (t − 2)) = −5` at
`w² = 3 + t`, the band quadratic's own class; and the interiority
`t² − 4` on its lower side at both brackets, the priced side
read. -/

example : stagesplit.gWitnessRead 2
    (rootTower [(BPair.ofNat 1).swap, BPair.ofNat 1])
    [[], [BPair.ofNat 1]]
    [[], [(BPair.ofNat 2).swap, BPair.ofNat 1]]
    ((BPair.ofNat 5).swap) := by decide +kernel

example : stage.sideLower
    ⟨[(BPair.ofNat 1).swap, BPair.ofNat 1],
     ⟨BPair.ofNat 9, 16⟩, ⟨BPair.ofNat 10, 16⟩⟩
    (poly.neg bandPoly) 1 16 := by decide +kernel
example : stage.sideLower
    ⟨[(BPair.ofNat 1).swap, BPair.ofNat 1],
     ⟨(BPair.ofNat 26).swap, 16⟩, ⟨(BPair.ofNat 25).swap, 16⟩⟩
    (poly.neg bandPoly) 1 16 := by decide +kernel

/-! The refusals.  The orthogonality and the deck relation fail at
the chord operator, a symmetric matrix off the permutations; they
hold at the rung-and-rail transposition, which is a permutation, and
what that transposition breaks is the cycle — the annihilation is
where it shows.  The annihilation refuses at the wrong side's symbol
and at a symbol with one coefficient moved besides, and the count
split refuses at a congruence whose first member leaves the unit
fiber. -/

private def rrM : Mat := permMatAt 9 swapRR

example : ¬ orthRead (chordOp chT3) 9 := by decide +kernel
example : ¬ deckOpRead (chordOp chT3) 9 := by decide +kernel

example : orthRead rrM 9 := by decide +kernel
example : deckOpRead rrM 9 := by decide +kernel
example : ¬ annihRead rrM 9 1 := by decide +kernel

example : ¬ annihRead orbT 5 1 := by decide +kernel

/-! The cycle read is load-bearing for the word's fixed reads: the
rung-and-rail transposition is a permutation of order two, its
third power off the identity, and `fixedWordRead` fails with it. -/

example : ¬ matOneValue (inertia.matPow rrM 9 3) (inertia.idMat 9) := by decide +kernel
example : ¬ fixedWordRead rrM 9 1 := by decide +kernel

example : ¬ matOneValue
    (matMul (chordOp orbT)
      (polyEvalM (poly.add (deck.pSum 2) poly.one)
        (chordOp orbT) 5))
    (inertia.matScaleB (BPair.ofNat 2)
      (polyEvalM (poly.add (deck.pSum 2) poly.one)
        (chordOp orbT) 5)) := by decide +kernel

example : ¬ blockCongrRead orbD
    ([[BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit, BPair.unit]]
      ++ orbLk) orbP orbQ 1 4 := by decide +kernel

/-! The doubling tier's band read at the free orbit: the block
datum `A` at `T = Tᵀ + A` squaring against the chord,
`A² + 4 = S²`, decided at the orbit and discharged by `chord_band`
beside it — the general theorem's own instance, the orthogonality
its one hypothesis.  The refusal sits at the chord operator itself,
a symmetric matrix off the permutations, where the orthogonality
fails and the band read with it. -/

example : matOneValue
    (matAdd (matMul (bandDatum orbT) (bandDatum orbT))
      (inertia.matScaleB (BPair.ofNat 4) (inertia.idMat 5)))
    (matMul (chordOp orbT) (chordOp orbT)) := by decide +kernel

example : matOneValue
    (matAdd (matMul (bandDatum orbT) (bandDatum orbT))
      (inertia.matScaleB (BPair.ofNat 4) (inertia.idMat 5)))
    (matMul (chordOp orbT) (chordOp orbT)) :=
  chord_band 5 orbT (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : matOneValue
    (matAdd (matMul (bandDatum chT3) (bandDatum chT3))
      (inertia.matScaleB (BPair.ofNat 4) (inertia.idMat 9)))
    (matMul (chordOp chT3) (chordOp chT3)) :=
  chord_band 9 chT3 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : ¬ matOneValue
    (matAdd (matMul (bandDatum (chordOp orbT)) (bandDatum (chordOp orbT)))
      (inertia.matScaleB (BPair.ofNat 4) (inertia.idMat 5)))
    (matMul (chordOp (chordOp orbT)) (chordOp (chordOp orbT))) := by decide +kernel

/-! The permutation-matrix kit's instances: the composition read at
the chain's own translation, the identity map's matrix, the
transpose as the witness's matrix, and the power against the cycle
read — the four general theorems discharged at the committed
windows rather than decided, with the range clause the refusal
below shows load-bearing. -/

example : matOneValue (matMul chT3 chT3)
    (permMatAt 9 (fun l => chainTransl 3 (chainTransl 3 l))) :=
  permMatAt_mul 9 (chainTransl 3) (chainTransl 3) (by decide +kernel)

example : matOneValue (permMatAt 9 (fun l => l)) (inertia.idMat 9) :=
  permMatAt_id 9

example : transposeM chT3 = permMatAt 9 (chainTranslInv 3) :=
  transposeM_permMatAt 9 (chainTransl 3) (chainTranslInv 3)
    (fun l hl => (permRead_at (chainRegion 3) (chainTransl 3)
      (chainTranslInv 3) chPerm3 l hl).1)
    (fun l hl => (permRead_at (chainRegion 3) (chainTransl 3)
      (chainTranslInv 3) chPerm3 l hl).2.1)

example : matOneValue (inertia.matPow chT5 15 5) (permMatAt 15 (iterAt (chainTransl 5) 5)) :=
  permMatAt_pow 15 (chainTransl 5) (by decide +kernel) (by decide +kernel) 5

example : matOneValue (inertia.matPow chT5 15 5) (inertia.idMat 15) :=
  cycleRead_pow (chainRegion 5) (chainTransl 5) (chainTranslInv 5) 5
    (by decide +kernel) chPerm5 chCyc5

/-! The range clause refused: a map whose values leave the key
range empties its matrix, and the composition read fails against
the composite's own — the clause `permRead` supplies is not
decoration. -/

example : ¬ matOneValue
    (matMul (permMatAt 3 (fun l => l - 3)) (permMatAt 3 (fun l => l + 3)))
    (permMatAt 3 (fun l => l)) := by decide +kernel

/-! The deck-family column at the residue, the side-five orbit's
own: the deck symbol's monic display, the column's membership read
`S u = x u` at the recursion closing cyclically, the
perpendicularity of the doubling datum's image, and the pair's
independence at its Gram determinant's Bézout witness. -/

private def orbCof : poly.Poly :=
  [BPair.ofNat 200, (BPair.ofNat 100).swap]

example : deck.monicRead 2 := by decide +kernel
example : colMemberRead 2 orbS (deckColumn 2) := by decide +kernel

/-! The window translation's shift matrix is the wrap shift's own
at the side, one kernel identity per window, so the general theorem
re-derives the read the kernel decides above. -/

example : permMatAt 5 (chainTransl 5) = permMatAt 5 (tShift 2) := by decide +kernel

example : colMemberRead 2 orbS (deckColumn 2) := by
  rw [show orbS = chordOp (permMatAt 5 (tShift 2)) by decide +kernel]
  exact colMember_wrap 2
example : perpRead 2 (bandDatum orbT) (deckColumn 2) := by decide +kernel
example : gramUnitRead 2 (bandDatum orbT) (deckColumn 2) orbCof
    (BPair.ofNat 50000) := by decide +kernel

/-! The per-orbit independence over the remainder lists at every
side: `perp_band` carries the perpendicularity at every square
matrix — the pairing against the doubling datum reading its own
memberwise swap at the datum's transpose — with `perp_wrap` its
read at the translation's permutation matrix, and
`deckColumn_selfPair` reads the column's self-pairing at the
doubled side `2L`.  The theorem routes stand beside the kernel's
own reads at the committed sides, the doubling datum at the wrap
shift's matrix, `orbT`'s own by the identification above; the
generality is pinned off the shift entirely, at a forged
three-by-three datum whose members carry no cyclic structure, and
the constant is load-bearing, the self-pairing refusing at the
neighbouring even values. -/

example : perpRead 2 (bandDatum (permMatAt (2 * 2 + 1) (tShift 2)))
    (deckColumn 2) := by apply perp_wrap
example : perpRead 3 (bandDatum (permMatAt (2 * 3 + 1) (tShift 3)))
    (deckColumn 3) := by decide +kernel
example : perpRead 3 (bandDatum (permMatAt (2 * 3 + 1) (tShift 3)))
    (deckColumn 3) := by apply perp_wrap

/-- A square datum off the permutations, its rows carrying no
cyclic structure: `perp_band`'s own generality at the doubling
datum. -/
private def forgedM : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3],
   [BPair.ofNat 7, BPair.ofNat 7, BPair.ofNat 4],
   [BPair.ofNat 5, BPair.ofNat 6, BPair.ofNat 9]]

example : perpRead 1 (bandDatum forgedM) (deckColumn 1) := by
  apply perp_band 1 3 forgedM (by decide +kernel) (by decide +kernel) (deckColumn 1)
    (by decide +kernel)
example : perpRead 1 (bandDatum forgedM) (deckColumn 1) := by decide +kernel

example : poly.oneValue (deck.redP 2 (pdotVec (deckColumn 2) (deckColumn 2)))
    (deck.redP 2 [BPair.ofNat (2 * (2 * 2 + 1))]) := by decide +kernel
example : poly.oneValue (deck.redP 2 (pdotVec (deckColumn 2) (deckColumn 2)))
    (deck.redP 2 [BPair.ofNat (2 * (2 * 2 + 1))]) := by
  apply deckColumn_selfPair
example : poly.oneValue (deck.redP 3 (pdotVec (deckColumn 3) (deckColumn 3)))
    (deck.redP 3 [BPair.ofNat (2 * (2 * 3 + 1))]) := by decide +kernel
example : poly.oneValue (deck.redP 3 (pdotVec (deckColumn 3) (deckColumn 3)))
    (deck.redP 3 [BPair.ofNat (2 * (2 * 3 + 1))]) := by
  apply deckColumn_selfPair

example : ¬ poly.oneValue (deck.redP 2 (pdotVec (deckColumn 2) (deckColumn 2)))
    (deck.redP 2 [BPair.ofNat 12]) := by decide +kernel
example : ¬ poly.oneValue (deck.redP 2 (pdotVec (deckColumn 2) (deckColumn 2)))
    (deck.redP 2 [BPair.ofNat 8]) := by decide +kernel
example : ¬ poly.oneValue (deck.redP 3 (pdotVec (deckColumn 3) (deckColumn 3)))
    (deck.redP 3 [BPair.ofNat 12]) := by decide +kernel

/-! The Gram witness at the tex's own divided cofactor: the pair's
determinant against the two divisions of the deck symbol by the
chord's own linear factors — `P_L / (z - 2)` against `P_L / (z + 2)`
— reads the cleared constant `4L³` at the residue, the depth's
parity member the side's own sign.  The witness is the general
form's exhibit at the two committed sides, beside `orbCof`'s
witness-parametric read above. -/

example : gramUnitRead 2 (bandDatum orbT) (deckColumn 2) (deck.gramCof 2)
    (ground.BPair.ofNat 500).swap := by decide +kernel
example : gramUnitRead 3 (bandDatum (permMatAt 7 (tShift 3))) (deckColumn 3)
    (deck.gramCof 3) (ground.BPair.ofNat 1372) := by decide +kernel

/-! The doubling tier's three general theorems discharged at the
side-five orbit, each beside its own kernel instance: the crossed
pairing's null class (`deckColumn_crossNull`), the image's
self-pairing at `⟨4 : x²⟩` against the doubled side
(`deckColumn_imagePair`), and the pair's Gram determinant at `4L²`
(`gramDet_wrap`).  The frame is the wrap shift's own permutation
matrix, the spelling the general theorems read. -/

example : poly.oneValue
    (deck.redP 2 (pdotVec (deckColumn 2)
      (pmatVec (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2))))
    (deck.redP 2 []) := by decide +kernel
example : poly.oneValue
    (deck.redP 2 (pdotVec (deckColumn 2)
      (pmatVec (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2))))
    (deck.redP 2 []) := by apply deckColumn_crossNull

example : poly.oneValue
    (deck.redP 2 (pdotVec
      (pmatVec (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2))
      (pmatVec (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2))))
    (deck.redP 2 (poly.mul bandPoly [ground.BPair.ofNat 10])) := by decide +kernel
example : poly.oneValue
    (deck.redP 2 (pdotVec
      (pmatVec (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2))
      (pmatVec (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2))))
    (deck.redP 2 (poly.mul bandPoly [ground.BPair.ofNat 10])) := by
  apply deckColumn_imagePair

example : poly.oneValue
    (gramDet 2 (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2))
    (deck.redP 2 (poly.mul bandPoly [ground.BPair.ofNat 100])) := by decide +kernel
example : poly.oneValue
    (gramDet 2 (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2))
    (deck.redP 2 (poly.mul bandPoly [ground.BPair.ofNat 100])) := by
  apply gramDet_wrap

/-! The independence read discharged by its own general theorem at
the successor sides, the frame the wrap shift's permutation matrix
and the constant the theorem's own `4L³` at the depth's parity
member: the side-five witness `500̌` and the side-three witness
`108`, each beside its kernel instance.  The constant-agreement
step is one decided class read at the two spellings, the read's own
two clauses transported along it. -/

example : gramUnitRead 2 (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2)
    (deck.gramCof 2) (ground.BPair.ofNat 500).swap := by decide +kernel
example : gramUnitRead 2 (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2)
    (deck.gramCof 2) (ground.BPair.ofNat 500).swap := by
  have h := gramUnit_wrap 1
  have hc : (ground.BPair.ofNat (4 * (5 * (5 * 5)))
      * (deck.parityMember 2).swap).oneValue
      (ground.BPair.ofNat 500).swap := by decide +kernel
  exact ⟨fun hh => h.1 (ground.BPair.oneValue_trans hc hh),
    poly.oneValue_trans h.2 ⟨hc, trivial⟩⟩

example : gramUnitRead 1 (bandDatum (permMatAt 3 (tShift 1))) (deckColumn 1)
    (deck.gramCof 1) (ground.BPair.ofNat 108) := by decide +kernel
example : gramUnitRead 1 (bandDatum (permMatAt 3 (tShift 1))) (deckColumn 1)
    (deck.gramCof 1) (ground.BPair.ofNat 108) := by
  have h := gramUnit_wrap 0
  have hc : (ground.BPair.ofNat (4 * (3 * (3 * 3)))
      * (deck.parityMember 1).swap).oneValue
      (ground.BPair.ofNat 108) := by decide +kernel
  exact ⟨fun hh => h.1 (ground.BPair.oneValue_trans hc hh),
    poly.oneValue_trans h.2 ⟨hc, trivial⟩⟩

/-! The successor binder's own ground: at the base side the deck
symbol is the constant one, every residue is the length-`0` list,
and the stated occupied constant refuses — the binder `m + 1` the
theorem carries is load-bearing, not a convenience.  Beside it the
parity refusal at side five: the witness reads the depth's parity
member, and the member itself in place of its swap refuses. -/

example : ¬ gramUnitRead 0 (bandDatum (permMatAt 1 (tShift 0))) (deckColumn 0)
    (deck.gramCof 0)
    (ground.BPair.ofNat 4 * (deck.parityMember 0).swap) := by decide +kernel

example : ¬ gramUnitRead 2 (bandDatum (permMatAt 5 (tShift 2))) (deckColumn 2)
    (deck.gramCof 2) (ground.BPair.ofNat 500) := by decide +kernel

/-! The band symbol against the joined cofactors at the committed
sides, the composed congruence's class read; the band's freeness at
the committed factors — side five's quadratic, side nine's cubic
and linear — with the length binder's isolation, the length-free
factor dividing at the trivial remainder; and the theorem route at
side nine's mixed pair. -/

example : poly.oneValue
    (deck.redP 2 (poly.mul bandPoly (deck.gramCof 2)))
    (deck.redP 2 [(BPair.ofNat 5 * deck.parityMember 2).swap]) := by decide +kernel
example : poly.oneValue
    (deck.redP 3 (poly.mul bandPoly (deck.gramCof 3)))
    (deck.redP 3 [(BPair.ofNat 7 * deck.parityMember 3).swap]) := by decide +kernel

example : ¬ poly.unitTail
    (poly.div [(BPair.ofNat 1).swap, BPair.ofNat 1] bandPoly).2 := by decide +kernel
example : ¬ poly.unitTail
    (poly.div [BPair.ofNat 1, (BPair.ofNat 3).swap, BPair.unit]
      bandPoly).2 := by decide +kernel
example : ¬ poly.unitTail
    (poly.div [BPair.ofNat 1] bandPoly).2 := by decide +kernel

example : poly.unitTail
    (poly.div ([] : poly.Poly) bandPoly).2 := by decide +kernel

/-! The cofactor binder's isolation: the band's own two ends divide
the band symbol at the unit remainder, and each sits off the deck
symbol's factors at the division displays, so the conclusion fails
exactly where the factor hypothesis does. -/

example : poly.unitTail
    (poly.div [(BPair.ofNat 2).swap] bandPoly).2 := by decide +kernel
example : poly.unitTail
    (poly.div [BPair.ofNat 2] bandPoly).2 := by decide +kernel

example : ¬ poly.unitTail
    (poly.div [BPair.ofNat 1, (BPair.ofNat 3).swap, BPair.unit]
      bandPoly).2 :=
  bandFree_factor 4 [BPair.ofNat 1, (BPair.ofNat 3).swap, BPair.unit]
    (poly.monic [BPair.ofNat 1]) (by decide +kernel) (by decide +kernel)

/-! The block entries at a stated symbol, side five at
q = 1 + 2x + 3x²: the diagonal at the symbol's multiples of the
doubled side and the band symbol, the crossed entries null, a
forged constant refused, and the chord's own symbol recovering the
membership read's pairing. -/

private def qB5 : poly.Poly := [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3]
private def opB5 : elim.Mat :=
  polyEvalM qB5 (chordOp (permMatAt 5 (tShift 2))) 5
private def bdB5 : elim.Mat := bandDatum (permMatAt 5 (tShift 2))

example : poly.oneValue
    (deck.redP 2 (pdotVec (deckColumn 2) (pmatVec opB5 (deckColumn 2))))
    (deck.redP 2 (poly.mul qB5 [BPair.ofNat 10])) := by decide +kernel
example : poly.unitTail
    (deck.redP 2 (pdotVec (deckColumn 2)
      (pmatVec opB5 (pmatVec bdB5 (deckColumn 2))))) := by decide +kernel
example : poly.unitTail
    (deck.redP 2 (pdotVec (pmatVec bdB5 (deckColumn 2))
      (pmatVec opB5 (deckColumn 2)))) := by decide +kernel
example : poly.oneValue
    (deck.redP 2 (pdotVec (pmatVec bdB5 (deckColumn 2))
      (pmatVec opB5 (pmatVec bdB5 (deckColumn 2)))))
    (deck.redP 2 (poly.mul qB5 (poly.mul bandPoly [BPair.ofNat 10]))) := by
  decide +kernel
example : ¬ poly.oneValue
    (deck.redP 2 (pdotVec (deckColumn 2) (pmatVec opB5 (deckColumn 2))))
    (deck.redP 2 (poly.mul qB5 [BPair.ofNat 12])) := by decide +kernel

example : poly.oneValue
    (deck.redP 2 (pdotVec (deckColumn 2)
      (pmatVec (polyEvalM deck.wPoly (chordOp (permMatAt 5 (tShift 2))) 5)
        (deckColumn 2))))
    (deck.redP 2 (poly.mul deck.wPoly [BPair.ofNat 10])) := by decide +kernel

/-! The four block-entry reads at their own theorems, side five at
the stated symbol: every binder of the pinned statements exercised
through the theorem route. -/

example : poly.oneValue
    (deck.redP 2 (pdotVec (deckColumn 2)
      (pmatVec (polyEvalM qB5 (chordOp (permMatAt (2 * 2 + 1) (tShift 2)))
        (2 * 2 + 1)) (deckColumn 2))))
    (deck.redP 2 (poly.mul qB5 [BPair.ofNat (2 * (2 * 2 + 1))])) :=
  blockEntry_top 2 qB5

example : poly.unitTail
    (deck.redP 2 (pdotVec (deckColumn 2)
      (pmatVec (polyEvalM qB5 (chordOp (permMatAt (2 * 2 + 1) (tShift 2)))
        (2 * 2 + 1))
        (pmatVec (bandDatum (permMatAt (2 * 2 + 1) (tShift 2)))
          (deckColumn 2))))) :=
  blockEntry_cross 2 qB5

example : poly.unitTail
    (deck.redP 2 (pdotVec
      (pmatVec (bandDatum (permMatAt (2 * 2 + 1) (tShift 2))) (deckColumn 2))
      (pmatVec (polyEvalM qB5 (chordOp (permMatAt (2 * 2 + 1) (tShift 2)))
        (2 * 2 + 1)) (deckColumn 2)))) :=
  blockEntry_crossT 2 qB5

example : poly.oneValue
    (deck.redP 2 (pdotVec
      (pmatVec (bandDatum (permMatAt (2 * 2 + 1) (tShift 2))) (deckColumn 2))
      (pmatVec (polyEvalM qB5 (chordOp (permMatAt (2 * 2 + 1) (tShift 2)))
        (2 * 2 + 1))
        (pmatVec (bandDatum (permMatAt (2 * 2 + 1) (tShift 2)))
          (deckColumn 2)))))
    (deck.redP 2 (poly.mul qB5 (poly.mul bandPoly
      [BPair.ofNat (2 * (2 * 2 + 1))]))) :=
  blockEntry_bot 2 qB5

/-! The orthogonal frame's own refusal at side five: the wrap shift
applied twice is again a permutation matrix of the window, and its
orthogonality decides outright beside the refusal below, so the
independence read refusing the side-five witness at that frame
isolates the orbit's own translation — the shift by one step — from
the orthogonality the two frames share. -/

example : orthRead (permMatAt 5 (fun b => tShift 2 (tShift 2 b))) 5 := by
  decide +kernel

example : ¬ gramUnitRead 2
    (bandDatum (permMatAt 5 (fun b => tShift 2 (tShift 2 b))))
    (deckColumn 2) (deck.gramCof 2) (ground.BPair.ofNat 500).swap := by decide +kernel

/-! The refusals at the column.  The membership read refuses at the
wrong side's symbol — the side-three residue against the side-five
orbit, where the wrap has period three — and at the column with two
of its keys exchanged; the perpendicularity refuses at the chord
operator in place of the doubling datum, a symmetric matrix where
the read wants `Aᵀ = Ǎ`; and the independence refuses at a
dependent pair, the identity's image the column itself. -/

example : ¬ colMemberRead 1 orbS
    ((List.range 5).map (fun b => deck.redP 1 (deck.pFamN b))) := by decide +kernel

/-! The residue's wrap identities read at the side-five orbit's own
divisor: `deck.pFamN_wrapDown`, `deck.pFamN_side` and
`deck.pFamN_wrapUp` are general theorems over the indices, and
their content at `P_5` is decided here — `p_5` reads `p_0`, `p_4`
reads `p_1`, `p_3` reads `p_2` and `p_6` reads `p_1` at the
residue.  The index join is load-bearing: `p_3` does not read
`p_1`, and at the side-three symbol the wrap has period three, so
`p_4` does not read `p_0` there. -/

example : poly.oneValue (deck.redP 2 (deck.pFamN 5)) (deck.redP 2 (deck.pFamN 0)) := by
  decide +kernel
example : poly.oneValue (deck.redP 2 (deck.pFamN 4)) (deck.redP 2 (deck.pFamN 1)) := by
  decide +kernel
example : poly.oneValue (deck.redP 2 (deck.pFamN 3)) (deck.redP 2 (deck.pFamN 2)) := by
  decide +kernel
example : poly.oneValue (deck.redP 2 (deck.pFamN 6)) (deck.redP 2 (deck.pFamN 1)) := by
  decide +kernel

example : ¬ poly.oneValue (deck.redP 2 (deck.pFamN 3))
    (deck.redP 2 (deck.pFamN 1)) := by decide +kernel
example : ¬ poly.oneValue (deck.redP 1 (deck.pFamN 4))
    (deck.redP 1 (deck.pFamN 0)) := by decide +kernel

example : ¬ colMemberRead 2 orbS
    [deck.redP 2 (deck.pFamN 0), deck.redP 2 (deck.pFamN 2), deck.redP 2 (deck.pFamN 1),
     deck.redP 2 (deck.pFamN 3), deck.redP 2 (deck.pFamN 4)] := by decide +kernel

example : ¬ perpRead 2 orbS (deckColumn 2) := by decide +kernel

example : ¬ gramUnitRead 2 (inertia.idMat 5) (deckColumn 2) orbCof
    (BPair.ofNat 50000) := by decide +kernel

/-! The vector bridge at the side-five symbol: the entrywise wrap
congruences `p_4 = p_1` and `p_3 = p_2` carry the two-entry vector
onto its own residue read (`prow_redP`), the class spelling read at
the membership read's own.  The entries are load-bearing: the read
refuses at a second entry the symbol does not join. -/

/-- The two-entry index read: a stated pair of congruences is the
indexed hypothesis the vector bridge consumes. -/
private theorem pairCong {m : Nat} {a b c d : poly.Poly}
    (h0 : ∃ e, deck.pCong m e a c) (h1 : ∃ e, deck.pCong m e b d) :
    ∀ i, i < [a, b].length →
      ∃ e, deck.pCong m e (ground.getAt [] [a, b] i)
        (ground.getAt [] [c, d] i)
  | 0, _ => h0
  | 1, _ => h1
  | _ + 2, h =>
    absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h))
      (Nat.not_lt_zero _)

example : split.prowOneValue
    (redVec 2 [deck.pFamN 4, deck.pFamN 3])
    (redVec 2 [deck.pFamN 1, deck.pFamN 2]) :=
  prow_redP 2 _ _ rfl
    (pairCong (deck.pFamN_wrapDown 2 1 1 rfl)
      (deck.pFamN_wrapDown 2 0 2 rfl))

example : ¬ split.prowOneValue
    (redVec 2 [deck.pFamN 4, deck.pFamN 1])
    (redVec 2 [deck.pFamN 1, deck.pFamN 0]) := by decide +kernel

/-! The chord's entries at the wrap shift, the general theorem
against the kernel.  `colMember_wrap` discharges the membership
read at every side off the deck symbol alone; the committed sides
run through seven, past the key where the divisor read's former
equality spelling refused, and side seven reads by the theorem and
by the kernel at once.  The chord is load-bearing: the bare shift
matrix, its witness's rows absent, refuses the read — the
recursion's sum needs both neighbours.  The shift's range reads
commit with their refusals: the shift leaves the range exactly at
the off-range keys, the witness's return clause refutes at the one
key past the range and holds at every further key, and the
witness-after-shift identity is unconditional, its off-range
instance beside the ranged one. -/

example : colMemberRead 1 (chordOp (permMatAt 3 (tShift 1))) (deckColumn 1) :=
  colMember_wrap 1

example : colMemberRead 2 (chordOp (permMatAt 5 (tShift 2))) (deckColumn 2) :=
  colMember_wrap 2

example : colMemberRead 3 (chordOp (permMatAt 7 (tShift 3))) (deckColumn 3) :=
  colMember_wrap 3

example : colMemberRead 1 (chordOp (permMatAt 3 (tShift 1))) (deckColumn 1) := by
  decide +kernel

example : colMemberRead 3 (chordOp (permMatAt 7 (tShift 3))) (deckColumn 3) := by
  decide +kernel

example : ¬ colMemberRead 2 (permMatAt 5 (tShift 2)) (deckColumn 2) := by decide +kernel

example : ∀ j, j < 2 * 2 + 1 → tShift 2 j < 2 * 2 + 1 := tShift_lt 2
example : ¬ (tShift 2 5 < 2 * 2 + 1) := by decide +kernel

example : sShift 2 (tShift 2 4) = 4 := sShift_tShift 2 4
example : sShift 2 (tShift 2 99) = 99 := sShift_tShift 2 99

example : tShift 2 (sShift 2 0) = 0 := tShift_sShift 2 0 (by decide +kernel)
example : ¬ (tShift 2 (sShift 2 5) = 5) := by decide +kernel
example : tShift 2 (sShift 2 6) = 6 := by decide +kernel

/-! The `Q`-family column is not a refusal, and the module records
what it exhibits rather than an expectation: the two deck families
run the one recursion and differ only at their seeds, so the shifted
`Q` list is again a cyclic eigenvector of the chord at the residue —
and it is an *independent* second member of the root block, which is
the doubling's own exhibit at the orbit.  What separates the
families is the seed `p₀ = 2` the tex's own column carries, not the
membership read; what the pair `(u, Q)` decides here is the same
`2`-dimensional block `(u, A u)` decides, off the doubling datum
entirely.  The `(p, Q)`-Gram at the residue is `15 - 20x`, whose
conjugate `35 + 20x` is its Bézout cofactor at the occupied constant
`125` — `gramDet`'s own expression and `gramUnitRead`'s own two
clauses, at two stated columns. -/

private def orbQCol : List poly.Poly :=
  (List.range 5).map (fun b => deck.redP 2 (deck.qFam (ground.posOfSucc b)))

example : colMemberRead 2 orbS orbQCol := by decide +kernel

/-- The `(p, Q)`-pair's Gram determinant at the residue, `gramDet`'s
expression read at two stated columns rather than at a column and
its doubling image. -/
private def pqGramDet : poly.Poly :=
  deck.redP 2
    (poly.add
      (poly.mul (pdotVec (deckColumn 2) (deckColumn 2))
        (pdotVec orbQCol orbQCol))
      (poly.neg (poly.mul (pdotVec (deckColumn 2) orbQCol)
        (pdotVec orbQCol (deckColumn 2)))))

private def pqCof : poly.Poly := [BPair.ofNat 35, BPair.ofNat 20]

example : ¬ (BPair.ofNat 125).oneValue BPair.unit := by decide +kernel

example : poly.oneValue (deck.redP 2 (poly.mul pqGramDet pqCof))
    [BPair.ofNat 125] := by decide +kernel

/-! The count squeeze at the residue: the identification at the
wrap shift, the unit fiber whole at the orbit's sum with that
fiber's span read, the pair base's own count, and the Horner read
at a doubled-chord fixed vector.  Each wrap read sits at the two
committed sides — the side-three bench and the side-five orbit —
with its general theorem applied beside the kernel's own decision
and the side-seven instance discharged by the theorem, and the
load-bearing binders carry their refusals: a stated vector off the
kernel refuses the span read at the sum's own list, and a vector
the chord fails to double refuses the Horner read's scale. -/

example : identRead (permMatAt 3 (tShift 1)) 3 := by decide +kernel
example : identRead (permMatAt 3 (tShift 1)) 3 := identRead_wrap 1
example : identRead (permMatAt 5 (tShift 2)) 5 := by decide +kernel
example : identRead (permMatAt 5 (tShift 2)) 5 := identRead_wrap 2
example : identRead (permMatAt 7 (tShift 3)) 7 := identRead_wrap 3

example : unitFiberRead (permMatAt 3 (tShift 1)) 3 [orbitSum 1] := by decide +kernel
example : unitFiberRead (permMatAt 3 (tShift 1)) 3 [orbitSum 1] :=
  unitFiber_wrap 1
example : unitFiberRead (permMatAt 5 (tShift 2)) 5 [orbitSum 2] := by decide +kernel
example : unitFiberRead (permMatAt 5 (tShift 2)) 5 [orbitSum 2] :=
  unitFiber_wrap 2
example : unitFiberRead (permMatAt 7 (tShift 3)) 7 [orbitSum 3] :=
  unitFiber_wrap 3

/-! The splitting's two stated lists at their own counts: the
orbit's sum at the side and the pair base at the doubled depth, the
theorem beside the decision. -/

example : (orbitSum 2).length = 5 := by decide +kernel
example : (pairBase 1).length = 2 := by decide +kernel
example : (pairBase 1).length = 2 := pairBase_len 1
example : (pairBase 2).length = 4 := by decide +kernel
example : (pairBase 2).length = 4 := pairBase_len 2
example : (pairBase 3).length = 6 := pairBase_len 3
example : poly.oneValue (sliceAt 0 (deckColumn 2))
    [BPair.ofNat 2, BPair.unit, (BPair.ofNat 1).swap,
      (BPair.ofNat 1).swap, BPair.unit] := by decide +kernel

/-! The unit fiber's span read at the sum's own list: an orbit
member reads through it, and the key-`0` seed vector — off the
pair `(S : 2)`'s kernel, its own refusal committed beside — reads
outside the span. -/

private def orbTriple : List BPair :=
  [BPair.ofNat 3, BPair.ofNat 3, BPair.ofNat 3]

private def orbSeed : List BPair :=
  [BPair.ofNat 1, BPair.unit, BPair.unit]

example : spanRel 3 [orbitSum 1] orbTriple := by decide +kernel
example : spanRel 3 [orbitSum 1] orbTriple :=
  unitFiber_span 1 orbTriple (by decide +kernel) (by decide +kernel)
example : spanRel 5 [orbitSum 2] (orbitSum 2) :=
  unitFiber_span 2 (orbitSum 2) (by decide +kernel) (by decide +kernel)

example : ¬ poly.unitTail
    (matVec (unitDatum (permMatAt 3 (tShift 1)) 3) orbSeed) := by decide +kernel
example : ¬ spanRel 3 [orbitSum 1] orbSeed := by decide +kernel

/-! The Horner read at the doubled-chord fixed vector: the deck
symbol at the side-three orbit reads the orbit's sum at the
evaluation's own scale, the theorem beside the decision, and the
seed vector — which the chord fails to double, its own refusal
committed beside — refuses the scale. -/

example : poly.oneValue
    (matVec (polyEvalM (deck.pSum 1) (chordOp (permMatAt 3 (tShift 1))) 3)
      (orbitSum 1))
    (vecScale (poly.eval (deck.pSum 1) (BPair.ofNat 2)) (orbitSum 1)) := by
  decide +kernel
example : poly.oneValue
    (matVec (polyEvalM (deck.pSum 1) (chordOp (permMatAt 3 (tShift 1))) 3)
      (orbitSum 1))
    (vecScale (poly.eval (deck.pSum 1) (BPair.ofNat 2)) (orbitSum 1)) :=
  polyEval_fixed 3 (deck.pSum 1) (chordOp (permMatAt 3 (tShift 1)))
    (orbitSum 1) (by decide +kernel) (by decide +kernel)
example : poly.oneValue
    (matVec (polyEvalM (deck.pSum 2) (chordOp (permMatAt 5 (tShift 2))) 5)
      (orbitSum 2))
    (vecScale (poly.eval (deck.pSum 2) (BPair.ofNat 2)) (orbitSum 2)) :=
  polyEval_fixed 5 (deck.pSum 2) (chordOp (permMatAt 5 (tShift 2)))
    (orbitSum 2) (by decide +kernel) (by decide +kernel)

example : ¬ poly.oneValue
    (matVec (chordOp (permMatAt 3 (tShift 1))) orbSeed)
    (vecScale (BPair.ofNat 2) orbSeed) := by decide +kernel
example : ¬ poly.oneValue
    (matVec (polyEvalM (deck.pSum 1) (chordOp (permMatAt 3 (tShift 1))) 3)
      orbSeed)
    (vecScale (poly.eval (deck.pSum 1) (BPair.ofNat 2)) orbSeed) := by decide +kernel

/-! The column's Horner read at the chord, `colMember_wrap`
iterated along a stated polynomial: at the deck symbol itself the
image residues are the symbol's own multiples, the null class key
by key — the exactness read the root datum's kernel consumes — and
at the chord variable the read is the membership itself.  Each sits
at the two committed sides with the theorem beside the kernel's own
decision, and the refusal separates the polynomials: the symbol's
read against the chord variable's target refuses. -/

example : split.prowOneValue
    (redVec 1 (pmatVec (polyEvalM (deck.pSum 1)
      (chordOp (permMatAt 3 (tShift 1))) 3) (deckColumn 1)))
    (redVec 1 ((deckColumn 1).map (fun p => poly.mul (deck.pSum 1) p))) := by
  decide +kernel
example : split.prowOneValue
    (redVec 1 (pmatVec (polyEvalM (deck.pSum 1)
      (chordOp (permMatAt 3 (tShift 1))) 3) (deckColumn 1)))
    (redVec 1 ((deckColumn 1).map (fun p => poly.mul (deck.pSum 1) p))) :=
  polyEval_column 1 (deck.pSum 1)
example : split.prowOneValue
    (redVec 2 (pmatVec (polyEvalM (deck.pSum 2)
      (chordOp (permMatAt 5 (tShift 2))) 5) (deckColumn 2)))
    (redVec 2 ((deckColumn 2).map (fun p => poly.mul (deck.pSum 2) p))) :=
  polyEval_column 2 (deck.pSum 2)
example : split.prowOneValue
    (redVec 3 (pmatVec (polyEvalM (deck.pSum 3)
      (chordOp (permMatAt 7 (tShift 3))) 7) (deckColumn 3)))
    (redVec 3 ((deckColumn 3).map (fun p => poly.mul (deck.pSum 3) p))) :=
  polyEval_column 3 (deck.pSum 3)

example : split.prowOneValue
    (redVec 2 (pmatVec (polyEvalM deck.wPoly
      (chordOp (permMatAt 5 (tShift 2))) 5) (deckColumn 2)))
    (redVec 2 ((deckColumn 2).map (fun p => poly.mul deck.wPoly p))) := by
  decide +kernel
example : split.prowOneValue
    (redVec 2 (pmatVec (polyEvalM deck.wPoly
      (chordOp (permMatAt 5 (tShift 2))) 5) (deckColumn 2)))
    (redVec 2 ((deckColumn 2).map (fun p => poly.mul deck.wPoly p))) :=
  polyEval_column 2 deck.wPoly

/-! The symbol's own multiples read the null class at the residue,
the division display's exactness at every key of the side-five
column. -/

example : ((deckColumn 2).map
    (fun p => deck.redP 2 (poly.mul (deck.pSum 2) p))).all
    (fun p => decide (poly.unitTail p)) = true := by decide +kernel

/-! The two polynomials separated: the symbol's Horner read against
the chord variable's own target refuses at side five. -/

example : ¬ split.prowOneValue
    (redVec 2 (pmatVec (polyEvalM (deck.pSum 2)
      (chordOp (permMatAt 5 (tShift 2))) 5) (deckColumn 2)))
    (redVec 2 ((deckColumn 2).map (fun p => poly.mul deck.wPoly p))) := by
  decide +kernel

/-! The count squeeze at the splitting's own lists
(`orbitSplit_indep`, `orbitSplit_span`, `rootBlock_wrap`,
`rootBlock_span`): the joined list independent at the orbit's own
count, the width bound turning the count into the span, the pair
base a kernel list at the independence, and a root-datum kernel
member reading through the pairs alone.  Each theorem route sits
beside a decision at every side, side seven's own reads decided
through the pivot descent (`elim.detD_eq`); the length binders are
the carrier's member frame (`con:places`'s matched lists), cited in
place. -/

example : indepRows 3 ([orbitSum 1] ++ pairBase 1) := by decide +kernel
example : indepRows 3 ([orbitSum 1] ++ pairBase 1) := orbitSplit_indep 1
example : indepRows 5 ([orbitSum 2] ++ pairBase 2) := by decide +kernel
example : indepRows 5 ([orbitSum 2] ++ pairBase 2) := orbitSplit_indep 2
example : indepRows 7 ([orbitSum 3] ++ pairBase 3) := by decide +kernel
example : indepRows 7 ([orbitSum 3] ++ pairBase 3) := orbitSplit_indep 3

/-! The independence refused at a forged pair base: the first
coefficient row repeated in the image row's place, the repeat a
dependency the joined list reads outright. -/

example : ¬ indepRows 3
    ([orbitSum 1] ++
      [sliceAt 0 (deckColumn 1), sliceAt 0 (deckColumn 1)]) := by decide +kernel

example : spanRel 3 ([orbitSum 1] ++ pairBase 1) orbSeed := by decide +kernel
example : spanRel 3 ([orbitSum 1] ++ pairBase 1) orbSeed :=
  orbitSplit_span 1 orbSeed (by decide +kernel)
example : spanRel 5 ([orbitSum 2] ++ pairBase 2)
    [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 3, BPair.ofNat 4,
      BPair.ofNat 5] :=
  orbitSplit_span 2 _ (by decide +kernel)

example : rootBlockRead (permMatAt 3 (tShift 1)) 3 1 (pairBase 1) := by
  decide +kernel
example : rootBlockRead (permMatAt 3 (tShift 1)) 3 1 (pairBase 1) :=
  rootBlock_wrap 1
example : rootBlockRead (permMatAt 5 (tShift 2)) 5 2 (pairBase 2) := by
  decide +kernel
example : rootBlockRead (permMatAt 5 (tShift 2)) 5 2 (pairBase 2) :=
  rootBlock_wrap 2
example : rootBlockRead (permMatAt 7 (tShift 3)) 7 3 (pairBase 3) := by
  decide +kernel
example : rootBlockRead (permMatAt 7 (tShift 3)) 7 3 (pairBase 3) :=
  rootBlock_wrap 3

/-! The kernel conjunct refused at the joined pool: the orbit's sum
reads the root datum at the word's value off the unit, so the
joined list sits off the kernel read while keeping the
independence. -/

example : ¬ rootBlockRead (permMatAt 3 (tShift 1)) 3 1
    ([orbitSum 1] ++ pairBase 1) := by decide +kernel

example : spanRel 3 (pairBase 1) (sliceAt 0 (deckColumn 1)) := by decide +kernel
example : spanRel 3 (pairBase 1) (sliceAt 0 (deckColumn 1)) :=
  rootBlock_span 1 (sliceAt 0 (deckColumn 1)) (by decide +kernel) (by decide +kernel)
example : spanRel 5 (pairBase 2) (sliceAt 1 (deckColumn 2)) :=
  rootBlock_span 2 (sliceAt 1 (deckColumn 2)) (by decide +kernel) (by decide +kernel)

/-! The kernel hypothesis isolated: the orbit's sum fails the root
datum's kernel read — its image the word's value `P_L(2) = L` off
the unit — and sits outside the pair base's span with it, the
exactly-two read's own refusal pair. -/

example : ¬ poly.unitTail
    (matVec (polyEvalM (deck.pSum 1)
      (chordOp (permMatAt 3 (tShift 1))) 3) (orbitSum 1)) := by decide +kernel
example : ¬ spanRel 3 (pairBase 1) (orbitSum 1) := by decide +kernel

/-! The band root and the fiber pencil: the band root's datum at a
rational bench chord — the located roots of `P_5` are irrational
and enter over `lem:stagesplit`'s quadratic extension, so the
ground-arithmetic instance is the chord `1` at the clearing `2`,
`4 s² + t² = 4` reading `s² = 3/4` — and the band congruence at the
orbit's own compression, a two-member block list carrying the
window pencil `S` against the unit gram to its level pencil, the
descent rescaling the image column, and the image at the shape
`lem:cellcount`'s counts consume. -/

example : bandRootRead (BPair.ofNat 2) (BPair.ofNat 3) (2 : Pos) := by
  decide +kernel

private def blkL : Mat :=
  [[BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1, BPair.ofNat 1,
    BPair.ofNat 1],
   [BPair.ofNat 1, BPair.unit, BPair.unit, BPair.unit, BPair.unit]]

/-- The pair descent at the block, its determinant the minor `2`. -/
private def blkT : SqMat 2 :=
  ⟨[[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 2]], by decide +kernel⟩

/-- The descent's invertibility witness at the integer carrier: the
adjugate, whose two products against the descent read the
determinant off the identity. -/
private def blkTw : SqMat 2 :=
  ⟨[[BPair.ofNat 2, BPair.unit], [BPair.unit, BPair.ofNat 1]], by decide +kernel⟩

private def fibP : split.PMat :=
  [[[(BPair.ofNat 10).swap, BPair.ofNat 5],
    [(BPair.ofNat 4).swap, BPair.ofNat 2]],
   [[(BPair.ofNat 4).swap, BPair.ofNat 2],
    [BPair.unit, BPair.ofNat 4]]]

example : fiberPencilRead 5 orbS (inertia.idMat 5) blkL blkT blkTw fibP 1
    (BPair.ofNat 2) (BPair.ofNat 3) (2 : Pos) := by decide +kernel

/-! The congruence refused off its own descent: the same block at
the identity descent — its own invertibility witness the identity,
the two product reads landing — leaves the image columns unrescaled,
and the stated fiber pencil is no longer its congruence. -/

example : ¬ bandCongrRead
    (split.zMat (matMul blkL (matMul orbS (transposeM blkL)))
      (matMul blkL (matMul (inertia.idMat 5) (transposeM blkL))))
    (⟨inertia.idMat 2, by decide +kernel⟩ : SqMat 2)
    (⟨inertia.idMat 2, by decide +kernel⟩ : SqMat 2) fibP := by decide +kernel

/-! The fiber pencil produced at sides three and five: the wrap
frame's chord operator against the unit gram, the descent entering
as stated data at the clearing's block diagonal with its adjugate —
the bench spelling of `lem:inertia`'s cleared congruence — every
conjunct of the stated data decided beside the theorem route.  The
binders classify: the window reads `hH`/`hG` are load-bearing at
the truncation trap (a ragged window refused below), the witness
conjuncts are the congruence's own data (the adjugate forged one
power short refused), and the root datum is the stated hypothesis —
refused at a square on the sum's unit alone (the identity and the
interiority kept, clearing one), at a square off `4 s² + t² = 4`,
and at the interiority alone (a negative square at the identity
kept); the shape read's degree conjunct has its refusal at
`lem:cellcount`'s battery. -/

private def wrapH (m : Nat) : Mat :=
  chordOp (permMatAt (2 * m + 1) (tShift m))

private def wrapZ (m : Nat) : split.PMat :=
  split.zMat
    (matMul (pairBase m) (matMul (wrapH m) (transposeM (pairBase m))))
    (matMul (pairBase m)
      (matMul (inertia.idMat (2 * m + 1)) (transposeM (pairBase m))))

private def dT1 : elim.Mat :=
  [[BPair.ofNat 1, BPair.unit], [BPair.unit, BPair.ofNat 2]]
private def dTw1 : elim.Mat :=
  [[BPair.ofNat 2, BPair.unit], [BPair.unit, BPair.ofNat 1]]
private def dT2 : elim.Mat :=
  split.diagM [BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 1, BPair.ofNat 2]
private def dTw2 : elim.Mat :=
  split.diagM [BPair.ofNat 4, BPair.ofNat 2, BPair.ofNat 4, BPair.ofNat 2]

example : (elim.minor dT2).oneValue (BPair.ofNat 4) := by decide +kernel
example : (elim.minor dT2).offUnit := by decide +kernel

example : elim.matOneValue (matMul dT2 dTw2)
    (inertia.matScaleB (elim.minor dT2) (inertia.idMat 4)) := by decide +kernel
example : elim.matOneValue (matMul dTw2 dT2)
    (inertia.matScaleB (elim.minor dT2) (inertia.idMat 4)) := by decide +kernel

example : ¬ elim.matOneValue (matMul dT2
    (split.diagM [BPair.ofNat 2, BPair.ofNat 1,
      BPair.ofNat 2, BPair.ofNat 1]))
    (inertia.matScaleB (elim.minor dT2) (inertia.idMat 4)) := by
  decide +kernel

example : ¬ bandRootRead (BPair.ofNat 2) BPair.unit (1 : Pos) := by decide +kernel
example : ¬ bandRootRead (BPair.ofNat 2) (BPair.ofNat 4) (2 : Pos) := by
  decide +kernel
example : ¬ bandRootRead (BPair.ofNat 4)
    (BPair.swap (BPair.ofNat 3)) (1 : Pos) := by decide +kernel

example : fiberPencilRead 3 (wrapH 1) (inertia.idMat 3) (pairBase 1)
    (⟨dT1, by decide +kernel⟩ : SqMat 2) (⟨dTw1, by decide +kernel⟩ : SqMat 2)
    (split.congrZ dT1 (wrapZ 1)) 1
    (BPair.ofNat 2) (BPair.ofNat 3) (2 : Pos) :=
  fiberPencil_produce 1 3 (wrapH 1) (inertia.idMat 3)
    (⟨dT1, by decide +kernel⟩ : SqMat 2) (⟨dTw1, by decide +kernel⟩ : SqMat 2) 2
    (BPair.ofNat 2) (BPair.ofNat 3) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : fiberPencilRead 5 (wrapH 2) (inertia.idMat 5) (pairBase 2)
    (⟨dT2, by decide +kernel⟩ : SqMat 4) (⟨dTw2, by decide +kernel⟩ : SqMat 4)
    (split.congrZ dT2 (wrapZ 2)) 1
    (BPair.ofNat 2) (BPair.ofNat 3) (2 : Pos) :=
  fiberPencil_produce 2 5 (wrapH 2) (inertia.idMat 5)
    (⟨dT2, by decide +kernel⟩ : SqMat 4) (⟨dTw2, by decide +kernel⟩ : SqMat 4) 2
    (BPair.ofNat 2) (BPair.ofNat 3) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The window reads refused at a ragged window: the truncated
compression would certify a mis-shaped pencil, and the read refuses
at the order conjunct alone, the further conjuncts kept at the
stated data. -/

example : ¬ fiberPencilRead 3 [[BPair.ofNat 1, BPair.ofNat 2]]
    (inertia.idMat 3) (pairBase 1)
    (⟨dT1, by decide +kernel⟩ : SqMat 2) (⟨dTw1, by decide +kernel⟩ : SqMat 2)
    (split.congrZ dT1
      (split.zMat
        (matMul (pairBase 1) (matMul [[BPair.ofNat 1, BPair.ofNat 2]]
          (transposeM (pairBase 1))))
        (matMul (pairBase 1) (matMul (inertia.idMat 3)
          (transposeM (pairBase 1)))))) 1
    (BPair.ofNat 2) (BPair.ofNat 3) (2 : Pos) := by decide +kernel

/-! A term's support at a fiber of three slots: on the two-direction
torus at side three over two letters, the adjoint on the eight
links of two squares sharing one vertex, that vertex at
multiplicity three (four adjoint links), beside the first square's
fundamental loop, five positions with the unit line.  The support
admits an entry within the three-slot fiber, the member its own
target on the square's row, and refuses one across the two
members, the loop off the adjoint member's row. -/

private def torW : Region := torusRegion 2 3
private def torPlaq (i : Nat) : List (Nat × Bool) := ground.getAt [] torW.plaqs i
private def torPair : List places.Shape :=
  (List.range torW.links).map (fun l =>
    if (torPlaq 0).any (fun e => e.1 == l) || (torPlaq 4).any (fun e => e.1 == l)
    then [2, 0] else [0, 0])
private def torLoop : List places.Shape :=
  (List.range torW.links).map (fun l =>
    if (torPlaq 0).any (fun e => e.1 == l) then [1, 0] else [0, 0])
private def ixT : List (List places.Shape) := [torPair, torLoop]
private def e5 (i j : Nat) : Mat :=
  ground.matOf 5 5 (fun a b =>
    if (a == i && b == j) || (a == j && b == i) then ⟨2, 1⟩ else BPair.unit)

example : (pairpencil.slotList (dataA 2) torW ixT).length = 4
    ∧ carrier.occupied (dataA 2) torW torPair = true := by decide +kernel
/-! The gram's block content at the three-slot fiber: the four-end
vertex's Gram at the direct tag over two letters (the kernel list's
three members at their primitive representatives in the slot
power's coordinates, the check module for `con:fiber`'s pin), the
six two-end
vertices at the coevaluation's three, the star's read at the tie
over two letters, and the eight links' scale `[1 : 3]` each, so at
the clearing nine the block is that vertex Gram outright, the loop
member's block the clearing;
the identity gram is refused with the coupling within the fiber it
admitted at the shape read alone, the block at the clearing one is
refused, and the two members coupled are refused. -/

private def gT5 : Mat :=
  [[BPair.ofNat 9, BPair.unit, BPair.unit, BPair.unit, BPair.unit],
   [BPair.unit, BPair.ofNat 144, (BPair.ofNat 144).swap, BPair.ofNat 48, BPair.unit],
   [BPair.unit, (BPair.ofNat 144).swap, BPair.ofNat 336, (BPair.ofNat 144).swap, BPair.unit],
   [BPair.unit, BPair.ofNat 48, (BPair.ofNat 144).swap, BPair.ofNat 144, BPair.unit],
   [BPair.unit, BPair.unit, BPair.unit, BPair.unit, BPair.ofNat 9]]

/-- The torus gram's split as stated data at the clearing nine
(`lem:inertia`'s certificate data, re-read by `splitRead`). -/
private def gT5Sp : inertia.Split 5 :=
  ⟨⟨[[⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 10⟩, ⟨104977, 1⟩, ⟨1, 37018604205637633⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨104977, 1⟩, ⟨1, 111055812616912897⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 222111625233825793⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨876604825116072439516682081700537912287760040895447041, 1⟩]], rfl⟩,
   ⟨[[⟨183953339572218355818288152625160962318886751936519204186186106405985053573121, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 20439259952468706202032016958351218035431861326279911576242900711776117063681⟩, ⟨20439259952468706202032016958351218035431861326279911576242900711776117063681, 1⟩, ⟨1, 6813086650822902067344005652783739345143953775426637192080966903925372354561⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1752337101549100325962964416868245716343609510140595985617532639898501121, 1⟩, ⟨1, 876168550774550162981482208434122858171804755070297992808766319949250561⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 828202213092463383696328963877361010922879082477364036239361⟩, ⟨1, 1⟩],
     [⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨209847509734914867068929, 1⟩]], rfl⟩,
   [.one ⟨10, 1⟩,
    .one ⟨11665, 1⟩,
    .one ⟨2115832430593, 1⟩,
    .one ⟨3946685925120918264859080080354181121, 1⟩,
    .one ⟨6915924174751019514658450555513427682916850342835994332150977291331874745396836324972592816085497413002854401, 1⟩],
   0, rfl⟩
example : pairpencil.gramBlockRead (dataA 2) torW 5 ixT 9 gT5
    ∧ inertia.splitRead gT5 gT5Sp ∧ inertia.pdAt gT5Sp := by decide +kernel
example : ¬ pairpencil.gramBlockRead (dataA 2) torW 5 ixT 1
      (matAdd (inertia.idMat 5) (e5 1 3))
    ∧ ¬ pairpencil.gramBlockRead (dataA 2) torW 5 ixT 1 gT5
    ∧ ¬ pairpencil.gramBlockRead (dataA 2) torW 5 ixT 9 (matAdd gT5 (e5 1 4)) := by
  decide +kernel
example : pairpencil.termSupport (dataA 2) torW 5 ixT (torPlaq 0) (e5 1 2) := by
  decide +kernel
example : ¬ pairpencil.termSupport (dataA 2) torW 5 ixT (torPlaq 0) (e5 1 4) := by
  decide +kernel
