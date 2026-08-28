import MassGap.Weyldim
import MassGapChecks.Sertables
/-!
The check module for `cor:weyldim`: the batteries re-read the
dimension product by kernel `decide` — the gap products on the
sorted displays, the dimension values against `def:blockcount`'s
pinned span dimensions at the su(2) and su(3) instances, and the
cross-multiplied naming read, per instance the exact cofactor's
whole verification.

The count-identity tier closes `cor:weyldim`'s A-series half:
`spanProd` by the theorem route with kernel-decided twins, the
computing read against the span's count, the display at every
shape, and the coherence-face refusals at the forged span counts.

The member battery tier closes the module at `B_2`'s first
fundamental: the two degree maps at the exchange with their crossed
count clauses, the crown `memberRead` applied whole by the theorem
route with the two gap products and the computed twin beside it,
the gap comparison `memberGap_le` at the same data, and the forge
tier at the load-bearing binders.  The fixtures' spelling follows
`ChecksMemberchar`'s — the multiplicity family, its witnesses, and
the shifted alternant's eight-member orbit are the self-contained
copies the check-module convention takes.
-/
set_option maxHeartbeats 4000000

open ground places weyldim

/-! The gap products on the displays. -/

example : gapProd [3, 1] = 2 := rfl
example : gapProd [5, 3, 1] = 16 := rfl
example : gapProd [3, 2, 1] = 2 := rfl

/-! The dimension values at the pinned span dimensions. -/

example : dimOf [1] = 1 := by decide +kernel
example : dimOf [1, 1] = 2 := by decide +kernel
example : dimOf [1, 0] = 2 := by decide +kernel
example : dimOf [2, 0] = 3 := by decide +kernel
example : dimOf [0, 1] = 1 := by decide +kernel
example : dimOf [2, 1] = 3 := by decide +kernel
example : dimOf [1, 0, 0] = 3 := by decide +kernel
example : dimOf [1, 1, 0] = 8 := by decide +kernel

/-! The naming read, the division's per-instance exactness
certificate. -/

example : weyldim.read [1, 0] := by decide +kernel
example : weyldim.read [1, 1, 0] := by decide +kernel
example : weyldim.read [0, 0, 1] := by decide +kernel
example : weyldim.read [2, 2, 0] := by decide +kernel

/-! The count identity tier (`cor:weyldim`'s A-series half): the
span's count against the unit display's gap product reads the
shape's own, `spanProd` applied whole by the theorem route with
the kernel-decided twin beside it, `dimOf_spanLen` and `readAll`
closing the display at the same shapes.  The `dimOf` values at
these shapes stand pinned above (the dimension-values tier).
Classification: `spanProd` is binderless — the shape is the
occupancy family, the carrier unique by construction — so the
forge tier pins the coherence face instead: a forged span count,
one off the true count, refusing the product identity, the
identity's own discrimination. -/

example : (blockcount.blockSpan ([1] : Shape)).length
    * gapProd (display (List.replicate 1 0))
  = gapProd (display ([1] : Shape)) := spanProd [1]
example : (blockcount.blockSpan ([1] : Shape)).length
    * gapProd (display (List.replicate 1 0))
  = gapProd (display ([1] : Shape)) := by decide +kernel

example : (blockcount.blockSpan ([1, 1] : Shape)).length
    * gapProd (display (List.replicate 2 0))
  = gapProd (display ([1, 1] : Shape)) := spanProd [1, 1]
example : (blockcount.blockSpan ([1, 1] : Shape)).length
    * gapProd (display (List.replicate 2 0))
  = gapProd (display ([1, 1] : Shape)) := by decide +kernel

example : (blockcount.blockSpan ([1, 1, 0] : Shape)).length
    * gapProd (display (List.replicate 3 0))
  = gapProd (display ([1, 1, 0] : Shape)) := spanProd [1, 1, 0]
example : (blockcount.blockSpan ([1, 1, 0] : Shape)).length
    * gapProd (display (List.replicate 3 0))
  = gapProd (display ([1, 1, 0] : Shape)) := by decide +kernel

example : dimOf [1] = (blockcount.blockSpan ([1] : Shape)).length :=
  dimOf_spanLen [1]
example : dimOf [1, 1]
    = (blockcount.blockSpan ([1, 1] : Shape)).length :=
  dimOf_spanLen [1, 1]
example : dimOf [1, 1, 0]
    = (blockcount.blockSpan ([1, 1, 0] : Shape)).length :=
  dimOf_spanLen [1, 1, 0]

example : weyldim.read [1] := readAll [1]
example : weyldim.read [1, 1] := readAll [1, 1]
example : weyldim.read [1, 1, 0] := readAll [1, 1, 0]

example : weyldim.read [1, 1, 1, 0] := by apply readAll

/-! The coherence face: the span count one off the true count
refuses the product identity, at the shape whose unit gap
product sits off one.  The kernel twins sit at the widths whose
span producer the module budget admits; the four-place face is
`readAll`'s instance above, the display whole through the
theorem route. -/

example : ¬ (((blockcount.blockSpan ([1, 1, 0] : Shape)).length + 1)
      * gapProd (display (List.replicate 3 0))
    = gapProd (display ([1, 1, 0] : Shape))) := by decide +kernel

/-! The member tier at `B_2`: the positive list's gaps against `ρ`
and against `λ+ρ` at the first fundamental's top content, the two
graded folds at two-member data, the gap product against its
collected form at the shared unit-gap power, the assembly instance
at the walk tier's own orbit data, and the multiplicity fold's
Horner read at the natural one. -/

open gentable sertables assembly

private def wTwo : List (List BPair × Bool) :=
  [([BPair.ofNat 1, BPair.ofNat 1], false),
   ([(BPair.ofNat 1).swap, BPair.ofNat 3], true)]

private def mTwo : List (List BPair) :=
  [[BPair.ofNat 1, BPair.unit],
   [(BPair.ofNat 1).swap, BPair.ofNat 2]]

example : (List.range tB2.posFolds.length).map
    (gapsAt tB2 fundB2 (rhoV tB2)) = [2, 4, 3, 1] := by decide +kernel

example : (List.range tB2.posFolds.length).map
    (gapsAt tB2 fundB2 (lamrho tB2 lamB2)) = [4, 6, 5, 1] := by decide +kernel

example : poly.oneValue
    (pfold fundB2 (rhoV tB2) (dotB fundB2 (rhoV tB2) (rhoV tB2)) wTwo)
    (poly.add (poly.smono false 10) (poly.smono true 8)) := by decide +kernel

example : poly.oneValue
    (lfold fundB2 (rhoV tB2) (dotB fundB2 lamB2 (rhoV tB2)) mTwo)
    (poly.add (poly.smono false 6) (poly.smono false 4)) := by decide +kernel

example : poly.oneValue (prodPos tB2 fundB2 (rhoV tB2))
    (poly.mul (poly.powOf (poly.tpair 1) 4)
      (ground.famFold poly.mul poly.one
        (fun j => poly.gword (gapsAt tB2 fundB2 (rhoV tB2) j))
        (List.range 4))) := by decide +kernel

example : poly.oneValue (prodPos tB2 fundB2 (rhoV tB2))
    (pfold fundB2 (rhoV tB2)
      (dotB fundB2 (rhoV tB2) (rhoV tB2)) wB2) :=
  prodPos_pfold tB2 fundB2 wB2 witsB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (rhoV tB2) (by decide +kernel)

example : (poly.eval (lfold fundB2 (rhoV tB2)
    (dotB fundB2 lamB2 (rhoV tB2)) mTwo) (BPair.ofNat 1)).oneValue
    (BPair.ofNat mTwo.length) := by decide +kernel

/-! The member battery tier at `B_2`'s first fundamental: the top
content `λ`, `thm:memberchar`'s five-key multiplicity family at its
dominance witnesses, and the shifted alternant — the free
eight-member orbit of `λ+ρ` at its parities and witnesses — the
fixtures `ChecksMemberchar`'s own spellings. -/

open memberchar

/-! The two degree maps at the exchange: the shifted orbit's margins
against `ρ` at the `λ+ρ`-square shift, and the `ρ`-orbit's margins
against `λ+ρ` at the crossed shift — one multiset in two orders,
the exchange's own face — with the crossed count clauses `hexch1`
and `hexch2` beside them, each occupied degree pair at one count in
both maps. -/

example : weyldim.dmap fundB2
    (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpB2
  = [(16, false), (12, true), (15, true), (7, false),
     (9, false), (1, true), (4, true), (0, false)] := by decide +kernel

example : weyldim.dmap fundB2
    (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
    (lamrho tB2 lamB2) wB2
  = [(16, false), (12, true), (15, true), (7, false),
     (4, true), (0, false), (1, true), (9, false)] := by decide +kernel

example : ∀ p ∈ weyldim.dmap fundB2
      (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpB2,
    ground.countOf p (weyldim.dmap fundB2
        (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpB2)
      = ground.countOf p (weyldim.dmap fundB2
          (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
          (lamrho tB2 lamB2) wB2) := by decide +kernel

example : ∀ p ∈ weyldim.dmap fundB2
      (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
      (lamrho tB2 lamB2) wB2,
    ground.countOf p (weyldim.dmap fundB2
        (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpB2)
      = ground.countOf p (weyldim.dmap fundB2
          (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
          (lamrho tB2 lamB2) wB2) := by decide +kernel

/-! The two gap products at the conclusion's own spelling — the
`ρ`-product and the `λ+ρ`-product over the positive list — and the
crown applied whole: `memberRead` by the theorem route at the
stated data, every binder at kernel `decide`, with the display's
computed twin beside it, the member count against the `ρ`-product
the `λ+ρ`-product. -/

example : ground.famFold Nat.mul 1
    (fun j => BPair.marginN
      (dotB fundB2 (posCorootV tB2 j) (rhoV tB2)))
    (List.range tB2.posFolds.length) = 24 := by decide +kernel

example : ground.famFold Nat.mul 1
    (fun j => BPair.marginN
      (dotB fundB2 (posCorootV tB2 j) (lamrho tB2 lamB2)))
    (List.range tB2.posFolds.length) = 120 := by decide +kernel

example : mB2.length * ground.famFold Nat.mul 1
      (fun j => BPair.marginN
        (dotB fundB2 (posCorootV tB2 j) (rhoV tB2)))
      (List.range tB2.posFolds.length)
    = ground.famFold Nat.mul 1
      (fun j => BPair.marginN
        (dotB fundB2 (posCorootV tB2 j) (lamrho tB2 lamB2)))
      (List.range tB2.posFolds.length) :=
  weyldim.memberRead tB2 fundB2 wB2 witsB2 mB2 mwitsB2 lamB2
    wpB2 wpwitsB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : mB2.length * ground.famFold Nat.mul 1
      (fun j => BPair.marginN
        (dotB fundB2 (posCorootV tB2 j) (rhoV tB2)))
      (List.range tB2.posFolds.length)
    = ground.famFold Nat.mul 1
      (fun j => BPair.marginN
        (dotB fundB2 (posCorootV tB2 j) (lamrho tB2 lamB2)))
      (List.range tB2.posFolds.length) := by decide +kernel

/-! The comparison at the same data: every positive member's gap at
`λ+ρ` at or beyond its gap at `ρ`, by the theorem route with the
computed twin beside it. -/

example : ∀ j, j < tB2.posFolds.length →
    BPair.marginN (dotB fundB2 (posCorootV tB2 j) (rhoV tB2))
      ≤ BPair.marginN
          (dotB fundB2 (posCorootV tB2 j) (lamrho tB2 lamB2)) :=
  weyldim.memberGap_le tB2 fundB2 (by decide +kernel) (by decide +kernel) lamB2
    (by decide +kernel)

example : ∀ j, j < tB2.posFolds.length →
    BPair.marginN (dotB fundB2 (posCorootV tB2 j) (rhoV tB2))
      ≤ BPair.marginN
          (dotB fundB2 (posCorootV tB2 j) (lamrho tB2 lamB2)) := by
  decide +kernel

/-! The forge tier, and the binder classification of `memberRead`'s
twenty-eight reads at this data.

Twenty-four are inherited — `identityRead`'s own list — with their
refusals the committed batteries of their tiers: the nine table
reads and the W-side four at `ρ`'s alternant in
`MassGapChecks/Assembly.lean`, the family five, the shifted-orbit
five and the recursion read in `MassGapChecks/Memberchar.lean`'s
conclusion-tier forges; they are cited, not re-forged.  One of
them, `htopL`, reads the one field the crown's conclusion binds
beyond the table and the top content — the family at its length —
so the display's own refusal lands there: at the doubled family the
member count doubles while the two gap products stand, the display
refusing beside `htopL`'s committed refusal with every other family
read surviving (`ChecksMemberchar`'s `mDblTop` pins).

`hexch1`/`hexch2` are load-bearing at the derivation, the crossed
count transfer's own face; the conclusion binds no field of the
shifted orbit, so their refusal is read-level, and it ISOLATES at
the balanced padding below: the `ρ`-orbit adjoined at both parities
extends the shifted orbit with shape, closure, top, dominance and
regularity all surviving — a balanced extra orbit is invisible to
every co-read and to the principal fold itself, the fold's
invariance pinned beside the refusal — while both crossed clauses
part.  The doubled orbit's face beside it parts the clauses
entangled with `htop'` per the `hsym` precedent
(`ChecksMemberchar`'s `wpDbl` pins the surviving co-reads).

`hnnW`/`hnnL` are load-bearing at the derivation — the degree
margins' additivity (`BPair.marginN_add`) reads each shifted dot at
or beyond the sum's unit — and the bounded attempts below land
their refusals entangled, the classification committed in place of
an isolation no genuine-shaped data admits.  The deep doubled orbit
adjoined to `ρ`'s parts the `W`-side read at its three deep members
while shape, closure, top and the recursion survive, but the
dominance witnesses die with it — the witness fold to `ρ` caps
every member's depth at `−ρ`, so the read is implied at
genuine-shaped data.  The deep member adjoined to the family parts
the `L`-side read while shape, support, top and the recursion
survive, but the reflection invariance dies with it — a sym-closed
family's deep member carries its dominant partner beyond the top,
where the support witness dies, so the invariance and the support
jointly cap the family's depth at the top's own negative.  No
refusal is faked.

`memberGap_le`'s three: `hshape`/`hgram` the inherited table pair,
and `hlam` load-bearing at its conclusion — at `−ρ` the shifted key
is the unit vector, every gap nought, and the comparison refuses
beside the dominance read's own refusal. -/

/-! The doubled shifted orbit: both crossed clauses part at the
doubled counts, the refusal entangled with the top count's
(`ChecksMemberchar`'s `wpDbl` pins the surviving co-reads). -/

private def wpDbl : List (List BPair × Bool) := wpB2 ++ wpB2

example : ¬ ∀ p ∈ weyldim.dmap fundB2
      (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpDbl,
    ground.countOf p (weyldim.dmap fundB2
        (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpDbl)
      = ground.countOf p (weyldim.dmap fundB2
          (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
          (lamrho tB2 lamB2) wB2) := by decide +kernel

example : ¬ ∀ p ∈ weyldim.dmap fundB2
      (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
      (lamrho tB2 lamB2) wB2,
    ground.countOf p (weyldim.dmap fundB2
        (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpDbl)
      = ground.countOf p (weyldim.dmap fundB2
          (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
          (lamrho tB2 lamB2) wB2) := by decide +kernel

/-! The balanced padding: the `ρ`-orbit adjoined at both parities.
Every co-read survives — the padding is balanced at every key — and
the principal fold reads one value with the unpadded orbit's, while
both crossed clauses part: the exchange read's isolating face. -/

private def wpPad : List (List BPair × Bool) :=
  wpB2 ++ (wB2 ++ wB2.map (fun vp => (vp.1, !vp.2)))

private def wpPadWits : List (List Nat) :=
  wpwitsB2 ++ witsB2.map (fun w => w.map (fun c => c + 1))
    ++ witsB2.map (fun w => w.map (fun c => c + 1))

example : wShapeRead tB2 wpPad := by decide +kernel
example : wCloseRead tB2 wpPad := by decide +kernel
example : wTopAt wpPad (lamrho tB2 lamB2) := by decide +kernel
example : wDomAt tB2 wpPad wpPadWits (lamrho tB2 lamB2) := by decide +kernel
example : wRegRead tB2 wpPad (lamrho tB2 lamB2) := by decide +kernel

example : ¬ ∀ p ∈ weyldim.dmap fundB2
      (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpPad,
    ground.countOf p (weyldim.dmap fundB2
        (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpPad)
      = ground.countOf p (weyldim.dmap fundB2
          (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
          (lamrho tB2 lamB2) wB2) := by decide +kernel

example : ¬ ∀ p ∈ weyldim.dmap fundB2
      (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
      (lamrho tB2 lamB2) wB2,
    ground.countOf p (weyldim.dmap fundB2
        (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) (rhoV tB2) wpPad)
      = ground.countOf p (weyldim.dmap fundB2
          (dotB fundB2 (rhoV tB2) (lamrho tB2 lamB2))
          (lamrho tB2 lamB2) wB2) := by decide +kernel

example : poly.oneValue
    (pfold fundB2 (rhoV tB2)
      (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) wpPad)
    (pfold fundB2 (rhoV tB2)
      (dotB fundB2 (lamrho tB2 lamB2) (rhoV tB2)) wpB2) := by decide +kernel

/-! The doubled multiplicity family: the crown's display refuses at
the doubled member count — the one conclusion-breaking forge, the
family's length the field the display binds — beside `htopL`'s
committed refusal. -/

private def mDbl : List (List BPair) := mB2 ++ mB2

example : ¬ (mDbl.length * ground.famFold Nat.mul 1
      (fun j => BPair.marginN
        (dotB fundB2 (posCorootV tB2 j) (rhoV tB2)))
      (List.range tB2.posFolds.length)
    = ground.famFold Nat.mul 1
      (fun j => BPair.marginN
        (dotB fundB2 (posCorootV tB2 j) (lamrho tB2 lamB2)))
      (List.range tB2.posFolds.length)) := by decide +kernel

/-! The `hnnW` attempt: the orbit of `2ρ` — each key of `ρ`'s orbit
scaled by two and normed, at `ρ`'s parities — adjoined whole.
Shape, closure, the top and the recursion survive; the dominance
witnesses refuse at every stated extension (a deep member holds no
natural fold to `ρ`), and the `W`-side nonneg read parts at the
three deep members. -/

private def wDeep : List (List BPair × Bool) :=
  wB2 ++ wB2.map (fun vp =>
    ((vp.1.map (BPair.mul (BPair.ofNat 2))).map BPair.norm, vp.2))

example : wShapeRead tB2 wDeep := by decide +kernel
example : wCloseRead tB2 wDeep := by decide +kernel
example : wTopRead tB2 wDeep := by decide +kernel

-- The recursion read survives the deep padding — the attempt's
-- refusal does not entangle with `hrec`.
example : recRead tB2 fundB2 wDeep mB2 lamB2 := by decide +kernel
example : ¬ wDomRead tB2 wDeep (witsB2 ++ witsB2) := by decide +kernel
example : ¬ ∀ vp ∈ wDeep, BPair.unit ≤ BPair.add
    (dotB fundB2 (rhoV tB2) (rhoV tB2))
    (dotB fundB2 vp.1 (rhoV tB2)) := by decide +kernel

/-! The `hnnL` attempt: `−2ρ`, a deep member below the top, adjoined
to the family at its own natural witness.  Shape, support, the top
and the recursion survive; the reflection invariance refuses (the
member's orbit partner sits beyond the top), and the `L`-side
nonneg read parts at the deep member. -/

private def deepNu : List BPair :=
  poly.pnorm (elim.vecScale ((BPair.ofNat 2).swap) (rhoV tB2))

private def mDeep : List (List BPair) := mB2 ++ [deepNu]

private def mDeepWits : List (List Nat) := mwitsB2 ++ [[4, 5]]

example : mShapeRead tB2 mDeep := by decide +kernel
example : supportRead tB2 mDeep mDeepWits lamB2 := by decide +kernel
example : topRead mDeep lamB2 := by decide +kernel
example : recRead tB2 fundB2 wB2 mDeep lamB2 := by decide +kernel
example : ¬ symRead tB2 mDeep := by decide +kernel
example : ¬ ∀ nu ∈ mDeep, BPair.unit ≤ BPair.add
    (dotB fundB2 lamB2 (rhoV tB2))
    (dotB fundB2 nu (rhoV tB2)) := by decide +kernel

/-! The `hlam` forge at `memberGap_le`: the top content forged to
`−ρ` — the shifted key the unit vector, every gap nought — the
dominance read and the comparison refusing together. -/

private def lamNeg : List BPair :=
  poly.pnorm (elim.vecScale ((BPair.ofNat 1).swap) (rhoV tB2))

example : ¬ lamRead tB2 lamNeg := by decide +kernel
example : ¬ ∀ j, j < tB2.posFolds.length →
    BPair.marginN (dotB fundB2 (posCorootV tB2 j) (rhoV tB2))
      ≤ BPair.marginN
          (dotB fundB2 (posCorootV tB2 j) (lamrho tB2 lamNeg)) := by
  decide +kernel

/-! The display's run tier: the descending run at a stated floor,
the head's gap fold with the falling-product law, the run's
floor-free gap product, and the unit display as the run at floor
one. -/

example : weyldim.descRun 4 3 = [6, 5, 4] := by decide +kernel
example : weyldim.descRun 1 4 = [4, 3, 2, 1] := by decide +kernel
example : (weyldim.descRun 5 7).length = 7 := weyldim.length_descRun 5 7
example : weyldim.gapHead 9 [6, 5, 4] = 60 := by decide +kernel
example : weyldim.gapHead 9 ([6, 5] ++ [4])
    = weyldim.gapHead 9 [6, 5] * weyldim.gapHead 9 [4] :=
  weyldim.gapHead_append 9 [6, 5] [4]
example : weyldim.gapHead 7 (3 :: [2]) = (7 - 3) * weyldim.gapHead 7 [2] :=
  weyldim.gapHead_cons 7 3 [2]
example : weyldim.gapProd [6, 5, 4]
    = weyldim.gapHead 6 [5, 4] * weyldim.gapProd [5, 4] :=
  weyldim.gapProd_cons 6 [5, 4]
example : weyldim.gapHead (3 + 2 + 4) (weyldim.descRun 4 3)
    * ground.factorial 2 = ground.factorial (3 + 2) :=
  weyldim.gapHead_descRun 4 3 2
example : weyldim.gapProd (weyldim.descRun 4 5)
    = weyldim.gapProd (weyldim.descRun 9 5) :=
  weyldim.gapProd_descRun 4 9 5
example : weyldim.gapProd (weyldim.descRun 4 5) = 288 := by decide +kernel
example : weyldim.gapProd (weyldim.descRun 3 4)
    = ground.factorial 3 * weyldim.gapProd (weyldim.descRun 3 3) :=
  weyldim.gapProd_descRun_succ 3 3
example : weyldim.gapProd (weyldim.descRun 4 2 ++ [2, 1])
    = weyldim.gapProd (weyldim.descRun 4 2)
      * (weyldim.gapProd [2, 1] * weyldim.gapRun [2, 1] 4 2) :=
  weyldim.gapProd_descRun_app [2, 1] 4 2
example : weyldim.gapRun [2, 1] 4 2 = 72 := by decide +kernel
example : weyldim.descRun 4 3 = weyldim.descRun (4 + 1) 2 ++ [4] :=
  weyldim.descRun_snoc 4 2
example : List.zipWith (fun l u => l + u) (List.replicate 3 2)
    (weyldim.descRun 1 3) = weyldim.descRun 3 3 :=
  weyldim.zipWith_descRun 2 1 3
example : places.unitDisp 5 = weyldim.descRun 1 5 :=
  weyldim.unitDisp_descRun 5
example : 0 < weyldim.gapProd (places.display (List.replicate 4 0)) :=
  weyldim.gapProdU_pos ([2, 0, 1, 0] : places.Shape)

/-! The class read: the dimension is blind to the full-column
key's occupancy. -/

example : weyldim.dimOf [1, 2] = weyldim.dimOf [1, 0] := by decide +kernel
example : weyldim.dimOf [2, 1, 3] = weyldim.dimOf [2, 1, 0] := by decide +kernel
example : weyldim.dimOf [2, 1, 3] = weyldim.dimOf [2, 1, 0] :=
  weyldim.dimOf_snoc [2, 1] 3
