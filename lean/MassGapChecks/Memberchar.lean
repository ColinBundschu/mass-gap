import MassGap.Memberchar
import MassGapChecks.Sertables
/-!
The check module for `thm:memberchar`'s read layer: the reads that
determine a shifted alternant and the recursion's own display are
re-read by kernel `decide` at `B_2`.  The shifted alternant's reads
enter at the one-member graded list of `ρ` — the support at its
stated witness, the top read at `ρ`'s key, and the regular read off
it — with the closure refused there, the one member carrying no
reflection image at the flipped side, the support refused at a
forged witness, and the regular read refused at a list joined by a
strictly dominant member off the top key, whose two graded counts
part.  The multiplicity family's three reads enter at the vacant
family and at the top content's own: the reflection invariance,
refused at the single-member family holding `ρ` alone, whose
reflected keys leave the family; the support at the unit witness;
and the top count, refused at the doubled family.  The convolution
count is read at the joined key, one at the even side and none at
the odd.  The recursion's reads close the battery: the line test
true at the key one positive member beyond and false at the key
itself, the line fold and its positive-list sum at equal members,
and the recursion read whole at the top content the unit — the
trivial member's own character, whose window keys carry no further
multiplicity — with its refusal at the family holding `ρ` alone,
which no member's character reads.  The cap read enters at its
defining bound.

The theorem tier's batteries close the module: the family shape
read at its decide pins, `(XX)` applied whole by the theorem route
at the four-member family off the unit value with its not-unit
read and its computed unit twin at the unit family, the
convolution counts, and `(E)` at the trivial member's character
with the window membership a constructor term.

The conclusion tier's batteries close at `B_2`'s first fundamental,
the tree's first genuine multiplicity family: the five-key string
at its dominance witnesses, the shifted alternant the regular key's
free eight-member orbit, `identityRead` applied whole at three
keys — the top, an interior key the convolution occupies at both
sides, and a key off the rank's frame — with `(E)` and `(XX)` at
the second window key, both factors off the unit, and one forge per
load-bearing binder, the padded alternant of the D2 refutation
among them, each breaking its own read with the balance failing at
a named key.
-/

namespace memberchar

open ground gentable sertables assembly

/-! The stated data: the one-member graded list of `ρ` at its
witness, the multiplicity families, and the two top contents — `ρ`
itself and the unit content — over the shared `B_2` data at
`MassGapChecks/Sertables.lean`. -/

private def rhoKey : List BPair := poly.pnorm (rhoV tB2)
private def rho2Key : List BPair :=
  poly.pnorm (elim.vecAdd (rhoV tB2) (rhoV tB2))

private def W0 : List (List BPair × Bool) := [(rhoKey, false)]
private def L0 : List (List BPair) := [rhoV tB2]
private def Lz : List (List BPair) := [zeroV]

/-! The shifted alternant's reads at the graded list — the support at its
stated witness, the top read at `ρ`'s key, and the regular read off
it — with the closure refused there, one member carrying no
reflection image, and the regular read refused at the list joined
by a strictly dominant member off the top key. -/

theorem pin1 : ¬ wCloseRead tB2 W0 := by decide +kernel
theorem pin2 : wDomAt tB2 W0 [[0, 0]] rhoKey := by decide +kernel
theorem pin3 : wTopAt W0 rhoKey := by decide +kernel
theorem pin4 : wRegRead tB2 W0 rhoKey := by decide +kernel

theorem pin5 : ¬ wRegRead tB2 (W0 ++ [(rho2Key, false)]) rhoKey := by decide +kernel

/-! The support read's own refusal at a forged witness: the unit
fold carries the member's key to `ρ` alone. -/

theorem pin6 : ¬ wDomAt tB2 W0 [[1, 0]] rhoKey := by decide +kernel

/-! The multiplicity family's three reads.  The reflection
invariance holds at the vacant family and refuses at the family
holding `ρ` alone, whose reflected keys leave it; the support read
carries the unit content to itself at the unit witness; and the top
count is one at the single-member family, refused at the doubled
one. -/

theorem pin7 : symRead tB2 ([] : List (List BPair)) := by decide +kernel
theorem pin8 : ¬ symRead tB2 L0 := by decide +kernel
theorem pin9 : symRead tB2 Lz := by decide +kernel

theorem pin10 : supportRead tB2 Lz [[0, 0]] zeroV := by decide +kernel
theorem pin11 : ¬ supportRead tB2 Lz [[1, 0]] zeroV := by decide +kernel

theorem pin12 : topRead L0 (rhoV tB2) := by decide +kernel
theorem pin13 : ¬ topRead (L0 ++ L0) (rhoV tB2) := by decide +kernel

theorem pin14 : lamRead tB2 (rhoV tB2) := by decide +kernel
theorem pin15 : lamRead tB2 zeroV := by decide +kernel

/-! The convolution count at the joined key: the graded list's one
member joins the family's one member at the even side. -/

theorem pin16 : convCount W0 L0 rho2Key false = 1 := by decide +kernel
theorem pin17 : convCount W0 L0 rho2Key true = 0 := by decide +kernel
theorem pin18 : convCount W0 L0 rhoKey false = 0 := by decide +kernel

/-! The line test at a positive member: true at the key one coroot
beyond, false at the key itself, with the line fold and the
positive list's sum at equal members where the family holds the
line's own key alone. -/

theorem pin19 : lineAt tB2 fundB2 (rhoV tB2)
    (poly.pnorm (elim.vecAdd (rhoV tB2) (posCorootV tB2 0))) 0
      = true := by decide +kernel
theorem pin20 : lineAt tB2 fundB2 (rhoV tB2) (rhoV tB2) 0 = false := by decide +kernel

theorem pin21 : BPair.oneValue (gAt tB2 fundB2 L0 (rhoV tB2) 0)
    BPair.unit := by decide +kernel
theorem pin22 : BPair.oneValue (gSum tB2 fundB2 L0 (rhoV tB2))
    BPair.unit := by decide +kernel

/-! The natural fold at the unit witness, the seed's own read. -/

theorem pin23 : poly.oneValue (cartanFold tB2 [0, 0])
    [BPair.unit, BPair.unit] := by decide +kernel

/-! The dominant window at the unit content, and the recursion read
whole there — the trivial member's character, one key carrying the
multiplicity and the window's further keys carrying none — with the
refusal at the family holding `ρ` alone, which no member's
character reads. -/

theorem pin24 : (domWindow tB2 fundB2 zeroV).length = 1 := by decide +kernel
theorem pin25 : recRead tB2 fundB2 W0 Lz zeroV := by decide +kernel
theorem pin26 : ¬ recRead tB2 fundB2 W0 L0 (rhoV tB2) := by decide +kernel

/-! The cap read at its defining bound, the count entering the
carrier at or below the pair. -/

theorem pin27 : BPair.capN (BPair.ofNat 5) = 6 := by decide +kernel
theorem pin28 : BPair.capN BPair.unit = 1 := by decide +kernel
theorem pin29 : 5 ≤ BPair.capN (BPair.ofNat 5) :=
  BPair.ofNat_le_capN (by decide +kernel)

/-! The line test's key read at its own conclusion: the test's
truth is the natural multiple within the two dots' gap at the
root's positive dot. -/

theorem pin30 : ∃ l, l < BPair.capN (BPair.add
        (dotB fundB2 (poly.pnorm (elim.vecAdd (rhoV tB2)
          (posCorootV tB2 0))) (rhoV tB2))
        ((dotB fundB2 (rhoV tB2) (rhoV tB2)).swap))
      / BPair.marginN (dotB fundB2 (posCorootV tB2 0) (rhoV tB2))
    ∧ poly.pnorm (elim.vecAdd (rhoV tB2)
        (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV tB2 0)))
      = poly.pnorm (elim.vecAdd (rhoV tB2) (posCorootV tB2 0)) :=
  (lineAt_iff tB2 fundB2 (rhoV tB2)
    (poly.pnorm (elim.vecAdd (rhoV tB2) (posCorootV tB2 0))) 0).mp
    (by decide +kernel)

/-! The height calculus at `B_2`: the table's lengths occupied and
the Gram's action on `ρ` at or beyond the sum's unit, both read
through their general theorems at the stated fundamental data, with
the computed values beside them. -/

theorem pin31 : 0 < ground.getAt 0 tB2.lenNums 0 :=
  lenNums_pos tB2 fundB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem pin32 : 0 < ground.getAt 0 tB2.lenNums 1 :=
  lenNums_pos tB2 fundB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem pin33 : ground.getAt 0 tB2.lenNums 0 = 2 := by decide +kernel
theorem pin34 : ground.getAt 0 tB2.lenNums 1 = 1 := by decide +kernel

theorem pin35 : BPair.unit ≤ ground.getAt BPair.unit
    (elim.matVec fundB2.gram (rhoV tB2)) 0 :=
  gramRho_nonneg tB2 fundB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem pin36 : BPair.unit ≤ ground.getAt BPair.unit
    (elim.matVec fundB2.gram (rhoV tB2)) 1 :=
  gramRho_nonneg tB2 fundB2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The telescope at its own conclusion: the line's fold at the key
one step below `ρ` reads the fold at `ρ` — where the family's own
member sits — joined to the step's doubled dot at its count. -/

private def nu1 : List BPair :=
  poly.pnorm (elim.vecAdd (rhoV tB2) (poly.neg (posCorootV tB2 0)))

theorem pin37 : BPair.oneValue (gAt tB2 fundB2 L0 nu1 0)
    (BPair.add
      (gAt tB2 fundB2 L0
        (poly.pnorm (elim.vecAdd nu1 (posCorootV tB2 0))) 0)
      (BPair.mul
        (BPair.add
          (dotB fundB2 (poly.pnorm (elim.vecAdd nu1
            (posCorootV tB2 0))) (posCorootV tB2 0))
          (dotB fundB2 (poly.pnorm (elim.vecAdd nu1
            (posCorootV tB2 0))) (posCorootV tB2 0)))
        (BPair.ofNat (ground.countOf
          (poly.pnorm (elim.vecAdd nu1 (posCorootV tB2 0))) L0)))) :=
  gAt_tel tB2 fundB2 (by decide +kernel) (by decide +kernel) L0 nu1 (by decide +kernel)
    (by decide +kernel)

theorem pin38 : ground.countOf
    (poly.pnorm (elim.vecAdd nu1 (posCorootV tB2 0))) L0 = 1 := by
  decide +kernel
theorem pin39 : ¬ BPair.oneValue (gAt tB2 fundB2 L0 nu1 0) BPair.unit := by
  decide +kernel
theorem pin40 : lineAt tB2 fundB2 nu1 (rhoV tB2) 0 = true := by decide +kernel

/-! The theorem tier's application pins at `B_2`: the shifted
alternant's own graded list with its witnesses, the multiplicity
family at the unit content, and the dominant window's one key.  The
alternant-weighted line folds `(XX)` and the eigen identity `(E)`
enter through their general theorems at the stated data, with the
family's shape read and the convolution's counts beside them. -/

theorem pin41 : mShapeRead tB2 Lz := by decide +kernel
theorem pin42 : mShapeRead tB2 L0 := by decide +kernel

/-! `(XX)` at the stated data: the line folds' signed collection over
the alternant reads the moved key's dot against the fold key joined
to `ρ`'s own, at the family's count — applied at an occupied
four-member family off the unit value, the not-unit read pinned
beside it, and at the unit content's family with its computed unit
twin. -/

private def L4 : List (List BPair) :=
  [rhoV tB2, zeroV, poly.pnorm (eKey tB2 [0]),
   poly.pnorm (eKey tB2 [1])]

theorem pin43 : mShapeRead tB2 L4 := by decide +kernel

theorem pin44 : BPair.oneValue
    (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (gSum tB2 fundB2 L4
          (poly.pnorm (elim.vecAdd zeroV (poly.neg vp.1))))) wB2)
    (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (((dotB fundB2
              (poly.pnorm (elim.vecAdd zeroV (poly.neg vp.1))) vp.1
            + (dotB fundB2
              (poly.pnorm (elim.vecAdd zeroV (poly.neg vp.1)))
              (rhoV tB2)).swap)
          + (dotB fundB2
              (poly.pnorm (elim.vecAdd zeroV (poly.neg vp.1))) vp.1
            + (dotB fundB2
              (poly.pnorm (elim.vecAdd zeroV (poly.neg vp.1)))
              (rhoV tB2)).swap))
          * BPair.ofNat (ground.countOf
              (poly.pnorm (elim.vecAdd zeroV (poly.neg vp.1)))
              L4))) wB2) :=
  convDots tB2 fundB2 wB2 witsB2 L4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) zeroV (by decide +kernel)

theorem pin45 : ¬ (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (gSum tB2 fundB2 L4
          (poly.pnorm (elim.vecAdd zeroV (poly.neg vp.1))))) wB2).oneValue
    BPair.unit := by decide +kernel

theorem pin46 : BPair.oneValue
    (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (gSum tB2 fundB2 Lz
          (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1))))) wB2)
    (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (((dotB fundB2
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1))) vp.1
            + (dotB fundB2
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1)))
              (rhoV tB2)).swap)
          + (dotB fundB2
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1))) vp.1
            + (dotB fundB2
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1)))
              (rhoV tB2)).swap))
          * BPair.ofNat (ground.countOf
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1))) Lz))) wB2) :=
  convDots tB2 fundB2 wB2 witsB2 Lz (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rhoKey (by decide +kernel)

theorem pin47 : BPair.oneValue
    (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (gSum tB2 fundB2 Lz
          (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1))))) wB2)
    BPair.unit := by decide +kernel

/-! `(E)` at the trivial member's character: the dominant window's
one key carries the eigen gap against the convolution's count pair
at the sum's unit, the window membership read off the computed
window. -/

theorem pin48 : convCount wB2 Lz rhoKey false = 1 := by decide +kernel
theorem pin49 : convCount wB2 Lz rhoKey true = 0 := by decide +kernel

theorem pin50 : BPair.oneValue
    ((dotB fundB2 (poly.pnorm (elim.vecAdd zeroV (rhoV tB2)))
          (poly.pnorm (elim.vecAdd zeroV (rhoV tB2)))
        + (dotB fundB2 rhoKey rhoKey).swap)
      * BPair.ofCounts (convCount wB2 Lz rhoKey false)
          (convCount wB2 Lz rhoKey true))
    BPair.unit :=
  eigenAt tB2 fundB2 wB2 witsB2 Lz zeroV (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rhoKey (List.Mem.head _)

/-! The conclusion tier's batteries at `B_2`'s first fundamental —
the vector block, the tree's first genuine multiplicity family.
The top content is the one-hot at the first key, its family the
five keys of the string (the top, its three reflection images, and
the middle), each once at its dominance witness, and the shifted
alternant is the free eight-member orbit of `λ + ρ` at its
parities.  `identityRead` enters whole at that data — at the top
key, at an interior key the convolution occupies at both sides, and
at a key off the rank's frame — with `eigenAt` at the second window
key, where the gap factor sits off the unit, and `convDots` at the
same key with its own fold off the unit.

The binder classification of `identityRead`'s twenty-four reads at
this data.  Seven are load-bearing at the conclusion, each with a
committed forge below whose surviving co-reads are pinned green
beside the refusal and whose balance fails at a named key:
`hsym` (its forge entangled with the recursion read, the
entanglement pinned rather than claimed isolated), `htopL` (the
doubled family, the recursion read surviving by its own count
homogeneity), `hrec`, `hsupp` (the orbit padding), `htop'` (the
doubled data), `hclose'` (the flipped even member), and `hreg'` —
the last the recorded refutation that forced the fourth read, the
padded list keeping closure, support and top while the regular
read parts at the padding's own dominant key.  `hdom'` is
load-bearing at the derivation — the walk's fuel cap, the second
determining read — with its refusal read-level: a padding off the
support sits unbalanced or cancels in the balance, so the
conclusion holds at every balanced padding and the read's own
refusal is the committed one.  Three are the frame: `hwsh'` and
`hmsh` the carrier convention (every key at the rank's order,
normed), `hwsh'` consumed by the off-frame vanishing at the third
application key, and `hlam` the top content's own frame.
Thirteen are inherited: the nine table reads (`fundShape`,
`gramRead`, `gramSymRead`, `simplePosRead`, `reflSquareRead`,
`permSquareRead`, `permImageRead`, `rhoDotRead`, `reflFormRead`)
and the W-side four at `ρ`'s own alternant (`wShapeRead`,
`wCloseRead`, `wDomRead`, `wTopRead`), whose refusals are the walk
tier's committed batteries in `MassGapChecks/Assembly.lean` — the
forged witness at the top member, the adjoined reflection closure
of a regular dominant key, the flipped side, the doubled list, and
the forged side at the top member. -/

/-! The top content and its multiplicity family: the first
fundamental's coroot list, the string's five keys, and the
dominance witnesses carrying each member back to the top at a
natural simple fold. -/

theorem pin51 : lamRead tB2 lamB2 := by decide +kernel
theorem pin52 : mShapeRead tB2 mB2 := by decide +kernel
theorem pin53 : symRead tB2 mB2 := by decide +kernel
theorem pin54 : topRead mB2 lamB2 := by decide +kernel
theorem pin55 : supportRead tB2 mB2 mwitsB2 lamB2 := by decide +kernel

/-! The shifted alternant at the top key `λ + ρ`: the regular key's
free orbit, eight members at their parities, with the witness folds
carrying each back to the top.  The four reads that determine it
enter at their own pins. -/

private def topB2 : List BPair :=
  poly.pnorm (elim.vecAdd lamB2 (rhoV tB2))

theorem pin56 : wShapeRead tB2 wpB2 := by decide +kernel
theorem pin57 : wCloseRead tB2 wpB2 := by decide +kernel
theorem pin58 : wDomAt tB2 wpB2 wpwitsB2 topB2 := by decide +kernel
theorem pin59 : wTopAt wpB2 topB2 := by decide +kernel
theorem pin60 : wRegRead tB2 wpB2 topB2 := by decide +kernel

/-! The recursion read at the genuine family — the dominant window
is the top key and `ρ`, the display holding against all eight
alternant members at both.  The pin is this battery's
heaviest and the one hypothesis the three conclusion applications
and the eigen pin each carry, so it is named once and consumed by
term. -/

private theorem hrecB2 : recRead tB2 fundB2 wB2 mB2 lamB2 := by decide +kernel

/-! `thm:memberchar` applied whole at the data: the identity's
per-key balance by the theorem route with its computed twin beside
it — at the top key, at `ρ` (an interior key the convolution
occupies at both sides while the alternant misses it), and at a key
off the rank's order, where the vacancy branch reads all four
counts at the count's unit. -/

theorem pin61 : identityAt wB2 mB2 wpB2 topB2 :=
  identityRead tB2 fundB2 wB2 witsB2 mB2 mwitsB2 lamB2 wpB2 wpwitsB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hrecB2 topB2

theorem pin62 : identityAt wB2 mB2 wpB2 topB2 := by decide +kernel

theorem pin63 : identityAt wB2 mB2 wpB2 rhoKey :=
  identityRead tB2 fundB2 wB2 witsB2 mB2 mwitsB2 lamB2 wpB2 wpwitsB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hrecB2 rhoKey

theorem pin64 : identityAt wB2 mB2 wpB2 rhoKey := by decide +kernel

theorem pin65 : convCount wB2 mB2 rhoKey false = 1 := by decide +kernel
theorem pin66 : convCount wB2 mB2 rhoKey true = 1 := by decide +kernel
theorem pin67 : wCount wpB2 rhoKey false = 0 := by decide +kernel

theorem pin68 : identityAt wB2 mB2 wpB2 [BPair.ofNat 1] :=
  identityRead tB2 fundB2 wB2 witsB2 mB2 mwitsB2 lamB2 wpB2 wpwitsB2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hrecB2 [BPair.ofNat 1]

theorem pin69 : identityAt wB2 mB2 wpB2 [BPair.ofNat 1] := by decide +kernel

/-! `(E)` at the genuine family, the second window key: the gap
factor `q₀(λ+ρ)` against `ρ`'s own square sits off the unit — the
pin discriminates the count pair, which the display forces to the
balanced pair. -/

theorem pin70 : ¬ (dotB fundB2 topB2 topB2
    + (dotB fundB2 rhoKey rhoKey).swap).oneValue BPair.unit := by decide +kernel

theorem pin71 : BPair.oneValue
    ((dotB fundB2 topB2 topB2 + (dotB fundB2 rhoKey rhoKey).swap)
      * BPair.ofCounts (convCount wB2 mB2 rhoKey false)
          (convCount wB2 mB2 rhoKey true))
    BPair.unit :=
  eigenAt tB2 fundB2 wB2 witsB2 mB2 lamB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hrecB2 rhoKey
    (List.Mem.tail _ (List.Mem.head _))

/-! `(XX)` at the same family and key: the line folds' signed
collection reads the moved keys' dots at the family's counts, its
own value off the unit. -/

theorem pin72 : BPair.oneValue
    (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (gSum tB2 fundB2 mB2
          (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1))))) wB2)
    (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (((dotB fundB2
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1))) vp.1
            + (dotB fundB2
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1)))
              (rhoV tB2)).swap)
          + (dotB fundB2
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1))) vp.1
            + (dotB fundB2
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1)))
              (rhoV tB2)).swap))
          * BPair.ofNat (ground.countOf
              (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1)))
              mB2))) wB2) :=
  convDots tB2 fundB2 wB2 witsB2 mB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) rhoKey (by decide +kernel)

theorem pin73 : ¬ (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (gSum tB2 fundB2 mB2
          (poly.pnorm (elim.vecAdd rhoKey (poly.neg vp.1))))) wB2).oneValue
    BPair.unit := by decide +kernel

/-! The refusal batteries, one forge per load-bearing binder.  The
D2-refutation forge first: the shifted alternant padded with the
full graded orbit of `ρ`, a dominant key strictly below the top.
The shape, the closure, the support at its extended witnesses and
the top read all survive the padding; the regular read parts at
`ρ`, the padding's own strictly dominant key, and the balance fails
there. -/

private def wpPad : List (List BPair × Bool) := wpB2 ++ wB2

private def wpPadWits : List (List Nat) :=
  wpwitsB2 ++ [[1, 1], [2, 1], [1, 2], [3, 2], [3, 5], [4, 5],
    [4, 4], [2, 4]]

theorem pin74 : wShapeRead tB2 wpPad := by decide +kernel
theorem pin75 : wCloseRead tB2 wpPad := by decide +kernel
theorem pin76 : wDomAt tB2 wpPad wpPadWits topB2 := by decide +kernel
theorem pin77 : wTopAt wpPad topB2 := by decide +kernel
theorem pin78 : ¬ wRegRead tB2 wpPad topB2 := by decide +kernel
theorem pin79 : ¬ identityAt wB2 mB2 wpPad rhoKey := by decide +kernel

/-! `htop'`: the top pair doubled in the shifted alternant — the
top read refuses at the count two, and the balance fails at the top
key itself. -/

private def wpDbl : List (List BPair × Bool) := wpB2 ++ wpB2

private def wpDblWits : List (List Nat) := wpwitsB2 ++ wpwitsB2

theorem pin80 : wShapeRead tB2 wpDbl := by decide +kernel
theorem pin81 : wCloseRead tB2 wpDbl := by decide +kernel
theorem pin82 : wDomAt tB2 wpDbl wpDblWits topB2 := by decide +kernel
theorem pin83 : wRegRead tB2 wpDbl topB2 := by decide +kernel
theorem pin84 : ¬ wTopAt wpDbl topB2 := by decide +kernel
theorem pin85 : ¬ identityAt wB2 mB2 wpDbl topB2 := by decide +kernel

/-! `htopL`: the top content doubled in the multiplicity family at
its own unit witness — the support read stays green, the top count
refuses, and the balance fails at the top key. -/

private def mDblTop : List (List BPair) := mB2 ++ mB2

private def mDblTopWits : List (List Nat) := mwitsB2 ++ mwitsB2

theorem pin86 : mShapeRead tB2 mDblTop := by decide +kernel
theorem pin87 : symRead tB2 mDblTop := by decide +kernel
theorem pin88 : supportRead tB2 mDblTop mDblTopWits lamB2 := by decide +kernel
theorem pin89 : recRead tB2 fundB2 wB2 mDblTop lamB2 := by decide +kernel
theorem pin90 : ¬ topRead mDblTop lamB2 := by decide +kernel
theorem pin91 : ¬ identityAt wB2 mDblTop wpB2 topB2 := by decide +kernel

/-! `hsym`: one non-dominant member dropped from the family — the
shape read stays green, the reflection invariance refuses at the
top's own image, and the balance fails at that image's key.  The
recursion read refuses with it, its own pin beside the isolation:
at genuine data every symmetry forge tried moves the recursion as
well, so the read's refusal is committed entangled rather than
claimed isolated. -/

private def mDrop : List (List BPair) :=
  [[BPair.ofNat 1, BPair.unit],
   [BPair.unit, BPair.unit],
   [BPair.ofNat 1, (BPair.ofNat 2).swap],
   [(BPair.ofNat 1).swap, BPair.unit]]

theorem pin92 : mShapeRead tB2 mDrop := by decide +kernel
theorem pin93 : ¬ symRead tB2 mDrop := by decide +kernel
theorem pin94 : ¬ recRead tB2 fundB2 wB2 mDrop lamB2 := by decide +kernel
theorem pin95 : ¬ identityAt wB2 mDrop wpB2 [BPair.unit, BPair.ofNat 3] := by
  decide +kernel

/-! `hrec`: the middle weight's multiplicity forged to two at its
own witness — every other family read stays green, the recursion
read refuses, and the balance fails at `ρ`, the window key the
forged member reaches. -/

private def mDblMid : List (List BPair) :=
  mB2 ++ [[BPair.unit, BPair.unit]]

private def mDblMidWits : List (List Nat) := mwitsB2 ++ [[1, 1]]

theorem pin96 : mShapeRead tB2 mDblMid := by decide +kernel
theorem pin97 : symRead tB2 mDblMid := by decide +kernel
theorem pin98 : supportRead tB2 mDblMid mDblMidWits lamB2 := by decide +kernel
theorem pin99 : topRead mDblMid lamB2 := by decide +kernel
theorem pin100 : ¬ recRead tB2 fundB2 wB2 mDblMid lamB2 := by decide +kernel
theorem pin101 : ¬ identityAt wB2 mDblMid wpB2 rhoKey := by decide +kernel

/-! `hdom'`: the top member's witness fold forged off the unit —
the support read at the shifted key refuses alone.  The read is
the walk's own fuel cap, the tex's second determining read for the
alternant's data; a padding the support cannot reach either sits
unbalanced (the regular read's own refusal) or balanced, where the
balance display absorbs it, so the committed refusal is the
read's own and the derivation consumes the read at the cap. -/

private def wpwitsBad : List (List Nat) :=
  [[1, 0], [2, 0], [0, 1], [2, 5], [3, 1], [5, 5], [3, 6], [5, 6]]

theorem pin102 : ¬ wDomAt tB2 wpB2 wpwitsBad topB2 := by decide +kernel

/-! `hclose'`: the side of the one non-dominant even member flipped
— shape, support, top and regular stay green, the closure refuses
at the flipped member, and the balance fails at exactly its key. -/

private def wpFlip : List (List BPair × Bool) :=
  [([(BPair.ofNat 2), (BPair.ofNat 1)], false),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 5)], true),
   ([(BPair.ofNat 3), (BPair.ofNat 1).swap], false),
   ([(BPair.ofNat 3), (BPair.ofNat 5).swap], false),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 5)], false),
   ([(BPair.ofNat 3).swap, (BPair.ofNat 1)], true),
   ([(BPair.ofNat 2), (BPair.ofNat 5).swap], true),
   ([(BPair.ofNat 2).swap, (BPair.ofNat 1).swap], false)]

theorem pin103 : wShapeRead tB2 wpFlip := by decide +kernel
theorem pin104 : wDomAt tB2 wpFlip wpwitsB2 topB2 := by decide +kernel
theorem pin105 : wTopAt wpFlip topB2 := by decide +kernel
theorem pin106 : wRegRead tB2 wpFlip topB2 := by decide +kernel
theorem pin107 : ¬ wCloseRead tB2 wpFlip := by decide +kernel
theorem pin108 : ¬ identityAt wB2 mB2 wpFlip
    [(BPair.ofNat 3), (BPair.ofNat 1).swap] := by decide +kernel

/-! `hsupp`: the family padded with the shifted key's whole orbit —
shape, invariance, top and recursion stay green, the support read
refuses (the padded keys hold no natural fold to the top), and the
balance fails at the shifted key's own `ρ`-translate. -/

private def mHi : List (List BPair) :=
  mB2 ++ (wpB2.map (fun vp => vp.1))

private def mHiWits : List (List Nat) :=
  mwitsB2 ++ [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0],
    [0, 0], [0, 0]]

theorem pin109 : mShapeRead tB2 mHi := by decide +kernel
theorem pin110 : symRead tB2 mHi := by decide +kernel
theorem pin111 : topRead mHi lamB2 := by decide +kernel
theorem pin112 : recRead tB2 fundB2 wB2 mHi lamB2 := by decide +kernel
theorem pin113 : ¬ supportRead tB2 mHi mHiWits lamB2 := by decide +kernel
theorem pin114 : ¬ identityAt wB2 mHi wpB2
    [(BPair.ofNat 3), (BPair.ofNat 2)] := by decide +kernel

/-! A repeated G2 root contributes once per family occurrence
and once per string index. The exact height cap is one. -/

private def rootG2 : List BPair := poly.pnorm (posCorootV tableG2 0)

private theorem rootG2_height : ∀ mu ∈ [rootG2, rootG2],
    dotB fundG2 mu (rhoV tableG2) ≤ BPair.ofNat 2 := by decide +kernel

theorem pin115 : (gAt tableG2 fundG2 [rootG2, rootG2] zeroV 0).oneValue (BPair.ofNat 16) := by
  have h := gAt_height tableG2 fundG2 fundShape_G2 gramSymRead_G2 rhoDotRead_G2
    (by decide +kernel : 0 < tableG2.posFolds.length) [rootG2, rootG2] zeroV rfl
    (by decide +kernel) 2 (fun mu hm => rootG2_height mu (ground.mem_of_countOf_pos _ _ hm))
  exact BPair.oneValue_trans h (by decide +kernel)

theorem pin116 : ground.famFold Nat.add 0
    (fun l => if rootG2 = poly.pnorm (elim.vecAdd zeroV
      (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV tableG2 0))) then 1 else 0)
    (List.range 1) = if lineAt tableG2 fundG2 zeroV rootG2 0 then 1 else 0 := by
  apply lineAt_count tableG2 fundG2 fundShape_G2 gramSymRead_G2 rhoDotRead_G2
    (by decide +kernel) zeroV rootG2 rfl 1
  intro l hhit
  exact lineAt_hit_bound tableG2 fundG2 fundShape_G2 rhoDotRead_G2
    (by decide +kernel) zeroV rootG2 (Nat.le_refl _) (by decide +kernel)
    2 l (by decide +kernel) hhit

/-- A cap below the first occupied step omits its contribution. -/
theorem pin117 : ¬ (gAt tableG2 fundG2 [rootG2, rootG2] zeroV 0).oneValue
    (ground.bsum (fun _ : Nat => BPair.ofNat 16) (List.range 0)) := by decide +kernel

/-- The upper-side starting-height requirement refuses the
negative root, whose step can reach the zero key at height zero. -/
theorem pin118 : ¬ BPair.unit ≤ dotB fundG2 (poly.neg rootG2) (rhoV tableG2)
    ∧ lineAt tableG2 fundG2 (poly.neg rootG2) zeroV 0 = true := by decide +kernel

/-- A zero Gram has no positive root-height read, and its line
test omits even the first root step. -/
theorem pin119 : ¬ rhoDotRead tableG2 { fundG2 with gram := List.replicate 2 zeroV }
    ∧ lineAt tableG2 { fundG2 with gram := List.replicate 2 zeroV } zeroV rootG2 0 = false := by decide +kernel

/-- The supported B2 family is capped by its top at every
occupied key, using the stored simple folds. -/
theorem pin120 (mu : List BPair) (hmu : 0 < ground.countOf mu mB2) :
    dotB fundB2 mu (rhoV tB2) ≤ dotB fundB2 lamB2 (rhoV tB2) :=
  supportRead_height tB2 fundB2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) mB2 mwitsB2 lamB2 rfl (by decide +kernel) mu hmu

/-- Reordering a family preserves the recursion, including the
multiplicity of each repeated content in its correction fold. -/
theorem pin121 (nu : List BPair) :
    (gSum tB2 fundB2 mB2.reverse nu).oneValue (gSum tB2 fundB2 mB2 nu) :=
  gSum_counts tB2 fundB2 _ mB2 (fun v => ground.countOf_reverse v mB2) nu

theorem pin122 : recRead tB2 fundB2 wB2 mB2.reverse lamB2 := by
  apply recRead_counts tB2 fundB2 wB2 _ mB2 lamB2
    (fun v => ground.countOf_reverse v mB2) (by decide +kernel)

theorem pin123 : symRead tB2 mB2.reverse := by
  apply symRead_counts tB2 _ mB2 (fun v => ground.countOf_reverse v mB2) (by decide +kernel)

theorem pin124 : mShapeRead tB2 mB2.reverse := by
  apply mShapeRead_counts tB2 _ mB2 (fun v => ground.countOf_reverse v mB2) (by decide +kernel)

/-- Relisting the multiplicity family preserves each graded
convolution count, including its odd contributions. -/
theorem pin125 (W : List (List BPair × Bool)) (y : List BPair) (side : Bool) :
    convCount W mB2.reverse y side = convCount W mB2 y side :=
  convCount_counts W _ mB2 (fun v => ground.countOf_reverse v mB2) y side


/-- The longest-word symmetry reads every canonical key,
including those outside the family's occupied support. -/
theorem pin126 (L : List (List BPair)) (hm : mShapeRead tableG2 L) (hs : symRead tableG2 L)
    (v : List BPair) (hv : v.length = 2) (hn : poly.pnorm v = v) :
    ground.countOf (poly.pnorm (poly.neg v)) L = ground.countOf v L :=
  count_neg_G2 L hm hs v hv hn

theorem pin127 : ¬ symRead tableG2 [[BPair.ofNat 1, BPair.unit]]
    ∧ ground.countOf [BPair.ofNat 1, BPair.unit] [[BPair.ofNat 1, BPair.unit]] = 1
    ∧ ground.countOf (poly.pnorm (poly.neg [BPair.ofNat 1, BPair.unit]))
      [[BPair.ofNat 1, BPair.unit]] = 0 := by decide +kernel

theorem pin128 (L : List (List BPair)) (w : List (List Nat)) (top : List BPair)
    (ht : top.length = 2) (hm : mShapeRead tableG2 L) (hs : symRead tableG2 L)
    (hd : supportRead tableG2 L w top) (v : List BPair) (hv : v ∈ L) :
    BPair.unit ≤ dotB fundG2 top (rhoV tableG2) + dotB fundG2 v (rhoV tableG2) :=
  supportRead_shift_G2 L w top ht hm hs hd v hv

/-- The top convolution reads the general joined top through
its two finite support families. -/
theorem pin129 (t : gentable.Table) (F : sertables.FundData)
    (W : List (List BPair × Bool)) (w : List (List Nat))
    (L : List (List BPair)) (wL : List (List Nat)) (lam top : List BPair)
    (hl : top.length = t.rank) (hF : fundShape t F) (hsp : simplePosRead t F) (hr : rhoDotRead t F)
    (hW : wShapeRead t W) (hdW : wDomAt t W w top) (htW : wTopAt W top)
    (hL : mShapeRead t L) (hdL : supportRead t L wL lam) (htL : topRead L lam) (hlam : lamRead t lam) :
    convCount W L (poly.pnorm (elim.vecAdd lam top)) false = 1
      ∧ convCount W L (poly.pnorm (elim.vecAdd lam top)) true = 0 :=
  convTopAt t F W w L wL lam top hl hF hsp hr hW hdW htW hL hdL htL hlam

end memberchar
