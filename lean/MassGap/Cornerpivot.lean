import MassGap.Poly
import MassGap.Inertia
import MassGap.Greenprod
import MassGap.Stage
/-!
`lem:cornerpivot`'s walk tier.  On a band-one head at the dual
representative, at a scale pair `η` and a probe level cross-added in
the diagonal (`thm:certconstruct`'s spelling), the count below the
probe is the pivot sequence's lower-side count (`lem:inertia`), and
the read at most one is settled by four displayed comparisons at the
corner scale on the depth axis.  That count tie is this tier's
frame, consumed at the certificate's assembly beside the probe-line
tiers; the tier itself carries the four comparisons.

The pivots are carried at their cleared representatives, the leading
minors of the band-one head: the pivot at depth `k` is the minor
pair `(D_{k+1} : D_k)`, the pivot identity
`p_{k+1} p_k + β² = a_{k+1} p_k` is the minor recursion
`D_{k+2} + β² D_k = a_{k+1} D_{k+1}` (one `oneValue` read over the
balance pairs), and every pivot comparison is its cross-multiplied
read at the minors — one value across the representatives by the
homogeneity principle (`def:ground`).  The bond weight `β` is the
consuming tier's uniform off-diagonal entry, entering the recursion
at its square and every comparison at its first power; the tex's
unit-bond display is this tier's stage-gauge instance, the weight
one.  The walk is the running minor pair `(D_m, D_{m+1})`
(`walkGo`), its seed and step reads definitional, with the recursion
read `walk_rec` the identity at each depth.

Clause (i) is the one-step pivot induction (`pivot_clears`): at a
positive list `v` on a segment with the termwise read
`β (v_m + v_{m+2}) ≤ a_{m+1} v_{m+1}` and the entry read
`p_{m₀} v_{m₀} ≥ β v_{m₀+1}`, every later pivot of the segment
clears its entry read, `p_m v_m ≥ β v_{m+1}`, the pivot identity and
the two reads driving one cross-multiplied step per depth.  The
minor list enters abstract, bound by the recursion alone, so the
swap-reseed of clause (iii) and the block lifts read the one
induction.

Clause (ii) is the profile tier: a segment's supersolution is a
stated polynomial profile, one polynomial `V` in the scale and the
depth's two pair reads `mη` and `m²η`, read per depth as
`v_m = V(η, mη, m²η)`.  The kernel `u² = ηs` forces the canonical
representation — the u-degree at most one — so the profile datum is
the pair of coefficient slabs `(u⁰-slab, u¹-slab)`, each a
`poly.PPoly` at the outer s-power key and the inner scale
polynomial, and every read is the per-depth collapse (`depthPoly`):
the monomial at u-degree `a`, s-power `b` and scale power `c` reads
`m^(a+2b) η^(a+b+c)`, a polynomial in the scale alone at each depth.
The comparisons enter cleared at the rate's and the residue's shared
constant `(r+1)·qd` and the scale pair's `ed²` — the pair reads
carry the scale, so the well's electric member sits at the square
scale — and the bond weight of the walk tier is
`BPair.ofNat ((r+1)*qd) * BPair.ofPos ed * BPair.ofPos ed`, the
diagonal entering as `diagPoly`, `(r+1)·qd·(2 + ηW)` at the well
read `W = ⟨[4:r+1](s+ru) : q⟩` and the probe line's rate
`q = [qn : qd]`, its three keys the band read's clearing, the rate's
balance partner and the well's electric member.  Clause (i)'s
termwise comparison is then one polynomial read in the scale per
depth (`termPoly` at the collapsed triple `termPolyAt`, the
factoring `termPoly_at`), whose origin coefficient reads the sum's
unit (`termPoly_base`, with `termPoly_shift` the shifted-tail read)
— the comparison the scale's multiple of the remainder's centered
read — and whose cleared evaluation at the clearing two powers past
the profile's is that depth's read (`termRead`), unpacked to clause
(i)'s comparison at `termRead_read`.  The segment read collects the
shape at the stated clearing (`profShape`, its faithfulness
`depthPoly_ble`), the segment's collapses folded once (`segPolys`
with its member read `segPolys_at`) at every member's positivity,
and the termwise comparison at each depth read at the shared
collapse list's consecutive triple (`superRead`, its two projection
bridges `superRead_pos` and `superRead_term`), and it clears the
pivots at `super_clears`.  The profiles themselves are certificate
data — committed at stated degrees, the reads deciding them, never
trusting them (`thm:windowsep`'s producer discipline).

Clause (ii)'s profiles carry their own algebra at the kernel
`u² = ηs`: the slabwise sum, memberwise swap and count rescaling
(`profAdd`, `profNeg`, `profScale`), the reduced product whose
u¹-slabs re-enter the u⁰-slab at the `ηs`-multiple (`profMul`,
`esMul`), and the depth shift substituting the successor depth's two
pair reads (`profShift` at the shifted square scale `sh1 = s + 2u + η`
and the shifted scale read `u1 = u + η`, the slabs' Horner walk
`shGo`).  Each operation's per-depth collapse is the balance-pair
polynomials' own — the seven bridges `depthPoly_profAdd`,
`depthPoly_profMul`, `depthPoly_profShift`, `depthPoly_profScale`,
`depthPoly_profNeg`, `depthPoly_diagProf` and `depthPoly_termProf` —
so the diagonal and the comparison enter as one canonical object
each (`diagProf`, `termProf`).

The certificate's box device prices a canonical object's collapse
from below on a stated box of square scales.  Its data are the box's
composite endpoints with the floor chain's interior cut list and the
two remainder arms' own, the priced side reads' bound, the box
top's cleared read, four floors and the shape clearing
(`BoxCert`); its read is the shape, the box top inside its cleared
read, the scale-free part's chained priced side read against the floors'
join (`profBase`, `chainRead` the consecutive-cuts fold of
`stage.keepUpper`, its conclusion `chainRead_all`), the remainder's
origin coefficients read on the box at the chained device — the
scale coefficients above the first leading floor's balance partner
(`profLin`), the u¹-slab's origins at their squared price against
the second floor's square (`profBaseU`), each comparison's floor at
or beyond the sum's unit — and the deeper coefficients' two fold
comparisons at the ceiling's powers through the box top's cleared
read, the squared one's floor at or beyond the sum's unit (`capF`,
`capS`), and the conclusion is that every depth whose square scale
sits inside the box reads the collapse strictly above the sum's
unit (`boxRead`, `boxRead_pos`).  Beside it the one-variable
scale-tail read
(`lowRead`, `lowRead_pos`) and the step clearance carrying a depth
inside one composite top to a square scale inside the next
(`stepClear`, `stepClear_step`), each at the cleared ceiling.

A ceiling is a balance pair against a positive clearing, `[e₀ⁿ : e₀ᵈ]`
the scale's own bound read as `η·e₀ᵈ ≤ e₀ⁿ·ed` — the integer balance
pair cannot hold a rational ceiling and every committed ceiling is
one.  The coefficient folds read against it are cleared at the second
member's powers: one inner list's fold at a stated clearing (`capF`,
the magnitudes against the first member's powers, the second
member's clearing the complement) and the slabs' Horner against the
square-scale cap (`capS`).  A cleared evaluation's price against
those folds is `capF_price` at one list, `slabPriceC` at a
one-shift slab walk with the clearing's whole power entering the
comparison's other side, and `slabPriceC2` at the two-shift walk
with one further ceiling power there, the shift's second scale
power read at the scale's bound.

Clause (iii) is the crossing tier: one located depth reads its pivot
on the lower side, and the following pivot exceeds its diagonal —
the identity at a positive predecessor, weighted by the bond's
square, read on the exceeding side (`rebound`, the rebound read).
The swapped minors carry the recursion (`rec_swap`), and the swapped
pair seeds the later segments' entry reads at the diagonal itself
(`seed_after_crossing`).

Clause (iv) is the constant supersolution: at depths whose diagonal
clears the bond's double by a stated margin the constant list
carries the termwise read (`const_term`), and the pivots stay clear
to the head's end (`tail_clear`).

The constant-floor instance of clause (ii) is the walk's own list at
a constant diagonal and unit bonds (`uWalk`, `thm:channeldiv`'s own
boundary recursion), the boundary's unit seed `U_1 = 1` with the
recurrence `U_j + U_{j+2} = g U_{j+1}` read from the boundary
(`uWalk_rec`).

Clause (v) is the ground witness and the lower line's arithmetic
tier.  The witness family is the square-scale pair cleared at the
scale's square, `witVal N m = m²(N²−m²)`, its truncated difference
the family's own read — equal members at the endpoint `N` and the
sum's unit past it.  Its three sums (`witSq`, `witSqM`, `witSqMM`)
and the bond-square sum `witDiffSq` are read against the power sums
`powSum k n = Σ_{m≤n} m^k`, whose eleven closed reads
(`powSum0_closed` … `powSum10_closed`) come from the binomial step
identity at each key; the four bridges (`witSq_bridge`,
`witSqM_bridge`, `witSqMM_bridge`, `witDiffSq_bridge`) decompose the
family's sums per depth at the gap witness `m² + g = N²`, and the
four closed reads (`witSq_closed`, `witSqM_closed`, `witSqMM_closed`,
`witDiffSq_closed`, the last at the occupied endpoints) are their
cleared assemblies, read back at the polynomial objects
`sqClosedPoly`, `diffClosedPoly` and `wellClosedPoly`
(`sqClosedPoly_eval`, `diffClosedPoly_eval`, `wellClosedPoly_eval`).
The lower rate's two data are `qLowNum` and `qLowDen`, its endpoint
key the least depth beyond one at `40N⁴η² ≥ 363(r+1)` with the
predecessor's refusal (`endRead`), and the tops' cofactor identities
are `topWell_read` and `topDiff_read` with the key's comparison
their equality (`keyEq_read`).  The form read telescopes at the
family (`witTele`, the margin's square at the balance pair's own,
`margSq_read`), the display's two sides read at every rate pair
(`witForm`), and at the lower rate's own data the well fold
withdraws against the difference and boundary squares, leaving the
cross fold alone (`witKernel`).

Clause (v)'s count tier assembles the head and reads the counts off
it.  The head is the scalar chain at the diagonal's cleared reads
and the bond weight's balance partner (`wellDiag`, `wellBond`,
`wellMat`), assembled deep end first — slab `k` holds depth `n − k`,
the elimination's ordering certificate data (`thm:decimation`(i)) —
and the witness family enters at the same gauge (`witList`).  A
scalar chain's form read is its two folds, the diagonal entries at
the squares with the bonds at the doubled consecutive products
(`chainQuad`); at the well head the diagonal fold reads the family's
window (`wellDiagFold`) and the bond fold reads the cross sum
(`wellCrossFold`), so the head's form is the display's two sides
(`wellForm`).  At the lower rate's own data those two sides join at
the sum's unit (`witQuad`, through `kernelCancel` at `witKernel`);
at a member line beyond it the site identity prices the diagonal at
the second scale's multiple against the rates' gap on the cross
member (`siteScale`), the folds split at the scale (`scaledDiagFold`,
`bondScale`), and the residue is the gap weight's balance partner on
the family's occupied square fold, strictly below the sum's unit
(`witStrict`).  The family is then the count's own witness at every
split (`witCount`, `lem:inertia`'s forcing clause at the one-member
combination), and the cap pair's read is the compressed two-by-two's
completed square: at a leading entry below the sum's unit and a
doubled cross read below the diagonal product's quadruple, every
split reads the reversal count at two or beyond (`capForcing`, with
`capStrict` and `capStrictVac` the two scale classes).

Clause (vi) is the count spine at a scale.  The walk's minors enter
the head's own data as `wellWalk`, the running leading minors at the
diagonal `wellDiag` and the bond `wellBond`, and the certificate the
count split consumes is the walk's own: at depth `k` the pivot is the
cleared datum `(D_k D_{k-1} : marg(D_{k-1})²)` (`pivotQ`) and the
recursion's witness the cleared datum
`(β̌ D_{k-1} D_k : marg(D_k)²)` (`pivotR`), the margin `margP` the
positive carrier of a minor off equal members, whose square is that
minor's own (`margP_sq`).  The deep-first assembly seeds the slab
recursion at the boundary, so slab `j` of an order-`n` head holds
depth `n − j`, and the two lists satisfy `lem:greenprod`'s tail
recursion at every depth (`wellTail`, with `pivotBase` the seed,
`pivotCross` the witness step and `pivotJoin` the join).  Each pivot
is a one-by-one datum, so its own split is the order-one certificate
at the identity congruence (`split1`, `splitRead_one`), and the slab
fold of those counts is decided by the signs alone: a stated crossing
depth leaves exactly one lower-side pivot, at the crossing itself,
and none otherwise (`wellRevFold`, `wellRevFoldZero`).  Through
`lem:greenprod`(ii)'s count split this reads the head's own reversal
count — one at a stated crossing (`certRevOne`), vacant at a
crossing-free walk (`certRevZero`).

Two member lines at one scale pair meet at the site identity: the
head is a scalar chain, so its entry at a key pair is the entry chart
`chainAt` (`chainEntry`, at the diagonal's and the bond's own entry
lists), and entrywise the second line's scaled head is the first's
scaled head against the rates' gap on the identity
(`lineSite`, with `lineDiag`, `lineBond` and `lineFar` the three
entry classes); the same reads give the gap itself as that scalar
diagonal (`lineGap`).  The lower rate's own data are occupied at an
occupied family (`qLowPos`).  The multiple cut's downward closure is
then the two-sided read: `witCount` prices every member line's count
at one or beyond, and the site datum's positive scalar diagonal
carries `lem:inertia`'s monotonicity across the two scaled heads, so
a lower member line's count sits at or below the upper's own
(`cutMono`) — the flat window, count one from the lower line's side
to the member's (`cutFlat`).

The count spine's two degenerate arms run at the same split.  At a
head whose last minor carries equal members the deep end's pivot is
singular, so its slab takes the order-one kernel certificate
(`split1K`, `splitRead_oneK`) and the fold is vacant
(`certRevZeroKern`).  At an interior degenerate spot the singular
pivot re-orders inside one slab (`lem:greenprod`'s parenthetical):
the slab list is mixed — order-one blocks off the spot and the spot's
own order-two block at the two consecutive depths (`spotMat`,
`mDiag`, `mOff`, `mNs`) — and the assembled matrix is the same head
(`mixRead`, `mixRows`, `mixSq`, `mixMat`, at the entry chart's
order-two and wide-off steps `twoEntry`, `wideEntry`).  The spot's
cleared pivot is the slab less the shallower chain's transfer
(`spotQ`), its two witnesses the solves against the neighbouring off
blocks (`spotWit`, `spotR`), and the four recursion identities are
the walk's own (`spotCross`, `spotJoin`, `spotCrossUp`,
`spotCrossUpZero`, `spotJoinUp`); the spot's minor is the chain's
cubed top against the depth beyond it (`minorSpot`,
`minorSpotZero`), so its order-two split (`split2`,
`splitRead_two`, `spotSplit`) counts one at the lower-side
determinant and every other slab's signs agree — the head's count is
one (`certRevOneMixed`).

The graded box device prices from below a canonical object vacant at
the scale-free order: the value's own grading at the kernel reads the
depth multiple of the u-slab's origin coefficients (`profBaseU`)
against the u⁰-slab's scale-key coefficients (`profLin`), the depth's
leading part one read per depth and linear in it, and the certificate
carries two cut lists (`GradCert`, `gradRead`, at the cleared
ceiling): the origin reads' own chain, and the two-armed chain
(`chainRead2`) of the scale-key read's line above the tail floors'
join, whose pieces keep the line's upper side (`lineL`) or the
squared comparison's (`lineSq`), the square scale's multiple of the
origin reads' square at the ceiling's cross-multiplied read above
the squared gap of the join to the scale-key read.  Its conclusion
is that every
depth beyond nought whose square scale sits inside the box reads the
collapse strictly above the sum's unit (`gradRead_pos`): the collapse
is the scale shift of the stripped walk, whose origin slabs are the
depth's own combination of the two base polynomials — the depth
multiple past the gap returned at the trichotomy of squares — and
whose tails are priced by the two cap conjuncts.  At both slabs
vacant at the origin the collapse is the stripped collapse's scale
shift (`profStrip`, `profVac`, `depthPoly_profStrip`).

The universal count identities of this tier are settled through two
devices, each a private engine: an expression's key form over two
variables (`Mir`, `mirEq`) for the polynomial identities, and a
product's count-and-exponent form over a stated datum list (`Mon`,
`monEq`) for the monomial ones.

The bundled certificate closes the count read at every scale and
order at once.  Its objects are the boundary comparison `seedProf`
(the shifted diagonal's multiple of the profile against the rate's
multiple of the shifted profile), the seam's crossed products
`crossProf`, the depth step `stepProf` and the final seam's
`slopeProf` at the pair allowance, each with its collapse bridge
(`seedProf_at`, `crossProf_at`, `stepProf_at`, `slopeProf_at`).
The certificate `DisconjCert` bundles the rate, the cleared
ceiling, the pre profile with its graded reads and boundary seed
clearings, the seam-chained segment lists on the two sides of the
crossing, and the final seam with the dominance margin; its
decidable reads are `segRead` (one segment's boxes at the two-step
overlap), `seamRead` (the crossed products on the seam's box with
the handover cap and the non-decreasing bottoms), `chainSegs` (a
chained list from a standing profile), `seedRead` (the boundary
floors), and `certRead` (the whole certificate).  `certCount` is
the glue: the certificate's read settles the reversal count at
most one at every line at or below the stated rate's, the cut
members' lines among them, at every scale under the ceiling, every
order and every split — the entry reads chain across the segments
to the crossing seam, the first lower-side pivot sits past it with
the later boxes' reads running from below it, and the count read
closes beyond it at the rebound seed and the dominance tail's
geometric list.
-/

namespace cornerpivot

open ground

/-- The band-one walk's minor pair at a diagonal and a bond weight —
the running pair `(D_m, D_{m+1})` of the leading minors, seeded at
the vacant product against the first diagonal entry, each further
minor the recursion's join `D_{m+2} + β² D_m = a_{m+1} D_{m+1}` at
the withdrawn member's bond-weighted swap. -/
def walkGo (β : BPair) (a : Nat → BPair) : Nat → BPair × BPair
  | 0 => (BPair.ofNat 1, a 0)
  | m + 1 =>
    let p := walkGo β a m
    (p.2, a (m + 1) * p.2 + (β * β * p.1).swap)

/-- The walk's seed: the vacant product against the head's first
diagonal entry. -/
theorem walk_zero (β : BPair) (a : Nat → BPair) :
    walkGo β a 0 = (BPair.ofNat 1, a 0) := rfl

/-- The walk's step: the pair advances by one depth, the arriving
minor the diagonal's multiple against the withdrawn member's
bond-weighted swap. -/
theorem walk_step (β : BPair) (a : Nat → BPair) (m : Nat) :
    walkGo β a (m + 1)
      = ((walkGo β a m).2,
         a (m + 1) * (walkGo β a m).2 + (β * β * (walkGo β a m).1).swap) :=
  rfl

/-- The walk's recursion read: the arriving minor against the
withdrawn one at the bond's square is the diagonal's multiple of the
standing minor, `D_{m+2} + β² D_m = a_{m+1} D_{m+1}`. -/
theorem walk_rec (β : BPair) (a : Nat → BPair) (m : Nat) :
    ((walkGo β a (m + 1)).2 + β * β * (walkGo β a m).1).oneValue
      (a (m + 1) * (walkGo β a m).2) :=
  BPair.add_swap_self _ _

/-- A product strictly above the sum's unit at a second factor at or
above it prices its first factor strictly above the unit. -/
private theorem unitLtOfMulRight {x y : BPair} (hy : BPair.unit ≤ y)
    (h : BPair.unit < x * y) : BPair.unit < x :=
  if hc : BPair.unit < x then hc
  else
    absurd h
      (leB_not_lt
        (leB_congr_left (BPair.oneValue_of_eq (BPair.mul_comm y x))
          (leB_congr_right (BPair.mul_unit y)
            (leB_mulR hy (leB_of_not_lt hc)))))

/-- Clause (i): at a positive list `v` on a segment with the
termwise read `β (v_m + v_{m+2}) ≤ a_{m+1} v_{m+1}` and the entry
read at the segment's head, every later pivot of the segment clears
its entry read, the comparison cross-multiplied at the minors and
weighted by the bond.  The minor list is bound by the recursion
alone. -/
theorem pivot_clears (a v D : Nat → BPair) (β : BPair) (len : Nat)
    (hβ : BPair.unit < β)
    (hrec : ∀ k, k < len →
      (D (k + 2) + β * β * D k).oneValue (a (k + 1) * D (k + 1)))
    (hterm : ∀ k, k < len →
      β * (v k + v (k + 2)) ≤ a (k + 1) * v (k + 1))
    (hpos : ∀ k, k ≤ len + 1 → BPair.unit < v k)
    (h0 : BPair.unit < D 0)
    (hseed : β * (D 0 * v 1) ≤ D 1 * v 0) :
    ∀ k, k ≤ len →
      BPair.unit < D (k + 1) ∧ β * (D k * v (k + 1)) ≤ D (k + 1) * v k := by
  have hβLe : BPair.unit ≤ β := leB_of_lt hβ
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, hseed⟩
    refine unitLtOfMulRight
      (leB_of_lt (hpos 0 (Nat.zero_le (len + 1)))) ?_
    exact ltB_trans_le
      (unitLtMul hβ (unitLtMul h0 (hpos 1 (Nat.succ_le_succ (Nat.zero_le len)))))
      hseed
  | succ k ih =>
    intro hk
    have hkl : k < len := hk
    have ihk := ih (Nat.le_of_succ_le hkl)
    have hDk : BPair.unit < D (k + 1) := ihk.1
    have hentry : β * (D k * v (k + 1)) ≤ D (k + 1) * v k := ihk.2
    have hDkLe : BPair.unit ≤ D (k + 1) := leB_of_lt hDk
    have e1 : β * β * D k * v (k + 1) = β * (β * (D k * v (k + 1))) := by
      rw [BPair.mul_assoc, BPair.mul_assoc]
    have e2 : D (k + 1) * (β * (v k + v (k + 2)))
        = β * (D (k + 1) * v k) + β * (D (k + 1) * v (k + 2)) := by
      rw [BPair.left_distrib β (v k) (v (k + 2)),
        BPair.left_distrib (D (k + 1)) (β * v k) (β * v (k + 2)),
        BPair.mul_left_comm (D (k + 1)) β (v k),
        BPair.mul_left_comm (D (k + 1)) β (v (k + 2))]
    have e3 : D (k + 1) * (a (k + 1) * v (k + 1))
        = a (k + 1) * D (k + 1) * v (k + 1) := by
      rw [BPair.mul_assoc, BPair.mul_left_comm]
    have e4 : (D (k + 2) + β * β * D k) * v (k + 1)
        = D (k + 2) * v (k + 1) + β * β * D k * v (k + 1) :=
      BPair.right_distrib (D (k + 2)) (β * β * D k) (v (k + 1))
    have hleft : β * β * D k * v (k + 1) + β * (D (k + 1) * v (k + 2))
        ≤ D (k + 1) * (β * (v k + v (k + 2))) := by
      rw [e1, e2]
      exact leB_add (leB_mulR hβLe hentry)
        (leB_refl (β * (D (k + 1) * v (k + 2))))
    have hmid : D (k + 1) * (β * (v k + v (k + 2)))
        ≤ a (k + 1) * D (k + 1) * v (k + 1) := by
      rw [← e3]
      exact leB_mulR hDkLe (hterm k hkl)
    have hrecMul : (a (k + 1) * D (k + 1) * v (k + 1)).oneValue
        (D (k + 2) * v (k + 1) + β * β * D k * v (k + 1)) :=
      BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.oneValue_symm (hrec k hkl)))
        (BPair.oneValue_of_eq e4)
    have hjoin : β * β * D k * v (k + 1) + β * (D (k + 1) * v (k + 2))
        ≤ β * β * D k * v (k + 1) + D (k + 2) * v (k + 1) := by
      refine leB_congr_right
        (BPair.oneValue_of_eq
          (BPair.add_comm (D (k + 2) * v (k + 1))
            (β * β * D k * v (k + 1)))) ?_
      exact leB_congr_right hrecMul (leB_trans hleft hmid)
    have hnext : β * (D (k + 1) * v (k + 2)) ≤ D (k + 2) * v (k + 1) :=
      leB_cancelL hjoin
    refine ⟨?_, hnext⟩
    refine unitLtOfMulRight
      (leB_of_lt (hpos (k + 1) (Nat.le_trans hkl (Nat.le_succ len)))) ?_
    exact ltB_trans_le
      (unitLtMul hβ (unitLtMul hDk (hpos (k + 2) (Nat.succ_le_succ hk))))
      hnext

/-- Clause (iii)'s rebound read: the identity at a positive
predecessor and an occupied bond, the square's positivity the bond's
own read, prices the arriving minor strictly below the diagonal's
multiple — the pivot past a lower-side one beyond its diagonal at
the cross-multiplied read.  The lower-side reading of `D1` is the
frame the comparison is named in. -/
theorem rebound (aP β D0 D1 D2 : BPair)
    (hrec : (D2 + β * β * D0).oneValue (aP * D1))
    (hβ : BPair.unit < β * β)
    (h0 : BPair.unit < D0) :
    D2 < aP * D1 :=
  BPair.lt_congr (BPair.oneValue_refl D2) hrec
    (ltB_addPos (unitLtMul hβ h0))

/-- The swapped minors carry the recursion: the memberwise swap
keeps the identity `D_{k+2} + β² D_k = a_{k+1} D_{k+1}` at the
swapped list, the bond weight standing. -/
theorem rec_swap {aP β Dk Dk1 Dk2 : BPair}
    (hrec : (Dk2 + β * β * Dk).oneValue (aP * Dk1)) :
    (Dk2.swap + β * β * Dk.swap).oneValue (aP * Dk1.swap) := by
  rw [BPair.mul_swap (β * β) Dk, BPair.swap_add, BPair.mul_swap aP Dk1]
  exact swap_congr hrec

/-- Clause (iii)'s reseed: past the crossing the swapped pair reads
its entry comparison at the diagonal itself, the later segments'
entry read seeded there at the bond weight.  The bond needs no sign
read and the predecessor only its upper-side-or-equal read: the
recursion's split prices the arriving minor at the bond square's
own positivity, `dom_of_split` at the square against the
predecessor. -/
theorem seed_after_crossing (aP β D0 D1 D2 v1 v2 : BPair)
    (hrec : (D2 + β * β * D0).oneValue (aP * D1))
    (h0 : BPair.unit ≤ D0)
    (hc : D1 < BPair.unit)
    (hpos : BPair.unit < v1)
    (hterm : β * v2 ≤ aP * v1) :
    β * (D1.swap * v2) ≤ D2.swap * v1 := by
  have hv1 : BPair.unit ≤ v1 := leB_of_lt hpos
  have hleft : D2 * v1 ≤ aP * D1 * v1 :=
    leB_congr (BPair.oneValue_of_eq (BPair.mul_comm v1 D2))
      (BPair.oneValue_of_eq (BPair.mul_comm v1 (aP * D1)))
      (leB_mulR hv1
        (ground.dom_of_split hrec (unitLeMul (unitLeSq β) h0)))
  have hswapPos : BPair.unit ≤ D1.swap := leB_of_lt (ltB_swap hc)
  have hswapped : (D1 * (β * v2)).swap ≤ (D1 * (aP * v1)).swap := by
    rw [← BPair.swap_mul, ← BPair.swap_mul]
    exact leB_mulR hswapPos hterm
  have hright : D1 * (aP * v1) ≤ D1 * (β * v2) := leB_swap hswapped
  have hmid : (aP * D1 * v1).oneValue (D1 * (aP * v1)) := by
    rw [BPair.mul_comm aP D1, BPair.mul_assoc]
    exact BPair.oneValue_refl _
  have hchain : D2 * v1 ≤ D1 * (β * v2) :=
    leB_trans hleft (leB_congr_left (BPair.oneValue_symm hmid) hright)
  rw [BPair.swap_mul D1 v2, BPair.mul_swap β (D1 * v2), BPair.swap_mul D2 v1]
  exact leB_swap
    (leB_congr_right
      (BPair.oneValue_of_eq (BPair.mul_left_comm D1 β v2)) hchain)

/-- Clause (iv)'s termwise read at the constant list: a diagonal
clearing the bond's double prices the constant supersolution's
termwise comparison. -/
theorem const_term (aP β c : BPair) (hpos : BPair.unit ≤ c)
    (ha : β * BPair.ofNat 2 ≤ aP) :
    β * (c + c) ≤ aP * c := by
  have hval : (BPair.ofNat 2 * c).oneValue (c + c) := BPair.ofNat_two_mul c
  have hβc : (β * BPair.ofNat 2 * c).oneValue (β * (c + c)) :=
    BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc β (BPair.ofNat 2) c))
      (BPair.mul_congr (BPair.oneValue_refl β) hval)
  refine leB_congr_left hβc ?_
  exact leB_congr
    (BPair.oneValue_of_eq (BPair.mul_comm c (β * BPair.ofNat 2)))
    (BPair.oneValue_of_eq (BPair.mul_comm c aP)) (leB_mulR hpos ha)

/-- Clause (iv): at depths whose diagonal clears the bond's double
by a stated margin the constant list is the supersolution, and the
pivots stay clear to the head's end. -/
theorem tail_clear (a D : Nat → BPair) (β : BPair) (len : Nat)
    (hβ : BPair.unit < β)
    (hrec : ∀ k, k < len →
      (D (k + 2) + β * β * D k).oneValue (a (k + 1) * D (k + 1)))
    (ha : ∀ k, k < len → β * BPair.ofNat 2 ≤ a (k + 1))
    (h0 : BPair.unit < D 0)
    (hseed : β * D 0 ≤ D 1) :
    ∀ k, k ≤ len → BPair.unit < D (k + 1) := by
  intro k hk
  refine (pivot_clears a (fun _ => BPair.ofNat 1) D β len hβ hrec ?_ ?_ h0 ?_ k
    hk).1
  · exact fun j hj =>
      const_term (a (j + 1)) β (BPair.ofNat 1) (unitLeOfNat 1) (ha j hj)
  · exact fun _ _ => unitLtOfPos (posOfSucc 0)
  · exact leB_congr
      (BPair.mul_congr (BPair.oneValue_refl β)
        (BPair.oneValue_symm (BPair.mul_ofNat_one (D 0))))
      (BPair.oneValue_symm (BPair.mul_ofNat_one (D 1))) hseed

/-- The walk's own list at a constant diagonal and unit bonds — the
boundary's unit seed `U_1 = 1` with the recurrence
`U_j + U_{j+2} = g U_{j+1}`, the truncation recursion's
integer-polynomial list at the floor (`thm:channeldiv`'s boundary
recursion read from the boundary). -/
def uWalk (g : BPair) : Nat → BPair
  | 0 => BPair.unit
  | m + 1 => (walkGo (BPair.ofNat 1) (fun _ => g) m).1

/-- The list's boundary entry, the sum's unit. -/
theorem uWalk_zero (g : BPair) : uWalk g 0 = BPair.unit := rfl

/-- The boundary's unit seed `U_1 = 1`. -/
theorem uWalk_one (g : BPair) : uWalk g 1 = BPair.ofNat 1 := rfl

/-- The unit bond's square withdraws from a product. -/
private theorem unitBond (x : BPair) :
    (BPair.ofNat 1 * BPair.ofNat 1 * x).oneValue x :=
  BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.mul_ofNat_one (BPair.ofNat 1)))
    (BPair.ofNat_one_mul x)

/-- The constant-floor list's recurrence `U_j + U_{j+2} = g U_{j+1}`
at every depth. -/
theorem uWalk_rec (g : BPair) (j : Nat) :
    (uWalk g (j + 2) + uWalk g j).oneValue (g * uWalk g (j + 1)) := by
  match j with
  | 0 =>
    exact BPair.oneValue_trans (BPair.add_unit g)
      (BPair.oneValue_symm (BPair.mul_ofNat_one g))
  | i + 1 =>
    show ((walkGo (BPair.ofNat 1) (fun _ => g) (i + 1)).2
        + (walkGo (BPair.ofNat 1) (fun _ => g) i).1).oneValue
      (g * (walkGo (BPair.ofNat 1) (fun _ => g) i).2)
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm
          (unitBond (walkGo (BPair.ofNat 1) (fun _ => g) i).1)))
      (walk_rec (BPair.ofNat 1) (fun _ => g) i)

/-! `lem:cornerpivot`(ii)'s profile tier: the stated polynomial
profiles, their per-depth collapse, the comparison polynomial with
its origin read, and the segment supersolution read. -/

/-- The profile's per-depth collapse — the u⁰-slab's s-power `b`
enters at the depth's power `(m²)^b` shifted `b` scale keys up, the
u¹-slab's at `m·(m²)^b` shifted `b+1`, the canonical monomial
`u^a s^b η^c` reading `m^(a+2b) η^(a+b+c)`; the collapse is a
polynomial in the scale alone at each depth, the profile's stated
read, the slab walk structural with the depth powers a running
product. -/
private def slabGo (mm : Nat) : Nat → Nat → poly.PPoly → poly.Poly
  | _, _, [] => []
  | b, w, p :: t =>
    poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
      (slabGo mm (b + 1) (w * mm) t)

def depthPoly (V : poly.PPoly × poly.PPoly) (m : Nat) : poly.Poly :=
  poly.add (slabGo (m * m) 0 1 V.1) (slabGo (m * m) 1 m V.2)

/-- The diagonal's cleared scale polynomial at the well read —
`(r+1)·qd·(2 + ηW)` at `W = ⟨[4:r+1](s+ru) : q⟩`, the rate
`q = [qn : qd]` and the pair reads `u = mη`, `s = m²η`: the constant
key the band read's clearing, the scale key the rate's balance
partner, and the square key the well's electric member, the pair
reads' own scale powers. -/
def diagPoly (r qn qd m : Nat) : poly.Poly :=
  [BPair.ofNat (2 * ((r + 1) * qd)),
   (BPair.ofNat ((r + 1) * qn)).swap,
   BPair.ofNat (4 * qd * (m * m + r * m))]

/-- The termwise comparison's polynomial at a collapsed triple — the
diagonal's multiple of the standing collapse against the cleared
neighbor sum, clause (i)'s comparison at stated collapse data. -/
def termPolyAt (P0 P1 P2 : poly.Poly) (r qn qd m : Nat) : poly.Poly :=
  poly.add
    (poly.mul (diagPoly r qn qd (m + 1)) P1)
    (poly.neg (poly.scaleP (BPair.ofNat ((r + 1) * qd))
      (poly.add P0 P2)))

/-- The termwise comparison's polynomial in the scale at a depth
— the comparison at the depth's own collapsed triple, the scale's
multiple of the remainder's centered read. -/
def termPoly (V : poly.PPoly × poly.PPoly) (r qn qd m : Nat) : poly.Poly :=
  termPolyAt (depthPoly V m) (depthPoly V (m + 1)) (depthPoly V (m + 2))
    r qn qd m

/-- The comparison factors through the collapsed triple, the
definitional read. -/
theorem termPoly_at (V : poly.PPoly × poly.PPoly) (r qn qd m : Nat) :
    termPoly V r qn qd m
      = termPolyAt (depthPoly V m) (depthPoly V (m + 1))
          (depthPoly V (m + 2)) r qn qd m :=
  rfl

/-- A slab walk from an occupied shift reads the origin at the sum's
unit, every member shifted past it. -/
private theorem slabHead (mm : Nat) : ∀ (b w : Nat) (l : poly.PPoly),
    (ground.getAt BPair.unit (slabGo mm (b + 1) w l) 0).oneValue
      BPair.unit
  | _, _, [] => BPair.oneValue_refl _
  | b, w, _ :: t =>
    BPair.oneValue_trans (poly.getAt_add _ _ 0)
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl BPair.unit)
          (slabHead mm (b + 1) (w * mm) t))
        (BPair.add_unit BPair.unit))

/-- The nought-shift slab walk's origin is its first member's own,
at the unit weight. -/
private theorem slabZeroHead (mm : Nat) : ∀ l : poly.PPoly,
    (ground.getAt BPair.unit (slabGo mm 0 1 l) 0).oneValue
      (ground.getAt BPair.unit (ground.getAt ([] : poly.Poly) l 0) 0)
  | [] => BPair.oneValue_refl _
  | _ :: t =>
    BPair.oneValue_trans (poly.getAt_add _ _ 0)
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans (poly.getAt_scaleP _ _ 0)
            (BPair.ofNat_one_mul _))
          (slabHead mm 0 (1 * mm) t))
        (BPair.add_unit _))

/-- The depth collapse's origin coefficient is depth-free: only the
u⁰-slab's nought s-power reaches the origin, and its scaling is the
depth's nought power. -/
private theorem depthPoly_head (V : poly.PPoly × poly.PPoly) (m : Nat) :
    (ground.getAt BPair.unit (depthPoly V m) 0).oneValue
      (ground.getAt BPair.unit
        (ground.getAt ([] : poly.Poly) V.1 0) 0) :=
  BPair.oneValue_trans (poly.getAt_add _ _ 0)
    (BPair.oneValue_trans
      (BPair.add_congr (slabZeroHead (m * m) V.1)
        (slabHead (m * m) 0 m V.2))
      (BPair.add_unit _))

/-- The origin of a product of coefficient lists is the origins'
product. -/
private theorem originMul : ∀ (p q : poly.Poly),
    (ground.getAt BPair.unit (poly.mul p q) 0).oneValue
      (ground.getAt BPair.unit p 0 * ground.getAt BPair.unit q 0)
  | [], q => BPair.oneValue_symm (BPair.unit_mul _)
  | c :: p, q => by
    show (ground.getAt BPair.unit
        (poly.add (q.map (fun d => c * d)) (BPair.unit :: poly.mul p q))
        0).oneValue (c * ground.getAt BPair.unit q 0)
    refine BPair.oneValue_trans (poly.getAt_add _ _ 0) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (poly.getAt_scale c q 0) (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_trans (BPair.add_unit _) (BPair.oneValue_refl _)

/-- The diagonal's origin read: the band read's clearing against the
second factor's own origin coefficient. -/
private theorem diagHead (r qn qd m : Nat) (q : poly.Poly) :
    (ground.getAt BPair.unit
      (poly.mul (diagPoly r qn qd m) q) 0).oneValue
      (BPair.ofNat (2 * ((r + 1) * qd))
        * ground.getAt BPair.unit q 0) :=
  originMul _ _

/-- The band read's double against a datum is the clearing constant's
multiple of the datum's own double. -/
private theorem baseArith (cst : Nat) (x : BPair) :
    (BPair.ofNat cst * (x + x)).oneValue
      (BPair.ofNat (2 * cst) * x) := by
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.ofNat_mul 2 cst)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.mul_assoc (BPair.ofNat 2) (BPair.ofNat cst) x)) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_of_eq
      (BPair.left_distrib (BPair.ofNat cst) x x).symm)
  rw [← BPair.scale_two (BPair.ofNat cst * x)]
  exact BPair.ofPos_scale 2 (BPair.ofNat cst * x)

/-- The comparison polynomial's origin coefficient reads the sum's
unit — the constant keys' reads are depth-free and the band read's
double withdraws against the cleared neighbor sum's, so the
comparison is the scale's multiple of the remainder, the
withdrawal's own read. -/
theorem termPoly_base (V : poly.PPoly × poly.PPoly) (r qn qd m : Nat) :
    (ground.getAt BPair.unit (termPoly V r qn qd m) 0).oneValue
      BPair.unit := by
  refine BPair.oneValue_trans (poly.getAt_add _ _ 0) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans (diagHead r qn qd (m + 1) _)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (depthPoly_head V (m + 1))))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (poly.getAt_neg _ 0))
        (ground.swap_congr
          (BPair.oneValue_trans (poly.getAt_scaleP _ _ 0)
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_trans (poly.getAt_add _ _ 0)
                (BPair.add_congr (depthPoly_head V m)
                  (depthPoly_head V (m + 2))))))))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
  exact BPair.swap_add_null (baseArith ((r + 1) * qd) _)

/-- A list whose origin coefficient reads the sum's unit is one
value with its own tail shifted onto the vacant origin. -/
private theorem ovShiftDrop : ∀ p : poly.Poly,
    (ground.getAt BPair.unit p 0).oneValue BPair.unit →
      poly.oneValue p (poly.shiftUp 1 (List.drop 1 p))
  | [], _ => ⟨BPair.oneValue_refl BPair.unit, trivial⟩
  | _ :: t, h => ⟨h, poly.oneValue_refl t⟩

/-- The comparison polynomial is one value with its own tail shifted
onto the vacant origin — the remainder's withdrawal at the stated
degree, `termPoly_base` the origin's read. -/
theorem termPoly_shift (V : poly.PPoly × poly.PPoly) (r qn qd m : Nat) :
    poly.oneValue (termPoly V r qn qd m)
      (poly.shiftUp 1 (List.drop 1 (termPoly V r qn qd m))) :=
  ovShiftDrop _ (termPoly_base V r qn qd m)

/-- The slab keys' clearance walk: every shifted coefficient list of
the slab sits inside the clearing power. -/
private def bleGo (K : Nat) : Nat → poly.PPoly → Bool
  | _, [] => true
  | b, p :: t => Nat.ble (b + p.length) (K + 1) && bleGo K (b + 1) t

/-- The profile's shape read at the stated clearing — every slab
key's shifted coefficient list sits inside the clearing power, the
cleared evaluation's faithfulness conjunct (`lem:cellcount`'s shape
discipline). -/
def profShape (V : poly.PPoly × poly.PPoly) (K : Nat) : Prop :=
  (bleGo K 0 V.1 && bleGo K 1 V.2) = true

instance (V : poly.PPoly × poly.PPoly) (K : Nat) :
    Decidable (profShape V K) :=
  inferInstanceAs (Decidable (_ = _))

/-- The slab walk's key count sits inside the clearing power at the
clearance walk's read. -/
private theorem slabGo_ble {K : Nat} (mm : Nat) :
    ∀ (b w : Nat) (l : poly.PPoly), bleGo K b l = true →
      (slabGo mm b w l).length ≤ K + 1
  | _, _, [], _ => Nat.zero_le _
  | b, w, p :: t, h => by
    have hs := ground.andSplitB h
    refine poly.add_len_le _ _ (K + 1) ?_ ?_
    · rw [poly.len_shift, poly.length_scaleP]
      exact Nat.le_of_ble_eq_true hs.1
    · exact slabGo_ble mm (b + 1) (w * mm) t hs.2

/-- The shape read prices every depth's collapse inside the stated
clearing power, the faithfulness of the cleared evaluation at the
profile's reads. -/
theorem depthPoly_ble {V : poly.PPoly × poly.PPoly} {K : Nat}
    (h : profShape V K) : ∀ m : Nat, (depthPoly V m).length ≤ K + 1 := by
  intro m
  have hs := ground.andSplitB h
  exact poly.add_len_le _ _ (K + 1)
    (slabGo_ble (m * m) 0 1 V.1 hs.1)
    (slabGo_ble (m * m) 1 m V.2 hs.2)

/-- The profile's positivity read on the segment — every depth of the
segment with its two successors reads the cleared evaluation strictly
above the sum's unit, clause (i)'s positive list. -/
def profPos (V : poly.PPoly × poly.PPoly) (en ed : Pos)
    (K mLo len : Nat) : Prop :=
  ∀ k, k < len + 2 →
    BPair.unit < poly.evalClear (depthPoly V (mLo + k))
      (BPair.ofPos en) ed K

instance (V : poly.PPoly × poly.PPoly) (en ed : Pos) (K mLo len : Nat) :
    Decidable (profPos V en ed K mLo len) :=
  Nat.decidableBallLT _ _

/-- The termwise comparison's read at a depth and a scale — the
comparison polynomial's cleared evaluation at or above the sum's
unit, the clearing two powers past the profile's at the diagonal's
square key. -/
def termRead (V : poly.PPoly × poly.PPoly) (r qn qd : Nat)
    (en ed : Pos) (K m : Nat) : Prop :=
  BPair.unit ≤ poly.evalClear (termPoly V r qn qd m)
    (BPair.ofPos en) ed (K + 2)

instance (V : poly.PPoly × poly.PPoly) (r qn qd : Nat) (en ed : Pos)
    (K m : Nat) : Decidable (termRead V r qn qd en ed K m) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The segment's collapse list, the depths' shared fold: each depth
of the segment with its two successors collapses once, every further
read the list's own member. -/
def segPolys (V : poly.PPoly × poly.PPoly) (mLo n : Nat) :
    List poly.Poly :=
  (List.range n).map (fun k => depthPoly V (mLo + k))

/-- The collapse list's member at a segment key is the key's own
collapse. -/
theorem segPolys_at (V : poly.PPoly × poly.PPoly) (mLo n j : Nat)
    (h : j < n) :
    ground.getAt [] (segPolys V mLo n) j = depthPoly V (mLo + j) := by
  show ground.getAt ([] : poly.Poly)
    ((List.range n).map (fun k => depthPoly V (mLo + k))) j = _
  rw [ground.getAt_map_range ([] : poly.Poly)
    (fun k => depthPoly V (mLo + k)) n j, if_pos h]

/-- The segment supersolution read — the shape at the stated
clearing, the segment's collapses folded once with every member's
positivity, and the termwise comparison at each depth of the segment
read at the shared collapse list's consecutive triple. -/
def superRead (V : poly.PPoly × poly.PPoly) (r qn qd : Nat)
    (en ed : Pos) (K mLo len : Nat) : Prop :=
  profShape V K
  ∧ (∀ j, j < len + 2 →
      BPair.unit < poly.evalClear
        (ground.getAt [] (segPolys V mLo (len + 2)) j)
        (BPair.ofPos en) ed K)
  ∧ ∀ k, k < len →
      BPair.unit ≤ poly.evalClear
        (termPolyAt (ground.getAt [] (segPolys V mLo (len + 2)) k)
          (ground.getAt [] (segPolys V mLo (len + 2)) (k + 1))
          (ground.getAt [] (segPolys V mLo (len + 2)) (k + 2))
          r qn qd (mLo + k))
        (BPair.ofPos en) ed (K + 2)

instance (V : poly.PPoly × poly.PPoly) (r qn qd : Nat) (en ed : Pos)
    (K mLo len : Nat) :
    Decidable (superRead V r qn qd en ed K mLo len) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The segment read's positivity conjunct is the profile's own
positivity read, the collapse list's members the depths' own. -/
theorem superRead_pos {V : poly.PPoly × poly.PPoly} {r qn qd : Nat}
    {en ed : Pos} {K mLo len : Nat}
    (h : superRead V r qn qd en ed K mLo len) :
    profPos V en ed K mLo len := by
  intro j hj
  have hread := h.2.1 j hj
  rwa [segPolys_at V mLo (len + 2) j hj] at hread

/-- The segment read's comparison conjunct is the termwise read at
each depth, the collapse list's triple the depth's own. -/
theorem superRead_term {V : poly.PPoly × poly.PPoly} {r qn qd : Nat}
    {en ed : Pos} {K mLo len : Nat}
    (h : superRead V r qn qd en ed K mLo len) :
    ∀ k, k < len → termRead V r qn qd en ed K (mLo + k) := by
  intro k hk
  have hread := h.2.2 k hk
  rw [segPolys_at V mLo (len + 2) k
      (Nat.lt_of_lt_of_le hk (Nat.le_add_right len 2)),
    segPolys_at V mLo (len + 2) (k + 1)
      (Nat.succ_lt_succ (Nat.lt_of_lt_of_le hk (Nat.le_succ len))),
    segPolys_at V mLo (len + 2) (k + 2)
      (Nat.succ_lt_succ (Nat.succ_lt_succ hk))] at hread
  exact hread

/-- The clearing lift at a vacancy-aligned polynomial: one further
clearing power multiplies the cleared read by the clearing. -/
private theorem evalPowLift (p : poly.Poly) (ln : BPair) (ed : Pos)
    (K : Nat)
    (hvac : ∀ j, K + 1 ≤ j →
      (ground.getAt BPair.unit p j).oneValue BPair.unit) :
    (poly.evalClear p ln ed (K + 1)).oneValue
      (BPair.ofPos ed * poly.evalClear p ln ed K) := by
  have hcap : (poly.vnorm p).length ≤ K + 1 := poly.vnormLen_cap hvac
  have he1 : K + 1 - K = 1 :=
    ground.addCancelL K (ground.natAddSubCancel (Nat.le_succ K))
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (poly.evalClear_congr (poly.vnorm_ov p) ln ed (K + 1))) ?_
  refine BPair.oneValue_trans
    (poly.evalClear_pow (poly.vnorm p) ln ed (K + 1) K hcap
      (Nat.le_succ K)) ?_
  rw [he1]
  exact BPair.mul_congr (ground.bpow_one_read (BPair.ofPos ed))
    (poly.evalClear_congr (poly.vnorm_ov p) ln ed K)

/-- The cleared evaluation at one clearing power up: the clearing's
own multiple of the read at the stated power, the keys inside it. -/
private theorem evalClear_up (q : poly.Poly) (en ed : Pos) (L : Nat)
    (hq : q.length ≤ L + 1) :
    (poly.evalClear q (BPair.ofPos en) ed (L + 1)).oneValue
      (BPair.ofPos ed * poly.evalClear q (BPair.ofPos en) ed L) :=
  evalPowLift q (BPair.ofPos en) ed L (fun j hj =>
    BPair.oneValue_of_eq
      (ground.getAt_over BPair.unit q j (Nat.le_trans hq hj)))

/-- The clearing's two-power lift: two clearing scales enter at the
shortened list's own read, the one-power lift twice. -/
private theorem evalClear_up2 (q : poly.Poly) (en ed : Pos) (L : Nat)
    (hq : q.length ≤ L + 1) :
    (poly.evalClear q (BPair.ofPos en) ed (L + 2)).oneValue
      (BPair.ofPos ed * (BPair.ofPos ed
        * poly.evalClear q (BPair.ofPos en) ed L)) :=
  BPair.oneValue_trans
    (evalClear_up q en ed (L + 1) (Nat.le_succ_of_le hq))
    (BPair.mul_congr (BPair.oneValue_refl _) (evalClear_up q en ed L hq))

/-- The comparison read unpacks to clause (i)'s termwise comparison at
the cleared evaluations — the bond weight the clearing constants'
product at the scale's square, the diagonal's evaluation at its own
clearing. -/
theorem termRead_read {V : poly.PPoly × poly.PPoly} {r qn qd : Nat}
    {en ed : Pos} {K m : Nat}
    (hsh : profShape V K)
    (h : termRead V r qn qd en ed K m) :
    BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
        * (poly.evalClear (depthPoly V m) (BPair.ofPos en) ed K
           + poly.evalClear (depthPoly V (m + 2)) (BPair.ofPos en) ed K)
      ≤ poly.evalClear (diagPoly r qn qd (m + 1)) (BPair.ofPos en) ed 2
        * poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed K := by
  have hP : (poly.evalClear
      (poly.mul (diagPoly r qn qd (m + 1)) (depthPoly V (m + 1)))
      (BPair.ofPos en) ed (K + 2)).oneValue
      (poly.evalClear (diagPoly r qn qd (m + 1)) (BPair.ofPos en) ed 2
        * poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed K) := by
    rw [show K + 2 = 2 + K from Nat.add_comm K 2]
    exact poly.evalClear_mul _ _ _ _ 2 K (Nat.le_refl 3)
      (depthPoly_ble hsh (m + 1))
  have hN : (poly.evalClear
      (poly.neg (poly.scaleP (BPair.ofNat ((r + 1) * qd))
        (poly.add (depthPoly V m) (depthPoly V (m + 2)))))
      (BPair.ofPos en) ed (K + 2)).oneValue
      (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
        * (poly.evalClear (depthPoly V m) (BPair.ofPos en) ed K
           + poly.evalClear (depthPoly V (m + 2))
             (BPair.ofPos en) ed K)).swap := by
    refine BPair.oneValue_trans (poly.evalClear_neg _ _ _ _) ?_
    refine ground.swap_congr ?_
    refine BPair.oneValue_trans (poly.evalClear_scaleP _ _ _ _ _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
          (BPair.add_congr (evalClear_up2 _ en ed K (depthPoly_ble hsh m))
            (evalClear_up2 _ en ed K
              (depthPoly_ble hsh (m + 2)))))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.left_distrib (BPair.ofPos ed),
      ← BPair.left_distrib (BPair.ofPos ed),
      ← BPair.mul_assoc (BPair.ofNat ((r + 1) * qd)) (BPair.ofPos ed),
      ← BPair.mul_assoc (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed)
        (BPair.ofPos ed)]
  exact ground.leB_of_unit_add
    (ground.leB_congr_right
      (BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
        (BPair.add_congr hP hN)) h)

/-- The supersolution clears the pivots — clause (ii)'s read feeding
clause (i) at the cleared instantiation, the bond weight the clearing
constants' product at the scale's square, the diagonal and the
profile at their cleared evaluations along the segment. -/
theorem super_clears (V : poly.PPoly × poly.PPoly) (r qn qd : Nat)
    (en ed : Pos) (K mLo len : Nat) (D : Nat → BPair)
    (hqd : 0 < qd)
    (hsr : superRead V r qn qd en ed K mLo len)
    (hrec : ∀ k, k < len →
      (D (k + 2)
          + BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
            * (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed
              * BPair.ofPos ed) * D k).oneValue
        (poly.evalClear (diagPoly r qn qd (mLo + k + 1))
            (BPair.ofPos en) ed 2 * D (k + 1)))
    (h0 : BPair.unit < D 0)
    (hseed : BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
        * (D 0 * poly.evalClear (depthPoly V (mLo + 1))
            (BPair.ofPos en) ed K)
      ≤ D 1 * poly.evalClear (depthPoly V mLo) (BPair.ofPos en) ed K) :
    ∀ k, k ≤ len →
      BPair.unit < D (k + 1)
      ∧ BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
          * (D k * poly.evalClear (depthPoly V (mLo + k + 1))
              (BPair.ofPos en) ed K)
        ≤ D (k + 1) * poly.evalClear (depthPoly V (mLo + k))
            (BPair.ofPos en) ed K :=
  pivot_clears
    (fun j => poly.evalClear (diagPoly r qn qd (mLo + j))
      (BPair.ofPos en) ed 2)
    (fun j => poly.evalClear (depthPoly V (mLo + j)) (BPair.ofPos en) ed K)
    D (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed) len
    (ground.unitLtMul
      (ground.unitLtMul (unitLtNat (Nat.mul_pos (Nat.succ_pos r) hqd))
        (ground.unitLtOfPos ed))
      (ground.unitLtOfPos ed))
    hrec
    (fun k hk => termRead_read hsr.1 (superRead_term hsr k hk))
    (fun k hk => superRead_pos hsr k (Nat.lt_succ_of_le hk))
    h0 hseed

/-! `lem:cornerpivot`(ii)'s canonical carrier algebra: the profile
operations at the kernel `u² = ηs`, and their collapse bridges —
every operation of the canonical carrier reads the balance-pair
polynomials' own at each depth. -/

/-- The `ηs`-multiple at the canonical carrier: the outer key up one
at the vacant head, the inner keys up one. -/
def esMul (P : poly.PPoly) : poly.PPoly :=
  ([] : poly.Poly) :: P.map (poly.shiftUp 1)

/-- The profile sum, slabwise. -/
def profAdd (V W : poly.PPoly × poly.PPoly) : poly.PPoly × poly.PPoly :=
  (poly.padd V.1 W.1, poly.padd V.2 W.2)

/-- The profile's memberwise swap, slabwise. -/
def profNeg (V : poly.PPoly × poly.PPoly) : poly.PPoly × poly.PPoly :=
  (V.1.map poly.neg, V.2.map poly.neg)

/-- The profile scaled at a stated count, slabwise. -/
def profScale (c : Nat) (V : poly.PPoly × poly.PPoly) :
    poly.PPoly × poly.PPoly :=
  (V.1.map (poly.scaleP (BPair.ofNat c)),
   V.2.map (poly.scaleP (BPair.ofNat c)))

/-- The reduced product at the kernel `u² = ηs`: the u¹-slabs'
product re-enters the u⁰-slab at the `ηs`-multiple. -/
def profMul (V W : poly.PPoly × poly.PPoly) : poly.PPoly × poly.PPoly :=
  (poly.padd (poly.pmul V.1 W.1) (esMul (poly.pmul V.2 W.2)),
   poly.padd (poly.pmul V.1 W.2) (poly.pmul V.2 W.1))

/-- The shifted square scale `s + 2u + η`, the canonical form of the
successor depth's square-scale read. -/
def sh1 : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 1], [BPair.ofNat 1]], [[BPair.ofNat 2]])

/-- The shifted scale read `u + η`, the successor depth's own. -/
def u1 : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 1]], [[BPair.ofNat 1]])

/-- One slab's substitution walk: the Horner fold of the inner
polynomials against the shifted square scale's powers. -/
def shGo : poly.PPoly → poly.PPoly × poly.PPoly
  | [] => (([] : poly.PPoly), ([] : poly.PPoly))
  | p :: t => profAdd ([p], ([] : poly.PPoly)) (profMul sh1 (shGo t))

/-- The depth shift at the canonical carrier: each slab's
substitution walk, the u¹-slab's against the shifted scale read. -/
def profShift (V : poly.PPoly × poly.PPoly) : poly.PPoly × poly.PPoly :=
  profAdd (shGo V.1) (profMul u1 (shGo V.2))

/-- The diagonal's canonical form at a rate: the band read's
clearing at the origin, the rate's balance partner at the scale
key, and the well's electric member on the square-scale and scale
keys. -/
def diagProf (r qn qd : Nat) : poly.PPoly × poly.PPoly :=
  ([[BPair.ofNat (2 * ((r + 1) * qd)), (BPair.ofNat ((r + 1) * qn)).swap],
    [BPair.unit, BPair.ofNat (4 * qd)]],
   [[BPair.unit, BPair.ofNat (4 * qd * r)]])

/-- The termwise comparison as one canonical object at a rate: the
shifted diagonal's multiple of the shifted profile against the
cleared neighbor sum. -/
def termProf (V : poly.PPoly × poly.PPoly) (r qn qd : Nat) :
    poly.PPoly × poly.PPoly :=
  profAdd (profMul (profShift (diagProf r qn qd)) (profShift V))
    (profNeg (profScale ((r + 1) * qd)
      (profAdd V (profShift (profShift V)))))

/-! `lem:cornerpivot`'s box device: the certificate data that price a
canonical object's collapse from below on a stated box of square
scales — the scale-free part's chained priced side read against the
scale-carrying terms' caps. -/

/-- The scale-free part: the inners' origin coefficients at the
outer keys, one polynomial in the square scale. -/
def profBase (V : poly.PPoly × poly.PPoly) : poly.Poly :=
  V.1.map (fun p => ground.getAt BPair.unit p 0)

/-- One inner list's coefficient fold at the ceiling pair, cleared
at the stated power: the magnitudes against the ceiling's first
member's powers, the second member's clearing the complement —
`Σ_c |p_c| e0n^c e0d^(K-c)`, one pass at two running accumulators
with the powers shared (`windowsep.foldPow`). -/
def capF (e0n : BPair) (e0d : Pos) (K : Nat) (p : poly.Poly) : BPair :=
  windowsep.foldPow
    ((List.range (K + 1)).map (fun c =>
      windowsep.mag (ground.getAt BPair.unit p c)))
    e0n (BPair.ofPos e0d)

/-- The slab cap at the ceiling pair: the inner folds' Horner
against the square-scale cap, one clearing power shared. -/
def capS (e0n : BPair) (e0d : Pos) (shB : BPair) (K : Nat) :
    poly.PPoly → BPair
  | [] => BPair.unit
  | p :: t => capF e0n e0d K p + shB * capS e0n e0d shB K t

/-- The chained priced side read: the upper side at every point
between consecutive cuts, one priced read per piece — the wide
segment's cover, `lem:cellcount`'s chained subintervals at the one
polynomial. -/
def chainRead (p : poly.Poly) (bN bD : BPair) : List CPair → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => stage.keepUpper p a b bN bD ∧ chainRead p bN bD (b :: t)

def decChainRead (p : poly.Poly) (bN bD : BPair) :
    ∀ cuts : List CPair, Decidable (chainRead p bN bD cuts)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | _ :: b :: t =>
    @instDecidableAnd _ _ inferInstance (decChainRead p bN bD (b :: t))

instance (p : poly.Poly) (bN bD : BPair) (cuts : List CPair) :
    Decidable (chainRead p bN bD cuts) :=
  decChainRead p bN bD cuts

/-- The two-armed chained read: each piece keeps the upper side at
one of the two stated polynomials, each piece at its one
comparison's kept side. -/
def chainRead2 (p q : poly.Poly) (bN bD : BPair) : List CPair → Prop
  | [] => True
  | [_] => True
  | a :: b :: t =>
    (stage.keepUpper p a b bN bD ∨ stage.keepUpper q a b bN bD)
    ∧ chainRead2 p q bN bD (b :: t)

def decChainRead2 (p q : poly.Poly) (bN bD : BPair) :
    ∀ cuts : List CPair, Decidable (chainRead2 p q bN bD cuts)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | _ :: b :: t =>
    @instDecidableAnd _ _ inferInstance (decChainRead2 p q bN bD (b :: t))

instance (p q : poly.Poly) (bN bD : BPair) (cuts : List CPair) :
    Decidable (chainRead2 p q bN bD cuts) :=
  decChainRead2 p q bN bD cuts

/-- The two slabs' scale-order polynomials in the square scale:
the u-slab's origin coefficients and the scale-free slab's
scale-key coefficients — the remainder's own origins, and the
graded device's leading pair. -/
def profBaseU (V : poly.PPoly × poly.PPoly) : poly.Poly :=
  V.2.map (fun p => ground.getAt BPair.unit p 0)

def profLin (V : poly.PPoly × poly.PPoly) : poly.Poly :=
  V.1.map (fun p => ground.getAt BPair.unit p 1)

set_option genInjectivity false in
/-- The box certificate: the box's composite endpoints with the
floor chain's interior cut list and the two remainder arms' own,
the priced side reads' bound, the box top's cleared read, the four
floors, and the shape clearing. -/
structure BoxCert where
  lo : CPair
  hi : CPair
  cuts : List CPair
  cutsL : List CPair
  cutsU : List CPair
  bN : BPair
  bD : BPair
  shB : BPair
  f1L : BPair
  f1D : BPair
  f2L : BPair
  f2D : BPair
  K : Nat

/-- The box device's read at the cleared ceiling: the shape at the
clearing, the box top's cleared read, the scale-free part clearing
the four floors' join on the box at the chained priced side read,
the remainder's origin coefficients read on the box at the chained
device — the scale coefficients above the first leading floor's
balance partner, the u-slab's origins at their squared price
against the second's square, the square scale the box's own
coordinate, each comparison's floor at or beyond the sum's unit —
and the deeper coefficients' two fold comparisons at the ceiling's
powers through the box top's cleared read, the squared one's floor
at or beyond the sum's unit, the ceiling's second member's powers
clearing each comparison's other side. -/
def boxRead (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : BoxCert) : Prop :=
  profShape V C.K
  ∧ C.hi ≤ stage.ofB C.shB
  ∧ BPair.unit ≤ C.f2L
  ∧ BPair.unit ≤ C.f2D
  ∧ chainRead (poly.add (profBase V)
      (poly.neg [C.f1L + C.f1D + (C.f2L + C.f2D)]))
      C.bN C.bD (C.lo :: C.cuts ++ [C.hi])
  ∧ BPair.unit ≤ C.f1L
  ∧ chainRead (poly.add [C.f1L * BPair.ofPos e0d]
      (poly.scaleP e0n (profLin V)))
      C.bN C.bD (C.lo :: C.cutsL ++ [C.hi])
  ∧ chainRead (poly.add [C.f2L * C.f2L * BPair.ofPos e0d]
      (poly.neg (poly.scaleP e0n
        (poly.shiftUp 1 (poly.mul (profBaseU V) (profBaseU V))))))
      C.bN C.bD (C.lo :: C.cutsU ++ [C.hi])
  ∧ e0n * (e0n * capS e0n e0d C.shB C.K (V.1.map (List.drop 2)))
      ≤ C.f1D * BPair.ofPos (Pos.powC e0d (C.K + 2))
  ∧ e0n * (C.shB
        * ((e0n * capS e0n e0d C.shB C.K (V.2.map (List.drop 1)))
          * (e0n * capS e0n e0d C.shB C.K (V.2.map (List.drop 1)))))
      ≤ C.f2D * C.f2D * BPair.ofPos (Pos.powC e0d (2 * C.K + 3))

instance (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : BoxCert) : Decidable (boxRead V e0n e0d C) :=
  inferInstanceAs
    (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The scale-tail read of one scale polynomial at the cleared
ceiling: the origin coefficient above the sum's unit and clearing
the tail's priced fold at the ceiling's first member, the ceiling's
second member's powers clearing the comparison's other side — the
read at every scale at or below the ceiling. -/
def lowRead (p : poly.Poly) (e0n : BPair) (e0d : Pos) (K : Nat) : Prop :=
  BPair.unit < ground.getAt BPair.unit p 0
  ∧ e0n * capF e0n e0d K (List.drop 1 p)
      < ground.getAt BPair.unit p 0 * BPair.ofPos (Pos.powC e0d (K + 1))

instance (p : poly.Poly) (e0n : BPair) (e0d : Pos) (K : Nat) :
    Decidable (lowRead p e0n e0d K) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The ceiling power's computing read at the balance carrier: the
value sites' literal power against the display's defining fold. -/
private theorem powCRead (d : Pos) (n : Nat) :
    (BPair.ofPos (Pos.powC d n)).oneValue
      (ground.bpow (BPair.ofPos d) n) := by
  rw [Pos.powC_eq]
  exact ground.ofPos_pow d n

/-- The step clearance between two composite tops at the cleared
ceiling: the outer clears the inner by at least the ceiling, and the
square-scale step's square at the inner top clears into the gap's
shifted square — so a depth inside the inner top steps to a square
scale inside the outer. -/
def stepClear (a b : CPair) (e0n : BPair) (e0d : Pos) : Prop :=
  a + (⟨e0n, e0d⟩ : CPair) ≤ b
  ∧ stage.ofB (BPair.ofNat 4) * (a * ⟨e0n, e0d⟩)
      ≤ (b + CPair.swap a + CPair.swap (⟨e0n, e0d⟩ : CPair))
        * (b + CPair.swap a + CPair.swap (⟨e0n, e0d⟩ : CPair))

instance (a b : CPair) (e0n : BPair) (e0d : Pos) :
    Decidable (stepClear a b e0n e0d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! The slab walk's exchange kit: the key shift and the rescaling
commute, the shift passes the product on its own factor, and the
memberwise swap passes the rescaling. -/

/-- The rescaling passes the key shift. -/
private theorem scaleP_shift (c : BPair) : ∀ (b : Nat) (p : poly.Poly),
    poly.oneValue (poly.scaleP c (poly.shiftUp b p))
      (poly.shiftUp b (poly.scaleP c p))
  | 0, _ => poly.oneValue_refl _
  | b + 1, p =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_unit c),
     scaleP_shift c b p⟩

/-- Two rescalings exchange at the scales' commuting product. -/
private theorem scaleP_swap (c d : BPair) (p : poly.Poly) :
    poly.oneValue (poly.scaleP c (poly.scaleP d p))
      (poly.scaleP d (poly.scaleP c p)) :=
  poly.oneValue_trans (poly.scaleP_mul c d p)
    (poly.oneValue_trans
      (poly.scaleP_congr (BPair.oneValue_of_eq (BPair.mul_comm c d)) p)
      (poly.oneValue_symm (poly.scaleP_mul d c p)))

/-- The key shift passes the product on the other factor. -/
private theorem mul_shiftL (n : Nat) (p q : poly.Poly) :
    poly.oneValue (poly.mul (poly.shiftUp n p) q)
      (poly.shiftUp n (poly.mul p q)) :=
  poly.oneValue_trans (poly.mul_comm (poly.shiftUp n p) q)
    (poly.oneValue_trans (poly.mul_shiftUp q n p)
      (poly.shiftUp_ov n (poly.mul_comm q p)))

/-! The slab walk's own reads: the walk from a stated shift and
weight is the nought walk shifted and rescaled, and the walk passes
the outer sum, the slabwise rescaling and the slabwise swap. -/

/-- The slab walk at a stated shift and weight is the nought walk's
own shift and rescaling. -/
private theorem slabGo_norm (mm : Nat) : ∀ (b w : Nat) (P : poly.PPoly),
    poly.oneValue (slabGo mm b w P)
      (poly.shiftUp b (poly.scaleP (BPair.ofNat w) (slabGo mm 0 1 P)))
  | b, w, [] => poly.unitTail_shiftUp b (poly.scaleP_unitTail _ [] trivial)
  | b, w, p :: t => by
    show poly.oneValue
      (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
        (slabGo mm (b + 1) (w * mm) t))
      (poly.shiftUp b (poly.scaleP (BPair.ofNat w)
        (poly.add (poly.scaleP (BPair.ofNat 1) p) (slabGo mm 1 (1 * mm) t))))
    refine poly.oneValue_symm (poly.oneValue_trans
      (poly.shiftUp_ov b (poly.scaleP_sum (BPair.ofNat w) _ _)) ?_)
    refine poly.oneValue_trans (poly.shiftUp_add b _ _) ?_
    refine poly.add_congr ?_ ?_
    · exact poly.shiftUp_ov b
        (poly.oneValue_trans
          (poly.oneValue_scaleP (BPair.ofNat w) (poly.scaleP_one p))
          (poly.oneValue_refl _))
    · refine poly.oneValue_symm (poly.oneValue_trans
        (slabGo_norm mm (b + 1) (w * mm) t) ?_)
      refine poly.oneValue_symm ?_
      refine poly.oneValue_trans
        (poly.shiftUp_ov b (poly.oneValue_scaleP (BPair.ofNat w)
          (slabGo_norm mm 1 (1 * mm) t))) ?_
      refine poly.oneValue_trans
        (poly.shiftUp_ov b (scaleP_shift (BPair.ofNat w) 1 _)) ?_
      rw [poly.shiftUp_shiftUp b 1 (poly.scaleP (BPair.ofNat w)
        (poly.scaleP (BPair.ofNat (1 * mm)) (slabGo mm 0 1 t)))]
      refine poly.shiftUp_ov (b + 1) ?_
      refine poly.oneValue_trans (poly.scaleP_mul _ _ _) ?_
      refine poly.scaleP_congr ?_ _
      exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_of_eq (congrArg BPair.ofNat (Nat.one_mul mm))))
        (BPair.oneValue_symm (BPair.ofNat_mul w mm))

/-- The slab walk passes the outer sum. -/
private theorem slabGo_padd (mm : Nat) : ∀ (b w : Nat) (P Q : poly.PPoly),
    poly.oneValue (slabGo mm b w (poly.padd P Q))
      (poly.add (slabGo mm b w P) (slabGo mm b w Q))
  | _, _, [], _ => poly.oneValue_refl _
  | _, _, _ :: _, [] => poly.oneValue_of_eq (poly.add_nil _).symm
  | b, w, p :: P, q :: Q => by
    show poly.oneValue
      (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w)
          (poly.add p q)))
        (slabGo mm (b + 1) (w * mm) (poly.padd P Q)))
      (poly.add
        (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
          (slabGo mm (b + 1) (w * mm) P))
        (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) q))
          (slabGo mm (b + 1) (w * mm) Q)))
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.oneValue_trans
          (poly.shiftUp_ov b (poly.scaleP_sum (BPair.ofNat w) p q))
          (poly.shiftUp_add b _ _))
        (slabGo_padd mm (b + 1) (w * mm) P Q)) ?_
    exact poly.add_shuffle _ _ _ _

/-- The slab walk passes a slabwise transform whose reads exchange
with the walk's own step: the transform's read at the vacant walk,
its sum read, and its exchange with the shifted rescaling. -/
private theorem slabGo_map (mm : Nat) (T : poly.Poly → poly.Poly)
    (hnil : poly.oneValue ([] : poly.Poly) (T []))
    (hsum : ∀ x y : poly.Poly,
      poly.oneValue (T (poly.add x y)) (poly.add (T x) (T y)))
    (hexch : ∀ (b w : Nat) (p : poly.Poly),
      poly.oneValue (T (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p)))
        (poly.shiftUp b (poly.scaleP (BPair.ofNat w) (T p)))) :
    ∀ (b w : Nat) (P : poly.PPoly),
    poly.oneValue (slabGo mm b w (P.map T)) (T (slabGo mm b w P))
  | _, _, [] => hnil
  | b, w, p :: t => by
    show poly.oneValue
      (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) (T p)))
        (slabGo mm (b + 1) (w * mm) (t.map T)))
      (T (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
        (slabGo mm (b + 1) (w * mm) t)))
    refine poly.oneValue_symm (poly.oneValue_trans (hsum _ _) ?_)
    exact poly.add_congr
      (hexch b w p)
      (poly.oneValue_symm
        (slabGo_map mm T hnil hsum hexch (b + 1) (w * mm) t))

/-- The slab walk passes the slabwise rescaling. -/
private theorem slabGo_scaleMap (mm : Nat) (c : BPair) (b w : Nat)
    (P : poly.PPoly) :
    poly.oneValue (slabGo mm b w (P.map (poly.scaleP c)))
      (poly.scaleP c (slabGo mm b w P)) :=
  slabGo_map mm (poly.scaleP c) (poly.oneValue_refl [])
    (poly.scaleP_sum c)
    (fun b w p => poly.oneValue_trans (scaleP_shift c b _)
      (poly.shiftUp_ov b (scaleP_swap c (BPair.ofNat w) p)))
    b w P

/-- The slab walk passes the slabwise memberwise swap. -/
private theorem slabGo_negMap (mm : Nat) (b w : Nat) (P : poly.PPoly) :
    poly.oneValue (slabGo mm b w (P.map poly.neg))
      (poly.neg (slabGo mm b w P)) :=
  slabGo_map mm poly.neg (poly.oneValue_refl [])
    (fun x y => poly.oneValue_of_eq (poly.neg_sum x y))
    (fun b w p => by
      rw [poly.neg_shiftUp]
      exact poly.shiftUp_ov b
        (poly.oneValue_symm (poly.scaleP_neg (BPair.ofNat w) p)))
    b w P

/-! The collapse bridges: the canonical operations' per-depth
collapses are the balance-pair polynomials' own. -/

/-- The profile sum's collapse is the collapses' sum. -/
theorem depthPoly_profAdd (V W : poly.PPoly × poly.PPoly) (m : Nat) :
    poly.oneValue (depthPoly (profAdd V W) m)
      (poly.add (depthPoly V m) (depthPoly W m)) :=
  poly.oneValue_trans
    (poly.add_congr (slabGo_padd (m * m) 0 1 V.1 W.1)
      (slabGo_padd (m * m) 1 m V.2 W.2))
    (poly.add_shuffle _ _ _ _)

/-- The scaled profile's collapse is the collapse's rescaling. -/
theorem depthPoly_profScale (V : poly.PPoly × poly.PPoly) (c m : Nat) :
    poly.oneValue (depthPoly (profScale c V) m)
      (poly.scaleP (BPair.ofNat c) (depthPoly V m)) :=
  poly.oneValue_trans
    (poly.add_congr (slabGo_scaleMap (m * m) (BPair.ofNat c) 0 1 V.1)
      (slabGo_scaleMap (m * m) (BPair.ofNat c) 1 m V.2))
    (poly.oneValue_symm (poly.scaleP_sum (BPair.ofNat c) _ _))

/-- The swapped profile's collapse is the collapse's memberwise
swap. -/
theorem depthPoly_profNeg (V : poly.PPoly × poly.PPoly) (m : Nat) :
    poly.oneValue (depthPoly (profNeg V) m) (poly.neg (depthPoly V m)) := by
  show poly.oneValue
    (poly.add (slabGo (m * m) 0 1 (V.1.map poly.neg))
      (slabGo (m * m) 1 m (V.2.map poly.neg)))
    (poly.neg (poly.add (slabGo (m * m) 0 1 V.1) (slabGo (m * m) 1 m V.2)))
  rw [poly.neg_sum]
  exact poly.add_congr (slabGo_negMap (m * m) 0 1 V.1)
    (slabGo_negMap (m * m) 1 m V.2)


/-! The product's exchange kit: the key shift and the rescaling ride
either factor of the convolution. -/

/-- The rescaling passes the product on the other factor. -/
private theorem mul_scaleR (c : BPair) (p q : poly.Poly) :
    poly.oneValue (poly.mul p (poly.scaleP c q))
      (poly.scaleP c (poly.mul p q)) :=
  poly.oneValue_trans (poly.mul_congr p (poly.scaleP_single c q))
    (poly.oneValue_trans (poly.oneValue_symm (poly.mul_assoc p q [c]))
      (poly.oneValue_symm (poly.scaleP_single c (poly.mul p q))))

/-- The rescaling passes the product on its own factor. -/
private theorem mul_scaleL (c : BPair) (p q : poly.Poly) :
    poly.oneValue (poly.mul (poly.scaleP c p) q)
      (poly.scaleP c (poly.mul p q)) :=
  poly.oneValue_trans (poly.mul_comm (poly.scaleP c p) q)
    (poly.oneValue_trans (mul_scaleR c q p)
      (poly.oneValue_scaleP c (poly.mul_comm q p)))

/-- The scale key's one-member product is the key shift of the
rescaling. -/
private theorem mul_scaleKey (c : BPair) (X : poly.Poly) :
    poly.oneValue (poly.mul [BPair.unit, c] X)
      (poly.shiftUp 1 (poly.scaleP c X)) :=
  poly.oneValue_trans (mul_shiftL 1 [c] X)
    (poly.shiftUp_ov 1
      (poly.oneValue_trans (poly.mul_comm [c] X)
        (poly.oneValue_symm (poly.scaleP_single c X))))

/-- The slab walk passes the slabwise product against a stated
factor. -/
private theorem slabGo_mulMap (mm : Nat) (c : poly.Poly) (b w : Nat)
    (Q : poly.PPoly) :
    poly.oneValue (slabGo mm b w (Q.map (poly.mul c)))
      (poly.mul c (slabGo mm b w Q)) :=
  slabGo_map mm (poly.mul c) (poly.mul_nil c)
    (poly.mul_sum c)
    (fun b w q => poly.oneValue_trans (poly.mul_shiftUp c b _)
      (poly.shiftUp_ov b (mul_scaleR (BPair.ofNat w) c q)))
    b w Q

/-- The slab walk passes the slabwise key shift. -/
private theorem slabGo_shiftMap (mm k : Nat) (b w : Nat)
    (P : poly.PPoly) :
    poly.oneValue (slabGo mm b w (P.map (poly.shiftUp k)))
      (poly.shiftUp k (slabGo mm b w P)) :=
  slabGo_map mm (poly.shiftUp k) (poly.unitTail_shiftUp k trivial)
    (poly.shiftUp_add k)
    (fun b w p => by
      rw [poly.shiftUp_shiftUp k b (poly.scaleP (BPair.ofNat w) p),
        Nat.add_comm k b,
        ← poly.shiftUp_shiftUp b k (poly.scaleP (BPair.ofNat w) p)]
      exact poly.shiftUp_ov b
        (poly.oneValue_symm (scaleP_shift (BPair.ofNat w) k p)))
    b w P

/-- The nought slab walk passes the outer convolution: the collapse
is multiplicative at the square scale. -/
private theorem slabGo_pmul (mm : Nat) : ∀ P Q : poly.PPoly,
    poly.oneValue (slabGo mm 0 1 (poly.pmul P Q))
      (poly.mul (slabGo mm 0 1 P) (slabGo mm 0 1 Q))
  | [], _ => trivial
  | c :: P, Q => by
    show poly.oneValue
      (slabGo mm 0 1 (poly.padd (Q.map (poly.mul c))
        (([] : poly.Poly) :: poly.pmul P Q)))
      (poly.mul
        (poly.add (poly.scaleP (BPair.ofNat 1) c)
          (slabGo mm 1 (1 * mm) P))
        (slabGo mm 0 1 Q))
    refine poly.oneValue_trans
      (slabGo_padd mm 0 1 (Q.map (poly.mul c))
        (([] : poly.Poly) :: poly.pmul P Q)) ?_
    refine poly.oneValue_trans
      (poly.add_congr (slabGo_mulMap mm c 0 1 Q)
        (show poly.oneValue
            (slabGo mm 0 1 (([] : poly.Poly) :: poly.pmul P Q))
            (poly.shiftUp 1 (poly.scaleP (BPair.ofNat (1 * mm))
              (poly.mul (slabGo mm 0 1 P) (slabGo mm 0 1 Q))))
          from poly.oneValue_trans
            (slabGo_norm mm 1 (1 * mm) (poly.pmul P Q))
            (poly.shiftUp_ov 1 (poly.oneValue_scaleP _
              (slabGo_pmul mm P Q))))) ?_
    refine poly.oneValue_symm ?_
    refine poly.oneValue_trans
      (poly.sum_mul (poly.scaleP (BPair.ofNat 1) c)
        (slabGo mm 1 (1 * mm) P) (slabGo mm 0 1 Q)) ?_
    refine poly.add_congr ?_ ?_
    · exact poly.mul_congr_left (poly.scaleP_one c) (slabGo mm 0 1 Q)
    · refine poly.oneValue_trans
        (poly.mul_congr_left (slabGo_norm mm 1 (1 * mm) P)
          (slabGo mm 0 1 Q)) ?_
      refine poly.oneValue_trans (mul_shiftL 1 _ _) ?_
      exact poly.shiftUp_ov 1 (mul_scaleL (BPair.ofNat (1 * mm)) _ _)

/-- The `ηs`-multiple's nought slab walk is the walk shifted two
scale keys at the square-scale weight. -/
private theorem slabGo_esMul (mm : Nat) (R : poly.PPoly) :
    poly.oneValue (slabGo mm 0 1 (esMul R))
      (poly.shiftUp 2 (poly.scaleP (BPair.ofNat mm)
        (slabGo mm 0 1 R))) := by
  refine poly.oneValue_trans
    (show poly.oneValue (slabGo mm 0 1 (esMul R))
        (slabGo mm 1 (1 * mm) (R.map (poly.shiftUp 1)))
      from poly.oneValue_refl _) ?_
  refine poly.oneValue_trans
    (slabGo_norm mm 1 (1 * mm) (R.map (poly.shiftUp 1))) ?_
  refine poly.oneValue_trans
    (poly.shiftUp_ov 1 (poly.oneValue_scaleP (BPair.ofNat (1 * mm))
      (slabGo_shiftMap mm 1 0 1 R))) ?_
  refine poly.oneValue_trans
    (poly.shiftUp_ov 1 (scaleP_shift (BPair.ofNat (1 * mm)) 1
      (slabGo mm 0 1 R))) ?_
  rw [poly.shiftUp_shiftUp 1 1 (poly.scaleP (BPair.ofNat (1 * mm))
    (slabGo mm 0 1 R)), Nat.one_mul mm]
  exact poly.oneValue_refl _

/-- The u-slab's product: two scale-key shifts collect at the joined
key and the weights' product. -/
private theorem mul_uu (a b : Nat) (X Y : poly.Poly) :
    poly.oneValue
      (poly.mul (poly.shiftUp 1 (poly.scaleP (BPair.ofNat a) X))
        (poly.shiftUp 1 (poly.scaleP (BPair.ofNat b) Y)))
      (poly.shiftUp 2 (poly.scaleP (BPair.ofNat (a * b))
        (poly.mul X Y))) := by
  refine poly.oneValue_trans (mul_shiftL 1 _ _) ?_
  refine poly.oneValue_trans (poly.shiftUp_ov 1 (poly.mul_shiftUp _ 1 _)) ?_
  rw [poly.shiftUp_shiftUp 1 1
    (poly.mul (poly.scaleP (BPair.ofNat a) X)
      (poly.scaleP (BPair.ofNat b) Y))]
  refine poly.shiftUp_ov 2 ?_
  refine poly.oneValue_trans
    (mul_scaleL (BPair.ofNat a) X (poly.scaleP (BPair.ofNat b) Y)) ?_
  refine poly.oneValue_trans
    (poly.oneValue_scaleP (BPair.ofNat a)
      (mul_scaleR (BPair.ofNat b) X Y)) ?_
  refine poly.oneValue_trans
    (poly.scaleP_mul (BPair.ofNat a) (BPair.ofNat b) (poly.mul X Y)) ?_
  exact poly.scaleP_congr
    (BPair.oneValue_symm (BPair.ofNat_mul a b)) _

/-- The reduced product's collapse is the collapses' product, the
kernel `u² = ηs` reading the square scale at the depth. -/
theorem depthPoly_profMul (V W : poly.PPoly × poly.PPoly) (m : Nat) :
    poly.oneValue (depthPoly (profMul V W) m)
      (poly.mul (depthPoly V m) (depthPoly W m)) := by
  have hV : poly.oneValue (depthPoly V m)
      (poly.add (slabGo (m * m) 0 1 V.1)
        (poly.shiftUp 1 (poly.scaleP (BPair.ofNat m)
          (slabGo (m * m) 0 1 V.2)))) :=
    poly.add_congr (poly.oneValue_refl _) (slabGo_norm (m * m) 1 m V.2)
  have hW : poly.oneValue (depthPoly W m)
      (poly.add (slabGo (m * m) 0 1 W.1)
        (poly.shiftUp 1 (poly.scaleP (BPair.ofNat m)
          (slabGo (m * m) 0 1 W.2)))) :=
    poly.add_congr (poly.oneValue_refl _) (slabGo_norm (m * m) 1 m W.2)
  refine poly.oneValue_trans ?_
    (poly.oneValue_symm (poly.oneValue_trans
      (poly.mul_congr_left hV (depthPoly W m))
      (poly.mul_congr _ hW)))
  refine poly.oneValue_trans
    (show poly.oneValue (depthPoly (profMul V W) m)
        (poly.add
          (poly.add (slabGo (m * m) 0 1 (poly.pmul V.1 W.1))
            (slabGo (m * m) 0 1 (esMul (poly.pmul V.2 W.2))))
          (poly.add (slabGo (m * m) 1 m (poly.pmul V.1 W.2))
            (slabGo (m * m) 1 m (poly.pmul V.2 W.1))))
      from poly.add_congr
        (slabGo_padd (m * m) 0 1 _ _)
        (slabGo_padd (m * m) 1 m _ _)) ?_
  refine poly.oneValue_trans
    (poly.add_congr
      (poly.add_congr (slabGo_pmul (m * m) V.1 W.1)
        (poly.oneValue_trans (slabGo_esMul (m * m) (poly.pmul V.2 W.2))
          (poly.shiftUp_ov 2 (poly.oneValue_scaleP _
            (slabGo_pmul (m * m) V.2 W.2)))))
      (poly.add_congr
        (poly.oneValue_trans (slabGo_norm (m * m) 1 m (poly.pmul V.1 W.2))
          (poly.shiftUp_ov 1 (poly.oneValue_scaleP _
            (slabGo_pmul (m * m) V.1 W.2))))
        (poly.oneValue_trans (slabGo_norm (m * m) 1 m (poly.pmul V.2 W.1))
          (poly.shiftUp_ov 1 (poly.oneValue_scaleP _
            (slabGo_pmul (m * m) V.2 W.1)))))) ?_
  refine poly.oneValue_symm ?_
  refine poly.oneValue_trans
    (poly.sum_mul _ _ _) ?_
  refine poly.oneValue_trans
    (poly.add_congr (poly.mul_sum _ _ _) (poly.mul_sum _ _ _)) ?_
  refine poly.oneValue_trans
    (poly.add_congr (poly.oneValue_refl _) (poly.add_comm _ _)) ?_
  refine poly.oneValue_trans (poly.add_shuffle _ _ _ _) ?_
  refine poly.add_congr ?_ ?_
  · refine poly.add_congr (poly.oneValue_refl _) ?_
    exact mul_uu m m (slabGo (m * m) 0 1 V.2) (slabGo (m * m) 0 1 W.2)
  · refine poly.add_congr ?_ ?_
    · refine poly.oneValue_trans (poly.mul_shiftUp _ 1 _) ?_
      exact poly.shiftUp_ov 1 (mul_scaleR (BPair.ofNat m) _ _)
    · refine poly.oneValue_trans (mul_shiftL 1 _ _) ?_
      exact poly.shiftUp_ov 1 (mul_scaleL (BPair.ofNat m) _ _)


/-! The shift bridge: the shifted square scale and the shifted scale
read collapse at the successor depth's own pair reads, and the
substitution walk collapses at the successor depth's square scale. -/

/-- The shifted square scale collapses at the successor depth's
square scale. -/
private theorem depthPoly_sh1 (m : Nat) :
    poly.oneValue (depthPoly sh1 m)
      [BPair.unit, BPair.ofNat ((m + 1) * (m + 1))] := by
  refine ⟨?_, ?_, trivial⟩
  · exact BPair.oneValue_trans
      (BPair.add_congr
        (BPair.add_congr
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.mul_unit (BPair.ofNat 1)))
          (BPair.oneValue_refl BPair.unit))
        (BPair.oneValue_refl BPair.unit))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.add_unit BPair.unit)
          (BPair.oneValue_refl BPair.unit))
        (BPair.add_unit BPair.unit))
  · refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.add_congr
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.ofNat_one_mul (BPair.ofNat 1)))
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.oneValue_trans
              (BPair.mul_ofNat_one (BPair.ofNat (1 * (m * m))))
              (BPair.oneValue_of_eq
                (congrArg BPair.ofNat (Nat.one_mul (m * m)))))))
        (BPair.oneValue_trans (BPair.norm_oneValue _)
          (BPair.oneValue_symm (BPair.ofNat_mul m 2)))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_symm (BPair.ofNat_add 1 (m * m)))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofNat_add (1 + m * m) (m * 2))) ?_
    exact BPair.oneValue_of_eq (congrArg BPair.ofNat
      (by rw [Nat.mul_two m, Nat.add_comm 1 (m * m), Nat.add_assoc,
        Nat.add_comm 1 (m + m), ground.sqSucc m] :
        1 + m * m + m * 2 = (m + 1) * (m + 1)))

/-- The shifted scale read collapses at the successor depth's
scale. -/
private theorem depthPoly_u1 (m : Nat) :
    poly.oneValue (depthPoly u1 m) [BPair.unit, BPair.ofNat (m + 1)] := by
  refine ⟨?_, ?_, trivial⟩
  · exact BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (BPair.norm_oneValue _)
          (BPair.mul_unit (BPair.ofNat 1)))
        (BPair.oneValue_refl BPair.unit))
      (BPair.add_unit BPair.unit)
  · refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (BPair.norm_oneValue _)
          (BPair.ofNat_one_mul (BPair.ofNat 1)))
        (BPair.oneValue_trans (BPair.norm_oneValue _)
          (BPair.mul_ofNat_one (BPair.ofNat m)))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofNat_add 1 m)) ?_
    exact BPair.oneValue_of_eq (congrArg BPair.ofNat (Nat.add_comm 1 m))

/-- The substitution walk collapses at the successor depth's square
scale: the slab's own walk there. -/
private theorem depthPoly_shGo (m : Nat) : ∀ P : poly.PPoly,
    poly.oneValue (depthPoly (shGo P) m)
      (slabGo ((m + 1) * (m + 1)) 0 1 P)
  | [] => trivial
  | p :: t => by
    refine poly.oneValue_trans
      (depthPoly_profAdd ([p], ([] : poly.PPoly))
        (profMul sh1 (shGo t)) m) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (show poly.oneValue (depthPoly ([p], ([] : poly.PPoly)) m) p from
          poly.oneValue_trans
            (poly.oneValue_of_eq (poly.add_nil _))
            (poly.oneValue_trans
              (poly.oneValue_of_eq (poly.add_nil _))
              (poly.scaleP_one p)))
        (poly.oneValue_trans (depthPoly_profMul sh1 (shGo t) m)
          (poly.oneValue_trans
            (poly.mul_congr_left (depthPoly_sh1 m) (depthPoly (shGo t) m))
            (poly.oneValue_trans
              (poly.mul_congr _ (depthPoly_shGo m t))
              (mul_scaleKey (BPair.ofNat ((m + 1) * (m + 1)))
                (slabGo ((m + 1) * (m + 1)) 0 1 t)))))) ?_
    refine poly.oneValue_symm ?_
    show poly.oneValue
      (poly.add (poly.shiftUp 0 (poly.scaleP (BPair.ofNat 1) p))
        (slabGo ((m + 1) * (m + 1)) 1 (1 * ((m + 1) * (m + 1))) t))
      (poly.add p
        (poly.shiftUp 1 (poly.scaleP (BPair.ofNat ((m + 1) * (m + 1)))
          (slabGo ((m + 1) * (m + 1)) 0 1 t))))
    refine poly.add_congr (poly.scaleP_one p) ?_
    refine poly.oneValue_trans
      (slabGo_norm ((m + 1) * (m + 1)) 1 (1 * ((m + 1) * (m + 1))) t) ?_
    refine poly.shiftUp_ov 1 (poly.scaleP_congr ?_ _)
    exact BPair.oneValue_of_eq
      (congrArg BPair.ofNat (Nat.one_mul ((m + 1) * (m + 1))))

/-- The shifted profile's collapse is the collapse at the successor
depth. -/
theorem depthPoly_profShift (V : poly.PPoly × poly.PPoly) (m : Nat) :
    poly.oneValue (depthPoly (profShift V) m) (depthPoly V (m + 1)) := by
  refine poly.oneValue_trans
    (depthPoly_profAdd (shGo V.1) (profMul u1 (shGo V.2)) m) ?_
  refine poly.oneValue_trans
    (poly.add_congr (depthPoly_shGo m V.1)
      (poly.oneValue_trans (depthPoly_profMul u1 (shGo V.2) m)
        (poly.oneValue_trans
          (poly.mul_congr_left (depthPoly_u1 m) (depthPoly (shGo V.2) m))
          (poly.oneValue_trans
            (poly.mul_congr _ (depthPoly_shGo m V.2))
            (mul_scaleKey (BPair.ofNat (m + 1))
              (slabGo ((m + 1) * (m + 1)) 0 1 V.2)))))) ?_
  exact poly.oneValue_symm
    (poly.add_congr (poly.oneValue_refl _)
      (slabGo_norm ((m + 1) * (m + 1)) 1 (m + 1) V.2))


/-! The diagonal and the comparison as canonical objects: the
diagonal's collapse is the cleared scale polynomial at the depth,
and the comparison profile's collapse is the comparison polynomial's
own. -/

/-- The diagonal's square key at the depth: the well's electric
member's two pair reads collect at the cleared count. -/
private theorem diagKey (qd r m : Nat) :
    1 * (m * m) * (4 * qd) + m * (4 * qd * r) = 4 * qd * (m * m + r * m) := by
  rw [Nat.one_mul, Nat.mul_add (4 * qd) (m * m) (r * m),
    Nat.mul_comm (m * m) (4 * qd), ← ground.mulAssoc (4 * qd) r m,
    Nat.mul_comm m (4 * qd * r)]

/-- The diagonal profile's collapse is the diagonal's cleared scale
polynomial at the depth. -/
theorem depthPoly_diagProf (r qn qd m : Nat) :
    poly.oneValue (depthPoly (diagProf r qn qd) m) (diagPoly r qn qd m) := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · exact BPair.oneValue_trans
      (BPair.add_congr
        (BPair.add_congr
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.ofNat_one_mul (BPair.ofNat (2 * ((r + 1) * qd)))))
          (BPair.oneValue_refl BPair.unit))
        (BPair.oneValue_refl BPair.unit))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.add_unit _) (BPair.oneValue_refl BPair.unit))
        (BPair.add_unit _))
  · exact BPair.oneValue_trans
      (BPair.add_congr
        (BPair.add_congr
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.ofNat_one_mul (BPair.ofNat ((r + 1) * qn)).swap))
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.mul_unit (BPair.ofNat (1 * (m * m))))))
        (BPair.oneValue_trans (BPair.norm_oneValue _)
          (BPair.mul_unit (BPair.ofNat m))))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.add_unit _) (BPair.oneValue_refl BPair.unit))
        (BPair.add_unit _))
  · refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (BPair.norm_oneValue _)
          (BPair.oneValue_symm
            (BPair.ofNat_mul (1 * (m * m)) (4 * qd))))
        (BPair.oneValue_trans (BPair.norm_oneValue _)
          (BPair.oneValue_symm (BPair.ofNat_mul m (4 * qd * r))))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.ofNat_add (1 * (m * m) * (4 * qd)) (m * (4 * qd * r)))) ?_
    exact BPair.oneValue_of_eq (congrArg BPair.ofNat (diagKey qd r m))

/-- The comparison profile's collapse is the termwise comparison's
own scale polynomial at the depth. -/
theorem depthPoly_termProf (V : poly.PPoly × poly.PPoly) (r qn qd m : Nat) :
    poly.oneValue (depthPoly (termProf V r qn qd) m)
      (termPoly V r qn qd m) := by
  refine poly.oneValue_trans
    (depthPoly_profAdd
      (profMul (profShift (diagProf r qn qd)) (profShift V))
      (profNeg (profScale ((r + 1) * qd)
        (profAdd V (profShift (profShift V))))) m) ?_
  refine poly.add_congr ?_ ?_
  · refine poly.oneValue_trans
      (depthPoly_profMul (profShift (diagProf r qn qd)) (profShift V) m) ?_
    exact poly.oneValue_trans
      (poly.mul_congr_left
        (poly.oneValue_trans (depthPoly_profShift (diagProf r qn qd) m)
          (depthPoly_diagProf r qn qd (m + 1)))
        (depthPoly (profShift V) m))
      (poly.mul_congr _ (depthPoly_profShift V m))
  · refine poly.oneValue_trans
      (depthPoly_profNeg
        (profScale ((r + 1) * qd) (profAdd V (profShift (profShift V)))) m)
      ?_
    refine poly.swapMap_oneValue ?_
    refine poly.oneValue_trans
      (depthPoly_profScale (profAdd V (profShift (profShift V)))
        ((r + 1) * qd) m) ?_
    refine poly.oneValue_scaleP _ ?_
    refine poly.oneValue_trans
      (depthPoly_profAdd V (profShift (profShift V)) m) ?_
    exact poly.add_congr (poly.oneValue_refl _)
      (poly.oneValue_trans (depthPoly_profShift (profShift V) m)
        (depthPoly_profShift V (m + 1)))


/-! The certificate's three further canonical objects: the boundary
comparison at the origin depth, the seam's crossed products, and the
final seam's slope object at the depth step. -/

/-- The boundary comparison's object: the shifted diagonal's
multiple of the profile against the rate's multiple of the shifted
profile — the collapse at the origin depth is the boundary seed's
comparison, the first diagonal's multiple of the boundary value
against the rate's multiple of the first value. -/
def seedProf (V : poly.PPoly × poly.PPoly) (r qn qd : Nat) :
    poly.PPoly × poly.PPoly :=
  profAdd (profMul (profShift (diagProf r qn qd)) V)
    (profNeg (profScale ((r + 1) * qd) (profShift V)))

/-- The boundary comparison's collapse at a depth: the successor
depth's diagonal on the depth's own value against the rate's
multiple of the successor value. -/
theorem seedProf_at (V : poly.PPoly × poly.PPoly) (r qn qd m : Nat) :
    poly.oneValue (depthPoly (seedProf V r qn qd) m)
      (poly.add (poly.mul (diagPoly r qn qd (m + 1)) (depthPoly V m))
        (poly.neg (poly.scaleP (BPair.ofNat ((r + 1) * qd))
          (depthPoly V (m + 1))))) := by
  refine poly.oneValue_trans
    (depthPoly_profAdd (profMul (profShift (diagProf r qn qd)) V)
      (profNeg (profScale ((r + 1) * qd) (profShift V))) m) ?_
  refine poly.add_congr ?_ ?_
  · refine poly.oneValue_trans
      (depthPoly_profMul (profShift (diagProf r qn qd)) V m) ?_
    exact poly.mul_congr_left
      (poly.oneValue_trans (depthPoly_profShift (diagProf r qn qd) m)
        (depthPoly_diagProf r qn qd (m + 1)))
      (depthPoly V m)
  · refine poly.oneValue_trans
      (depthPoly_profNeg (profScale ((r + 1) * qd) (profShift V)) m) ?_
    refine poly.swapMap_oneValue ?_
    refine poly.oneValue_trans
      (depthPoly_profScale (profShift V) ((r + 1) * qd) m) ?_
    exact poly.oneValue_scaleP _ (depthPoly_profShift V m)

/-- The seam's crossed products: the outgoing profile's shift
against the incoming profile, joined at the swap to the incoming's
shift against the outgoing. -/
def crossProf (V W : poly.PPoly × poly.PPoly) :
    poly.PPoly × poly.PPoly :=
  profAdd (profMul (profShift V) W) (profNeg (profMul V (profShift W)))

/-- The seam object's collapse at a depth: the two profiles'
consecutive values crossed, the outgoing's successor against the
incoming's own less the exchanged product. -/
theorem crossProf_at (V W : poly.PPoly × poly.PPoly) (m : Nat) :
    poly.oneValue (depthPoly (crossProf V W) m)
      (poly.add (poly.mul (depthPoly V (m + 1)) (depthPoly W m))
        (poly.neg (poly.mul (depthPoly V m) (depthPoly W (m + 1))))) := by
  refine poly.oneValue_trans
    (depthPoly_profAdd (profMul (profShift V) W)
      (profNeg (profMul V (profShift W))) m) ?_
  refine poly.add_congr ?_ ?_
  · refine poly.oneValue_trans (depthPoly_profMul (profShift V) W m) ?_
    exact poly.mul_congr_left (depthPoly_profShift V m) (depthPoly W m)
  · refine poly.oneValue_trans
      (depthPoly_profNeg (profMul V (profShift W)) m) ?_
    refine poly.swapMap_oneValue ?_
    refine poly.oneValue_trans (depthPoly_profMul V (profShift W) m) ?_
    exact poly.mul_congr _ (depthPoly_profShift W m)

/-- The depth step's read `2u + η`, the square scale's own move. -/
def stepProf : poly.PPoly × poly.PPoly :=
  ([[BPair.unit, BPair.ofNat 1]], [[BPair.ofNat 2]])

/-- The depth step's key count at a depth. -/
private theorem stepKey (m : Nat) : 2 * m + 1 = 1 + m * 2 := by
  rw [Nat.add_comm (2 * m) 1, Nat.mul_comm 2 m]

/-- The depth step's collapse at a depth: the scale's odd multiple
`2m + 1` at the scale key, the square scale's own move. -/
theorem stepProf_at (m : Nat) :
    poly.oneValue (depthPoly stepProf m)
      [BPair.unit, BPair.ofNat (2 * m + 1)] := by
  refine ⟨?_, ?_, trivial⟩
  · refine BPair.oneValue_trans (BPair.add_unit _) ?_
    exact BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.ofNat_one_mul BPair.unit)
  · refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (BPair.norm_oneValue _)
          (BPair.ofNat_one_mul (BPair.ofNat 1)))
        (BPair.oneValue_trans (BPair.norm_oneValue _)
          (BPair.oneValue_symm (BPair.ofNat_mul m 2)))) ?_
    refine BPair.oneValue_symm ?_
    rw [stepKey m]
    exact BPair.ofNat_add 1 (m * 2)

/-- The final seam's object at the slope allowance, a pair at the
stated clearing: the clearing's multiple of the profile's shift
joined to the allowance's first datum's multiple of the step read
of the profile, against the clearing's multiple of the profile
itself. -/
def slopeProf (V : poly.PPoly × poly.PPoly) (alN alD : Nat) :
    poly.PPoly × poly.PPoly :=
  profAdd (profScale alD (profAdd (profShift V) (profNeg V)))
    (profScale alN (profMul stepProf V))

/-- The slope object's collapse at a depth: the clearing's multiple
of the successor value less the depth's own, joined to the
allowance's multiple of the depth step's scale read on that
value. -/
theorem slopeProf_at (V : poly.PPoly × poly.PPoly) (alN alD m : Nat) :
    poly.oneValue (depthPoly (slopeProf V alN alD) m)
      (poly.add
        (poly.scaleP (BPair.ofNat alD)
          (poly.add (depthPoly V (m + 1)) (poly.neg (depthPoly V m))))
        (poly.scaleP (BPair.ofNat alN)
          (poly.mul [BPair.unit, BPair.ofNat (2 * m + 1)]
            (depthPoly V m)))) := by
  refine poly.oneValue_trans
    (depthPoly_profAdd (profScale alD (profAdd (profShift V) (profNeg V)))
      (profScale alN (profMul stepProf V)) m) ?_
  refine poly.add_congr ?_ ?_
  · refine poly.oneValue_trans
      (depthPoly_profScale (profAdd (profShift V) (profNeg V)) alD m) ?_
    refine poly.oneValue_scaleP _ ?_
    refine poly.oneValue_trans
      (depthPoly_profAdd (profShift V) (profNeg V) m) ?_
    exact poly.add_congr (depthPoly_profShift V m) (depthPoly_profNeg V m)
  · refine poly.oneValue_trans
      (depthPoly_profScale (profMul stepProf V) alN m) ?_
    refine poly.oneValue_scaleP _ ?_
    refine poly.oneValue_trans (depthPoly_profMul stepProf V m) ?_
    exact poly.mul_congr_left (stepProf_at m) (depthPoly V m)


/-- The chain's walk: from a piece's lower cut the value keeps the
upper side at every point of the remaining cover. -/
private theorem chainGo (p : poly.Poly) (bN bD : BPair) :
    ∀ (a b : CPair) (t : List CPair) (x : CPair),
      chainRead p bN bD (a :: b :: t) →
      a ≤ x → x ≤ ground.getAt stage.unitC (b :: t) t.length →
      stage.unitC < stage.evalC p x
  | a, b, [], x, h, hax, hxb =>
    stage.keepUpper_all p a b bN bD h.1 x hax hxb
  | a, b, c :: t, x, h, hax, hxb =>
    match CPair.le_total x b with
    | Or.inl hxb2 => stage.keepUpper_all p a b bN bD h.1 x hax hxb2
    | Or.inr hbx => chainGo p bN bD b c t x h.2 hbx hxb

/-- The chained read's conclusion: the value keeps the upper side at
every point of the whole cover. -/
theorem chainRead_all (p : poly.Poly) (bN bD : BPair) (cuts : List CPair)
    (x : CPair) (h : chainRead p bN bD cuts)
    (hlo : ground.getAt stage.unitC cuts 0 ≤ x)
    (hhi : x ≤ ground.getAt stage.unitC cuts (cuts.length - 1))
    (hlen : 2 ≤ cuts.length) : stage.unitC < stage.evalC p x := by
  match cuts, h, hlo, hhi, hlen with
  | [], _, _, _, hlen => exact absurd hlen (Nat.not_succ_le_zero 1)
  | [_], _, _, _, hlen =>
    exact absurd (Nat.le_of_succ_le_succ hlen) (Nat.not_succ_le_zero 0)
  | a :: b :: t, h, hlo, hhi, _ => exact chainGo p bN bD a b t x h hlo hhi

/-- The two-armed chain's walk: from a piece's lower cut one of the
two stated polynomials keeps the upper side at every point of the
remaining cover, the piece's own comparison the arm. -/
private theorem chainGo2 (p q : poly.Poly) (bN bD : BPair) :
    ∀ (a b : CPair) (t : List CPair) (x : CPair),
      chainRead2 p q bN bD (a :: b :: t) →
      a ≤ x → x ≤ ground.getAt stage.unitC (b :: t) t.length →
      stage.unitC < stage.evalC p x ∨ stage.unitC < stage.evalC q x
  | a, b, [], x, h, hax, hxb =>
    match h.1 with
    | Or.inl hp =>
      Or.inl (stage.keepUpper_all p a b bN bD hp x hax hxb)
    | Or.inr hq =>
      Or.inr (stage.keepUpper_all q a b bN bD hq x hax hxb)
  | a, b, c :: t, x, h, hax, hxb =>
    match CPair.le_total x b with
    | Or.inl hxb2 =>
      match h.1 with
      | Or.inl hp =>
        Or.inl (stage.keepUpper_all p a b bN bD hp x hax hxb2)
      | Or.inr hq =>
        Or.inr (stage.keepUpper_all q a b bN bD hq x hax hxb2)
    | Or.inr hbx => chainGo2 p q bN bD b c t x h.2 hbx hxb

/-- The two-armed chained read's conclusion: at every point of the
whole cover one of the two polynomials keeps the upper side. -/
theorem chainRead2_all (p q : poly.Poly) (bN bD : BPair)
    (cuts : List CPair) (x : CPair) (h : chainRead2 p q bN bD cuts)
    (hlo : ground.getAt stage.unitC cuts 0 ≤ x)
    (hhi : x ≤ ground.getAt stage.unitC cuts (cuts.length - 1))
    (hlen : 2 ≤ cuts.length) :
    stage.unitC < stage.evalC p x ∨ stage.unitC < stage.evalC q x := by
  match cuts, h, hlo, hhi, hlen with
  | [], _, _, _, hlen => exact absurd hlen (Nat.not_succ_le_zero 1)
  | [_], _, _, _, hlen =>
    exact absurd (Nat.le_of_succ_le_succ hlen) (Nat.not_succ_le_zero 0)
  | a :: b :: t, h, hlo, hhi, _ =>
    exact chainGo2 p q bN bD a b t x h hlo hhi

/-! The pricing kit: the value's representative reaches no further
than the list, and a cleared evaluation at a scale below the ceiling
sits inside the coefficient fold's price at the ceiling. -/


/-- The key-range fold at any count beyond the family's support. -/
private theorem foldRange_le (F : Nat → BPair) (N n : Nat) (hNn : N ≤ n)
    (hoff : ∀ j, N ≤ j → (F j).oneValue BPair.unit) :
    (ground.famFold BPair.add BPair.unit F (List.range n)).oneValue
      (ground.famFold BPair.add BPair.unit F (List.range N)) := by
  obtain ⟨g, hg⟩ := Nat.le.dest hNn
  rw [← hg]
  exact ground.famFold_range_ext F N hoff g

/-! The cleared ceiling's pricing kit: the ceiling carried as a
balance pair against a positive clearing, the clearing's powers
entering the comparison's other side. -/

/-- The pass's value at the clamped monomial fold, the fold's own
read at the ceiling's two members. -/
private theorem capF_read (e0n : BPair) (e0d : Pos) (K : Nat)
    (p : poly.Poly) :
    (capF e0n e0d K p).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun c => windowsep.mag (ground.getAt BPair.unit p c)
          * ground.bpow e0n c * ground.bpow (BPair.ofPos e0d) (K - c))
        (List.range (K + 1))) := by
  have hlen : ((List.range (K + 1)).map (fun c =>
      windowsep.mag (ground.getAt BPair.unit p c))).length = K + 1 := by
    rw [ground.length_map, ground.length_range]
  refine BPair.oneValue_trans
    (windowsep.foldPow_read _ e0n (BPair.ofPos e0d)) ?_
  rw [hlen]
  refine ground.foldB_congr_members _ _ (List.range (K + 1))
    (fun i hi => ?_)
  refine BPair.oneValue_of_eq ?_
  rw [ground.getAt_map_range BPair.unit
    (fun c => windowsep.mag (ground.getAt BPair.unit p c)) (K + 1) i,
    if_pos (ground.ltOfMem hi)]
  rfl

/-- The cleared ceiling's own coefficient fold sits at or above the
sum's unit. -/
private theorem unitLe_capF (e0n : BPair) (e0d : Pos) (K : Nat)
    (he0n : BPair.unit ≤ e0n) (p : poly.Poly) :
    BPair.unit ≤ capF e0n e0d K p :=
  ground.leB_congr_right
    (BPair.oneValue_symm (capF_read e0n e0d K p))
    (ground.foldB_nonneg _ (List.range (K + 1))
      (fun c _ => ground.unitLeMul
        (ground.unitLeMul (windowsep.unitLe_mag _)
          (windowsep.unitLe_bpow he0n c))
        (windowsep.unitLe_bpow
          (ground.leB_of_lt (ground.unitLtOfPos e0d)) (K - c))))

/-- The slab cap at the cleared ceiling sits at or above the sum's
unit. -/
private theorem unitLe_capS {e0n shB : BPair} {e0d : Pos} {K : Nat}
    (he0n : BPair.unit ≤ e0n) (hshB : BPair.unit ≤ shB) :
    ∀ P : poly.PPoly, BPair.unit ≤ capS e0n e0d shB K P
  | [] => ground.leB_refl _
  | p :: t =>
    ground.unitLeAdd (unitLe_capF e0n e0d K he0n p)
      (ground.unitLeMul hshB (unitLe_capS he0n hshB t))

/-- The cleared ceiling sits at or above the sum's unit. -/
private theorem unitLe_of_clear {e0n : BPair} {e0d en ed : Pos}
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    BPair.unit ≤ e0n := by
  refine ground.leB_unscale (ground.unitLtOfPos ed) ?_
  refine ground.leB_congr_left
    (BPair.oneValue_symm (BPair.unit_mul (BPair.ofPos ed))) ?_
  exact ground.leB_trans
    (ground.unitLeMul (ground.leB_of_lt (ground.unitLtOfPos en))
      (ground.leB_of_lt (ground.unitLtOfPos e0d))) he

/-- One key's price at the cleared ceiling: a coefficient against the
scale's power and the clearing's complementary power, cleared at the
ceiling's second member's whole power, sits inside its magnitude
against the ceiling's first member's power and the clearing's
complement, at the scale clearing's whole power. -/
private theorem priceTermC {e0n : BPair} {e0d en ed : Pos} {M K k : Nat}
    (hkM : k ≤ M) (hkK : k ≤ K)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (c : BPair) :
    windowsep.mag (c * ground.bpow (BPair.ofPos en) k
        * ground.bpow (BPair.ofPos ed) (M - k))
        * ground.bpow (BPair.ofPos e0d) K
      ≤ windowsep.mag c * ground.bpow e0n k
          * ground.bpow (BPair.ofPos e0d) (K - k)
        * ground.bpow (BPair.ofPos ed) M := by
  have hEn : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hE0d : BPair.unit ≤ BPair.ofPos e0d :=
    ground.leB_of_lt (ground.unitLtOfPos e0d)
  have hE0n : BPair.unit ≤ e0n := unitLe_of_clear he
  have hL : (windowsep.mag (c * ground.bpow (BPair.ofPos en) k
        * ground.bpow (BPair.ofPos ed) (M - k))).oneValue
      (windowsep.mag c * ground.bpow (BPair.ofPos en) k
        * ground.bpow (BPair.ofPos ed) (M - k)) :=
    BPair.oneValue_trans (windowsep.mag_mul _ _)
      (BPair.mul_congr
        (BPair.oneValue_trans (windowsep.mag_mul c _)
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_of_eq
              (windowsep.mag_unitLe (windowsep.unitLe_bpow hEn k)))))
        (BPair.oneValue_of_eq
          (windowsep.mag_unitLe (windowsep.unitLe_bpow hEd (M - k)))))
  refine ground.leB_congr_left
    (BPair.mul_congr_left (BPair.oneValue_symm hL)) ?_
  -- the powers' comparison, the ceiling's cross-multiplied read
  have hbase : ground.bpow (BPair.ofPos en) k * ground.bpow (BPair.ofPos e0d) k
      ≤ ground.bpow e0n k * ground.bpow (BPair.ofPos ed) k := by
    refine ground.leB_congr
      (ground.bpow_mul (BPair.ofPos en) (BPair.ofPos e0d) k)
      (ground.bpow_mul e0n (BPair.ofPos ed) k) ?_
    exact windowsep.bpow_mono (ground.unitLeMul hEn hE0d) he k
  have hA : (ground.bpow (BPair.ofPos e0d) K).oneValue
      (ground.bpow (BPair.ofPos e0d) k
        * ground.bpow (BPair.ofPos e0d) (K - k)) := by
    have h0 := ground.bpow_add (BPair.ofPos e0d) k (K - k)
    rw [ground.natAddSubCancel hkK] at h0
    exact h0
  have hB : (ground.bpow (BPair.ofPos ed) M).oneValue
      (ground.bpow (BPair.ofPos ed) k
        * ground.bpow (BPair.ofPos ed) (M - k)) := by
    have h0 := ground.bpow_add (BPair.ofPos ed) k (M - k)
    rw [ground.natAddSubCancel hkM] at h0
    exact h0
  have hinner : ground.bpow (BPair.ofPos en) k
        * ground.bpow (BPair.ofPos ed) (M - k)
        * ground.bpow (BPair.ofPos e0d) K
      ≤ ground.bpow e0n k * ground.bpow (BPair.ofPos e0d) (K - k)
        * ground.bpow (BPair.ofPos ed) M := by
    refine ground.leB_congr_left
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) hA)
          (BPair.oneValue_of_eq
            (BPair.mul_mul_mul_comm (ground.bpow (BPair.ofPos en) k)
              (ground.bpow (BPair.ofPos ed) (M - k))
              (ground.bpow (BPair.ofPos e0d) k)
              (ground.bpow (BPair.ofPos e0d) (K - k)))))) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) hB)
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq
              (BPair.mul_mul_mul_comm (ground.bpow e0n k)
                (ground.bpow (BPair.ofPos e0d) (K - k))
                (ground.bpow (BPair.ofPos ed) k)
                (ground.bpow (BPair.ofPos ed) (M - k))))
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_of_eq
                (BPair.mul_comm (ground.bpow (BPair.ofPos e0d) (K - k))
                  (ground.bpow (BPair.ofPos ed) (M - k)))))))) ?_
    exact ground.leB_mul_mono
      (ground.unitLeMul (windowsep.unitLe_bpow hEd (M - k))
        (windowsep.unitLe_bpow hE0d (K - k)))
      (ground.unitLeMul (windowsep.unitLe_bpow hE0n k)
        (windowsep.unitLe_bpow hEd k))
      hbase (ground.leB_refl _)
  have hEqL : windowsep.mag c * (ground.bpow (BPair.ofPos en) k
        * ground.bpow (BPair.ofPos ed) (M - k)
        * ground.bpow (BPair.ofPos e0d) K)
      = windowsep.mag c * ground.bpow (BPair.ofPos en) k
        * ground.bpow (BPair.ofPos ed) (M - k)
        * ground.bpow (BPair.ofPos e0d) K := by
    rw [← BPair.mul_assoc, ← BPair.mul_assoc]
  have hEqR : windowsep.mag c * (ground.bpow e0n k
        * ground.bpow (BPair.ofPos e0d) (K - k)
        * ground.bpow (BPair.ofPos ed) M)
      = windowsep.mag c * ground.bpow e0n k
        * ground.bpow (BPair.ofPos e0d) (K - k)
        * ground.bpow (BPair.ofPos ed) M := by
    rw [← BPair.mul_assoc, ← BPair.mul_assoc]
  exact ground.leB_congr (BPair.oneValue_of_eq hEqL)
    (BPair.oneValue_of_eq hEqR)
    (ground.leB_mulR (windowsep.unitLe_mag c) hinner)

/-- The cleared evaluation at a scale below the cleared ceiling sits
inside the ceiling's coefficient fold, the clearing's whole power on
one side and the scale clearing's on the other. -/
private theorem capF_price {e0n : BPair} {e0d en ed : Pos} (q : poly.Poly)
    (K M : Nat) (hK : (poly.vnorm q).length ≤ K + 1)
    (hM : (poly.vnorm q).length ≤ M + 1)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    windowsep.mag (poly.evalClear q (BPair.ofPos en) ed M)
        * ground.bpow (BPair.ofPos e0d) K
      ≤ capF e0n e0d K q * ground.bpow (BPair.ofPos ed) M := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hE0d : BPair.unit ≤ BPair.ofPos e0d :=
    ground.leB_of_lt (ground.unitLtOfPos e0d)
  have hE0n : BPair.unit ≤ e0n := unitLe_of_clear he
  have hval : (poly.evalClear q (BPair.ofPos en) ed M).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit (poly.vnorm q) k
          * ground.bpow (BPair.ofPos en) k
          * ground.bpow (BPair.ofPos ed) (M - k))
        (List.range (poly.vnorm q).length)) :=
    BPair.oneValue_trans
      (BPair.oneValue_symm
        (poly.evalClear_congr (poly.vnorm_ov q) (BPair.ofPos en) ed M))
      (poly.evalClear_read (poly.vnorm q) (BPair.ofPos en) ed M)
  have hcap : (capF e0n e0d K q).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun i => windowsep.mag (ground.getAt BPair.unit (poly.vnorm q) i)
          * ground.bpow e0n i
          * ground.bpow (BPair.ofPos e0d) (K - i))
        (List.range (poly.vnorm q).length)) := by
    refine BPair.oneValue_trans (capF_read e0n e0d K q) ?_
    refine BPair.oneValue_trans
      (foldRange_le _ (poly.vnorm q).length (K + 1) hK (fun j hj => ?_)) ?_
    · refine BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.mul_congr_left
            (BPair.oneValue_trans
              (windowsep.mag_congr
                (BPair.oneValue_symm
                  (poly.oneValue_getAt j (poly.vnorm_ov q))))
              (BPair.oneValue_of_eq
                (congrArg windowsep.mag
                  (ground.getAt_over BPair.unit (poly.vnorm q) j hj)))))) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.mul_congr_left
            (BPair.oneValue_of_eq
              (windowsep.mag_unitLe (ground.leB_refl BPair.unit))))) ?_
      exact BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.unit_mul _)) (BPair.unit_mul _)
    · exact ground.foldB_congr_members _ _
        (List.range (poly.vnorm q).length)
        (fun i _ => BPair.mul_congr_left
          (BPair.mul_congr_left
            (windowsep.mag_congr
              (BPair.oneValue_symm
                (poly.oneValue_getAt i (poly.vnorm_ov q))))))
  refine ground.leB_congr_left
    (BPair.mul_congr_left (windowsep.mag_congr (BPair.oneValue_symm hval)))
    ?_
  refine ground.leB_congr_right
    (BPair.mul_congr_left (BPair.oneValue_symm hcap)) ?_
  refine ground.leB_trans
    (ground.leB_mul_mono (windowsep.unitLe_bpow hE0d K)
      (ground.foldB_nonneg _ (List.range (poly.vnorm q).length)
        (fun i _ => windowsep.unitLe_mag _))
      (windowsep.mag_famFold_le _ _) (ground.leB_refl _)) ?_
  refine ground.leB_congr_left
    (BPair.oneValue_trans
      (ground.foldB_congr_members
        (fun i => windowsep.mag (ground.getAt BPair.unit (poly.vnorm q) i
            * ground.bpow (BPair.ofPos en) i
            * ground.bpow (BPair.ofPos ed) (M - i))
          * ground.bpow (BPair.ofPos e0d) K)
        (fun i => ground.bpow (BPair.ofPos e0d) K
          * windowsep.mag (ground.getAt BPair.unit (poly.vnorm q) i
            * ground.bpow (BPair.ofPos en) i
            * ground.bpow (BPair.ofPos ed) (M - i)))
        (List.range (poly.vnorm q).length)
        (fun i _ => BPair.oneValue_of_eq (BPair.mul_comm _ _)))
      (BPair.oneValue_trans
        (ground.foldB_mul_left (ground.bpow (BPair.ofPos e0d) K) _
          (List.range (poly.vnorm q).length))
        (BPair.oneValue_of_eq (BPair.mul_comm _ _)))) ?_
  refine ground.leB_trans
    (ground.bsum_le _
      (fun i => windowsep.mag (ground.getAt BPair.unit (poly.vnorm q) i)
        * ground.bpow e0n i
        * ground.bpow (BPair.ofPos e0d) (K - i)
        * ground.bpow (BPair.ofPos ed) M)
      (List.range (poly.vnorm q).length) ?_) ?_
  · intro i hi
    rw [ground.countOf_range i (poly.vnorm q).length] at hi
    match Nat.lt_or_ge i (poly.vnorm q).length with
    | Or.inl hlt =>
      exact priceTermC
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hM))
        (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hK)) he _
    | Or.inr hge =>
      rw [if_neg (fun hc => Nat.not_lt_of_ge hge hc)] at hi
      exact absurd hi (Nat.lt_irrefl 0)
  · refine ground.leB_congr_right
      (BPair.oneValue_trans
        (ground.foldB_congr_members
          (fun i => windowsep.mag (ground.getAt BPair.unit (poly.vnorm q) i)
              * ground.bpow e0n i
              * ground.bpow (BPair.ofPos e0d) (K - i)
            * ground.bpow (BPair.ofPos ed) M)
          (fun i => ground.bpow (BPair.ofPos ed) M
            * (windowsep.mag (ground.getAt BPair.unit (poly.vnorm q) i)
              * ground.bpow e0n i
              * ground.bpow (BPair.ofPos e0d) (K - i)))
          (List.range (poly.vnorm q).length)
          (fun i _ => BPair.oneValue_of_eq (BPair.mul_comm _ _)))
        (BPair.oneValue_trans
          (ground.foldB_mul_left (ground.bpow (BPair.ofPos ed) M) _
            (List.range (poly.vnorm q).length))
          (BPair.oneValue_of_eq (BPair.mul_comm _ _)))) ?_
    exact ground.leB_refl _

/-- Five factors' reordering, the scale-key price's own shape. -/
private theorem prodShuffle5 (A B C D E : BPair) :
    A * (B * E) * C * D = E * D * (A * B * C) := by
  rw [← BPair.mul_assoc A B E, BPair.mul_assoc (A * B) E C,
    BPair.mul_comm E C, ← BPair.mul_assoc (A * B) C E,
    BPair.mul_assoc (A * B * C) E D,
    BPair.mul_comm (A * B * C) (E * D)]

/-- The scale-carrying keys' price at the cleared ceiling: a list's
cleared fold from the scale key up sits inside the ceiling's first
member against its own coefficient fold, the clearing's power beyond
the fold's own on the comparison's other side. -/
private theorem tailPriceC {e0n : BPair} {e0d en ed : Pos} (t : poly.Poly)
    (K : Nat) (hlen : t.length ≤ K)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    windowsep.mag (ground.famFold BPair.add BPair.unit
        (fun j => ground.getAt BPair.unit t j
          * ground.bpow (BPair.ofPos en) (j + 1)
          * ground.bpow (BPair.ofPos ed) (K - (j + 1)))
        (List.range t.length))
        * ground.bpow (BPair.ofPos e0d) (K + 1)
      ≤ e0n * capF e0n e0d K t
        * ground.bpow (BPair.ofPos ed) K := by
  have hE0d : BPair.unit ≤ BPair.ofPos e0d :=
    ground.leB_of_lt (ground.unitLtOfPos e0d)
  have hE0n : BPair.unit ≤ e0n := unitLe_of_clear he
  refine ground.leB_trans
    (ground.leB_mul_mono (windowsep.unitLe_bpow hE0d (K + 1))
      (ground.foldB_nonneg _ (List.range t.length)
        (fun j _ => windowsep.unitLe_mag _))
      (windowsep.mag_famFold_le _ _) (ground.leB_refl _)) ?_
  refine ground.leB_congr_left
    (BPair.oneValue_trans
      (ground.foldB_congr_members
        (fun j => windowsep.mag (ground.getAt BPair.unit t j
            * ground.bpow (BPair.ofPos en) (j + 1)
            * ground.bpow (BPair.ofPos ed) (K - (j + 1)))
          * ground.bpow (BPair.ofPos e0d) (K + 1))
        (fun j => ground.bpow (BPair.ofPos e0d) (K + 1)
          * windowsep.mag (ground.getAt BPair.unit t j
            * ground.bpow (BPair.ofPos en) (j + 1)
            * ground.bpow (BPair.ofPos ed) (K - (j + 1))))
        (List.range t.length)
        (fun j _ => BPair.oneValue_of_eq (BPair.mul_comm _ _)))
      (BPair.oneValue_trans
        (ground.foldB_mul_left (ground.bpow (BPair.ofPos e0d) (K + 1)) _
          (List.range t.length))
        (BPair.oneValue_of_eq (BPair.mul_comm _ _)))) ?_
  refine ground.leB_trans
    (ground.bsum_le _
      (fun j => e0n * ground.bpow (BPair.ofPos ed) K
        * (windowsep.mag (ground.getAt BPair.unit t j)
          * ground.bpow e0n j * ground.bpow (BPair.ofPos e0d) (K - j)))
      (List.range t.length) ?_) ?_
  · intro i hi
    rw [ground.countOf_range i t.length] at hi
    match Nat.lt_or_ge i t.length with
    | Or.inl hlt =>
      have hiK : i + 1 ≤ K :=
        Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hlt hlen)
      refine ground.leB_trans
        (priceTermC (M := K) (K := K + 1) (k := i + 1) hiK
          (Nat.le_trans hiK (Nat.le_succ K)) he _) ?_
      rw [Nat.succ_sub_succ K i]
      refine ground.leB_congr_left
        (BPair.mul_congr_left
          (BPair.mul_congr_left
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_symm
                (BPair.oneValue_trans (ground.bpow_add e0n i 1)
                  (BPair.mul_congr (BPair.oneValue_refl _)
                    (ground.bpow_one_read e0n))))))) ?_
      refine ground.leB_congr_left
        (BPair.oneValue_of_eq
          (prodShuffle5 (windowsep.mag (ground.getAt BPair.unit t i))
            (ground.bpow e0n i) (ground.bpow (BPair.ofPos e0d) (K - i))
            (ground.bpow (BPair.ofPos ed) K) e0n).symm) ?_
      exact ground.leB_refl _
    | Or.inr hge =>
      rw [if_neg (fun hc => Nat.not_lt_of_ge hge hc)] at hi
      exact absurd hi (Nat.lt_irrefl 0)
  · refine ground.leB_congr_left
      (BPair.oneValue_symm
        (ground.foldB_mul_left (e0n * ground.bpow (BPair.ofPos ed) K) _
          (List.range t.length))) ?_
    refine ground.leB_congr_left
      (BPair.mul_congr (BPair.oneValue_refl _)
        (foldRange_le _ t.length (K + 1)
          (Nat.le_trans hlen (Nat.le_succ K)) (fun j hj => ?_))) ?_
    · refine BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.mul_congr_left
            (BPair.oneValue_of_eq
              (congrArg windowsep.mag
                (ground.getAt_over BPair.unit t j hj))))) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.mul_congr_left
            (BPair.oneValue_of_eq
              (windowsep.mag_unitLe (ground.leB_refl BPair.unit))))) ?_
      exact BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.unit_mul _)) (BPair.unit_mul _)
    · refine ground.leB_congr_left
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.mul_right_comm e0n (capF e0n e0d K t)
              (ground.bpow (BPair.ofPos ed) K)))
          (BPair.mul_congr
            (BPair.oneValue_refl (e0n * ground.bpow (BPair.ofPos ed) K))
            (capF_read e0n e0d K t)))
        (ground.leB_refl _)

/-- The scale-tail read prices the whole scale polynomial from below:
at every scale at or below the ceiling the cleared evaluation sits
strictly above the sum's unit. -/
theorem lowRead_pos (p : poly.Poly) (e0n : BPair) (e0d : Pos) (K : Nat)
    (h : lowRead p e0n e0d K) (hlen : p.length ≤ K + 1)
    (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    BPair.unit < poly.evalClear p (BPair.ofPos en) ed K := by
  match p, h, hlen with
  | [], h, _ =>
    exact absurd h.1 (ground.leB_not_lt (ground.leB_refl BPair.unit))
  | c :: t, h, hlen =>
    have hE0d : BPair.unit ≤ BPair.ofPos e0d :=
      ground.leB_of_lt (ground.unitLtOfPos e0d)
    have hK : t.length ≤ K := Nat.le_of_succ_le_succ hlen
    have hval : (poly.evalClear (c :: t) (BPair.ofPos en) ed K).oneValue
        (c * ground.bpow (BPair.ofPos ed) K
          + ground.famFold BPair.add BPair.unit
            (fun j => ground.getAt BPair.unit t j
              * ground.bpow (BPair.ofPos en) (j + 1)
              * ground.bpow (BPair.ofPos ed) (K - (j + 1)))
            (List.range t.length)) := by
      refine BPair.oneValue_trans
        (poly.evalClear_read (c :: t) (BPair.ofPos en) ed K) ?_
      rw [show (c :: t).length = t.length + 1 from rfl,
        ground.foldB_range_cons]
      exact BPair.add_congr
        (BPair.mul_congr_left (BPair.mul_one_read c))
        (BPair.oneValue_refl _)
    refine BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (BPair.oneValue_symm hval) ?_
    refine ground.unitLt_of_swap_lt ?_
    refine ground.ltB_unscale (windowsep.unitLe_bpow hE0d (K + 1)) ?_
    refine ground.leB_ltB_trans
      (ground.leB_mul_mono (windowsep.unitLe_bpow hE0d (K + 1))
        (windowsep.unitLe_mag _)
        (windowsep.swap_le_mag _) (ground.leB_refl _)) ?_
    refine ground.leB_ltB_trans (tailPriceC t K hK he) ?_
    refine BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_of_eq
        (BPair.mul_right_comm c (ground.bpow (BPair.ofPos e0d) (K + 1))
          (ground.bpow (BPair.ofPos ed) K))) ?_
    exact ground.ltB_mulPos
      (BPair.lt_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (powCRead e0d (K + 1)))
        h.2)
      (windowsep.unitLt_bpow (ground.unitLtOfPos ed) K)


/-! The composite order's kit at the certificate's instances: the
side read at the first datum, the sum and the product keeping the
order, and a squared comparison reading back at a side above the
sum's unit. -/

/-- A composite at a first datum above the sum's unit sits above the
composite unit. -/
private theorem cunitLe {u : BPair} {w : Pos} (h : BPair.unit ≤ u) :
    stage.unitC ≤ (⟨u, w⟩ : CPair) := by
  show BPair.unit.scale w ≤ u.scale Pos.one
  rw [BPair.scale_one]
  exact ground.leB_congr_left (BPair.oneValue_symm (BPair.unit_scale w)) h

/-- The step clearance's plain order: the outer top clears the
inner outright at the cleared ceiling. -/
private theorem stepClear_le {a b : CPair} {e0n : BPair} {e0d : Pos}
    {en ed : Pos} (h : stepClear a b e0n e0d)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    a ≤ b := by
  have h0 : (a + stage.unitC).oneValue a := by
    rw [CPair.add_comm]
    exact stage.addC_unitC a
  refine CPair.le_trans (CPair.le_congr h0 (CPair.oneValue_refl _)
    (CPair.le_add (CPair.le_refl a)
      (cunitLe (unitLe_of_clear he)))) h.1

/-- A composite joined to its memberwise swap is the composite
unit. -/
private theorem czero (x : CPair) :
    (x + CPair.swap x).oneValue stage.unitC :=
  CPair.oneValue_trans
    (CPair.oneValue_symm (stage.addC_unitC (x + CPair.swap x)))
    (CPair.add_swap_unit x stage.unitC)

/-- The scale step's square at the doubled depth. -/
private theorem stepSq (m : Nat) : m * 2 * (m * 2) = 4 * (m * m) := by
  rw [Nat.mul_comm m 2, ground.mulAssoc 2 m (2 * m),
    ground.mulLeftComm m 2 m, ← ground.mulAssoc 2 2 (m * m)]

/-- The step clearance carries a depth inside the inner top to a
square scale inside the outer. -/
theorem stepClear_step (a b : CPair) (e0n : BPair) (e0d : Pos)
    (h : stepClear a b e0n e0d)
    (m : Nat) (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hle : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair) ≤ a) :
    (⟨BPair.ofNat ((m + 1) * (m + 1)) * BPair.ofPos en, ed⟩ : CPair)
      ≤ b := by
  have hEnU : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hunitS : stage.unitC ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
      : CPair) :=
    cunitLe (ground.unitLeMul (ground.unitLeOfNat (m * m)) hEnU)
  have hunitT : stage.unitC ≤ (⟨BPair.ofNat (m * 2) * BPair.ofPos en, ed⟩
      : CPair) :=
    cunitLe (ground.unitLeMul (ground.unitLeOfNat (m * 2)) hEnU)
  have hunitH : stage.unitC ≤ (⟨BPair.ofPos en, ed⟩ : CPair) :=
    cunitLe hEnU
  have hunitE : stage.unitC ≤ (⟨e0n, e0d⟩ : CPair) :=
    cunitLe (unitLe_of_clear he)
  have hunitF : stage.unitC ≤ stage.ofB (BPair.ofNat 4) :=
    cunitLe (ground.unitLeOfNat 4)
  have hunita : stage.unitC ≤ a := CPair.le_trans hunitS hle
  have hHE : (⟨BPair.ofPos en, ed⟩ : CPair) ≤ (⟨e0n, e0d⟩ : CPair) := by
    show (BPair.ofPos en).scale e0d ≤ e0n.scale ed
    exact ground.leB_congr
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.mul_comm (BPair.ofPos en) (BPair.ofPos e0d)))
        (BPair.ofPos_scale e0d (BPair.ofPos en)))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm e0n (BPair.ofPos ed)))
        (BPair.ofPos_scale ed e0n)) he
  -- the square-scale step's square against the gap's square
  have hSH : stage.unitC ≤ ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
      : CPair) * ⟨BPair.ofPos en, ed⟩) :=
    cunitLe (ground.unitLeMul
      (ground.unitLeMul (ground.unitLeOfNat (m * m)) hEnU) hEnU)
  have hmul : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair)
      * ⟨BPair.ofPos en, ed⟩ ≤ a * (⟨e0n, e0d⟩ : CPair) :=
    stage.mulC_le_mono hunitH hunita hle hHE
  have hFmul : stage.ofB (BPair.ofNat 4)
      * ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair)
        * ⟨BPair.ofPos en, ed⟩)
      ≤ stage.ofB (BPair.ofNat 4) * (a * (⟨e0n, e0d⟩ : CPair)) :=
    stage.mulC_le_mono hSH hunitF (CPair.le_refl _) hmul
  have hcoef : ((BPair.ofNat (m * 2) * BPair.ofPos en)
        * (BPair.ofNat (m * 2) * BPair.ofPos en)).oneValue
      (BPair.ofNat 4
        * (BPair.ofNat (m * m) * BPair.ofPos en * BPair.ofPos en)) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_mul_mul_comm (BPair.ofNat (m * 2)) (BPair.ofPos en)
          (BPair.ofNat (m * 2)) (BPair.ofPos en))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.oneValue_trans
          (BPair.oneValue_symm (BPair.ofNat_mul (m * 2) (m * 2)))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (congrArg BPair.ofNat (stepSq m)))
            (BPair.ofNat_mul 4 (m * m))))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_assoc (BPair.ofNat 4) (BPair.ofNat (m * m))
        (BPair.ofPos en * BPair.ofPos en),
      ← BPair.mul_assoc (BPair.ofNat (m * m)) (BPair.ofPos en)
        (BPair.ofPos en)]
  have hTsq : ((⟨BPair.ofNat (m * 2) * BPair.ofPos en, ed⟩ : CPair)
      * ⟨BPair.ofNat (m * 2) * BPair.ofPos en, ed⟩).oneValue
      (stage.ofB (BPair.ofNat 4)
        * ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair)
          * ⟨BPair.ofPos en, ed⟩)) :=
    CPair.oneValue_trans
      (CPair.num_oneValue hcoef (ed * ed))
      (CPair.den_congr (ground.one_mul (ed * ed)).symm)
  -- the gap sits above the composite unit
  have hzeroL : (a + (⟨e0n, e0d⟩ : CPair)
      + (CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair)))).oneValue
      stage.unitC := by
    rw [CPair.add_assoc a ((⟨e0n, e0d⟩ : CPair))
        (CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair))),
      CPair.add_left_comm ((⟨e0n, e0d⟩ : CPair)) (CPair.swap a)
        (CPair.swap ((⟨e0n, e0d⟩ : CPair))),
      ← CPair.add_assoc a (CPair.swap a)
        ((⟨e0n, e0d⟩ : CPair) + CPair.swap ((⟨e0n, e0d⟩ : CPair)))]
    exact CPair.oneValue_trans
      (CPair.add_congr (czero a) (czero ((⟨e0n, e0d⟩ : CPair))))
      (stage.addC_unitC stage.unitC)
  have hgap : stage.unitC ≤ b + CPair.swap a
      + CPair.swap ((⟨e0n, e0d⟩ : CPair)) := by
    have hstep : a + (⟨e0n, e0d⟩ : CPair)
        + (CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair)))
        ≤ b + (CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair))) :=
      CPair.le_add h.1
        (CPair.le_refl (CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair))))
    rw [← CPair.add_assoc b (CPair.swap a)
      (CPair.swap ((⟨e0n, e0d⟩ : CPair)))] at hstep
    exact CPair.le_congr hzeroL (CPair.oneValue_refl _) hstep
  have hTG : (⟨BPair.ofNat (m * 2) * BPair.ofPos en, ed⟩ : CPair)
      ≤ b + CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair)) :=
    stage.leC_of_sq_le hgap
      (CPair.le_congr (CPair.oneValue_symm hTsq) (CPair.oneValue_refl _)
        (CPair.le_trans hFmul h.2))
  -- the step lands inside the outer top
  have hsum : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair)
      + ⟨BPair.ofNat (m * 2) * BPair.ofPos en, ed⟩
      + ⟨BPair.ofPos en, ed⟩
      ≤ a + (b + CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair)))
        + (⟨e0n, e0d⟩ : CPair) :=
    CPair.le_add (CPair.le_add hle hTG) hHE
  have hnum : (BPair.ofNat (m * m) * BPair.ofPos en
        + BPair.ofNat (m * 2) * BPair.ofPos en
        + BPair.ofPos en).oneValue
      (BPair.ofNat ((m + 1) * (m + 1)) * BPair.ofPos en) := by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (BPair.ofNat_one_mul (BPair.ofPos en)))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (congrArg (fun z => z + BPair.ofNat 1 * BPair.ofPos en)
          (BPair.right_distrib (BPair.ofNat (m * m))
            (BPair.ofNat (m * 2)) (BPair.ofPos en)).symm)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.right_distrib
          (BPair.ofNat (m * m) + BPair.ofNat (m * 2))
          (BPair.ofNat 1) (BPair.ofPos en)).symm) ?_
    refine BPair.mul_congr_left ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_symm (BPair.ofNat_add (m * m) (m * 2)))
        (BPair.oneValue_refl (BPair.ofNat 1))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofNat_add (m * m + m * 2) 1)) ?_
    exact BPair.oneValue_of_eq (congrArg BPair.ofNat
      (by rw [Nat.mul_two m, Nat.add_assoc, ground.sqSucc m] :
        m * m + m * 2 + 1 = (m + 1) * (m + 1)))
  have hSTH : ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair)
      + ⟨BPair.ofNat (m * 2) * BPair.ofPos en, ed⟩
      + ⟨BPair.ofPos en, ed⟩).oneValue
      ⟨BPair.ofNat ((m + 1) * (m + 1)) * BPair.ofPos en, ed⟩ :=
    CPair.oneValue_trans
      (CPair.add_congr
        (CPair.add_same (BPair.ofNat (m * m) * BPair.ofPos en)
          (BPair.ofNat (m * 2) * BPair.ofPos en) ed)
        (CPair.oneValue_refl (⟨BPair.ofPos en, ed⟩ : CPair)))
      (CPair.oneValue_trans
        (CPair.add_same
          (BPair.ofNat (m * m) * BPair.ofPos en
            + BPair.ofNat (m * 2) * BPair.ofPos en)
          (BPair.ofPos en) ed)
        (CPair.num_oneValue hnum ed))
  have heq : a + (b + CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair)))
      + (⟨e0n, e0d⟩ : CPair)
      = b + (a + CPair.swap a)
        + ((⟨e0n, e0d⟩ : CPair) + CPair.swap ((⟨e0n, e0d⟩ : CPair))) := by
    rw [CPair.add_assoc b (CPair.swap a) (CPair.swap ((⟨e0n, e0d⟩ : CPair))),
      CPair.add_left_comm a b
        (CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair))),
      ← CPair.add_assoc a (CPair.swap a)
        (CPair.swap ((⟨e0n, e0d⟩ : CPair))),
      ← CPair.add_assoc b (a + CPair.swap a)
        (CPair.swap ((⟨e0n, e0d⟩ : CPair))),
      CPair.add_assoc (b + (a + CPair.swap a))
        (CPair.swap ((⟨e0n, e0d⟩ : CPair))) ((⟨e0n, e0d⟩ : CPair)),
      CPair.add_comm (CPair.swap ((⟨e0n, e0d⟩ : CPair))) ((⟨e0n, e0d⟩ : CPair))]
  have hb : (a + (b + CPair.swap a + CPair.swap ((⟨e0n, e0d⟩ : CPair)))
      + (⟨e0n, e0d⟩ : CPair)).oneValue b := by
    rw [heq]
    exact CPair.oneValue_trans
      (CPair.add_swap_unit ((⟨e0n, e0d⟩ : CPair)) (b + (a + CPair.swap a)))
      (CPair.add_swap_unit a b)
  exact CPair.le_congr hSTH hb hsum


/-! The shift's cleared read and the fold's range split, the box
device's two computing tools. -/

/-- A key-range fold splits at a stated count. -/
private theorem foldRange_add (F : Nat → BPair) (b n : Nat) :
    (ground.famFold BPair.add BPair.unit F (List.range (b + n))).oneValue
      (ground.famFold BPair.add BPair.unit F (List.range b)
        + ground.famFold BPair.add BPair.unit (fun j => F (b + j))
            (List.range n)) := by
  rw [ground.range_split b n,
    ← ground.famFold_map BPair.add BPair.unit F (fun c => b + c)
      (List.range n)]
  exact ground.famFold_append_ov ground.bpairFoldLaws F (List.range b)
    ((List.range n).map (fun c => b + c))

/-- The shifted list's cleared read: the point's power at the shift
against the cleared read at the remaining clearing. -/
private theorem evalClear_shiftUp (b : Nat) (q : poly.Poly) (ln : BPair)
    (cc : Pos) (N : Nat) :
    (poly.evalClear (poly.shiftUp b q) ln cc N).oneValue
      (ground.bpow ln b * poly.evalClear q ln cc (N - b)) := by
  refine BPair.oneValue_trans
    (poly.evalClear_read (poly.shiftUp b q) ln cc N) ?_
  rw [poly.len_shift b q]
  refine BPair.oneValue_trans (foldRange_add _ b q.length) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (ground.foldB_nullRange _ b (fun k hk => ?_))
      (ground.foldB_congr_members _
        (fun j => ground.bpow ln b
          * (ground.getAt BPair.unit q j * ground.bpow ln j
            * ground.bpow (BPair.ofPos cc) (N - b - j)))
        (List.range q.length) (fun j _ => ?_))) ?_
  · rw [poly.getAt_shiftUp_lt b q k hk]
    exact BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.unit_mul _)) (BPair.unit_mul _)
  · rw [poly.getAt_shiftUp_add b q j, ground.subSub N b j,
      show b + j = b + j from rfl]
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.mul_congr (BPair.oneValue_refl _)
          (ground.bpow_add ln b j))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.mul_assoc (ground.getAt BPair.unit q j)
        (ground.bpow ln b) (ground.bpow ln j),
      BPair.mul_comm (ground.getAt BPair.unit q j) (ground.bpow ln b),
      BPair.mul_assoc (ground.bpow ln b)
        (ground.getAt BPair.unit q j) (ground.bpow ln j),
      BPair.mul_assoc (ground.bpow ln b)
        (ground.getAt BPair.unit q j * ground.bpow ln j)
        (ground.bpow (BPair.ofPos cc) (N - (b + j)))]
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  refine BPair.oneValue_trans
    (ground.foldB_mul_left (ground.bpow ln b) _ (List.range q.length)) ?_
  exact BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (poly.evalClear_read q ln cc (N - b)))

/-- The chain's two endpoints at the composite cut list: the last
cut is the stated top and the list holds its two ends. -/
private theorem chainEnds (lo hi : CPair) (cutsX : List CPair) :
    ground.getAt stage.unitC (lo :: cutsX ++ [hi])
        ((lo :: cutsX ++ [hi]).length - 1) = hi
    ∧ 2 ≤ (lo :: cutsX ++ [hi]).length := by
  constructor
  · rw [show (lo :: cutsX ++ [hi]).length = cutsX.length + 1 + 1 from
      congrArg (· + 1) (ground.length_append cutsX [hi])]
    show ground.getAt stage.unitC (cutsX ++ [hi]) cutsX.length = hi
    exact ground.getAt_append_add stage.unitC cutsX [hi] 0
  · rw [show (lo :: cutsX ++ [hi]).length = cutsX.length + 1 + 1 from
      congrArg (· + 1) (ground.length_append cutsX [hi])]
    exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))

/-- A chained floor at a box point: a polynomial vacant beyond a
stated clearing, whose covered chain holds the upper side, sits
strictly above the sum's unit at that clearing. -/
private theorem chainFloor {P : poly.Poly} {J : Nat}
    (hvac : ∀ j, J + 1 ≤ j →
      (ground.getAt BPair.unit P j).oneValue BPair.unit)
    (bN bD : BPair) (cuts : List CPair) (x : BPair) (ed : Pos)
    (hchain : chainRead P bN bD cuts)
    (hclo : ground.getAt stage.unitC cuts 0 ≤ (⟨x, ed⟩ : CPair))
    (hchi : (⟨x, ed⟩ : CPair)
      ≤ ground.getAt stage.unitC cuts (cuts.length - 1))
    (hlen : 2 ≤ cuts.length) :
    BPair.unit < poly.evalClear P x ed J :=
  stage.evalFloor hvac x ed
    (chainRead_all P bN bD cuts ⟨x, ed⟩ hchain hclo hchi hlen)

/-- The key shift's vacancy transfer: a list vacant from a stated
key is vacant one key later across the unit shift. -/
private theorem shiftVac (W : poly.Poly) {K : Nat}
    (h : ∀ j, K ≤ j →
      (ground.getAt BPair.unit W j).oneValue BPair.unit) :
    ∀ j, K + 1 ≤ j →
      (ground.getAt BPair.unit (poly.shiftUp 1 W) j).oneValue
        BPair.unit := by
  intro j hj
  obtain ⟨d, hd⟩ := Nat.le.dest
    (show 1 ≤ j from Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hj)
  rw [← hd] at hj ⊢
  rw [poly.getAt_shiftUp_add 1 W d]
  rw [Nat.add_comm 1 d] at hj
  exact h d (Nat.le_of_succ_le_succ hj)

/-- The rescaled list is vacant where the list is. -/
private theorem scalePVac (c : BPair) {p : poly.Poly} {N : Nat}
    (hvac : ∀ j, N ≤ j →
      (ground.getAt BPair.unit p j).oneValue BPair.unit) :
    ∀ j, N ≤ j →
      (ground.getAt BPair.unit (poly.scaleP c p) j).oneValue
        BPair.unit := fun j hj =>
  BPair.oneValue_trans (poly.getAt_scaleP c p j)
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (hvac j hj))
      (BPair.mul_unit _))

/-- A natural weight against a clearance power reads its own
magnitude. -/
private theorem magPow (w : Nat) {en : Pos} (S : Nat) :
    windowsep.mag (BPair.ofNat w * ground.bpow (BPair.ofPos en) S)
      = BPair.ofNat w * ground.bpow (BPair.ofPos en) S :=
  windowsep.mag_unitLe (ground.unitLeMul (ground.unitLeOfNat w)
    (windowsep.unitLe_bpow (ground.leB_of_lt (ground.unitLtOfPos en)) S))

/-- The successor power splits off its own base. -/
private theorem bpowSucc (x : BPair) (K : Nat) :
    (ground.bpow x (K + 1)).oneValue (ground.bpow x K * x) :=
  BPair.oneValue_trans (ground.bpow_add x K 1)
    (BPair.mul_congr (BPair.oneValue_refl _) (ground.bpow_one_read x))

/-- The doubled power's successor splits into the two powers and the
base. -/
private theorem bpowTwoK (x : BPair) (K : Nat) :
    (ground.bpow x (2 * K + 1)).oneValue
      (ground.bpow x K * ground.bpow x K * x) := by
  rw [Nat.two_mul K]
  refine BPair.oneValue_trans (ground.bpow_add x (K + K) 1) ?_
  exact BPair.mul_congr (ground.bpow_add x K K) (ground.bpow_one_read x)

/-! The chained cap: one chained side read of a floored polynomial
extracts at every box point, and a comparison pair reads the
withdrawn polynomial's cleared magnitude there — the remainder's
origin arms' own device. -/

/-- One chained side read of a floored polynomial on the box: at a
box point the withdrawn part's cleared read sits inside the floor's
clearing, the chain's positivity moved to the vacancy-aligned
clearing. -/
private theorem chainCapSide (c : BPair) (Q : poly.Poly)
    (bN bD : BPair) (lo hi : CPair) (cutsX : List CPair)
    (hch : chainRead (poly.add [c] Q) bN bD (lo :: cutsX ++ [hi]))
    {X : BPair} {ed : Pos} (J : Nat)
    (hvac : ∀ j, J + 1 ≤ j →
      (ground.getAt BPair.unit Q j).oneValue BPair.unit)
    (hlo : lo ≤ (⟨X, ed⟩ : CPair))
    (hhi : (⟨X, ed⟩ : CPair) ≤ hi) :
    (poly.evalClear Q X ed J).swap
      ≤ c * ground.bpow (BPair.ofPos ed) J := by
  have hpb : ∀ j, J + 1 ≤ j →
      (ground.getAt BPair.unit (poly.add [c] Q) j).oneValue
        BPair.unit := by
    intro j hj
    refine BPair.oneValue_trans (poly.getAt_add _ _ j) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_of_eq
          (ground.getAt_over BPair.unit [c] j
            (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hj)))
        (hvac j hj)) ?_
    exact BPair.add_unit BPair.unit
  have hends := chainEnds lo hi cutsX
  have hJpos : BPair.unit < poly.evalClear (poly.add [c] Q) X ed J := by
    refine chainFloor hpb bN bD (lo :: cutsX ++ [hi]) X ed hch hlo ?_
      hends.2
    rw [hends.1]
    exact hhi
  refine ground.leB_of_unit_add ?_
  refine ground.leB_of_lt ?_
  refine BPair.lt_congr (BPair.oneValue_refl _) ?_ hJpos
  exact BPair.oneValue_trans (poly.evalClear_add [c] Q X ed J)
    (BPair.add_congr (poly.evalClear_single c X ed J) (BPair.oneValue_refl _))


/-- The squared cap's root read: a depth-weighted datum whose
square, at the box coordinate's weight, sits inside the floor's
squared clearing reads its magnitude inside the floor's own, the
ceiling absorbed once and the root at the floor's positivity. -/
private theorem chainCapRoot (e0n f Z : BPair) {m : Nat}
    {en ed e0d : Pos} (J : Nat)
    (hf : BPair.unit ≤ f)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbig : e0n * (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z))
      ≤ f * f * BPair.ofPos e0d
        * ground.bpow (BPair.ofPos ed) (J + J + 1)) :
    windowsep.mag (BPair.ofNat m * BPair.ofPos en * Z)
      ≤ f * ground.bpow (BPair.ofPos ed) (J + 1) := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hEn : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hXZ : BPair.unit
      ≤ BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z) :=
    ground.unitLeMul
      (ground.unitLeMul (ground.unitLeOfNat (m * m)) hEn)
      (ground.unitLeSq Z)
  have haa : (BPair.ofNat m * BPair.ofPos en * Z
        * (BPair.ofNat m * BPair.ofPos en * Z)).oneValue
      (BPair.ofPos en
        * (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_mul_mul_comm (BPair.ofNat m * BPair.ofPos en) Z
          (BPair.ofNat m * BPair.ofPos en) Z)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.oneValue_of_eq
          (BPair.mul_mul_mul_comm (BPair.ofNat m) (BPair.ofPos en)
            (BPair.ofNat m) (BPair.ofPos en)))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.mul_congr_left
          (BPair.oneValue_symm (BPair.ofNat_mul m m)))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.mul_assoc (BPair.ofNat (m * m)) (BPair.ofPos en)
        (BPair.ofPos en),
      BPair.mul_assoc (BPair.ofNat (m * m) * BPair.ofPos en)
        (BPair.ofPos en) (Z * Z),
      BPair.mul_comm (BPair.ofNat (m * m) * BPair.ofPos en)
        (BPair.ofPos en * (Z * Z)),
      BPair.mul_assoc (BPair.ofPos en) (Z * Z)
        (BPair.ofNat (m * m) * BPair.ofPos en),
      BPair.mul_comm (Z * Z) (BPair.ofNat (m * m) * BPair.ofPos en),
      ← BPair.mul_assoc (BPair.ofPos en)
        (BPair.ofNat (m * m) * BPair.ofPos en) (Z * Z),
      BPair.mul_assoc (BPair.ofPos en)
        (BPair.ofNat (m * m) * BPair.ofPos en) (Z * Z)]
  have hb : BPair.unit ≤ f * ground.bpow (BPair.ofPos ed) (J + 1) :=
    ground.unitLeMul hf (windowsep.unitLe_bpow hEd (J + 1))
  have hbp : (BPair.ofPos ed
        * ground.bpow (BPair.ofPos ed) (J + J + 1)).oneValue
      (ground.bpow (BPair.ofPos ed) (J + J + 1 + 1)) :=
    BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos ed)
        (ground.bpow (BPair.ofPos ed) (J + J + 1))))
      (BPair.oneValue_symm (bpowSucc (BPair.ofPos ed) (J + J + 1)))
  have hbb : (f * ground.bpow (BPair.ofPos ed) (J + 1)
        * (f * ground.bpow (BPair.ofPos ed) (J + 1))).oneValue
      (f * f * ground.bpow (BPair.ofPos ed) (J + J + 1 + 1)) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_mul_mul_comm f (ground.bpow (BPair.ofPos ed) (J + 1))
          f (ground.bpow (BPair.ofPos ed) (J + 1)))) ?_
    refine BPair.mul_congr (BPair.oneValue_refl (f * f)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (ground.bpow_add (BPair.ofPos ed) (J + 1) (J + 1))) ?_
    exact BPair.oneValue_of_eq
      (congrArg (ground.bpow (BPair.ofPos ed))
        (by rw [← Nat.add_assoc (J + 1) J 1, Nat.add_right_comm J 1 J]))
  have hM1 : (BPair.ofPos en
        * (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z)))
        * BPair.ofPos e0d
      = (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z))
        * (BPair.ofPos en * BPair.ofPos e0d) := by
    rw [BPair.mul_comm (BPair.ofPos en)
        (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z)),
      BPair.mul_assoc (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z))
        (BPair.ofPos en) (BPair.ofPos e0d)]
  have hM2 : (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z))
        * (e0n * BPair.ofPos ed)
      = BPair.ofPos ed
        * (e0n * (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z))) := by
    rw [BPair.mul_comm e0n (BPair.ofPos ed),
      ← BPair.mul_assoc (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z))
        (BPair.ofPos ed) e0n,
      BPair.mul_comm (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z))
        (BPair.ofPos ed),
      BPair.mul_assoc (BPair.ofPos ed)
        (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z)) e0n,
      BPair.mul_comm (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z)) e0n]
  have hstep1 : (BPair.ofNat m * BPair.ofPos en * Z
        * (BPair.ofNat m * BPair.ofPos en * Z)) * BPair.ofPos e0d
      ≤ BPair.ofPos ed
        * (e0n * (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z))) :=
    ground.leB_congr_left
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.mul_congr_left haa)
          (BPair.oneValue_of_eq hM1)))
      (ground.leB_congr_right (BPair.oneValue_of_eq hM2)
        (ground.leB_mulR hXZ he))
  have hstep2 : BPair.ofPos ed
        * (e0n * (BPair.ofNat (m * m) * BPair.ofPos en * (Z * Z)))
      ≤ BPair.ofPos ed
        * (f * f * BPair.ofPos e0d
          * ground.bpow (BPair.ofPos ed) (J + J + 1)) :=
    ground.leB_mulR hEd hbig
  have heq3 : BPair.ofPos ed
        * (f * f * BPair.ofPos e0d
          * ground.bpow (BPair.ofPos ed) (J + J + 1))
      = (f * f * (BPair.ofPos ed
          * ground.bpow (BPair.ofPos ed) (J + J + 1)))
        * BPair.ofPos e0d := by
    rw [BPair.mul_comm (BPair.ofPos ed)
        (f * f * BPair.ofPos e0d
          * ground.bpow (BPair.ofPos ed) (J + J + 1)),
      BPair.mul_assoc (f * f) (BPair.ofPos e0d)
        (ground.bpow (BPair.ofPos ed) (J + J + 1)),
      BPair.mul_comm (BPair.ofPos e0d)
        (ground.bpow (BPair.ofPos ed) (J + J + 1)),
      ← BPair.mul_assoc (f * f)
        (ground.bpow (BPair.ofPos ed) (J + J + 1)) (BPair.ofPos e0d),
      BPair.mul_assoc
        (f * f * ground.bpow (BPair.ofPos ed) (J + J + 1))
        (BPair.ofPos e0d) (BPair.ofPos ed),
      BPair.mul_comm (BPair.ofPos e0d) (BPair.ofPos ed),
      ← BPair.mul_assoc
        (f * f * ground.bpow (BPair.ofPos ed) (J + J + 1))
        (BPair.ofPos ed) (BPair.ofPos e0d),
      BPair.mul_assoc (f * f)
        (ground.bpow (BPair.ofPos ed) (J + J + 1)) (BPair.ofPos ed),
      BPair.mul_comm (ground.bpow (BPair.ofPos ed) (J + J + 1))
        (BPair.ofPos ed)]
  have hstep3 : (BPair.ofPos ed
        * (f * f * BPair.ofPos e0d
          * ground.bpow (BPair.ofPos ed) (J + J + 1))).oneValue
      ((f * ground.bpow (BPair.ofPos ed) (J + 1)
        * (f * ground.bpow (BPair.ofPos ed) (J + 1)))
        * BPair.ofPos e0d) :=
    BPair.oneValue_trans (BPair.oneValue_of_eq heq3)
      (BPair.mul_congr_left
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl (f * f)) hbp)
          (BPair.oneValue_symm hbb)))
  have hquad' : (BPair.ofNat m * BPair.ofPos en * Z
        * (BPair.ofNat m * BPair.ofPos en * Z)) * BPair.ofPos e0d
      ≤ (f * ground.bpow (BPair.ofPos ed) (J + 1)
        * (f * ground.bpow (BPair.ofPos ed) (J + 1)))
        * BPair.ofPos e0d :=
    ground.leB_congr_right hstep3 (ground.leB_trans hstep1 hstep2)
  have hquad : BPair.ofNat m * BPair.ofPos en * Z
        * (BPair.ofNat m * BPair.ofPos en * Z)
      ≤ f * ground.bpow (BPair.ofPos ed) (J + 1)
        * (f * ground.bpow (BPair.ofPos ed) (J + 1)) :=
    ground.leB_unscale (ground.unitLtOfPos e0d) hquad'
  have hmagSq : (windowsep.mag (BPair.ofNat m * BPair.ofPos en * Z)
        * windowsep.mag
          (BPair.ofNat m * BPair.ofPos en * Z)).oneValue
      (BPair.ofNat m * BPair.ofPos en * Z
        * (BPair.ofNat m * BPair.ofPos en * Z)) :=
    BPair.oneValue_trans
      (BPair.oneValue_symm
        (windowsep.mag_mul (BPair.ofNat m * BPair.ofPos en * Z)
          (BPair.ofNat m * BPair.ofPos en * Z)))
      (BPair.oneValue_of_eq
        (windowsep.mag_unitLe
          (ground.unitLeSq (BPair.ofNat m * BPair.ofPos en * Z))))
  have hquadM : windowsep.mag (BPair.ofNat m * BPair.ofPos en * Z)
        * windowsep.mag (BPair.ofNat m * BPair.ofPos en * Z)
      ≤ f * ground.bpow (BPair.ofPos ed) (J + 1)
        * (f * ground.bpow (BPair.ofPos ed) (J + 1)) :=
    ground.leB_congr_left (BPair.oneValue_symm hmagSq) hquad
  exact ground.leB_of_sq_le hb (ground.leB_not_lt hquadM)

/-- The chained squared read's magnitude: the one side read of the
ceiling-weighted square, the square scale its own coordinate, caps
the depth-weighted origin polynomial's cleared magnitude at every
box point, the root read at the floor's positivity. -/
private theorem chainCapSq (e0n f : BPair) (U : poly.Poly)
    (bN bD : BPair) (lo hi : CPair) (cutsX : List CPair) (e0d : Pos)
    (hch : chainRead (poly.add [f * f * BPair.ofPos e0d]
        (poly.neg (poly.scaleP e0n
          (poly.shiftUp 1 (poly.mul U U))))) bN bD
        (lo :: cutsX ++ [hi]))
    {m : Nat} {en ed : Pos} (J : Nat)
    (hlen : (poly.vnorm U).length ≤ J + 1)
    (hf : BPair.unit ≤ f)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hlo : lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair))
    (hhi : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair) ≤ hi) :
    windowsep.mag (BPair.ofNat m * BPair.ofPos en
        * poly.evalClear U (BPair.ofNat (m * m) * BPair.ofPos en) ed J)
      ≤ f * ground.bpow (BPair.ofPos ed) (J + 1) := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hEn : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hmm2 : poly.oneValue (poly.mul U U)
      (poly.mul (poly.vnorm U) (poly.vnorm U)) :=
    poly.mul_vnorm_ov U U
  have hml : (poly.mul (poly.vnorm U) (poly.vnorm U)).length
      ≤ J + J + 1 :=
    poly.mul_len_le (poly.vnorm U) (poly.vnorm U) J J hlen hlen
  have hmulVac : ∀ d, J + J + 1 ≤ d →
      (ground.getAt BPair.unit (poly.mul U U) d).oneValue
        BPair.unit := fun d hdJ =>
    BPair.oneValue_trans (poly.oneValue_getAt d hmm2)
      (BPair.oneValue_of_eq
        (ground.getAt_over BPair.unit
          (poly.mul (poly.vnorm U) (poly.vnorm U)) d
          (Nat.le_trans hml hdJ)))
  have hvacQ : ∀ j, J + J + 1 + 1 ≤ j →
      (ground.getAt BPair.unit
        (poly.neg (poly.scaleP e0n
          (poly.shiftUp 1 (poly.mul U U)))) j).oneValue
        BPair.unit := by
    intro j hj
    rw [poly.getAt_neg]
    refine BPair.oneValue_trans
      (ground.swap_congr
        (scalePVac e0n (shiftVac (poly.mul U U) hmulVac) j hj)) ?_
    exact BPair.oneValue_refl BPair.unit
  have hs := chainCapSide (f * f * BPair.ofPos e0d)
    (poly.neg (poly.scaleP e0n (poly.shiftUp 1 (poly.mul U U))))
    bN bD lo hi cutsX hch (J + J + 1) hvacQ hlo hhi
  have hbig : e0n * (BPair.ofNat (m * m) * BPair.ofPos en
        * (poly.evalClear U (BPair.ofNat (m * m) * BPair.ofPos en) ed J
          * poly.evalClear U
              (BPair.ofNat (m * m) * BPair.ofPos en) ed J))
      ≤ f * f * BPair.ofPos e0d
        * ground.bpow (BPair.ofPos ed) (J + J + 1) := by
    refine ground.leB_congr_left ?_ hs
    refine BPair.oneValue_trans
      (ground.swap_congr
        (poly.evalClear_neg
          (poly.scaleP e0n (poly.shiftUp 1 (poly.mul U U)))
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (J + J + 1))) ?_
    refine BPair.oneValue_trans
      (poly.evalClear_scaleP e0n (poly.shiftUp 1 (poly.mul U U))
        (BPair.ofNat (m * m) * BPair.ofPos en) ed (J + J + 1)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl e0n) ?_
    refine BPair.oneValue_trans
      (evalClear_shiftUp 1 (poly.mul U U)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed (J + J + 1)) ?_
    refine BPair.mul_congr
      (ground.bpow_one_read (BPair.ofNat (m * m) * BPair.ofPos en)) ?_
    refine BPair.oneValue_trans
      (poly.evalClear_congr hmm2
        (BPair.ofNat (m * m) * BPair.ofPos en) ed (J + J)) ?_
    refine BPair.oneValue_trans
      (poly.evalClear_mul (poly.vnorm U) (poly.vnorm U)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed J J hlen hlen) ?_
    exact BPair.mul_congr
      (poly.evalClear_congr (poly.vnorm_ov U) _ ed J)
      (poly.evalClear_congr (poly.vnorm_ov U) _ ed J)
  exact chainCapRoot e0n f
    (poly.evalClear U (BPair.ofNat (m * m) * BPair.ofPos en) ed J) J
    hf he hbig


/-! The scale-free part's collapse: the key-scaled list at the square
scale, its cleared read the scale-free polynomial's own at the
square-scale point. -/

/-- The key-scaled list: each key's coefficient against the running
square-scale count. -/
private def keyScale (mm : Nat) : Nat → poly.Poly → poly.Poly
  | _, [] => []
  | w, c :: t => BPair.ofNat w * c :: keyScale mm (w * mm) t

/-- The key scaling keeps the key count. -/
private theorem keyScale_len (mm : Nat) : ∀ (w : Nat) (q : poly.Poly),
    (keyScale mm w q).length = q.length
  | _, [] => rfl
  | w, _ :: t => by
    show (keyScale mm (w * mm) t).length + 1 = t.length + 1
    rw [keyScale_len mm (w * mm) t]

/-- The key scaling reads at every key. -/
private theorem getAt_keyScale (mm : Nat) :
    ∀ (w : Nat) (q : poly.Poly) (j : Nat),
    (ground.getAt BPair.unit (keyScale mm w q) j).oneValue
      (BPair.ofNat w * ground.bpow (BPair.ofNat mm) j
        * ground.getAt BPair.unit q j)
  | _, [], _ => BPair.oneValue_symm (BPair.mul_unit _)
  | w, _ :: _, 0 =>
    BPair.oneValue_symm (BPair.mul_congr_left (BPair.mul_one_read _))
  | w, _ :: t, j + 1 => by
    refine BPair.oneValue_trans (getAt_keyScale mm (w * mm) t j) ?_
    refine BPair.mul_congr_left ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.ofNat_mul w mm)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (BPair.norm_oneValue _))

/-- The constant slabs' walk is the key scaling, shifted. -/
private theorem slabGo_const (mm : Nat) : ∀ (b w : Nat) (q : poly.Poly),
    poly.oneValue (slabGo mm b w (q.map (fun c => [c])))
      (poly.shiftUp b (keyScale mm w q))
  | b, _, [] => poly.unitTail_shiftUp b trivial
  | b, w, c :: t => by
    show poly.oneValue
      (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) [c]))
        (slabGo mm (b + 1) (w * mm) (t.map (fun c => [c]))))
      (poly.shiftUp b (BPair.ofNat w * c :: keyScale mm (w * mm) t))
    refine poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl _)
        (poly.oneValue_trans (slabGo_const mm (b + 1) (w * mm) t)
          (poly.oneValue_of_eq
            (poly.shiftUp_shiftUp b 1 (keyScale mm (w * mm) t)).symm))) ?_
    refine poly.oneValue_trans
      (poly.oneValue_symm (poly.shiftUp_add b _ _)) ?_
    refine poly.shiftUp_ov b ?_
    exact ⟨BPair.oneValue_trans
        (BPair.add_congr (BPair.norm_oneValue _)
          (BPair.oneValue_refl BPair.unit))
        (BPair.add_unit _),
      poly.oneValue_refl _⟩

/-- The key-scaled list's cleared read is the list's own at the
square-scale point. -/
private theorem evalClear_keyScale (mm w : Nat) (q : poly.Poly)
    (ln : BPair) (cc : Pos) (N : Nat) :
    (poly.evalClear (keyScale mm w q) ln cc N).oneValue
      (BPair.ofNat w * poly.evalClear q (BPair.ofNat mm * ln) cc N) := by
  refine BPair.oneValue_trans
    (poly.evalClear_read (keyScale mm w q) ln cc N) ?_
  rw [keyScale_len mm w q]
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => BPair.ofNat w
        * (ground.getAt BPair.unit q k
            * ground.bpow (BPair.ofNat mm * ln) k
            * ground.bpow (BPair.ofPos cc) (N - k)))
      (List.range q.length) (fun k _ => ?_)) ?_
  · refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.mul_congr_left (getAt_keyScale mm w q k))) ?_
    refine BPair.oneValue_trans ?_
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat w))
        (BPair.mul_congr_left
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_symm (ground.bpow_mul (BPair.ofNat mm) ln k)))))
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_assoc (BPair.ofNat w) (ground.bpow (BPair.ofNat mm) k)
        (ground.getAt BPair.unit q k),
      BPair.mul_comm (ground.bpow (BPair.ofNat mm) k)
        (ground.getAt BPair.unit q k),
      BPair.mul_assoc (BPair.ofNat w)
        (ground.getAt BPair.unit q k * ground.bpow (BPair.ofNat mm) k)
        (ground.bpow ln k),
      BPair.mul_assoc (BPair.ofNat w)
        (ground.getAt BPair.unit q k * ground.bpow (BPair.ofNat mm) k
          * ground.bpow ln k)
        (ground.bpow (BPair.ofPos cc) (N - k)),
      BPair.mul_assoc (ground.getAt BPair.unit q k)
        (ground.bpow (BPair.ofNat mm) k) (ground.bpow ln k)]
  · exact BPair.oneValue_trans
      (ground.foldB_mul_left (BPair.ofNat w) _ (List.range q.length))
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm
          (poly.evalClear_read q (BPair.ofNat mm * ln) cc N)))


/-! The slab walk's price: at a scale below the ceiling and a square
scale below the box's top, a slab walk's cleared value sits inside
its cap against the running prefactor. -/

/-- The remaining clearing's count at a shift inside it. -/
private theorem subShift {b x N : Nat} (hb : b ≤ N) (h : b + x ≤ N + 1) :
    x ≤ N - b + 1 := by
  have hN : b + (N - b) = N := ground.natAddSubCancel hb
  refine ground.leCancelL b ?_
  rw [← Nat.add_assoc, hN]
  exact h

/-! The slab walk's price at the cleared ceiling: the same walk read
against the ceiling pair's own cap, the clearing's whole power on the
comparison's other side. -/


/-- The magnitude's positive scale passes inside. -/
private theorem magScaleP (p : Pos) (x : BPair) :
    (BPair.ofPos p * windowsep.mag x).oneValue
      (windowsep.mag (BPair.ofPos p * x)) := by
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (windowsep.mag_mul (BPair.ofPos p) x) ?_
  exact BPair.mul_congr_left
    (BPair.oneValue_of_eq (windowsep.mag_unitLe
      (ground.leB_of_lt (ground.unitLtOfPos p))))

/-- The keyed-scale arm's lift: the clearing's weight of the
shifted key-scaled walk reads the scale's weight of the inner
polynomial's cleared read at the depth's square, the vacancy
aligning the clearing. -/
private theorem liftKS (mm w : Nat) (q : poly.Poly) {en ed : Pos}
    {K : Nat}
    (hqvac : ∀ j, K ≤ j →
      (ground.getAt BPair.unit q j).oneValue BPair.unit) :
    (BPair.ofPos ed * poly.evalClear
        (poly.shiftUp 1 (keyScale mm w q))
        (BPair.ofPos en) ed K).oneValue
      (BPair.ofPos en * (BPair.ofNat w
        * poly.evalClear q (BPair.ofNat mm * BPair.ofPos en) ed K)) := by
  have hvacW : ∀ j, K ≤ j →
      (ground.getAt BPair.unit (keyScale mm w q) j).oneValue
        BPair.unit := fun j hj =>
    BPair.oneValue_trans (getAt_keyScale mm w q j)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) (hqvac j hj))
        (BPair.mul_unit _))
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (evalPowLift
      (poly.shiftUp 1 (keyScale mm w q)) (BPair.ofPos en) ed K
      (shiftVac (keyScale mm w q) hvacW))) ?_
  refine BPair.oneValue_trans
    (evalClear_shiftUp 1 (keyScale mm w q) (BPair.ofPos en) ed
      (K + 1)) ?_
  exact BPair.mul_congr (ground.bpow_one_read (BPair.ofPos en))
    (evalClear_keyScale mm w q (BPair.ofPos en) ed ((K + 1) - 1))

/-- The cleared ceiling's coefficient fold at a vacant list reads the
sum's unit. -/
private theorem capF_vac {e0n : BPair} {e0d : Pos} {K : Nat}
    {p : poly.Poly} (hL : (poly.vnorm p).length = 0) :
    (capF e0n e0d K p).oneValue BPair.unit :=
  BPair.oneValue_trans (capF_read e0n e0d K p)
    (ground.foldB_nullRange _ (K + 1) (fun c _ => by
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.mul_congr_left
          (BPair.oneValue_trans
            (windowsep.mag_congr
              (BPair.oneValue_symm
                (poly.oneValue_getAt c (poly.vnorm_ov p))))
            (BPair.oneValue_of_eq
              (congrArg windowsep.mag
                (ground.getAt_over BPair.unit (poly.vnorm p) c
                  (by rw [hL]; exact Nat.zero_le c))))))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.mul_congr_left
          (BPair.oneValue_of_eq
            (windowsep.mag_unitLe (ground.leB_refl BPair.unit))))) ?_
    exact BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.unit_mul _)) (BPair.unit_mul _)))

/-- One slab key's price at the cleared ceiling. -/
private theorem slabTermPriceC {e0n : BPair} {e0d en ed : Pos} {N K : Nat}
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hNK : N ≤ K)
    (p : poly.Poly) (b w c : Nat) (Wn : BPair)
    (hWn : BPair.unit ≤ Wn)
    (hW : windowsep.mag (BPair.ofNat w * ground.bpow (BPair.ofPos en) b)
        * ground.bpow (BPair.ofPos ed) c
      ≤ Wn * ground.bpow (BPair.ofPos ed) b)
    (hsh : 0 < (poly.vnorm p).length →
      b + (poly.vnorm p).length ≤ N + 1) :
    windowsep.mag (poly.evalClear
        (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
        (BPair.ofPos en) ed N)
        * ground.bpow (BPair.ofPos ed) c
        * ground.bpow (BPair.ofPos e0d) K
      ≤ Wn * capF e0n e0d K p
        * ground.bpow (BPair.ofPos ed) N := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hE0d : BPair.unit ≤ BPair.ofPos e0d :=
    ground.leB_of_lt (ground.unitLtOfPos e0d)
  have hval : (poly.evalClear
      (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
      (BPair.ofPos en) ed N).oneValue
      (BPair.ofNat w * ground.bpow (BPair.ofPos en) b
        * poly.evalClear p (BPair.ofPos en) ed (N - b)) := by
    refine BPair.oneValue_trans
      (evalClear_shiftUp b (poly.scaleP (BPair.ofNat w) p)
        (BPair.ofPos en) ed N) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (poly.evalClear_scaleP (BPair.ofNat w) p (BPair.ofPos en) ed
          (N - b))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.mul_assoc,
      BPair.mul_comm (ground.bpow (BPair.ofPos en) b) (BPair.ofNat w)]
  have hmag : (windowsep.mag (poly.evalClear
      (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
      (BPair.ofPos en) ed N)).oneValue
      (windowsep.mag (BPair.ofNat w * ground.bpow (BPair.ofPos en) b)
        * windowsep.mag (poly.evalClear p (BPair.ofPos en) ed (N - b))) :=
    BPair.oneValue_trans (windowsep.mag_congr hval) (windowsep.mag_mul _ _)
  cases hL : (poly.vnorm p).length with
  | zero =>
    have hcap0 : (capF e0n e0d K p).oneValue BPair.unit := capF_vac hL
    have hup : windowsep.mag (poly.evalClear p (BPair.ofPos en) ed (N - b))
        * ground.bpow (BPair.ofPos e0d) K
        ≤ capF e0n e0d K p * ground.bpow (BPair.ofPos ed) (N - b) :=
      capF_price p K (N - b) (by rw [hL]; exact Nat.zero_le _)
        (by rw [hL]; exact Nat.zero_le _) he
    have hz : (windowsep.mag
        (poly.evalClear p (BPair.ofPos en) ed (N - b))).oneValue
        BPair.unit := by
      refine ground.leB_antisymm ?_ (windowsep.unitLe_mag _)
      refine ground.leB_unscale
        (windowsep.unitLt_bpow (ground.unitLtOfPos e0d) K) ?_
      refine ground.leB_congr_right
        (BPair.oneValue_symm (BPair.unit_mul _)) ?_
      refine ground.leB_trans hup ?_
      exact ground.leB_congr_left
        (BPair.oneValue_symm
          (BPair.oneValue_trans (BPair.mul_congr_left hcap0)
            (BPair.unit_mul _)))
        (ground.leB_refl _)
    refine ground.leB_congr ?_ ?_ (ground.leB_refl BPair.unit)
    · exact BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.mul_congr_left
            (BPair.mul_congr_left
              (BPair.oneValue_trans hmag
                (BPair.oneValue_trans
                  (BPair.mul_congr (BPair.oneValue_refl _) hz)
                  (BPair.mul_unit _)))))
          (BPair.oneValue_trans
            (BPair.mul_congr_left (BPair.unit_mul _))
            (BPair.unit_mul _)))
    · exact BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.mul_congr_left
            (BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl Wn) hcap0)
              (BPair.mul_unit Wn)))
          (BPair.unit_mul _))
  | succ L =>
    have hb : b ≤ N :=
      Nat.le_trans (Nat.le_add_right b L)
        (Nat.le_of_succ_le_succ
          (by rw [hL] at hsh; exact hsh (Nat.succ_pos L)))
    have hlen : (poly.vnorm p).length ≤ N - b + 1 :=
      subShift hb (hsh (by rw [hL]; exact Nat.succ_pos L))
    have hKlen : (poly.vnorm p).length ≤ K + 1 :=
      Nat.le_trans hlen
        (Nat.succ_le_succ (Nat.le_trans (Nat.sub_le N b) hNK))
    have hup : windowsep.mag (poly.evalClear p (BPair.ofPos en) ed (N - b))
        * ground.bpow (BPair.ofPos e0d) K
        ≤ capF e0n e0d K p * ground.bpow (BPair.ofPos ed) (N - b) :=
      capF_price p K (N - b) hKlen hlen he
    have hpow : (ground.bpow (BPair.ofPos ed) N).oneValue
        (ground.bpow (BPair.ofPos ed) b
          * ground.bpow (BPair.ofPos ed) (N - b)) := by
      have h0 := ground.bpow_add (BPair.ofPos ed) b (N - b)
      rw [ground.natAddSubCancel hb] at h0
      exact h0
    refine ground.leB_congr ?_ ?_
      (ground.leB_mul_mono
        (ground.unitLeMul (windowsep.unitLe_mag _)
          (windowsep.unitLe_bpow hE0d K))
        (ground.unitLeMul hWn (windowsep.unitLe_bpow hEd b)) hW hup)
    · refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.mul_congr_left hmag)) ?_
      refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_assoc
          (windowsep.mag (BPair.ofNat w * ground.bpow (BPair.ofPos en) b)
            * windowsep.mag (poly.evalClear p (BPair.ofPos en) ed (N - b)))
          (ground.bpow (BPair.ofPos ed) c)
          (ground.bpow (BPair.ofPos e0d) K),
        BPair.mul_mul_mul_comm
          (windowsep.mag (BPair.ofNat w * ground.bpow (BPair.ofPos en) b))
          (windowsep.mag (poly.evalClear p (BPair.ofPos en) ed (N - b)))
          (ground.bpow (BPair.ofPos ed) c)
          (ground.bpow (BPair.ofPos e0d) K)]
    · refine BPair.oneValue_trans ?_
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm hpow))
      exact BPair.oneValue_of_eq
        (BPair.mul_mul_mul_comm Wn (ground.bpow (BPair.ofPos ed) b)
          (capF e0n e0d K p)
          (ground.bpow (BPair.ofPos ed) (N - b)))

/-- The slab walk's whole price at the cleared ceiling: the cap
against the running prefactor, the square scale's ceiling entering
once per outer key, the clearing's whole power shared. -/
private theorem slabPriceC {mm : Nat} {e0n shB : BPair} {e0d en ed : Pos}
    {N K : Nat}
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hs : BPair.ofNat mm * BPair.ofPos en ≤ shB * BPair.ofPos ed)
    (hshB : BPair.unit ≤ shB) (hNK : N ≤ K) :
    ∀ (P : poly.PPoly) (b w c : Nat) (Wn : BPair),
      BPair.unit ≤ Wn →
      windowsep.mag (BPair.ofNat w * ground.bpow (BPair.ofPos en) b)
          * ground.bpow (BPair.ofPos ed) c
        ≤ Wn * ground.bpow (BPair.ofPos ed) b →
      (∀ j, j < P.length →
        0 < (poly.vnorm (ground.getAt ([] : poly.Poly) P j)).length →
        b + j + (poly.vnorm (ground.getAt ([] : poly.Poly) P j)).length
          ≤ N + 1) →
      windowsep.mag (poly.evalClear (slabGo mm b w P) (BPair.ofPos en) ed N)
          * ground.bpow (BPair.ofPos ed) c
          * ground.bpow (BPair.ofPos e0d) K
        ≤ Wn * capS e0n e0d shB K P * ground.bpow (BPair.ofPos ed) N
  | [], _, _, _, Wn, _, _, _ => by
    refine ground.leB_congr ?_ ?_ (ground.leB_refl BPair.unit)
    · exact BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.mul_congr_left
            (BPair.mul_congr_left
              (BPair.oneValue_of_eq
                (windowsep.mag_unitLe (ground.leB_refl BPair.unit)))))
          (BPair.oneValue_trans
            (BPair.mul_congr_left (BPair.unit_mul _))
            (BPair.unit_mul _)))
    · exact BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.mul_congr_left (BPair.mul_unit Wn))
          (BPair.unit_mul _))
  | p :: t, b, w, c, Wn, hWn, hW, hsh => by
    have hEd : BPair.unit ≤ BPair.ofPos ed :=
      ground.leB_of_lt (ground.unitLtOfPos ed)
    have hE0d : BPair.unit ≤ BPair.ofPos e0d :=
      ground.leB_of_lt (ground.unitLtOfPos e0d)
    have hterm := slabTermPriceC he hNK p b w c Wn hWn hW
      (hsh 0 (Nat.succ_pos t.length))
    have hWnext : windowsep.mag (BPair.ofNat (w * mm)
          * ground.bpow (BPair.ofPos en) (b + 1))
        * ground.bpow (BPair.ofPos ed) c
      ≤ Wn * shB * ground.bpow (BPair.ofPos ed) (b + 1) := by
      have hsplit : (windowsep.mag (BPair.ofNat (w * mm)
            * ground.bpow (BPair.ofPos en) (b + 1))).oneValue
          (windowsep.mag (BPair.ofNat w * ground.bpow (BPair.ofPos en) b)
            * (BPair.ofNat mm * BPair.ofPos en)) := by
        refine BPair.oneValue_trans
          (windowsep.mag_congr
            (BPair.oneValue_trans
              (BPair.mul_congr (BPair.ofNat_mul w mm)
                (BPair.oneValue_trans
                  (ground.bpow_add (BPair.ofPos en) b 1)
                  (BPair.mul_congr (BPair.oneValue_refl _)
                    (ground.bpow_one_read (BPair.ofPos en)))))
              (BPair.oneValue_of_eq
                (BPair.mul_mul_mul_comm (BPair.ofNat w) (BPair.ofNat mm)
                  (ground.bpow (BPair.ofPos en) b) (BPair.ofPos en))))) ?_
        exact BPair.oneValue_trans (windowsep.mag_mul _ _)
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_of_eq
              (windowsep.mag_unitLe
                (ground.unitLeMul (ground.unitLeOfNat mm)
                  (ground.leB_of_lt (ground.unitLtOfPos en))))))
      have hstep := ground.leB_mul_mono
        (ground.unitLeMul (ground.unitLeOfNat mm)
          (ground.leB_of_lt (ground.unitLtOfPos en)))
        (ground.unitLeMul hWn (windowsep.unitLe_bpow hEd b)) hW hs
      refine ground.leB_congr ?_ ?_ hstep
      · exact BPair.oneValue_symm
          (BPair.oneValue_trans (BPair.mul_congr_left hsplit)
            (BPair.oneValue_of_eq
              (BPair.mul_right_comm
                (windowsep.mag (BPair.ofNat w
                  * ground.bpow (BPair.ofPos en) b))
                (BPair.ofNat mm * BPair.ofPos en)
                (ground.bpow (BPair.ofPos ed) c))))
      · refine BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.mul_mul_mul_comm Wn (ground.bpow (BPair.ofPos ed) b)
              shB (BPair.ofPos ed))) ?_
        exact BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm
            (BPair.oneValue_trans (ground.bpow_add (BPair.ofPos ed) b 1)
              (BPair.mul_congr (BPair.oneValue_refl _)
                (ground.bpow_one_read (BPair.ofPos ed)))))
    have hIH := slabPriceC he hs hshB hNK t (b + 1) (w * mm) c (Wn * shB)
      (ground.unitLeMul hWn hshB) hWnext
      (fun j hj hpos => by
        have h0 := hsh (j + 1) (Nat.succ_lt_succ hj) hpos
        rw [← Nat.add_assoc b j 1, Nat.add_right_comm b j 1] at h0
        exact h0)
    have hadd : windowsep.mag (poly.evalClear
        (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
          (slabGo mm (b + 1) (w * mm) t)) (BPair.ofPos en) ed N)
        ≤ windowsep.mag (poly.evalClear
            (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
            (BPair.ofPos en) ed N)
          + windowsep.mag (poly.evalClear (slabGo mm (b + 1) (w * mm) t)
            (BPair.ofPos en) ed N) :=
      ground.leB_congr_left
        (BPair.oneValue_symm
          (windowsep.mag_congr (poly.evalClear_add _ _ _ _ _)))
        (windowsep.mag_add_le _ _)
    show windowsep.mag (poly.evalClear
        (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
          (slabGo mm (b + 1) (w * mm) t)) (BPair.ofPos en) ed N)
        * ground.bpow (BPair.ofPos ed) c
        * ground.bpow (BPair.ofPos e0d) K
      ≤ Wn * (capF e0n e0d K p + shB * capS e0n e0d shB K t)
        * ground.bpow (BPair.ofPos ed) N
    refine ground.leB_trans
      (ground.leB_mul_mono (windowsep.unitLe_bpow hE0d K)
        (ground.unitLeMul
          (ground.unitLeAdd (windowsep.unitLe_mag _)
            (windowsep.unitLe_mag _))
          (windowsep.unitLe_bpow hEd c))
        (ground.leB_mul_mono (windowsep.unitLe_bpow hEd c)
          (ground.unitLeAdd (windowsep.unitLe_mag _)
            (windowsep.unitLe_mag _))
          hadd (ground.leB_refl _))
        (ground.leB_refl _)) ?_
    have hdist : (windowsep.mag (poly.evalClear
            (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
            (BPair.ofPos en) ed N)
          + windowsep.mag (poly.evalClear (slabGo mm (b + 1) (w * mm) t)
            (BPair.ofPos en) ed N))
          * ground.bpow (BPair.ofPos ed) c
          * ground.bpow (BPair.ofPos e0d) K
        = windowsep.mag (poly.evalClear
              (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
              (BPair.ofPos en) ed N)
            * ground.bpow (BPair.ofPos ed) c
            * ground.bpow (BPair.ofPos e0d) K
          + windowsep.mag (poly.evalClear (slabGo mm (b + 1) (w * mm) t)
              (BPair.ofPos en) ed N)
            * ground.bpow (BPair.ofPos ed) c
            * ground.bpow (BPair.ofPos e0d) K := by
      rw [BPair.right_distrib
          (windowsep.mag (poly.evalClear
            (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
            (BPair.ofPos en) ed N))
          (windowsep.mag (poly.evalClear (slabGo mm (b + 1) (w * mm) t)
            (BPair.ofPos en) ed N))
          (ground.bpow (BPair.ofPos ed) c),
        BPair.right_distrib
          (windowsep.mag (poly.evalClear
              (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
              (BPair.ofPos en) ed N)
            * ground.bpow (BPair.ofPos ed) c)
          (windowsep.mag (poly.evalClear (slabGo mm (b + 1) (w * mm) t)
              (BPair.ofPos en) ed N)
            * ground.bpow (BPair.ofPos ed) c)
          (ground.bpow (BPair.ofPos e0d) K)]
    refine ground.leB_congr_left (BPair.oneValue_of_eq hdist.symm) ?_
    refine ground.leB_congr_right ?_ (ground.leB_add hterm hIH)
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.right_distrib (Wn * capF e0n e0d K p)
          (Wn * shB * capS e0n e0d shB K t)
          (ground.bpow (BPair.ofPos ed) N)).symm) ?_
    refine BPair.mul_congr_left ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_of_eq
          (BPair.mul_assoc Wn shB (capS e0n e0d shB K t))))
      ?_
    exact BPair.oneValue_of_eq
      (BPair.left_distrib Wn (capF e0n e0d K p)
        (shB * capS e0n e0d shB K t)).symm

/-! The box device: the scale-free part's chained side read against
the floors' join, the remainder's two chained arm reads, and the
deeper tails' two ceiling-fold caps. -/

/-- The origin split: a list is its origin coefficient joined to its
shifted tail. -/
private theorem headTailSplit : ∀ p : poly.Poly,
    poly.oneValue p
      (poly.add [ground.getAt BPair.unit p 0]
        (poly.shiftUp 1 (List.drop 1 p)))
  | [] => ⟨BPair.add_unit BPair.unit, trivial⟩
  | c :: t => ⟨BPair.oneValue_symm (BPair.add_unit c), poly.oneValue_refl t⟩

/-- The slab walk splits into its origin slabs and its shifted tail
slabs. -/
private theorem slabGo_split (mm : Nat) : ∀ (b w : Nat) (P : poly.PPoly),
    poly.oneValue (slabGo mm b w P)
      (poly.add
        (slabGo mm b w (P.map (fun p => [ground.getAt BPair.unit p 0])))
        (slabGo mm b w (P.map (fun p => poly.shiftUp 1 (List.drop 1 p)))))
  | _, _, [] => poly.oneValue_refl _
  | b, w, p :: t => by
    show poly.oneValue
      (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
        (slabGo mm (b + 1) (w * mm) t))
      (poly.add
        (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w)
            [ground.getAt BPair.unit p 0]))
          (slabGo mm (b + 1) (w * mm)
            (t.map (fun p => [ground.getAt BPair.unit p 0]))))
        (poly.add (poly.shiftUp b (poly.scaleP (BPair.ofNat w)
            (poly.shiftUp 1 (List.drop 1 p))))
          (slabGo mm (b + 1) (w * mm)
            (t.map (fun p => poly.shiftUp 1 (List.drop 1 p))))))
    refine poly.oneValue_trans ?_
      (poly.oneValue_symm (poly.add_shuffle _ _ _ _))
    refine poly.add_congr ?_ (slabGo_split mm (b + 1) (w * mm) t)
    refine poly.oneValue_trans
      (poly.shiftUp_ov b
        (poly.oneValue_scaleP (BPair.ofNat w) (headTailSplit p))) ?_
    refine poly.oneValue_trans
      (poly.shiftUp_ov b (poly.scaleP_sum (BPair.ofNat w) _ _)) ?_
    exact poly.shiftUp_add b _ _

/-- The clearance walk's per-key read. -/
private theorem bleGo_at {K : Nat} : ∀ (b : Nat) (l : poly.PPoly),
    bleGo K b l = true →
    ∀ j, j < l.length →
      b + j + (ground.getAt ([] : poly.Poly) l j).length ≤ K + 1
  | _, [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | b, p :: _, h, 0, _ => by
    rw [Nat.add_zero]
    exact Nat.le_of_ble_eq_true (ground.andSplitB h).1
  | b, _ :: t, h, j + 1, hj => by
    have hIH := bleGo_at (b + 1) t (ground.andSplitB h).2 j
      (Nat.lt_of_succ_lt_succ hj)
    rw [← Nat.add_assoc b j 1, Nat.add_right_comm b j 1]
    exact hIH

/-- The shifted-tail slabs' walk is the dropped slabs' walk one
scale key up. -/
private theorem slabGo_shiftTail (mm : Nat) :
    ∀ (b w : Nat) (P : poly.PPoly),
    poly.oneValue
      (slabGo mm b w (P.map (fun p => poly.shiftUp 1 (List.drop 1 p))))
      (slabGo mm (b + 1) w (P.map (List.drop 1)))
  | _, _, [] => poly.oneValue_refl _
  | b, w, p :: t => by
    show poly.oneValue
      (poly.add (poly.shiftUp b
          (poly.scaleP (BPair.ofNat w) (poly.shiftUp 1 (List.drop 1 p))))
        (slabGo mm (b + 1) (w * mm)
          (t.map (fun p => poly.shiftUp 1 (List.drop 1 p)))))
      (poly.add (poly.shiftUp (b + 1)
          (poly.scaleP (BPair.ofNat w) (List.drop 1 p)))
        (slabGo mm (b + 1 + 1) (w * mm) (t.map (List.drop 1))))
    refine poly.add_congr ?_ (slabGo_shiftTail mm (b + 1) (w * mm) t)
    rw [← poly.shiftUp_shiftUp b 1
      (poly.scaleP (BPair.ofNat w) (List.drop 1 p))]
    exact poly.shiftUp_ov b (scaleP_shift (BPair.ofNat w) 1 (List.drop 1 p))


/-- The first slab's tail price read against its cap conjunct: the
clearing's powers withdraw and the price lands at the floor. -/
private theorem capCancelB {Mb F1 cB e0n : BPair} {e0d ed en : Pos}
    {K J : Nat}
    (hF1 : BPair.unit ≤ F1)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hp : Mb * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) K
        ≤ BPair.ofPos en * F1 * ground.bpow (BPair.ofPos ed) J)
    (hcap : e0n * F1 ≤ cB * ground.bpow (BPair.ofPos e0d) (K + 1)) :
    Mb * BPair.ofPos ed
      ≤ cB * ground.bpow (BPair.ofPos ed) J * BPair.ofPos ed := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hEn : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hE0d : BPair.unit ≤ BPair.ofPos e0d :=
    ground.leB_of_lt (ground.unitLtOfPos e0d)
  have hEdJ : BPair.unit ≤ ground.bpow (BPair.ofPos ed) J :=
    windowsep.unitLe_bpow hEd J
  have hE0n : BPair.unit ≤ e0n := unitLe_of_clear he
  have hcB : BPair.unit ≤ cB * ground.bpow (BPair.ofPos e0d) (K + 1) :=
    ground.leB_trans (ground.unitLeMul hE0n hF1) hcap
  refine ground.leB_unscale
    (ground.unitLtMul
      (windowsep.unitLt_bpow (ground.unitLtOfPos e0d) K)
      (ground.unitLtOfPos e0d)) ?_
  have heq1 : Mb * BPair.ofPos ed
        * (ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d)
      = Mb * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) K
        * BPair.ofPos e0d := by
    rw [← BPair.mul_assoc]
  have heq2 : BPair.ofPos en * F1 * ground.bpow (BPair.ofPos ed) J
        * BPair.ofPos e0d
      = BPair.ofPos en * BPair.ofPos e0d
        * (F1 * ground.bpow (BPair.ofPos ed) J) := by
    rw [BPair.mul_right_comm (BPair.ofPos en * F1)
        (ground.bpow (BPair.ofPos ed) J) (BPair.ofPos e0d),
      BPair.mul_assoc (BPair.ofPos en) F1 (BPair.ofPos e0d),
      BPair.mul_comm F1 (BPair.ofPos e0d),
      ← BPair.mul_assoc (BPair.ofPos en) (BPair.ofPos e0d) F1,
      BPair.mul_assoc (BPair.ofPos en * BPair.ofPos e0d) F1
        (ground.bpow (BPair.ofPos ed) J)]
  have heq3 : e0n * BPair.ofPos ed * (F1 * ground.bpow (BPair.ofPos ed) J)
      = e0n * F1 * (BPair.ofPos ed * ground.bpow (BPair.ofPos ed) J) :=
    BPair.mul_mul_mul_comm e0n (BPair.ofPos ed) F1
      (ground.bpow (BPair.ofPos ed) J)
  have heq4 : cB * (ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d)
        * (BPair.ofPos ed * ground.bpow (BPair.ofPos ed) J)
      = cB * ground.bpow (BPair.ofPos ed) J * BPair.ofPos ed
        * (ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d) := by
    rw [BPair.mul_mul_mul_comm cB
        (ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d)
        (BPair.ofPos ed) (ground.bpow (BPair.ofPos ed) J),
      BPair.mul_comm (ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d)
        (ground.bpow (BPair.ofPos ed) J),
      ← BPair.mul_assoc (cB * BPair.ofPos ed)
        (ground.bpow (BPair.ofPos ed) J)
        (ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d),
      BPair.mul_right_comm cB (BPair.ofPos ed)
        (ground.bpow (BPair.ofPos ed) J)]
  refine ground.leB_congr_left (BPair.oneValue_of_eq heq1.symm) ?_
  refine ground.leB_congr_right (BPair.oneValue_of_eq heq4) ?_
  refine ground.leB_trans
    (ground.leB_mul_mono hE0d
      (ground.unitLeMul (ground.unitLeMul hEn hF1) hEdJ)
      hp (ground.leB_refl _)) ?_
  refine ground.leB_congr_left (BPair.oneValue_of_eq heq2.symm) ?_
  refine ground.leB_trans
    (ground.leB_mul_mono
      (ground.unitLeMul hF1 hEdJ)
      (ground.unitLeMul hE0n hEd) he (ground.leB_refl _)) ?_
  refine ground.leB_congr_left (BPair.oneValue_of_eq heq3.symm) ?_
  refine ground.leB_trans
    (ground.leB_mul_mono (ground.unitLeMul hEd hEdJ) hcB hcap
      (ground.leB_refl _)) ?_
  exact ground.leB_congr_left
    (BPair.oneValue_symm
      (BPair.mul_congr_left
        (BPair.mul_congr (BPair.oneValue_refl cB)
          (bpowSucc (BPair.ofPos e0d) K))))
    (ground.leB_refl _)

/-- The scale slab's tail price read against its squared cap
conjunct: the clearing's powers withdraw and the squared comparison
reads back at the floor. -/
private theorem capCancelA {Mg G fA e0n shB : BPair} {e0d ed en : Pos}
    {K J m : Nat}
    (hMg : BPair.unit ≤ Mg) (hG : BPair.unit ≤ G) (hfA : BPair.unit ≤ fA)
    (hshB : BPair.unit ≤ shB)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hs : BPair.ofNat (m * m) * BPair.ofPos en ≤ shB * BPair.ofPos ed)
    (hp : Mg * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) K
        ≤ BPair.ofNat m * BPair.ofPos en
          * (G * ground.bpow (BPair.ofPos ed) J))
    (hcap : e0n * (shB * (G * G))
      ≤ fA * fA * ground.bpow (BPair.ofPos e0d) (2 * K + 1)) :
    Mg * BPair.ofPos ed
      ≤ fA * ground.bpow (BPair.ofPos ed) J * BPair.ofPos ed := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hEn : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hE0d : BPair.unit ≤ BPair.ofPos e0d :=
    ground.leB_of_lt (ground.unitLtOfPos e0d)
  have hE0n : BPair.unit ≤ e0n := unitLe_of_clear he
  have hDJ : BPair.unit ≤ ground.bpow (BPair.ofPos ed) J :=
    windowsep.unitLe_bpow hEd J
  have hE : BPair.unit ≤ ground.bpow (BPair.ofPos e0d) K :=
    windowsep.unitLe_bpow hE0d K
  have hU : BPair.unit ≤ Mg * BPair.ofPos ed := ground.unitLeMul hMg hEd
  have hA : BPair.unit ≤ BPair.ofNat m * BPair.ofPos en :=
    ground.unitLeMul (ground.unitLeOfNat m) hEn
  have hB : BPair.unit ≤ G * ground.bpow (BPair.ofPos ed) J :=
    ground.unitLeMul hG hDJ
  have hW : BPair.unit ≤ fA * ground.bpow (BPair.ofPos ed) J
      * BPair.ofPos ed :=
    ground.unitLeMul (ground.unitLeMul hfA hDJ) hEd
  -- the prefactor's square against the box and the ceiling
  have hsqA : BPair.ofNat m * BPair.ofPos en
        * (BPair.ofNat m * BPair.ofPos en) * BPair.ofPos e0d
      ≤ e0n * shB * (BPair.ofPos ed * BPair.ofPos ed) := by
    have hcoef : (BPair.ofNat m * BPair.ofPos en
          * (BPair.ofNat m * BPair.ofPos en) * BPair.ofPos e0d).oneValue
        (BPair.ofNat (m * m) * BPair.ofPos en
          * (BPair.ofPos en * BPair.ofPos e0d)) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.oneValue_of_eq
            (BPair.mul_mul_mul_comm (BPair.ofNat m) (BPair.ofPos en)
              (BPair.ofNat m) (BPair.ofPos en)))) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.mul_congr_left
            (BPair.oneValue_symm (BPair.ofNat_mul m m)))) ?_
      have hz : BPair.ofNat (m * m) * (BPair.ofPos en * BPair.ofPos en)
            * BPair.ofPos e0d
          = BPair.ofNat (m * m) * BPair.ofPos en
            * (BPair.ofPos en * BPair.ofPos e0d) := by
        rw [BPair.mul_assoc (BPair.ofNat (m * m))
            (BPair.ofPos en * BPair.ofPos en) (BPair.ofPos e0d),
          BPair.mul_assoc (BPair.ofPos en) (BPair.ofPos en)
            (BPair.ofPos e0d),
          ← BPair.mul_assoc (BPair.ofNat (m * m)) (BPair.ofPos en)
            (BPair.ofPos en * BPair.ofPos e0d)]
      exact BPair.oneValue_of_eq hz
    refine ground.leB_congr_left (BPair.oneValue_symm hcoef) ?_
    refine ground.leB_trans
      (ground.leB_mul_mono (ground.unitLeMul hEn hE0d)
        (ground.unitLeMul hshB hEd) hs he) ?_
    have hz2 : shB * BPair.ofPos ed * (e0n * BPair.ofPos ed)
        = e0n * shB * (BPair.ofPos ed * BPair.ofPos ed) := by
      rw [BPair.mul_mul_mul_comm shB (BPair.ofPos ed) e0n (BPair.ofPos ed),
        BPair.mul_comm shB e0n]
    exact ground.leB_congr_right (BPair.oneValue_of_eq hz2)
      (ground.leB_refl _)
  -- the cap conjunct at the split clearing powers
  have hcap' : e0n * shB * (G * G)
      ≤ fA * fA * (ground.bpow (BPair.ofPos e0d) K
        * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d) := by
    refine ground.leB_congr_left
      (BPair.oneValue_of_eq
        (BPair.mul_assoc e0n shB (G * G)).symm) ?_
    exact ground.leB_congr_right
      (BPair.mul_congr (BPair.oneValue_refl _)
        (bpowTwoK (BPair.ofPos e0d) K)) hcap
  -- the squared price
  have hsq : Mg * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) K
        * (Mg * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) K)
      ≤ BPair.ofNat m * BPair.ofPos en
          * (G * ground.bpow (BPair.ofPos ed) J)
        * (BPair.ofNat m * BPair.ofPos en
          * (G * ground.bpow (BPair.ofPos ed) J)) :=
    ground.leB_mul_mono (ground.unitLeMul hU hE) (ground.unitLeMul hA hB)
      hp hp
  have hsqe : Mg * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) K
        * (Mg * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) K)
        * BPair.ofPos e0d
      ≤ BPair.ofNat m * BPair.ofPos en
          * (G * ground.bpow (BPair.ofPos ed) J)
        * (BPair.ofNat m * BPair.ofPos en
          * (G * ground.bpow (BPair.ofPos ed) J))
        * BPair.ofPos e0d :=
    ground.leB_mul_mono hE0d
      (ground.unitLeMul (ground.unitLeMul hA hB) (ground.unitLeMul hA hB))
      hsq (ground.leB_refl _)
  have eqL : Mg * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) K
        * (Mg * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) K)
        * BPair.ofPos e0d
      = Mg * BPair.ofPos ed * (Mg * BPair.ofPos ed)
        * (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d) := by
    rw [BPair.mul_mul_mul_comm (Mg * BPair.ofPos ed)
        (ground.bpow (BPair.ofPos e0d) K) (Mg * BPair.ofPos ed)
        (ground.bpow (BPair.ofPos e0d) K),
      BPair.mul_assoc (Mg * BPair.ofPos ed * (Mg * BPair.ofPos ed))
        (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K) (BPair.ofPos e0d)]
  have eq2 : BPair.ofNat m * BPair.ofPos en
        * (G * ground.bpow (BPair.ofPos ed) J)
        * (BPair.ofNat m * BPair.ofPos en
          * (G * ground.bpow (BPair.ofPos ed) J))
        * BPair.ofPos e0d
      = BPair.ofNat m * BPair.ofPos en * (BPair.ofNat m * BPair.ofPos en)
          * BPair.ofPos e0d
        * (G * ground.bpow (BPair.ofPos ed) J
          * (G * ground.bpow (BPair.ofPos ed) J)) := by
    rw [BPair.mul_mul_mul_comm (BPair.ofNat m * BPair.ofPos en)
        (G * ground.bpow (BPair.ofPos ed) J)
        (BPair.ofNat m * BPair.ofPos en)
        (G * ground.bpow (BPair.ofPos ed) J),
      BPair.mul_right_comm
        (BPair.ofNat m * BPair.ofPos en * (BPair.ofNat m * BPair.ofPos en))
        (G * ground.bpow (BPair.ofPos ed) J
          * (G * ground.bpow (BPair.ofPos ed) J))
        (BPair.ofPos e0d)]
  have eq3 : e0n * shB * (BPair.ofPos ed * BPair.ofPos ed)
        * (G * ground.bpow (BPair.ofPos ed) J
          * (G * ground.bpow (BPair.ofPos ed) J))
      = e0n * shB * (G * G)
        * (BPair.ofPos ed * BPair.ofPos ed
          * (ground.bpow (BPair.ofPos ed) J
            * ground.bpow (BPair.ofPos ed) J)) := by
    rw [BPair.mul_mul_mul_comm G (ground.bpow (BPair.ofPos ed) J) G
        (ground.bpow (BPair.ofPos ed) J),
      BPair.mul_mul_mul_comm (e0n * shB)
        (BPair.ofPos ed * BPair.ofPos ed) (G * G)
        (ground.bpow (BPair.ofPos ed) J
          * ground.bpow (BPair.ofPos ed) J)]
  have eq4 : fA * fA * (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d)
        * (BPair.ofPos ed * BPair.ofPos ed
          * (ground.bpow (BPair.ofPos ed) J
            * ground.bpow (BPair.ofPos ed) J))
      = fA * ground.bpow (BPair.ofPos ed) J * BPair.ofPos ed
          * (fA * ground.bpow (BPair.ofPos ed) J * BPair.ofPos ed)
        * (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d) := by
    rw [BPair.mul_mul_mul_comm (fA * ground.bpow (BPair.ofPos ed) J)
        (BPair.ofPos ed) (fA * ground.bpow (BPair.ofPos ed) J)
        (BPair.ofPos ed),
      BPair.mul_mul_mul_comm fA (ground.bpow (BPair.ofPos ed) J) fA
        (ground.bpow (BPair.ofPos ed) J),
      BPair.mul_assoc (fA * fA
          * (ground.bpow (BPair.ofPos ed) J
            * ground.bpow (BPair.ofPos ed) J))
        (BPair.ofPos ed * BPair.ofPos ed)
        (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d),
      BPair.mul_mul_mul_comm (fA * fA)
        (ground.bpow (BPair.ofPos ed) J
          * ground.bpow (BPair.ofPos ed) J)
        (BPair.ofPos ed * BPair.ofPos ed)
        (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d),
      BPair.mul_mul_mul_comm (fA * fA)
        (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d)
        (BPair.ofPos ed * BPair.ofPos ed)
        (ground.bpow (BPair.ofPos ed) J
          * ground.bpow (BPair.ofPos ed) J),
      BPair.mul_comm (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d)
        (ground.bpow (BPair.ofPos ed) J
          * ground.bpow (BPair.ofPos ed) J)]
  -- the chain
  have hchain : Mg * BPair.ofPos ed * (Mg * BPair.ofPos ed)
        * (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d)
      ≤ fA * ground.bpow (BPair.ofPos ed) J * BPair.ofPos ed
          * (fA * ground.bpow (BPair.ofPos ed) J * BPair.ofPos ed)
        * (ground.bpow (BPair.ofPos e0d) K
          * ground.bpow (BPair.ofPos e0d) K * BPair.ofPos e0d) := by
    refine ground.leB_congr_left (BPair.oneValue_of_eq eqL) ?_
    refine ground.leB_congr_right (BPair.oneValue_of_eq eq4) ?_
    refine ground.leB_trans hsqe ?_
    refine ground.leB_congr_left (BPair.oneValue_of_eq eq2.symm) ?_
    refine ground.leB_trans
      (ground.leB_mul_mono (ground.unitLeMul hB hB)
        (ground.unitLeMul (ground.unitLeMul hE0n hshB)
          (ground.unitLeMul hEd hEd))
        hsqA (ground.leB_refl _)) ?_
    refine ground.leB_congr_left (BPair.oneValue_of_eq eq3.symm) ?_
    exact ground.leB_mul_mono
      (ground.unitLeMul (ground.unitLeMul hEd hEd)
        (ground.unitLeMul hDJ hDJ))
      (ground.unitLeMul (ground.unitLeMul hfA hfA)
        (ground.unitLeMul (ground.unitLeMul hE hE) hE0d))
      hcap' (ground.leB_refl _)
  refine ground.leB_of_sq_le hW (ground.leB_not_lt ?_)
  exact ground.leB_unscale
    (ground.unitLtMul
      (ground.unitLtMul (windowsep.unitLt_bpow (ground.unitLtOfPos e0d) K)
        (windowsep.unitLt_bpow (ground.unitLtOfPos e0d) K))
      (ground.unitLtOfPos e0d))
    hchain

/-- Every slab vacant makes the walk vacant: the shifted scaled
entries and the recursion's tail read unit tails throughout. -/
private theorem slabGo_vacAll (mm : Nat) : ∀ (b w : Nat) (P : poly.PPoly),
    (∀ j, j < P.length →
      (poly.vnorm (ground.getAt ([] : poly.Poly) P j)).length = 0) →
    poly.unitTail (slabGo mm b w P)
  | _, _, [], _ => trivial
  | b, w, p :: t, h => by
    refine poly.unitTail_sum ?_ ?_
    · refine poly.unitTail_shiftUp b ?_
      refine poly.scaleP_unitTail (BPair.ofNat w) p ?_
      have h0 := h 0 (Nat.succ_pos t.length)
      match hv : poly.vnorm p with
      | [] =>
        exact poly.unitTail_oneValue_right
          (q := ([] : poly.Poly)) True.intro
          (show poly.oneValue [] p from hv ▸ poly.vnorm_ov p)
      | c :: r =>
        rw [show ground.getAt ([] : poly.Poly) (p :: t) 0 = p from rfl,
          hv] at h0
        exact Nat.noConfusion h0
    · exact slabGo_vacAll mm (b + 1) (w * mm) t
        (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))

/-- The collected arm's monomial exchange, left side. -/
private theorem mulShufL (a b c d e f g : BPair) :
    a * b * (c * d) * e * (f * g)
      = c * a * e * (b * g) * (d * f) := by
  rw [BPair.mul_mul_mul_comm a b c d,
    BPair.mul_comm a c,
    BPair.mul_right_comm (c * a) (b * d) e,
    BPair.mul_comm f g,
    BPair.mul_assoc (c * a * e) (b * d) (g * f),
    BPair.mul_mul_mul_comm b d g f,
    ← BPair.mul_assoc (c * a * e) (b * g) (d * f)]

/-- The collected arm's monomial exchange, right side. -/
private theorem mulShufR (c e x s p : BPair) :
    c * e * (x * e) * (s * p)
      = x * c * (s * (p * (e * e))) := by
  rw [BPair.mul_mul_mul_comm c e x e,
    BPair.mul_comm c x,
    BPair.mul_assoc (x * c) (e * e) (s * p),
    BPair.mul_comm (e * e) (s * p),
    BPair.mul_assoc s p (e * e)]

/-- The priced arm's weight exchange at the squared cancel. -/
private theorem mulShufD (x c s p : BPair) :
    x * c * (s * p) = c * (x * s * p) := by
  rw [BPair.mul_comm x c,
    BPair.mul_assoc c x (s * p),
    ← BPair.mul_assoc x s p]

/-- The two-shift slab price at the kept clearing: the walk
renormalized to the origin with the shift's clearing read off the
evaluation, the origin walk priced at the vacant weight, and the
shift's second scale power read at the scale's bound, so the
cleared side gains one further ceiling power. -/
private theorem slabPriceC2 {mm : Nat} {e0n shB : BPair} {e0d en ed : Pos}
    {K : Nat}
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hs : BPair.ofNat mm * BPair.ofPos en ≤ shB * BPair.ofPos ed)
    (hshB : BPair.unit ≤ shB) (P : poly.PPoly) (w : Nat)
    (hsh : ∀ j, j < P.length →
      0 < (poly.vnorm (ground.getAt ([] : poly.Poly) P j)).length →
      2 + j + (poly.vnorm (ground.getAt ([] : poly.Poly) P j)).length
        ≤ K + 1) :
    windowsep.mag (poly.evalClear (slabGo mm 2 w P) (BPair.ofPos en) ed K)
        * BPair.ofPos ed * ground.bpow (BPair.ofPos e0d) (K + 1)
      ≤ e0n * (BPair.ofNat w * BPair.ofPos en)
        * (capS e0n e0d shB K P * ground.bpow (BPair.ofPos ed) K) := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hEn : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hE0d : BPair.unit ≤ BPair.ofPos e0d :=
    ground.leB_of_lt (ground.unitLtOfPos e0d)
  have hE0n : BPair.unit ≤ e0n := unitLe_of_clear he
  have hRHS : BPair.unit ≤ e0n * (BPair.ofNat w * BPair.ofPos en)
      * (capS e0n e0d shB K P * ground.bpow (BPair.ofPos ed) K) :=
    ground.unitLeMul (ground.unitLeMul hE0n
      (ground.unitLeMul (ground.unitLeOfNat w) hEn))
      (ground.unitLeMul (unitLe_capS hE0n hshB P)
        (windowsep.unitLe_bpow hEd K))
  match Nat.lt_or_ge K 2 with
  | Or.inl hK2 =>
    have hvac : poly.unitTail (slabGo mm 2 w P) := by
      refine slabGo_vacAll mm 2 w P (fun j hj => ?_)
      match hv : poly.vnorm (ground.getAt ([] : poly.Poly) P j) with
      | [] => rfl
      | c :: r =>
        have hK := hsh j hj (by rw [hv]; exact Nat.succ_pos r.length)
        rw [hv] at hK
        have h3 : 2 + 1 ≤ 2 + j + (c :: r).length :=
          Nat.add_le_add (Nat.add_le_add_left (Nat.zero_le j) 2)
            (Nat.succ_le_succ (Nat.zero_le r.length))
        have h2K : 2 ≤ K := Nat.le_of_succ_le_succ (Nat.le_trans h3 hK)
        exact absurd (Nat.lt_of_lt_of_le hK2 h2K) (Nat.lt_irrefl K)
    have hone : (windowsep.mag (poly.evalClear (slabGo mm 2 w P)
          (BPair.ofPos en) ed K)
        * BPair.ofPos ed
        * ground.bpow (BPair.ofPos e0d) (K + 1)).oneValue BPair.unit := by
      refine BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.mul_congr_left
          (BPair.oneValue_trans
            (windowsep.mag_congr (poly.evalClear_congr
              (poly.unitTail_oneValue (q := ([] : poly.Poly))
                hvac True.intro)
              (BPair.ofPos en) ed K))
            (show (windowsep.mag (poly.evalClear ([] : poly.Poly)
                  (BPair.ofPos en) ed K)).oneValue BPair.unit from
              BPair.oneValue_of_eq
                (windowsep.mag_unitLe
                  (ground.leB_refl BPair.unit)))))) ?_
      exact BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.unit_mul _)) (BPair.unit_mul _)
    exact ground.leB_congr_left (BPair.oneValue_symm hone) hRHS
  | Or.inr hK2 =>
    obtain ⟨d, hd⟩ := Nat.le.dest hK2
    rw [Nat.add_comm] at hd
    subst hd
    have hsh0 : ∀ j, j < P.length →
        0 < (poly.vnorm (ground.getAt ([] : poly.Poly) P j)).length →
        0 + j + (poly.vnorm (ground.getAt ([] : poly.Poly) P j)).length
          ≤ d + 1 := by
      intro j hj hpos
      have h0 := hsh j hj hpos
      rw [Nat.zero_add]
      rw [Nat.add_assoc 2 j
        (poly.vnorm (ground.getAt ([] : poly.Poly) P j)).length,
        show d + 2 + 1 = 2 + (d + 1) by
          rw [Nat.add_comm d 2, Nat.add_assoc 2 d 1]] at h0
      exact ground.leCancelL 2 h0
    have hpr := slabPriceC he hs hshB (Nat.le_add_right d 2) P 0 1 0
      (BPair.ofNat 1) (ground.unitLeOfNat 1)
      (by
        refine ground.leB_congr_left ?_
          (ground.leB_refl (BPair.ofNat 1 * ground.bpow (BPair.ofPos ed) 0))
        refine BPair.mul_congr ?_ (BPair.oneValue_refl _)
        refine BPair.oneValue_trans
          (show (BPair.ofNat 1).oneValue
              (BPair.ofNat 1 * ground.bpow (BPair.ofPos en) 0) from
            BPair.oneValue_symm (BPair.mul_ofNat_one (BPair.ofNat 1))) ?_
        exact BPair.oneValue_of_eq
          (windowsep.mag_unitLe
            (ground.unitLeMul (ground.unitLeOfNat 1)
              (windowsep.unitLe_bpow hEn 0))).symm)
      hsh0
    have hnorm : (poly.evalClear (slabGo mm 2 w P) (BPair.ofPos en) ed
          (d + 2)).oneValue
        (ground.bpow (BPair.ofPos en) 2
          * (BPair.ofNat w
            * poly.evalClear (slabGo mm 0 1 P) (BPair.ofPos en) ed d)) := by
      refine BPair.oneValue_trans
        (poly.evalClear_congr (slabGo_norm mm 2 w P) (BPair.ofPos en) ed
          (d + 2)) ?_
      refine BPair.oneValue_trans
        (evalClear_shiftUp 2
          (poly.scaleP (BPair.ofNat w) (slabGo mm 0 1 P))
          (BPair.ofPos en) ed (d + 2)) ?_
      exact BPair.mul_congr (BPair.oneValue_refl _)
        (poly.evalClear_scaleP (BPair.ofNat w) (slabGo mm 0 1 P)
          (BPair.ofPos en) ed d)
    have hmagArm : (windowsep.mag (poly.evalClear (slabGo mm 2 w P)
          (BPair.ofPos en) ed (d + 2))).oneValue
        (ground.bpow (BPair.ofPos en) 2
          * (BPair.ofNat w
            * windowsep.mag (poly.evalClear (slabGo mm 0 1 P)
              (BPair.ofPos en) ed d))) := by
      refine BPair.oneValue_trans (windowsep.mag_congr hnorm) ?_
      refine BPair.oneValue_trans
        (windowsep.mag_mul (ground.bpow (BPair.ofPos en) 2)
          (BPair.ofNat w
            * poly.evalClear (slabGo mm 0 1 P) (BPair.ofPos en) ed d)) ?_
      refine BPair.mul_congr
        (BPair.oneValue_of_eq
          (windowsep.mag_unitLe (windowsep.unitLe_bpow hEn 2))) ?_
      refine BPair.oneValue_trans
        (windowsep.mag_mul (BPair.ofNat w)
          (poly.evalClear (slabGo mm 0 1 P) (BPair.ofPos en) ed d)) ?_
      exact BPair.mul_congr_left
        (BPair.oneValue_of_eq
          (windowsep.mag_unitLe (ground.unitLeOfNat w)))
    have hpr' : windowsep.mag (poly.evalClear (slabGo mm 0 1 P)
          (BPair.ofPos en) ed d)
        * ground.bpow (BPair.ofPos e0d) (d + 2)
      ≤ capS e0n e0d shB (d + 2) P * ground.bpow (BPair.ofPos ed) d := by
      refine ground.leB_congr ?_ ?_ hpr
      · exact BPair.mul_congr_left (BPair.mul_ofNat_one _)
      · exact BPair.mul_congr_left (BPair.ofNat_one_mul _)
    have hM0 : BPair.unit ≤ windowsep.mag (poly.evalClear (slabGo mm 0 1 P)
        (BPair.ofPos en) ed d) := windowsep.unitLe_mag _
    -- the three-factor product comparison at the flattened monomials
    have hmain : BPair.ofNat w * BPair.ofPos en * BPair.ofPos ed
          * (BPair.ofPos en * BPair.ofPos e0d)
          * (windowsep.mag (poly.evalClear (slabGo mm 0 1 P)
              (BPair.ofPos en) ed d)
            * ground.bpow (BPair.ofPos e0d) (d + 2))
        ≤ BPair.ofNat w * BPair.ofPos en * BPair.ofPos ed
          * (e0n * BPair.ofPos ed)
          * (capS e0n e0d shB (d + 2) P * ground.bpow (BPair.ofPos ed) d) :=
      ground.leB_mul_mono
        (ground.unitLeMul hM0
          (windowsep.unitLe_bpow hE0d (d + 2)))
        (ground.unitLeMul
          (ground.unitLeMul (ground.unitLeMul
            (ground.unitLeOfNat w) hEn) hEd)
          (ground.unitLeMul hE0n hEd))
        (ground.leB_mul_mono
          (ground.unitLeMul hEn hE0d)
          (ground.unitLeMul (ground.unitLeMul
            (ground.unitLeOfNat w) hEn) hEd)
          (ground.leB_refl _) he)
        hpr'
    refine ground.leB_congr ?_ ?_ hmain
    · refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.mul_congr hmagArm (BPair.oneValue_refl (BPair.ofPos ed)))
          (bpowSucc (BPair.ofPos e0d) (d + 2))) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.mul_congr
            (BPair.mul_congr
              (BPair.oneValue_trans (bpowSucc (BPair.ofPos en) 1)
                (BPair.mul_congr (ground.bpow_one_read _)
                  (BPair.oneValue_refl _)))
              (BPair.oneValue_refl _))
            (BPair.oneValue_refl _))
          (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_of_eq
        (mulShufL (BPair.ofPos en) (BPair.ofPos en) (BPair.ofNat w)
          (windowsep.mag (poly.evalClear (slabGo mm 0 1 P)
            (BPair.ofPos en) ed d))
          (BPair.ofPos ed) (ground.bpow (BPair.ofPos e0d) (d + 2))
          (BPair.ofPos e0d))
    · refine BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (mulShufR (BPair.ofNat w * BPair.ofPos en) (BPair.ofPos ed)
            e0n (capS e0n e0d shB (d + 2) P)
            (ground.bpow (BPair.ofPos ed) d))) ?_
      refine BPair.mul_congr (BPair.oneValue_refl _) ?_
      refine BPair.mul_congr (BPair.oneValue_refl _) ?_
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans (ground.bpow_add (BPair.ofPos ed) d 2) ?_
      exact BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (bpowSucc (BPair.ofPos ed) 1)
          (BPair.mul_congr (ground.bpow_one_read _)
            (BPair.oneValue_refl _)))

/-- A drop either exhausts its list or takes its count off the
front. -/
private theorem dropVac : ∀ (n : Nat) (p : poly.Poly), p.length ≤ n →
    (List.drop n p).length = 0
  | 0, [], _ => rfl
  | 0, _ :: t, h => absurd h (Nat.not_succ_le_zero t.length)
  | _ + 1, [], _ => rfl
  | n + 1, _ :: t, h => dropVac n t (Nat.le_of_succ_le_succ h)

/-- A drop's key count against the list's, the occupied side the
count identity (`ground.length_drop`) and the vacant side the
drop's own unit read. -/
private theorem lenDrop (n : Nat) (p : poly.Poly) :
    (List.drop n p).length = 0 ∨ (List.drop n p).length + n = p.length :=
  match Nat.lt_or_ge p.length n with
  | Or.inl hlt => Or.inl (dropVac n p (Nat.le_of_lt hlt))
  | Or.inr hge => Or.inr (ground.length_drop n p hge)

/-- The dropped slabs' origin reads are the slabs' own scale-key
reads. -/
private theorem mapLin (P : poly.PPoly) :
    (P.map (List.drop 1)).map (fun p => [ground.getAt BPair.unit p 0])
      = (P.map (fun p => ground.getAt BPair.unit p 1)).map (fun c => [c]) := by
  rw [ground.map_map, ground.map_map]
  exact ground.map_congr_all _ _
    (fun p => congrArg (fun x => [x])
      (ground.getAt_drop BPair.unit 1 p 0)) P
/-- Two scale-key drops are the drop of the pair. -/
private theorem dropDrop : ∀ p : poly.Poly,
    List.drop 1 (List.drop 1 p) = List.drop 2 p
  | [] => rfl
  | _ :: _ => rfl
/-- The twice-dropped slabs are the slabs dropped at the pair. -/
private theorem mapDropDrop (P : poly.PPoly) :
    (P.map (List.drop 1)).map (List.drop 1) = P.map (List.drop 2) := by
  rw [ground.map_map]
  exact ground.map_congr_all _ _ dropDrop P
/-- A slab's key reads are vacant from the clearing up: the shape's
clearance prices each inner list inside the clearing's own key, the
map key joining the slab base at one. -/
private theorem slabKey_vac {L : poly.PPoly} {K b k : Nat}
    (hble : bleGo K b L = true) (hbk : b + k = 1) :
    ∀ j, K ≤ j →
      (ground.getAt BPair.unit
        (L.map (fun p => ground.getAt BPair.unit p k)) j).oneValue
        BPair.unit := by
  intro j hjK
  match Nat.lt_or_ge j L.length with
  | Or.inr hge =>
    refine BPair.oneValue_of_eq ?_
    refine ground.getAt_over BPair.unit _ j ?_
    rw [ground.length_map]
    exact hge
  | Or.inl hlt =>
    have hb := bleGo_at b L hble j hlt
    refine BPair.oneValue_of_eq ?_
    rw [ground.getAt_map ([] : poly.Poly) BPair.unit
      (fun p => ground.getAt BPair.unit p k) L j hlt]
    refine ground.getAt_over BPair.unit
      (ground.getAt ([] : poly.Poly) L j) k ?_
    refine ground.leCancelL (b + j) ?_
    refine Nat.le_trans hb ?_
    rw [Nat.add_right_comm b j k, hbk, Nat.add_comm 1 j]
    exact Nat.succ_le_succ hjK
/-- The scale slab's origin reads are vacant from the clearing up,
the slab vacancy at base one and key nought. -/
private theorem profBaseU_vac {V : poly.PPoly × poly.PPoly} {K : Nat}
    (hsh : profShape V K) :
    ∀ j, K ≤ j →
      (ground.getAt BPair.unit (profBaseU V) j).oneValue BPair.unit :=
  slabKey_vac (ground.andSplitB hsh).2 rfl
/-- The first slab's scale-key reads are vacant from the clearing
up, the slab vacancy at base nought and key one. -/
private theorem profLin_vac {V : poly.PPoly × poly.PPoly} {K : Nat}
    (hsh : profShape V K) :
    ∀ j, K ≤ j →
      (ground.getAt BPair.unit (profLin V) j).oneValue BPair.unit :=
  slabKey_vac (ground.andSplitB hsh).1 rfl

/-- A dropped slab's occupied inner count sits inside the clearing:
the clearance walk's per-key read at the drop, the dropped count
rejoined to the drop. -/
private theorem slabDrop_shape {K : Nat} (b k : Nat) (L : poly.PPoly)
    (hble : bleGo K b L = true) :
    ∀ j, j < (L.map (List.drop k)).length →
      0 < (poly.vnorm (ground.getAt ([] : poly.Poly)
        (L.map (List.drop k)) j)).length →
      b + j + ((poly.vnorm (ground.getAt ([] : poly.Poly)
        (L.map (List.drop k)) j)).length + k) ≤ K + 1 := by
  intro j hj hpos
  rw [ground.length_map] at hj
  rw [ground.getAt_map ([] : poly.Poly) ([] : poly.Poly)
    (List.drop k) L j hj] at hpos ⊢
  have hb := bleGo_at b L hble j hj
  have hvl :=
    poly.vnormLen_le (List.drop k (ground.getAt ([] : poly.Poly) L j))
  have hd : 0 < (List.drop k
      (ground.getAt ([] : poly.Poly) L j)).length :=
    Nat.lt_of_lt_of_le hpos hvl
  match lenDrop k (ground.getAt ([] : poly.Poly) L j) with
  | Or.inl h0 =>
    rw [h0] at hd
    exact absurd hd (Nat.lt_irrefl 0)
  | Or.inr heq =>
    refine Nat.le_trans ?_ hb
    rw [← heq]
    exact Nat.add_le_add_left (Nat.add_le_add_right hvl k) (b + j)

/-- The device's conclusion: at every depth and scale inside the box
at the cleared ceiling, the collapse's cleared evaluation sits
strictly above the sum's unit. -/
theorem boxRead_pos (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : BoxCert) (h : boxRead V e0n e0d C) (m : Nat) (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hlo : C.lo ≤ ⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩)
    (hhi : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair) ≤ C.hi) :
    BPair.unit < poly.evalClear (depthPoly V m) (BPair.ofPos en) ed C.K := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hEn : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hE0n : BPair.unit ≤ e0n := unitLe_of_clear he
  have hxhi : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair)
      ≤ stage.ofB C.shB := CPair.le_trans hhi h.2.1
  have hs : BPair.ofNat (m * m) * BPair.ofPos en
      ≤ C.shB * BPair.ofPos ed := by
    have h0 : (BPair.ofNat (m * m) * BPair.ofPos en).scale Pos.one
        ≤ C.shB.scale ed := hxhi
    rw [BPair.scale_one] at h0
    exact ground.leB_congr_right
      (BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.ofPos_scale ed C.shB))
        (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos ed) C.shB))) h0
  have hshB : BPair.unit ≤ C.shB :=
    stage.unitC_le_fst (CPair.le_trans
      (cunitLe (ground.unitLeMul (ground.unitLeOfNat (m * m)) hEn)) hxhi)
  have hsh1 := ground.andSplitB h.1
  -- the scale-free part's floor read
  have hbaseLt : BPair.unit < poly.evalClear
      (poly.add (profBase V)
        (poly.neg [C.f1L + C.f1D + (C.f2L + C.f2D)]))
      (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K := by
    have hpb : ∀ j, C.K + 1 ≤ j →
        (ground.getAt BPair.unit
          (poly.add (profBase V) (poly.neg [C.f1L + C.f1D + (C.f2L + C.f2D)])) j).oneValue
          BPair.unit := by
      intro j hj
      refine BPair.oneValue_trans (poly.getAt_add _ _ j) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr ?_ ?_) (BPair.add_unit BPair.unit)
      · match Nat.lt_or_ge j V.1.length with
        | Or.inr hge =>
          refine BPair.oneValue_of_eq ?_
          refine ground.getAt_over BPair.unit (profBase V) j ?_
          rw [show (profBase V).length = V.1.length from
            ground.length_map _ V.1]
          exact hge
        | Or.inl hlt =>
          have hb := bleGo_at 0 V.1 hsh1.1 j hlt
          rw [Nat.zero_add] at hb
          refine BPair.oneValue_of_eq ?_
          show ground.getAt BPair.unit
            (V.1.map (fun p => ground.getAt BPair.unit p 0)) j
            = BPair.unit
          rw [ground.getAt_map ([] : poly.Poly) BPair.unit
            (fun p => ground.getAt BPair.unit p 0) V.1 j hlt]
          refine ground.getAt_over BPair.unit
            (ground.getAt ([] : poly.Poly) V.1 j) 0 ?_
          exact ground.leCancelL j
            (Nat.le_trans hb (Nat.add_le_add_right hj 0))
      · refine BPair.oneValue_of_eq ?_
        refine ground.getAt_over BPair.unit
          (poly.neg [C.f1L + C.f1D + (C.f2L + C.f2D)]) j ?_
        exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hj
    have hends := chainEnds C.lo C.hi C.cuts
    refine chainFloor hpb C.bN C.bD (C.lo :: C.cuts ++ [C.hi])
      (BPair.ofNat (m * m) * BPair.ofPos en) ed h.2.2.2.2.1 hlo ?_
      hends.2
    rw [hends.1]
    exact hhi
  -- the slabs' vacancy reads at the clearing
  have hLvac := profLin_vac h.1
  have hUvac := profBaseU_vac h.1
  have hLvac1 : ∀ j, C.K + 1 ≤ j →
      (ground.getAt BPair.unit (profLin V) j).oneValue BPair.unit :=
    fun j hj => hLvac j (Nat.le_of_succ_le hj)
  have hUvac1 : ∀ j, C.K + 1 ≤ j →
      (ground.getAt BPair.unit (profBaseU V) j).oneValue BPair.unit :=
    fun j hj => hUvac j (Nat.le_of_succ_le hj)
  -- the u⁰-slab's scale keys above the first leading floor's partner
  have hvacS : ∀ j, C.K + 1 ≤ j →
      (ground.getAt BPair.unit
        (poly.scaleP e0n (profLin V)) j).oneValue BPair.unit :=
    scalePVac e0n hLvac1
  have hAswap : e0n * (poly.evalClear (profLin V)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K).swap
      ≤ C.f1L * BPair.ofPos e0d * ground.bpow (BPair.ofPos ed) C.K :=
    ground.leB_congr_left
      (BPair.oneValue_trans
        (ground.swap_congr
          (poly.evalClear_scaleP e0n (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K))
        (BPair.oneValue_of_eq
          (BPair.mul_swap e0n (poly.evalClear (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K)).symm))
      (chainCapSide (C.f1L * BPair.ofPos e0d)
        (poly.scaleP e0n (profLin V)) C.bN C.bD C.lo C.hi C.cutsL
        h.2.2.2.2.2.2.1 C.K hvacS hlo hhi)
  have hliftA : (BPair.ofPos ed * poly.evalClear
        (poly.shiftUp 1 (keyScale (m * m) 1 (profLin V)))
        (BPair.ofPos en) ed C.K).oneValue
      (BPair.ofPos en * (BPair.ofNat 1
        * poly.evalClear (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K)) :=
    liftKS (m * m) 1 (profLin V) hLvac
  have hliftAsw : (BPair.ofPos ed * (poly.evalClear
        (poly.shiftUp 1 (keyScale (m * m) 1 (profLin V)))
        (BPair.ofPos en) ed C.K).swap).oneValue
      (BPair.ofPos en * (poly.evalClear (profLin V)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K).swap) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_swap (BPair.ofPos ed) _)) ?_
    refine BPair.oneValue_trans (ground.swap_congr hliftA) ?_
    refine BPair.oneValue_trans
      (ground.swap_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.ofNat_one_mul _))) ?_
    exact BPair.oneValue_of_eq
      (BPair.mul_swap (BPair.ofPos en) _).symm
  have hA' : (poly.evalClear
        (poly.shiftUp 1 (keyScale (m * m) 1 (profLin V)))
        (BPair.ofPos en) ed C.K).swap
      ≤ C.f1L * ground.bpow (BPair.ofPos ed) C.K := by
    have hf1L : BPair.unit ≤ C.f1L * ground.bpow (BPair.ofPos ed) C.K :=
      ground.unitLeMul h.2.2.2.2.2.1 (windowsep.unitLe_bpow hEd C.K)
    have hposn : BPair.unit < e0n * BPair.ofPos ed :=
      ground.ltB_trans_le
        (ground.unitLtMul (ground.unitLtOfPos en)
          (ground.unitLtOfPos e0d)) he
    have heq1 : BPair.ofPos en
          * (e0n * (poly.evalClear (profLin V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K).swap)
        = e0n * (BPair.ofPos en * (poly.evalClear (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K).swap) := by
      rw [← BPair.mul_assoc (BPair.ofPos en) e0n
          ((poly.evalClear (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K).swap),
        BPair.mul_comm (BPair.ofPos en) e0n,
        BPair.mul_assoc e0n (BPair.ofPos en)
          ((poly.evalClear (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K).swap)]
    have heq2 : BPair.ofPos en
          * (C.f1L * BPair.ofPos e0d * ground.bpow (BPair.ofPos ed) C.K)
        = BPair.ofPos en * BPair.ofPos e0d
          * (C.f1L * ground.bpow (BPair.ofPos ed) C.K) := by
      rw [BPair.mul_right_comm C.f1L (BPair.ofPos e0d)
          (ground.bpow (BPair.ofPos ed) C.K),
        BPair.mul_comm (C.f1L * ground.bpow (BPair.ofPos ed) C.K)
          (BPair.ofPos e0d),
        ← BPair.mul_assoc (BPair.ofPos en) (BPair.ofPos e0d)
          (C.f1L * ground.bpow (BPair.ofPos ed) C.K)]
    have hstep : e0n * BPair.ofPos ed
          * (poly.evalClear
              (poly.shiftUp 1 (keyScale (m * m) 1 (profLin V)))
              (BPair.ofPos en) ed C.K).swap
        ≤ e0n * BPair.ofPos ed
          * (C.f1L * ground.bpow (BPair.ofPos ed) C.K) := by
      refine ground.leB_congr_left
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq
              (BPair.mul_assoc e0n (BPair.ofPos ed)
                ((poly.evalClear
                  (poly.shiftUp 1 (keyScale (m * m) 1 (profLin V)))
                  (BPair.ofPos en) ed C.K).swap)))
            (BPair.mul_congr (BPair.oneValue_refl e0n) hliftAsw))) ?_
      refine ground.leB_congr_left (BPair.oneValue_of_eq heq1) ?_
      refine ground.leB_trans (ground.leB_mulR hEn hAswap) ?_
      refine ground.leB_congr_left
        (BPair.oneValue_of_eq heq2.symm) ?_
      exact ground.leB_mul_mono hf1L (ground.unitLeMul hE0n hEd) he
        (ground.leB_refl _)
    refine ground.leB_unscale hposn ?_
    exact ground.leB_congr
      (BPair.oneValue_of_eq (BPair.mul_comm (e0n * BPair.ofPos ed)
        ((poly.evalClear
          (poly.shiftUp 1 (keyScale (m * m) 1 (profLin V)))
          (BPair.ofPos en) ed C.K).swap)))
      (BPair.oneValue_of_eq (BPair.mul_comm (e0n * BPair.ofPos ed)
        (C.f1L * ground.bpow (BPair.ofPos ed) C.K)))
      hstep
  -- the u¹-slab's origins at their squared price
  have hlenU : (poly.vnorm (profBaseU V)).length ≤ C.K + 1 :=
    poly.vnormLen_cap hUvac1
  have hCcap : windowsep.mag (BPair.ofNat m * BPair.ofPos en
        * poly.evalClear (profBaseU V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K)
      ≤ C.f2L * ground.bpow (BPair.ofPos ed) (C.K + 1) :=
    chainCapSq e0n C.f2L (profBaseU V) C.bN C.bD C.lo C.hi C.cutsU e0d
      h.2.2.2.2.2.2.2.1 C.K hlenU h.2.2.1 he hlo hhi
  have hliftC : (BPair.ofPos ed * poly.evalClear
        (poly.shiftUp 1 (keyScale (m * m) m (profBaseU V)))
        (BPair.ofPos en) ed C.K).oneValue
      (BPair.ofPos en * (BPair.ofNat m
        * poly.evalClear (profBaseU V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K)) :=
    liftKS (m * m) m (profBaseU V) hUvac
  have hC' : windowsep.mag (poly.evalClear
        (poly.shiftUp 1 (keyScale (m * m) m (profBaseU V)))
        (BPair.ofPos en) ed C.K)
      ≤ C.f2L * ground.bpow (BPair.ofPos ed) C.K := by
    have h1 : (BPair.ofPos ed * windowsep.mag (poly.evalClear
          (poly.shiftUp 1 (keyScale (m * m) m (profBaseU V)))
          (BPair.ofPos en) ed C.K)).oneValue
        (windowsep.mag (BPair.ofNat m * BPair.ofPos en
          * poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K)) := by
      refine BPair.oneValue_trans (magScaleP ed _) ?_
      refine BPair.oneValue_trans (windowsep.mag_congr hliftC) ?_
      refine windowsep.mag_congr (BPair.oneValue_of_eq ?_)
      rw [← BPair.mul_assoc (BPair.ofPos en) (BPair.ofNat m)
          (poly.evalClear (profBaseU V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K),
        BPair.mul_comm (BPair.ofPos en) (BPair.ofNat m)]
    have h2 : (C.f2L * ground.bpow (BPair.ofPos ed) (C.K + 1)).oneValue
        (C.f2L * ground.bpow (BPair.ofPos ed) C.K * BPair.ofPos ed) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (bpowSucc (BPair.ofPos ed) C.K)) ?_
      exact BPair.oneValue_of_eq
        (BPair.mul_assoc C.f2L (ground.bpow (BPair.ofPos ed) C.K)
          (BPair.ofPos ed)).symm
    refine ground.leB_unscale (ground.unitLtOfPos ed) ?_
    refine ground.leB_congr_left
      (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos ed)
        (windowsep.mag (poly.evalClear
          (poly.shiftUp 1 (keyScale (m * m) m (profBaseU V)))
          (BPair.ofPos en) ed C.K)))) ?_
    exact ground.leB_congr (BPair.oneValue_symm h1) h2 hCcap
  -- the deeper u⁰-slab tail at the ceiling's fold
  have hshapeB : ∀ j, j < (V.1.map (List.drop 2)).length →
      0 < (poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.1.map (List.drop 2)) j)).length →
      2 + j + (poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.1.map (List.drop 2)) j)).length ≤ C.K + 1 := by
    intro j hj hpos
    have h0 := slabDrop_shape 0 2 V.1 hsh1.1 j hj hpos
    rw [Nat.zero_add] at h0
    rw [Nat.add_comm 2 j,
      Nat.add_assoc j 2
        (poly.vnorm (ground.getAt ([] : poly.Poly)
          (V.1.map (List.drop 2)) j)).length,
      Nat.add_comm 2
        (poly.vnorm (ground.getAt ([] : poly.Poly)
          (V.1.map (List.drop 2)) j)).length]
    exact h0
  have hB' : windowsep.mag (poly.evalClear
        (slabGo (m * m) 2 1 (V.1.map (List.drop 2)))
        (BPair.ofPos en) ed C.K)
      ≤ C.f1D * ground.bpow (BPair.ofPos ed) C.K := by
    refine ground.leB_unscale (ground.unitLtOfPos ed) ?_
    refine capCancelB (K := C.K + 1)
      (ground.unitLeMul hE0n
        (unitLe_capS hE0n hshB (V.1.map (List.drop 2)))) he ?_
      (ground.leB_congr_right
        (BPair.mul_congr (BPair.oneValue_refl _)
          (powCRead e0d (C.K + 2)))
        h.2.2.2.2.2.2.2.2.1)
    refine ground.leB_congr (BPair.oneValue_refl _) ?_
      (slabPriceC2 he hs hshB (V.1.map (List.drop 2)) 1 hshapeB)
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.mul_congr (BPair.oneValue_refl e0n)
          (BPair.ofNat_one_mul (BPair.ofPos en)))
        (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_of_eq
      ((mulShufD e0n (BPair.ofPos en)
          (capS e0n e0d C.shB C.K (V.1.map (List.drop 2)))
          (ground.bpow (BPair.ofPos ed) C.K)).trans
        (BPair.mul_assoc (BPair.ofPos en)
          (e0n * capS e0n e0d C.shB C.K (V.1.map (List.drop 2)))
          (ground.bpow (BPair.ofPos ed) C.K)).symm)
  -- the deeper u¹-slab tail at the ceiling's fold
  have hshapeD : ∀ j, j < (V.2.map (List.drop 1)).length →
      0 < (poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.2.map (List.drop 1)) j)).length →
      2 + j + (poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.2.map (List.drop 1)) j)).length ≤ C.K + 1 := by
    intro j hj hpos
    have h0 := slabDrop_shape 1 1 V.2 hsh1.2 j hj hpos
    rw [Nat.add_comm 1 j] at h0
    rw [Nat.add_assoc j 1
      ((poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.2.map (List.drop 1)) j)).length + 1)] at h0
    rw [Nat.add_comm 1
      ((poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.2.map (List.drop 1)) j)).length + 1)] at h0
    rw [Nat.add_assoc
      (poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.2.map (List.drop 1)) j)).length 1 1] at h0
    rw [Nat.add_comm 2 j,
      Nat.add_assoc j 2
        (poly.vnorm (ground.getAt ([] : poly.Poly)
          (V.2.map (List.drop 1)) j)).length,
      Nat.add_comm 2
        (poly.vnorm (ground.getAt ([] : poly.Poly)
          (V.2.map (List.drop 1)) j)).length]
    exact h0
  have hD' : windowsep.mag (poly.evalClear
        (slabGo (m * m) 2 m (V.2.map (List.drop 1)))
        (BPair.ofPos en) ed C.K)
      ≤ C.f2D * ground.bpow (BPair.ofPos ed) C.K := by
    refine ground.leB_unscale (ground.unitLtOfPos ed) ?_
    refine capCancelA (K := C.K + 1) (windowsep.unitLe_mag _)
      (ground.unitLeMul hE0n
        (unitLe_capS hE0n hshB (V.2.map (List.drop 1))))
      h.2.2.2.1 hshB he hs ?_
      (ground.leB_congr_right
        (BPair.mul_congr (BPair.oneValue_refl _)
          (powCRead e0d (2 * C.K + 3)))
        h.2.2.2.2.2.2.2.2.2)
    refine ground.leB_congr (BPair.oneValue_refl _) ?_
      (slabPriceC2 he hs hshB (V.2.map (List.drop 1)) m hshapeD)
    exact BPair.oneValue_of_eq
      (mulShufD e0n (BPair.ofNat m * BPair.ofPos en)
        (capS e0n e0d C.shB C.K (V.2.map (List.drop 1)))
        (ground.bpow (BPair.ofPos ed) C.K))
  -- the scale-free part's cleared value at the depth
  have hHead : (poly.evalClear
      (slabGo (m * m) 0 1
        (V.1.map (fun p => [ground.getAt BPair.unit p 0])))
      (BPair.ofPos en) ed C.K).oneValue
      (poly.evalClear (profBase V)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K) := by
    have hmap : V.1.map (fun p => [ground.getAt BPair.unit p 0])
        = (profBase V).map (fun c => [c]) := by
      show V.1.map (fun p => [ground.getAt BPair.unit p 0])
        = (V.1.map (fun p => ground.getAt BPair.unit p 0)).map
            (fun c => [c])
      rw [ground.map_map]
    rw [hmap]
    refine BPair.oneValue_trans
      (poly.evalClear_congr
        (slabGo_const (m * m) 0 1 (profBase V)) _ ed _) ?_
    refine BPair.oneValue_trans
      (evalClear_keyScale (m * m) 1 (profBase V) (BPair.ofPos en) ed C.K)
      ?_
    exact BPair.ofNat_one_mul _
  -- the collapse's four-arm split
  have hL1 : poly.oneValue (slabGo (m * m) 0 1 V.1)
      (poly.add
        (slabGo (m * m) 0 1
          (V.1.map (fun p => [ground.getAt BPair.unit p 0])))
        (poly.add
          (poly.shiftUp 1 (keyScale (m * m) 1 (profLin V)))
          (slabGo (m * m) 2 1 (V.1.map (List.drop 2))))) := by
    refine poly.oneValue_trans (slabGo_split (m * m) 0 1 V.1) ?_
    refine poly.add_congr (poly.oneValue_refl _) ?_
    refine poly.oneValue_trans (slabGo_shiftTail (m * m) 0 1 V.1) ?_
    refine poly.oneValue_trans
      (slabGo_split (m * m) 1 1 (V.1.map (List.drop 1))) ?_
    refine poly.add_congr ?_ ?_
    · rw [mapLin V.1]
      exact slabGo_const (m * m) 1 1 (profLin V)
    · refine poly.oneValue_trans
        (slabGo_shiftTail (m * m) 1 1 (V.1.map (List.drop 1))) ?_
      rw [mapDropDrop V.1]
      exact poly.oneValue_refl _
  have hmapU : V.2.map (fun p => [ground.getAt BPair.unit p 0])
      = (profBaseU V).map (fun c => [c]) := by
    show V.2.map (fun p => [ground.getAt BPair.unit p 0])
      = (V.2.map (fun p => ground.getAt BPair.unit p 0)).map
          (fun c => [c])
    rw [ground.map_map]
  have hR1 : poly.oneValue (slabGo (m * m) 1 m V.2)
      (poly.add
        (poly.shiftUp 1 (keyScale (m * m) m (profBaseU V)))
        (slabGo (m * m) 2 m (V.2.map (List.drop 1)))) := by
    refine poly.oneValue_trans (slabGo_split (m * m) 1 m V.2) ?_
    refine poly.add_congr ?_ (slabGo_shiftTail (m * m) 1 m V.2)
    rw [hmapU]
    exact slabGo_const (m * m) 1 m (profBaseU V)
  -- the collapse's value at the depth
  have hval : (poly.evalClear (depthPoly V m)
      (BPair.ofPos en) ed C.K).oneValue
      (poly.evalClear (profBase V)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K
        + ((poly.evalClear
              (poly.shiftUp 1 (keyScale (m * m) 1 (profLin V)))
              (BPair.ofPos en) ed C.K
            + poly.evalClear
              (slabGo (m * m) 2 1 (V.1.map (List.drop 2)))
              (BPair.ofPos en) ed C.K)
          + (poly.evalClear
              (poly.shiftUp 1 (keyScale (m * m) m (profBaseU V)))
              (BPair.ofPos en) ed C.K
            + poly.evalClear
              (slabGo (m * m) 2 m (V.2.map (List.drop 1)))
              (BPair.ofPos en) ed C.K))) := by
    refine BPair.oneValue_trans
      (poly.evalClear_add (slabGo (m * m) 0 1 V.1)
        (slabGo (m * m) 1 m V.2) (BPair.ofPos en) ed C.K) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (poly.evalClear_congr hL1 (BPair.ofPos en) ed C.K)
        (poly.evalClear_congr hR1 (BPair.ofPos en) ed C.K)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (poly.evalClear_add _ _ (BPair.ofPos en) ed C.K)
          (BPair.add_congr hHead
            (poly.evalClear_add _ _ (BPair.ofPos en) ed C.K)))
        (poly.evalClear_add _ _ (BPair.ofPos en) ed C.K)) ?_
    exact BPair.oneValue_of_eq (BPair.add_assoc _ _ _)
  -- the floor read against the four caps
  have hPsplit : (poly.evalClear
      (poly.add (profBase V)
        (poly.neg [C.f1L + C.f1D + (C.f2L + C.f2D)]))
      (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K).oneValue
      (poly.evalClear (profBase V)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed C.K
        + ((C.f1L + C.f1D + (C.f2L + C.f2D))
            * ground.bpow (BPair.ofPos ed) C.K).swap) :=
    BPair.oneValue_trans
      (poly.evalClear_add _ _ _ ed C.K)
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (poly.evalClear_neg _ _ ed C.K)
          (ground.swap_congr
            (poly.evalClear_single (C.f1L + C.f1D + (C.f2L + C.f2D))
              _ ed C.K))))
  have hswapRU : ((poly.evalClear
        (poly.shiftUp 1 (keyScale (m * m) 1 (profLin V)))
        (BPair.ofPos en) ed C.K
      + poly.evalClear (slabGo (m * m) 2 1 (V.1.map (List.drop 2)))
        (BPair.ofPos en) ed C.K)
      + (poly.evalClear
          (poly.shiftUp 1 (keyScale (m * m) m (profBaseU V)))
          (BPair.ofPos en) ed C.K
        + poly.evalClear (slabGo (m * m) 2 m (V.2.map (List.drop 1)))
          (BPair.ofPos en) ed C.K)).swap
    ≤ (C.f1L + C.f1D + (C.f2L + C.f2D))
        * ground.bpow (BPair.ofPos ed) C.K := by
    refine ground.leB_congr_left
      (BPair.oneValue_of_eq (BPair.swap_add _ _)) ?_
    refine ground.leB_congr_left
      (BPair.add_congr
        (BPair.oneValue_of_eq (BPair.swap_add _ _))
        (BPair.oneValue_of_eq (BPair.swap_add _ _))) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.right_distrib (C.f1L + C.f1D) (C.f2L + C.f2D)
              (ground.bpow (BPair.ofPos ed) C.K)))
          (BPair.add_congr
            (BPair.oneValue_of_eq
              (BPair.right_distrib C.f1L C.f1D
                (ground.bpow (BPair.ofPos ed) C.K)))
            (BPair.oneValue_of_eq
              (BPair.right_distrib C.f2L C.f2D
                (ground.bpow (BPair.ofPos ed) C.K)))))) ?_
    refine ground.leB_add (ground.leB_add ?_ ?_) (ground.leB_add ?_ ?_)
    · exact hA'
    · exact ground.leB_trans (windowsep.swap_le_mag _) hB'
    · exact ground.leB_trans (windowsep.swap_le_mag _) hC'
    · exact ground.leB_trans (windowsep.swap_le_mag _) hD'
  refine BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm hval) ?_
  refine ground.ltB_trans_le
    (BPair.lt_congr (BPair.oneValue_refl _) hPsplit hbaseLt) ?_
  exact ground.leB_add (ground.leB_refl _) (ground.leB_swap hswapRU)

/-! `lem:cornerpivot`'s graded box device: the certificate data that
price from below a canonical object vacant at the scale-free order,
the value's own grading at the kernel `u² = ηs` — the depth's
multiple of the u¹-slab's origin reads against the u⁰-slab's
scale-key reads, both polynomials in the square scale. -/

set_option genInjectivity false in
/-- The graded box certificate: the box's composite endpoints with
the two chains' interior cut lists, the priced side reads' bound,
the box top's cleared read, the two slabs' tail floors, and the
shape clearing. -/
structure GradCert where
  lo : CPair
  hi : CPair
  cutsB : List CPair
  bN : BPair
  bD : BPair
  shB : BPair
  fA : BPair
  fB : BPair
  cutsA : List CPair
  K : Nat

/-- The scale-key read's line above the tail floors' join, the
depth family's one line: the scale-free slab's scale-key reads
above the join. -/
def lineL (V : poly.PPoly × poly.PPoly) (F : BPair) :
    poly.Poly :=
  poly.add (profLin V) (poly.neg [F])

/-- The squared comparison's line: the square scale's multiple of
the origin reads' square at the ceiling's cross-multiplied read
above the squared gap of the join to the scale-key read. -/
def lineSq (V : poly.PPoly × poly.PPoly) (e0n : BPair)
    (e0d : Pos) (F : BPair) : poly.Poly :=
  poly.add
    (poly.scaleP (BPair.ofPos e0d)
      (poly.shiftUp 1 (poly.mul (profBaseU V) (profBaseU V))))
    (poly.neg (poly.scaleP e0n
      (poly.mul (lineL V F) (lineL V F))))

/-- The graded box device's read at an object vacant at the
scale-free order — the value's own grading at the kernel,
`value = η·(m·B(s) + L(s)) + priced tails` at the origin reads `B`
(the u-slab's) and the scale-key reads `L` (the scale-free slab's),
the depth's leading part one read per depth and linear in it: the
shape, the box top's cleared-read tie, the vacancy, the two tail
budgets (the scale-free slab's scale tail at its squared price
over the depth read, the u-slab's at the ceiling), the origin
reads' chain — a vacant u-slab reading the line's chain alone —
and the line's two-armed chain over the box's composite cover,
each piece keeping the line's upper side or the squared
comparison's, each piece at its one comparison's kept side. -/
def gradRead (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : GradCert) : Prop :=
  profShape V C.K
  ∧ C.hi ≤ stage.ofB C.shB
  ∧ poly.unitTail (profBase V)
  ∧ BPair.unit ≤ C.fA
  ∧ e0n * (C.shB * (capS e0n e0d C.shB C.K (V.2.map (List.drop 1))
        * capS e0n e0d C.shB C.K (V.2.map (List.drop 1))))
      ≤ C.fA * C.fA * BPair.ofPos (Pos.powC e0d (2 * C.K + 1))
  ∧ e0n * capS e0n e0d C.shB C.K (V.1.map (List.drop 2))
      ≤ C.fB * BPair.ofPos (Pos.powC e0d (C.K + 1))
  ∧ (poly.unitTail (profBaseU V)
    ∨ chainRead (profBaseU V) C.bN C.bD (C.lo :: C.cutsA ++ [C.hi]))
  ∧ chainRead2 (lineL V (C.fA + C.fB))
      (lineSq V e0n e0d (C.fA + C.fB)) C.bN C.bD
      (C.lo :: C.cutsB ++ [C.hi])

instance (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : GradCert) : Decidable (gradRead V e0n e0d C) :=
  inferInstanceAs
    (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The scale strip: every inner polynomial dropped one scale key,
the object's own scale factor withdrawn — legitimate exactly at the
vacancy read, both slabs' origin coefficients the sum's unit. -/
def profStrip (V : poly.PPoly × poly.PPoly) : poly.PPoly × poly.PPoly :=
  (V.1.map (List.drop 1), V.2.map (List.drop 1))

/-- The strip's vacancy read: both slabs' origin coefficients at
the sum's unit, the scale factor's own occupancy witness. -/
def profVac (V : poly.PPoly × poly.PPoly) : Prop :=
  poly.unitTail (profBase V) ∧ poly.unitTail (profBaseU V)

instance (V : poly.PPoly × poly.PPoly) : Decidable (profVac V) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The unit key shift exchanges with any key shift. -/
private theorem shiftUp_comm1 (b : Nat) (X : poly.Poly) :
    poly.shiftUp 1 (poly.shiftUp b X) = poly.shiftUp b (poly.shiftUp 1 X) := by
  rw [poly.shiftUp_shiftUp 1 b X, poly.shiftUp_shiftUp b 1 X,
    Nat.add_comm 1 b]

/-- One slab's walk at inner polynomials vacant at the origin is
the stripped walk's own key shift. -/
private theorem slabGo_strip (mm : Nat) : ∀ (b w : Nat) (P : poly.PPoly),
    poly.unitTail (P.map (fun p => ground.getAt BPair.unit p 0)) →
    poly.oneValue (slabGo mm b w P)
      (poly.shiftUp 1 (slabGo mm b w (P.map (List.drop 1))))
  | _, _, [], _ => ⟨BPair.oneValue_refl _, trivial⟩
  | b, w, p :: t, h => by
    have h1 : poly.oneValue (poly.shiftUp b (poly.scaleP (BPair.ofNat w) p))
        (poly.shiftUp 1
          (poly.shiftUp b (poly.scaleP (BPair.ofNat w) (List.drop 1 p)))) := by
      rw [shiftUp_comm1 b (poly.scaleP (BPair.ofNat w) (List.drop 1 p))]
      exact poly.shiftUp_ov b
        (poly.oneValue_trans
          (poly.oneValue_scaleP (BPair.ofNat w) (ovShiftDrop p h.1))
          (scaleP_shift (BPair.ofNat w) 1 (List.drop 1 p)))
    refine poly.oneValue_trans
      (poly.add_congr h1 (slabGo_strip mm (b + 1) (w * mm) t h.2)) ?_
    exact poly.oneValue_symm (poly.shiftUp_add 1 _ _)

/-! The graded device's own kit: the two lines' vacancy beyond the
graded clearing. -/


/-- The least cleared multiple's line is vacant beyond the graded
clearing: the shape read forces the scale-key reads at every outer
key from the clearing up, and the join's key sits at the origin. -/
private theorem lineL_vac {V : poly.PPoly × poly.PPoly} {K : Nat}
    (hsh : profShape V K) (F : BPair) :
    ∀ j, K - 1 + 1 ≤ j →
      (ground.getAt BPair.unit (lineL V F) j).oneValue BPair.unit := by
  intro j hj
  have hjK : K ≤ j := Nat.le_trans (ground.lePredSucc K) hj
  refine BPair.oneValue_trans (poly.getAt_add _ _ j) ?_
  refine BPair.oneValue_trans (BPair.add_congr ?_ ?_)
    (BPair.add_unit BPair.unit)
  · exact profLin_vac hsh j hjK
  · refine BPair.oneValue_of_eq ?_
    refine ground.getAt_over BPair.unit (poly.neg [F]) j ?_
    exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le (K - 1))) hj

/-- The squared comparison's line is vacant beyond the doubled
clearing, the two factors' vacancy at the products' key count. -/
private theorem lineSq_vac {V : poly.PPoly × poly.PPoly} {K : Nat}
    (hsh : profShape V K) (e0n : BPair) (e0d : Pos) (F : BPair) :
    ∀ j, K - 1 + (K - 1) + 1 + 1 ≤ j →
      (ground.getAt BPair.unit (lineSq V e0n e0d F) j).oneValue
        BPair.unit := by
  intro j hj
  have hlenB : (poly.vnorm (profBaseU V)).length ≤ K - 1 + 1 :=
    poly.vnormLen_cap (fun d hd => profBaseU_vac hsh d
      (Nat.le_trans (ground.lePredSucc K) hd))
  have hlenL : (poly.vnorm (lineL V F)).length ≤ K - 1 + 1 :=
    poly.vnormLen_cap (lineL_vac hsh F)
  have hovB : poly.oneValue
      (poly.mul (profBaseU V) (profBaseU V))
      (poly.mul (poly.vnorm (profBaseU V))
        (poly.vnorm (profBaseU V))) :=
    poly.mul_vnorm_ov (profBaseU V) (profBaseU V)
  have hovL : poly.oneValue
      (poly.mul (lineL V F) (lineL V F))
      (poly.mul (poly.vnorm (lineL V F))
        (poly.vnorm (lineL V F))) :=
    poly.mul_vnorm_ov (lineL V F) (lineL V F)
  have hmulVacB : ∀ d, K - 1 + (K - 1) + 1 ≤ d →
      (ground.getAt BPair.unit
        (poly.mul (profBaseU V) (profBaseU V)) d).oneValue
        BPair.unit := fun d hdJ =>
    BPair.oneValue_trans (poly.oneValue_getAt d hovB)
      (BPair.oneValue_of_eq
        (ground.getAt_over BPair.unit
          (poly.mul (poly.vnorm (profBaseU V))
            (poly.vnorm (profBaseU V))) d
          (Nat.le_trans
            (poly.mul_len_le _ _ (K - 1) (K - 1) hlenB hlenB) hdJ)))
  have hmulVacL : ∀ d, K - 1 + (K - 1) + 1 ≤ d →
      (ground.getAt BPair.unit
        (poly.mul (lineL V F) (lineL V F)) d).oneValue
        BPair.unit := fun d hdJ =>
    BPair.oneValue_trans (poly.oneValue_getAt d hovL)
      (BPair.oneValue_of_eq
        (ground.getAt_over BPair.unit
          (poly.mul (poly.vnorm (lineL V F))
            (poly.vnorm (lineL V F))) d
          (Nat.le_trans
            (poly.mul_len_le _ _ (K - 1) (K - 1) hlenL hlenL) hdJ)))
  refine BPair.oneValue_trans (poly.getAt_add _ _ j) ?_
  refine BPair.oneValue_trans (BPair.add_congr ?_ ?_)
    (BPair.add_unit BPair.unit)
  · exact scalePVac (BPair.ofPos e0d)
      (shiftVac (poly.mul (profBaseU V) (profBaseU V)) hmulVacB) j hj
  · rw [poly.getAt_neg]
    refine BPair.oneValue_trans
      (ground.swap_congr
        (scalePVac e0n hmulVacL j
          (Nat.le_trans (Nat.le_add_right _ 1) hj))) ?_
    exact BPair.oneValue_refl BPair.unit


/-! The graded device's two cancellations: the tail prices read
against the cap conjuncts, the clearing's powers withdrawn. -/

/-- The strip's collapse bridge: at the vacancy read the collapse is
the stripped collapse's scale shift. -/
theorem depthPoly_profStrip : ∀ (V : poly.PPoly × poly.PPoly) (m : Nat),
    profVac V →
    poly.oneValue (depthPoly V m)
      (poly.shiftUp 1 (depthPoly (profStrip V) m)) := by
  intro V m h
  refine poly.oneValue_trans
    (poly.add_congr (slabGo_strip (m * m) 0 1 V.1 h.1)
      (slabGo_strip (m * m) 1 m V.2 h.2)) ?_
  exact poly.oneValue_symm (poly.shiftUp_add 1 _ _)

/-! The scale-free slab calculus: the origin reads of the profile
operations.  The shift keeps the scale-free slab and moves the
first slab's doubled derivative into the second, and the
comparison object's two origin slabs withdraw — the vacancy is the
construction's own fact. -/

/-- The k-th inner polynomial's origin coefficient. -/
private def bAt (P : poly.PPoly) (k : Nat) : BPair :=
  ground.getAt BPair.unit (ground.getAt [] P k) 0

/-- The slab's origin list reads the inner origins. -/
private theorem bAt_read : ∀ (P : poly.PPoly) (k : Nat),
    ground.getAt BPair.unit
        (P.map (fun p => ground.getAt BPair.unit p 0)) k
      = bAt P k
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: P, k + 1 => bAt_read P k

/-- The slab sum's origin read is the origins' sum. -/
private theorem bAt_padd : ∀ (P Q : poly.PPoly) (k : Nat),
    (bAt (poly.padd P Q) k).oneValue (bAt P k + bAt Q k)
  | [], Q, k => BPair.oneValue_symm (BPair.unit_add _)
  | _ :: _, [], k => by
    show (bAt _ k).oneValue (bAt _ k + bAt ([] : poly.PPoly) k)
    exact BPair.oneValue_symm (BPair.add_unit _)
  | p :: P, q :: Q, 0 => poly.getAt_add p q 0
  | _ :: P, _ :: Q, k + 1 => bAt_padd P Q k

/-- A mapped slab's origin read at an origin-keeping map. -/
private theorem bAt_map (f : poly.Poly → poly.Poly)
    (hf : (ground.getAt BPair.unit (f []) 0).oneValue BPair.unit)
    (P : poly.PPoly) : ∀ k,
    (bAt (P.map f) k).oneValue
      (ground.getAt BPair.unit (f (ground.getAt [] P k)) 0) := by
  induction P with
  | nil =>
    intro k
    exact BPair.oneValue_symm hf
  | cons p t ih =>
    intro k
    match k with
    | 0 => exact BPair.oneValue_refl _
    | k + 1 => exact ih k

/-- The scaled-slab origin read. -/
private theorem bAt_pmulC (c : poly.Poly) (P : poly.PPoly) (k : Nat) :
    (bAt (P.map (poly.mul c)) k).oneValue
      (ground.getAt BPair.unit c 0 * bAt P k) := by
  refine BPair.oneValue_trans
    (bAt_map (poly.mul c)
      (BPair.oneValue_trans (originMul c []) (BPair.mul_unit _)) P k) ?_
  exact originMul c _

/-- The eta-multiple slab's origin slab is vacant. -/
private theorem bAt_esMul (P : poly.PPoly) : ∀ k,
    (bAt (esMul P) k).oneValue BPair.unit
  | 0 => BPair.oneValue_refl _
  | k + 1 => by
    show (bAt (P.map (poly.shiftUp 1)) k).oneValue BPair.unit
    refine BPair.oneValue_trans
      (bAt_map (poly.shiftUp 1) (BPair.oneValue_refl _) P k) ?_
    match ground.getAt [] P k with
    | _ => exact BPair.oneValue_refl _

/-- A product slab at vacant origins reads vacant origins. -/
private theorem bAt_pmul_vac : ∀ (P : poly.PPoly),
    (∀ j, (bAt P j).oneValue BPair.unit) →
    ∀ (Q : poly.PPoly) (k : Nat),
      (bAt (poly.pmul P Q) k).oneValue BPair.unit
  | [], _, _, k => BPair.oneValue_refl _
  | c :: P, h, Q, k => by
    show (bAt (poly.padd (Q.map (poly.mul c))
        (([] : poly.Poly) :: poly.pmul P Q)) k).oneValue BPair.unit
    refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
    have hc : (ground.getAt BPair.unit c 0).oneValue BPair.unit := h 0
    have h1 : (bAt (Q.map (poly.mul c)) k).oneValue BPair.unit := by
      refine BPair.oneValue_trans (bAt_pmulC c Q k) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr hc (BPair.oneValue_refl _)) ?_
      exact BPair.unit_mul _
    have h2 : (bAt (([] : poly.Poly) :: poly.pmul P Q) k).oneValue
        BPair.unit := by
      match k with
      | 0 => exact BPair.oneValue_refl _
      | k + 1 => exact bAt_pmul_vac P (fun j => h (j + 1)) Q k
    exact BPair.oneValue_trans (BPair.add_congr h1 h2) (BPair.add_unit _)

/-- A product slab whose first factor's origins sit at the head
alone reads the head's multiple. -/
private theorem bAt_pmul_head : ∀ (P : poly.PPoly),
    (∀ j, (bAt P (j + 1)).oneValue BPair.unit) →
    ∀ (Q : poly.PPoly) (k : Nat),
      (bAt (poly.pmul P Q) k).oneValue (bAt P 0 * bAt Q k)
  | [], _, Q, k => BPair.oneValue_symm (BPair.unit_mul _)
  | c :: P, h, Q, k => by
    show (bAt (poly.padd (Q.map (poly.mul c))
        (([] : poly.Poly) :: poly.pmul P Q)) k).oneValue
      (ground.getAt BPair.unit c 0 * bAt Q k)
    refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
    have h2 : (bAt (([] : poly.Poly) :: poly.pmul P Q) k).oneValue
        BPair.unit := by
      match k with
      | 0 => exact BPair.oneValue_refl _
      | k + 1 => exact bAt_pmul_vac P (fun j => h j) Q k
    refine BPair.oneValue_trans
      (BPair.add_congr (bAt_pmulC c Q k) h2) ?_
    exact BPair.add_unit _

/-- A one-key product slab reads the key's multiple. -/
private theorem bAt_pmul1 (a : poly.Poly) (Q : poly.PPoly) (k : Nat) :
    (bAt (poly.pmul [a] Q) k).oneValue
      (ground.getAt BPair.unit a 0 * bAt Q k) := by
  show (bAt (poly.padd (Q.map (poly.mul a))
      (([] : poly.Poly) :: poly.pmul [] Q)) k).oneValue _
  refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
  have h2 : (bAt (([] : poly.Poly) :: poly.pmul [] Q) k).oneValue
      BPair.unit := by
    match k with
    | 0 => exact BPair.oneValue_refl _
    | k + 1 => exact BPair.oneValue_refl _
  exact BPair.oneValue_trans
    (BPair.add_congr (bAt_pmulC a Q k) h2) (BPair.add_unit _)

/-- A two-key product slab's origin read. -/
private theorem bAt_pmul2_zero (a b : poly.Poly) (Q : poly.PPoly) :
    (bAt (poly.pmul [a, b] Q) 0).oneValue
      (ground.getAt BPair.unit a 0 * bAt Q 0) := by
  show (bAt (poly.padd (Q.map (poly.mul a))
      (([] : poly.Poly) :: poly.pmul [b] Q)) 0).oneValue _
  refine BPair.oneValue_trans (bAt_padd _ _ 0) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr (bAt_pmulC a Q 0) (BPair.oneValue_refl BPair.unit))
    (BPair.add_unit _)

/-- A two-key product slab's deeper reads: the head against the key
and the second key against the withdrawn one. -/
private theorem bAt_pmul2_succ (a b : poly.Poly) (Q : poly.PPoly)
    (k : Nat) :
    (bAt (poly.pmul [a, b] Q) (k + 1)).oneValue
      (ground.getAt BPair.unit a 0 * bAt Q (k + 1)
        + ground.getAt BPair.unit b 0 * bAt Q k) := by
  show (bAt (poly.padd (Q.map (poly.mul a))
      (([] : poly.Poly) :: poly.pmul [b] Q)) (k + 1)).oneValue _
  refine BPair.oneValue_trans (bAt_padd _ _ (k + 1)) ?_
  exact BPair.add_congr (bAt_pmulC a Q (k + 1)) (bAt_pmul1 b Q k)

/-- The substitution walk keeps the scale-free slab. -/
private theorem bAt_shGo1 : ∀ (P : poly.PPoly) (k : Nat),
    (bAt (shGo P).1 k).oneValue (bAt P k)
  | [], _ => BPair.oneValue_refl _
  | p :: t, k => by
    show (bAt (poly.padd [p] (profMul sh1 (shGo t)).1) k).oneValue
      (bAt (p :: t) k)
    refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
    match k with
    | 0 =>
      have hmul : (bAt (profMul sh1 (shGo t)).1 0).oneValue BPair.unit := by
        show (bAt (poly.padd (poly.pmul sh1.1 (shGo t).1)
            (esMul (poly.pmul sh1.2 (shGo t).2))) 0).oneValue _
        refine BPair.oneValue_trans (bAt_padd _ _ 0) ?_
        refine BPair.oneValue_trans
          (BPair.add_congr
            (BPair.oneValue_trans (bAt_pmul2_zero _ _ (shGo t).1)
              (BPair.unit_mul _))
            (bAt_esMul _ 0)) ?_
        exact BPair.add_unit _
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) hmul) (BPair.add_unit _)
    | k + 1 =>
      have hmul : (bAt (profMul sh1 (shGo t)).1 (k + 1)).oneValue
          (bAt (shGo t).1 k) := by
        show (bAt (poly.padd (poly.pmul sh1.1 (shGo t).1)
            (esMul (poly.pmul sh1.2 (shGo t).2))) (k + 1)).oneValue _
        refine BPair.oneValue_trans (bAt_padd _ _ (k + 1)) ?_
        refine BPair.oneValue_trans
          (BPair.add_congr
            (BPair.oneValue_trans (bAt_pmul2_succ _ _ (shGo t).1 k)
              (BPair.oneValue_trans
                (BPair.add_congr (BPair.unit_mul _)
                  (BPair.ofNat_one_mul _))
                (BPair.oneValue_trans
                  (BPair.oneValue_of_eq (BPair.add_comm _ _))
                  (BPair.add_unit _))))
            (bAt_esMul _ (k + 1))) ?_
        exact BPair.add_unit _
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl (bAt [p] (k + 1))) hmul) ?_
      show (bAt [p] (k + 1) + bAt (shGo t).1 k).oneValue (bAt t k)
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl BPair.unit)
          (bAt_shGo1 t k)) ?_
      exact BPair.unit_add _

/-- The substitution walk moves the scale-free slab's doubled
derivative into the second slab. -/
private theorem bAt_shGo2 : ∀ (P : poly.PPoly) (k : Nat),
    (bAt (shGo P).2 k).oneValue
      (BPair.ofNat (2 * (k + 1)) * bAt P (k + 1))
  | [], k => BPair.oneValue_symm (BPair.mul_unit _)
  | p :: t, k => by
    show (bAt (poly.padd []
        (poly.padd (poly.pmul sh1.1 (shGo t).2)
          (poly.pmul sh1.2 (shGo t).1))) k).oneValue _
    refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl BPair.unit)
        (bAt_padd _ _ k)) ?_
    refine BPair.oneValue_trans (BPair.unit_add _) ?_
    match k with
    | 0 =>
      have h1 : (bAt (poly.pmul sh1.1 (shGo t).2) 0).oneValue
          BPair.unit := by
        refine BPair.oneValue_trans (bAt_pmul2_zero _ _ (shGo t).2) ?_
        exact BPair.unit_mul _
      have h2 : (bAt (poly.pmul sh1.2 (shGo t).1) 0).oneValue
          (BPair.ofNat 2 * bAt t 0) := by
        refine BPair.oneValue_trans (bAt_pmul1 _ (shGo t).1 0) ?_
        exact BPair.mul_congr (BPair.oneValue_refl _) (bAt_shGo1 t 0)
      refine BPair.oneValue_trans (BPair.add_congr h1 h2) ?_
      exact BPair.unit_add _
    | k + 1 =>
      have h1 : (bAt (poly.pmul sh1.1 (shGo t).2) (k + 1)).oneValue
          (BPair.ofNat (2 * (k + 1)) * bAt t (k + 1)) := by
        refine BPair.oneValue_trans (bAt_pmul2_succ _ _ (shGo t).2 k) ?_
        refine BPair.oneValue_trans
          (BPair.add_congr (BPair.unit_mul _)
            (BPair.ofNat_one_mul _)) ?_
        refine BPair.oneValue_trans (BPair.unit_add _) ?_
        exact bAt_shGo2 t k
      have h2 : (bAt (poly.pmul sh1.2 (shGo t).1) (k + 1)).oneValue
          (BPair.ofNat 2 * bAt t (k + 1)) := by
        refine BPair.oneValue_trans (bAt_pmul1 _ (shGo t).1 (k + 1)) ?_
        exact BPair.mul_congr (BPair.oneValue_refl _) (bAt_shGo1 t (k + 1))
      refine BPair.oneValue_trans (BPair.add_congr h1 h2) ?_
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.ofNat_add (2 * (k + 1)) 2)
          (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_of_eq (BPair.right_distrib _ _ _)

/-- The depth shift keeps the scale-free slab. -/
private theorem bAt_shift1 (V : poly.PPoly × poly.PPoly) (k : Nat) :
    (bAt (profShift V).1 k).oneValue (bAt V.1 k) := by
  show (bAt (poly.padd (shGo V.1).1
      (poly.padd (poly.pmul u1.1 (shGo V.2).1)
        (esMul (poly.pmul u1.2 (shGo V.2).2)))) k).oneValue _
  refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
  have h2 : (bAt (poly.padd (poly.pmul u1.1 (shGo V.2).1)
      (esMul (poly.pmul u1.2 (shGo V.2).2))) k).oneValue BPair.unit := by
    refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (bAt_pmul1 _ (shGo V.2).1 k)
          (BPair.unit_mul _))
        (bAt_esMul _ k)) ?_
    exact BPair.add_unit _
  refine BPair.oneValue_trans (BPair.add_congr (bAt_shGo1 V.1 k) h2) ?_
  exact BPair.add_unit _

/-- The depth shift's second slab: the first slab's doubled
derivative joined to the second slab's own read. -/
private theorem bAt_shift2 (V : poly.PPoly × poly.PPoly) (k : Nat) :
    (bAt (profShift V).2 k).oneValue
      (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1) + bAt V.2 k) := by
  show (bAt (poly.padd (shGo V.1).2
      (poly.padd (poly.pmul u1.1 (shGo V.2).2)
        (poly.pmul u1.2 (shGo V.2).1))) k).oneValue _
  refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
  have h2 : (bAt (poly.padd (poly.pmul u1.1 (shGo V.2).2)
      (poly.pmul u1.2 (shGo V.2).1)) k).oneValue (bAt V.2 k) := by
    refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (bAt_pmul1 _ (shGo V.2).2 k)
          (BPair.unit_mul _))
        (BPair.oneValue_trans (bAt_pmul1 _ (shGo V.2).1 k)
          (BPair.oneValue_trans (BPair.ofNat_one_mul _)
            (bAt_shGo1 V.2 k)))) ?_
    exact BPair.unit_add _
  exact BPair.add_congr (bAt_shGo2 V.1 k) h2

/-- A mapped slab's inner list at an origin-keeping map. -/
private theorem getAt_map_poly (f : poly.Poly → poly.Poly)
    (hf : f [] = []) : ∀ (P : poly.PPoly) (k : Nat),
    ground.getAt [] (P.map f) k = f (ground.getAt [] P k)
  | [], _ => hf.symm
  | _ :: _, 0 => rfl
  | _ :: P, k + 1 => getAt_map_poly f hf P k

/-- The negated scaled slab's origin read: the scale's multiple at
the swap. -/
private theorem bAt_negScale (b : Nat) (Z : poly.PPoly) (k : Nat) :
    (bAt ((Z.map (poly.scaleP (BPair.ofNat b))).map poly.neg) k).oneValue
      ((BPair.ofNat b * bAt Z k).swap) := by
  show (ground.getAt BPair.unit
    (ground.getAt []
      ((Z.map (poly.scaleP (BPair.ofNat b))).map poly.neg) k) 0).oneValue _
  rw [getAt_map_poly poly.neg rfl, poly.getAt_neg,
    getAt_map_poly (poly.scaleP (BPair.ofNat b)) rfl]
  exact ground.swap_congr (poly.getAt_scaleP (BPair.ofNat b) _ 0)

/-- The diagonal's scale-free slab is vacant past the origin. -/
private theorem bAt_diag1_succ (r qn qd k : Nat) :
    (bAt (diagProf r qn qd).1 (k + 1)).oneValue BPair.unit := by
  match k with
  | 0 => exact BPair.oneValue_refl _
  | k + 1 => exact BPair.oneValue_refl _

/-- The diagonal's second slab's origins are vacant. -/
private theorem bAt_diag2 (r qn qd k : Nat) :
    (bAt (diagProf r qn qd).2 k).oneValue BPair.unit := by
  match k with
  | 0 => exact BPair.oneValue_refl _
  | k + 1 => exact BPair.oneValue_refl _

/-- The shifted diagonal keeps the vacancies past the origin. -/
private theorem bAt_shD1_succ (r qn qd j : Nat) :
    (bAt (profShift (diagProf r qn qd)).1 (j + 1)).oneValue
      BPair.unit :=
  BPair.oneValue_trans (bAt_shift1 (diagProf r qn qd) (j + 1))
    (bAt_diag1_succ r qn qd j)

/-- The shifted diagonal's second slab is vacant. -/
private theorem bAt_shD2 (r qn qd k : Nat) :
    (bAt (profShift (diagProf r qn qd)).2 k).oneValue BPair.unit := by
  refine BPair.oneValue_trans (bAt_shift2 (diagProf r qn qd) k) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (bAt_diag1_succ r qn qd k))
        (BPair.mul_unit _))
      (bAt_diag2 r qn qd k)) ?_
  exact BPair.add_unit _

/-- The comparison object's first product slab reads the band
clearing's multiple of the profile's scale-free slab. -/
private theorem bAt_X1 (r qn qd : Nat) (V : poly.PPoly × poly.PPoly)
    (k : Nat) :
    (bAt (profMul (profShift (diagProf r qn qd)) (profShift V)).1
      k).oneValue
      (BPair.ofNat (2 * ((r + 1) * qd)) * bAt V.1 k) := by
  show (bAt (poly.padd
      (poly.pmul (profShift (diagProf r qn qd)).1 (profShift V).1)
      (esMul (poly.pmul (profShift (diagProf r qn qd)).2
        (profShift V).2))) k).oneValue _
  refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (bAt_pmul_head _ (bAt_shD1_succ r qn qd) (profShift V).1 k)
      (bAt_esMul _ k)) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact BPair.mul_congr (bAt_shift1 (diagProf r qn qd) 0)
    (bAt_shift1 V k)

/-- The comparison object's second product slab reads the band
clearing's multiple of the shifted profile's second slab. -/
private theorem bAt_X2 (r qn qd : Nat) (V : poly.PPoly × poly.PPoly)
    (k : Nat) :
    (bAt (profMul (profShift (diagProf r qn qd)) (profShift V)).2
      k).oneValue
      (BPair.ofNat (2 * ((r + 1) * qd))
        * (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1) + bAt V.2 k)) := by
  show (bAt (poly.padd
      (poly.pmul (profShift (diagProf r qn qd)).1 (profShift V).2)
      (poly.pmul (profShift (diagProf r qn qd)).2
        (profShift V).1)) k).oneValue _
  refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (bAt_pmul_head _ (bAt_shD1_succ r qn qd) (profShift V).2 k)
      (bAt_pmul_vac _ (bAt_shD2 r qn qd) (profShift V).1 k)) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact BPair.mul_congr (bAt_shift1 (diagProf r qn qd) 0)
    (bAt_shift2 V k)

/-- The comparison object is vacant at the scale-free order at
every profile and rate: the band read's double withdraws against
the cleared neighbor sum's at both origin slabs, the collapse
identity `termPoly_base`'s own sentence at the slab level.  The
vacancy is the construction's fact, never certificate data. -/
theorem termProf_vac (V : poly.PPoly × poly.PPoly) (r qn qd : Nat) :
    profVac (termProf V r qn qd) := by
  constructor
  · refine poly.unitTail_of_getAt (fun k => ?_)
    show (ground.getAt BPair.unit
      ((termProf V r qn qd).1.map
        (fun p => ground.getAt BPair.unit p 0)) k).oneValue BPair.unit
    rw [bAt_read]
    show (bAt (poly.padd
      (profMul (profShift (diagProf r qn qd)) (profShift V)).1
      (((poly.padd V.1 (profShift (profShift V)).1).map
          (poly.scaleP (BPair.ofNat ((r + 1) * qd)))).map
        poly.neg)) k).oneValue BPair.unit
    refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
    have hR : (bAt (((poly.padd V.1 (profShift (profShift V)).1).map
        (poly.scaleP (BPair.ofNat ((r + 1) * qd)))).map poly.neg)
        k).oneValue
        ((BPair.ofNat ((r + 1) * qd) * bAt V.1 k
          + BPair.ofNat ((r + 1) * qd) * bAt V.1 k).swap) := by
      refine BPair.oneValue_trans (bAt_negScale _ _ k) ?_
      refine ground.swap_congr ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (bAt_padd _ _ k)
            (BPair.add_congr (BPair.oneValue_refl _)
              (BPair.oneValue_trans (bAt_shift1 (profShift V) k)
                (bAt_shift1 V k))))) ?_
      exact BPair.oneValue_of_eq (BPair.left_distrib _ _ _)
    have hL : (bAt (profMul (profShift (diagProf r qn qd))
        (profShift V)).1 k).oneValue
        (BPair.ofNat ((r + 1) * qd) * bAt V.1 k
          + BPair.ofNat ((r + 1) * qd) * bAt V.1 k) := by
      refine BPair.oneValue_trans (bAt_X1 r qn qd V k) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq
              (congrArg BPair.ofNat (Nat.two_mul ((r + 1) * qd))))
            (BPair.ofNat_add ((r + 1) * qd) ((r + 1) * qd)))
          (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_of_eq (BPair.right_distrib _ _ _)
    refine BPair.oneValue_trans (BPair.add_congr hL hR) ?_
    exact ground.unitOfOne (BPair.oneValue_refl _)
  · refine poly.unitTail_of_getAt (fun k => ?_)
    show (ground.getAt BPair.unit
      ((termProf V r qn qd).2.map
        (fun p => ground.getAt BPair.unit p 0)) k).oneValue BPair.unit
    rw [bAt_read]
    show (bAt (poly.padd
      (profMul (profShift (diagProf r qn qd)) (profShift V)).2
      (((poly.padd V.2 (profShift (profShift V)).2).map
          (poly.scaleP (BPair.ofNat ((r + 1) * qd)))).map
        poly.neg)) k).oneValue BPair.unit
    refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
    have hM : (bAt (poly.padd V.2 (profShift (profShift V)).2) k).oneValue
        ((BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1) + bAt V.2 k)
          + (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1) + bAt V.2 k)) := by
      refine BPair.oneValue_trans (bAt_padd _ _ k) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl (bAt V.2 k))
          (BPair.oneValue_trans (bAt_shift2 (profShift V) k)
            (BPair.add_congr
              (BPair.mul_congr (BPair.oneValue_refl _)
                (bAt_shift1 V (k + 1)))
              (bAt_shift2 V k)))) ?_
      refine BPair.oneValue_of_eq ?_
      rw [← BPair.add_assoc (bAt V.2 k)
        (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1))
        (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1) + bAt V.2 k)]
      rw [BPair.add_comm (bAt V.2 k)
        (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1))]
    have hR : (bAt (((poly.padd V.2 (profShift (profShift V)).2).map
        (poly.scaleP (BPair.ofNat ((r + 1) * qd)))).map poly.neg)
        k).oneValue
        ((BPair.ofNat ((r + 1) * qd)
            * (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1) + bAt V.2 k)
          + BPair.ofNat ((r + 1) * qd)
            * (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1)
              + bAt V.2 k)).swap) := by
      refine BPair.oneValue_trans (bAt_negScale _ _ k) ?_
      refine ground.swap_congr ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) hM) ?_
      exact BPair.oneValue_of_eq (BPair.left_distrib _ _ _)
    have hL : (bAt (profMul (profShift (diagProf r qn qd))
        (profShift V)).2 k).oneValue
        (BPair.ofNat ((r + 1) * qd)
            * (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1) + bAt V.2 k)
          + BPair.ofNat ((r + 1) * qd)
            * (BPair.ofNat (2 * (k + 1)) * bAt V.1 (k + 1)
              + bAt V.2 k)) := by
      refine BPair.oneValue_trans (bAt_X2 r qn qd V k) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq
              (congrArg BPair.ofNat (Nat.two_mul ((r + 1) * qd))))
            (BPair.ofNat_add ((r + 1) * qd) ((r + 1) * qd)))
          (BPair.oneValue_refl _)) ?_
      exact BPair.oneValue_of_eq (BPair.right_distrib _ _ _)
    refine BPair.oneValue_trans (BPair.add_congr hL hR) ?_
    exact ground.unitOfOne (BPair.oneValue_refl _)

/-- A vacant scale-free slab reads every collapse's origin at the
sum's unit. -/
private theorem vacHead (V : poly.PPoly × poly.PPoly)
    (h : poly.unitTail (profBase V)) (m : Nat) :
    (ground.getAt BPair.unit (depthPoly V m) 0).oneValue
      BPair.unit := by
  refine BPair.oneValue_trans (depthPoly_head V m) ?_
  have hh : (ground.getAt BPair.unit
      (V.1.map (fun p => ground.getAt BPair.unit p 0)) 0).oneValue
      BPair.unit := poly.getAt_unitTail h 0
  rw [bAt_read] at hh
  exact hh

/-- The boundary comparison's origin is vacant at a vacant
scale-free slab. -/
private theorem seedHeadVac (V : poly.PPoly × poly.PPoly)
    (r qn qd : Nat) (h : poly.unitTail (profBase V)) :
    (ground.getAt BPair.unit
      (depthPoly (seedProf V r qn qd) 0) 0).oneValue BPair.unit := by
  refine BPair.oneValue_trans
    (poly.oneValue_getAt 0 (seedProf_at V r qn qd 0)) ?_
  refine BPair.oneValue_trans (poly.getAt_add _ _ 0) ?_
  have hneg : (ground.getAt BPair.unit
      (poly.neg (poly.scaleP (BPair.ofNat ((r + 1) * qd))
        (depthPoly V 1))) 0).oneValue BPair.unit := by
    rw [poly.getAt_neg]
    refine BPair.oneValue_trans
      (ground.swap_congr
        (BPair.oneValue_trans (poly.getAt_scaleP _ _ 0)
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _) (vacHead V h 1))
            (BPair.mul_unit _)))) ?_
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans (diagHead r qn qd 1 (depthPoly V 0))
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) (vacHead V h 0))
          (BPair.mul_unit _)))
      hneg) ?_
  exact BPair.add_unit _

/-- A slab walk from a two-step shift is vacant at the scale key,
every member shifted past it. -/
private theorem slabKey1Deep (mm : Nat) : ∀ (b w : Nat) (l : poly.PPoly),
    (ground.getAt BPair.unit (slabGo mm (b + 2) w l) 1).oneValue
      BPair.unit
  | _, _, [] => BPair.oneValue_refl _
  | b, w, p :: t => by
    refine BPair.oneValue_trans (poly.getAt_add _ _ 1) ?_
    rw [poly.getAt_shiftUp_lt (b + 2) (poly.scaleP (BPair.ofNat w) p) 1
      (Nat.le_add_left 2 b)]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (slabKey1Deep mm (b + 1) (w * mm) t)) ?_
    exact BPair.add_unit _

/-- The one-shift slab walk's scale key reads its first member's
origin at the walk's weight. -/
private theorem slabKey1One (mm : Nat) : ∀ (w : Nat) (l : poly.PPoly),
    (ground.getAt BPair.unit (slabGo mm 1 w l) 1).oneValue
      (BPair.ofNat w * bAt l 0)
  | _, [] => BPair.oneValue_symm (BPair.mul_unit _)
  | w, p :: t => by
    refine BPair.oneValue_trans (poly.getAt_add _ _ 1) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (poly.getAt_scaleP (BPair.ofNat w) p 0)
        (slabKey1Deep mm 0 (w * mm) t)) ?_
    exact BPair.add_unit _

/-- The nought-shift slab walk's scale key at a vacant deeper base
is the first member's own scale coefficient. -/
private theorem slabKey1Zero (mm : Nat) :
    ∀ (l : poly.PPoly),
    poly.unitTail (l.map (fun p => ground.getAt BPair.unit p 0)) →
    (ground.getAt BPair.unit (slabGo mm 0 1 l) 1).oneValue
      (ground.getAt BPair.unit (ground.getAt [] l 0) 1)
  | [], _ => BPair.oneValue_refl _
  | p :: t, h => by
    refine BPair.oneValue_trans (poly.getAt_add _ _ 1) ?_
    have hh : (bAt t 0).oneValue BPair.unit := by
      have h0 := poly.getAt_unitTail h.2 0
      rw [bAt_read] at h0
      exact h0
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (poly.getAt_scaleP (BPair.ofNat 1) p 1)
          (BPair.ofNat_one_mul _))
        (BPair.oneValue_trans (slabKey1One mm (1 * mm) t)
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _) hh)
            (BPair.mul_unit _)))) ?_
    exact BPair.add_unit _

/-- The depth collapse's scale coefficient at a vacant scale-free
slab is affine in the depth: the first inner's own scale
coefficient joined to the depth's weight of the u-slab's origin —
the square-scale weights enter at the vacant deeper origins alone,
so the depth's square drops from the read. -/
private theorem depthPoly_key1 (V : poly.PPoly × poly.PPoly) (m : Nat)
    (h : poly.unitTail (profBase V)) :
    (ground.getAt BPair.unit (depthPoly V m) 1).oneValue
      (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1
        + BPair.ofNat m * bAt V.2 0) := by
  refine BPair.oneValue_trans (poly.getAt_add _ _ 1) ?_
  exact BPair.add_congr (slabKey1Zero (m * m) V.1 h)
    (slabKey1One (m * m) m V.2)

/-- The scale-key read of a product at an occupied first factor:
the head against the second factor's scale coefficient, joined to
the tail product's origin. -/
private theorem mulKey1 (c : BPair) (p q : poly.Poly) :
    (ground.getAt BPair.unit (poly.mul (c :: p) q) 1).oneValue
      (c * ground.getAt BPair.unit q 1
        + ground.getAt BPair.unit (poly.mul p q) 0) := by
  show (ground.getAt BPair.unit
      (poly.add (q.map (fun d => c * d)) (BPair.unit :: poly.mul p q))
      1).oneValue _
  refine BPair.oneValue_trans (poly.getAt_add _ _ 1) ?_
  exact BPair.add_congr (poly.getAt_scale c q 1) (BPair.oneValue_refl _)

/-- The stripped comparison's origin at the boundary depth is
vacant at a vacant scale-free slab: the comparison's scale
coefficient is the affine collapse reads' second difference, the
band read's double of the middle read against the cleared neighbor
sum, and the strip bridge reads it at the stripped object's
origin. -/
private theorem stripHeadVac (V : poly.PPoly × poly.PPoly)
    (r qn qd : Nat) (h : poly.unitTail (profBase V)) :
    (ground.getAt BPair.unit
      (depthPoly (profStrip (termProf V r qn qd)) 0) 0).oneValue
      BPair.unit := by
  have hsh : ground.getAt BPair.unit
      (poly.shiftUp 1 (depthPoly (profStrip (termProf V r qn qd)) 0)) 1
      = ground.getAt BPair.unit
        (depthPoly (profStrip (termProf V r qn qd)) 0) 0 :=
    poly.getAt_shiftUp_add 1 _ 0
  have e1 : (ground.getAt BPair.unit
      (depthPoly (termProf V r qn qd) 0) 1).oneValue
      (ground.getAt BPair.unit
        (depthPoly (profStrip (termProf V r qn qd)) 0) 0) := by
    have e0 := poly.oneValue_getAt 1
      (depthPoly_profStrip (termProf V r qn qd) 0 (termProf_vac V r qn qd))
    rw [hsh] at e0
    exact e0
  refine BPair.oneValue_trans (BPair.oneValue_symm e1) ?_
  refine BPair.oneValue_trans
    (poly.oneValue_getAt 1 (depthPoly_termProf V r qn qd 0)) ?_
  rw [termPoly_at]
  refine BPair.oneValue_trans (poly.getAt_add _ _ 1) ?_
  have hc2 : (BPair.ofNat (0 + 2) * bAt V.2 0).oneValue
      (bAt V.2 0 + bAt V.2 0) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.ofNat_add 1 1)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.right_distrib _ _ _)) ?_
    exact BPair.add_congr (BPair.ofNat_one_mul _) (BPair.ofNat_one_mul _)
  have hP0 : (ground.getAt BPair.unit (depthPoly V 0) 1).oneValue
      (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1) := by
    refine BPair.oneValue_trans (depthPoly_key1 V 0 h) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.unit_mul _)) ?_
    exact BPair.add_unit _
  have hP1 : (ground.getAt BPair.unit (depthPoly V (0 + 1)) 1).oneValue
      (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1 + bAt V.2 0) := by
    refine BPair.oneValue_trans (depthPoly_key1 V (0 + 1) h) ?_
    exact BPair.add_congr (BPair.oneValue_refl _) (BPair.ofNat_one_mul _)
  have hP2 : (ground.getAt BPair.unit (depthPoly V (0 + 2)) 1).oneValue
      (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1
        + (bAt V.2 0 + bAt V.2 0)) := by
    refine BPair.oneValue_trans (depthPoly_key1 V (0 + 2) h) ?_
    exact BPair.add_congr (BPair.oneValue_refl _) hc2
  have hE : (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1 + bAt V.2 0)
      + (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1 + bAt V.2 0)
      = ground.getAt BPair.unit (ground.getAt [] V.1 0) 1
        + (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1
          + (bAt V.2 0 + bAt V.2 0)) := by
    rw [BPair.add_assoc, BPair.add_left_comm (bAt V.2 0)
      (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1) (bAt V.2 0)]
  have hA : (ground.getAt BPair.unit
      (poly.mul (diagPoly r qn qd (0 + 1)) (depthPoly V (0 + 1)))
      1).oneValue
      (BPair.ofNat ((r + 1) * qd)
        * (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1
          + (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1
            + (bAt V.2 0 + bAt V.2 0)))) := by
    refine BPair.oneValue_trans (mulKey1 _ _ _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _) hP1)
        (BPair.oneValue_trans (originMul _ _)
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _)
              (vacHead V h (0 + 1)))
            (BPair.mul_unit _)))) ?_
    refine BPair.oneValue_trans (BPair.add_unit _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (congrArg BPair.ofNat (Nat.two_mul ((r + 1) * qd))))
          (BPair.ofNat_add ((r + 1) * qd) ((r + 1) * qd)))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.right_distrib _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.left_distrib _ _ _).symm) ?_
    exact BPair.oneValue_of_eq
      (congrArg (BPair.ofNat ((r + 1) * qd) * ·) hE)
  have hB : (ground.getAt BPair.unit
      (poly.neg (poly.scaleP (BPair.ofNat ((r + 1) * qd))
        (poly.add (depthPoly V 0) (depthPoly V (0 + 2))))) 1).oneValue
      ((BPair.ofNat ((r + 1) * qd)
        * (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1
          + (ground.getAt BPair.unit (ground.getAt [] V.1 0) 1
            + (bAt V.2 0 + bAt V.2 0)))).swap) := by
    rw [poly.getAt_neg]
    refine ground.swap_congr ?_
    refine BPair.oneValue_trans (poly.getAt_scaleP _ _ 1) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans (poly.getAt_add _ _ 1) ?_
    exact BPair.add_congr hP0 hP2
  refine BPair.oneValue_trans (BPair.add_congr hA hB) ?_
  exact ground.unitOfOne (BPair.oneValue_refl _)

/-- The shape read's arithmetic at the once-dropped slab. -/
private theorem addOneLe {a d K : Nat} (h : a + (d + 1) ≤ K + 1) :
    a + d ≤ K :=
  Nat.le_of_succ_le_succ
    (Nat.le_trans (Nat.le_of_eq (Nat.add_assoc a d 1)) h)

/-- The shape read's arithmetic at the twice-dropped slab, the
once-dropped read's instance. -/
private theorem addTwoLe {j d K : Nat} (h : j + (d + 2) ≤ K + 1) :
    1 + j + d ≤ K :=
  addOneLe (Nat.le_trans (Nat.le_of_eq (by
    rw [Nat.add_comm 1 j, Nat.add_right_comm j 1 (d + 1),
      Nat.add_assoc j (d + 1) 1])) h)

/-- The graded device's conclusion: at every depth and every scale
inside the box at the cleared ceiling, the collapse's cleared
evaluation sits strictly above the sum's unit. -/
theorem gradRead_pos (V : poly.PPoly × poly.PPoly) (e0n : BPair) (e0d : Pos)
    (C : GradCert) (h : gradRead V e0n e0d C) (m : Nat) (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hlo : C.lo ≤ ⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩)
    (hhi : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair) ≤ C.hi) :
    BPair.unit < poly.evalClear (depthPoly V m) (BPair.ofPos en) ed C.K := by
  have hEd : BPair.unit ≤ BPair.ofPos ed :=
    ground.leB_of_lt (ground.unitLtOfPos ed)
  have hEn : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hE0n : BPair.unit ≤ e0n := unitLe_of_clear he
  have hxhi : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair)
      ≤ stage.ofB C.shB := CPair.le_trans hhi h.2.1
  have hs : BPair.ofNat (m * m) * BPair.ofPos en
      ≤ C.shB * BPair.ofPos ed := by
    have h0 : (BPair.ofNat (m * m) * BPair.ofPos en).scale Pos.one
        ≤ C.shB.scale ed := hxhi
    rw [BPair.scale_one] at h0
    exact ground.leB_congr_right
      (BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.ofPos_scale ed C.shB))
        (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos ed) C.shB))) h0
  have hshB : BPair.unit ≤ C.shB :=
    stage.unitC_le_fst (CPair.le_trans
      (cunitLe (ground.unitLeMul (ground.unitLeOfNat (m * m)) hEn)) hxhi)
  -- the scale slab's own side
  have hA : BPair.unit ≤ poly.evalClear (profBaseU V)
      (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1) := by
    match h.2.2.2.2.2.2.1 with
    | Or.inl hut =>
      have h0 : (poly.evalClear (profBaseU V)
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)).oneValue
          BPair.unit :=
        poly.evalClear_congr
          (poly.unitTail_oneValue (q := ([] : poly.Poly)) hut trivial)
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
      exact ground.leB_congr_right (BPair.oneValue_symm h0)
        (ground.leB_refl BPair.unit)
    | Or.inr harm =>
      have hends := chainEnds C.lo C.hi C.cutsA
      refine ground.leB_of_lt ?_
      refine chainFloor
        (fun j hj => profBaseU_vac h.1 j
          (Nat.le_trans (ground.lePredSucc C.K) hj))
        C.bN C.bD (C.lo :: C.cutsA ++ [C.hi])
        (BPair.ofNat (m * m) * BPair.ofPos en) ed harm hlo ?_ hends.2
      rw [hends.1]
      exact hhi
  -- the leading part's floor at the two-armed chain
  have hvacL := lineL_vac (V := V) h.1 (C.fA + C.fB)
  have hmB : BPair.unit ≤ BPair.ofNat m * poly.evalClear (profBaseU V)
      (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1) :=
    ground.unitLeMul (ground.unitLeOfNat m) hA
  have hbase : BPair.unit <
      BPair.ofNat m * poly.evalClear (profBaseU V)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
      + poly.evalClear (lineL V (C.fA + C.fB))
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1) := by
    have hends := chainEnds C.lo C.hi C.cutsB
    match chainRead2_all (lineL V (C.fA + C.fB))
        (lineSq V e0n e0d (C.fA + C.fB)) C.bN C.bD
        (C.lo :: C.cutsB ++ [C.hi])
        ⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
        h.2.2.2.2.2.2.2 hlo
        (by rw [hends.1]; exact hhi) hends.2 with
    | Or.inl hL =>
      refine ground.ltB_trans_le
        (stage.evalFloor hvacL
          (BPair.ofNat (m * m) * BPair.ofPos en) ed hL) ?_
      refine ground.leB_congr_left (BPair.unit_add _) ?_
      exact ground.leB_add hmB (ground.leB_refl _)
    | Or.inr hP =>
      have hlenB : (poly.vnorm (profBaseU V)).length ≤ C.K - 1 + 1 :=
        poly.vnormLen_cap (fun d hd => profBaseU_vac h.1 d
          (Nat.le_trans (ground.lePredSucc C.K) hd))
      have hlenL : (poly.vnorm (lineL V (C.fA + C.fB))).length
          ≤ C.K - 1 + 1 :=
        poly.vnormLen_cap hvacL
      have hovB : poly.oneValue
          (poly.mul (profBaseU V) (profBaseU V))
          (poly.mul (poly.vnorm (profBaseU V))
            (poly.vnorm (profBaseU V))) :=
        poly.mul_vnorm_ov (profBaseU V) (profBaseU V)
      have hovL : poly.oneValue
          (poly.mul (lineL V (C.fA + C.fB)) (lineL V (C.fA + C.fB)))
          (poly.mul (poly.vnorm (lineL V (C.fA + C.fB)))
            (poly.vnorm (lineL V (C.fA + C.fB)))) :=
        poly.mul_vnorm_ov (lineL V (C.fA + C.fB))
          (lineL V (C.fA + C.fB))
      have hPfloor : BPair.unit < poly.evalClear
          (lineSq V e0n e0d (C.fA + C.fB))
          (BPair.ofNat (m * m) * BPair.ofPos en) ed
          (C.K - 1 + (C.K - 1) + 1) :=
        stage.evalFloor (lineSq_vac h.1 e0n e0d (C.fA + C.fB))
          (BPair.ofNat (m * m) * BPair.ofPos en) ed hP
      have hPval : (poly.evalClear (lineSq V e0n e0d (C.fA + C.fB))
          (BPair.ofNat (m * m) * BPair.ofPos en) ed
          (C.K - 1 + (C.K - 1) + 1)).oneValue
          (BPair.ofPos e0d * (BPair.ofNat (m * m) * BPair.ofPos en
              * (poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed
                  (C.K - 1)))
            + (e0n * (BPair.ofPos ed
                * (poly.evalClear (lineL V (C.fA + C.fB))
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed
                    (C.K - 1)
                  * poly.evalClear (lineL V (C.fA + C.fB))
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed
                    (C.K - 1)))).swap) := by
        refine BPair.oneValue_trans
          (poly.evalClear_add _ _
            (BPair.ofNat (m * m) * BPair.ofPos en) ed
            (C.K - 1 + (C.K - 1) + 1)) ?_
        refine BPair.add_congr ?_ ?_
        · refine BPair.oneValue_trans
            (poly.evalClear_scaleP (BPair.ofPos e0d)
              (poly.shiftUp 1 (poly.mul (profBaseU V) (profBaseU V)))
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1 + (C.K - 1) + 1)) ?_
          refine BPair.mul_congr (BPair.oneValue_refl _) ?_
          refine BPair.oneValue_trans
            (evalClear_shiftUp 1
              (poly.mul (profBaseU V) (profBaseU V))
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1 + (C.K - 1) + 1)) ?_
          refine BPair.mul_congr
            (ground.bpow_one_read
              (BPair.ofNat (m * m) * BPair.ofPos en)) ?_
          refine BPair.oneValue_trans
            (poly.evalClear_congr hovB
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1 + (C.K - 1))) ?_
          refine BPair.oneValue_trans
            (poly.evalClear_mul (poly.vnorm (profBaseU V))
              (poly.vnorm (profBaseU V))
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1) (C.K - 1) hlenB hlenB) ?_
          exact BPair.mul_congr
            (poly.evalClear_congr (poly.vnorm_ov (profBaseU V)) _ ed
              (C.K - 1))
            (poly.evalClear_congr (poly.vnorm_ov (profBaseU V)) _ ed
              (C.K - 1))
        · refine BPair.oneValue_trans
            (poly.evalClear_neg
              (poly.scaleP e0n
                (poly.mul (lineL V (C.fA + C.fB))
                  (lineL V (C.fA + C.fB))))
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1 + (C.K - 1) + 1)) ?_
          refine ground.swap_congr ?_
          refine BPair.oneValue_trans
            (poly.evalClear_scaleP e0n
              (poly.mul (lineL V (C.fA + C.fB))
                (lineL V (C.fA + C.fB)))
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1 + (C.K - 1) + 1)) ?_
          refine BPair.mul_congr (BPair.oneValue_refl e0n) ?_
          refine BPair.oneValue_trans
            (poly.evalClear_congr hovL
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1 + (C.K - 1) + 1)) ?_
          refine BPair.oneValue_trans
            (poly.evalClear_pow
              (poly.mul (poly.vnorm (lineL V (C.fA + C.fB)))
                (poly.vnorm (lineL V (C.fA + C.fB))))
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1 + (C.K - 1) + 1) (C.K - 1 + (C.K - 1))
              (poly.mul_len_le _ _ (C.K - 1) (C.K - 1) hlenL hlenL)
              (Nat.le_add_right _ 1)) ?_
          refine BPair.mul_congr ?_ ?_
          · exact BPair.oneValue_trans
              (BPair.oneValue_of_eq
                (congrArg (ground.bpow (BPair.ofPos ed))
                  (ground.addSubSelfL (C.K - 1 + (C.K - 1)) 1)))
              (ground.bpow_one_read (BPair.ofPos ed))
          · refine BPair.oneValue_trans
              (poly.evalClear_mul (poly.vnorm (lineL V (C.fA + C.fB)))
                (poly.vnorm (lineL V (C.fA + C.fB)))
                (BPair.ofNat (m * m) * BPair.ofPos en) ed
                (C.K - 1) (C.K - 1) hlenL hlenL) ?_
            exact BPair.mul_congr
              (poly.evalClear_congr
                (poly.vnorm_ov (lineL V (C.fA + C.fB))) _ ed
                (C.K - 1))
              (poly.evalClear_congr
                (poly.vnorm_ov (lineL V (C.fA + C.fB))) _ ed
                (C.K - 1))
      have hlt1 : e0n * (BPair.ofPos ed
            * (poly.evalClear (lineL V (C.fA + C.fB))
                (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
              * poly.evalClear (lineL V (C.fA + C.fB))
                (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)))
          < BPair.ofPos e0d * (BPair.ofNat (m * m) * BPair.ofPos en
              * (poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed
                  (C.K - 1))) :=
        ground.swapLt_of_unitLt
          (BPair.lt_congr (BPair.oneValue_refl _) hPval hPfloor)
      have hsqm : ((BPair.ofNat m * poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
            * (BPair.ofNat m * poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1))).oneValue
          (BPair.ofNat (m * m)
            * (poly.evalClear (profBaseU V)
                (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
              * poly.evalClear (profBaseU V)
                (BPair.ofNat (m * m) * BPair.ofPos en) ed
                (C.K - 1))) := by
        refine BPair.oneValue_trans (BPair.oneValue_of_eq ?_)
          (BPair.oneValue_symm (BPair.ofNat_mul_mul m m _))
        rw [BPair.mul_assoc (BPair.ofNat m)
            (poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
            (BPair.ofNat m * poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)),
          ← BPair.mul_assoc
            (poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
            (BPair.ofNat m)
            (poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)),
          BPair.mul_comm
            (poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
            (BPair.ofNat m),
          BPair.mul_assoc (BPair.ofNat m)
            (poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
            (poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))]
      have hker : BPair.ofPos e0d * (BPair.ofNat (m * m) * BPair.ofPos en
              * (poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)))
          ≤ e0n * (BPair.ofPos ed
            * ((BPair.ofNat m * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
              * (BPair.ofNat m * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed
                  (C.K - 1)))) := by
        have heqL : BPair.ofPos e0d
            * (BPair.ofNat (m * m) * BPair.ofPos en
              * (poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)))
            = BPair.ofPos en * BPair.ofPos e0d
              * (BPair.ofNat (m * m)
                * (poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                  * poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed
                    (C.K - 1))) := by
          rw [BPair.mul_assoc (BPair.ofNat (m * m)) (BPair.ofPos en)
              (poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)),
            BPair.mul_left_comm (BPair.ofPos e0d) (BPair.ofNat (m * m))
              (BPair.ofPos en
                * (poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                  * poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed
                    (C.K - 1))),
            BPair.mul_left_comm (BPair.ofPos e0d) (BPair.ofPos en)
              (poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)),
            BPair.mul_assoc (BPair.ofPos en) (BPair.ofPos e0d)
              (BPair.ofNat (m * m)
                * (poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                  * poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed
                    (C.K - 1))),
            BPair.mul_left_comm (BPair.ofPos e0d) (BPair.ofNat (m * m))
              (poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)),
            BPair.mul_left_comm (BPair.ofNat (m * m)) (BPair.ofPos en)
              (BPair.ofPos e0d
                * (poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                  * poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed
                    (C.K - 1)))]
        have h2 : ((e0n * BPair.ofPos ed)
            * (BPair.ofNat (m * m)
              * (poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
                * poly.evalClear (profBaseU V)
                  (BPair.ofNat (m * m) * BPair.ofPos en) ed
                  (C.K - 1)))).oneValue
            (e0n * (BPair.ofPos ed
              * ((BPair.ofNat m * poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed
                    (C.K - 1))
                * (BPair.ofNat m * poly.evalClear (profBaseU V)
                    (BPair.ofNat (m * m) * BPair.ofPos en) ed
                    (C.K - 1))))) := by
          refine BPair.oneValue_trans
            (BPair.oneValue_of_eq
              (BPair.mul_assoc e0n (BPair.ofPos ed) _)) ?_
          exact BPair.mul_congr (BPair.oneValue_refl e0n)
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_symm hsqm))
        refine ground.leB_congr (BPair.oneValue_of_eq heqL.symm) h2 ?_
        exact ground.leB_mul_mono
          (ground.unitLeMul (ground.unitLeOfNat (m * m))
            (ground.unitLeMul hA hA))
          (ground.unitLeMul hE0n hEd) he (ground.leB_refl _)
      have hsq : poly.evalClear (lineL V (C.fA + C.fB))
            (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
          * poly.evalClear (lineL V (C.fA + C.fB))
            (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
          < (BPair.ofNat m * poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
            * (BPair.ofNat m * poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed
              (C.K - 1)) := by
        have heqc : ∀ Z : BPair,
            e0n * (BPair.ofPos ed * Z)
              = Z * (e0n * BPair.ofPos ed) := by
          intro Z
          rw [← BPair.mul_assoc e0n (BPair.ofPos ed) Z,
            BPair.mul_comm (e0n * BPair.ofPos ed) Z]
        exact ground.ltB_unscale
          (ground.unitLeMul hE0n hEd)
          (BPair.lt_congr (BPair.oneValue_of_eq (heqc _))
            (BPair.oneValue_of_eq (heqc _))
            (ground.ltB_trans_le hlt1 hker))
      refine ground.unitLt_of_swap_lt ?_
      refine ground.ltB_of_sq hmB ?_
      refine BPair.lt_congr
        (BPair.oneValue_of_eq
          (BPair.swap_sq (poly.evalClear (lineL V (C.fA + C.fB))
            (BPair.ofNat (m * m) * BPair.ofPos en) ed
            (C.K - 1))).symm)
        (BPair.oneValue_refl _) hsq
  -- the two tails' prices
  have hshape1 : ∀ j, j < (V.1.map (List.drop 2)).length →
      0 < (poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.1.map (List.drop 2)) j)).length →
      1 + j + (poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.1.map (List.drop 2)) j)).length ≤ C.K - 1 + 1 := by
    intro j hj hpos
    have h0 := slabDrop_shape 0 2 V.1 (ground.andSplitB h.1).1 j hj hpos
    rw [Nat.zero_add] at h0
    exact Nat.le_trans (addTwoLe h0) (ground.lePredSucc C.K)
  have hshape2 : ∀ j, j < (V.2.map (List.drop 1)).length →
      0 < (poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.2.map (List.drop 1)) j)).length →
      1 + j + (poly.vnorm (ground.getAt ([] : poly.Poly)
        (V.2.map (List.drop 1)) j)).length ≤ C.K - 1 + 1 := by
    intro j hj hpos
    have h0 := slabDrop_shape 1 1 V.2 (ground.andSplitB h.1).2 j hj hpos
    exact Nat.le_trans (addOneLe h0) (ground.lePredSucc C.K)
  have hW1 : windowsep.mag (BPair.ofNat 1 * ground.bpow (BPair.ofPos en) 1)
        * ground.bpow (BPair.ofPos ed) 1
      ≤ BPair.ofPos en * ground.bpow (BPair.ofPos ed) 1 :=
    ground.leB_congr_left
      (BPair.oneValue_symm
        (BPair.mul_congr_left
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (magPow 1 1))
            (BPair.oneValue_trans (BPair.ofNat_one_mul _)
              (ground.bpow_one_read (BPair.ofPos en))))))
      (ground.leB_refl _)
  have hWU : windowsep.mag (BPair.ofNat m * ground.bpow (BPair.ofPos en) 1)
        * ground.bpow (BPair.ofPos ed) 1
      ≤ BPair.ofNat m * BPair.ofPos en * ground.bpow (BPair.ofPos ed) 1 :=
    ground.leB_congr_left
      (BPair.oneValue_symm
        (BPair.mul_congr_left
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (magPow m 1))
            (BPair.mul_congr (BPair.oneValue_refl _)
              (ground.bpow_one_read (BPair.ofPos en))))))
      (ground.leB_refl _)
  have hp1 := slabPriceC he hs hshB (Nat.sub_le C.K 1)
    (V.1.map (List.drop 2)) 1 1 1 (BPair.ofPos en) hEn hW1 hshape1
  have hp2 := slabPriceC he hs hshB (Nat.sub_le C.K 1)
    (V.2.map (List.drop 1)) 1 m 1 (BPair.ofNat m * BPair.ofPos en)
    (ground.unitLeMul (ground.unitLeOfNat m) hEn) hWU hshape2
  have hR1 : windowsep.mag (poly.evalClear
        (slabGo (m * m) 1 1 (V.1.map (List.drop 2)))
        (BPair.ofPos en) ed (C.K - 1))
      ≤ C.fB * ground.bpow (BPair.ofPos ed) (C.K - 1) := by
    refine ground.leB_unscale (ground.unitLtOfPos ed) ?_
    refine capCancelB
      (unitLe_capS hE0n hshB (V.1.map (List.drop 2))) he ?_
      (ground.leB_congr_right
        (BPair.mul_congr (BPair.oneValue_refl _)
          (powCRead e0d (C.K + 1)))
        h.2.2.2.2.2.1)
    exact ground.leB_congr_left
      (BPair.mul_congr_left
        (BPair.mul_congr (BPair.oneValue_refl _)
          (ground.bpow_one_read (BPair.ofPos ed)))) hp1
  have hR2 : windowsep.mag (poly.evalClear
        (slabGo (m * m) 1 m (V.2.map (List.drop 1)))
        (BPair.ofPos en) ed (C.K - 1))
      ≤ C.fA * ground.bpow (BPair.ofPos ed) (C.K - 1) := by
    refine ground.leB_unscale (ground.unitLtOfPos ed) ?_
    refine capCancelA (windowsep.unitLe_mag _)
      (unitLe_capS hE0n hshB (V.2.map (List.drop 1))) h.2.2.2.1 hshB
      he hs ?_
      (ground.leB_congr_right
        (BPair.mul_congr (BPair.oneValue_refl _)
          (powCRead e0d (2 * C.K + 1)))
        h.2.2.2.2.1)
    refine ground.leB_congr_right
      (BPair.oneValue_of_eq
        (BPair.mul_assoc (BPair.ofNat m * BPair.ofPos en)
          (capS e0n e0d C.shB C.K (V.2.map (List.drop 1)))
          (ground.bpow (BPair.ofPos ed) (C.K - 1)))) ?_
    exact ground.leB_congr_left
      (BPair.mul_congr_left
        (BPair.mul_congr (BPair.oneValue_refl _)
          (ground.bpow_one_read (BPair.ofPos ed)))) hp2
  -- the collapse's value at the depth
  have hstrip : poly.oneValue (depthPoly V m)
      (poly.shiftUp 1 (poly.add
        (slabGo (m * m) 0 1 (V.1.map (List.drop 1)))
        (slabGo (m * m) 0 m V.2))) := by
    refine poly.oneValue_trans
      (poly.add_congr (slabGo_strip (m * m) 0 1 V.1 h.2.2.1)
        (poly.oneValue_trans (slabGo_norm (m * m) 1 m V.2)
          (poly.oneValue_symm
            (poly.shiftUp_ov 1 (slabGo_norm (m * m) 0 m V.2))))) ?_
    exact poly.oneValue_symm (poly.shiftUp_add 1 _ _)
  have hT1eq : poly.oneValue
      (slabGo (m * m) 0 1 ((V.1.map (List.drop 1)).map
        (fun p => poly.shiftUp 1 (List.drop 1 p))))
      (slabGo (m * m) 1 1 (V.1.map (List.drop 2))) := by
    rw [← mapDropDrop V.1]
    exact slabGo_shiftTail (m * m) 0 1 (V.1.map (List.drop 1))
  have hT2eq : poly.oneValue
      (slabGo (m * m) 0 m (V.2.map (fun p => poly.shiftUp 1 (List.drop 1 p))))
      (slabGo (m * m) 1 m (V.2.map (List.drop 1))) :=
    slabGo_shiftTail (m * m) 0 m V.2
  have hO1 : (poly.evalClear
      (slabGo (m * m) 0 1 ((V.1.map (List.drop 1)).map
        (fun p => [ground.getAt BPair.unit p 0])))
      (BPair.ofPos en) ed (C.K - 1)).oneValue
      (poly.evalClear (profLin V)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)) := by
    rw [mapLin V.1]
    refine BPair.oneValue_trans
      (poly.evalClear_congr (slabGo_const (m * m) 0 1 (profLin V))
        (BPair.ofPos en) ed (C.K - 1)) ?_
    refine BPair.oneValue_trans
      (evalClear_keyScale (m * m) 1 (profLin V) (BPair.ofPos en) ed
        (C.K - 1)) ?_
    exact BPair.ofNat_one_mul _
  have hmap2 : V.2.map (fun p => [ground.getAt BPair.unit p 0])
      = (profBaseU V).map (fun c => [c]) := by
    show V.2.map (fun p => [ground.getAt BPair.unit p 0])
      = (V.2.map (fun p => ground.getAt BPair.unit p 0)).map (fun c => [c])
    rw [ground.map_map]
  have hO2 : (poly.evalClear
      (slabGo (m * m) 0 m (V.2.map (fun p => [ground.getAt BPair.unit p 0])))
      (BPair.ofPos en) ed (C.K - 1)).oneValue
      (BPair.ofNat m * poly.evalClear (profBaseU V)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)) := by
    rw [hmap2]
    refine BPair.oneValue_trans
      (poly.evalClear_congr (slabGo_const (m * m) 0 m (profBaseU V))
        (BPair.ofPos en) ed (C.K - 1)) ?_
    exact evalClear_keyScale (m * m) m (profBaseU V) (BPair.ofPos en) ed
      (C.K - 1)
  have hWval : (poly.evalClear (poly.add
        (slabGo (m * m) 0 1 (V.1.map (List.drop 1)))
        (slabGo (m * m) 0 m V.2)) (BPair.ofPos en) ed (C.K - 1)).oneValue
      ((poly.evalClear (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
          + poly.evalClear (slabGo (m * m) 1 1 (V.1.map (List.drop 2)))
              (BPair.ofPos en) ed (C.K - 1))
        + (BPair.ofNat m * poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
          + poly.evalClear (slabGo (m * m) 1 m (V.2.map (List.drop 1)))
              (BPair.ofPos en) ed (C.K - 1))) := by
    refine BPair.oneValue_trans
      (poly.evalClear_add _ _ (BPair.ofPos en) ed (C.K - 1)) ?_
    refine BPair.add_congr ?_ ?_
    · refine BPair.oneValue_trans
        (poly.evalClear_congr (slabGo_split (m * m) 0 1
          (V.1.map (List.drop 1))) (BPair.ofPos en) ed (C.K - 1)) ?_
      refine BPair.oneValue_trans
        (poly.evalClear_add _ _ (BPair.ofPos en) ed (C.K - 1)) ?_
      exact BPair.add_congr hO1
        (poly.evalClear_congr hT1eq (BPair.ofPos en) ed (C.K - 1))
    · refine BPair.oneValue_trans
        (poly.evalClear_congr (slabGo_split (m * m) 0 m V.2)
          (BPair.ofPos en) ed (C.K - 1)) ?_
      refine BPair.oneValue_trans
        (poly.evalClear_add _ _ (BPair.ofPos en) ed (C.K - 1)) ?_
      exact BPair.add_congr hO2
        (poly.evalClear_congr hT2eq (BPair.ofPos en) ed (C.K - 1))
  have hGval : (poly.evalClear (lineL V (C.fA + C.fB))
      (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)).oneValue
      (poly.evalClear (profLin V)
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
        + ((C.fA + C.fB)
            * ground.bpow (BPair.ofPos ed) (C.K - 1)).swap) := by
    refine BPair.oneValue_trans
      (poly.evalClear_add _ _ (BPair.ofNat (m * m) * BPair.ofPos en) ed
        (C.K - 1)) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    exact BPair.oneValue_trans
      (poly.evalClear_neg _ _ ed (C.K - 1))
      (ground.swap_congr
        (poly.evalClear_single (C.fA + C.fB) _ ed (C.K - 1)))
  have hsplit : (BPair.ofNat m * poly.evalClear (profBaseU V)
        (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
      + poly.evalClear (lineL V (C.fA + C.fB))
          (BPair.ofNat (m * m) * BPair.ofPos en) ed
          (C.K - 1)).oneValue
      ((BPair.ofNat m * poly.evalClear (profBaseU V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
          + poly.evalClear (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
        + ((C.fA + C.fB)
            * ground.bpow (BPair.ofPos ed) (C.K - 1)).swap) := by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) hGval) ?_
    exact BPair.oneValue_of_eq
      (BPair.add_assoc (BPair.ofNat m * poly.evalClear (profBaseU V)
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
        (poly.evalClear (profLin V)
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
        ((C.fA + C.fB)
          * ground.bpow (BPair.ofPos ed) (C.K - 1)).swap).symm
  have hshuffle : (BPair.ofNat m * poly.evalClear (profBaseU V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
          + poly.evalClear (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
        + (poly.evalClear (slabGo (m * m) 1 1 (V.1.map (List.drop 2)))
              (BPair.ofPos en) ed (C.K - 1)
          + poly.evalClear (slabGo (m * m) 1 m (V.2.map (List.drop 1)))
              (BPair.ofPos en) ed (C.K - 1))
      = (poly.evalClear (profLin V)
            (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
          + poly.evalClear (slabGo (m * m) 1 1 (V.1.map (List.drop 2)))
              (BPair.ofPos en) ed (C.K - 1))
        + (BPair.ofNat m * poly.evalClear (profBaseU V)
              (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1)
          + poly.evalClear (slabGo (m * m) 1 m (V.2.map (List.drop 1)))
              (BPair.ofPos en) ed (C.K - 1)) := by
    rw [BPair.add_add_comm
        (poly.evalClear (profLin V)
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
        (poly.evalClear (slabGo (m * m) 1 1 (V.1.map (List.drop 2)))
          (BPair.ofPos en) ed (C.K - 1))
        (BPair.ofNat m * poly.evalClear (profBaseU V)
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
        (poly.evalClear (slabGo (m * m) 1 m (V.2.map (List.drop 1)))
          (BPair.ofPos en) ed (C.K - 1)),
      BPair.add_comm
        (BPair.ofNat m * poly.evalClear (profBaseU V)
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))
        (poly.evalClear (profLin V)
          (BPair.ofNat (m * m) * BPair.ofPos en) ed (C.K - 1))]
  have hswapRU : (poly.evalClear (slabGo (m * m) 1 1 (V.1.map (List.drop 2)))
          (BPair.ofPos en) ed (C.K - 1)
        + poly.evalClear (slabGo (m * m) 1 m (V.2.map (List.drop 1)))
          (BPair.ofPos en) ed (C.K - 1)).swap
      ≤ (C.fA + C.fB) * ground.bpow (BPair.ofPos ed) (C.K - 1) := by
    refine ground.leB_congr_left
      (BPair.oneValue_of_eq (BPair.swap_add _ _)) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.add_comm (C.fB * ground.bpow (BPair.ofPos ed) (C.K - 1))
            (C.fA * ground.bpow (BPair.ofPos ed) (C.K - 1))))
        (BPair.oneValue_of_eq
          (BPair.right_distrib C.fA C.fB
            (ground.bpow (BPair.ofPos ed) (C.K - 1))).symm)) ?_
    exact ground.leB_add
      (ground.leB_trans (windowsep.swap_le_mag _) hR1)
      (ground.leB_trans (windowsep.swap_le_mag _) hR2)
  refine BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm
      (poly.evalClear_congr hstrip (BPair.ofPos en) ed C.K)) ?_
  refine BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm
      (evalClear_shiftUp 1 (poly.add
        (slabGo (m * m) 0 1 (V.1.map (List.drop 1)))
        (slabGo (m * m) 0 m V.2)) (BPair.ofPos en) ed C.K)) ?_
  refine ground.unitLtMul
    (windowsep.unitLt_bpow (ground.unitLtOfPos en) 1) ?_
  refine BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm hWval) ?_
  refine BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_of_eq hshuffle) ?_
  refine ground.ltB_trans_le
    (BPair.lt_congr (BPair.oneValue_refl _) hsplit hbase) ?_
  exact ground.leB_add (ground.leB_refl _) (ground.leB_swap hswapRU)


/-! The bundled corner disconjugacy certificate: the segment and
seam data with their reads, and the whole certificate's decidable
read — the one stated rate, the positive tier's chain from the
boundary seed, the post chain from its own head segment, and the
final seam at the slope allowance with the dominance margin. -/

set_option genInjectivity false in
/-- A seam's certificate: the crossed products' graded read with
the handover cap, one step past the incoming box's bottom. -/
structure SeamCert where
  b : CPair
  cert : GradCert

set_option genInjectivity false in
/-- A segment's certificate: the jet with its positivity box, the
two-step overlap's middle top, and the termwise box at the
stripped comparison object. -/
structure SegCert where
  jet : poly.PPoly × poly.PPoly
  pos : BoxCert
  mid : CPair
  term : BoxCert

set_option genInjectivity false in
/-- The corner disconjugacy certificate: the one stated rate, the
cleared scale ceiling, the pre profile with its graded reads and
boundary seed data, the segment list with its seams, and the final
seam at the slope allowance with the dominance margin; the count's
line is read at every rate at or below the stated one, the glue's
own binder, the cut members' lines among them. -/
structure DisconjCert where
  qcN : Nat
  qcD : Nat
  e0n : BPair
  e0d : Pos
  preV : poly.PPoly × poly.PPoly
  prePos : GradCert
  preMid : CPair
  preTerm : GradCert
  seedK : Nat
  seedCK : Nat
  seedTK : Nat
  posChain : List (SeamCert × SegCert)
  postSeg0 : SegCert
  postRest : List (SeamCert × SegCert)
  fin : SeamCert
  alN : Nat
  alD : Nat
  ws : Nat

/-- One segment's read: the jet's positivity box, the stripped
comparison's box, and the two-step overlap of the termwise box
inside the positivity box. -/
def segRead (r qcN qcD : Nat) (e0n : BPair) (e0d : Pos)
    (S : SegCert) : Prop :=
  boxRead S.jet e0n e0d S.pos
  ∧ boxRead (profStrip (termProf S.jet r qcN qcD)) e0n e0d S.term
  ∧ S.pos.lo ≤ S.term.lo
  ∧ stepClear S.term.hi S.mid e0n e0d
  ∧ stepClear S.mid S.pos.hi e0n e0d

instance (r qcN qcD : Nat) (e0n : BPair) (e0d : Pos) (S : SegCert) :
    Decidable (segRead r qcN qcD e0n e0d S) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- One seam's read against the outgoing coverage: the crossed
products' graded read on the seam's box, the handover cap one step
past the incoming box's bottom and inside the seam's box, the
outgoing coverage and the incoming box both reaching it, and the
incoming bottom at or beyond the outgoing one, the handover depths
non-decreasing along the chain. -/
def seamRead (e0n : BPair) (e0d : Pos)
    (Vp : poly.PPoly × poly.PPoly) (loPrev hiPrev : CPair)
    (M : SeamCert) (S : SegCert) : Prop :=
  gradRead (crossProf Vp S.jet) e0n e0d M.cert
  ∧ M.cert.lo ≤ S.term.lo
  ∧ stepClear S.term.lo M.b e0n e0d
  ∧ M.b ≤ M.cert.hi
  ∧ M.b ≤ hiPrev
  ∧ M.b ≤ S.term.hi
  ∧ loPrev ≤ S.term.lo

instance (e0n : BPair) (e0d : Pos) (Vp : poly.PPoly × poly.PPoly)
    (loPrev hiPrev : CPair) (M : SeamCert) (S : SegCert) :
    Decidable (seamRead e0n e0d Vp loPrev hiPrev M S) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A seam-chained segment list's read from a standing profile and
its coverage top: each segment enters with its seam against the
standing one. -/
def chainSegs (r qN qD : Nat) (e0n : BPair) (e0d : Pos) :
    (poly.PPoly × poly.PPoly) → CPair → CPair →
      List (SeamCert × SegCert) → Prop
  | _, _, _, [] => True
  | Vp, loPrev, hiPrev, (M, S) :: t =>
    seamRead e0n e0d Vp loPrev hiPrev M S
    ∧ segRead r qN qD e0n e0d S
    ∧ chainSegs r qN qD e0n e0d S.jet S.term.lo S.term.hi t

def decChainSegs (r qN qD : Nat) (e0n : BPair) (e0d : Pos) :
    ∀ (Vp : poly.PPoly × poly.PPoly) (loPrev hiPrev : CPair)
      (l : List (SeamCert × SegCert)),
      Decidable (chainSegs r qN qD e0n e0d Vp loPrev hiPrev l)
  | _, _, _, [] => isTrue trivial
  | _Vp, _loPrev, _hiPrev, (_M, S) :: t =>
    @instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ inferInstance
        (decChainSegs r qN qD e0n e0d S.jet S.term.lo S.term.hi t))

instance (r qN qD : Nat) (e0n : BPair) (e0d : Pos)
    (Vp : poly.PPoly × poly.PPoly) (loPrev hiPrev : CPair)
    (l : List (SeamCert × SegCert)) :
    Decidable (chainSegs r qN qD e0n e0d Vp loPrev hiPrev l) :=
  decChainSegs r qN qD e0n e0d Vp loPrev hiPrev l

/-- The segment list's last member, the final seam's outgoing
segment. -/
def lastSeg (S0 : SegCert) (rest : List (SeamCert × SegCert)) :
    SegCert :=
  rest.foldl (fun _ p => p.2) S0

/-- The positive tier's coverage top: the last chained segment's
termwise box top, the pre coverage's at a vacant chain. -/
def posTop (hiPre : CPair) (l : List (SeamCert × SegCert)) : CPair :=
  l.foldl (fun _ p => p.2.term.hi) hiPre

/-- The boundary seed's read: the boundary value, the boundary
comparison and the boundary termwise comparison at the stripped
object, their lengths inside the stated clearings and each floored
past its origin by the ceiling's priced fold — the three origins
are vacant at the graded device's scale-free vacancy
(`vacHead`, `seedHeadVac`, `stripHeadVac`), so the floors are the
seed's whole data. -/
def seedRead (r qN qD : Nat) (e0n : BPair) (e0d : Pos)
    (V : poly.PPoly × poly.PPoly) (K0 Kc Kt : Nat) : Prop :=
  (depthPoly V 0).length ≤ K0 + 2
  ∧ lowRead (List.drop 1 (depthPoly V 0)) e0n e0d K0
  ∧ (depthPoly (seedProf V r qN qD) 0).length ≤ Kc + 2
  ∧ lowRead (List.drop 1 (depthPoly (seedProf V r qN qD) 0))
      e0n e0d Kc
  ∧ (depthPoly (profStrip (termProf V r qN qD)) 0).length ≤ Kt + 2
  ∧ lowRead
      (List.drop 1 (depthPoly (profStrip (termProf V r qN qD)) 0))
      e0n e0d Kt

instance (r qN qD : Nat) (e0n : BPair) (e0d : Pos)
    (V : poly.PPoly × poly.PPoly) (K0 Kc Kt : Nat) :
    Decidable (seedRead r qN qD e0n e0d V K0 Kc Kt) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The certificate's read: the one stated rate and the allowance
data occupied; the pre tier's graded reads with the
boundary seed and the positive chain; the post chain from its own
head segment, its first box reaching below the positive coverage
top, the crossing seam the two chains' break at that comparison
alone; and the final seam at the slope allowance with the located
dominance margin and the tail's two allowance comparisons. -/
def certRead (r : Nat) (C : DisconjCert) : Prop :=
  1 ≤ C.qcD
  ∧ 1 ≤ C.alD
  ∧ gradRead C.preV C.e0n C.e0d C.prePos
  ∧ gradRead (profStrip (termProf C.preV r C.qcN C.qcD))
      C.e0n C.e0d C.preTerm
  ∧ C.prePos.lo ≤ stage.unitC
  ∧ C.preTerm.lo ≤ stage.unitC
  ∧ stepClear C.preTerm.hi C.preMid C.e0n C.e0d
  ∧ stepClear C.preMid C.prePos.hi C.e0n C.e0d
  ∧ seedRead r C.qcN C.qcD C.e0n C.e0d C.preV C.seedK C.seedCK
      C.seedTK
  ∧ chainSegs r C.qcN C.qcD C.e0n C.e0d C.preV stage.unitC
      C.preTerm.hi C.posChain
  ∧ segRead r C.qcN C.qcD C.e0n C.e0d C.postSeg0
  ∧ C.postSeg0.term.lo ≤ posTop C.preTerm.hi C.posChain
  ∧ chainSegs r C.qcN C.qcD C.e0n C.e0d C.postSeg0.jet
      C.postSeg0.term.lo C.postSeg0.term.hi C.postRest
  ∧ gradRead (slopeProf (lastSeg C.postSeg0 C.postRest).jet
      C.alN C.alD) C.e0n C.e0d C.fin.cert
  ∧ stage.unitC < C.fin.cert.lo
  ∧ (lastSeg C.postSeg0 C.postRest).term.lo ≤ C.fin.cert.lo
  ∧ stepClear C.fin.cert.lo C.fin.b C.e0n C.e0d
  ∧ C.fin.b ≤ C.fin.cert.hi
  ∧ C.fin.b ≤ (lastSeg C.postSeg0 C.postRest).term.hi
  ∧ stage.ofB (BPair.ofNat ((r + 1) * C.qcN + C.ws))
      ≤ stage.ofB (BPair.ofNat (4 * C.qcD)) * C.fin.cert.lo
  ∧ stage.ofB (BPair.ofNat (18 * ((r + 1) * C.qcD)
        * (C.alN * C.alN))) * C.fin.b
      ≤ stage.ofB (BPair.ofNat (C.ws * (C.alD * C.alD)))
  ∧ stage.ofB (BPair.ofNat (36 * (C.alN * C.alN)))
      * (C.fin.b * (⟨C.e0n, C.e0d⟩ : CPair))
      ≤ stage.ofB (BPair.ofNat (C.alD * C.alD))

instance (r : Nat) (C : DisconjCert) : Decidable (certRead r C) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))


/-! `lem:cornerpivot`(v)'s ground witness: the family
`x_m = s⟨s₂:s⟩` at the square-scale pair `s₂ = N²η`, cleared at the
scale's square, with its power sums, its closed reads, the lower
rate's two data and the endpoint key. -/

/-- The witness family's cleared value at a depth: `w_m = m²(N²−m²)`,
the square-scale pair's balance at the scale's square withdrawn
(`lem:corner`'s clearing), the truncated difference the family's own
read — equal members at the endpoint and the sum's unit beyond. -/
def witVal (N m : Nat) : Nat := m * m * (N * N - m * m)

/-- The power sum `S_k(n) = Σ_{m=1}^{n} m^k`, the closed reads'
shared carrier (`def:poly`'s binomial identities close it). -/
def powSum (k n : Nat) : Nat :=
  ground.sumNat ((List.range n).map (fun j => (j + 1) ^ k))

/-- The family's square sum. -/
def witSq (N : Nat) : Nat :=
  ground.sumNat ((List.range N).map (fun k => (witVal N (k + 1)) ^ 2))

/-- The well sum's linear part, `Σ m·w_m²`. -/
def witSqM (N : Nat) : Nat :=
  ground.sumNat ((List.range N).map (fun k => (k + 1) * (witVal N (k + 1)) ^
    2))

/-- The well sum's square part, `Σ m²·w_m²`. -/
def witSqMM (N : Nat) : Nat :=
  ground.sumNat ((List.range N).map
    (fun k => (k + 1) * (k + 1) * (witVal N (k + 1)) ^ 2))

/-- The margin of two naturals, the trichotomy's one value. -/
def marg (a b : Nat) : Nat := (a - b) + (b - a)

/-- The difference sum, `Σ ⟨x_{m+1}:x_m⟩²` at the cleared bond pair
`(2m+1)·⟨N² : 2m²+2m+1⟩`, the margin's square per depth. -/
def witDiffSq (N : Nat) : Nat :=
  ground.sumNat ((List.range (N - 1)).map (fun k =>
    ((2 * (k + 1) + 1) * marg (N * N)
      (2 * (k + 1) * (k + 1) + 2 * (k + 1) + 1)) ^ 2))

/-- The lower rate's first datum, the display's right side cleared:
`4en²(Σm²w² + rΣmw²) + (r+1)ed²(Σd² + w₁²)`. -/
def qLowNum (en ed r N : Nat) : Nat :=
  4 * en ^ 2 * (witSqMM N + r * witSqM N)
    + (r + 1) * ed ^ 2 * (witDiffSq N + (N * N - 1) ^ 2)

/-- The lower rate's second datum, the cleared `en·ed·(r+1)·Σw²`. -/
def qLowDen (en ed r N : Nat) : Nat := en * ed * (r + 1) * witSq N

/-- The endpoint key's read: the depth beyond one, the comparison
`40N⁴η² ≥ 363(r+1)` at the scale's cleared members, and the
leastness among the depths beyond one — the depth two outright, or
the predecessor's refusal. -/
def endRead (en ed r N : Nat) : Prop :=
  2 ≤ N ∧ 363 * (r + 1) * ed ^ 2 ≤ 40 * N ^ 4 * en ^ 2
    ∧ (N = 2 ∨ ¬ 363 * (r + 1) * ed ^ 2 ≤ 40 * (N - 1) ^ 4 * en ^ 2)

instance (en ed r N : Nat) : Decidable (endRead en ed r N) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _)))

/-- The closed reads' polynomial objects: the family's square at the
630-clearing, keys 0..9. -/
def sqClosedPoly : poly.Poly :=
  [BPair.unit, (BPair.ofNat 21).swap, BPair.unit, BPair.ofNat 110,
   BPair.unit, (BPair.ofNat 105).swap, BPair.unit, BPair.unit,
   BPair.unit, BPair.ofNat 16]

/-- The difference sum's polynomial at the 105-clearing, keys 0..7. -/
def diffClosedPoly : poly.Poly :=
  [(BPair.ofNat 105).swap, (BPair.ofNat 23).swap, BPair.ofNat 210,
   BPair.ofNat 126, (BPair.ofNat 105).swap, (BPair.ofNat 147).swap,
   BPair.unit, BPair.ofNat 44]

/-- The square well part's polynomial at the 6930-clearing, keys 0..11. -/
def wellClosedPoly : poly.Poly :=
  [BPair.unit, BPair.ofNat 525, BPair.unit, (BPair.ofNat 3003).swap,
   BPair.unit, BPair.ofNat 4015, BPair.unit, (BPair.ofNat 1617).swap,
   BPair.unit, BPair.unit, BPair.unit, BPair.ofNat 80]

/-! `lem:cornerpivot`(v)'s arithmetic tier: the ground witness
family, its power sums with their closed reads, the lower rate's
two data with the endpoint key, and the telescope, form and kernel
identities the tex's three displays carry.

The universal count identities the tier consumes — the power sums'
binomial steps, the bridges' per-depth reads and the closed reads'
assemblies — are settled through one device: an expression mirrors
into a count family over two variables, the outer variable's keys
carrying the inner variable's own families (`Mir.keys`), the
mirror's value is the expression itself (`Mir.val`), the Horner
reads agree with the expression node by node (`Mir.read`), and two
expressions whose mirrored families reduce alike read one value
(`mirEq`). -/

/-- The count family's Horner read at a count. -/
private def hread : List Nat → Nat → Nat
  | [], _ => 0
  | c :: p, g => c + g * hread p g

/-- Two count families' key-by-key sum, the longer family's tail
riding. -/
private def hadd : List Nat → List Nat → List Nat
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => (c + d) :: hadd p q

/-- Two count families' convolution. -/
private def hmul : List Nat → List Nat → List Nat
  | [], _ => []
  | c :: p, q => hadd (q.map (fun d => c * d)) (0 :: hmul p q)

private theorem hread_add : ∀ (p q : List Nat) (n : Nat),
    hread (hadd p q) n = hread p n + hread q n
  | [], q, n => (Nat.zero_add (hread q n)).symm
  | c :: p, [], n => (Nat.add_zero (hread (c :: p) n)).symm
  | c :: p, d :: q, n => by
    show c + d + n * hread (hadd p q) n
      = c + n * hread p n + (d + n * hread q n)
    rw [hread_add p q n, Nat.left_distrib n (hread p n) (hread q n),
      Nat.add_add_add_comm c d (n * hread p n) (n * hread q n)]

private theorem hread_scale : ∀ (q : List Nat) (c n : Nat),
    hread (q.map (fun d => c * d)) n = c * hread q n
  | [], c, _ => (Nat.mul_zero c).symm
  | d :: q, c, n => by
    show c * d + n * hread (q.map (fun d => c * d)) n
      = c * (d + n * hread q n)
    rw [hread_scale q c n, Nat.left_distrib c d (n * hread q n),
      ground.mulLeftComm n c (hread q n)]

private theorem hread_mul : ∀ (p q : List Nat) (n : Nat),
    hread (hmul p q) n = hread p n * hread q n
  | [], q, n => (Nat.zero_mul (hread q n)).symm
  | c :: p, q, n => by
    show hread (hadd (q.map (fun d => c * d)) (0 :: hmul p q)) n
      = (c + n * hread p n) * hread q n
    rw [hread_add (q.map (fun d => c * d)) (0 :: hmul p q) n,
      hread_scale q c n]
    show c * hread q n + (0 + n * hread (hmul p q) n)
      = (c + n * hread p n) * hread q n
    rw [hread_mul p q n, Nat.zero_add,
      ground.mulAddR c (n * hread p n) (hread q n),
      ground.mulAssoc n (hread p n) (hread q n)]

private theorem hread_cst (c g : Nat) : hread [c] g = c := by
  show c + g * 0 = c
  rw [Nat.mul_zero g, Nat.add_zero c]

private theorem hread_lin (a b g : Nat) : hread [a, b] g = a + g * b := by
  show a + g * (b + g * 0) = a + g * b
  rw [Nat.mul_zero g, Nat.add_zero b]

/-- The two-variable Horner read: the outer variable's keys are the
inner variable's own count families. -/
private def h2read : List (List Nat) → Nat → Nat → Nat
  | [], _, _ => 0
  | c :: p, m, g => hread c g + m * h2read p m g

private def h2add : List (List Nat) → List (List Nat) → List (List Nat)
  | [], q => q
  | c :: p, [] => c :: p
  | c :: p, d :: q => hadd c d :: h2add p q

private def h2mul : List (List Nat) → List (List Nat) → List (List Nat)
  | [], _ => []
  | c :: p, q => h2add (q.map (fun d => hmul c d)) ([] :: h2mul p q)

private theorem h2read_add : ∀ (p q : List (List Nat)) (m g : Nat),
    h2read (h2add p q) m g = h2read p m g + h2read q m g
  | [], q, m, g => (Nat.zero_add (h2read q m g)).symm
  | c :: p, [], m, g => (Nat.add_zero (h2read (c :: p) m g)).symm
  | c :: p, d :: q, m, g => by
    show hread (hadd c d) g + m * h2read (h2add p q) m g
      = hread c g + m * h2read p m g + (hread d g + m * h2read q m g)
    rw [hread_add c d g, h2read_add p q m g,
      Nat.left_distrib m (h2read p m g) (h2read q m g),
      Nat.add_add_add_comm (hread c g) (hread d g)
        (m * h2read p m g) (m * h2read q m g)]

private theorem h2read_scale : ∀ (q : List (List Nat)) (c : List Nat)
    (m g : Nat),
    h2read (q.map (fun d => hmul c d)) m g = hread c g * h2read q m g
  | [], c, _, g => (Nat.mul_zero (hread c g)).symm
  | d :: q, c, m, g => by
    show hread (hmul c d) g + m * h2read (q.map (fun d => hmul c d)) m g
      = hread c g * (hread d g + m * h2read q m g)
    rw [hread_mul c d g, h2read_scale q c m g,
      Nat.left_distrib (hread c g) (hread d g) (m * h2read q m g),
      ground.mulLeftComm m (hread c g) (h2read q m g)]

private theorem h2read_mul : ∀ (p q : List (List Nat)) (m g : Nat),
    h2read (h2mul p q) m g = h2read p m g * h2read q m g
  | [], q, m, g => (Nat.zero_mul (h2read q m g)).symm
  | c :: p, q, m, g => by
    show h2read (h2add (q.map (fun d => hmul c d)) ([] :: h2mul p q)) m g
      = (hread c g + m * h2read p m g) * h2read q m g
    rw [h2read_add (q.map (fun d => hmul c d)) ([] :: h2mul p q) m g,
      h2read_scale q c m g]
    show hread c g * h2read q m g + (0 + m * h2read (h2mul p q) m g)
      = (hread c g + m * h2read p m g) * h2read q m g
    rw [h2read_mul p q m g, Nat.zero_add,
      ground.mulAddR (hread c g) (m * h2read p m g) (h2read q m g),
      ground.mulAssoc m (h2read p m g) (h2read q m g)]

private def h2pow (p : List (List Nat)) : Nat → List (List Nat)
  | 0 => [[1]]
  | k + 1 => h2mul p (h2pow p k)

private theorem h2read_pow (p : List (List Nat)) (m g : Nat) :
    ∀ k : Nat, h2read (h2pow p k) m g = h2read p m g ^ k
  | 0 => by
    show hread [1] g + m * 0 = h2read p m g ^ 0
    rw [hread_cst 1 g, Nat.mul_zero m, Nat.add_zero 1, Nat.pow_zero]
  | k + 1 => by
    rw [show h2pow p (k + 1) = h2mul p (h2pow p k) from rfl,
      h2read_mul p (h2pow p k) m g, h2read_pow p m g k, Nat.pow_succ,
      Nat.mul_comm (h2read p m g) (h2read p m g ^ k)]

set_option genInjectivity false in
/-- The mirrored expression over two variables: the constants, the
two variables, and the sum, the product and the stated power. -/
private inductive Mir where
  | cst : Nat → Mir
  | x : Mir
  | y : Mir
  | add : Mir → Mir → Mir
  | mul : Mir → Mir → Mir
  | pow : Mir → Nat → Mir

/-- The mirror's count families, one key family per outer key. -/
private def Mir.keys : Mir → List (List Nat)
  | .cst c => [[c]]
  | .x => [[0], [1]]
  | .y => [[0, 1]]
  | .add a b => h2add a.keys b.keys
  | .mul a b => h2mul a.keys b.keys
  | .pow a k => h2pow a.keys k

/-- The mirror's own value at the two counts. -/
private def Mir.val (m g : Nat) : Mir → Nat
  | .cst c => c
  | .x => m
  | .y => g
  | .add a b => a.val m g + b.val m g
  | .mul a b => a.val m g * b.val m g
  | .pow a k => a.val m g ^ k

/-- The mirrored families' Horner read is the expression's value. -/
private theorem Mir.read (m g : Nat) : ∀ e : Mir,
    h2read e.keys m g = e.val m g
  | .cst c => by
    show hread [c] g + m * 0 = c
    rw [hread_cst c g, Nat.mul_zero m, Nat.add_zero c]
  | .x => by
    show hread [0] g + m * (hread [1] g + m * 0) = m
    rw [hread_cst 0 g, hread_cst 1 g, Nat.mul_zero m, Nat.add_zero 1,
      Nat.mul_one m, Nat.zero_add m]
  | .y => by
    show hread [0, 1] g + m * 0 = g
    rw [hread_lin 0 1 g, Nat.mul_zero m, Nat.add_zero (0 + g * 1),
      Nat.mul_one g, Nat.zero_add g]
  | .add a b => by
    show h2read (h2add a.keys b.keys) m g = a.val m g + b.val m g
    rw [h2read_add a.keys b.keys m g, Mir.read m g a, Mir.read m g b]
  | .mul a b => by
    show h2read (h2mul a.keys b.keys) m g = a.val m g * b.val m g
    rw [h2read_mul a.keys b.keys m g, Mir.read m g a, Mir.read m g b]
  | .pow a k => by
    show h2read (h2pow a.keys k) m g = a.val m g ^ k
    rw [h2read_pow a.keys m g k, Mir.read m g a]

/-- The vacant families' padding, the key window the mirrors are
compared inside. -/
private def zeroPad : List (List Nat) :=
  List.replicate 32 (List.replicate 16 0)

private theorem hread_zeroRow (g : Nat) :
    ∀ J : Nat, hread (List.replicate J 0) g = 0
  | 0 => rfl
  | J + 1 => by
    show 0 + g * hread (List.replicate J 0) g = 0
    rw [hread_zeroRow g J, Nat.mul_zero g, Nat.add_zero 0]

private theorem h2read_zeroRows (m g : Nat) :
    ∀ K : Nat, h2read (List.replicate K (List.replicate 16 0)) m g = 0
  | 0 => rfl
  | K + 1 => by
    show hread (List.replicate 16 0) g
        + m * h2read (List.replicate K (List.replicate 16 0)) m g = 0
    rw [hread_zeroRow g 16, h2read_zeroRows m g K, Nat.mul_zero m,
      Nat.add_zero 0]

private theorem h2read_zeroPad (m g : Nat) : h2read zeroPad m g = 0 :=
  h2read_zeroRows m g 32

/-- A count family agreeing with a mirror's padded families reads
the mirror's own value. -/
private theorem mirRaw (m g : Nat) (K : List (List Nat)) (b : Mir)
    (h : h2add K zeroPad = h2add b.keys zeroPad) :
    h2read K m g = b.val m g := by
  have hK : h2read (h2add K zeroPad) m g = h2read K m g := by
    rw [h2read_add K zeroPad m g, h2read_zeroPad m g, Nat.add_zero]
  have hb : h2read (h2add b.keys zeroPad) m g = b.val m g := by
    rw [h2read_add b.keys zeroPad m g, h2read_zeroPad m g,
      Nat.add_zero, Mir.read m g b]
  rw [← hK, ← hb, h]

/-- Two mirrors whose padded count families agree read one value at
every count pair. -/
private theorem mirEq (m g : Nat) (a b : Mir)
    (h : h2add a.keys zeroPad = h2add b.keys zeroPad) :
    a.val m g = b.val m g :=
  (Mir.read m g a).symm.trans (mirRaw m g a.keys b h)

/-- A one-variable count family enters the two-variable read at its
one-count keys. -/
private theorem hreadRow : ∀ (L : List Nat) (N : Nat),
    hread L N = h2read (L.map (fun c => [c])) N 0
  | [], _ => rfl
  | c :: t, N => by
    show c + N * hread t N
      = hread [c] 0 + N * h2read (t.map (fun c => [c])) N 0
    rw [hread_cst c 0, hreadRow t N]

/-! The monomial device: a product mirrors into a count and an
exponent family over a stated datum list, the mirror's value is the
product itself, and two products whose counts and exponent families
agree read one value. -/

private theorem powAdd (x a : Nat) : ∀ b : Nat, x ^ (a + b) = x ^ a * x ^ b
  | 0 => by rw [Nat.add_zero a, Nat.pow_zero x, Nat.mul_one (x ^ a)]
  | b + 1 => by
    rw [← Nat.add_assoc a b 1, Nat.pow_succ x (a + b), powAdd x a b,
      Nat.pow_succ x b, ground.mulAssoc (x ^ a) (x ^ b) x]

private theorem powOne (x : Nat) : x ^ 1 = x := by
  rw [Nat.pow_succ x 0, Nat.pow_zero x, Nat.one_mul x]

/-- The exponent family's product against a stated datum list, from
a stated key. -/
private def expVal (env : List Nat) : Nat → List Nat → Nat
  | _, [] => 1
  | i, k :: t => ground.getAt 0 env i ^ k * expVal env (i + 1) t

/-- The one-key exponent family. -/
private def unitAt : Nat → List Nat
  | 0 => [1]
  | i + 1 => 0 :: unitAt i

private theorem expVal_hadd (env : List Nat) : ∀ (i : Nat) (u v : List Nat),
    expVal env i (hadd u v) = expVal env i u * expVal env i v
  | i, [], v => (Nat.one_mul (expVal env i v)).symm
  | i, a :: u, [] => (Nat.mul_one (expVal env i (a :: u))).symm
  | i, a :: u, b :: v => by
    show ground.getAt 0 env i ^ (a + b) * expVal env (i + 1) (hadd u v)
      = ground.getAt 0 env i ^ a * expVal env (i + 1) u
        * (ground.getAt 0 env i ^ b * expVal env (i + 1) v)
    rw [powAdd (ground.getAt 0 env i) a b, expVal_hadd env (i + 1) u v,
      ground.mulMulMulComm (ground.getAt 0 env i ^ a)
        (ground.getAt 0 env i ^ b) (expVal env (i + 1) u)
        (expVal env (i + 1) v)]

private theorem expVal_unitAt (env : List Nat) : ∀ (j i : Nat),
    expVal env j (unitAt i) = ground.getAt 0 env (j + i)
  | j, 0 => by
    show ground.getAt 0 env j ^ 1 * 1 = ground.getAt 0 env (j + 0)
    rw [Nat.mul_one, powOne, Nat.add_zero j]
  | j, i + 1 => by
    show ground.getAt 0 env j ^ 0 * expVal env (j + 1) (unitAt i)
      = ground.getAt 0 env (j + (i + 1))
    rw [Nat.pow_zero, Nat.one_mul, expVal_unitAt env (j + 1) i,
      Nat.add_right_comm j 1 i, Nat.add_assoc j i 1]

set_option genInjectivity false in
/-- The mirrored product: the counts, the stated data and the
product. -/
private inductive Mon where
  | cst : Nat → Mon
  | var : Nat → Mon
  | mul : Mon → Mon → Mon

/-- The mirror's own value at a stated datum list. -/
private def Mon.val (env : List Nat) : Mon → Nat
  | .cst c => c
  | .var i => ground.getAt 0 env i
  | .mul a b => a.val env * b.val env

/-- The mirror's count. -/
private def Mon.coef : Mon → Nat
  | .cst c => c
  | .var _ => 1
  | .mul a b => a.coef * b.coef

/-- The mirror's exponent family. -/
private def Mon.exps : Mon → List Nat
  | .cst _ => []
  | .var i => unitAt i
  | .mul a b => hadd a.exps b.exps

private theorem Mon.read (env : List Nat) : ∀ m : Mon,
    m.val env = m.coef * expVal env 0 m.exps
  | .cst c => by
    show c = c * 1
    rw [Nat.mul_one c]
  | .var i => by
    show ground.getAt 0 env i = 1 * expVal env 0 (unitAt i)
    rw [Nat.one_mul, expVal_unitAt env 0 i, Nat.zero_add i]
  | .mul a b => by
    show a.val env * b.val env
      = a.coef * b.coef * expVal env 0 (hadd a.exps b.exps)
    rw [Mon.read env a, Mon.read env b, expVal_hadd env 0 a.exps b.exps,
      ground.mulMulMulComm a.coef (expVal env 0 a.exps) b.coef
        (expVal env 0 b.exps)]

/-- Two mirrored products whose counts and exponent families agree
read one value at every datum list. -/
private theorem monEq (env : List Nat) (a b : Mon)
    (hc : a.coef = b.coef) (he : a.exps = b.exps) :
    a.val env = b.val env := by
  rw [Mon.read env a, Mon.read env b, hc, he]

example (en ed r : Nat) :
    4 * (en * en) * 80 * 630 * (11 * (r + 1) * ed)
      = 6930 * (en * ed * (r + 1) * 16) * (20 * en) :=
  monEq [en, ed, r + 1]
    (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4)
        (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.cst 80)) (Mon.cst 630))
      (Mon.mul (Mon.mul (Mon.cst 11) (Mon.var 2)) (Mon.var 1)))
    (Mon.mul (Mon.mul (Mon.cst 6930)
        (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
          (Mon.cst 16)))
      (Mon.mul (Mon.cst 20) (Mon.var 0)))
    (by decide +kernel) (by decide +kernel)

/-- The power sum grows at its endpoint by the arriving depth's own
power. -/
private theorem powSum_succ (k n : Nat) :
    powSum k (n + 1) = powSum k n + (n + 1) ^ k := by
  show ground.sumNat (((List.range (n + 1))).map (fun j => (j + 1) ^ k))
    = ground.sumNat ((List.range n).map (fun j => (j + 1) ^ k))
      + (n + 1) ^ k
  rw [ground.range_succ n, ground.map_append, ground.sumNat_append]
  rfl

/-- A count family's total scales through its scalar. -/
private theorem sumNat_scale (c : Nat) (f : Nat → Nat)
    (l : List Nat) :
    c * ground.sumNat (l.map f)
      = ground.sumNat (l.map (fun x => c * f x)) := by
  rw [ground.sumMap f l, ground.sumMap (fun x => c * f x) l]
  exact ground.famFold_mul c f l

/-- The closed read's induction: the base at the vacant endpoint and
one step identity per depth settle the cleared read at every
endpoint. -/
private theorem sumClosed (k a : Nat) (L R : Nat → Nat)
    (hb : L 0 = R 0)
    (hs : ∀ n : Nat, R (n + 1) + L n = R n + L (n + 1) + a * (n + 1) ^ k) :
    ∀ n : Nat, a * powSum k n + L n = R n
  | 0 => by
    show a * 0 + L 0 = R 0
    rw [Nat.mul_zero a, Nat.zero_add]
    exact hb
  | n + 1 => by
    refine ground.addCancelR (L n) ?_
    rw [powSum_succ k n,
      Nat.left_distrib a (powSum k n) ((n + 1) ^ k), hs n,
      Nat.add_right_comm (a * powSum k n) (a * (n + 1) ^ k) (L (n + 1)),
      Nat.add_assoc (a * powSum k n + L (n + 1)) (a * (n + 1) ^ k) (L n),
      Nat.add_comm (a * (n + 1) ^ k) (L n),
      ← Nat.add_assoc (a * powSum k n + L (n + 1)) (L n) (a * (n + 1) ^ k),
      Nat.add_right_comm (a * powSum k n) (L (n + 1)) (L n),
      sumClosed k a L R hb hs n,
      Nat.add_right_comm (R n) (L (n + 1)) (a * (n + 1) ^ k)]

/-- The power sum's step identity at the key 1. -/
private theorem powStep1 (n : Nat) :
    (n + 1) ^ 2 + (n + 1)
      = n ^ 2 + n + 2 * (n + 1) ^ 1 :=
  mirEq n 0 (Mir.add (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 2) (Mir.add
    Mir.x (Mir.cst 1))) (Mir.add (Mir.add (Mir.pow Mir.x 2) Mir.x)
    (Mir.mul (Mir.cst 2) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 1))) (by decide +kernel)

/-- The power sum's step identity at the key 2. -/
private theorem powStep2 (n : Nat) :
    2 * (n + 1) ^ 3 + 3 * (n + 1) ^ 2 + (n + 1)
      = 2 * n ^ 3 + 3 * n ^ 2 + n + 6 * (n + 1) ^ 2 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.mul (Mir.cst 2) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 3)) (Mir.mul (Mir.cst 3) (Mir.pow (Mir.add Mir.x (Mir.cst
    1)) 2))) (Mir.add Mir.x (Mir.cst 1))) (Mir.add (Mir.add (Mir.add
    (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 3)) (Mir.mul (Mir.cst 3) (Mir.pow
    Mir.x 2))) Mir.x) (Mir.mul (Mir.cst 6) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 2))) (by decide +kernel)

/-- The power sum's step identity at the key 3. -/
private theorem powStep3 (n : Nat) :
    (n + 1) ^ 4 + 2 * (n + 1) ^ 3 + (n + 1) ^ 2
      = n ^ 4 + 2 * n ^ 3 + n ^ 2 + 4 * (n + 1) ^ 3 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 4)
    (Mir.mul (Mir.cst 2) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 3)))
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 2)) (Mir.add (Mir.add (Mir.add
    (Mir.pow Mir.x 4) (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 3))) (Mir.pow
    Mir.x 2)) (Mir.mul (Mir.cst 4) (Mir.pow (Mir.add Mir.x (Mir.cst 1))
    3))) (by decide +kernel)

/-- The power sum's step identity at the key 4. -/
private theorem powStep4 (n : Nat) :
    6 * (n + 1) ^ 5 + 15 * (n + 1) ^ 4 + 10 * (n + 1) ^ 3 + n
      = 6 * n ^ 5 + 15 * n ^ 4 + 10 * n ^ 3 + ((n + 1)) + 30 * (n + 1) ^ 4
        :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 5)) (Mir.mul (Mir.cst 15) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 4))) (Mir.mul (Mir.cst 10) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 3))) Mir.x) (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 5)) (Mir.mul (Mir.cst 15)
    (Mir.pow Mir.x 4))) (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 3))) (Mir.add
    Mir.x (Mir.cst 1))) (Mir.mul (Mir.cst 30) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 4))) (by decide +kernel)

/-- The power sum's step identity at the key 5. -/
private theorem powStep5 (n : Nat) :
    2 * (n + 1) ^ 6 + 6 * (n + 1) ^ 5 + 5 * (n + 1) ^ 4 + n ^ 2
      = 2 * n ^ 6 + 6 * n ^ 5 + 5 * n ^ 4 + ((n + 1) ^ 2) + 12 * (n + 1) ^
        5 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 2) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 6)) (Mir.mul (Mir.cst 6) (Mir.pow (Mir.add
    Mir.x (Mir.cst 1)) 5))) (Mir.mul (Mir.cst 5) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 4))) (Mir.pow Mir.x 2)) (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 6)) (Mir.mul (Mir.cst 6)
    (Mir.pow Mir.x 5))) (Mir.mul (Mir.cst 5) (Mir.pow Mir.x 4))) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 2)) (Mir.mul (Mir.cst 12) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 5))) (by decide +kernel)

/-- The power sum's step identity at the key 6. -/
private theorem powStep6 (n : Nat) :
    6 * (n + 1) ^ 7 + 21 * (n + 1) ^ 6 + 21 * (n + 1) ^ 5 + (n + 1) + 7 *
      n ^ 3
      = 6 * n ^ 7 + 21 * n ^ 6 + 21 * n ^ 5 + n + (7 * (n + 1) ^ 3) + 42 *
        (n + 1) ^ 6 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 6)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 7)) (Mir.mul (Mir.cst 21)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 6))) (Mir.mul (Mir.cst 21)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 5))) (Mir.add Mir.x (Mir.cst 1)))
    (Mir.mul (Mir.cst 7) (Mir.pow Mir.x 3))) (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 7)) (Mir.mul
    (Mir.cst 21) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst 21) (Mir.pow Mir.x
    5))) Mir.x) (Mir.mul (Mir.cst 7) (Mir.pow (Mir.add Mir.x (Mir.cst 1))
    3))) (Mir.mul (Mir.cst 42) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 6)))
    (by decide +kernel)

/-- The power sum's step identity at the key 7. -/
private theorem powStep7 (n : Nat) :
    3 * (n + 1) ^ 8 + 12 * (n + 1) ^ 7 + 14 * (n + 1) ^ 6 + 2 * (n + 1) ^
      2 + 7 * n ^ 4
      = 3 * n ^ 8 + 12 * n ^ 7 + 14 * n ^ 6 + 2 * n ^ 2 + (7 * (n + 1) ^
        4) + 24 * (n + 1) ^ 7 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 3)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 8)) (Mir.mul (Mir.cst 12)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 7))) (Mir.mul (Mir.cst 14)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 6))) (Mir.mul (Mir.cst 2)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 2))) (Mir.mul (Mir.cst 7)
    (Mir.pow Mir.x 4))) (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add
    (Mir.mul (Mir.cst 3) (Mir.pow Mir.x 8)) (Mir.mul (Mir.cst 12) (Mir.pow
    Mir.x 7))) (Mir.mul (Mir.cst 14) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst
    2) (Mir.pow Mir.x 2))) (Mir.mul (Mir.cst 7) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 4))) (Mir.mul (Mir.cst 24) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 7))) (by decide +kernel)

/-- The power sum's step identity at the key 8. -/
private theorem powStep8 (n : Nat) :
    10 * (n + 1) ^ 9 + 45 * (n + 1) ^ 8 + 60 * (n + 1) ^ 7 + 20 * (n + 1)
      ^ 3 + (42 * n ^ 5 + 3 * n)
      = 10 * n ^ 9 + 45 * n ^ 8 + 60 * n ^ 7 + 20 * n ^ 3 + (42 * (n + 1)
        ^ 5 + 3 * (n + 1)) + 90 * (n + 1) ^ 8 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 10)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 9)) (Mir.mul (Mir.cst 45)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 8))) (Mir.mul (Mir.cst 60)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 7))) (Mir.mul (Mir.cst 20)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 3))) (Mir.add (Mir.mul (Mir.cst
    42) (Mir.pow Mir.x 5)) (Mir.mul (Mir.cst 3) Mir.x))) (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 9))
    (Mir.mul (Mir.cst 45) (Mir.pow Mir.x 8))) (Mir.mul (Mir.cst 60)
    (Mir.pow Mir.x 7))) (Mir.mul (Mir.cst 20) (Mir.pow Mir.x 3))) (Mir.add
    (Mir.mul (Mir.cst 42) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 5))
    (Mir.mul (Mir.cst 3) (Mir.add Mir.x (Mir.cst 1))))) (Mir.mul (Mir.cst
    90) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 8))) (by decide +kernel)

/-- The power sum's step identity at the key 9. -/
private theorem powStep9 (n : Nat) :
    2 * (n + 1) ^ 10 + 10 * (n + 1) ^ 9 + 15 * (n + 1) ^ 8 + 10 * (n + 1)
      ^ 4 + (14 * n ^ 6 + 3 * n ^ 2)
      = 2 * n ^ 10 + 10 * n ^ 9 + 15 * n ^ 8 + 10 * n ^ 4 + (14 * (n + 1)
        ^ 6 + 3 * (n + 1) ^ 2) + 20 * (n + 1) ^ 9 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 2)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 10)) (Mir.mul (Mir.cst 10)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 9))) (Mir.mul (Mir.cst 15)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 8))) (Mir.mul (Mir.cst 10)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 4))) (Mir.add (Mir.mul (Mir.cst
    14) (Mir.pow Mir.x 6)) (Mir.mul (Mir.cst 3) (Mir.pow Mir.x 2))))
    (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 2)
    (Mir.pow Mir.x 10)) (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 9))) (Mir.mul
    (Mir.cst 15) (Mir.pow Mir.x 8))) (Mir.mul (Mir.cst 10) (Mir.pow Mir.x
    4))) (Mir.add (Mir.mul (Mir.cst 14) (Mir.pow (Mir.add Mir.x (Mir.cst
    1)) 6)) (Mir.mul (Mir.cst 3) (Mir.pow (Mir.add Mir.x (Mir.cst 1))
    2)))) (Mir.mul (Mir.cst 20) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 9)))
    (by decide +kernel)

/-- The power sum's step identity at the key 10. -/
private theorem powStep10 (n : Nat) :
    6 * (n + 1) ^ 11 + 33 * (n + 1) ^ 10 + 55 * (n + 1) ^ 9 + 66 * (n + 1)
      ^ 5 + 5 * (n + 1) + (66 * n ^ 7 + 33 * n ^ 3)
      = 6 * n ^ 11 + 33 * n ^ 10 + 55 * n ^ 9 + 66 * n ^ 5 + 5 * n + (66 *
        (n + 1) ^ 7 + 33 * (n + 1) ^ 3) + 66 * (n + 1) ^ 10 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst
    6) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 11)) (Mir.mul (Mir.cst 33)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 10))) (Mir.mul (Mir.cst 55)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 9))) (Mir.mul (Mir.cst 66)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 5))) (Mir.mul (Mir.cst 5)
    (Mir.add Mir.x (Mir.cst 1)))) (Mir.add (Mir.mul (Mir.cst 66) (Mir.pow
    Mir.x 7)) (Mir.mul (Mir.cst 33) (Mir.pow Mir.x 3)))) (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow
    Mir.x 11)) (Mir.mul (Mir.cst 33) (Mir.pow Mir.x 10))) (Mir.mul
    (Mir.cst 55) (Mir.pow Mir.x 9))) (Mir.mul (Mir.cst 66) (Mir.pow Mir.x
    5))) (Mir.mul (Mir.cst 5) Mir.x)) (Mir.add (Mir.mul (Mir.cst 66)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 7)) (Mir.mul (Mir.cst 33)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 3)))) (Mir.mul (Mir.cst 66)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 10))) (by decide +kernel)

/-- The vacant key's power sum is the endpoint's own count. -/
theorem powSum0_closed : ∀ n : Nat, powSum 0 n = n
  | 0 => rfl
  | n + 1 => by
    rw [powSum_succ 0 n, powSum0_closed n, Nat.pow_zero]

/-- The power sum's closed read at the key 1, cross-added. -/
theorem powSum1_closed (n : Nat) :
    2 * powSum 1 n
      = n ^ 2 + n :=
  sumClosed 1 2 (fun _ => 0) (fun n => n ^ 2 + n) rfl powStep1 n

/-- The power sum's closed read at the key 2, cross-added. -/
theorem powSum2_closed (n : Nat) :
    6 * powSum 2 n
      = 2 * n ^ 3 + 3 * n ^ 2 + n :=
  sumClosed 2 6 (fun _ => 0) (fun n => 2 * n ^ 3 + 3 * n ^ 2 + n) rfl
    powStep2 n

/-- The power sum's closed read at the key 3, cross-added. -/
theorem powSum3_closed (n : Nat) :
    4 * powSum 3 n
      = n ^ 4 + 2 * n ^ 3 + n ^ 2 :=
  sumClosed 3 4 (fun _ => 0) (fun n => n ^ 4 + 2 * n ^ 3 + n ^ 2) rfl
    powStep3 n

/-- The power sum's closed read at the key 4, cross-added. -/
theorem powSum4_closed (n : Nat) :
    30 * powSum 4 n + n
      = 6 * n ^ 5 + 15 * n ^ 4 + 10 * n ^ 3 :=
  sumClosed 4 30 (fun n => n) (fun n => 6 * n ^ 5 + 15 * n ^ 4 + 10 * n ^
    3) rfl powStep4 n

/-- The power sum's closed read at the key 5, cross-added. -/
theorem powSum5_closed (n : Nat) :
    12 * powSum 5 n + n ^ 2
      = 2 * n ^ 6 + 6 * n ^ 5 + 5 * n ^ 4 :=
  sumClosed 5 12 (fun n => n ^ 2) (fun n => 2 * n ^ 6 + 6 * n ^ 5 + 5 * n
    ^ 4) rfl powStep5 n

/-- The power sum's closed read at the key 6, cross-added. -/
theorem powSum6_closed (n : Nat) :
    42 * powSum 6 n + 7 * n ^ 3
      = 6 * n ^ 7 + 21 * n ^ 6 + 21 * n ^ 5 + n :=
  sumClosed 6 42 (fun n => 7 * n ^ 3) (fun n => 6 * n ^ 7 + 21 * n ^ 6 +
    21 * n ^ 5 + n) rfl powStep6 n

/-- The power sum's closed read at the key 7, cross-added. -/
theorem powSum7_closed (n : Nat) :
    24 * powSum 7 n + 7 * n ^ 4
      = 3 * n ^ 8 + 12 * n ^ 7 + 14 * n ^ 6 + 2 * n ^ 2 :=
  sumClosed 7 24 (fun n => 7 * n ^ 4) (fun n => 3 * n ^ 8 + 12 * n ^ 7 +
    14 * n ^ 6 + 2 * n ^ 2) rfl powStep7 n

/-- The power sum's closed read at the key 8, cross-added. -/
theorem powSum8_closed (n : Nat) :
    90 * powSum 8 n + 42 * n ^ 5 + 3 * n
      = 10 * n ^ 9 + 45 * n ^ 8 + 60 * n ^ 7 + 20 * n ^ 3 :=
  by
  rw [Nat.add_assoc (90 * powSum 8 n) (42 * n ^ 5) (3 * n)]
  exact
    sumClosed 8 90 (fun n => 42 * n ^ 5 + 3 * n) (fun n => 10 * n ^ 9 + 45
      * n ^ 8 + 60 * n ^ 7 + 20 * n ^ 3) rfl powStep8 n

/-- The power sum's closed read at the key 9, cross-added. -/
theorem powSum9_closed (n : Nat) :
    20 * powSum 9 n + 14 * n ^ 6 + 3 * n ^ 2
      = 2 * n ^ 10 + 10 * n ^ 9 + 15 * n ^ 8 + 10 * n ^ 4 :=
  by
  rw [Nat.add_assoc (20 * powSum 9 n) (14 * n ^ 6) (3 * n ^ 2)]
  exact
    sumClosed 9 20 (fun n => 14 * n ^ 6 + 3 * n ^ 2) (fun n => 2 * n ^ 10
      + 10 * n ^ 9 + 15 * n ^ 8 + 10 * n ^ 4) rfl powStep9 n

/-- The power sum's closed read at the key 10, cross-added. -/
theorem powSum10_closed (n : Nat) :
    66 * powSum 10 n + 66 * n ^ 7 + 33 * n ^ 3
      = 6 * n ^ 11 + 33 * n ^ 10 + 55 * n ^ 9 + 66 * n ^ 5 + 5 * n :=
  by
  rw [Nat.add_assoc (66 * powSum 10 n) (66 * n ^ 7) (33 * n ^ 3)]
  exact
    sumClosed 10 66 (fun n => 66 * n ^ 7 + 33 * n ^ 3) (fun n => 6 * n ^
      11 + 33 * n ^ 10 + 55 * n ^ 9 + 66 * n ^ 5 + 5 * n) rfl powStep10 n

/-- The square at the product's own reading. -/
private theorem sqRead (a : Nat) :
    a ^ 2
      = a * a :=
  mirEq a 0 (Mir.pow Mir.x 2) (Mir.mul Mir.x Mir.x) (by decide +kernel)

/-- The fourth power at the square's own square. -/
private theorem quadRead (a : Nat) :
    a ^ 4
      = a * a * (a * a) :=
  mirEq a 0 (Mir.pow Mir.x 4) (Mir.mul (Mir.mul Mir.x Mir.x) (Mir.mul
    Mir.x Mir.x)) (by decide +kernel)

/-- A product's square at the factors' squares. -/
private theorem mulSq (a b : Nat) :
    (a * b) ^ 2
      = a ^ 2 * b ^ 2 :=
  mirEq a b (Mir.pow (Mir.mul Mir.x Mir.y) 2) (Mir.mul (Mir.pow Mir.x 2)
    (Mir.pow Mir.y 2)) (by decide +kernel)

/-- The doubled product at its two orders. -/
private theorem twoMul (a b : Nat) :
    2 * a * b
      = a * b + b * a :=
  mirEq a b (Mir.mul (Mir.mul (Mir.cst 2) Mir.x) Mir.y) (Mir.add (Mir.mul
    Mir.x Mir.y) (Mir.mul Mir.y Mir.x)) (by decide +kernel)

/-- The gap's square against the shifted pair's crossed product. -/
private theorem margShiftSq (b d : Nat) :
    d ^ 2 + 2 * (b + d) * b
      = (b + d) * (b + d) + b * b :=
  mirEq b d (Mir.add (Mir.pow Mir.y 2) (Mir.mul (Mir.mul (Mir.cst 2)
    (Mir.add Mir.x Mir.y)) Mir.x)) (Mir.add (Mir.mul (Mir.add Mir.x Mir.y)
    (Mir.add Mir.x Mir.y)) (Mir.mul Mir.x Mir.x)) (by decide +kernel)

/-- The family's square at a depth, in the depth and the gap. -/
private theorem sqTerm0 (m g : Nat) :
    (m * m * g) ^ 2 + 2 * (m * m + g) * m ^ 6
      = (m * m + g) * (m * m + g) * m ^ 4 + m ^ 8 :=
  mirEq m g (Mir.add (Mir.pow (Mir.mul (Mir.mul Mir.x Mir.x) Mir.y) 2)
    (Mir.mul (Mir.mul (Mir.cst 2) (Mir.add (Mir.mul Mir.x Mir.x) Mir.y))
    (Mir.pow Mir.x 6))) (Mir.add (Mir.mul (Mir.mul (Mir.add (Mir.mul Mir.x
    Mir.x) Mir.y) (Mir.add (Mir.mul Mir.x Mir.x) Mir.y)) (Mir.pow Mir.x
    4)) (Mir.pow Mir.x 8)) (by decide +kernel)

/-- The well's linear part at a depth, in the depth and the gap. -/
private theorem sqTerm1 (m g : Nat) :
    m * (m * m * g) ^ 2 + 2 * (m * m + g) * m ^ 7
      = (m * m + g) * (m * m + g) * m ^ 5 + m ^ 9 :=
  mirEq m g (Mir.add (Mir.mul Mir.x (Mir.pow (Mir.mul (Mir.mul Mir.x
    Mir.x) Mir.y) 2)) (Mir.mul (Mir.mul (Mir.cst 2) (Mir.add (Mir.mul
    Mir.x Mir.x) Mir.y)) (Mir.pow Mir.x 7))) (Mir.add (Mir.mul (Mir.mul
    (Mir.add (Mir.mul Mir.x Mir.x) Mir.y) (Mir.add (Mir.mul Mir.x Mir.x)
    Mir.y)) (Mir.pow Mir.x 5)) (Mir.pow Mir.x 9)) (by decide +kernel)

/-- The well's square part at a depth, in the depth and the gap. -/
private theorem sqTerm2 (m g : Nat) :
    m * m * (m * m * g) ^ 2 + 2 * (m * m + g) * m ^ 8
      = (m * m + g) * (m * m + g) * m ^ 6 + m ^ 10 :=
  mirEq m g (Mir.add (Mir.mul (Mir.mul Mir.x Mir.x) (Mir.pow (Mir.mul
    (Mir.mul Mir.x Mir.x) Mir.y) 2)) (Mir.mul (Mir.mul (Mir.cst 2)
    (Mir.add (Mir.mul Mir.x Mir.x) Mir.y)) (Mir.pow Mir.x 8))) (Mir.add
    (Mir.mul (Mir.mul (Mir.add (Mir.mul Mir.x Mir.x) Mir.y) (Mir.add
    (Mir.mul Mir.x Mir.x) Mir.y)) (Mir.pow Mir.x 6)) (Mir.pow Mir.x 10))
    (by decide +kernel)

/-- The bond square's per-depth read at the balance pair's own square, in
  the depth and the scale's square. -/
private theorem diffCore (m X : Nat) :
    (2 * m + 1) ^ 2 * (X * X + (2 * m * m + 2 * m + 1) * (2 * m * m + 2 *
      m + 1)) + 2 * X * m ^ 0 + 12 * X * m ^ 1 + 28 * X * m ^ 2 + 32 * X *
      m ^ 3 + 16 * X * m ^ 4
      = m ^ 0 + X * X * m ^ 0 + 8 * m ^ 1 + 4 * (X * X) * m ^ 1 + 28 * m ^
        2 + 4 * (X * X) * m ^ 2 + 56 * m ^ 3 + 68 * m ^ 4 + 48 * m ^ 5 +
        16 * m ^ 6 + (2 * m + 1) ^ 2 * (2 * X * (2 * m * m + 2 * m + 1)) :=
  mirEq m X (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.pow
    (Mir.add (Mir.mul (Mir.cst 2) Mir.x) (Mir.cst 1)) 2) (Mir.add (Mir.mul
    Mir.y Mir.y) (Mir.mul (Mir.add (Mir.add (Mir.mul (Mir.mul (Mir.cst 2)
    Mir.x) Mir.x) (Mir.mul (Mir.cst 2) Mir.x)) (Mir.cst 1)) (Mir.add
    (Mir.add (Mir.mul (Mir.mul (Mir.cst 2) Mir.x) Mir.x) (Mir.mul (Mir.cst
    2) Mir.x)) (Mir.cst 1))))) (Mir.mul (Mir.mul (Mir.cst 2) Mir.y)
    (Mir.pow Mir.x 0))) (Mir.mul (Mir.mul (Mir.cst 12) Mir.y) (Mir.pow
    Mir.x 1))) (Mir.mul (Mir.mul (Mir.cst 28) Mir.y) (Mir.pow Mir.x 2)))
    (Mir.mul (Mir.mul (Mir.cst 32) Mir.y) (Mir.pow Mir.x 3))) (Mir.mul
    (Mir.mul (Mir.cst 16) Mir.y) (Mir.pow Mir.x 4))) (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.pow Mir.x 0) (Mir.mul (Mir.mul Mir.y Mir.y) (Mir.pow
    Mir.x 0))) (Mir.mul (Mir.cst 8) (Mir.pow Mir.x 1))) (Mir.mul (Mir.mul
    (Mir.cst 4) (Mir.mul Mir.y Mir.y)) (Mir.pow Mir.x 1))) (Mir.mul
    (Mir.cst 28) (Mir.pow Mir.x 2))) (Mir.mul (Mir.mul (Mir.cst 4)
    (Mir.mul Mir.y Mir.y)) (Mir.pow Mir.x 2))) (Mir.mul (Mir.cst 56)
    (Mir.pow Mir.x 3))) (Mir.mul (Mir.cst 68) (Mir.pow Mir.x 4))) (Mir.mul
    (Mir.cst 48) (Mir.pow Mir.x 5))) (Mir.mul (Mir.cst 16) (Mir.pow Mir.x
    6))) (Mir.mul (Mir.pow (Mir.add (Mir.mul (Mir.cst 2) Mir.x) (Mir.cst
    1)) 2) (Mir.mul (Mir.mul (Mir.cst 2) Mir.y) (Mir.add (Mir.add (Mir.mul
    (Mir.mul (Mir.cst 2) Mir.x) Mir.x) (Mir.mul (Mir.cst 2) Mir.x))
    (Mir.cst 1))))) (by decide +kernel)

/-- The margin at a shifted first datum is the shift. -/
private theorem margShift (b d : Nat) : marg (b + d) b = d := by
  show b + d - b + (b - (b + d)) = d
  rw [ground.addSubSelfL b d, ground.subLe b (b + d) (Nat.le_add_right b d),
    Nat.add_zero d]

/-- The margin reads one value at either order. -/
private theorem margComm (a b : Nat) : marg a b = marg b a :=
  Nat.add_comm (a - b) (b - a)

/-- The margin's square against the doubled product reads the two
squares, the trichotomy's one identity. -/
private theorem margSqNat (a b : Nat) :
    marg a b ^ 2 + 2 * a * b = a * a + b * b := by
  match Nat.le_total b a with
  | Or.inl h =>
    have hd : b + (a - b) = a :=
      (Nat.add_comm b (a - b)).trans (ground.subAdd h)
    have key : marg (b + (a - b)) b ^ 2 + 2 * (b + (a - b)) * b
        = (b + (a - b)) * (b + (a - b)) + b * b := by
      rw [margShift b (a - b)]
      exact margShiftSq b (a - b)
    rw [hd] at key
    exact key
  | Or.inr h =>
    have hd : a + (b - a) = b :=
      (Nat.add_comm a (b - a)).trans (ground.subAdd h)
    have key : marg (a + (b - a)) a ^ 2 + 2 * (a + (b - a)) * a
        = (a + (b - a)) * (a + (b - a)) + a * a := by
      rw [margShift a (b - a)]
      exact margShiftSq a (b - a)
    rw [hd] at key
    rw [margComm a b, ground.mulRightComm 2 a b, Nat.add_comm (a * a) (b *
      b)]
    exact key

/-- The count pair's square: the two squares against the doubled
crossed product. -/
private theorem ofCounts_sq (a b : Nat) :
    (BPair.ofCounts a b * BPair.ofCounts a b).oneValue
      (BPair.ofCounts (a * a + b * b) (a * b + b * a)) := by
  refine BPair.oneValue_symm ?_
  show (BPair.ofNat (a * a + b * b)
      + (BPair.ofNat (a * b + b * a)).swap).oneValue
    ((BPair.ofNat a + (BPair.ofNat b).swap)
      * (BPair.ofNat a + (BPair.ofNat b).swap))
  rw [BPair.sq_expand_swap (BPair.ofNat a) (BPair.ofNat b)]
  refine BPair.add_congr ?_ ?_
  · exact BPair.oneValue_trans (BPair.ofNat_add (a * a) (b * b))
      (BPair.add_congr (BPair.ofNat_mul a a) (BPair.ofNat_mul b b))
  · refine BPair.oneValue_trans
      (ground.swap_congr (BPair.ofNat_add (a * b) (b * a))) ?_
    rw [← BPair.swap_add (BPair.ofNat (a * b)) (BPair.ofNat (b * a))]
    exact BPair.add_congr (ground.swap_congr (BPair.ofNat_mul a b))
      (ground.swap_congr
        (BPair.oneValue_trans (BPair.ofNat_mul b a)
          (BPair.oneValue_of_eq
            (BPair.mul_comm (BPair.ofNat b) (BPair.ofNat a)))))

/-- The margin's square is the balance pair's own square read, the
trichotomy's one generic lemma. -/
theorem margSq_read (a b : Nat) :
    (BPair.ofNat (marg a b ^ 2)).oneValue
      (BPair.ofCounts a b * BPair.ofCounts a b) := by
  have h0 : (BPair.ofNat (marg a b ^ 2)).oneValue
      (BPair.ofCounts (marg a b ^ 2) 0) :=
    BPair.oneValue_symm (BPair.add_unit (BPair.ofNat (marg a b ^ 2)))
  refine BPair.oneValue_trans h0 ?_
  refine BPair.oneValue_trans (BPair.ofCounts_crossed ?_)
    (BPair.oneValue_symm (ofCounts_sq a b))
  rw [← twoMul a b, Nat.add_zero (a * a + b * b)]
  exact margSqNat a b

/-- The seeded sum moves its last summand past an arriving one, at
five standing summands. -/
private theorem addShiftFive (t c a0 a1 a2 a3 a4 : Nat) :
    t + a0 + a1 + a2 + a3 + a4 + c = t + c + a0 + a1 + a2 + a3 + a4 := by
  rw [Nat.add_right_comm (t + a0 + a1 + a2 + a3) a4 c,
    Nat.add_right_comm (t + a0 + a1 + a2) a3 c,
    Nat.add_right_comm (t + a0 + a1) a2 c,
    Nat.add_right_comm (t + a0) a1 c,
    Nat.add_right_comm t a0 c]

private theorem powSum_read (k n : Nat) :
    powSum k n = ground.sumNat ((List.range n).map (fun j => (j + 1) ^ k))
      :=
  rfl

private theorem witSq_read (N : Nat) :
    witSq N
      = ground.sumNat ((List.range N).map (fun k => witVal N (k + 1) ^ 2))
        :=
  rfl

private theorem witSqM_read (N : Nat) :
    witSqM N = ground.sumNat ((List.range N).map
      (fun k => (k + 1) * witVal N (k + 1) ^ 2)) :=
  rfl

private theorem witSqMM_read (N : Nat) :
    witSqMM N = ground.sumNat ((List.range N).map
      (fun k => (k + 1) * (k + 1) * witVal N (k + 1) ^ 2)) :=
  rfl

private theorem witDiffSq_read (N : Nat) :
    witDiffSq N = ground.sumNat ((List.range (N - 1)).map (fun k =>
      ((2 * (k + 1) + 1) * marg (N * N)
        (2 * (k + 1) * (k + 1) + 2 * (k + 1) + 1)) ^ 2)) :=
  rfl

/-- The family's square at a depth inside the endpoint: the gap
witness carries the depth's read. -/
private theorem witSqTerm (N m : Nat) (h : m * m ≤ N * N) :
    witVal N m ^ 2 + 2 * N ^ 2 * m ^ 6 = N ^ 4 * m ^ 4 + m ^ 8 := by
  have hg : m * m + (N * N - m * m) = N * N :=
    (Nat.add_comm (m * m) (N * N - m * m)).trans (ground.subAdd h)
  have key := sqTerm0 m (N * N - m * m)
  rw [hg] at key
  show (m * m * (N * N - m * m)) ^ 2 + 2 * N ^ 2 * m ^ 6
    = N ^ 4 * m ^ 4 + m ^ 8
  rw [sqRead N, quadRead N]
  exact key

/-- The well's linear part at a depth inside the endpoint. -/
private theorem witSqMTerm (N m : Nat) (h : m * m ≤ N * N) :
    m * witVal N m ^ 2 + 2 * N ^ 2 * m ^ 7 = N ^ 4 * m ^ 5 + m ^ 9 := by
  have hg : m * m + (N * N - m * m) = N * N :=
    (Nat.add_comm (m * m) (N * N - m * m)).trans (ground.subAdd h)
  have key := sqTerm1 m (N * N - m * m)
  rw [hg] at key
  show m * (m * m * (N * N - m * m)) ^ 2 + 2 * N ^ 2 * m ^ 7
    = N ^ 4 * m ^ 5 + m ^ 9
  rw [sqRead N, quadRead N]
  exact key

/-- The well's square part at a depth inside the endpoint. -/
private theorem witSqMMTerm (N m : Nat) (h : m * m ≤ N * N) :
    m * m * witVal N m ^ 2 + 2 * N ^ 2 * m ^ 8
      = N ^ 4 * m ^ 6 + m ^ 10 := by
  have hg : m * m + (N * N - m * m) = N * N :=
    (Nat.add_comm (m * m) (N * N - m * m)).trans (ground.subAdd h)
  have key := sqTerm2 m (N * N - m * m)
  rw [hg] at key
  show m * m * (m * m * (N * N - m * m)) ^ 2 + 2 * N ^ 2 * m ^ 8
    = N ^ 4 * m ^ 6 + m ^ 10
  rw [sqRead N, quadRead N]
  exact key

/-- The bond square at a depth: the margin's own square read against
the balance pair's, the depth's powers cross-added. -/
private theorem witDiffTerm (N m : Nat) :
    ((2 * m + 1) * marg (N * N) (2 * m * m + 2 * m + 1)) ^ 2
        + 2 * N ^ 2 * m ^ 0 + 12 * N ^ 2 * m ^ 1 + 28 * N ^ 2 * m ^ 2
        + 32 * N ^ 2 * m ^ 3 + 16 * N ^ 2 * m ^ 4
      = m ^ 0 + N ^ 4 * m ^ 0 + 8 * m ^ 1 + 4 * N ^ 4 * m ^ 1
        + 28 * m ^ 2 + 4 * N ^ 4 * m ^ 2 + 56 * m ^ 3 + 68 * m ^ 4
        + 48 * m ^ 5 + 16 * m ^ 6 := by
  have hkey : ((2 * m + 1) * marg (N * N) (2 * m * m + 2 * m + 1)) ^ 2
      + (2 * m + 1) ^ 2 * (2 * (N * N) * (2 * m * m + 2 * m + 1))
      = (2 * m + 1) ^ 2
        * (N * N * (N * N)
          + (2 * m * m + 2 * m + 1) * (2 * m * m + 2 * m + 1)) := by
    rw [mulSq (2 * m + 1) (marg (N * N) (2 * m * m + 2 * m + 1)),
      ← Nat.left_distrib ((2 * m + 1) ^ 2)
        (marg (N * N) (2 * m * m + 2 * m + 1) ^ 2)
        (2 * (N * N) * (2 * m * m + 2 * m + 1)),
      margSqNat (N * N) (2 * m * m + 2 * m + 1)]
  rw [sqRead N, quadRead N]
  refine ground.addCancelR
    ((2 * m + 1) ^ 2 * (2 * (N * N) * (2 * m * m + 2 * m + 1))) ?_
  rw [addShiftFive
      (((2 * m + 1) * marg (N * N) (2 * m * m + 2 * m + 1)) ^ 2)
      ((2 * m + 1) ^ 2 * (2 * (N * N) * (2 * m * m + 2 * m + 1)))
      (2 * (N * N) * m ^ 0) (12 * (N * N) * m ^ 1)
      (28 * (N * N) * m ^ 2) (32 * (N * N) * m ^ 3)
      (16 * (N * N) * m ^ 4),
    hkey]
  exact diffCore m (N * N)

/-- The bridge from the family's square to the power sums, the
per-depth decomposition folded. -/
theorem witSq_bridge (N : Nat) :
    witSq N + 2 * N ^ 2 * powSum 6 N
      = N ^ 4 * powSum 4 N + powSum 8 N := by
  rw [witSq_read N, powSum_read 6 N, powSum_read 4 N, powSum_read 8 N,
    sumNat_scale (2 * N ^ 2) (fun j => (j + 1) ^ 6) (List.range N),
    sumNat_scale (N ^ 4) (fun j => (j + 1) ^ 4) (List.range N),
    ← ground.sumNat_map_add (fun k => witVal N (k + 1) ^ 2)
      (fun j => 2 * N ^ 2 * (j + 1) ^ 6) (List.range N),
    ← ground.sumNat_map_add (fun j => N ^ 4 * (j + 1) ^ 4)
      (fun j => (j + 1) ^ 8) (List.range N),
    ground.sumMap, ground.sumMap]
  exact ground.famFold_congr_range _ _ N (fun i hi =>
    witSqTerm N (i + 1) (Nat.mul_le_mul hi hi))

/-- The bridge from the well's linear part to the power sums. -/
theorem witSqM_bridge (N : Nat) :
    witSqM N + 2 * N ^ 2 * powSum 7 N
      = N ^ 4 * powSum 5 N + powSum 9 N := by
  rw [witSqM_read N, powSum_read 7 N, powSum_read 5 N, powSum_read 9 N,
    sumNat_scale (2 * N ^ 2) (fun j => (j + 1) ^ 7) (List.range N),
    sumNat_scale (N ^ 4) (fun j => (j + 1) ^ 5) (List.range N),
    ← ground.sumNat_map_add (fun k => (k + 1) * witVal N (k + 1) ^ 2)
      (fun j => 2 * N ^ 2 * (j + 1) ^ 7) (List.range N),
    ← ground.sumNat_map_add (fun j => N ^ 4 * (j + 1) ^ 5)
      (fun j => (j + 1) ^ 9) (List.range N),
    ground.sumMap, ground.sumMap]
  exact ground.famFold_congr_range _ _ N (fun i hi =>
    witSqMTerm N (i + 1) (Nat.mul_le_mul hi hi))

/-- The bridge from the well's square part to the power sums. -/
theorem witSqMM_bridge (N : Nat) :
    witSqMM N + 2 * N ^ 2 * powSum 8 N
      = N ^ 4 * powSum 6 N + powSum 10 N := by
  rw [witSqMM_read N, powSum_read 8 N, powSum_read 6 N, powSum_read 10 N,
    sumNat_scale (2 * N ^ 2) (fun j => (j + 1) ^ 8) (List.range N),
    sumNat_scale (N ^ 4) (fun j => (j + 1) ^ 6) (List.range N),
    ← ground.sumNat_map_add
      (fun k => (k + 1) * (k + 1) * witVal N (k + 1) ^ 2)
      (fun j => 2 * N ^ 2 * (j + 1) ^ 8) (List.range N),
    ← ground.sumNat_map_add (fun j => N ^ 4 * (j + 1) ^ 6)
      (fun j => (j + 1) ^ 10) (List.range N),
    ground.sumMap, ground.sumMap]
  exact ground.famFold_congr_range _ _ N (fun i hi =>
    witSqMMTerm N (i + 1) (Nat.mul_le_mul hi hi))

/-- The bridge from the difference sum to the power sums below the
endpoint, the bond square's per-depth read folded. -/
theorem witDiffSq_bridge (N : Nat) :
    witDiffSq N + 2 * N ^ 2 * powSum 0 (N - 1)
        + 12 * N ^ 2 * powSum 1 (N - 1) + 28 * N ^ 2 * powSum 2 (N - 1)
        + 32 * N ^ 2 * powSum 3 (N - 1) + 16 * N ^ 2 * powSum 4 (N - 1)
      = powSum 0 (N - 1) + N ^ 4 * powSum 0 (N - 1)
        + 8 * powSum 1 (N - 1) + 4 * N ^ 4 * powSum 1 (N - 1)
        + 28 * powSum 2 (N - 1) + 4 * N ^ 4 * powSum 2 (N - 1)
        + 56 * powSum 3 (N - 1) + 68 * powSum 4 (N - 1)
        + 48 * powSum 5 (N - 1) + 16 * powSum 6 (N - 1) := by
  rw [witDiffSq_read N, powSum_read 0 (N - 1), powSum_read 1 (N - 1),
    powSum_read 2 (N - 1), powSum_read 3 (N - 1), powSum_read 4 (N - 1),
    powSum_read 5 (N - 1), powSum_read 6 (N - 1),
    sumNat_scale (2 * N ^ 2) (fun j => (j + 1) ^ 0) (List.range (N - 1)),
    sumNat_scale (12 * N ^ 2) (fun j => (j + 1) ^ 1) (List.range (N - 1)),
    sumNat_scale (28 * N ^ 2) (fun j => (j + 1) ^ 2) (List.range (N - 1)),
    sumNat_scale (32 * N ^ 2) (fun j => (j + 1) ^ 3) (List.range (N - 1)),
    sumNat_scale (16 * N ^ 2) (fun j => (j + 1) ^ 4) (List.range (N - 1)),
    sumNat_scale (N ^ 4) (fun j => (j + 1) ^ 0) (List.range (N - 1)),
    sumNat_scale 8 (fun j => (j + 1) ^ 1) (List.range (N - 1)),
    sumNat_scale (4 * N ^ 4) (fun j => (j + 1) ^ 1) (List.range (N - 1)),
    sumNat_scale 28 (fun j => (j + 1) ^ 2) (List.range (N - 1)),
    sumNat_scale (4 * N ^ 4) (fun j => (j + 1) ^ 2) (List.range (N - 1)),
    sumNat_scale 56 (fun j => (j + 1) ^ 3) (List.range (N - 1)),
    sumNat_scale 68 (fun j => (j + 1) ^ 4) (List.range (N - 1)),
    sumNat_scale 48 (fun j => (j + 1) ^ 5) (List.range (N - 1)),
    sumNat_scale 16 (fun j => (j + 1) ^ 6) (List.range (N - 1)),
    ← ground.sumNat_map_add, ← ground.sumNat_map_add,
    ← ground.sumNat_map_add, ← ground.sumNat_map_add,
    ← ground.sumNat_map_add, ← ground.sumNat_map_add,
    ← ground.sumNat_map_add, ← ground.sumNat_map_add,
    ← ground.sumNat_map_add, ← ground.sumNat_map_add,
    ← ground.sumNat_map_add, ← ground.sumNat_map_add,
    ← ground.sumNat_map_add, ← ground.sumNat_map_add,
    ground.sumMap, ground.sumMap]
  exact ground.famFold_congr_range _ _ (N - 1)
    (fun i _ => witDiffTerm N (i + 1))

/-- The four-factor product's head regroup at a scalar. -/
private theorem mulRegroup (c a b x : Nat) :
    c * (a * b * x) = c * a * b * x := by
  rw [ground.mulAssoc (c * a) b x, ground.mulAssoc c a (b * x),
    ground.mulAssoc a b x]

/-- The four-factor product's exchange at a scaled second factor. -/
private theorem mulRegroup4 (c b a x : Nat) :
    c * b * (a * x) = c * a * b * x := by
  rw [← ground.mulAssoc (c * b) a x, ground.mulRightComm c b a]

/-- A cleared read scales through its multiplier. -/
private theorem scaleRead {a S L R : Nat} (h : a * S + L = R) (c : Nat) :
    c * (a * S) + c * L = c * R := by
  rw [← Nat.left_distrib c (a * S) L, h]

/-- Two equations at matched sides join at the balanced additions. -/
private theorem balancedAdd {A B C D : Nat} (h : A + B = C + D)
    (p r s : Nat) : A + (B + p) + (r + s) = C + r + (D + s) + p := by
  rw [← Nat.add_assoc A B p, ← Nat.add_assoc (A + B + p) r s, h,
    ← Nat.add_assoc (C + r) D s,
    Nat.add_right_comm (C + D) p r,
    Nat.add_right_comm (C + D + r) p s,
    Nat.add_right_comm C D r]

/-- An equation rides a stated scalar. -/
private theorem mulEq (c : Nat) {a b : Nat} (h : a = b) : c * a = c * b :=
  by
  rw [h]

/-- An equation rides a stated summand. -/
private theorem addEq (c : Nat) {a b : Nat} (h : a = b) : a + c = b + c :=
  by
  rw [h]

/-- The square closed read's left side at the balanced additions. -/
private theorem sqClosedLeft (N W : Nat) :
    630 * W + 105 * N ^ 5 + 21 * N + (30 * N ^ 2 * (6 * N ^ 7 + 21 * N ^ 6
      + 21 * N ^ 5 + N) + 210 * N ^ 5)
      = 630 * W + 30 * N ^ 2 * (6 * N ^ 7 + 21 * N ^ 6 + 21 * N ^ 5 + N) +
        (21 * N ^ 5 + (294 * N ^ 5 + 21 * N)) :=
  mirEq N W (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 630) Mir.y)
    (Mir.mul (Mir.cst 105) (Mir.pow Mir.x 5))) (Mir.mul (Mir.cst 21)
    Mir.x)) (Mir.add (Mir.mul (Mir.mul (Mir.cst 30) (Mir.pow Mir.x 2))
    (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 7))
    (Mir.mul (Mir.cst 21) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst 21)
    (Mir.pow Mir.x 5))) Mir.x)) (Mir.mul (Mir.cst 210) (Mir.pow Mir.x
    5)))) (Mir.add (Mir.add (Mir.mul (Mir.cst 630) Mir.y) (Mir.mul
    (Mir.mul (Mir.cst 30) (Mir.pow Mir.x 2)) (Mir.add (Mir.add (Mir.add
    (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 7)) (Mir.mul (Mir.cst 21) (Mir.pow
    Mir.x 6))) (Mir.mul (Mir.cst 21) (Mir.pow Mir.x 5))) Mir.x))) (Mir.add
    (Mir.mul (Mir.cst 21) (Mir.pow Mir.x 5)) (Mir.add (Mir.mul (Mir.cst
    294) (Mir.pow Mir.x 5)) (Mir.mul (Mir.cst 21) Mir.x)))) (by decide +kernel)

/-- The square closed read's right side at the balanced additions. -/
private theorem sqClosedRight (N : Nat) :
    16 * N ^ 9 + 110 * N ^ 3 + (30 * N ^ 2 * (6 * N ^ 7 + 21 * N ^ 6 + 21
      * N ^ 5 + N) + 210 * N ^ 5)
      = 21 * N ^ 4 * (6 * N ^ 5 + 15 * N ^ 4 + 10 * N ^ 3) + 7 * (10 * N ^
        9 + 45 * N ^ 8 + 60 * N ^ 7 + 20 * N ^ 3) + 210 * N ^ 5 :=
  mirEq N 0 (Mir.add (Mir.add (Mir.mul (Mir.cst 16) (Mir.pow Mir.x 9))
    (Mir.mul (Mir.cst 110) (Mir.pow Mir.x 3))) (Mir.add (Mir.mul (Mir.mul
    (Mir.cst 30) (Mir.pow Mir.x 2)) (Mir.add (Mir.add (Mir.add (Mir.mul
    (Mir.cst 6) (Mir.pow Mir.x 7)) (Mir.mul (Mir.cst 21) (Mir.pow Mir.x
    6))) (Mir.mul (Mir.cst 21) (Mir.pow Mir.x 5))) Mir.x)) (Mir.mul
    (Mir.cst 210) (Mir.pow Mir.x 5)))) (Mir.add (Mir.add (Mir.mul (Mir.mul
    (Mir.cst 21) (Mir.pow Mir.x 4)) (Mir.add (Mir.add (Mir.mul (Mir.cst 6)
    (Mir.pow Mir.x 5)) (Mir.mul (Mir.cst 15) (Mir.pow Mir.x 4))) (Mir.mul
    (Mir.cst 10) (Mir.pow Mir.x 3)))) (Mir.mul (Mir.cst 7) (Mir.add
    (Mir.add (Mir.add (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 9)) (Mir.mul
    (Mir.cst 45) (Mir.pow Mir.x 8))) (Mir.mul (Mir.cst 60) (Mir.pow Mir.x
    7))) (Mir.mul (Mir.cst 20) (Mir.pow Mir.x 3))))) (Mir.mul (Mir.cst
    210) (Mir.pow Mir.x 5))) (by decide +kernel)

private theorem regPow1 (N : Nat) : 30 * N ^ 2 * (7 * N ^ 3) = 210 * N ^ 5
  :=
  mirEq N 0
    (Mir.mul (Mir.mul (Mir.cst 30) (Mir.pow Mir.x 2))
      (Mir.mul (Mir.cst 7) (Mir.pow Mir.x 3)))
    (Mir.mul (Mir.cst 210) (Mir.pow Mir.x 5)) (by decide +kernel)

private theorem regPow2 (N : Nat) : 21 * N ^ 4 * N = 21 * N ^ 5 :=
  mirEq N 0
    (Mir.mul (Mir.mul (Mir.cst 21) (Mir.pow Mir.x 4)) Mir.x)
    (Mir.mul (Mir.cst 21) (Mir.pow Mir.x 5)) (by decide +kernel)

/-- The family's square closed read, `630·Σw²` at its displayed
polynomial, cross-added. -/
theorem witSq_closed (N : Nat) :
    630 * witSq N + 105 * N ^ 5 + 21 * N = 16 * N ^ 9 + 110 * N ^ 3 := by
  have hb0 : 630 * (witSq N + 2 * N ^ 2 * powSum 6 N)
      = 630 * (N ^ 4 * powSum 4 N + powSum 8 N) :=
    congrArg (fun t => 630 * t) (witSq_bridge N)
  rw [Nat.left_distrib 630 (witSq N) (2 * N ^ 2 * powSum 6 N),
    Nat.left_distrib 630 (N ^ 4 * powSum 4 N) (powSum 8 N),
    mulRegroup 630 2 (N ^ 2) (powSum 6 N),
    ← ground.mulAssoc 630 (N ^ 4) (powSum 4 N)] at hb0
  have h6 := scaleRead (powSum6_closed N) (30 * N ^ 2)
  rw [mulRegroup4 30 (N ^ 2) 42 (powSum 6 N), regPow1 N] at h6
  have h4 := scaleRead (powSum4_closed N) (21 * N ^ 4)
  rw [mulRegroup4 21 (N ^ 4) 30 (powSum 4 N), regPow2 N] at h4
  have h8' : 90 * powSum 8 N + (42 * N ^ 5 + 3 * N)
      = 10 * N ^ 9 + 45 * N ^ 8 + 60 * N ^ 7 + 20 * N ^ 3 := by
    rw [← Nat.add_assoc (90 * powSum 8 N) (42 * N ^ 5) (3 * N)]
    exact powSum8_closed N
  have h8 := scaleRead h8' 7
  rw [← ground.mulAssoc 7 90 (powSum 8 N),
    Nat.left_distrib 7 (42 * N ^ 5) (3 * N),
    ← ground.mulAssoc 7 42 (N ^ 5), ← ground.mulAssoc 7 3 N] at h8
  have hfin := balancedAdd hb0 (210 * N ^ 5) (21 * N ^ 5)
    (294 * N ^ 5 + 21 * N)
  rw [h6, h4, h8] at hfin
  refine ground.addCancelR
    (30 * N ^ 2 * (6 * N ^ 7 + 21 * N ^ 6 + 21 * N ^ 5 + N)
      + 210 * N ^ 5) ?_
  rw [sqClosedLeft N (witSq N), sqClosedRight N]
  exact hfin

private theorem regPow3 (N : Nat) :
    5 * N ^ 2 * (7 * N ^ 4)
      = 35 * N ^ 6 :=
  mirEq N 0 (Mir.mul (Mir.mul (Mir.cst 5) (Mir.pow Mir.x 2)) (Mir.mul
    (Mir.cst 7) (Mir.pow Mir.x 4))) (Mir.mul (Mir.cst 35) (Mir.pow Mir.x
    6)) (by decide +kernel)

private theorem regPow4 (N : Nat) :
    5 * N ^ 4 * N ^ 2
      = 5 * N ^ 6 :=
  mirEq N 0 (Mir.mul (Mir.mul (Mir.cst 5) (Mir.pow Mir.x 4)) (Mir.pow
    Mir.x 2)) (Mir.mul (Mir.cst 5) (Mir.pow Mir.x 6)) (by decide +kernel)

private theorem regPow5 (N : Nat) :
    154 * N ^ 2 * (42 * N ^ 5)
      = 6468 * N ^ 7 :=
  mirEq N 0 (Mir.mul (Mir.mul (Mir.cst 154) (Mir.pow Mir.x 2)) (Mir.mul
    (Mir.cst 42) (Mir.pow Mir.x 5))) (Mir.mul (Mir.cst 6468) (Mir.pow
    Mir.x 7)) (by decide +kernel)

private theorem regPow6 (N : Nat) :
    154 * N ^ 2 * (3 * N)
      = 462 * N ^ 3 :=
  mirEq N 0 (Mir.mul (Mir.mul (Mir.cst 154) (Mir.pow Mir.x 2)) (Mir.mul
    (Mir.cst 3) Mir.x)) (Mir.mul (Mir.cst 462) (Mir.pow Mir.x 3)) (by decide +kernel)

private theorem regPow7 (N : Nat) :
    165 * N ^ 4 * (7 * N ^ 3)
      = 1155 * N ^ 7 :=
  mirEq N 0 (Mir.mul (Mir.mul (Mir.cst 165) (Mir.pow Mir.x 4)) (Mir.mul
    (Mir.cst 7) (Mir.pow Mir.x 3))) (Mir.mul (Mir.cst 1155) (Mir.pow Mir.x
    7)) (by decide +kernel)

/-- The linear well part's left side at the balanced additions. -/
private theorem wellLinLeft (N W : Nat) :
    60 * W + 12 * N ^ 6 + 9 * N ^ 2 + (5 * N ^ 2 * (3 * N ^ 8 + 12 * N ^ 7
      + 14 * N ^ 6 + 2 * N ^ 2) + 35 * N ^ 6)
      = 60 * W + 5 * N ^ 2 * (3 * N ^ 8 + 12 * N ^ 7 + 14 * N ^ 6 + 2 * N
        ^ 2) + (5 * N ^ 6 + (42 * N ^ 6 + 9 * N ^ 2)) :=
  mirEq N W (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 60) Mir.y)
    (Mir.mul (Mir.cst 12) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst 9)
    (Mir.pow Mir.x 2))) (Mir.add (Mir.mul (Mir.mul (Mir.cst 5) (Mir.pow
    Mir.x 2)) (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 3) (Mir.pow
    Mir.x 8)) (Mir.mul (Mir.cst 12) (Mir.pow Mir.x 7))) (Mir.mul (Mir.cst
    14) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 2))))
    (Mir.mul (Mir.cst 35) (Mir.pow Mir.x 6)))) (Mir.add (Mir.add (Mir.mul
    (Mir.cst 60) Mir.y) (Mir.mul (Mir.mul (Mir.cst 5) (Mir.pow Mir.x 2))
    (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 3) (Mir.pow Mir.x 8))
    (Mir.mul (Mir.cst 12) (Mir.pow Mir.x 7))) (Mir.mul (Mir.cst 14)
    (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 2)))))
    (Mir.add (Mir.mul (Mir.cst 5) (Mir.pow Mir.x 6)) (Mir.add (Mir.mul
    (Mir.cst 42) (Mir.pow Mir.x 6)) (Mir.mul (Mir.cst 9) (Mir.pow Mir.x
    2))))) (by decide +kernel)

/-- The linear well part's right side at the balanced additions. -/
private theorem wellLinRight (N : Nat) :
    N ^ 10 + 20 * N ^ 4 + (5 * N ^ 2 * (3 * N ^ 8 + 12 * N ^ 7 + 14 * N ^
      6 + 2 * N ^ 2) + 35 * N ^ 6)
      = 5 * N ^ 4 * (2 * N ^ 6 + 6 * N ^ 5 + 5 * N ^ 4) + 3 * (2 * N ^ 10
        + 10 * N ^ 9 + 15 * N ^ 8 + 10 * N ^ 4) + 35 * N ^ 6 :=
  mirEq N 0 (Mir.add (Mir.add (Mir.pow Mir.x 10) (Mir.mul (Mir.cst 20)
    (Mir.pow Mir.x 4))) (Mir.add (Mir.mul (Mir.mul (Mir.cst 5) (Mir.pow
    Mir.x 2)) (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 3) (Mir.pow
    Mir.x 8)) (Mir.mul (Mir.cst 12) (Mir.pow Mir.x 7))) (Mir.mul (Mir.cst
    14) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 2))))
    (Mir.mul (Mir.cst 35) (Mir.pow Mir.x 6)))) (Mir.add (Mir.add (Mir.mul
    (Mir.mul (Mir.cst 5) (Mir.pow Mir.x 4)) (Mir.add (Mir.add (Mir.mul
    (Mir.cst 2) (Mir.pow Mir.x 6)) (Mir.mul (Mir.cst 6) (Mir.pow Mir.x
    5))) (Mir.mul (Mir.cst 5) (Mir.pow Mir.x 4)))) (Mir.mul (Mir.cst 3)
    (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 10))
    (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 9))) (Mir.mul (Mir.cst 15)
    (Mir.pow Mir.x 8))) (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 4)))))
    (Mir.mul (Mir.cst 35) (Mir.pow Mir.x 6))) (by decide +kernel)

/-- The square well part's left side at the balanced additions. -/
private theorem wellSqLeft (N W : Nat) :
    6930 * W + 1617 * N ^ 7 + 3003 * N ^ 3 + (154 * N ^ 2 * (10 * N ^ 9 +
      45 * N ^ 8 + 60 * N ^ 7 + 20 * N ^ 3) + (6468 * N ^ 7 + 462 * N ^
      3))
      = 6930 * W + 154 * N ^ 2 * (10 * N ^ 9 + 45 * N ^ 8 + 60 * N ^ 7 +
        20 * N ^ 3) + (1155 * N ^ 7 + (6930 * N ^ 7 + 3465 * N ^ 3)) :=
  mirEq N W (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 6930) Mir.y)
    (Mir.mul (Mir.cst 1617) (Mir.pow Mir.x 7))) (Mir.mul (Mir.cst 3003)
    (Mir.pow Mir.x 3))) (Mir.add (Mir.mul (Mir.mul (Mir.cst 154) (Mir.pow
    Mir.x 2)) (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 10) (Mir.pow
    Mir.x 9)) (Mir.mul (Mir.cst 45) (Mir.pow Mir.x 8))) (Mir.mul (Mir.cst
    60) (Mir.pow Mir.x 7))) (Mir.mul (Mir.cst 20) (Mir.pow Mir.x 3))))
    (Mir.add (Mir.mul (Mir.cst 6468) (Mir.pow Mir.x 7)) (Mir.mul (Mir.cst
    462) (Mir.pow Mir.x 3))))) (Mir.add (Mir.add (Mir.mul (Mir.cst 6930)
    Mir.y) (Mir.mul (Mir.mul (Mir.cst 154) (Mir.pow Mir.x 2)) (Mir.add
    (Mir.add (Mir.add (Mir.mul (Mir.cst 10) (Mir.pow Mir.x 9)) (Mir.mul
    (Mir.cst 45) (Mir.pow Mir.x 8))) (Mir.mul (Mir.cst 60) (Mir.pow Mir.x
    7))) (Mir.mul (Mir.cst 20) (Mir.pow Mir.x 3))))) (Mir.add (Mir.mul
    (Mir.cst 1155) (Mir.pow Mir.x 7)) (Mir.add (Mir.mul (Mir.cst 6930)
    (Mir.pow Mir.x 7)) (Mir.mul (Mir.cst 3465) (Mir.pow Mir.x 3))))) (by decide +kernel)

/-- The square well part's right side at the balanced additions. -/
private theorem wellSqRight (N : Nat) :
    80 * N ^ 11 + 4015 * N ^ 5 + 525 * N + (154 * N ^ 2 * (10 * N ^ 9 + 45
      * N ^ 8 + 60 * N ^ 7 + 20 * N ^ 3) + (6468 * N ^ 7 + 462 * N ^ 3))
      = 165 * N ^ 4 * (6 * N ^ 7 + 21 * N ^ 6 + 21 * N ^ 5 + N) + 105 * (6
        * N ^ 11 + 33 * N ^ 10 + 55 * N ^ 9 + 66 * N ^ 5 + 5 * N) + (6468
        * N ^ 7 + 462 * N ^ 3) :=
  mirEq N 0 (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 80) (Mir.pow
    Mir.x 11)) (Mir.mul (Mir.cst 4015) (Mir.pow Mir.x 5))) (Mir.mul
    (Mir.cst 525) Mir.x)) (Mir.add (Mir.mul (Mir.mul (Mir.cst 154)
    (Mir.pow Mir.x 2)) (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 10)
    (Mir.pow Mir.x 9)) (Mir.mul (Mir.cst 45) (Mir.pow Mir.x 8))) (Mir.mul
    (Mir.cst 60) (Mir.pow Mir.x 7))) (Mir.mul (Mir.cst 20) (Mir.pow Mir.x
    3)))) (Mir.add (Mir.mul (Mir.cst 6468) (Mir.pow Mir.x 7)) (Mir.mul
    (Mir.cst 462) (Mir.pow Mir.x 3))))) (Mir.add (Mir.add (Mir.mul
    (Mir.mul (Mir.cst 165) (Mir.pow Mir.x 4)) (Mir.add (Mir.add (Mir.add
    (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 7)) (Mir.mul (Mir.cst 21) (Mir.pow
    Mir.x 6))) (Mir.mul (Mir.cst 21) (Mir.pow Mir.x 5))) Mir.x)) (Mir.mul
    (Mir.cst 105) (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 6)
    (Mir.pow Mir.x 11)) (Mir.mul (Mir.cst 33) (Mir.pow Mir.x 10)))
    (Mir.mul (Mir.cst 55) (Mir.pow Mir.x 9))) (Mir.mul (Mir.cst 66)
    (Mir.pow Mir.x 5))) (Mir.mul (Mir.cst 5) Mir.x)))) (Mir.add (Mir.mul
    (Mir.cst 6468) (Mir.pow Mir.x 7)) (Mir.mul (Mir.cst 462) (Mir.pow
    Mir.x 3)))) (by decide +kernel)

/-- The linear well part's closed read. -/
theorem witSqM_closed (N : Nat) :
    60 * witSqM N + 12 * N ^ 6 + 9 * N ^ 2 = N ^ 10 + 20 * N ^ 4 := by
  have hb0 : 60 * (witSqM N + 2 * N ^ 2 * powSum 7 N)
      = 60 * (N ^ 4 * powSum 5 N + powSum 9 N) :=
    congrArg (fun t => 60 * t) (witSqM_bridge N)
  rw [Nat.left_distrib 60 (witSqM N) (2 * N ^ 2 * powSum 7 N),
    Nat.left_distrib 60 (N ^ 4 * powSum 5 N) (powSum 9 N),
    mulRegroup 60 2 (N ^ 2) (powSum 7 N),
    ← ground.mulAssoc 60 (N ^ 4) (powSum 5 N)] at hb0
  have h7 := scaleRead (powSum7_closed N) (5 * N ^ 2)
  rw [mulRegroup4 5 (N ^ 2) 24 (powSum 7 N), regPow3 N] at h7
  have h5 := scaleRead (powSum5_closed N) (5 * N ^ 4)
  rw [mulRegroup4 5 (N ^ 4) 12 (powSum 5 N), regPow4 N] at h5
  have h9' : 20 * powSum 9 N + (14 * N ^ 6 + 3 * N ^ 2)
      = 2 * N ^ 10 + 10 * N ^ 9 + 15 * N ^ 8 + 10 * N ^ 4 := by
    rw [← Nat.add_assoc (20 * powSum 9 N) (14 * N ^ 6) (3 * N ^ 2)]
    exact powSum9_closed N
  have h9 := scaleRead h9' 3
  rw [← ground.mulAssoc 3 20 (powSum 9 N),
    Nat.left_distrib 3 (14 * N ^ 6) (3 * N ^ 2),
    ← ground.mulAssoc 3 14 (N ^ 6), ← ground.mulAssoc 3 3 (N ^ 2)] at h9
  have hfin := balancedAdd hb0 (35 * N ^ 6) (5 * N ^ 6)
    (42 * N ^ 6 + 9 * N ^ 2)
  rw [h7, h5, h9] at hfin
  refine ground.addCancelR
    (5 * N ^ 2 * (3 * N ^ 8 + 12 * N ^ 7 + 14 * N ^ 6 + 2 * N ^ 2)
      + 35 * N ^ 6) ?_
  rw [wellLinLeft N (witSqM N), wellLinRight N]
  exact hfin

/-- The square well part's closed read. -/
theorem witSqMM_closed (N : Nat) :
    6930 * witSqMM N + 1617 * N ^ 7 + 3003 * N ^ 3
      = 80 * N ^ 11 + 4015 * N ^ 5 + 525 * N := by
  have hb0 : 6930 * (witSqMM N + 2 * N ^ 2 * powSum 8 N)
      = 6930 * (N ^ 4 * powSum 6 N + powSum 10 N) :=
    congrArg (fun t => 6930 * t) (witSqMM_bridge N)
  rw [Nat.left_distrib 6930 (witSqMM N) (2 * N ^ 2 * powSum 8 N),
    Nat.left_distrib 6930 (N ^ 4 * powSum 6 N) (powSum 10 N),
    mulRegroup 6930 2 (N ^ 2) (powSum 8 N),
    ← ground.mulAssoc 6930 (N ^ 4) (powSum 6 N)] at hb0
  have h8' : 90 * powSum 8 N + (42 * N ^ 5 + 3 * N)
      = 10 * N ^ 9 + 45 * N ^ 8 + 60 * N ^ 7 + 20 * N ^ 3 := by
    rw [← Nat.add_assoc (90 * powSum 8 N) (42 * N ^ 5) (3 * N)]
    exact powSum8_closed N
  have h8 := scaleRead h8' (154 * N ^ 2)
  rw [mulRegroup4 154 (N ^ 2) 90 (powSum 8 N),
    Nat.left_distrib (154 * N ^ 2) (42 * N ^ 5) (3 * N),
    regPow5 N, regPow6 N] at h8
  have h6 := scaleRead (powSum6_closed N) (165 * N ^ 4)
  rw [mulRegroup4 165 (N ^ 4) 42 (powSum 6 N), regPow7 N] at h6
  have h10' : 66 * powSum 10 N + (66 * N ^ 7 + 33 * N ^ 3)
      = 6 * N ^ 11 + 33 * N ^ 10 + 55 * N ^ 9 + 66 * N ^ 5 + 5 * N := by
    rw [← Nat.add_assoc (66 * powSum 10 N) (66 * N ^ 7) (33 * N ^ 3)]
    exact powSum10_closed N
  have h10 := scaleRead h10' 105
  rw [← ground.mulAssoc 105 66 (powSum 10 N),
    Nat.left_distrib 105 (66 * N ^ 7) (33 * N ^ 3),
    ← ground.mulAssoc 105 66 (N ^ 7),
    ← ground.mulAssoc 105 33 (N ^ 3)] at h10
  have hfin := balancedAdd hb0 (6468 * N ^ 7 + 462 * N ^ 3) (1155 * N ^ 7)
    (6930 * N ^ 7 + 3465 * N ^ 3)
  rw [h8, h6, h10] at hfin
  refine ground.addCancelR
    (154 * N ^ 2 * (10 * N ^ 9 + 45 * N ^ 8 + 60 * N ^ 7 + 20 * N ^ 3)
      + (6468 * N ^ 7 + 462 * N ^ 3)) ?_
  rw [wellSqLeft N (witSqMM N), wellSqRight N]
  exact hfin

private theorem dL0 (N W : Nat) :
    105 * (2 * N ^ 2 * W)
      = 210 * N ^ 2 * W :=
  mirEq N W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.mul (Mir.cst 2) (Mir.pow
    Mir.x 2)) Mir.y)) (Mir.mul (Mir.mul (Mir.cst 210) (Mir.pow Mir.x 2))
    Mir.y) (by decide +kernel)

private theorem dL1 (N W : Nat) :
    105 * (12 * N ^ 2 * W)
      = 630 * N ^ 2 * (2 * W) :=
  mirEq N W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.mul (Mir.cst 12) (Mir.pow
    Mir.x 2)) Mir.y)) (Mir.mul (Mir.mul (Mir.cst 630) (Mir.pow Mir.x 2))
    (Mir.mul (Mir.cst 2) Mir.y)) (by decide +kernel)

private theorem dL2 (N W : Nat) :
    105 * (28 * N ^ 2 * W)
      = 490 * N ^ 2 * (6 * W) :=
  mirEq N W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.mul (Mir.cst 28) (Mir.pow
    Mir.x 2)) Mir.y)) (Mir.mul (Mir.mul (Mir.cst 490) (Mir.pow Mir.x 2))
    (Mir.mul (Mir.cst 6) Mir.y)) (by decide +kernel)

private theorem dL3 (N W : Nat) :
    105 * (32 * N ^ 2 * W)
      = 840 * N ^ 2 * (4 * W) :=
  mirEq N W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.mul (Mir.cst 32) (Mir.pow
    Mir.x 2)) Mir.y)) (Mir.mul (Mir.mul (Mir.cst 840) (Mir.pow Mir.x 2))
    (Mir.mul (Mir.cst 4) Mir.y)) (by decide +kernel)

private theorem dL4 (N W : Nat) :
    105 * (16 * N ^ 2 * W)
      = 56 * N ^ 2 * (30 * W) :=
  mirEq N W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.mul (Mir.cst 16) (Mir.pow
    Mir.x 2)) Mir.y)) (Mir.mul (Mir.mul (Mir.cst 56) (Mir.pow Mir.x 2))
    (Mir.mul (Mir.cst 30) Mir.y)) (by decide +kernel)

private theorem dR1 (N W : Nat) :
    105 * (N ^ 4 * W)
      = 105 * N ^ 4 * W :=
  mirEq N W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.pow Mir.x 4) Mir.y))
    (Mir.mul (Mir.mul (Mir.cst 105) (Mir.pow Mir.x 4)) Mir.y) (by decide +kernel)

private theorem dR3 (N W : Nat) :
    105 * (4 * N ^ 4 * W)
      = 210 * N ^ 4 * (2 * W) :=
  mirEq N W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.mul (Mir.cst 4) (Mir.pow
    Mir.x 4)) Mir.y)) (Mir.mul (Mir.mul (Mir.cst 210) (Mir.pow Mir.x 4))
    (Mir.mul (Mir.cst 2) Mir.y)) (by decide +kernel)

private theorem dR5 (N W : Nat) :
    105 * (4 * N ^ 4 * W)
      = 70 * N ^ 4 * (6 * W) :=
  mirEq N W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.mul (Mir.cst 4) (Mir.pow
    Mir.x 4)) Mir.y)) (Mir.mul (Mir.mul (Mir.cst 70) (Mir.pow Mir.x 4))
    (Mir.mul (Mir.cst 6) Mir.y)) (by decide +kernel)

private theorem dR2 (W : Nat) :
    105 * (8 * W)
      = 420 * (2 * W) :=
  mirEq 0 W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.cst 8) Mir.y)) (Mir.mul
    (Mir.cst 420) (Mir.mul (Mir.cst 2) Mir.y)) (by decide +kernel)

private theorem dR4 (W : Nat) :
    105 * (28 * W)
      = 490 * (6 * W) :=
  mirEq 0 W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.cst 28) Mir.y)) (Mir.mul
    (Mir.cst 490) (Mir.mul (Mir.cst 6) Mir.y)) (by decide +kernel)

private theorem dR6 (W : Nat) :
    105 * (56 * W)
      = 1470 * (4 * W) :=
  mirEq 0 W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.cst 56) Mir.y)) (Mir.mul
    (Mir.cst 1470) (Mir.mul (Mir.cst 4) Mir.y)) (by decide +kernel)

private theorem dR7 (W : Nat) :
    105 * (68 * W)
      = 238 * (30 * W) :=
  mirEq 0 W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.cst 68) Mir.y)) (Mir.mul
    (Mir.cst 238) (Mir.mul (Mir.cst 30) Mir.y)) (by decide +kernel)

private theorem dR8 (W : Nat) :
    105 * (48 * W)
      = 420 * (12 * W) :=
  mirEq 0 W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.cst 48) Mir.y)) (Mir.mul
    (Mir.cst 420) (Mir.mul (Mir.cst 12) Mir.y)) (by decide +kernel)

private theorem dR9 (W : Nat) :
    105 * (16 * W)
      = 40 * (42 * W) :=
  mirEq 0 W (Mir.mul (Mir.cst 105) (Mir.mul (Mir.cst 16) Mir.y)) (Mir.mul
    (Mir.cst 40) (Mir.mul (Mir.cst 42) Mir.y)) (by decide +kernel)

/-- The difference closed read's left side at the balanced additions. -/
private theorem diffLeft (n W : Nat) :
    105 * W + 147 * (n + 1) ^ 5 + 105 * (n + 1) ^ 4 + 23 * (n + 1) + 105 +
      (336 * n ^ 7 + 2352 * n ^ 6 + 6769 * n ^ 5 + 10220 * n ^ 4 + 8820 *
      n ^ 3 + 3920 * n ^ 2 + 390 * n)
      = 105 * W + 210 * (n + 1) ^ 2 * n + 630 * (n + 1) ^ 2 * (n ^ 2 + n)
        + 490 * (n + 1) ^ 2 * (2 * n ^ 3 + 3 * n ^ 2 + n) + 840 * (n + 1)
        ^ 2 * (n ^ 4 + 2 * n ^ 3 + n ^ 2) + 56 * (n + 1) ^ 2 * (6 * n ^ 5
        + 15 * n ^ 4 + 10 * n ^ 3) + 238 * n + 420 * n ^ 2 + 40 * (7 * n ^
        3) + 380 :=
  mirEq n W (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst
    105) Mir.y) (Mir.mul (Mir.cst 147) (Mir.pow (Mir.add Mir.x (Mir.cst
    1)) 5))) (Mir.mul (Mir.cst 105) (Mir.pow (Mir.add Mir.x (Mir.cst 1))
    4))) (Mir.mul (Mir.cst 23) (Mir.add Mir.x (Mir.cst 1)))) (Mir.cst
    105)) (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul
    (Mir.cst 336) (Mir.pow Mir.x 7)) (Mir.mul (Mir.cst 2352) (Mir.pow
    Mir.x 6))) (Mir.mul (Mir.cst 6769) (Mir.pow Mir.x 5))) (Mir.mul
    (Mir.cst 10220) (Mir.pow Mir.x 4))) (Mir.mul (Mir.cst 8820) (Mir.pow
    Mir.x 3))) (Mir.mul (Mir.cst 3920) (Mir.pow Mir.x 2))) (Mir.mul
    (Mir.cst 390) Mir.x))) (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 105) Mir.y)
    (Mir.mul (Mir.mul (Mir.cst 210) (Mir.pow (Mir.add Mir.x (Mir.cst 1))
    2)) Mir.x)) (Mir.mul (Mir.mul (Mir.cst 630) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 2)) (Mir.add (Mir.pow Mir.x 2) Mir.x))) (Mir.mul (Mir.mul
    (Mir.cst 490) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 2)) (Mir.add
    (Mir.add (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 3)) (Mir.mul (Mir.cst 3)
    (Mir.pow Mir.x 2))) Mir.x))) (Mir.mul (Mir.mul (Mir.cst 840) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 2)) (Mir.add (Mir.add (Mir.pow Mir.x 4)
    (Mir.mul (Mir.cst 2) (Mir.pow Mir.x 3))) (Mir.pow Mir.x 2)))) (Mir.mul
    (Mir.mul (Mir.cst 56) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 2))
    (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 5)) (Mir.mul
    (Mir.cst 15) (Mir.pow Mir.x 4))) (Mir.mul (Mir.cst 10) (Mir.pow Mir.x
    3))))) (Mir.mul (Mir.cst 238) Mir.x)) (Mir.mul (Mir.cst 420) (Mir.pow
    Mir.x 2))) (Mir.mul (Mir.cst 40) (Mir.mul (Mir.cst 7) (Mir.pow Mir.x
    3)))) (Mir.cst 380)) (by decide +kernel)

/-- The difference closed read's right side at the balanced additions. -/
private theorem diffRight (n : Nat) :
    44 * (n + 1) ^ 7 + 126 * (n + 1) ^ 3 + 210 * (n + 1) ^ 2 + (336 * n ^
      7 + 2352 * n ^ 6 + 6769 * n ^ 5 + 10220 * n ^ 4 + 8820 * n ^ 3 +
      3920 * n ^ 2 + 390 * n)
      = 105 * n + 105 * (n + 1) ^ 4 * n + 420 * (n ^ 2 + n) + 210 * (n +
        1) ^ 4 * (n ^ 2 + n) + 490 * (2 * n ^ 3 + 3 * n ^ 2 + n) + 70 * (n
        + 1) ^ 4 * (2 * n ^ 3 + 3 * n ^ 2 + n) + 1470 * (n ^ 4 + 2 * n ^ 3
        + n ^ 2) + 238 * (6 * n ^ 5 + 15 * n ^ 4 + 10 * n ^ 3) + 420 * (2
        * n ^ 6 + 6 * n ^ 5 + 5 * n ^ 4) + 40 * (6 * n ^ 7 + 21 * n ^ 6 +
        21 * n ^ 5 + n) + 56 * (n + 1) ^ 2 * n + 380 :=
  mirEq n 0 (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 44) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 7)) (Mir.mul (Mir.cst 126) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 3))) (Mir.mul (Mir.cst 210) (Mir.pow
    (Mir.add Mir.x (Mir.cst 1)) 2))) (Mir.add (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.mul (Mir.cst 336) (Mir.pow Mir.x 7)) (Mir.mul
    (Mir.cst 2352) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst 6769) (Mir.pow
    Mir.x 5))) (Mir.mul (Mir.cst 10220) (Mir.pow Mir.x 4))) (Mir.mul
    (Mir.cst 8820) (Mir.pow Mir.x 3))) (Mir.mul (Mir.cst 3920) (Mir.pow
    Mir.x 2))) (Mir.mul (Mir.cst 390) Mir.x))) (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add (Mir.add
    (Mir.add (Mir.mul (Mir.cst 105) Mir.x) (Mir.mul (Mir.mul (Mir.cst 105)
    (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 4)) Mir.x)) (Mir.mul (Mir.cst
    420) (Mir.add (Mir.pow Mir.x 2) Mir.x))) (Mir.mul (Mir.mul (Mir.cst
    210) (Mir.pow (Mir.add Mir.x (Mir.cst 1)) 4)) (Mir.add (Mir.pow Mir.x
    2) Mir.x))) (Mir.mul (Mir.cst 490) (Mir.add (Mir.add (Mir.mul (Mir.cst
    2) (Mir.pow Mir.x 3)) (Mir.mul (Mir.cst 3) (Mir.pow Mir.x 2)))
    Mir.x))) (Mir.mul (Mir.mul (Mir.cst 70) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 4)) (Mir.add (Mir.add (Mir.mul (Mir.cst 2) (Mir.pow Mir.x
    3)) (Mir.mul (Mir.cst 3) (Mir.pow Mir.x 2))) Mir.x))) (Mir.mul
    (Mir.cst 1470) (Mir.add (Mir.add (Mir.pow Mir.x 4) (Mir.mul (Mir.cst
    2) (Mir.pow Mir.x 3))) (Mir.pow Mir.x 2)))) (Mir.mul (Mir.cst 238)
    (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 5)) (Mir.mul
    (Mir.cst 15) (Mir.pow Mir.x 4))) (Mir.mul (Mir.cst 10) (Mir.pow Mir.x
    3))))) (Mir.mul (Mir.cst 420) (Mir.add (Mir.add (Mir.mul (Mir.cst 2)
    (Mir.pow Mir.x 6)) (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 5))) (Mir.mul
    (Mir.cst 5) (Mir.pow Mir.x 4))))) (Mir.mul (Mir.cst 40) (Mir.add
    (Mir.add (Mir.add (Mir.mul (Mir.cst 6) (Mir.pow Mir.x 7)) (Mir.mul
    (Mir.cst 21) (Mir.pow Mir.x 6))) (Mir.mul (Mir.cst 21) (Mir.pow Mir.x
    5))) Mir.x))) (Mir.mul (Mir.mul (Mir.cst 56) (Mir.pow (Mir.add Mir.x
    (Mir.cst 1)) 2)) Mir.x)) (Mir.cst 380)) (by decide +kernel)

/-- The difference sum's closed read, at the occupied depths. -/
theorem witDiffSq_closed : ∀ N : Nat, 1 ≤ N →
    105 * witDiffSq N + 147 * N ^ 5 + 105 * N ^ 4 + 23 * N + 105
      = 44 * N ^ 7 + 126 * N ^ 3 + 210 * N ^ 2
  | 0, h => absurd h (Nat.not_succ_le_zero 0)
  | n + 1, _ => by
    have h := witDiffSq_bridge (n + 1)
    rw [show n + 1 - 1 = n from rfl] at h
    have h105 := mulEq 105 h
    rw [Nat.left_distrib, Nat.left_distrib, Nat.left_distrib,
      Nat.left_distrib, Nat.left_distrib, Nat.left_distrib,
      Nat.left_distrib, Nat.left_distrib, Nat.left_distrib,
      Nat.left_distrib, Nat.left_distrib, Nat.left_distrib,
      Nat.left_distrib, Nat.left_distrib] at h105
    rw [dL0 (n + 1) (powSum 0 n), dL1 (n + 1) (powSum 1 n),
      dL2 (n + 1) (powSum 2 n), dL3 (n + 1) (powSum 3 n),
      dL4 (n + 1) (powSum 4 n), dR1 (n + 1) (powSum 0 n),
      dR2 (powSum 1 n), dR3 (n + 1) (powSum 1 n),
      dR4 (powSum 2 n), dR5 (n + 1) (powSum 2 n),
      dR6 (powSum 3 n), dR7 (powSum 4 n), dR8 (powSum 5 n),
      dR9 (powSum 6 n), powSum0_closed n, powSum1_closed n,
      powSum2_closed n, powSum3_closed n] at h105
    have g4L := scaleRead (powSum4_closed n) (56 * (n + 1) ^ 2)
    have g4R := scaleRead (powSum4_closed n) 238
    have g5R := scaleRead (powSum5_closed n) 420
    have g6R := scaleRead (powSum6_closed n) 40
    have hA := addEq (56 * (n + 1) ^ 2 * n) h105
    rw [Nat.add_assoc
        (105 * witDiffSq (n + 1) + 210 * (n + 1) ^ 2 * n
          + 630 * (n + 1) ^ 2 * (n ^ 2 + n)
          + 490 * (n + 1) ^ 2 * (2 * n ^ 3 + 3 * n ^ 2 + n)
          + 840 * (n + 1) ^ 2 * (n ^ 4 + 2 * n ^ 3 + n ^ 2))
        (56 * (n + 1) ^ 2 * (30 * powSum 4 n))
        (56 * (n + 1) ^ 2 * n),
      g4L] at hA
    have hB := addEq (238 * n) hA
    rw [Nat.add_right_comm _ (56 * (n + 1) ^ 2 * n) (238 * n),
      Nat.add_right_comm _ (40 * (42 * powSum 6 n)) (238 * n),
      Nat.add_right_comm _ (420 * (12 * powSum 5 n)) (238 * n),
      Nat.add_assoc _ (238 * (30 * powSum 4 n)) (238 * n),
      g4R] at hB
    have hC := addEq (420 * n ^ 2) hB
    rw [Nat.add_right_comm _ (56 * (n + 1) ^ 2 * n) (420 * n ^ 2),
      Nat.add_right_comm _ (40 * (42 * powSum 6 n)) (420 * n ^ 2),
      Nat.add_assoc _ (420 * (12 * powSum 5 n)) (420 * n ^ 2),
      g5R] at hC
    have hD := addEq (40 * (7 * n ^ 3)) hC
    rw [Nat.add_right_comm _ (56 * (n + 1) ^ 2 * n) (40 * (7 * n ^ 3)),
      Nat.add_assoc _ (40 * (42 * powSum 6 n)) (40 * (7 * n ^ 3)),
      g6R] at hD
    have hfin := addEq 380 hD
    refine ground.addCancelR
      (336 * n ^ 7 + 2352 * n ^ 6 + 6769 * n ^ 5 + 10220 * n ^ 4
        + 8820 * n ^ 3 + 3920 * n ^ 2 + 390 * n) ?_
    rw [diffLeft n (witDiffSq (n + 1)), diffRight n]
    exact hfin

private theorem hornerSqU (N : Nat) :
    0 + N * (0 + N * (0 + N * (110 + N * (0 + N * (0 + N * (0 + N * (0 + N
      * (0 + N * (16 + N * (0))))))))))
      = 16 * N ^ 9 + 110 * N ^ 3 := by
  show hread [0, 0, 0, 110, 0, 0, 0, 0, 0, 16] N = 16 * N ^ 9 + 110 * N ^
    3
  rw [hreadRow [0, 0, 0, 110, 0, 0, 0, 0, 0, 16] N]
  exact mirRaw N 0 ([0, 0, 0, 110, 0, 0, 0, 0, 0, 16].map (fun c => [c]))
    (Mir.add (Mir.mul (Mir.cst 16) (Mir.pow Mir.x 9)) (Mir.mul (Mir.cst
    110) (Mir.pow Mir.x 3))) rfl

private theorem hornerSqV (N : Nat) :
    0 + N * (21 + N * (0 + N * (0 + N * (0 + N * (105 + N * (0 + N * (0 +
      N * (0 + N * (0 + N * (0))))))))))
      = 105 * N ^ 5 + 21 * N := by
  show hread [0, 21, 0, 0, 0, 105, 0, 0, 0, 0] N = 105 * N ^ 5 + 21 * N
  rw [hreadRow [0, 21, 0, 0, 0, 105, 0, 0, 0, 0] N]
  exact mirRaw N 0 ([0, 21, 0, 0, 0, 105, 0, 0, 0, 0].map (fun c => [c]))
    (Mir.add (Mir.mul (Mir.cst 105) (Mir.pow Mir.x 5)) (Mir.mul (Mir.cst
    21) Mir.x)) rfl

private theorem hornerDiffU (N : Nat) :
    0 + N * (0 + N * (210 + N * (126 + N * (0 + N * (0 + N * (0 + N * (44
      + N * (0))))))))
      = 44 * N ^ 7 + 126 * N ^ 3 + 210 * N ^ 2 := by
  show hread [0, 0, 210, 126, 0, 0, 0, 44] N = 44 * N ^ 7 + 126 * N ^ 3 +
    210 * N ^ 2
  rw [hreadRow [0, 0, 210, 126, 0, 0, 0, 44] N]
  exact mirRaw N 0 ([0, 0, 210, 126, 0, 0, 0, 44].map (fun c => [c]))
    (Mir.add (Mir.add (Mir.mul (Mir.cst 44) (Mir.pow Mir.x 7)) (Mir.mul
    (Mir.cst 126) (Mir.pow Mir.x 3))) (Mir.mul (Mir.cst 210) (Mir.pow
    Mir.x 2))) rfl

private theorem hornerDiffV (N : Nat) :
    105 + N * (23 + N * (0 + N * (0 + N * (105 + N * (147 + N * (0 + N *
      (0 + N * (0))))))))
      = 147 * N ^ 5 + 105 * N ^ 4 + 23 * N + 105 := by
  show hread [105, 23, 0, 0, 105, 147, 0, 0] N = 147 * N ^ 5 + 105 * N ^ 4
    + 23 * N + 105
  rw [hreadRow [105, 23, 0, 0, 105, 147, 0, 0] N]
  exact mirRaw N 0 ([105, 23, 0, 0, 105, 147, 0, 0].map (fun c => [c]))
    (Mir.add (Mir.add (Mir.add (Mir.mul (Mir.cst 147) (Mir.pow Mir.x 5))
    (Mir.mul (Mir.cst 105) (Mir.pow Mir.x 4))) (Mir.mul (Mir.cst 23)
    Mir.x)) (Mir.cst 105)) rfl

private theorem hornerWellU (N : Nat) :
    0 + N * (525 + N * (0 + N * (0 + N * (0 + N * (4015 + N * (0 + N * (0
      + N * (0 + N * (0 + N * (0 + N * (80 + N * (0))))))))))))
      = 80 * N ^ 11 + 4015 * N ^ 5 + 525 * N := by
  show hread [0, 525, 0, 0, 0, 4015, 0, 0, 0, 0, 0, 80] N = 80 * N ^ 11 +
    4015 * N ^ 5 + 525 * N
  rw [hreadRow [0, 525, 0, 0, 0, 4015, 0, 0, 0, 0, 0, 80] N]
  exact mirRaw N 0 ([0, 525, 0, 0, 0, 4015, 0, 0, 0, 0, 0, 80].map (fun c
    => [c])) (Mir.add (Mir.add (Mir.mul (Mir.cst 80) (Mir.pow Mir.x 11))
    (Mir.mul (Mir.cst 4015) (Mir.pow Mir.x 5))) (Mir.mul (Mir.cst 525)
    Mir.x)) rfl

private theorem hornerWellV (N : Nat) :
    0 + N * (0 + N * (0 + N * (3003 + N * (0 + N * (0 + N * (0 + N * (1617
      + N * (0 + N * (0 + N * (0 + N * (0 + N * (0))))))))))))
      = 1617 * N ^ 7 + 3003 * N ^ 3 := by
  show hread [0, 0, 0, 3003, 0, 0, 0, 1617, 0, 0, 0, 0] N = 1617 * N ^ 7 +
    3003 * N ^ 3
  rw [hreadRow [0, 0, 0, 3003, 0, 0, 0, 1617, 0, 0, 0, 0] N]
  exact mirRaw N 0 ([0, 0, 0, 3003, 0, 0, 0, 1617, 0, 0, 0, 0].map (fun c
    => [c])) (Mir.add (Mir.mul (Mir.cst 1617) (Mir.pow Mir.x 7)) (Mir.mul
    (Mir.cst 3003) (Mir.pow Mir.x 3))) rfl

/-- The family's square polynomial reads the cleared sum at every endpoint.
  -/
theorem sqClosedPoly_eval (N : Nat) :
    (poly.eval sqClosedPoly (BPair.ofNat N)).oneValue
      (BPair.ofNat (630 * witSq N)) := by
  refine poly.reads_ov (p := poly.eval sqClosedPoly (BPair.ofNat N))
    (poly.reads_step (poly.reads_step (poly.reads_step (poly.reads_step
    (poly.reads_step (poly.reads_step (poly.reads_step (poly.reads_step
    (poly.reads_step (poly.reads_step poly.reads_unit 16 0 N) 0 0 N) 0 0
    N) 0 0 N) 0 105 N) 0 0 N) 110 0 N) 0 0 N) 0 21 N) 0 0 N) ?_
  rw [hornerSqU N, hornerSqV N, ← Nat.add_assoc]
  exact (witSq_closed N).symm

/-- The difference polynomial reads the cleared sum at the occupied
  endpoints. -/
theorem diffClosedPoly_eval (N : Nat) (hN : 1 ≤ N) :
    (poly.eval diffClosedPoly (BPair.ofNat N)).oneValue
      (BPair.ofNat (105 * witDiffSq N)) := by
  refine poly.reads_ov (p := poly.eval diffClosedPoly (BPair.ofNat N))
    (poly.reads_step (poly.reads_step (poly.reads_step (poly.reads_step
    (poly.reads_step (poly.reads_step (poly.reads_step (poly.reads_step
    poly.reads_unit 44 0 N) 0 0 N) 0 147 N) 0 105 N) 126 0 N) 210 0 N) 0
    23 N) 0 105 N) ?_
  rw [hornerDiffU N, hornerDiffV N,
    ← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc]
  exact (witDiffSq_closed N hN).symm

/-- The square well part's polynomial reads the cleared sum at every
  endpoint. -/
theorem wellClosedPoly_eval (N : Nat) :
    (poly.eval wellClosedPoly (BPair.ofNat N)).oneValue
      (BPair.ofNat (6930 * witSqMM N)) := by
  refine poly.reads_ov (p := poly.eval wellClosedPoly (BPair.ofNat N))
    (poly.reads_step (poly.reads_step (poly.reads_step (poly.reads_step
    (poly.reads_step (poly.reads_step (poly.reads_step (poly.reads_step
    (poly.reads_step (poly.reads_step (poly.reads_step (poly.reads_step
    poly.reads_unit 80 0 N) 0 0 N) 0 0 N) 0 0 N) 0 1617 N) 0 0 N) 4015 0
    N) 0 0 N) 0 3003 N) 0 0 N) 525 0 N) 0 0 N) ?_
  rw [hornerWellU N, hornerWellV N, ← Nat.add_assoc]
  exact (witSqMM_closed N).symm

/-- The well part's top against the denominator's reads at the
scale's factor, the cross-multiplied identity. -/
theorem topWell_read (en ed r : Nat) :
    4 * en ^ 2 * 80 * 630 * (11 * (r + 1) * ed)
      = 6930 * (en * ed * (r + 1) * 16) * (20 * en) := by
  rw [sqRead en]
  exact monEq [en, ed, r + 1]
    (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4)
        (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.cst 80)) (Mon.cst 630))
      (Mon.mul (Mon.mul (Mon.cst 11) (Mon.var 2)) (Mon.var 1)))
    (Mon.mul (Mon.mul (Mon.cst 6930)
        (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
          (Mon.cst 16)))
      (Mon.mul (Mon.cst 20) (Mon.var 0)))
    (by decide +kernel) (by decide +kernel)

/-- The difference part's top against the denominator's reads, the
cross-multiplied identity. -/
theorem topDiff_read (en ed r : Nat) :
    (r + 1) * ed ^ 2 * 44 * 630 * (2 * en)
      = 105 * (en * ed * (r + 1) * 16) * (33 * ed) := by
  rw [sqRead ed]
  exact monEq [en, ed, r + 1]
    (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2)
        (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.cst 44)) (Mon.cst 630))
      (Mon.mul (Mon.cst 2) (Mon.var 0)))
    (Mon.mul (Mon.mul (Mon.cst 105)
        (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
          (Mon.cst 16)))
      (Mon.mul (Mon.cst 33) (Mon.var 1)))
    (by decide +kernel) (by decide +kernel)

/-- The tops' equality is the endpoint key's comparison, the two
sides one value at the scale's cleared members. -/
theorem keyEq_read (en ed r N : Nat) :
    20 * en * N ^ 2 * (2 * en * N ^ 2) = 363 * (r + 1) * ed ^ 2
      ↔ 40 * N ^ 4 * en ^ 2 = 363 * (r + 1) * ed ^ 2 := by
  have hm : 20 * en * N ^ 2 * (2 * en * N ^ 2) = 40 * N ^ 4 * en ^ 2 := by
    rw [sqRead N, quadRead N, sqRead en]
    exact monEq [en, N]
      (Mon.mul (Mon.mul (Mon.mul (Mon.cst 20) (Mon.var 0))
          (Mon.mul (Mon.var 1) (Mon.var 1)))
        (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0))
          (Mon.mul (Mon.var 1) (Mon.var 1))))
      (Mon.mul (Mon.mul (Mon.cst 40)
          (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1))
            (Mon.mul (Mon.var 1) (Mon.var 1))))
        (Mon.mul (Mon.var 0) (Mon.var 0)))
      (by decide +kernel) (by decide +kernel)
  exact ⟨fun h => hm.symm.trans h, fun h => hm.trans h⟩

/-- The family is vacant one depth past the endpoint. -/
private theorem witVal_top (N : Nat) : witVal N (N + 1) = 0 := by
  show (N + 1) * (N + 1) * (N * N - (N + 1) * (N + 1)) = 0
  rw [ground.subLe (N * N) ((N + 1) * (N + 1))
      (Nat.mul_le_mul (Nat.le_succ N) (Nat.le_succ N)),
    Nat.mul_zero]

/-- The square fold at the shifted depths against the fold at the
depths: the boundary square withdraws and the endpoint's joins. -/
private theorem witSq_shift (N : Nat) : ∀ n : Nat,
    ground.famFold Nat.add 0 (fun k => witVal N (k + 2) ^ 2) (List.range n)
        + witVal N 1 ^ 2
      = ground.famFold Nat.add 0 (fun k => witVal N (k + 1) ^ 2)
          (List.range n) + witVal N (n + 1) ^ 2
  | 0 => rfl
  | n + 1 => by
    rw [ground.range_succ n,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun k => witVal N (k + 2) ^ 2) (List.range n) [n],
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun k => witVal N (k + 1) ^ 2) (List.range n) [n]]
    show ground.famFold Nat.add 0 (fun k => witVal N (k + 2) ^ 2)
          (List.range n) + (witVal N (n + 2) ^ 2 + 0) + witVal N 1 ^ 2
      = ground.famFold Nat.add 0 (fun k => witVal N (k + 1) ^ 2)
          (List.range n) + (witVal N (n + 1) ^ 2 + 0)
        + witVal N (n + 1 + 1) ^ 2
    rw [Nat.add_zero (witVal N (n + 2) ^ 2),
      Nat.add_zero (witVal N (n + 1) ^ 2),
      Nat.add_right_comm
        (ground.famFold Nat.add 0 (fun k => witVal N (k + 2) ^ 2)
          (List.range n)) (witVal N (n + 2) ^ 2) (witVal N 1 ^ 2),
      witSq_shift N n,
      Nat.add_right_comm
        (ground.famFold Nat.add 0 (fun k => witVal N (k + 1) ^ 2)
          (List.range n)) (witVal N (n + 1) ^ 2) (witVal N (n + 2) ^ 2)]

/-- The telescope's count identity: the doubled square total against
the crossed total joins the doubled cross total, the boundary square
and the two shifted squares' total. -/
private theorem witTele_arith (N : Nat) :
    2 * witSq N
        + ground.famFold Nat.add 0 (fun k =>
            witVal N (k + 2) * witVal N (k + 1)
              + witVal N (k + 1) * witVal N (k + 2)) (List.range N)
      = 2 * ground.sumNat ((List.range N).map (fun k =>
            witVal N (k + 1) * witVal N (k + 2)))
          + witVal N 1 ^ 2
          + ground.famFold Nat.add 0 (fun k =>
              witVal N (k + 2) * witVal N (k + 2)
                + witVal N (k + 1) * witVal N (k + 1)) (List.range N) := by
  have hcross : ground.famFold Nat.add 0 (fun k =>
        witVal N (k + 2) * witVal N (k + 1)
          + witVal N (k + 1) * witVal N (k + 2)) (List.range N)
      = 2 * ground.sumNat ((List.range N).map (fun k =>
          witVal N (k + 1) * witVal N (k + 2))) := by
    rw [ground.famFold_congr_range _
        (fun k => witVal N (k + 1) * witVal N (k + 2)
          + witVal N (k + 1) * witVal N (k + 2)) N
        (fun i _ => by rw [Nat.mul_comm (witVal N (i + 2)) (witVal N (i +
          1))]),
      ground.famFold_add_split (fun k => witVal N (k + 1) * witVal N (k +
        2))
        (fun k => witVal N (k + 1) * witVal N (k + 2)) (List.range N),
      ground.sumMap, Nat.two_mul]
  have hsq : ground.famFold Nat.add 0 (fun k =>
        witVal N (k + 2) * witVal N (k + 2)
          + witVal N (k + 1) * witVal N (k + 1)) (List.range N)
      + witVal N 1 ^ 2 = 2 * witSq N := by
    rw [ground.famFold_congr_range _
        (fun k => witVal N (k + 2) ^ 2 + witVal N (k + 1) ^ 2) N
        (fun i _ => by
          rw [sqRead (witVal N (i + 2)), sqRead (witVal N (i + 1))]),
      ground.famFold_add_split (fun k => witVal N (k + 2) ^ 2)
        (fun k => witVal N (k + 1) ^ 2) (List.range N),
      Nat.add_right_comm
        (ground.famFold Nat.add 0 (fun k => witVal N (k + 2) ^ 2)
          (List.range N))
        (ground.famFold Nat.add 0 (fun k => witVal N (k + 1) ^ 2)
          (List.range N)) (witVal N 1 ^ 2),
      witSq_shift N N, witVal_top N, show (0 : Nat) ^ 2 = 0 from rfl,
      Nat.add_zero, witSq_read N, ground.sumMap, Nat.two_mul]
  rw [hcross, ← hsq, Nat.add_comm
      (ground.famFold Nat.add 0 (fun k =>
        witVal N (k + 2) * witVal N (k + 2)
          + witVal N (k + 1) * witVal N (k + 1)) (List.range N))
      (witVal N 1 ^ 2),
    Nat.add_right_comm (witVal N 1 ^ 2)
      (ground.famFold Nat.add 0 (fun k =>
        witVal N (k + 2) * witVal N (k + 2)
          + witVal N (k + 1) * witVal N (k + 1)) (List.range N))
      (2 * ground.sumNat ((List.range N).map (fun k =>
        witVal N (k + 1) * witVal N (k + 2)))),
    Nat.add_comm (witVal N 1 ^ 2)
      (2 * ground.sumNat ((List.range N).map (fun k =>
        witVal N (k + 1) * witVal N (k + 2))))]

/-- The telescope's core at the witness family: the doubled square
fold against the doubled cross fold with the boundary square and the
bond squares, the display's scale-free half at the cleared family. -/
theorem witTele (N : Nat) :
    (BPair.ofNat (2 * witSq N)).oneValue
      (BPair.ofNat (2 * ground.sumNat ((List.range N).map (fun k =>
          witVal N (k + 1) * witVal N (k + 2))))
        + BPair.ofNat (witVal N 1 ^ 2)
        + ground.bsum (fun k =>
            BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1))
              * BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1)))
          (List.range N)) := by
  have hb : (ground.bsum (fun k =>
        BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1))
          * BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1)))
      (List.range N)).oneValue
      (BPair.ofCounts
        (ground.famFold Nat.add 0 (fun k =>
          witVal N (k + 2) * witVal N (k + 2)
            + witVal N (k + 1) * witVal N (k + 1)) (List.range N))
        (ground.famFold Nat.add 0 (fun k =>
          witVal N (k + 2) * witVal N (k + 1)
            + witVal N (k + 1) * witVal N (k + 2)) (List.range N))) :=
    BPair.oneValue_trans
      (ground.foldB_congr_members _ _ (List.range N)
        (fun k _ => ofCounts_sq (witVal N (k + 2)) (witVal N (k + 1))))
      (BPair.oneValue_symm (ground.foldB_ofCounts _ _ (List.range N)))
  have hA : (BPair.ofNat (2 * ground.sumNat ((List.range N).map (fun k =>
        witVal N (k + 1) * witVal N (k + 2))))).oneValue
      (BPair.ofCounts (2 * ground.sumNat ((List.range N).map (fun k =>
        witVal N (k + 1) * witVal N (k + 2)))) 0) :=
    BPair.oneValue_symm (BPair.add_unit _)
  have hB : (BPair.ofNat (witVal N 1 ^ 2)).oneValue
      (BPair.ofCounts (witVal N 1 ^ 2) 0) :=
    BPair.oneValue_symm (BPair.add_unit _)
  have h0 : (BPair.ofNat (2 * witSq N)).oneValue
      (BPair.ofCounts (2 * witSq N) 0) :=
    BPair.oneValue_symm (BPair.add_unit _)
  have hmid : (BPair.ofCounts (2 * witSq N) 0).oneValue
      (BPair.ofCounts
        (2 * ground.sumNat ((List.range N).map (fun k =>
        witVal N (k + 1) * witVal N (k + 2)))
          + witVal N 1 ^ 2
          + (ground.famFold Nat.add 0 (fun k =>
        witVal N (k + 2) * witVal N (k + 2)
          + witVal N (k + 1) * witVal N (k + 1)) (List.range N)))
        (0 + 0 + (ground.famFold Nat.add 0 (fun k =>
        witVal N (k + 2) * witVal N (k + 1)
          + witVal N (k + 1) * witVal N (k + 2)) (List.range N)))) := by
    refine BPair.ofCounts_crossed ?_
    rw [Nat.zero_add 0, Nat.zero_add (ground.famFold Nat.add 0 (fun k =>
        witVal N (k + 2) * witVal N (k + 1)
          + witVal N (k + 1) * witVal N (k + 2)) (List.range N)),
      Nat.add_zero]
    exact witTele_arith N
  refine BPair.oneValue_trans h0 (BPair.oneValue_trans hmid ?_)
  refine BPair.oneValue_trans (BPair.ofCounts_add _ _ _ _) ?_
  exact BPair.add_congr
    (BPair.oneValue_trans (BPair.ofCounts_add _ _ _ _)
      (BPair.add_congr (BPair.oneValue_symm hA) (BPair.oneValue_symm hB)))
    (BPair.oneValue_symm hb)

/-- The square power reads the datum's own product. -/
private theorem bpowTwo (y : BPair) : (ground.bpow y 2).oneValue (y * y) :=
  BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.mul_congr (BPair.oneValue_refl y) (ground.bpow_one_read y))

/-- The diagonal's cleared evaluation at the clearing two: the band
read's clearing at the scale's square against the well's electric
member and the rate's balance partner. -/
private theorem diagRead (r qn qd m : Nat) (en ed : Pos) :
    (poly.evalClear (diagPoly r qn qd m) (BPair.ofPos en) ed 2).oneValue
      (BPair.ofNat 2 * (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed
            * BPair.ofPos ed)
        + (BPair.ofNat (4 * qd * (m * m + r * m)) * BPair.ofPos en
              * BPair.ofPos en
            + (BPair.ofNat ((r + 1) * qn) * BPair.ofPos en
                * BPair.ofPos ed).swap)) := by
  refine BPair.oneValue_trans
    (poly.evalClear_read (diagPoly r qn qd m) (BPair.ofPos en) ed 2) ?_
  show (BPair.ofNat (2 * ((r + 1) * qd))
        * ground.bpow (BPair.ofPos en) 0 * ground.bpow (BPair.ofPos ed) 2
      + ((BPair.ofNat ((r + 1) * qn)).swap
          * ground.bpow (BPair.ofPos en) 1 * ground.bpow (BPair.ofPos ed) 1
        + (BPair.ofNat (4 * qd * (m * m + r * m))
            * ground.bpow (BPair.ofPos en) 2
            * ground.bpow (BPair.ofPos ed) 0 + BPair.unit))).oneValue _
  refine BPair.add_congr ?_ ?_
  · refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.mul_congr (BPair.ofNat_mul 2 ((r + 1) * qd))
          (BPair.oneValue_refl (ground.bpow (BPair.ofPos en) 0)))
        (bpowTwo (BPair.ofPos ed))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.mul_one_read _)) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_assoc (BPair.ofNat 2) (BPair.ofNat ((r + 1) * qd))
        (BPair.ofPos ed * BPair.ofPos ed),
      BPair.mul_assoc (BPair.ofNat ((r + 1) * qd)) (BPair.ofPos ed)
        (BPair.ofPos ed)]
  · refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
    refine BPair.add_congr ?_ ?_
    · refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.mul_congr (BPair.oneValue_refl _)
            (bpowTwo (BPair.ofPos en)))
          (BPair.oneValue_refl (ground.bpow (BPair.ofPos ed) 0))) ?_
      refine BPair.oneValue_trans (BPair.mul_one_read _) ?_
      exact BPair.oneValue_of_eq
        (BPair.mul_assoc (BPair.ofNat (4 * qd * (m * m + r * m)))
          (BPair.ofPos en) (BPair.ofPos en)).symm
    · refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.mul_congr (BPair.oneValue_refl _)
            (ground.bpow_one_read (BPair.ofPos en)))
          (ground.bpow_one_read (BPair.ofPos ed))) ?_
      rw [BPair.swap_mul, BPair.swap_mul]
      exact BPair.oneValue_refl _

/-- The square fold at the family's cleared entries. -/
private theorem witSq_fold (N : Nat) :
    ground.famFold Nat.add 0
        (fun k => witVal N (k + 1) * witVal N (k + 1)) (List.range N)
      = witSq N := by
  rw [ground.famFold_congr_range _ (fun k => witVal N (k + 1) ^ 2) N
      (fun i _ => (sqRead (witVal N (i + 1))).symm),
    witSq_read N, ground.sumMap]

/-- The form-read display at the diagonal's cleared evaluation: the
diagonal fold at the family against the display's right side, the
well fold at the rate's balance carried inside the diagonal's own
evaluation, the bond weight the clearing constants' product at the
scale's square. -/
theorem witForm (r qn qd N : Nat) (en ed : Pos) :
    (ground.bsum (fun k =>
        poly.evalClear (diagPoly r qn qd (k + 1)) (BPair.ofPos en) ed 2
          * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1))))
      (List.range N)).oneValue
    (BPair.ofNat 2
        * (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed)
        * BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
            witVal N (k + 1) * witVal N (k + 2))))
      + BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
        * BPair.ofNat (witVal N 1 ^ 2)
      + BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
        * ground.bsum (fun k =>
            BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1))
              * BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1)))
          (List.range N)
      + ground.bsum (fun k =>
          (BPair.ofNat (4 * qd * ((k + 1) * (k + 1) + r * (k + 1)))
              * BPair.ofPos en * BPair.ofPos en
            + (BPair.ofNat ((r + 1) * qn) * BPair.ofPos en
                * BPair.ofPos ed).swap)
            * (BPair.ofNat (witVal N (k + 1))
                * BPair.ofNat (witVal N (k + 1))))
        (List.range N)) := by
  have hsplit := ground.foldB_add
    (fun k => BPair.ofNat 2
      * (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed)
      * (BPair.ofNat (witVal N (k + 1)) * BPair.ofNat (witVal N (k + 1))))
    (fun k => (BPair.ofNat (4 * qd * ((k + 1) * (k + 1) + r * (k + 1)))
        * BPair.ofPos en * BPair.ofPos en
      + (BPair.ofNat ((r + 1) * qn) * BPair.ofPos en
          * BPair.ofPos ed).swap)
      * (BPair.ofNat (witVal N (k + 1)) * BPair.ofNat (witVal N (k + 1))))
    (List.range N)
  have hstep : (ground.bsum (fun k =>
        poly.evalClear (diagPoly r qn qd (k + 1)) (BPair.ofPos en) ed 2
          * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1))))
      (List.range N)).oneValue
      (ground.bsum (fun k =>
        BPair.ofNat 2
            * (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed
              * BPair.ofPos ed)
            * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1)))
          + (BPair.ofNat (4 * qd * ((k + 1) * (k + 1) + r * (k + 1)))
                * BPair.ofPos en * BPair.ofPos en
              + (BPair.ofNat ((r + 1) * qn) * BPair.ofPos en
                  * BPair.ofPos ed).swap)
              * (BPair.ofNat (witVal N (k + 1))
                * BPair.ofNat (witVal N (k + 1))))
        (List.range N)) :=
    ground.foldB_congr_members _ _ (List.range N) (fun k _ =>
      BPair.oneValue_trans
        (BPair.mul_congr_left (diagRead r qn qd (k + 1) en ed))
        (BPair.oneValue_of_eq (BPair.right_distrib _ _ _)))
  have hscal : (ground.bsum (fun k =>
        BPair.ofNat 2
          * (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed)
          * (BPair.ofNat (witVal N (k + 1))
            * BPair.ofNat (witVal N (k + 1)))) (List.range N)).oneValue
      (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
        * BPair.ofNat (2 * witSq N)) := by
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => BPair.ofNat (witVal N (k + 1) * witVal N (k + 1))
          * (BPair.ofNat 2
            * (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed
              * BPair.ofPos ed))) (List.range N) (fun k _ => ?_)) ?_
    · refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm
            (BPair.ofNat_mul (witVal N (k + 1)) (witVal N (k + 1))))) ?_
      exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
    · refine BPair.oneValue_trans
        (ground.bsum_scalar (fun k => witVal N (k + 1) * witVal N (k + 1))
          (BPair.ofNat 2
            * (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed
              * BPair.ofPos ed)) (List.range N)) ?_
      rw [witSq_fold N]
      refine BPair.oneValue_trans ?_
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (BPair.ofNat_mul 2 (witSq N))))
      refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_assoc (BPair.ofNat ((r + 1) * qd)) (BPair.ofPos ed)
          (BPair.ofPos ed),
        BPair.mul_comm (BPair.ofNat (witSq N))
          (BPair.ofNat 2 * (BPair.ofNat ((r + 1) * qd)
            * (BPair.ofPos ed * BPair.ofPos ed))),
        BPair.mul_assoc (BPair.ofNat 2)
          (BPair.ofNat ((r + 1) * qd) * (BPair.ofPos ed * BPair.ofPos ed))
          (BPair.ofNat (witSq N)),
        BPair.mul_left_comm (BPair.ofNat 2)
          (BPair.ofNat ((r + 1) * qd) * (BPair.ofPos ed * BPair.ofPos ed))
          (BPair.ofNat (witSq N))]
  have htele : (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
        * BPair.ofNat (2 * witSq N)).oneValue
      (BPair.ofNat 2
          * (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed)
          * BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
              witVal N (k + 1) * witVal N (k + 2))))
        + BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
          * BPair.ofNat (witVal N 1 ^ 2)
        + BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed
          * ground.bsum (fun k =>
              BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1))
                * BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1)))
            (List.range N)) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (witTele N)) ?_
    rw [BPair.left_distrib, BPair.left_distrib]
    refine BPair.add_congr (BPair.add_congr ?_ (BPair.oneValue_refl _))
      (BPair.oneValue_refl _)
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.ofNat_mul 2 (ground.sumNat ((List.range N).map (fun k =>
          witVal N (k + 1) * witVal N (k + 2)))))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_left_comm
        (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed)
        (BPair.ofNat 2)
        (BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
          witVal N (k + 1) * witVal N (k + 2))))),
      ← BPair.mul_assoc (BPair.ofNat 2)
        (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed)
        (BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
          witVal N (k + 1) * witVal N (k + 2)))))]
  exact BPair.oneValue_trans hstep
    (BPair.oneValue_trans hsplit
      (BPair.add_congr (BPair.oneValue_trans hscal htele)
        (BPair.oneValue_refl _)))

/-- The bond square's per-depth read in the depth and the gap. -/
private theorem bondCore (m G : Nat) :
    ((m + 1) * (m + 1) * G) * ((m + 1) * (m + 1) * G) + (m * m * (G + (2 *
      m + 1))) * (m * m * (G + (2 * m + 1))) + (2 * m + 1) ^ 2 * (2 * ((m
      + 1) * (m + 1) + G) * (2 * m * m + 2 * m + 1))
      = (2 * m + 1) ^ 2 * (((m + 1) * (m + 1) + G) * ((m + 1) * (m + 1) +
        G) + (2 * m * m + 2 * m + 1) * (2 * m * m + 2 * m + 1)) + 2 * ((m
        + 1) * (m + 1) * G) * (m * m * (G + (2 * m + 1))) :=
  mirEq m G (Mir.add (Mir.add (Mir.mul (Mir.mul (Mir.mul (Mir.add Mir.x
    (Mir.cst 1)) (Mir.add Mir.x (Mir.cst 1))) Mir.y) (Mir.mul (Mir.mul
    (Mir.add Mir.x (Mir.cst 1)) (Mir.add Mir.x (Mir.cst 1))) Mir.y))
    (Mir.mul (Mir.mul (Mir.mul Mir.x Mir.x) (Mir.add Mir.y (Mir.add
    (Mir.mul (Mir.cst 2) Mir.x) (Mir.cst 1)))) (Mir.mul (Mir.mul Mir.x
    Mir.x) (Mir.add Mir.y (Mir.add (Mir.mul (Mir.cst 2) Mir.x) (Mir.cst
    1)))))) (Mir.mul (Mir.pow (Mir.add (Mir.mul (Mir.cst 2) Mir.x)
    (Mir.cst 1)) 2) (Mir.mul (Mir.mul (Mir.cst 2) (Mir.add (Mir.mul
    (Mir.add Mir.x (Mir.cst 1)) (Mir.add Mir.x (Mir.cst 1))) Mir.y))
    (Mir.add (Mir.add (Mir.mul (Mir.mul (Mir.cst 2) Mir.x) Mir.x) (Mir.mul
    (Mir.cst 2) Mir.x)) (Mir.cst 1))))) (Mir.add (Mir.mul (Mir.pow
    (Mir.add (Mir.mul (Mir.cst 2) Mir.x) (Mir.cst 1)) 2) (Mir.add (Mir.mul
    (Mir.add (Mir.mul (Mir.add Mir.x (Mir.cst 1)) (Mir.add Mir.x (Mir.cst
    1))) Mir.y) (Mir.add (Mir.mul (Mir.add Mir.x (Mir.cst 1)) (Mir.add
    Mir.x (Mir.cst 1))) Mir.y)) (Mir.mul (Mir.add (Mir.add (Mir.mul
    (Mir.mul (Mir.cst 2) Mir.x) Mir.x) (Mir.mul (Mir.cst 2) Mir.x))
    (Mir.cst 1)) (Mir.add (Mir.add (Mir.mul (Mir.mul (Mir.cst 2) Mir.x)
    Mir.x) (Mir.mul (Mir.cst 2) Mir.x)) (Mir.cst 1))))) (Mir.mul (Mir.mul
    (Mir.cst 2) (Mir.mul (Mir.mul (Mir.add Mir.x (Mir.cst 1)) (Mir.add
    Mir.x (Mir.cst 1))) Mir.y)) (Mir.mul (Mir.mul Mir.x Mir.x) (Mir.add
    Mir.y (Mir.add (Mir.mul (Mir.cst 2) Mir.x) (Mir.cst 1)))))) (by decide +kernel)

/-- The successor's square at the depth's own. -/
private theorem succSq (m : Nat) :
    (m + 1) * (m + 1)
      = m * m + (2 * m + 1) :=
  mirEq m 0 (Mir.mul (Mir.add Mir.x (Mir.cst 1)) (Mir.add Mir.x (Mir.cst
    1))) (Mir.add (Mir.mul Mir.x Mir.x) (Mir.add (Mir.mul (Mir.cst 2)
    Mir.x) (Mir.cst 1))) (by decide +kernel)

/-- The bond square's per-depth read at a stated scale square. -/
private theorem bondCoreGap (m G NN : Nat) (h : (m + 1) * (m + 1) + G = NN)
  :
    (m + 1) * (m + 1) * G * ((m + 1) * (m + 1) * G)
        + m * m * (G + (2 * m + 1)) * (m * m * (G + (2 * m + 1)))
        + (2 * m + 1) ^ 2 * (2 * NN * (2 * m * m + 2 * m + 1))
      = (2 * m + 1) ^ 2
          * (NN * NN + (2 * m * m + 2 * m + 1) * (2 * m * m + 2 * m + 1))
        + 2 * ((m + 1) * (m + 1) * G) * (m * m * (G + (2 * m + 1))) := by
  rw [← h]
  exact bondCore m G
/-- The bond square at a depth inside the endpoint reads the
displayed pair's square. -/
private theorem bondSq (N m : Nat) (h : m + 1 ≤ N) :
    marg (witVal N (m + 1)) (witVal N m) ^ 2
      = ((2 * m + 1) * marg (N * N) (2 * m * m + 2 * m + 1)) ^ 2 := by
  have hG : (m + 1) * (m + 1) + (N * N - (m + 1) * (m + 1)) = N * N :=
    (Nat.add_comm _ _).trans (ground.subAdd (Nat.mul_le_mul h h))
  have hsum : m * m + (N * N - (m + 1) * (m + 1) + (2 * m + 1)) = N * N :=
    by
    rw [Nat.add_comm (N * N - (m + 1) * (m + 1)) (2 * m + 1),
      ← Nat.add_assoc (m * m) (2 * m + 1) (N * N - (m + 1) * (m + 1)),
      ← succSq m]
    exact hG
  have hgap : N * N - m * m = N * N - (m + 1) * (m + 1) + (2 * m + 1) :=
    (congrArg (fun t => t - m * m) hsum).symm.trans
      (ground.addSubSelfL (m * m) _)
  have hw : witVal N m
      = m * m * (N * N - (m + 1) * (m + 1) + (2 * m + 1)) := by
    show m * m * (N * N - m * m) = _
    rw [hgap]
  have hw' : witVal N (m + 1)
      = (m + 1) * (m + 1) * (N * N - (m + 1) * (m + 1)) := rfl
  have e1 := margSqNat (witVal N (m + 1)) (witVal N m)
  have e2 := margSqNat (N * N) (2 * m * m + 2 * m + 1)
  refine ground.addCancelR
    (2 * witVal N (m + 1) * witVal N m
      + (2 * m + 1) ^ 2 * (2 * (N * N) * (2 * m * m + 2 * m + 1))) ?_
  rw [← Nat.add_assoc
      (marg (witVal N (m + 1)) (witVal N m) ^ 2)
      (2 * witVal N (m + 1) * witVal N m)
      ((2 * m + 1) ^ 2 * (2 * (N * N) * (2 * m * m + 2 * m + 1))),
    ← Nat.add_assoc
      (((2 * m + 1) * marg (N * N) (2 * m * m + 2 * m + 1)) ^ 2)
      (2 * witVal N (m + 1) * witVal N m)
      ((2 * m + 1) ^ 2 * (2 * (N * N) * (2 * m * m + 2 * m + 1))),
    e1,
    mulSq (2 * m + 1) (marg (N * N) (2 * m * m + 2 * m + 1)),
    Nat.add_right_comm
      ((2 * m + 1) ^ 2 * marg (N * N) (2 * m * m + 2 * m + 1) ^ 2)
      (2 * witVal N (m + 1) * witVal N m)
      ((2 * m + 1) ^ 2 * (2 * (N * N) * (2 * m * m + 2 * m + 1))),
    ← Nat.left_distrib ((2 * m + 1) ^ 2)
      (marg (N * N) (2 * m * m + 2 * m + 1) ^ 2)
      (2 * (N * N) * (2 * m * m + 2 * m + 1)),
    e2, hw, hw']
  exact bondCoreGap m (N * N - (m + 1) * (m + 1)) (N * N) hG

/-- The family is vacant at the endpoint itself. -/
private theorem witVal_diag (N : Nat) : witVal N N = 0 := by
  show N * N * (N * N - N * N) = 0
  rw [ground.subLe (N * N) (N * N) (Nat.le_refl (N * N)), Nat.mul_zero]

/-- The family's first depth reads the scale square's predecessor. -/
private theorem witVal_one (N : Nat) : witVal N 1 = N * N - 1 := by
  show 1 * 1 * (N * N - 1 * 1) = N * N - 1
  rw [Nat.mul_one 1, Nat.one_mul (N * N - 1)]

/-- The bond squares' fold reads the difference sum. -/
private theorem bondFold : ∀ N : Nat,
    ground.famFold Nat.add 0
        (fun k => marg (witVal N (k + 2)) (witVal N (k + 1)) ^ 2)
        (List.range N)
      = witDiffSq N
  | 0 => rfl
  | n + 1 => by
    have hlast : marg (witVal (n + 1) (n + 2)) (witVal (n + 1) (n + 1)) ^ 2
        = 0 := by
      rw [show witVal (n + 1) (n + 2) = 0 from witVal_top (n + 1),
        show witVal (n + 1) (n + 1) = 0 from witVal_diag (n + 1)]
      rfl
    rw [ground.range_succ n,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun k => marg (witVal (n + 1) (k + 2))
          (witVal (n + 1) (k + 1)) ^ 2) (List.range n) [n]]
    show ground.famFold Nat.add 0
        (fun k => marg (witVal (n + 1) (k + 2))
          (witVal (n + 1) (k + 1)) ^ 2) (List.range n)
        + (marg (witVal (n + 1) (n + 2)) (witVal (n + 1) (n + 1)) ^ 2 + 0)
      = witDiffSq (n + 1)
    rw [hlast, Nat.add_zero 0, Nat.add_zero,
      ground.famFold_congr_range _
        (fun k => ((2 * (k + 1) + 1) * marg ((n + 1) * (n + 1))
          (2 * (k + 1) * (k + 1) + 2 * (k + 1) + 1)) ^ 2) n
        (fun i hi => bondSq (n + 1) (i + 1) (Nat.succ_le_succ hi))]
    show _ = ground.sumNat ((List.range n).map (fun k =>
      ((2 * (k + 1) + 1) * marg ((n + 1) * (n + 1))
        (2 * (k + 1) * (k + 1) + 2 * (k + 1) + 1)) ^ 2))
    exact (ground.sumMap _ (List.range n)).symm

/-- The well fold at the rate's balance: the depth's square and
linear weights against the family's squares. -/
private theorem wellFold (qd r N : Nat) :
    ground.famFold Nat.add 0 (fun k =>
        4 * qd * ((k + 1) * (k + 1) + r * (k + 1))
          * (witVal N (k + 1) * witVal N (k + 1))) (List.range N)
      = 4 * qd * (witSqMM N + r * witSqM N) := by
  rw [ground.famFold_congr_range _
      (fun k => 4 * qd * ((k + 1) * (k + 1) * witVal N (k + 1) ^ 2
        + r * ((k + 1) * witVal N (k + 1) ^ 2))) N (fun i _ => by
        rw [ground.mulAssoc (4 * qd)
            ((i + 1) * (i + 1) + r * (i + 1))
            (witVal N (i + 1) * witVal N (i + 1)),
          ground.mulAddR ((i + 1) * (i + 1)) (r * (i + 1))
            (witVal N (i + 1) * witVal N (i + 1)),
          ground.mulAssoc r (i + 1)
            (witVal N (i + 1) * witVal N (i + 1)),
          ← sqRead (witVal N (i + 1))]),
    ← ground.famFold_mul (4 * qd)
      (fun k => (k + 1) * (k + 1) * witVal N (k + 1) ^ 2
        + r * ((k + 1) * witVal N (k + 1) ^ 2)) (List.range N),
    ground.famFold_add_split
      (fun k => (k + 1) * (k + 1) * witVal N (k + 1) ^ 2)
      (fun k => r * ((k + 1) * witVal N (k + 1) ^ 2)) (List.range N),
    ← ground.famFold_mul r (fun k => (k + 1) * witVal N (k + 1) ^ 2)
      (List.range N),
    witSqMM_read N, witSqM_read N, ground.sumMap, ground.sumMap]

private theorem qLowNum_read (e d r N : Nat) :
    qLowNum e d r N
      = 4 * e ^ 2 * (witSqMM N + r * witSqM N)
        + (r + 1) * d ^ 2 * (witDiffSq N + (N * N - 1) ^ 2) := rfl

private theorem qLowDen_read (e d r N : Nat) :
    qLowDen e d r N = e * d * (r + 1) * witSq N := rfl

/-- The lower rate's defining identity at the cleared data: the
difference and boundary squares against the well's own weights. -/
private theorem kernelCore (e d R S A T : Nat) :
    R * (e * d * R * S) * d * d * T + 4 * (e * d * R * S) * A * (e * e)
      = S * (R * (4 * (e * e) * A + R * (d * d) * T) * e * d) := by
  have m1 : R * (e * d * R * S) * d * d * T
      = S * (R * (R * (d * d) * T) * e * d) :=
    monEq [e, d, R, S, T]
      (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2)
          (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
            (Mon.var 3))) (Mon.var 1)) (Mon.var 1)) (Mon.var 4))
      (Mon.mul (Mon.var 3)
        (Mon.mul (Mon.mul (Mon.mul (Mon.var 2)
            (Mon.mul (Mon.mul (Mon.var 2) (Mon.mul (Mon.var 1) (Mon.var 1)))
              (Mon.var 4))) (Mon.var 0)) (Mon.var 1)))
      (by decide +kernel) (by decide +kernel)
  have m2 : 4 * (e * d * R * S) * A * (e * e)
      = S * (R * (4 * (e * e) * A) * e * d) :=
    monEq [e, d, R, S, A]
      (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4)
          (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
            (Mon.var 3))) (Mon.var 4)) (Mon.mul (Mon.var 0) (Mon.var 0)))
      (Mon.mul (Mon.var 3)
        (Mon.mul (Mon.mul (Mon.mul (Mon.var 2)
            (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.var 0) (Mon.var 0)))
              (Mon.var 4))) (Mon.var 0)) (Mon.var 1)))
      (by decide +kernel) (by decide +kernel)
  have hd : S * (R * (4 * (e * e) * A + R * (d * d) * T) * e * d)
      = S * (R * (4 * (e * e) * A) * e * d)
        + S * (R * (R * (d * d) * T) * e * d) := by
    rw [Nat.left_distrib R (4 * (e * e) * A) (R * (d * d) * T),
      ground.mulAddR (R * (4 * (e * e) * A)) (R * (R * (d * d) * T)) e,
      ground.mulAddR (R * (4 * (e * e) * A) * e)
        (R * (R * (d * d) * T) * e) d,
      Nat.left_distrib S (R * (4 * (e * e) * A) * e * d)
        (R * (R * (d * d) * T) * e * d)]
  rw [hd, m1, m2, Nat.add_comm (S * (R * (4 * (e * e) * A) * e * d))
    (S * (R * (R * (d * d) * T) * e * d))]

/-- The kernel's count identity at the lower rate's data. -/
private theorem kernelArith (e d r S A D B : Nat) :
    (r + 1) * (e * d * (r + 1) * S) * d * d * B
        + (r + 1) * (e * d * (r + 1) * S) * d * d * D
        + 4 * (e * d * (r + 1) * S) * A * (e * e)
      = S * ((r + 1) * (4 * (e * e) * A + (r + 1) * (d * d) * (D + B))
          * e * d) := by
  rw [← Nat.left_distrib ((r + 1) * (e * d * (r + 1) * S) * d * d) B D,
    Nat.add_comm B D]
  exact kernelCore e d (r + 1) S A (D + B)

private theorem collect2 (a b : Nat) :
    (BPair.ofNat a * BPair.ofNat b).oneValue (BPair.ofNat (a * b)) :=
  BPair.oneValue_symm (BPair.ofNat_mul a b)

private theorem collect3 (a b c : Nat) :
    (BPair.ofNat a * BPair.ofNat b * BPair.ofNat c).oneValue
      (BPair.ofNat (a * b * c)) :=
  BPair.oneValue_trans (BPair.mul_congr_left (collect2 a b))
    (collect2 (a * b) c)

private theorem collect4 (a b c x : Nat) :
    (BPair.ofNat a * BPair.ofNat b * BPair.ofNat c
        * BPair.ofNat x).oneValue (BPair.ofNat (a * b * c * x)) :=
  BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.mul_congr_left (collect2 a b)))
    (BPair.oneValue_trans (BPair.mul_congr_left (collect2 (a * b) c))
      (collect2 (a * b * c) x))

/-- The bond squares' fold reads the difference sum at the balance
carrier. -/
private theorem bsumBond (N : Nat) :
    (ground.bsum (fun k =>
        BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1))
          * BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1)))
      (List.range N)).oneValue (BPair.ofNat (witDiffSq N)) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => BPair.ofNat (marg (witVal N (k + 2))
        (witVal N (k + 1)) ^ 2)) (List.range N)
      (fun k _ => BPair.oneValue_symm
        (margSq_read (witVal N (k + 2)) (witVal N (k + 1))))) ?_
  rw [← bondFold N]
  exact BPair.oneValue_symm (ground.ofNat_famFold _ (List.range N))

/-- The kernel read at the lower rate's own data: the display's two
sides join at the family, the well fold withdrawing against the
difference and boundary squares at the rate's definitional tie. -/
theorem witKernel (en ed : Pos) (r N : Nat) :
    (ground.bsum (fun k =>
        poly.evalClear
          (diagPoly r (qLowNum (ground.posVal en) (ground.posVal ed) r N)
            (qLowDen (ground.posVal en) (ground.posVal ed) r N) (k + 1))
          (BPair.ofPos en) ed 2
          * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1))))
      (List.range N)).oneValue
    (BPair.ofNat 2
      * (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal en) (ground.posVal
        ed) r N))
          * BPair.ofPos ed * BPair.ofPos ed)
      * BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
          witVal N (k + 1) * witVal N (k + 2))))) := by
  have hT2 : (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal en)
    (ground.posVal ed) r N)) * BPair.ofPos ed
        * BPair.ofPos ed * BPair.ofNat (witVal N 1 ^ 2)).oneValue
      (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal en) (ground.posVal ed)
        r N) * (ground.posVal ed) * (ground.posVal ed)
        * (N * N - 1) ^ 2)) := by
    rw [BPair.ofPos_val ed, witVal_one N]
    exact collect4 ((r + 1) * (qLowDen (ground.posVal en) (ground.posVal ed)
      r N)) (ground.posVal ed) (ground.posVal ed) ((N * N - 1) ^ 2)
  have hT3 : (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal en)
    (ground.posVal ed) r N)) * BPair.ofPos ed
        * BPair.ofPos ed
        * ground.bsum (fun k =>
            BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1))
              * BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1)))
          (List.range N)).oneValue
      (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal en) (ground.posVal ed)
        r N) * (ground.posVal ed) * (ground.posVal ed)
        * witDiffSq N)) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (bsumBond N)) ?_
    rw [BPair.ofPos_val ed]
    exact collect4 ((r + 1) * (qLowDen (ground.posVal en) (ground.posVal ed)
      r N)) (ground.posVal ed) (ground.posVal ed) (witDiffSq N)
  have hT4a : (ground.bsum (fun k =>
        BPair.ofNat (4 * (qLowDen (ground.posVal en) (ground.posVal ed) r N)
          * ((k + 1) * (k + 1) + r * (k + 1)))
            * BPair.ofPos en * BPair.ofPos en
          * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1)))) (List.range N)).oneValue
      (BPair.ofNat (4 * (qLowDen (ground.posVal en) (ground.posVal ed) r N)
        * (witSqMM N + r * witSqM N) * ((ground.posVal en) * (ground.posVal
        en)))) := by
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => BPair.ofNat (4 * (qLowDen (ground.posVal en)
          (ground.posVal ed) r N)
            * ((k + 1) * (k + 1) + r * (k + 1))
            * (witVal N (k + 1) * witVal N (k + 1)))
          * (BPair.ofNat (ground.posVal en) * BPair.ofNat (ground.posVal
            en)))
        (List.range N) (fun k _ => ?_)) ?_
    · rw [BPair.ofPos_val en]
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (collect2 (witVal N (k + 1)) (witVal N (k + 1)))) ?_
      refine BPair.oneValue_trans (BPair.oneValue_of_eq ?_)
        (BPair.mul_congr_left
          (collect2 (4 * (qLowDen (ground.posVal en) (ground.posVal ed) r N)
            * ((k + 1) * (k + 1) + r * (k + 1)))
            (witVal N (k + 1) * witVal N (k + 1))))
      rw [BPair.mul_assoc (BPair.ofNat (4 * (qLowDen (ground.posVal en)
        (ground.posVal ed) r N)
            * ((k + 1) * (k + 1) + r * (k + 1)))) (BPair.ofNat
              (ground.posVal en)) (BPair.ofNat (ground.posVal en)),
        BPair.mul_assoc (BPair.ofNat (4 * (qLowDen (ground.posVal en)
          (ground.posVal ed) r N)
            * ((k + 1) * (k + 1) + r * (k + 1))))
          (BPair.ofNat (ground.posVal en) * BPair.ofNat (ground.posVal en))
          (BPair.ofNat (witVal N (k + 1) * witVal N (k + 1))),
        BPair.mul_comm (BPair.ofNat (ground.posVal en) * BPair.ofNat
          (ground.posVal en))
          (BPair.ofNat (witVal N (k + 1) * witVal N (k + 1))),
        ← BPair.mul_assoc (BPair.ofNat (4 * (qLowDen (ground.posVal en)
          (ground.posVal ed) r N)
            * ((k + 1) * (k + 1) + r * (k + 1))))
          (BPair.ofNat (witVal N (k + 1) * witVal N (k + 1)))
          (BPair.ofNat (ground.posVal en) * BPair.ofNat (ground.posVal en))]
    · refine BPair.oneValue_trans
        (ground.bsum_scalar (fun k => 4 * (qLowDen (ground.posVal en)
          (ground.posVal ed) r N)
            * ((k + 1) * (k + 1) + r * (k + 1))
            * (witVal N (k + 1) * witVal N (k + 1)))
          (BPair.ofNat (ground.posVal en) * BPair.ofNat (ground.posVal en))
            (List.range N)) ?_
      rw [wellFold (qLowDen (ground.posVal en) (ground.posVal ed) r N) r N]
      exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) (collect2 (ground.posVal
          en) (ground.posVal en)))
        (collect2 (4 * (qLowDen (ground.posVal en) (ground.posVal ed) r N) *
          (witSqMM N + r * witSqM N)) ((ground.posVal en) * (ground.posVal
          en)))
  have hT4b : (ground.bsum (fun k =>
        (BPair.ofNat ((r + 1) * (qLowNum (ground.posVal en) (ground.posVal
          ed) r N)) * BPair.ofPos en
            * BPair.ofPos ed).swap
          * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1)))) (List.range N)).oneValue
      (BPair.ofNat (witSq N * ((r + 1) * (qLowNum (ground.posVal en)
        (ground.posVal ed) r N) * (ground.posVal en) * (ground.posVal
        ed)))).swap := by
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => BPair.ofNat (witVal N (k + 1) * witVal N (k + 1))
          * (BPair.ofNat ((r + 1) * (qLowNum (ground.posVal en)
            (ground.posVal ed) r N)) * BPair.ofPos en
              * BPair.ofPos ed).swap)
        (List.range N) (fun k _ =>
          BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _)
              (collect2 (witVal N (k + 1)) (witVal N (k + 1))))
            (BPair.oneValue_of_eq (BPair.mul_comm _ _)))) ?_
    refine BPair.oneValue_trans
      (ground.bsum_scalar (fun k => witVal N (k + 1) * witVal N (k + 1))
        ((BPair.ofNat ((r + 1) * (qLowNum (ground.posVal en) (ground.posVal
          ed) r N)) * BPair.ofPos en
          * BPair.ofPos ed).swap) (List.range N)) ?_
    rw [witSq_fold N, BPair.ofPos_val en, BPair.ofPos_val ed,
      BPair.mul_swap]
    refine ground.swap_congr ?_
    exact BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (collect3 ((r + 1) * (qLowNum (ground.posVal en) (ground.posVal ed)
          r N)) (ground.posVal en) (ground.posVal ed)))
      (collect2 (witSq N) ((r + 1) * (qLowNum (ground.posVal en)
        (ground.posVal ed) r N) * (ground.posVal en) * (ground.posVal ed)))
  have hT4 : (ground.bsum (fun k =>
        (BPair.ofNat (4 * (qLowDen (ground.posVal en) (ground.posVal ed) r
          N) * ((k + 1) * (k + 1) + r * (k + 1)))
            * BPair.ofPos en * BPair.ofPos en
          + (BPair.ofNat ((r + 1) * (qLowNum (ground.posVal en)
            (ground.posVal ed) r N)) * BPair.ofPos en
              * BPair.ofPos ed).swap)
          * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1))))
      (List.range N)).oneValue
      (BPair.ofNat (4 * (qLowDen (ground.posVal en) (ground.posVal ed) r N)
        * (witSqMM N + r * witSqM N) * ((ground.posVal en) * (ground.posVal
        en))) + (BPair.ofNat (witSq N * ((r + 1) * (qLowNum (ground.posVal
        en) (ground.posVal ed) r N) * (ground.posVal en) * (ground.posVal
        ed)))).swap) := by
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => BPair.ofNat (4 * (qLowDen (ground.posVal en)
          (ground.posVal ed) r N)
              * ((k + 1) * (k + 1) + r * (k + 1)))
            * BPair.ofPos en * BPair.ofPos en
            * (BPair.ofNat (witVal N (k + 1))
                * BPair.ofNat (witVal N (k + 1)))
          + (BPair.ofNat ((r + 1) * (qLowNum (ground.posVal en)
            (ground.posVal ed) r N)) * BPair.ofPos en
                * BPair.ofPos ed).swap
              * (BPair.ofNat (witVal N (k + 1))
                  * BPair.ofNat (witVal N (k + 1))))
        (List.range N)
        (fun _ _ => BPair.oneValue_of_eq (BPair.right_distrib _ _ _))) ?_
    exact BPair.oneValue_trans (ground.foldB_add _ _ (List.range N))
      (BPair.add_congr hT4a hT4b)
  have harith : (r + 1) * (qLowDen (ground.posVal en) (ground.posVal ed) r
    N) * (ground.posVal ed) * (ground.posVal ed) * (N * N - 1) ^ 2 + ((r +
    1) * (qLowDen (ground.posVal en) (ground.posVal ed) r N) *
    (ground.posVal ed) * (ground.posVal ed) * witDiffSq N + 4 * (qLowDen
    (ground.posVal en) (ground.posVal ed) r N) * (witSqMM N + r * witSqM N)
    * ((ground.posVal en) * (ground.posVal en))) = witSq N * ((r + 1) *
    (qLowNum (ground.posVal en) (ground.posVal ed) r N) * (ground.posVal en)
    * (ground.posVal ed)) := by
    rw [← Nat.add_assoc, qLowDen_read, qLowNum_read, sqRead (ground.posVal
      en),
      sqRead (ground.posVal ed)]
    exact kernelArith (ground.posVal en) (ground.posVal ed) r (witSq N)
      (witSqMM N + r * witSqM N) (witDiffSq N)
      ((N * N - 1) ^ 2)
  have hzero : (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal en)
    (ground.posVal ed) r N)) * BPair.ofPos ed * BPair.ofPos ed
        * BPair.ofNat (witVal N 1 ^ 2)
      + (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal en) (ground.posVal
        ed) r N)) * BPair.ofPos ed * BPair.ofPos ed
        * ground.bsum (fun k =>
            BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1))
              * BPair.ofCounts (witVal N (k + 2)) (witVal N (k + 1)))
          (List.range N)
        + ground.bsum (fun k =>
          (BPair.ofNat (4 * (qLowDen (ground.posVal en) (ground.posVal ed) r
            N) * ((k + 1) * (k + 1) + r * (k + 1)))
              * BPair.ofPos en * BPair.ofPos en
            + (BPair.ofNat ((r + 1) * (qLowNum (ground.posVal en)
              (ground.posVal ed) r N)) * BPair.ofPos en
                * BPair.ofPos ed).swap)
            * (BPair.ofNat (witVal N (k + 1))
                * BPair.ofNat (witVal N (k + 1))))
        (List.range N))).oneValue BPair.unit := by
    refine BPair.oneValue_trans
      (BPair.add_congr hT2 (BPair.add_congr hT3 hT4)) ?_
    rw [← BPair.add_assoc (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal
      en) (ground.posVal ed) r N) * (ground.posVal ed) * (ground.posVal ed)
      * witDiffSq N)) (BPair.ofNat (4 * (qLowDen (ground.posVal en)
      (ground.posVal ed) r N) * (witSqMM N + r * witSqM N) * ((ground.posVal
      en) * (ground.posVal en))))
          (BPair.ofNat (witSq N * ((r + 1) * (qLowNum (ground.posVal en)
            (ground.posVal ed) r N) * (ground.posVal en) * (ground.posVal
            ed)))).swap,
        ← BPair.add_assoc (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal
          en) (ground.posVal ed) r N) * (ground.posVal ed) * (ground.posVal
          ed) * (N * N - 1) ^ 2))
          (BPair.ofNat ((r + 1) * (qLowDen (ground.posVal en) (ground.posVal
            ed) r N) * (ground.posVal ed) * (ground.posVal ed) * witDiffSq
            N) + BPair.ofNat (4 * (qLowDen (ground.posVal en) (ground.posVal
            ed) r N) * (witSqMM N + r * witSqM N) * ((ground.posVal en) *
            (ground.posVal en))))
          (BPair.ofNat (witSq N * ((r + 1) * (qLowNum (ground.posVal en)
            (ground.posVal ed) r N) * (ground.posVal en) * (ground.posVal
            ed)))).swap]
    refine BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.oneValue_refl (BPair.ofNat ((r + 1) *
              (qLowDen (ground.posVal en) (ground.posVal ed) r N) *
              (ground.posVal ed) * (ground.posVal ed) * (N * N - 1) ^ 2)))
              (BPair.oneValue_symm (BPair.ofNat_add ((r + 1) * (qLowDen
                (ground.posVal en) (ground.posVal ed) r N) * (ground.posVal
                ed) * (ground.posVal ed) * witDiffSq N) (4 * (qLowDen
                (ground.posVal en) (ground.posVal ed) r N) * (witSqMM N + r
                * witSqM N) * ((ground.posVal en) * (ground.posVal en))))))
            (BPair.oneValue_symm
              (BPair.ofNat_add ((r + 1) * (qLowDen (ground.posVal en)
                (ground.posVal ed) r N) * (ground.posVal ed) *
                (ground.posVal ed) * (N * N - 1) ^ 2) ((r + 1) * (qLowDen
                (ground.posVal en) (ground.posVal ed) r N) * (ground.posVal
                ed) * (ground.posVal ed) * witDiffSq N + (4 * (qLowDen
                (ground.posVal en) (ground.posVal ed) r N) * (witSqMM N + r
                * witSqM N) * ((ground.posVal en) * (ground.posVal en)))))))
          (BPair.oneValue_refl (BPair.ofNat (witSq N * ((r + 1) * (qLowNum
            (ground.posVal en) (ground.posVal ed) r N) * (ground.posVal en)
            * (ground.posVal ed)))).swap)) ?_
    exact BPair.ofCounts_unit.mpr harith
  refine BPair.oneValue_trans (witForm r (qLowNum (ground.posVal en)
    (ground.posVal ed) r N) (qLowDen (ground.posVal en) (ground.posVal ed) r
    N) N en ed) ?_
  rw [BPair.add_assoc, BPair.add_assoc]
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) hzero) (BPair.add_unit _)

/-- The diagonal's cleared read at a depth. -/
def wellDiag (r qn qd : Nat) (en ed : Pos) (m : Nat) : BPair :=
  poly.evalClear (diagPoly r qn qd m) (BPair.ofPos en) ed 2

/-- The bond weight, the clearing constants' product at the scale's
square. -/
def wellBond (r qd : Nat) (ed : Pos) : BPair :=
  BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed

/-- The well head at a stated order, assembled deep end first: the
elimination's ordering is certificate data (`thm:decimation`(i)),
and the deep-first ordering seeds the slab recursion at the
boundary, the walk's own pivots. -/
def wellMat (r qn qd : Nat) (en ed : Pos) (n : Nat) : elim.Mat :=
  greenprod.assemble
    ((List.range n).map (fun k => [[wellDiag r qn qd en ed (n - k)]]))
    ((List.range (n - 1)).map (fun _ => [[(wellBond r qd ed).swap]]))

/-- The witness family's list at the head's order and gauge. -/
def witList (N n : Nat) : List BPair :=
  (List.range n).map (fun k => BPair.ofNat (witVal N (n - k)))

/-- The keyed pair walk at two matched families is the zipped
family. -/
private theorem rangeZipCons (d : BPair) (dd : List BPair) :
    ∀ (c : List BPair) (rest : elim.Mat), c.length = rest.length →
      (List.range rest.length).map
          (fun r => ground.getAt d c r :: ground.getAt dd rest r)
        = List.zipWith (fun a b => a :: b) c rest
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | a :: ct, R :: rt, h => by
    show (List.range (rt.length + 1)).map _ = (a :: R) :: _
    rw [ground.range_cons rt.length]
    show (a :: R) :: ((List.range rt.length).map (fun j => j + 1)).map
        (fun r => ground.getAt d (a :: ct) r :: ground.getAt dd (R :: rt) r)
      = (a :: R) :: _
    rw [ground.map_map]
    show (a :: R) :: (List.range rt.length).map
        (fun j => ground.getAt d ct j :: ground.getAt dd rt j) = _
    rw [rangeZipCons d dd ct rt (Nat.succ.inj h)]


/-- The block row's pairing splits at the leading column: the rows'
folds against the walked vector are the column's scaled fold and the
tail block's own. -/
private theorem consDot (x : BPair) (w : List BPair) :
    ∀ (c : List BPair) (rest : elim.Mat), c.length = rest.length →
    ∀ v : List BPair,
      (elim.dotP v ((List.zipWith (fun a b => a :: b) c rest).map
          (fun rr => elim.dotP rr (x :: w)))).oneValue
        (elim.dotP v (c.map (fun cc => cc * x))
          + elim.dotP v (rest.map (fun rr => elim.dotP rr w)))
  | [], [], _, v => by
    show (elim.dotP v []).oneValue (elim.dotP v [] + elim.dotP v [])
    rw [elim.dotP_nil_right v]
    exact BPair.oneValue_symm (BPair.add_unit BPair.unit)
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | _ :: _, _ :: _, _, [] => by
    show (elim.dotP [] _).oneValue (elim.dotP [] _ + elim.dotP [] _)
    exact BPair.oneValue_symm (BPair.add_unit BPair.unit)
  | cc :: ct, R :: rt, h, z :: vt => by
    show (z * (cc * x + elim.dotP R w)
        + elim.dotP vt ((List.zipWith (fun a b => a :: b) ct rt).map
          (fun rr => elim.dotP rr (x :: w)))).oneValue
      ((z * (cc * x) + elim.dotP vt (ct.map (fun cc => cc * x)))
        + (z * elim.dotP R w + elim.dotP vt (rt.map (fun rr => elim.dotP rr w))))
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_of_eq (BPair.left_distrib z (cc * x)
        (elim.dotP R w))) (consDot x w ct rt (Nat.succ.inj h) vt)) ?_
    exact BPair.oneValue_of_eq (BPair.add_add_comm _ _ _ _)


/-- The scalar chain's shape: the assembled matrix is square at the
diagonal's count, its leading row the same width. -/
private theorem chainLen : ∀ (diag off : List BPair),
    off.length + 1 = diag.length →
    (greenprod.assemble (diag.map (fun a => [[a]]))
        (off.map (fun b => [[b]]))).length = diag.length
      ∧ ((greenprod.assemble (diag.map (fun a => [[a]]))
        (off.map (fun b => [[b]]))).headD []).length = diag.length
  | [], _, h => Nat.noConfusion h
  | [_], [], _ => ⟨rfl, rfl⟩
  | [_], _ :: _, h => Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _, [], h => Nat.noConfusion (Nat.succ.inj h)
  | a :: a' :: dt, b :: ot, h => by
    have hIH := chainLen (a' :: dt) ot (Nat.succ.inj h)
    refine ⟨?_, ?_⟩
    · show ((List.range (greenprod.assemble ((a' :: dt).map
          (fun a => [[a]])) (ot.map (fun b => [[b]]))).length).map _).length
            + 1 = dt.length + 1 + 1
      rw [ground.length_mapRange, hIH.1]
      rfl
    · show (a :: b :: List.replicate
        (((greenprod.assemble ((a' :: dt).map (fun a => [[a]]))
          (ot.map (fun b => [[b]]))).headD []).length - 1)
          BPair.unit).length = dt.length + 1 + 1
      show (List.replicate
        (((greenprod.assemble ((a' :: dt).map (fun a => [[a]]))
          (ot.map (fun b => [[b]]))).headD []).length - 1)
          BPair.unit).length + 1 + 1 = dt.length + 1 + 1
      rw [ground.length_replicate, hIH.2]
      rfl


/-- The pairing against a scaled constant family sits at the sum's
unit. -/
private theorem dotP_replMul (x : BPair) : ∀ (v : List BPair) (p : Nat),
    (elim.dotP v ((List.replicate p BPair.unit).map
      (fun cc => cc * x))).oneValue BPair.unit
  | [], _ => BPair.oneValue_refl _
  | _ :: _, 0 => BPair.oneValue_refl _
  | z :: vt, p + 1 => by
    show (z * (BPair.unit * x) + elim.dotP vt _).oneValue BPair.unit
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl z) (BPair.unit_mul x))
      (dotP_replMul x vt p)) ?_
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_unit z) (BPair.oneValue_refl BPair.unit))
      (BPair.unit_add BPair.unit)

/-- The leading slab's own contribution: the diagonal entry at the
square and the bond entry at the doubled consecutive product. -/
private theorem consArith (a b x y : BPair) :
    (x * (a * x + b * y) + y * (b * x)).oneValue
      (a * (x * x) + BPair.ofNat 2 * (b * (x * y))) := by
  rw [BPair.left_distrib x (a * x) (b * y),
    BPair.mul_left_comm x a x, BPair.mul_left_comm x b y,
    BPair.mul_comm y (b * x), BPair.mul_assoc b x y,
    BPair.add_assoc]
  exact BPair.add_congr (BPair.oneValue_refl (a * (x * x)))
    (BPair.oneValue_symm (BPair.ofNat_two_mul (b * (x * y))))


/-- The leading slab's row read at the assembled chain: the head
row's fold and the block rows' folds split into the slab's own
entries and the tail chain's fold. -/
private theorem consQuad (a b x y : BPair) (ut : List BPair) (rest : elim.Mat)
    (hlen : rest.length = ut.length + 1)
    (hhd : (rest.headD []).length = ut.length + 1) :
    (elim.dotP (x :: y :: ut)
        (((a :: b :: List.replicate ((rest.headD []).length - 1) BPair.unit)
            :: (List.range rest.length).map (fun r =>
              (if r < 1 then ground.getAt [] [[b]] r
               else List.replicate 1 BPair.unit)
                ++ ground.getAt [] rest r)).map
          (fun rr => elim.dotP rr (x :: y :: ut)))).oneValue
      (a * (x * x) + BPair.ofNat 2 * (b * (x * y))
        + elim.dotP (y :: ut) (rest.map (fun rr => elim.dotP rr (y :: ut)))) := by
  have hcol : (b :: List.replicate ut.length BPair.unit).length
      = rest.length := by
    rw [hlen]
    show (List.replicate ut.length BPair.unit).length + 1 = ut.length + 1
    rw [ground.length_replicate]
  have hpt : ∀ r : Nat,
      (if r < 1 then ground.getAt [] [[b]] r
       else List.replicate 1 BPair.unit) ++ ground.getAt [] rest r
        = ground.getAt BPair.unit (b :: List.replicate ut.length BPair.unit) r
          :: ground.getAt [] rest r := by
    intro r
    match r with
    | 0 => rfl
    | j + 1 =>
      show List.replicate 1 BPair.unit ++ ground.getAt [] rest (j + 1)
        = ground.getAt BPair.unit (List.replicate ut.length BPair.unit) j
          :: ground.getAt [] rest (j + 1)
      rw [ground.getAt_replicate_self BPair.unit ut.length j]
      rfl
  rw [hhd]
  show (x * elim.dotP (a :: b :: List.replicate (ut.length + 1 - 1) BPair.unit)
        (x :: y :: ut)
      + elim.dotP (y :: ut)
        (((List.range rest.length).map (fun r =>
            (if r < 1 then ground.getAt [] [[b]] r
             else List.replicate 1 BPair.unit)
              ++ ground.getAt [] rest r)).map
          (fun rr => elim.dotP rr (x :: y :: ut)))).oneValue _
  rw [ground.map_congr_all _
      (fun r => ground.getAt BPair.unit
        (b :: List.replicate ut.length BPair.unit) r
          :: ground.getAt [] rest r) hpt,
    rangeZipCons BPair.unit [] (b :: List.replicate ut.length BPair.unit)
      rest hcol]
  have hhead : (elim.dotP (a :: b :: List.replicate (ut.length + 1 - 1) BPair.unit)
      (x :: y :: ut)).oneValue (a * x + b * y) := by
    show (a * x + (b * y
      + elim.dotP (List.replicate (ut.length + 1 - 1) BPair.unit) ut)).oneValue
        (a * x + b * y)
    refine BPair.add_congr (BPair.oneValue_refl (a * x)) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl (b * y))
      ?_) (BPair.add_unit (b * y))
    rw [elim.dotP_comm (List.replicate (ut.length + 1 - 1) BPair.unit) ut]
    exact elim.dotP_repl_unit ut (ut.length + 1 - 1)
  have hcolDot : (elim.dotP (y :: ut)
      ((b :: List.replicate ut.length BPair.unit).map
        (fun cc => cc * x))).oneValue (y * (b * x)) := by
    show (y * (b * x) + elim.dotP ut ((List.replicate ut.length BPair.unit).map
        (fun cc => cc * x))).oneValue (y * (b * x))
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (y * (b * x)))
        (dotP_replMul x ut ut.length)) (BPair.add_unit (y * (b * x)))
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.mul_congr (BPair.oneValue_refl x) hhead)
    (consDot x (y :: ut) (b :: List.replicate ut.length BPair.unit) rest
      hcol (y :: ut))) ?_
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr hcolDot (BPair.oneValue_refl _))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
  exact BPair.add_congr (consArith a b x y) (BPair.oneValue_refl _)


/-- The scalar chain's plain form read: the diagonal entries at the
squares with the bonds at the doubled consecutive products. -/
private theorem chainDot : ∀ (diag off u : List BPair),
    diag.length = u.length → off.length + 1 = diag.length →
    (elim.dotP u ((greenprod.assemble (diag.map (fun a => [[a]]))
        (off.map (fun b => [[b]]))).map (fun rr => elim.dotP rr u))).oneValue
      (ground.bsum (fun k =>
          ground.getAt BPair.unit diag k
            * (ground.getAt BPair.unit u k
              * ground.getAt BPair.unit u k))
        (List.range u.length)
      + BPair.ofNat 2
        * ground.bsum (fun k =>
            ground.getAt BPair.unit off k
              * (ground.getAt BPair.unit u k
                * ground.getAt BPair.unit u (k + 1)))
          (List.range off.length))
  | [], _, _, _, h => Nat.noConfusion h
  | [_], _ :: _, _, _, h => Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _, [], _, _, h => Nat.noConfusion (Nat.succ.inj h)
  | [_], [], [], h, _ => Nat.noConfusion h
  | [_], [], _ :: _ :: _, h, _ => Nat.noConfusion (Nat.succ.inj h)
  | [a], [], [x], _, _ => by
    show (x * (a * x + BPair.unit) + BPair.unit).oneValue
      ((a * (x * x) + BPair.unit) + BPair.ofNat 2 * BPair.unit)
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl x) (BPair.add_unit (a * x)))
      (BPair.oneValue_refl BPair.unit)) ?_
    refine BPair.oneValue_trans (BPair.add_unit (x * (a * x))) ?_
    rw [BPair.mul_left_comm x a x]
    refine BPair.oneValue_symm ?_
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.add_unit (a * (x * x)))
        (BPair.mul_unit (BPair.ofNat 2)))
      (BPair.add_unit (a * (x * x)))
  | _ :: _ :: _, _ :: _, [], h, _ => Nat.noConfusion h
  | _ :: _ :: _, _ :: _, [_], h, _ => Nat.noConfusion (Nat.succ.inj h)
  | a :: a' :: dt, b :: ot, x :: y :: ut, h1, h2 => by
    have hut : dt.length = ut.length := Nat.succ.inj (Nat.succ.inj h1)
    have hIH := chainDot (a' :: dt) ot (y :: ut)
      (Nat.succ.inj h1) (Nat.succ.inj h2)
    have hsh := chainLen (a' :: dt) ot (Nat.succ.inj h2)
    have hlen : (greenprod.assemble ((a' :: dt).map (fun a => [[a]]))
        (ot.map (fun b => [[b]]))).length = ut.length + 1 := by
      rw [hsh.1]
      show dt.length + 1 = ut.length + 1
      rw [hut]
    have hhd : ((greenprod.assemble ((a' :: dt).map (fun a => [[a]]))
        (ot.map (fun b => [[b]]))).headD []).length = ut.length + 1 := by
      rw [hsh.2]
      show dt.length + 1 = ut.length + 1
      rw [hut]
    have hM : greenprod.assemble ((a :: a' :: dt).map (fun a => [[a]]))
          ((b :: ot).map (fun b => [[b]]))
        = (a :: b :: List.replicate
              (((greenprod.assemble ((a' :: dt).map (fun a => [[a]]))
                (ot.map (fun b => [[b]]))).headD []).length - 1) BPair.unit)
          :: (List.range (greenprod.assemble ((a' :: dt).map (fun a => [[a]]))
                (ot.map (fun b => [[b]]))).length).map (fun r =>
              (if r < 1 then ground.getAt [] [[b]] r
               else List.replicate 1 BPair.unit)
                ++ ground.getAt [] (greenprod.assemble
                  ((a' :: dt).map (fun a => [[a]]))
                  (ot.map (fun b => [[b]]))) r) := rfl
    have hF : ground.bsum (fun k =>
          ground.getAt BPair.unit (a :: a' :: dt) k
            * (ground.getAt BPair.unit (x :: y :: ut) k
              * ground.getAt BPair.unit (x :: y :: ut) k))
          (List.range (ut.length + 1 + 1))
        = a * (x * x)
          + ground.bsum (fun k =>
            ground.getAt BPair.unit (a' :: dt) k
              * (ground.getAt BPair.unit (y :: ut) k
                * ground.getAt BPair.unit (y :: ut) k))
            (List.range (ut.length + 1)) := by
      rw [ground.range_cons (ut.length + 1)]
      show a * (x * x) + ground.bsum _
          ((List.range (ut.length + 1)).map (fun j => j + 1)) = _
      rw [ground.bsum_map]
      rfl
    have hG : ground.bsum (fun k =>
          ground.getAt BPair.unit (b :: ot) k
            * (ground.getAt BPair.unit (x :: y :: ut) k
              * ground.getAt BPair.unit (x :: y :: ut) (k + 1)))
          (List.range (ot.length + 1))
        = b * (x * y)
          + ground.bsum (fun k =>
            ground.getAt BPair.unit ot k
              * (ground.getAt BPair.unit (y :: ut) k
                * ground.getAt BPair.unit (y :: ut) (k + 1)))
            (List.range ot.length) := by
      rw [ground.range_cons ot.length]
      show b * (x * y) + ground.bsum _
          ((List.range ot.length).map (fun j => j + 1)) = _
      rw [ground.bsum_map]
      rfl
    rw [hM]
    show (elim.dotP (x :: y :: ut) _).oneValue
      (ground.bsum _ (List.range (ut.length + 1 + 1))
        + BPair.ofNat 2 * ground.bsum _ (List.range (ot.length + 1)))
    rw [hF, hG]
    refine BPair.oneValue_trans (consQuad a b x y ut _ hlen hhd) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) hIH) ?_
    rw [BPair.left_distrib (BPair.ofNat 2) (b * (x * y)) _]
    exact BPair.oneValue_of_eq (BPair.add_add_comm _ _ _ _)


/-- The scalar chain's form read is the display's two folds: the
diagonal entries at the squares with the bonds at the doubled
consecutive products. -/
private theorem chainQuad : ∀ (diag off u : List BPair),
    diag.length = u.length → off.length + 1 = diag.length →
    (inertia.quadForm
        (greenprod.assemble (diag.map (fun a => [[a]]))
          (off.map (fun b => [[b]])))
        u).oneValue
      (ground.bsum (fun k =>
          ground.getAt BPair.unit diag k
            * (ground.getAt BPair.unit u k
              * ground.getAt BPair.unit u k))
        (List.range u.length)
      + BPair.ofNat 2
        * ground.bsum (fun k =>
            ground.getAt BPair.unit off k
              * (ground.getAt BPair.unit u k
                * ground.getAt BPair.unit u (k + 1)))
          (List.range off.length)) :=
  fun diag off u hl ho =>
    BPair.oneValue_trans (elim.quadP_read _ u) (chainDot diag off u hl ho)

/-- The gap at an exceeded key: the strict order's witness read. -/
private theorem gapAt {x n : Nat} (h : x < n) :
    ∃ g : Nat, x + 1 + g = n ∧ n - 1 = x + g ∧ n - 1 - x = g := by
  obtain ⟨g, hg⟩ := Nat.le.dest h
  have hn : n = x + g + 1 := by
    rw [← hg, Nat.add_right_comm x 1 g]
  have hpred : n - 1 = x + g := by
    rw [hn]
    exact rfl
  have hsub : n - 1 - x = g := by
    rw [hpred, Nat.add_comm x g]
    have h1 : x + (g + x - x) = g + x := by
      rw [Nat.add_comm g x]
      exact ground.natAddSubCancel (Nat.le_add_right x g)
    have h2 : x + (g + x - x) = x + g := by
      rw [h1, Nat.add_comm g x]
    exact ground.addCancelL x h2
  exact ⟨g, hg, hpred, hsub⟩

/-- The reversing index is its own involution inside the range. -/
private theorem revIdx {x n : Nat} (h : x < n) :
    n - 1 - (n - 1 - x) = x := by
  obtain ⟨g, -, hpred, hsub⟩ := gapAt h
  rw [hsub, hpred]
  have h1 : g + (x + g - g) = x + g := by
    rw [Nat.add_comm x g]
    exact ground.natAddSubCancel (Nat.le_add_right g x)
  exact ground.addCancelL g (h1.trans (Nat.add_comm x g))

/-- The key range's fold reverses: the family read deep end first is
the family read at the boundary, the reindexing read at the range's
own involution. -/
private theorem bsumRev (F : Nat → BPair) (n : Nat) :
    (ground.bsum (fun k => F (n - k)) (List.range n)).oneValue
      (ground.bsum (fun k => F (k + 1)) (List.range n)) := by
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (ground.famFold_reindex_ov ground.bpairFoldLaws.toCommLaws BPair.unit
      (fun k => F (k + 1)) (l := List.range n)
      (g := fun x => n - 1 - x) (h := fun x => n - 1 - x)
      (fun x _ => by
        rw [ground.countOf_range x n]
        cases hd : Nat.decLt x n with
        | isTrue ht => rw [if_pos ht]; exact Nat.le_refl 1
        | isFalse hf => rw [if_neg hf]; exact Nat.zero_le 1)
      (fun x hx => revIdx (ground.ltOfMem hx))
      (fun x hx => revIdx (ground.ltOfMem hx))
      (fun x hx => by
        rw [ground.countOf_range, if_pos (ground.predSubLt (ground.ltOfMem hx))]
        exact Nat.one_pos)
      (fun x hx => by
        rw [ground.countOf_range, if_pos (ground.predSubLt (ground.ltOfMem hx))]
        exact Nat.one_pos)) ?_
  refine ground.foldB_congr_members _ _ (List.range n) (fun j hj => ?_)
  obtain ⟨g, hg, -, hsub⟩ := gapAt (ground.ltOfMem hj)
  rw [hsub]
  have hn : j + (1 + g) = n := by
    rw [← hg, Nat.add_assoc]
  have h2 : j + (n - j) = n :=
    ground.natAddSubCancel (Nat.le_of_lt (ground.ltOfMem hj))
  have h3 : n - j = 1 + g := ground.addCancelL j (h2.trans hn.symm)
  rw [h3, Nat.add_comm 1 g]
  exact BPair.oneValue_refl _

/-- The key range's fold truncates at a family vacant beyond a
count. -/
private theorem bsumTrunc (F : Nat → BPair) (M L : Nat) (hML : M ≤ L)
    (h0 : ∀ k, M ≤ k → (F k).oneValue BPair.unit) :
    (ground.bsum F (List.range L)).oneValue
      (ground.bsum F (List.range M)) := by
  have hg : M + (L - M) = L := ground.natAddSubCancel hML
  rw [← hg, ground.range_split M (L - M)]
  refine BPair.oneValue_trans
    (ground.famFold_append_ov ground.bpairFoldLaws F (List.range M) _) ?_
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) ?_)
    (BPair.add_unit _)
  show (ground.bsum F ((List.range (L - M)).map (fun c => M + c))).oneValue
    BPair.unit
  rw [ground.bsum_map]
  exact ground.foldB_nullRange _ _ (fun k _ => h0 (M + k) (Nat.le_add_right M k))


/-- The family is vacant at or beyond its own depth. -/
private theorem witVal_vac (N m : Nat) (h : N ≤ m) : witVal N m = 0 := by
  show m * m * (N * N - m * m) = 0
  rw [ground.subLe (N * N) (m * m) (Nat.mul_le_mul h h)]
  rfl

/-- A weighted pair at a vacant left entry reads the sum's unit. -/
private theorem mulVacL (c X Y : BPair) (h : X.oneValue BPair.unit) :
    (c * (X * Y)).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl c)
    (BPair.oneValue_trans (BPair.mul_congr h (BPair.oneValue_refl Y))
      (BPair.unit_mul Y))) (BPair.mul_unit c)

/-- The family's vacant entry reads the sum's unit. -/
private theorem witVac (N j : Nat) (h : N ≤ j) :
    (BPair.ofNat (witVal N j)).oneValue BPair.unit :=
  BPair.oneValue_of_eq (congrArg BPair.ofNat (witVal_vac N j h))

/-- The family reads the sum's unit at the nought depth. -/
private theorem witVal_zero (N : Nat) : witVal N 0 = 0 := by
  show 0 * 0 * (N * N - 0 * 0) = 0
  rw [Nat.zero_mul (N * N - 0 * 0)]


/-- The family's own count. -/
private theorem witList_len (N n : Nat) : (witList N n).length = n :=
  ground.length_mapRange _ n

/-- The family's entry read at a key below the order. -/
private theorem witList_at (N n k : Nat) (hk : k < n) :
    ground.getAt BPair.unit (witList N n) k
      = BPair.ofNat (witVal N (n - k)) := by
  show ground.getAt BPair.unit
      ((List.range n).map (fun j => BPair.ofNat (witVal N (n - j)))) k = _
  rw [ground.getAt_map_range BPair.unit _ n k, if_pos hk]

/-- The head's diagonal fold at the witness family: the deep-first
walk read at the boundary and truncated at the family's window. -/
private theorem wellDiagFold (r qn qd N n : Nat) (en ed : Pos) (h : N ≤ n) :
    (ground.bsum (fun k =>
        ground.getAt BPair.unit
            ((List.range n).map (fun j => wellDiag r qn qd en ed (n - j))) k
          * (ground.getAt BPair.unit (witList N n) k
            * ground.getAt BPair.unit (witList N n) k))
      (List.range n)).oneValue
      (ground.bsum (fun k =>
          wellDiag r qn qd en ed (k + 1)
            * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1))))
        (List.range N)) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => wellDiag r qn qd en ed (n - k)
        * (BPair.ofNat (witVal N (n - k)) * BPair.ofNat (witVal N (n - k))))
      (List.range n) (fun k hk => ?_)) ?_
  · have hkn : k < n := ground.ltOfMem hk
    refine BPair.oneValue_of_eq ?_
    rw [ground.getAt_map_range BPair.unit _ n k, if_pos hkn,
      witList_at N n k hkn]
  · refine BPair.oneValue_trans
      (bsumRev (fun j => wellDiag r qn qd en ed j
        * (BPair.ofNat (witVal N j) * BPair.ofNat (witVal N j))) n) ?_
    exact bsumTrunc _ N n h (fun k hk =>
      mulVacL _ _ _ (witVac N (k + 1) (Nat.le_trans hk (Nat.le_succ k))))


/-- The key range's fold drops a vacant leading key. -/
private theorem bsumHead (F : Nat → BPair) (n : Nat)
    (h0 : (F 0).oneValue BPair.unit) :
    (ground.bsum F (List.range (n + 1))).oneValue
      (ground.bsum (fun k => F (k + 1)) (List.range n)) := by
  rw [ground.range_cons n]
  show (F 0 + ground.bsum F ((List.range n).map (fun j => j + 1))).oneValue _
  rw [ground.bsum_map]
  exact BPair.oneValue_trans
    (BPair.add_congr h0 (BPair.oneValue_refl _)) (BPair.unit_add _)

/-- The head's bond fold at the witness family: the constant weight
against the family's consecutive products, read at the boundary and
at the family's window. -/
private theorem wellCrossFold : ∀ (r qd N n : Nat) (ed : Pos), N ≤ n →
    (ground.bsum (fun k =>
        ground.getAt BPair.unit
            ((List.range (n - 1)).map (fun _ => (wellBond r qd ed).swap)) k
          * (ground.getAt BPair.unit (witList N n) k
            * ground.getAt BPair.unit (witList N n) (k + 1)))
      (List.range (n - 1))).oneValue
      ((wellBond r qd ed).swap
        * BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
            witVal N (k + 1) * witVal N (k + 2)))))
  | _, _, _ + 1, 0, _, h => absurd h (Nat.not_succ_le_zero _)
  | r, qd, 0, 0, ed, _ =>
    BPair.oneValue_symm (BPair.mul_unit ((wellBond r qd ed).swap))
  | r, qd, N, p + 1, ed, h => by
    have hg : ∀ l : Nat, N - 1 ≤ l →
        witVal N (l + 1) * witVal N (l + 2) = 0 := by
      intro l hl
      rw [witVal_vac N (l + 1)
          (Nat.le_trans (ground.lePredSucc N) (Nat.succ_le_succ hl)),
        Nat.zero_mul (witVal N (l + 2))]
    have hstep : (ground.bsum (fun k =>
          ground.getAt BPair.unit
              ((List.range p).map (fun _ => (wellBond r qd ed).swap)) k
            * (ground.getAt BPair.unit (witList N (p + 1)) k
              * ground.getAt BPair.unit (witList N (p + 1)) (k + 1)))
        (List.range p)).oneValue
        (ground.bsum (fun k => (wellBond r qd ed).swap
            * (BPair.ofNat (witVal N (p + 1 - k))
              * BPair.ofNat (witVal N (p + 1 - k - 1))))
          (List.range p)) := by
      refine ground.foldB_congr_members _ _ (List.range p) (fun k hk => ?_)
      have hkp : k < p := ground.ltOfMem hk
      refine BPair.oneValue_of_eq ?_
      rw [ground.getAt_map_range BPair.unit _ p k, if_pos hkp,
        witList_at N (p + 1) k (Nat.lt_succ_of_lt hkp),
        witList_at N (p + 1) (k + 1) (Nat.succ_lt_succ hkp),
        ground.subSub (p + 1) k 1]
    refine BPair.oneValue_trans hstep ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (bsumTrunc (fun k => (wellBond r qd ed).swap
          * (BPair.ofNat (witVal N (p + 1 - k))
            * BPair.ofNat (witVal N (p + 1 - k - 1))))
        p (p + 1) (Nat.le_succ p) (fun k hk => ?_))) ?_
    · rw [BPair.mul_comm (BPair.ofNat (witVal N (p + 1 - k)))
        (BPair.ofNat (witVal N (p + 1 - k - 1)))]
      refine mulVacL _ _ _ ?_
      rw [ground.subSub (p + 1) k 1,
        ground.subLe (p + 1) (k + 1) (Nat.succ_le_succ hk), witVal_zero N]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans
      (bsumRev (fun j => (wellBond r qd ed).swap
        * (BPair.ofNat (witVal N j) * BPair.ofNat (witVal N (j - 1))))
        (p + 1)) ?_
    refine BPair.oneValue_trans
      (bsumHead (fun k => (wellBond r qd ed).swap
          * (BPair.ofNat (witVal N (k + 1))
            * BPair.ofNat (witVal N (k + 1 - 1)))) p ?_) ?_
    · rw [BPair.mul_comm (BPair.ofNat (witVal N (0 + 1)))
        (BPair.ofNat (witVal N (0 + 1 - 1)))]
      refine mulVacL _ _ _ ?_
      rw [witVal_zero N]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans
      (ground.foldB_mul_left ((wellBond r qd ed).swap)
        (fun k => BPair.ofNat (witVal N (k + 2))
          * BPair.ofNat (witVal N (k + 1))) (List.range p)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => BPair.ofNat (witVal N (k + 1) * witVal N (k + 2)))
        (List.range p) (fun k _ => ?_)) ?_
    · refine BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.oneValue_of_eq (congrArg BPair.ofNat
          (Nat.mul_comm (witVal N (k + 1)) (witVal N (k + 2))))) ?_)
      exact BPair.ofNat_mul (witVal N (k + 2)) (witVal N (k + 1))
    refine BPair.oneValue_symm ?_
    rw [ground.sumMap (fun k => witVal N (k + 1) * witVal N (k + 2))
        (List.range N),
      ground.foldExtend' (fun k => witVal N (k + 1) * witVal N (k + 2))
        (N - 1) N (Nat.sub_le N 1) hg,
      ← ground.foldExtend' (fun k => witVal N (k + 1) * witVal N (k + 2))
        (N - 1) p (Nat.sub_le_sub_right h 1) hg]
    exact ground.ofNat_famFold _ (List.range p)


/-- The head's form read at the witness family: the diagonal fold
at the family's window against the bond's doubled cross fold. -/
private theorem wellForm : ∀ (r qn qd N n : Nat) (en ed : Pos), N ≤ n →
    (inertia.quadForm (wellMat r qn qd en ed n) (witList N n)).oneValue
      (ground.bsum (fun k =>
          wellDiag r qn qd en ed (k + 1)
            * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1))))
        (List.range N)
      + BPair.ofNat 2
        * ((wellBond r qd ed).swap
          * BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
              witVal N (k + 1) * witVal N (k + 2))))))
  | _, _, _, _ + 1, 0, _, _, h => absurd h (Nat.not_succ_le_zero _)
  | r, _, qd, 0, 0, _, ed, _ =>
    BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl BPair.unit)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 2))
            (BPair.oneValue_of_eq (BPair.mul_comm
              ((wellBond r qd ed).swap) (BPair.ofNat 0))))
          (mulVacL (BPair.ofNat 2) (BPair.ofNat 0)
            ((wellBond r qd ed).swap) (BPair.oneValue_refl BPair.unit))))
      (BPair.unit_add BPair.unit))
  | r, qn, qd, N, p + 1, en, ed, h => by
    have hmat : greenprod.assemble
          (((List.range (p + 1)).map (fun j =>
            wellDiag r qn qd en ed (p + 1 - j))).map (fun a => [[a]]))
          (((List.range p).map (fun _ =>
            (wellBond r qd ed).swap)).map (fun b => [[b]]))
        = wellMat r qn qd en ed (p + 1) := by
      rw [ground.map_map, ground.map_map]
      rfl
    rw [← hmat]
    refine BPair.oneValue_trans
      (chainQuad _ _ (witList N (p + 1)) ?_ ?_) ?_
    · rw [ground.length_mapRange, witList_len]
    · rw [ground.length_mapRange, ground.length_mapRange]
    rw [witList_len N (p + 1),
      show ((List.range p).map (fun _ =>
          (wellBond r qd ed).swap)).length = p from
        ground.length_mapRange _ p]
    exact BPair.add_congr (wellDiagFold r qn qd N (p + 1) en ed h)
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 2))
        (wellCrossFold r qd N (p + 1) ed h))

/-- The lower rate's two folds join at the sum's unit: the kernel
identity against the bond's own doubled cross fold. -/
private theorem kernelCancel (en ed : Pos) (r N : Nat) :
    (ground.bsum (fun k =>
        wellDiag r (qLowNum (ground.posVal en) (ground.posVal ed) r N)
            (qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed (k + 1)
          * (BPair.ofNat (witVal N (k + 1))
            * BPair.ofNat (witVal N (k + 1))))
      (List.range N)
    + BPair.ofNat 2
      * ((wellBond r (qLowDen (ground.posVal en) (ground.posVal ed) r N)
            ed).swap
        * BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
            witVal N (k + 1) * witVal N (k + 2)))))).oneValue
      BPair.unit := by
  refine BPair.oneValue_trans
    (BPair.add_congr (witKernel en ed r N) (BPair.oneValue_refl _)) ?_
  rw [show BPair.ofNat ((r + 1)
        * qLowDen (ground.posVal en) (ground.posVal ed) r N)
          * BPair.ofPos ed * BPair.ofPos ed
      = wellBond r (qLowDen (ground.posVal en) (ground.posVal ed) r N) ed
      from rfl,
    BPair.mul_assoc (BPair.ofNat 2)
      (wellBond r (qLowDen (ground.posVal en) (ground.posVal ed) r N) ed)
      (BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
        witVal N (k + 1) * witVal N (k + 2))))),
    BPair.swap_mul
      (wellBond r (qLowDen (ground.posVal en) (ground.posVal ed) r N) ed)
      (BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
        witVal N (k + 1) * witVal N (k + 2))))),
    BPair.mul_swap (BPair.ofNat 2)
      (wellBond r (qLowDen (ground.posVal en) (ground.posVal ed) r N) ed
        * BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
          witVal N (k + 1) * witVal N (k + 2))))),
    BPair.add_comm]
  exact BPair.swap_add_null (BPair.oneValue_refl _)

/-- The kernel read at the head: the form read at the lower rate's
own data joins the family at equal members, the two sides' one
value at the telescope. -/
theorem witQuad : ∀ (en ed : Pos) (r N n : Nat), N ≤ n →
    (inertia.quadForm
        (wellMat r (qLowNum (ground.posVal en) (ground.posVal ed) r N)
          (qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n)
        (witList N n)).oneValue BPair.unit :=
  fun en ed r N n h =>
    BPair.oneValue_trans
      (wellForm r (qLowNum (ground.posVal en) (ground.posVal ed) r N)
        (qLowDen (ground.posVal en) (ground.posVal ed) r N) N n en ed h)
      (kernelCancel en ed r N)
/-- A count factor withdraws from a three-factor product. -/
private theorem countScale3 (b c : Nat) (X Y : BPair) :
    (BPair.ofNat (b * c) * X * Y).oneValue
      (BPair.ofNat b * (BPair.ofNat c * X * Y)) := by
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.mul_congr (BPair.ofNat_mul b c)
      (BPair.oneValue_refl X)) (BPair.oneValue_refl Y)) ?_
  refine BPair.oneValue_of_eq ?_
  rw [BPair.mul_assoc (BPair.ofNat b) (BPair.ofNat c) X,
    BPair.mul_assoc (BPair.ofNat b) (BPair.ofNat c * X) Y]

/-- A sum's three-factor product splits at the summands. -/
private theorem addMul3 (U V X Y : BPair) :
    (U + V) * X * Y = U * X * Y + V * X * Y := by
  rw [BPair.mul_comm (U + V) X, BPair.left_distrib X U V,
    BPair.mul_comm (X * U + X * V) Y, BPair.left_distrib Y (X * U) (X * V),
    BPair.mul_comm U X, BPair.mul_comm V X,
    BPair.mul_comm (X * U) Y, BPair.mul_comm (X * V) Y]

/-- The two scales exchange across a shared factor. -/
private theorem crossNat1 (u b b' w : Nat) :
    b' * (u * (b * w)) = b * (u * (b' * w)) := by
  rw [ground.mulLeftComm b' u (b * w), ground.mulLeftComm b u (b' * w),
    ground.mulLeftComm b' b w]

/-- The two scales exchange across the depth's own weight. -/
private theorem crossNat2 (b b' qd M : Nat) :
    b' * (4 * (b * qd) * M) = b * (4 * (b' * qd) * M) := by
  rw [ground.mulLeftComm 4 b qd, ground.mulLeftComm 4 b' qd,
    ground.mulAssoc b (4 * qd) M, ground.mulAssoc b' (4 * qd) M,
    ground.mulLeftComm b' b (4 * qd * M)]

/-- The two lines' cross-added numerators differ by the gap's own
weight. -/
private theorem crossNat3 (u qn a b a' b' gg : Nat)
    (hab : a' * b + gg = a * b') :
    b' * (u * (a * qn)) = b * (u * (a' * qn)) + u * (gg * qn) := by
  rw [ground.mulLeftComm b' u (a * qn), ground.mulLeftComm b u (a' * qn),
    ← ground.mulAssoc b' a qn, ← ground.mulAssoc b a' qn,
    Nat.mul_comm b' a, Nat.mul_comm b a',
    ← Nat.left_distrib u (a' * b * qn) (gg * qn),
    ← ground.mulAddR (a' * b) gg qn, hab]

/-- A count factor enters the doubled product at the numerator. -/
private theorem twoScale (c u : Nat) (D : BPair) :
    (BPair.ofNat c * (BPair.ofNat 2 * (BPair.ofNat u * D * D))).oneValue
      (BPair.ofNat 2 * (BPair.ofNat (c * u) * D * D)) :=
  BPair.oneValue_trans (BPair.oneValue_of_eq
      (BPair.mul_left_comm (BPair.ofNat c) (BPair.ofNat 2) _))
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (countScale3 c u D D)))

/-- A count factor enters a three-factor product at the
numerator. -/
private theorem numScale (c u : Nat) (E F : BPair) :
    (BPair.ofNat c * (BPair.ofNat u * E * F)).oneValue
      (BPair.ofNat (c * u) * E * F) :=
  BPair.oneValue_symm (countScale3 c u E F)

/-- A scale distributes over a three-summand sum. -/
private theorem mulAdd3 (c X Y Z : BPair) :
    c * (X + (Y + Z)) = c * X + (c * Y + c * Z) := by
  rw [BPair.left_distrib c X (Y + Z), BPair.left_distrib c Y Z]

/-- The two lines' three summands combine at the gap's own
summand. -/
private theorem lineCombine (T1 T2 T3 S1 S2 S3 G : BPair)
    (h1 : T1.oneValue S1) (h2 : T2.oneValue S2)
    (h3 : (T3 + G).oneValue S3) :
    (T1 + (T2 + T3) + G).oneValue (S1 + (S2 + S3)) := by
  rw [BPair.add_assoc T1 (T2 + T3) G, BPair.add_assoc T2 T3 G]
  exact BPair.add_congr h1 (BPair.add_congr h2 h3)

/-- The rates' balance partners at the two lines differ by the
gap's own weight. -/
private theorem lineT3 (r qn a b a' b' gg : Nat) (E D : BPair)
    (hab : a' * b + gg = a * b') :
    (BPair.ofNat b' * (BPair.ofNat ((r + 1) * (a * qn)) * E * D).swap
        + BPair.ofNat ((r + 1) * (gg * qn)) * E * D).oneValue
      (BPair.ofNat b * (BPair.ofNat ((r + 1) * (a' * qn)) * E * D).swap) := by
  rw [BPair.mul_swap (BPair.ofNat b') (BPair.ofNat ((r + 1) * (a * qn)) * E * D),
    BPair.mul_swap (BPair.ofNat b) (BPair.ofNat ((r + 1) * (a' * qn)) * E * D)]
  refine BPair.oneValue_trans
    (BPair.add_congr (ground.swap_congr (numScale b' ((r + 1) * (a * qn)) E D))
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans ?_
    (ground.swap_congr
      (BPair.oneValue_symm (numScale b ((r + 1) * (a' * qn)) E D)))
  rw [crossNat3 (r + 1) qn a b a' b' gg hab]
  refine BPair.oneValue_trans
    (BPair.add_congr (ground.swap_congr
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.mul_congr
          (BPair.ofNat_add (b * ((r + 1) * (a' * qn))) ((r + 1) * (gg * qn)))
          (BPair.oneValue_refl E)) (BPair.oneValue_refl D))
        (BPair.oneValue_of_eq (addMul3 (BPair.ofNat (b * ((r + 1) * (a' * qn))))
          (BPair.ofNat ((r + 1) * (gg * qn))) E D))))
      (BPair.oneValue_refl _)) ?_
  rw [← BPair.swap_add, BPair.add_assoc]
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.swap_add_null (BPair.oneValue_refl _))) ?_
  exact BPair.add_unit _

/-- The two member lines' diagonal identity at a depth: the
cross-multiplied datum gap is the stated positive weight. -/
private theorem lineDiag (r qn qd a b a' b' gg m : Nat) (en ed : Pos)
    (hab : a' * b + gg = a * b') :
    (BPair.ofNat b' * wellDiag r (a * qn) (b * qd) en ed m
        + BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en
          * BPair.ofPos ed).oneValue
      (BPair.ofNat b * wellDiag r (a' * qn) (b' * qd) en ed m) := by
  have h1 : (BPair.ofNat b' * (BPair.ofNat 2
        * (BPair.ofNat ((r + 1) * (b * qd)) * BPair.ofPos ed
          * BPair.ofPos ed))).oneValue
      (BPair.ofNat b * (BPair.ofNat 2
        * (BPair.ofNat ((r + 1) * (b' * qd)) * BPair.ofPos ed
          * BPair.ofPos ed))) := by
    refine BPair.oneValue_trans
      (twoScale b' ((r + 1) * (b * qd)) (BPair.ofPos ed)) ?_
    rw [crossNat1 (r + 1) b b' qd]
    exact BPair.oneValue_symm (twoScale b ((r + 1) * (b' * qd)) (BPair.ofPos ed))
  have h2 : (BPair.ofNat b' * (BPair.ofNat (4 * (b * qd) * (m * m + r * m))
        * BPair.ofPos en * BPair.ofPos en)).oneValue
      (BPair.ofNat b * (BPair.ofNat (4 * (b' * qd) * (m * m + r * m))
        * BPair.ofPos en * BPair.ofPos en)) := by
    refine BPair.oneValue_trans
      (numScale b' (4 * (b * qd) * (m * m + r * m))
        (BPair.ofPos en) (BPair.ofPos en)) ?_
    rw [crossNat2 b b' qd (m * m + r * m)]
    exact BPair.oneValue_symm (numScale b (4 * (b' * qd) * (m * m + r * m))
      (BPair.ofPos en) (BPair.ofPos en))
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl _)
      (diagRead r (a * qn) (b * qd) m en ed)) (BPair.oneValue_refl _))
    (BPair.oneValue_trans ?_
      (BPair.oneValue_symm (BPair.mul_congr (BPair.oneValue_refl _)
        (diagRead r (a' * qn) (b' * qd) m en ed))))
  rw [mulAdd3 (BPair.ofNat b') _ _ _, mulAdd3 (BPair.ofNat b) _ _ _]
  exact lineCombine _ _ _ _ _ _ _ h1 h2
    (lineT3 r qn a b a' b' gg (BPair.ofPos en) (BPair.ofPos ed) hab)

/-- A summand withdraws at its balance partner. -/
private theorem gapOfAdd {X W Y : BPair} (h : (X + W).oneValue Y) :
    (Y + X.swap).oneValue W := by
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_symm h) (BPair.oneValue_refl X.swap)) ?_
  rw [BPair.add_right_comm X W X.swap, BPair.add_comm X X.swap]
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.swap_add_null (BPair.oneValue_refl X)) (BPair.oneValue_refl W)) ?_
  exact BPair.unit_add W

/-- The site identity at a depth: the diagonal at the scaled rate is
the second scale's multiple of the diagonal against the rates' gap
on the cross member — the two lines' diagonal identity at the unit
second pair. -/
private theorem siteScale (r qn qd a b g m : Nat) (en ed : Pos)
    (hab : b + g = a) :
    (wellDiag r (a * qn) (b * qd) en ed m).oneValue
      (BPair.ofNat b * wellDiag r qn qd en ed m
        + (BPair.ofNat ((r + 1) * (g * qn)) * BPair.ofPos en
            * BPair.ofPos ed).swap) := by
  have hab' : 1 * b + g = a * 1 := by
    rw [Nat.one_mul, Nat.mul_one]
    exact hab
  have hld := lineDiag r qn qd a b 1 1 g m en ed hab'
  rw [Nat.one_mul qn, Nat.one_mul qd] at hld
  have hld2 : (wellDiag r (a * qn) (b * qd) en ed m
      + BPair.ofNat ((r + 1) * (g * qn)) * BPair.ofPos en
        * BPair.ofPos ed).oneValue
      (BPair.ofNat b * wellDiag r qn qd en ed m) :=
    BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_symm (BPair.ofNat_one_mul _))
        (BPair.oneValue_refl _)) hld
  have hcm : (BPair.ofNat ((r + 1) * (g * qn)) * BPair.ofPos en
      * BPair.ofPos ed
      + wellDiag r (a * qn) (b * qd) en ed m).oneValue
      (BPair.ofNat b * wellDiag r qn qd en ed m) :=
    BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _)) hld2
  exact BPair.oneValue_symm (gapOfAdd hcm)

/-- The bond weight at the scaled rate is the scale's multiple. -/
private theorem bondScale (r qd b : Nat) (ed : Pos) :
    (wellBond r (b * qd) ed).oneValue
      (BPair.ofNat b * wellBond r qd ed) := by
  show (BPair.ofNat ((r + 1) * (b * qd)) * BPair.ofPos ed
    * BPair.ofPos ed).oneValue _
  rw [ground.mulLeftComm (r + 1) b qd]
  exact countScale3 b ((r + 1) * qd) (BPair.ofPos ed) (BPair.ofPos ed)

/-- The family's square fold at the balance carrier. -/
private theorem witSqBsum (N : Nat) :
    (ground.bsum (fun k => BPair.ofNat (witVal N (k + 1))
        * BPair.ofNat (witVal N (k + 1))) (List.range N)).oneValue
      (BPair.ofNat (witSq N)) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => BPair.ofNat (witVal N (k + 1) * witVal N (k + 1)))
      (List.range N)
      (fun k _ => BPair.oneValue_symm
        (BPair.ofNat_mul (witVal N (k + 1)) (witVal N (k + 1))))) ?_
  rw [← witSq_fold N]
  exact BPair.oneValue_symm (ground.ofNat_famFold _ (List.range N))

/-- The diagonal fold at the scaled rate: the second scale's
multiple of the lower rate's own fold against the gap's cross weight
on the family's square fold. -/
private theorem scaledDiagFold (r qn qd a b g N : Nat) (en ed : Pos)
    (hab : b + g = a) :
    (ground.bsum (fun k =>
        wellDiag r (a * qn) (b * qd) en ed (k + 1)
          * (BPair.ofNat (witVal N (k + 1))
            * BPair.ofNat (witVal N (k + 1))))
      (List.range N)).oneValue
      (BPair.ofNat b
          * ground.bsum (fun k =>
              wellDiag r qn qd en ed (k + 1)
                * (BPair.ofNat (witVal N (k + 1))
                  * BPair.ofNat (witVal N (k + 1))))
            (List.range N)
        + (BPair.ofNat ((r + 1) * (g * qn)) * BPair.ofPos en
            * BPair.ofPos ed).swap * BPair.ofNat (witSq N)) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => BPair.ofNat b * (wellDiag r qn qd en ed (k + 1)
            * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1))))
        + (BPair.ofNat ((r + 1) * (g * qn)) * BPair.ofPos en
              * BPair.ofPos ed).swap
            * (BPair.ofNat (witVal N (k + 1))
              * BPair.ofNat (witVal N (k + 1))))
      (List.range N) (fun k _ => ?_)) ?_
  · refine BPair.oneValue_trans
      (BPair.mul_congr (siteScale r qn qd a b g (k + 1) en ed hab)
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.right_distrib, BPair.mul_assoc]
  · refine BPair.oneValue_trans (ground.foldB_add _ _ (List.range N)) ?_
    exact BPair.add_congr (ground.foldB_mul_left _ _ (List.range N))
      (BPair.oneValue_trans (ground.foldB_mul_left _ _ (List.range N))
        (BPair.mul_congr (BPair.oneValue_refl _) (witSqBsum N)))

/-- The family's window is occupied at a depth beyond one. -/
private theorem posSqM (N : Nat) (h : 2 ≤ N) : 0 < N * N - 1 :=
  ground.subPos (Nat.lt_of_lt_of_le (by decide +kernel : 1 < 2 * 2)
    (Nat.mul_le_mul h h))

/-- The family's square sum is occupied at a depth beyond one. -/
private theorem posWitSq (N : Nat) (h : 2 ≤ N) : 0 < witSq N := by
  have h1 : witVal N 1 = N * N - 1 := by
    show 1 * 1 * (N * N - 1 * 1) = N * N - 1
    rw [Nat.one_mul (N * N - 1 * 1)]
  rw [← witSq_fold N]
  refine Nat.lt_of_lt_of_le ?_ (ground.famFold_mem_le
    (fun k => witVal N (k + 1) * witVal N (k + 1)) (List.range N) 0
    (ground.memRange (Nat.lt_of_lt_of_le (by decide +kernel) h)))
  show 0 < witVal N 1 * witVal N 1
  rw [h1]
  exact Nat.mul_pos (posSqM N h) (posSqM N h)

/-- The lower rate's first datum is occupied at a depth beyond
one. -/
private theorem posQLow (en ed r N : Nat) (hed : 0 < ed) (h : 2 ≤ N) :
    0 < qLowNum en ed r N := by
  have hsq : 0 < (N * N - 1) ^ 2 := by
    rw [sqRead (N * N - 1)]
    exact Nat.mul_pos (posSqM N h) (posSqM N h)
  have hed2 : 0 < ed ^ 2 := by
    rw [sqRead ed]
    exact Nat.mul_pos hed hed
  refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left _
    (4 * en ^ 2 * (witSqMM N + r * witSqM N)))
  exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos r) hed2)
    (Nat.lt_of_lt_of_le hsq (Nat.le_add_left _ (witDiffSq N)))

/-- The four-factor exchange at the leading pair. -/
private theorem mulShuffle (u v w z : BPair) :
    u * (v * w * z) = v * (u * (w * z)) := by
  rw [BPair.mul_assoc v w z, BPair.mul_left_comm u v (w * z)]

/-- The scaled form's two summands against the lower rate's own
cancellation: the residue is the gap weight's balance partner. -/
private theorem strictCombine (bB K Z C W : BPair)
    (hK : (K + Z).oneValue BPair.unit) :
    ((bB * K + C.swap * W) + bB * Z).oneValue ((C * W).swap) := by
  rw [BPair.add_right_comm (bB * K) (C.swap * W) (bB * Z),
    ← BPair.left_distrib bB K Z, BPair.swap_mul C W]
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl bB) hK)
      (BPair.mul_unit bB)) (BPair.oneValue_refl ((C * W).swap))) ?_
  exact BPair.unit_add ((C * W).swap)

/-- At a member line beyond the lower rate the family's form read
sits strictly lower, the rates' gap against the family's occupied
square fold. -/
theorem witStrict : ∀ (en ed : Pos) (r N n a b g : Nat),
    2 ≤ N → N ≤ n → b + g = a → 1 ≤ g →
    inertia.quadForm
        (wellMat r (a * qLowNum (ground.posVal en) (ground.posVal ed) r N)
          (b * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n)
        (witList N n)
      < BPair.unit := by
  intro en ed r N n a b g hN h hab hg
  have hC : BPair.unit
      < BPair.ofNat ((r + 1)
            * (g * qLowNum (ground.posVal en) (ground.posVal ed) r N))
          * BPair.ofPos en * BPair.ofPos ed * BPair.ofNat (witSq N) :=
    ground.unitLtMul
      (ground.unitLtMul
        (ground.unitLtMul
          (ground.unitLtNat (Nat.mul_pos (Nat.succ_pos r)
            (Nat.mul_pos hg (posQLow (ground.posVal en) (ground.posVal ed)
              r N (ground.posVal_pos ed) hN))))
          (ground.unitLtOfPos en))
        (ground.unitLtOfPos ed))
      (ground.unitLtNat (posWitSq N hN))
  have heq : BPair.ofNat 2
        * ((BPair.ofNat b
            * wellBond r (qLowDen (ground.posVal en) (ground.posVal ed) r N)
              ed).swap
          * BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
              witVal N (k + 1) * witVal N (k + 2)))))
      = BPair.ofNat b * (BPair.ofNat 2
          * ((wellBond r (qLowDen (ground.posVal en) (ground.posVal ed) r N)
                ed).swap
            * BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
                witVal N (k + 1) * witVal N (k + 2)))))) := by
    rw [← BPair.mul_swap (BPair.ofNat b)
      (wellBond r (qLowDen (ground.posVal en) (ground.posVal ed) r N) ed)]
    exact mulShuffle (BPair.ofNat 2) (BPair.ofNat b)
      ((wellBond r (qLowDen (ground.posVal en) (ground.posVal ed) r N)
        ed).swap)
      (BPair.ofNat (ground.sumNat ((List.range N).map (fun k =>
        witVal N (k + 1) * witVal N (k + 2)))))
  have hform : (inertia.quadForm
      (wellMat r (a * qLowNum (ground.posVal en) (ground.posVal ed) r N)
        (b * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n)
      (witList N n)).oneValue
      ((BPair.ofNat ((r + 1)
            * (g * qLowNum (ground.posVal en) (ground.posVal ed) r N))
          * BPair.ofPos en * BPair.ofPos ed
        * BPair.ofNat (witSq N)).swap) := by
    refine BPair.oneValue_trans
      (wellForm r (a * qLowNum (ground.posVal en) (ground.posVal ed) r N)
        (b * qLowDen (ground.posVal en) (ground.posVal ed) r N) N n en ed
        h) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (scaledDiagFold r (qLowNum (ground.posVal en) (ground.posVal ed) r N)
        (qLowDen (ground.posVal en) (ground.posVal ed) r N) a b g N en ed
        hab)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 2))
          (BPair.mul_congr (ground.swap_congr
            (bondScale r (qLowDen (ground.posVal en) (ground.posVal ed) r N)
              b ed)) (BPair.oneValue_refl _)))
        (BPair.oneValue_of_eq heq))) ?_
    exact strictCombine (BPair.ofNat b) _ _ _ _ (kernelCancel en ed r N)
  exact BPair.lt_congr (BPair.oneValue_symm hform)
    (BPair.oneValue_refl BPair.unit) (ground.ltB_swap hC)

/-- A vector joined with the constant unit family reads itself. -/
private theorem vecAddRepl : ∀ (v : List BPair) (n : Nat), v.length = n →
    poly.oneValue (elim.vecAdd v (List.replicate n BPair.unit)) v
  | [], 0, _ => trivial
  | [], _ + 1, h => Nat.noConfusion h
  | _ :: _, 0, h => Nat.noConfusion h
  | a :: t, n + 1, h =>
    ⟨BPair.add_unit a, vecAddRepl t n (Nat.succ.inj h)⟩

/-- The combination at one member is that member's scale. -/
private theorem combo_one (n : Nat) (c : BPair) (u : List BPair)
    (hu : u.length = n) :
    poly.oneValue (elim.combo n [c] [u]) (elim.vecScale c u) :=
  vecAddRepl (elim.vecScale c u) n
    ((ground.length_map (fun y => c * y) u).trans hu)

/-- The family is the count's own witness at every member line: one
lower-side member forces the reversal count occupied at every split
of the head's datum (`lem:inertia`'s forcing clause). -/
theorem witCount : ∀ (en ed : Pos) (r N n a b g : Nat),
    2 ≤ N → N ≤ n → b + g = a → 1 ≤ g →
    ∀ sp : inertia.Split n,
      inertia.splitRead
        (wellMat r (a * qLowNum (ground.posVal en) (ground.posVal ed) r N)
          (b * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n)
        sp →
      1 ≤ inertia.revAt sp := by
  intro en ed r N n a b g hN h hab hg sp hsp
  refine inertia.forcing _ sp hsp [witList N n] ⟨witList_len N n, trivial⟩ ?_
  intro cs hcs hu
  match cs, hcs, hu with
  | [], hcs, _ => exact Nat.noConfusion hcs
  | _ :: _ :: _, hcs, _ => exact Nat.noConfusion (Nat.succ.inj hcs)
  | [c], _, hu =>
    have hcu : ¬ c.oneValue BPair.unit := fun hc => hu ⟨hc, trivial⟩
    have hscale := inertia.quadScaleVec
      (wellMat r (a * qLowNum (ground.posVal en) (ground.posVal ed) r N)
        (b * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n)
      c (witList N n) (elim.combo n [c] [witList N n])
      (combo_one n c (witList N n) (witList_len N n))
    exact BPair.lt_congr (BPair.oneValue_symm hscale)
      (BPair.oneValue_refl BPair.unit)
      (BPair.lt_congr
        (BPair.oneValue_of_eq (BPair.mul_comm _ (c * c)))
        (BPair.unit_mul (c * c))
        (ground.ltB_mulPos
          (witStrict en ed r N n a b g hN h hab hg)
          (ground.sq_pos hcu)))

/-- The count four's scale is the doubled doubling. -/
private theorem fourRead (c : BPair) :
    (BPair.ofNat 4 * c).oneValue (c + c + (c + c)) := by
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.ofNat_add 2 2) (BPair.oneValue_refl c)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.right_distrib (BPair.ofNat 2) (BPair.ofNat 2) c)) ?_
  exact BPair.add_congr (BPair.ofNat_two_mul c) (BPair.ofNat_two_mul c)

/-- The doubled doubling splits over a sum. -/
private theorem four_add (z w : BPair) :
    (z + w) + (z + w) + ((z + w) + (z + w))
      = (z + z + (z + z)) + (w + w + (w + w)) := by
  rw [BPair.add_add_comm z w z w,
    BPair.add_add_comm (z + z) (w + w) (z + z) (w + w)]

/-- The completed square at the doubled leading datum: the
quadruple of a form's three summands against the doubled leading
datum's square. -/
private theorem capCore (A E R : BPair) :
    (A * A + (A * E + R)) + (A * A + (A * E + R))
        + ((A * A + (A * E + R)) + (A * A + (A * E + R))) + E * E
      = (A + A + E) * (A + A + E) + (R + R + (R + R)) := by
  rw [four_add (A * A) (A * E + R), four_add (A * E) R,
    BPair.sq_expand (A + A) E, BPair.sq_expand A A,
    BPair.right_distrib A A E,
    ← BPair.add_assoc (A * A + A * A + (A * A + A * A))
      (A * E + A * E + (A * E + A * E)) (R + R + (R + R)),
    BPair.add_right_comm (A * A + A * A + (A * A + A * A)
        + (A * E + A * E + (A * E + A * E)))
      (R + R + (R + R)) (E * E),
    BPair.add_right_comm (A * A + A * A + (A * A + A * A))
      (A * E + A * E + (A * E + A * E)) (E * E)]


/-- Two vectors joined with the constant unit family read their own
join. -/
private theorem vecAddRepl2 : ∀ (A B : List BPair) (n : Nat),
    A.length = n → B.length = n →
    poly.oneValue
      (elim.vecAdd A (elim.vecAdd B (List.replicate n BPair.unit)))
      (elim.vecAdd A B)
  | [], [], 0, _, _ => trivial
  | [], [], _ + 1, h, _ => Nat.noConfusion h
  | [], _ :: _, 0, _, h => Nat.noConfusion h
  | [], _ :: _, _ + 1, h, _ => Nat.noConfusion h
  | _ :: _, [], 0, h, _ => Nat.noConfusion h
  | _ :: _, [], _ + 1, _, h => Nat.noConfusion h
  | _ :: _, _ :: _, 0, h, _ => Nat.noConfusion h
  | a :: A', b :: B', m + 1, hA, hB =>
    ⟨BPair.add_congr (BPair.oneValue_refl a) (BPair.add_unit b),
     vecAddRepl2 A' B' m (Nat.succ.inj hA) (Nat.succ.inj hB)⟩

/-- The combination at two members is the members' scaled join. -/
private theorem comboPair (n : Nat) (c1 c2 : BPair) (u w : List BPair)
    (hu : u.length = n) (hw : w.length = n) :
    poly.oneValue (elim.combo n [c1, c2] [u, w])
      (elim.vecAdd (elim.vecScale c1 u) (elim.vecScale c2 w)) :=
  vecAddRepl2 (elim.vecScale c1 u) (elim.vecScale c2 w) n
    ((elim.length_vecScale c1 u).trans hu)
    ((elim.length_vecScale c2 w).trans hw)

/-- The cross pairing at two scaled vectors carries both scales. -/
private theorem crossScale (S : elim.Mat) (c1 c2 : BPair)
    (u w : List BPair) :
    (elim.dotN (elim.vecScale c1 u)
        (elim.matVec S (elim.vecScale c2 w))).oneValue
      (c1 * (c2 * elim.dotN u (elim.matVec S w))) := by
  refine BPair.oneValue_trans (elim.dotN_congrR _ _ _
    (elim.matVec_vecScale_free S c2 w)) ?_
  refine BPair.oneValue_trans
    (elim.dotN_scaleRow_free c1 u (elim.vecScale c2 (elim.matVec S w))) ?_
  exact BPair.mul_congr (BPair.oneValue_refl c1)
    (elim.dotN_scaleV c2 u (elim.matVec S w))

/-- The form at a two-member combination: the two squares at the
scales' own with the cross reads at their product. -/
private theorem quadPairExpand (S : elim.Mat) (n : Nat)
    (hSr : elim.rowsLen n S) (hSl : S.length = n)
    (c1 c2 : BPair) (u w : List BPair)
    (hu : u.length = n) (hw : w.length = n) :
    (inertia.quadForm S
        (elim.vecAdd (elim.vecScale c1 u) (elim.vecScale c2 w))).oneValue
      (c1 * c1 * inertia.quadForm S u
        + (c1 * c2 * (elim.dotN u (elim.matVec S w)
              + elim.dotN w (elim.matVec S u))
          + c2 * c2 * inertia.quadForm S w)) := by
  refine BPair.oneValue_trans
    (inertia.quadAdd S n hSr hSl (elim.vecScale c1 u) (elim.vecScale c2 w)
      ((elim.length_vecScale c1 u).trans hu)
      ((elim.length_vecScale c2 w).trans hw)) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.add_congr
      (inertia.quadScaleVec S c1 u (elim.vecScale c1 u)
        (poly.oneValue_refl _))
      (crossScale S c1 c2 u w))
    (BPair.add_congr (crossScale S c2 c1 w u)
      (inertia.quadScaleVec S c2 w (elim.vecScale c2 w)
        (poly.oneValue_refl _)))) ?_
  refine BPair.oneValue_of_eq ?_
  rw [BPair.mul_left_comm c2 c1 (elim.dotN w (elim.matVec S u)),
    ← BPair.mul_assoc c1 c2 (elim.dotN u (elim.matVec S w)),
    ← BPair.mul_assoc c1 c2 (elim.dotN w (elim.matVec S u)),
    BPair.add_assoc (c1 * c1 * inertia.quadForm S u)
      (c1 * c2 * elim.dotN u (elim.matVec S w))
      (c1 * c2 * elim.dotN w (elim.matVec S u)
        + c2 * c2 * inertia.quadForm S w),
    ← BPair.add_assoc (c1 * c2 * elim.dotN u (elim.matVec S w))
      (c1 * c2 * elim.dotN w (elim.matVec S u))
      (c2 * c2 * inertia.quadForm S w),
    ← BPair.left_distrib (c1 * c2) (elim.dotN u (elim.matVec S w))
      (elim.dotN w (elim.matVec S u))]

/-- The form's product at the leading entry, the square's own. -/
private theorem qMulSq (q c : BPair) : q * (c * c * q) = c * q * (c * q) := by
  rw [BPair.mul_left_comm q (c * c) q, BPair.mul_assoc c q (c * q),
    BPair.mul_left_comm q c q, ← BPair.mul_assoc c c (q * q)]

/-- The form's product at the cross entry. -/
private theorem qMulCross (q c1 c2 X : BPair) :
    q * (c1 * c2 * X) = c1 * q * (c2 * X) := by
  rw [BPair.mul_left_comm q (c1 * c2) X, BPair.mul_assoc c1 q (c2 * X),
    BPair.mul_left_comm q c2 X, ← BPair.mul_assoc c1 c2 (q * X)]

/-- A scaled datum's square at the scale's own square. -/
private theorem scaleSq (c X : BPair) : c * X * (c * X) = c * c * (X * X) := by
  rw [BPair.mul_assoc c X (c * X), BPair.mul_left_comm X c X,
    ← BPair.mul_assoc c c (X * X)]

/-- The cap pair's strict read at an occupied second scale: the
completed square against the discriminant's own comparison. -/
private theorem capStrict {q11 q22 X c1 c2 : BPair}
    (hq : q11 < BPair.unit)
    (hd : X * X < BPair.ofNat 4 * (q11 * q22))
    (hc2 : ¬ c2.oneValue BPair.unit) :
    c1 * c1 * q11 + (c1 * c2 * X + c2 * c2 * q22) < BPair.unit := by
  have hqQ : q11 * (c1 * c1 * q11 + (c1 * c2 * X + c2 * c2 * q22))
      = c1 * q11 * (c1 * q11)
        + (c1 * q11 * (c2 * X) + c2 * c2 * (q11 * q22)) := by
    rw [BPair.left_distrib q11 (c1 * c1 * q11) (c1 * c2 * X + c2 * c2 * q22),
      BPair.left_distrib q11 (c1 * c2 * X) (c2 * c2 * q22),
      qMulSq q11 c1, qMulCross q11 c1 c2 X,
      BPair.mul_left_comm q11 (c2 * c2) q22]
  have hZ' : (c2 * c2 * (BPair.ofNat 4 * (q11 * q22))).oneValue
      (c2 * c2 * (q11 * q22) + c2 * c2 * (q11 * q22)
        + (c2 * c2 * (q11 * q22) + c2 * c2 * (q11 * q22))) := by
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (fourRead (q11 * q22))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.left_distrib (c2 * c2) (q11 * q22 + q11 * q22)
        (q11 * q22 + q11 * q22),
      BPair.left_distrib (c2 * c2) (q11 * q22) (q11 * q22)]
  have hid : (BPair.ofNat 4
        * (q11 * (c1 * c1 * q11 + (c1 * c2 * X + c2 * c2 * q22)))
      + c2 * c2 * (X * X)).oneValue
      ((c1 * q11 + c1 * q11 + c2 * X) * (c1 * q11 + c1 * q11 + c2 * X)
        + (c2 * c2 * (q11 * q22) + c2 * c2 * (q11 * q22)
          + (c2 * c2 * (q11 * q22) + c2 * c2 * (q11 * q22)))) := by
    rw [hqQ, ← scaleSq c2 X]
    refine BPair.oneValue_trans (BPair.add_congr
      (fourRead _) (BPair.oneValue_refl (c2 * X * (c2 * X)))) ?_
    exact BPair.oneValue_of_eq
      (capCore (c1 * q11) (c2 * X) (c2 * c2 * (q11 * q22)))
  have hlt : c2 * c2 * (X * X)
      < c2 * c2 * (BPair.ofNat 4 * (q11 * q22)) :=
    BPair.lt_congr (BPair.oneValue_of_eq (BPair.mul_comm (X * X) (c2 * c2)))
      (BPair.oneValue_of_eq
        (BPair.mul_comm (BPair.ofNat 4 * (q11 * q22)) (c2 * c2)))
      (ground.ltB_mulPos hd (ground.sq_pos hc2))
  have hUV : BPair.unit
      < c2 * c2 * (BPair.ofNat 4 * (q11 * q22))
        + (c2 * c2 * (X * X)).swap :=
    ground.unitLt_of_swap_lt hlt
  have hW3 : (BPair.ofNat 4
      * (q11 * (c1 * c1 * q11 + (c1 * c2 * X + c2 * c2 * q22)))).oneValue
      ((c1 * q11 + c1 * q11 + c2 * X) * (c1 * q11 + c1 * q11 + c2 * X)
        + (c2 * c2 * (BPair.ofNat 4 * (q11 * q22))
          + (c2 * c2 * (X * X)).swap)) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.add_swap_self _ ((c2 * c2 * (X * X)).swap)))
      ?_
    refine BPair.oneValue_trans
      (BPair.add_congr hid (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hZ'))
      (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_of_eq (BPair.add_assoc _ _ _)
  have hpos : BPair.unit < BPair.ofNat 4
      * (q11 * (c1 * c1 * q11 + (c1 * c2 * X + c2 * c2 * q22))) :=
    ground.leB_ltB_trans (ground.unitLeSq (c1 * q11 + c1 * q11 + c2 * X))
      (BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hW3)
        (ground.ltB_addPos hUV))
  have hK : BPair.ofNat 4 * q11 < BPair.unit :=
    BPair.lt_congr (BPair.oneValue_of_eq (BPair.mul_comm q11 (BPair.ofNat 4)))
      (BPair.unit_mul (BPair.ofNat 4))
      (ground.ltB_mulPos hq (ground.unitLtNat (by decide +kernel)))
  have hposKQ : BPair.unit
      < (BPair.ofNat 4 * q11).swap
        * (c1 * c1 * q11 + (c1 * c2 * X + c2 * c2 * q22)).swap := by
    refine BPair.lt_congr (BPair.oneValue_refl _) ?_ hpos
    refine BPair.oneValue_of_eq ?_
    rw [BPair.swap_mul_swap, BPair.mul_assoc (BPair.ofNat 4) q11
      (c1 * c1 * q11 + (c1 * c2 * X + c2 * c2 * q22))]
  have hQs : BPair.unit
      < (c1 * c1 * q11 + (c1 * c2 * X + c2 * c2 * q22)).swap :=
    inertia.scaleReflLt (ground.ltB_swap hK) hposKQ
  exact ground.ltB_swap hQs

/-- The cap pair's strict read at a vacant second scale: the leading
entry's own strict order at an occupied first scale. -/
private theorem capStrictVac {q11 q22 X c1 c2 : BPair}
    (hq : q11 < BPair.unit) (hc1 : ¬ c1.oneValue BPair.unit)
    (hc2 : c2.oneValue BPair.unit) :
    c1 * c1 * q11 + (c1 * c2 * X + c2 * c2 * q22) < BPair.unit := by
  have hv1 : (c1 * c2 * X).oneValue BPair.unit :=
    BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl c1) hc2) (BPair.mul_unit c1))
        (BPair.oneValue_refl X)) (BPair.unit_mul X)
  have hv2 : (c2 * c2 * q22).oneValue BPair.unit :=
    BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_trans
        (BPair.mul_congr hc2 (BPair.oneValue_refl c2)) (BPair.unit_mul c2))
        (BPair.oneValue_refl q22)) (BPair.unit_mul q22)
  refine BPair.lt_congr ?_ (BPair.oneValue_refl BPair.unit)
    (BPair.lt_congr (BPair.oneValue_of_eq (BPair.mul_comm q11 (c1 * c1)))
      (BPair.unit_mul (c1 * c1))
      (ground.ltB_mulPos hq (ground.sq_pos hc1)))
  refine BPair.oneValue_symm (BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_refl (c1 * c1 * q11))
    (BPair.oneValue_trans (BPair.add_congr hv1 hv2)
      (BPair.unit_add BPair.unit))) (BPair.add_unit (c1 * c1 * q11)))

/-- The cap pair's read: at two members whose compressed two-by-two
reads the lower side at the leading entry and its doubled cross read
below the diagonal product's quadruple, every split of the datum
reads the reversal count at two or beyond — the second root below
the cap, the compression's counts at or below the full form's. -/
theorem capForcing : ∀ {n : Nat} (S : elim.Mat) (x x' : List BPair),
    x.length = n → x'.length = n →
    inertia.quadForm S x < BPair.unit →
    (elim.dotN x (elim.matVec S x') + elim.dotN x' (elim.matVec S x))
        * (elim.dotN x (elim.matVec S x')
          + elim.dotN x' (elim.matVec S x))
      < BPair.ofNat 4 * (inertia.quadForm S x * inertia.quadForm S x') →
    ∀ sp : inertia.Split n, inertia.splitRead S sp →
      2 ≤ inertia.revAt sp := by
  intro n S x x' hx hx' hq hd sp hsp
  have hSl : S.length = n := elim.sqAt_len hsp.1
  have hSr : elim.rowsLen n S := elim.rowsLen_of_sqAt hsp.1
  refine inertia.forcing S sp hsp [x, x'] ⟨hx, hx', trivial⟩ ?_
  intro cs hcs hu
  match cs, hcs, hu with
  | [], hcs, _ => exact Nat.noConfusion hcs
  | [_], hcs, _ => exact Nat.noConfusion (Nat.succ.inj hcs)
  | _ :: _ :: _ :: _, hcs, _ =>
    exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hcs))
  | [c1, c2], _, hu =>
    have hexp : (inertia.quadForm S
        (elim.combo n [c1, c2] [x, x'])).oneValue
        (c1 * c1 * inertia.quadForm S x
          + (c1 * c2 * (elim.dotN x (elim.matVec S x')
                + elim.dotN x' (elim.matVec S x))
            + c2 * c2 * inertia.quadForm S x')) :=
      BPair.oneValue_trans
        (inertia.quadForm_congr S (comboPair n c1 c2 x x' hx hx'))
        (quadPairExpand S n hSr hSl c1 c2 x x' hx hx')
    refine BPair.lt_congr (BPair.oneValue_symm hexp)
      (BPair.oneValue_refl BPair.unit) ?_
    match (inferInstance : Decidable (c2.oneValue BPair.unit)) with
    | isTrue h2 => exact capStrictVac hq (fun h1 => hu ⟨h1, h2, trivial⟩) h2
    | isFalse h2 => exact capStrict hq hd h2

/-- The walk's minor at a depth, the walk recursion's first member. -/
def wellWalk (r qn qd : Nat) (en ed : Pos) (k : Nat) : BPair :=
  (walkGo (wellBond r qd ed)
    (fun m => wellDiag r qn qd en ed (m + 1)) k).1

/-- The margin's positive carrier at a member off equal members; at
equal members the read is off every consumer's guard. -/
def margP (x : BPair) : Pos :=
  posOfSucc ((ground.posVal x.fst - ground.posVal x.snd)
    + (ground.posVal x.snd - ground.posVal x.fst) - 1)

/-- The pivot's cleared datum at a depth: the consecutive minors'
product against the predecessor's squared margin, the cofactor's own
cleared representative. -/
def pivotQ (r qn qd : Nat) (en ed : Pos) (k : Nat) : greenprod.MatQ :=
  ([[wellWalk r qn qd en ed k * wellWalk r qn qd en ed (k - 1)]],
   Pos.pow (margP (wellWalk r qn qd en ed (k - 1))) 2)

/-- The recursion witness's cleared datum at a depth. -/
def pivotR (r qn qd : Nat) (en ed : Pos) (k : Nat) : greenprod.MatQ :=
  ([[(wellBond r qd ed).swap * wellWalk r qn qd en ed (k - 1)
      * wellWalk r qn qd en ed k]],
   Pos.pow (margP (wellWalk r qn qd en ed k)) 2)

/-- A balance pair is its two members' value counts.  -/
private theorem countsOfPair (x : BPair) :
    (BPair.ofCounts (ground.posVal x.fst) (ground.posVal x.snd)).oneValue x := by
  show (BPair.ofNat (ground.posVal x.fst)
    + (BPair.ofNat (ground.posVal x.snd)).swap).oneValue x
  rw [← BPair.ofPos_val x.fst, ← BPair.ofPos_val x.snd]
  show x.fst + Pos.one + Pos.one + x.snd
    = x.fst + (Pos.one + (x.snd + Pos.one))
  rw [ground.add_assoc x.fst Pos.one Pos.one,
    ground.add_assoc x.fst (Pos.one + Pos.one) x.snd,
    ground.add_assoc Pos.one Pos.one x.snd,
    ground.add_comm Pos.one x.snd]

/-- Two counts off each other have an occupied margin. -/
private theorem margPos {u v : Nat} (h : ¬ u = v) : 0 < marg u v := by
  match Nat.lt_or_ge u v with
  | Or.inl h1 =>
    show 0 < (u - v) + (v - u)
    exact Nat.lt_of_lt_of_le (ground.subPos h1) (Nat.le_add_left _ _)
  | Or.inr h2 =>
    show 0 < (u - v) + (v - u)
    exact Nat.lt_of_lt_of_le
      (ground.subPos (Nat.lt_of_le_of_ne h2 (fun he => h he.symm)))
      (Nat.le_add_right _ _)

/-- The margin's carrier reads the two members' own margin, at a
datum off equal members. -/
private theorem margP_val (x : BPair) (h : ¬ x.oneValue BPair.unit) :
    ground.posVal (margP x)
      = marg (ground.posVal x.fst) (ground.posVal x.snd) := by
  have hne : ¬ (ground.posVal x.fst = ground.posVal x.snd) := fun hu =>
    h (BPair.oneValue_trans (BPair.oneValue_symm (countsOfPair x))
      (BPair.ofCounts_unit.mpr hu))
  show (marg (ground.posVal x.fst) (ground.posVal x.snd) - 1) + 1 = _
  exact ground.subAdd (margPos hne)

/-- The margin's square is the datum's own square, at a datum off
equal members. -/
private theorem margP_sq (x : BPair) (h : ¬ x.oneValue BPair.unit) :
    (BPair.ofPos (Pos.pow (margP x) 2)).oneValue (x * x) := by
  refine BPair.oneValue_trans (ground.ofPos_pow (margP x) 2) ?_
  refine BPair.oneValue_trans (bpowTwo (BPair.ofPos (margP x))) ?_
  rw [BPair.ofPos_val (margP x), margP_val x h]
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.ofNat_mul
      (marg (ground.posVal x.fst) (ground.posVal x.snd))
      (marg (ground.posVal x.fst) (ground.posVal x.snd)))) ?_
  rw [← sqRead (marg (ground.posVal x.fst) (ground.posVal x.snd))]
  exact BPair.oneValue_trans
    (margSq_read (ground.posVal x.fst) (ground.posVal x.snd))
    (BPair.mul_congr (countsOfPair x) (countsOfPair x))

/-- The order-one identity carrier. -/
private def id1 : elim.SqMat 1 := ⟨inertia.idMat 1, by decide +kernel⟩

/-- The order-one identity congruence, its own adjugate at the
determinant one. -/
private theorem cc1 : inertia.clearedCongr id1 id1 := by decide +kernel

/-- The order-one split at a stated entry: the identity congruence
with the entry the single nonsingular block. -/
private def split1 (x : BPair) : inertia.Split 1 :=
  ⟨id1, id1, [inertia.SBlock.one x], 0, rfl⟩

/-- A one-by-one datum reading an occupied entry splits at that
entry's order-one certificate. -/
private theorem splitRead_one (x y : BPair) (hx : ¬ x.oneValue BPair.unit)
    (hy : y.oneValue x) : inertia.splitRead [[y]] (split1 x) := by
  have hSr : elim.rowsLen 1 [[y]] := ⟨rfl, trivial⟩
  have hy1 : elim.matOneValue [[y]]
      (inertia.blockMat [inertia.SBlock.one x] 0) := ⟨⟨hy, trivial⟩, trivial⟩
  refine ⟨rfl, cc1, ?_, ?_⟩
  · show elim.matOneValue
      (elim.matMul (elim.transposeM (inertia.idMat 1))
        (elim.matMul [[y]] (inertia.idMat 1)))
      (inertia.blockMat [inertia.SBlock.one x] 0)
    rw [inertia.transposeM_idMat 1]
    refine elim.matOne_trans ?_ hy1
    refine elim.matOne_trans ?_
      (inertia.idMat_matMul (k := 1) 1 [[y]] hSr rfl (by decide +kernel))
    exact elim.matMul_congrR (n := 1) (k := 1) (inertia.idMat 1)
      (elim.matMul [[y]] (inertia.idMat 1)) [[y]]
      (elim.rowsLen_cast
        (by rw [inertia.transposeM_idMat 1, inertia.idMat_len 1])
        (elim.rowsLen_matMul [[y]] (inertia.idMat 1)))
      hSr ((elim.length_matMul [[y]] (inertia.idMat 1)).trans rfl) rfl
      (by decide +kernel)
      (inertia.matMul_idR (k := 1) 1 [[y]] hSr rfl (by decide +kernel) (by decide +kernel))
  · show (!(decide (x.oneValue BPair.unit)) && true) = true
    rw [decide_eq_false hx]
    rfl

/-- A mapped key range conses at its nought key, the tail the
shifted family's own map. -/
private theorem rangeMapCons {α : Type} (f g : Nat → α) (n : Nat)
    (h : ∀ j, f (j + 1) = g j) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map g := by
  rw [ground.range_cons n]
  show f 0 :: ((List.range n).map (fun j => j + 1)).map f
    = f 0 :: (List.range n).map g
  rw [ground.map_map (fun j => j + 1) f (List.range n),
    ground.map_congr_all (fun j => f (j + 1)) g h (List.range n)]

/-- The well walk's recursion read: the arriving minor against the
withdrawn one at the bond's square is the diagonal's multiple of the
standing minor. -/
private theorem wellWalk_rec (r qn qd : Nat) (en ed : Pos) (m : Nat) :
    (wellWalk r qn qd en ed (m + 2)
        + wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed m).oneValue
      (wellDiag r qn qd en ed (m + 2) * wellWalk r qn qd en ed (m + 1)) :=
  walk_rec (wellBond r qd ed) (fun j => wellDiag r qn qd en ed (j + 1)) m

/-- The pivot cross product's exchange: the two minors' product
against the witness's is the minors' squares at the bond. -/
private theorem prodShuffle (u v w : BPair) :
    u * v * (w * v * u) = v * v * (u * u) * w := by
  rw [BPair.mul_assoc w v u, BPair.mul_assoc u v (w * (v * u)),
    BPair.mul_left_comm v w (v * u), BPair.mul_comm v u,
    BPair.mul_left_comm v u v, BPair.mul_left_comm w u (v * v),
    BPair.mul_assoc (v * v) (u * u) w, BPair.mul_assoc v v ((u * u) * w),
    BPair.mul_assoc u u w, BPair.mul_left_comm w v v,
    BPair.mul_left_comm u v (w * v), BPair.mul_left_comm u v (u * (w * v)),
    BPair.mul_comm w v, BPair.mul_left_comm u v w,
    BPair.mul_left_comm u v (u * w)]

/-- A cleared entry's cross-scaled read. -/
private theorem qEntry {x y : BPair} {p q : Pos}
    (h : (BPair.ofPos q * x).oneValue (BPair.ofPos p * y)) :
    (x.scale q).oneValue (y.scale p) :=
  BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofPos_scale q x))
    (BPair.oneValue_trans h (BPair.ofPos_scale p y))

/-- The two margins' clearing reads the two minors' squares. -/
private theorem margPair (r qn qd : Nat) (en ed : Pos) (m k : Nat)
    (h0 : ¬ (wellWalk r qn qd en ed m).oneValue BPair.unit)
    (h1 : ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit) :
    (BPair.ofPos (Pos.pow (margP (wellWalk r qn qd en ed m)) 2
        * Pos.pow (margP (wellWalk r qn qd en ed k)) 2)).oneValue
      (wellWalk r qn qd en ed m * wellWalk r qn qd en ed m
        * (wellWalk r qn qd en ed k * wellWalk r qn qd en ed k)) :=
  BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofPos_mul _ _))
    (BPair.mul_congr (margP_sq _ h0) (margP_sq _ h1))

/-- Two order-one cleared data read one value at the cross-scaled
entries. -/
private theorem oneQ11 {a b : BPair} {p q : Pos}
    (h : (BPair.ofPos q * a).oneValue (BPair.ofPos p * b)) :
    greenprod.oneValueQ ([[a]], p) ([[b]], q) :=
  ⟨⟨qEntry h, trivial⟩, trivial⟩


/-- The recursion's witness step at a depth: the pivot against the
witness reads the off block's exchange, the two margins clearing the
minors' squares. -/
private theorem pivotCross (r qn qd : Nat) (en ed : Pos) (n : Nat)
    (h0 : ¬ (wellWalk r qn qd en ed n).oneValue BPair.unit)
    (h1 : ¬ (wellWalk r qn qd en ed (n + 1)).oneValue BPair.unit) :
    greenprod.oneValueQ
      (greenprod.mulQ (pivotQ r qn qd en ed (n + 1))
        (pivotR r qn qd en ed (n + 1)))
      (greenprod.ofM (elim.transposeM [[(wellBond r qd ed).swap]])) := by
  refine oneQ11
    (a := elim.dotN [wellWalk r qn qd en ed (n + 1) * wellWalk r qn qd en ed n]
      [(wellBond r qd ed).swap * wellWalk r qn qd en ed n
        * wellWalk r qn qd en ed (n + 1)])
    (b := (wellBond r qd ed).swap)
    (p := Pos.pow (margP (wellWalk r qn qd en ed n)) 2
      * Pos.pow (margP (wellWalk r qn qd en ed (n + 1))) 2)
    (q := Pos.one) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_trans (BPair.ofPos_one_mul _)
      (BPair.oneValue_trans (inertia.dotN_single _ _)
        (BPair.oneValue_of_eq (prodShuffle (wellWalk r qn qd en ed (n + 1))
          (wellWalk r qn qd en ed n) (wellBond r qd ed).swap))))
    (BPair.oneValue_symm ?_)
  exact BPair.mul_congr
    (margPair r qn qd en ed n (n + 1) h0 h1)
    (BPair.oneValue_refl _)

/-- The bond's repeated factor collects at the square. -/
private theorem bondShuffle (w a b : BPair) : w * (w * a * b) = w * w * a * b := by
  rw [← BPair.mul_assoc w (w * a) b, ← BPair.mul_assoc w w a]

/-- A product's two trailing factors exchange across the leading
one. -/
private theorem mulShuffleACB (A B C : BPair) :
    A * (B * C) = A * C * B := by
  rw [BPair.mul_comm B C, ← BPair.mul_assoc A C B]

/-- The scaled triple's exchange at the repeated member. -/
private theorem joinShuffle (c x y : BPair) :
    c * (y * x * x) = c * (x * x) * y := by
  rw [BPair.mul_assoc y x x]
  exact mulShuffleACB c y (x * x)

/-- The recursion's join at the balance carrier: the pivot against
the bond-weighted witness reads the diagonal, the predecessor's square
the shared clearing. -/
private theorem joinCore (A2 A1 A0 d b : BPair) (P : Pos)
    (hP : (BPair.ofPos P).oneValue (A1 * A1))
    (hrec : (A2 + b * b * A0).oneValue (d * A1)) :
    (BPair.ofPos Pos.one
        * ((A2 * A1).scale (Pos.one * P)
          + (elim.dotN [b.swap] [b.swap * A0 * A1]).scale P)).oneValue
      (BPair.ofPos (P * (Pos.one * P)) * d) := by
  rw [ground.one_mul P]
  refine BPair.oneValue_trans (BPair.ofPos_one_mul _) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_symm (BPair.ofPos_scale P (A2 * A1)))
      (BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.ofPos_scale P _))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (inertia.dotN_single b.swap (b.swap * A0 * A1))))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.left_distrib (BPair.ofPos P) (A2 * A1)
        (b.swap * (b.swap * A0 * A1))).symm) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_of_eq
          (by rw [bondShuffle b.swap A0 A1, BPair.swap_sq b])))) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_of_eq
        (BPair.right_distrib A2 (b * b * A0) A1).symm)) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.mul_congr hrec (BPair.oneValue_refl A1))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (joinShuffle (BPair.ofPos P) A1 d)) ?_
  exact BPair.oneValue_symm
    (BPair.mul_congr
      (BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofPos_mul P P))
        (BPair.mul_congr (BPair.oneValue_refl _) hP))
      (BPair.oneValue_refl d))

/-- The well head's diagonal slabs, deep end first. -/
private def wDiagL (r qn qd : Nat) (en ed : Pos) (n : Nat) : List elim.Mat :=
  (List.range n).map (fun k => [[wellDiag r qn qd en ed (n - k)]])

/-- The well head's off-diagonal slabs, the bond weight throughout. -/
private def wOffL (r qd : Nat) (ed : Pos) (n : Nat) : List elim.Mat :=
  (List.range (n - 1)).map (fun _ => [[(wellBond r qd ed).swap]])

/-- The tail recursion's pivots at the slab indexing. -/
private def wXL (r qn qd : Nat) (en ed : Pos) (n : Nat) : List greenprod.MatQ :=
  (List.range n).map (fun j => pivotQ r qn qd en ed (n - j))

/-- The tail recursion's witnesses at the slab indexing. -/
private def wRL (r qn qd : Nat) (en ed : Pos) (n : Nat) : List greenprod.MatQ :=
  (List.range (n - 1)).map (fun i => pivotR r qn qd en ed (n - 1 - i))

/-- The diagonal slab list conses at the deepest slab. -/
private theorem wDiagL_cons (r qn qd : Nat) (en ed : Pos) (n : Nat) :
    wDiagL r qn qd en ed (n + 1)
      = [[wellDiag r qn qd en ed (n + 1)]] :: wDiagL r qn qd en ed n :=
  rangeMapCons _ _ n (fun j => by rw [Nat.succ_sub_succ n j])

/-- The off-diagonal slab list conses at the leading bond. -/
private theorem wOffL_cons (r qd : Nat) (ed : Pos) (n : Nat) :
    wOffL r qd ed (n + 2) = [[(wellBond r qd ed).swap]] :: wOffL r qd ed (n + 1) :=
  rangeMapCons _ _ n (fun _ => rfl)

/-- The pivot list conses at the deepest pivot. -/
private theorem wXL_cons (r qn qd : Nat) (en ed : Pos) (n : Nat) :
    wXL r qn qd en ed (n + 1)
      = pivotQ r qn qd en ed (n + 1) :: wXL r qn qd en ed n :=
  rangeMapCons _ _ n (fun j => by rw [Nat.succ_sub_succ n j])

/-- The witness list conses at the leading witness. -/
private theorem wRL_cons (r qn qd : Nat) (en ed : Pos) (n : Nat) :
    wRL r qn qd en ed (n + 2)
      = pivotR r qn qd en ed (n + 1) :: wRL r qn qd en ed (n + 1) :=
  rangeMapCons _ _ n (fun j => by
    show pivotR r qn qd en ed (n + 1 - (j + 1))
      = pivotR r qn qd en ed (n - j)
    rw [Nat.succ_sub_succ n j])


/-- The walk's seed minor is the vacant product. -/
private theorem walkNought (b : BPair) (a : Nat → BPair) :
    (walkGo b a 0).1 = BPair.ofNat 1 := rfl

/-- The walk's first minor is the head's diagonal entry. -/
private theorem walkOne (b : BPair) (a : Nat → BPair) :
    (walkGo b a 1).1 = a 0 := rfl

/-- The well walk's seed minor is the vacant product. -/
private theorem wellWalk_zero (r qn qd : Nat) (en ed : Pos) :
    wellWalk r qn qd en ed 0 = BPair.ofNat 1 :=
  walkNought (wellBond r qd ed) (fun m => wellDiag r qn qd en ed (m + 1))

/-- The well walk's first minor is the depth-one diagonal. -/
private theorem wellWalk_one (r qn qd : Nat) (en ed : Pos) :
    wellWalk r qn qd en ed 1 = wellDiag r qn qd en ed 1 :=
  walkOne (wellBond r qd ed) (fun m => wellDiag r qn qd en ed (m + 1))

/-- The recursion's seed at the boundary slab: the depth-one pivot
is that slab's own diagonal. -/
private theorem pivotBase (r qn qd : Nat) (en ed : Pos) :
    greenprod.oneValueQ (pivotQ r qn qd en ed 1)
      (greenprod.ofM [[wellDiag r qn qd en ed 1]]) := by
  refine oneQ11 (a := wellWalk r qn qd en ed 1 * wellWalk r qn qd en ed 0)
    (b := wellDiag r qn qd en ed 1) (p := Pos.one) (q := Pos.one) ?_
  rw [wellWalk_one r qn qd en ed, wellWalk_zero r qn qd en ed]
  exact BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.mul_one_read (wellDiag r qn qd en ed 1))
/-- The recursion's join at a depth: the pivot against the
bond-weighted witness reads the diagonal entry. -/
private theorem pivotJoin (r qn qd : Nat) (en ed : Pos) (n : Nat)
    (h1 : ¬ (wellWalk r qn qd en ed (n + 1)).oneValue BPair.unit) :
    greenprod.oneValueQ
      (greenprod.addQ (pivotQ r qn qd en ed (n + 2))
        (greenprod.mulQ (greenprod.ofM [[(wellBond r qd ed).swap]])
          (pivotR r qn qd en ed (n + 1))))
      (greenprod.ofM [[wellDiag r qn qd en ed (n + 2)]]) :=
  oneQ11 (joinCore (wellWalk r qn qd en ed (n + 2))
    (wellWalk r qn qd en ed (n + 1)) (wellWalk r qn qd en ed n)
    (wellDiag r qn qd en ed (n + 2)) (wellBond r qd ed)
    (Pos.pow (margP (wellWalk r qn qd en ed (n + 1))) 2)
    (margP_sq _ h1) (wellWalk_rec r qn qd en ed n))

/-- The well head's tail recursion at every depth, the pivots and
witnesses the walk's own cleared data. -/
private theorem wellTail (r qn qd : Nat) (en ed : Pos) : ∀ n : Nat,
    (∀ k, k ≤ n →
      ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit) →
      greenprod.tailSteps (wDiagL r qn qd en ed (n + 1))
        (wOffL r qd ed (n + 1)) (wXL r qn qd en ed (n + 1))
        (wRL r qn qd en ed (n + 1))
  | 0, _ => by
    show greenprod.tailSteps [[[wellDiag r qn qd en ed 1]]] []
      [pivotQ r qn qd en ed 1] []
    exact pivotBase r qn qd en ed
  | n + 1, hoff => by
    have ih := wellTail r qn qd en ed n
      (fun k hk => hoff k (Nat.le_trans hk (Nat.le_succ n)))
    rw [wDiagL_cons r qn qd en ed n, wXL_cons r qn qd en ed n] at ih
    rw [wDiagL_cons r qn qd en ed (n + 1), wDiagL_cons r qn qd en ed n,
      wOffL_cons r qd ed n, wXL_cons r qn qd en ed (n + 1),
      wXL_cons r qn qd en ed n, wRL_cons r qn qd en ed n]
    have hn : ¬ (wellWalk r qn qd en ed n).oneValue BPair.unit :=
      hoff n (Nat.le_succ n)
    have hn1 : ¬ (wellWalk r qn qd en ed (n + 1)).oneValue BPair.unit :=
      hoff (n + 1) (Nat.le_refl (n + 1))
    refine ⟨⟨?_, pivotCross r qn qd en ed n hn hn1,
      pivotJoin r qn qd en ed n hn1⟩, ih⟩
    show ¬ (wellWalk r qn qd en ed (n + 1)
      * wellWalk r qn qd en ed n).oneValue BPair.unit
    exact ground.mulOffUnit hn1 hn

/-- The well head's slab shape at the unit orders. -/
private theorem wellSlab (r qn qd : Nat) (en ed : Pos) : ∀ n : Nat,
    greenprod.slabShape (wDiagL r qn qd en ed (n + 1)) (wOffL r qd ed (n + 1))
      (List.replicate (n + 1) 1)
  | 0 => by
    show greenprod.slabShape [[[wellDiag r qn qd en ed 1]]] [] [1]
    exact ⟨Nat.zero_lt_one, rfl⟩
  | n + 1 => by
    have ih := wellSlab r qn qd en ed n
    rw [wDiagL_cons r qn qd en ed n] at ih
    rw [wDiagL_cons r qn qd en ed (n + 1), wDiagL_cons r qn qd en ed n,
      wOffL_cons r qd ed n]
    exact ⟨Nat.zero_lt_one, rfl, rfl, ih⟩

/-- The pivots' shape at the unit orders. -/
private theorem wellQShape (r qn qd : Nat) (en ed : Pos) : ∀ n : Nat,
    greenprod.qShape (wXL r qn qd en ed (n + 1)) (List.replicate (n + 1) 1)
  | 0 => by
    show greenprod.qShape [pivotQ r qn qd en ed 1] [1]
    exact ⟨rfl, trivial⟩
  | n + 1 => by
    have ih := wellQShape r qn qd en ed n
    rw [wXL_cons r qn qd en ed (n + 1)]
    exact ⟨rfl, ih⟩

/-- The witnesses' shape at the unit orders. -/
private theorem wellWShape (r qn qd : Nat) (en ed : Pos) : ∀ n : Nat,
    greenprod.wShapeR (wRL r qn qd en ed (n + 1)) (List.replicate (n + 1) 1)
  | 0 => by
    show greenprod.wShapeR [] [1]
    trivial
  | n + 1 => by
    have ih := wellWShape r qn qd en ed n
    rw [wRL_cons r qn qd en ed n]
    exact ⟨rfl, ih⟩

/-- The well head's tail recursion read whole. -/
private theorem wellTailRead (r qn qd : Nat) (en ed : Pos) (n : Nat)
    (hoff : ∀ k, k ≤ n →
      ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit) :
    greenprod.tailRead (wDiagL r qn qd en ed (n + 1)) (wOffL r qd ed (n + 1))
      (wXL r qn qd en ed (n + 1)) (wRL r qn qd en ed (n + 1))
      (List.replicate (n + 1) 1) :=
  ⟨wellSlab r qn qd en ed n, wellQShape r qn qd en ed n,
    wellWShape r qn qd en ed n, wellTail r qn qd en ed n hoff⟩

/-- The pivots' splits, one order-one certificate per slab. -/
private def wSpL (r qn qd : Nat) (en ed : Pos) (n : Nat) :
    List ((k : Nat) × inertia.Split k) :=
  (List.range n).map (fun j =>
    ⟨1, split1 (wellWalk r qn qd en ed (n - j)
      * wellWalk r qn qd en ed (n - j - 1))⟩)

/-- The split list conses at the deepest pivot. -/
private theorem wSpL_cons (r qn qd : Nat) (en ed : Pos) (n : Nat) :
    wSpL r qn qd en ed (n + 1)
      = ⟨1, split1 (wellWalk r qn qd en ed (n + 1)
          * wellWalk r qn qd en ed n)⟩ :: wSpL r qn qd en ed n :=
  rangeMapCons _ _ n (fun j => by
    show (⟨1, split1 (wellWalk r qn qd en ed (n + 1 - (j + 1))
        * wellWalk r qn qd en ed (n + 1 - (j + 1) - 1))⟩ :
        (k : Nat) × inertia.Split k)
      = ⟨1, split1 (wellWalk r qn qd en ed (n - j)
        * wellWalk r qn qd en ed (n - j - 1))⟩
    rw [Nat.succ_sub_succ n j])

/-- Every pivot's split reads its own datum. -/
private theorem wellRevList (r qn qd : Nat) (en ed : Pos) : ∀ n : Nat,
    (∀ k, k ≤ n → ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit) →
    greenprod.revListRead (wXL r qn qd en ed n) (wSpL r qn qd en ed n)
  | 0, _ => trivial
  | n + 1, hoff => by
    have hx : ¬ (wellWalk r qn qd en ed (n + 1)
        * wellWalk r qn qd en ed n).oneValue BPair.unit :=
      ground.mulOffUnit (hoff (n + 1) (Nat.le_refl (n + 1)))
        (hoff n (Nat.le_of_succ_le (Nat.le_refl (n + 1))))
    rw [wXL_cons r qn qd en ed n, wSpL_cons r qn qd en ed n]
    exact ⟨splitRead_one _ _ hx (BPair.oneValue_refl _),
      wellRevList r qn qd en ed n
        (fun k hk => hoff k (Nat.le_of_succ_le (Nat.succ_le_succ hk)))⟩

/-- The reversal fold over a mapped family is the family fold of
the per-member counts. -/
private theorem revFoldMap (g : Nat → (k : Nat) × inertia.Split k) :
    ∀ (L : List Nat) (acc : Nat),
      (L.map g).foldl (fun m s => m + inertia.revAt s.2) acc
        = acc + ground.famFold Nat.add 0
            (fun j => inertia.revAt (g j).2) L
  | [], acc => (Nat.add_zero acc).symm
  | a :: t, acc => by
    show (t.map g).foldl (fun m s => m + inertia.revAt s.2)
        (acc + inertia.revAt (g a).2)
      = acc + (inertia.revAt (g a).2
        + ground.famFold Nat.add 0 (fun j => inertia.revAt (g j).2) t)
    rw [revFoldMap g t (acc + inertia.revAt (g a).2),
      Nat.add_assoc acc (inertia.revAt (g a).2) _]

/-- A family occupied at one key alone folds to that key's count. -/
private theorem sumOne : ∀ (j0 m : Nat) (F : Nat → Nat), j0 < m →
    (∀ j, j < j0 → F j = 0) → F j0 = 1 →
    (∀ j, j0 < j → j < m → F j = 0) →
    ground.famFold Nat.add 0 F (List.range m) = 1
  | 0, 0, _, hm, _, _, _ => absurd hm (Nat.not_lt_zero 0)
  | 0, m + 1, F, _, _, h1, hhi => by
    rw [ground.famFold_range_cons Nat.add 0 F m, h1,
      ground.famFold_rangeZero (fun j => F (j + 1)) m
        (fun j hj => hhi (j + 1) (Nat.succ_pos j) (Nat.succ_lt_succ hj))]
  | j0 + 1, 0, _, hm, _, _, _ => absurd hm (Nat.not_lt_zero (j0 + 1))
  | j0 + 1, m + 1, F, hm, hlo, h1, hhi => by
    rw [ground.famFold_range_cons Nat.add 0 F m, hlo 0 (Nat.succ_pos j0),
      sumOne j0 m (fun j => F (j + 1)) (Nat.lt_of_succ_lt_succ hm)
        (fun j hj => hlo (j + 1) (Nat.succ_lt_succ hj)) h1
        (fun j hj hjm => hhi (j + 1) (Nat.succ_lt_succ hj)
          (Nat.succ_lt_succ hjm))]


/-- Two lower-side factors' product sits on the upper side. -/
private theorem mulNegNeg {a b : BPair} (ha : a < BPair.unit)
    (hb : b < BPair.unit) : BPair.unit < a * b := by
  have has : BPair.unit < a.swap := ground.ltB_swap ha
  have h1 : b * a.swap < BPair.unit :=
    BPair.lt_congr (BPair.oneValue_refl _) (BPair.unit_mul a.swap)
      (ground.ltB_mulPos hb has)
  have h2 : BPair.unit < (b * a.swap).swap := ground.ltB_swap h1
  exact BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_of_eq (BPair.mul_comm b a)) h2

/-- The minors through the crossing depth sit on the upper side,
the seed among them. -/
private theorem walkPos (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hlo : ∀ k, k < c → BPair.unit < wellWalk r qn qd en ed (k + 1)) :
    ∀ m, m ≤ c → BPair.unit < wellWalk r qn qd en ed m
  | 0, _ => by
    rw [wellWalk_zero r qn qd en ed]
    exact ground.unitLtNat (Nat.succ_pos 0)
  | m + 1, h => hlo m (Nat.lt_of_succ_le h)

/-- The minors beyond the crossing depth sit on the lower side. -/
private theorem walkNeg (r qn qd : Nat) (en ed : Pos) (n c : Nat)
    (hhi : ∀ k, c ≤ k → k < n →
      wellWalk r qn qd en ed (k + 1) < BPair.unit) :
    ∀ m, c < m → m ≤ n → wellWalk r qn qd en ed m < BPair.unit
  | 0, h, _ => absurd h (Nat.not_lt_zero c)
  | m + 1, h, h2 => hhi m (Nat.le_of_lt_succ h) (Nat.lt_of_succ_le h2)

/-- A one-block split's count is its block's own reversal read. -/
private theorem revAt_single {n : Nat} (T Tw : elim.SqMat n)
    (b : inertia.SBlock)
    (h : Nat.beq (inertia.widthOf [b] 0) n = true) :
    inertia.revAt (⟨T, Tw, [b], 0, h⟩ : inertia.Split n) = b.rev :=
  Nat.zero_add b.rev

/-- An order-one split at a lower-side entry counts one. -/
private theorem revSplit1_lt {x : BPair} (h : x < BPair.unit) :
    inertia.revAt (split1 x) = 1 := by
  rw [show inertia.revAt (split1 x) = (inertia.SBlock.one x).rev from
    revAt_single id1 id1 _ rfl, inertia.rev_one_lt h]

/-- An order-one split at an entry at or above the unit counts
nought. -/
private theorem revSplit1_le {x : BPair} (h : BPair.unit ≤ x) :
    inertia.revAt (split1 x) = 0 := by
  rw [show inertia.revAt (split1 x) = (inertia.SBlock.one x).rev from
    revAt_single id1 id1 _ rfl, inertia.rev_one_le h]

/-- A key below the complement's own reads the complement below the
key's. -/
private theorem subFlip {j c n : Nat} (hm : c + 1 ≤ n)
    (h : j < n - (c + 1)) : c + 1 < n - j := by
  have he : (c + 1) + (n - (c + 1)) = n := ground.natAddSubCancel hm
  have h1 : (c + 1) + j < n := by
    rw [← he]
    exact Nat.add_lt_add_left h (c + 1)
  have hj : j ≤ n :=
    Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_left j (c + 1)) h1)
  refine Nat.lt_of_add_lt_add_left (n := j) ?_
  rw [ground.natAddSubCancel hj, Nat.add_comm j (c + 1)]
  exact h1

/-- A key beyond the complement's own caps the complement at the
crossing depth. -/
private theorem subDrop {j c n : Nat} (hm : c + 1 ≤ n)
    (h : n - (c + 1) < j) : n - j ≤ c := by
  have he : (c + 1) + (n - (c + 1)) = n := ground.natAddSubCancel hm
  have h1 : n < (c + 1) + j := by
    rw [← he]
    exact Nat.add_lt_add_left h (c + 1)
  rw [show (c + 1) + j = (c + j) + 1 from Nat.add_right_comm c 1 j] at h1
  exact Nat.le_trans (Nat.sub_le_sub_right (Nat.le_of_lt_succ h1) j)
    (Nat.le_of_eq (ground.addSubSelfR c j))

/-- The pivots' reversal fold at a stated crossing is one: the
signs agree at every slab but the crossing's own. -/
private theorem wellRevFold (r qn qd : Nat) (en ed : Pos) (n c : Nat)
    (hc : c < n)
    (hlo : ∀ k, k < c → BPair.unit < wellWalk r qn qd en ed (k + 1))
    (hhi : ∀ k, c ≤ k → k < n →
      wellWalk r qn qd en ed (k + 1) < BPair.unit) :
    greenprod.revFold (wSpL r qn qd en ed n) = 1 := by
  have hpos := walkPos r qn qd en ed c hlo
  have hneg := walkNeg r qn qd en ed n c hhi
  show ((List.range n).map (fun j =>
      (⟨1, split1 (wellWalk r qn qd en ed (n - j)
        * wellWalk r qn qd en ed (n - j - 1))⟩ :
        (k : Nat) × inertia.Split k))).foldl
      (fun m s => m + inertia.revAt s.2) 0 = 1
  rw [revFoldMap _ (List.range n) 0, Nat.zero_add]
  refine sumOne (n - (c + 1)) n _
    (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le c) hc) (Nat.succ_pos c))
    ?_ ?_ ?_
  · intro j hj
    have hk : c + 1 < n - j := subFlip hc hj
    have h1 : wellWalk r qn qd en ed (n - j) < BPair.unit :=
      hneg (n - j) (Nat.lt_of_succ_lt hk) (Nat.sub_le n j)
    have hk2 : c < n - j - 1 := Nat.sub_le_sub_right (Nat.succ_le_of_lt hk) 1
    have h2 : wellWalk r qn qd en ed (n - j - 1) < BPair.unit :=
      hneg (n - j - 1) hk2
        (Nat.le_trans (Nat.sub_le (n - j) 1) (Nat.sub_le n j))
    exact revSplit1_le (ground.leB_of_lt (mulNegNeg h1 h2))
  · show inertia.revAt (split1 (wellWalk r qn qd en ed (n - (n - (c + 1)))
      * wellWalk r qn qd en ed (n - (n - (c + 1)) - 1))) = 1
    rw [ground.natSubSubCancel n (c + 1) hc]
    exact revSplit1_lt
      (mulNegPos (hneg (c + 1) (Nat.lt_succ_self c) hc) (hpos c (Nat.le_refl c)))
  · intro j hj _
    have hk : n - j ≤ c := subDrop hc hj
    exact revSplit1_le (ground.leB_of_lt
      (ground.unitLtMul (hpos (n - j) hk)
        (hpos (n - j - 1) (Nat.le_trans (Nat.sub_le (n - j) 1) hk))))

/-- The pivots' reversal fold at minors positive throughout is
the sum's unit. -/
private theorem wellRevFoldZero (r qn qd : Nat) (en ed : Pos) (n : Nat)
    (hlo : ∀ k, k < n → BPair.unit < wellWalk r qn qd en ed (k + 1)) :
    ∀ acc : Nat, (wSpL r qn qd en ed n).foldl
      (fun m s => m + inertia.revAt s.2) acc = acc := by
  intro acc
  have hpos := walkPos r qn qd en ed n hlo
  show ((List.range n).map (fun j =>
      (⟨1, split1 (wellWalk r qn qd en ed (n - j)
        * wellWalk r qn qd en ed (n - j - 1))⟩ :
        (k : Nat) × inertia.Split k))).foldl
      (fun m s => m + inertia.revAt s.2) acc = acc
  have hz : ground.famFold Nat.add 0
      (fun j => inertia.revAt (⟨1, split1 (wellWalk r qn qd en ed (n - j)
        * wellWalk r qn qd en ed (n - j - 1))⟩ :
        (k : Nat) × inertia.Split k).2) (List.range n) = 0 := by
    refine ground.famFold_rangeZero _ n ?_
    intro j _
    exact revSplit1_le (ground.leB_of_lt
      (ground.unitLtMul (hpos (n - j) (Nat.sub_le n j))
        (hpos (n - j - 1)
          (Nat.le_trans (Nat.sub_le (n - j) 1) (Nat.sub_le n j)))))
  rw [revFoldMap _ (List.range n) acc, hz, Nat.add_zero]

/-- The tail recursion read at an occupied order. -/
private theorem wellTailReadOf (r qn qd : Nat) (en ed : Pos) :
    ∀ (n : Nat), 1 ≤ n →
      (∀ k, k ≤ n → ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit) →
      greenprod.tailRead (wDiagL r qn qd en ed n) (wOffL r qd ed n)
        (wXL r qn qd en ed n) (wRL r qn qd en ed n) (List.replicate n 1)
  | 0, h, _ => absurd h (Nat.not_succ_le_zero 0)
  | m + 1, _, hoff =>
    wellTailRead r qn qd en ed m
      (fun k hk => hoff k (Nat.le_trans hk (Nat.le_succ m)))

/-- A block list's width conses at the leading block's order. -/
private theorem widthCons (b : inertia.SBlock) (t : List inertia.SBlock)
    (k : Nat) : inertia.widthOf (b :: t) k
      = inertia.widthOf t k + b.order :=
  inertia.widthOf_shift t k b.order

/-- A block list of vacant width is vacant, its reversal fold the
sum's unit. -/
private theorem revNilOfWidth : ∀ (bs : List inertia.SBlock) (k : Nat),
    Nat.beq (inertia.widthOf bs k) 0 = true →
      bs.foldl (fun m b => m + b.rev) 0 = 0
  | [], _, _ => rfl
  | b :: t, k, h => by
    rw [widthCons b t k] at h
    match b, h with
    | .one _, h => exact Bool.noConfusion h
    | .two _ _ _, h => exact Bool.noConfusion h

/-- Every minor at or below the head's order sits off equal
members. -/
private theorem wellOffWalk (r qn qd : Nat) (en ed : Pos) (n c : Nat)
    (hpos : ∀ m, m ≤ c → BPair.unit < wellWalk r qn qd en ed m)
    (hneg : ∀ m, c < m → m ≤ n → wellWalk r qn qd en ed m < BPair.unit) :
    ∀ k, k ≤ n → ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit := by
  intro k hk
  match Nat.decLt c k with
  | isTrue h => exact ground.offOfLtUnit (hneg k h hk)
  | isFalse h => exact ground.offOfUnitLt (hpos k (Nat.le_of_not_lt h))

/-- The crossing-free arm at an occupied order. -/
private theorem certZeroPos (r qn qd : Nat) (en ed : Pos) (m : Nat)
    (hlo : ∀ k, k < m + 1 → BPair.unit < wellWalk r qn qd en ed (k + 1))
    (sp : inertia.Split (m + 1))
    (hsp : inertia.splitRead (wellMat r qn qd en ed (m + 1)) sp) :
    inertia.revAt sp = 0 := by
  have hoff := wellOffWalk r qn qd en ed (m + 1) (m + 1)
    (walkPos r qn qd en ed (m + 1) hlo)
    (fun _ h h2 => absurd (Nat.lt_of_lt_of_le h h2) (Nat.lt_irrefl (m + 1)))
  rw [greenprod.countSplit (wDiagL r qn qd en ed (m + 1))
    (wOffL r qd ed (m + 1)) (wXL r qn qd en ed (m + 1))
    (wRL r qn qd en ed (m + 1)) (List.replicate (m + 1) 1)
    (wSpL r qn qd en ed (m + 1)) sp
    (wellTailReadOf r qn qd en ed (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
      hoff)
    (wellRevList r qn qd en ed (m + 1) hoff) hsp]
  exact wellRevFoldZero r qn qd en ed (m + 1) hlo 0

/-- The crossing-free arm: minors positive to the head's end read
the count vacant. -/
theorem certRevZero : ∀ (r qn qd : Nat) (en ed : Pos) (n : Nat),
    (∀ k, k < n → BPair.unit < wellWalk r qn qd en ed (k + 1)) →
    ∀ sp : inertia.Split n,
      inertia.splitRead (wellMat r qn qd en ed n) sp →
      inertia.revAt sp = 0 := by
  intro r qn qd en ed n
  cases n with
  | zero => exact fun _ sp _ => revNilOfWidth sp.blocks sp.kern sp.width
  | succ m => exact certZeroPos r qn qd en ed m


/-- The order-one kernel split: the identity congruence with no
nonsingular block, the single place the kernel's own. -/
private def split1K : inertia.Split 1 :=
  ⟨id1, id1, [], 1, rfl⟩

/-- A one-by-one datum at equal members splits at the order-one
kernel certificate. -/
private theorem splitRead_oneK (y : BPair) (hy : y.oneValue BPair.unit) :
    inertia.splitRead [[y]] split1K := by
  have hSr : elim.rowsLen 1 [[y]] := ⟨rfl, trivial⟩
  have hy1 : elim.matOneValue [[y]] (inertia.blockMat [] 1) :=
    ⟨⟨hy, trivial⟩, trivial⟩
  refine ⟨rfl, cc1, ?_, rfl⟩
  show elim.matOneValue
    (elim.matMul (elim.transposeM (inertia.idMat 1))
      (elim.matMul [[y]] (inertia.idMat 1)))
    (inertia.blockMat [] 1)
  rw [inertia.transposeM_idMat 1]
  refine elim.matOne_trans ?_ hy1
  refine elim.matOne_trans ?_
    (inertia.idMat_matMul (k := 1) 1 [[y]] hSr rfl (by decide +kernel))
  exact elim.matMul_congrR (n := 1) (k := 1) (inertia.idMat 1)
    (elim.matMul [[y]] (inertia.idMat 1)) [[y]]
    (elim.rowsLen_cast
      (by rw [inertia.transposeM_idMat 1, inertia.idMat_len 1])
      (elim.rowsLen_matMul [[y]] (inertia.idMat 1)))
    hSr ((elim.length_matMul [[y]] (inertia.idMat 1)).trans rfl) rfl
    (by decide +kernel)
    (inertia.matMul_idR (k := 1) 1 [[y]] hSr rfl (by decide +kernel) (by decide +kernel))

/-- The pivots' splits at a boundary-degenerate head: the deep end's
pivot reads equal members and takes the kernel certificate, every
shallower pivot its own occupied entry. -/
private theorem wellRevListKern (r qn qd : Nat) (en ed : Pos) (m : Nat)
    (hoff : ∀ k, k ≤ m → ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit)
    (hy : (wellWalk r qn qd en ed (m + 1)).oneValue BPair.unit) :
    greenprod.revListRead (wXL r qn qd en ed (m + 1))
      (⟨1, split1K⟩ :: wSpL r qn qd en ed m) := by
  rw [wXL_cons r qn qd en ed m]
  exact ⟨splitRead_oneK _
      (BPair.oneValue_trans
        (BPair.mul_congr hy (BPair.oneValue_refl (wellWalk r qn qd en ed m)))
        (BPair.unit_mul (wellWalk r qn qd en ed m))),
    wellRevList r qn qd en ed m hoff⟩

/-- The boundary-degenerate arm's fold: the kernel block counts
nought and every shallower pivot's signs agree. -/
private theorem revFoldKern (r qn qd : Nat) (en ed : Pos) (m : Nat)
    (hlo : ∀ k, k < m → BPair.unit < wellWalk r qn qd en ed (k + 1)) :
    greenprod.revFold (⟨1, split1K⟩ :: wSpL r qn qd en ed m) = 0 := by
  show (wSpL r qn qd en ed m).foldl
    (fun a s => a + inertia.revAt s.2) 0 = 0
  exact wellRevFoldZero r qn qd en ed m hlo 0

/-- The boundary-degenerate arm: minors positive below the head's
last, whose read is equal members — the count vacant, the last spot
the kernel block. -/
theorem certRevZeroKern : ∀ (r qn qd : Nat) (en ed : Pos) (n : Nat),
    (∀ k, k + 1 < n → BPair.unit < wellWalk r qn qd en ed (k + 1)) →
    (wellWalk r qn qd en ed n).oneValue BPair.unit →
    ∀ sp : inertia.Split n,
      inertia.splitRead (wellMat r qn qd en ed n) sp →
      inertia.revAt sp = 0 := by
  intro r qn qd en ed n hlo hy sp hsp
  cases n with
  | zero =>
    rw [wellWalk_zero r qn qd en ed] at hy
    exact absurd hy (by decide +kernel)
  | succ m =>
    have hlo' : ∀ k, k < m → BPair.unit < wellWalk r qn qd en ed (k + 1) :=
      fun k hk => hlo k (Nat.succ_lt_succ hk)
    have hoff : ∀ k, k ≤ m →
        ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit :=
      fun k hk => ground.offOfUnitLt (walkPos r qn qd en ed m hlo' k hk)
    rw [greenprod.countSplit (wDiagL r qn qd en ed (m + 1))
      (wOffL r qd ed (m + 1)) (wXL r qn qd en ed (m + 1))
      (wRL r qn qd en ed (m + 1)) (List.replicate (m + 1) 1)
      (⟨1, split1K⟩ :: wSpL r qn qd en ed m) sp
      (wellTailRead r qn qd en ed m hoff)
      (wellRevListKern r qn qd en ed m hoff hy) hsp]
    exact revFoldKern r qn qd en ed m hlo'

/-- The scalar chain's entry chart: the diagonal at the key pair's
agreement, the bond at the consecutive pairs, the sum's unit beyond. -/
private def chainAt (d o : List BPair) (i j : Nat) : BPair :=
  if j = i then ground.getAt BPair.unit d i
  else if j + 1 = i then ground.getAt BPair.unit o j
  else if i + 1 = j then ground.getAt BPair.unit o i
  else BPair.unit

/-- The entry chart drops its leading slab at a shifted key pair. -/
private theorem chainAt_step (a b : BPair) (dl ot : List BPair) (r j : Nat) :
    chainAt (a :: dl) (b :: ot) (r + 1) (j + 1) = chainAt dl ot r j := by
  show (if j + 1 = r + 1 then ground.getAt BPair.unit (a :: dl) (r + 1)
      else if j + 1 + 1 = r + 1 then ground.getAt BPair.unit (b :: ot) (j + 1)
      else if r + 1 + 1 = j + 1 then ground.getAt BPair.unit (b :: ot) (r + 1)
      else BPair.unit)
    = if j = r then ground.getAt BPair.unit dl r
      else if j + 1 = r then ground.getAt BPair.unit ot j
      else if r + 1 = j then ground.getAt BPair.unit ot r
      else BPair.unit
  match Nat.decEq j r with
  | isTrue hh =>
    rw [if_pos (congrArg (fun z => z + 1) hh), if_pos hh]
    rfl
  | isFalse hh =>
    rw [if_neg (fun hz => hh (Nat.succ.inj hz)), if_neg hh]
    match Nat.decEq (j + 1) r with
    | isTrue h2 =>
      rw [if_pos (congrArg (fun z => z + 1) h2), if_pos h2]
      rfl
    | isFalse h2 =>
      rw [if_neg (fun hz => h2 (Nat.succ.inj hz)), if_neg h2]
      match Nat.decEq (r + 1) j with
      | isTrue h3 =>
        rw [if_pos (congrArg (fun z => z + 1) h3), if_pos h3]
        rfl
      | isFalse h3 =>
        rw [if_neg (fun hz => h3 (Nat.succ.inj hz)), if_neg h3]

/-- The assembled chain's block row: the leading column's entry
against the tail chain's own row. -/
private theorem chainRow (b : BPair) (L : Nat) (rest : elim.Mat) (r : Nat)
    (hr : r < rest.length) :
    ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun s =>
          (if s < 1 then ground.getAt [] [[b]] s
           else List.replicate 1 BPair.unit) ++ ground.getAt [] rest s)) r
      = ground.getAt BPair.unit (b :: List.replicate L BPair.unit) r
        :: ground.getAt [] rest r := by
  rw [ground.getAt_map 0 ([] : List BPair) _ (List.range rest.length) r
      (by rw [ground.length_range]; exact hr),
    ground.getAt_range rest.length r hr]
  match r with
  | 0 => rfl
  | m + 1 =>
    show List.replicate 1 BPair.unit ++ ground.getAt [] rest (m + 1)
      = ground.getAt BPair.unit (List.replicate L BPair.unit) m
        :: ground.getAt [] rest (m + 1)
    rw [ground.getAt_replicate_self BPair.unit L m]
    rfl

/-- The assembled chain's entry at the leading slab: the diagonal
and bond at the leading keys, the tail chain's own beyond. -/
private theorem consEntry (a b : BPair) (dl ot : List BPair) (rest : elim.Mat)
    (hlen : rest.length = dl.length)
    (hrest : ∀ r j : Nat, r < dl.length → j < dl.length →
      ground.getAt BPair.unit (ground.getAt ([] : List BPair) rest r) j
        = chainAt dl ot r j) :
    ∀ i j : Nat, i < dl.length + 1 → j < dl.length + 1 →
      ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        ((a :: b :: List.replicate ((rest.headD []).length - 1) BPair.unit)
          :: (List.range rest.length).map (fun s =>
            (if s < 1 then ground.getAt [] [[b]] s
             else List.replicate 1 BPair.unit) ++ ground.getAt [] rest s)) i) j
      = chainAt (a :: dl) (b :: ot) i j := by
  intro i j hi hj
  match i, j, hi, hj with
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, k + 2, _, _ =>
    show ground.getAt BPair.unit
      (List.replicate ((rest.headD []).length - 1) BPair.unit) k
      = chainAt (a :: dl) (b :: ot) 0 (k + 2)
    rw [ground.getAt_replicate_self BPair.unit
      ((rest.headD []).length - 1) k]
    rfl
  | r + 1, 0, hi, _ =>
    have hr : r < rest.length := by
      rw [hlen]
      exact Nat.lt_of_succ_lt_succ hi
    show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun s =>
          (if s < 1 then ground.getAt [] [[b]] s
           else List.replicate 1 BPair.unit) ++ ground.getAt [] rest s)) r) 0
      = chainAt (a :: dl) (b :: ot) (r + 1) 0
    rw [chainRow b dl.length rest r hr]
    match r with
    | 0 => rfl
    | m + 1 =>
      show ground.getAt BPair.unit (List.replicate dl.length BPair.unit) m
        = chainAt (a :: dl) (b :: ot) (m + 2) 0
      rw [ground.getAt_replicate_self BPair.unit dl.length m]
      rfl
  | r + 1, j' + 1, hi, hj =>
    have hr : r < rest.length := by
      rw [hlen]
      exact Nat.lt_of_succ_lt_succ hi
    show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun s =>
          (if s < 1 then ground.getAt [] [[b]] s
           else List.replicate 1 BPair.unit) ++ ground.getAt [] rest s)) r)
        (j' + 1)
      = chainAt (a :: dl) (b :: ot) (r + 1) (j' + 1)
    rw [chainRow b dl.length rest r hr, chainAt_step a b dl ot r j']
    exact hrest r j' (by rw [← hlen]; exact hr) (Nat.lt_of_succ_lt_succ hj)

/-- The scalar chain's entry read: the assembled matrix is the
entry chart at every key pair inside the order. -/
private theorem chainEntry : ∀ (d o : List BPair), o.length + 1 = d.length →
    ∀ i j : Nat, i < d.length → j < d.length →
      ground.getAt BPair.unit (ground.getAt ([] : List BPair)
          (greenprod.assemble (d.map (fun x => [[x]]))
            (o.map (fun x => [[x]]))) i) j
        = chainAt d o i j
  | [], _, h, _, _, _, _ => Nat.noConfusion h
  | [_], _ :: _, h, _, _, _, _ => Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _, [], h, _, _, _, _ => Nat.noConfusion (Nat.succ.inj h)
  | [_], [], _, 0, 0, _, _ => rfl
  | [_], [], _, 0, _ + 1, _, hj =>
    absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero _)
  | [_], [], _, _ + 1, _, hi, _ =>
    absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero _)
  | a :: a' :: dt, b :: ot, h, i, j, hi, hj =>
    consEntry a b (a' :: dt) ot
      (greenprod.assemble ((a' :: dt).map (fun x => [[x]]))
        (ot.map (fun x => [[x]])))
      (chainLen (a' :: dt) ot (Nat.succ.inj h)).1
      (fun r s hr hs => chainEntry (a' :: dt) ot (Nat.succ.inj h) r s hr hs)
      i j hi hj

/-- The scalar chain's rows read the diagonal's count. -/
private theorem chainRows : ∀ (d o : List BPair), o.length + 1 = d.length →
    elim.rowsLen d.length (greenprod.assemble (d.map (fun x => [[x]]))
      (o.map (fun x => [[x]])))
  | [], _, h => Nat.noConfusion h
  | [_], _ :: _, h => Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _, [], h => Nat.noConfusion (Nat.succ.inj h)
  | [_], [], _ => ⟨rfl, trivial⟩
  | _ :: a' :: dt, b :: ot, h => by
    have hIH := chainLen (a' :: dt) ot (Nat.succ.inj h)
    have hrows := chainRows (a' :: dt) ot (Nat.succ.inj h)
    have key : ∀ u v : List BPair, u.length = 1 → v.length = dt.length + 1 →
        (u ++ v).length = dt.length + 1 + 1 := by
      intro u v hu hv
      rw [ground.length_append, hu, hv]
      exact Nat.add_comm 1 (dt.length + 1)
    refine ⟨?_, ?_⟩
    · show (List.replicate
        (((greenprod.assemble ((a' :: dt).map (fun x => [[x]]))
          (ot.map (fun x => [[x]]))).headD []).length - 1)
          BPair.unit).length + 1 + 1 = dt.length + 1 + 1
      rw [ground.length_replicate, hIH.2]
      rfl
    · refine elim.rowsLen_map _ (dt.length + 1 + 1) _ (fun s hs => ?_)
      have hs' : s < (greenprod.assemble ((a' :: dt).map (fun x => [[x]]))
          (ot.map (fun x => [[x]]))).length := ground.ltOfMemRange hs
      have h1 : ((if s < 1 then ground.getAt [] [[b]] s
          else List.replicate 1 BPair.unit) : List BPair).length = 1 := by
        match s with
        | 0 => rfl
        | _ + 1 => rfl
      exact key _ _ h1 (elim.rowsLen_getAt _ s hrows hs')

/-- The well head's diagonal entries, deep end first. -/
private def wDiagE (r qn qd : Nat) (en ed : Pos) (n : Nat) : List BPair :=
  (List.range n).map (fun k => wellDiag r qn qd en ed (n - k))

/-- The well head's off-diagonal entries, the bond weight
throughout. -/
private def wOffE (r qd : Nat) (ed : Pos) (n : Nat) : List BPair :=
  (List.range (n - 1)).map (fun _ => (wellBond r qd ed).swap)

/-- The diagonal entry list's count is the head's order. -/
private theorem wDiagE_len (r qn qd : Nat) (en ed : Pos) (n : Nat) :
    (wDiagE r qn qd en ed n).length = n :=
  ground.length_mapRange _ n

/-- The off-diagonal entry list's count is the head's order less
one. -/
private theorem wOffE_len (r qd : Nat) (ed : Pos) (n : Nat) :
    (wOffE r qd ed n).length = n - 1 :=
  ground.length_mapRange _ (n - 1)

/-- The diagonal entry at a key is that key's own depth. -/
private theorem wDiagE_at (r qn qd : Nat) (en ed : Pos) (n i : Nat)
    (hi : i < n) :
    ground.getAt BPair.unit (wDiagE r qn qd en ed n) i
      = wellDiag r qn qd en ed (n - i) := by
  show ground.getAt BPair.unit
    ((List.range n).map (fun k => wellDiag r qn qd en ed (n - k))) i = _
  rw [ground.getAt_map 0 BPair.unit _ (List.range n) i
      (by rw [ground.length_range]; exact hi),
    ground.getAt_range n i hi]

/-- Every off-diagonal entry is the bond weight's swap. -/
private theorem wOffE_at (r qd : Nat) (ed : Pos) (n j : Nat)
    (hj : j < n - 1) :
    ground.getAt BPair.unit (wOffE r qd ed n) j = (wellBond r qd ed).swap := by
  show ground.getAt BPair.unit
    ((List.range (n - 1)).map (fun _ => (wellBond r qd ed).swap)) j = _
  rw [ground.getAt_map 0 BPair.unit _ (List.range (n - 1)) j
      (by rw [ground.length_range]; exact hj)]

/-- The well head is the scalar chain at its two entry lists. -/
private theorem wellMat_chain (r qn qd : Nat) (en ed : Pos) (n : Nat) :
    wellMat r qn qd en ed n
      = greenprod.assemble ((wDiagE r qn qd en ed n).map (fun x => [[x]]))
          ((wOffE r qd ed n).map (fun x => [[x]])) := by
  show greenprod.assemble
      ((List.range n).map (fun k => [[wellDiag r qn qd en ed (n - k)]]))
      ((List.range (n - 1)).map (fun _ => [[(wellBond r qd ed).swap]]))
    = greenprod.assemble
      (((List.range n).map (fun k => wellDiag r qn qd en ed (n - k))).map
        (fun x => [[x]]))
      (((List.range (n - 1)).map (fun _ => (wellBond r qd ed).swap)).map
        (fun x => [[x]]))
  rw [ground.map_map (fun k => wellDiag r qn qd en ed (n - k))
      (fun x => [[x]]) (List.range n),
    ground.map_map (fun _ : Nat => (wellBond r qd ed).swap)
      (fun x => [[x]]) (List.range (n - 1))]

/-- The two entry lists' counts meet the chain's own tie. -/
private theorem wellChainLen (r qn qd : Nat) (en ed : Pos) (m : Nat) :
    (wOffE r qd ed (m + 1)).length + 1
      = (wDiagE r qn qd en ed (m + 1)).length := by
  rw [wOffE_len r qd ed (m + 1), wDiagE_len r qn qd en ed (m + 1)]
  rfl

/-- The well head's row count is its order. -/
private theorem wellLen (r qn qd : Nat) (en ed : Pos) (m : Nat) :
    (wellMat r qn qd en ed (m + 1)).length = m + 1 := by
  rw [wellMat_chain r qn qd en ed (m + 1),
    (chainLen (wDiagE r qn qd en ed (m + 1)) (wOffE r qd ed (m + 1))
      (wellChainLen r qn qd en ed m)).1,
    wDiagE_len r qn qd en ed (m + 1)]

/-- The well head's rows read its order. -/
private theorem wellRows (r qn qd : Nat) (en ed : Pos) (m : Nat) :
    elim.rowsLen (m + 1) (wellMat r qn qd en ed (m + 1)) := by
  rw [wellMat_chain r qn qd en ed (m + 1)]
  have h := chainRows (wDiagE r qn qd en ed (m + 1)) (wOffE r qd ed (m + 1))
    (wellChainLen r qn qd en ed m)
  rw [wDiagE_len r qn qd en ed (m + 1)] at h
  exact h

/-- The well head's entry is the entry chart at its two entry
lists. -/
private theorem wellEntry (r qn qd : Nat) (en ed : Pos) (m i j : Nat)
    (hi : i < m + 1) (hj : j < m + 1) :
    ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (wellMat r qn qd en ed (m + 1)) i) j
      = chainAt (wDiagE r qn qd en ed (m + 1)) (wOffE r qd ed (m + 1)) i j := by
  rw [wellMat_chain r qn qd en ed (m + 1)]
  exact chainEntry _ _ (wellChainLen r qn qd en ed m) i j
    (by rw [wDiagE_len r qn qd en ed (m + 1)]; exact hi)
    (by rw [wDiagE_len r qn qd en ed (m + 1)]; exact hj)


/-! `lem:greenprod`'s singular-slab clause at the well head: the
degenerate spot re-orders inside one order-two slab, the slab list
mixed — order-one blocks off the spot and the spot's own
two-by-two — and the assembled matrix the same head. -/

/-- The degenerate spot's order-two slab: the two consecutive
depths' diagonal entries with the bond weight off the diagonal. -/
private def spotMat (r qn qd : Nat) (en ed : Pos) (c : Nat) : elim.Mat :=
  [[wellDiag r qn qd en ed (c + 2), (wellBond r qd ed).swap],
   [(wellBond r qd ed).swap, wellDiag r qn qd en ed (c + 1)]]

/-- The mixed slab list's diagonal blocks, deep end first: the
order-one blocks above the spot, the spot's order-two block, and the
order-one blocks below it. -/
private def mDiag (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    Nat → List elim.Mat
  | 0 => spotMat r qn qd en ed c :: wDiagL r qn qd en ed c
  | t + 1 =>
    [[wellDiag r qn qd en ed (c + 2 + t + 1)]] :: mDiag r qn qd en ed c t

/-- The mixed off-diagonal blocks at and below the spot: the spot's
own order-two-against-order-one block with the shallower chain's. -/
private def mOffBase (r qd : Nat) (ed : Pos) : Nat → List elim.Mat
  | 0 => []
  | c + 1 => [[BPair.unit], [(wellBond r qd ed).swap]] :: wOffL r qd ed (c + 1)

/-- The mixed off-diagonal blocks: the order-one chain above the
spot, the order-one-against-order-two block at the spot's upper
side, and the spot's own below it. -/
private def mOff (r qd : Nat) (ed : Pos) (c : Nat) : Nat → List elim.Mat
  | 0 => mOffBase r qd ed c
  | 1 => [[(wellBond r qd ed).swap, BPair.unit]] :: mOffBase r qd ed c
  | t + 2 => [[(wellBond r qd ed).swap]] :: mOff r qd ed c (t + 1)

/-- The mixed slab orders: the spot's two among the order-one
slabs. -/
private def mNs (c : Nat) : Nat → List Nat
  | 0 => 2 :: List.replicate c 1
  | t + 1 => 1 :: mNs c t

/-- The diagonal entry list conses at the deepest depth. -/
private theorem wDiagE_cons (r qn qd : Nat) (en ed : Pos) (n : Nat) :
    wDiagE r qn qd en ed (n + 1)
      = wellDiag r qn qd en ed (n + 1) :: wDiagE r qn qd en ed n :=
  rangeMapCons _ _ n (fun j => by rw [Nat.succ_sub_succ n j])

/-- The off-diagonal entry list conses at the leading bond. -/
private theorem wOffE_cons (r qd : Nat) (ed : Pos) (n : Nat) :
    wOffE r qd ed (n + 2) = (wellBond r qd ed).swap :: wOffE r qd ed (n + 1) :=
  rangeMapCons _ _ n (fun _ => rfl)

/-- The diagonal slab list is the entry list's one-by-one blocks. -/
private theorem wDiagL_map (r qn qd : Nat) (en ed : Pos) (n : Nat) :
    wDiagL r qn qd en ed n
      = (wDiagE r qn qd en ed n).map (fun x => [[x]]) := by
  show (List.range n).map (fun k => [[wellDiag r qn qd en ed (n - k)]])
    = ((List.range n).map (fun k => wellDiag r qn qd en ed (n - k))).map
        (fun x => [[x]])
  rw [ground.map_map (fun k => wellDiag r qn qd en ed (n - k))
    (fun x => [[x]]) (List.range n)]

/-- The off-diagonal slab list is the entry list's one-by-one
blocks. -/
private theorem wOffL_map (r qd : Nat) (ed : Pos) (n : Nat) :
    wOffL r qd ed n = (wOffE r qd ed n).map (fun x => [[x]]) := by
  show (List.range (n - 1)).map (fun _ => [[(wellBond r qd ed).swap]])
    = ((List.range (n - 1)).map (fun _ => (wellBond r qd ed).swap)).map
        (fun x => [[x]])
  rw [ground.map_map (fun _ : Nat => (wellBond r qd ed).swap)
    (fun x => [[x]]) (List.range (n - 1))]

/-- The assembled block row beneath an order-two leading slab: the
two leading columns' entries against the trailing assembly's own
row. -/
private theorem twoRow (bb : BPair) (L : Nat) (rest : elim.Mat) (s : Nat)
    (hs : s < rest.length) :
    ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun z =>
          (if z < 1 then ground.getAt [] [[BPair.unit, bb]] z
           else List.replicate 2 BPair.unit) ++ ground.getAt [] rest z)) s
      = BPair.unit
        :: ground.getAt BPair.unit (bb :: List.replicate L BPair.unit) s
        :: ground.getAt [] rest s := by
  rw [ground.getAt_map 0 ([] : List BPair) _ (List.range rest.length) s
      (by rw [ground.length_range]; exact hs),
    ground.getAt_range rest.length s hs]
  match s with
  | 0 => rfl
  | m + 1 =>
    show (List.replicate 2 BPair.unit) ++ ground.getAt [] rest (m + 1)
      = BPair.unit
        :: ground.getAt BPair.unit (List.replicate L BPair.unit) m
        :: ground.getAt [] rest (m + 1)
    rw [ground.getAt_replicate_self BPair.unit L m]
    rfl

/-- The assembled matrix at an order-two leading slab reads the
entry chart at the two depths spliced into the entry lists. -/
private theorem twoEntry (a b c bb : BPair) (dl ot : List BPair)
    (rest : elim.Mat)
    (hlen : rest.length = dl.length)
    (hrest : ∀ i j : Nat, i < dl.length → j < dl.length →
      ground.getAt BPair.unit (ground.getAt ([] : List BPair) rest i) j
        = chainAt dl ot i j) :
    ∀ i j : Nat, i < dl.length + 2 → j < dl.length + 2 →
      ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        ((a :: b :: BPair.unit
            :: List.replicate ((rest.headD ([] : List BPair)).length - 1)
                BPair.unit)
         :: (b :: c :: bb
            :: List.replicate ((rest.headD ([] : List BPair)).length - 1)
                BPair.unit)
         :: (List.range rest.length).map (fun z =>
              (if z < 1 then ground.getAt [] [[BPair.unit, bb]] z
               else List.replicate 2 BPair.unit)
                ++ ground.getAt [] rest z)) i) j
      = chainAt (a :: c :: dl) (b :: bb :: ot) i j := by
  intro i j hi hj
  match i, j, hi, hj with
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, k + 2, _, _ =>
    show ground.getAt BPair.unit
      (BPair.unit :: List.replicate
        ((rest.headD ([] : List BPair)).length - 1) BPair.unit) k
      = chainAt (a :: c :: dl) (b :: bb :: ot) 0 (k + 2)
    rw [show ground.getAt BPair.unit (BPair.unit :: List.replicate
        ((rest.headD ([] : List BPair)).length - 1) BPair.unit) k
      = BPair.unit from ground.getAt_replicate_self BPair.unit
        ((rest.headD ([] : List BPair)).length - 1 + 1) k]
    rfl
  | 1, 0, _, _ => rfl
  | 1, 1, _, _ => rfl
  | 1, 2, _, _ => rfl
  | 1, k + 3, _, _ =>
    show ground.getAt BPair.unit
      (List.replicate ((rest.headD ([] : List BPair)).length - 1)
        BPair.unit) k
      = chainAt (a :: c :: dl) (b :: bb :: ot) 1 (k + 3)
    rw [ground.getAt_replicate_self BPair.unit
      ((rest.headD ([] : List BPair)).length - 1) k]
    rfl
  | s + 2, 0, hi, _ =>
    have hs : s < rest.length := by
      rw [hlen]
      exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)
    show ground.getAt BPair.unit
      (ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun z =>
          (if z < 1 then ground.getAt [] [[BPair.unit, bb]] z
           else List.replicate 2 BPair.unit) ++ ground.getAt [] rest z)) s) 0
      = chainAt (a :: c :: dl) (b :: bb :: ot) (s + 2) 0
    rw [twoRow bb dl.length rest s hs]
    rfl
  | s + 2, 1, hi, _ =>
    have hs : s < rest.length := by
      rw [hlen]
      exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)
    show ground.getAt BPair.unit
      (ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun z =>
          (if z < 1 then ground.getAt [] [[BPair.unit, bb]] z
           else List.replicate 2 BPair.unit) ++ ground.getAt [] rest z)) s) 1
      = chainAt (a :: c :: dl) (b :: bb :: ot) (s + 2) 1
    rw [twoRow bb dl.length rest s hs]
    show ground.getAt BPair.unit
        (bb :: List.replicate dl.length BPair.unit) s
      = chainAt (a :: c :: dl) (b :: bb :: ot) (s + 2) 1
    match s with
    | 0 => rfl
    | m + 1 =>
      show ground.getAt BPair.unit (List.replicate dl.length BPair.unit) m
        = chainAt (a :: c :: dl) (b :: bb :: ot) (m + 3) 1
      rw [ground.getAt_replicate_self BPair.unit dl.length m]
      rfl
  | s + 2, k + 2, hi, hj =>
    have hs : s < rest.length := by
      rw [hlen]
      exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)
    show ground.getAt BPair.unit
      (ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun z =>
          (if z < 1 then ground.getAt [] [[BPair.unit, bb]] z
           else List.replicate 2 BPair.unit) ++ ground.getAt [] rest z)) s)
        (k + 2)
      = chainAt (a :: c :: dl) (b :: bb :: ot) (s + 2) (k + 2)
    rw [twoRow bb dl.length rest s hs,
      chainAt_step a b (c :: dl) (bb :: ot) (s + 1) (k + 1),
      chainAt_step c bb dl ot s k]
    exact hrest s k (by rw [← hlen]; exact hs)
      (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj))


/-- The assembled block row beneath an order-one leading slab whose
off block spans the order-two slab below it. -/
private theorem wideRow (bb : BPair) (L : Nat) (rest : elim.Mat) (s : Nat)
    (hs : s < rest.length) :
    ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun z =>
          (if z < 2 then ground.getAt [] [[bb], [BPair.unit]] z
           else List.replicate 1 BPair.unit) ++ ground.getAt [] rest z)) s
      = ground.getAt BPair.unit (bb :: List.replicate L BPair.unit) s
        :: ground.getAt [] rest s := by
  rw [ground.getAt_map 0 ([] : List BPair) _ (List.range rest.length) s
      (by rw [ground.length_range]; exact hs),
    ground.getAt_range rest.length s hs]
  match s with
  | 0 => rfl
  | 1 =>
    show (BPair.unit :: ([] : List BPair)) ++ ground.getAt [] rest 1
      = ground.getAt BPair.unit (List.replicate L BPair.unit) 0
        :: ground.getAt [] rest 1
    rw [ground.getAt_replicate_self BPair.unit L 0]
    rfl
  | m + 2 =>
    show (List.replicate 1 BPair.unit) ++ ground.getAt [] rest (m + 2)
      = ground.getAt BPair.unit (List.replicate L BPair.unit) (m + 1)
        :: ground.getAt [] rest (m + 2)
    rw [ground.getAt_replicate_self BPair.unit L (m + 1)]
    rfl

/-- The assembled matrix at an order-one leading slab whose off
block spans the order-two slab below reads the entry chart at the
depth spliced into the entry lists. -/
private theorem wideEntry (a bb : BPair) (dl ot : List BPair)
    (rest : elim.Mat)
    (hlen : rest.length = dl.length)
    (hrest : ∀ i j : Nat, i < dl.length → j < dl.length →
      ground.getAt BPair.unit (ground.getAt ([] : List BPair) rest i) j
        = chainAt dl ot i j) :
    ∀ i j : Nat, i < dl.length + 1 → j < dl.length + 1 →
      ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        ((a :: bb :: BPair.unit
            :: List.replicate ((rest.headD ([] : List BPair)).length - 2)
                BPair.unit)
         :: (List.range rest.length).map (fun z =>
              (if z < 2 then ground.getAt [] [[bb], [BPair.unit]] z
               else List.replicate 1 BPair.unit)
                ++ ground.getAt [] rest z)) i) j
      = chainAt (a :: dl) (bb :: ot) i j := by
  intro i j hi hj
  match i, j, hi, hj with
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, k + 2, _, _ =>
    show ground.getAt BPair.unit
      (BPair.unit :: List.replicate
        ((rest.headD ([] : List BPair)).length - 2) BPair.unit) k
      = chainAt (a :: dl) (bb :: ot) 0 (k + 2)
    rw [show ground.getAt BPair.unit (BPair.unit :: List.replicate
        ((rest.headD ([] : List BPair)).length - 2) BPair.unit) k
      = BPair.unit from ground.getAt_replicate_self BPair.unit
        ((rest.headD ([] : List BPair)).length - 2 + 1) k]
    rfl
  | s + 1, 0, hi, _ =>
    have hs : s < rest.length := by
      rw [hlen]
      exact Nat.lt_of_succ_lt_succ hi
    show ground.getAt BPair.unit
      (ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun z =>
          (if z < 2 then ground.getAt [] [[bb], [BPair.unit]] z
           else List.replicate 1 BPair.unit) ++ ground.getAt [] rest z)) s) 0
      = chainAt (a :: dl) (bb :: ot) (s + 1) 0
    rw [wideRow bb dl.length rest s hs]
    match s with
    | 0 => rfl
    | m + 1 =>
      show ground.getAt BPair.unit (List.replicate dl.length BPair.unit) m
        = chainAt (a :: dl) (bb :: ot) (m + 2) 0
      rw [ground.getAt_replicate_self BPair.unit dl.length m]
      rfl
  | s + 1, k + 1, hi, hj =>
    have hs : s < rest.length := by
      rw [hlen]
      exact Nat.lt_of_succ_lt_succ hi
    show ground.getAt BPair.unit
      (ground.getAt ([] : List BPair)
        ((List.range rest.length).map (fun z =>
          (if z < 2 then ground.getAt [] [[bb], [BPair.unit]] z
           else List.replicate 1 BPair.unit) ++ ground.getAt [] rest z)) s)
        (k + 1)
      = chainAt (a :: dl) (bb :: ot) (s + 1) (k + 1)
    rw [wideRow bb dl.length rest s hs, chainAt_step a bb dl ot s k]
    exact hrest s k (by rw [← hlen]; exact hs)
      (Nat.lt_of_succ_lt_succ hj)

/-- The bare order-two chain's entries at its two depths. -/
private theorem twoNilEntry (a b c : BPair) :
    ∀ i j : Nat, i < 2 → j < 2 →
      ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) [[a, b], [b, c]] i) j
        = chainAt [a, c] [b] i j := by
  intro i j hi hj
  match i, j, hi, hj with
  | 0, 0, _, _ => rfl
  | 0, 1, _, _ => rfl
  | 0, k + 2, _, hj =>
    exact absurd (Nat.lt_of_le_of_lt (Nat.le_add_left 2 k) hj)
      (Nat.lt_irrefl 2)
  | 1, 0, _, _ => rfl
  | 1, 1, _, _ => rfl
  | 1, k + 2, _, hj =>
    exact absurd (Nat.lt_of_le_of_lt (Nat.le_add_left 2 k) hj)
      (Nat.lt_irrefl 2)
  | i' + 2, _, hi, _ =>
    exact absurd (Nat.lt_of_le_of_lt (Nat.le_add_left 2 i') hi)
      (Nat.lt_irrefl 2)

/-- The mixed assembly is the well head's own scalar chain: its
order, its row width and its entries at the spliced entry lists. -/
private theorem mixRead (r qn qd : Nat) (en ed : Pos) (c : Nat) : ∀ t : Nat,
    (greenprod.assemble (mDiag r qn qd en ed c t)
        (mOff r qd ed c t)).length = c + 2 + t
    ∧ ((greenprod.assemble (mDiag r qn qd en ed c t)
        (mOff r qd ed c t)).headD ([] : List BPair)).length = c + 2 + t
    ∧ ∀ i j : Nat, i < c + 2 + t → j < c + 2 + t →
        ground.getAt BPair.unit (ground.getAt ([] : List BPair)
          (greenprod.assemble (mDiag r qn qd en ed c t)
            (mOff r qd ed c t)) i) j
          = chainAt (wDiagE r qn qd en ed (c + 2 + t))
              (wOffE r qd ed (c + 2 + t)) i j := by
  intro t
  induction t with
  | zero =>
    match c with
    | 0 =>
      have hass : greenprod.assemble (mDiag r qn qd en ed 0 0)
          (mOff r qd ed 0 0) = spotMat r qn qd en ed 0 := rfl
      have hd1 : wDiagE r qn qd en ed (0 + 2 + 0)
          = wellDiag r qn qd en ed (0 + 2) :: wDiagE r qn qd en ed (0 + 1) :=
        wDiagE_cons r qn qd en ed (0 + 1)
      have hd2 : wDiagE r qn qd en ed (0 + 1)
          = wellDiag r qn qd en ed (0 + 1) :: wDiagE r qn qd en ed 0 :=
        wDiagE_cons r qn qd en ed 0
      have hd0 : wDiagE r qn qd en ed 0 = ([] : List BPair) := rfl
      have ho1 : wOffE r qd ed (0 + 2 + 0)
          = (wellBond r qd ed).swap :: wOffE r qd ed (0 + 1) :=
        wOffE_cons r qd ed 0
      have ho0 : wOffE r qd ed (0 + 1) = ([] : List BPair) := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hass]; rfl
      · rw [hass]; rfl
      · rw [hass, hd1, hd2, hd0, ho1, ho0]
        exact twoNilEntry (wellDiag r qn qd en ed (0 + 2))
          (wellBond r qd ed).swap (wellDiag r qn qd en ed (0 + 1))
    | c' + 1 =>
      have hdl : (wDiagE r qn qd en ed (c' + 1)).length = c' + 1 :=
        wDiagE_len r qn qd en ed (c' + 1)
      have hchl : (wOffE r qd ed (c' + 1)).length + 1
          = (wDiagE r qn qd en ed (c' + 1)).length := by
        rw [wOffE_len r qd ed (c' + 1), hdl]
        rfl
      have hL := chainLen (wDiagE r qn qd en ed (c' + 1))
        (wOffE r qd ed (c' + 1)) hchl
      have hE := chainEntry (wDiagE r qn qd en ed (c' + 1))
        (wOffE r qd ed (c' + 1)) hchl
      rw [← wDiagL_map r qn qd en ed (c' + 1),
        ← wOffL_map r qd ed (c' + 1)] at hL hE
      have hd1 : wDiagE r qn qd en ed (c' + 1 + 2 + 0)
          = wellDiag r qn qd en ed (c' + 1 + 2)
            :: wDiagE r qn qd en ed (c' + 1 + 1) :=
        wDiagE_cons r qn qd en ed (c' + 1 + 1)
      have hd2 : wDiagE r qn qd en ed (c' + 1 + 1)
          = wellDiag r qn qd en ed (c' + 1 + 1)
            :: wDiagE r qn qd en ed (c' + 1) :=
        wDiagE_cons r qn qd en ed (c' + 1)
      have ho1 : wOffE r qd ed (c' + 1 + 2 + 0)
          = (wellBond r qd ed).swap :: wOffE r qd ed (c' + 1 + 1) :=
        wOffE_cons r qd ed (c' + 1)
      have ho2 : wOffE r qd ed (c' + 1 + 1)
          = (wellBond r qd ed).swap :: wOffE r qd ed (c' + 1) :=
        wOffE_cons r qd ed c'
      refine ⟨?_, ?_, ?_⟩
      · show ((List.range (greenprod.assemble (wDiagL r qn qd en ed (c' + 1))
            (wOffL r qd ed (c' + 1))).length).map _).length + 1 + 1
          = c' + 1 + 2 + 0
        rw [ground.length_mapRange, hL.1, hdl]
      · show (List.replicate
          (((greenprod.assemble (wDiagL r qn qd en ed (c' + 1))
            (wOffL r qd ed (c' + 1))).headD ([] : List BPair)).length - 1)
            BPair.unit).length + 1 + 1 + 1 = c' + 1 + 2 + 0
        rw [ground.length_replicate, hL.2, hdl]
        rfl
      · rw [hd1, hd2, ho1, ho2]
        have key := twoEntry (wellDiag r qn qd en ed (c' + 1 + 2))
          (wellBond r qd ed).swap (wellDiag r qn qd en ed (c' + 1 + 1))
          (wellBond r qd ed).swap (wDiagE r qn qd en ed (c' + 1))
          (wOffE r qd ed (c' + 1))
          (greenprod.assemble (wDiagL r qn qd en ed (c' + 1))
            (wOffL r qd ed (c' + 1)))
          hL.1 hE
        rw [hdl] at key
        exact key
  | succ t ih =>
    match t with
    | 0 =>
      have hd1 : wDiagE r qn qd en ed (c + 2 + (0 + 1))
          = wellDiag r qn qd en ed (c + 2 + 0 + 1)
            :: wDiagE r qn qd en ed (c + 2 + 0) :=
        wDiagE_cons r qn qd en ed (c + 2 + 0)
      have ho1 : wOffE r qd ed (c + 2 + (0 + 1))
          = (wellBond r qd ed).swap :: wOffE r qd ed (c + 2 + 0) :=
        wOffE_cons r qd ed (c + 1)
      have hlen : (greenprod.assemble (mDiag r qn qd en ed c 0)
          (mOff r qd ed c 0)).length
          = (wDiagE r qn qd en ed (c + 2 + 0)).length := by
        rw [ih.1, wDiagE_len r qn qd en ed (c + 2 + 0)]
      have hent : ∀ i j : Nat,
          i < (wDiagE r qn qd en ed (c + 2 + 0)).length →
          j < (wDiagE r qn qd en ed (c + 2 + 0)).length →
          ground.getAt BPair.unit (ground.getAt ([] : List BPair)
            (greenprod.assemble (mDiag r qn qd en ed c 0)
              (mOff r qd ed c 0)) i) j
            = chainAt (wDiagE r qn qd en ed (c + 2 + 0))
                (wOffE r qd ed (c + 2 + 0)) i j := by
        intro i j hi hj
        rw [wDiagE_len r qn qd en ed (c + 2 + 0)] at hi hj
        exact ih.2.2 i j hi hj
      refine ⟨?_, ?_, ?_⟩
      · show ((List.range (greenprod.assemble (mDiag r qn qd en ed c 0)
            (mOff r qd ed c 0)).length).map _).length + 1
          = c + 2 + (0 + 1)
        rw [ground.length_mapRange, ih.1]
      · show (List.replicate
          (((greenprod.assemble (mDiag r qn qd en ed c 0)
            (mOff r qd ed c 0)).headD ([] : List BPair)).length - 2)
            BPair.unit).length + 1 + 1 + 1 = c + 2 + (0 + 1)
        rw [ground.length_replicate, ih.2.1]
        rfl
      · rw [hd1, ho1]
        have key := wideEntry (wellDiag r qn qd en ed (c + 2 + 0 + 1))
          (wellBond r qd ed).swap (wDiagE r qn qd en ed (c + 2 + 0))
          (wOffE r qd ed (c + 2 + 0))
          (greenprod.assemble (mDiag r qn qd en ed c 0) (mOff r qd ed c 0))
          hlen hent
        rw [wDiagE_len r qn qd en ed (c + 2 + 0)] at key
        exact key
    | t' + 1 =>
      have hd1 : wDiagE r qn qd en ed (c + 2 + (t' + 1 + 1))
          = wellDiag r qn qd en ed (c + 2 + (t' + 1) + 1)
            :: wDiagE r qn qd en ed (c + 2 + (t' + 1)) :=
        wDiagE_cons r qn qd en ed (c + 2 + (t' + 1))
      have ho1 : wOffE r qd ed (c + 2 + (t' + 1 + 1))
          = (wellBond r qd ed).swap :: wOffE r qd ed (c + 2 + (t' + 1)) :=
        wOffE_cons r qd ed (c + 2 + t')
      have hlen : (greenprod.assemble (mDiag r qn qd en ed c (t' + 1))
          (mOff r qd ed c (t' + 1))).length
          = (wDiagE r qn qd en ed (c + 2 + (t' + 1))).length := by
        rw [ih.1, wDiagE_len r qn qd en ed (c + 2 + (t' + 1))]
      have hent : ∀ i j : Nat,
          i < (wDiagE r qn qd en ed (c + 2 + (t' + 1))).length →
          j < (wDiagE r qn qd en ed (c + 2 + (t' + 1))).length →
          ground.getAt BPair.unit (ground.getAt ([] : List BPair)
            (greenprod.assemble (mDiag r qn qd en ed c (t' + 1))
              (mOff r qd ed c (t' + 1))) i) j
            = chainAt (wDiagE r qn qd en ed (c + 2 + (t' + 1)))
                (wOffE r qd ed (c + 2 + (t' + 1))) i j := by
        intro i j hi hj
        rw [wDiagE_len r qn qd en ed (c + 2 + (t' + 1))] at hi hj
        exact ih.2.2 i j hi hj
      refine ⟨?_, ?_, ?_⟩
      · show ((List.range (greenprod.assemble
            (mDiag r qn qd en ed c (t' + 1))
            (mOff r qd ed c (t' + 1))).length).map _).length + 1
          = c + 2 + (t' + 1 + 1)
        rw [ground.length_mapRange, ih.1]
        rfl
      · show (List.replicate
          (((greenprod.assemble (mDiag r qn qd en ed c (t' + 1))
            (mOff r qd ed c (t' + 1))).headD ([] : List BPair)).length - 1)
            BPair.unit).length + 1 + 1 = c + 2 + (t' + 1 + 1)
        rw [ground.length_replicate, ih.2.1]
        rfl
      · rw [hd1, ho1]
        have key := consEntry (wellDiag r qn qd en ed (c + 2 + (t' + 1) + 1))
          (wellBond r qd ed).swap (wDiagE r qn qd en ed (c + 2 + (t' + 1)))
          (wOffE r qd ed (c + 2 + (t' + 1)))
          (greenprod.assemble (mDiag r qn qd en ed c (t' + 1))
            (mOff r qd ed c (t' + 1)))
          hlen hent
        rw [wDiagE_len r qn qd en ed (c + 2 + (t' + 1))] at key
        exact key


/-- The mixed assembly's rows read its own order. -/
private theorem mixRows (r qn qd : Nat) (en ed : Pos) (c : Nat) : ∀ t : Nat,
    elim.rowsLen (c + 2 + t) (greenprod.assemble (mDiag r qn qd en ed c t)
      (mOff r qd ed c t)) := by
  intro t
  induction t with
  | zero =>
    match c with
    | 0 =>
      have hass : greenprod.assemble (mDiag r qn qd en ed 0 0)
          (mOff r qd ed 0 0) = spotMat r qn qd en ed 0 := rfl
      rw [hass]
      exact ⟨rfl, rfl, trivial⟩
    | c' + 1 =>
      have hdl : (wDiagE r qn qd en ed (c' + 1)).length = c' + 1 :=
        wDiagE_len r qn qd en ed (c' + 1)
      have hchl : (wOffE r qd ed (c' + 1)).length + 1
          = (wDiagE r qn qd en ed (c' + 1)).length := by
        rw [wOffE_len r qd ed (c' + 1), hdl]
        rfl
      have hL := chainLen (wDiagE r qn qd en ed (c' + 1))
        (wOffE r qd ed (c' + 1)) hchl
      have hR := chainRows (wDiagE r qn qd en ed (c' + 1))
        (wOffE r qd ed (c' + 1)) hchl
      rw [← wDiagL_map r qn qd en ed (c' + 1),
        ← wOffL_map r qd ed (c' + 1)] at hL hR
      rw [hdl] at hL hR
      refine ⟨?_, ?_, ?_⟩
      · show (List.replicate
          (((greenprod.assemble (wDiagL r qn qd en ed (c' + 1))
            (wOffL r qd ed (c' + 1))).headD ([] : List BPair)).length - 1)
            BPair.unit).length + 1 + 1 + 1 = c' + 1 + 2 + 0
        rw [ground.length_replicate, hL.2]
        rfl
      · show (List.replicate
          (((greenprod.assemble (wDiagL r qn qd en ed (c' + 1))
            (wOffL r qd ed (c' + 1))).headD ([] : List BPair)).length - 1)
            BPair.unit).length + 1 + 1 + 1 = c' + 1 + 2 + 0
        rw [ground.length_replicate, hL.2]
        rfl
      · refine elim.rowsLen_map _ (c' + 1 + 2 + 0) _ (fun s hs => ?_)
        have hs' : s < (greenprod.assemble (wDiagL r qn qd en ed (c' + 1))
            (wOffL r qd ed (c' + 1))).length := ground.ltOfMemRange hs
        have h1 : ((if s < 1
            then ground.getAt [] [[BPair.unit, (wellBond r qd ed).swap]] s
            else List.replicate 2 BPair.unit) : List BPair).length = 2 := by
          match s with
          | 0 => rfl
          | _ + 1 => rfl
        show ((if s < 1
            then ground.getAt [] [[BPair.unit, (wellBond r qd ed).swap]] s
            else List.replicate 2 BPair.unit)
              ++ ground.getAt [] (greenprod.assemble
                  (wDiagL r qn qd en ed (c' + 1))
                  (wOffL r qd ed (c' + 1))) s).length = c' + 1 + 2 + 0
        rw [ground.length_append, h1, elim.rowsLen_getAt _ s hR hs']
        exact Nat.add_comm 2 (c' + 1)
  | succ t ih =>
    match t with
    | 0 =>
      refine ⟨?_, ?_⟩
      · show (List.replicate
          (((greenprod.assemble (mDiag r qn qd en ed c 0)
            (mOff r qd ed c 0)).headD ([] : List BPair)).length - 2)
            BPair.unit).length + 1 + 1 + 1 = c + 2 + (0 + 1)
        rw [ground.length_replicate, (mixRead r qn qd en ed c 0).2.1]
        rfl
      · refine elim.rowsLen_map _ (c + 2 + (0 + 1)) _ (fun s hs => ?_)
        have hs' : s < (greenprod.assemble (mDiag r qn qd en ed c 0)
            (mOff r qd ed c 0)).length := ground.ltOfMemRange hs
        have h1 : ((if s < 2
            then ground.getAt [] [[(wellBond r qd ed).swap], [BPair.unit]] s
            else List.replicate 1 BPair.unit) : List BPair).length = 1 := by
          match s with
          | 0 => rfl
          | 1 => rfl
          | _ + 2 => rfl
        show ((if s < 2
            then ground.getAt [] [[(wellBond r qd ed).swap], [BPair.unit]] s
            else List.replicate 1 BPair.unit)
              ++ ground.getAt [] (greenprod.assemble
                  (mDiag r qn qd en ed c 0) (mOff r qd ed c 0)) s).length
          = c + 2 + (0 + 1)
        rw [ground.length_append, h1, elim.rowsLen_getAt _ s ih hs']
        exact Nat.add_comm 1 (c + 2 + 0)
    | t' + 1 =>
      refine ⟨?_, ?_⟩
      · show (List.replicate
          (((greenprod.assemble (mDiag r qn qd en ed c (t' + 1))
            (mOff r qd ed c (t' + 1))).headD ([] : List BPair)).length - 1)
            BPair.unit).length + 1 + 1 = c + 2 + (t' + 1 + 1)
        rw [ground.length_replicate, (mixRead r qn qd en ed c (t' + 1)).2.1]
        rfl
      · refine elim.rowsLen_map _ (c + 2 + (t' + 1 + 1)) _ (fun s hs => ?_)
        have hs' : s < (greenprod.assemble (mDiag r qn qd en ed c (t' + 1))
            (mOff r qd ed c (t' + 1))).length := ground.ltOfMemRange hs
        have h1 : ((if s < 1
            then ground.getAt [] [[(wellBond r qd ed).swap]] s
            else List.replicate 1 BPair.unit) : List BPair).length = 1 := by
          match s with
          | 0 => rfl
          | _ + 1 => rfl
        show ((if s < 1
            then ground.getAt [] [[(wellBond r qd ed).swap]] s
            else List.replicate 1 BPair.unit)
              ++ ground.getAt [] (greenprod.assemble
                  (mDiag r qn qd en ed c (t' + 1))
                  (mOff r qd ed c (t' + 1))) s).length
          = c + 2 + (t' + 1 + 1)
        rw [ground.length_append, h1, elim.rowsLen_getAt _ s ih hs']
        exact Nat.add_comm 1 (c + 2 + (t' + 1))

/-- The mixed assembly is square at the head's order. -/
private theorem mixSq (r qn qd : Nat) (en ed : Pos) (c t : Nat) :
    elim.sqAt (greenprod.assemble (mDiag r qn qd en ed c t)
      (mOff r qd ed c t)) (c + 2 + t) :=
  elim.sqAt_of (mixRead r qn qd en ed c t).1 (mixRows r qn qd en ed c t)

/-- The well head reads the mixed assembly's value: the degenerate
spot's two depths re-ordered inside one slab, the matrix the
same. -/
private theorem mixMat (r qn qd : Nat) (en ed : Pos) (c t : Nat) :
    elim.matOneValue (wellMat r qn qd en ed (c + 2 + t))
      (greenprod.assemble (mDiag r qn qd en ed c t) (mOff r qd ed c t)) := by
  have harith : c + 2 + t = c + 1 + t + 1 := Nat.add_right_comm (c + 1) 1 t
  have hwl : (wellMat r qn qd en ed (c + 2 + t)).length = c + 2 + t := by
    rw [harith]
    exact wellLen r qn qd en ed (c + 1 + t)
  have hwr : elim.rowsLen (c + 2 + t)
      (wellMat r qn qd en ed (c + 2 + t)) := by
    rw [harith]
    exact wellRows r qn qd en ed (c + 1 + t)
  refine elim.matOne_of_entries _ _ (c + 2 + t) hwl hwr
    (mixRead r qn qd en ed c t).1 (mixRows r qn qd en ed c t) ?_
  intro i j hi hj
  have hw : ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (wellMat r qn qd en ed (c + 2 + t)) i) j
      = chainAt (wDiagE r qn qd en ed (c + 2 + t))
          (wOffE r qd ed (c + 2 + t)) i j := by
    rw [harith]
    exact wellEntry r qn qd en ed (c + 1 + t) i j
      (by rw [← harith]; exact hi) (by rw [← harith]; exact hj)
  rw [hw, (mixRead r qn qd en ed c t).2.2 i j hi hj]
  exact BPair.oneValue_refl _


/-- The degenerate spot's cleared order-two pivot: the spot's slab
less the shallower chain's transfer, cleared at the boundary minor's
square, the seed arm the slab itself. -/
private def spotQ (r qn qd : Nat) (en ed : Pos) : Nat → greenprod.MatQ
  | 0 => greenprod.ofM (spotMat r qn qd en ed 0)
  | c + 1 =>
    ([[wellDiag r qn qd en ed (c + 1 + 2)
          * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)),
        (wellBond r qd ed).swap
          * (wellWalk r qn qd en ed (c + 1)
            * wellWalk r qn qd en ed (c + 1))],
       [(wellBond r qd ed).swap
          * (wellWalk r qn qd en ed (c + 1)
            * wellWalk r qn qd en ed (c + 1)),
        wellDiag r qn qd en ed (c + 1 + 1)
            * (wellWalk r qn qd en ed (c + 1)
              * wellWalk r qn qd en ed (c + 1))
          + (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
              * wellWalk r qn qd en ed (c + 1)).swap]],
     Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)

/-- The spot's witness against the shallower chain, the order-one
pivot's solve at the spot's own off block. -/
private def spotWit (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    greenprod.MatQ :=
  ([[BPair.unit, (wellBond r qd ed).swap * wellWalk r qn qd en ed c
      * wellWalk r qn qd en ed (c + 1)]],
   Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)

/-- The witness above the spot: the order-two pivot's solve at the
depth beyond the spot's own. -/
private def spotR (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    greenprod.MatQ :=
  ([[(wellBond r qd ed).swap * wellWalk r qn qd en ed (c + 1)
      * wellWalk r qn qd en ed (c + 2)],
    [(wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
      * wellWalk r qn qd en ed (c + 2)).swap]],
   Pos.pow (margP (wellWalk r qn qd en ed (c + 2))) 2)

/-- The mixed pivot list: the spot's order-two pivot among the
order-one pivots. -/
private def mX (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    Nat → List greenprod.MatQ
  | 0 => spotQ r qn qd en ed c :: wXL r qn qd en ed c
  | t + 1 =>
    pivotQ r qn qd en ed (c + 2 + t + 1) :: mX r qn qd en ed c t

/-- The mixed witness list at and below the spot. -/
private def mRBase (r qn qd : Nat) (en ed : Pos) :
    Nat → List greenprod.MatQ
  | 0 => []
  | c + 1 => spotWit r qn qd en ed c :: wRL r qn qd en ed (c + 1)

/-- The mixed witness list: the order-one chain's witnesses above
the spot, the spot's own at its upper side, and the spot's solve
against the shallower chain below it. -/
private def mR (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    Nat → List greenprod.MatQ
  | 0 => mRBase r qn qd en ed c
  | 1 => spotR r qn qd en ed c :: mRBase r qn qd en ed c
  | t + 2 =>
    pivotR r qn qd en ed (c + 2 + t + 1) :: mR r qn qd en ed c (t + 1)

/-- The mixed slab walk's shape at the mixed orders. -/
private theorem mixSlab (r qn qd : Nat) (en ed : Pos) (c : Nat) : ∀ t : Nat,
    greenprod.slabShape (mDiag r qn qd en ed c t) (mOff r qd ed c t)
      (mNs c t) := by
  intro t
  induction t with
  | zero =>
    match c with
    | 0 =>
      show 0 < 2 ∧ elim.sqAt (spotMat r qn qd en ed 0) 2
      exact ⟨Nat.succ_pos 1, rfl⟩
    | c' + 1 =>
      have hcons : mDiag r qn qd en ed (c' + 1) 0
          = spotMat r qn qd en ed (c' + 1)
            :: [[wellDiag r qn qd en ed (c' + 1)]]
              :: wDiagL r qn qd en ed c' := by
        show spotMat r qn qd en ed (c' + 1)
          :: wDiagL r qn qd en ed (c' + 1) = _
        rw [wDiagL_cons r qn qd en ed c']
      rw [hcons]
      show 0 < 2 ∧ elim.sqAt (spotMat r qn qd en ed (c' + 1)) 2
        ∧ elim.rectAt [[BPair.unit], [(wellBond r qd ed).swap]] 2 1
        ∧ greenprod.slabShape
            ([[wellDiag r qn qd en ed (c' + 1)]] :: wDiagL r qn qd en ed c')
            (wOffL r qd ed (c' + 1)) (List.replicate (c' + 1) 1)
      refine ⟨Nat.succ_pos 1, rfl, rfl, ?_⟩
      rw [← wDiagL_cons r qn qd en ed c']
      exact wellSlab r qn qd en ed c'
  | succ t ih =>
    match t with
    | 0 =>
      show 0 < 1 ∧ elim.sqAt [[wellDiag r qn qd en ed (c + 2 + 0 + 1)]] 1
        ∧ elim.rectAt [[(wellBond r qd ed).swap, BPair.unit]] 1 2
        ∧ greenprod.slabShape (mDiag r qn qd en ed c 0)
            (mOff r qd ed c 0) (mNs c 0)
      exact ⟨Nat.zero_lt_one, rfl, rfl, ih⟩
    | t' + 1 =>
      show 0 < 1
        ∧ elim.sqAt [[wellDiag r qn qd en ed (c + 2 + (t' + 1) + 1)]] 1
        ∧ elim.rectAt [[(wellBond r qd ed).swap]] 1 1
        ∧ greenprod.slabShape (mDiag r qn qd en ed c (t' + 1))
            (mOff r qd ed c (t' + 1)) (mNs c (t' + 1))
      exact ⟨Nat.zero_lt_one, rfl, rfl, ih⟩

/-- The mixed pivots' shape at the mixed orders. -/
private theorem mixQShape (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    ∀ t : Nat, greenprod.qShape (mX r qn qd en ed c t) (mNs c t) := by
  intro t
  induction t with
  | zero =>
    match c with
    | 0 =>
      show elim.sqAt (spotQ r qn qd en ed 0).1 2
        ∧ greenprod.qShape ([] : List greenprod.MatQ) ([] : List Nat)
      exact ⟨rfl, trivial⟩
    | c' + 1 =>
      show elim.sqAt (spotQ r qn qd en ed (c' + 1)).1 2
        ∧ greenprod.qShape (wXL r qn qd en ed (c' + 1))
            (List.replicate (c' + 1) 1)
      exact ⟨rfl, wellQShape r qn qd en ed c'⟩
  | succ t ih =>
    show elim.sqAt (pivotQ r qn qd en ed (c + 2 + t + 1)).1 1
      ∧ greenprod.qShape (mX r qn qd en ed c t) (mNs c t)
    exact ⟨rfl, ih⟩

/-- The mixed witnesses' shape at the mixed orders. -/
private theorem mixWShape (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    ∀ t : Nat, greenprod.wShapeR (mR r qn qd en ed c t) (mNs c t) := by
  intro t
  induction t with
  | zero =>
    match c with
    | 0 => exact trivial
    | c' + 1 =>
      show elim.rectAt (spotWit r qn qd en ed c').1 1 2
        ∧ greenprod.wShapeR (wRL r qn qd en ed (c' + 1))
            (List.replicate (c' + 1) 1)
      exact ⟨rfl, wellWShape r qn qd en ed c'⟩
  | succ t ih =>
    match t with
    | 0 =>
      show elim.rectAt (spotR r qn qd en ed c).1 2 1
        ∧ greenprod.wShapeR (mR r qn qd en ed c 0) (mNs c 0)
      exact ⟨rfl, ih⟩
    | t' + 1 =>
      show elim.rectAt (pivotR r qn qd en ed (c + 2 + t' + 1)).1 1 1
        ∧ greenprod.wShapeR (mR r qn qd en ed c (t' + 1)) (mNs c (t' + 1))
      exact ⟨rfl, ih⟩


/-- Order-two cleared data read one value entry by entry. -/
private theorem oneQ22 {a b c d a' b' c' d' : BPair} {p q : Pos}
    (h11 : (BPair.ofPos q * a).oneValue (BPair.ofPos p * a'))
    (h12 : (BPair.ofPos q * b).oneValue (BPair.ofPos p * b'))
    (h21 : (BPair.ofPos q * c).oneValue (BPair.ofPos p * c'))
    (h22 : (BPair.ofPos q * d).oneValue (BPair.ofPos p * d')) :
    greenprod.oneValueQ ([[a, b], [c, d]], p) ([[a', b'], [c', d']], q) :=
  ⟨⟨qEntry h11, qEntry h12, trivial⟩,
   ⟨qEntry h21, qEntry h22, trivial⟩, trivial⟩

/-- A one-by-two cleared datum's read. -/
private theorem oneQ12 {a b a' b' : BPair} {p q : Pos}
    (h1 : (BPair.ofPos q * a).oneValue (BPair.ofPos p * a'))
    (h2 : (BPair.ofPos q * b).oneValue (BPair.ofPos p * b')) :
    greenprod.oneValueQ ([[a, b]], p) ([[a', b']], q) :=
  ⟨⟨qEntry h1, qEntry h2, trivial⟩, trivial⟩

/-- A two-by-one cleared datum's read. -/
private theorem oneQ21 {a b a' b' : BPair} {p q : Pos}
    (h1 : (BPair.ofPos q * a).oneValue (BPair.ofPos p * a'))
    (h2 : (BPair.ofPos q * b).oneValue (BPair.ofPos p * b')) :
    greenprod.oneValueQ ([[a], [b]], p) ([[a'], [b']], q) :=
  ⟨⟨qEntry h1, trivial⟩, ⟨qEntry h2, trivial⟩, trivial⟩

/-- A repeated factor collects at the square. -/
private theorem sqShuffle (x y : BPair) : x * (y * x) = x * x * y := by
  rw [BPair.mul_left_comm x y x, BPair.mul_comm y (x * x)]

/-- A vacant entry's fold against any partner is the sum's unit. -/
private theorem dotUnitL (x : BPair) :
    (elim.dotN [BPair.unit] [x]).oneValue BPair.unit :=
  BPair.oneValue_trans (inertia.dotN_single BPair.unit x) (BPair.unit_mul x)

/-- A fold against a vacant partner is the sum's unit. -/
private theorem dotUnitR (x : BPair) :
    (elim.dotN [x] [BPair.unit]).oneValue BPair.unit :=
  BPair.oneValue_trans (inertia.dotN_single x BPair.unit) (BPair.mul_unit x)

/-- The spot's witness step: the shallower chain's pivot against the
spot's witness reads the spot's off block exchanged. -/
private theorem spotCross (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (h0 : ¬ (wellWalk r qn qd en ed c).oneValue BPair.unit)
    (h1 : ¬ (wellWalk r qn qd en ed (c + 1)).oneValue BPair.unit) :
    greenprod.oneValueQ
      (greenprod.mulQ (pivotQ r qn qd en ed (c + 1))
        (spotWit r qn qd en ed c))
      (greenprod.ofM (elim.transposeM
        [[BPair.unit], [(wellBond r qd ed).swap]])) := by
  refine oneQ12
    (a := elim.dotN
      [wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed c]
      [BPair.unit])
    (b := elim.dotN
      [wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed c]
      [(wellBond r qd ed).swap * wellWalk r qn qd en ed c
        * wellWalk r qn qd en ed (c + 1)])
    (a' := BPair.unit) (b' := (wellBond r qd ed).swap)
    (p := Pos.pow (margP (wellWalk r qn qd en ed c)) 2
      * Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)
    (q := Pos.one) ?_ ?_
  · exact BPair.oneValue_trans
      (BPair.oneValue_trans (BPair.ofPos_one_mul _) (dotUnitR _))
      (BPair.oneValue_symm (BPair.mul_unit _))
  · refine BPair.oneValue_trans
      (BPair.oneValue_trans (BPair.ofPos_one_mul _)
        (BPair.oneValue_trans (inertia.dotN_single _ _)
          (BPair.oneValue_of_eq (prodShuffle (wellWalk r qn qd en ed (c + 1))
            (wellWalk r qn qd en ed c) (wellBond r qd ed).swap))))
      (BPair.oneValue_symm ?_)
    exact BPair.mul_congr (margPair r qn qd en ed c (c + 1) h0 h1)
      (BPair.oneValue_refl _)


/-- The spot's recursion join: the spot's pivot against the
bond-weighted witness reads the spot's own slab. -/
private theorem spotJoin (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (h1 : ¬ (wellWalk r qn qd en ed (c + 1)).oneValue BPair.unit) :
    greenprod.oneValueQ
      (greenprod.addQ (spotQ r qn qd en ed (c + 1))
        (greenprod.mulQ
          (greenprod.ofM [[BPair.unit], [(wellBond r qd ed).swap]])
          (spotWit r qn qd en ed c)))
      (greenprod.ofM (spotMat r qn qd en ed (c + 1))) := by
  have hsq : (BPair.ofPos (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2
        * (Pos.one * Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2))).oneValue
      (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)
        * (wellWalk r qn qd en ed (c + 1)
          * wellWalk r qn qd en ed (c + 1))) := by
    rw [ground.one_mul (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)]
    exact margPair r qn qd en ed (c + 1) (c + 1) h1 h1
  have hcore : ∀ x z y : BPair,
      (z + y).oneValue (x * (wellWalk r qn qd en ed (c + 1)
        * wellWalk r qn qd en ed (c + 1))) →
      (BPair.ofPos Pos.one
          * (z.scale (Pos.one
                * Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)
            + y.scale
                (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2))).oneValue
        (BPair.ofPos (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2
            * (Pos.one
              * Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)) * x) := by
    intro x z y hzy
    rw [ground.one_mul (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)]
    refine BPair.oneValue_trans (BPair.ofPos_one_mul _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_symm (BPair.ofPos_scale _ z))
        (BPair.oneValue_symm (BPair.ofPos_scale _ y))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.left_distrib
          (BPair.ofPos (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2))
          z y).symm) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) hzy) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (margP_sq _ h1) (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (sqShuffle (wellWalk r qn qd en ed (c + 1)
          * wellWalk r qn qd en ed (c + 1)) x)) ?_
    refine BPair.oneValue_symm (BPair.mul_congr ?_ (BPair.oneValue_refl x))
    rw [ground.one_mul (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)]
      at hsq
    exact hsq
  have hbb : (wellBond r qd ed).swap
        * ((wellBond r qd ed).swap * wellWalk r qn qd en ed c
          * wellWalk r qn qd en ed (c + 1))
      = wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
        * wellWalk r qn qd en ed (c + 1) := by
    rw [bondShuffle (wellBond r qd ed).swap (wellWalk r qn qd en ed c)
      (wellWalk r qn qd en ed (c + 1)), BPair.swap_sq (wellBond r qd ed)]
  exact oneQ22
    (a := (wellDiag r qn qd en ed (c + 1 + 2)
          * (wellWalk r qn qd en ed (c + 1)
            * wellWalk r qn qd en ed (c + 1))).scale
        (Pos.one * Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)
      + (elim.dotN [BPair.unit] [BPair.unit]).scale
        (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2))
    (b := ((wellBond r qd ed).swap
          * (wellWalk r qn qd en ed (c + 1)
            * wellWalk r qn qd en ed (c + 1))).scale
        (Pos.one * Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)
      + (elim.dotN [BPair.unit]
          [(wellBond r qd ed).swap * wellWalk r qn qd en ed c
            * wellWalk r qn qd en ed (c + 1)]).scale
        (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2))
    (c := ((wellBond r qd ed).swap
          * (wellWalk r qn qd en ed (c + 1)
            * wellWalk r qn qd en ed (c + 1))).scale
        (Pos.one * Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)
      + (elim.dotN [(wellBond r qd ed).swap] [BPair.unit]).scale
        (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2))
    (d := (wellDiag r qn qd en ed (c + 1 + 1)
            * (wellWalk r qn qd en ed (c + 1)
              * wellWalk r qn qd en ed (c + 1))
          + (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
              * wellWalk r qn qd en ed (c + 1)).swap).scale
        (Pos.one * Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2)
      + (elim.dotN [(wellBond r qd ed).swap]
          [(wellBond r qd ed).swap * wellWalk r qn qd en ed c
            * wellWalk r qn qd en ed (c + 1)]).scale
        (Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2))
    (a' := wellDiag r qn qd en ed (c + 1 + 2))
    (b' := (wellBond r qd ed).swap)
    (c' := (wellBond r qd ed).swap)
    (d' := wellDiag r qn qd en ed (c + 1 + 1))
    (p := Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2
      * (Pos.one * Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2))
    (q := Pos.one)
    (hcore (wellDiag r qn qd en ed (c + 1 + 2))
      (wellDiag r qn qd en ed (c + 1 + 2)
        * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)))
      (elim.dotN [BPair.unit] [BPair.unit])
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (dotUnitL BPair.unit))
        (BPair.add_unit _)))
    (hcore (wellBond r qd ed).swap
      ((wellBond r qd ed).swap
        * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)))
      (elim.dotN [BPair.unit]
        [(wellBond r qd ed).swap * wellWalk r qn qd en ed c
          * wellWalk r qn qd en ed (c + 1)])
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (dotUnitL _))
        (BPair.add_unit _)))
    (hcore (wellBond r qd ed).swap
      ((wellBond r qd ed).swap
        * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)))
      (elim.dotN [(wellBond r qd ed).swap] [BPair.unit])
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (dotUnitR _))
        (BPair.add_unit _)))
    (hcore (wellDiag r qn qd en ed (c + 1 + 1))
      (wellDiag r qn qd en ed (c + 1 + 1)
          * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1))
        + (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
            * wellWalk r qn qd en ed (c + 1)).swap)
      (elim.dotN [(wellBond r qd ed).swap]
        [(wellBond r qd ed).swap * wellWalk r qn qd en ed c
          * wellWalk r qn qd en ed (c + 1)])
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans
            (inertia.dotN_single (wellBond r qd ed).swap
              ((wellBond r qd ed).swap * wellWalk r qn qd en ed c
                * wellWalk r qn qd en ed (c + 1)))
            (BPair.oneValue_of_eq hbb)))
        (BPair.add_swap_self _ _)))


/-- The two-key fold reads its two products' sum. -/
private theorem dotN_pair (a b x y : BPair) :
    (elim.dotN [a, b] [x, y]).oneValue (a * x + b * y) := by
  refine BPair.oneValue_trans (elim.dotN_read [a, b] [x, y]) ?_
  show (a * x + (b * y + BPair.unit)).oneValue (a * x + b * y)
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit (b * y))

/-- The recursion's step at a scaled carrier: the recursion read
carried through the shared factor withdraws the transfer. -/
private theorem crossStep (K A B S : BPair) (h : (S + B).oneValue A) :
    (K * A + (K * B).swap).oneValue (K * S) := by
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl K) (BPair.oneValue_symm h))
        (BPair.oneValue_of_eq (BPair.left_distrib K S B)))
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc (K * S) (K * B) (K * B).swap)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_of_eq (BPair.add_comm (K * B) (K * B).swap))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.add_assoc (K * S) (K * B).swap (K * B)).symm) ?_
  exact BPair.add_swap_self (K * S) (K * B)

/-- The spot's first row against its witness collects at the
shared carrier. -/
private theorem shA (a d b w2 w3 : BPair) :
    a * (d * d) * (b * w2 * w3) = b * (d * d) * w3 * (a * w2) := by
  rw [BPair.mul_assoc b w2 w3, BPair.mul_assoc a (d * d) (b * (w2 * w3)),
    BPair.mul_assoc d d (b * (w2 * w3)),
    BPair.mul_left_comm a d (d * (b * (w2 * w3))),
    BPair.mul_left_comm a d (b * (w2 * w3)),
    BPair.mul_left_comm a b (w2 * w3),
    BPair.mul_assoc (b * (d * d)) w3 (a * w2),
    BPair.mul_assoc b (d * d) (w3 * (a * w2)),
    BPair.mul_assoc d d (w3 * (a * w2)),
    BPair.mul_left_comm w3 a w2, BPair.mul_comm w3 w2,
    BPair.mul_left_comm b d (d * (a * (w2 * w3))),
    BPair.mul_left_comm b d (a * (w2 * w3))]

/-- The spot's transfer collects at the same carrier. -/
private theorem shB (b d u w3 : BPair) :
    b * (d * d) * (u * d * w3) = b * (d * d) * w3 * (u * d) :=
  mulShuffleACB (b * (d * d)) (u * d) w3

/-- The collected carrier's square reads the two clearings' own. -/
private theorem shC (b d w3 : BPair) :
    b * (d * d) * w3 * w3 = d * d * (w3 * w3) * b := by
  rw [BPair.mul_assoc (b * (d * d)) w3 w3, BPair.mul_comm b (d * d),
    BPair.mul_assoc (d * d) b (w3 * w3),
    BPair.mul_left_comm (d * d) b (w3 * w3),
    BPair.mul_comm b (d * d * (w3 * w3))]

/-- The solved column against the transfer collects at the bond's
square. -/
private theorem shF (d w2 u w3 : BPair) :
    d * w2 * (u * d * w3) = u * (d * d * (w2 * w3)) := by
  rw [BPair.mul_assoc u d w3, BPair.mul_assoc d w2 (u * (d * w3)),
    BPair.mul_left_comm w2 u (d * w3),
    BPair.mul_left_comm d u (w2 * (d * w3)),
    BPair.mul_left_comm w2 d w3, BPair.mul_left_comm d d (w2 * w3),
    BPair.mul_assoc d d (w2 * w3)]

/-- The spot's second row collects at the bond's square. -/
private theorem shG (b d w2 w3 : BPair) :
    b * (d * d) * (b * w2 * w3) = b * b * (d * d * (w2 * w3)) := by
  rw [BPair.mul_assoc b w2 w3, BPair.mul_assoc b (d * d) (b * (w2 * w3)),
    BPair.mul_left_comm (d * d) b (w2 * w3),
    BPair.mul_assoc b b (d * d * (w2 * w3))]


/-- The spot's lower entry after the shallower chain's transfer is
the spot's own minor scaled at the chain's top. -/
private theorem spotLower (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    (wellDiag r qn qd en ed (c + 2)
        * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1))
      + (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
          * wellWalk r qn qd en ed (c + 1)).swap).oneValue
      (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 2)) := by
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_of_eq
        (BPair.mul_left_comm (wellDiag r qn qd en ed (c + 2))
          (wellWalk r qn qd en ed (c + 1))
          (wellWalk r qn qd en ed (c + 1))))
      (BPair.oneValue_of_eq (congrArg BPair.swap
        (BPair.mul_comm
          (wellBond r qd ed * wellBond r qd ed
            * wellWalk r qn qd en ed c)
          (wellWalk r qn qd en ed (c + 1)))))) ?_
  exact crossStep (wellWalk r qn qd en ed (c + 1))
    (wellDiag r qn qd en ed (c + 2) * wellWalk r qn qd en ed (c + 1))
    (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c)
    (wellWalk r qn qd en ed (c + 2)) (wellWalk_rec r qn qd en ed c)

/-- The step above the spot: the spot's order-two pivot against its
own witness reads the off block exchanged, the two walk recursions
the identity's engine. -/
private theorem spotCrossUp (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hD : ¬ (wellWalk r qn qd en ed (c + 1)).oneValue BPair.unit)
    (hT : ¬ (wellWalk r qn qd en ed (c + 3)).oneValue BPair.unit) :
    greenprod.oneValueQ
      (greenprod.mulQ (spotQ r qn qd en ed (c + 1))
        (spotR r qn qd en ed (c + 1)))
      (greenprod.ofM (elim.transposeM
        [[(wellBond r qd ed).swap, BPair.unit]])) := by
  have hZ := spotLower r qn qd en ed c
  refine oneQ21
    (a := elim.dotN
      [wellDiag r qn qd en ed (c + 3)
          * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)),
        (wellBond r qd ed).swap
          * (wellWalk r qn qd en ed (c + 1)
            * wellWalk r qn qd en ed (c + 1))]
      [(wellBond r qd ed).swap * wellWalk r qn qd en ed (c + 2)
          * wellWalk r qn qd en ed (c + 3),
        (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed (c + 1)
          * wellWalk r qn qd en ed (c + 3)).swap])
    (b := elim.dotN
      [(wellBond r qd ed).swap
          * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)),
        wellDiag r qn qd en ed (c + 2)
            * (wellWalk r qn qd en ed (c + 1)
              * wellWalk r qn qd en ed (c + 1))
          + (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
              * wellWalk r qn qd en ed (c + 1)).swap]
      [(wellBond r qd ed).swap * wellWalk r qn qd en ed (c + 2)
          * wellWalk r qn qd en ed (c + 3),
        (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed (c + 1)
          * wellWalk r qn qd en ed (c + 3)).swap])
    (a' := (wellBond r qd ed).swap) (b' := BPair.unit)
    (p := Pos.pow (margP (wellWalk r qn qd en ed (c + 1))) 2
      * Pos.pow (margP (wellWalk r qn qd en ed (c + 3))) 2)
    (q := Pos.one) ?_ ?_
  · refine BPair.oneValue_trans (BPair.ofPos_one_mul _) ?_
    refine BPair.oneValue_trans (dotN_pair _ _ _ _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_of_eq
          (shA (wellDiag r qn qd en ed (c + 3))
            (wellWalk r qn qd en ed (c + 1)) (wellBond r qd ed).swap
            (wellWalk r qn qd en ed (c + 2))
            (wellWalk r qn qd en ed (c + 3))))
        (BPair.oneValue_of_eq (congrArg BPair.swap
          (shB (wellBond r qd ed).swap (wellWalk r qn qd en ed (c + 1))
            (wellBond r qd ed * wellBond r qd ed)
            (wellWalk r qn qd en ed (c + 3)))))) ?_
    refine BPair.oneValue_trans
      (crossStep
        ((wellBond r qd ed).swap
            * (wellWalk r qn qd en ed (c + 1)
              * wellWalk r qn qd en ed (c + 1))
          * wellWalk r qn qd en ed (c + 3))
        (wellDiag r qn qd en ed (c + 3) * wellWalk r qn qd en ed (c + 2))
        (wellBond r qd ed * wellBond r qd ed
          * wellWalk r qn qd en ed (c + 1))
        (wellWalk r qn qd en ed (c + 3))
        (wellWalk_rec r qn qd en ed (c + 1))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (shC (wellBond r qd ed).swap (wellWalk r qn qd en ed (c + 1))
          (wellWalk r qn qd en ed (c + 3)))) ?_
    exact BPair.oneValue_symm
      (BPair.mul_congr (margPair r qn qd en ed (c + 1) (c + 3) hD hT)
        (BPair.oneValue_refl _))
  · have hin : ((wellDiag r qn qd en ed (c + 2)
            * (wellWalk r qn qd en ed (c + 1)
              * wellWalk r qn qd en ed (c + 1))
          + (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
              * wellWalk r qn qd en ed (c + 1)).swap)
        * (wellBond r qd ed * wellBond r qd ed
          * wellWalk r qn qd en ed (c + 1)
          * wellWalk r qn qd en ed (c + 3))).oneValue
        ((wellBond r qd ed).swap
            * (wellWalk r qn qd en ed (c + 1)
              * wellWalk r qn qd en ed (c + 1))
          * ((wellBond r qd ed).swap * wellWalk r qn qd en ed (c + 2)
            * wellWalk r qn qd en ed (c + 3))) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr hZ (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (shF (wellWalk r qn qd en ed (c + 1))
            (wellWalk r qn qd en ed (c + 2))
            (wellBond r qd ed * wellBond r qd ed)
            (wellWalk r qn qd en ed (c + 3)))) ?_
      refine BPair.oneValue_symm (BPair.oneValue_of_eq ?_)
      rw [shG (wellBond r qd ed).swap (wellWalk r qn qd en ed (c + 1))
          (wellWalk r qn qd en ed (c + 2)) (wellWalk r qn qd en ed (c + 3)),
        BPair.swap_sq (wellBond r qd ed)]
    refine BPair.oneValue_trans (BPair.ofPos_one_mul _) ?_
    refine BPair.oneValue_trans (dotN_pair _ _ _ _) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
    exact BPair.oneValue_trans (BPair.swap_add_null hin)
      (BPair.oneValue_symm (BPair.mul_unit _))


/-- The clearing's square collects the depth's carrier. -/
private theorem shH (w a : BPair) : w * w * (a * w * w) = w * w * (w * w) * a := by
  rw [BPair.mul_assoc a w w, sqShuffle (w * w) a]

/-- The join above the spot: the depth beyond the spot's pivot
against the bond-weighted witness reads that depth's diagonal. -/
private theorem spotJoinUp (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hW : ¬ (wellWalk r qn qd en ed (c + 2)).oneValue BPair.unit) :
    greenprod.oneValueQ
      (greenprod.addQ (pivotQ r qn qd en ed (c + 3))
        (greenprod.mulQ
          (greenprod.ofM [[(wellBond r qd ed).swap, BPair.unit]])
          (spotR r qn qd en ed c)))
      (greenprod.ofM [[wellDiag r qn qd en ed (c + 3)]]) := by
  have hdot : (elim.dotN [(wellBond r qd ed).swap, BPair.unit]
        [(wellBond r qd ed).swap * wellWalk r qn qd en ed (c + 1)
          * wellWalk r qn qd en ed (c + 2),
         (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
           * wellWalk r qn qd en ed (c + 2)).swap]).oneValue
      (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed (c + 1)
        * wellWalk r qn qd en ed (c + 2)) := by
    refine BPair.oneValue_trans (dotN_pair _ _ _ _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.unit_mul _)) ?_
    refine BPair.oneValue_trans (BPair.add_unit _) ?_
    refine BPair.oneValue_of_eq ?_
    rw [bondShuffle (wellBond r qd ed).swap (wellWalk r qn qd en ed (c + 1))
        (wellWalk r qn qd en ed (c + 2)),
      BPair.swap_sq (wellBond r qd ed)]
  refine oneQ11
    (a := (wellWalk r qn qd en ed (c + 3)
          * wellWalk r qn qd en ed (c + 2)).scale
        (Pos.one * Pos.pow (margP (wellWalk r qn qd en ed (c + 2))) 2)
      + (elim.dotN [(wellBond r qd ed).swap, BPair.unit]
          [(wellBond r qd ed).swap * wellWalk r qn qd en ed (c + 1)
            * wellWalk r qn qd en ed (c + 2),
           (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
             * wellWalk r qn qd en ed (c + 2)).swap]).scale
        (Pos.pow (margP (wellWalk r qn qd en ed (c + 2))) 2))
    (b := wellDiag r qn qd en ed (c + 3))
    (p := Pos.pow (margP (wellWalk r qn qd en ed (c + 2))) 2
      * (Pos.one * Pos.pow (margP (wellWalk r qn qd en ed (c + 2))) 2))
    (q := Pos.one) ?_
  rw [ground.one_mul (Pos.pow (margP (wellWalk r qn qd en ed (c + 2))) 2)]
  refine BPair.oneValue_trans (BPair.ofPos_one_mul _) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_symm (BPair.ofPos_scale _ _))
      (BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.ofPos_scale _ _))
        (BPair.mul_congr (BPair.oneValue_refl _) hdot))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.left_distrib
        (BPair.ofPos (Pos.pow (margP (wellWalk r qn qd en ed (c + 2))) 2))
        (wellWalk r qn qd en ed (c + 3) * wellWalk r qn qd en ed (c + 2))
        (wellBond r qd ed * wellBond r qd ed
          * wellWalk r qn qd en ed (c + 1)
          * wellWalk r qn qd en ed (c + 2))).symm) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.right_distrib (wellWalk r qn qd en ed (c + 3))
            (wellBond r qd ed * wellBond r qd ed
              * wellWalk r qn qd en ed (c + 1))
            (wellWalk r qn qd en ed (c + 2))).symm)
        (BPair.mul_congr (wellWalk_rec r qn qd en ed (c + 1))
          (BPair.oneValue_refl _)))) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (margP_sq _ hW) (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (shH (wellWalk r qn qd en ed (c + 2))
        (wellDiag r qn qd en ed (c + 3)))) ?_
  exact BPair.oneValue_symm
    (BPair.mul_congr (margPair r qn qd en ed (c + 2) (c + 2) hW hW)
      (BPair.oneValue_refl _))


/-- The boundary spot's row collects at its own carrier. -/
private theorem shI (a b w1 w2 : BPair) : a * (b * w1 * w2) = b * w2 * (a * w1) := by
  rw [BPair.mul_assoc b w1 w2, BPair.mul_left_comm a b (w1 * w2),
    BPair.mul_assoc b w2 (a * w1), BPair.mul_left_comm w2 a w1,
    BPair.mul_comm w2 w1]

/-- The boundary spot's transfer collects at the same carrier. -/
private theorem shJ (b u w0 w2 : BPair) :
    b * (u * w0 * w2) = b * w2 * (u * w0) :=
  mulShuffleACB b (u * w0) w2

/-- The carrier's square withdraws its factor. -/
private theorem shK (b w : BPair) : b * w * w = w * w * b := by
  rw [BPair.mul_assoc b w w, BPair.mul_comm b (w * w)]

/-- One factor passes to the head. -/
private theorem shL (a u w : BPair) : a * (u * w) = u * a * w := by
  rw [BPair.mul_left_comm a u w, ← BPair.mul_assoc u a w]

/-- The step above the boundary spot: the seed slab against its own
witness reads the off block exchanged. -/
private theorem spotCrossUpZero (r qn qd : Nat) (en ed : Pos)
    (hT : ¬ (wellWalk r qn qd en ed 2).oneValue BPair.unit) :
    greenprod.oneValueQ
      (greenprod.mulQ (spotQ r qn qd en ed 0) (spotR r qn qd en ed 0))
      (greenprod.ofM (elim.transposeM
        [[(wellBond r qd ed).swap, BPair.unit]])) := by
  refine oneQ21
    (a := elim.dotN
      [wellDiag r qn qd en ed 2, (wellBond r qd ed).swap]
      [(wellBond r qd ed).swap * wellWalk r qn qd en ed 1
          * wellWalk r qn qd en ed 2,
        (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed 0
          * wellWalk r qn qd en ed 2).swap])
    (b := elim.dotN
      [(wellBond r qd ed).swap, wellDiag r qn qd en ed 1]
      [(wellBond r qd ed).swap * wellWalk r qn qd en ed 1
          * wellWalk r qn qd en ed 2,
        (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed 0
          * wellWalk r qn qd en ed 2).swap])
    (a' := (wellBond r qd ed).swap) (b' := BPair.unit)
    (p := Pos.one * Pos.pow (margP (wellWalk r qn qd en ed 2)) 2)
    (q := Pos.one) ?_ ?_
  · rw [ground.one_mul (Pos.pow (margP (wellWalk r qn qd en ed 2)) 2)]
    refine BPair.oneValue_trans (BPair.ofPos_one_mul _) ?_
    refine BPair.oneValue_trans (dotN_pair _ _ _ _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_of_eq
          (shI (wellDiag r qn qd en ed 2) (wellBond r qd ed).swap
            (wellWalk r qn qd en ed 1) (wellWalk r qn qd en ed 2)))
        (BPair.oneValue_of_eq (congrArg BPair.swap
          (shJ (wellBond r qd ed).swap
            (wellBond r qd ed * wellBond r qd ed)
            (wellWalk r qn qd en ed 0) (wellWalk r qn qd en ed 2))))) ?_
    refine BPair.oneValue_trans
      (crossStep ((wellBond r qd ed).swap * wellWalk r qn qd en ed 2)
        (wellDiag r qn qd en ed 2 * wellWalk r qn qd en ed 1)
        (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed 0)
        (wellWalk r qn qd en ed 2) (wellWalk_rec r qn qd en ed 0)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (shK (wellBond r qd ed).swap (wellWalk r qn qd en ed 2))) ?_
    exact BPair.oneValue_symm
      (BPair.mul_congr (margP_sq _ hT) (BPair.oneValue_refl _))
  · have hin : (wellDiag r qn qd en ed 1
        * (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed 0
          * wellWalk r qn qd en ed 2)).oneValue
        ((wellBond r qd ed).swap
          * ((wellBond r qd ed).swap * wellWalk r qn qd en ed 1
            * wellWalk r qn qd en ed 2)) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.mul_congr
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_of_eq (wellWalk_zero r qn qd en ed)))
            (BPair.oneValue_refl _))) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.mul_congr
            (BPair.mul_one_read (wellBond r qd ed * wellBond r qd ed))
            (BPair.oneValue_refl _))) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (shL (wellDiag r qn qd en ed 1)
            (wellBond r qd ed * wellBond r qd ed)
            (wellWalk r qn qd en ed 2))) ?_
      refine BPair.oneValue_symm (BPair.oneValue_of_eq ?_)
      rw [bondShuffle (wellBond r qd ed).swap (wellWalk r qn qd en ed 1)
          (wellWalk r qn qd en ed 2),
        BPair.swap_sq (wellBond r qd ed), wellWalk_one r qn qd en ed]
    rw [ground.one_mul (Pos.pow (margP (wellWalk r qn qd en ed 2)) 2)]
    refine BPair.oneValue_trans (BPair.ofPos_one_mul _) ?_
    refine BPair.oneValue_trans (dotN_pair _ _ _ _) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
    exact BPair.oneValue_trans (BPair.swap_add_null hin)
      (BPair.oneValue_symm (BPair.mul_unit _))


/-- The order-two minor at a symmetric datum. -/
private theorem minorTwo (a b c : BPair) :
    (elim.minor [[a, b], [b, c]]).oneValue (a * c + (b * b).swap) := by
  show ((((a * c).norm)
      + ((((b * b).norm).swap + BPair.unit).norm)).norm).oneValue
    (a * c + (b * b).swap)
  refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.norm_oneValue _) (BPair.norm_oneValue _)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr (ground.swap_congr (BPair.norm_oneValue _))
        (BPair.oneValue_refl BPair.unit))) ?_
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _)

/-- The recursion's step at the bare carrier, the scaled step's
read at the count one. -/
private theorem crossStep0 (A B S : BPair) (h : (S + B).oneValue A) :
    (A + B.swap).oneValue S :=
  BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_symm (BPair.ofNat_one_mul A))
      (ground.swap_congr (BPair.oneValue_symm (BPair.ofNat_one_mul B))))
    (BPair.oneValue_trans (crossStep (BPair.ofNat 1) A B S h)
      (BPair.ofNat_one_mul S))

/-- The spot's determinant collects at the chain's cubed top. -/
private theorem shM (a d w : BPair) :
    a * (d * d) * (d * w) = d * d * d * (a * w) := by
  rw [BPair.mul_assoc a (d * d) (d * w), BPair.mul_assoc d d (d * w),
    BPair.mul_left_comm a d (d * (d * w)),
    BPair.mul_left_comm a d (d * w),
    BPair.mul_left_comm a d w,
    BPair.mul_assoc (d * d) d (a * w), BPair.mul_assoc d d (d * (a * w))]

/-- The spot's off square collects at the same carrier. -/
private theorem shN (b d : BPair) :
    b * (d * d) * (b * (d * d)) = d * d * d * (b * b * d) := by
  rw [BPair.mul_mul_mul_comm b (d * d) b (d * d),
    BPair.mul_mul_mul_comm (d * d) d (b * b) d,
    BPair.mul_assoc (d * d) (b * b) (d * d),
    BPair.mul_left_comm (d * d) (b * b) (d * d)]

/-- The spot's own minor: the chain's top cubed against the depth
beyond the spot. -/
private theorem minorSpot (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    (elim.minor (spotQ r qn qd en ed (c + 1)).1).oneValue
      (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)
        * wellWalk r qn qd en ed (c + 1)
        * wellWalk r qn qd en ed (c + 3)) := by
  have hoff : (wellBond r qd ed).swap
        * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1))
        * ((wellBond r qd ed).swap
          * (wellWalk r qn qd en ed (c + 1)
            * wellWalk r qn qd en ed (c + 1)))
      = wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)
          * wellWalk r qn qd en ed (c + 1)
        * (wellBond r qd ed * wellBond r qd ed
          * wellWalk r qn qd en ed (c + 1)) := by
    rw [shN (wellBond r qd ed).swap (wellWalk r qn qd en ed (c + 1)),
      BPair.swap_sq (wellBond r qd ed)]
  refine BPair.oneValue_trans (minorTwo _ _ _) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) (spotLower r qn qd en ed c))
        (BPair.oneValue_of_eq
          (shM (wellDiag r qn qd en ed (c + 3))
            (wellWalk r qn qd en ed (c + 1))
            (wellWalk r qn qd en ed (c + 2)))))
      (BPair.oneValue_of_eq (congrArg BPair.swap hoff))) ?_
  · exact crossStep
      (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)
        * wellWalk r qn qd en ed (c + 1))
      (wellDiag r qn qd en ed (c + 3) * wellWalk r qn qd en ed (c + 2))
      (wellBond r qd ed * wellBond r qd ed
        * wellWalk r qn qd en ed (c + 1))
      (wellWalk r qn qd en ed (c + 3)) (wellWalk_rec r qn qd en ed (c + 1))

/-- The boundary spot's own minor is the depth beyond it. -/
private theorem minorSpotZero (r qn qd : Nat) (en ed : Pos) :
    (elim.minor (spotQ r qn qd en ed 0).1).oneValue
      (wellWalk r qn qd en ed 2) := by
  have hb : ((wellBond r qd ed).swap * (wellBond r qd ed).swap).oneValue
      (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed 0) := by
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_of_eq (wellWalk_zero r qn qd en ed))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_one_read (wellBond r qd ed * wellBond r qd ed)) ?_
    exact BPair.oneValue_symm
      (BPair.oneValue_of_eq (BPair.swap_sq (wellBond r qd ed)))
  refine BPair.oneValue_trans (minorTwo _ _ _) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl (wellDiag r qn qd en ed 2))
        (BPair.oneValue_of_eq (wellWalk_one r qn qd en ed).symm))
      (ground.swap_congr hb)) ?_
  exact crossStep0
    (wellDiag r qn qd en ed 2 * wellWalk r qn qd en ed 1)
    (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed 0)
    (wellWalk r qn qd en ed 2) (wellWalk_rec r qn qd en ed 0)

/-- The order-two identity congruence. -/
private def id2 : elim.SqMat 2 := ⟨inertia.idMat 2, by decide +kernel⟩

private theorem cc2 : inertia.clearedCongr id2 id2 := by decide +kernel

/-- The order-two split at a symmetric datum: the identity
congruence with the datum the single nonsingular block. -/
private def split2 (a b c : BPair) : inertia.Split 2 :=
  ⟨id2, id2, [inertia.SBlock.two a b c], 0, rfl⟩

/-- A two-by-two datum at an occupied determinant splits at its own
order-two certificate. -/
private theorem splitRead_two (a b c : BPair)
    (hd : ¬ (inertia.SBlock.two a b c).det.oneValue BPair.unit) :
    inertia.splitRead [[a, b], [b, c]] (split2 a b c) := by
  have hSr : elim.rowsLen 2 [[a, b], [b, c]] := ⟨rfl, rfl, trivial⟩
  have hy1 : elim.matOneValue [[a, b], [b, c]]
      (inertia.blockMat [inertia.SBlock.two a b c] 0) :=
    ⟨⟨BPair.oneValue_refl a, BPair.oneValue_refl b, trivial⟩,
     ⟨BPair.oneValue_refl b, BPair.oneValue_refl c, trivial⟩, trivial⟩
  refine ⟨rfl, cc2, ?_, ?_⟩
  · show elim.matOneValue
      (elim.matMul (elim.transposeM (inertia.idMat 2))
        (elim.matMul [[a, b], [b, c]] (inertia.idMat 2)))
      (inertia.blockMat [inertia.SBlock.two a b c] 0)
    rw [inertia.transposeM_idMat 2]
    refine elim.matOne_trans ?_ hy1
    refine elim.matOne_trans ?_
      (inertia.idMat_matMul (k := 2) 2 [[a, b], [b, c]] hSr rfl (by decide +kernel))
    exact elim.matMul_congrR (n := 2) (k := 2) (inertia.idMat 2)
      (elim.matMul [[a, b], [b, c]] (inertia.idMat 2)) [[a, b], [b, c]]
      (elim.rowsLen_cast
        (by rw [inertia.transposeM_idMat 2, inertia.idMat_len 2])
        (elim.rowsLen_matMul [[a, b], [b, c]] (inertia.idMat 2)))
      hSr ((elim.length_matMul [[a, b], [b, c]] (inertia.idMat 2)).trans rfl)
      rfl (by decide +kernel)
      (inertia.matMul_idR (k := 2) 2 [[a, b], [b, c]] hSr rfl (by decide +kernel)
        (by decide +kernel))
  · show (!(decide ((inertia.SBlock.two a b c).det.oneValue BPair.unit))
      && true) = true
    rw [decide_eq_false hd]
    rfl

/-- An order-two split at a lower-side determinant counts one. -/
private theorem revSplit2_lt {a b c : BPair}
    (h : (inertia.SBlock.two a b c).det < BPair.unit) :
    inertia.revAt (split2 a b c) = 1 := by
  rw [show inertia.revAt (split2 a b c) = (inertia.SBlock.two a b c).rev
    from revAt_single id2 id2 _ rfl, inertia.rev_two_detLt h]


/-- A datum reading an occupied value is itself occupied. -/
private theorem offOfOv {x y : BPair} (h : x.oneValue y)
    (hy : ¬ y.oneValue BPair.unit) : ¬ x.oneValue BPair.unit :=
  fun hx => hy (BPair.oneValue_trans (BPair.oneValue_symm h) hx)

/-- The spot's pivot is nonsingular at the chain's occupied top and
the occupied depth beyond it. -/
private theorem spotMinorOff (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hA : ∀ k, k ≤ c → ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit)
    (h2 : ¬ (wellWalk r qn qd en ed (c + 2)).oneValue BPair.unit) :
    ¬ (elim.minor (spotQ r qn qd en ed c).1).oneValue BPair.unit := by
  cases c with
  | zero => exact offOfOv (minorSpotZero r qn qd en ed) h2
  | succ c' =>
    exact offOfOv (minorSpot r qn qd en ed c')
      (ground.mulOffUnit
        (ground.mulOffUnit
          (ground.mulOffUnit (hA (c' + 1) (Nat.le_refl (c' + 1)))
            (hA (c' + 1) (Nat.le_refl (c' + 1))))
          (hA (c' + 1) (Nat.le_refl (c' + 1))))
        h2)

/-- The step above the spot at either arm of the spot's pivot. -/
private theorem spotCrossAt (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hA : ∀ k, k ≤ c → ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit)
    (h2 : ¬ (wellWalk r qn qd en ed (c + 2)).oneValue BPair.unit) :
    greenprod.oneValueQ
      (greenprod.mulQ (spotQ r qn qd en ed c) (spotR r qn qd en ed c))
      (greenprod.ofM (elim.transposeM
        [[(wellBond r qd ed).swap, BPair.unit]])) := by
  cases c with
  | zero => exact spotCrossUpZero r qn qd en ed h2
  | succ c' =>
    exact spotCrossUp r qn qd en ed c'
      (hA (c' + 1) (Nat.le_refl (c' + 1))) h2

/-- The mixed head's recursion at the spot and below it. -/
private theorem mixTailBase (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hA : ∀ k, k ≤ c → ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit) :
    greenprod.tailSteps (mDiag r qn qd en ed c 0) (mOff r qd ed c 0)
      (mX r qn qd en ed c 0) (mR r qn qd en ed c 0) := by
  cases c with
  | zero =>
    show greenprod.oneValueQ (spotQ r qn qd en ed 0)
      (greenprod.ofM (spotMat r qn qd en ed 0))
    exact elim.matOne_refl _
  | succ c' =>
    show greenprod.tailSteps
      (spotMat r qn qd en ed (c' + 1) :: wDiagL r qn qd en ed (c' + 1))
      ([[BPair.unit], [(wellBond r qd ed).swap]] :: wOffL r qd ed (c' + 1))
      (spotQ r qn qd en ed (c' + 1) :: wXL r qn qd en ed (c' + 1))
      (spotWit r qn qd en ed c' :: wRL r qn qd en ed (c' + 1))
    rw [wDiagL_cons r qn qd en ed c', wXL_cons r qn qd en ed c']
    refine ⟨⟨?_,
      spotCross r qn qd en ed c' (hA c' (Nat.le_succ c'))
        (hA (c' + 1) (Nat.le_refl (c' + 1))),
      spotJoin r qn qd en ed c' (hA (c' + 1) (Nat.le_refl (c' + 1)))⟩, ?_⟩
    · show ¬ (wellWalk r qn qd en ed (c' + 1)
        * wellWalk r qn qd en ed c').oneValue BPair.unit
      exact ground.mulOffUnit (hA (c' + 1) (Nat.le_refl (c' + 1)))
        (hA c' (Nat.le_succ c'))
    · rw [← wDiagL_cons r qn qd en ed c', ← wXL_cons r qn qd en ed c']
      exact wellTail r qn qd en ed c'
        (fun k hk => hA k (Nat.le_trans hk (Nat.le_succ c')))

/-- The mixed head's tail recursion at every slab: the order-one
steps off the spot, the spot's own two steps, and the shallower
chain's landed recursion. -/
private theorem mixTail (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hA : ∀ k, k ≤ c → ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit) :
    ∀ t : Nat,
      (∀ k, c + 2 ≤ k → k ≤ c + 2 + t →
        ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit) →
      greenprod.tailSteps (mDiag r qn qd en ed c t) (mOff r qd ed c t)
        (mX r qn qd en ed c t) (mR r qn qd en ed c t) := by
  intro t
  induction t with
  | zero => exact fun _ => mixTailBase r qn qd en ed c hA
  | succ t ih =>
    intro hB
    have hspot : ¬ (wellWalk r qn qd en ed (c + 2)).oneValue BPair.unit :=
      hB (c + 2) (Nat.le_refl (c + 2)) (Nat.le_add_right (c + 2) (t + 1))
    match t with
    | 0 =>
      exact ⟨⟨spotMinorOff r qn qd en ed c hA hspot,
        spotCrossAt r qn qd en ed c hA hspot,
        spotJoinUp r qn qd en ed c hspot⟩,
        ih (fun k hk hk2 => hB k hk (Nat.le_trans hk2 (Nat.le_succ _)))⟩
    | t' + 1 =>
      have h0 : ¬ (wellWalk r qn qd en ed (c + 2 + t')).oneValue BPair.unit :=
        hB (c + 2 + t') (Nat.le_add_right (c + 2) t')
          (Nat.le_trans (Nat.le_succ (c + 2 + t')) (Nat.le_succ _))
      have h1 : ¬ (wellWalk r qn qd en ed (c + 2 + t' + 1)).oneValue
          BPair.unit :=
        hB (c + 2 + t' + 1)
          (Nat.le_trans (Nat.le_add_right (c + 2) t') (Nat.le_succ _))
          (Nat.le_succ (c + 2 + t' + 1))
      refine ⟨⟨?_, pivotCross r qn qd en ed (c + 2 + t') h0 h1,
        pivotJoin r qn qd en ed (c + 2 + t') h1⟩,
        ih (fun k hk hk2 => hB k hk (Nat.le_trans hk2 (Nat.le_succ _)))⟩
      show ¬ (wellWalk r qn qd en ed (c + 2 + t' + 1)
        * wellWalk r qn qd en ed (c + 2 + t')).oneValue BPair.unit
      exact ground.mulOffUnit h1 h0


/-- The order-two block's determinant is its datum's own minor. -/
private theorem detTwo_ov (a b c : BPair) :
    ((inertia.SBlock.two a b c).det).oneValue
      (elim.minor [[a, b], [b, c]]) :=
  BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_symm (minorTwo a b c))

/-- The spot's own order-two split. -/
private def spotSplit (r qn qd : Nat) (en ed : Pos) : Nat → inertia.Split 2
  | 0 =>
    split2 (wellDiag r qn qd en ed 2) (wellBond r qd ed).swap
      (wellDiag r qn qd en ed 1)
  | c + 1 =>
    split2
      (wellDiag r qn qd en ed (c + 1 + 2)
        * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)))
      ((wellBond r qd ed).swap
        * (wellWalk r qn qd en ed (c + 1) * wellWalk r qn qd en ed (c + 1)))
      (wellDiag r qn qd en ed (c + 1 + 1)
          * (wellWalk r qn qd en ed (c + 1)
            * wellWalk r qn qd en ed (c + 1))
        + (wellBond r qd ed * wellBond r qd ed * wellWalk r qn qd en ed c
            * wellWalk r qn qd en ed (c + 1)).swap)

/-- The spot's pivot reads its own order-two certificate. -/
private theorem spotSplitRead (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hd : ¬ (elim.minor (spotQ r qn qd en ed c).1).oneValue BPair.unit) :
    inertia.splitRead (spotQ r qn qd en ed c).1
      (spotSplit r qn qd en ed c) := by
  cases c with
  | zero => exact splitRead_two _ _ _ (offOfOv (detTwo_ov _ _ _) hd)
  | succ c' => exact splitRead_two _ _ _ (offOfOv (detTwo_ov _ _ _) hd)

/-- The spot's determinant sits on the lower side: the chain's
occupied top against the depth beyond the spot. -/
private theorem spotDetLt (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hpos : ∀ k, k ≤ c → BPair.unit < wellWalk r qn qd en ed k)
    (hneg : wellWalk r qn qd en ed (c + 2) < BPair.unit) :
    elim.minor (spotQ r qn qd en ed c).1 < BPair.unit := by
  cases c with
  | zero =>
    exact BPair.lt_congr
      (BPair.oneValue_symm (minorSpotZero r qn qd en ed))
      (BPair.oneValue_refl BPair.unit) hneg
  | succ c' =>
    have h3 : BPair.unit < wellWalk r qn qd en ed (c' + 1)
        * wellWalk r qn qd en ed (c' + 1)
        * wellWalk r qn qd en ed (c' + 1) :=
      ground.unitLtMul
        (ground.unitLtMul (hpos (c' + 1) (Nat.le_refl (c' + 1)))
          (hpos (c' + 1) (Nat.le_refl (c' + 1))))
        (hpos (c' + 1) (Nat.le_refl (c' + 1)))
    refine BPair.lt_congr
      (BPair.oneValue_symm (minorSpot r qn qd en ed c'))
      (BPair.oneValue_refl BPair.unit) ?_
    exact BPair.lt_congr
      (BPair.oneValue_of_eq
        (BPair.mul_comm (wellWalk r qn qd en ed (c' + 3))
          (wellWalk r qn qd en ed (c' + 1) * wellWalk r qn qd en ed (c' + 1)
            * wellWalk r qn qd en ed (c' + 1))))
      (BPair.oneValue_refl BPair.unit) (mulNegPos hneg h3)

/-- The spot's split counts one. -/
private theorem spotRev (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hlt : elim.minor (spotQ r qn qd en ed c).1 < BPair.unit) :
    inertia.revAt (spotSplit r qn qd en ed c) = 1 := by
  cases c with
  | zero =>
    exact revSplit2_lt
      (BPair.lt_congr (BPair.oneValue_symm (detTwo_ov _ _ _))
        (BPair.oneValue_refl BPair.unit) hlt)
  | succ c' =>
    exact revSplit2_lt
      (BPair.lt_congr (BPair.oneValue_symm (detTwo_ov _ _ _))
        (BPair.oneValue_refl BPair.unit) hlt)

/-- The mixed pivots' splits, the spot's order-two certificate among
the order-one ones. -/
private def mSp (r qn qd : Nat) (en ed : Pos) (c : Nat) :
    Nat → List ((k : Nat) × inertia.Split k)
  | 0 => ⟨2, spotSplit r qn qd en ed c⟩ :: wSpL r qn qd en ed c
  | t + 1 =>
    ⟨1, split1 (wellWalk r qn qd en ed (c + 2 + t + 1)
      * wellWalk r qn qd en ed (c + 2 + t))⟩ :: mSp r qn qd en ed c t

/-- Every mixed pivot's split reads its own datum. -/
private theorem mixRevList (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hA : ∀ k, k ≤ c → ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit)
    (hsp : ¬ (elim.minor (spotQ r qn qd en ed c).1).oneValue BPair.unit) :
    ∀ t : Nat,
      (∀ k, c + 2 ≤ k → k ≤ c + 2 + t →
        ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit) →
      greenprod.revListRead (mX r qn qd en ed c t)
        (mSp r qn qd en ed c t) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨spotSplitRead r qn qd en ed c hsp, wellRevList r qn qd en ed c hA⟩
  | succ t ih =>
    intro hB
    refine ⟨splitRead_one _ _ ?_ (BPair.oneValue_refl _),
      ih (fun k hk hk2 => hB k hk (Nat.le_trans hk2 (Nat.le_succ _)))⟩
    exact ground.mulOffUnit
      (hB (c + 2 + t + 1)
        (Nat.le_trans (Nat.le_add_right (c + 2) t) (Nat.le_succ _))
        (Nat.le_refl (c + 2 + t + 1)))
      (hB (c + 2 + t) (Nat.le_add_right (c + 2) t)
        (Nat.le_succ (c + 2 + t)))

/-- The mixed pivots' reversal fold is one: the spot's own count
with every other slab's signs agreeing. -/
private theorem mixRevFold (r qn qd : Nat) (en ed : Pos) (c : Nat)
    (hlo : ∀ k, k < c → BPair.unit < wellWalk r qn qd en ed (k + 1))
    (hrev : inertia.revAt (spotSplit r qn qd en ed c) = 1) :
    ∀ t : Nat,
      (∀ k, c + 2 ≤ k → k ≤ c + 2 + t →
        wellWalk r qn qd en ed k < BPair.unit) →
      ∀ acc : Nat, (mSp r qn qd en ed c t).foldl
        (fun m s => m + inertia.revAt s.2) acc = acc + 1 := by
  intro t
  induction t with
  | zero =>
    intro _ acc
    show (wSpL r qn qd en ed c).foldl (fun m s => m + inertia.revAt s.2)
      (acc + inertia.revAt (spotSplit r qn qd en ed c)) = acc + 1
    rw [hrev]
    exact wellRevFoldZero r qn qd en ed c hlo (acc + 1)
  | succ t ih =>
    intro hB acc
    show (mSp r qn qd en ed c t).foldl (fun m s => m + inertia.revAt s.2)
      (acc + inertia.revAt (split1 (wellWalk r qn qd en ed (c + 2 + t + 1)
        * wellWalk r qn qd en ed (c + 2 + t)))) = acc + 1
    rw [revSplit1_le (ground.leB_of_lt (mulNegNeg
        (hB (c + 2 + t + 1)
          (Nat.le_trans (Nat.le_add_right (c + 2) t) (Nat.le_succ _))
          (Nat.le_refl (c + 2 + t + 1)))
        (hB (c + 2 + t) (Nat.le_add_right (c + 2) t)
          (Nat.le_succ (c + 2 + t))))),
      Nat.add_zero]
    exact ih (fun k hk hk2 => hB k hk (Nat.le_trans hk2 (Nat.le_succ _))) acc

/-- The degenerate arm at the spliced order: the mixed slab list's
count is one at every split of the head. -/
private theorem certMixedAt (r qn qd : Nat) (en ed : Pos) (c t : Nat)
    (hlo : ∀ k, k < c → BPair.unit < wellWalk r qn qd en ed (k + 1))
    (hB : ∀ k, c + 2 ≤ k → k ≤ c + 2 + t →
      wellWalk r qn qd en ed k < BPair.unit)
    (sp : inertia.Split (c + 2 + t))
    (hsp : inertia.splitRead (wellMat r qn qd en ed (c + 2 + t)) sp) :
    inertia.revAt sp = 1 := by
  have hpos := walkPos r qn qd en ed c hlo
  have hA : ∀ k, k ≤ c →
      ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit :=
    fun k hk => ground.offOfUnitLt (hpos k hk)
  have hBoff : ∀ k, c + 2 ≤ k → k ≤ c + 2 + t →
      ¬ (wellWalk r qn qd en ed k).oneValue BPair.unit :=
    fun k h1 h2 => ground.offOfLtUnit (hB k h1 h2)
  have hspot : wellWalk r qn qd en ed (c + 2) < BPair.unit :=
    hB (c + 2) (Nat.le_refl (c + 2)) (Nat.le_add_right (c + 2) t)
  have hmin : ¬ (elim.minor (spotQ r qn qd en ed c).1).oneValue BPair.unit :=
    spotMinorOff r qn qd en ed c hA (ground.offOfLtUnit hspot)
  have hsp' : inertia.splitRead
      (greenprod.assemble (mDiag r qn qd en ed c t) (mOff r qd ed c t)) sp :=
    inertia.splitRead_congr _ _ (mixSq r qn qd en ed c t)
      (mixMat r qn qd en ed c t) sp hsp
  rw [greenprod.countSplit (mDiag r qn qd en ed c t) (mOff r qd ed c t)
    (mX r qn qd en ed c t) (mR r qn qd en ed c t) (mNs c t)
    (mSp r qn qd en ed c t) sp
    ⟨mixSlab r qn qd en ed c t, mixQShape r qn qd en ed c t,
      mixWShape r qn qd en ed c t, mixTail r qn qd en ed c hA t hBoff⟩
    (mixRevList r qn qd en ed c hA hmin t hBoff) hsp']
  show (mSp r qn qd en ed c t).foldl (fun m s => m + inertia.revAt s.2) 0 = 1
  exact mixRevFold r qn qd en ed c hlo
    (spotRev r qn qd en ed c (spotDetLt r qn qd en ed c hpos hspot)) t hB 0

/-- The one-spot arm: minors positive to the spot and on the
swapped side strictly beyond it read the count one at every split,
the spot's own minor unread — a two-by-two slab pivot at a
lower-side determinant, the recursion pricing the spot's minor
product through its neighbors. -/
theorem certRevOneMixed : ∀ (r qn qd : Nat) (en ed : Pos) (n c : Nat),
    c + 2 ≤ n →
    (∀ k, k < c → BPair.unit < wellWalk r qn qd en ed (k + 1)) →
    (∀ k, c + 1 ≤ k → k < n →
      wellWalk r qn qd en ed (k + 1) < BPair.unit) →
    ∀ sp : inertia.Split n,
      inertia.splitRead (wellMat r qn qd en ed n) sp →
      inertia.revAt sp = 1 := by
  intro r qn qd en ed n c hcn hlo hhi
  have hn : c + 2 + (n - (c + 2)) = n := ground.natAddSubCancel hcn
  have hneg := walkNeg r qn qd en ed n (c + 1) hhi
  have hB : ∀ k, c + 2 ≤ k → k ≤ c + 2 + (n - (c + 2)) →
      wellWalk r qn qd en ed k < BPair.unit := by
    intro k h1 h2
    rw [hn] at h2
    exact hneg k h1 h2
  rw [← hn]
  intro sp hsp
  exact certMixedAt r qn qd en ed c (n - (c + 2)) hlo hB sp hsp

/-- The certificate's count read at a stated crossing: minors
positive through the crossing depth and on the swapped side beyond
it read the reversal count one at every split of the head's datum,
the count split over the depth pivots — the interior crossings the
one-spot arm's own read at the withdrawn spot minor, the boundary
crossing the walk fold's. -/
theorem certRevOne : ∀ (r qn qd : Nat) (en ed : Pos) (n c : Nat),
    c < n →
    (∀ k, k < c → BPair.unit < wellWalk r qn qd en ed (k + 1)) →
    (∀ k, c ≤ k → k < n → wellWalk r qn qd en ed (k + 1) < BPair.unit) →
    ∀ sp : inertia.Split n,
      inertia.splitRead (wellMat r qn qd en ed n) sp →
      inertia.revAt sp = 1 := by
  intro r qn qd en ed n c hc hlo hhi
  match Nat.lt_or_ge (c + 1) n with
  | Or.inl h2 =>
    exact certRevOneMixed r qn qd en ed n c h2 hlo
      (fun k hk1 => hhi k (Nat.le_of_succ_le hk1))
  | Or.inr _ =>
  intro sp hsp
  have hoff := wellOffWalk r qn qd en ed n c (walkPos r qn qd en ed c hlo)
    (walkNeg r qn qd en ed n c hhi)
  rw [greenprod.countSplit (wDiagL r qn qd en ed n) (wOffL r qd ed n)
    (wXL r qn qd en ed n) (wRL r qn qd en ed n) (List.replicate n 1)
    (wSpL r qn qd en ed n) sp
    (wellTailReadOf r qn qd en ed n
      (Nat.lt_of_le_of_lt (Nat.zero_le c) hc) hoff)
    (wellRevList r qn qd en ed n hoff) hsp]
  exact wellRevFold r qn qd en ed n c hc hlo hhi

/-- The two lines' bond identity: the bond weight at either scaled
rate is the scale's multiple of the one bond, the scale pass read
twice. -/
private theorem lineBond (r qd b b' : Nat) (ed : Pos) (W : BPair) :
    (BPair.ofNat b' * (wellBond r (b * qd) ed).swap + W * BPair.unit).oneValue
      (BPair.ofNat b * (wellBond r (b' * qd) ed).swap) := by
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.mul_unit W)) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
    (ground.swap_congr (bondScale r qd b ed))) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm (BPair.mul_congr (BPair.oneValue_refl _)
      (ground.swap_congr (bondScale r qd b' ed))))
  rw [BPair.mul_swap (BPair.ofNat b') (BPair.ofNat b * wellBond r qd ed),
    BPair.mul_swap (BPair.ofNat b) (BPair.ofNat b' * wellBond r qd ed)]
  exact ground.swap_congr (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _))

/-- The two member lines agree off the band, the gap's weight
entering the vacant site. -/
private theorem lineFar (b b' : Nat) (W : BPair) :
    (BPair.ofNat b' * BPair.unit + W * BPair.unit).oneValue
      (BPair.ofNat b * BPair.unit) :=
  BPair.oneValue_trans
    (BPair.add_congr (BPair.mul_unit (BPair.ofNat b')) (BPair.mul_unit W))
    (BPair.oneValue_trans (BPair.add_unit BPair.unit)
      (BPair.oneValue_symm (BPair.mul_unit (BPair.ofNat b))))

/-- The representatives' sum reads the summands' own. -/
private theorem normPair {x y z : BPair} (h : (x + y).oneValue z) :
    (x.norm + y.norm).oneValue z.norm :=
  BPair.oneValue_trans
    (BPair.add_congr (BPair.norm_oneValue x) (BPair.norm_oneValue y))
    (BPair.oneValue_trans h (BPair.oneValue_symm (BPair.norm_oneValue z)))

/-- The entry chart at the diagonal key. -/
private theorem chainAt_diag (d o : List BPair) (i : Nat) :
    chainAt d o i i = ground.getAt BPair.unit d i := if_pos rfl

/-- The entry chart one key below the diagonal. -/
private theorem chainAt_low (d o : List BPair) (i j : Nat) (h1 : ¬ j = i)
    (h2 : j + 1 = i) : chainAt d o i j = ground.getAt BPair.unit o j := by
  show (if j = i then ground.getAt BPair.unit d i
      else if j + 1 = i then ground.getAt BPair.unit o j
      else if i + 1 = j then ground.getAt BPair.unit o i
      else BPair.unit) = _
  rw [if_neg h1, if_pos h2]

/-- The entry chart one key above the diagonal. -/
private theorem chainAt_up (d o : List BPair) (i j : Nat) (h1 : ¬ j = i)
    (h2 : ¬ j + 1 = i) (h3 : i + 1 = j) :
    chainAt d o i j = ground.getAt BPair.unit o i := by
  show (if j = i then ground.getAt BPair.unit d i
      else if j + 1 = i then ground.getAt BPair.unit o j
      else if i + 1 = j then ground.getAt BPair.unit o i
      else BPair.unit) = _
  rw [if_neg h1, if_neg h2, if_pos h3]

/-- The entry chart beyond the band. -/
private theorem chainAt_far (d o : List BPair) (i j : Nat) (h1 : ¬ j = i)
    (h2 : ¬ j + 1 = i) (h3 : ¬ i + 1 = j) :
    chainAt d o i j = BPair.unit := by
  show (if j = i then ground.getAt BPair.unit d i
      else if j + 1 = i then ground.getAt BPair.unit o j
      else if i + 1 = j then ground.getAt BPair.unit o i
      else BPair.unit) = _
  rw [if_neg h1, if_neg h2, if_neg h3]

/-- Two member lines' site identity: the cross-multiplied datum
gap is the stated positive diagonal, one cross-multiplication per
scale -- the rates' gap's own matrix read. -/
theorem lineSite : ∀ (r qn qd : Nat) (en ed : Pos) (n a b a' b' gg : Nat),
    a' * b + gg = a * b' →
    elim.matOneValue
      (elim.matAdd
        (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed n))
        (inertia.matScaleB
          (BPair.ofNat ((r + 1) * (gg * qn))
            * BPair.ofPos en * BPair.ofPos ed)
          (inertia.idMat n)))
      (inertia.matScaleB (BPair.ofNat b)
        (wellMat r (a' * qn) (b' * qd) en ed n)) := by
  intro r qn qd en ed n a b a' b' gg hab
  cases n with
  | zero => trivial
  | succ m =>
    have hsc : ∀ (c : BPair) (A : elim.Mat) (k i j : Nat), elim.rowsLen k A →
        i < A.length → j < k →
        ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) (inertia.matScaleB c A) i) j
          = (c * ground.getAt BPair.unit
              (ground.getAt ([] : List BPair) A i) j).norm :=
      fun c A k i j hA hi hj => inertia.entry_scaleB c A k hA i j hi hj
    have hM1l := wellLen r (a * qn) (b * qd) en ed m
    have hM1r := wellRows r (a * qn) (b * qd) en ed m
    have hM2l := wellLen r (a' * qn) (b' * qd) en ed m
    have hM2r := wellRows r (a' * qn) (b' * qd) en ed m
    have hAl : (inertia.matScaleB (BPair.ofNat b')
        (wellMat r (a * qn) (b * qd) en ed (m + 1))).length = m + 1 := by
      rw [inertia.length_scaleB]
      exact hM1l
    have hBl : (inertia.matScaleB
        (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en * BPair.ofPos ed)
        (inertia.idMat (m + 1))).length = m + 1 := by
      rw [inertia.length_scaleB]
      exact inertia.idMat_len (m + 1)
    have hAr := inertia.rowsLen_scaleB (BPair.ofNat b') (m + 1) _ hM1r
    have hBr := inertia.rowsLen_scaleB
      (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en * BPair.ofPos ed)
      (m + 1) _ (inertia.idMat_rows (m + 1))
    refine elim.matOne_of_entries _ _ (m + 1)
      ((elim.length_matAdd _ _ (hAl.trans hBl.symm)).trans hAl)
      (elim.rowsLen_matAdd (m + 1) _ _ hAr hBr)
      (by rw [inertia.length_scaleB]; exact hM2l)
      (inertia.rowsLen_scaleB (BPair.ofNat b) (m + 1) _ hM2r) ?_
    intro i j hi hj
    rw [elim.entry_matAdd _ _ (m + 1) hAr hBr i j
        (by rw [hAl]; exact hi) (by rw [hBl]; exact hi) hj,
      hsc (BPair.ofNat b') _ (m + 1) i j hM1r (by rw [hM1l]; exact hi) hj,
      hsc (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en * BPair.ofPos ed)
        _ (m + 1) i j (inertia.idMat_rows (m + 1))
        (by rw [inertia.idMat_len]; exact hi) hj,
      hsc (BPair.ofNat b) _ (m + 1) i j hM2r (by rw [hM2l]; exact hi) hj,
      wellEntry r (a * qn) (b * qd) en ed m i j hi hj,
      wellEntry r (a' * qn) (b' * qd) en ed m i j hi hj,
      inertia.getAt_idMat (m + 1) i j hi hj]
    match Nat.decEq j i with
    | isTrue hji =>
      rw [hji, chainAt_diag, chainAt_diag, if_pos rfl,
        wDiagE_at r (a * qn) (b * qd) en ed (m + 1) i hi,
        wDiagE_at r (a' * qn) (b' * qd) en ed (m + 1) i hi]
      refine normPair ?_
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.mul_one_read _)) ?_
      exact lineDiag r qn qd a b a' b' gg (m + 1 - i) en ed hab
    | isFalse hji =>
      rw [if_neg hji]
      match Nat.decEq (j + 1) i with
      | isTrue hlo =>
        have hjm : j < m + 1 - 1 := by
          rw [← hlo] at hi
          exact Nat.lt_of_succ_lt_succ hi
        rw [chainAt_low _ _ i j hji hlo, chainAt_low _ _ i j hji hlo,
          wOffE_at r (b * qd) ed (m + 1) j hjm,
          wOffE_at r (b' * qd) ed (m + 1) j hjm]
        exact normPair (lineBond r qd b b' ed _)
      | isFalse hlo =>
        match Nat.decEq (i + 1) j with
        | isTrue hup =>
          have him : i < m + 1 - 1 := by
            rw [← hup] at hj
            exact Nat.lt_of_succ_lt_succ hj
          rw [chainAt_up _ _ i j hji hlo hup, chainAt_up _ _ i j hji hlo hup,
            wOffE_at r (b * qd) ed (m + 1) i him,
            wOffE_at r (b' * qd) ed (m + 1) i him]
          exact normPair (lineBond r qd b b' ed _)
        | isFalse hup =>
          rw [chainAt_far _ _ i j hji hlo hup,
            chainAt_far _ _ i j hji hlo hup]
          exact normPair (lineFar b b' _)

/-- The site datum of two member lines' scaled heads is the gap's
scalar diagonal: the line identity read at the sum's own
rearrangement, the balanced copy withdrawing. -/
private theorem lineGap (r qn qd : Nat) (en ed : Pos) (n a b a' b' gg : Nat)
    (hab : a' * b + gg = a * b') :
    elim.matOneValue
      (inertia.siteDatum
        (inertia.matScaleB (BPair.ofNat b)
          (wellMat r (a' * qn) (b' * qd) en ed n))
        (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed n)))
      (inertia.matScaleB
        (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en * BPair.ofPos ed)
        (inertia.idMat n)) := by
  cases n with
  | zero => trivial
  | succ m =>
    have hLS := lineSite r qn qd en ed (m + 1) a b a' b' gg hab
    have hXr : elim.rowsLen (m + 1)
        (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1))) :=
      inertia.rowsLen_scaleB _ _ _ (wellRows r (a * qn) (b * qd) en ed m)
    have hXl : (((inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1)))) : elim.Mat).length = m + 1 := by
      rw [inertia.length_scaleB]
      exact wellLen r (a * qn) (b * qd) en ed m
    have hYr : elim.rowsLen (m + 1)
        (inertia.matScaleB (BPair.ofNat b)
          (wellMat r (a' * qn) (b' * qd) en ed (m + 1))) :=
      inertia.rowsLen_scaleB _ _ _ (wellRows r (a' * qn) (b' * qd) en ed m)
    have hWr : elim.rowsLen (m + 1)
        (inertia.matScaleB
          (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en
            * BPair.ofPos ed)
          (inertia.idMat (m + 1))) :=
      inertia.rowsLen_scaleB _ _ _ (inertia.idMat_rows (m + 1))
    have hWl : (((inertia.matScaleB
          (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en
            * BPair.ofPos ed)
          (inertia.idMat (m + 1)))) : elim.Mat).length = m + 1 := by
      rw [inertia.length_scaleB]
      exact inertia.idMat_len (m + 1)
    have hSXr : elim.rowsLen (m + 1) (elim.matSwap (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1)))) :=
      elim.rowsLen_mapRows _ _ (m + 1) hXr
    have hAr : elim.rowsLen (m + 1)
        (elim.matAdd (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1))) (inertia.matScaleB
          (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en
            * BPair.ofPos ed)
          (inertia.idMat (m + 1)))) :=
      elim.rowsLen_matAdd (m + 1) _ _ hXr hWr
    have hnull : elim.matNull
        (elim.matAdd (elim.matSwap (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1)))) (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1)))) := by
      rw [elim.matAdd_comm]
      exact elim.matNull_add_swap _
    have hZl : (elim.matAdd (elim.matSwap (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1)))) (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1)))).length
        = (((inertia.matScaleB
          (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en
            * BPair.ofPos ed)
          (inertia.idMat (m + 1)))) : elim.Mat).length := by
      rw [elim.length_matAdd _ _ (elim.length_matSwap _),
        elim.length_matSwap, hXl, hWl]
    have hZr : elim.rowsLen (m + 1)
        (elim.matAdd (elim.matSwap (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1)))) (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1)))) :=
      elim.rowsLen_matAdd (m + 1) _ _ hSXr hXr
    show elim.matOneValue
      (elim.matAdd (inertia.matScaleB (BPair.ofNat b)
          (wellMat r (a' * qn) (b' * qd) en ed (m + 1))) (elim.matSwap (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1))))) (inertia.matScaleB
          (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en
            * BPair.ofPos ed)
          (inertia.idMat (m + 1)))
    refine elim.matOne_trans
      (elim.matAdd_cong2 (m + 1) _ _ _ _ hYr hSXr hAr hSXr
        (elim.matOne_symm hLS) (elim.matOne_refl _)) ?_
    rw [elim.matAdd_comm (elim.matAdd (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1))) (inertia.matScaleB
          (BPair.ofNat ((r + 1) * (gg * qn)) * BPair.ofPos en
            * BPair.ofPos ed)
          (inertia.idMat (m + 1)))) (elim.matSwap (inertia.matScaleB (BPair.ofNat b')
          (wellMat r (a * qn) (b * qd) en ed (m + 1)))),
      ← elim.matAdd_assoc]
    exact elim.matAdd_nullL _ _ hnull hZl hZr hWr

/-- A matrix reading a vacant matrix's value is vacant. -/
private theorem matNull_congr : ∀ {M B : elim.Mat},
    elim.matOneValue M B → elim.matNull B → elim.matNull M
  | [], _, _, _ => trivial
  | _ :: _, [], h, _ => h.elim
  | _ :: _, _ :: _, h, hb =>
    ⟨poly.oneValue_unitTail h.1 hb.1, matNull_congr h.2 hb.2⟩

/-- A matrix scaled by the sum's unit is vacant. -/
private theorem scaleB_null (W : BPair) (hW : W.oneValue BPair.unit) :
    ∀ M : elim.Mat, elim.matNull (inertia.matScaleB W M)
  | [] => trivial
  | r :: t => ⟨poly.scaleP_null hW r, scaleB_null W hW t⟩

/-- The monotone core: at cross-multiplied member data the lower
line's count sits at or below the upper's, the site datum's scalar
diagonal the comparison's carrier. -/
theorem cutMono : ∀ (r qn qd : Nat) (en ed : Pos) (n a b a' b' : Nat),
    1 ≤ b → 1 ≤ b' → a' * b ≤ a * b' →
    ∀ sp : inertia.Split n,
      inertia.splitRead (wellMat r (a * qn) (b * qd) en ed n) sp →
    ∀ sp' : inertia.Split n,
      inertia.splitRead (wellMat r (a' * qn) (b' * qd) en ed n) sp' →
      inertia.revAt sp' ≤ inertia.revAt sp := by
  intro r qn qd en ed n a b a' b' hb hb' hle sp hsp sp' hsp'
  have hgg : a' * b + (a * b' - a' * b) = a * b' :=
    ground.natAddSubCancel hle
  have hb1 : BPair.unit < BPair.ofNat b := ground.unitLtNat hb
  have hb1' : BPair.unit < BPair.ofNat b' := ground.unitLtNat hb'
  have hA := inertia.scaleSplit_read (BPair.ofNat b')
    (ground.offOfUnitLt hb1')
    (wellMat r (a * qn) (b * qd) en ed n) sp hsp
  have hC := inertia.scaleSplit_read (BPair.ofNat b)
    (ground.offOfUnitLt hb1)
    (wellMat r (a' * qn) (b' * qd) en ed n) sp' hsp'
  have hsqD := inertia.sqAt_siteDatum n _ _ hC.1 hA.1
  have hgap := lineGap r qn qd en ed n a b a' b' (a * b' - a' * b) hgg
  have key : inertia.revAt (inertia.scaleSplit (BPair.ofNat b) sp')
      ≤ inertia.revAt (inertia.scaleSplit (BPair.ofNat b') sp) := by
    match Nat.decEq ((r + 1) * ((a * b' - a' * b) * qn)) 0 with
    | isTrue hK =>
      have hWu : (BPair.ofNat ((r + 1) * ((a * b' - a' * b) * qn))
          * BPair.ofPos en * BPair.ofPos ed).oneValue BPair.unit := by
        rw [hK]
        exact BPair.oneValue_trans
          (BPair.mul_congr (BPair.unit_mul (BPair.ofPos en))
            (BPair.oneValue_refl (BPair.ofPos ed)))
          (BPair.unit_mul (BPair.ofPos ed))
      exact inertia.rev_mono _ _ (inertia.unitSplit n) _ _
        (inertia.unitSplit_read _ hsqD
          (matNull_congr hgap (scaleB_null _ hWu _)))
        (inertia.unitSplit_psd n) hA hC
    | isFalse hK =>
      have hWpos : BPair.unit < (BPair.ofNat ((r + 1)
            * ((a * b' - a' * b) * qn))
          * BPair.ofPos en * BPair.ofPos ed) :=
        ground.unitLtMul
          (ground.unitLtMul (ground.unitLtNat (Nat.pos_of_ne_zero hK))
            (ground.unitLtOfPos en)) (ground.unitLtOfPos ed)
      have hid : inertia.splitRead (inertia.idMat n)
          (inertia.scalarSplit n Pos.one) :=
        inertia.scalarSplit_read Pos.one (inertia.idMat n)
          (elim.sqAt_of (inertia.idMat_len n) (inertia.idMat_rows n))
          (by rw [inertia.matScale_one]; exact elim.matOne_refl _)
      have hspd := inertia.splitRead_congr _ _ hsqD (elim.matOne_symm hgap) _
        (inertia.scaleSplit_read _ (ground.offOfUnitLt hWpos)
          (inertia.idMat n) (inertia.scalarSplit n Pos.one) hid)
      have hpsd : inertia.psdAt (inertia.scaleSplit
          (BPair.ofNat ((r + 1) * ((a * b' - a' * b) * qn))
            * BPair.ofPos en * BPair.ofPos ed)
          (inertia.scalarSplit n Pos.one)) := by
        show inertia.revAt _ = 0
        rw [inertia.scaleSplit_rev _ hWpos (inertia.scalarSplit n Pos.one)]
        exact inertia.scalarSplit_psd n Pos.one
      exact inertia.rev_mono _ _ _ _ _ hspd hpsd hA hC
  rw [inertia.scaleSplit_rev (BPair.ofNat b) hb1 sp',
    inertia.scaleSplit_rev (BPair.ofNat b') hb1' sp] at key
  exact key


/-- The multiple cut's downward closure at the count's read: a
member's crossing data settle every pair at or below it toward one,
the counting function monotone in its level and the family the
occupied witness -- the flat window, count one from the lower line's
side to the member's. -/
theorem cutFlat : ∀ (en ed : Pos) (r N n c a b a' b' g' : Nat),
    2 ≤ N → N ≤ n → c < n →
    1 ≤ b →
    1 ≤ b' → b' + g' = a' → 1 ≤ g' →
    a' * b ≤ a * b' →
    (∀ k, k < c →
      BPair.unit < wellWalk r
        (a * qLowNum (ground.posVal en) (ground.posVal ed) r N)
        (b * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed (k + 1)) →
    (∀ k, c ≤ k → k < n →
      wellWalk r (a * qLowNum (ground.posVal en) (ground.posVal ed) r N)
        (b * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed (k + 1)
        < BPair.unit) →
    ∀ sp : inertia.Split n,
      inertia.splitRead
        (wellMat r (a * qLowNum (ground.posVal en) (ground.posVal ed) r N)
          (b * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n) sp →
    ∀ sp' : inertia.Split n,
      inertia.splitRead
        (wellMat r (a' * qLowNum (ground.posVal en) (ground.posVal ed) r N)
          (b' * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n) sp' →
      inertia.revAt sp' = 1 := by
  intro en ed r N n c a b a' b' g' hN hNn hc hb hb' hab' hg' hle
    hlo hhi sp hsp sp' hsp'
  refine Nat.le_antisymm ?_
    (witCount en ed r N n a' b' g' hN hNn hab' hg' sp' hsp')
  rw [← certRevOne r (a * qLowNum (ground.posVal en) (ground.posVal ed) r N)
    (b * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n c
    hc hlo hhi sp hsp]
  exact cutMono r (qLowNum (ground.posVal en) (ground.posVal ed) r N)
    (qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n a b a' b'
    hb hb' hle sp hsp sp' hsp'

/-- The lower rate's data are occupied at an occupied family. -/
theorem qLowPos : ∀ (en ed r N : Nat), 1 ≤ en → 1 ≤ ed → 2 ≤ N →
    0 < qLowNum en ed r N ∧ 0 < qLowDen en ed r N := by
  intro en ed r N hen hed hN
  refine ⟨posQLow en ed r N hed hN, ?_⟩
  show 0 < en * ed * (r + 1) * witSq N
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hen hed) (Nat.succ_pos r))
    (posWitSq N hN)

/-- The rates' gap at a cut member, `o = [g:b]·q₋`: the read's two
data at the member's gap. -/
def gapLow (en ed r N g b : Nat) : Nat × Nat :=
  (g * qLowNum en ed r N, b * qLowDen en ed r N)

/-- The gap's data are occupied at an occupied family: positive by
its shape. -/
theorem gapLow_pos (en ed r N g b : Nat) (hen : 1 ≤ en) (hed : 1 ≤ ed)
    (hN : 2 ≤ N) (hg : 1 ≤ g) (hb : 1 ≤ b) :
    0 < (gapLow en ed r N g b).1 ∧ 0 < (gapLow en ed r N g b).2 :=
  ⟨Nat.mul_pos hg (qLowPos en ed r N hen hed hN).1,
   Nat.mul_pos hb (qLowPos en ed r N hen hed hN).2⟩

/-- The gap joins the lower rate to the member's own,
`q₋ + o = μq₋`, one cross-multiplied identity at the member's gap. -/
theorem gapLow_tie (en ed r N g b a : Nat) (hab : b + g = a) :
    qLowNum en ed r N * (b * qLowDen en ed r N)
        + g * qLowNum en ed r N * qLowDen en ed r N
      = a * qLowNum en ed r N * qLowDen en ed r N := by
  rw [← hab, ground.mulAddR b g (qLowNum en ed r N),
    ground.mulAddR (b * qLowNum en ed r N) (g * qLowNum en ed r N)
      (qLowDen en ed r N)]
  rw [ground.mulLeftComm (qLowNum en ed r N) b (qLowDen en ed r N)]
  rw [ground.mulAssoc b (qLowNum en ed r N) (qLowDen en ed r N)]

/-- The cap pair's read at the well head: a second stated family of
the witness's shape at its own endpoint, the compressed pencil's
two-by-two entries the folds of the two lists, and a compressed
count of two at the cap line placing two chain roots below the cap
— the second root below the cap, the compression's counts at or
below the full form's. -/
theorem capPair : ∀ (en ed : Pos) (r N N' n ac bc : Nat),
    inertia.quadForm
        (wellMat r (ac * qLowNum (ground.posVal en) (ground.posVal ed) r N)
          (bc * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n)
        (witList N n)
      < BPair.unit →
    (elim.dotN (witList N n)
        (elim.matVec
          (wellMat r (ac * qLowNum (ground.posVal en) (ground.posVal ed) r N)
            (bc * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n)
          (witList N' n))
      + elim.dotN (witList N' n)
        (elim.matVec
          (wellMat r (ac * qLowNum (ground.posVal en) (ground.posVal ed) r N)
            (bc * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n)
          (witList N n)))
        * (elim.dotN (witList N n)
            (elim.matVec
              (wellMat r
                (ac * qLowNum (ground.posVal en) (ground.posVal ed) r N)
                (bc * qLowDen (ground.posVal en) (ground.posVal ed) r N)
                en ed n)
              (witList N' n))
          + elim.dotN (witList N' n)
            (elim.matVec
              (wellMat r
                (ac * qLowNum (ground.posVal en) (ground.posVal ed) r N)
                (bc * qLowDen (ground.posVal en) (ground.posVal ed) r N)
                en ed n)
              (witList N n)))
      < BPair.ofNat 4
        * (inertia.quadForm
            (wellMat r
              (ac * qLowNum (ground.posVal en) (ground.posVal ed) r N)
              (bc * qLowDen (ground.posVal en) (ground.posVal ed) r N)
              en ed n)
            (witList N n)
          * inertia.quadForm
            (wellMat r
              (ac * qLowNum (ground.posVal en) (ground.posVal ed) r N)
              (bc * qLowDen (ground.posVal en) (ground.posVal ed) r N)
              en ed n)
            (witList N' n)) →
    ∀ sp : inertia.Split n,
      inertia.splitRead
        (wellMat r (ac * qLowNum (ground.posVal en) (ground.posVal ed) r N)
          (bc * qLowDen (ground.posVal en) (ground.posVal ed) r N) en ed n)
        sp →
      2 ≤ inertia.revAt sp := by
  intro en ed r N N' n ac bc h11 hdet sp hsp
  exact capForcing _ (witList N n) (witList N' n) (witList_len N n)
    (witList_len N' n) h11 hdet sp hsp


/-! The bundled certificate's glue: the depth reads' geometry, the
rate transfer from the cap line to the member line, the profile
chains across the segments and seams, the geometric tail, and the
crossing's arms. -/

/-- The depth's square-scale read as a composite, `m²η` at the
scale's cleared members. -/
private def sAt (en ed : Pos) (m : Nat) : CPair :=
  ⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩

/-- A composite comparison at a shared second datum is the first
data's own. -/
private theorem cleNum {a b : BPair} {w : Pos} (h : a ≤ b) :
    (⟨a, w⟩ : CPair) ≤ ⟨b, w⟩ :=
  ground.leB_scale h w

/-- The depth read grows with the depth. -/
private theorem sAt_mono (en ed : Pos) {m m' : Nat} (h : m ≤ m') :
    sAt en ed m ≤ sAt en ed m' :=
  cleNum (ground.leB_mul_mono
    (ground.leB_of_lt (ground.unitLtOfPos en))
    (ground.unitLeOfNat (m' * m'))
    (ground.leB_ofNat (Nat.mul_le_mul h h))
    (ground.leB_refl (BPair.ofPos en)))

/-- Every depth read sits at or above the composite unit. -/
private theorem sAt_unit (en ed : Pos) (m : Nat) :
    stage.unitC ≤ sAt en ed m :=
  cunitLe (ground.unitLeMul (ground.unitLeOfNat (m * m))
    (ground.leB_of_lt (ground.unitLtOfPos en)))

/-! The rate transfer: the certificate's device reads are the cap
line's, and every comparison of the cap line's bond against its
diagonal carries to the member line at the cross-multiplied rate
read. -/

/-- The two lines' diagonals at a depth: the cap line's diagonal
scaled at the member's second datum sits at or below the member
line's scaled at the cap's, the rates' gap the difference. -/
private theorem rateDiag (r qcN qcD A B : Nat) (en ed : Pos) (m : Nat)
    (h : A * qcD ≤ qcN * B) :
    BPair.ofNat B * wellDiag r qcN qcD en ed m
      ≤ BPair.ofNat qcD * wellDiag r A B en ed m := by
  have hld := lineDiag r 1 1 qcN qcD A B (qcN * B - A * qcD) m en ed
    (ground.natAddSubCancel h)
  rw [Nat.mul_one qcN, Nat.mul_one qcD, Nat.mul_one A, Nat.mul_one B,
    Nat.mul_one (qcN * B - A * qcD)] at hld
  exact ground.dom_of_split hld
    (ground.unitLeMul
      (ground.unitLeMul (ground.unitLeOfNat ((r + 1) * (qcN * B - A * qcD)))
        (ground.leB_of_lt (ground.unitLtOfPos en)))
      (ground.leB_of_lt (ground.unitLtOfPos ed)))

/-- The two lines' bond weights at a depth: each scaled at the
other's second datum reads one value, the weights' shared count. -/
private theorem rateBond (r qcD B : Nat) (ed : Pos) :
    (BPair.ofNat B * wellBond r qcD ed).oneValue
      (BPair.ofNat qcD * wellBond r B ed) := by
  refine BPair.oneValue_trans
    (numScale B ((r + 1) * qcD) (BPair.ofPos ed) (BPair.ofPos ed)) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm
      (numScale qcD ((r + 1) * B) (BPair.ofPos ed) (BPair.ofPos ed)))
  rw [ground.mulLeftComm B (r + 1) qcD, ground.mulLeftComm qcD (r + 1) B,
    Nat.mul_comm B qcD]
  exact BPair.oneValue_refl _

/-- The rate transfer: a comparison of the cap line's bond weight
against its diagonal carries to the member line, the cap's second
datum cancelled at the cross-multiplied rate read. -/
private theorem rateStep (r qcN qcD A B : Nat) (en ed : Pos) (m : Nat)
    (X Y : BPair) (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (hY : BPair.unit ≤ Y)
    (h : wellBond r qcD ed * X ≤ wellDiag r qcN qcD en ed m * Y) :
    wellBond r B ed * X ≤ wellDiag r A B en ed m * Y := by
  have hQ : BPair.unit ≤ BPair.ofNat B := ground.unitLeOfNat B
  have hP : BPair.unit < BPair.ofNat qcD := ground.unitLtNat hqcD
  refine ground.leB_unscale hP ?_
  have step1 : BPair.ofNat B * (wellBond r qcD ed * X)
      ≤ BPair.ofNat B * (wellDiag r qcN qcD en ed m * Y) :=
    ground.leB_mulR hQ h
  have eL : (BPair.ofNat B * (wellBond r qcD ed * X)).oneValue
      (wellBond r B ed * X * BPair.ofNat qcD) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_assoc (BPair.ofNat B) (wellBond r qcD ed) X).symm) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr_left (rateBond r qcD B ed)) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_assoc (BPair.ofNat qcD) (wellBond r B ed) X,
      BPair.mul_comm (BPair.ofNat qcD) (wellBond r B ed * X)]
  have hR : BPair.ofNat B * (wellDiag r qcN qcD en ed m * Y)
      ≤ wellDiag r A B en ed m * Y * BPair.ofNat qcD := by
    refine ground.leB_congr ?_ ?_
      (ground.leB_mulR hY (rateDiag r qcN qcD A B en ed m hrate))
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_comm Y (BPair.ofNat B * wellDiag r qcN qcD en ed m),
        BPair.mul_assoc (BPair.ofNat B) (wellDiag r qcN qcD en ed m) Y]
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_comm Y (BPair.ofNat qcD * wellDiag r A B en ed m),
        BPair.mul_assoc (BPair.ofNat qcD) (wellDiag r A B en ed m) Y,
        BPair.mul_comm (BPair.ofNat qcD) (wellDiag r A B en ed m * Y)]
  exact ground.leB_trans (ground.leB_congr_left eL step1) hR

/-! The clearing kit: a cleared evaluation's positivity is
clearing-free, the two objects one value and each inside its own
clearing power. -/

/-- A positive cleared read carries across one-value objects at
either clearing power, each object inside its own. -/
private theorem posMove {p q : poly.Poly} {x : BPair} {c : Pos} {J J' : Nat}
    (hpq : poly.oneValue p q) (hp : p.length ≤ J' + 1)
    (hq : q.length ≤ J + 1)
    (h : BPair.unit < poly.evalClear q x c J) :
    BPair.unit < poly.evalClear p x c J' := by
  have hc : BPair.unit < BPair.ofPos c := ground.unitLtOfPos c
  match Nat.le_total J J' with
  | Or.inl hle =>
    refine BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (poly.evalClear_congr hpq x c J')) ?_
    refine BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (poly.evalClear_pow q x c J' J hq hle)) ?_
    exact ground.unitLtMul (windowsep.unitLt_bpow hc (J' - J)) h
  | Or.inr hle =>
    have hpJ : BPair.unit < poly.evalClear p x c J :=
      BPair.lt_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (poly.evalClear_congr hpq x c J)) h
    have hsplit : BPair.unit
        < ground.bpow (BPair.ofPos c) (J - J') * poly.evalClear p x c J' :=
      BPair.lt_congr (BPair.oneValue_refl _)
        (poly.evalClear_pow p x c J J' hp hle) hpJ
    refine unitLtOfMulRight
      (ground.leB_of_lt (windowsep.unitLt_bpow hc (J - J'))) ?_
    exact BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_of_eq
        (BPair.mul_comm (ground.bpow (BPair.ofPos c) (J - J'))
          (poly.evalClear p x c J'))) hsplit

/-- The comparison polynomial's key count sits two powers past the
profile's clearing. -/
private theorem termPoly_len {V : poly.PPoly × poly.PPoly} {K : Nat}
    (hsh : profShape V K) (r qn qd m : Nat) :
    (termPoly V r qn qd m).length ≤ K + 2 + 1 := by
  show (poly.add (poly.mul (diagPoly r qn qd (m + 1)) (depthPoly V (m + 1)))
      (poly.neg (poly.scaleP (BPair.ofNat ((r + 1) * qd))
        (poly.add (depthPoly V m) (depthPoly V (m + 2)))))).length ≤ K + 2 + 1
  refine poly.add_len_le _ _ (K + 2 + 1) ?_ ?_
  · rw [Nat.add_comm K 2]
    exact poly.mul_len_le (diagPoly r qn qd (m + 1)) (depthPoly V (m + 1))
      2 K (Nat.le_refl 3) (depthPoly_ble hsh (m + 1))
  · rw [poly.length_neg, poly.length_scaleP]
    exact Nat.le_trans
      (poly.add_len_le _ _ (K + 1) (depthPoly_ble hsh m)
        (depthPoly_ble hsh (m + 2)))
      (Nat.le_add_right (K + 1) 2)

/-! The device unpacking: a positive read of the stripped
comparison object at a depth is clause (i)'s termwise comparison at
the cap line, the profile's cleared evaluations the segment's
list. -/

/-- The stripped comparison object's positive read at a depth is
the termwise comparison at the cap line: the scale factor
withdrawn at the vacancy, the comparison polynomial's own read at
the profile's clearing two powers up. -/
private theorem termOfStrip (r qcN qcD : Nat) (en ed : Pos)
    (V : poly.PPoly × poly.PPoly) (Kv Kt m : Nat)
    (hsh : profShape V Kv)
    (hshT : profShape (profStrip (termProf V r qcN qcD)) Kt)
    (hpos : BPair.unit < poly.evalClear
      (depthPoly (profStrip (termProf V r qcN qcD)) m)
      (BPair.ofPos en) ed Kt) :
    wellBond r qcD ed
        * (poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv
          + poly.evalClear (depthPoly V (m + 2)) (BPair.ofPos en) ed Kv)
      ≤ wellDiag r qcN qcD en ed (m + 1)
        * poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed Kv := by
  have hshift : BPair.unit < poly.evalClear
      (poly.shiftUp 1 (depthPoly (profStrip (termProf V r qcN qcD)) m))
      (BPair.ofPos en) ed (Kt + 1) := by
    refine BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (evalClear_shiftUp 1
        (depthPoly (profStrip (termProf V r qcN qcD)) m)
        (BPair.ofPos en) ed (Kt + 1))) ?_
    exact ground.unitLtMul
      (windowsep.unitLt_bpow (ground.unitLtOfPos en) 1) hpos
  refine termRead_read hsh (ground.leB_of_lt (posMove ?_ ?_ ?_ hshift))
  · exact poly.oneValue_trans
      (poly.oneValue_symm (depthPoly_termProf V r qcN qcD m))
      (depthPoly_profStrip (termProf V r qcN qcD) m
        (termProf_vac V r qcN qcD))
  · exact termPoly_len hsh r qcN qcD m
  · rw [poly.len_shift 1 (depthPoly (profStrip (termProf V r qcN qcD)) m),
      Nat.add_comm 1 (depthPoly (profStrip (termProf V r qcN qcD)) m).length]
    exact Nat.succ_le_succ (depthPoly_ble hshT m)

/-- A segment's termwise comparison at the cap line, at every depth
whose square scale sits inside the term box. -/
private theorem segTermCap (r qcN qcD : Nat) (e0n : BPair) (e0d : Pos)
    (S : SegCert) (h : segRead r qcN qcD e0n e0d S) (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (m : Nat) (hlo : S.term.lo ≤ sAt en ed m)
    (hhi : sAt en ed m ≤ S.term.hi) :
    wellBond r qcD ed
        * (poly.evalClear (depthPoly S.jet m) (BPair.ofPos en) ed S.pos.K
          + poly.evalClear (depthPoly S.jet (m + 2))
              (BPair.ofPos en) ed S.pos.K)
      ≤ wellDiag r qcN qcD en ed (m + 1)
        * poly.evalClear (depthPoly S.jet (m + 1))
            (BPair.ofPos en) ed S.pos.K :=
  termOfStrip r qcN qcD en ed S.jet S.pos.K S.term.K m h.1.1
    h.2.1.1
    (boxRead_pos (profStrip (termProf S.jet r qcN qcD)) e0n e0d S.term
      h.2.1 m en ed he hlo hhi)

/-- A segment's profile positivity, at every depth whose square
scale sits inside the positivity box. -/
private theorem segPos (r qcN qcD : Nat) (e0n : BPair) (e0d : Pos)
    (S : SegCert) (h : segRead r qcN qcD e0n e0d S) (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (m : Nat) (hlo : S.pos.lo ≤ sAt en ed m)
    (hhi : sAt en ed m ≤ S.pos.hi) :
    BPair.unit
      < poly.evalClear (depthPoly S.jet m) (BPair.ofPos en) ed S.pos.K :=
  boxRead_pos S.jet e0n e0d S.pos h.1 m en ed he hlo hhi

/-- A segment's two-step overlap carries a depth inside the term
box's top to the square scale two depths on inside the positivity
box's. -/
private theorem segTwoStep (r qcN qcD : Nat) (e0n : BPair) (e0d : Pos)
    (S : SegCert) (h : segRead r qcN qcD e0n e0d S) (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (m : Nat) (hm : sAt en ed m ≤ S.term.hi) :
    sAt en ed (m + 2) ≤ S.pos.hi :=
  stepClear_step S.mid S.pos.hi e0n e0d h.2.2.2.2 (m + 1) en ed he
    (stepClear_step S.term.hi S.mid e0n e0d h.2.2.2.1 m en ed he hm)

/-! The seam: the crossed products' positive read carries an entry
read across the seam, the products' injectivity reading the crossed
entry back at positive profile values. -/

/-- The seam object's positive read at a depth is the crossed
products' order: the outgoing profile's consecutive values against
the incoming's. -/
private theorem crossOrder (Vp Vs : poly.PPoly × poly.PPoly) (K1 K2 : Nat)
    (en ed : Pos) (m Kc : Nat)
    (hshc : profShape (crossProf Vp Vs) Kc)
    (hp : profShape Vp K1) (hs : profShape Vs K2)
    (hpos : BPair.unit < poly.evalClear (depthPoly (crossProf Vp Vs) m)
      (BPair.ofPos en) ed Kc) :
    poly.evalClear (depthPoly Vp m) (BPair.ofPos en) ed K1
        * poly.evalClear (depthPoly Vs (m + 1)) (BPair.ofPos en) ed K2
      ≤ poly.evalClear (depthPoly Vp (m + 1)) (BPair.ofPos en) ed K1
        * poly.evalClear (depthPoly Vs m) (BPair.ofPos en) ed K2 := by
  have hmul1 : (poly.mul (depthPoly Vp (m + 1)) (depthPoly Vs m)).length
      ≤ K1 + K2 + 1 :=
    poly.mul_len_le _ _ K1 K2 (depthPoly_ble hp (m + 1)) (depthPoly_ble hs m)
  have hmul2 : (poly.mul (depthPoly Vp m) (depthPoly Vs (m + 1))).length
      ≤ K1 + K2 + 1 :=
    poly.mul_len_le _ _ K1 K2 (depthPoly_ble hp m) (depthPoly_ble hs (m + 1))
  have hsplit : BPair.unit < poly.evalClear
      (poly.add (poly.mul (depthPoly Vp (m + 1)) (depthPoly Vs m))
        (poly.neg (poly.mul (depthPoly Vp m) (depthPoly Vs (m + 1)))))
      (BPair.ofPos en) ed (K1 + K2) := by
    refine posMove (q := depthPoly (crossProf Vp Vs) m) ?_ ?_ ?_ hpos
    · exact poly.oneValue_symm (crossProf_at Vp Vs m)
    · refine poly.add_len_le _ _ (K1 + K2 + 1) hmul1 ?_
      rw [poly.length_neg]
      exact hmul2
    · exact depthPoly_ble hshc m
  have hval : BPair.unit ≤
      poly.evalClear (depthPoly Vp (m + 1)) (BPair.ofPos en) ed K1
          * poly.evalClear (depthPoly Vs m) (BPair.ofPos en) ed K2
        + (poly.evalClear (depthPoly Vp m) (BPair.ofPos en) ed K1
            * poly.evalClear (depthPoly Vs (m + 1))
              (BPair.ofPos en) ed K2).swap := by
    refine ground.leB_congr_right ?_ (ground.leB_of_lt hsplit)
    refine BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _) ?_
    refine BPair.add_congr
      (poly.evalClear_mul _ _ (BPair.ofPos en) ed K1 K2
        (depthPoly_ble hp (m + 1)) (depthPoly_ble hs m)) ?_
    refine BPair.oneValue_trans (poly.evalClear_neg _ _ _ _) ?_
    exact ground.swap_congr
      (poly.evalClear_mul _ _ (BPair.ofPos en) ed K1 K2
        (depthPoly_ble hp m) (depthPoly_ble hs (m + 1)))
  exact ground.leB_of_unit_add hval

/-- The seam's transfer: an entry read at the outgoing profile
crosses to the incoming one at the crossed products' order, the
outgoing value's positive factor cancelled. -/
private theorem crossTransfer {β Dk Dk1 p1 p2 s1 s2 : BPair}
    (hβD : BPair.unit ≤ β * Dk)
    (hp1 : BPair.unit < p1) (hs1 : BPair.unit ≤ s1)
    (hcross : p1 * s2 ≤ p2 * s1)
    (h1 : β * (Dk * p2) ≤ Dk1 * p1) :
    β * (Dk * s2) ≤ Dk1 * s1 := by
  refine ground.leB_unscale hp1 ?_
  have e1 : (β * (Dk * s2) * p1).oneValue (β * Dk * (p1 * s2)) := by
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.mul_assoc β Dk s2, BPair.mul_assoc (β * Dk) s2 p1,
      BPair.mul_comm s2 p1]
  have e2 : (β * Dk * (p2 * s1)).oneValue (β * (Dk * p2) * s1) := by
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.mul_assoc (β * Dk) p2 s1, BPair.mul_assoc β Dk p2]
  have step1 : β * Dk * (p1 * s2) ≤ β * Dk * (p2 * s1) :=
    ground.leB_mulR hβD hcross
  have step2 : β * (Dk * p2) * s1 ≤ Dk1 * p1 * s1 := by
    refine ground.leB_congr ?_ ?_ (ground.leB_mulR hs1 h1)
    · exact BPair.oneValue_of_eq (BPair.mul_comm s1 (β * (Dk * p2)))
    · exact BPair.oneValue_of_eq (BPair.mul_comm s1 (Dk1 * p1))
  have mid : β * Dk * (p1 * s2) ≤ Dk1 * p1 * s1 :=
    ground.leB_trans step1
      (ground.leB_congr_left (BPair.oneValue_symm e2) step2)
  refine ground.leB_congr_left (BPair.oneValue_symm e1) ?_
  refine ground.leB_congr_right ?_ mid
  refine BPair.oneValue_of_eq ?_
  rw [BPair.mul_assoc Dk1 p1 s1, BPair.mul_comm p1 s1,
    ← BPair.mul_assoc Dk1 s1 p1]

/-! The chain: clause (i)'s induction at the member line over one
stage's depths, the minor list bound by the walk's recursion alone
so the swapped side reads the same run, and the profile's index one
step behind the walk's. -/

/-- The diagonal grows with the depth at a fixed scale: the well's
electric member is the depth's own square-and-linear count. -/
private theorem wellDiag_mono (r qn qd : Nat) (en ed : Pos) {m m' : Nat}
    (h : m ≤ m') :
    wellDiag r qn qd en ed m ≤ wellDiag r qn qd en ed m' := by
  have hE : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hcount : 4 * qd * (m * m + r * m) ≤ 4 * qd * (m' * m' + r * m') :=
    Nat.mul_le_mul_left (4 * qd)
      (Nat.add_le_add (Nat.mul_le_mul h h) (Nat.mul_le_mul_left r h))
  refine ground.leB_congr (BPair.oneValue_symm (diagRead r qn qd m en ed))
    (BPair.oneValue_symm (diagRead r qn qd m' en ed)) ?_
  refine ground.leB_add (ground.leB_refl _) ?_
  refine ground.leB_add ?_ (ground.leB_refl _)
  refine ground.leB_mul_mono hE
    (ground.unitLeMul (ground.unitLeOfNat (4 * qd * (m' * m' + r * m'))) hE)
    ?_ (ground.leB_refl (BPair.ofPos en))
  exact ground.leB_mul_mono hE
    (ground.unitLeOfNat (4 * qd * (m' * m' + r * m')))
    (ground.leB_ofNat hcount) (ground.leB_refl (BPair.ofPos en))

/-- The stage's run: from an entry read at a walk depth with the
profile's index at most one step beyond it, every later pivot of
the covered depths clears its entry read, the minor list bound by
the recursion alone. -/
private theorem runD (r A B : Nat) (en ed : Pos) (D u : Nat → BPair)
    (hβ : BPair.unit < wellBond r B ed)
    (hrec : ∀ m, (D (m + 2)
        + wellBond r B ed * wellBond r B ed * D m).oneValue
      (wellDiag r A B en ed (m + 2) * D (m + 1)))
    (k p len : Nat) (hpk : p ≤ k + 1)
    (hpos : ∀ i, i ≤ len + 1 → BPair.unit < u (p + i))
    (hterm : ∀ i, i < len → wellBond r B ed * (u (p + i) + u (p + i + 2))
      ≤ wellDiag r A B en ed (p + i + 1) * u (p + i + 1))
    (h0 : BPair.unit < D k)
    (hent : wellBond r B ed * (D k * u (p + 1)) ≤ D (k + 1) * u p) :
    ∀ j, j ≤ len →
      BPair.unit < D (k + j + 1)
      ∧ wellBond r B ed * (D (k + j) * u (p + j + 1))
        ≤ D (k + j + 1) * u (p + j) := by
  refine pivot_clears
    (fun i => wellDiag r A B en ed (k + i + 1))
    (fun i => u (p + i)) (fun i => D (k + i)) (wellBond r B ed) len hβ
    (fun i _ => hrec (k + i)) ?_ hpos h0 hent
  intro i hi
  refine ground.leB_trans (hterm i hi) ?_
  refine ground.leB_congr
    (BPair.oneValue_of_eq
      (BPair.mul_comm (u (p + i + 1)) (wellDiag r A B en ed (p + i + 1))))
    (BPair.oneValue_of_eq
      (BPair.mul_comm (u (p + i + 1)) (wellDiag r A B en ed (k + i + 2))))
    ?_
  refine ground.leB_mulR
    (ground.leB_of_lt (hpos (i + 1) (Nat.succ_le_succ (Nat.le_of_lt hi)))) ?_
  refine wellDiag_mono r A B en ed (m' := k + i + 2) ?_
  rw [show k + i + 2 = k + 1 + i + 1 from by
    rw [Nat.add_right_comm k 1 i]]
  exact Nat.add_le_add_right (Nat.add_le_add_right hpk i) 1

/-! The stages' reads at the member line: a segment's boxes and the
pre tier's graded reads each hand the run its positivity and its
termwise comparison over a covered window. -/

/-- A segment's positivity over a window inside the term box, the
two-step overlap carrying the last two depths. -/
private theorem segStagePos (r qcN qcD : Nat) (e0n : BPair) (e0d : Pos)
    (en ed : Pos) (S : SegCert) (hseg : segRead r qcN qcD e0n e0d S)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (p len : Nat)
    (hlo : S.term.lo ≤ sAt en ed p)
    (hhi : sAt en ed (p + len) ≤ S.term.hi) :
    ∀ i, i ≤ len + 1 → BPair.unit
      < poly.evalClear (depthPoly S.jet (p + i)) (BPair.ofPos en) ed S.pos.K := by
  intro i hi
  refine segPos r qcN qcD e0n e0d S hseg en ed he (p + i) ?_ ?_
  · exact CPair.le_trans hseg.2.2.1
      (CPair.le_trans hlo (sAt_mono en ed (Nat.le_add_right p i)))
  · refine CPair.le_trans
      (sAt_mono en ed (h := Nat.add_le_add_left
        (Nat.le_trans hi (Nat.succ_le_succ (Nat.le_succ len))) p)) ?_
    exact segTwoStep r qcN qcD e0n e0d S hseg en ed he (p + len) hhi

/-- A segment's termwise comparison at the member line over a
window inside the term box. -/
private theorem segStageTerm (r qcN qcD A B : Nat) (e0n : BPair) (e0d : Pos)
    (en ed : Pos) (S : SegCert) (hseg : segRead r qcN qcD e0n e0d S)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (p len : Nat)
    (hlo : S.term.lo ≤ sAt en ed p)
    (hhi : sAt en ed (p + len) ≤ S.term.hi) :
    ∀ i, i < len → wellBond r B ed
        * (poly.evalClear (depthPoly S.jet (p + i)) (BPair.ofPos en) ed S.pos.K
          + poly.evalClear (depthPoly S.jet (p + i + 2))
              (BPair.ofPos en) ed S.pos.K)
      ≤ wellDiag r A B en ed (p + i + 1)
        * poly.evalClear (depthPoly S.jet (p + i + 1))
            (BPair.ofPos en) ed S.pos.K := by
  intro i hi
  refine rateStep r qcN qcD A B en ed (p + i + 1) _ _ hqcD hrate
    (ground.leB_of_lt (segStagePos r qcN qcD e0n e0d en ed S hseg he p len
      hlo hhi (i + 1) (Nat.succ_le_succ (Nat.le_of_lt hi)))) ?_
  refine segTermCap r qcN qcD e0n e0d S hseg en ed he (p + i) ?_ ?_
  · exact CPair.le_trans hlo (sAt_mono en ed (Nat.le_add_right p i))
  · exact CPair.le_trans
      (sAt_mono en ed (h := Nat.add_le_add_left (Nat.le_of_lt hi) p)) hhi

/-! The geometric tail's arithmetic: the cleared list's termwise
comparison is the margin's clearing of the squared gap's doubled
price, the gap at most the pair's half. -/

/-- The neighbor sum at the geometric pair: the arriving member's
double joins the gap's square against the withdrawn member. -/
private theorem sqSplit (g X : Nat) :
    (g + X) * (g + X) + g * g = 2 * (g * (g + X)) + X * X :=
  mirEq g X
    (Mir.add (Mir.mul (Mir.add Mir.x Mir.y) (Mir.add Mir.x Mir.y))
      (Mir.mul Mir.x Mir.x))
    (Mir.add (Mir.mul (Mir.cst 2) (Mir.mul Mir.x (Mir.add Mir.x Mir.y)))
      (Mir.mul Mir.y Mir.y))
    (by decide +kernel)

/-- The geometric list's termwise comparison at the cleared data:
the squared gap's price inside the margin's, the rate's balance
partner inside the diagonal's electric member. -/
private theorem geomNat (P Q M wde G W X : Nat)
    (hPX : P * (W * (X * X)) ≤ wde * (W * G))
    (hQM : Q * (W * G) + wde * (W * G) ≤ M * (W * G)) :
    P * (W * (2 * G + X * X)) + Q * (W * G) ≤ (2 * P + M) * (W * G) := by
  rw [Nat.mul_add W (2 * G) (X * X),
    Nat.mul_add P (W * (2 * G)) (W * (X * X)),
    ground.mulAddR (2 * P) M (W * G),
    ground.mulLeftComm W 2 G,
    ground.mulLeftComm P 2 (W * G),
    ground.mulAssoc 2 P (W * G),
    Nat.add_assoc (2 * (P * (W * G))) (P * (W * (X * X))) (Q * (W * G))]
  refine Nat.add_le_add_left ?_ (2 * (P * (W * G)))
  refine Nat.le_trans ?_ hQM
  rw [Nat.add_comm (Q * (W * G)) (wde * (W * G))]
  exact Nat.add_le_add hPX (Nat.le_refl (Q * (W * G)))

/-- The bond weight's count: the rate's clearing at the scale's
square. -/
private theorem bondNat (r qd : Nat) (ed : Pos) :
    (wellBond r qd ed).oneValue
      (BPair.ofNat ((r + 1) * qd * ground.posVal ed * ground.posVal ed)) := by
  show (BPair.ofNat ((r + 1) * qd) * BPair.ofPos ed * BPair.ofPos ed).oneValue _
  rw [BPair.ofPos_val ed]
  exact collect3 ((r + 1) * qd) (ground.posVal ed) (ground.posVal ed)

/-- The diagonal's counts: the band read's clearing with the well's
electric member against the rate's balance partner. -/
private theorem diagNat (r qn qd m : Nat) (en ed : Pos) :
    (wellDiag r qn qd en ed m).oneValue
      (BPair.ofNat (2 * ((r + 1) * qd * ground.posVal ed * ground.posVal ed)
          + 4 * qd * (m * m + r * m) * ground.posVal en * ground.posVal en)
        + (BPair.ofNat ((r + 1) * qn * ground.posVal en
            * ground.posVal ed)).swap) := by
  refine BPair.oneValue_trans (diagRead r qn qd m en ed) ?_
  rw [BPair.ofPos_val en, BPair.ofPos_val ed]
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
  refine BPair.add_congr ?_
    (ground.swap_congr
      (collect3 ((r + 1) * qn) (ground.posVal en) (ground.posVal ed)))
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 2))
        (collect3 ((r + 1) * qd) (ground.posVal ed) (ground.posVal ed)))
      (collect3 (4 * qd * (m * m + r * m)) (ground.posVal en)
        (ground.posVal en))) ?_
  exact BPair.oneValue_symm
    (BPair.oneValue_trans
      (BPair.ofNat_add
        (2 * ((r + 1) * qd * ground.posVal ed * ground.posVal ed))
        (4 * qd * (m * m + r * m) * ground.posVal en * ground.posVal en))
      (BPair.add_congr
        (BPair.ofNat_mul 2
          ((r + 1) * qd * ground.posVal ed * ground.posVal ed))
        (BPair.oneValue_refl _)))

/-- The termwise comparison at counted values: the bond weight's
count against the diagonal's, one cross-added natural read. -/
private theorem diagCompare (r qn qd m : Nat) (en ed : Pos) (a0 a2 a1 : Nat)
    (h : (r + 1) * qd * ground.posVal ed * ground.posVal ed * (a0 + a2)
          + (r + 1) * qn * ground.posVal en * ground.posVal ed * a1
      ≤ (2 * ((r + 1) * qd * ground.posVal ed * ground.posVal ed)
          + 4 * qd * (m * m + r * m) * ground.posVal en
            * ground.posVal en) * a1) :
    wellBond r qd ed * (BPair.ofNat a0 + BPair.ofNat a2)
      ≤ wellDiag r qn qd en ed m * BPair.ofNat a1 := by
  refine ground.leB_congr_left
    (BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.mul_congr (bondNat r qd ed)
          (BPair.oneValue_symm (BPair.ofNat_add a0 a2)))
        (BPair.oneValue_symm (BPair.ofNat_mul _ (a0 + a2))))) ?_
  have hR : (wellDiag r qn qd en ed m * BPair.ofNat a1).oneValue
      (BPair.ofNat ((2 * ((r + 1) * qd * ground.posVal ed * ground.posVal ed)
            + 4 * qd * (m * m + r * m) * ground.posVal en
              * ground.posVal en) * a1)
        + (BPair.ofNat ((r + 1) * qn * ground.posVal en
            * ground.posVal ed * a1)).swap) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (diagNat r qn qd m en ed)
        (BPair.oneValue_refl (BPair.ofNat a1))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.right_distrib _ _ (BPair.ofNat a1))) ?_
    refine BPair.add_congr
      (BPair.oneValue_symm (BPair.ofNat_mul _ a1)) ?_
    rw [BPair.swap_mul]
    exact ground.swap_congr (BPair.oneValue_symm (BPair.ofNat_mul _ a1))
  refine ground.leB_congr_right (BPair.oneValue_symm hR) ?_
  refine ground.leB_swapL ?_
  refine ground.leB_congr_left (BPair.ofNat_add _ _) ?_
  exact ground.leB_ofNat h

/-- The odd count at a depth beyond nought sits inside its triple. -/
private theorem oddCap (k : Nat) (h : 1 ≤ k) : 2 * k + 1 ≤ 3 * k := by
  rw [show (3 : Nat) * k = 2 * k + k from by
    rw [show (3 : Nat) = 2 + 1 from rfl, ground.mulAddR 2 1 k, Nat.one_mul]]
  exact Nat.add_le_add_left h (2 * k)

/-- The odd count's square at a depth beyond nought sits inside the
depth's own square at the ninefold count. -/
private theorem oddSq (k : Nat) (h : 1 ≤ k) :
    (2 * k + 1) * (2 * k + 1) ≤ 9 * (k * k) := by
  refine Nat.le_trans (Nat.mul_le_mul (oddCap k h) (oddCap k h))
    (Nat.le_of_eq ?_)
  rw [ground.mulAssoc 3 k (3 * k), ground.mulLeftComm k 3 k,
    ← ground.mulAssoc 3 3 (k * k)]

/-- A count's double. -/
private theorem twoNat (x : Nat) : 2 * x = x + x := by
  rw [show (2 : Nat) = 1 + 1 from rfl, ground.mulAddR 1 1 x, Nat.one_mul]

/-- The gap sits at or above the pair's half: the allowance's
cleared read of the depth step is at most half the clearing's
scale. -/
private theorem gapHalf (alN alD e d k0 g X : Nat)
    (hgX : g + X = alD * d) (hX : X = alN * (2 * k0 + 1) * e)
    (hhalf : 6 * (alN * k0 * e) ≤ alD * d) (hk0 : 1 ≤ k0) :
    alD * d ≤ 2 * g := by
  have h2X : 2 * X ≤ alD * d := by
    rw [hX]
    refine Nat.le_trans
      (Nat.mul_le_mul_left 2
        (Nat.mul_le_mul_right e
          (Nat.mul_le_mul_left alN (oddCap k0 hk0)))) ?_
    refine Nat.le_trans (Nat.le_of_eq ?_) hhalf
    exact monEq [alN, k0, e]
      (Mon.mul (Mon.cst 2)
        (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.cst 3) (Mon.var 1)))
          (Mon.var 2)))
      (Mon.mul (Mon.cst 6)
        (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))
      (by decide +kernel) (by decide +kernel)
  refine ground.leCancelR (alD * d) ?_
  have hdouble : 2 * g + 2 * X = alD * d + alD * d := by
    rw [← Nat.mul_add 2 g X, hgX, twoNat (alD * d)]
  rw [← hdouble]
  exact Nat.add_le_add_left h2X (2 * g)

/-- The tail's cleared margin: the allowance's squared read at the
seam's top sits inside the margin's own multiple of the gap. -/
private theorem tailCore (R qcD ws alN alD e d k0 g X : Nat)
    (hgX : g + X = alD * d) (hX : X = alN * (2 * k0 + 1) * e)
    (hws : 18 * (R * qcD) * (alN * alN) * (k0 * k0) * e
      ≤ ws * (alD * alD) * d)
    (hhalf : 6 * (alN * k0 * e) ≤ alD * d) (hk0 : 1 ≤ k0) :
    R * qcD * (alN * alN) * ((2 * k0 + 1) * (2 * k0 + 1)) * e
      ≤ ws * alD * g := by
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos 1)
  have step1 : 2 * (R * qcD * (alN * alN)
        * ((2 * k0 + 1) * (2 * k0 + 1)) * e)
      ≤ 2 * (R * qcD * (alN * alN) * (9 * (k0 * k0)) * e) :=
    Nat.mul_le_mul_left 2
      (Nat.mul_le_mul_right e
        (Nat.mul_le_mul_left (R * qcD * (alN * alN)) (oddSq k0 hk0)))
  have step2 : 2 * (R * qcD * (alN * alN) * (9 * (k0 * k0)) * e)
      = 18 * (R * qcD) * (alN * alN) * (k0 * k0) * e :=
    monEq [R, qcD, alN, k0, e]
      (Mon.mul (Mon.cst 2)
        (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
            (Mon.mul (Mon.var 2) (Mon.var 2)))
          (Mon.mul (Mon.cst 9) (Mon.mul (Mon.var 3) (Mon.var 3))))
          (Mon.var 4)))
      (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 18)
          (Mon.mul (Mon.var 0) (Mon.var 1)))
        (Mon.mul (Mon.var 2) (Mon.var 2)))
        (Mon.mul (Mon.var 3) (Mon.var 3))) (Mon.var 4))
      (by decide +kernel) (by decide +kernel)
  have step4 : ws * (alD * alD) * d = ws * alD * (alD * d) :=
    monEq [ws, alD, d]
      (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1) (Mon.var 1)))
        (Mon.var 2))
      (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
        (Mon.mul (Mon.var 1) (Mon.var 2)))
      (by decide +kernel) (by decide +kernel)
  have step6 : ws * alD * (2 * g) = 2 * (ws * alD * g) :=
    monEq [ws, alD, g]
      (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
        (Mon.mul (Mon.cst 2) (Mon.var 2)))
      (Mon.mul (Mon.cst 2)
        (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))
      (by decide +kernel) (by decide +kernel)
  refine Nat.le_trans step1 ?_
  rw [step2, ← step6]
  refine Nat.le_trans hws ?_
  rw [step4]
  exact Nat.mul_le_mul_left (ws * alD)
    (gapHalf alN alD e d k0 g X hgX hX hhalf hk0)

/-- The squared gap's price at the cleared geometric member. -/
private theorem tailPX (R qcD ws alN alD e d k0 g W : Nat)
    (hcore : R * qcD * (alN * alN) * ((2 * k0 + 1) * (2 * k0 + 1)) * e
      ≤ ws * alD * g) :
    R * qcD * d * d
        * (W * (alN * (2 * k0 + 1) * e * (alN * (2 * k0 + 1) * e)))
      ≤ ws * d * e * (W * (g * (alD * d))) := by
  have hL : R * qcD * d * d
        * (W * (alN * (2 * k0 + 1) * e * (alN * (2 * k0 + 1) * e)))
      = R * qcD * (alN * alN) * ((2 * k0 + 1) * (2 * k0 + 1)) * e
        * (W * (d * d * e)) :=
    monEq [R, qcD, d, W, alN, 2 * k0 + 1, e]
      (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
          (Mon.var 2)) (Mon.var 2))
        (Mon.mul (Mon.var 3)
          (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 5)) (Mon.var 6))
            (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 5)) (Mon.var 6)))))
      (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
          (Mon.mul (Mon.var 4) (Mon.var 4)))
        (Mon.mul (Mon.var 5) (Mon.var 5))) (Mon.var 6))
        (Mon.mul (Mon.var 3) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2))
          (Mon.var 6))))
      (by decide +kernel) (by decide +kernel)
  have hR : ws * alD * g * (W * (d * d * e))
      = ws * d * e * (W * (g * (alD * d))) :=
    monEq [ws, alD, g, W, d, e]
      (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
        (Mon.mul (Mon.var 3) (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4))
          (Mon.var 5))))
      (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 4)) (Mon.var 5))
        (Mon.mul (Mon.var 3)
          (Mon.mul (Mon.var 2) (Mon.mul (Mon.var 1) (Mon.var 4)))))
      (by decide +kernel) (by decide +kernel)
  rw [hL, ← hR]
  exact Nat.mul_le_mul_right (W * (d * d * e)) hcore

/-- The rate's balance partner joins the margin inside the
diagonal's electric member at every depth at or beyond the seam. -/
private theorem tailQM (R qcN qcD ws S T e d WG : Nat)
    (hTS : T ≤ S)
    (hdom : (R * qcN + ws) * d ≤ 4 * qcD * T * e) :
    R * qcN * e * d * WG + ws * d * e * WG
      ≤ 4 * qcD * S * e * e * WG := by
  have e1 : R * qcN * d * (e * WG) = R * qcN * e * d * WG :=
    monEq [R, qcN, d, e, WG]
      (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
        (Mon.mul (Mon.var 3) (Mon.var 4)))
      (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
        (Mon.var 3)) (Mon.var 2)) (Mon.var 4))
      (by decide +kernel) (by decide +kernel)
  have e2 : ws * d * (e * WG) = ws * d * e * WG :=
    monEq [ws, d, e, WG]
      (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
        (Mon.mul (Mon.var 2) (Mon.var 3)))
      (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
        (Mon.var 3))
      (by decide +kernel) (by decide +kernel)
  have e3 : 4 * qcD * S * e * (e * WG) = 4 * qcD * S * e * e * WG :=
    (ground.mulAssoc (4 * qcD * S * e) e WG).symm
  have hstep : (R * qcN + ws) * d * (e * WG) ≤ 4 * qcD * T * e * (e * WG) :=
    Nat.mul_le_mul_right (e * WG) hdom
  rw [ground.mulAddR (R * qcN) ws d,
    ground.mulAddR (R * qcN * d) (ws * d) (e * WG), e1, e2] at hstep
  refine Nat.le_trans hstep ?_
  rw [← e3]
  refine Nat.mul_le_mul_right (e * WG) (Nat.mul_le_mul_right e ?_)
  exact Nat.mul_le_mul_left (4 * qcD) hTS

/-- The geometric list's termwise comparison at the cap line: the
cleared members' neighbor sum against the diagonal's multiple of the
arriving member, at every depth at or beyond the seam. -/
private theorem geomTermCap (r qcN qcD ws alN alD k0 m1 g W : Nat)
    (en ed : Pos)
    (hgX : g + alN * (2 * k0 + 1) * ground.posVal en
      = alD * ground.posVal ed)
    (hws : 18 * ((r + 1) * qcD) * (alN * alN) * (k0 * k0)
        * ground.posVal en
      ≤ ws * (alD * alD) * ground.posVal ed)
    (hhalf : 6 * (alN * k0 * ground.posVal en) ≤ alD * ground.posVal ed)
    (hk0 : 1 ≤ k0)
    (hdom : ((r + 1) * qcN + ws) * ground.posVal ed
      ≤ 4 * qcD * (m1 * m1) * ground.posVal en) :
    wellBond r qcD ed
        * (BPair.ofNat (W * (alD * ground.posVal ed
              * (alD * ground.posVal ed)))
          + BPair.ofNat (W * (g * g)))
      ≤ wellDiag r qcN qcD en ed m1
        * BPair.ofNat (W * (g * (alD * ground.posVal ed))) := by
  have hcore := tailCore (r + 1) qcD ws alN alD (ground.posVal en)
    (ground.posVal ed) k0 g (alN * (2 * k0 + 1) * ground.posVal en)
    hgX rfl hws hhalf hk0
  have hPX := tailPX (r + 1) qcD ws alN alD (ground.posVal en)
    (ground.posVal ed) k0 g W hcore
  have hQM := tailQM (r + 1) qcN qcD ws (m1 * m1 + r * m1) (m1 * m1)
    (ground.posVal en) (ground.posVal ed)
    (W * (g * (alD * ground.posVal ed)))
    (Nat.le_add_right (m1 * m1) (r * m1)) hdom
  refine diagCompare r qcN qcD m1 en ed _ _ _ ?_
  rw [← hgX] at hPX hQM ⊢
  rw [← Nat.mul_add W
      ((g + alN * (2 * k0 + 1) * ground.posVal en)
        * (g + alN * (2 * k0 + 1) * ground.posVal en)) (g * g),
    sqSplit g (alN * (2 * k0 + 1) * ground.posVal en)]
  exact geomNat ((r + 1) * qcD * ground.posVal ed * ground.posVal ed)
    ((r + 1) * qcN * ground.posVal en * ground.posVal ed)
    (4 * qcD * (m1 * m1 + r * m1) * ground.posVal en * ground.posVal en)
    (ws * ground.posVal ed * ground.posVal en)
    (g * (g + alN * (2 * k0 + 1) * ground.posVal en)) W
    (alN * (2 * k0 + 1) * ground.posVal en) hPX hQM

/-! The geometric list: each member the prior member's multiple at
one pair of the scale's data, read at the cleared powers. -/

/-- The geometric list's cleared member at a depth: the gap's power
against the clearing's, the two counts' total the stated length. -/
private def geoU (g D0 k0 L : Nat) (m : Nat) : BPair :=
  BPair.ofNat (g ^ (m - k0) * D0 ^ (L - (m - k0)))

/-- The list's three consecutive members factor at one shared
member: the withdrawn member's square scale, the arriving member's
mixed pair and the far member's squared gap. -/
private theorem geoTriple (g D0 L i : Nat) (h : i + 2 ≤ L) :
    g ^ i * D0 ^ (L - i)
        = g ^ i * D0 ^ (L - (i + 2)) * (D0 * D0)
    ∧ g ^ (i + 1) * D0 ^ (L - (i + 1))
        = g ^ i * D0 ^ (L - (i + 2)) * (g * D0)
    ∧ g ^ (i + 2) * D0 ^ (L - (i + 2))
        = g ^ i * D0 ^ (L - (i + 2)) * (g * g) := by
  obtain ⟨w, hw⟩ := Nat.le.dest h
  have hsplit : i + 2 + w = i + 1 + (1 + w) := by
    rw [Nat.add_assoc i 1 (1 + w), Nat.add_assoc i 2 w,
      show (2 : Nat) + w = 1 + (1 + w) from Nat.add_assoc 1 1 w]
  have e0 : L - i = 2 + w := by
    rw [← hw, Nat.add_assoc i 2 w, ground.addSubSelfL i (2 + w)]
  have e1 : L - (i + 1) = 1 + w := by
    rw [← hw, hsplit, ground.addSubSelfL (i + 1) (1 + w)]
  have e2 : L - (i + 2) = w := by
    rw [← hw, ground.addSubSelfL (i + 2) w]
  have hsq : D0 ^ 2 = D0 * D0 := by
    rw [Nat.pow_succ D0 1, powOne D0]
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, e2, powAdd D0 2 w, hsq]
    exact monEq [g ^ i, D0 ^ w, D0]
      (Mon.mul (Mon.var 0)
        (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 1)))
      (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
        (Mon.mul (Mon.var 2) (Mon.var 2)))
      (by decide +kernel) (by decide +kernel)
  · rw [e1, e2, powAdd D0 1 w, powOne D0, Nat.pow_succ g i]
    exact monEq [g ^ i, D0 ^ w, D0, g]
      (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 3))
        (Mon.mul (Mon.var 2) (Mon.var 1)))
      (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
        (Mon.mul (Mon.var 3) (Mon.var 2)))
      (by decide +kernel) (by decide +kernel)
  · rw [e2, Nat.pow_succ g (i + 1), Nat.pow_succ g i]
    exact monEq [g ^ i, D0 ^ w, g]
      (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 2)) (Mon.var 2))
        (Mon.var 1))
      (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
        (Mon.mul (Mon.var 2) (Mon.var 2)))
      (by decide +kernel) (by decide +kernel)

/-! The composite comparisons at their counts: the certificate's
tail reads are cross-multiplied natural comparisons. -/

/-- A composite comparison at counted first data is the counts'
cross-multiplied read. -/
private theorem cnatCore {X Y : BPair} {w v : Pos} {a b : Nat}
    (hX : X.oneValue (BPair.ofNat a)) (hY : Y.oneValue (BPair.ofNat b))
    (h : (⟨X, w⟩ : CPair) ≤ ⟨Y, v⟩) :
    ground.posVal v * a ≤ ground.posVal w * b := by
  refine ground.leB_ofNat_cancel ?_
  have h' : X.scale v ≤ Y.scale w := h
  refine ground.leB_congr ?_ ?_ h'
  · exact BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofPos_scale v X))
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos v)) hX)
        (BPair.oneValue_symm (BPair.ofNat_mul (ground.posVal v) a)))
  · exact BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofPos_scale w Y))
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos w)) hY)
        (BPair.oneValue_symm (BPair.ofNat_mul (ground.posVal w) b)))

/-- The depth read's first datum at its count. -/
private theorem sAtNat (en : Pos) (k : Nat) :
    (BPair.ofNat (k * k) * BPair.ofPos en).oneValue
      (BPair.ofNat (k * k * ground.posVal en)) :=
  BPair.oneValue_symm (BPair.ofNat_mul (k * k) (ground.posVal en))

/-- The dominance read at its counts: the margin's join inside the
seam's own square-scale bottom. -/
private theorem cnatDom (A B k : Nat) (en ed : Pos) (X : CPair)
    (hXu : stage.unitC ≤ X) (hX : X ≤ sAt en ed k)
    (h : stage.ofB (BPair.ofNat A) ≤ stage.ofB (BPair.ofNat B) * X) :
    ground.posVal ed * A ≤ B * (k * k * ground.posVal en) := by
  have hmul : stage.ofB (BPair.ofNat B) * X
      ≤ stage.ofB (BPair.ofNat B) * sAt en ed k :=
    stage.mulC_le_mono hXu (cunitLe (ground.unitLeOfNat B))
      (CPair.le_refl _) hX
  have h2 : (⟨BPair.ofNat A, Pos.one⟩ : CPair)
      ≤ ⟨BPair.ofNat B * (BPair.ofNat (k * k) * BPair.ofPos en),
        Pos.one * ed⟩ := CPair.le_trans h hmul
  rw [ground.one_mul ed] at h2
  have hres := cnatCore (BPair.oneValue_refl (BPair.ofNat A))
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat B))
        (sAtNat en k))
      (BPair.oneValue_symm
        (BPair.ofNat_mul B (k * k * ground.posVal en)))) h2
  rw [show ground.posVal Pos.one = 1 from rfl, Nat.one_mul] at hres
  exact hres

/-! The boundary seed tier: the boundary value and the boundary
comparison are each vacant at the scale-free order and floored at
the scale order, so each reads positive at every clearing power. -/

/-- A scale-vacant object floored at the scale order by the
ceiling's priced fold reads positive at every clearing power. -/
private theorem seedFloor {p t : poly.Poly} {e0n : BPair} {e0d : Pos}
    {K J : Nat} (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hvac : (ground.getAt BPair.unit p 0).oneValue BPair.unit)
    (hlen : p.length ≤ K + 2)
    (hlow : lowRead (List.drop 1 p) e0n e0d K)
    (ht : poly.oneValue t p) (htlen : t.length ≤ J + 1) :
    BPair.unit < poly.evalClear t (BPair.ofPos en) ed J := by
  have hdlen : (List.drop 1 p).length ≤ K + 1 := by
    match lenDrop 1 p with
    | Or.inl h0 => rw [h0]; exact Nat.zero_le (K + 1)
    | Or.inr h1 =>
      have h2 : (List.drop 1 p).length + 1 ≤ K + 1 + 1 := by
        rw [h1]
        exact hlen
      exact Nat.le_of_succ_le_succ h2
  have hpos := lowRead_pos (List.drop 1 p) e0n e0d K hlow hdlen en ed he
  have hshift : BPair.unit
      < poly.evalClear (poly.shiftUp 1 (List.drop 1 p))
          (BPair.ofPos en) ed (K + 1) := by
    refine BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (evalClear_shiftUp 1 (List.drop 1 p)
        (BPair.ofPos en) ed (K + 1))) ?_
    exact ground.unitLtMul
      (windowsep.unitLt_bpow (ground.unitLtOfPos en) 1) hpos
  refine posMove (q := poly.shiftUp 1 (List.drop 1 p)) ?_ htlen ?_ hshift
  · exact poly.oneValue_trans ht (ovShiftDrop p hvac)
  · rw [poly.len_shift 1 (List.drop 1 p),
      Nat.add_comm 1 (List.drop 1 p).length]
    exact Nat.succ_le_succ hdlen

/-- The boundary value's positivity at the origin depth. -/
private theorem seedPos (r qN qD : Nat) (e0n : BPair) (e0d : Pos)
    (en ed : Pos) (V : poly.PPoly × poly.PPoly) (K0 Kc Kt Kv : Nat)
    (hsh : profShape V Kv)
    (hu : poly.unitTail (profBase V))
    (hseed : seedRead r qN qD e0n e0d V K0 Kc Kt)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    BPair.unit
      < poly.evalClear (depthPoly V 0) (BPair.ofPos en) ed Kv :=
  seedFloor en ed he (vacHead V hu 0) hseed.1 hseed.2.1
    (poly.oneValue_refl (depthPoly V 0)) (depthPoly_ble hsh 0)

/-- The boundary comparison's read: the first diagonal's multiple of
the boundary value clears the rate's multiple of the first value,
the entry read at the origin depth. -/
private theorem seedRead_read (r qN qD : Nat) (e0n : BPair) (e0d : Pos)
    (en ed : Pos) (V : poly.PPoly × poly.PPoly) (K0 Kc Kt Kv : Nat)
    (hsh : profShape V Kv)
    (hu : poly.unitTail (profBase V))
    (hseed : seedRead r qN qD e0n e0d V K0 Kc Kt)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    wellBond r qD ed
        * poly.evalClear (depthPoly V 1) (BPair.ofPos en) ed Kv
      ≤ wellDiag r qN qD en ed 1
        * poly.evalClear (depthPoly V 0) (BPair.ofPos en) ed Kv := by
  have htlen : (poly.add
      (poly.mul (diagPoly r qN qD 1) (depthPoly V 0))
      (poly.neg (poly.scaleP (BPair.ofNat ((r + 1) * qD))
        (depthPoly V 1)))).length ≤ Kv + 2 + 1 := by
    refine poly.add_len_le _ _ (Kv + 2 + 1) ?_ ?_
    · rw [Nat.add_comm Kv 2]
      exact poly.mul_len_le (diagPoly r qN qD 1) (depthPoly V 0) 2 Kv
        (Nat.le_refl 3) (depthPoly_ble hsh 0)
    · rw [poly.length_neg, poly.length_scaleP]
      exact Nat.le_trans (depthPoly_ble hsh 1)
        (Nat.le_add_right (Kv + 1) 2)
  have hval : BPair.unit < poly.evalClear
      (poly.add (poly.mul (diagPoly r qN qD 1) (depthPoly V 0))
        (poly.neg (poly.scaleP (BPair.ofNat ((r + 1) * qD))
          (depthPoly V 1)))) (BPair.ofPos en) ed (Kv + 2) :=
    seedFloor (p := depthPoly (seedProf V r qN qD) 0) en ed he
      (seedHeadVac V r qN qD hu) hseed.2.2.1 hseed.2.2.2.1
      (poly.oneValue_symm (seedProf_at V r qN qD 0)) htlen
  have hP : (poly.evalClear
      (poly.mul (diagPoly r qN qD 1) (depthPoly V 0))
      (BPair.ofPos en) ed (Kv + 2)).oneValue
      (wellDiag r qN qD en ed 1
        * poly.evalClear (depthPoly V 0) (BPair.ofPos en) ed Kv) := by
    rw [show Kv + 2 = 2 + Kv from Nat.add_comm Kv 2]
    exact poly.evalClear_mul _ _ _ _ 2 Kv (Nat.le_refl 3)
      (depthPoly_ble hsh 0)
  have hN : (poly.evalClear
      (poly.neg (poly.scaleP (BPair.ofNat ((r + 1) * qD))
        (depthPoly V 1))) (BPair.ofPos en) ed (Kv + 2)).oneValue
      (wellBond r qD ed
        * poly.evalClear (depthPoly V 1) (BPair.ofPos en) ed Kv).swap := by
    refine BPair.oneValue_trans (poly.evalClear_neg _ _ _ _) ?_
    refine ground.swap_congr ?_
    refine BPair.oneValue_trans (poly.evalClear_scaleP _ _ _ _ _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (evalClear_up2 (depthPoly V 1) en ed Kv
          (depthPoly_ble hsh 1))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.mul_assoc (BPair.ofNat ((r + 1) * qD)) (BPair.ofPos ed),
      ← BPair.mul_assoc (BPair.ofNat ((r + 1) * qD) * BPair.ofPos ed)
        (BPair.ofPos ed)]
    rfl
  exact ground.leB_of_unit_add
    (ground.leB_congr_right
      (BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
        (BPair.add_congr hP hN))
      (ground.leB_of_lt hval))

/-- The boundary termwise comparison at the origin depth: the
stripped comparison object vacant at the scale-free order and
floored at the scale order reads clause (i)'s comparison there, the
scale factor withdrawn twice. -/
private theorem seedTerm (r qN qD : Nat) (e0n : BPair) (e0d : Pos)
    (en ed : Pos) (V : poly.PPoly × poly.PPoly) (K0 Kc Kt Kv : Nat)
    (hsh : profShape V Kv)
    (hu : poly.unitTail (profBase V))
    (hseed : seedRead r qN qD e0n e0d V K0 Kc Kt)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    wellBond r qD ed
        * (poly.evalClear (depthPoly V 0) (BPair.ofPos en) ed Kv
          + poly.evalClear (depthPoly V 2) (BPair.ofPos en) ed Kv)
      ≤ wellDiag r qN qD en ed 1
        * poly.evalClear (depthPoly V 1) (BPair.ofPos en) ed Kv := by
  have hstrip : BPair.unit < poly.evalClear
      (depthPoly (profStrip (termProf V r qN qD)) 0)
      (BPair.ofPos en) ed (Kt + 1) :=
    seedFloor en ed he (stripHeadVac V r qN qD hu) hseed.2.2.2.2.1
      hseed.2.2.2.2.2
      (poly.oneValue_refl (depthPoly (profStrip (termProf V r qN qD)) 0))
      hseed.2.2.2.2.1
  have hshift : BPair.unit < poly.evalClear
      (poly.shiftUp 1 (depthPoly (profStrip (termProf V r qN qD)) 0))
      (BPair.ofPos en) ed (Kt + 2) := by
    refine BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (evalClear_shiftUp 1
        (depthPoly (profStrip (termProf V r qN qD)) 0)
        (BPair.ofPos en) ed (Kt + 2))) ?_
    exact ground.unitLtMul
      (windowsep.unitLt_bpow (ground.unitLtOfPos en) 1) hstrip
  refine termRead_read hsh (ground.leB_of_lt (posMove ?_ ?_ ?_ hshift))
  · exact poly.oneValue_trans
      (poly.oneValue_symm (depthPoly_termProf V r qN qD 0))
      (depthPoly_profStrip (termProf V r qN qD) 0
        (termProf_vac V r qN qD))
  · exact termPoly_len hsh r qN qD 0
  · rw [poly.len_shift 1 (depthPoly (profStrip (termProf V r qN qD)) 0),
      Nat.add_comm 1
        (depthPoly (profStrip (termProf V r qN qD)) 0).length]
    exact Nat.succ_le_succ hseed.2.2.2.2.1

/-- The margin read at its counts: the allowance's squared price at
the seam's top inside the margin's own. -/
private theorem cnatWs (A B k : Nat) (en ed : Pos) (X : CPair)
    (hX : sAt en ed k ≤ X)
    (h : stage.ofB (BPair.ofNat A) * X ≤ stage.ofB (BPair.ofNat B)) :
    A * (k * k * ground.posVal en) ≤ ground.posVal ed * B := by
  have hmul : stage.ofB (BPair.ofNat A) * sAt en ed k
      ≤ stage.ofB (BPair.ofNat A) * X :=
    stage.mulC_le_mono (cunitLe (ground.unitLeMul (ground.unitLeOfNat (k * k))
        (ground.leB_of_lt (ground.unitLtOfPos en))))
      (cunitLe (ground.unitLeOfNat A)) (CPair.le_refl _) hX
  have h2 : (⟨BPair.ofNat A * (BPair.ofNat (k * k) * BPair.ofPos en),
      Pos.one * ed⟩ : CPair) ≤ ⟨BPair.ofNat B, Pos.one⟩ :=
    CPair.le_trans hmul h
  rw [ground.one_mul ed] at h2
  have hres := cnatCore
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat A)) (sAtNat en k))
      (BPair.oneValue_symm
        (BPair.ofNat_mul A (k * k * ground.posVal en))))
    (BPair.oneValue_refl (BPair.ofNat B)) h2
  rw [show ground.posVal Pos.one = 1 from rfl, Nat.one_mul] at hres
  exact hres

/-- The scale pair sits inside the cleared ceiling. -/
private theorem cleCeil (en ed : Pos) (e0n : BPair) (e0d : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    (⟨BPair.ofPos en, ed⟩ : CPair) ≤ ⟨e0n, e0d⟩ := by
  show (BPair.ofPos en).scale e0d ≤ e0n.scale ed
  refine ground.leB_congr (BPair.ofPos_scale e0d (BPair.ofPos en))
    (BPair.ofPos_scale ed e0n) ?_
  refine ground.leB_congr
    (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos en) (BPair.ofPos e0d)))
    (BPair.oneValue_of_eq (BPair.mul_comm e0n (BPair.ofPos ed))) he

/-- The half cap at its counts: the allowance's cleared read of the
depth step at the seam depth is at most half the clearing's scale,
the comparison read back through the squares. -/
private theorem cnatHalf (alN alD k : Nat) (en ed : Pos)
    (b c : CPair) (hb : sAt en ed k ≤ b)
    (hc : (⟨BPair.ofPos en, ed⟩ : CPair) ≤ c)
    (h : stage.ofB (BPair.ofNat (36 * (alN * alN))) * (b * c)
      ≤ stage.ofB (BPair.ofNat (alD * alD))) :
    6 * (alN * k * ground.posVal en) ≤ alD * ground.posVal ed := by
  have hEu : BPair.unit ≤ BPair.ofPos en :=
    ground.leB_of_lt (ground.unitLtOfPos en)
  have hz : stage.unitC
      ≤ sAt en ed k * (⟨BPair.ofPos en, ed⟩ : CPair) :=
    cunitLe (ground.unitLeMul
      (ground.unitLeMul (ground.unitLeOfNat (k * k)) hEu) hEu)
  have hinner : sAt en ed k * (⟨BPair.ofPos en, ed⟩ : CPair) ≤ b * c :=
    stage.mulC_le_mono (cunitLe hEu)
      (CPair.le_trans (sAt_unit en ed k) hb) hb hc
  have hmul : stage.ofB (BPair.ofNat (36 * (alN * alN)))
        * (sAt en ed k * (⟨BPair.ofPos en, ed⟩ : CPair))
      ≤ stage.ofB (BPair.ofNat (36 * (alN * alN))) * (b * c) :=
    stage.mulC_le_mono hz (cunitLe (ground.unitLeOfNat (36 * (alN * alN))))
      (CPair.le_refl (stage.ofB (BPair.ofNat (36 * (alN * alN))))) hinner
  have h2 : (⟨BPair.ofNat (36 * (alN * alN))
        * (BPair.ofNat (k * k) * BPair.ofPos en * BPair.ofPos en),
      Pos.one * (ed * ed)⟩ : CPair)
      ≤ ⟨BPair.ofNat (alD * alD), Pos.one⟩ := CPair.le_trans hmul h
  rw [ground.one_mul (ed * ed)] at h2
  have hres := cnatCore
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat (36 * (alN * alN))))
        (collect3 (k * k) (ground.posVal en) (ground.posVal en)))
      (BPair.oneValue_symm (BPair.ofNat_mul (36 * (alN * alN))
        (k * k * ground.posVal en * ground.posVal en))))
    (BPair.oneValue_refl (BPair.ofNat (alD * alD))) h2
  rw [show ground.posVal Pos.one = 1 from rfl, Nat.one_mul,
    ground.val_mul ed ed] at hres
  refine ground.leOfSqLe ?_
  refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans hres (Nat.le_of_eq ?_))
  · exact monEq [alN, k, ground.posVal en]
      (Mon.mul
        (Mon.mul (Mon.cst 6)
          (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))
        (Mon.mul (Mon.cst 6)
          (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))))
      (Mon.mul (Mon.mul (Mon.cst 36) (Mon.mul (Mon.var 0) (Mon.var 0)))
        (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.var 2))
          (Mon.var 2)))
      (by decide +kernel) (by decide +kernel)
  · exact monEq [alD, ground.posVal ed]
      (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1))
        (Mon.mul (Mon.var 0) (Mon.var 0)))
      (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1))
        (Mon.mul (Mon.var 0) (Mon.var 1)))
      (by decide +kernel) (by decide +kernel)

/-! The final seam's slope read: the profile's shift joined to the
allowance's multiple of the step read clears the profile, so the
gap's multiple of the standing value sits inside the clearing's
multiple of the arriving one. -/

/-- The depth step's own cleared evaluation at the scale order. -/
private theorem stepEval (t : Nat) (en ed : Pos) :
    (poly.evalClear [BPair.unit, BPair.ofNat t] (BPair.ofPos en) ed 1).oneValue
      (BPair.ofNat t * BPair.ofPos en) := by
  refine BPair.oneValue_trans
    (poly.evalClear_read [BPair.unit, BPair.ofNat t] (BPair.ofPos en) ed 1) ?_
  show (BPair.unit * ground.bpow (BPair.ofPos en) 0
        * ground.bpow (BPair.ofPos ed) 1
      + (BPair.ofNat t * ground.bpow (BPair.ofPos en) 1
          * ground.bpow (BPair.ofPos ed) 0 + BPair.unit)).oneValue _
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans (BPair.mul_congr_left (BPair.unit_mul _))
        (BPair.unit_mul _))
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans
            (BPair.mul_congr_left
              (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat t))
                (bpow_one_read (BPair.ofPos en))))
            (BPair.mul_ofNat_one (BPair.ofNat t * BPair.ofPos en)))
          (BPair.oneValue_refl BPair.unit))
        (BPair.add_unit _))) ?_
  exact BPair.unit_add _

/-- The slope read at a depth inside the final seam's box: the
clearing's multiple of the standing value sits inside the
allowance's multiple of it joined to the clearing's multiple of the
arriving value. -/
private theorem slopeRead (V : poly.PPoly × poly.PPoly) (alN alD : Nat)
    (e0n : BPair) (e0d : Pos) (Cf : GradCert) (en ed : Pos) (Kv m : Nat)
    (hgr : gradRead (slopeProf V alN alD) e0n e0d Cf)
    (hsh : profShape V Kv)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hlo : Cf.lo ≤ sAt en ed m) (hhi : sAt en ed m ≤ Cf.hi) :
    BPair.ofNat (alD * ground.posVal ed)
        * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv
      ≤ BPair.ofNat (alN * (2 * m + 1) * ground.posVal en)
          * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv
        + BPair.ofNat (alD * ground.posVal ed)
          * poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed Kv := by
  have hlenA : (poly.scaleP (BPair.ofNat alD)
      (poly.add (depthPoly V (m + 1)) (poly.neg (depthPoly V m)))).length
      ≤ Kv + 1 + 1 := by
    rw [poly.length_scaleP]
    exact Nat.le_succ_of_le (poly.add_len_le _ _ (Kv + 1)
      (depthPoly_ble hsh (m + 1))
      (by rw [poly.length_neg]; exact depthPoly_ble hsh m))
  have hlenB : (poly.scaleP (BPair.ofNat alN)
      (poly.mul [BPair.unit, BPair.ofNat (2 * m + 1)]
        (depthPoly V m))).length ≤ Kv + 1 + 1 := by
    rw [poly.length_scaleP,
      show Kv + 1 + 1 = 1 + Kv + 1 from by rw [Nat.add_comm Kv 1]]
    exact poly.mul_len_le [BPair.unit, BPair.ofNat (2 * m + 1)]
      (depthPoly V m) 1 Kv (Nat.le_refl 2) (depthPoly_ble hsh m)
  have hP : BPair.unit < poly.evalClear
      (poly.add
        (poly.scaleP (BPair.ofNat alD)
          (poly.add (depthPoly V (m + 1)) (poly.neg (depthPoly V m))))
        (poly.scaleP (BPair.ofNat alN)
          (poly.mul [BPair.unit, BPair.ofNat (2 * m + 1)]
            (depthPoly V m))))
      (BPair.ofPos en) ed (Kv + 1) := by
    refine posMove (q := depthPoly (slopeProf V alN alD) m) ?_
      (poly.add_len_le _ _ (Kv + 1 + 1) hlenA hlenB)
      (depthPoly_ble hgr.1 m) ?_
    · exact poly.oneValue_symm (slopeProf_at V alN alD m)
    · exact gradRead_pos (slopeProf V alN alD) e0n e0d Cf hgr m en ed he
        hlo hhi
  have hA : (poly.evalClear
      (poly.scaleP (BPair.ofNat alD)
        (poly.add (depthPoly V (m + 1)) (poly.neg (depthPoly V m))))
      (BPair.ofPos en) ed (Kv + 1)).oneValue
      (BPair.ofNat (alD * ground.posVal ed)
          * poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed Kv
        + (BPair.ofNat (alD * ground.posVal ed)
          * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv).swap) := by
    refine BPair.oneValue_trans (poly.evalClear_scaleP _ _ _ _ _) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat alD))
        (BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
          (BPair.add_congr (evalClear_up _ en ed Kv (depthPoly_ble hsh (m + 1)))
            (BPair.oneValue_trans (poly.evalClear_neg _ _ _ _)
              (ground.swap_congr (evalClear_up _ en ed Kv (depthPoly_ble hsh m))))))) ?_
    have hcoef : (BPair.ofNat alD * BPair.ofPos ed).oneValue
        (BPair.ofNat (alD * ground.posVal ed)) :=
      BPair.oneValue_symm (BPair.ofNat_mul alD (ground.posVal ed))
    rw [BPair.left_distrib (BPair.ofNat alD)
        (BPair.ofPos ed
          * poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed Kv)
        (BPair.ofPos ed
          * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv).swap,
      BPair.mul_swap (BPair.ofNat alD)
        (BPair.ofPos ed
          * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv),
      ← BPair.mul_assoc (BPair.ofNat alD) (BPair.ofPos ed)
        (poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed Kv),
      ← BPair.mul_assoc (BPair.ofNat alD) (BPair.ofPos ed)
        (poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv)]
    exact BPair.add_congr (BPair.mul_congr_left hcoef)
      (ground.swap_congr (BPair.mul_congr_left hcoef))
  have hB : (poly.evalClear
      (poly.scaleP (BPair.ofNat alN)
        (poly.mul [BPair.unit, BPair.ofNat (2 * m + 1)] (depthPoly V m)))
      (BPair.ofPos en) ed (Kv + 1)).oneValue
      (BPair.ofNat (alN * (2 * m + 1) * ground.posVal en)
        * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv) := by
    refine BPair.oneValue_trans (poly.evalClear_scaleP _ _ _ _ _) ?_
    rw [show Kv + 1 = 1 + Kv from Nat.add_comm Kv 1]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat alN))
        (BPair.oneValue_trans
          (poly.evalClear_mul _ _ (BPair.ofPos en) ed 1 Kv (Nat.le_refl 2)
            (depthPoly_ble hsh m))
          (BPair.mul_congr_left (stepEval (2 * m + 1) en ed)))) ?_
    rw [← BPair.mul_assoc (BPair.ofNat alN)
      (BPair.ofNat (2 * m + 1) * BPair.ofPos en)
      (poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv),
      ← BPair.mul_assoc (BPair.ofNat alN) (BPair.ofNat (2 * m + 1))
        (BPair.ofPos en)]
    refine BPair.mul_congr_left ?_
    exact BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.ofNat_mul (alN * (2 * m + 1)) (ground.posVal en))
        (BPair.mul_congr_left (BPair.ofNat_mul alN (2 * m + 1))))
  refine ground.leB_of_unit_add
    (U := BPair.ofNat (alN * (2 * m + 1) * ground.posVal en)
        * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv
      + BPair.ofNat (alD * ground.posVal ed)
        * poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed Kv)
    (V := (BPair.ofNat (alD * ground.posVal ed)
      * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv).swap)
    (ground.leB_congr_right ?_ (ground.leB_of_lt hP))
  refine BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _) ?_
  refine BPair.oneValue_trans (BPair.add_congr hA hB) ?_
  rw [BPair.add_right_comm
      (BPair.ofNat (alD * ground.posVal ed)
        * poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed Kv)
      (BPair.ofNat (alD * ground.posVal ed)
        * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv).swap
      (BPair.ofNat (alN * (2 * m + 1) * ground.posVal en)
        * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv),
    BPair.add_comm
      (BPair.ofNat (alD * ground.posVal ed)
        * poly.evalClear (depthPoly V (m + 1)) (BPair.ofPos en) ed Kv)
      (BPair.ofNat (alN * (2 * m + 1) * ground.posVal en)
        * poly.evalClear (depthPoly V m) (BPair.ofPos en) ed Kv)]
  exact BPair.oneValue_refl _

/-- An occupied count's powers are occupied. -/
private theorem powPos {a : Nat} (h : 1 ≤ a) : ∀ k, 1 ≤ a ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => by
    rw [Nat.pow_succ]
    exact Nat.le_trans (Nat.le_of_eq (Nat.one_mul 1).symm)
      (Nat.mul_le_mul (powPos h k) h)

/-- The geometric list's member at a depth beyond the seam reads the
gap's own power against the clearing's. -/
private theorem geoAt (g D0 k0 L i : Nat) :
    geoU g D0 k0 L (k0 + i) = BPair.ofNat (g ^ i * D0 ^ (L - i)) := by
  show BPair.ofNat (g ^ (k0 + i - k0) * D0 ^ (L - (k0 + i - k0))) = _
  rw [ground.addSubSelfL k0 i]

/-- Every geometric member is occupied at an occupied gap and
clearing. -/
private theorem geoPos {g D0 : Nat} (hg : 1 ≤ g) (hD : 1 ≤ D0)
    (k0 L m : Nat) : BPair.unit < geoU g D0 k0 L m :=
  ground.unitLtNat (Nat.le_trans (Nat.le_of_eq (Nat.one_mul 1).symm)
    (Nat.mul_le_mul (powPos hg (m - k0)) (powPos hD (L - (m - k0)))))

/-- The geometric list's termwise comparison at the member line, at
every depth of the tail. -/
private theorem geoTermMem (r qcN qcD ws alN alD A B k0 L i g : Nat)
    (en ed : Pos)
    (hgX : g + alN * (2 * k0 + 1) * ground.posVal en
      = alD * ground.posVal ed)
    (hws : 18 * ((r + 1) * qcD) * (alN * alN) * (k0 * k0)
        * ground.posVal en
      ≤ ws * (alD * alD) * ground.posVal ed)
    (hhalf : 6 * (alN * k0 * ground.posVal en) ≤ alD * ground.posVal ed)
    (hk0 : 1 ≤ k0)
    (hdom : ((r + 1) * qcN + ws) * ground.posVal ed
      ≤ 4 * qcD * (k0 * k0) * ground.posVal en)
    (hi : i + 2 ≤ L) (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (hg : 1 ≤ g) (hD : 1 ≤ alD * ground.posVal ed) :
    wellBond r B ed
        * (geoU g (alD * ground.posVal ed) k0 L (k0 + i)
          + geoU g (alD * ground.posVal ed) k0 L (k0 + i + 2))
      ≤ wellDiag r A B en ed (k0 + i + 1)
        * geoU g (alD * ground.posVal ed) k0 L (k0 + i + 1) := by
  obtain ⟨e0, e1, e2⟩ := geoTriple g (alD * ground.posVal ed) L i hi
  have g1 : geoU g (alD * ground.posVal ed) k0 L (k0 + i + 1)
      = BPair.ofNat (g ^ (i + 1)
        * (alD * ground.posVal ed) ^ (L - (i + 1))) :=
    geoAt g (alD * ground.posVal ed) k0 L (i + 1)
  have g2 : geoU g (alD * ground.posVal ed) k0 L (k0 + i + 2)
      = BPair.ofNat (g ^ (i + 2)
        * (alD * ground.posVal ed) ^ (L - (i + 2))) :=
    geoAt g (alD * ground.posVal ed) k0 L (i + 2)
  rw [geoAt g (alD * ground.posVal ed) k0 L i, g1, g2, e0, e1, e2]
  refine rateStep r qcN qcD A B en ed (k0 + i + 1) _ _ hqcD hrate
    (ground.leB_of_lt (ground.unitLtNat
      (Nat.le_trans (Nat.le_of_eq (Nat.one_mul 1).symm)
        (Nat.mul_le_mul
          (Nat.le_trans (Nat.le_of_eq (Nat.one_mul 1).symm)
            (Nat.mul_le_mul (powPos hg i) (powPos hD (L - (i + 2)))))
          (Nat.le_trans (Nat.le_of_eq (Nat.one_mul 1).symm)
            (Nat.mul_le_mul hg hD)))))) ?_
  refine geomTermCap r qcN qcD ws alN alD k0 (k0 + i + 1) g
    (g ^ i * (alD * ground.posVal ed) ^ (L - (i + 2))) en ed hgX hws hhalf
    hk0 ?_
  refine Nat.le_trans hdom ?_
  refine Nat.mul_le_mul_right (ground.posVal en) ?_
  refine Nat.mul_le_mul_left (4 * qcD) ?_
  exact Nat.mul_le_mul (Nat.le_add_right k0 (i + 1))
    (Nat.le_add_right k0 (i + 1))

/-- The tail's run: the entry read at the last profile crosses to
the geometric list at the slope read, and the geometric list clears
the pivots to the head's end. -/
private theorem tailRun (r qcN qcD ws alN alD A B n k0 g : Nat)
    (en ed : Pos) (D uP : Nat → BPair)
    (hβ : BPair.unit < wellBond r B ed)
    (hrec : ∀ m, (D (m + 2)
        + wellBond r B ed * wellBond r B ed * D m).oneValue
      (wellDiag r A B en ed (m + 2) * D (m + 1)))
    (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (hgX : g + alN * (2 * k0 + 1) * ground.posVal en
      = alD * ground.posVal ed)
    (hws : 18 * ((r + 1) * qcD) * (alN * alN) * (k0 * k0)
        * ground.posVal en
      ≤ ws * (alD * alD) * ground.posVal ed)
    (hhalf : 6 * (alN * k0 * ground.posVal en) ≤ alD * ground.posVal ed)
    (hk0 : 1 ≤ k0)
    (hdom : ((r + 1) * qcN + ws) * ground.posVal ed
      ≤ 4 * qcD * (k0 * k0) * ground.posVal en)
    (hg : 1 ≤ g) (hD : 1 ≤ alD * ground.posVal ed)
    (h0 : BPair.unit < D k0) (hP0 : BPair.unit < uP k0)
    (hslope : BPair.ofNat g * uP k0
      ≤ BPair.ofNat (alD * ground.posVal ed) * uP (k0 + 1))
    (hent : wellBond r B ed * (D k0 * uP (k0 + 1)) ≤ D (k0 + 1) * uP k0) :
    ∀ j, k0 ≤ j → j ≤ n → BPair.unit < D (j + 1) := by
  have hDD : 1 ≤ alD * ground.posVal ed := hD
  have hL : (alD * ground.posVal ed) ^ (n + 3 - 1)
      * (alD * ground.posVal ed) = (alD * ground.posVal ed) ^ (n + 3) := by
    rw [show n + 3 - 1 = n + 2 from rfl, ← Nat.pow_succ]
  have hg0 : geoU g (alD * ground.posVal ed) k0 (n + 3) k0
      = BPair.ofNat ((alD * ground.posVal ed) ^ (n + 3)) := by
    have h := geoAt g (alD * ground.posVal ed) k0 (n + 3) 0
    rw [Nat.pow_zero, Nat.sub_zero, Nat.one_mul] at h
    exact h
  have hg1 : geoU g (alD * ground.posVal ed) k0 (n + 3) (k0 + 1)
      = BPair.ofNat (g * (alD * ground.posVal ed) ^ (n + 3 - 1)) := by
    have h := geoAt g (alD * ground.posVal ed) k0 (n + 3) 1
    rw [powOne] at h
    exact h
  have hcross : uP k0 * geoU g (alD * ground.posVal ed) k0 (n + 3) (k0 + 1)
      ≤ uP (k0 + 1) * geoU g (alD * ground.posVal ed) k0 (n + 3) k0 := by
    rw [hg0, hg1]
    have hstep := ground.leB_mulR
      (ground.unitLeOfNat ((alD * ground.posVal ed) ^ (n + 3 - 1))) hslope
    refine ground.leB_congr ?_ ?_ hstep
    · refine BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.mul_assoc
            (BPair.ofNat ((alD * ground.posVal ed) ^ (n + 3 - 1)))
            (BPair.ofNat g) (uP k0)).symm) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.oneValue_symm
            (BPair.ofNat_mul ((alD * ground.posVal ed) ^ (n + 3 - 1)) g))) ?_
      rw [Nat.mul_comm ((alD * ground.posVal ed) ^ (n + 3 - 1)) g]
      exact BPair.oneValue_of_eq
        (BPair.mul_comm (BPair.ofNat (g * (alD * ground.posVal ed) ^ (n + 3 - 1)))
          (uP k0))
    · refine BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.mul_assoc
            (BPair.ofNat ((alD * ground.posVal ed) ^ (n + 3 - 1)))
            (BPair.ofNat (alD * ground.posVal ed)) (uP (k0 + 1))).symm) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.oneValue_symm
            (BPair.ofNat_mul ((alD * ground.posVal ed) ^ (n + 3 - 1))
              (alD * ground.posVal ed)))) ?_
      rw [hL]
      exact BPair.oneValue_of_eq
        (BPair.mul_comm (BPair.ofNat ((alD * ground.posVal ed) ^ (n + 3)))
          (uP (k0 + 1)))
  have hentGeo : wellBond r B ed
      * (D k0 * geoU g (alD * ground.posVal ed) k0 (n + 3) (k0 + 1))
      ≤ D (k0 + 1) * geoU g (alD * ground.posVal ed) k0 (n + 3) k0 :=
    crossTransfer (ground.unitLeMul (ground.leB_of_lt hβ) (ground.leB_of_lt h0))
      hP0 (ground.leB_of_lt (geoPos hg hDD k0 (n + 3) k0)) hcross hent
  have hrun := runD r A B en ed D (geoU g (alD * ground.posVal ed) k0 (n + 3))
    hβ hrec k0 k0 n (Nat.le_succ k0)
    (fun i _ => geoPos hg hDD k0 (n + 3) (k0 + i))
    (fun i hi => geoTermMem r qcN qcD ws alN alD A B k0 (n + 3) i g en ed
      hgX hws hhalf hk0 hdom
      (Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.le_of_lt hi)))
        (Nat.le_add_right (n + 2) 1))
      hqcD hrate hg hDD)
    h0 hentGeo
  intro j hkj hjn
  obtain ⟨w, hw⟩ := Nat.le.dest hkj
  rw [← hw]
  exact (hrun w (Nat.le_trans (Nat.le_of_eq (ground.addSubSelfL k0 w).symm)
    (Nat.le_trans (Nat.sub_le (k0 + w) k0)
      (Nat.le_trans (Nat.le_of_eq hw) hjn)))).1

/-! The handover depth: the first depth of a segment's term box at
or beyond the standing one, found by the bounded walk. -/

/-- The first depth at or beyond a stated one whose square scale
reaches a stated bottom, the bounded first-hit search's instance
at the square-scale read. -/
private abbrev firstGE (en ed : Pos) (LO : CPair) : Nat → Nat → Nat :=
  ground.firstAt (fun m => LO ≤ sAt en ed m)

/-- A chained list's last segment sits at or above the standing
segment's bottom, the seams' bottoms non-decreasing. -/
private theorem chainBot (r qN qD : Nat) (e0n : BPair) (e0d : Pos) :
    ∀ (l : List (SeamCert × SegCert)) (P : SegCert),
      chainSegs r qN qD e0n e0d P.jet P.term.lo P.term.hi l →
      P.term.lo ≤ (lastSeg P l).term.lo
  | [], _, _ => CPair.le_refl _
  | (_, S) :: t, _, h =>
    CPair.le_trans h.1.2.2.2.2.2.2 (chainBot r qN qD e0n e0d t S h.2.2)

/-- The last segment's run: the chain reaches the final seam's
depth, the slope read crosses to the geometric list and the tail
clears the pivots to the head's end. -/
private theorem lastRun (r qcN qcD ws alN alD A B n k0 g : Nat)
    (e0n : BPair) (e0d : Pos) (en ed : Pos) (D : Nat → BPair)
    (Cf : SeamCert) (P : SegCert)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hβ : BPair.unit < wellBond r B ed)
    (hrec : ∀ m, (D (m + 2)
        + wellBond r B ed * wellBond r B ed * D m).oneValue
      (wellDiag r A B en ed (m + 2) * D (m + 1)))
    (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (hgX : g + alN * (2 * k0 + 1) * ground.posVal en
      = alD * ground.posVal ed)
    (hws : 18 * ((r + 1) * qcD) * (alN * alN) * (k0 * k0)
        * ground.posVal en
      ≤ ws * (alD * alD) * ground.posVal ed)
    (hhalf : 6 * (alN * k0 * ground.posVal en) ≤ alD * ground.posVal ed)
    (hk0pos : 1 ≤ k0)
    (hdom : ((r + 1) * qcN + ws) * ground.posVal ed
      ≤ 4 * qcD * (k0 * k0) * ground.posVal en)
    (hg : 1 ≤ g) (hDD : 1 ≤ alD * ground.posVal ed)
    (hk0lo : Cf.cert.lo ≤ sAt en ed k0)
    (hk0b : sAt en ed k0 ≤ Cf.b) (hbhi : Cf.b ≤ Cf.cert.hi)
    (hP : segRead r qcN qcD e0n e0d P)
    (hgrF : gradRead (slopeProf P.jet alN alD) e0n e0d Cf.cert)
    (hbhi2 : Cf.b ≤ P.term.hi)
    (k : Nat) (hPk : P.term.lo ≤ sAt en ed k) (hkk0 : k ≤ k0)
    (h0 : BPair.unit < D k)
    (hent : wellBond r B ed
        * (D k * poly.evalClear (depthPoly P.jet (k + 1))
            (BPair.ofPos en) ed P.pos.K)
      ≤ D (k + 1) * poly.evalClear (depthPoly P.jet k)
          (BPair.ofPos en) ed P.pos.K) :
    ∀ j, k ≤ j → j ≤ n → BPair.unit < D (j + 1) := by
  have hlen : k + (k0 - k) = k0 := ground.natAddSubCancel hkk0
  have hk0hi : sAt en ed k0 ≤ P.term.hi := CPair.le_trans hk0b hbhi2
  have hhiA : sAt en ed (k + (k0 - k)) ≤ P.term.hi := by
    rw [hlen]
    exact hk0hi
  have hposP := segStagePos r qcN qcD e0n e0d en ed P hP he k (k0 - k)
    hPk hhiA
  have hrun := runD r A B en ed D
    (fun m => poly.evalClear (depthPoly P.jet m) (BPair.ofPos en) ed P.pos.K)
    hβ hrec k k (k0 - k) (Nat.le_succ k) hposP
    (segStageTerm r qcN qcD A B e0n e0d en ed P hP he hqcD hrate k (k0 - k)
      hPk hhiA)
    h0 hent
  have hDat : ∀ tt, k ≤ tt → tt ≤ k0 → BPair.unit < D tt := by
    intro tt hktt httk0
    match Nat.lt_or_ge k tt with
    | Or.inr hge =>
      rw [Nat.le_antisymm hge hktt]
      exact h0
    | Or.inl hlt =>
      obtain ⟨w, hw⟩ := Nat.le.dest hlt
      have heq : k + (w + 1) = tt := by
        rw [← Nat.add_assoc k w 1, Nat.add_right_comm k w 1]
        exact hw
      have hwle : w ≤ k0 - k := by
        refine Nat.le_trans (Nat.le_add_right w 1) (ground.leCancelL k ?_)
        rw [hlen, heq]
        exact httk0
      have hstep := (hrun w hwle).1
      rw [show k + w + 1 = tt from by
        rw [← heq, Nat.add_assoc k w 1]] at hstep
      exact hstep
  have hentK0 : wellBond r B ed
      * (D k0 * poly.evalClear (depthPoly P.jet (k0 + 1))
          (BPair.ofPos en) ed P.pos.K)
      ≤ D (k0 + 1) * poly.evalClear (depthPoly P.jet k0)
          (BPair.ofPos en) ed P.pos.K := by
    have hstep := (hrun (k0 - k) (Nat.le_refl (k0 - k))).2
    rw [hlen] at hstep
    exact hstep
  have hslopeRaw := slopeRead P.jet alN alD e0n e0d Cf.cert en ed P.pos.K k0
    hgrF hP.1.1 he hk0lo (CPair.le_trans hk0b hbhi)
  have hslope : BPair.ofNat g
        * poly.evalClear (depthPoly P.jet k0) (BPair.ofPos en) ed P.pos.K
      ≤ BPair.ofNat (alD * ground.posVal ed)
        * poly.evalClear (depthPoly P.jet (k0 + 1))
            (BPair.ofPos en) ed P.pos.K := by
    refine ground.leB_cancelL
      (x := BPair.ofNat (alN * (2 * k0 + 1) * ground.posVal en)
        * poly.evalClear (depthPoly P.jet k0) (BPair.ofPos en) ed P.pos.K) ?_
    refine ground.leB_congr_left ?_ hslopeRaw
    rw [← hgX, Nat.add_comm g (alN * (2 * k0 + 1) * ground.posVal en)]
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.ofNat_add (alN * (2 * k0 + 1) * ground.posVal en) g)) ?_
    exact BPair.oneValue_of_eq
      (BPair.right_distrib
        (BPair.ofNat (alN * (2 * k0 + 1) * ground.posVal en))
        (BPair.ofNat g)
        (poly.evalClear (depthPoly P.jet k0) (BPair.ofPos en) ed P.pos.K))
  have htail := tailRun r qcN qcD ws alN alD A B n k0 g en ed D
    (fun m => poly.evalClear (depthPoly P.jet m) (BPair.ofPos en) ed P.pos.K)
    hβ hrec hqcD hrate hgX hws hhalf hk0pos hdom hg hDD
    (hDat k0 hkk0 (Nat.le_refl k0))
    (segPos r qcN qcD e0n e0d P hP en ed he k0
      (CPair.le_trans hP.2.2.1
        (CPair.le_trans hPk (sAt_mono en ed hkk0)))
      (CPair.le_trans (sAt_mono en ed (Nat.le_add_right k0 2))
        (segTwoStep r qcN qcD e0n e0d P hP en ed he k0 hk0hi)))
    hslope hentK0
  intro j hkj hjn
  match Nat.lt_or_ge j k0 with
  | Or.inl hlt => exact hDat (j + 1) (Nat.le_succ_of_le hkj) hlt
  | Or.inr hge => exact htail j hge hjn

/-- The post tier's run: from the crossing's covering segment the
swapped chain crosses each seam at its own first depth and reaches
the final seam, the handover depths non-decreasing along the
chain. -/
private theorem postRun (r qcN qcD ws alN alD A B n k0 g : Nat)
    (e0n : BPair) (e0d : Pos) (en ed : Pos) (D : Nat → BPair)
    (Cf : SeamCert)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hβ : BPair.unit < wellBond r B ed)
    (hrec : ∀ m, (D (m + 2)
        + wellBond r B ed * wellBond r B ed * D m).oneValue
      (wellDiag r A B en ed (m + 2) * D (m + 1)))
    (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (hgX : g + alN * (2 * k0 + 1) * ground.posVal en
      = alD * ground.posVal ed)
    (hws : 18 * ((r + 1) * qcD) * (alN * alN) * (k0 * k0)
        * ground.posVal en
      ≤ ws * (alD * alD) * ground.posVal ed)
    (hhalf : 6 * (alN * k0 * ground.posVal en) ≤ alD * ground.posVal ed)
    (hk0pos : 1 ≤ k0)
    (hdom : ((r + 1) * qcN + ws) * ground.posVal ed
      ≤ 4 * qcD * (k0 * k0) * ground.posVal en)
    (hg : 1 ≤ g) (hDD : 1 ≤ alD * ground.posVal ed)
    (hk0lo : Cf.cert.lo ≤ sAt en ed k0)
    (hk0b : sAt en ed k0 ≤ Cf.b) (hbhi : Cf.b ≤ Cf.cert.hi) :
    ∀ (l : List (SeamCert × SegCert)) (P : SegCert) (k : Nat),
      chainSegs r qcN qcD e0n e0d P.jet P.term.lo P.term.hi l →
      segRead r qcN qcD e0n e0d P →
      gradRead (slopeProf (lastSeg P l).jet alN alD) e0n e0d Cf.cert →
      (lastSeg P l).term.lo ≤ Cf.cert.lo →
      Cf.b ≤ (lastSeg P l).term.hi →
      P.term.lo ≤ sAt en ed k →
      (∀ M' S' t', l = (M', S') :: t' →
        ∀ m, m + 1 ≤ k → sAt en ed m ≤ S'.term.lo) →
      1 ≤ k → k ≤ k0 →
      BPair.unit < D k →
      wellBond r B ed
          * (D k * poly.evalClear (depthPoly P.jet (k + 1))
              (BPair.ofPos en) ed P.pos.K)
        ≤ D (k + 1) * poly.evalClear (depthPoly P.jet k)
            (BPair.ofPos en) ed P.pos.K →
      ∀ j, k ≤ j → j ≤ n → BPair.unit < D (j + 1) := by
  intro l
  induction l with
  | nil =>
    intro P k _ hP hgrF _ hbhi2 hPk _ _ hkk0 h0 hent
    exact lastRun r qcN qcD ws alN alD A B n k0 g e0n e0d en ed D Cf P he hβ
      hrec hqcD hrate hgX hws hhalf hk0pos hdom hg hDD hk0lo hk0b hbhi hP
      hgrF hbhi2 k hPk hkk0 h0 hent
  | cons hd t ih =>
    obtain ⟨M, S⟩ := hd
    intro P k hch hP hgrF hlolo hbhi2 hPk hk hk1 hkk0 h0 hent
    have hSk0 : S.term.lo ≤ sAt en ed k0 :=
      CPair.le_trans (chainBot r qcN qcD e0n e0d t S hch.2.2)
        (CPair.le_trans hlolo hk0lo)
    have hsum : k + (k0 - k) = k0 := ground.natAddSubCancel hkk0
    have hdk : k ≤ firstGE en ed S.term.lo k (k0 - k) :=
      ground.firstAt_ge (fun m => S.term.lo ≤ sAt en ed m) (k0 - k) k
    have hdk0 : firstGE en ed S.term.lo k (k0 - k) ≤ k0 := by
      have hle := ground.firstAt_le (fun m => S.term.lo ≤ sAt en ed m) (k0 - k) k
      rw [hsum] at hle
      exact hle
    have hdhit : S.term.lo
        ≤ sAt en ed (firstGE en ed S.term.lo k (k0 - k)) := by
      refine ground.firstAt_hit (fun m => S.term.lo ≤ sAt en ed m) (k0 - k) k ?_
      rw [hsum]
      exact hSk0
    have hd1 : 1 ≤ firstGE en ed S.term.lo k (k0 - k) := Nat.le_trans hk1 hdk
    have hd1e : firstGE en ed S.term.lo k (k0 - k) - 1 + 1
        = firstGE en ed S.term.lo k (k0 - k) := by
      rw [Nat.add_comm]
      exact ground.natAddSubCancel hd1
    have hbelow : sAt en ed (firstGE en ed S.term.lo k (k0 - k) - 1)
        ≤ S.term.lo := by
      match Nat.eq_or_lt_of_le hdk with
      | Or.inl heq =>
        refine hk M S t rfl (firstGE en ed S.term.lo k (k0 - k) - 1) ?_
        rw [hd1e, ← heq]
        exact Nat.le_refl k
      | Or.inr hlt =>
        refine (CPair.le_total _ _).resolve_right
          (ground.firstAt_below (fun m => S.term.lo ≤ sAt en ed m)
            (k0 - k) k (firstGE en ed S.term.lo k (k0 - k) - 1) ?_ ?_)
        · refine Nat.le_of_succ_le_succ ?_
          show k + 1 ≤ firstGE en ed S.term.lo k (k0 - k) - 1 + 1
          rw [hd1e]
          exact hlt
        · show firstGE en ed S.term.lo k (k0 - k) - 1 + 1
            ≤ firstGE en ed S.term.lo k (k0 - k)
          rw [hd1e]
          exact Nat.le_refl _
    have hdb : sAt en ed (firstGE en ed S.term.lo k (k0 - k)) ≤ M.b := by
      have hstep := stepClear_step S.term.lo M.b e0n e0d hch.1.2.2.1
        (firstGE en ed S.term.lo k (k0 - k) - 1) en ed he hbelow
      rw [hd1e] at hstep
      exact hstep
    have hlend : k + (firstGE en ed S.term.lo k (k0 - k) - k)
        = firstGE en ed S.term.lo k (k0 - k) := ground.natAddSubCancel hdk
    have hhiD : sAt en ed (k + (firstGE en ed S.term.lo k (k0 - k) - k))
        ≤ P.term.hi := by
      rw [hlend]
      exact CPair.le_trans hdb hch.1.2.2.2.2.1
    have hposP := segStagePos r qcN qcD e0n e0d en ed P hP he k
      (firstGE en ed S.term.lo k (k0 - k) - k) hPk hhiD
    have hrun := runD r A B en ed D
      (fun m => poly.evalClear (depthPoly P.jet m) (BPair.ofPos en) ed P.pos.K)
      hβ hrec k k (firstGE en ed S.term.lo k (k0 - k) - k) (Nat.le_succ k)
      hposP
      (segStageTerm r qcN qcD A B e0n e0d en ed P hP he hqcD hrate k
        (firstGE en ed S.term.lo k (k0 - k) - k) hPk hhiD)
      h0 hent
    have hDat : ∀ tt, k ≤ tt → tt ≤ firstGE en ed S.term.lo k (k0 - k) →
        BPair.unit < D tt := by
      intro tt hktt httd
      match Nat.lt_or_ge k tt with
      | Or.inr hge =>
        rw [Nat.le_antisymm hge hktt]
        exact h0
      | Or.inl hlt =>
        obtain ⟨w, hw⟩ := Nat.le.dest hlt
        have heq : k + (w + 1) = tt := by
          rw [← Nat.add_assoc k w 1, Nat.add_right_comm k w 1]
          exact hw
        have hwle : w ≤ firstGE en ed S.term.lo k (k0 - k) - k := by
          refine Nat.le_trans (Nat.le_add_right w 1) (ground.leCancelL k ?_)
          rw [hlend, heq]
          exact httd
        have hstep := (hrun w hwle).1
        rw [show k + w + 1 = tt from by
          rw [← heq, Nat.add_assoc k w 1]] at hstep
        exact hstep
    have hposD : BPair.unit < poly.evalClear
        (depthPoly P.jet (firstGE en ed S.term.lo k (k0 - k)))
        (BPair.ofPos en) ed P.pos.K := by
      have hstep := hposP (firstGE en ed S.term.lo k (k0 - k) - k)
        (Nat.le_succ_of_le (Nat.le_refl _))
      rw [hlend] at hstep
      exact hstep
    have hentD : wellBond r B ed
        * (D (firstGE en ed S.term.lo k (k0 - k))
            * poly.evalClear (depthPoly P.jet
                (firstGE en ed S.term.lo k (k0 - k) + 1))
              (BPair.ofPos en) ed P.pos.K)
        ≤ D (firstGE en ed S.term.lo k (k0 - k) + 1)
          * poly.evalClear (depthPoly P.jet
              (firstGE en ed S.term.lo k (k0 - k)))
            (BPair.ofPos en) ed P.pos.K := by
      have hstep := (hrun (firstGE en ed S.term.lo k (k0 - k) - k)
        (Nat.le_refl _)).2
      rw [hlend] at hstep
      exact hstep
    have hSpos : BPair.unit < poly.evalClear
        (depthPoly S.jet (firstGE en ed S.term.lo k (k0 - k)))
        (BPair.ofPos en) ed S.pos.K :=
      segPos r qcN qcD e0n e0d S hch.2.1 en ed he _
        (CPair.le_trans hch.2.1.2.2.1 hdhit)
        (CPair.le_trans
          (sAt_mono en ed
            (Nat.le_add_right (firstGE en ed S.term.lo k (k0 - k)) 2))
          (segTwoStep r qcN qcD e0n e0d S hch.2.1 en ed he _
            (CPair.le_trans hdb hch.1.2.2.2.2.2.1)))
    have hentS := crossTransfer
      (ground.unitLeMul (ground.leB_of_lt hβ)
        (ground.leB_of_lt (hDat _ hdk (Nat.le_refl _))))
      hposD (ground.leB_of_lt hSpos)
      (crossOrder P.jet S.jet P.pos.K S.pos.K en ed
        (firstGE en ed S.term.lo k (k0 - k)) M.cert.K hch.1.1.1 hP.1.1
        hch.2.1.1.1
        (gradRead_pos (crossProf P.jet S.jet) e0n e0d M.cert hch.1.1 _ en ed
          he (CPair.le_trans hch.1.2.1 hdhit)
          (CPair.le_trans hdb hch.1.2.2.2.1)))
      hentD
    have hnext := ih S (firstGE en ed S.term.lo k (k0 - k)) hch.2.2 hch.2.1
      hgrF hlolo hbhi2 hdhit
      (fun M' S' t' hEq m hm =>
        CPair.le_trans
          (sAt_mono en ed (Nat.le_of_succ_le_succ (by
            show m + 1 ≤ firstGE en ed S.term.lo k (k0 - k) - 1 + 1
            rw [hd1e]
            exact hm)))
          (CPair.le_trans hbelow
            (by
              rw [hEq] at hch
              exact hch.2.2.1.2.2.2.2.2.2)))
      hd1 hdk0 (hDat _ hdk (Nat.le_refl _)) hentS
    intro j hkj hjn
    match Nat.lt_or_ge j (firstGE en ed S.term.lo k (k0 - k)) with
    | Or.inl hlt => exact hDat (j + 1) (Nat.le_succ_of_le hkj) hlt
    | Or.inr hge => exact hnext j hge hjn

/-- A segment's positivity at a depth inside its term box's bottom
and its positivity box's top. -/
private theorem segPosAt (r qcN qcD : Nat) (e0n : BPair) (e0d : Pos)
    (en ed : Pos) (S : SegCert) (hseg : segRead r qcN qcD e0n e0d S)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (m : Nat) (hlo : S.term.lo ≤ sAt en ed m)
    (hhi : sAt en ed m ≤ S.pos.hi) :
    BPair.unit
      < poly.evalClear (depthPoly S.jet m) (BPair.ofPos en) ed S.pos.K :=
  segPos r qcN qcD e0n e0d S hseg en ed he m
    (CPair.le_trans hseg.2.2.1 hlo) hhi

/-- A segment's termwise comparison at the member line at a depth
inside its term box. -/
private theorem segTermAt (r qcN qcD A B : Nat) (e0n : BPair) (e0d : Pos)
    (en ed : Pos) (S : SegCert) (hseg : segRead r qcN qcD e0n e0d S)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (m : Nat) (hlo : S.term.lo ≤ sAt en ed m)
    (hhi : sAt en ed m ≤ S.term.hi) :
    wellBond r B ed
        * (poly.evalClear (depthPoly S.jet m) (BPair.ofPos en) ed S.pos.K
          + poly.evalClear (depthPoly S.jet (m + 2))
              (BPair.ofPos en) ed S.pos.K)
      ≤ wellDiag r A B en ed (m + 1)
        * poly.evalClear (depthPoly S.jet (m + 1))
            (BPair.ofPos en) ed S.pos.K := by
  refine rateStep r qcN qcD A B en ed (m + 1) _ _ hqcD hrate
    (ground.leB_of_lt (segPosAt r qcN qcD e0n e0d en ed S hseg he (m + 1)
      (CPair.le_trans hlo (sAt_mono en ed (Nat.le_succ m)))
      (CPair.le_trans (sAt_mono en ed (Nat.succ_le_succ (Nat.le_succ m)))
        (segTwoStep r qcN qcD e0n e0d S hseg en ed he m hhi)))) ?_
  exact segTermCap r qcN qcD e0n e0d S hseg en ed he m hlo hhi

/-- The positive tier's run: from the boundary seed the chain
crosses each seam at its own first depth and clears the pivots
through the positive coverage. -/
private theorem posRun (r qN qD A B : Nat) (e0n : BPair) (e0d : Pos)
    (en ed : Pos) (D : Nat → BPair)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hβ : BPair.unit < wellBond r B ed)
    (hrec : ∀ m, (D (m + 2)
        + wellBond r B ed * wellBond r B ed * D m).oneValue
      (wellDiag r A B en ed (m + 2) * D (m + 1)))
    (hqD : 1 ≤ qD) (hrate : A * qD ≤ qN * B) :
    ∀ (l : List (SeamCert × SegCert)) (Vp : poly.PPoly × poly.PPoly)
      (Kp : Nat) (loP hiP hiPos : CPair) (k : Nat),
      chainSegs r qN qD e0n e0d Vp loP hiP l →
      profShape Vp Kp →
      (∀ m, loP ≤ sAt en ed m → sAt en ed m ≤ hiPos →
        BPair.unit
          < poly.evalClear (depthPoly Vp m) (BPair.ofPos en) ed Kp) →
      (∀ m, loP ≤ sAt en ed m → sAt en ed m ≤ hiP →
        wellBond r B ed
            * (poly.evalClear (depthPoly Vp m) (BPair.ofPos en) ed Kp
              + poly.evalClear (depthPoly Vp (m + 2)) (BPair.ofPos en) ed Kp)
          ≤ wellDiag r A B en ed (m + 1)
            * poly.evalClear (depthPoly Vp (m + 1)) (BPair.ofPos en) ed Kp) →
      (∀ m, sAt en ed m ≤ hiP → sAt en ed (m + 2) ≤ hiPos) →
      loP ≤ sAt en ed k →
      (∀ M' S' t', l = (M', S') :: t' →
        ∀ m, m + 1 ≤ k → sAt en ed m ≤ S'.term.lo) →
      1 ≤ k →
      BPair.unit < D k →
      wellBond r B ed
          * (D k * poly.evalClear (depthPoly Vp (k + 1))
              (BPair.ofPos en) ed Kp)
        ≤ D (k + 1) * poly.evalClear (depthPoly Vp k) (BPair.ofPos en) ed Kp →
      ∀ j, k ≤ j → sAt en ed j ≤ posTop hiP l →
        BPair.unit < D (j + 1) := by
  intro l
  induction l with
  | nil =>
    intro Vp Kp loP hiP hiPos k _ _ hPos hTerm hTwo hlok _ _ h0 hent j hkj hjt
    have hsum : k + (j - k) = j := ground.natAddSubCancel hkj
    have hjhi : sAt en ed (k + (j - k)) ≤ hiP := by
      rw [hsum]
      exact hjt
    have hrun := runD r A B en ed D
      (fun m => poly.evalClear (depthPoly Vp m) (BPair.ofPos en) ed Kp)
      hβ hrec k k (j - k) (Nat.le_succ k)
      (fun i hi => hPos (k + i)
        (CPair.le_trans hlok (sAt_mono en ed (Nat.le_add_right k i)))
        (CPair.le_trans
          (sAt_mono en ed (Nat.add_le_add_left
            (Nat.le_trans hi (Nat.succ_le_succ (Nat.le_succ (j - k)))) k))
          (hTwo (k + (j - k)) hjhi)))
      (fun i hi => hTerm (k + i)
        (CPair.le_trans hlok (sAt_mono en ed (Nat.le_add_right k i)))
        (CPair.le_trans
          (sAt_mono en ed (Nat.add_le_add_left (Nat.le_of_lt hi) k)) hjhi))
      h0 hent
    have hstep := (hrun (j - k) (Nat.le_refl _)).1
    rw [hsum] at hstep
    exact hstep
  | cons hd t ih =>
    obtain ⟨M, S⟩ := hd
    intro Vp Kp loP hiP hiPos k hch hsh hPos hTerm hTwo hlok hk hk1 h0 hent
      j hkj hjt
    have hsum : k + (j - k) = j := ground.natAddSubCancel hkj
    match (inferInstance : Decidable (S.term.lo ≤ sAt en ed j)) with
    | isFalse hno =>
      have hjS : sAt en ed j ≤ S.term.lo :=
        match CPair.le_total (sAt en ed j) S.term.lo with
        | Or.inl h => h
        | Or.inr h => absurd h hno
      have hjhi : sAt en ed (k + (j - k)) ≤ hiP := by
        rw [hsum]
        exact CPair.le_trans hjS
          (CPair.le_trans (stepClear_le hch.1.2.2.1 he)
            hch.1.2.2.2.2.1)
      have hrun := runD r A B en ed D
        (fun m => poly.evalClear (depthPoly Vp m) (BPair.ofPos en) ed Kp)
        hβ hrec k k (j - k) (Nat.le_succ k)
        (fun i hi => hPos (k + i)
          (CPair.le_trans hlok (sAt_mono en ed (Nat.le_add_right k i)))
          (CPair.le_trans
            (sAt_mono en ed (Nat.add_le_add_left
              (Nat.le_trans hi (Nat.succ_le_succ (Nat.le_succ (j - k)))) k))
            (hTwo (k + (j - k)) hjhi)))
        (fun i hi => hTerm (k + i)
          (CPair.le_trans hlok (sAt_mono en ed (Nat.le_add_right k i)))
          (CPair.le_trans
            (sAt_mono en ed (Nat.add_le_add_left (Nat.le_of_lt hi) k)) hjhi))
        h0 hent
      have hstep := (hrun (j - k) (Nat.le_refl _)).1
      rw [hsum] at hstep
      exact hstep
    | isTrue hyes =>
      have hdk : k ≤ firstGE en ed S.term.lo k (j - k) :=
        ground.firstAt_ge (fun m => S.term.lo ≤ sAt en ed m) (j - k) k
      have hdj : firstGE en ed S.term.lo k (j - k) ≤ j := by
        have hle := ground.firstAt_le (fun m => S.term.lo ≤ sAt en ed m) (j - k) k
        rw [hsum] at hle
        exact hle
      have hdhit : S.term.lo
          ≤ sAt en ed (firstGE en ed S.term.lo k (j - k)) := by
        refine ground.firstAt_hit (fun m => S.term.lo ≤ sAt en ed m) (j - k) k ?_
        rw [hsum]
        exact hyes
      have hd1 : 1 ≤ firstGE en ed S.term.lo k (j - k) := Nat.le_trans hk1 hdk
      have hd1e : firstGE en ed S.term.lo k (j - k) - 1 + 1
          = firstGE en ed S.term.lo k (j - k) := by
        rw [Nat.add_comm]
        exact ground.natAddSubCancel hd1
      have hbelow : sAt en ed (firstGE en ed S.term.lo k (j - k) - 1)
          ≤ S.term.lo := by
        match Nat.eq_or_lt_of_le hdk with
        | Or.inl heq =>
          refine hk M S t rfl (firstGE en ed S.term.lo k (j - k) - 1) ?_
          rw [hd1e, ← heq]
          exact Nat.le_refl k
        | Or.inr hlt =>
          refine (CPair.le_total _ _).resolve_right
            (ground.firstAt_below (fun m => S.term.lo ≤ sAt en ed m)
              (j - k) k (firstGE en ed S.term.lo k (j - k) - 1) ?_ ?_)
          · refine Nat.le_of_succ_le_succ ?_
            show k + 1 ≤ firstGE en ed S.term.lo k (j - k) - 1 + 1
            rw [hd1e]
            exact hlt
          · show firstGE en ed S.term.lo k (j - k) - 1 + 1
              ≤ firstGE en ed S.term.lo k (j - k)
            rw [hd1e]
            exact Nat.le_refl _
      have hdb : sAt en ed (firstGE en ed S.term.lo k (j - k)) ≤ M.b := by
        have hstep := stepClear_step S.term.lo M.b e0n e0d hch.1.2.2.1
          (firstGE en ed S.term.lo k (j - k) - 1) en ed he hbelow
        rw [hd1e] at hstep
        exact hstep
      have hlend : k + (firstGE en ed S.term.lo k (j - k) - k)
          = firstGE en ed S.term.lo k (j - k) := ground.natAddSubCancel hdk
      have hhiD : sAt en ed (k + (firstGE en ed S.term.lo k (j - k) - k))
          ≤ hiP := by
        rw [hlend]
        exact CPair.le_trans hdb hch.1.2.2.2.2.1
      have hrun := runD r A B en ed D
        (fun m => poly.evalClear (depthPoly Vp m) (BPair.ofPos en) ed Kp)
        hβ hrec k k (firstGE en ed S.term.lo k (j - k) - k) (Nat.le_succ k)
        (fun i hi => hPos (k + i)
          (CPair.le_trans hlok (sAt_mono en ed (Nat.le_add_right k i)))
          (CPair.le_trans
            (sAt_mono en ed (Nat.add_le_add_left
              (Nat.le_trans hi (Nat.succ_le_succ
                (Nat.le_succ (firstGE en ed S.term.lo k (j - k) - k)))) k))
            (hTwo (k + (firstGE en ed S.term.lo k (j - k) - k)) hhiD)))
        (fun i hi => hTerm (k + i)
          (CPair.le_trans hlok (sAt_mono en ed (Nat.le_add_right k i)))
          (CPair.le_trans
            (sAt_mono en ed (Nat.add_le_add_left (Nat.le_of_lt hi) k)) hhiD))
        h0 hent
      have hDat : ∀ tt, k ≤ tt → tt ≤ firstGE en ed S.term.lo k (j - k) →
          BPair.unit < D tt := by
        intro tt hktt httd
        match Nat.lt_or_ge k tt with
        | Or.inr hge =>
          rw [Nat.le_antisymm hge hktt]
          exact h0
        | Or.inl hlt =>
          obtain ⟨w, hw⟩ := Nat.le.dest hlt
          have heq : k + (w + 1) = tt := by
            rw [← Nat.add_assoc k w 1, Nat.add_right_comm k w 1]
            exact hw
          have hwle : w ≤ firstGE en ed S.term.lo k (j - k) - k := by
            refine Nat.le_trans (Nat.le_add_right w 1) (ground.leCancelL k ?_)
            rw [hlend, heq]
            exact httd
          have hstep := (hrun w hwle).1
          rw [show k + w + 1 = tt from by
            rw [← heq, Nat.add_assoc k w 1]] at hstep
          exact hstep
      have hposD : BPair.unit < poly.evalClear
          (depthPoly Vp (firstGE en ed S.term.lo k (j - k)))
          (BPair.ofPos en) ed Kp := by
        have hstep := hPos (k + (firstGE en ed S.term.lo k (j - k) - k))
          (CPair.le_trans hlok (sAt_mono en ed (Nat.le_add_right k _)))
          (CPair.le_trans (sAt_mono en ed (Nat.le_add_right _ 2))
            (hTwo (k + (firstGE en ed S.term.lo k (j - k) - k)) hhiD))
        rw [hlend] at hstep
        exact hstep
      have hentD : wellBond r B ed
          * (D (firstGE en ed S.term.lo k (j - k))
              * poly.evalClear (depthPoly Vp
                  (firstGE en ed S.term.lo k (j - k) + 1))
                (BPair.ofPos en) ed Kp)
          ≤ D (firstGE en ed S.term.lo k (j - k) + 1)
            * poly.evalClear (depthPoly Vp
                (firstGE en ed S.term.lo k (j - k))) (BPair.ofPos en) ed Kp := by
        have hstep := (hrun (firstGE en ed S.term.lo k (j - k) - k)
          (Nat.le_refl _)).2
        rw [hlend] at hstep
        exact hstep
      have hSpos : BPair.unit < poly.evalClear
          (depthPoly S.jet (firstGE en ed S.term.lo k (j - k)))
          (BPair.ofPos en) ed S.pos.K :=
        segPosAt r qN qD e0n e0d en ed S hch.2.1 he _ hdhit
          (CPair.le_trans (sAt_mono en ed (Nat.le_add_right _ 2))
            (segTwoStep r qN qD e0n e0d S hch.2.1 en ed he _
              (CPair.le_trans hdb hch.1.2.2.2.2.2.1)))
      have hentS := crossTransfer
        (ground.unitLeMul (ground.leB_of_lt hβ)
          (ground.leB_of_lt (hDat _ hdk (Nat.le_refl _))))
        hposD (ground.leB_of_lt hSpos)
        (crossOrder Vp S.jet Kp S.pos.K en ed
          (firstGE en ed S.term.lo k (j - k)) M.cert.K hch.1.1.1 hsh
          hch.2.1.1.1
          (gradRead_pos (crossProf Vp S.jet) e0n e0d M.cert hch.1.1 _ en ed
            he (CPair.le_trans hch.1.2.1 hdhit)
            (CPair.le_trans hdb hch.1.2.2.2.1)))
        hentD
      refine ih S.jet S.pos.K S.term.lo S.term.hi S.pos.hi
        (firstGE en ed S.term.lo k (j - k)) hch.2.2 hch.2.1.1.1
        (fun m hlo hhi => segPosAt r qN qD e0n e0d en ed S hch.2.1 he m
          hlo hhi)
        (fun m hlo hhi => segTermAt r qN qD A B e0n e0d en ed S hch.2.1 he
          hqD hrate m hlo hhi)
        (fun m hhi => segTwoStep r qN qD e0n e0d S hch.2.1 en ed he m hhi)
        hdhit
        (fun M' S' t' hEq m hm =>
          CPair.le_trans
            (sAt_mono en ed (Nat.le_of_succ_le_succ (by
              show m + 1 ≤ firstGE en ed S.term.lo k (j - k) - 1 + 1
              rw [hd1e]
              exact hm)))
            (CPair.le_trans hbelow
              (by
                rw [hEq] at hch
                exact hch.2.2.1.2.2.2.2.2.2)))
        hd1 (hDat _ hdk (Nat.le_refl _)) hentS j hdj hjt

/-- The chained coverage top is the last segment's own. -/
private theorem posTop_last :
    ∀ (l : List (SeamCert × SegCert)) (P : SegCert),
      posTop P.term.hi l = (lastSeg P l).term.hi
  | [], _ => rfl
  | (_, S) :: t, _ => posTop_last t S

/-- The crossing's seed at the covering segment: the rebound read
seeds the swapped chain's entry read one depth past the crossing. -/
private theorem crossSeed (r qcN qcD A B cc : Nat) (e0n : BPair) (e0d : Pos)
    (en ed : Pos) (P : SegCert)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hβ : BPair.unit < wellBond r B ed)
    (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (hP : segRead r qcN qcD e0n e0d P)
    (hPcc : P.term.lo ≤ sAt en ed cc)
    (hcchi : sAt en ed cc ≤ P.term.hi)
    (hW0 : BPair.unit ≤ wellWalk r A B en ed cc)
    (hW1 : wellWalk r A B en ed (cc + 1) < BPair.unit) :
    wellBond r B ed
        * ((wellWalk r A B en ed (cc + 1)).swap
          * poly.evalClear (depthPoly P.jet (cc + 2))
              (BPair.ofPos en) ed P.pos.K)
      ≤ (wellWalk r A B en ed (cc + 2)).swap
        * poly.evalClear (depthPoly P.jet (cc + 1))
            (BPair.ofPos en) ed P.pos.K := by
  have hposcc : BPair.unit < poly.evalClear (depthPoly P.jet cc)
      (BPair.ofPos en) ed P.pos.K :=
    segPosAt r qcN qcD e0n e0d en ed P hP he cc hPcc
      (CPair.le_trans (sAt_mono en ed (Nat.le_add_right cc 2))
        (segTwoStep r qcN qcD e0n e0d P hP en ed he cc hcchi))
  have hposcc1 : BPair.unit < poly.evalClear (depthPoly P.jet (cc + 1))
      (BPair.ofPos en) ed P.pos.K :=
    segPosAt r qcN qcD e0n e0d en ed P hP he (cc + 1)
      (CPair.le_trans hPcc (sAt_mono en ed (Nat.le_succ cc)))
      (CPair.le_trans (sAt_mono en ed (Nat.succ_le_succ (Nat.le_succ cc)))
        (segTwoStep r qcN qcD e0n e0d P hP en ed he cc hcchi))
  have htermcc := segTermAt r qcN qcD A B e0n e0d en ed P hP he hqcD hrate cc
    hPcc hcchi
  have hdrop : wellBond r B ed
        * poly.evalClear (depthPoly P.jet (cc + 2)) (BPair.ofPos en) ed P.pos.K
      ≤ wellBond r B ed
        * (poly.evalClear (depthPoly P.jet cc) (BPair.ofPos en) ed P.pos.K
          + poly.evalClear (depthPoly P.jet (cc + 2))
              (BPair.ofPos en) ed P.pos.K) := by
    refine ground.leB_congr_right
      (BPair.oneValue_of_eq
        (BPair.left_distrib (wellBond r B ed)
          (poly.evalClear (depthPoly P.jet cc) (BPair.ofPos en) ed P.pos.K)
          (poly.evalClear (depthPoly P.jet (cc + 2))
            (BPair.ofPos en) ed P.pos.K)).symm) ?_
    refine ground.leB_congr_left (BPair.unit_add _) ?_
    exact ground.leB_add
      (ground.unitLeMul (ground.leB_of_lt hβ) (ground.leB_of_lt hposcc))
      (ground.leB_refl _)
  have hterm' : wellBond r B ed
        * poly.evalClear (depthPoly P.jet (cc + 2)) (BPair.ofPos en) ed P.pos.K
      ≤ wellDiag r A B en ed (cc + 2)
        * poly.evalClear (depthPoly P.jet (cc + 1))
            (BPair.ofPos en) ed P.pos.K := by
    refine ground.leB_trans (ground.leB_trans hdrop htermcc) ?_
    refine ground.leB_congr
      (BPair.oneValue_of_eq
        (BPair.mul_comm
          (poly.evalClear (depthPoly P.jet (cc + 1)) (BPair.ofPos en) ed
            P.pos.K)
          (wellDiag r A B en ed (cc + 1))))
      (BPair.oneValue_of_eq
        (BPair.mul_comm
          (poly.evalClear (depthPoly P.jet (cc + 1)) (BPair.ofPos en) ed
            P.pos.K)
          (wellDiag r A B en ed (cc + 2)))) ?_
    exact ground.leB_mulR (ground.leB_of_lt hposcc1)
      (wellDiag_mono r A B en ed (Nat.le_succ (cc + 1)))
  exact seed_after_crossing (wellDiag r A B en ed (cc + 2))
    (wellBond r B ed) (wellWalk r A B en ed cc)
    (wellWalk r A B en ed (cc + 1)) (wellWalk r A B en ed (cc + 2))
    (poly.evalClear (depthPoly P.jet (cc + 1)) (BPair.ofPos en) ed P.pos.K)
    (poly.evalClear (depthPoly P.jet (cc + 2)) (BPair.ofPos en) ed P.pos.K)
    (wellWalk_rec r A B en ed cc) hW0 hW1 hposcc1 hterm'

/-- The covering segment's search: the post chain's last stage whose
term box reaches below the crossing carries the seed, and every
later stage's bottom sits beyond it. -/
private theorem coverFind (r qcN qcD alN alD cc : Nat) (e0n : BPair)
    (e0d : Pos) (en ed : Pos) (Cf : SeamCert) (Q : Prop)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hcclo : sAt en ed cc ≤ Cf.cert.lo) :
    ∀ (l : List (SeamCert × SegCert)) (P : SegCert),
      chainSegs r qcN qcD e0n e0d P.jet P.term.lo P.term.hi l →
      segRead r qcN qcD e0n e0d P →
      gradRead (slopeProf (lastSeg P l).jet alN alD) e0n e0d Cf.cert →
      (lastSeg P l).term.lo ≤ Cf.cert.lo →
      Cf.b ≤ (lastSeg P l).term.hi →
      Cf.cert.lo ≤ (lastSeg P l).term.hi →
      P.term.lo ≤ sAt en ed cc →
      (∀ (P' : SegCert) (l' : List (SeamCert × SegCert)),
        chainSegs r qcN qcD e0n e0d P'.jet P'.term.lo P'.term.hi l' →
        segRead r qcN qcD e0n e0d P' →
        gradRead (slopeProf (lastSeg P' l').jet alN alD) e0n e0d Cf.cert →
        (lastSeg P' l').term.lo ≤ Cf.cert.lo →
        Cf.b ≤ (lastSeg P' l').term.hi →
        Cf.cert.lo ≤ (lastSeg P' l').term.hi →
        P'.term.lo ≤ sAt en ed cc →
        sAt en ed cc ≤ P'.term.hi →
        (∀ M' S' t', l' = (M', S') :: t' →
          ∀ m, m + 1 ≤ cc + 1 → sAt en ed m ≤ S'.term.lo) →
        Q) → Q := by
  intro l
  induction l with
  | nil =>
    intro P hch hP hgrF hlolo hbhi2 hfhi hPcc hcont
    exact hcont P [] hch hP hgrF hlolo hbhi2 hfhi hPcc
      (CPair.le_trans hcclo hfhi) (fun _ _ _ hEq => by injection hEq)
  | cons hd t ih =>
    obtain ⟨M, S⟩ := hd
    intro P hch hP hgrF hlolo hbhi2 hfhi hPcc hcont
    match (inferInstance : Decidable (S.term.lo ≤ sAt en ed cc)) with
    | isTrue hyes =>
      exact ih S hch.2.2 hch.2.1 hgrF hlolo hbhi2 hfhi hyes hcont
    | isFalse hno =>
      have hccS : sAt en ed cc ≤ S.term.lo :=
        match CPair.le_total (sAt en ed cc) S.term.lo with
        | Or.inl h => h
        | Or.inr h => absurd h hno
      exact hcont P ((M, S) :: t) hch hP hgrF hlolo hbhi2 hfhi hPcc
        (CPair.le_trans hccS
          (CPair.le_trans (stepClear_le hch.1.2.2.1 he)
            hch.1.2.2.2.2.1))
        (fun M' S' t' hEq m hm => by
          injection hEq with h1 _
          injection h1 with _ h3
          rw [← h3]
          exact CPair.le_trans (sAt_mono en ed (Nat.le_of_succ_le_succ hm))
            hccS)

/-- The walk's reading past the crossing at the swapped list's
index shift. -/
private theorem swapShift (r A B n cc : Nat) (en ed : Pos)
    (h0' : BPair.unit < (wellWalk r A B en ed (cc + 1)).swap)
    (hrun : ∀ j, cc + 1 ≤ j → j ≤ n →
      BPair.unit < (wellWalk r A B en ed (j + 1)).swap) :
    ∀ j, cc + 1 ≤ j → j ≤ n → wellWalk r A B en ed j < BPair.unit := by
  intro j hccj hjn
  match Nat.eq_or_lt_of_le hccj with
  | Or.inl heq =>
    rw [← heq]
    exact ground.ltB_swap h0'
  | Or.inr hlt =>
    have hj1 : j - 1 + 1 = j := by
      rw [Nat.add_comm]
      exact ground.natAddSubCancel
        (Nat.le_trans (Nat.zero_lt_succ cc) (Nat.le_of_lt hlt))
    have hccj1 : cc + 1 ≤ j - 1 := by
      refine Nat.le_of_succ_le_succ ?_
      show cc + 1 + 1 ≤ j - 1 + 1
      rw [hj1]
      exact hlt
    have hstep := hrun (j - 1) hccj1 (Nat.le_trans (Nat.sub_le j 1) hjn)
    rw [hj1] at hstep
    exact ground.ltB_swap hstep

/-- The crossing's run at the tail-engaging cut: the seed carries
through the post chain to the final seam and the geometric tail. -/
private theorem coverCoreA (r qcN qcD ws alN alD A B n k0 g cc : Nat)
    (e0n : BPair) (e0d : Pos) (en ed : Pos) (Cf : SeamCert)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hβ : BPair.unit < wellBond r B ed)
    (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (hgX : g + alN * (2 * k0 + 1) * ground.posVal en
      = alD * ground.posVal ed)
    (hws : 18 * ((r + 1) * qcD) * (alN * alN) * (k0 * k0)
        * ground.posVal en
      ≤ ws * (alD * alD) * ground.posVal ed)
    (hhalf : 6 * (alN * k0 * ground.posVal en) ≤ alD * ground.posVal ed)
    (hk0pos : 1 ≤ k0)
    (hdom : ((r + 1) * qcN + ws) * ground.posVal ed
      ≤ 4 * qcD * (k0 * k0) * ground.posVal en)
    (hg : 1 ≤ g) (hDD : 1 ≤ alD * ground.posVal ed)
    (hk0lo : Cf.cert.lo ≤ sAt en ed k0)
    (hk0b : sAt en ed k0 ≤ Cf.b) (hbhi : Cf.b ≤ Cf.cert.hi)
    (hW0 : BPair.unit ≤ wellWalk r A B en ed cc)
    (hW1 : wellWalk r A B en ed (cc + 1) < BPair.unit)
    (hcck0 : cc + 1 ≤ k0)
    (P : SegCert) (l : List (SeamCert × SegCert))
    (hch : chainSegs r qcN qcD e0n e0d P.jet P.term.lo P.term.hi l)
    (hP : segRead r qcN qcD e0n e0d P)
    (hgrF : gradRead (slopeProf (lastSeg P l).jet alN alD) e0n e0d Cf.cert)
    (hlolo : (lastSeg P l).term.lo ≤ Cf.cert.lo)
    (hbhi2 : Cf.b ≤ (lastSeg P l).term.hi)
    (hPcc : P.term.lo ≤ sAt en ed cc)
    (hcchi : sAt en ed cc ≤ P.term.hi)
    (hk : ∀ M' S' t', l = (M', S') :: t' →
      ∀ m, m + 1 ≤ cc + 1 → sAt en ed m ≤ S'.term.lo) :
    ∀ j, cc + 1 ≤ j → j ≤ n → wellWalk r A B en ed j < BPair.unit :=
  swapShift r A B n cc en ed (ground.ltB_swap hW1)
    (postRun r qcN qcD ws alN alD A B n k0 g e0n e0d en ed
      (fun m => (wellWalk r A B en ed m).swap) Cf he hβ
      (fun m => rec_swap (wellWalk_rec r A B en ed m)) hqcD hrate hgX hws
      hhalf hk0pos hdom hg hDD hk0lo hk0b hbhi l P (cc + 1) hch hP hgrF hlolo
      hbhi2 (CPair.le_trans hPcc (sAt_mono en ed (Nat.le_succ cc))) hk
      (Nat.succ_le_succ (Nat.zero_le cc)) hcck0 (ground.ltB_swap hW1)
      (crossSeed r qcN qcD A B cc e0n e0d en ed P he hβ hqcD hrate hP hPcc
        hcchi hW0 hW1))

/-- The crossing's run at a cut whose tail never engages: the post
chain's own coverage carries the seed to the head's end. -/
private theorem coverCoreB (r qcN qcD A B n cc : Nat)
    (e0n : BPair) (e0d : Pos) (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hβ : BPair.unit < wellBond r B ed)
    (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (hW0 : BPair.unit ≤ wellWalk r A B en ed cc)
    (hW1 : wellWalk r A B en ed (cc + 1) < BPair.unit)
    (P : SegCert) (l : List (SeamCert × SegCert))
    (hch : chainSegs r qcN qcD e0n e0d P.jet P.term.lo P.term.hi l)
    (hP : segRead r qcN qcD e0n e0d P)
    (hPcc : P.term.lo ≤ sAt en ed cc)
    (hcchi : sAt en ed cc ≤ P.term.hi)
    (hk : ∀ M' S' t', l = (M', S') :: t' →
      ∀ m, m + 1 ≤ cc + 1 → sAt en ed m ≤ S'.term.lo)
    (hcov : ∀ j, j ≤ n → sAt en ed j ≤ (lastSeg P l).term.hi) :
    ∀ j, cc + 1 ≤ j → j ≤ n → wellWalk r A B en ed j < BPair.unit := by
  refine swapShift r A B n cc en ed (ground.ltB_swap hW1) ?_
  intro j hccj hjn
  refine posRun r qcN qcD A B e0n e0d en ed
    (fun m => (wellWalk r A B en ed m).swap) he hβ
    (fun m => rec_swap (wellWalk_rec r A B en ed m)) hqcD hrate l P.jet
    P.pos.K P.term.lo P.term.hi P.pos.hi (cc + 1) hch hP.1.1
    (fun m hlo hhi => segPosAt r qcN qcD e0n e0d en ed P hP he m hlo hhi)
    (fun m hlo hhi => segTermAt r qcN qcD A B e0n e0d en ed P hP he hqcD
      hrate m hlo hhi)
    (fun m hhi => segTwoStep r qcN qcD e0n e0d P hP en ed he m hhi)
    (CPair.le_trans hPcc (sAt_mono en ed (Nat.le_succ cc))) hk
    (Nat.succ_le_succ (Nat.zero_le cc)) (ground.ltB_swap hW1)
    (crossSeed r qcN qcD A B cc e0n e0d en ed P he hβ hqcD hrate hP hPcc
      hcchi hW0 hW1) j hccj ?_
  rw [posTop_last l P]
  exact hcov j hjn

/-- The first depth from a stated one at which a decidable read
fails, the bounded first-hit search's instance at the read's
refusal. -/
private abbrev firstBad (Q : Nat → Prop) [DecidablePred Q] :
    Nat → Nat → Nat :=
  ground.firstAt (fun m => ¬ Q m)

/-- The crossing inside the tail: the geometric list carries the
seed from the crossing to the head's end. -/
private theorem tailCover (r qcN qcD ws alN alD A B n k0 g cc : Nat)
    (en ed : Pos)
    (hβ : BPair.unit < wellBond r B ed)
    (hqcD : 1 ≤ qcD) (hrate : A * qcD ≤ qcN * B)
    (hgX : g + alN * (2 * k0 + 1) * ground.posVal en
      = alD * ground.posVal ed)
    (hws : 18 * ((r + 1) * qcD) * (alN * alN) * (k0 * k0)
        * ground.posVal en
      ≤ ws * (alD * alD) * ground.posVal ed)
    (hhalf : 6 * (alN * k0 * ground.posVal en) ≤ alD * ground.posVal ed)
    (hk0pos : 1 ≤ k0)
    (hdom : ((r + 1) * qcN + ws) * ground.posVal ed
      ≤ 4 * qcD * (k0 * k0) * ground.posVal en)
    (hg : 1 ≤ g) (hDD : 1 ≤ alD * ground.posVal ed)
    (hk0cc : k0 ≤ cc) (hccn : cc ≤ n)
    (hW0 : BPair.unit ≤ wellWalk r A B en ed cc)
    (hW1 : wellWalk r A B en ed (cc + 1) < BPair.unit) :
    ∀ j, cc + 1 ≤ j → j ≤ n → wellWalk r A B en ed j < BPair.unit := by
  have hcc : k0 + (cc - k0) = cc := ground.natAddSubCancel hk0cc
  have hgeoTerm : ∀ i, i + 2 ≤ n + 3 →
      wellBond r B ed
          * (geoU g (alD * ground.posVal ed) k0 (n + 3) (k0 + i)
            + geoU g (alD * ground.posVal ed) k0 (n + 3) (k0 + i + 2))
        ≤ wellDiag r A B en ed (k0 + i + 1)
          * geoU g (alD * ground.posVal ed) k0 (n + 3) (k0 + i + 1) :=
    fun i hi => geoTermMem r qcN qcD ws alN alD A B k0 (n + 3) i g en ed hgX
      hws hhalf hk0pos hdom hi hqcD hrate hg hDD
  have hccbnd : cc - k0 + 2 ≤ n + 3 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.le_trans (Nat.sub_le cc k0) hccn) 2)
      (Nat.add_le_add_left (Nat.le_succ 2) n)
  have htermcc : wellBond r B ed
        * (geoU g (alD * ground.posVal ed) k0 (n + 3) cc
          + geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 2))
      ≤ wellDiag r A B en ed (cc + 1)
        * geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 1) := by
    have hstep := hgeoTerm (cc - k0) hccbnd
    rw [hcc] at hstep
    exact hstep
  have hposcc := geoPos hg hDD k0 (n + 3) cc
  have hposcc1 := geoPos hg hDD k0 (n + 3) (cc + 1)
  have hdrop : wellBond r B ed
        * geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 2)
      ≤ wellBond r B ed
        * (geoU g (alD * ground.posVal ed) k0 (n + 3) cc
          + geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 2)) := by
    refine ground.leB_congr_right
      (BPair.oneValue_of_eq
        (BPair.left_distrib (wellBond r B ed)
          (geoU g (alD * ground.posVal ed) k0 (n + 3) cc)
          (geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 2))).symm) ?_
    refine ground.leB_congr_left (BPair.unit_add _) ?_
    exact ground.leB_add
      (ground.unitLeMul (ground.leB_of_lt hβ) (ground.leB_of_lt hposcc))
      (ground.leB_refl _)
  have hterm' : wellBond r B ed
        * geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 2)
      ≤ wellDiag r A B en ed (cc + 2)
        * geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 1) := by
    refine ground.leB_trans (ground.leB_trans hdrop htermcc) ?_
    refine ground.leB_congr
      (BPair.oneValue_of_eq
        (BPair.mul_comm (geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 1))
          (wellDiag r A B en ed (cc + 1))))
      (BPair.oneValue_of_eq
        (BPair.mul_comm (geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 1))
          (wellDiag r A B en ed (cc + 2)))) ?_
    exact ground.leB_mulR (ground.leB_of_lt hposcc1)
      (wellDiag_mono r A B en ed (Nat.le_succ (cc + 1)))
  have hseed := seed_after_crossing (wellDiag r A B en ed (cc + 2))
    (wellBond r B ed) (wellWalk r A B en ed cc)
    (wellWalk r A B en ed (cc + 1)) (wellWalk r A B en ed (cc + 2))
    (geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 1))
    (geoU g (alD * ground.posVal ed) k0 (n + 3) (cc + 2))
    (wellWalk_rec r A B en ed cc) hW0 hW1 hposcc1 hterm'
  have hrun := runD r A B en ed (fun m => (wellWalk r A B en ed m).swap)
    (geoU g (alD * ground.posVal ed) k0 (n + 3)) hβ
    (fun m => rec_swap (wellWalk_rec r A B en ed m)) (cc + 1) (cc + 1)
    (n - cc) (Nat.le_succ (cc + 1))
    (fun i _ => geoPos hg hDD k0 (n + 3) (cc + 1 + i))
    (fun i hi => by
      have hidx : k0 + (cc - k0 + 1 + i) = cc + 1 + i := by
        rw [← Nat.add_assoc k0 (cc - k0 + 1) i, ← Nat.add_assoc k0 (cc - k0) 1,
          hcc]
      have hb1 : cc + i + 1 ≤ n := by
        rw [Nat.add_assoc cc i 1]
        refine Nat.le_trans (Nat.add_le_add_left hi cc) ?_
        rw [ground.natAddSubCancel hccn]
        exact Nat.le_refl n
      have hbnd : cc - k0 + 1 + i + 2 ≤ n + 3 := by
        refine Nat.le_trans
          (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.add_le_add_right (Nat.sub_le cc k0) 1) i) 2) ?_
        rw [Nat.add_right_comm cc 1 i]
        exact Nat.le_trans (Nat.add_le_add_right hb1 2)
          (Nat.add_le_add_left (Nat.le_succ 2) n)
      have hstep := hgeoTerm (cc - k0 + 1 + i) hbnd
      rw [hidx] at hstep
      exact hstep)
    (ground.ltB_swap hW1) hseed
  refine swapShift r A B n cc en ed (ground.ltB_swap hW1) ?_
  intro j hccj hjn
  obtain ⟨w, hw⟩ := Nat.le.dest hccj
  have hjw : cc + w + 1 = j := by
    rw [Nat.add_right_comm cc w 1]
    exact hw
  have hwle : w ≤ n - cc := by
    refine ground.leCancelL cc ?_
    rw [ground.natAddSubCancel hccn]
    refine Nat.le_trans (Nat.le_succ (cc + w)) ?_
    show cc + w + 1 ≤ n
    rw [hjw]
    exact hjn
  have hstep := (hrun w hwle).1
  rw [show cc + 1 + w + 1 = j + 1 from by rw [hw]] at hstep
  exact hstep

/-- A composite at a first datum at or below the sum's unit sits at
or below the composite unit. -/
private theorem cleUnit {u : BPair} {w : Pos} (h : u ≤ BPair.unit) :
    (⟨u, w⟩ : CPair) ≤ stage.unitC := by
  show u.scale Pos.one ≤ BPair.unit.scale w
  rw [BPair.scale_one]
  exact ground.leB_congr_right (BPair.oneValue_symm (BPair.unit_scale w)) h

/-- The origin depth's square-scale read is the composite unit. -/
private theorem sAt_zero (en ed : Pos) :
    sAt en ed 0 ≤ stage.unitC :=
  cleUnit
    (ground.leB_congr_left (BPair.oneValue_symm (BPair.unit_mul (BPair.ofPos en)))
      (ground.leB_refl BPair.unit))

/-- The positive chain's coverage top sits at or above the composite
unit whenever the chain reaches a depth. -/
private theorem preHiUnit (r qN qD : Nat) (e0n : BPair) (e0d : Pos)
    (Vp : poly.PPoly × poly.PPoly) (hiP : CPair) (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    ∀ (l : List (SeamCert × SegCert)),
      chainSegs r qN qD e0n e0d Vp stage.unitC hiP l →
      stage.unitC ≤ posTop hiP l → stage.unitC ≤ hiP
  | [], _, h => h
  | (_, _) :: _, hch, _ =>
    CPair.le_trans hch.1.2.2.2.2.2.2
      (CPair.le_trans (stepClear_le hch.1.2.2.1 he)
        hch.1.2.2.2.2.1)

/-- The positive tier's bracket: the crossing sits at or beyond the
positive coverage top, the boundary seed's chain clearing every
pivot below it. -/
private theorem posPhase (r A B c : Nat) (C : DisconjCert) (en ed : Pos)
    (hC : certRead r C)
    (he : BPair.ofPos en * BPair.ofPos C.e0d ≤ C.e0n * BPair.ofPos ed)
    (hrate : A * C.qcD ≤ C.qcN * B)
    (hβ : BPair.unit < wellBond r B ed)
    (hQc : ¬ (BPair.unit < wellWalk r A B en ed (c + 1))) :
    posTop C.preTerm.hi C.posChain ≤ sAt en ed c := by
  match CPair.le_total (posTop C.preTerm.hi C.posChain) (sAt en ed c) with
  | Or.inl h => exact h
  | Or.inr h =>
    obtain ⟨hqcD, halD, hgrPos, hgrTerm, hploU, hptloU,
      hst1, hst2, hseedR, hchP, hsegP0, hcov0, hchQ, hgrFin, hfinU, hfinLo,
      hstF, hfbHi, hfbLast, hdomC, hwsC, hhalfC⟩ := hC
    have hpreHi : stage.unitC ≤ C.preTerm.hi :=
      preHiUnit r C.qcN C.qcD C.e0n C.e0d C.preV C.preTerm.hi en ed he
        C.posChain hchP
        (CPair.le_trans (sAt_unit en ed c) h)
    have hTwo : ∀ m, sAt en ed m ≤ C.preTerm.hi →
        sAt en ed (m + 2) ≤ C.prePos.hi := fun m hm =>
      stepClear_step C.preMid C.prePos.hi C.e0n C.e0d hst2 (m + 1) en ed he
        (stepClear_step C.preTerm.hi C.preMid C.e0n C.e0d hst1 m en ed he hm)
    have hcov0' : sAt en ed 0 ≤ C.preTerm.hi :=
      CPair.le_trans (sAt_zero en ed) hpreHi
    have hPos : ∀ m, stage.unitC ≤ sAt en ed m →
        sAt en ed m ≤ C.prePos.hi →
        BPair.unit < poly.evalClear (depthPoly C.preV m) (BPair.ofPos en) ed
          C.prePos.K := by
      intro m _ hhi
      match m with
      | 0 =>
        exact seedPos r C.qcN C.qcD C.e0n C.e0d en ed C.preV C.seedK C.seedCK
          C.seedTK C.prePos.K hgrPos.1 hgrPos.2.2.1 hseedR he
      | m' + 1 =>
        exact gradRead_pos C.preV C.e0n C.e0d C.prePos hgrPos (m' + 1) en ed
          he (CPair.le_trans hploU (sAt_unit en ed (m' + 1))) hhi
    have hTerm : ∀ m, stage.unitC ≤ sAt en ed m →
        sAt en ed m ≤ C.preTerm.hi →
        wellBond r B ed
            * (poly.evalClear (depthPoly C.preV m) (BPair.ofPos en) ed
                C.prePos.K
              + poly.evalClear (depthPoly C.preV (m + 2)) (BPair.ofPos en) ed
                  C.prePos.K)
          ≤ wellDiag r A B en ed (m + 1)
            * poly.evalClear (depthPoly C.preV (m + 1)) (BPair.ofPos en) ed
                C.prePos.K := by
      intro m hlo hhi
      refine rateStep r C.qcN C.qcD A B en ed (m + 1) _ _ hqcD hrate
        (ground.leB_of_lt (hPos (m + 1)
          (CPair.le_trans hlo (sAt_mono en ed (Nat.le_succ m)))
          (CPair.le_trans (sAt_mono en ed (Nat.succ_le_succ (Nat.le_succ m)))
            (hTwo m hhi)))) ?_
      match m with
      | 0 =>
        exact seedTerm r C.qcN C.qcD C.e0n C.e0d en ed C.preV C.seedK C.seedCK
          C.seedTK C.prePos.K hgrPos.1 hgrPos.2.2.1 hseedR he
      | m' + 1 =>
        refine termOfStrip r C.qcN C.qcD en ed C.preV C.prePos.K C.preTerm.K
          (m' + 1) hgrPos.1 hgrTerm.1 ?_
        exact gradRead_pos (profStrip (termProf C.preV r C.qcN C.qcD)) C.e0n
          C.e0d C.preTerm hgrTerm (m' + 1) en ed
          he (CPair.le_trans hptloU (sAt_unit en ed (m' + 1))) hhi
    have hp0hi : sAt en ed 0 ≤ C.prePos.hi :=
      CPair.le_trans (sAt_mono en ed (Nat.zero_le 2)) (hTwo 0 hcov0')
    have hent0 : wellBond r B ed
          * (wellWalk r A B en ed 0
            * poly.evalClear (depthPoly C.preV 1) (BPair.ofPos en) ed
                C.prePos.K)
        ≤ wellWalk r A B en ed 1
          * poly.evalClear (depthPoly C.preV 0) (BPair.ofPos en) ed
              C.prePos.K := by
      rw [wellWalk_zero, wellWalk_one]
      refine ground.leB_congr_left
        (BPair.mul_congr (BPair.oneValue_refl (wellBond r B ed))
          (BPair.oneValue_symm (BPair.ofNat_one_mul _))) ?_
      exact rateStep r C.qcN C.qcD A B en ed 1
        (poly.evalClear (depthPoly C.preV 1) (BPair.ofPos en) ed C.prePos.K)
        (poly.evalClear (depthPoly C.preV 0) (BPair.ofPos en) ed C.prePos.K)
        hqcD hrate
        (ground.leB_of_lt (hPos 0 (sAt_unit en ed 0) hp0hi))
        (seedRead_read r C.qcN C.qcD C.e0n C.e0d en ed C.preV C.seedK
          C.seedCK C.seedTK C.prePos.K hgrPos.1 hgrPos.2.2.1 hseedR he)
    have hrun0 := runD r A B en ed (wellWalk r A B en ed)
      (fun m => poly.evalClear (depthPoly C.preV m) (BPair.ofPos en) ed
        C.prePos.K)
      hβ (fun m => wellWalk_rec r A B en ed m) 0 0 1 (Nat.zero_le 1)
      (fun i hi => by
        rw [Nat.zero_add i]
        exact hPos i (sAt_unit en ed i)
          (CPair.le_trans (sAt_mono en ed hi) (hTwo 0 hcov0')))
      (fun i hi => by
        rw [Nat.zero_add i]
        exact hTerm i (sAt_unit en ed i)
          (CPair.le_trans (sAt_mono en ed (Nat.le_of_lt_succ hi)) hcov0'))
      (by
        rw [wellWalk_zero]
        exact ground.unitLtNat (Nat.le_refl 1))
      hent0
    match Nat.lt_or_ge 0 c with
    | Or.inr hc0 =>
      rw [Nat.le_antisymm hc0 (Nat.zero_le c)] at hQc
      exact absurd (hrun0 0 (Nat.zero_le 1)).1 hQc
    | Or.inl hc1 =>
      refine absurd ?_ hQc
      exact posRun r C.qcN C.qcD A B C.e0n C.e0d en ed (wellWalk r A B en ed)
        he hβ (fun m => wellWalk_rec r A B en ed m) hqcD hrate C.posChain
        C.preV C.prePos.K stage.unitC C.preTerm.hi C.prePos.hi 1 hchP
        hgrPos.1 hPos hTerm hTwo (sAt_unit en ed 1)
        (fun M' S' t' hEq m hm => by
          rw [hEq] at hchP
          exact CPair.le_trans
            (CPair.le_trans (sAt_mono en ed (Nat.le_of_succ_le_succ hm))
              (sAt_zero en ed))
            hchP.1.2.2.2.2.2.2)
        (Nat.le_refl 1) (hrun0 0 (Nat.zero_le 1)).1
        (hrun0 1 (Nat.le_refl 1)).2 c hc1 h

/-- The bundled certificate's glue: at every line whose rate sits
at or below the stated rate and at every scale under the cleared
ceiling, the certificate's read settles the head's reversal count
at most one at every order and every split — the positive tier's
chain brackets the crossing from below, the swapped chain runs
from the crossing through the post tier's seams to the final
seam's geometric tail, and the count tier's arms read the count at
the crossing's own position; the cut members' lines read here at
their multiples of the lower rate. -/
theorem certCount (r : Nat) (C : DisconjCert) (A B n : Nat)
    (en ed : Pos) (hC : certRead r C)
    (he : BPair.ofPos en * BPair.ofPos C.e0d ≤ C.e0n * BPair.ofPos ed)
    (hrateC : A * C.qcD ≤ C.qcN * B)
    (hB1 : 1 ≤ B) (sp : inertia.Split n)
    (hsp : inertia.splitRead (wellMat r A B en ed n) sp) :
    inertia.revAt sp ≤ 1 := by
  obtain ⟨hqcD, halD, hgrPos, hgrTerm, hploU, hptloU,
    hst1, hst2, hseedR, hchP, hsegP0, hcov0, hchQ, hgrFin, hfinU, hfinLo,
    hstF, hfbHi, hfbLast, hdomC, hwsC, hhalfC⟩ := hC
  have hfinHi : C.fin.cert.lo
      ≤ (lastSeg C.postSeg0 C.postRest).term.hi :=
    CPair.le_trans (stepClear_le hstF he) hfbLast
  have hβ : BPair.unit < wellBond r B ed := by
    show BPair.unit
      < BPair.ofNat ((r + 1) * B) * BPair.ofPos ed * BPair.ofPos ed
    refine ground.unitLtMul (ground.unitLtMul (ground.unitLtNat ?_)
      (ground.unitLtOfPos ed)) (ground.unitLtOfPos ed)
    exact Nat.le_trans (Nat.le_of_eq (Nat.one_mul 1).symm)
      (Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le r)) hB1)
  have hd1 : 1 ≤ ground.posVal ed := ground.posVal_pos ed
  have hDD : 1 ≤ C.alD * ground.posVal ed :=
    Nat.le_trans (Nat.le_of_eq (Nat.one_mul 1).symm)
      (Nat.mul_le_mul halD hd1)
  have hk0pos : 1 ≤ firstGE en ed C.fin.cert.lo 1 (n + 2) :=
    ground.firstAt_ge (fun m => C.fin.cert.lo ≤ sAt en ed m) (n + 2) 1
  have hk0e : firstGE en ed C.fin.cert.lo 1 (n + 2) - 1 + 1
      = firstGE en ed C.fin.cert.lo 1 (n + 2) := by
    rw [Nat.add_comm]
    exact ground.natAddSubCancel hk0pos
  have hunitFin : sAt en ed 0 ≤ C.fin.cert.lo :=
    CPair.le_trans (sAt_zero en ed) (Or.inr hfinU)
  have hneg : ∀ cc, BPair.unit ≤ wellWalk r A B en ed cc →
      wellWalk r A B en ed (cc + 1) < BPair.unit →
      posTop C.preTerm.hi C.posChain ≤ sAt en ed cc → cc ≤ n →
      ∀ j, cc + 1 ≤ j → j ≤ n → wellWalk r A B en ed j < BPair.unit := by
    intro cc hW0 hW1 hcctop hccn
    have hP0cc : C.postSeg0.term.lo ≤ sAt en ed cc :=
      CPair.le_trans hcov0 hcctop
    match (inferInstance : Decidable (C.fin.cert.lo
        ≤ sAt en ed (firstGE en ed C.fin.cert.lo 1 (n + 2)))) with
    | isFalse hB =>
      have hmiss := ground.firstAt_miss (fun m => C.fin.cert.lo ≤ sAt en ed m) (n + 2) 1 hB
      have hlejfin : ∀ j, j ≤ n → sAt en ed j ≤ C.fin.cert.lo := by
        intro j hj
        match Nat.lt_or_ge 0 j with
        | Or.inr hj0 =>
          rw [Nat.le_antisymm hj0 (Nat.zero_le j)]
          exact hunitFin
        | Or.inl hj1 =>
          refine (CPair.le_total _ _).resolve_right
            (ground.firstAt_below (fun m => C.fin.cert.lo ≤ sAt en ed m)
              (n + 2) 1 j hj1 ?_)
          rw [hmiss]
          refine Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hj) ?_
          rw [Nat.add_comm 1 (n + 2)]
          exact Nat.add_le_add_left (Nat.le_add_left 1 2) n
      exact coverFind r C.qcN C.qcD C.alN C.alD cc C.e0n C.e0d en ed C.fin _
        he (hlejfin cc hccn) C.postRest C.postSeg0 hchQ hsegP0 hgrFin hfinLo
        hfbLast hfinHi hP0cc
        (fun P' l' hch' hP' _ _ _ hf' hPcc' hcchi' hk' =>
          coverCoreB r C.qcN C.qcD A B n cc C.e0n C.e0d en ed he hβ hqcD
            hrateC hW0 hW1 P' l' hch' hP' hPcc' hcchi' hk'
            (fun j hj => CPair.le_trans (hlejfin j hj) hf'))
    | isTrue hA =>
      have hk0prev : sAt en ed (firstGE en ed C.fin.cert.lo 1 (n + 2) - 1)
          ≤ C.fin.cert.lo := by
        match Nat.eq_or_lt_of_le hk0pos with
        | Or.inl h1 =>
          rw [← h1]
          exact hunitFin
        | Or.inr h1 =>
          refine (CPair.le_total _ _).resolve_right
            (ground.firstAt_below (fun m => C.fin.cert.lo ≤ sAt en ed m)
              (n + 2) 1 _ ?_ ?_)
          · refine Nat.le_of_succ_le_succ ?_
            show 1 + 1 ≤ firstGE en ed C.fin.cert.lo 1 (n + 2) - 1 + 1
            rw [hk0e]
            exact h1
          · show firstGE en ed C.fin.cert.lo 1 (n + 2) - 1 + 1
              ≤ firstGE en ed C.fin.cert.lo 1 (n + 2)
            rw [hk0e]
            exact Nat.le_refl _
      have hk0b : sAt en ed (firstGE en ed C.fin.cert.lo 1 (n + 2))
          ≤ C.fin.b := by
        have hstep := stepClear_step C.fin.cert.lo C.fin.b C.e0n C.e0d hstF
          (firstGE en ed C.fin.cert.lo 1 (n + 2) - 1) en ed he hk0prev
        rw [hk0e] at hstep
        exact hstep
      have hhalf : 6 * (C.alN * firstGE en ed C.fin.cert.lo 1 (n + 2)
            * ground.posVal en)
          ≤ C.alD * ground.posVal ed :=
        cnatHalf C.alN C.alD (firstGE en ed C.fin.cert.lo 1 (n + 2)) en ed
          C.fin.b ⟨C.e0n, C.e0d⟩ hk0b (cleCeil en ed C.e0n C.e0d he) hhalfC
      have hs1 : C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
            * ground.posVal en
          ≤ C.alN * (3 * firstGE en ed C.fin.cert.lo 1 (n + 2))
            * ground.posVal en :=
        Nat.mul_le_mul_right (ground.posVal en)
          (Nat.mul_le_mul_left C.alN
            (oddCap (firstGE en ed C.fin.cert.lo 1 (n + 2)) hk0pos))
      have hs2 : C.alN * (3 * firstGE en ed C.fin.cert.lo 1 (n + 2))
            * ground.posVal en
          = 3 * (C.alN * firstGE en ed C.fin.cert.lo 1 (n + 2)
            * ground.posVal en) :=
        monEq [C.alN, firstGE en ed C.fin.cert.lo 1 (n + 2), ground.posVal en]
          (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.cst 3) (Mon.var 1)))
            (Mon.var 2))
          (Mon.mul (Mon.cst 3)
            (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))
          (by decide +kernel) (by decide +kernel)
      have hs3 : 3 * (C.alN * firstGE en ed C.fin.cert.lo 1 (n + 2)
            * ground.posVal en)
          ≤ 6 * (C.alN * firstGE en ed C.fin.cert.lo 1 (n + 2)
            * ground.posVal en) :=
        Nat.mul_le_mul_right
          (C.alN * firstGE en ed C.fin.cert.lo 1 (n + 2) * ground.posVal en)
          (by decide +kernel)
      have hXle : C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
            * ground.posVal en
          ≤ C.alD * ground.posVal ed :=
        Nat.le_trans hs1
          (Nat.le_trans (Nat.le_of_eq hs2) (Nat.le_trans hs3 hhalf))
      have hgX : C.alD * ground.posVal ed
            - C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
              * ground.posVal en
          + C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
              * ground.posVal en = C.alD * ground.posVal ed := by
        rw [Nat.add_comm]
        exact ground.natAddSubCancel hXle
      have ht2 : 2 * (C.alN * (3 * firstGE en ed C.fin.cert.lo 1 (n + 2))
            * ground.posVal en)
          = 6 * (C.alN * firstGE en ed C.fin.cert.lo 1 (n + 2)
            * ground.posVal en) :=
        monEq [C.alN, firstGE en ed C.fin.cert.lo 1 (n + 2), ground.posVal en]
          (Mon.mul (Mon.cst 2)
            (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.cst 3) (Mon.var 1)))
              (Mon.var 2)))
          (Mon.mul (Mon.cst 6)
            (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))
          (by decide +kernel) (by decide +kernel)
      have h2X : 2 * (C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
            * ground.posVal en) ≤ C.alD * ground.posVal ed :=
        Nat.le_trans (Nat.mul_le_mul_left 2 hs1)
          (Nat.le_trans (Nat.le_of_eq ht2) hhalf)
      have hXg : C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
            * ground.posVal en
          ≤ C.alD * ground.posVal ed
            - C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
              * ground.posVal en := by
        refine ground.leCancelR (C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2)
          + 1) * ground.posVal en) ?_
        rw [hgX, ← twoNat]
        exact h2X
      have hg : 1 ≤ C.alD * ground.posVal ed
          - C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
            * ground.posVal en := by
        match Nat.lt_or_ge 0 (C.alD * ground.posVal ed
          - C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
            * ground.posVal en) with
        | Or.inl hpos => exact hpos
        | Or.inr hzero =>
          have hz := Nat.le_antisymm hzero (Nat.zero_le _)
          have hX0 : C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
              * ground.posVal en = 0 := Nat.le_antisymm (by rw [← hz]; exact hXg)
                (Nat.zero_le _)
          refine absurd hDD ?_
          rw [← hgX, hz, hX0]
          exact Nat.not_succ_le_zero 0
      have hdom : ((r + 1) * C.qcN + C.ws) * ground.posVal ed
          ≤ 4 * C.qcD * (firstGE en ed C.fin.cert.lo 1 (n + 2)
            * firstGE en ed C.fin.cert.lo 1 (n + 2)) * ground.posVal en := by
        have hraw := cnatDom ((r + 1) * C.qcN + C.ws) (4 * C.qcD)
          (firstGE en ed C.fin.cert.lo 1 (n + 2)) en ed C.fin.cert.lo
          (Or.inr hfinU) hA hdomC
        refine Nat.le_trans (Nat.le_of_eq ?_)
          (Nat.le_trans hraw (Nat.le_of_eq ?_))
        · exact Nat.mul_comm ((r + 1) * C.qcN + C.ws) (ground.posVal ed)
        · exact (ground.mulAssoc (4 * C.qcD)
            (firstGE en ed C.fin.cert.lo 1 (n + 2)
              * firstGE en ed C.fin.cert.lo 1 (n + 2))
            (ground.posVal en)).symm
      have hws : 18 * ((r + 1) * C.qcD) * (C.alN * C.alN)
            * (firstGE en ed C.fin.cert.lo 1 (n + 2)
              * firstGE en ed C.fin.cert.lo 1 (n + 2)) * ground.posVal en
          ≤ C.ws * (C.alD * C.alD) * ground.posVal ed := by
        have hraw := cnatWs (18 * ((r + 1) * C.qcD) * (C.alN * C.alN))
          (C.ws * (C.alD * C.alD)) (firstGE en ed C.fin.cert.lo 1 (n + 2))
          en ed C.fin.b hk0b hwsC
        refine Nat.le_trans (Nat.le_of_eq ?_)
          (Nat.le_trans hraw (Nat.le_of_eq ?_))
        · exact ground.mulAssoc (18 * ((r + 1) * C.qcD) * (C.alN * C.alN))
            (firstGE en ed C.fin.cert.lo 1 (n + 2)
              * firstGE en ed C.fin.cert.lo 1 (n + 2)) (ground.posVal en)
        · exact Nat.mul_comm (ground.posVal ed) (C.ws * (C.alD * C.alD))
      match Nat.lt_or_ge cc (firstGE en ed C.fin.cert.lo 1 (n + 2)) with
      | Or.inr hk0cc =>
        exact tailCover r C.qcN C.qcD C.ws C.alN C.alD A B n
          (firstGE en ed C.fin.cert.lo 1 (n + 2))
          (C.alD * ground.posVal ed
            - C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
              * ground.posVal en) cc en ed hβ hqcD hrateC hgX hws hhalf
          hk0pos hdom hg hDD hk0cc hccn hW0 hW1
      | Or.inl hcck0 =>
        have hcclo : sAt en ed cc ≤ C.fin.cert.lo := by
          match Nat.lt_or_ge 0 cc with
          | Or.inr hcc0 =>
            rw [Nat.le_antisymm hcc0 (Nat.zero_le cc)]
            exact hunitFin
          | Or.inl hcc1 =>
            exact (CPair.le_total _ _).resolve_right
              (ground.firstAt_below (fun m => C.fin.cert.lo ≤ sAt en ed m)
                (n + 2) 1 cc hcc1 hcck0)
        exact coverFind r C.qcN C.qcD C.alN C.alD cc C.e0n C.e0d en ed C.fin _
          he hcclo C.postRest C.postSeg0 hchQ hsegP0 hgrFin hfinLo hfbLast
          hfinHi hP0cc
          (fun P' l' hch' hP' hgr' hlo' hb' _ hPcc' hcchi' hk' =>
            coverCoreA r C.qcN C.qcD C.ws C.alN C.alD A B n
              (firstGE en ed C.fin.cert.lo 1 (n + 2))
              (C.alD * ground.posVal ed
                - C.alN * (2 * firstGE en ed C.fin.cert.lo 1 (n + 2) + 1)
                  * ground.posVal en) cc C.e0n C.e0d en ed C.fin he hβ hqcD
              hrateC hgX hws hhalf hk0pos hdom hg hDD hA hk0b hfbHi hW0 hW1
              hcck0 P' l' hch' hP' hgr' hlo' hb' hPcc' hcchi' hk')
  have hcle : firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1))
      0 n ≤ n := by
    have hle := ground.firstAt_le
      (fun m => ¬ BPair.unit < wellWalk r A B en ed (m + 1)) n 0
    rw [Nat.zero_add] at hle
    exact hle
  have hbel : ∀ k, k < firstBad
      (fun k => BPair.unit < wellWalk r A B en ed (k + 1)) 0 n →
      BPair.unit < wellWalk r A B en ed (k + 1) :=
    fun k hk => Decidable.of_not_not
      (ground.firstAt_below _ n 0 k (Nat.zero_le k) hk)
  match Nat.lt_or_ge (firstBad
      (fun k => BPair.unit < wellWalk r A B en ed (k + 1)) 0 n) n with
  | Or.inr hge =>
    rw [certRevZero r A B en ed n
      (fun k hk => hbel k (by rw [Nat.le_antisymm hcle hge]; exact hk)) sp hsp]
    exact Nat.zero_le 1
  | Or.inl hlt =>
    have hQc : ¬ (BPair.unit < wellWalk r A B en ed
        (firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1)) 0 n
          + 1)) := by
      refine ground.firstAt_stop
        (fun m => ¬ BPair.unit < wellWalk r A B en ed (m + 1)) n 0 ?_
      rw [Nat.zero_add]
      exact hlt
    have hWc : BPair.unit < wellWalk r A B en ed
        (firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1)) 0 n) := by
      match Nat.lt_or_ge 0 (firstBad
          (fun k => BPair.unit < wellWalk r A B en ed (k + 1)) 0 n) with
      | Or.inr hc0 =>
        rw [Nat.le_antisymm hc0 (Nat.zero_le _), wellWalk_zero]
        exact ground.unitLtNat (Nat.le_refl 1)
      | Or.inl hc1 =>
        have hce : firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1))
            0 n - 1 + 1
            = firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1))
              0 n := by
          rw [Nat.add_comm]
          exact ground.natAddSubCancel hc1
        have hstep := hbel _ (by
          show firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1))
            0 n - 1 + 1
            ≤ firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1)) 0 n
          rw [hce]
          exact Nat.le_refl _)
        rw [hce] at hstep
        exact hstep
    have hcctop := posPhase r A B
      (firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1)) 0 n) C
      en ed ⟨hqcD, halD, hgrPos, hgrTerm, hploU, hptloU,
        hst1, hst2, hseedR, hchP, hsegP0, hcov0, hchQ, hgrFin, hfinU, hfinLo,
        hstF, hfbHi, hfbLast, hdomC, hwsC, hhalfC⟩ he hrateC hβ hQc
    match ground.leB_of_not_lt hQc with
    | Or.inr hstrict =>
      rw [certRevOne r A B en ed n _ hlt hbel
        (fun k hck hkn =>
          hneg _ (ground.leB_of_lt hWc) hstrict hcctop (Nat.le_of_lt hlt)
            (k + 1) (Nat.succ_le_succ hck) hkn) sp hsp]
      exact Nat.le_refl 1
    | Or.inl hone =>
      match Nat.lt_or_ge (firstBad
          (fun k => BPair.unit < wellWalk r A B en ed (k + 1)) 0 n + 1) n with
      | Or.inr hge2 =>
        have hn : firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1))
            0 n + 1 = n := Nat.le_antisymm hlt hge2
        rw [certRevZeroKern r A B en ed n
          (fun k hk => hbel k (by
            refine Nat.le_of_succ_le_succ ?_
            show k + 1 + 1
              ≤ firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1))
                  0 n + 1
            rw [hn]
            exact hk))
          (by rw [← hn]; exact hone) sp hsp]
        exact Nat.zero_le 1
      | Or.inl hlt2 =>
        have hrecc := wellWalk_rec r A B en ed
          (firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1)) 0 n)
        have hzero : (wellDiag r A B en ed
              (firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1))
                0 n + 2)
            * wellWalk r A B en ed
              (firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1))
                0 n + 1)).oneValue BPair.unit :=
          BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _) hone)
            (BPair.mul_unit _)
        have hW2 : wellWalk r A B en ed
            (firstBad (fun k => BPair.unit < wellWalk r A B en ed (k + 1))
              0 n + 2) < BPair.unit :=
          BPair.lt_congr (BPair.oneValue_refl _)
            (BPair.oneValue_trans hrecc hzero)
            (ground.ltB_addPos (ground.unitLtMul
              (ground.unitLtMul hβ hβ) hWc))
        rw [certRevOneMixed r A B en ed n _ hlt2 hbel
          (fun k hck hkn =>
            hneg _ (Or.inl (BPair.oneValue_symm hone)) hW2
              (CPair.le_trans hcctop (sAt_mono en ed (Nat.le_succ _)))
              (Nat.le_of_lt hlt2) (k + 1) (Nat.succ_le_succ hck) hkn) sp hsp]
        exact Nat.le_refl 1


end cornerpivot
