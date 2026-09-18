import MassGap.Serstable
import MassGap.Steinberg
import MassGap.Fusion
/-!
`lem:memberdata` — the member count and involution, the fusion
interface's two constructed fields at a member's table, with the
interface instantiations beneath them (`con:fusion`'s member
clause).

The producers run at the coroot presentation: a label is its
coroot list, the walk carrier the balance vectors, and every form
read goes through one cleared fundamental Gram — `gramOf`, row `i`
the adjugate solve of the Cartan rows at the scaled unit column at
its descent read (`elim.adjD`, the bordered descent's cofactors), the
whole matrix at one positive clearing scale
(the Cartan determinant against the doubled length denominator),
so numerators and denominators compare at matched scales
throughout.  The multiplicity family is the recursion's one solve
(`lem:memberdata`(i)): the dominant keys enter at the coroot box
under the top's `ρ`-dot cap filtered at the fold membership
(`domKeys`, the transposed Cartan's adjugate solve at its descent
read the membership test), the solve descends the
cleared `ρ`-dots from the top (`famGo`, the trace recursion's
display read per key with each moved count at its dominant image
through the dominance walk `domWalk`, a vacant gap, starved walk
or inexact cofactor refusing the whole family), and the full
family expands the dominant keys over their reflection orbits at
their counts (`multFam`), the fold witnesses `foldWits` the
support reads' own data.  The member count is the
member display's gap read at the family fold (`countM`,
`lem:memberdata`(i)'s display fold): each occupied content's
moved key walks to its dominant image at the walk's letter
parity (`walkP`), a walk ending at the shifted second factor the
tie's one element at the regular reads and every further end off
the ties — the row the occupied targets over the fused window
(`rowM`).  The letters' closure at a shifted key (`orbitFam`,
one parity per image at the regular reads) is `con:sertables`'
word list, the displayed signed-permutation lists
(`sertables.serWeylB/C/D`) reading it one member per element
(`con:sertables`' one-member-each read).  The
involution is the shifted walk (`lem:memberdata`(ii)): the dual
label joined to `ρ` is the dominant image of the shifted key's
balance partner (`dualM`). The returned dominance key satisfies
`memberchar.lamRead` at `domWalk_lam`, and the returned dual label
has the coroot width (`dualM_length`). A reflection-closed finite
family completes the dominance walk at its rho-dot gap
(`domWalk_complete`) or its cardinality (`domWalk_finite`). At G2
the negative shifted key follows six alternating simple letters,
giving `dualM_G2` at every label and every step count from six.

The natural support witnesses read exactly through the computed
Cartan solve (`foldSolve_decode`, `foldWits_eq`). At a natural Gram
with positive row sums, every supported dominant content belongs
to the actual key enumeration (`domKeys_support`). The numerator
at higher dominant counts is the trace correction (`numAt_gSum`),
and its cofactor is the family's count (`numAt_rec_count`). The
descending recursion therefore reads each dominant multiplicity
at every label (`domFam_lookup`), at the five fixed members'
stored fuels (`domFam_lookup_G2/F4/E6/E7/E8`). A framed invariant
family at those support, top and recursion reads has one count at
every content (`multiplicity_unique`). The orbit expansion reads
that family where the computed orbits have their seed as sole
dominant key and preserve reflection counts (`multFam_read`).
Completed dominance walks, numerators and dominant families keep
their values at every larger fuel (`domWalk_more`, `numAt_more`,
`domFam_more`). Once the rank-width orbits complete as well,
the full family, fusion count and row keep their values and list
orders at every larger fuel (`multFam_more`, `countM_more`,
`rowM_more`), and the shifted dual walk does (`dualM_more`).
These reads hold at the stored B/C/D and G2 fuels (`fuel_more_B`,
`fuel_more_C`, `fuel_more_D`, `fuel_more_G2`).

The generated orbits have
canonical coroot keys (`orbitSet_shape`, `orbitFam_shape`), and the
multiplicity family satisfies `memberchar.mShapeRead` at every top
(`multFam_shape`). The orbit queue is reflection-closed, is contained
in every closed family at its seed, and completes at a distinct
reference family's count where simple-letter images separate off
the input key (`orbitSet_closed`, `orbitSet_least`, `orbitSet_complete`).
The graded keys read the ungraded list exactly (`orbitFam_keys`),
with reflection counts and the seed's parity read at `orbitFam_close`
and `orbitFam_top`; the multiplicity family's symmetry is
`multFam_sym` at the orbit reads. At B/C/D and G2 the actual
stored-fuel orbits have their natural seed as their sole dominant
key, including chamber walls (`orbitSet_dom_B`, `orbitSet_dom_C`,
`orbitSet_dom_D`, `orbitSet_dom_G2`). The full families' dominant
counts are the computed table's lookups; the series' full counts
are determined by those lookups (`multFam_read_B`,
`multFam_read_C`, `multFam_read_D`). At G2 every invariant block
family at the support, top and trace reads is the computed full
family at every content (`multFam_read_G2`), and its decoded
support, top and recursion reads hold on that producer
(`multFam_reads_G2`). Supported families pass the fold test at
every occupied content, and the Cartan decoder constructs support
witnesses after relisting at equal multiplicity counts
(`supportRead_foldTest`, `supportRead_counts`). The recursion, support and Gram reads are
`memberchar.recRead`, `foldWits`' solves and the Grams' defining
reads at the produced families and displayed Weyl lists. Each
walk's step count is stated data, with a starved walk reading the
vacant list; every reflection along a walk
or a closure is the letter's join read (`assembly.reflF`,
`con:gentable`'s display), one value with the matrix action at
`reflF_eq`.

The parity walk's graded-count transport (`walkP_wCount`) and
the regular orbit's dominant singleton (`walkP_orbit_count`)
identify the actual family fold with the shifted orbit's two
convolution counts (`countM_conv`, `countM_orbit_conv`). The reads
hold at the actual B/C/D/G2 stored-fuel queues (`countM_conv_B`,
`countM_conv_C`, `countM_conv_D`, `countM_conv_G2`). G2's adjugate
gap matrices give natural support witnesses for every dominant
seed (`weylG2_foldTest`), and the actual shifted queues satisfy
the five alternant reads (`orbitFam_character_G2`). The character
identity holds at those queues for every family with the block's
trace reads (`identityRead_G2`, `multFam_identity_G2`). A stated
tensor-product exhaustion at those reads identifies the implemented
count with the channel-top multiplicity (`countM_exhaustion_G2`),
keeps the count under the factors' exchange (`countM_comm_G2`),
and gives complete row support where the channel tops have their
natural support witnesses (`rowM_exhaustion_G2`).

The unit label's dominant window is its singleton (`domKeys_unit`),
the recursion reads its one top count (`domFam_unit`), and its
reflection queue processes one entry (`orbitSet_unit`). Thus the
actual unit family is a single zero content at every positive
queue fuel (`multFam_unit`), the left-unit fusion count is label
equality (`countM_unit_left`), and the unit row is the second
label alone (`rowM_unit_left`). These give the interface's unit
counts at arbitrary padded spellings and its unit rows at every
canonical label for all five fixed members (`fusion.unitCount_dataOf`,
`fusion.unitRowLaw_dataOf` at the member Cartan solves).

The instantiations (`con:fusion`): `fusion.dataB`, `dataC` and
`dataD` at the rank and `dataG2`, `dataF4`, `dataE6`, `dataE7`
and `dataE8` at the fixed tables, every field the table's own
derived read — the labels coroot lists at the padded equality,
`θ` the theta fold's coroot list (`thetaKey`, one read at every
member), the count and row the producers', the involution the
shifted walk's, the dimension the member gap product's exact
cofactor (`dimM`, `cor:weyldim`'s member display), the cleared
Casimir the Gram's quadratic read (`c2M`), the base the
`θ`-row diagonal's own count (`prop:row`'s member read), the
enumeration the coroot box at the Casimir cap (`belowM`), and the
class data the displayed remainder reads per member
(`lem:chargedcell`(i)'s class groups at the coroot lists) with
the winding floors the end members' Casimir reads, and the
presentation field at the member's generating table
(`fiber.presT` over `con:memtable`'s tables — `B` and `D` at the
defining table joined to the spinor's, `C` at the defining table,
`G_2` and `F_4` at the folds, `E_8` at its adjoint table, `E_7`
and `E_6` at the `56` and the `27` with its dual inside it — with
the reach lists, each fundamental's top among the keys or in the
stated product of two earlier fundamentals' blocks (`reachB`,
`reachC`, `reachD` and the fixed members' displayed lists), and
the fundamentals' involution (`fundInv`)).  The interface
cutoff bounds and nonunit reads hold at every cutoff
(`belowSound_dataOf`, `belowNonunit_dataOf`), the unit with that
list distinct (`below_distinct_dataOf`); every listed row target
has positive count (`row_count_pos_dataOf`), and the row's targets
are distinct (`row_distinct_dataOf`). Natural Gram rows with
occupied sums give positivity and cutoff nesting (`casPos_dataOf`,
`belowNest_dataOf`), with the five fixed members at their displayed
adjugate rows. The unit-class constructors satisfy the three class
laws at every label (`clsLaws_dataFixed`), and G2's shifted dual
fixes every label at the interface equality, its Casimir and its
dimension (`dual_dataG2`, `casDualLaw_dataG2`, `dimDualLaw_dataG2`).
The B/C/D stored-fuel walks return the unique strictly dominant
key in their regular displayed orbit. B and C duals fix the padded
label; the D dual fixes it at even rank and exchanges the final two
simple coordinates at odd rank. These actual duals are involutions
and preserve dimension and the cleared Casimir. Each dual class
joins its original class to the unit, with the D class code
reversed in the four-class cycle at odd rank. For D the positive
root factors pair across the final exchange, and the computed Gram
respects the same symmetry by its adjugate equation; every leading
Cartan minor is nonzero because the matrix is the Gram of the
independent displayed simple roots.

The principal specialization reads the actual G2 queues at word
reversal (`orbitFam_dmap_exchange_G2`), their counts those of the
displayed Weyl family (`orbitFam_counts_G2`). At the mathematical
block's shape, symmetry, support, top and trace reads, the Weyl
product is the family's count (`dimM_family_G2`), and the actual
multiplicity producer's count (`dimM_multFam_G2`). At a naturally
supported tensor exhaustion the computed row satisfies the
dimension identity (`dimM_exhaustion_G2`, `fusion.dimLaw_dataG2`).
The common exhaustion gives interface commutativity and complete
row support (`fusion.commLaw_dataG2`, `fusion.rowLaw_dataG2`).
Natural support forces the joined top's one Cartan count
(`countM_cartan_G2`, `fusion.cartanLaw_dataG2`), and the character
identity at shifted dominant targets gives the right-unit count
and row (`countM_unit_right_G2`, `rowM_unit_right_G2`). Singleton
rows share the positive-count filter read (`rowM_single`).
The interface reads the right-unit count at padded equality and
the row at canonical width (`fusion.rightUnitCount_dataG2`,
`fusion.rightUnitRow_dataG2`).

The product's bounds depend on the root table alone. Positive
rho factors give a positive dimension and unit dimension one
(`dimM_pos`, `dimM_unit`). At a nonunit label an occupied simple
coordinate doubles its own factor while every other factor grows,
so the dimension is at least two (`dimM_ge_two`) and equals one
exactly at the unit (`dimM_eq_one`). The reads hold at every B/C/D
rank in their domains and at every fixed member, using the
positive root folds and their simple-root members.

The actual G2 generating construction's occupancy family
(`fiber.blockWeights`) has its natural support and unique top at
every two-coroot label (`blockWeights_support_G2`,
`blockWeights_topRead_G2`). Each occupied simple lowering increments
its own natural support coefficient, and the stored span's tail
has an occupied fold (`blockSpanT_top_tail_G2`); the Cartan solve
excludes a return to the top. The support witnesses are the actual
`foldWits` reads, and every family member's rho height is at or
below its label's (`blockWeights_height_G2`).
-/

namespace memberdata
open ground

/-- A coroot list on the balance carrier. -/
def natV (m : List Nat) : List BPair := m.map BPair.ofNat

/-- The coroot lists' pairing reads the counts' own, the fold's
count read entrywise. -/
theorem natV_dot : ∀ m Y : List Nat,
    (elim.dotP (natV m) (natV Y)).oneValue
      (BPair.ofNat (ground.dotNat m Y))
  | [], _ => BPair.oneValue_refl _
  | _ :: _, [] => BPair.oneValue_refl _
  | a :: m, b :: Y => by
    show (BPair.ofNat a * BPair.ofNat b
        + elim.dotP (natV m) (natV Y)).oneValue
      (BPair.ofNat (a * b + ground.dotNat m Y))
    exact BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.ofNat_add (a * b) (ground.dotNat m Y))
      (BPair.add_congr (BPair.ofNat_mul a b)
        (BPair.oneValue_symm (natV_dot m Y))))

/-- The rank padding: a label read at the table's key count. -/
def padN (l : Nat) (m : List Nat) : List Nat :=
  (List.range l).map (fun k => getAt 0 m k)

/-- Padding reads one coordinate per key of the stated rank. -/
theorem padN_length (l : Nat) (m : List Nat) : (padN l m).length = l :=
  ground.length_mapRange _ _

/-- A coroot list of the stated rank is fixed by the coordinate
read (`lem:memberdata`'s coroot presentation). -/
theorem padN_of_length (l : Nat) (m : List Nat) (h : m.length = l) :
    padN l m = m := ground.range_map_getAt 0 l m h

/-- Refusal of padded equality to the unit means that the
padded coroot list has an occupied coordinate. -/
theorem padN_ne_unit (n : Nat) (a : List Nat)
    (h : (padN n a == padN n (List.replicate n 0)) = false) :
    padN n a ≠ List.replicate n 0 := by
  intro he
  rw [padN_of_length n _ (ground.length_replicate _ _), he, ground.listEqBeq] at h
  exact Bool.noConfusion h

/-- A balance vector's coroot list at the magnitudes, the
upper-side gaps at a dominant vector. -/
def natsOf (v : List BPair) : List Nat := v.map BPair.marginN

/-- The shifted key: the coroot list joined to `ρ`, normed. -/
def shiftV (t : gentable.Table) (m : List Nat) : List BPair :=
  poly.pnorm (elim.vecAdd (natV m) (sertables.rhoV t))

/-- Shifting a label of the table's width keeps that width. -/
theorem shiftV_length (t : gentable.Table) (a : List Nat) (ha : a.length = t.rank) :
    (shiftV t a).length = t.rank := by
  show (poly.pnorm (elim.vecAdd (natV a) (sertables.rhoV t))).length = t.rank
  rw [poly.pnorm_length]
  exact elim.length_vecAdd _ _ t.rank
    ((ground.length_map BPair.ofNat a).trans ha) (ground.length_replicate _ t.rank)

/-- The shifted coroot entry is the label coordinate's successor. -/
theorem shiftV_read (t : gentable.Table) (a : List Nat) (ha : a.length = t.rank)
    (i : Nat) (hi : i < t.rank) :
    (ground.getAt BPair.unit (shiftV t a) i).oneValue (BPair.ofNat (ground.getAt 0 a i + 1)) := by
  have h := poly.oneValue_getAt i (poly.pnorm_oneValue (elim.vecAdd (natV a) (sertables.rhoV t)))
  rw [elim.getAt_vecAdd _ _ i (by change i < (a.map BPair.ofNat).length; rw [ground.length_map, ha]; exact hi)
      (by rw [sertables.rhoV, ground.length_replicate]; exact hi)] at h
  have hn : ground.getAt BPair.unit (natV a) i = BPair.ofNat (ground.getAt 0 a i) :=
    ground.getAt_map 0 BPair.unit BPair.ofNat a i (by rw [ha]; exact hi)
  have hr : ground.getAt BPair.unit (sertables.rhoV t) i = BPair.ofNat 1 :=
    ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank i hi
  rw [hn, hr] at h
  exact BPair.oneValue_trans h (BPair.oneValue_symm (BPair.ofNat_add _ _))

/-- The shifted key has strictly positive simple coroot entries. -/
theorem shiftV_pos (t : gentable.Table) (a : List Nat) (ha : a.length = t.rank) :
    ∀ i, i < t.rank → BPair.unit < ground.getAt BPair.unit (shiftV t a) i := by
  intro i hi
  exact BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (shiftV_read t a ha i hi))
    (ground.unitLtNat (Nat.succ_pos _))

/-- Reading the shifted key's margins and withdrawing one returns
the original coroot label. -/
theorem shiftV_unshift (t : gentable.Table) (a : List Nat) (ha : a.length = t.rank) :
    (natsOf (shiftV t a)).map (fun n => n - 1) = a := by
  change ((shiftV t a).map BPair.marginN).map (fun n => n - 1) = a
  refine ground.getAt_ext 0 _ _ (by rw [ground.length_map, ground.length_map, shiftV_length t a ha, ha]) ?_
  intro i hi
  rw [ground.length_map, ground.length_map, shiftV_length t a ha] at hi
  rw [ground.getAt_map 0 0 (fun n => n - 1) _ i (by rw [ground.length_map, shiftV_length t a ha]; exact hi),
    ground.getAt_map BPair.unit 0 BPair.marginN _ i (by rw [shiftV_length t a ha]; exact hi),
    BPair.marginN_congr (shiftV_read t a ha i hi), BPair.marginN_ofNat, ground.addSubSelfR]

/-- Shifting preserves equality of rank-width natural labels;
the margin read followed by the predecessor reads each label back. -/
theorem shiftV_inj (t : gentable.Table) (a b : List Nat)
    (ha : a.length = t.rank) (hb : b.length = t.rank) (h : shiftV t a = shiftV t b) : a = b := by
  have he := congrArg (fun w => (natsOf w).map (fun n => n - 1)) h
  rw [shiftV_unshift t a ha, shiftV_unshift t b hb] at he
  exact he

/-- The scaled unit column. -/
private def scaledE (n i s : Nat) : List BPair :=
  (List.range n).map (fun k => if k == i then BPair.ofNat s else BPair.unit)

/-- The cleared fundamental Gram: row `i` the adjugate solve of the
Cartan rows at the length-scaled unit column, so the Cartan rows
against row `i` read the determinant-scaled length diagonal — the
whole matrix the fundamentals' pairings at the one positive
clearing scale, the Cartan determinant against the doubled length
denominator (`con:sertables`' adjugate-row form reads at every
member). -/
def gramOf (t : gentable.Table) : elim.Mat :=
  (List.range t.rank).map (fun i =>
    poly.pnorm (elim.adjD t.cartan (scaledE t.rank i (getAt 0 t.lenNums i))))

/-- The computed Gram has one row per simple key, each row of the
Cartan order. -/
theorem gramOf_shape (t : gentable.Table) (h : t.cartan.length = t.rank) :
    (gramOf t).length = t.rank ∧ elim.rowsLen t.rank (gramOf t) := by
  refine ⟨ground.length_mapRange _ _, elim.rowsLen_map _ _ _ (fun i _ => ?_)⟩
  rw [poly.pnorm_length, elim.length_adjD, h]

private theorem scaledE_adjSwap (n t i s : Nat) (ht : t + 1 < n) :
    ground.adjSwap t (scaledE n i s) = scaledE n (ground.swapIx t (t + 1) i) s := by
  have he (a b : Nat) : (ground.swapIx t (t + 1) a = b) ↔ (a = ground.swapIx t (t + 1) b) :=
    ⟨fun h => by rw [← h, ground.swapIx_invol], fun h => by rw [h, ground.swapIx_invol]⟩
  refine ground.getAt_ext BPair.unit _ _ (by rw [ground.length_adjSwap]; exact ground.length_mapRange _ n |>.trans (ground.length_mapRange _ n).symm) ?_
  intro j hj
  rw [ground.length_adjSwap, scaledE, ground.length_mapRange] at hj
  rw [ground.getAt_adjSwap BPair.unit t _ (by rw [scaledE, ground.length_mapRange]; exact ht)]
  have hjs := ground.swapIx_lt (Nat.lt_trans (Nat.lt_succ_self t) ht) ht j hj
  unfold scaledE
  rw [ground.getAt_map 0 BPair.unit _ _ _ (by rw [ground.length_range]; exact hjs), ground.getAt_range _ _ hjs,
    ground.getAt_map 0 BPair.unit _ _ j (by rw [ground.length_range]; exact hj), ground.getAt_range _ j hj]
  by_cases hjv : ground.swapIx t (t + 1) j = i
  · rw [ground.eqBeqOf hjv, ground.eqBeqOf ((he j i).1 hjv)]
  · rw [ground.neBeqOf hjv, ground.neBeqOf (fun h => hjv ((he j i).2 h))]

/-- The Gram produced by the D Cartan descent respects the final
two simple keys' exchange. -/
theorem gramOf_forkSwap_D (k i : Nat) (hi : i < k + 2) :
    poly.oneValue (ground.adjSwap k (ground.getAt [] (gramOf (sertables.tableD (k + 2))) i))
      (ground.getAt [] (gramOf (sertables.tableD (k + 2))) (ground.swapIx k (k + 1) i)) := by
  let t := sertables.tableD (k + 2)
  have ht : t.cartan.length = k + 2 := ground.matOf_length _ _ _
  have hrows : elim.rowsLen t.cartan.length t.cartan := by
    rw [ht]; exact elim.rowsLen_matOf _ _ _
  have his := ground.swapIx_lt (Nat.lt_succ_of_lt (Nat.lt_succ_self k)) (Nat.lt_succ_self (k + 1)) i hi
  have hlen (j : Nat) (hj : j < k + 2) : ground.getAt 0 t.lenNums j = 2 :=
    ground.getAt_replicate 0 2 (k + 2) j hj
  have hg (j : Nat) (hj : j < k + 2) : ground.getAt [] (gramOf t) j
      = poly.pnorm (elim.adjD t.cartan (scaledE (k + 2) j 2)) := by
    unfold gramOf
    rw [ground.getAt_map 0 [] _ _ j (by rw [ground.length_range]; exact hj),
      ground.getAt_range t.rank j hj, hlen j hj]
    rfl
  rw [hg i hi, hg _ his]
  have hs := elim.adjD_adjSwap t.cartan hrows
    (fun m hm => sertables.cartanD_lead k m (by rw [ht] at hm; exact hm)) k
    (by rw [ht]; exact Nat.lt_succ_self _) (fun j hj =>
      by rw [sertables.cartanD_forkSwap k j (by rw [ht] at hj; exact hj)]; exact poly.oneValue_refl _)
    (scaledE (k + 2) i 2) (by rw [scaledE, ground.length_mapRange, ht])
  rw [scaledE_adjSwap (k + 2) k i 2 (Nat.lt_succ_self _)] at hs
  refine poly.oneValue_of_entries _ _ (by rw [ground.length_adjSwap, poly.pnorm_length,
    poly.pnorm_length, elim.length_adjD, elim.length_adjD]) ?_
  intro j _
  rw [ground.getAt_adjSwap BPair.unit k _ (by rw [poly.pnorm_length, elim.length_adjD, ht]; exact Nat.lt_succ_self _)]
  refine BPair.oneValue_trans (poly.oneValue_getAt _ (poly.pnorm_oneValue _)) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (poly.oneValue_getAt _ (poly.pnorm_oneValue _)))
  have hh := poly.oneValue_getAt j hs
  rw [ground.getAt_adjSwap BPair.unit k _ (by rw [elim.length_adjD, ht]; exact Nat.lt_succ_self _)] at hh
  exact BPair.oneValue_symm hh

/-- The cleared form at the produced Gram, normed
(`sertables.dotG`'s read at the canonical representative). -/
def formC (G : elim.Mat) (x y : List BPair) : BPair :=
  BPair.norm (sertables.dotG G x y)

/-- The first lower-side key. -/
private def lowGo : List BPair → Nat → Option Nat
  | [], _ => none
  | x :: tl, k => if x < BPair.unit then some k else lowGo tl (k + 1)

/-- The parity walk: the dominance walk with its letter count's
parity, one letter per raise (`lem:memberdata`(i), the walk's
letter count reading the element's parity at the reversed word's
class); a starved walk refuses the read. -/
def walkP (t : gentable.Table) :
    Nat → List BPair → Bool → Option (List BPair × Bool)
  | 0, v, p =>
    match lowGo v 0 with
    | none => some (v, p)
    | some _ => none
  | fuel + 1, v, p =>
    match lowGo v 0 with
    | none => some (v, p)
    | some i => walkP t fuel (assembly.reflF t i v) (!p)

/-- The dominance walk: raise at the first lower-side key until
every key sits at or beyond the unit, the parity walk's key read;
a starved walk reads the vacant list. -/
def domWalk (t : gentable.Table) (fuel : Nat) (v : List BPair) :
    List BPair :=
  match walkP t fuel v false with
  | none => []
  | some q => q.1

/-- The dual label at the shifted walk (`lem:memberdata`(ii)): the
label joined to `ρ`, read at its balance partner's dominant image,
withdrawn by `ρ`. -/
def dualM (t : gentable.Table) (fuel : Nat) (a : List Nat) : List Nat :=
  (natsOf (domWalk t fuel
    (poly.pnorm (poly.neg (shiftV t a))))).map (fun x => x - 1)

private def memFstB (v : List BPair) :
    List (List BPair × Bool) → Bool
  | [] => false
  | p :: tl => (p.1 == v) || memFstB v tl

/-- The orbit queue expands one member per step, appending the
images refused by the accumulated-key test to both lists. A
queue at the step bound reads the vacant list. -/
private def orbitGo {α : Type} (step : α → List α)
    (known : α → List α → Bool) : Nat → List α → List α → List α
  | 0, acc, [] => acc
  | 0, _, _ :: _ => []
  | _ + 1, acc, [] => acc
  | fuel + 1, acc, h :: tl =>
    let fresh := (step h).filter (fun q => !(known q acc))
    orbitGo step known fuel (acc ++ fresh) (tl ++ fresh)

/-- The graded orbit family at a shifted key: the reflection
images with their parities, one parity per image at the shifted
key's regular reads (`con:sertables`). -/
def orbitFam (t : gentable.Table) (fuel : Nat) (v : List BPair) :
    List (List BPair × Bool) :=
  orbitGo (fun h => (List.range t.rank).map
      (fun i => (assembly.reflF t i h.1, !h.2)))
    (fun q acc => memFstB q.1 acc) fuel
    [(poly.pnorm v, false)] [(poly.pnorm v, false)]

/-- A content's reflection orbit, the closure at the letters. -/
def orbitSet (t : gentable.Table) (fuel : Nat) (v : List BPair) :
    List (List BPair) :=
  orbitGo (fun h => (List.range t.rank).map (fun i => assembly.reflF t i h))
    (fun q acc => ground.containsB acc q) fuel [poly.pnorm v] [poly.pnorm v]

/-- The fold solve at a gap: the transposed Cartan's adjugate
column at its descent read, the natural simple fold's
determinant-scaled coefficients (`con:gentable`'s dominance order,
the coefficients one solve at the simple folds' injectivity). -/
def foldSolve (t : gentable.Table) (v : List BPair) :
    List BPair :=
  elim.adjD (elim.transposeM t.cartan) v

/-- The transposed Cartan's determinant at the descent read, the
fold solve's clearing scale. -/
def foldDet (t : gentable.Table) : Nat :=
  BPair.marginN (elim.detD (elim.transposeM t.cartan))

/-- The fold-membership test: every solved entry at or beyond the
unit and at the determinant's own multiple. -/
def foldTest (t : gentable.Table) (v : List BPair) : Bool :=
  let d := foldDet t
  (foldSolve t v).all (fun x =>
    !(x < BPair.unit) && (BPair.marginN (BPair.norm x) % d == 0))

/-- At a natural simple-root fold, each computed adjugate entry
reads the corresponding coefficient at the determinant's scale. -/
theorem foldSolve_read (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (v : List BPair) (hv : v.length = t.rank) (c : List Nat)
    (hc : c.length = t.rank) (hfold : poly.oneValue (assembly.cartanFold t c) v) :
    poly.oneValue (foldSolve t v)
      (elim.vecScale (elim.detD (elim.transposeM t.cartan)) (natV c)) := by
  let G := elim.transposeM t.cartan
  have hGl : G.length = t.rank := elim.transposeLen t.cartan (elim.rowsLen_of_sqAt hsq) (elim.sqAt_len hsq)
  have hGr : elim.rowsLen G.length G := by
    rw [hGl]
    exact elim.rowsLen_cast (elim.sqAt_len hsq) (elim.rowsLen_transposeM t.cartan)
  have hz : (natV c).length = G.length := (ground.length_map BPair.ofNat c).trans (hc.trans hGl.symm)
  have he : poly.oneValue (elim.matVec G (natV c)) v :=
    poly.oneValue_trans (poly.oneValue_symm (assembly.cartanFold_matVec t hsq c hc)) hfold
  exact poly.oneValue_trans (elim.adjD_solve G hGr
    (fun k hk => hlead k (by rw [← hGl]; exact hk)) (natV c) v hz (hv.trans hGl.symm) he)
    (elim.vecScale_congr (BPair.oneValue_symm (elim.detD_eq G hGr)) (natV c))

/-- A computed fold cofactor is the stated natural coefficient
at the positive determinant's scale. -/
theorem foldSolve_coefficient (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (v : List BPair) (hv : v.length = t.rank) (c : List Nat)
    (hc : c.length = t.rank) (hfold : poly.oneValue (assembly.cartanFold t c) v)
    (i : Nat) (hi : i < t.rank) :
    (ground.getAt BPair.unit (foldSolve t v) i).oneValue
      (BPair.ofNat (foldDet t * ground.getAt 0 c i)) := by
  have hr := poly.oneValue_getAt i (foldSolve_read t hsq hlead v hv c hc hfold)
  rw [elim.getAt_vecScale _ (natV c) i (by rw [natV, ground.length_map, hc]; exact hi), natV,
    ground.getAt_map 0 BPair.unit BPair.ofNat c i (by rw [hc]; exact hi)] at hr
  exact BPair.oneValue_trans hr (BPair.oneValue_trans
    (BPair.mul_congr (BPair.ofNat_marginN (ground.leB_of_lt hdet)) (BPair.oneValue_refl _))
    (BPair.oneValue_symm (BPair.ofNat_mul _ _)))

/-- Decoding the computed cofactors returns the stated natural
coefficient vector exactly. -/
theorem foldSolve_decode (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (v : List BPair) (hv : v.length = t.rank) (c : List Nat)
    (hc : c.length = t.rank) (hfold : poly.oneValue (assembly.cartanFold t c) v) :
    (foldSolve t v).map (fun x => x.norm.marginN / foldDet t) = c := by
  have hl : (foldSolve t v).length = t.rank := (elim.length_adjD _ _).trans
    (elim.transposeLen t.cartan (elim.rowsLen_of_sqAt hsq) (elim.sqAt_len hsq))
  refine ground.getAt_ext 0 _ _ (by rw [ground.length_map, hl, hc]) ?_
  intro i hi
  rw [ground.length_map, hl] at hi
  rw [ground.getAt_map BPair.unit 0 _ _ i (by rw [hl]; exact hi),
    BPair.marginN_congr (BPair.norm_oneValue _),
    BPair.marginN_congr (foldSolve_coefficient t hsq hlead hdet v hv c hc hfold i hi),
    BPair.marginN_ofNat, Nat.mul_comm]
  exact ground.divMulSelf _ (foldDet t) (BPair.marginN_pos hdet)

/-- A natural simple-root fold passes the actual fold-membership
test. The computed cofactors are nonnegative determinant multiples. -/
theorem foldTest_complete (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (v : List BPair) (hv : v.length = t.rank) (c : List Nat)
    (hc : c.length = t.rank) (hfold : poly.oneValue (assembly.cartanFold t c) v) :
    foldTest t v = true := by
  have hsl : (foldSolve t v).length = t.rank := (elim.length_adjD _ _).trans
    (elim.transposeLen t.cartan (elim.rowsLen_of_sqAt hsq) (elim.sqAt_len hsq))
  apply ground.all_of_getAt BPair.unit
  intro i hi
  have hi' : i < t.rank := by rw [← hsl]; exact hi
  have hp := foldSolve_coefficient t hsq hlead hdet v hv c hc hfold i hi'
  have hnon : ¬ ground.getAt BPair.unit (foldSolve t v) i < BPair.unit :=
    ground.leB_not_lt (ground.leB_congr_right (BPair.oneValue_symm hp) (ground.unitLeOfNat _))
  have hm : (BPair.norm (ground.getAt BPair.unit (foldSolve t v) i)).marginN
      = foldDet t * ground.getAt 0 c i :=
    (BPair.marginN_congr (BPair.oneValue_trans (BPair.norm_oneValue _) hp)).trans (BPair.marginN_ofNat _)
  change (!(decide (ground.getAt BPair.unit (foldSolve t v) i < BPair.unit)) &&
    ((BPair.norm (ground.getAt BPair.unit (foldSolve t v) i)).marginN % foldDet t == 0)) = true
  rw [decide_eq_false hnon, hm, Nat.mul_comm (foldDet t), ground.modMulSelf]
  rfl

/-- A member's fold witness at a top: the fold solve read at the
determinant's cofactor (`thm:memberchar`'s support witnesses). -/
def foldWits (t : gentable.Table) (lam nu : List BPair) : List Nat :=
  let d := foldDet t
  (foldSolve t (elim.vecAdd lam (poly.neg nu))).map (fun x =>
    BPair.marginN (BPair.norm x) / d)


/-- Passing the fold test gives a natural coefficient vector
whose simple-root fold is the tested gap. The positive Cartan
determinant cancels the descent solve's exact cofactors. -/
theorem foldTest_sound (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (v : List BPair) (hv : v.length = t.rank) (hpass : foldTest t v = true) :
    let c := (foldSolve t v).map (fun x => BPair.marginN (BPair.norm x) / foldDet t)
    c.length = t.rank ∧ poly.oneValue (assembly.cartanFold t c) v := by
  let G := elim.transposeM t.cartan
  let d := foldDet t
  let c := (foldSolve t v).map (fun x => BPair.marginN (BPair.norm x) / d)
  have hGl : G.length = t.rank := elim.transposeLen t.cartan (elim.rowsLen_of_sqAt hsq) (elim.sqAt_len hsq)
  have hGr : elim.rowsLen G.length G := by
    rw [hGl]
    exact elim.rowsLen_cast (elim.sqAt_len hsq) (elim.rowsLen_transposeM t.cartan)
  have hd : 0 < d := BPair.marginN_pos hdet
  have hsl : (foldSolve t v).length = t.rank := (elim.length_adjD G v).trans hGl
  have hcl : c.length = t.rank := (ground.length_map _ _).trans hsl
  have hbits (i : Nat) (hi : i < G.length) :
      BPair.unit ≤ ground.getAt BPair.unit (foldSolve t v) i
        ∧ (ground.getAt BPair.unit (foldSolve t v) i).marginN % d = 0 := by
    have hi' : i < (foldSolve t v).length := by rw [hsl, ← hGl]; exact hi
    have hb := ground.all_getAt BPair.unit (foldSolve t v) hpass i hi'
    have hparts := ground.andSplitB hb
    have hp : ¬ ground.getAt BPair.unit (foldSolve t v) i < BPair.unit := by
      intro h
      have hf := hparts.1
      rw [decide_eq_true h] at hf
      exact Bool.noConfusion hf
    refine ⟨ground.leB_of_not_lt hp, ?_⟩
    have hm := ground.beqEqOf hparts.2
    rw [BPair.marginN_congr (BPair.norm_oneValue _)] at hm
    exact hm
  have hnat : natV c = (elim.adjD G v).map (fun x => BPair.ofNat (x.marginN / d)) := by
    change (((foldSolve t v).map (fun x => x.norm.marginN / d)).map BPair.ofNat) = _
    rw [ground.map_map]
    exact ground.map_congr_all _ _ (fun x => by rw [BPair.marginN_congr (BPair.norm_oneValue x)]) _
  refine ⟨hcl, poly.oneValue_trans (assembly.cartanFold_matVec t hsq c hcl) ?_⟩
  change poly.oneValue (elim.matVec G (natV c)) v
  rw [hnat]
  exact elim.adjD_nat_solution G hGr
    (fun k hk => hlead k (by rw [← hGl]; exact hk)) v (hv.trans hGl.symm) d hd
    (BPair.oneValue_trans (BPair.oneValue_symm (elim.detD_eq G hGr))
      (BPair.ofNat_marginN (ground.leB_of_lt hdet)))
    (fun i hi => (hbits i hi).1) (fun i hi => (hbits i hi).2)

/-- Every stated natural dominance join passes the computed
test at the upper key minus the lower key. -/
theorem foldTest_join (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam nu : List BPair) (hlam : lam.length = t.rank) (hnu : nu.length = t.rank)
    (c : List Nat) (hc : c.length = t.rank)
    (hjoin : poly.pnorm (elim.vecAdd nu (assembly.cartanFold t c)) = poly.pnorm lam) :
    foldTest t (elim.vecAdd lam (poly.neg nu)) = true := by
  exact foldTest_complete t hsq hlead hdet _
    (elim.length_vecAdd _ _ t.rank hlam ((poly.length_neg nu).trans hnu)) c hc
    (assembly.cartanFold_solve t hsq lam nu hlam hnu c hjoin)

/-- The actual witness decoder reads a stated dominance join
at its unique natural coefficient vector. -/
theorem foldWits_eq (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam nu : List BPair) (hlam : lam.length = t.rank) (hnu : nu.length = t.rank)
    (c : List Nat) (hc : c.length = t.rank)
    (hjoin : poly.pnorm (elim.vecAdd nu (assembly.cartanFold t c)) = poly.pnorm lam) :
    foldWits t lam nu = c :=
  foldSolve_decode t hsq hlead hdet _
    (elim.length_vecAdd _ _ t.rank hlam ((poly.length_neg nu).trans hnu)) c hc
    (assembly.cartanFold_solve t hsq lam nu hlam hnu c hjoin)

/-- The accepted fold witness joins its lower key back to the
stated upper key, at the actual adjugate-cofactor construction. -/
theorem foldWits_read (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam nu : List BPair) (hlam : lam.length = t.rank) (hnu : nu.length = t.rank)
    (hpass : foldTest t (elim.vecAdd lam (poly.neg nu)) = true) :
    (foldWits t lam nu).length = t.rank
      ∧ poly.pnorm (elim.vecAdd nu (assembly.cartanFold t (foldWits t lam nu))) = poly.pnorm lam := by
  have hgap : (elim.vecAdd lam (poly.neg nu)).length = t.rank :=
    elim.length_vecAdd _ _ t.rank hlam ((poly.length_neg nu).trans hnu)
  have hs := foldTest_sound t hsq hlead hdet _ hgap hpass
  refine ⟨hs.1, poly.pnorm_congr _ _ ?_ ?_⟩
  · rw [elim.length_vecAdd _ _ t.rank hnu (assembly.cartanFold_length t hsq _), hlam]
  · refine poly.oneValue_trans (elim.vecAdd_congr2 nu nu _ _ rfl
      ((assembly.cartanFold_length t hsq _).trans hgap.symm) (poly.oneValue_refl nu) hs.2) ?_
    rw [← elim.vecAdd_assoc, elim.vecAdd_comm nu lam, elim.vecAdd_assoc]
    exact elim.vecAdd_null_right lam (elim.vecAdd nu (poly.neg nu))
      (by rw [elim.length_vecAdd _ _ t.rank hnu ((poly.length_neg nu).trans hnu), hlam])
      (elim.vecAdd_swap_unitTail nu)

/-- A supported content passes the computed natural-fold test.
Witness lists may have any displayed length: only the rank's
coefficients enter the Cartan fold. -/
theorem supportRead_foldTest (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (L : List (List BPair)) (wits : List (List Nat)) (lam : List BPair)
    (hlam : lam.length = t.rank) (hnorm : poly.pnorm lam = lam)
    (hsupp : memberchar.supportRead t L wits lam)
    (nu : List BPair) (hnu : nu.length = t.rank) (hn : nu ∈ L) :
    foldTest t (elim.vecAdd lam (poly.neg nu)) = true := by
  obtain ⟨k, hk, he⟩ := ground.getAt_of_mem ([] : List BPair) hn
  have hjoin := hsupp.2 k hk
  rw [he] at hjoin
  let c := padN t.rank (ground.getAt [] wits k)
  have hcl : c.length = t.rank := ground.length_mapRange _ _
  have hcf := assembly.cartanFold_congr t hsq c (ground.getAt [] wits k) (fun i hi => by
    change ground.getAt 0 ((List.range t.rank).map
      (fun j => ground.getAt 0 (ground.getAt [] wits k) j)) i = _
    rw [ground.getAt_map_range 0 _ t.rank i, if_pos hi])
  apply foldTest_join t hsq hlead hdet lam nu hlam hnu c hcl
  rw [hnorm]
  refine Eq.trans (poly.pnorm_congr _ _ ?_ ?_) hjoin
  · rw [elim.length_vecAdd _ _ t.rank hnu (assembly.cartanFold_length t hsq c),
      elim.length_vecAdd _ _ t.rank hnu (assembly.cartanFold_length t hsq _)]
  · exact elim.vecAdd_congr2 _ _ _ _ rfl
      ((assembly.cartanFold_length t hsq c).trans (assembly.cartanFold_length t hsq _).symm)
      (poly.oneValue_refl nu) hcf

/-- The computed support witnesses recover the stated joins
for any equal-count listing of a supported family. Repeated keys
receive the same decoded natural coefficients at each occurrence. -/
theorem supportRead_counts (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (L R : List (List BPair)) (wits : List (List Nat)) (lam : List BPair)
    (hlam : lam.length = t.rank) (hnorm : poly.pnorm lam = lam)
    (hc : ∀ v, ground.countOf v L = ground.countOf v R)
    (hm : memberchar.mShapeRead t R) (hs : memberchar.supportRead t R wits lam) :
    memberchar.supportRead t L (L.map (foldWits t lam)) lam := by
  refine ⟨ground.length_map _ _, ?_⟩
  intro k hk
  have hn := ground.mem_getAt ([] : List BPair) L k hk
  have hr : ground.getAt [] L k ∈ R := ground.mem_of_countOf_pos _ R (by
    rw [← hc]
    exact ground.countOf_pos_of_mem hn)
  rw [ground.getAt_map [] [] (foldWits t lam) L k hk]
  have hp := supportRead_foldTest t hsq hlead hdet R wits lam hlam hnorm hs _ (hm _ hr).1 hr
  exact (foldWits_read t hsq hlead hdet lam _ hlam (hm _ hr).1 hp).2.trans hnorm

/-- The actual Cartan decoder supplies the support witnesses
of a graded family whose every key passes the natural-fold test. -/
theorem wDomAt_foldWits (t : gentable.Table) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (W : List (List BPair × Bool)) (hw : sertables.wShapeRead t W)
    (top : List BPair) (ht : top.length = t.rank)
    (hpass : ∀ p ∈ W, foldTest t (elim.vecAdd top (poly.neg p.1)) = true) :
    assembly.wDomAt t W (W.map (fun p => foldWits t top p.1)) (poly.pnorm top) := by
  refine ⟨ground.length_map _ _, ?_⟩
  intro k hk
  have hm := ground.mem_getAt ([], false) W k hk
  rw [ground.getAt_map ([], false) [] (fun p => foldWits t top p.1) W k hk]
  exact (foldWits_read t hsq hlead hdet top _ ht (hw _ hm).1 (hpass _ hm)).2

/-- The cleared `ρ`-dot of a coroot list at the Gram. -/
def rdKey (t : gentable.Table) (G : elim.Mat)
    (m : List Nat) : Nat :=
  BPair.marginN (formC G (natV m) (sertables.rhoV t))

/-- A dominant canonical key's natural margin list represents
that same content on the balance carrier. -/
theorem natV_natsOf (v : List BPair)
    (hp : ∀ i, i < v.length → BPair.unit ≤ ground.getAt BPair.unit v i) :
    poly.oneValue (natV (natsOf v)) v := by
  refine poly.oneValue_of_entries _ _ (by rw [natV, natsOf, ground.length_map, ground.length_map]) ?_
  intro i hi
  rw [natV, natsOf, ground.length_map, ground.length_map] at hi
  rw [natV, ground.getAt_map 0 BPair.unit BPair.ofNat _ i (by rw [natsOf, ground.length_map]; exact hi)]
  change (BPair.ofNat (ground.getAt 0 (v.map BPair.marginN) i)).oneValue _
  rw [ground.getAt_map BPair.unit 0 BPair.marginN v i hi]
  exact BPair.oneValue_symm (BPair.ofNat_marginN (hp i hi))

/-- A natural coroot list is fixed by coordinate normalization. -/
theorem natV_pnorm (m : List Nat) : poly.pnorm (natV m) = natV m := by
  change (m.map BPair.ofNat).map BPair.norm = m.map BPair.ofNat
  rw [ground.map_map]
  exact ground.map_congr_all _ _ BPair.norm_ofNat m

/-- The natural margin list reads back a natural coroot label. -/
theorem natsOf_natV (m : List Nat) : natsOf (natV m) = m := by
  change (m.map BPair.ofNat).map BPair.marginN = m
  rw [ground.map_map]
  exact (ground.map_congr_all _ _ BPair.marginN_ofNat m).trans (ground.map_id m)

/-- Shifting a natural label by rho is its coordinatewise
successor list on the balance carrier. -/
theorem shiftV_natV (t : gentable.Table) (m : List Nat) (hm : m.length = t.rank) :
    shiftV t m = natV (m.map (fun n => n + 1)) := by
  have hl : (shiftV t m).length = (natV (m.map (fun n => n + 1))).length := by
    rw [shiftV_length t m hm, natV, ground.length_map, ground.length_map, hm]
  have he := poly.pnorm_congr _ _ hl (poly.oneValue_of_entries _ _ hl (fun i hi => by
    rw [shiftV_length t m hm] at hi
    rw [natV, ground.getAt_map 0 BPair.unit BPair.ofNat _ i
      (by rw [ground.length_map, hm]; exact hi),
      ground.getAt_map 0 0 (fun n => n + 1) m i (by rw [hm]; exact hi)]
    exact shiftV_read t m hm i hi))
  rw [show poly.pnorm (shiftV t m) = shiftV t m from poly.pnorm_pnorm _, natV_pnorm] at he
  exact he

/-- The shifted sum of two labels is the first coroot key
joined to the second label's shifted key. -/
theorem shiftV_join (t : gentable.Table) (a b : List Nat)
    (ha : a.length = t.rank) (hb : b.length = t.rank) :
    shiftV t (List.zipWith Nat.add a b)
      = poly.pnorm (elim.vecAdd (natV a) (shiftV t b)) := by
  have hla : (natV a).length = t.rank := (ground.length_map _ a).trans ha
  have hlb : (natV b).length = t.rank := (ground.length_map _ b).trans hb
  have hlr : (sertables.rhoV t).length = t.rank := ground.length_replicate _ _
  have hab := ground.length_zipWith Nat.add a b t.rank ha hb
  have hsum : (natV (List.zipWith Nat.add a b)).length = t.rank := (ground.length_map _ _).trans hab
  change poly.pnorm (elim.vecAdd (natV (List.zipWith Nat.add a b)) (sertables.rhoV t))
    = poly.pnorm (elim.vecAdd (natV a) (poly.pnorm (elim.vecAdd (natV b) (sertables.rhoV t))))
  rw [elim.vecAdd_comm (natV a), elim.pnorm_vecAdd_left _ _
    ((elim.length_vecAdd _ _ t.rank hlb hlr).trans hla.symm),
    elim.vecAdd_comm (elim.vecAdd (natV b) (sertables.rhoV t)), ← elim.vecAdd_assoc]
  apply poly.pnorm_congr
  · rw [elim.length_vecAdd _ _ t.rank hsum hlr,
      elim.length_vecAdd _ _ t.rank (elim.length_vecAdd _ _ t.rank hla hlb) hlr]
  · exact elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_symm (elim.vecAdd_ofNat a b))
      (poly.oneValue_refl _) (hsum.trans (elim.length_vecAdd _ _ t.rank hla hlb).symm) rfl

/-- The natural coroot embedding preserves every occurrence
count, its inverse margin read separating the labels. -/
theorem countOf_natV_map (c : List Nat) (cs : List (List Nat)) :
    ground.countOf (natV c) (cs.map natV) = ground.countOf c cs := by
  apply ground.countOf_map_inj natV c cs
  intro d _ he
  have h := congrArg natsOf he
  rw [natsOf_natV, natsOf_natV] at h
  exact h

/-- A canonical upper-side key is exactly its natural margin
list's image on the balance carrier. -/
theorem natV_natsOf_eq (v : List BPair) (hn : poly.pnorm v = v)
    (hp : ∀ i, i < v.length → BPair.unit ≤ ground.getAt BPair.unit v i) :
    natV (natsOf v) = v := by
  have h := poly.pnorm_congr (natV (natsOf v)) v
    (by rw [natV, natsOf, ground.length_map, ground.length_map]) (natV_natsOf v hp)
  rw [natV_pnorm, hn] at h
  exact h

/-- The dominant keys at or below a top: the coroot box under the
top's `ρ`-dot cap, filtered at the fold membership
(`lem:memberdata`(i), the dominant keys' `ρ`-dots capped by the
top's own). -/
def domKeys (t : gentable.Table) (G : elim.Mat) (lam : List Nat) :
    List (List Nat) :=
  let cap := rdKey t G lam
  let bounds := (List.range t.rank).map (fun i =>
    cap / BPair.marginN (elim.dotP (getAt [] G i) (sertables.rhoV t)))
  (ground.boxAll bounds).filter (fun m =>
    decide (rdKey t G m ≤ cap)
      && foldTest t (elim.vecAdd (natV lam) (poly.neg (natV m))))

private def sortDesc (key : List Nat → Nat) :
    List (List Nat) → List (List Nat)
  | [] => []
  | h :: tl => ground.insertKeyDesc key h (sortDesc key tl)

/-- The standing dominant multiplicity at a label, zero when absent. -/
def lookupN (m : List Nat) (l : List (List Nat × Nat)) : Nat :=
  (fusion.lookupBy (fun a b => a == b) m l).getD 0

/-- Looking up a family with a stated value at each label reads
that value on its keys and zero off its keys. Repeated keys have
the stated value at every occurrence. -/
theorem lookupN_map (value : List Nat → Nat) (m : List Nat) : ∀ ks : List (List Nat),
    lookupN m (ks.map (fun k => (k, value k)))
      = if ground.countOf m ks = 0 then 0 else value m
  | [] => rfl
  | k :: ks => by
    change (if k == m then some (value k) else
      fusion.lookupBy (fun a b => a == b) m (ks.map (fun q => (q, value q)))).getD 0 = _
    rw [ground.listBeq_decide]
    by_cases h : k = m
    · rw [if_pos (decide_eq_true h), h, ground.countOf_head,
        if_neg (Nat.ne_of_gt (Nat.succ_pos _))]
      rfl
    · rw [if_neg (fun hd => h (of_decide_eq_true hd)),
        ground.countOf_head_ne (fun he => h he.symm)]
      exact lookupN_map value m ks

/-- A key list covering every positive value gives that value
at every lookup, including labels outside the list. -/
theorem lookupN_map_eq (value : List Nat → Nat) (ks : List (List Nat))
    (hcover : ∀ m, 0 < value m → m ∈ ks) (m : List Nat) :
    lookupN m (ks.map (fun k => (k, value k))) = value m := by
  rw [lookupN_map]
  by_cases h : ground.countOf m ks = 0
  · rw [if_pos h]
    cases Nat.eq_zero_or_pos (value m) with
    | inl he => exact he.symm
    | inr hp =>
      have hc := ground.countOf_pos_of_mem (hcover m hp)
      rw [h] at hc
      exact absurd hc (Nat.lt_irrefl 0)
  · rw [if_neg h]

/-- One key's moved-fold numerator: per positive member and step
within the `ρ`-dot cap, the moved content's doubled form read
against the member, weighted at the standing family's count at the
moved content's dominant image — the trace recursion's fold side
(`lem:memberdata`(i)); a starved walk refuses the whole read. -/
def numAt (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (acc : List (List Nat × Nat)) (rdTop : Nat) (m : List Nat) :
    Option BPair :=
  (List.range t.posFolds.length).foldl (fun s j =>
    match s with
    | none => none
    | some sv =>
      let av := poly.pnorm (sertables.posCorootV t j)
      let rda := BPair.marginN (formC G av (sertables.rhoV t))
      let lcap := (rdTop - rdKey t G m) / rda
      (List.range lcap).foldl (fun s2 l0 =>
        match s2 with
        | none => none
        | some sv2 =>
          let mv := poly.pnorm (elim.vecAdd (natV m)
            (elim.vecScale (BPair.ofNat (l0 + 1)) av))
          let w := domWalk t fuel mv
          if w == ([] : List BPair) then none
          else
            let mm := lookupN (natsOf w) acc
            if mm == 0 then some sv2
            else some (sv2 + formC G mv av * BPair.ofNat (2 * mm)))
        (some sv))
    (some BPair.unit)

/-- The returned trace numerator is the finite root-and-string
sum at the accumulator's dominant-key reads. Skipping a zero
multiplicity contributes exactly the sum's unit. -/
theorem numAt_read (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (acc : List (List Nat × Nat)) (rdTop : Nat) (m : List Nat) (hm : m.length = t.rank) :
    let line := fun j =>
      let av := poly.pnorm (sertables.posCorootV t j)
      let cap := (rdTop - rdKey t G m) / BPair.marginN (formC G av (sertables.rhoV t))
      ground.bsum (fun k =>
        let mv := poly.pnorm (elim.vecAdd (natV m) (elim.vecScale (BPair.ofNat (k + 1)) av))
        formC G mv av * BPair.ofNat (2 * lookupN (natsOf (domWalk t fuel mv)) acc)) (List.range cap)
    ∃ n, numAt t G fuel acc rdTop m = some n
      ∧ n.oneValue (ground.bsum line (List.range t.posFolds.length)) := by
  let line := fun j =>
    let av := poly.pnorm (sertables.posCorootV t j)
    let cap := (rdTop - rdKey t G m) / BPair.marginN (formC G av (sertables.rhoV t))
    ground.bsum (fun k =>
      let mv := poly.pnorm (elim.vecAdd (natV m) (elim.vecScale (BPair.ofNat (k + 1)) av))
      formC G mv av * BPair.ofNat (2 * lookupN (natsOf (domWalk t fuel mv)) acc)) (List.range cap)
  have h : ∃ n, numAt t G fuel acc rdTop m = some n
      ∧ n.oneValue (BPair.unit + ground.bsum line (List.range t.posFolds.length)) := by
    unfold numAt
    apply ground.foldl_some_sum
    intro j _ a
    let av := poly.pnorm (sertables.posCorootV t j)
    let cap := (rdTop - rdKey t G m) / BPair.marginN (formC G av (sertables.rhoV t))
    let term := fun k =>
      let mv := poly.pnorm (elim.vecAdd (natV m) (elim.vecScale (BPair.ofNat (k + 1)) av))
      formC G mv av * BPair.ofNat (2 * lookupN (natsOf (domWalk t fuel mv)) acc)
    change ∃ b, (List.range cap).foldl _ (some a) = some b ∧ b.oneValue (a + ground.bsum term (List.range cap))
    apply ground.foldl_some_sum
    intro k _ b
    let raw := elim.vecAdd (natV m) (elim.vecScale (BPair.ofNat (k + 1)) av)
    let mv := poly.pnorm raw
    have hr : raw.length = t.rank :=
      elim.length_vecAdd _ _ t.rank ((ground.length_map BPair.ofNat m).trans hm)
        (by rw [elim.length_vecScale, poly.pnorm_length, sertables.posCorootV_length])
    have hn := hwalk raw hr
    change ∃ c, (if domWalk t fuel mv == ([] : List BPair) then none else
      if lookupN (natsOf (domWalk t fuel mv)) acc == 0 then some b
      else some (b + term k)) = some c ∧ c.oneValue (b + term k)
    rw [if_neg (fun h => hn (ground.listBeqEq h))]
    by_cases hz : lookupN (natsOf (domWalk t fuel mv)) acc = 0
    · rw [ground.eqBeqOf hz]
      refine ⟨b, rfl, ?_⟩
      change b.oneValue (b + formC G mv av * BPair.ofNat (2 * lookupN (natsOf (domWalk t fuel mv)) acc))
      rw [hz, Nat.mul_zero]
      exact BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.mul_unit _)) (BPair.add_unit _))
    · rw [ground.neBeqOf hz]
      exact ⟨_, rfl, BPair.oneValue_refl _⟩
  obtain ⟨n, hn, hv⟩ := h
  exact ⟨n, hn, BPair.oneValue_trans hv (BPair.unit_add _)⟩

/-- When every moved dominance walk completes, the trace
numerator returns a balance value for every accumulator. -/
theorem numAt_complete (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (acc : List (List Nat × Nat)) (rdTop : Nat) (m : List Nat) (hm : m.length = t.rank) :
    ∃ n, numAt t G fuel acc rdTop m = some n := by
  obtain ⟨n, hn, _⟩ := numAt_read t G fuel hwalk acc rdTop m hm
  exact ⟨n, hn⟩

/-- The dominant solve: the keys in descending `ρ`-dot order, the
top's count one at the top line, each further key's count the
moved-fold numerator's exact cofactor at the two Casimir reads'
gap (`lem:memberdata`(i), the recursion's one solution); a vacant
gap, a starved walk or an inexact cofactor refuses the whole
family, the vacant list the pins' own refusal. -/
private def famGo (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (top : List Nat) (rdTop : Nat) :
    List (List Nat) → List (List Nat × Nat) → List (List Nat × Nat)
  | [], acc => acc
  | m :: tl, acc =>
    if m == top then famGo t G fuel top rdTop tl (acc ++ [(m, 1)])
    else
      let denom := BPair.marginN (BPair.norm
        (formC G (shiftV t top) (shiftV t top)
          + (formC G (shiftV t m) (shiftV t m)).swap))
      if denom == 0 then []
      else
        match numAt t G fuel acc rdTop m with
        | none => []
        | some numer =>
          let n := BPair.marginN (BPair.norm numer)
          if n % denom == 0 then
            famGo t G fuel top rdTop tl (acc ++ [(m, n / denom)])
          else []

/-- The dominant multiplicity family at a top: the solve over the
sorted dominant keys. -/
def domFam (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (lam : List Nat) : List (List Nat × Nat) :=
  famGo t G fuel lam (rdKey t G lam)
    (sortDesc (rdKey t G) (domKeys t G lam)) []

/-- The full multiplicity family: the dominant keys expanded over
their reflection orbits, each at its count — the block's family,
every occupied content at its summand's count, a starved orbit
closure refusing the whole family (`lem:memberdata`(i); the
family the reads of `thm:memberchar`'s kit decide). -/
def multFam (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (lam : List Nat) : List (List BPair) :=
  let parts := (domFam t G fuel lam).map
    (fun p => (orbitSet t fuel (natV p.1), p.2))
  if parts.any (fun q => q.1.isEmpty) then []
  else parts.flatMap (fun q => q.1.flatMap (List.replicate q.2))

/-- The family fold's graded pair at a target: per occupied
content one walk of the moved key, the even and the odd hits at
the shifted second factor collected in one pass; a starved walk
refuses the whole read (`lem:memberdata`(i)'s display fold, one
walk per occupied content). -/
private def famCount (t : gentable.Table) (fuel : Nat)
    (kb kc : List BPair) : List (List BPair) → Option (Nat × Nat)
  | [] => some (0, 0)
  | nu :: tl =>
    match famCount t fuel kb kc tl with
    | none => none
    | some p =>
      match walkP t fuel
          (poly.pnorm (elim.vecAdd kc (poly.neg nu))) false with
      | none => none
      | some w =>
        if w.1 == kb then
          if w.2 then some (p.1, p.2 + 1) else some (p.1 + 1, p.2)
        else some p

/-- The member fusion count: the member display's gap read at the
produced family, the display's fold at the family
(`lem:memberdata`(i); `cor:steinberg`'s member display) — each
occupied content's moved key, the target's shifted key joined to
the content's balance partner, walked to its dominant image at the
walk's letter parity, a walk ending at the shifted second factor
the tie's one element at the regular reads and every further end
off the ties (`con:sertables`); a starved walk reads the vacant
count, the pins' own refusal. -/
def countM (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (a b c : List Nat) : Nat :=
  match famCount t fuel (shiftV t b) (shiftV t c)
      (multFam t G fuel a) with
  | none => 0
  | some p => p.1 - p.2

/-- The fusion row at two labels: the dominant targets at occupied
counts over the fused window, the targets at or below the labels'
sum, the family fold read once per target at the one produced
family (`lem:memberdata`(i)). -/
def rowM (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (a b : List Nat) : List (List Nat) :=
  let kb := shiftV t b
  let La := multFam t G fuel a
  (domKeys t G (List.zipWith Nat.add a b)).filter
    (fun c =>
      match famCount t fuel kb (shiftV t c) La with
      | none => false
      | some p => decide (0 < p.1 - p.2))

/-- `θ`'s coroot list, the theta fold's coroot reads — one read at
every member (`con:sertables`' adjugate rows, the highest root the
fundamental at the fold row's key, with the low-rank sum-family
seeds its further instances). -/
def thetaKey (t : gentable.Table) : List Nat :=
  natsOf ((List.range t.rank).map (gentable.corootAt t t.thetaFold))

/-- The member dimension: the gap product at the shifted label
against the gap product at `ρ`, the exact cofactor
(`cor:weyldim`'s member display at `serstable.gapAt`). -/
def dimM (t : gentable.Table) (m : List Nat) : Nat :=
  ground.prodOver (serstable.gapAt t (m.map (· + 1)))
      (List.range t.posFolds.length)
    / ground.prodOver (serstable.gapAt t (List.replicate t.rank 1))
      (List.range t.posFolds.length)

/-- The member dimension is positive wherever its rho factors
are positive. Every shifted factor is at least its rho factor. -/
theorem dimM_pos (t : gentable.Table) (hlen : t.lenNums.length = t.rank)
    (hrho : ∀ j, j < t.posFolds.length → 0 < serstable.gapAt t (List.replicate t.rank 1) j)
    (m : List Nat) (hm : m.length = t.rank) : 0 < dimM t m := by
  have hd := ground.prodOver_pos (serstable.gapAt t (List.replicate t.rank 1))
    (List.range t.posFolds.length) (fun j hj => hrho j (ground.ltOfMem hj))
  apply ground.le_div_of_mul_le 1 _ _ hd
  rw [Nat.mul_one]
  exact ground.prodOver_le _ _ _ (fun j _ => serstable.gapAt_shift_le t hlen m hm j)

/-- The unit label's two gap products agree, so its exact
dimension is one at every table with positive rho factors. -/
theorem dimM_unit (t : gentable.Table)
    (hrho : ∀ j, j < t.posFolds.length → 0 < serstable.gapAt t (List.replicate t.rank 1) j) :
    dimM t (List.replicate t.rank 0) = 1 := by
  unfold dimM
  rw [ground.map_replicate]
  have hd := ground.prodOver_pos (serstable.gapAt t (List.replicate t.rank 1))
    (List.range t.posFolds.length) (fun j hj => hrho j (ground.ltOfMem hj))
  have he := ground.divMulSelf 1 _ hd
  rw [Nat.one_mul] at he
  exact he

/-- A nonunit label's Weyl product is at least two. An occupied
coroot coordinate doubles its simple-root factor, and every other
factor is at least the rho factor (`cor:weyldim`; `thm:drift`). -/
theorem dimM_ge_two (t : gentable.Table) (hlen : t.lenNums.length = t.rank)
    (hrho : ∀ j, j < t.posFolds.length → 0 < serstable.gapAt t (List.replicate t.rank 1) j)
    (hsimple : ∀ i, i < t.rank →
      ((List.range t.rank).map (fun k => if k == i then 1 else 0)) ∈ t.posFolds)
    (m : List Nat) (hm : m.length = t.rank) (hne : m ≠ List.replicate t.rank 0) :
    2 ≤ dimM t m := by
  have hp : 0 < ground.sumNat m := by
    cases Nat.eq_zero_or_pos (ground.sumNat m) with
    | inl hz =>
      have he := ground.replicate_of_sum_zero m hz
      rw [hm] at he
      exact False.elim (hne he)
    | inr h => exact h
  obtain ⟨x, hx, hxpos⟩ := ground.famFold_pos_mem (fun n => n) m hp
  obtain ⟨i, hi, hie⟩ := ground.getAt_of_mem 0 hx
  have hir : i < t.rank := by rw [← hm]; exact hi
  obtain ⟨j, hj, hjf⟩ := ground.getAt_of_mem ([] : List Nat) (hsimple i hir)
  let D := serstable.gapAt t (List.replicate t.rank 1)
  let N := serstable.gapAt t (m.map (fun n => n + 1))
  let K := List.range t.posFolds.length
  have hD : 0 < ground.prodOver D K :=
    ground.prodOver_pos D K (fun k hk => hrho k (ground.ltOfMem hk))
  have hone : ground.countOf j K = 1 := ground.countOf_range_one hj
  have hfactor : 2 * D j ≤ N j := by
    unfold D N
    rw [serstable.gapAt_simple t hlen i j hir hjf _ (ground.length_replicate _ _),
      serstable.gapAt_simple t hlen i j hir hjf _ ((ground.length_map _ m).trans hm),
      ground.getAt_replicate 0 1 t.rank i hir, Nat.mul_one,
      ground.getAt_map 0 0 (fun n => n + 1) m i hi, hie, Nat.mul_comm 2]
    exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hxpos)
  have hrest : ground.prodOver (fun k => if k = j then 1 else D k) K
      ≤ ground.prodOver (fun k => if k = j then 1 else N k) K := by
    apply ground.prodOver_le
    intro k _
    by_cases he : k = j
    · rw [if_pos he, if_pos he]; exact Nat.le_refl 1
    · rw [if_neg he, if_neg he]
      exact serstable.gapAt_shift_le t hlen m hm k
  apply ground.le_div_of_mul_le 2 _ _ hD
  change ground.prodOver D K * 2 ≤ ground.prodOver N K
  rw [← ground.prodOver_pick D j K hone, ← ground.prodOver_pick N j K hone,
    ground.mulAssoc, Nat.mul_comm (D j) 2]
  exact Nat.mul_le_mul hrest hfactor

/-- The Weyl-product dimension equals one exactly at the unit
label, when the positive list contains every simple root. -/
theorem dimM_eq_one (t : gentable.Table) (hlen : t.lenNums.length = t.rank)
    (hrho : ∀ j, j < t.posFolds.length → 0 < serstable.gapAt t (List.replicate t.rank 1) j)
    (hsimple : ∀ i, i < t.rank →
      ((List.range t.rank).map (fun k => if k == i then 1 else 0)) ∈ t.posFolds)
    (m : List Nat) (hm : m.length = t.rank) :
    dimM t m = 1 ↔ m = List.replicate t.rank 0 := by
  refine ⟨?_, ?_⟩
  · intro hd
    by_cases he : m = List.replicate t.rank 0
    · exact he
    · have h := dimM_ge_two t hlen hrho hsimple m hm he
      rw [hd] at h
      exact False.elim (Nat.not_succ_le_self 1 h)
  · intro he
    rw [he]
    exact dimM_unit t hrho

/-- The cleared Casimir at the produced Gram:
`⟨m, m + 2ρ⟩` at the one clearing scale. -/
def c2M (t : gentable.Table) (G : elim.Mat) (m : List Nat) : Nat :=
  BPair.marginN (formC G (natV m)
    (elim.vecAdd (natV m)
      (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t))))

/-- The coroot list joined to twice the unit list reads each
coordinate at its second successor. -/
private theorem natV_twoRho : ∀ m : List Nat,
    poly.oneValue
      (elim.vecAdd (natV m) (elim.vecAdd (List.replicate m.length (BPair.ofNat 1))
        (List.replicate m.length (BPair.ofNat 1))))
      (natV (m.map (fun n => n + 2)))
  | [] => trivial
  | a :: tl => by
    refine ⟨?_, natV_twoRho tl⟩
    exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.ofNat_add a 2)
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.ofNat_add 1 1)))

/-- D's cleared Casimir is unchanged by exchanging its final two
simple coroot coordinates. -/
theorem c2M_forkSwap_D (k : Nat) (a : List Nat) (ha : a.length = k + 2) :
    c2M (sertables.tableD (k + 2)) (gramOf (sertables.tableD (k + 2))) (ground.adjSwap k a)
      = c2M (sertables.tableD (k + 2)) (gramOf (sertables.tableD (k + 2))) a := by
  let t := sertables.tableD (k + 2)
  let G := gramOf t
  have hG := gramOf_shape t (ground.matOf_length _ _ _)
  have hform (m : List Nat) (hm : m.length = k + 2) :
      (formC G (natV m) (elim.vecAdd (natV m) (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t)))).oneValue
        (elim.dotAt G (natV m) (natV (m.map (fun n => n + 2)))) := by
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine elim.dotP_oneValue_right _ _ _ (elim.matVec_congr G _ _ ?_)
    change poly.oneValue (elim.vecAdd (natV m) (elim.vecAdd (List.replicate (k + 2) (BPair.ofNat 1))
      (List.replicate (k + 2) (BPair.ofNat 1)))) _
    rw [← hm]
    exact natV_twoRho m
  have he := elim.dotAt_adjSwap G (by rw [hG.1]; exact hG.2) k (by rw [hG.1]; exact Nat.lt_succ_self _)
    (fun i hi => gramOf_forkSwap_D k i (by rw [hG.1] at hi; exact hi))
    (natV a) (natV (a.map (fun n => n + 2)))
    (by rw [natV, ground.length_map, ha, hG.1]; rfl)
    (by rw [natV, ground.length_map, ground.length_map, ha, hG.1]; rfl)
  change BPair.marginN _ = BPair.marginN _
  refine BPair.marginN_congr (BPair.oneValue_trans (hform _ ((ground.length_adjSwap k a).trans ha)) ?_)
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (hform a ha))
  change (elim.dotAt G ((ground.adjSwap k a).map BPair.ofNat)
    (((ground.adjSwap k a).map (fun n => n + 2)).map BPair.ofNat)).oneValue _
  rw [← ground.adjSwap_map, ← ground.adjSwap_map, ← ground.adjSwap_map]
  exact he

/-- A matrix of coroot counts acts by the count-valued row dots. -/
private theorem natV_matVec (y : List Nat) : ∀ A : List (List Nat),
    poly.oneValue (elim.matVec (A.map natV) (natV y))
      (natV (A.map (fun r => ground.dotNat r y)))
  | [] => trivial
  | r :: A => ⟨BPair.oneValue_trans (elim.dotN_read _ _) (natV_dot r y), natV_matVec y A⟩

/-- Natural rows and natural vectors read their natural matrix
pairing on the balance carrier, without any width padding. -/
theorem dotG_natV (A : List (List Nat)) (x y : List Nat) :
    (sertables.dotG (A.map natV) (natV x) (natV y)).oneValue
      (BPair.ofNat (ground.dotNat x (A.map (fun r => ground.dotNat r y)))) :=
  BPair.oneValue_trans (elim.dotP_oneValue_right _ _ _ (natV_matVec y A)) (natV_dot x _)

/-- A natural Gram reads every natural coroot label's rho height
on or above the sum's unit. -/
theorem rhoDot_natV_upper (t : gentable.Table) (A : List (List Nat)) (m : List Nat) :
    BPair.unit ≤ sertables.dotG (A.map natV) (natV m) (sertables.rhoV t) := by
  have hr : natV (List.replicate t.rank 1) = sertables.rhoV t := ground.map_replicate BPair.ofNat 1 t.rank
  rw [← hr]
  exact ground.leB_congr_right (BPair.oneValue_symm (dotG_natV A m (List.replicate t.rank 1)))
    (ground.leB_ofNat (Nat.zero_le _))

/-- At a Gram with natural entries the cleared Casimir is the
natural quadratic fold at the second-successor coordinates
(`con:sertables`' form reads; `lem:casimir`). -/
theorem c2M_nat (t : gentable.Table) (A : List (List Nat)) (m : List Nat)
    (hm : m.length = t.rank) :
    c2M t (A.map natV) m
      = ground.dotNat m (A.map (fun r => ground.dotNat r (m.map (fun n => n + 2)))) := by
  have hy : poly.oneValue
      (elim.vecAdd (natV m) (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t)))
      (natV (m.map (fun n => n + 2))) := by
    show poly.oneValue
      (elim.vecAdd (natV m) (elim.vecAdd (List.replicate t.rank (BPair.ofNat 1))
        (List.replicate t.rank (BPair.ofNat 1)))) _
    rw [← hm]
    exact natV_twoRho m
  have hx := elim.dotP_oneValue_right (natV m) _ _ (elim.matVec_congr (A.map natV) _ _ hy)
  exact (BPair.marginN_congr (BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_trans hx (dotG_natV A m (m.map (fun n => n + 2)))))).trans (BPair.marginN_ofNat _)

/-- A natural Gram whose rows have occupied sums bounds the coroot
total by the cleared Casimir (`con:sertables`; `prop:windowfinite`). -/
theorem sumNat_le_c2M (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (m : List Nat) (hm : m.length = t.rank) : ground.sumNat m ≤ c2M t (A.map natV) m := by
  rw [c2M_nat t A m hm]
  refine ground.sumNat_le_dotNat m _ ?_ ?_
  · rw [ground.length_map, hA, hm]
    exact Nat.le_refl _
  · intro i hi
    have hiA : i < A.length := by rw [hA, ← hm]; exact hi
    rw [ground.getAt_map [] 0 _ A i hiA]
    have hr := hrows (ground.getAt [] A i) (ground.mem_getAt [] A i hiA)
    refine Nat.le_trans hr.2 (ground.sumNat_le_dotNat _ _ ?_ ?_)
    · rw [ground.length_map, hr.1, hm]
      exact Nat.le_refl _
    · intro j hj
      have hjm : j < m.length := by rw [hm, ← hr.1]; exact hj
      rw [ground.getAt_map 0 0 _ m j hjm]
      exact Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_add_left 2 _)

/-- The shifted coordinate dot splits into its quadratic part and
twice the row sum. -/
private theorem rowDot_two : ∀ r m : List Nat, r.length = m.length →
    ground.dotNat r (m.map (fun n => n + 2))
      = ground.dotNat r m + 2 * ground.sumNat r
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | a :: r, b :: m, h => by
    change a * (b + 2) + ground.dotNat r (m.map (fun n => n + 2))
      = (a * b + ground.dotNat r m) + 2 * (a + ground.sumNat r)
    rw [Nat.mul_add, rowDot_two r m (Nat.succ.inj h), Nat.mul_add,
      Nat.mul_comm a 2, Nat.add_add_add_comm]

/-- A natural Gram row's rho-dot is its coordinate sum, the
cutoff box's linear coefficient (`con:sertables`). -/
theorem natV_rhoDot (t : gentable.Table) (r : List Nat) (hr : r.length = t.rank) :
    BPair.marginN (elim.dotP (natV r) (sertables.rhoV t)) = ground.sumNat r := by
  have hrep : natV (List.replicate t.rank 1) = sertables.rhoV t :=
    ground.map_replicate BPair.ofNat 1 t.rank
  rw [← hrep]
  have h := BPair.oneValue_trans (BPair.oneValue_of_eq (elim.dotP_comm _ _))
    (natV_dot (List.replicate t.rank 1) r)
  rw [ground.dotOnesL t.rank r hr] at h
  exact (BPair.marginN_congr h).trans (BPair.marginN_ofNat _)

/-- The rho key at a natural Gram is the coroot list paired
against the Gram's row sums. -/
theorem rdKey_nat (t : gentable.Table) (A : List (List Nat))
    (hrows : ∀ r ∈ A, r.length = t.rank) (m : List Nat) :
    rdKey t (A.map natV) m = ground.dotNat m (A.map ground.sumNat) := by
  have hrep : natV (List.replicate t.rank 1) = sertables.rhoV t := ground.map_replicate BPair.ofNat 1 t.rank
  have he : A.map (fun r => ground.dotNat r (List.replicate t.rank 1)) = A.map ground.sumNat := by
    apply ground.map_congr_members
    intro r hr
    have hv := natV_dot r (List.replicate t.rank 1)
    rw [hrep] at hv
    exact (BPair.marginN_ofNat _).symm.trans
      ((BPair.marginN_congr (BPair.oneValue_symm hv)).trans
        (natV_rhoDot t r (hrows r (ground.mem_of_countOf_pos r A hr))))
  have hv := dotG_natV A m (List.replicate t.rank 1)
  rw [hrep, he] at hv
  exact (BPair.marginN_congr (BPair.oneValue_trans (BPair.norm_oneValue _) hv)).trans
    (BPair.marginN_ofNat _)

/-- Each coroot coordinate's rho contribution is bounded by the
whole rho key at a natural Gram. -/
theorem rdKey_coordinate (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank) (hrows : ∀ r ∈ A, r.length = t.rank)
    (m : List Nat) (hm : m.length = t.rank) (i : Nat) (hi : i < t.rank) :
    ground.sumNat (ground.getAt [] A i) * ground.getAt 0 m i ≤ rdKey t (A.map natV) m := by
  rw [rdKey_nat t A hrows m, ground.dotNat_index m _ (by rw [ground.length_map, hA, hm])]
  have h := ground.famFold_mem_le
    (fun j => ground.getAt 0 m j * ground.getAt 0 (A.map ground.sumNat) j)
    (List.range m.length) i (ground.memRange (by rw [hm]; exact hi))
  rw [ground.getAt_map [] 0 ground.sumNat A i (by rw [hA]; exact hi), Nat.mul_comm] at h
  exact h

/-- Each coordinate's linear contribution lies below the full
natural Casimir fold (`prop:windowfinite`'s finite coroot box). -/
theorem c2M_coordinate (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank) (hrows : ∀ r ∈ A, r.length = t.rank)
    (m : List Nat) (hm : m.length = t.rank) (i : Nat) (hi : i < t.rank) :
    (2 * ground.sumNat (ground.getAt [] A i)) * ground.getAt 0 m i
      ≤ c2M t (A.map natV) m := by
  have hiA : i < A.length := by rw [hA]; exact hi
  have him : i < m.length := by rw [hm]; exact hi
  have hr := hrows (ground.getAt [] A i) (ground.mem_getAt [] A i hiA)
  rw [c2M_nat t A m hm, ground.dotNat_index m _
    (by rw [ground.length_map, hA, hm])]
  have hterm := ground.famFold_mem_le
    (fun j => ground.getAt 0 m j * ground.getAt 0
      (A.map (fun r => ground.dotNat r (m.map (fun n => n + 2)))) j)
    (List.range m.length) i
    (ground.mem_of_countOf_pos i _ (by rw [ground.countOf_range, if_pos him]; exact Nat.succ_pos 0))
  rw [ground.getAt_map [] 0 _ A i hiA, rowDot_two _ m (hr.trans hm.symm)] at hterm
  refine Nat.le_trans ?_ hterm
  rw [Nat.mul_comm (2 * ground.sumNat (ground.getAt [] A i)) (ground.getAt 0 m i)]
  exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

/-- The below-cutoff enumeration: the nonunit coroot lists of the
box at the Casimir cap (`prop:windowfinite`'s route at the member,
every Gram pairing positive at the natural entries). -/
def belowM (t : gentable.Table) (G : elim.Mat) (k : Nat) :
    List (List Nat) :=
  let bounds := (List.range t.rank).map (fun i =>
    k / (2 * BPair.marginN (elim.dotP (getAt [] G i) (sertables.rhoV t))))
  (ground.boxAll bounds).filter (fun m =>
    (0 < ground.sumNat m) && (c2M t G m ≤ k))

/-- At a natural Gram the cutoff box reads its coordinate bounds
at twice the rows' sums. -/
private theorem belowM_nat (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank) (hrows : ∀ r ∈ A, r.length = t.rank) (k : Nat) :
    belowM t (A.map natV) k
      = (ground.boxAll ((List.range t.rank).map
          (fun i => k / (2 * ground.sumNat (ground.getAt [] A i))))).filter
        (fun m => (0 < ground.sumNat m) && (c2M t (A.map natV) m ≤ k)) := by
  apply congrArg (List.filter (fun m => (0 < ground.sumNat m) && (c2M t (A.map natV) m ≤ k)))
  apply congrArg ground.boxAll
  refine ground.map_congr_members _ _ (List.range t.rank) ?_
  intro i hi
  have hiA : i < A.length := by rw [hA]; exact ground.ltOfMem hi
  rw [ground.getAt_map [] [] natV A i hiA,
    natV_rhoDot t (ground.getAt [] A i) (hrows _ (ground.mem_getAt [] A i hiA))]

/-- The nonunit coroot enumeration at a smaller cutoff is the
larger enumeration filtered at that cutoff, in its original order
(`prop:windowfinite`). The natural Gram's linear coordinate floors
place every accepted label inside the smaller box. -/
theorem belowM_nest (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (k k' : Nat) (hk : k ≤ k') :
    belowM t (A.map natV) k
      = (belowM t (A.map natV) k').filter (fun m => decide (c2M t (A.map natV) m ≤ k)) := by
  let bounds := fun c => (List.range t.rank).map
    (fun i => c / (2 * ground.sumNat (ground.getAt [] A i)))
  have hw : ∀ c, (bounds c).length = t.rank := fun c => ground.length_mapRange _ _
  have hb : ∀ c i, i < t.rank →
      ground.getAt 0 (bounds c) i = c / (2 * ground.sumNat (ground.getAt [] A i)) := by
    intro c i hi
    rw [ground.getAt_map_range 0 _ t.rank i, if_pos hi]
  have hbox : ∀ m, m.length = (bounds k).length →
      ((0 < ground.sumNat m) && (c2M t (A.map natV) m ≤ k)) = true →
      ∀ i, i < (bounds k).length → ground.getAt 0 m i ≤ ground.getAt 0 (bounds k) i := by
    intro m hm hkeep i hi
    rw [hw] at hm hi
    rw [hb k i hi]
    have hiA : i < A.length := by rw [hA]; exact hi
    have hr := hrows _ (ground.mem_getAt [] A i hiA)
    refine ground.le_div_of_mul_le _ _ k (Nat.mul_pos (by decide : 0 < 2) hr.2) ?_
    exact Nat.le_trans (c2M_coordinate t A hA (fun r h => (hrows r h).1) m hm i hi)
      (of_decide_eq_true (ground.andSplitB hkeep).2)
  rw [belowM_nat t A hA (fun r h => (hrows r h).1) k,
    belowM_nat t A hA (fun r h => (hrows r h).1) k', ground.filter_filter]
  have hguard : ∀ m : List Nat,
      (((0 < ground.sumNat m) && (c2M t (A.map natV) m ≤ k'))
        && decide (c2M t (A.map natV) m ≤ k))
        = ((0 < ground.sumNat m) && (c2M t (A.map natV) m ≤ k)) := by
    intro m
    cases h : decide (c2M t (A.map natV) m ≤ k) with
    | false => rw [Bool.and_false, Bool.and_false]
    | true =>
      rw [Bool.and_true, Bool.and_true,
        decide_eq_true (Nat.le_trans (of_decide_eq_true h) hk), Bool.and_true]
  rw [ground.filter_congr _ _ hguard]
  exact (ground.boxAll_filter_eq (bounds k) (bounds k') ((hw k).trans (hw k').symm)
    (fun i hi => by
      rw [hw] at hi
      rw [hb k i hi, hb k' i hi]
      exact ground.divMono k k' _ hk) _ hbox).symm

/-- A dominant key has one coordinate per simple key, the box's
own width (`lem:memberdata`(i)). -/
private theorem domKeys_length (t : gentable.Table) (G : elim.Mat)
    (a c : List Nat) (hc : c ∈ domKeys t G a) : c.length = t.rank := by
  obtain ⟨hb, _⟩ := ground.mem_filter_of _ _ c hc
  have hw := (ground.mem_prodLists_of 0 _ c hb).1
  rw [ground.length_map, ground.length_mapRange] at hw
  exact hw


/-- A height-bounded natural coroot list passing the fold test
is a member of the producer's dominant enumeration. Positive row
sums put each coordinate inside its actual quotient bound. -/
theorem domKeys_mem (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (lam m : List Nat) (hm : m.length = t.rank)
    (hcap : rdKey t (A.map natV) m ≤ rdKey t (A.map natV) lam)
    (hpass : foldTest t (elim.vecAdd (natV lam) (poly.neg (natV m))) = true) :
    m ∈ domKeys t (A.map natV) lam := by
  let cap := rdKey t (A.map natV) lam
  let bounds := (List.range t.rank).map (fun i =>
    cap / BPair.marginN (elim.dotP (ground.getAt [] (A.map natV) i) (sertables.rhoV t)))
  have hb : bounds.length = t.rank := ground.length_mapRange _ _
  have hc : ∀ i, i < bounds.length → ground.getAt 0 m i ≤ ground.getAt 0 bounds i := by
    intro i hi
    rw [hb] at hi
    have hiA : i < A.length := by rw [hA]; exact hi
    have hr := hrows _ (ground.mem_getAt [] A i hiA)
    rw [ground.getAt_map_range 0 _ t.rank i, if_pos hi,
      ground.getAt_map [] [] natV A i hiA, natV_rhoDot t _ hr.1]
    exact ground.le_div_of_mul_le _ _ _ hr.2
      (Nat.le_trans (rdKey_coordinate t A hA (fun r hr => (hrows r hr).1) m hm i hi) hcap)
  have hbox : m ∈ ground.boxAll bounds := ground.mem_of_countOf_pos _ _ (by
    rw [ground.boxAll_countOf, if_pos (And.intro (hm.trans hb.symm) hc)]
    exact Nat.succ_pos 0)
  apply ground.mem_filter_to _ hbox
  rw [decide_eq_true hcap, hpass]
  rfl

/-- Every width-matched natural label is in its own dominant
window. Its support witness is the vacant simple fold. -/
theorem domKeys_top (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank) (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam : List Nat) (hlam : lam.length = t.rank) : lam ∈ domKeys t (A.map natV) lam := by
  apply domKeys_mem t A hA hrows lam lam hlam (Nat.le_refl _)
  have hn : (natV lam).length = t.rank := (ground.length_map BPair.ofNat lam).trans hlam
  apply foldTest_join t hsq hlead hdet (natV lam) (natV lam) hn hn
    (List.replicate t.rank 0) (ground.length_replicate _ _)
  rw [natV_pnorm]
  exact assembly.foldNull_key t _ (assembly.cartanFold_length t hsq _)
    (fun i hi => ground.getAt_replicate 0 0 t.rank i hi) (natV lam) hn (natV_pnorm lam)

/-- The zero coroot label has zero rho key at every Gram,
the first pairing argument a unit tail. -/
theorem rdKey_unit (t : gentable.Table) (G : elim.Mat) :
    rdKey t G (List.replicate t.rank 0) = 0 := by
  have hz : natV (List.replicate t.rank 0) = List.replicate t.rank BPair.unit :=
    ground.map_replicate BPair.ofNat 0 t.rank
  unfold rdKey formC
  rw [hz]
  have h : (sertables.dotG G (List.replicate t.rank BPair.unit) (sertables.rhoV t)).oneValue BPair.unit :=
    elim.dotP_null_tail_left _ _ (poly.unitTail_replicate t.rank)
  rw [BPair.norm_congr h]
  rfl

/-- The zero label's dominant window is its singleton, at a
valid Cartan solve, independently of the Gram's entries. -/
theorem domKeys_unit (t : gentable.Table) (G : elim.Mat)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan)) :
    domKeys t G (List.replicate t.rank 0) = [List.replicate t.rank 0] := by
  let z := List.replicate t.rank 0
  have hl : (natV z).length = t.rank := (ground.length_map BPair.ofNat z).trans (ground.length_replicate _ _)
  have hpass : foldTest t (elim.vecAdd (natV z) (poly.neg (natV z))) = true := by
    apply foldTest_join t hsq hlead hdet _ _ hl hl z (ground.length_replicate _ _)
    rw [natV_pnorm]
    exact assembly.foldNull_key t z (assembly.cartanFold_length t hsq z)
      (fun i hi => ground.getAt_replicate 0 0 t.rank i hi) (natV z) hl (natV_pnorm z)
  unfold domKeys
  rw [rdKey_unit]
  have hb : (List.range t.rank).map (fun i => 0 / BPair.marginN (elim.dotP (getAt [] G i) (sertables.rhoV t)))
      = List.replicate t.rank 0 := by
    refine Eq.trans (ground.map_congr_all _ (fun _ => 0) (fun i => ground.divZeroLeft _) _) ?_
    rw [ground.map_const, ground.length_range]
  change (ground.boxAll ((List.range t.rank).map
    (fun i => 0 / BPair.marginN (elim.dotP (getAt [] G i) (sertables.rhoV t))))).filter
    (fun m => decide (rdKey t G m ≤ 0) && foldTest t (elim.vecAdd (natV z) (poly.neg (natV m)))) = [z]
  rw [hb, ground.boxAll_zero]
  have hr : rdKey t G z = 0 := rdKey_unit t G
  have hkeep : (decide (rdKey t G z ≤ 0) && foldTest t (elim.vecAdd (natV z) (poly.neg (natV z)))) = true := by
    rw [hr, hpass]
    rfl
  change [z].filter (fun m => decide (rdKey t G m ≤ 0) && foldTest t (elim.vecAdd (natV z) (poly.neg (natV m)))) = [z]
  rw [ground.filter_cons, hkeep]
  rfl

/-- Every natural dominance join lies in the actual dominant
enumeration at a natural Gram with positive row sums. -/
theorem domKeys_complete (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hsp : sertables.simplePosRead t F)
    (hrd : sertables.rhoDotRead t F) (A : List (List Nat)) (hG : F.gram = A.map natV)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam m : List Nat) (hlam : lam.length = t.rank) (hm : m.length = t.rank)
    (c : List Nat) (hc : c.length = t.rank)
    (hjoin : poly.pnorm (elim.vecAdd (natV m) (assembly.cartanFold t c)) = natV lam) :
    m ∈ domKeys t F.gram lam := by
  have hnl : (natV lam).length = t.rank := (ground.length_map BPair.ofNat lam).trans hlam
  have hnm : (natV m).length = t.rank := (ground.length_map BPair.ofNat m).trans hm
  have hA : A.length = t.rank := by
    have h := hshape.1
    rw [hG, ground.length_map] at h
    exact h
  have hp (x : List Nat) : BPair.unit ≤ sertables.dotB F (natV x) (sertables.rhoV t) := by
    change BPair.unit ≤ sertables.dotG F.gram (natV x) (sertables.rhoV t)
    rw [hG]
    exact rhoDot_natV_upper t A x
  have he (x : List Nat) : (sertables.dotB F (natV x) (sertables.rhoV t)).oneValue
      (BPair.ofNat (rdKey t F.gram x)) := by
    have hn : rdKey t F.gram x = (sertables.dotB F (natV x) (sertables.rhoV t)).marginN :=
      BPair.marginN_congr (BPair.norm_oneValue _)
    rw [hn]
    exact BPair.ofNat_marginN (hp x)
  have hcap := ground.leB_ofNat_cancel (ground.leB_congr (he m) (he lam)
    (assembly.dotB_foldKey_le t F hshape hsp hrd (natV m) c (natV lam) hnl hjoin))
  have hpass := foldTest_join t hsq hlead hdet (natV lam) (natV m) hnl hnm c hc
    (hjoin.trans (natV_pnorm lam).symm)
  rw [hG] at hcap ⊢
  exact domKeys_mem t A hA hrows lam m hm hcap hpass

/-- Every occupied dominant content of a supported family is
listed by the producer, with its natural coroot label. -/
theorem domKeys_support (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hsp : sertables.simplePosRead t F)
    (hrd : sertables.rhoDotRead t F) (A : List (List Nat)) (hG : F.gram = A.map natV)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam : List Nat) (hlam : lam.length = t.rank) (L : List (List BPair))
    (wits : List (List Nat)) (hsupp : memberchar.supportRead t L wits (natV lam))
    (w : List BPair) (hw : memberchar.lamRead t w) (hc : 0 < ground.countOf w L) :
    natsOf w ∈ domKeys t F.gram lam := by
  have hn := ground.mem_of_countOf_pos w L hc
  have hp := supportRead_foldTest t hsq hlead hdet L wits (natV lam)
    ((ground.length_map BPair.ofNat lam).trans hlam) (natV_pnorm lam) hsupp w hw.1 hn
  have hfold := foldWits_read t hsq hlead hdet (natV lam) w
    ((ground.length_map BPair.ofNat lam).trans hlam) hw.1 hp
  have hnv : natV (natsOf w) = w := natV_natsOf_eq w hw.2.1
    (fun i hi => hw.2.2 i (by rw [← hw.1]; exact hi))
  apply domKeys_complete t F hshape hsp hrd A hG hrows hsq hlead hdet lam (natsOf w) hlam
    ((ground.length_map BPair.marginN w).trans hw.1) (foldWits t (natV lam) w) hfold.1
  rw [hnv]
  exact hfold.2.trans (natV_pnorm lam)

/-- An enumerated dominant key carries the actual natural
simple-root witness back to its top label. -/
theorem domKeys_foldWits (t : gentable.Table) (G : elim.Mat)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam : List Nat) (hlam : lam.length = t.rank) (m : List Nat) (hm : m ∈ domKeys t G lam) :
    (foldWits t (natV lam) (natV m)).length = t.rank
      ∧ poly.pnorm (elim.vecAdd (natV m) (assembly.cartanFold t (foldWits t (natV lam) (natV m))))
        = poly.pnorm (natV lam) := by
  have hpass := (ground.andSplitB (ground.mem_filter_of _ _ m hm).2).2
  exact foldWits_read t hsq hlead hdet (natV lam) (natV m)
    ((ground.length_map BPair.ofNat lam).trans hlam)
    ((ground.length_map BPair.ofNat m).trans (domKeys_length t G lam m hm)) hpass

/-- Natural labels give dominant canonical coroot keys. -/
theorem lamRead_natV (t : gentable.Table) (m : List Nat) (hm : m.length = t.rank) :
    memberchar.lamRead t (poly.pnorm (natV m)) := by
  refine ⟨(poly.pnorm_length _).trans ((ground.length_map BPair.ofNat m).trans hm), poly.pnorm_pnorm _, ?_⟩
  intro i hi
  have he := poly.oneValue_getAt i (poly.pnorm_oneValue (natV m))
  change (ground.getAt BPair.unit (poly.pnorm (natV m)) i).oneValue
    (ground.getAt BPair.unit (m.map BPair.ofNat) i) at he
  rw [ground.getAt_map 0 BPair.unit BPair.ofNat m i (by rw [hm]; exact hi)] at he
  exact ground.leB_congr_right (BPair.oneValue_symm he) (ground.unitLeOfNat _)

/-- The producer's dominant keys, shifted by rho, lie in the
character theorem's dominant window at their decoded simple folds. -/
theorem domKeys_window (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F) (hsp : sertables.simplePosRead t F)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam : List Nat) (hlam : lam.length = t.rank) (m : List Nat) (hm : m ∈ domKeys t F.gram lam) :
    shiftV t m ∈ memberchar.domWindow t F (poly.pnorm (natV lam)) := by
  have hml := domKeys_length t F.gram lam m hm
  let c := foldWits t (natV lam) (natV m)
  have hc := domKeys_foldWits t F.gram hsq hlead hdet lam hlam m hm
  have hcf := assembly.cartanFold_length t hsq c
  have hnl : (natV lam).length = t.rank := (ground.length_map BPair.ofNat lam).trans hlam
  have hnm : (natV m).length = t.rank := (ground.length_map BPair.ofNat m).trans hml
  have hr : (sertables.rhoV t).length = t.rank := ground.length_replicate _ _
  have htop : poly.pnorm (elim.vecAdd (poly.pnorm (natV lam)) (sertables.rhoV t)) = shiftV t lam :=
    elim.pnorm_vecAdd_left _ _ (hnl.trans hr.symm)
  have hkey : poly.pnorm (elim.vecAdd (shiftV t m) (assembly.cartanFold t c)) = shiftV t lam := by
    change poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd (natV m) (sertables.rhoV t))) _) = _
    rw [elim.pnorm_vecAdd_left _ _ ((elim.length_vecAdd _ _ t.rank hnm hr).trans hcf.symm),
      elim.vecAdd_assoc (natV m) (sertables.rhoV t), elim.vecAdd_comm (sertables.rhoV t),
      ← elim.vecAdd_assoc (natV m) (assembly.cartanFold t c),
      ← elim.pnorm_vecAdd_left _ _ ((elim.length_vecAdd _ _ t.rank hnm hcf).trans hr.symm), hc.2,
      elim.pnorm_vecAdd_left _ _ (hnl.trans hr.symm)]
    rfl
  apply memberchar.domWindow_mem t F (poly.pnorm (natV lam)) hshape hgram hgsym hsp hpsq hpi hrd
    (lamRead_natV t lam hlam) (shiftV t m) (shiftV_length t m hml) (poly.pnorm_pnorm _)
    (shiftV_pos t m hml) c hc.1
  rw [htop]
  exact hkey

/-- A non-top enumerated dominant key has strictly smaller shifted
Casimir square, by the character window's separation theorem. -/
theorem domKeys_sq_lt (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F) (hsp : sertables.simplePosRead t F)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam : List Nat) (hlam : lam.length = t.rank) (m : List Nat)
    (hm : m ∈ domKeys t F.gram lam) (hne : m ≠ lam) :
    sertables.dotB F (shiftV t m) (shiftV t m)
      < sertables.dotB F (shiftV t lam) (shiftV t lam) := by
  have hml := domKeys_length t F.gram lam m hm
  have hr : (sertables.rhoV t).length = t.rank := ground.length_replicate _ _
  have htop : poly.pnorm (elim.vecAdd (poly.pnorm (natV lam)) (sertables.rhoV t)) = shiftV t lam :=
    elim.pnorm_vecAdd_left _ _ (((ground.length_map BPair.ofNat lam).trans hlam).trans hr.symm)
  have hneq : shiftV t m ≠ poly.pnorm (elim.vecAdd (poly.pnorm (natV lam)) (sertables.rhoV t)) := by
    rw [htop]
    intro he
    have h := congrArg (fun v => (natsOf v).map (fun n => n - 1)) he
    rw [shiftV_unshift t m hml, shiftV_unshift t lam hlam] at h
    exact hne h
  have hsep := memberchar.sep_lt t F (poly.pnorm (natV lam)) hshape hgram hgsym hsp hrd
    (lamRead_natV t lam hlam) (shiftV t m)
    (domKeys_window t F hshape hgram hgsym hsp hpsq hpi hrd hsq hlead hdet lam hlam m hm) hneq
  rw [htop] at hsep
  exact hsep

/-- Every non-top dominant key has a positive recursion
denominator, by the character window's strict Casimir separation. -/
theorem domKeys_gap_pos (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F) (hsp : sertables.simplePosRead t F)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam : List Nat) (hlam : lam.length = t.rank) (m : List Nat)
    (hm : m ∈ domKeys t F.gram lam) (hne : m ≠ lam) :
    0 < BPair.marginN (BPair.norm (formC F.gram (shiftV t lam) (shiftV t lam)
      + (formC F.gram (shiftV t m) (shiftV t m)).swap)) := by
  have hsep := domKeys_sq_lt t F hshape hgram hgsym hsp hpsq hpi hrd hsq hlead hdet lam hlam m hm hne
  have hform : formC F.gram (shiftV t m) (shiftV t m) < formC F.gram (shiftV t lam) (shiftV t lam) :=
    BPair.lt_congr (BPair.oneValue_symm (BPair.norm_oneValue _))
      (BPair.oneValue_symm (BPair.norm_oneValue _)) hsep
  have hgap : BPair.unit < formC F.gram (shiftV t lam) (shiftV t lam)
      + (formC F.gram (shiftV t m) (shiftV t m)).swap := by
    apply ground.unitLt_of_swap_lt
    rw [BPair.swap_swap]
    exact hform
  exact BPair.marginN_pos (BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (BPair.norm_oneValue _)) hgap)


/-- At a dominant non-top window key, the trace recursion forces
the exact natural quotient used by the producer. Any numerator of
the correction's one value has zero remainder and reads the
family's multiplicity at that key. -/
theorem recRead_cofactor (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F) (hsp : sertables.simplePosRead t F)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (lam : List Nat) (hlam : lam.length = t.rank) (m : List Nat)
    (hm : m ∈ domKeys t F.gram lam) (hne : m ≠ lam)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hseed : (sertables.rhoV t, false) ∈ W)
    (hrec : memberchar.recRead t F W L (poly.pnorm (natV lam)))
    (numer : BPair) (hnum : numer.oneValue (memberchar.gSum t F L (poly.pnorm (natV m)))) :
    let den := BPair.marginN (BPair.norm (formC F.gram (shiftV t lam) (shiftV t lam)
      + (formC F.gram (shiftV t m) (shiftV t m)).swap))
    0 < den ∧ numer.norm.marginN % den = 0
      ∧ numer.norm.marginN / den = ground.countOf (poly.pnorm (natV m)) L := by
  have hml := domKeys_length t F.gram lam m hm
  have hnl : (natV lam).length = t.rank := (ground.length_map BPair.ofNat lam).trans hlam
  have hnm : (natV m).length = t.rank := (ground.length_map BPair.ofNat m).trans hml
  have hr : (sertables.rhoV t).length = t.rank := ground.length_replicate _ _
  have htop : poly.pnorm (elim.vecAdd (poly.pnorm (natV lam)) (sertables.rhoV t)) = shiftV t lam :=
    elim.pnorm_vecAdd_left _ _ (hnl.trans hr.symm)
  have hmshift : poly.pnorm (elim.vecAdd (poly.pnorm (natV m)) (sertables.rhoV t)) = shiftV t m :=
    elim.pnorm_vecAdd_left _ _ (hnm.trans hr.symm)
  let u := poly.pnorm (elim.vecAdd (shiftV t m) (poly.neg (sertables.rhoV t)))
  have hu : u = poly.pnorm (natV m) := assembly.addKey_solve t.rank (shiftV t m)
    (sertables.rhoV t) (poly.pnorm (natV m)) (shiftV_length t m hml) (poly.pnorm_pnorm _) hr
    ((poly.pnorm_length _).trans hnm) (poly.pnorm_pnorm _) hmshift
  have hc : (sertables.dotB F
      (poly.pnorm (elim.vecAdd (poly.pnorm (natV lam)) (sertables.rhoV t)))
      (poly.pnorm (elim.vecAdd (poly.pnorm (natV lam)) (sertables.rhoV t)))
      * BPair.ofNat (ground.countOf u L)).oneValue
      (sertables.dotB F (poly.pnorm (elim.vecAdd u (sertables.rhoV t)))
          (poly.pnorm (elim.vecAdd u (sertables.rhoV t))) * BPair.ofNat (ground.countOf u L)
        + memberchar.gSum t F L u) :=
    hrec (shiftV t m) (domKeys_window t F hshape hgram hgsym hsp hpsq hpi hrd hsq hlead hdet lam hlam m hm)
      (sertables.rhoV t, false) hseed
  rw [htop, hu, hmshift] at hc
  have hmul : (formC F.gram (shiftV t lam) (shiftV t lam)
      * BPair.ofNat (ground.countOf (poly.pnorm (natV m)) L)).oneValue
      (formC F.gram (shiftV t m) (shiftV t m)
        * BPair.ofNat (ground.countOf (poly.pnorm (natV m)) L) + numer) :=
    BPair.oneValue_trans (BPair.mul_congr (BPair.norm_oneValue _) (BPair.oneValue_refl _))
      (BPair.oneValue_trans hc (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_symm (BPair.norm_oneValue _)) (BPair.oneValue_refl _))
        (BPair.oneValue_symm hnum)))
  have hlt : formC F.gram (shiftV t m) (shiftV t m) < formC F.gram (shiftV t lam) (shiftV t lam) :=
    BPair.lt_congr (BPair.oneValue_symm (BPair.norm_oneValue _)) (BPair.oneValue_symm (BPair.norm_oneValue _))
      (domKeys_sq_lt t F hshape hgram hgsym hsp hpsq hpi hrd hsq hlead hdet lam hlam m hm hne)
  exact BPair.rec_count _ hlt hmul

/-- Every non-top G2 dominant key has a positive denominator
in the actual multiplicity recursion. -/
theorem domKeys_gap_pos_G2 (lam : List Nat) (hlam : lam.length = 2)
    (m : List Nat) (hm : m ∈ domKeys sertables.tableG2 (sertables.gramRows sertables.tableG2 sertables.adjG2) lam) (hne : m ≠ lam) :
    0 < BPair.marginN (BPair.norm
      (formC (sertables.gramRows sertables.tableG2 sertables.adjG2) (shiftV sertables.tableG2 lam) (shiftV sertables.tableG2 lam)
        + (formC (sertables.gramRows sertables.tableG2 sertables.adjG2) (shiftV sertables.tableG2 m) (shiftV sertables.tableG2 m)).swap)) := by
  apply domKeys_gap_pos sertables.tableG2 sertables.fundG2
    sertables.fundShape_G2 sertables.gramRead_G2 sertables.gramSymRead_G2
    sertables.simplePosRead_G2 sertables.permSquareRead_G2 sertables.permImageRead_G2
    sertables.rhoDotRead_G2 sertables.cartanSolve_G2.1
    sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2 lam hlam m hm hne

/-- Every non-top F4 dominant key has a positive denominator
in the actual multiplicity recursion. -/
theorem domKeys_gap_pos_F4 (lam : List Nat) (hlam : lam.length = 4)
    (m : List Nat) (hm : m ∈ domKeys sertables.tableF4 (sertables.gramRows sertables.tableF4 sertables.adjF4) lam) (hne : m ≠ lam) :
    0 < BPair.marginN (BPair.norm
      (formC (sertables.gramRows sertables.tableF4 sertables.adjF4) (shiftV sertables.tableF4 lam) (shiftV sertables.tableF4 lam)
        + (formC (sertables.gramRows sertables.tableF4 sertables.adjF4) (shiftV sertables.tableF4 m) (shiftV sertables.tableF4 m)).swap)) := by
  apply domKeys_gap_pos sertables.tableF4 sertables.fundF4
    sertables.fundShape_F4 sertables.gramRead_F4 sertables.gramSymRead_F4
    sertables.simplePosRead_F4 sertables.permSquareRead_F4 sertables.permImageRead_F4
    sertables.rhoDotRead_F4 sertables.cartanSolve_F4.1
    sertables.cartanSolve_F4.2.1 sertables.cartanSolve_F4.2.2 lam hlam m hm hne

/-- Every non-top E6 dominant key has a positive denominator
in the actual multiplicity recursion. -/
theorem domKeys_gap_pos_E6 (lam : List Nat) (hlam : lam.length = 6)
    (m : List Nat) (hm : m ∈ domKeys sertables.tableE6 (sertables.gramRows sertables.tableE6 sertables.adjE6) lam) (hne : m ≠ lam) :
    0 < BPair.marginN (BPair.norm
      (formC (sertables.gramRows sertables.tableE6 sertables.adjE6) (shiftV sertables.tableE6 lam) (shiftV sertables.tableE6 lam)
        + (formC (sertables.gramRows sertables.tableE6 sertables.adjE6) (shiftV sertables.tableE6 m) (shiftV sertables.tableE6 m)).swap)) := by
  apply domKeys_gap_pos sertables.tableE6 sertables.fundE6
    sertables.fundShape_E6 sertables.gramRead_E6 sertables.gramSymRead_E6
    sertables.simplePosRead_E6 sertables.permSquareRead_E6 sertables.permImageRead_E6
    sertables.rhoDotRead_E6 sertables.cartanSolve_E6.1
    sertables.cartanSolve_E6.2.1 sertables.cartanSolve_E6.2.2 lam hlam m hm hne

/-- Every non-top E7 dominant key has a positive denominator
in the actual multiplicity recursion. -/
theorem domKeys_gap_pos_E7 (lam : List Nat) (hlam : lam.length = 7)
    (m : List Nat) (hm : m ∈ domKeys sertables.tableE7 (sertables.gramRows sertables.tableE7 sertables.adjE7) lam) (hne : m ≠ lam) :
    0 < BPair.marginN (BPair.norm
      (formC (sertables.gramRows sertables.tableE7 sertables.adjE7) (shiftV sertables.tableE7 lam) (shiftV sertables.tableE7 lam)
        + (formC (sertables.gramRows sertables.tableE7 sertables.adjE7) (shiftV sertables.tableE7 m) (shiftV sertables.tableE7 m)).swap)) := by
  apply domKeys_gap_pos sertables.tableE7 sertables.fundE7
    sertables.fundShape_E7 sertables.gramRead_E7 sertables.gramSymRead_E7
    sertables.simplePosRead_E7 sertables.permSquareRead_E7 sertables.permImageRead_E7
    sertables.rhoDotRead_E7 sertables.cartanSolve_E7.1
    sertables.cartanSolve_E7.2.1 sertables.cartanSolve_E7.2.2 lam hlam m hm hne

/-- Every non-top E8 dominant key has a positive denominator
in the actual multiplicity recursion. -/
theorem domKeys_gap_pos_E8 (lam : List Nat) (hlam : lam.length = 8)
    (m : List Nat) (hm : m ∈ domKeys sertables.tableE8 (sertables.gramRows sertables.tableE8 sertables.adjE8) lam) (hne : m ≠ lam) :
    0 < BPair.marginN (BPair.norm
      (formC (sertables.gramRows sertables.tableE8 sertables.adjE8) (shiftV sertables.tableE8 lam) (shiftV sertables.tableE8 lam)
        + (formC (sertables.gramRows sertables.tableE8 sertables.adjE8) (shiftV sertables.tableE8 m) (shiftV sertables.tableE8 m)).swap)) := by
  apply domKeys_gap_pos sertables.tableE8 sertables.fundE8
    sertables.fundShape_E8 sertables.gramRead_E8 sertables.gramSymRead_E8
    sertables.simplePosRead_E8 sertables.permSquareRead_E8 sertables.permImageRead_E8
    sertables.rhoDotRead_E8 sertables.cartanSolve_E8.1
    sertables.cartanSolve_E8.2.1 sertables.cartanSolve_E8.2.2 lam hlam m hm hne

/-- The row selects exactly the positive computed counts in
the enumerated dominant target window. -/
theorem rowM_filter (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (a b : List Nat) :
    rowM t G fuel a b = (domKeys t G (List.zipWith Nat.add a b)).filter
      (fun c => decide (0 < countM t G fuel a b c)) := by
  apply ground.filter_congr
  intro c
  unfold countM
  cases h : famCount t fuel (shiftV t b) (shiftV t c) (multFam t G fuel a) <;> rfl

/-- The row's filter reads the count at the same produced family,
with every target in the coroot box. -/
private theorem rowM_mem (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (a b c : List Nat) (hc : c ∈ rowM t G fuel a b) :
    c.length = t.rank ∧ 0 < countM t G fuel a b c := by
  rw [rowM_filter] at hc
  obtain ⟨hd, hp⟩ := ground.mem_filter_of _ _ c hc
  exact ⟨domKeys_length t G _ c hd, of_decide_eq_true hp⟩

/-- A positive computed count is in the row whenever its target
has the stated natural dominance join to the labels' sum. -/
theorem rowM_of_count (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (a b c : List Nat) (hc : c ∈ domKeys t G (List.zipWith Nat.add a b))
    (hp : 0 < countM t G fuel a b c) : c ∈ rowM t G fuel a b := by
  rw [rowM_filter]
  exact ground.mem_filter_to _ hc (decide_eq_true hp)

/-- The cutoff filter's member has the coroot width, an occupied
coordinate sum, and the stated Casimir bound. -/
private theorem belowM_mem (t : gentable.Table) (G : elim.Mat)
    (k : Nat) (m : List Nat) (hm : m ∈ belowM t G k) :
    m.length = t.rank ∧ 0 < ground.sumNat m ∧ c2M t G m ≤ k := by
  obtain ⟨hb, hp⟩ := ground.mem_filter_of _ _ m hm
  have hw := (ground.mem_prodLists_of 0 _ m hb).1
  rw [ground.length_map, ground.length_mapRange] at hw
  exact ⟨hw, of_decide_eq_true (ground.andSplitB hp).1,
    of_decide_eq_true (ground.andSplitB hp).2⟩

/-- The dominant-key list is a selection from one range box,
so every key occurs at most once. -/
private theorem domKeys_distinct (t : gentable.Table) (G : elim.Mat)
    (a : List Nat) : ground.distinctList (domKeys t G a) :=
  ground.distinctList_filter _ _ (ground.boxAll_distinct _)

/-- The cutoff list is a selection from one range box,
so every label occurs at most once. -/
private theorem belowM_distinct (t : gentable.Table) (G : elim.Mat)
    (k : Nat) : ground.distinctList (belowM t G k) :=
  ground.distinctList_filter _ _ (ground.boxAll_distinct _)

/-- A completed scan has every coordinate on its upper side or
at equal members. -/
private theorem lowGo_none : ∀ (v : List BPair) (k : Nat),
    lowGo v k = none → ∀ x ∈ v, BPair.unit ≤ x
  | [], _, _, _, h => nomatch h
  | x :: tl, k, h, y, hy => by
    change (if x < BPair.unit then some k else lowGo tl (k + 1)) = none at h
    by_cases hx : x < BPair.unit
    · rw [if_pos hx] at h
      exact nomatch h
    · rw [if_neg hx] at h
      cases hy with
      | head => exact ground.leB_of_not_lt hx
      | tail _ ht => exact lowGo_none tl (k + 1) h y ht

/-- A list of upper-side coordinates completes the scan. -/
private theorem lowGo_of_nonneg : ∀ (v : List BPair) (k : Nat),
    (∀ x ∈ v, BPair.unit ≤ x) → lowGo v k = none
  | [], _, _ => rfl
  | x :: tl, k, h => by
    show (if x < BPair.unit then some k else lowGo tl (k + 1)) = none
    rw [if_neg (ground.leB_not_lt (h x (List.Mem.head tl)))]
    exact lowGo_of_nonneg tl (k + 1) (fun y hy => h y (List.Mem.tail x hy))

/-- At a completed scan the parity walk returns its input key and
side at every stated step count. -/
private theorem walkP_stop (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (p : Bool) (h : lowGo v 0 = none) : walkP t fuel v p = some (v, p) := by
  cases fuel with
  | zero =>
    show (match lowGo v 0 with | none => some (v, p) | some _ => none) = _
    rw [h]
  | succ n =>
    show (match lowGo v 0 with
      | none => some (v, p)
      | some i => walkP t n (assembly.reflF t i v) (!p)) = _
    rw [h]

/-- A returned scan key names a coordinate on its lower side,
with its position measured from the scan's starting key. -/
private theorem lowGo_some : ∀ (v : List BPair) (k i : Nat),
    lowGo v k = some i → ∃ j, j < v.length ∧ i = k + j
      ∧ getAt BPair.unit v j < BPair.unit
  | [], _, _, h => nomatch h
  | x :: tl, k, i, h => by
    change (if x < BPair.unit then some k else lowGo tl (k + 1)) = some i at h
    by_cases hx : x < BPair.unit
    · rw [if_pos hx] at h
      have he := Option.some.inj h
      rw [← he]
      exact ⟨0, Nat.succ_pos _, rfl, hx⟩
    · rw [if_neg hx] at h
      obtain ⟨j, hj, hij, hlow⟩ := lowGo_some tl (k + 1) i h
      exact ⟨j + 1, Nat.succ_lt_succ hj,
        hij.trans (Nat.add_right_comm k 1 j), hlow⟩

/-- A walk whose raises stay inside a capped family returns a key
once its step count clears the height gap. -/
private theorem walkP_complete (t : gentable.Table) (S : List (List BPair))
    (height : List BPair → BPair) (cap : BPair)
    (hcap : ∀ v ∈ S, height v ≤ cap)
    (hrise : ∀ v ∈ S, ∀ i, lowGo v 0 = some i →
      assembly.reflF t i v ∈ S ∧ height v + BPair.ofNat 1 ≤ height (assembly.reflF t i v)) :
    ∀ (fuel : Nat) (v : List BPair) (p : Bool), v ∈ S →
      cap ≤ height v + BPair.ofNat fuel →
      ∃ q, walkP t fuel v p = some q ∧ q.1 ∈ S
  | 0, v, p, hv, hfuel => by
    cases hl : lowGo v 0 with
    | none => exact ⟨(v, p), walkP_stop t 0 v p hl, hv⟩
    | some i =>
      obtain ⟨hmem, hgap⟩ := hrise v hv i hl
      have hh : height v + BPair.ofNat 1 ≤ height v :=
        ground.leB_trans hgap (ground.leB_trans (hcap _ hmem)
          (ground.leB_congr_right (BPair.add_unit _) hfuel))
      exact absurd (ground.ltB_addPos
        (by decide +kernel : BPair.unit < BPair.ofNat 1)) (ground.leB_not_lt hh)
  | fuel + 1, v, p, hv, hfuel => by
    cases hl : lowGo v 0 with
    | none => exact ⟨(v, p), walkP_stop t (fuel + 1) v p hl, hv⟩
    | some i =>
      obtain ⟨hmem, hgap⟩ := hrise v hv i hl
      have he : (height v + BPair.ofNat (fuel + 1)).oneValue
          (height v + BPair.ofNat 1 + BPair.ofNat fuel) := by
        refine BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl _) (BPair.ofNat_succ fuel)) ?_
        rw [BPair.add_comm (BPair.ofNat fuel) (BPair.ofNat 1), ← BPair.add_assoc]
        exact BPair.oneValue_refl _
      obtain ⟨q, hq, hqS⟩ := walkP_complete t S height cap hcap hrise fuel
        (assembly.reflF t i v) (!p) hmem
        (ground.leB_trans hfuel (ground.leB_congr_left (BPair.oneValue_symm he)
          (ground.leB_add hgap (ground.leB_refl _))))
      refine ⟨q, ?_, hqS⟩
      change (match lowGo v 0 with
        | none => some (v, p)
        | some j => walkP t fuel (assembly.reflF t j v) (!p)) = some q
      rw [hl]
      exact hq

/-- The completed scan at a canonical coroot list is the dominant
label read of `thm:memberchar`. -/
private theorem lamRead_of_lowGo (t : gentable.Table) (v : List BPair)
    (hw : v.length = t.rank) (hn : poly.pnorm v = v) (h : lowGo v 0 = none) :
    memberchar.lamRead t v :=
  ⟨hw, hn, fun k hk => lowGo_none v 0 h (ground.getAt BPair.unit v k)
    (ground.mem_getAt BPair.unit v k (by rw [hw]; exact hk))⟩

/-- Every returned parity-walk key is a canonical dominant key.
The reflection join preserves the width and its canonical form. -/
private theorem walkP_lam (t : gentable.Table) :
    ∀ (fuel : Nat) (v : List BPair) (p : Bool) (q : List BPair × Bool),
      v.length = t.rank → poly.pnorm v = v → walkP t fuel v p = some q →
      memberchar.lamRead t q.1
  | 0, v, p, q, hw, hn, h => by
    cases hl : lowGo v 0 with
    | none =>
      have he := Option.some.inj ((walkP_stop t 0 v p hl).symm.trans h)
      rw [← he]
      exact lamRead_of_lowGo t v hw hn hl
    | some i =>
      change (match lowGo v 0 with | none => some (v, p) | some _ => none) = some q at h
      rw [hl] at h
      exact nomatch h
  | fuel + 1, v, p, q, hw, hn, h => by
    cases hl : lowGo v 0 with
    | none =>
      have he := Option.some.inj ((walkP_stop t (fuel + 1) v p hl).symm.trans h)
      rw [← he]
      exact lamRead_of_lowGo t v hw hn hl
    | some i =>
      change (match lowGo v 0 with
        | none => some (v, p)
        | some j => walkP t fuel (assembly.reflF t j v) (!p)) = some q at h
      rw [hl] at h
      obtain ⟨hw', hn'⟩ := assembly.reflF_shape t i v hw
      exact walkP_lam t fuel (assembly.reflF t i v) (!p) q hw' hn' h

private theorem domWalk_result (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (hout : domWalk t fuel v ≠ []) :
    ∃ q, walkP t fuel v false = some q ∧ domWalk t fuel v = q.1 := by
  cases h : walkP t fuel v false with
  | none =>
    have he : domWalk t fuel v = [] := by
      change (match walkP t fuel v false with | none => [] | some q => q.1) = []
      rw [h]
    exact False.elim (hout he)
  | some q =>
    refine ⟨q, rfl, ?_⟩
    change (match walkP t fuel v false with | none => [] | some p => p.1) = q.1
    rw [h]

/-- A returned dominance-walk key satisfies the dominant label
read (`lem:memberdata`(ii)). The output condition separates the
returned key from the walk's refusal value. -/
theorem domWalk_lam (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (hw : v.length = t.rank) (hn : poly.pnorm v = v)
    (hout : domWalk t fuel v ≠ []) : memberchar.lamRead t (domWalk t fuel v) := by
  obtain ⟨q, hq, he⟩ := domWalk_result t fuel v hout
  rw [he]
  exact walkP_lam t fuel v false q hw hn hq

/-- A completed parity walk transports each graded orbit
count at the parity accumulated by its simple letters. The read
holds at keys outside the orbit as well (`lem:memberdata`'s
family fold at the reversed tie element). -/
theorem walkP_wCount (t : gentable.Table) (W : List (List BPair × Bool))
    (hclose : assembly.wCloseRead t W) (hsq : sertables.reflSquareRead t) :
    ∀ (fuel : Nat) (v : List BPair) (p : Bool) (q : List BPair × Bool),
      v.length = t.rank → poly.pnorm v = v → walkP t fuel v p = some q →
      ∀ side : Bool, assembly.wCount W v (xor p side) = assembly.wCount W q.1 (xor q.2 side)
  | 0, v, p, q, _, _, h, side => by
    cases hs : lowGo v 0 with
    | none =>
      have he := Option.some.inj ((walkP_stop t 0 v p hs).symm.trans h)
      rw [← he]
    | some i =>
      change (match lowGo v 0 with | none => some (v, p) | some _ => none) = some q at h
      rw [hs] at h
      exact nomatch h
  | fuel + 1, v, p, q, hv, hn, h, side => by
    cases hs : lowGo v 0 with
    | none =>
      have he := Option.some.inj ((walkP_stop t (fuel + 1) v p hs).symm.trans h)
      rw [← he]
    | some i =>
      change (match lowGo v 0 with
        | none => some (v, p)
        | some j => walkP t fuel (assembly.reflF t j v) (!p)) = some q at h
      rw [hs] at h
      obtain ⟨j, hj, he, _⟩ := lowGo_some v 0 i hs
      rw [Nat.zero_add] at he
      rw [← he, hv] at hj
      have hstep : assembly.wCount W v (xor p side)
          = assembly.wCount W (assembly.reflF t i v) (xor (!p) side) := by
        rw [assembly.reflF_eq t i v hv,
          assembly.wCount_refl t W hclose hsq i hj v hv hn]
        cases p <;> cases side <;> rfl
      exact hstep.trans (walkP_wCount t W hclose hsq fuel (assembly.reflF t i v) (!p) q
        (assembly.reflF_shape t i v hv).1 (assembly.reflF_shape t i v hv).2 h side)

/-- The endpoint and parity of a completed walk give the two
counts in a regular graded orbit. At the shifted top the read is
one on the walk's side; at every other endpoint it is vacant. -/
theorem walkP_orbit_count (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W) (hkeys : ground.distinctList (W.map Prod.fst))
    (hclose : assembly.wCloseRead t W) (hsq : sertables.reflSquareRead t)
    (top : List BPair) (htop : assembly.wTopAt W top)
    (hpin : ∀ p ∈ W, (∀ i, i < t.rank → BPair.unit < ground.getAt BPair.unit p.1 i) → p.1 = top)
    (fuel : Nat) (v : List BPair) (hv : v.length = t.rank) (hn : poly.pnorm v = v)
    (q : List BPair × Bool) (hq : walkP t fuel v false = some q) (side : Bool) :
    assembly.wCount W v side = if q.1 = top then (if q.2 = side then 1 else 0) else 0 := by
  have ht := walkP_wCount t W hclose hsq fuel v false q hv hn hq side
  have hdom := walkP_lam t fuel v false q hv hn hq
  have hb : xor false side = side := by cases side <;> rfl
  rw [hb] at ht
  rw [ht, assembly.wCount_dominant t W hshape hkeys hclose top htop hpin q.1 hdom.2.2]
  by_cases he : q.1 = top
  · rw [if_pos he, if_pos he]
    cases hp : q.2 <;> cases side <;> decide +kernel
  · rw [if_neg he, if_neg he]

/-- Two regular graded families with one dominant top have the
same counts at every key, read through any completed dominance
walk. Shape controls the counts outside the coroot carrier. -/
theorem regular_counts (t : gentable.Table) (hsq : sertables.reflSquareRead t)
    (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (W R : List (List BPair × Bool))
    (hw : sertables.wShapeRead t W) (hr : sertables.wShapeRead t R)
    (hdw : ground.distinctList (W.map Prod.fst)) (hdr : ground.distinctList (R.map Prod.fst))
    (hcw : assembly.wCloseRead t W) (hcr : assembly.wCloseRead t R)
    (top : List BPair) (htw : assembly.wTopAt W top) (htr : assembly.wTopAt R top)
    (hpw : ∀ p ∈ W, (∀ i, i < t.rank → BPair.unit < ground.getAt BPair.unit p.1 i) → p.1 = top)
    (hpr : ∀ p ∈ R, (∀ i, i < t.rank → BPair.unit < ground.getAt BPair.unit p.1 i) → p.1 = top)
    (v : List BPair) (side : Bool) : assembly.wCount W v side = assembly.wCount R v side := by
  by_cases hf : v.length = t.rank ∧ poly.pnorm v = v
  · have hout := hwalk v hf.1
    rw [hf.2] at hout
    obtain ⟨q, hq, _⟩ := domWalk_result t fuel v hout
    rw [walkP_orbit_count t W hw hdw hcw hsq top htw hpw fuel v hf.1 hf.2 q hq side,
      walkP_orbit_count t R hr hdr hcr hsq top htr hpr fuel v hf.1 hf.2 q hq side]
  · rw [assembly.wCount_offFrame t W hw v hf side, assembly.wCount_offFrame t R hr v hf side]

/-- A natural measure dropping once per selected reflection bounds
the actual parity walk, regardless of the magnitude of its seed. -/
private theorem walkP_measure (t : gentable.Table) (measure : List BPair → Nat)
    (hstep : ∀ v, v.length = t.rank → ∀ i, lowGo v 0 = some i →
      measure (assembly.reflF t i v) + 1 = measure v) :
    ∀ fuel v p, v.length = t.rank → measure v ≤ fuel →
      ∃ q, walkP t fuel v p = some q
  | 0, v, p, hv, hm => by
    cases hs : lowGo v 0 with
    | none => exact ⟨(v, p), walkP_stop t 0 v p hs⟩
    | some i =>
      have he := hstep v hv i hs
      rw [← he] at hm
      exact False.elim (Nat.not_succ_le_zero _ hm)
  | fuel + 1, v, p, hv, hm => by
    cases hs : lowGo v 0 with
    | none => exact ⟨(v, p), walkP_stop t (fuel + 1) v p hs⟩
    | some i =>
      have he := hstep v hv i hs
      rw [← he] at hm
      obtain ⟨q, hq⟩ := walkP_measure t measure hstep fuel (assembly.reflF t i v) (!p)
        (assembly.reflF_shape t i v hv).1 (Nat.le_of_succ_le_succ hm)
      refine ⟨q, ?_⟩
      change (match lowGo v 0 with
        | none => some (v, p)
        | some j => walkP t fuel (assembly.reflF t j v) (!p)) = some q
      rw [hs]
      exact hq

/-- The displayed positive-root count completes a member's
actual dominance walk. A chosen negative simple pair removes
one negative root pairing at each step. -/
theorem domWalk_root_complete (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hsp : sertables.simplePosRead t F) (hsq : sertables.reflSquareRead t)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hform : sertables.reflFormRead t F)
    (fuel : Nat) (hfuel : t.posFolds.length ≤ fuel) (v : List BPair) (hv : v.length = t.rank) :
    memberchar.lamRead t (domWalk t fuel (poly.pnorm v)) := by
  have hstep : ∀ w : List BPair, w.length = t.rank → ∀ i, lowGo w 0 = some i →
      assembly.rootNegCount t F (assembly.reflF t i w) + 1 = assembly.rootNegCount t F w := by
    intro w hw i hs
    obtain ⟨j, hj, hij, hn⟩ := lowGo_some w 0 i hs
    rw [Nat.zero_add] at hij
    rw [← hij] at hj hn
    rw [hw] at hj
    exact assembly.rootNegCount_step t F hshape hgram hsp hsq hpsq hpi hrd hform w hw i hj hn
  have hn := poly.pnorm_pnorm v
  have hw : (poly.pnorm v).length = t.rank := (poly.pnorm_length v).trans hv
  obtain ⟨q, hq⟩ := walkP_measure t (assembly.rootNegCount t F) hstep fuel (poly.pnorm v) false hw
    (Nat.le_trans (assembly.rootNegCount_le t F _) hfuel)
  have he : domWalk t fuel (poly.pnorm v) = q.1 := by
    change (match walkP t fuel (poly.pnorm v) false with | none => [] | some p => p.1) = q.1
    rw [hq]
  rw [he]
  exact walkP_lam t fuel (poly.pnorm v) false q hw hn hq


/-- A predicate kept by each selected reflection holds at every
completed parity-walk result. -/
private theorem walkP_invariant (t : gentable.Table) (P : List BPair → Prop)
    (hstep : ∀ v, v.length = t.rank → P v → ∀ i, lowGo v 0 = some i → P (assembly.reflF t i v)) :
    ∀ fuel v p q, v.length = t.rank → P v → walkP t fuel v p = some q → P q.1
  | 0, v, p, q, _, hp, h => by
    cases hs : lowGo v 0 with
    | none =>
      have he := Option.some.inj ((walkP_stop t 0 v p hs).symm.trans h)
      rw [← he]
      exact hp
    | some i =>
      change (match lowGo v 0 with | none => some (v, p) | some _ => none) = some q at h
      rw [hs] at h
      exact nomatch h
  | fuel + 1, v, p, q, hv, hp, h => by
    cases hs : lowGo v 0 with
    | none =>
      have he := Option.some.inj ((walkP_stop t (fuel + 1) v p hs).symm.trans h)
      rw [← he]
      exact hp
    | some i =>
      change (match lowGo v 0 with
        | none => some (v, p)
        | some j => walkP t fuel (assembly.reflF t j v) (!p)) = some q at h
      rw [hs] at h
      exact walkP_invariant t P hstep fuel (assembly.reflF t i v) (!p) q
        (assembly.reflF_shape t i v hv).1 (hstep v hv hp i hs) h

/-- A completed dominance walk never lowers the cleared rho
pairing of its input. -/
theorem domWalk_rho_mono (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hsp : sertables.simplePosRead t F)
    (hrd : sertables.rhoDotRead t F) (fuel : Nat) (v : List BPair) (hv : v.length = t.rank)
    (hout : domWalk t fuel v ≠ []) :
    sertables.dotB F v (sertables.rhoV t)
      ≤ sertables.dotB F (domWalk t fuel v) (sertables.rhoV t) := by
  have hrise : ∀ w, w.length = t.rank → ∀ i, lowGo w 0 = some i →
      sertables.dotB F w (sertables.rhoV t) ≤ sertables.dotB F (assembly.reflF t i w) (sertables.rhoV t) := by
    intro w hw i hs
    obtain ⟨j, hj, hij, hn⟩ := lowGo_some w 0 i hs
    rw [Nat.zero_add] at hij
    rw [← hij] at hj hn
    rw [hw] at hj
    rw [assembly.reflF_eq t i w hw]
    exact ground.leB_trans
      (ground.leB_of_lt (ground.ltB_addPos (by decide +kernel : BPair.unit < BPair.ofNat 1)))
      (assembly.rise_gap t F hshape hsp hrd i hj w hw hn)
  obtain ⟨q, hq, he⟩ := domWalk_result t fuel v hout
  rw [he]
  exact walkP_invariant t (fun w => sertables.dotB F v (sertables.rhoV t) ≤ sertables.dotB F w (sertables.rhoV t))
    (fun w hw hp i hs => ground.leB_trans hp (hrise w hw i hs)) fuel v false q hv (ground.leB_refl _) hq

/-- A completed parity walk has the same result at every larger
fuel, including its terminal step at zero remaining fuel. -/
private theorem walkP_more (t : gentable.Table) : ∀ fuel extra v p q,
    walkP t fuel v p = some q → walkP t (fuel + extra) v p = some q
  | 0, extra, v, p, q, h => by
    cases hs : lowGo v 0 with
    | none =>
      rw [walkP_stop t 0 v p hs] at h
      exact (walkP_stop t (0 + extra) v p hs).trans h
    | some i =>
      change (match lowGo v 0 with | none => some (v, p) | some _ => none) = some q at h
      rw [hs] at h
      exact nomatch h
  | fuel + 1, extra, v, p, q, h => by
    cases hs : lowGo v 0 with
    | none =>
      rw [walkP_stop t (fuel + 1) v p hs] at h
      exact (walkP_stop t (fuel + 1 + extra) v p hs).trans h
    | some i =>
      change (match lowGo v 0 with
        | none => some (v, p)
        | some j => walkP t fuel (assembly.reflF t j v) (!p)) = some q at h
      rw [hs] at h
      rw [Nat.add_right_comm fuel 1 extra]
      change (match lowGo v 0 with
        | none => some (v, p)
        | some j => walkP t (fuel + extra) (assembly.reflF t j v) (!p)) = some q
      rw [hs]
      exact walkP_more t fuel extra _ _ q h

/-- A completed dominance walk is fixed at every larger fuel. -/
theorem domWalk_more (t : gentable.Table) (fuel extra : Nat) (v : List BPair)
    (h : domWalk t fuel v ≠ []) : domWalk t (fuel + extra) v = domWalk t fuel v := by
  obtain ⟨q, hq, he⟩ := domWalk_result t fuel v h
  rw [he]
  change (match walkP t (fuel + extra) v false with | none => [] | some p => p.1) = q.1
  rw [walkP_more t fuel extra v false q hq]

/-- At completed width-matched walks, increasing their fuel
preserves the actual numerator, including all refusal branches. -/
theorem numAt_more (t : gentable.Table) (G : elim.Mat) (fuel extra : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (acc : List (List Nat × Nat)) (top : Nat) (m : List Nat) (hm : m.length = t.rank) :
    numAt t G (fuel + extra) acc top m = numAt t G fuel acc top m := by
  unfold numAt
  apply ground.foldl_congr
  intro s j
  cases s with
  | none => rfl
  | some a =>
    apply ground.foldl_congr
    intro s k
    cases s with
    | none => rfl
    | some b =>
      let av := poly.pnorm (sertables.posCorootV t j)
      let raw := elim.vecAdd (natV m) (elim.vecScale (BPair.ofNat (k + 1)) av)
      have hl : raw.length = t.rank := elim.length_vecAdd _ _ t.rank
        ((ground.length_map BPair.ofNat m).trans hm)
        ((elim.length_vecScale _ _).trans ((poly.pnorm_length _).trans (sertables.posCorootV_length t j)))
      have he := domWalk_more t fuel extra (poly.pnorm raw) (hwalk raw hl)
      change (if domWalk t (fuel + extra) (poly.pnorm raw) == [] then none else _) =
        (if domWalk t fuel (poly.pnorm raw) == [] then none else _)
      rw [he]

/-- The actual dominance walk preserves every multiplicity in a
reflection-invariant framed family, including unoccupied keys. -/
theorem domWalk_count (t : gentable.Table) (L : List (List BPair))
    (hsq : sertables.reflSquareRead t) (hshape : memberchar.mShapeRead t L)
    (hsym : memberchar.symRead t L) (fuel : Nat) (v : List BPair)
    (hv : v.length = t.rank) (hn : poly.pnorm v = v) (hout : domWalk t fuel v ≠ []) :
    ground.countOf (domWalk t fuel v) L = ground.countOf v L := by
  have hstep : ∀ w, w.length = t.rank →
      (poly.pnorm w = w ∧ ground.countOf w L = ground.countOf v L) → ∀ i, lowGo w 0 = some i →
      poly.pnorm (assembly.reflF t i w) = assembly.reflF t i w
        ∧ ground.countOf (assembly.reflF t i w) L = ground.countOf v L := by
    intro w hw hp i hs
    obtain ⟨j, hj, hij, _⟩ := lowGo_some w 0 i hs
    rw [Nat.zero_add] at hij
    rw [← hij, hw] at hj
    refine ⟨(assembly.reflF_shape t i w hw).2, ?_⟩
    rw [assembly.reflF_eq t i w hw, memberchar.count_reflAt t L hsq hshape hsym i hj w hw hp.1]
    exact hp.2
  obtain ⟨q, hq, he⟩ := domWalk_result t fuel v hout
  rw [he]
  exact (walkP_invariant t (fun w => poly.pnorm w = w ∧ ground.countOf w L = ground.countOf v L)
    hstep fuel v false q hv ⟨hn, rfl⟩ hq).2

/-- A positive-root string move followed by its completed
dominance walk reads a strictly higher natural rho key. Thus a
trace numerator only consumes multiplicities above its own key. -/
theorem moved_dom_rdKey (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hsp : sertables.simplePosRead t F)
    (hrd : sertables.rhoDotRead t F) (fuel : Nat) (m : List Nat) (hm : m.length = t.rank)
    (hbase : BPair.unit ≤ sertables.dotB F (natV m) (sertables.rhoV t))
    (j k : Nat) (hj : j < t.posFolds.length)
    (hout : domWalk t fuel (poly.pnorm (elim.vecAdd (natV m)
      (elim.vecScale (BPair.ofNat (k + 1)) (poly.pnorm (sertables.posCorootV t j))))) ≠ []) :
    rdKey t F.gram m < rdKey t F.gram (natsOf (domWalk t fuel (poly.pnorm (elim.vecAdd (natV m)
      (elim.vecScale (BPair.ofNat (k + 1)) (poly.pnorm (sertables.posCorootV t j))))))) := by
  let av := poly.pnorm (sertables.posCorootV t j)
  let raw := elim.vecAdd (natV m) (elim.vecScale (BPair.ofNat (k + 1)) av)
  let mv := poly.pnorm raw
  let w := domWalk t fuel mv
  have ha : av.length = t.rank := (poly.pnorm_length _).trans (sertables.posCorootV_length t j)
  have hm' : (natV m).length = t.rank := (ground.length_map BPair.ofNat m).trans hm
  have hs : (elim.vecScale (BPair.ofNat (k + 1)) av).length = t.rank := (elim.length_vecScale _ _).trans ha
  have hraw : raw.length = t.rank := elim.length_vecAdd _ _ t.rank hm' hs
  have hmv : mv.length = t.rank := (poly.pnorm_length raw).trans hraw
  have hav : BPair.unit < sertables.dotB F av (sertables.rhoV t) :=
    BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm
      (sertables.dotB_congrL F _ _ _ (poly.pnorm_oneValue _))) (hrd j hj)
  have hpair : (sertables.dotB F mv (sertables.rhoV t)).oneValue
      (sertables.dotB F (natV m) (sertables.rhoV t)
        + BPair.ofNat (k + 1) * sertables.dotB F av (sertables.rhoV t)) :=
    BPair.oneValue_trans (sertables.dotB_congrL F _ _ _ (poly.pnorm_oneValue raw))
      (BPair.oneValue_trans (sertables.dotB_addL t F hshape (natV m)
        (elim.vecScale (BPair.ofNat (k + 1)) av) (sertables.rhoV t) hm' hs)
        (BPair.add_congr (BPair.oneValue_refl _) (elim.dotP_scaleL _ _ _)))
  have hmove : sertables.dotB F (natV m) (sertables.rhoV t) < sertables.dotB F mv (sertables.rhoV t) :=
    BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hpair)
      (ground.ltB_addPos (ground.unitLtMul (ground.unitLtNat (Nat.succ_pos k)) hav))
  have hmono := domWalk_rho_mono t F hshape hsp hrd fuel mv hmv hout
  have hdom : memberchar.lamRead t w := domWalk_lam t fuel mv hmv (poly.pnorm_pnorm raw) hout
  have hn : poly.oneValue (natV (natsOf w)) w :=
    natV_natsOf w (fun i hi => hdom.2.2 i (by rw [← hdom.1]; exact hi))
  have hleft : rdKey t F.gram m = (sertables.dotB F (natV m) (sertables.rhoV t)).marginN :=
    BPair.marginN_congr (BPair.norm_oneValue _)
  have hright : rdKey t F.gram (natsOf w) = (sertables.dotB F w (sertables.rhoV t)).marginN :=
    BPair.marginN_congr (BPair.oneValue_trans (BPair.norm_oneValue _)
      (sertables.dotB_congrL F _ _ _ hn))
  change rdKey t F.gram m < rdKey t F.gram (natsOf w)
  rw [hleft, hright]
  exact BPair.marginN_lt hbase (ground.ltB_trans_le hmove hmono)

/-- At the higher dominant counts of a reflection-invariant
family, the actual numerator returns the trace correction. The
family's height bound fixes the stored string caps, and each
completed walk transports the moved key's count. -/
theorem numAt_gSum (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgsym : sertables.gramSymRead F)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (hsq : sertables.reflSquareRead t) (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (L : List (List BPair)) (hmsh : memberchar.mShapeRead t L)
    (hsym : memberchar.symRead t L) (acc : List (List Nat × Nat))
    (top : Nat) (m : List Nat) (hm : m.length = t.rank)
    (hbase : BPair.unit ≤ sertables.dotB F (natV m) (sertables.rhoV t))
    (htop : ∀ v, 0 < ground.countOf v L →
      sertables.dotB F v (sertables.rhoV t) ≤ BPair.ofNat top)
    (hacc : ∀ w, memberchar.lamRead t w →
      rdKey t F.gram m < rdKey t F.gram (natsOf w) →
      lookupN (natsOf w) acc = ground.countOf w L) :
    ∃ n, numAt t F.gram fuel acc top m = some n
      ∧ n.oneValue (memberchar.gSum t F L (natV m)) := by
  obtain ⟨n, hn, hv⟩ := numAt_read t F.gram fuel hwalk acc top m hm
  refine ⟨n, hn, BPair.oneValue_trans hv ?_⟩
  have hm' : (natV m).length = t.rank := (ground.length_map BPair.ofNat m).trans hm
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
    (memberchar.gSum_height t F hshape hgsym hrd L (natV m) hm' hbase top htop))
  apply ground.foldB_congr_members
  intro j hj
  have hj' := ground.ltOfMem hj
  let a := sertables.posCorootV t j
  let av := poly.pnorm a
  have ha : a.length = t.rank := sertables.posCorootV_length t j
  have hav : av.length = t.rank := (poly.pnorm_length a).trans ha
  have hb : rdKey t F.gram m = (sertables.dotB F (natV m) (sertables.rhoV t)).marginN :=
    BPair.marginN_congr (BPair.norm_oneValue _)
  have hd : (formC F.gram av (sertables.rhoV t)).marginN
      = (sertables.dotB F a (sertables.rhoV t)).marginN :=
    BPair.marginN_congr (BPair.oneValue_trans (BPair.norm_oneValue _)
      (sertables.dotB_congrL F _ _ _ (poly.pnorm_oneValue a)))
  change (ground.bsum (fun k =>
      let mv := poly.pnorm (elim.vecAdd (natV m) (elim.vecScale (BPair.ofNat (k + 1)) av))
      formC F.gram mv av * BPair.ofNat (2 * lookupN (natsOf (domWalk t fuel mv)) acc))
      (List.range ((top - rdKey t F.gram m) /
        (formC F.gram av (sertables.rhoV t)).marginN))).oneValue _
  rw [hb, hd]
  apply ground.foldB_congr_members
  intro k _
  let raw := elim.vecAdd (natV m) (elim.vecScale (BPair.ofNat (k + 1)) av)
  let mv := poly.pnorm raw
  have hraw : raw.length = t.rank := elim.length_vecAdd _ _ t.rank hm'
    ((elim.length_vecScale _ av).trans hav)
  have hmv : mv.length = t.rank := (poly.pnorm_length raw).trans hraw
  have hout : domWalk t fuel mv ≠ [] := hwalk raw hraw
  have hl := domWalk_lam t fuel mv hmv (poly.pnorm_pnorm raw) hout
  have hc : lookupN (natsOf (domWalk t fuel mv)) acc = ground.countOf mv L :=
    (hacc _ hl (moved_dom_rdKey t F hshape hsp hrd fuel m hm hbase j k hj' hout)).trans
      (domWalk_count t L hsq hmsh hsym fuel mv hmv (poly.pnorm_pnorm raw) hout)
  have hk : mv = poly.pnorm (elim.vecAdd (natV m)
      (elim.vecScale (BPair.ofNat (k + 1)) a)) := by
    apply poly.pnorm_congr
    · exact hraw.trans (elim.length_vecAdd _ _ t.rank hm'
        ((elim.length_vecScale _ a).trans ha)).symm
    · exact elim.vecAdd_congr2 _ _ _ _ rfl
        (by rw [elim.length_vecScale, elim.length_vecScale, poly.pnorm_length])
        (poly.oneValue_refl _) (elim.vecScale_oneValue _ av a (poly.pnorm_oneValue a))
  change (formC F.gram mv av * BPair.ofNat (2 * lookupN (natsOf (domWalk t fuel mv)) acc)).oneValue _
  rw [hc]
  refine BPair.oneValue_trans (BPair.mul_congr
    (BPair.oneValue_trans (BPair.norm_oneValue _)
      (sertables.dotB_congrR F mv av a (poly.pnorm_oneValue a))) (BPair.oneValue_refl _)) ?_
  rw [hk]
  exact BPair.oneValue_refl _

/-- At support below a natural top, the actual numerator's
height cap is the top label's own rho key. -/
theorem numAt_support (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgsym : sertables.gramSymRead F)
    (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (hsq : sertables.reflSquareRead t) (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (L : List (List BPair)) (hmsh : memberchar.mShapeRead t L)
    (hsym : memberchar.symRead t L) (wits : List (List Nat))
    (lam : List Nat) (hlam : lam.length = t.rank)
    (hsupp : memberchar.supportRead t L wits (natV lam))
    (htop : BPair.unit ≤ sertables.dotB F (natV lam) (sertables.rhoV t))
    (acc : List (List Nat × Nat)) (m : List Nat) (hm : m.length = t.rank)
    (hbase : BPair.unit ≤ sertables.dotB F (natV m) (sertables.rhoV t))
    (hacc : ∀ w, memberchar.lamRead t w →
      rdKey t F.gram m < rdKey t F.gram (natsOf w) →
      lookupN (natsOf w) acc = ground.countOf w L) :
    ∃ n, numAt t F.gram fuel acc (rdKey t F.gram lam) m = some n
      ∧ n.oneValue (memberchar.gSum t F L (natV m)) := by
  apply numAt_gSum t F hshape hgsym hsp hrd hsq fuel hwalk L hmsh hsym
    acc _ m hm hbase _ hacc
  intro v hv
  have h := memberchar.supportRead_height t F hshape hsp hrd L wits (natV lam)
    ((ground.length_map BPair.ofNat lam).trans hlam) hsupp v hv
  have he : rdKey t F.gram lam = (sertables.dotB F (natV lam) (sertables.rhoV t)).marginN :=
    BPair.marginN_congr (BPair.norm_oneValue _)
  rw [he]
  exact ground.leB_congr_right (BPair.ofNat_marginN htop) h

/-- The actual non-top recursion step has a positive divisor,
zero remainder and the family's multiplicity as its quotient,
once the higher dominant counts are present in its accumulator. -/
theorem numAt_rec_count (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F) (hsp : sertables.simplePosRead t F)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hrsq : sertables.reflSquareRead t)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (lam : List Nat) (hlam : lam.length = t.rank) (m : List Nat)
    (hm : m ∈ domKeys t F.gram lam) (hne : m ≠ lam)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hmsh : memberchar.mShapeRead t L) (hsym : memberchar.symRead t L)
    (wits : List (List Nat)) (hsupp : memberchar.supportRead t L wits (natV lam))
    (hseed : (sertables.rhoV t, false) ∈ W)
    (hrec : memberchar.recRead t F W L (poly.pnorm (natV lam)))
    (htop : BPair.unit ≤ sertables.dotB F (natV lam) (sertables.rhoV t))
    (hbase : BPair.unit ≤ sertables.dotB F (natV m) (sertables.rhoV t))
    (acc : List (List Nat × Nat))
    (hacc : ∀ w, memberchar.lamRead t w →
      rdKey t F.gram m < rdKey t F.gram (natsOf w) →
      lookupN (natsOf w) acc = ground.countOf w L) :
    let den := BPair.marginN (BPair.norm (formC F.gram (shiftV t lam) (shiftV t lam)
      + (formC F.gram (shiftV t m) (shiftV t m)).swap))
    ∃ n, numAt t F.gram fuel acc (rdKey t F.gram lam) m = some n
      ∧ 0 < den ∧ n.norm.marginN % den = 0
      ∧ n.norm.marginN / den = ground.countOf (natV m) L := by
  obtain ⟨n, hn, hv⟩ := numAt_support t F hshape hgsym hsp hrd hrsq fuel hwalk
    L hmsh hsym wits lam hlam hsupp htop acc m (domKeys_length t F.gram lam m hm) hbase hacc
  have hnum : n.oneValue (memberchar.gSum t F L (poly.pnorm (natV m))) := by
    rw [natV_pnorm]
    exact hv
  have h := recRead_cofactor t F hshape hgram hgsym hsp hpsq hpi hrd hsq hlead hdet
    lam hlam m hm hne W L hseed hrec n hnum
  rw [natV_pnorm] at h
  exact ⟨n, hn, h⟩

/-- An upper-side key is fixed by the dominance walk. -/
theorem domWalk_of_nonneg (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (h : ∀ x ∈ v, BPair.unit ≤ x) : domWalk t fuel v = v := by
  show (match walkP t fuel v false with | none => [] | some q => q.1) = v
  rw [walkP_stop t fuel v false (lowGo_of_nonneg v 0 h)]

/-- A selected lower-side coordinate raises the cleared rho-dot
inside a reflection-closed family. -/
private theorem lowGo_rise (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hsp : sertables.simplePosRead t F)
    (hrd : sertables.rhoDotRead t F)
    (S : List (List BPair)) (hS : memberchar.mShapeRead t S)
    (hclose : ∀ v ∈ S, ∀ i, i < t.rank → assembly.reflF t i v ∈ S)
    (w : List BPair) (hw : w ∈ S) (i : Nat) (hi : lowGo w 0 = some i) :
    assembly.reflF t i w ∈ S
      ∧ sertables.dotB F w (sertables.rhoV t) + BPair.ofNat 1
        ≤ sertables.dotB F (assembly.reflF t i w) (sertables.rhoV t) := by
  obtain ⟨j, hj, hij, hlow⟩ := lowGo_some w 0 i hi
  rw [Nat.zero_add] at hij
  rw [← hij] at hj hlow
  rw [(hS w hw).1] at hj
  refine ⟨hclose w hw i hj, ?_⟩
  rw [assembly.reflF_eq t i w (hS w hw).1]
  exact assembly.rise_gap t F hshape hsp hrd i hj w (hS w hw).1 hlow

/-- The dominance walk returns a dominant member of a finite
reflection-closed family at its rho-dot cap (`lem:memberdata`(i)).
Each lower-side raise gains at least one in the cleared dot
(`thm:assembly`), so the stated gap's step count completes the walk. -/
theorem domWalk_complete (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hsp : sertables.simplePosRead t F)
    (hrd : sertables.rhoDotRead t F)
    (S : List (List BPair)) (hS : memberchar.mShapeRead t S)
    (hclose : ∀ v ∈ S, ∀ i, i < t.rank → assembly.reflF t i v ∈ S)
    (cap : BPair) (hcap : ∀ v ∈ S, sertables.dotB F v (sertables.rhoV t) ≤ cap)
    (fuel : Nat) (v : List BPair) (hv : v ∈ S)
    (hfuel : cap ≤ sertables.dotB F v (sertables.rhoV t) + BPair.ofNat fuel) :
    domWalk t fuel v ∈ S ∧ memberchar.lamRead t (domWalk t fuel v) := by
  obtain ⟨q, hq, hqS⟩ := walkP_complete t S
    (fun w => sertables.dotB F w (sertables.rhoV t)) cap hcap
    (lowGo_rise t F hshape hsp hrd S hS hclose) fuel v false hv hfuel
  have he : domWalk t fuel v = q.1 := by
    show (match walkP t fuel v false with | none => [] | some q => q.1) = q.1
    rw [hq]
  rw [he]
  exact ⟨hqS, walkP_lam t fuel v false q (hS v hv).1 (hS v hv).2 hq⟩

/-- A strictly rising scalar read on a finite reflection-closed
family bounds the dominance walk by that family's count. -/
theorem domWalk_finite_height (t : gentable.Table) (S : List (List BPair))
    (hS : memberchar.mShapeRead t S)
    (hclose : ∀ v ∈ S, ∀ i, i < t.rank → assembly.reflF t i v ∈ S)
    (dot : List BPair → BPair)
    (hrise : ∀ w ∈ S, ∀ i, i < t.rank → ground.getAt BPair.unit w i < BPair.unit →
      dot w < dot (assembly.reflF t i w))
    (fuel : Nat) (hfuel : S.length ≤ fuel) (v : List BPair) (hv : v ∈ S) :
    domWalk t fuel v ∈ S ∧ memberchar.lamRead t (domWalk t fuel v) := by
  let rank := fun w => ground.countBy (fun z => decide (dot z ≤ dot w)) S
  have hcap : ∀ w ∈ S, BPair.ofNat (rank w) ≤ BPair.ofNat S.length := by
    intro w _
    apply ground.leB_ofNat
    rw [show rank w = (S.filter (fun z => decide (dot z ≤ dot w))).length
      from (ground.length_filterBy _ _).symm]
    exact ground.length_filter_le _ _
  have hrise : ∀ w ∈ S, ∀ i, lowGo w 0 = some i →
      assembly.reflF t i w ∈ S ∧ BPair.ofNat (rank w) + BPair.ofNat 1
        ≤ BPair.ofNat (rank (assembly.reflF t i w)) := by
    intro w hw i hi
    obtain ⟨j, hj, hij, hlow⟩ := lowGo_some w 0 i hi
    rw [Nat.zero_add] at hij
    rw [← hij] at hj hlow
    rw [(hS w hw).1] at hj
    have hmem := hclose w hw i hj
    have hlt : dot w < dot (assembly.reflF t i w) := hrise w hw i hj hlow
    let P := fun z => decide (dot z ≤ dot w)
    let Q := fun z => decide (dot z ≤ dot (assembly.reflF t i w))
    have himp : ∀ z, P z = true → Q z = true := fun z hz =>
      decide_eq_true (ground.leB_trans (of_decide_eq_true hz) (ground.leB_of_lt hlt))
    have hle : rank w ≤ rank (assembly.reflF t i w) := ground.countBy_mono P Q himp S
    have hne : rank (assembly.reflF t i w) ≠ rank w := by
      intro he
      have hall := ground.countBy_eq_all P Q himp S he.symm
      have h := ground.all_of_mem _ S hall (assembly.reflF t i w) hmem
      have hp : P (assembly.reflF t i w) = false :=
        decide_eq_false (ground.leB_not_lt · hlt)
      have hq : Q (assembly.reflF t i w) = true := decide_eq_true (ground.leB_refl _)
      rw [hp, hq] at h
      exact Bool.noConfusion h
    exact ⟨hmem, ground.leB_congr_left (BPair.ofNat_add _ _)
      (ground.leB_ofNat (Nat.lt_of_le_of_ne hle (fun he => hne he.symm)))⟩
  obtain ⟨q, hq, hqS⟩ := walkP_complete t S (fun w => BPair.ofNat (rank w))
    (BPair.ofNat S.length) hcap hrise fuel v false hv
    (ground.leB_congr_right (BPair.ofNat_add _ _)
      (ground.leB_ofNat (Nat.le_trans hfuel (Nat.le_add_left _ _))))
  have he : domWalk t fuel v = q.1 := by
    show (match walkP t fuel v false with | none => [] | some q => q.1) = q.1
    rw [hq]
  rw [he]
  exact ⟨hqS, walkP_lam t fuel v false q (hS v hv).1 (hS v hv).2 hq⟩

/-- A finite reflection-closed family's count bounds the dominance
walk (`con:sertables`; `lem:memberdata`). Each raise strictly grows
the number of family entries at or below its rho-dot, a count at
or below the family's length. -/
theorem domWalk_finite (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hsp : sertables.simplePosRead t F)
    (hrd : sertables.rhoDotRead t F)
    (S : List (List BPair)) (hS : memberchar.mShapeRead t S)
    (hclose : ∀ v ∈ S, ∀ i, i < t.rank → assembly.reflF t i v ∈ S)
    (fuel : Nat) (hfuel : S.length ≤ fuel) (v : List BPair) (hv : v ∈ S) :
    domWalk t fuel v ∈ S ∧ memberchar.lamRead t (domWalk t fuel v) := by
  apply domWalk_finite_height t S hS hclose
    (fun w => sertables.dotB F w (sertables.rhoV t)) ?_ fuel hfuel v hv
  intro w hw i hi hlow
  have hgap := assembly.rise_gap t F hshape hsp hrd i hi w (hS w hw).1 hlow
  rw [← assembly.reflF_eq t i w (hS w hw).1] at hgap
  exact ground.ltB_trans_le (ground.ltB_addPos
    (by decide +kernel : BPair.unit < BPair.ofNat 1)) hgap

/-- The displayed family's length completes the dominance walk from any of its keys
when each lower-side reflection raises its scalar pairing. -/
theorem domWalk_finite_family_keys (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W)
    (hclose : ∀ w ∈ W, ∀ i, i < t.rank → (assembly.reflF t i w.1, !w.2) ∈ W)
    (dot : List BPair → BPair)
    (hrise : ∀ w, w.length = t.rank → ∀ i, i < t.rank →
      ground.getAt BPair.unit w i < BPair.unit → dot w < dot (assembly.reflF t i w))
    (fuel : Nat) (hfuel : W.length ≤ fuel) (v : List BPair) (hv : poly.pnorm v ∈ W.map Prod.fst) :
    domWalk t fuel (poly.pnorm v) ∈ W.map Prod.fst
      ∧ memberchar.lamRead t (domWalk t fuel (poly.pnorm v)) := by
  have hs : memberchar.mShapeRead t (W.map Prod.fst) := by
    intro w hw
    obtain ⟨p, hp, he⟩ := ground.mem_map_of Prod.fst W w hw
    rw [← he]
    exact hshape p hp
  apply domWalk_finite_height t (W.map Prod.fst) hs ?_ dot
    (fun w hw => hrise w (hs w hw).1) fuel
    (by rw [ground.length_map]; exact hfuel) (poly.pnorm v) hv
  intro w hw i hi
  obtain ⟨p, hp, he⟩ := ground.mem_map_of Prod.fst W w hw
  rw [← he]
  exact ground.mem_map_to Prod.fst (hclose p hp i hi)

/-- The displayed family's length completes the dominance walk
when each lower-side reflection raises its scalar pairing. -/
theorem domWalk_finite_family (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W)
    (hclose : ∀ w ∈ W, ∀ i, i < t.rank → (assembly.reflF t i w.1, !w.2) ∈ W)
    (dot : List BPair → BPair)
    (hrise : ∀ w, w.length = t.rank → ∀ i, i < t.rank →
      ground.getAt BPair.unit w i < BPair.unit → dot w < dot (assembly.reflF t i w))
    (fuel : Nat) (hfuel : W.length ≤ fuel) (v : List BPair) (hv : (poly.pnorm v, false) ∈ W) :
    domWalk t fuel (poly.pnorm v) ∈ W.map Prod.fst
      ∧ memberchar.lamRead t (domWalk t fuel (poly.pnorm v)) :=
  domWalk_finite_family_keys t W hshape hclose dot hrise fuel hfuel v (ground.mem_map_to Prod.fst hv)

private theorem domWalk_eq_of_top (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W) (hkeys : ground.distinctList (W.map Prod.fst))
    (hclose : assembly.wCloseRead t W) (top : List BPair)
    (htop : ∀ p ∈ W, (∀ i, i < t.rank → BPair.unit < ground.getAt BPair.unit p.1 i) →
      poly.pnorm p.1 = poly.pnorm top)
    (fuel : Nat) (v : List BPair)
    (hwalk : domWalk t fuel (poly.pnorm v) ∈ W.map Prod.fst
      ∧ memberchar.lamRead t (domWalk t fuel (poly.pnorm v))) :
    domWalk t fuel (poly.pnorm v) = poly.pnorm top := by
  obtain ⟨p, hp, he⟩ := ground.mem_map_of Prod.fst W _ hwalk.1
  have hstrict := assembly.wClose_strict t W hshape hkeys hclose p hp (by
    intro i hi
    rw [he]
    exact hwalk.2.2.2 i hi)
  have h := htop p hp hstrict
  rw [he, hwalk.2.2.1] at h
  exact h

/-- A returned dual label has one coroot coordinate per simple
key (`lem:memberdata`(ii)), the shift and the final unit withdrawal
preserving the coordinate list. -/
theorem dualM_length (t : gentable.Table) (fuel : Nat) (a : List Nat)
    (ha : a.length = t.rank)
    (hout : domWalk t fuel (poly.pnorm (poly.neg (shiftV t a))) ≠ []) :
    (dualM t fuel a).length = t.rank := by
  have hshift := shiftV_length t a ha
  have hs := domWalk_lam t fuel (poly.pnorm (poly.neg (shiftV t a)))
    (by rw [poly.pnorm_length, poly.length_neg, hshift]) (poly.pnorm_pnorm _) hout
  show (((domWalk t fuel (poly.pnorm (poly.neg (shiftV t a)))).map
    BPair.marginN).map (fun x => x - 1)).length = t.rank
  rw [ground.length_map, ground.length_map]
  exact hs.1

/-- A dominance walk complete at every coroot key returns a dual
label of the table's width at every label of that width. -/
theorem dualM_length_complete (t : gentable.Table) (fuel : Nat)
    (hcomplete : ∀ v : List BPair, v.length = t.rank →
      memberchar.lamRead t (domWalk t fuel (poly.pnorm v)))
    (a : List Nat) (ha : a.length = t.rank) : (dualM t fuel a).length = t.rank := by
  have h := hcomplete (poly.neg (shiftV t a)) (by rw [poly.length_neg, shiftV_length t a ha])
  show (((domWalk t fuel (poly.pnorm (poly.neg (shiftV t a)))).map
    BPair.marginN).map (fun x => x - 1)).length = t.rank
  rw [ground.length_map, ground.length_map]
  exact h.1

/-- An occupied natural row reads positively at two positive
coroot coordinates. -/
private theorem g2Row_pos (r : List Nat) (hr : r.length = 2) (hp : 0 < sumNat r)
    (a b : Nat) : BPair.unit < (elim.dotN (natV r) (natV [a + 1, b + 1])).norm := by
  have hcoords : ∀ i, i < 2 → 1 ≤ ground.getAt 0 [a + 1, b + 1] i := by
    intro i hi
    cases i with
    | zero => exact Nat.succ_pos a
    | succ i =>
      cases i with
      | zero => exact Nat.succ_pos b
      | succ i =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)) (Nat.not_lt_zero i)
  have hdot : 0 < ground.dotNat r [a + 1, b + 1] := Nat.lt_of_lt_of_le hp
    (ground.sumNat_le_dotNat r _ (by rw [hr]; exact Nat.le_refl 2)
      (fun i hi => hcoords i (by rw [← hr]; exact hi)))
  have h := BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_trans (elim.dotN_read _ _) (natV_dot r [a + 1, b + 1]))
  exact BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm h) (ground.unitLtNat hdot)

private theorem g2Row_neg (r : List Nat) (hr : r.length = 2) (hp : 0 < sumNat r)
    (a b : Nat) : (elim.dotN (poly.neg (natV r)) (natV [a + 1, b + 1])).norm < BPair.unit := by
  show (elim.dotN ((natV r).map BPair.swap) (natV [a + 1, b + 1])).norm < BPair.unit
  rw [elim.dotN_swapLeft, BPair.norm_swap]
  exact ground.ltB_swap (g2Row_pos r hr hp a b)

private theorem lowGo_pair_left (x y : BPair) (hx : x < BPair.unit) :
    lowGo [x, y] 0 = some 0 := by
  change (if x < BPair.unit then some 0 else lowGo [y] 1) = some 0
  rw [if_pos hx]

private theorem lowGo_pair_right (x y : BPair) (hx : BPair.unit ≤ x) (hy : y < BPair.unit) :
    lowGo [x, y] 0 = some 1 := by
  change (if x < BPair.unit then some 0 else if y < BPair.unit then some 1 else none) = some 1
  rw [if_neg (ground.leB_not_lt hx), if_pos hy]

/-- The first lower-side coordinate alternates along the six
prefixes at every positive shifted key. -/
private theorem g2DualMat_scan (a b : Nat) : ∀ j, j < 6 →
    lowGo (poly.pnorm (elim.matVec (sertables.g2DualMat j) (natV [a + 1, b + 1]))) 0 = some (j % 2)
  | 0, _ => lowGo_pair_left _ _ (g2Row_neg [1, 0] rfl (by decide) a b)
  | 1, _ => lowGo_pair_right _ _
      (ground.leB_of_lt (g2Row_pos [1, 0] rfl (by decide) a b))
      (g2Row_neg [1, 1] rfl (by decide) a b)
  | 2, _ => lowGo_pair_left _ _ (g2Row_neg [2, 3] rfl (by decide) a b)
  | 3, _ => lowGo_pair_right _ _
      (ground.leB_of_lt (g2Row_pos [2, 3] rfl (by decide) a b))
      (g2Row_neg [1, 2] rfl (by decide) a b)
  | 4, _ => lowGo_pair_left _ _ (g2Row_neg [1, 3] rfl (by decide) a b)
  | 5, _ => lowGo_pair_right _ _
      (ground.leB_of_lt (g2Row_pos [1, 3] rfl (by decide) a b))
      (g2Row_neg [0, 1] rfl (by decide) a b)
  | j + 6, h => absurd h (Nat.not_lt_of_ge (Nat.le_add_left 6 j))

private theorem g2DualMat_move (j : Nat) (hj : j < 6) (w : List BPair) (hw : w.length = 2) :
    assembly.reflF sertables.tableG2 (j % 2) (poly.pnorm (elim.matVec (sertables.g2DualMat j) w))
      = poly.pnorm (elim.matVec (sertables.g2DualMat (j + 1)) w) := by
  rw [← sertables.weylMatG2_prefix j (Nat.lt_trans hj (by decide)),
    assembly.reflF_G2_weylMat (j % 2) j (Nat.mod_lt j (by decide)) (Nat.lt_trans hj (by decide)) w hw,
    sertables.weylStepG2_prefix j hj, sertables.weylMatG2_prefix (j + 1) (Nat.succ_lt_succ hj)]

private theorem walkP_step (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (p : Bool) (i : Nat) (h : lowGo v 0 = some i) :
    walkP t (fuel + 1) v p = walkP t fuel (assembly.reflF t i v) (!p) := by
  change (match lowGo v 0 with
    | none => some (v, p)
    | some j => walkP t fuel (assembly.reflF t j v) (!p)) = _
  rw [h]

/-- The six prescribed G2 raises return the positive key at even
parity; every later scan is complete. -/
private theorem g2Dual_walk (a b extra : Nat) :
    walkP sertables.tableG2 (extra + 6)
      (poly.pnorm (elim.matVec (sertables.g2DualMat 0) (natV [a + 1, b + 1]))) false
      = some (poly.pnorm (natV [a + 1, b + 1]), false) := by
  rw [walkP_step _ (extra + 5) _ false 0 (g2DualMat_scan a b 0 (by decide)),
    g2DualMat_move 0 (by decide) _ rfl, Bool.not_false,
    walkP_step _ (extra + 4) _ true 1 (g2DualMat_scan a b 1 (by decide)),
    g2DualMat_move 1 (by decide) _ rfl, Bool.not_true,
    walkP_step _ (extra + 3) _ false 0 (g2DualMat_scan a b 2 (by decide)),
    g2DualMat_move 2 (by decide) _ rfl, Bool.not_false,
    walkP_step _ (extra + 2) _ true 1 (g2DualMat_scan a b 3 (by decide)),
    g2DualMat_move 3 (by decide) _ rfl, Bool.not_true,
    walkP_step _ (extra + 1) _ false 0 (g2DualMat_scan a b 4 (by decide)),
    g2DualMat_move 4 (by decide) _ rfl, Bool.not_false,
    walkP_step _ extra _ true 1 (g2DualMat_scan a b 5 (by decide)),
    g2DualMat_move 5 (by decide) _ rfl, Bool.not_true]
  have hstop : lowGo (poly.pnorm (elim.matVec (sertables.g2DualMat 6) (natV [a + 1, b + 1]))) 0 = none := by
    change (if (elim.dotN (natV [1, 0]) (natV [a + 1, b + 1])).norm < BPair.unit
      then some 0 else if (elim.dotN (natV [0, 1]) (natV [a + 1, b + 1])).norm < BPair.unit
      then some 1 else none) = none
    rw [if_neg (ground.leB_not_lt (ground.leB_of_lt (g2Row_pos [1, 0] rfl (by decide) a b))),
      if_neg (ground.leB_not_lt (ground.leB_of_lt (g2Row_pos [0, 1] rfl (by decide) a b)))]
  rw [walkP_stop _ extra _ false hstop]
  have he : poly.pnorm (elim.matVec (sertables.g2DualMat 6) (natV [a + 1, b + 1]))
      = poly.pnorm (natV [a + 1, b + 1]) :=
    poly.pnorm_congr _ _ rfl (elim.matVec_idMat 2 _ rfl)
  rw [he]

/-- Every G2 label is self-dual at the shifted walk
(`lem:memberdata`(ii)): six alternating reflections send the
negative shifted key to the positive shifted key. -/
theorem dualM_G2 (extra a b : Nat) : dualM sertables.tableG2 (extra + 6) [a, b] = [a, b] := by
  have hshift : poly.oneValue (shiftV sertables.tableG2 [a, b]) (natV [a + 1, b + 1]) := by
    refine poly.oneValue_trans (poly.pnorm_oneValue _) ?_
    exact ⟨BPair.oneValue_symm (BPair.ofNat_add a 1),
      BPair.oneValue_symm (BPair.ofNat_add b 1), trivial⟩
  have hstart : poly.oneValue (elim.matVec (sertables.g2DualMat 0) (natV [a + 1, b + 1]))
      (poly.neg (natV [a + 1, b + 1])) := by
    change poly.oneValue (elim.matVec (elim.matSwap (elim.idMat 2)) (natV [a + 1, b + 1])) _
    rw [elim.matVec_swapM]
    exact poly.swapMap_oneValue (elim.matVec_idMat 2 _ rfl)
  have he : poly.pnorm (poly.neg (shiftV sertables.tableG2 [a, b]))
      = poly.pnorm (elim.matVec (sertables.g2DualMat 0) (natV [a + 1, b + 1])) :=
    poly.pnorm_congr _ _ rfl
      (poly.oneValue_trans (poly.swapMap_oneValue hshift) (poly.oneValue_symm hstart))
  have hw : domWalk sertables.tableG2 (extra + 6)
      (poly.pnorm (poly.neg (shiftV sertables.tableG2 [a, b])))
      = poly.pnorm (natV [a + 1, b + 1]) := by
    show (match walkP sertables.tableG2 (extra + 6) _ false with | none => [] | some q => q.1) = _
    rw [he, g2Dual_walk a b extra]
  change ((domWalk sertables.tableG2 (extra + 6) _).map BPair.marginN).map (fun x => x - 1) = _
  rw [hw]
  change [BPair.marginN (BPair.ofNat (a + 1)).norm - 1,
    BPair.marginN (BPair.ofNat (b + 1)).norm - 1] = [a, b]
  rw [BPair.marginN_congr (BPair.norm_oneValue _), BPair.marginN_congr (BPair.norm_oneValue _),
    BPair.marginN_ofNat, BPair.marginN_ofNat, ground.addSubSelfR, ground.addSubSelfR]

/-- A predicate preserved by every image holds throughout the
orbit queue, at its accumulated and pending members. -/
private theorem orbitGo_all {α : Type} (step : α → List α)
    (known : α → List α → Bool) (P : α → Prop)
    (hstep : ∀ x, P x → ∀ y ∈ step x, P y) :
    ∀ (fuel : Nat) (acc todo : List α),
      (∀ x ∈ acc, P x) → (∀ x ∈ todo, P x) →
      ∀ x ∈ orbitGo step known fuel acc todo, P x
  | 0, acc, [], ha, _ => ha
  | 0, _, _ :: _, _, _ => fun _ h => nomatch h
  | _ + 1, acc, [], ha, _ => ha
  | fuel + 1, acc, h :: tl, ha, ht => by
    let fresh := (step h).filter (fun q => !(known q acc))
    have hf : ∀ v ∈ fresh, P v := fun v hv =>
      hstep h (ht h (List.Mem.head tl)) v
        (ground.mem_filter_of _ _ v hv).1
    change ∀ x ∈ orbitGo step known fuel (acc ++ fresh) (tl ++ fresh), P x
    refine orbitGo_all step known P hstep fuel _ _ ?_ ?_
    · intro v hv
      cases ground.mem_append_of acc fresh hv with
      | inl h => exact ha v h
      | inr h => exact hf v h
    · intro v hv
      cases ground.mem_append_of tl fresh hv with
      | inl h' => exact ht v (List.Mem.tail h h')
      | inr h' => exact hf v h'

/-- A completed orbit queue has one result at every larger step
bound, the terminal accumulated list. -/
private theorem orbitGo_more {α : Type} (step : α → List α)
    (known : α → List α → Bool) :
    ∀ (fuel extra : Nat) (acc todo : List α),
      orbitGo step known fuel acc todo ≠ [] →
      orbitGo step known (fuel + extra) acc todo = orbitGo step known fuel acc todo
  | 0, extra, acc, [], _ => by
    rw [Nat.zero_add]
    cases extra <;> rfl
  | 0, _, _, _ :: _, h => absurd rfl h
  | fuel + 1, extra, acc, [], _ => by
    rw [Nat.add_right_comm fuel 1 extra]
    rfl
  | fuel + 1, extra, acc, h :: tl, hout => by
    rw [Nat.add_right_comm fuel 1 extra]
    exact orbitGo_more step known fuel extra
      (acc ++ (step h).filter (fun q => !(known q acc)))
      (tl ++ (step h).filter (fun q => !(known q acc))) hout

/-- A projection commuting with the images and the known-key test
commutes with the orbit queue, including its refusal value. -/
private theorem orbitGo_map {α β : Type} (f : α → β)
    (stepA : α → List α) (knownA : α → List α → Bool)
    (stepB : β → List β) (knownB : β → List β → Bool)
    (hstep : ∀ x, (stepA x).map f = stepB (f x))
    (hknown : ∀ x acc, knownA x acc = knownB (f x) (acc.map f)) :
    ∀ (fuel : Nat) (acc todo : List α),
      (orbitGo stepA knownA fuel acc todo).map f
        = orbitGo stepB knownB fuel (acc.map f) (todo.map f)
  | 0, _, [] => rfl
  | 0, _, _ :: _ => rfl
  | _ + 1, _, [] => rfl
  | fuel + 1, acc, h :: tl => by
    let fresh := (stepA h).filter (fun q => !(knownA q acc))
    have hf : fresh.map f = (stepB (f h)).filter (fun q => !(knownB q (acc.map f))) := by
      rw [← hstep h, ground.filter_map]
      refine congrArg (List.map f) (ground.filter_congr _ _ (fun q => ?_) _)
      rw [hknown q acc]
    change (orbitGo stepA knownA fuel (acc ++ fresh) (tl ++ fresh)).map f
      = orbitGo stepB knownB fuel
        (acc.map f ++ (stepB (f h)).filter (fun q => !(knownB q (acc.map f))))
        (tl.map f ++ (stepB (f h)).filter (fun q => !(knownB q (acc.map f))))
    rw [orbitGo_map f stepA knownA stepB knownB hstep hknown,
      ground.map_append, ground.map_append, hf]

/-- The graded queue's key test is the ungraded projected list's
membership read. -/
private theorem memFstB_project (v : List BPair) :
    ∀ acc : List (List BPair × Bool), memFstB v acc = ground.containsB (acc.map Prod.fst) v
  | [] => rfl
  | p :: tl => by
    change (p.1 == v || memFstB v tl) = ground.containsB (p.1 :: tl.map Prod.fst) v
    by_cases he : p.1 = v
    · rw [he, ground.listEqBeq]
      exact (ground.containsB_head v (tl.map Prod.fst)).symm
    · have hb : (p.1 == v) = false :=
        ground.listBeqRefuse (fun _ _ h => ground.beqEqOf h) he
      rw [hb, Bool.false_or, ground.containsB_cons_ne (fun h => he h.symm),
        memFstB_project v tl]

/-- Every accumulated member is in a completed queue's result. -/
private theorem orbitGo_keeps {α : Type} (step : α → List α)
    (known : α → List α → Bool) :
    ∀ (fuel : Nat) (acc todo : List α),
      orbitGo step known fuel acc todo ≠ [] →
      ∀ x ∈ acc, x ∈ orbitGo step known fuel acc todo
  | 0, _, [], _, _, hx => hx
  | 0, _, _ :: _, h, _, _ => absurd rfl h
  | _ + 1, _, [], _, _, hx => hx
  | fuel + 1, acc, h :: tl, hout, x, hx =>
    orbitGo_keeps step known fuel
      (acc ++ (step h).filter (fun q => !(known q acc)))
      (tl ++ (step h).filter (fun q => !(known q acc))) hout x
      (ground.mem_append_left _ hx)

/-- At every accumulated key, either its images are accumulated
or the key is pending. Exhausting the queue closes every image. -/
private theorem orbitGo_closed {α : Type} (step : α → List α)
    (known : α → List α → Bool)
    (hknown : ∀ x acc, known x acc = true → x ∈ acc) :
    ∀ (fuel : Nat) (acc todo : List α),
      (∀ x ∈ acc, x ∈ todo ∨ ∀ y ∈ step x, y ∈ acc) →
      ∀ x ∈ orbitGo step known fuel acc todo,
        ∀ y ∈ step x, y ∈ orbitGo step known fuel acc todo
  | 0, acc, [], hacc, x, hx, y, hy => by
    cases hacc x hx with
    | inl h => exact nomatch h
    | inr h => exact h y hy
  | 0, _, _ :: _, _, _, hx, _, _ => nomatch hx
  | _ + 1, acc, [], hacc, x, hx, y, hy => by
    cases hacc x hx with
    | inl h => exact nomatch h
    | inr h => exact h y hy
  | fuel + 1, acc, h :: tl, hacc, x, hx, y, hy => by
    let fresh := (step h).filter (fun q => !(known q acc))
    have hstep : ∀ z ∈ step h, z ∈ acc ++ fresh := by
      intro z hz
      cases hk : known z acc with
      | true => exact ground.mem_append_left _ (hknown z acc hk)
      | false =>
        refine ground.mem_append_right acc (ground.mem_filter_to _ hz ?_)
        show (!known z acc) = true
        rw [hk]
        rfl
    refine orbitGo_closed step known hknown fuel (acc ++ fresh) (tl ++ fresh)
      (fun z hz => ?_) x hx y hy
    cases ground.mem_append_of acc fresh hz with
    | inr hf => exact Or.inl (ground.mem_append_right tl hf)
    | inl ha =>
      cases hacc z ha with
      | inr hc => exact Or.inr (fun w hw => ground.mem_append_left _ (hc w hw))
      | inl ht =>
        cases ht with
        | head => exact Or.inr hstep
        | tail _ htl => exact Or.inl (ground.mem_append_left fresh htl)

/-- A queue inside a distinct finite reference list completes at
the reference count. Each expansion removes one pending member
and appends its fresh members to both lists. -/
private theorem orbitGo_complete {α : Type} [DecidableEq α]
    (step : α → List α) (known : α → List α → Bool)
    (S : List α) (hS : ground.distinctList S)
    (hstep : ∀ x ∈ S, ∀ y ∈ step x, y ∈ S)
    (hknown : ∀ x acc, x ∈ acc → known x acc = true)
    (hfresh : ∀ acc, (∀ x ∈ acc, x ∈ S) → ∀ x ∈ acc,
      ground.distinctList ((step x).filter (fun q => !(known q acc)))) :
    ∀ (fuel : Nat) (acc todo : List α),
      acc ≠ [] → ground.distinctList acc → (∀ x ∈ acc, x ∈ S) →
      (∀ x ∈ todo, x ∈ acc) → S.length + todo.length ≤ fuel + acc.length →
      orbitGo step known fuel acc todo ≠ []
        ∧ ground.distinctList (orbitGo step known fuel acc todo)
  | 0, acc, [], ha, hd, _, _, _ => ⟨ha, hd⟩
  | 0, acc, x :: tl, _, hd, hsub, _, hb => by
    have hlen : acc.length ≤ S.length := ground.length_le_of_distinct_mem acc S
      (ground.distinctList_all hd) hsub hS
    rw [Nat.zero_add] at hb
    have hh : S.length + (tl.length + 1) ≤ acc.length := hb
    exact absurd (Nat.lt_of_lt_of_le
      (Nat.lt_add_of_pos_right (Nat.succ_pos tl.length)) (Nat.le_trans hh hlen))
      (Nat.lt_irrefl S.length)
  | _ + 1, acc, [], ha, hd, _, _, _ => ⟨ha, hd⟩
  | fuel + 1, acc, x :: tl, ha, hd, hsub, ht, hb => by
    let fresh := (step x).filter (fun q => !(known q acc))
    have hx : x ∈ acc := ht x (List.Mem.head tl)
    have hf : ∀ y ∈ fresh, y ∈ S := fun y hy =>
      hstep x (hsub x hx) y (ground.mem_filter_of _ _ y hy).1
    have hn : acc ++ fresh ≠ [] := by
      cases acc with
      | nil => exact absurd rfl ha
      | cons a as => exact fun h => nomatch h
    have hd' : ground.distinctList (acc ++ fresh) :=
      ground.distinctList_append_disjoint acc fresh hd (hfresh acc hsub x hx)
        (fun y hya hyf => by
          have h := (ground.mem_filter_of _ _ y hyf).2
          rw [hknown y acc hya] at h
          exact Bool.noConfusion h)
    have hs' : ∀ y ∈ acc ++ fresh, y ∈ S := by
      intro y hy
      cases ground.mem_append_of acc fresh hy with
      | inl h => exact hsub y h
      | inr h => exact hf y h
    have ht' : ∀ y ∈ tl ++ fresh, y ∈ acc ++ fresh := by
      intro y hy
      cases ground.mem_append_of tl fresh hy with
      | inl h => exact ground.mem_append_left fresh (ht y (List.Mem.tail x h))
      | inr h => exact ground.mem_append_right acc h
    have hb' : S.length + (tl ++ fresh).length ≤ fuel + (acc ++ fresh).length := by
      change S.length + (tl.length + 1) ≤ (fuel + 1) + acc.length at hb
      rw [← Nat.add_assoc, Nat.add_right_comm fuel 1 acc.length] at hb
      rw [ground.length_append, ground.length_append,
        ← Nat.add_assoc, ← Nat.add_assoc]
      exact Nat.add_le_add_right (Nat.le_of_succ_le_succ hb) fresh.length
    exact orbitGo_complete step known S hS hstep hknown hfresh fuel
      (acc ++ fresh) (tl ++ fresh) hn hd' hs' ht' hb'

/-- The reflection orbit is a family of canonical coroot lists
(`lem:memberdata`(i)), at every stated closure count. -/
theorem orbitSet_shape (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (hv : v.length = t.rank) : memberchar.mShapeRead t (orbitSet t fuel v) := by
  have hs : memberchar.mShapeRead t [poly.pnorm v] := by
    intro w hw
    rw [ground.eq_of_mem_single hw, poly.pnorm_length]
    exact ⟨hv, poly.pnorm_pnorm v⟩
  refine orbitGo_all _ _
    (fun w : List BPair => w.length = t.rank ∧ poly.pnorm w = w) ?_ fuel _ _ hs hs
  intro w hw y hy
  obtain ⟨i, _, hiy⟩ := ground.mem_map_of _ _ y hy
  rw [← hiy]
  exact assembly.reflF_shape t i w hw.1

/-- The graded Weyl family is a family of canonical coroot lists
(`con:sertables`; `lem:memberdata`), at every stated closure count. -/
theorem orbitFam_shape (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (hv : v.length = t.rank) : sertables.wShapeRead t (orbitFam t fuel v) := by
  have hs : sertables.wShapeRead t [(poly.pnorm v, false)] := by
    intro w hw
    rw [ground.eq_of_mem_single hw]
    exact ⟨(poly.pnorm_length v).trans hv, poly.pnorm_pnorm v⟩
  refine orbitGo_all _ _
    (fun w : List BPair × Bool => w.1.length = t.rank ∧ poly.pnorm w.1 = w.1)
    ?_ fuel _ _ hs hs
  intro w hw y hy
  obtain ⟨i, _, hiy⟩ := ground.mem_map_of _ _ y hy
  rw [← hiy]
  exact assembly.reflF_shape t i w.1 hw.1

/-- Every reflected member belongs to the produced orbit
(`con:sertables`' reflection closure; `lem:memberdata`(i)). -/
theorem orbitSet_closed (t : gentable.Table) (fuel : Nat) (v w : List BPair)
    (hw : w ∈ orbitSet t fuel v) (i : Nat) (hi : i < t.rank) :
    assembly.reflF t i w ∈ orbitSet t fuel v := by
  refine orbitGo_closed _ _ (fun _ _ h => ground.mem_of_containsB h) fuel
    [poly.pnorm v] [poly.pnorm v] (fun _ h => Or.inl h) w hw _ ?_
  exact ground.mem_map_to _
    (ground.mem_of_countOf_pos i (List.range t.rank) (by
      rw [ground.countOf_range, if_pos hi]
      exact Nat.succ_pos 0))

/-- The orbit lies in every reflection-closed family containing
its seed (`con:sertables`' orbit at the simple letters). -/
theorem orbitSet_least (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (S : List (List BPair)) (hv : poly.pnorm v ∈ S)
    (hclose : ∀ w ∈ S, ∀ i, i < t.rank → assembly.reflF t i w ∈ S) :
    ∀ w ∈ orbitSet t fuel v, w ∈ S := by
  refine orbitGo_all _ _ (fun w => w ∈ S) ?_ fuel _ _ ?_ ?_
  · intro w hw y hy
    obtain ⟨i, hi, hiy⟩ := ground.mem_map_of _ _ y hy
    rw [← hiy]
    exact hclose w hw i (ground.ltOfMem (ground.countOf_pos_of_mem hi))
  · intro w hw
    rw [ground.eq_of_mem_single hw]
    exact hv
  · intro w hw
    rw [ground.eq_of_mem_single hw]
    exact hv

/-- The graded orbit's keys are exactly the ungraded orbit in
their enumeration order, at every step bound. -/
theorem orbitFam_keys (t : gentable.Table) (fuel : Nat) (v : List BPair) :
    (orbitFam t fuel v).map Prod.fst = orbitSet t fuel v := by
  refine orbitGo_map Prod.fst _ _ _ _ ?_ ?_ fuel _ _
  · intro x
    rw [ground.map_map]
  · intro x acc
    exact memFstB_project x.1 acc

/-- The reflected images off their input key are distinct where
two letters have distinct images off that key. -/
private theorem orbitFresh_distinct (t : gentable.Table) (S : List (List BPair))
    (hsep : ∀ w ∈ S, ∀ i, i < t.rank → ∀ j, j < t.rank →
      assembly.reflF t i w = assembly.reflF t j w →
        i = j ∨ assembly.reflF t i w = w)
    (acc : List (List BPair)) (hsub : ∀ x ∈ acc, x ∈ S)
    (w : List BPair) (hw : w ∈ acc) : ground.distinctList
      (((List.range t.rank).map (fun i => assembly.reflF t i w)).filter
        (fun q => !(ground.containsB acc q))) := by
  intro q hq
  obtain ⟨hm, hnew⟩ := ground.mem_filter_of _ _ q hq
  obtain ⟨i, hi, hiq⟩ := ground.mem_map_of _ _ q hm
  have hqw : q ≠ w := by
    intro he
    rw [he, ground.containsB_of_mem hw] at hnew
    exact Bool.noConfusion hnew
  rw [ground.countOf_filter, if_pos hnew, ← hiq,
    ground.countOf_map_inj (fun j => assembly.reflF t j w) i
      (List.range t.rank) (fun j hj hji => by
        cases hsep w (hsub w hw) j (ground.ltOfMem hj) i
            (ground.ltOfMem (ground.countOf_pos_of_mem hi)) hji with
        | inl he => exact he
        | inr he => exact absurd (hiq.symm.trans (hji.symm.trans he)) hqw)]
  exact ground.distinctList_range t.rank i hi

/-- A reference orbit bounds the produced queue's step count
(`con:sertables`' finite Weyl list). The reference is distinct and
reflection-closed, and two simple letters have distinct images
off the input key. -/
theorem orbitSet_complete (t : gentable.Table) (S : List (List BPair))
    (hS : ground.distinctList S)
    (hclose : ∀ w ∈ S, ∀ i, i < t.rank → assembly.reflF t i w ∈ S)
    (hsep : ∀ w ∈ S, ∀ i, i < t.rank → ∀ j, j < t.rank →
      assembly.reflF t i w = assembly.reflF t j w →
        i = j ∨ assembly.reflF t i w = w)
    (fuel : Nat) (hfuel : S.length ≤ fuel) (v : List BPair) (hv : poly.pnorm v ∈ S) :
    orbitSet t fuel v ≠ [] ∧ ground.distinctList (orbitSet t fuel v) := by
  refine orbitGo_complete _ _ S hS ?_ (fun _ _ h => ground.containsB_of_mem h)
    (orbitFresh_distinct t S hsep) fuel [poly.pnorm v] [poly.pnorm v]
    (fun h => nomatch h) ?_ ?_ (fun _ h => h) (Nat.succ_le_succ hfuel)
  · intro w hw y hy
    obtain ⟨i, hi, hiy⟩ := ground.mem_map_of _ _ y hy
    rw [← hiy]
    exact hclose w hw i (ground.ltOfMem (ground.countOf_pos_of_mem hi))
  · intro w hw
    rw [ground.eq_of_mem_single hw, ground.countOf_head]
    exact Nat.le_refl 1
  · intro w hw
    rw [ground.eq_of_mem_single hw]
    exact hv

/-- The graded queue completes at the reference orbit's count,
its key list the ungraded queue's at every step. -/
theorem orbitFam_complete (t : gentable.Table) (S : List (List BPair))
    (hS : ground.distinctList S)
    (hclose : ∀ w ∈ S, ∀ i, i < t.rank → assembly.reflF t i w ∈ S)
    (hsep : ∀ w ∈ S, ∀ i, i < t.rank → ∀ j, j < t.rank →
      assembly.reflF t i w = assembly.reflF t j w →
        i = j ∨ assembly.reflF t i w = w)
    (fuel : Nat) (hfuel : S.length ≤ fuel) (v : List BPair) (hv : poly.pnorm v ∈ S) :
    orbitFam t fuel v ≠ [] ∧ ground.distinctList ((orbitFam t fuel v).map Prod.fst) := by
  have h := orbitSet_complete t S hS hclose hsep fuel hfuel v hv
  refine ⟨?_, ?_⟩
  · intro he
    have hk := orbitFam_keys t fuel v
    rw [he] at hk
    exact h.1 hk.symm
  · rw [orbitFam_keys]
    exact h.2

/-- A finite displayed family closes both queues at any bound
on its distinct keys. The displayed family itself may repeat keys. -/
theorem orbit_complete_family (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W)
    (hclose : ∀ w ∈ W, ∀ i, i < t.rank → (assembly.reflF t i w.1, !w.2) ∈ W)
    (hsep : ∀ w, w.length = t.rank → poly.pnorm w = w →
      ∀ i, i < t.rank → ∀ j, j < t.rank →
        assembly.reflF t i w = assembly.reflF t j w → i = j ∨ assembly.reflF t i w = w)
    (fuel : Nat) (hfuel : (ground.dedupF (W.map Prod.fst)).length ≤ fuel)
    (v : List BPair) (hv : (poly.pnorm v, false) ∈ W) :
    (orbitSet t fuel v ≠ [] ∧ ground.distinctList (orbitSet t fuel v))
      ∧ (orbitFam t fuel v ≠ [] ∧ ground.distinctList ((orbitFam t fuel v).map Prod.fst)) := by
  let S := ground.dedupF (W.map Prod.fst)
  have hS : ground.distinctList S := fun w _ => ground.countOf_dedupF_le w (W.map Prod.fst)
  have hclosed : ∀ w ∈ S, ∀ i, i < t.rank → assembly.reflF t i w ∈ S := by
    intro w hw i hi
    obtain ⟨p, hp, he⟩ := ground.mem_map_of Prod.fst W w (ground.mem_of_dedupF hw)
    rw [← he]
    exact ground.mem_dedupF (ground.mem_map_to Prod.fst (hclose p hp i hi))
  have hseparated : ∀ w ∈ S, ∀ i, i < t.rank → ∀ j, j < t.rank →
      assembly.reflF t i w = assembly.reflF t j w → i = j ∨ assembly.reflF t i w = w := by
    intro w hw
    obtain ⟨p, hp, he⟩ := ground.mem_map_of Prod.fst W w (ground.mem_of_dedupF hw)
    rw [← he]
    exact hsep p.1 (hshape p hp).1 (hshape p hp).2
  have hseed : poly.pnorm v ∈ S := ground.mem_dedupF (ground.mem_map_to Prod.fst hv)
  exact ⟨orbitSet_complete t S hS hclosed hseparated fuel hfuel v hseed,
    orbitFam_complete t S hS hclosed hseparated fuel hfuel v hseed⟩

/-- The produced orbit's keys are distinct at every step bound.
A completed queue agrees with its result at the reference count,
and the refusal value is distinct outright. -/
theorem orbitSet_distinct (t : gentable.Table) (S : List (List BPair))
    (hS : ground.distinctList S)
    (hclose : ∀ w ∈ S, ∀ i, i < t.rank → assembly.reflF t i w ∈ S)
    (hsep : ∀ w ∈ S, ∀ i, i < t.rank → ∀ j, j < t.rank →
      assembly.reflF t i w = assembly.reflF t j w →
        i = j ∨ assembly.reflF t i w = w)
    (fuel : Nat) (v : List BPair) (hv : poly.pnorm v ∈ S) :
    ground.distinctList (orbitSet t fuel v) := by
  by_cases hc : orbitSet t fuel v = []
  · rw [hc]
    exact fun _ h => nomatch h
  · have hd := (orbitSet_complete t S hS hclose hsep (fuel + S.length)
      (Nat.le_add_left _ _) v hv).2
    have he : orbitSet t (fuel + S.length) v = orbitSet t fuel v :=
      orbitGo_more _ _ fuel S.length _ _ hc
    rw [he] at hd
    exact hd

/-- A distinct computed orbit has reflection-invariant counts
at every occupied member, by its closure at the simple letters. -/
theorem orbitSet_sym_of_distinct (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (hv : v.length = t.rank) (hd : ground.distinctList (orbitSet t fuel v)) :
    memberchar.symRead t (orbitSet t fuel v) := by
  intro w hw i hi
  have hm := orbitSet_closed t fuel v w hw i hi
  rw [assembly.reflF_eq t i w (orbitSet_shape t fuel v hv w hw).1] at hm
  rw [ground.countOf_distinct_one hd hm, ground.countOf_distinct_one hd hw]

/-- Every produced orbit member and its reflected key have count
one (`lem:strings`); a refused orbit reads the vacant family. -/
theorem orbitSet_sym (t : gentable.Table) (S : List (List BPair))
    (hS : ground.distinctList S)
    (hclose : ∀ w ∈ S, ∀ i, i < t.rank → assembly.reflF t i w ∈ S)
    (hsep : ∀ w ∈ S, ∀ i, i < t.rank → ∀ j, j < t.rank →
      assembly.reflF t i w = assembly.reflF t j w →
        i = j ∨ assembly.reflF t i w = w)
    (fuel : Nat) (v : List BPair)
    (hv : poly.pnorm v ∈ S) (hwidth : v.length = t.rank) :
    memberchar.symRead t (orbitSet t fuel v) := by
  exact orbitSet_sym_of_distinct t fuel v hwidth (orbitSet_distinct t S hS hclose hsep fuel v hv)

/-- A completed orbit contains its seed's canonical key. -/
theorem orbitSet_seed (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (h : orbitSet t fuel v ≠ []) : poly.pnorm v ∈ orbitSet t fuel v :=
  orbitGo_keeps _ _ fuel _ _ h _ (List.Mem.head [])

/-- A closed displayed family with one dominant key identifies
the nonnegative filter of the actual completed orbit. -/
theorem orbitSet_dominant_filter (t : gentable.Table) (fuel : Nat) (m : List Nat)
    (hm : m.length = t.rank)
    (hcomplete : orbitSet t fuel (natV m) ≠ [] ∧ ground.distinctList (orbitSet t fuel (natV m)))
    (W : List (List BPair × Bool))
    (hseed : (poly.pnorm (natV m), false) ∈ W)
    (hclose : ∀ p ∈ W, ∀ i, i < t.rank → (assembly.reflF t i p.1, !p.2) ∈ W)
    (hunique : ∀ p ∈ W, (∀ i, i < t.rank → BPair.unit ≤ ground.getAt BPair.unit p.1 i) →
      poly.pnorm p.1 = natV m) :
    (orbitSet t fuel (natV m)).filter (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV m] := by
  have hv : (natV m).length = t.rank := (ground.length_map BPair.ofNat m).trans hm
  have hsub := orbitSet_least t fuel (natV m) (W.map Prod.fst)
    (ground.mem_map_to Prod.fst hseed) (fun w hw i hi => by
      obtain ⟨p, hp, he⟩ := ground.mem_map_of Prod.fst W w hw
      rw [← he]
      exact ground.mem_map_to Prod.fst (hclose p hp i hi))
  have hseed' := orbitSet_seed t fuel (natV m) hcomplete.1
  rw [natV_pnorm] at hseed'
  have hkeep : (natV m).all (fun x => decide (BPair.unit ≤ x)) = true := by
    change (m.map BPair.ofNat).all _ = true
    rw [ground.all_map]
    exact ground.all_of_pointwise _ m (fun x => decide_eq_true (ground.unitLeOfNat x))
  have hpin : ∀ w ∈ orbitSet t fuel (natV m),
      w.all (fun x => decide (BPair.unit ≤ x)) = true → w = natV m := by
    intro w hw hp
    have hsh := orbitSet_shape t fuel (natV m) hv w hw
    obtain ⟨p, hpW, he⟩ := ground.mem_map_of Prod.fst W w (hsub w hw)
    have h := hunique p hpW (fun i hi => by
      rw [he]
      exact of_decide_eq_true (ground.all_getAt BPair.unit w hp i (by rw [hsh.1]; exact hi)))
    rw [he, hsh.2] at h
    exact h
  apply ground.single_of_counts
  intro w
  by_cases he : w = natV m
  · rw [if_pos he, he, ground.countOf_filter, hkeep]
    exact ground.countOf_distinct_one hcomplete.2 hseed'
  · rw [if_neg he]
    apply ground.countOf_zero_of_not_mem
    intro hw
    have h := ground.mem_filter_of _ _ w hw
    exact he (hpin w h.1 h.2)

/-- The zero content's actual reflection orbit is a singleton
as soon as its one queue entry can be processed. -/
theorem orbitSet_unit (t : gentable.Table) (fuel : Nat) :
    orbitSet t (fuel + 1) (List.replicate t.rank BPair.unit) = [List.replicate t.rank BPair.unit] := by
  let z := List.replicate t.rank BPair.unit
  have hz : poly.pnorm z = z := by
    change (List.replicate t.rank BPair.unit).map BPair.norm = _
    rw [ground.map_replicate]
    rfl
  have hl : z.length = t.rank := ground.length_replicate _ _
  have hfix (i : Nat) (hi : i < t.rank) : assembly.reflF t i z = z := by
    rw [assembly.reflF_eq t i z hl]
    apply assembly.reflAt_fix t i hi z hl hz
    rw [ground.getAt_replicate_self]
    exact BPair.oneValue_refl _
  have hd : ground.distinctList [z] := by
    intro w hw
    rw [ground.eq_of_mem_single hw, ground.countOf_head]
    exact Nat.le_refl 1
  have hclose : ∀ w ∈ [z], ∀ i, i < t.rank → assembly.reflF t i w ∈ [z] := by
    intro w hw i hi
    rw [ground.eq_of_mem_single hw, hfix i hi]
    exact List.Mem.head _
  have hs : poly.pnorm z ∈ [z] := by rw [hz]; exact List.Mem.head _
  have hcomplete := orbitSet_complete t [z] hd hclose
    (fun w hw i hi _ _ _ => Or.inr (by rw [ground.eq_of_mem_single hw]; exact hfix i hi))
    (fuel + 1) (Nat.succ_le_succ (Nat.zero_le fuel)) z hs
  have hsub := orbitSet_least t (fuel + 1) z [z] hs hclose
  have hseed := orbitSet_seed t (fuel + 1) z hcomplete.1
  rw [hz] at hseed
  apply ground.single_of_counts
  intro w
  by_cases he : w = z
  · rw [if_pos he, he]
    exact ground.countOf_distinct_one hcomplete.2 hseed
  · rw [if_neg he]
    exact ground.countOf_zero_of_not_mem (fun hw => he (ground.eq_of_mem_single (hsub w hw)))

/-- A completed graded orbit contains its even seed. -/
theorem orbitFam_seed (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (h : orbitFam t fuel v ≠ []) : (poly.pnorm v, false) ∈ orbitFam t fuel v :=
  orbitGo_keeps _ _ fuel _ _ h _ (List.Mem.head [])

/-- A completed reflection orbit is fixed by a larger step bound. -/
theorem orbitSet_more (t : gentable.Table) (fuel extra : Nat) (v : List BPair)
    (h : orbitSet t fuel v ≠ []) : orbitSet t (fuel + extra) v = orbitSet t fuel v :=
  orbitGo_more _ _ fuel extra _ _ h

/-- A completed graded orbit is fixed by a larger step bound. -/
theorem orbitFam_more (t : gentable.Table) (fuel extra : Nat) (v : List BPair)
    (h : orbitFam t fuel v ≠ []) : orbitFam t (fuel + extra) v = orbitFam t fuel v :=
  orbitGo_more _ _ fuel extra _ _ h

/-- A reference Weyl family's closure read contains every
reflection image with its flipped parity. -/
private theorem orbitFam_step (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W) (hclose : assembly.wCloseRead t W)
    (p : List BPair × Bool) (hp : p ∈ W) (i : Nat) (hi : i < t.rank) :
    (assembly.reflF t i p.1, !p.2) ∈ W := by
  rw [assembly.reflF_eq t i p.1 (hshape p hp).1]
  refine ground.mem_of_countOf_pos _ W ?_
  rw [hclose p hp i hi]
  exact ground.countOf_pos_of_mem hp

/-- The graded orbit is contained in every closed Weyl family at
its even seed (`con:sertables`' reflection grading). -/
theorem orbitFam_sub (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W) (hclose : assembly.wCloseRead t W)
    (fuel : Nat) (v : List BPair) (hv : (poly.pnorm v, false) ∈ W) :
    ∀ p ∈ orbitFam t fuel v, p ∈ W := by
  refine orbitGo_all _ _ (fun p => p ∈ W) ?_ fuel _ _ ?_ ?_
  · intro p hp q hq
    obtain ⟨i, hi, hiq⟩ := ground.mem_map_of _ _ q hq
    rw [← hiq]
    exact orbitFam_step t W hshape hclose p hp i
      (ground.ltOfMem (ground.countOf_pos_of_mem hi))
  · intro p hp
    rw [ground.eq_of_mem_single hp]
    exact hv
  · intro p hp
    rw [ground.eq_of_mem_single hp]
    exact hv

/-- The produced graded family satisfies the reflection-count
read at every step bound (`con:sertables`).
Distinct reference keys determine parity at every encountered key,
and the completed key queue lists each image once. -/
theorem orbitFam_close (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W) (hclose : assembly.wCloseRead t W)
    (hkeys : ground.distinctList (W.map Prod.fst))
    (hsep : ∀ w ∈ W.map Prod.fst, ∀ i, i < t.rank → ∀ j, j < t.rank →
      assembly.reflF t i w = assembly.reflF t j w →
        i = j ∨ assembly.reflF t i w = w)
    (fuel : Nat) (v : List BPair)
    (hv : (poly.pnorm v, false) ∈ W) : assembly.wCloseRead t (orbitFam t fuel v) := by
  have hkeyClose : ∀ w ∈ W.map Prod.fst, ∀ i, i < t.rank →
      assembly.reflF t i w ∈ W.map Prod.fst := by
    intro w hw i hi
    obtain ⟨p, hp, hpw⟩ := ground.mem_map_of Prod.fst W w hw
    rw [← hpw]
    exact ground.mem_map_to Prod.fst (orbitFam_step t W hshape hclose p hp i hi)
  have hd : ground.distinctList ((orbitFam t fuel v).map Prod.fst) := by
    rw [orbitFam_keys]
    exact orbitSet_distinct t (W.map Prod.fst) hkeys hkeyClose hsep fuel v
      (ground.mem_map_to Prod.fst hv)
  have hsub := orbitFam_sub t W hshape hclose fuel v hv
  intro p hp i hi
  have hpW := hsub p hp
  have href := orbitFam_step t W hshape hclose p hpW i hi
  have hkey : assembly.reflF t i p.1 ∈ (orbitFam t fuel v).map Prod.fst := by
    rw [orbitFam_keys]
    apply orbitSet_closed t fuel v p.1 ?_ i hi
    rw [← orbitFam_keys]
    exact ground.mem_map_to Prod.fst hp
  obtain ⟨q, hq, hqkey⟩ := ground.mem_map_of Prod.fst _ _ hkey
  have he : q = (assembly.reflF t i p.1, !p.2) :=
    ground.map_inj_distinct Prod.fst W hkeys q _ (hsub q hq) href hqkey
  rw [he, assembly.reflF_eq t i p.1 (hshape p hpW).1] at hq
  rw [ground.countOf_distinct_map Prod.fst _ hd _ hq, ground.countOf_distinct_map Prod.fst _ hd p hp]

/-- A key already accepted by a monotone known-key test gains no
copies during a completed queue. -/
private theorem orbitGo_count {α : Type} [DecidableEq α]
    (step : α → List α) (known : α → List α → Bool)
    (hmono : ∀ q acc more, known q acc = true → known q (acc ++ more) = true) :
    ∀ (fuel : Nat) (acc todo : List α) (q : α),
      orbitGo step known fuel acc todo ≠ [] → known q acc = true →
      ground.countOf q (orbitGo step known fuel acc todo) = ground.countOf q acc
  | 0, _, [], _, _, _ => rfl
  | 0, _, _ :: _, _, h, _ => absurd rfl h
  | _ + 1, _, [], _, _, _ => rfl
  | fuel + 1, acc, h :: tl, q, hout, hknown => by
    let fresh := (step h).filter (fun x => !(known x acc))
    have hz : ground.countOf q fresh = 0 := by
      rw [ground.countOf_filter, hknown]
      rfl
    change ground.countOf q (orbitGo step known fuel (acc ++ fresh) (tl ++ fresh)) = _
    rw [orbitGo_count step known hmono fuel _ _ q hout (hmono q acc fresh hknown),
      ground.countOf_append, hz, Nat.add_zero]

/-- At a completed graded orbit, the seed is listed once even and
has vacant odd count (`con:sertables`): the seed's key is known at
every expansion, on either parity. -/
theorem orbitFam_top (t : gentable.Table) (fuel : Nat) (v : List BPair)
    (hc : orbitFam t fuel v ≠ []) :
    assembly.wTopAt (orbitFam t fuel v) (poly.pnorm v) := by
  have hmono : ∀ (q : List BPair × Bool) acc more,
      memFstB q.1 acc = true → memFstB q.1 (acc ++ more) = true := by
    intro q acc more h
    rw [memFstB_project] at h
    rw [memFstB_project, ground.map_append]
    exact ground.containsB_of_mem
      (ground.mem_append_left _ (ground.mem_of_containsB h))
  have hknown : memFstB (poly.pnorm v) [(poly.pnorm v, false)] = true := by
    change ((poly.pnorm v == poly.pnorm v) || false) = true
    rw [ground.listEqBeq]
    rfl
  have hcount : ∀ b : Bool,
      ground.countOf (poly.pnorm v, b) (orbitFam t fuel v)
        = ground.countOf (poly.pnorm v, b) [(poly.pnorm v, false)] := fun b =>
    orbitGo_count _ _ hmono fuel _ _ (poly.pnorm v, b) hc hknown
  refine ⟨?_, ?_⟩
  · rw [hcount false, ground.countOf_head]
    rfl
  · rw [hcount true, ground.countOf_head_ne (fun he =>
      Bool.noConfusion (show true = false from congrArg Prod.snd he))]
    rfl

/-- At a regular displayed reference, the completed queue has
the reference's shape and graded closure, and its seed counts
once on the even side and at the vacant count on the odd side. -/
theorem orbitFam_reads_family (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W) (hclose : assembly.wCloseRead t W)
    (hkeys : ground.distinctList (W.map Prod.fst))
    (hsep : ∀ w, w.length = t.rank → poly.pnorm w = w →
      ∀ i, i < t.rank → ∀ j, j < t.rank →
        assembly.reflF t i w = assembly.reflF t j w → i = j ∨ assembly.reflF t i w = w)
    (fuel : Nat) (hfuel : (ground.dedupF (W.map Prod.fst)).length ≤ fuel)
    (v : List BPair) (hv : (poly.pnorm v, false) ∈ W) :
    sertables.wShapeRead t (orbitFam t fuel v)
      ∧ assembly.wCloseRead t (orbitFam t fuel v)
      ∧ assembly.wTopAt (orbitFam t fuel v) (poly.pnorm v) := by
  have hmember : ∀ w ∈ W, ∀ i, i < t.rank → (assembly.reflF t i w.1, !w.2) ∈ W :=
    orbitFam_step t W hshape hclose
  have hc := orbit_complete_family t W hshape hmember hsep fuel hfuel v hv
  refine ⟨orbitFam_shape t fuel v ((poly.pnorm_length v).symm.trans (hshape _ hv).1),
    orbitFam_close t W hshape hclose hkeys ?_ fuel v hv, orbitFam_top t fuel v hc.2.1⟩
  intro w hw
  obtain ⟨p, hp, he⟩ := ground.mem_map_of Prod.fst W w hw
  rw [← he]
  exact hsep p.1 (hshape p hp).1 (hshape p hp).2

/-- The descending key sort preserves every member's count. -/
private theorem countOf_sortDesc (key : List Nat → Nat) (x : List Nat) :
    ∀ l : List (List Nat), ground.countOf x (sortDesc key l) = ground.countOf x l
  | [] => rfl
  | m :: tl => by
    show ground.countOf x (ground.insertKeyDesc key m (sortDesc key tl)) = _
    rw [ground.countOf_insertKeyDesc key m x, ground.countOf_cons,
      countOf_sortDesc key x tl, ground.countOf_cons x m tl]

/-- The actual insertion sort orders rho keys weakly downward;
labels of equal height keep separate entries. -/
private theorem sortDesc_order (key : List Nat → Nat) : ∀ l : List (List Nat),
    ground.keysInOrder (fun a b => decide (key b ≤ key a))
      ((sortDesc key l).map (fun m => (m, ()))) = true
  | [] => rfl
  | m :: tl => ground.insertKeyDesc_order key m (sortDesc key tl) (sortDesc_order key tl)

/-- The descending recursion reconstructs stated counts when
its non-top step reads those counts from the higher keys. The
processed prefix and the unprocessed suffix cover the occupied
labels, including every dependency of a current step. -/
private theorem famGo_reconstruct (t : gentable.Table) (G : elim.Mat)
    (fuel : Nat) (top : List Nat) (rdTop : Nat) (allKeys : List (List Nat))
    (value : List Nat → Nat) (htop : value top = 1)
    (hstep : ∀ m ∈ allKeys, m ≠ top → ∀ acc : List (List Nat × Nat),
      (∀ q, rdKey t G m < rdKey t G q → lookupN q acc = value q) →
      let den := BPair.marginN (BPair.norm (formC G (shiftV t top) (shiftV t top)
        + (formC G (shiftV t m) (shiftV t m)).swap))
      ∃ n, numAt t G fuel acc rdTop m = some n ∧ 0 < den
        ∧ n.norm.marginN % den = 0 ∧ n.norm.marginN / den = value m) :
    ∀ (ks done : List (List Nat)),
    (∀ m ∈ ks, m ∈ allKeys) →
    ground.keysInOrder (fun a b => decide (rdKey t G b ≤ rdKey t G a))
      (ks.map (fun m => (m, ()))) = true →
    (∀ q, 0 < value q → q ∈ done ++ ks) →
    famGo t G fuel top rdTop ks (done.map (fun m => (m, value m)))
      = (done ++ ks).map (fun m => (m, value m))
  | [], done, _, _, _ => by
    change done.map (fun m => (m, value m)) = _
    rw [ground.append_nil]
  | m :: ks, done, hkeys, hord, hcover => by
    let acc := done.map (fun q => (q, value q))
    have hacc : ∀ q, rdKey t G m < rdKey t G q → lookupN q acc = value q := by
      intro q hq
      rw [lookupN_map]
      by_cases hc : ground.countOf q done = 0
      · rw [if_pos hc]
        cases Nat.eq_zero_or_pos (value q) with
        | inl hz => exact hz.symm
        | inr hp =>
          cases ground.mem_append_of done (m :: ks) (hcover q hp) with
          | inl hd =>
            have hx := ground.countOf_pos_of_mem hd
            rw [hc] at hx
            exact absurd hx (Nat.lt_irrefl 0)
          | inr hs =>
            have hall := ground.ltAll_of_sorted
              (fun a b => decide (rdKey t G b ≤ rdKey t G a))
              (fun _ _ _ hab hbc => decide_eq_true
                (Nat.le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab)))
              m (m, ()) (ks.map (fun q => (q, ()))) hord (decide_eq_true (Nat.le_refl _))
            have hle : rdKey t G q ≤ rdKey t G m := of_decide_eq_true
              (ground.all_of_mem _ _ hall (q, ()) (ground.mem_map_to (fun q => (q, ())) hs))
            exact absurd (Nat.lt_of_lt_of_le hq hle) (Nat.lt_irrefl _)
      · rw [if_neg hc]
    have hnxt := famGo_reconstruct t G fuel top rdTop allKeys value htop hstep ks (done ++ [m])
      (fun q hq => hkeys q (List.Mem.tail m hq))
      (ground.sorted_tail _ (m, ()) _ hord)
      (fun q hq => by rw [ground.append_assoc]; exact hcover q hq)
    rw [ground.map_append, ground.append_assoc] at hnxt
    change famGo t G fuel top rdTop ks (acc ++ [(m, value m)])
      = (done ++ m :: ks).map (fun q => (q, value q)) at hnxt
    change (if m == top then famGo t G fuel top rdTop ks (acc ++ [(m, 1)]) else _) = _
    by_cases he : m = top
    · rw [if_pos (by rw [he]; exact ground.listEqBeq top)]
      have hv : value m = 1 := by rw [he]; exact htop
      rw [← hv]
      exact hnxt
    · rw [if_neg (fun h => he (ground.listBeqEq h))]
      obtain ⟨n, hn, hd, hr, hv⟩ := hstep m (hkeys m (List.Mem.head ks)) he acc hacc
      let den := BPair.marginN (BPair.norm (formC G (shiftV t top) (shiftV t top)
        + (formC G (shiftV t m) (shiftV t m)).swap))
      change (if den == 0 then [] else _) = _
      rw [if_neg (fun h => Nat.ne_of_gt hd (ground.beqEqOf h)), hn]
      change (if n.norm.marginN % den == 0 then
        famGo t G fuel top rdTop ks (acc ++ [(m, n.norm.marginN / den)]) else []) = _
      rw [if_pos (ground.eqBeqOf hr), hv]
      exact hnxt

/-- The actual dominant solve is its sorted key list at the
supported family's counts; those keys cover every positive
dominant count. -/
private theorem domFam_counts (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F) (hsp : sertables.simplePosRead t F)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hrsq : sertables.reflSquareRead t)
    (A : List (List Nat)) (hG : F.gram = A.map natV)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (lam : List Nat) (hlam : lam.length = t.rank)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hmsh : memberchar.mShapeRead t L) (hsym : memberchar.symRead t L)
    (wits : List (List Nat)) (hsupp : memberchar.supportRead t L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV t, false) ∈ W)
    (hrec : memberchar.recRead t F W L (poly.pnorm (natV lam))) :
    let ks := sortDesc (rdKey t F.gram) (domKeys t F.gram lam)
    domFam t F.gram fuel lam = ks.map (fun m => (m, ground.countOf (natV m) L))
      ∧ ∀ m, 0 < ground.countOf (natV m) L → m ∈ ks := by
  let ks := sortDesc (rdKey t F.gram) (domKeys t F.gram lam)
  have hcover : ∀ m, 0 < ground.countOf (natV m) L → m ∈ ks := by
    intro m hm
    have hl : m.length = t.rank := (ground.length_map BPair.ofNat m).symm.trans
      (hmsh _ (ground.mem_of_countOf_pos _ _ hm)).1
    have hdom := lamRead_natV t m hl
    rw [natV_pnorm] at hdom
    have hkey := domKeys_support t F hshape hsp hrd A hG hrows hsq hlead hdet lam hlam
      L wits hsupp (natV m) hdom hm
    rw [natsOf_natV] at hkey
    apply ground.mem_of_countOf_pos
    rw [countOf_sortDesc]
    exact ground.countOf_pos_of_mem hkey
  refine ⟨?_, hcover⟩
  have hp (m : List Nat) : BPair.unit ≤ sertables.dotB F (natV m) (sertables.rhoV t) := by
    change BPair.unit ≤ sertables.dotG F.gram (natV m) (sertables.rhoV t)
    rw [hG]
    exact rhoDot_natV_upper t A m
  apply famGo_reconstruct t F.gram fuel lam (rdKey t F.gram lam) (domKeys t F.gram lam)
    (fun m => ground.countOf (natV m) L) htop ?_ ks [] ?_ (sortDesc_order _ _) hcover
  · intro m hm hne acc hacc
    apply numAt_rec_count t F hshape hgram hgsym hsp hpsq hpi hrd hrsq hsq hlead hdet
      fuel hwalk lam hlam m hm hne W L hmsh hsym wits hsupp hseed hrec (hp lam) (hp m) acc
    intro w hw hlt
    have he := hacc (natsOf w) hlt
    rw [natV_natsOf_eq w hw.2.1 (fun i hi => hw.2.2 i (by rw [← hw.1]; exact hi))] at he
    exact he
  · intro m hm
    apply ground.mem_of_countOf_pos
    have h := ground.countOf_pos_of_mem hm
    rw [countOf_sortDesc] at h
    exact h

/-- Every natural coroot label's actual dominant multiplicity
is the supported reflection-invariant family's count, including
zero counts and labels outside the dominant enumeration. -/
theorem domFam_lookup (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F) (hsp : sertables.simplePosRead t F)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hrsq : sertables.reflSquareRead t)
    (A : List (List Nat)) (hG : F.gram = A.map natV)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (lam : List Nat) (hlam : lam.length = t.rank)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hmsh : memberchar.mShapeRead t L) (hsym : memberchar.symRead t L)
    (wits : List (List Nat)) (hsupp : memberchar.supportRead t L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV t, false) ∈ W)
    (hrec : memberchar.recRead t F W L (poly.pnorm (natV lam))) (m : List Nat) :
    lookupN m (domFam t F.gram fuel lam) = ground.countOf (natV m) L := by
  obtain ⟨he, hc⟩ := domFam_counts t F hshape hgram hgsym hsp hpsq hpi hrd hrsq
    A hG hrows hsq hlead hdet fuel hwalk lam hlam W L hmsh hsym wits hsupp htop hseed hrec
  rw [he]
  exact lookupN_map_eq (fun m => ground.countOf (natV m) L) _ hc m

/-- At fuel covering the positive-root count, the actual
dominant recursion reads every multiplicity of a supported family.
The reflection data establish completion of all of its walks. -/
theorem domFam_lookup_bound (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F) (hsp : sertables.simplePosRead t F)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hrsq : sertables.reflSquareRead t)
    (hform : sertables.reflFormRead t F) (hrank : 0 < t.rank)
    (A : List (List Nat)) (hG : F.gram = A.map natV)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (fuel : Nat) (hfuel : t.posFolds.length ≤ fuel)
    (lam : List Nat) (hlam : lam.length = t.rank)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hmsh : memberchar.mShapeRead t L) (hsym : memberchar.symRead t L)
    (wits : List (List Nat)) (hsupp : memberchar.supportRead t L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV t, false) ∈ W)
    (hrec : memberchar.recRead t F W L (poly.pnorm (natV lam))) (m : List Nat) :
    lookupN m (domFam t F.gram fuel lam) = ground.countOf (natV m) L := by
  apply domFam_lookup t F hshape hgram hgsym hsp hpsq hpi hrd hrsq A hG hrows
    hsq hlead hdet fuel _ lam hlam W L hmsh hsym wits hsupp htop hseed hrec m
  intro v hv he
  have h := (domWalk_root_complete t F hshape hgram hsp hrsq hpsq hpi hrd hform fuel hfuel v hv).1
  rw [he] at h
  exact Nat.ne_of_gt hrank h.symm

/-- G2's actual dominant recursion at the stored fuel reads
every count of a supported reflection-invariant trace family. -/
theorem domFam_lookup_G2 (lam : List Nat) (hlam : lam.length = 2)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hmsh : memberchar.mShapeRead sertables.tableG2 L)
    (hsym : memberchar.symRead sertables.tableG2 L) (wits : List (List Nat))
    (hsupp : memberchar.supportRead sertables.tableG2 L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV sertables.tableG2, false) ∈ W)
    (hrec : memberchar.recRead sertables.tableG2 sertables.fundG2 W L (poly.pnorm (natV lam)))
    (m : List Nat) :
    lookupN m (domFam sertables.tableG2 sertables.fundG2.gram 16 lam)
      = ground.countOf (natV m) L := by
  apply domFam_lookup_bound sertables.tableG2 sertables.fundG2
    sertables.fundShape_G2 sertables.gramRead_G2 sertables.gramSymRead_G2
    sertables.simplePosRead_G2 sertables.permSquareRead_G2 sertables.permImageRead_G2
    sertables.rhoDotRead_G2 sertables.reflSquareRead_G2 sertables.reflFormRead_G2
    (by decide +kernel) [[4, 6], [6, 12]] (by decide +kernel) (by decide +kernel)
    sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2
    16 (by decide +kernel) lam hlam W L hmsh hsym wits hsupp htop hseed hrec m

/-- F4's actual dominant recursion at the stored fuel reads
every count of a supported reflection-invariant trace family. -/
theorem domFam_lookup_F4 (lam : List Nat) (hlam : lam.length = 4)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hmsh : memberchar.mShapeRead sertables.tableF4 L)
    (hsym : memberchar.symRead sertables.tableF4 L) (wits : List (List Nat))
    (hsupp : memberchar.supportRead sertables.tableF4 L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV sertables.tableF4, false) ∈ W)
    (hrec : memberchar.recRead sertables.tableF4 sertables.fundF4 W L (poly.pnorm (natV lam)))
    (m : List Nat) :
    lookupN m (domFam sertables.tableF4 sertables.fundF4.gram 1200 lam)
      = ground.countOf (natV m) L := by
  apply domFam_lookup_bound sertables.tableF4 sertables.fundF4
    sertables.fundShape_F4 sertables.gramRead_F4 sertables.gramSymRead_F4
    sertables.simplePosRead_F4 sertables.permSquareRead_F4 sertables.permImageRead_F4
    sertables.rhoDotRead_F4 sertables.reflSquareRead_F4 sertables.reflFormRead_F4
    (by decide +kernel) (sertables.adjF4.map (fun r => List.zipWith Nat.mul r sertables.tableF4.lenNums)) (by decide +kernel) (by decide +kernel)
    sertables.cartanSolve_F4.1 sertables.cartanSolve_F4.2.1 sertables.cartanSolve_F4.2.2
    1200 (by decide +kernel) lam hlam W L hmsh hsym wits hsupp htop hseed hrec m

/-- E6's actual dominant recursion at the stored fuel reads
every count of a supported reflection-invariant trace family. -/
theorem domFam_lookup_E6 (lam : List Nat) (hlam : lam.length = 6)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hmsh : memberchar.mShapeRead sertables.tableE6 L)
    (hsym : memberchar.symRead sertables.tableE6 L) (wits : List (List Nat))
    (hsupp : memberchar.supportRead sertables.tableE6 L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV sertables.tableE6, false) ∈ W)
    (hrec : memberchar.recRead sertables.tableE6 sertables.fundE6 W L (poly.pnorm (natV lam)))
    (m : List Nat) :
    lookupN m (domFam sertables.tableE6 sertables.fundE6.gram 52000 lam)
      = ground.countOf (natV m) L := by
  apply domFam_lookup_bound sertables.tableE6 sertables.fundE6
    sertables.fundShape_E6 sertables.gramRead_E6 sertables.gramSymRead_E6
    sertables.simplePosRead_E6 sertables.permSquareRead_E6 sertables.permImageRead_E6
    sertables.rhoDotRead_E6 sertables.reflSquareRead_E6 sertables.reflFormRead_E6
    (by decide +kernel) (sertables.adjE6.map (fun r => List.zipWith Nat.mul r sertables.tableE6.lenNums)) (by decide +kernel) (by decide +kernel)
    sertables.cartanSolve_E6.1 sertables.cartanSolve_E6.2.1 sertables.cartanSolve_E6.2.2
    52000 (by decide +kernel) lam hlam W L hmsh hsym wits hsupp htop hseed hrec m

/-- E7's actual dominant recursion at the stored fuel reads
every count of a supported reflection-invariant trace family. -/
theorem domFam_lookup_E7 (lam : List Nat) (hlam : lam.length = 7)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hmsh : memberchar.mShapeRead sertables.tableE7 L)
    (hsym : memberchar.symRead sertables.tableE7 L) (wits : List (List Nat))
    (hsupp : memberchar.supportRead sertables.tableE7 L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV sertables.tableE7, false) ∈ W)
    (hrec : memberchar.recRead sertables.tableE7 sertables.fundE7 W L (poly.pnorm (natV lam)))
    (m : List Nat) :
    lookupN m (domFam sertables.tableE7 sertables.fundE7.gram 2903040 lam)
      = ground.countOf (natV m) L := by
  apply domFam_lookup_bound sertables.tableE7 sertables.fundE7
    sertables.fundShape_E7 sertables.gramRead_E7 sertables.gramSymRead_E7
    sertables.simplePosRead_E7 sertables.permSquareRead_E7 sertables.permImageRead_E7
    sertables.rhoDotRead_E7 sertables.reflSquareRead_E7 sertables.reflFormRead_E7
    (by decide +kernel) (sertables.adjE7.map (fun r => List.zipWith Nat.mul r sertables.tableE7.lenNums)) (by decide +kernel) (by decide +kernel)
    sertables.cartanSolve_E7.1 sertables.cartanSolve_E7.2.1 sertables.cartanSolve_E7.2.2
    2903040 (by decide +kernel) lam hlam W L hmsh hsym wits hsupp htop hseed hrec m

/-- E8's actual dominant recursion at the stored fuel reads
every count of a supported reflection-invariant trace family. -/
theorem domFam_lookup_E8 (lam : List Nat) (hlam : lam.length = 8)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hmsh : memberchar.mShapeRead sertables.tableE8 L)
    (hsym : memberchar.symRead sertables.tableE8 L) (wits : List (List Nat))
    (hsupp : memberchar.supportRead sertables.tableE8 L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV sertables.tableE8, false) ∈ W)
    (hrec : memberchar.recRead sertables.tableE8 sertables.fundE8 W L (poly.pnorm (natV lam)))
    (m : List Nat) :
    lookupN m (domFam sertables.tableE8 sertables.fundE8.gram 696729600 lam)
      = ground.countOf (natV m) L := by
  apply domFam_lookup_bound sertables.tableE8 sertables.fundE8
    sertables.fundShape_E8 sertables.gramRead_E8 sertables.gramSymRead_E8
    sertables.simplePosRead_E8 sertables.permSquareRead_E8 sertables.permImageRead_E8
    sertables.rhoDotRead_E8 sertables.reflSquareRead_E8 sertables.reflFormRead_E8
    (by decide +kernel) (sertables.adjE8.map (fun r => List.zipWith Nat.mul r sertables.tableE8.lenNums)) (by decide +kernel) (by decide +kernel)
    sertables.cartanSolve_E8.1 sertables.cartanSolve_E8.2.1 sertables.cartanSolve_E8.2.2
    696729600 (by decide +kernel) lam hlam W L hmsh hsym wits hsupp htop hseed hrec m

/-- Reflection-invariant framed families are determined by their
natural dominant counts. Completed walks transport every framed
key to that list; keys outside the frame have zero counts. -/
theorem count_eq_of_dominant (t : gentable.Table) (hsq : sertables.reflSquareRead t)
    (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (L R : List (List BPair)) (hL : memberchar.mShapeRead t L) (hR : memberchar.mShapeRead t R)
    (hsL : memberchar.symRead t L) (hsR : memberchar.symRead t R)
    (hdom : ∀ m, ground.countOf (natV m) L = ground.countOf (natV m) R)
    (v : List BPair) : ground.countOf v L = ground.countOf v R := by
  by_cases hf : v.length = t.rank ∧ poly.pnorm v = v
  · have hout := hwalk v hf.1
    rw [hf.2] at hout
    have hd := domWalk_lam t fuel v hf.1 hf.2 hout
    have he := hdom (natsOf (domWalk t fuel v))
    rw [natV_natsOf_eq _ hd.2.1 (fun i hi => hd.2.2 i (by rw [← hd.1]; exact hi))] at he
    rw [← domWalk_count t L hsq hL hsL fuel v hf.1 hf.2 hout,
      ← domWalk_count t R hsq hR hsR fuel v hf.1 hf.2 hout]
    exact he
  · rw [ground.countOf_zero_of_not_mem (fun h => hf (hL v h)),
      ground.countOf_zero_of_not_mem (fun h => hf (hR v h))]

/-- The supported reflection-invariant multiplicity family with
top count one and the trace recursion is unique, key by key.
Both families read the actual dominant solve at their dominant
keys, and reflection walks read every further occupied key. -/
theorem multiplicity_unique (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hgram : sertables.gramRead t F)
    (hgsym : sertables.gramSymRead F) (hsp : sertables.simplePosRead t F)
    (hpsq : sertables.permSquareRead t F) (hpi : sertables.permImageRead t F)
    (hrd : sertables.rhoDotRead t F) (hrsq : sertables.reflSquareRead t)
    (A : List (List Nat)) (hG : F.gram = A.map natV)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (lam : List Nat) (hlam : lam.length = t.rank) (W : List (List BPair × Bool))
    (hseed : (sertables.rhoV t, false) ∈ W)
    (L R : List (List BPair)) (witsL witsR : List (List Nat))
    (hmL : memberchar.mShapeRead t L) (hmR : memberchar.mShapeRead t R)
    (hsL : memberchar.symRead t L) (hsR : memberchar.symRead t R)
    (hdL : memberchar.supportRead t L witsL (natV lam))
    (hdR : memberchar.supportRead t R witsR (natV lam))
    (htL : memberchar.topRead L (natV lam)) (htR : memberchar.topRead R (natV lam))
    (hrL : memberchar.recRead t F W L (poly.pnorm (natV lam)))
    (hrR : memberchar.recRead t F W R (poly.pnorm (natV lam))) (v : List BPair) :
    ground.countOf v L = ground.countOf v R := by
  apply count_eq_of_dominant t hrsq fuel hwalk L R hmL hmR hsL hsR _ v
  intro m
  exact (domFam_lookup t F hshape hgram hgsym hsp hpsq hpi hrd hrsq A hG hrows
    hsq hlead hdet fuel hwalk lam hlam W L hmL hsL witsL hdL htL hseed hrL m).symm.trans
    (domFam_lookup t F hshape hgram hgsym hsp hpsq hpi hrd hrsq A hG hrows
      hsq hlead hdet fuel hwalk lam hlam W R hmR hsR witsR hdR htR hseed hrR m)

/-- Increasing completed walks' fuel preserves every recursion
step and therefore the whole dominant solve. -/
private theorem famGo_more (t : gentable.Table) (G : elim.Mat) (fuel extra : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (top : List Nat) (cap : Nat) : ∀ ks acc,
    (∀ m ∈ ks, m.length = t.rank) →
    famGo t G (fuel + extra) top cap ks acc = famGo t G fuel top cap ks acc
  | [], _, _ => rfl
  | m :: ks, acc, hwidth => by
    have hnxt := fun acc => famGo_more t G fuel extra hwalk top cap ks acc
      (fun q hq => hwidth q (List.Mem.tail m hq))
    change (if m == top then famGo t G (fuel + extra) top cap ks (acc ++ [(m, 1)]) else _) =
      (if m == top then famGo t G fuel top cap ks (acc ++ [(m, 1)]) else _)
    by_cases he : (m == top) = true
    · rw [if_pos he, if_pos he]
      exact hnxt _
    · rw [if_neg he, if_neg he]
      let den := BPair.marginN (BPair.norm (formC G (shiftV t top) (shiftV t top)
        + (formC G (shiftV t m) (shiftV t m)).swap))
      change (if den == 0 then [] else _) = (if den == 0 then [] else _)
      by_cases hd : (den == 0) = true
      · rw [if_pos hd, if_pos hd]
      · rw [if_neg hd, if_neg hd, numAt_more t G fuel extra hwalk acc cap m (hwidth m (List.Mem.head ks))]
        cases hn : numAt t G fuel acc cap m with
        | none => rfl
        | some n =>
          change (if n.norm.marginN % den == 0 then
            famGo t G (fuel + extra) top cap ks (acc ++ [(m, n.norm.marginN / den)]) else []) =
            (if n.norm.marginN % den == 0 then
            famGo t G fuel top cap ks (acc ++ [(m, n.norm.marginN / den)]) else [])
          by_cases hr : (n.norm.marginN % den == 0) = true
          · rw [if_pos hr, if_pos hr]
            exact hnxt _
          · rw [if_neg hr, if_neg hr]

/-- Once all rank-width dominance walks complete, the actual
dominant multiplicities are fixed by every larger fuel. -/
theorem domFam_more (t : gentable.Table) (G : elim.Mat) (fuel extra : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (lam : List Nat) : domFam t G (fuel + extra) lam = domFam t G fuel lam := by
  apply famGo_more t G fuel extra hwalk lam (rdKey t G lam)
  intro m hm
  have hc := ground.countOf_pos_of_mem hm
  rw [countOf_sortDesc] at hc
  exact domKeys_length t G lam m (ground.mem_of_countOf_pos _ _ hc)

/-- A successful dominant solve appends every remaining key once,
in the input order, including keys whose multiplicity is zero. -/
private theorem famGo_keys (t : gentable.Table) (G : elim.Mat)
    (fuel : Nat) (top : List Nat) (rdTop : Nat) :
    ∀ (ks : List (List Nat)) (acc : List (List Nat × Nat)),
      famGo t G fuel top rdTop ks acc = [] ∨
        (famGo t G fuel top rdTop ks acc).map Prod.fst = acc.map Prod.fst ++ ks
  | [], acc => Or.inr (ground.append_nil _).symm
  | m :: tl, acc => by
    have step (n : Nat) : famGo t G fuel top rdTop tl (acc ++ [(m, n)]) = [] ∨
        (famGo t G fuel top rdTop tl (acc ++ [(m, n)])).map Prod.fst = acc.map Prod.fst ++ m :: tl := by
      cases famGo_keys t G fuel top rdTop tl (acc ++ [(m, n)]) with
      | inl h => exact Or.inl h
      | inr h =>
        refine Or.inr (h.trans ?_)
        rw [ground.map_append, ground.append_assoc]
        rfl
    change (let out := if m == top then famGo t G fuel top rdTop tl (acc ++ [(m, 1)])
      else
        let den := BPair.marginN (BPair.norm
          (formC G (shiftV t top) (shiftV t top)
            + (formC G (shiftV t m) (shiftV t m)).swap))
        if den == 0 then []
        else
          match numAt t G fuel acc rdTop m with
          | none => []
          | some numer =>
            let n := numer.norm.marginN
            if n % den == 0 then famGo t G fuel top rdTop tl (acc ++ [(m, n / den)]) else []
      out = [] ∨ out.map Prod.fst = acc.map Prod.fst ++ m :: tl)
    by_cases he : (m == top) = true
    · rw [if_pos he]
      exact step 1
    · rw [if_neg he]
      by_cases hz : (BPair.marginN (BPair.norm
          (formC G (shiftV t top) (shiftV t top)
            + (formC G (shiftV t m) (shiftV t m)).swap)) == 0) = true
      · rw [if_pos hz]
        exact Or.inl rfl
      · rw [if_neg hz]
        cases hn : numAt t G fuel acc rdTop m with
        | none => exact Or.inl rfl
        | some numer =>
          let den := BPair.marginN (BPair.norm
            (formC G (shiftV t top) (shiftV t top)
              + (formC G (shiftV t m) (shiftV t m)).swap))
          let n := BPair.marginN (BPair.norm numer)
          change (if n % den == 0 then famGo t G fuel top rdTop tl (acc ++ [(m, n / den)]) else []) = [] ∨
            (if n % den == 0 then famGo t G fuel top rdTop tl (acc ++ [(m, n / den)]) else []).map Prod.fst
              = acc.map Prod.fst ++ m :: tl
          by_cases hm : (n % den == 0) = true
          · rw [if_pos hm]
            exact step _
          · rw [if_neg hm]
            exact Or.inl rfl

/-- The dominant solve's labels have the input keys' coroot width,
including each label whose computed multiplicity is vacant. -/
private theorem famGo_width (t : gentable.Table) (G : elim.Mat)
    (fuel : Nat) (top : List Nat) (rdTop : Nat)
    (ks : List (List Nat)) (acc : List (List Nat × Nat))
    (hk : ∀ m ∈ ks, m.length = t.rank) (ha : ∀ p ∈ acc, p.1.length = t.rank) :
    ∀ p ∈ famGo t G fuel top rdTop ks acc, p.1.length = t.rank := by
  cases famGo_keys t G fuel top rdTop ks acc with
  | inl h => rw [h]; exact fun _ hp => nomatch hp
  | inr h =>
    intro p hp
    have hm := ground.mem_map_to Prod.fst hp
    rw [h] at hm
    cases ground.mem_append_of _ _ hm with
    | inl hacc =>
      obtain ⟨q, hq, hqp⟩ := ground.mem_map_of Prod.fst acc p.1 hacc
      rw [← hqp]
      exact ha q hq
    | inr hks => exact hk p.1 hks

/-- Every completed dominant family has exactly the window's
key multiset. The only alternative is the explicit refusal list. -/
theorem domFam_keys (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (lam : List Nat) :
    domFam t G fuel lam = [] ∨ ∀ m,
      ground.countOf m ((domFam t G fuel lam).map Prod.fst) = ground.countOf m (domKeys t G lam) := by
  cases famGo_keys t G fuel lam (rdKey t G lam) (sortDesc (rdKey t G) (domKeys t G lam)) [] with
  | inl h => exact Or.inl h
  | inr h =>
    refine Or.inr (fun m => ?_)
    change ground.countOf m ((famGo t G fuel lam (rdKey t G lam) _ []).map Prod.fst) = _
    rw [h]
    exact countOf_sortDesc (rdKey t G) m (domKeys t G lam)

/-- The dominant multiplicity producer never repeats a key,
including its refusal value. -/
theorem domFam_distinct (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (lam : List Nat) :
    ground.distinctList ((domFam t G fuel lam).map Prod.fst) := by
  cases domFam_keys t G fuel lam with
  | inl h => rw [h]; exact fun _ hm => nomatch hm
  | inr h =>
    intro m _
    rw [h m]
    exact ground.distinctList_all (domKeys_distinct t G lam) m

/-- Every produced dominant label has the table's rank. -/
private theorem domFam_width (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (lam : List Nat) : ∀ p ∈ domFam t G fuel lam, p.1.length = t.rank := by
  refine famGo_width t G fuel lam (rdKey t G lam) _ [] ?_ (fun _ h => nomatch h)
  intro m hm
  have hc := ground.countOf_pos_of_mem hm
  rw [countOf_sortDesc] at hc
  exact domKeys_length t G lam m (ground.mem_of_countOf_pos _ _ hc)

/-- The produced multiplicity family satisfies the shape read at
every top and closure count (`lem:memberdata`(i)); each dominant
key's orbit is canonical and has the coroot width. -/
theorem multFam_shape (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (lam : List Nat) : memberchar.mShapeRead t (multFam t G fuel lam) := by
  let parts := (domFam t G fuel lam).map
    (fun p => (orbitSet t fuel (natV p.1), p.2))
  show memberchar.mShapeRead t
    (if parts.any (fun q => q.1.isEmpty) then []
      else parts.flatMap (fun q => q.1.flatMap (List.replicate q.2)))
  by_cases he : parts.any (fun q => q.1.isEmpty) = true
  · rw [if_pos he]
    exact fun _ h => nomatch h
  · rw [if_neg he]
    intro v hv
    obtain ⟨q, hq, hvq⟩ := ground.mem_flatMap_of _ parts v hv
    obtain ⟨p, hp, hpq⟩ := ground.mem_map_of _ (domFam t G fuel lam) q hq
    rw [← hpq] at hvq
    obtain ⟨w, hw, hvw⟩ := ground.mem_flatMap_of _ (orbitSet t fuel (natV p.1)) v hvq
    have hvw' : v = w := ground.mem_replicate_eq w _ v hvw
    rw [hvw']
    exact orbitSet_shape t fuel (natV p.1)
      ((ground.length_map BPair.ofNat p.1).trans (domFam_width t G fuel lam p hp)) w hw

/-- Copying every orbit key at one multiplicity scales its
occurrence count by that multiplicity. -/
private theorem countOf_orbitCopies (n : Nat) (x : List BPair) :
    ∀ L : List (List BPair),
      ground.countOf x (L.flatMap (List.replicate n)) = n * ground.countOf x L
  | [] => (Nat.mul_zero n).symm
  | y :: tl => by
    change ground.countOf x (List.replicate n y ++ tl.flatMap (List.replicate n))
      = n * ground.countOf x (y :: tl)
    rw [ground.countOf_append, countOf_orbitCopies n x tl,
      ground.countOf_cons, Nat.mul_add]
    by_cases he : x = y
    · rw [he, ground.countOf_replicate, if_pos rfl, Nat.mul_one]
    · rw [ground.countOf_replicate_ne x y he n, if_neg he, Nat.mul_zero]

/-- Filtering a family to its nonnegative keys preserves the
count of every natural coroot label. -/
theorem natV_count_nonneg (L : List (List BPair)) (m : List Nat) :
    ground.countOf (natV m) L = ground.countOf (natV m)
      (L.filter (fun v => v.all (fun x => decide (BPair.unit ≤ x)))) := by
  have hp : (natV m).all (fun x => decide (BPair.unit ≤ x)) = true := by
    apply ground.all_of_mem_intro
    intro x hx
    obtain ⟨n, _, hn⟩ := ground.mem_map_of BPair.ofNat m x hx
    rw [← hn]
    exact decide_eq_true (ground.unitLeOfNat n)
  rw [ground.countOf_filter, hp]
  rfl

/-- A family whose nonnegative keys consist of one natural
label reads every natural label at the corresponding delta. -/
theorem natV_count_single_dom (L : List (List BPair)) (k : List Nat)
    (h : L.filter (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV k]) (m : List Nat) :
    ground.countOf (natV m) L = if m = k then 1 else 0 := by
  rw [natV_count_nonneg L m, h, ground.countOf_cons]
  by_cases he : m = k
  · rw [if_pos he, he, if_pos rfl]
    rfl
  · have hv : natV m ≠ natV k := by
      intro hv
      have hn := congrArg natsOf hv
      rw [natsOf_natV, natsOf_natV] at hn
      exact he hn
    rw [if_neg he, if_neg hv]
    rfl

/-- Completed orbit expansions read their counts as the
dominant entries' multiplicities against the orbit counts. -/
theorem multFam_count (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (lam : List Nat)
    (horbit : ∀ p ∈ domFam t G fuel lam, orbitSet t fuel (natV p.1) ≠ []) (v : List BPair) :
    ground.countOf v (multFam t G fuel lam) = ground.famFold Nat.add 0
      (fun p => p.2 * ground.countOf v (orbitSet t fuel (natV p.1))) (domFam t G fuel lam) := by
  let parts := (domFam t G fuel lam).map (fun p => (orbitSet t fuel (natV p.1), p.2))
  have hf : parts.any (fun q => q.1.isEmpty) = false := by
    apply ground.any_false_of_all_not
    apply ground.all_of_mem_intro
    intro q hq
    obtain ⟨p, hp, hpq⟩ := ground.mem_map_of _ _ q hq
    rw [← hpq]
    cases he : orbitSet t fuel (natV p.1) with
    | nil => exact absurd he (horbit p hp)
    | cons _ _ => rfl
  change ground.countOf v (if parts.any (fun q => q.1.isEmpty) then []
    else parts.flatMap (fun q => q.1.flatMap (List.replicate q.2))) = _
  rw [hf]
  change ground.countOf v (((domFam t G fuel lam).map
    (fun p => (orbitSet t fuel (natV p.1), p.2))).flatMap
    (fun q => q.1.flatMap (List.replicate q.2))) = _
  rw [ground.countOf_flatMap, ground.famFold_map]
  apply ground.famFold_congr_mem Nat.add 0
  intro p _
  exact countOf_orbitCopies p.2 v (orbitSet t fuel (natV p.1))

/-- If each computed orbit has its seed as its sole dominant
key, the expanded family's dominant counts are exactly the
actual dominant table's lookups. -/
theorem multFam_dominant (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (lam : List Nat)
    (hdom : ∀ p ∈ domFam t G fuel lam,
      (orbitSet t fuel (natV p.1)).filter (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV p.1])
    (m : List Nat) :
    ground.countOf (natV m) (multFam t G fuel lam) = lookupN m (domFam t G fuel lam) := by
  have horbit : ∀ p ∈ domFam t G fuel lam, orbitSet t fuel (natV p.1) ≠ [] := by
    intro p hp he
    have h := hdom p hp
    rw [he] at h
    exact nomatch h
  rw [multFam_count t G fuel lam horbit]
  have hl := fusion.lookupBy_sum (fun a b : List Nat => a == b) ground.listBeq_decide
    m (domFam t G fuel lam) (domFam_distinct t G fuel lam)
  change _ = (fusion.lookupBy (fun a b : List Nat => a == b) m (domFam t G fuel lam)).getD 0
  rw [hl]
  apply ground.famFold_congr_mem Nat.add 0
  intro p hp
  rw [natV_count_single_dom _ p.1 (hdom p hp) m]
  by_cases he : m = p.1
  · rw [if_pos he, if_pos he.symm, Nat.mul_one]
  · rw [if_neg he, if_neg (fun h => he h.symm), Nat.mul_zero]

/-- The multiplicity family inherits the reflection invariance of
its dominant keys' orbits (`lem:memberdata`(i); `lem:strings`).
Each orbit enters at one multiplicity throughout the family. -/
theorem multFam_sym (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (lam : List Nat)
    (hsq : sertables.reflSquareRead t)
    (hsym : ∀ p ∈ domFam t G fuel lam,
      memberchar.symRead t (orbitSet t fuel (natV p.1))) :
    memberchar.symRead t (multFam t G fuel lam) := by
  let parts := (domFam t G fuel lam).map
    (fun p => (orbitSet t fuel (natV p.1), p.2))
  intro w hw i hi
  have hwidth := multFam_shape t G fuel lam w hw
  change ground.countOf (sertables.reflAt t i w)
      (if parts.any (fun q => q.1.isEmpty) then []
       else parts.flatMap (fun q => q.1.flatMap (List.replicate q.2)))
    = ground.countOf w
      (if parts.any (fun q => q.1.isEmpty) then []
       else parts.flatMap (fun q => q.1.flatMap (List.replicate q.2)))
  by_cases he : parts.any (fun q => q.1.isEmpty) = true
  · rw [if_pos he]
    rfl
  · rw [if_neg he, ground.countOf_flatMap, ground.countOf_flatMap]
    refine ground.famFold_congr_mem Nat.add 0 _ _ parts ?_
    intro q hq
    obtain ⟨p, hp, hpq⟩ := ground.mem_map_of _ _ q hq
    rw [← hpq, countOf_orbitCopies, countOf_orbitCopies]
    exact congrArg (fun k => p.2 * k)
      (memberchar.count_reflAt t _ hsq
        (orbitSet_shape t fuel (natV p.1)
          ((ground.length_map BPair.ofNat p.1).trans (domFam_width t G fuel lam p hp)))
        (hsym p hp) i hi w hwidth.1 hwidth.2)


/-- The actual orbit-expanded family reads a framed invariant
family at every content once its dominant lookups agree and the
computed orbits have the reflection and unique-dominant reads. -/
theorem multFam_read (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (lam : List Nat)
    (hsq : sertables.reflSquareRead t)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (L : List (List BPair)) (hmsh : memberchar.mShapeRead t L) (hsym : memberchar.symRead t L)
    (hlookup : ∀ m, lookupN m (domFam t G fuel lam) = ground.countOf (natV m) L)
    (horbit : ∀ p ∈ domFam t G fuel lam, memberchar.symRead t (orbitSet t fuel (natV p.1)))
    (hdom : ∀ p ∈ domFam t G fuel lam,
      (orbitSet t fuel (natV p.1)).filter (fun v => v.all (fun x => decide (BPair.unit ≤ x))) = [natV p.1])
    (v : List BPair) : ground.countOf v (multFam t G fuel lam) = ground.countOf v L :=
  count_eq_of_dominant t hsq fuel hwalk _ L (multFam_shape t G fuel lam) hmsh
    (multFam_sym t G fuel lam hsq horbit) hsym
    (fun m => (multFam_dominant t G fuel lam hdom m).trans (hlookup m)) v

/-- The actual family-first parity fold reads both graded
convolution counts, one contribution per occupied occurrence.
Every moved key's completed walk reads its regular orbit count. -/
private theorem famCount_conv (t : gentable.Table) (W : List (List BPair × Bool))
    (hshape : sertables.wShapeRead t W) (hkeys : ground.distinctList (W.map Prod.fst))
    (hclose : assembly.wCloseRead t W) (hsq : sertables.reflSquareRead t)
    (top : List BPair) (htop : assembly.wTopAt W top)
    (hpin : ∀ p ∈ W, (∀ i, i < t.rank → BPair.unit < ground.getAt BPair.unit p.1 i) → p.1 = top)
    (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (y : List BPair) (hy : y.length = t.rank) :
    ∀ L : List (List BPair), (∀ nu ∈ L, nu.length = t.rank) →
      famCount t fuel top y L = some
        (ground.famFold Nat.add 0 (fun nu => assembly.wCount W (poly.pnorm (elim.vecAdd y (poly.neg nu))) false) L,
         ground.famFold Nat.add 0 (fun nu => assembly.wCount W (poly.pnorm (elim.vecAdd y (poly.neg nu))) true) L)
  | [], _ => rfl
  | nu :: L, hL => by
    have ht := famCount_conv t W hshape hkeys hclose hsq top htop hpin fuel hwalk y hy L
      (fun w hw => hL w (List.Mem.tail nu hw))
    let raw := elim.vecAdd y (poly.neg nu)
    have hraw : raw.length = t.rank := elim.length_vecAdd _ _ t.rank hy
      ((poly.length_neg nu).trans (hL nu (List.Mem.head _)))
    obtain ⟨q, hq, _⟩ := domWalk_result t fuel (poly.pnorm raw) (hwalk raw hraw)
    have hcnt := walkP_orbit_count t W hshape hkeys hclose hsq top htop hpin fuel
      (poly.pnorm raw) ((poly.pnorm_length raw).trans hraw) (poly.pnorm_pnorm raw) q hq
    change (match famCount t fuel top y L with
      | none => none
      | some p => match walkP t fuel (poly.pnorm raw) false with
        | none => none
        | some w => if w.1 == top then
            if w.2 then some (p.1, p.2 + 1) else some (p.1 + 1, p.2)
          else some p) = some (_, _)
    rw [ht, hq]
    change (if q.1 == top then if q.2 then some (_, _) else some (_, _) else some (_, _))
      = some (assembly.wCount W (poly.pnorm raw) false + _, assembly.wCount W (poly.pnorm raw) true + _)
    rw [hcnt false, hcnt true]
    by_cases he : q.1 = top
    · rw [if_pos (by rw [he]; exact ground.listEqBeq _), if_pos he, if_pos he]
      cases hb : q.2 with
      | false =>
        change some (_ + 1, _) = some (1 + _, 0 + _)
        rw [Nat.add_comm _ 1, Nat.zero_add]
      | true =>
        change some (_, _ + 1) = some (0 + _, 1 + _)
        rw [Nat.add_comm _ 1, Nat.zero_add]
    · rw [if_neg (fun h => he (ground.listBeqEq h)), if_neg he, if_neg he, Nat.zero_add, Nat.zero_add]

/-- The implemented member fusion count is the even convolution
count less the odd one at the shifted target. All occurrences of
the actual computed multiplicity family enter the fold
(`lem:memberdata`(i); `cor:steinberg`). -/
theorem countM_conv (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (hsq : sertables.reflSquareRead t) (a b c : List Nat) (hc : c.length = t.rank)
    (W : List (List BPair × Bool)) (hshape : sertables.wShapeRead t W)
    (hkeys : ground.distinctList (W.map Prod.fst)) (hclose : assembly.wCloseRead t W)
    (htop : assembly.wTopAt W (shiftV t b))
    (hpin : ∀ p ∈ W, (∀ i, i < t.rank → BPair.unit < ground.getAt BPair.unit p.1 i) → p.1 = shiftV t b) :
    countM t G fuel a b c = memberchar.convCount W (multFam t G fuel a) (shiftV t c) false
      - memberchar.convCount W (multFam t G fuel a) (shiftV t c) true := by
  have hm := multFam_shape t G fuel a
  have hy := shiftV_length t c hc
  have hn : poly.pnorm (shiftV t c) = shiftV t c := poly.pnorm_pnorm _
  unfold countM
  rw [famCount_conv t W hshape hkeys hclose hsq (shiftV t b) htop hpin fuel hwalk (shiftV t c) hy
    (multFam t G fuel a) (fun nu hnu => (hm nu hnu).1),
    memberchar.convCount_wFold t W _ hshape hm (shiftV t c) hy hn false,
    memberchar.convCount_wFold t W _ hshape hm (shiftV t c) hy hn true]
  rfl

/-- The implemented fusion count equals the channel count in
Steinberg's member display. The displayed additive identity
forces the natural subtraction's exact value. -/
theorem countM_memberAt (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (hsq : sertables.reflSquareRead t) (a b c : List Nat) (hc : c.length = t.rank)
    (W : List (List BPair × Bool)) (hshape : sertables.wShapeRead t W)
    (hkeys : ground.distinctList (W.map Prod.fst)) (hclose : assembly.wCloseRead t W)
    (htop : assembly.wTopAt W (shiftV t b))
    (hpin : ∀ p ∈ W, (∀ i, i < t.rank → BPair.unit < ground.getAt BPair.unit p.1 i) → p.1 = shiftV t b)
    (tops : List (List BPair))
    (hr : steinberg.memberAt t W (multFam t G fuel a) tops (natV c)) :
    countM t G fuel a b c = ground.countOf (natV c) tops := by
  rw [countM_conv t G fuel hwalk hsq a b c hc W hshape hkeys hclose htop hpin]
  change ground.countOf (natV c) tops + memberchar.convCount W (multFam t G fuel a) (shiftV t c) true
    = memberchar.convCount W (multFam t G fuel a) (shiftV t c) false at hr
  rw [← hr, ground.addSubSelfR]

/-- The actual stored graded orbit can be used in the fusion
convolution whenever a closed regular displayed family contains
its shifted seed and its finite key count fits the stored fuel. -/
theorem countM_orbit_conv (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (hsq : sertables.reflSquareRead t) (a b c : List Nat) (hc : c.length = t.rank)
    (W : List (List BPair × Bool)) (hshape : sertables.wShapeRead t W)
    (hkeys : ground.distinctList (W.map Prod.fst)) (hclose : assembly.wCloseRead t W)
    (hseed : (shiftV t b, false) ∈ W)
    (hpin : ∀ p ∈ W, (∀ i, i < t.rank → BPair.unit < ground.getAt BPair.unit p.1 i) → p.1 = shiftV t b)
    (hsep : ∀ w, w.length = t.rank → poly.pnorm w = w →
      ∀ i, i < t.rank → ∀ j, j < t.rank →
        assembly.reflF t i w = assembly.reflF t j w → i = j ∨ assembly.reflF t i w = w)
    (hfuel : (ground.dedupF (W.map Prod.fst)).length ≤ fuel) :
    countM t G fuel a b c =
      memberchar.convCount (orbitFam t fuel (shiftV t b)) (multFam t G fuel a) (shiftV t c) false
        - memberchar.convCount (orbitFam t fuel (shiftV t b)) (multFam t G fuel a) (shiftV t c) true := by
  have hsn : poly.pnorm (shiftV t b) = shiftV t b := poly.pnorm_pnorm _
  have hseed' : (poly.pnorm (shiftV t b), false) ∈ W := by rw [hsn]; exact hseed
  have hr := orbitFam_reads_family t W hshape hclose hkeys hsep fuel hfuel (shiftV t b) hseed'
  have hd := (orbit_complete_family t W hshape (orbitFam_step t W hshape hclose) hsep fuel hfuel
    (shiftV t b) hseed').2.2
  apply countM_conv t G fuel hwalk hsq a b c hc _ hr.1 hd hr.2.1
  · have h := hr.2.2
    rw [hsn] at h
    exact h
  · intro p hp hpos
    exact hpin p (orbitFam_sub t W hshape hclose fuel (shiftV t b) hseed' p hp) hpos

/-- The dominant recursion at the zero label returns its one
top count, with no higher-count query, at every step bound. -/
theorem domFam_unit (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan)) :
    domFam t G fuel (List.replicate t.rank 0) = [(List.replicate t.rank 0, 1)] := by
  unfold domFam
  rw [domKeys_unit t G hsq hlead hdet]
  change (if List.replicate t.rank 0 == List.replicate t.rank 0 then [(List.replicate t.rank 0, 1)] else _) = _
  rw [if_pos (ground.listEqBeq _)]

/-- The actual unit multiplicity family is one zero content at
any positive queue fuel and any Gram, given the Cartan solve. -/
theorem multFam_unit (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan)) :
    multFam t G (fuel + 1) (List.replicate t.rank 0) = [List.replicate t.rank BPair.unit] := by
  unfold multFam
  rw [domFam_unit t G (fuel + 1) hsq hlead hdet]
  have he : natV (List.replicate t.rank 0) = List.replicate t.rank BPair.unit := ground.map_replicate BPair.ofNat 0 t.rank
  change (if [(orbitSet t (fuel + 1) (natV (List.replicate t.rank 0)), 1)].any (fun q => q.1.isEmpty) then []
    else [(orbitSet t (fuel + 1) (natV (List.replicate t.rank 0)), 1)].flatMap
      (fun q => q.1.flatMap (List.replicate q.2))) = _
  rw [he, orbitSet_unit]
  rfl

/-- A singleton unit multiplicity family makes the left unit's
fusion count the label equality read, at every width-matched
second factor and target, without an orbit enumeration. -/
theorem countM_unit_left (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (unit : List Nat) (hunit : multFam t G fuel unit = [List.replicate t.rank BPair.unit])
    (b c : List Nat) (hb : b.length = t.rank) (hc : c.length = t.rank) :
    countM t G fuel unit b c = if c = b then 1 else 0 := by
  have hl := shiftV_length t c hc
  have hkey : poly.pnorm (elim.vecAdd (shiftV t c) (poly.neg (List.replicate t.rank BPair.unit))) = shiftV t c :=
    assembly.offKey_unit t.rank _ hl (poly.pnorm_pnorm _)
  have hstop : lowGo (shiftV t c) 0 = none := lowGo_of_nonneg _ 0
    (fun x hx => by
      obtain ⟨i, hi, he⟩ := ground.getAt_of_mem BPair.unit hx
      rw [← he]
      exact ground.leB_of_lt (shiftV_pos t c hc i (by rw [← hl]; exact hi)))
  unfold countM
  rw [hunit]
  change (match (match walkP t fuel
      (poly.pnorm (elim.vecAdd (shiftV t c) (poly.neg (List.replicate t.rank BPair.unit)))) false with
    | none => none
    | some w => if w.1 == shiftV t b then
        if w.2 then some (0, 0 + 1) else some (0 + 1, 0)
      else some (0, 0)) with | none => 0 | some p => p.1 - p.2) = _
  rw [hkey, walkP_stop t fuel (shiftV t c) false hstop]
  change (match (if shiftV t c == shiftV t b then some (1, 0) else some (0, 0)) with
    | none => 0 | some p => p.1 - p.2) = _
  by_cases he : c = b
  · rw [if_pos he, he, if_pos (ground.listEqBeq _)]
    rfl
  · have hne : ¬ (shiftV t c == shiftV t b) = true := by
      intro heq
      exact he (shiftV_inj t c b hc hb (ground.listBeqEq heq))
    rw [if_neg hne, if_neg he]
    rfl

/-- A row whose counts select one target lists that target
alone, provided the target belongs to the dominant window. -/
theorem rowM_single (t : gentable.Table) (G : elim.Mat) (fuel : Nat) (a b c : List Nat)
    (hc : c ∈ domKeys t G (List.zipWith Nat.add a b))
    (hcount : ∀ d ∈ domKeys t G (List.zipWith Nat.add a b),
      countM t G fuel a b d = if d = c then 1 else 0) : rowM t G fuel a b = [c] := by
  rw [rowM_filter]
  have hf : (domKeys t G (List.zipWith Nat.add a b)).filter
      (fun d => decide (0 < countM t G fuel a b d))
      = (domKeys t G (List.zipWith Nat.add a b)).filter (fun d => decide (d = c)) := by
    apply ground.filter_congr_mem
    intro d hd
    rw [hcount d (ground.mem_of_countOf_pos _ _ hd)]
    by_cases he : d = c
    · rw [if_pos he, decide_eq_true he]; rfl
    · rw [if_neg he, decide_eq_false he]; rfl
  rw [hf]
  apply ground.single_of_counts
  intro d
  rw [ground.countOf_filter]
  by_cases he : d = c
  · rw [decide_eq_true he, if_pos he, he]
    exact ground.countOf_distinct_one (domKeys_distinct t G _) hc
  · rw [decide_eq_false he, if_neg he]
    rfl

/-- The unit row is the singleton second label once that label
is in its own dominant window and the unit family is its one
zero content. -/
theorem rowM_unit_left (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (hunit : multFam t G fuel (List.replicate t.rank 0) = [List.replicate t.rank BPair.unit])
    (b : List Nat) (hb : b.length = t.rank) (hmem : b ∈ domKeys t G b) :
    rowM t G fuel (List.replicate t.rank 0) b = [b] := by
  have he : List.zipWith Nat.add (List.replicate t.rank 0) b = b := ground.zipWith_zero_left t.rank b hb
  apply rowM_single t G fuel (List.replicate t.rank 0) b b
  · rw [he]; exact hmem
  · intro c hc
    rw [he] at hc
    exact countM_unit_left t G fuel _ hunit b c hb (domKeys_length t G b c hc)

/-- At a supported channel family whose natural top counts are
the computed fusion counts, the actual row contains every
positive count and lists each target once. -/
theorem rowM_supported (t : gentable.Table) (F : sertables.FundData)
    (hshape : sertables.fundShape t F) (hsp : sertables.simplePosRead t F) (hrd : sertables.rhoDotRead t F)
    (A : List (List Nat)) (hG : F.gram = A.map natV)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan)) (fuel : Nat)
    (a b : List Nat) (ha : a.length = t.rank) (hb : b.length = t.rank)
    (tops : List (List BPair)) (wits : List (List Nat))
    (hsupp : memberchar.supportRead t tops wits (natV (List.zipWith Nat.add a b)))
    (hcount : ∀ c, c.length = t.rank → countM t F.gram fuel a b c = ground.countOf (natV c) tops)
    (c : List Nat) (hc : c.length = t.rank) :
    (0 < countM t F.gram fuel a b c ↔ 0 < ground.countOf c (rowM t F.gram fuel a b))
      ∧ ground.countOf c (rowM t F.gram fuel a b) ≤ 1 := by
  have hdist : ground.distinctList (rowM t F.gram fuel a b) := by
    rw [rowM_filter]
    exact ground.distinctList_filter _ _ (domKeys_distinct t F.gram _)
  refine ⟨⟨?_, ?_⟩, ground.distinctList_all hdist c⟩
  · intro hpos
    have hpc : 0 < ground.countOf (natV c) tops := by rw [← hcount c hc]; exact hpos
    have hdom := lamRead_natV t c hc
    rw [natV_pnorm] at hdom
    have hkey := domKeys_support t F hshape hsp hrd A hG hrows hsq hlead hdet
      (List.zipWith Nat.add a b) (ground.length_zipWith Nat.add a b t.rank ha hb) tops wits hsupp
      (natV c) hdom hpc
    rw [natsOf_natV] at hkey
    exact ground.countOf_pos_of_mem (rowM_of_count t F.gram fuel a b c hkey hpos)
  · intro hpos
    exact (rowM_mem t F.gram fuel a b c (ground.mem_of_countOf_pos _ _ hpos)).2

/-- At completed rank-width dominance walks, extra fuel keeps
the shifted-walk construction of the dual label. -/
theorem dualM_more (t : gentable.Table) (fuel extra : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (a : List Nat) (ha : a.length = t.rank) :
    dualM t (fuel + extra) a = dualM t fuel a := by
  unfold dualM
  rw [domWalk_more t fuel extra _ (hwalk (poly.neg (shiftV t a))
    ((poly.length_neg _).trans (shiftV_length t a ha)))]

/-- Once dominant walks and rank-width orbits complete, the
full multiplicity family is fixed at every larger fuel, including
its original occurrence order and all refusal branches. -/
theorem multFam_more (t : gentable.Table) (G : elim.Mat) (fuel extra : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (horbit : ∀ v : List BPair, v.length = t.rank → orbitSet t fuel v ≠ [])
    (lam : List Nat) : multFam t G (fuel + extra) lam = multFam t G fuel lam := by
  unfold multFam
  rw [domFam_more t G fuel extra hwalk lam]
  have he : ((domFam t G fuel lam).map (fun p => (orbitSet t (fuel + extra) (natV p.1), p.2)))
      = ((domFam t G fuel lam).map (fun p => (orbitSet t fuel (natV p.1), p.2))) := by
    apply ground.map_congr_members
    intro p hp
    rw [orbitSet_more t fuel extra (natV p.1) (horbit _
      ((ground.length_map BPair.ofNat p.1).trans
        (domFam_width t G fuel lam p (ground.mem_of_countOf_pos _ _ hp))))]
  rw [he]

/-- The completed parity walks give one graded family count at
any larger fuel, with the terminal parities kept. -/
private theorem famCount_more (t : gentable.Table) (fuel extra : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (kb kc : List BPair) (hc : kc.length = t.rank) :
    ∀ L : List (List BPair), (∀ nu ∈ L, nu.length = t.rank) →
      famCount t (fuel + extra) kb kc L = famCount t fuel kb kc L
  | [], _ => rfl
  | nu :: L, hL => by
    have ht := famCount_more t fuel extra hwalk kb kc hc L
      (fun w hw => hL w (List.Mem.tail nu hw))
    let raw := elim.vecAdd kc (poly.neg nu)
    have hraw : raw.length = t.rank := elim.length_vecAdd _ _ t.rank hc
      ((poly.length_neg nu).trans (hL nu (List.Mem.head _)))
    obtain ⟨q, hq, _⟩ := domWalk_result t fuel (poly.pnorm raw) (hwalk raw hraw)
    have hmore := walkP_more t fuel extra (poly.pnorm raw) false q hq
    change (match famCount t (fuel + extra) kb kc L with
      | none => none
      | some p => match walkP t (fuel + extra) (poly.pnorm raw) false with
        | none => none
        | some w => if w.1 == kb then
            if w.2 then some (p.1, p.2 + 1) else some (p.1 + 1, p.2)
          else some p) = _
    rw [ht]
    cases ht' : famCount t fuel kb kc L with
    | none =>
      change none = (match famCount t fuel kb kc L with | none => none | some p => _)
      rw [ht']
    | some p =>
      change (match walkP t (fuel + extra) (poly.pnorm raw) false with
        | none => none
        | some w => if w.1 == kb then
            if w.2 then some (p.1, p.2 + 1) else some (p.1 + 1, p.2)
          else some p) =
        (match famCount t fuel kb kc L with | none => none | some p => _)
      rw [hmore, ht']
      change _ = (match walkP t fuel (poly.pnorm raw) false with
        | none => none
        | some w => if w.1 == kb then
            if w.2 then some (p.1, p.2 + 1) else some (p.1 + 1, p.2)
          else some p)
      rw [hq]

/-- At completed walks and orbits, extra fuel keeps the fusion
count at every target of the member's width, with its graded
even and odd contributions fixed individually. -/
theorem countM_more (t : gentable.Table) (G : elim.Mat) (fuel extra : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (horbit : ∀ v : List BPair, v.length = t.rank → orbitSet t fuel v ≠ [])
    (a b c : List Nat) (hc : c.length = t.rank) :
    countM t G (fuel + extra) a b c = countM t G fuel a b c := by
  unfold countM
  rw [multFam_more t G fuel extra hwalk horbit a,
    famCount_more t fuel extra hwalk (shiftV t b) (shiftV t c) (shiftV_length t c hc)
      (multFam t G fuel a) (fun nu hn => (multFam_shape t G fuel a nu hn).1)]

/-- At completed walks and orbits, extra fuel keeps the actual
fusion row as a list, including its target order. -/
theorem rowM_more (t : gentable.Table) (G : elim.Mat) (fuel extra : Nat)
    (hwalk : ∀ v : List BPair, v.length = t.rank → domWalk t fuel (poly.pnorm v) ≠ [])
    (horbit : ∀ v : List BPair, v.length = t.rank → orbitSet t fuel v ≠ [])
    (a b : List Nat) : rowM t G (fuel + extra) a b = rowM t G fuel a b := by
  unfold rowM
  rw [multFam_more t G fuel extra hwalk horbit a]
  apply ground.filter_congr_mem
  intro c hc
  rw [famCount_more t fuel extra hwalk (shiftV t b) (shiftV t c)
    (shiftV_length t c (domKeys_length t G _ c (ground.mem_of_countOf_pos _ _ hc)))
    (multFam t G fuel a) (fun nu hn => (multFam_shape t G fuel a nu hn).1)]


end memberdata

namespace fusion
open ground

/-- The fundamentals' involution at a member: the index of the dual
label's read at a fundamental (`dualM` at the unit fold). -/
def fundInv (t : gentable.Table) (fuel : Nat) (i : Nat) : Nat :=
  places.idxOf (memberdata.dualM t fuel (unitAt t.rank i))
    ((List.range t.rank).map (unitAt t.rank))

/-- The series' reach lists (`con:memtable`): at `B` the vector
and the spinor among the keys with every further fundamental in
the prior's block against the vector's, at `C` the first
fundamental among the keys with the rest so, and at `D` the vector
and the two spinors among the keys with the rest so. -/
def reachB (l : Nat) : List (Option (Nat × Nat)) :=
  [none] ++ (List.range (l - 2)).map (fun j => some (j, 0)) ++ [none]

def reachC (l : Nat) : List (Option (Nat × Nat)) :=
  [none] ++ (List.range (l - 1)).map (fun j => some (j, 0))

def reachD (l : Nat) : List (Option (Nat × Nat)) :=
  [none] ++ (List.range (l - 3)).map (fun j => some (j, 0)) ++ [none, none]

/-- A member instantiation at a table with stated class data: every
field the table's own derived read at the coroot lists, the count
and involution `lem:memberdata`'s constructions, the walks' fuel a
stated datum (`con:fusion`'s member clause). -/
def dataOf (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat)) : Data (List Nat) :=
  let pad := memberdata.padN t.rank
  ⟨(fun a b => pad a == pad b),
   (fun _ => ground.listEqBeq _),
   List.replicate t.rank 0,
   (fun a => memberdata.dualM t fuel (pad a)),
   (fun a b => List.zipWith Nat.add (pad a) (pad b)),
   memberdata.thetaKey t,
   (fun a b c => memberdata.countM t G fuel (pad a) (pad b) (pad c)),
   (fun a b => memberdata.rowM t G fuel (pad a) (pad b)),
   (fun a => memberdata.dimM t (pad a)),
   (fun a => memberdata.c2M t G (pad a)),
   memberdata.c2M t G (memberdata.thetaKey t),
   memberdata.countM t G fuel (memberdata.thetaKey t)
     (memberdata.thetaKey t) (memberdata.thetaKey t),
   gentable.residue t,
   (fun k => memberdata.belowM t G k),
   (fun a => cls (memberdata.padN t.rank a)), clsAdd, clsFloorN, P⟩

/-- The member interface's Casimir reads a padded label at its
original value, the coordinate read's idempotence. -/
theorem c2N_pad_dataOf (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat)) (a : List Nat) :
    (dataOf t G fuel cls clsAdd clsFloorN P).c2N (memberdata.padN t.rank a)
      = (dataOf t G fuel cls clsAdd clsFloorN P).c2N a := by
  change memberdata.c2M t G (memberdata.padN t.rank (memberdata.padN t.rank a))
    = memberdata.c2M t G (memberdata.padN t.rank a)
  rw [memberdata.padN_of_length t.rank _ (memberdata.padN_length t.rank a)]

/-- The member interface's dimension reads a padded label at its
original value, the coordinate read's idempotence. -/
theorem dim_pad_dataOf (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat)) (a : List Nat) :
    (dataOf t G fuel cls clsAdd clsFloorN P).dim (memberdata.padN t.rank a)
      = (dataOf t G fuel cls clsAdd clsFloorN P).dim a := by
  change memberdata.dimM t (memberdata.padN t.rank (memberdata.padN t.rank a))
    = memberdata.dimM t (memberdata.padN t.rank a)
  rw [memberdata.padN_of_length t.rank _ (memberdata.padN_length t.rank a)]

/-- Every produced member row lists an occupied count at its
own target. The coroot box fixes each target under padding
(`lem:memberdata`(i); `con:fusion`). -/
theorem row_count_pos_dataOf (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat))
    (a b c : List Nat) (hc : c ∈ (dataOf t G fuel cls clsAdd clsFloorN P).row a b) :
    0 < (dataOf t G fuel cls clsAdd clsFloorN P).count a b c := by
  obtain ⟨hw, hp⟩ := memberdata.rowM_mem t G fuel
    (memberdata.padN t.rank a) (memberdata.padN t.rank b) c hc
  show 0 < memberdata.countM t G fuel
    (memberdata.padN t.rank a) (memberdata.padN t.rank b) (memberdata.padN t.rank c)
  rw [memberdata.padN_of_length t.rank c hw]
  exact hp

/-- The member interface's left unit has count one at the same
padded label and zero at every other label. The read holds for
arbitrary label spellings through the interface's equality. -/
theorem unitCount_dataOf (t : gentable.Table) (G : elim.Mat)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (fuel : Nat) (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat)) (a b : List Nat) :
    (dataOf t G (fuel + 1) cls clsAdd clsFloorN P).count
      (dataOf t G (fuel + 1) cls clsAdd clsFloorN P).unit a b
      = if (dataOf t G (fuel + 1) cls clsAdd clsFloorN P).eqL a b then 1 else 0 := by
  change memberdata.countM t G (fuel + 1) (memberdata.padN t.rank (List.replicate t.rank 0))
    (memberdata.padN t.rank a) (memberdata.padN t.rank b)
    = if memberdata.padN t.rank a == memberdata.padN t.rank b then 1 else 0
  rw [memberdata.padN_of_length t.rank (List.replicate t.rank 0) (ground.length_replicate _ _),
    memberdata.countM_unit_left t G (fuel + 1) _ (memberdata.multFam_unit t G fuel hsq hlead hdet)
      _ _ (memberdata.padN_length t.rank a) (memberdata.padN_length t.rank b)]
  by_cases he : memberdata.padN t.rank b = memberdata.padN t.rank a
  · rw [if_pos he, he, if_pos (ground.listEqBeq _)]
  · rw [if_neg he, if_neg (fun h => he (ground.listBeqEq h).symm)]

/-- At a positive queue fuel and the Cartan solve, the member
interface's unit row reads its second label alone. -/
theorem unitRowLaw_dataOf (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank) (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (hsq : elim.sqAt t.cartan t.rank)
    (hlead : ∀ k, k < t.rank → ¬ (elim.leadMinor (elim.transposeM t.cartan) (k + 1)).oneValue BPair.unit)
    (hdet : BPair.unit < elim.detD (elim.transposeM t.cartan))
    (fuel : Nat) (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat)) (b : List Nat) (hb : b.length = t.rank) :
    unitRowLaw (dataOf t (A.map memberdata.natV) (fuel + 1) cls clsAdd clsFloorN P) b := by
  change memberdata.rowM t (A.map memberdata.natV) (fuel + 1)
    (memberdata.padN t.rank (List.replicate t.rank 0)) (memberdata.padN t.rank b) = [b]
  rw [memberdata.padN_of_length t.rank (List.replicate t.rank 0) (ground.length_replicate _ _),
    memberdata.padN_of_length t.rank b hb]
  exact memberdata.rowM_unit_left t _ (fuel + 1) (memberdata.multFam_unit t _ fuel hsq hlead hdet) b hb
    (memberdata.domKeys_top t A hA hrows hsq hlead hdet b hb)

/-- At natural Gram rows with occupied sums, the interface reads
the unit label or a positive Casimir at every coroot list
(`con:fusion`; `con:sertables`' fundamental form). -/
theorem casPos_dataOf (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (fuel : Nat) (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat)) (a : List Nat) :
    casPos (dataOf t (A.map memberdata.natV) fuel cls clsAdd clsFloorN P) a := by
  cases Nat.eq_zero_or_pos (ground.sumNat (memberdata.padN t.rank a)) with
  | inl hz =>
    have hu := ground.replicate_of_sum_zero (memberdata.padN t.rank a) hz
    rw [memberdata.padN_length] at hu
    show ((memberdata.padN t.rank a
        == memberdata.padN t.rank (List.replicate t.rank 0)) || _) = true
    rw [hu, memberdata.padN_of_length t.rank (List.replicate t.rank 0)
      (ground.length_replicate 0 t.rank), ground.listEqBeq]
    rfl
  | inr hp =>
    have hpos := Nat.lt_of_lt_of_le hp (memberdata.sumNat_le_c2M t A hA hrows
      (memberdata.padN t.rank a) (memberdata.padN_length t.rank a))
    show (_ || decide (0 < memberdata.c2M t (A.map memberdata.natV)
      (memberdata.padN t.rank a))) = true
    rw [decide_eq_true hpos]
    exact Bool.or_true _

/-- Every member row lists each target at most once, the count's
filter selecting the distinct dominant-key box (`con:fusion`). -/
theorem row_distinct_dataOf (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat))
    (a b : List Nat) : ground.distinctList ((dataOf t G fuel cls clsAdd clsFloorN P).row a b) :=
  ground.distinctList_filter _ _ (memberdata.domKeys_distinct t G _)

/-- The member interface's cutoff list satisfies its bound at
every cutoff (`prop:windowfinite`; `con:fusion`). -/
theorem belowSound_dataOf (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat))
    (k : Nat) : belowSound (dataOf t G fuel cls clsAdd clsFloorN P) k := by
  refine ground.all_of_mem_intro _ _ (fun m hm => ?_)
  obtain ⟨hw, _, hk⟩ := memberdata.belowM_mem t G k m hm
  show decide (memberdata.c2M t G (memberdata.padN t.rank m) ≤ k) = true
  rw [memberdata.padN_of_length t.rank m hw]
  exact decide_eq_true hk

/-- The member cutoff list contains nonunit labels: its occupied
coordinate sum refuses the unit coroot list (`con:fusion`). -/
theorem belowNonunit_dataOf (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat))
    (k : Nat) : belowNonunit (dataOf t G fuel cls clsAdd clsFloorN P) k := by
  refine ground.all_of_mem_intro _ _ (fun m hm => ?_)
  obtain ⟨hw, hp, _⟩ := memberdata.belowM_mem t G k m hm
  show (!(memberdata.padN t.rank m
    == memberdata.padN t.rank (List.replicate t.rank 0))) = true
  rw [memberdata.padN_of_length t.rank m hw,
    memberdata.padN_of_length t.rank (List.replicate t.rank 0)
      (ground.length_replicate 0 t.rank)]
  cases he : (m == List.replicate t.rank 0) with
  | false => rfl
  | true =>
    have hm0 := ground.listBeqEq he
    rw [hm0, ground.sumNat_replicate_zero] at hp
    exact absurd hp (Nat.lt_irrefl 0)

/-- Natural Gram rows with occupied sums give the interface's
cutoff nesting at every ordered cutoff pair (`prop:windowfinite`). -/
theorem belowNest_dataOf (t : gentable.Table) (A : List (List Nat))
    (hA : A.length = t.rank)
    (hrows : ∀ r ∈ A, r.length = t.rank ∧ 0 < ground.sumNat r)
    (fuel : Nat) (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat))
    (k k' : Nat) (hk : k ≤ k') :
    belowNest (dataOf t (A.map memberdata.natV) fuel cls clsAdd clsFloorN P) k k' := by
  change memberdata.belowM t (A.map memberdata.natV) k
    = (memberdata.belowM t (A.map memberdata.natV) k').filter
      (fun m => decide (memberdata.c2M t (A.map memberdata.natV) (memberdata.padN t.rank m) ≤ k))
  rw [memberdata.belowM_nest t A hA hrows k k' hk]
  refine ground.filter_congr_mem _ _ _ (fun m hm => ?_)
  have hw := (memberdata.belowM_mem t (A.map memberdata.natV) k' m
    (ground.mem_of_countOf_pos m _ hm)).1
  rw [memberdata.padN_of_length t.rank m hw]

/-- The unit joined to the member cutoff list is distinct,
the occupied coordinate sum separating the list from the unit
(`def:carrier`; `prop:windowfinite`). -/
theorem below_distinct_dataOf (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) (P : fiber.Pres (List Nat))
    (k : Nat) : ground.distinctList
      ((dataOf t G fuel cls clsAdd clsFloorN P).unit :: (dataOf t G fuel cls clsAdd clsFloorN P).below k) := by
  have hunit : ground.countOf (List.replicate t.rank 0) (memberdata.belowM t G k) = 0 := by
    cases Nat.eq_zero_or_pos (ground.countOf (List.replicate t.rank 0)
        (memberdata.belowM t G k)) with
    | inl h0 => exact h0
    | inr hp =>
      have ho := (memberdata.belowM_mem t G k (List.replicate t.rank 0)
        (ground.mem_of_countOf_pos _ _ hp)).2.1
      rw [ground.sumNat_replicate_zero] at ho
      exact absurd ho (Nat.lt_irrefl 0)
  intro x hx
  show ground.countOf x (List.replicate t.rank 0 :: memberdata.belowM t G k) ≤ 1
  rw [ground.countOf_cons]
  by_cases he : x = List.replicate t.rank 0
  · rw [if_pos he, he, hunit]
    exact Nat.le_refl 1
  · rw [if_neg he, Nat.zero_add]
    have hm : x ∈ memberdata.belowM t G k := by
      cases hx with
      | head => exact absurd rfl he
      | tail _ h => exact h
    exact memberdata.belowM_distinct t G k x hm

/-- The signed-permutation order at the rank, the series orbits'
fuel: the closure's round count at the shifted key's whole
orbit. -/
def wFuel (l : Nat) : Nat :=
  2 ^ l * (List.range l).foldl (fun a k => a * (k + 1)) 1 + l

/-- The stored step count reads the signed-permutation count
joined to the rank (`con:sertables`; `lem:memberdata`). -/
theorem wFuel_eq (l : Nat) : wFuel l = 2 ^ l * ground.factorial l + l := by
  unfold wFuel
  rw [ground.factorial_foldl]

/-- B's displayed family and its distinct key list fit within
the stored step count, at every seed. -/
theorem serWeylB_fuel (l : Nat) (v : List BPair) :
    (sertables.serWeylB l v).length ≤ wFuel l
      ∧ (ground.dedupF ((sertables.serWeylB l v).map Prod.fst)).length ≤ wFuel l := by
  rw [wFuel_eq]
  exact ⟨by rw [sertables.serWeylB_length]; exact Nat.le_add_right _ _,
    Nat.le_trans (sertables.serWeylB_keys_length l v) (Nat.le_add_right _ _)⟩

/-- C's displayed family and its distinct key list fit within
the stored step count, at every seed. -/
theorem serWeylC_fuel (l : Nat) (v : List BPair) :
    (sertables.serWeylC l v).length ≤ wFuel l
      ∧ (ground.dedupF ((sertables.serWeylC l v).map Prod.fst)).length ≤ wFuel l := by
  rw [wFuel_eq]
  exact ⟨by rw [sertables.serWeylC_length]; exact Nat.le_add_right _ _,
    Nat.le_trans (sertables.serWeylC_keys_length l v) (Nat.le_add_right _ _)⟩

/-- D's even-sign family and its distinct key list fit within
the stored step count, at every seed. -/
theorem serWeylD_fuel (l : Nat) (v : List BPair) :
    (sertables.serWeylD l v).length ≤ wFuel l
      ∧ (ground.dedupF ((sertables.serWeylD l v).map Prod.fst)).length ≤ wFuel l := by
  rw [wFuel_eq]
  exact ⟨Nat.le_trans (sertables.serWeylD_length_le l v) (Nat.le_add_right _ _),
    Nat.le_trans (sertables.serWeylD_keys_length l v) (Nat.le_add_right _ _)⟩

/-- The `B` series' class read: the spinor parity, the last coroot
key's (`lem:chargedcell`(i), the short family's doubled keys
generating the unit class). -/
def clsB (l : Nat) (m : List Nat) : Nat := getAt 0 m (l - 1) % 2

/-- The `C` series' class read: the box parity, the positions'
weighted fold (`lem:chargedcell`(i), the even-sum lists the unit
class). -/
def clsC (m : List Nat) : Nat :=
  (List.range m.length).foldl (fun a i => a + (i + 1) * getAt 0 m i) 0 % 2

/-- The `D` series' class read at even rank: the two spinor
parities as a two-bit code (`lem:chargedcell`(i)'s four classes,
each its own inverse). -/
def clsDEven (l : Nat) (m : List Nat) : Nat :=
  2 * (((List.range (l - 2)).foldl (fun a i => a + (i + 1) * getAt 0 m i) 0
        + getAt 0 m (l - 2)) % 2)
    + ((List.range (l - 2)).foldl (fun a i => a + (i + 1) * getAt 0 m i) 0
        + getAt 0 m (l - 1)) % 2

/-- The `D` series' class read at odd rank: the four-fold cycle,
the spinors at the odd reads (`lem:chargedcell`(i)). -/
def clsDOdd (l : Nat) (m : List Nat) : Nat :=
  (2 * (List.range (l - 2)).foldl (fun a i => a + (i + 1) * getAt 0 m i) 0
    + getAt 0 m (l - 2) + 3 * getAt 0 m (l - 1)) % 4

/-- The `B` member instantiation at the rank. -/
def dataB (l : Nat) : Data (List Nat) :=
  dataOf (sertables.tableB l) (memberdata.gramOf (sertables.tableB l))
    (wFuel l) (clsB l) (fun x y => (x + y) % 2)
    (fun c => if c == 0 then 0
      else memberdata.c2M (sertables.tableB l)
        (memberdata.gramOf (sertables.tableB l))
        ((List.range l).map (fun k => if k + 1 == l then 1 else 0)))
    (fiber.presT (memtable.genB l) (reachB l) (fundInv (sertables.tableB l) (wFuel l))
      (memberdata.thetaKey (sertables.tableB l)))

/-- The `C` member instantiation at the rank. -/
def dataC (l : Nat) : Data (List Nat) :=
  dataOf (sertables.tableC l) (memberdata.gramOf (sertables.tableC l))
    (wFuel l) clsC (fun x y => (x + y) % 2)
    (fun c => if c == 0 then 0
      else memberdata.c2M (sertables.tableC l)
        (memberdata.gramOf (sertables.tableC l))
        ((List.range l).map (fun k => if k == 0 then 1 else 0)))
    (fiber.presT (memtable.definingC l) (reachC l) (fundInv (sertables.tableC l) (wFuel l))
      (memberdata.thetaKey (sertables.tableC l)))

/-- The `D` member instantiation at the rank: the class code and
its sum at the rank's parity, the winding floors the three end
members' reads (`lem:chargedcell`(ii)). -/
def dataD (l : Nat) : Data (List Nat) :=
  dataOf (sertables.tableD l) (memberdata.gramOf (sertables.tableD l))
    (wFuel l)
    (if l % 2 == 0 then clsDEven l else clsDOdd l)
    (if l % 2 == 0 then fun x y => 2 * ((x / 2 + y / 2) % 2) + (x + y) % 2
      else fun x y => (x + y) % 4)
    (fun c =>
      let t := sertables.tableD l
      let G := memberdata.gramOf t
      let e := fun k0 => (List.range l).map (fun k => if k == k0 then 1 else 0)
      if c == 0 then 0
      else if (if l % 2 == 0 then c == 3 else c == 2) then
        memberdata.c2M t G (e 0)
      else if (if l % 2 == 0 then c == 2 else c == 1) then
        memberdata.c2M t G (e (l - 2))
      else memberdata.c2M t G (e (l - 1)))
    (fiber.presT (memtable.genD l) (reachD l) (fundInv (sertables.tableD l) (wFuel l))
      (memberdata.thetaKey (sertables.tableD l)))

/-- A trivial-class member instantiation at its displayed adjugate
rows: the one class with the vacant floor (`lem:chargedcell`(i)'s
one-sector read at `G_2`, `F_4` and `E_8`). -/
def dataFixed (t : gentable.Table) (rows : List (List Nat))
    (fuel : Nat) (P : fiber.Pres (List Nat)) : Data (List Nat) :=
  dataOf t (sertables.gramRows t rows) fuel
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) P

/-- The one-class members satisfy all three class laws at every
label: the row's classes, the dual join and theta's class are the
unit class (`con:sertables`; `lem:chargedcell`(i)). -/
theorem clsLaws_dataFixed (t : gentable.Table) (rows : List (List Nat))
    (fuel : Nat) (P : fiber.Pres (List Nat)) (a b : List Nat) :
    clsLaw (dataFixed t rows fuel P) a b
      ∧ clsDualLaw (dataFixed t rows fuel P) a ∧ clsThetaLaw (dataFixed t rows fuel P) := by
  refine ⟨ground.all_of_mem_intro _ _ (fun _ _ => rfl), rfl, rfl⟩

/-- The `G_2` instantiation. -/
def dataG2 : Data (List Nat) :=
  dataFixed sertables.tableG2 sertables.adjG2 16
    (fiber.presT memtable.genG2 [none, some (0, 0)] (fundInv sertables.tableG2 16)
      (memberdata.thetaKey sertables.tableG2))

/-- The `F_4` instantiation. -/
def dataF4 : Data (List Nat) :=
  dataFixed sertables.tableF4 sertables.adjF4 1200
    (fiber.presT memtable.genF4 [none, some (0, 0), some (3, 3), none]
      (fundInv sertables.tableF4 1200) (memberdata.thetaKey sertables.tableF4))

/-- The `E_6` instantiation: the three classes at the key-three
remainders (`con:sertables`' adjugate rows;
`lem:chargedcell`(i)), the winding floor the paired fundamentals'
shared least. -/
def dataE6 : Data (List Nat) :=
  dataOf sertables.tableE6 (sertables.gramRows sertables.tableE6 sertables.adjE6)
    52000
    (fun m => (getAt 0 m 0 + 2 * getAt 0 m 2 + getAt 0 m 4
      + 2 * getAt 0 m 5) % 3)
    (fun x y => (x + y) % 3)
    (fun c => if c == 0 then 0
      else memberdata.c2M sertables.tableE6
        (sertables.gramRows sertables.tableE6 sertables.adjE6)
        [1, 0, 0, 0, 0, 0])
    (fiber.presT memtable.genE6
      [none, some (0, 5), some (0, 0), some (1, 1), some (5, 5), none]
      (fundInv sertables.tableE6 52000) (memberdata.thetaKey sertables.tableE6))

/-- The `E_7` instantiation: the two classes at the key-two
remainders, the winding floor the minuscule member's read. -/
def dataE7 : Data (List Nat) :=
  dataOf sertables.tableE7 (sertables.gramRows sertables.tableE7 sertables.adjE7)
    2903040
    (fun m => (getAt 0 m 1 + getAt 0 m 4 + getAt 0 m 6) % 2)
    (fun x y => (x + y) % 2)
    (fun c => if c == 0 then 0
      else memberdata.c2M sertables.tableE7
        (sertables.gramRows sertables.tableE7 sertables.adjE7)
        [0, 0, 0, 0, 0, 0, 1])
    (fiber.presT memtable.genE7
      [some (6, 6), some (6, 0), some (6, 1), some (6, 4), some (6, 5), some (6, 6), none]
      (fundInv sertables.tableE7 2903040) (memberdata.thetaKey sertables.tableE7))

/-- The `E_8` instantiation. -/
def dataE8 : Data (List Nat) :=
  dataFixed sertables.tableE8 sertables.adjE8 696729600
    (fiber.presT memtable.adjointE8
      [some (7, 7), some (7, 0), some (7, 1), some (7, 4), some (7, 5), some (7, 6),
       some (7, 7), none]
      (fundInv sertables.tableE8 696729600) (memberdata.thetaKey sertables.tableE8))

/-! The fixed members' positive fundamental forms, at the
displayed adjugate rows (`con:sertables`). -/

/-- The G2 Casimir is positive at every nonunit label. -/
theorem casPos_dataG2 (a : List Nat) : casPos dataG2 a := by
  apply casPos_dataOf sertables.tableG2
    (sertables.adjG2.map (fun r => List.zipWith Nat.mul r sertables.tableG2.lenNums))
    (by decide +kernel) (by decide +kernel) 16
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) dataG2.pres a

/-- The F4 Casimir is positive at every nonunit label. -/
theorem casPos_dataF4 (a : List Nat) : casPos dataF4 a := by
  apply casPos_dataOf sertables.tableF4
    (sertables.adjF4.map (fun r => List.zipWith Nat.mul r sertables.tableF4.lenNums))
    (by decide +kernel) (by decide +kernel) 1200
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) dataF4.pres a

/-- The E6 Casimir is positive at every nonunit label. -/
theorem casPos_dataE6 (a : List Nat) : casPos dataE6 a := by
  apply casPos_dataOf sertables.tableE6
    (sertables.adjE6.map (fun r => List.zipWith Nat.mul r sertables.tableE6.lenNums))
    (by decide +kernel) (by decide +kernel) 52000
    dataE6.cls dataE6.clsAdd dataE6.clsFloorN dataE6.pres a

/-- The E7 Casimir is positive at every nonunit label. -/
theorem casPos_dataE7 (a : List Nat) : casPos dataE7 a := by
  apply casPos_dataOf sertables.tableE7
    (sertables.adjE7.map (fun r => List.zipWith Nat.mul r sertables.tableE7.lenNums))
    (by decide +kernel) (by decide +kernel) 2903040
    dataE7.cls dataE7.clsAdd dataE7.clsFloorN dataE7.pres a

/-- The E8 Casimir is positive at every nonunit label. -/
theorem casPos_dataE8 (a : List Nat) : casPos dataE8 a := by
  apply casPos_dataOf sertables.tableE8
    (sertables.adjE8.map (fun r => List.zipWith Nat.mul r sertables.tableE8.lenNums))
    (by decide +kernel) (by decide +kernel) 696729600
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) dataE8.pres a

/-- The G2 cutoff enumerations nest in their product order. -/
theorem belowNest_dataG2 (k k' : Nat) (h : k ≤ k') : belowNest dataG2 k k' := by
  apply belowNest_dataOf sertables.tableG2
    (sertables.adjG2.map (fun r => List.zipWith Nat.mul r sertables.tableG2.lenNums))
    (by decide +kernel) (by decide +kernel) 16
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) dataG2.pres k k' h

/-- The F4 cutoff enumerations nest in their product order. -/
theorem belowNest_dataF4 (k k' : Nat) (h : k ≤ k') : belowNest dataF4 k k' := by
  apply belowNest_dataOf sertables.tableF4
    (sertables.adjF4.map (fun r => List.zipWith Nat.mul r sertables.tableF4.lenNums))
    (by decide +kernel) (by decide +kernel) 1200
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) dataF4.pres k k' h

/-- The E6 cutoff enumerations nest in their product order. -/
theorem belowNest_dataE6 (k k' : Nat) (h : k ≤ k') : belowNest dataE6 k k' := by
  apply belowNest_dataOf sertables.tableE6
    (sertables.adjE6.map (fun r => List.zipWith Nat.mul r sertables.tableE6.lenNums))
    (by decide +kernel) (by decide +kernel) 52000
    dataE6.cls dataE6.clsAdd dataE6.clsFloorN dataE6.pres k k' h

/-- The E7 cutoff enumerations nest in their product order. -/
theorem belowNest_dataE7 (k k' : Nat) (h : k ≤ k') : belowNest dataE7 k k' := by
  apply belowNest_dataOf sertables.tableE7
    (sertables.adjE7.map (fun r => List.zipWith Nat.mul r sertables.tableE7.lenNums))
    (by decide +kernel) (by decide +kernel) 2903040
    dataE7.cls dataE7.clsAdd dataE7.clsFloorN dataE7.pres k k' h

/-- The E8 cutoff enumerations nest in their product order. -/
theorem belowNest_dataE8 (k k' : Nat) (h : k ≤ k') : belowNest dataE8 k k' := by
  apply belowNest_dataOf sertables.tableE8
    (sertables.adjE8.map (fun r => List.zipWith Nat.mul r sertables.tableE8.lenNums))
    (by decide +kernel) (by decide +kernel) 696729600
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0) dataE8.pres k k' h

/-- The E6 highest root has the unit class at the adjugate rows'
key-three remainder family (`con:sertables`). -/
theorem clsThetaLaw_dataE6 : clsThetaLaw dataE6 := by decide +kernel

/-- The E7 highest root has the unit class at the adjugate rows'
key-two remainder family (`con:sertables`). -/
theorem clsThetaLaw_dataE7 : clsThetaLaw dataE7 := by decide +kernel

/-- The G2 interface's dual is its own padded coroot list, at the
six-letter shifted walk (`lem:memberdata`(ii)). -/
theorem dual_dataG2 (a : List Nat) : dataG2.dual a = memberdata.padN 2 a :=
  memberdata.dualM_G2 10 (ground.getAt 0 a 0) (ground.getAt 0 a 1)

/-- The G2 dual preserves the cleared Casimir at every label. -/
theorem casDualLaw_dataG2 (a : List Nat) : casDualLaw dataG2 a := by
  change dataG2.c2N (dataG2.dual a) = dataG2.c2N a
  rw [dual_dataG2]
  apply c2N_pad_dataOf sertables.tableG2 (sertables.gramRows sertables.tableG2 sertables.adjG2)
    16 (fun _ => 0) (fun _ _ => 0) (fun _ => 0) dataG2.pres a

/-- The G2 dual preserves the dimension at every label. -/
theorem dimDualLaw_dataG2 (a : List Nat) : dimDualLaw dataG2 a := by
  change dataG2.dim (dataG2.dual a) = dataG2.dim a
  rw [dual_dataG2]
  apply dim_pad_dataOf sertables.tableG2 (sertables.gramRows sertables.tableG2 sertables.adjG2)
    16 (fun _ => 0) (fun _ _ => 0) (fun _ => 0) dataG2.pres a

/-- The G2 highest root is fixed at the interface equality. -/
theorem thetaSelfDual_dataG2 : thetaSelfDual dataG2 := by
  change (memberdata.padN 2 (dataG2.dual dataG2.theta)
    == memberdata.padN 2 dataG2.theta) = true
  rw [dual_dataG2, memberdata.padN_of_length 2 _ (memberdata.padN_length 2 dataG2.theta),
    ground.listEqBeq]

/-- The F4 highest root is fixed by its table's shifted walk. -/
theorem thetaSelfDual_dataF4 : thetaSelfDual dataF4 := by decide +kernel

/-- The E6 highest root is fixed by its table's shifted walk. -/
theorem thetaSelfDual_dataE6 : thetaSelfDual dataE6 := by decide +kernel

/-- The E7 highest root is fixed by its table's shifted walk. -/
theorem thetaSelfDual_dataE7 : thetaSelfDual dataE7 := by decide +kernel

/-- The E8 highest root is fixed by its table's shifted walk. -/
theorem thetaSelfDual_dataE8 : thetaSelfDual dataE8 := by decide +kernel

end fusion

namespace memberdata

/-- C's ungraded and graded queues complete at the constructor's
stored step count, with each returned key listed once. The
distinct displayed reference includes singular seeds. -/
theorem orbit_complete_C (l : Nat) (hl : 0 < l) (v : List ground.BPair) (hv : v.length = l) :
    (orbitSet (sertables.tableC l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList (orbitSet (sertables.tableC l) (fusion.wFuel l) v))
    ∧ (orbitFam (sertables.tableC l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList ((orbitFam (sertables.tableC l) (fusion.wFuel l) v).map Prod.fst)) :=
  orbit_complete_family (sertables.tableC l) (sertables.serWeylC l v)
    (sertables.serWeylC_shape l hl v) (assembly.serWeylC_closed l v)
    (fun w hw hn i hi j hj he => assembly.reflF_C_separate l w hw hn i j hi hj he)
    (fusion.wFuel l) (fusion.serWeylC_fuel l v).2 v (sertables.serWeylC_seed l v hv hl)

/-- B's ungraded and graded queues complete at the constructor's
stored step count, with each returned key listed once, including
singular seeds. -/
theorem orbit_complete_B (l : Nat) (hl : 0 < l) (v : List ground.BPair) (hv : v.length = l) :
    (orbitSet (sertables.tableB l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList (orbitSet (sertables.tableB l) (fusion.wFuel l) v))
    ∧ (orbitFam (sertables.tableB l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList ((orbitFam (sertables.tableB l) (fusion.wFuel l) v).map Prod.fst)) :=
  orbit_complete_family (sertables.tableB l) (sertables.serWeylB l v)
    (sertables.serWeylB_shape l hl v) (assembly.serWeylB_closed l v hv)
    (fun w hw hn i hi j hj he => assembly.reflF_B_separate l w hw hn i j hi hj he)
    (fusion.wFuel l) (fusion.serWeylB_fuel l v).2 v (sertables.serWeylB_seed l v hv hl)

/-- D's ungraded and graded queues complete at the constructor's
stored step count, with each returned key listed once, including
singular seeds. -/
theorem orbit_complete_D (l : Nat) (hl : 2 ≤ l) (v : List ground.BPair) (hv : v.length = l) :
    (orbitSet (sertables.tableD l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList (orbitSet (sertables.tableD l) (fusion.wFuel l) v))
    ∧ (orbitFam (sertables.tableD l) (fusion.wFuel l) v ≠ []
      ∧ ground.distinctList ((orbitFam (sertables.tableD l) (fusion.wFuel l) v).map Prod.fst)) :=
  orbit_complete_family (sertables.tableD l) (sertables.serWeylD l v)
    (sertables.serWeylD_shape l (Nat.lt_of_lt_of_le (by decide : 0 < 2) hl) v)
    (assembly.serWeylD_closed l hl v hv)
    (fun w hw hn i hi j hj he => assembly.reflF_D_separate l w hw hn i j hi hj he)
    (fusion.wFuel l) (fusion.serWeylD_fuel l v).2 v (sertables.serWeylD_seed l v hv hl)


/-- G2's two orbit queues complete at the constructor's stored
sixteen steps, for every two-coroot seed, regular or singular. -/
theorem orbit_complete_G2 (v : List ground.BPair) (hv : v.length = 2) :
    (orbitSet sertables.tableG2 16 v ≠ [] ∧ ground.distinctList (orbitSet sertables.tableG2 16 v))
      ∧ (orbitFam sertables.tableG2 16 v ≠ []
        ∧ ground.distinctList ((orbitFam sertables.tableG2 16 v).map Prod.fst)) := by
  apply orbit_complete_family sertables.tableG2 (sertables.weylG2 v)
    (sertables.weylG2_shape v) (assembly.weylG2_closed v hv)
    (fun w hw hn i hi j hj he => assembly.reflF_G2_separate w hw hn i j hi hj he)
    16 ?_ v (sertables.weylG2_seed v hv)
  exact Nat.le_trans (ground.length_dedupF_le _)
    (by rw [ground.length_map, sertables.weylG2_length]; decide)

/-- G2's actual dominance walk completes at the stored sixteen
steps and returns a dominant key from the displayed family. -/
theorem domWalk_complete_G2 (v : List ground.BPair) (hv : v.length = 2) :
    domWalk sertables.tableG2 16 (poly.pnorm v) ∈ (sertables.weylG2 v).map Prod.fst
      ∧ memberchar.lamRead sertables.tableG2 (domWalk sertables.tableG2 16 (poly.pnorm v)) :=
  domWalk_finite_family sertables.tableG2 (sertables.weylG2 v)
    (sertables.weylG2_shape v) (assembly.weylG2_closed v hv)
    (fun w => sertables.dotB sertables.fundG2 w (sertables.rhoV sertables.tableG2))
    assembly.reflF_G2_rho_rise 16 (by rw [sertables.weylG2_length]; decide) v (sertables.weylG2_seed v hv)

/-- B's actual stored-fuel orbit has reflection-invariant
counts at every rank-width seed, including singular seeds. -/
theorem orbitSet_sym_B (l : Nat) (hl : 0 < l) (v : List ground.BPair) (hv : v.length = l) :
    memberchar.symRead (sertables.tableB l) (orbitSet (sertables.tableB l) (fusion.wFuel l) v) :=
  orbitSet_sym_of_distinct (sertables.tableB l) (fusion.wFuel l) v hv (orbit_complete_B l hl v hv).1.2

/-- The nonnegative filter of B's actual orbit is its natural
seed alone, at every label of the member's width. -/
theorem orbitSet_dom_B (l : Nat) (hl : 0 < l) (m : List Nat) (hm : m.length = l) :
    (orbitSet (sertables.tableB l) (fusion.wFuel l) (natV m)).filter
      (fun v => v.all (fun x => decide (ground.BPair.unit ≤ x))) = [natV m] := by
  have hv : (natV m).length = l := (ground.length_map ground.BPair.ofNat m).trans hm
  have hd := lamRead_natV (sertables.tableB l) m hm
  rw [natV_pnorm] at hd
  apply orbitSet_dominant_filter (sertables.tableB l) (fusion.wFuel l) m hm (orbit_complete_B l hl (natV m) hv).1
    (sertables.serWeylB l (natV m)) (sertables.serWeylB_seed l (natV m) hv hl) (assembly.serWeylB_closed l (natV m) hv)
  intro p hp hpw
  have h := sertables.serWeylB_dominant_top l hl (natV m) p.1 hv
      (sertables.serWeylB_shape l hl (natV m) p hp).1 hd.2.2 hpw p.2 hp
  rw [natV_pnorm] at h
  exact h

/-- B's full orbit-expanded family reads every dominant
multiplicity at the actual dominant table's lookup. -/
theorem multFam_dominant_B (l : Nat) (hl : 0 < l) (G : elim.Mat) (lam m : List Nat) :
    ground.countOf (natV m) (multFam (sertables.tableB l) G (fusion.wFuel l) lam)
      = lookupN m (domFam (sertables.tableB l) G (fusion.wFuel l) lam) :=
  multFam_dominant (sertables.tableB l) G (fusion.wFuel l) lam
    (fun p hp => orbitSet_dom_B l hl p.1 (domFam_width (sertables.tableB l) G (fusion.wFuel l) lam p hp)) m

/-- C's actual stored-fuel orbit has reflection-invariant
counts at every rank-width seed, including singular seeds. -/
theorem orbitSet_sym_C (l : Nat) (hl : 0 < l) (v : List ground.BPair) (hv : v.length = l) :
    memberchar.symRead (sertables.tableC l) (orbitSet (sertables.tableC l) (fusion.wFuel l) v) :=
  orbitSet_sym_of_distinct (sertables.tableC l) (fusion.wFuel l) v hv (orbit_complete_C l hl v hv).1.2

/-- The nonnegative filter of C's actual orbit is its natural
seed alone, at every label of the member's width. -/
theorem orbitSet_dom_C (l : Nat) (hl : 0 < l) (m : List Nat) (hm : m.length = l) :
    (orbitSet (sertables.tableC l) (fusion.wFuel l) (natV m)).filter
      (fun v => v.all (fun x => decide (ground.BPair.unit ≤ x))) = [natV m] := by
  have hv : (natV m).length = l := (ground.length_map ground.BPair.ofNat m).trans hm
  have hd := lamRead_natV (sertables.tableC l) m hm
  rw [natV_pnorm] at hd
  apply orbitSet_dominant_filter (sertables.tableC l) (fusion.wFuel l) m hm (orbit_complete_C l hl (natV m) hv).1
    (sertables.serWeylC l (natV m)) (sertables.serWeylC_seed l (natV m) hv hl) (assembly.serWeylC_closed l (natV m))
  intro p hp hpw
  have h := sertables.serWeylC_dominant_top l hl (natV m) p.1 hv
      (sertables.serWeylC_shape l hl (natV m) p hp).1 hd.2.2 hpw p.2 hp
  rw [natV_pnorm] at h
  exact h

/-- C's full orbit-expanded family reads every dominant
multiplicity at the actual dominant table's lookup. -/
theorem multFam_dominant_C (l : Nat) (hl : 0 < l) (G : elim.Mat) (lam m : List Nat) :
    ground.countOf (natV m) (multFam (sertables.tableC l) G (fusion.wFuel l) lam)
      = lookupN m (domFam (sertables.tableC l) G (fusion.wFuel l) lam) :=
  multFam_dominant (sertables.tableC l) G (fusion.wFuel l) lam
    (fun p hp => orbitSet_dom_C l hl p.1 (domFam_width (sertables.tableC l) G (fusion.wFuel l) lam p hp)) m

/-- D's actual stored-fuel orbit has reflection-invariant
counts at every rank-width seed, including singular seeds. -/
theorem orbitSet_sym_D (l : Nat) (hl : 2 ≤ l) (v : List ground.BPair) (hv : v.length = l) :
    memberchar.symRead (sertables.tableD l) (orbitSet (sertables.tableD l) (fusion.wFuel l) v) :=
  orbitSet_sym_of_distinct (sertables.tableD l) (fusion.wFuel l) v hv (orbit_complete_D l hl v hv).1.2

/-- The dominant filter of D's actual orbit is its natural
seed alone, including repeated coordinate magnitudes. -/
theorem orbitSet_dom_D (l : Nat) (hl : 2 ≤ l) (m : List Nat) (hm : m.length = l) :
    (orbitSet (sertables.tableD l) (fusion.wFuel l) (natV m)).filter
      (fun v => v.all (fun x => decide (ground.BPair.unit ≤ x))) = [natV m] := by
  have hv : (natV m).length = l := (ground.length_map ground.BPair.ofNat m).trans hm
  have hd := lamRead_natV (sertables.tableD l) m hm
  rw [natV_pnorm] at hd
  apply orbitSet_dominant_filter (sertables.tableD l) (fusion.wFuel l) m hm (orbit_complete_D l hl (natV m) hv).1
    (sertables.serWeylD l (natV m)) (sertables.serWeylD_seed l (natV m) hv hl) (assembly.serWeylD_closed l hl (natV m) hv)
  intro p hp hpw
  have h := sertables.serWeylD_dominant_top l hl (natV m) p.1 hv
      (sertables.serWeylD_shape l (Nat.lt_of_lt_of_le (by decide +kernel : 0 < 2) hl) (natV m) p hp).1 hd.2.2 hpw p.2 hp
  rw [natV_pnorm] at h
  exact h

/-- D's full orbit-expanded family reads every dominant
multiplicity at the actual dominant table's lookup. -/
theorem multFam_dominant_D (l : Nat) (hl : 2 ≤ l) (G : elim.Mat) (lam m : List Nat) :
    ground.countOf (natV m) (multFam (sertables.tableD l) G (fusion.wFuel l) lam)
      = lookupN m (domFam (sertables.tableD l) G (fusion.wFuel l) lam) :=
  multFam_dominant (sertables.tableD l) G (fusion.wFuel l) lam
    (fun p hp => orbitSet_dom_D l hl p.1 (domFam_width (sertables.tableD l) G (fusion.wFuel l) lam p hp)) m

/-- G2's actual stored-fuel orbit has reflection-invariant
counts at every rank-width seed, including singular seeds. -/
theorem orbitSet_sym_G2 (v : List ground.BPair) (hv : v.length = 2) :
    memberchar.symRead sertables.tableG2 (orbitSet sertables.tableG2 16 v) :=
  orbitSet_sym_of_distinct sertables.tableG2 16 v hv (orbit_complete_G2 v hv).1.2

/-- The nonnegative filter of G2's actual orbit is its natural
seed alone, at every label of the member's width. -/
theorem orbitSet_dom_G2 (m : List Nat) (hm : m.length = 2) :
    (orbitSet sertables.tableG2 16 (natV m)).filter
      (fun v => v.all (fun x => decide (ground.BPair.unit ≤ x))) = [natV m] := by
  have hv : (natV m).length = 2 := (ground.length_map ground.BPair.ofNat m).trans hm
  have hd := lamRead_natV sertables.tableG2 m hm
  rw [natV_pnorm] at hd
  apply orbitSet_dominant_filter sertables.tableG2 16 m hm (orbit_complete_G2 (natV m) hv).1
    (sertables.weylG2 (natV m)) (sertables.weylG2_seed (natV m) hv) (assembly.weylG2_closed (natV m) hv)
  intro p hp hpw
  have h := sertables.weylG2_dominant_top (natV m) p.1 hv hd.2.2 hpw p.2 hp
  rw [natV_pnorm] at h
  exact h

/-- G2's full orbit-expanded family reads every dominant
multiplicity at the actual dominant table's lookup. -/
theorem multFam_dominant_G2 (G : elim.Mat) (lam m : List Nat) :
    ground.countOf (natV m) (multFam sertables.tableG2 G 16 lam)
      = lookupN m (domFam sertables.tableG2 G 16 lam) :=
  multFam_dominant sertables.tableG2 G 16 lam
    (fun p hp => orbitSet_dom_G2 p.1 (domFam_width sertables.tableG2 G 16 lam p hp)) m

/-- G2's computed full multiplicity family equals every supported
invariant trace family with its top count one, at every label and
every content. Its orbit reads hold at the actual stored fuel. -/
theorem multFam_read_G2 (lam : List Nat) (hlam : lam.length = 2)
    (W : List (List ground.BPair × Bool)) (L : List (List ground.BPair))
    (hmsh : memberchar.mShapeRead sertables.tableG2 L)
    (hsym : memberchar.symRead sertables.tableG2 L) (wits : List (List Nat))
    (hsupp : memberchar.supportRead sertables.tableG2 L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV sertables.tableG2, false) ∈ W)
    (hrec : memberchar.recRead sertables.tableG2 sertables.fundG2 W L (poly.pnorm (natV lam)))
    (v : List ground.BPair) :
    ground.countOf v (multFam sertables.tableG2 sertables.fundG2.gram 16 lam) = ground.countOf v L := by
  apply multFam_read sertables.tableG2 sertables.fundG2.gram 16 lam sertables.reflSquareRead_G2 _ L hmsh hsym
    (domFam_lookup_G2 lam hlam W L hmsh hsym wits hsupp htop hseed hrec) _ _ v
  · intro w hw he
    have h := (domWalk_complete_G2 w hw).2.1
    rw [he] at h
    exact Nat.noConfusion h
  · intro p hp
    exact orbitSet_sym_G2 (natV p.1) ((ground.length_map ground.BPair.ofNat p.1).trans
      (domFam_width sertables.tableG2 sertables.fundG2.gram 16 lam p hp))
  · intro p hp
    exact orbitSet_dom_G2 p.1 (domFam_width sertables.tableG2 sertables.fundG2.gram 16 lam p hp)

/-- G2's actual multiplicity producer satisfies the support,
top and trace reads of its block family, with the support
witnesses computed by the Cartan decoder at every occurrence. -/
theorem multFam_reads_G2 (lam : List Nat) (hlam : lam.length = 2)
    (W : List (List ground.BPair × Bool)) (L : List (List ground.BPair))
    (hmsh : memberchar.mShapeRead sertables.tableG2 L)
    (hsym : memberchar.symRead sertables.tableG2 L) (wits : List (List Nat))
    (hsupp : memberchar.supportRead sertables.tableG2 L wits (natV lam))
    (htop : memberchar.topRead L (natV lam))
    (hseed : (sertables.rhoV sertables.tableG2, false) ∈ W)
    (hrec : memberchar.recRead sertables.tableG2 sertables.fundG2 W L (poly.pnorm (natV lam))) :
    memberchar.mShapeRead sertables.tableG2 (multFam sertables.tableG2 sertables.fundG2.gram 16 lam)
      ∧ memberchar.symRead sertables.tableG2 (multFam sertables.tableG2 sertables.fundG2.gram 16 lam)
      ∧ memberchar.supportRead sertables.tableG2 (multFam sertables.tableG2 sertables.fundG2.gram 16 lam)
        ((multFam sertables.tableG2 sertables.fundG2.gram 16 lam).map (foldWits sertables.tableG2 (natV lam))) (natV lam)
      ∧ memberchar.topRead (multFam sertables.tableG2 sertables.fundG2.gram 16 lam) (natV lam)
      ∧ memberchar.recRead sertables.tableG2 sertables.fundG2 W
        (multFam sertables.tableG2 sertables.fundG2.gram 16 lam) (poly.pnorm (natV lam)) := by
  have hc := multFam_read_G2 lam hlam W L hmsh hsym wits hsupp htop hseed hrec
  refine ⟨multFam_shape sertables.tableG2 sertables.fundG2.gram 16 lam,
    memberchar.symRead_counts sertables.tableG2 _ L hc hsym, ?_, ?_,
    memberchar.recRead_counts sertables.tableG2 sertables.fundG2 W _ L _ hc hrec⟩
  · exact supportRead_counts sertables.tableG2 sertables.cartanSolve_G2.1
      sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2 _ L wits (natV lam)
      ((ground.length_map ground.BPair.ofNat lam).trans hlam) (natV_pnorm lam) hc hmsh hsupp
  · exact (hc (natV lam)).trans htop

/-- Every F4 coroot key completes the actual dominance walk
at the constructor's stored step count, by the positive-root bound. -/
theorem domWalk_complete_F4 (v : List ground.BPair) (hv : v.length = 4) :
    memberchar.lamRead sertables.tableF4 (domWalk sertables.tableF4 1200 (poly.pnorm v)) := by
  apply domWalk_root_complete sertables.tableF4 sertables.fundF4
    sertables.fundShape_F4 sertables.gramRead_F4 sertables.simplePosRead_F4
    sertables.reflSquareRead_F4 sertables.permSquareRead_F4 sertables.permImageRead_F4
    sertables.rhoDotRead_F4 sertables.reflFormRead_F4 1200 (by decide +kernel) v hv

/-- Every E6 coroot key completes the actual dominance walk
at the constructor's stored step count, by the positive-root bound. -/
theorem domWalk_complete_E6 (v : List ground.BPair) (hv : v.length = 6) :
    memberchar.lamRead sertables.tableE6 (domWalk sertables.tableE6 52000 (poly.pnorm v)) := by
  apply domWalk_root_complete sertables.tableE6 sertables.fundE6
    sertables.fundShape_E6 sertables.gramRead_E6 sertables.simplePosRead_E6
    sertables.reflSquareRead_E6 sertables.permSquareRead_E6 sertables.permImageRead_E6
    sertables.rhoDotRead_E6 sertables.reflFormRead_E6 52000 (by decide +kernel) v hv

/-- Every E7 coroot key completes the actual dominance walk
at the constructor's stored step count, by the positive-root bound. -/
theorem domWalk_complete_E7 (v : List ground.BPair) (hv : v.length = 7) :
    memberchar.lamRead sertables.tableE7 (domWalk sertables.tableE7 2903040 (poly.pnorm v)) := by
  apply domWalk_root_complete sertables.tableE7 sertables.fundE7
    sertables.fundShape_E7 sertables.gramRead_E7 sertables.simplePosRead_E7
    sertables.reflSquareRead_E7 sertables.permSquareRead_E7 sertables.permImageRead_E7
    sertables.rhoDotRead_E7 sertables.reflFormRead_E7 2903040 (by decide +kernel) v hv

/-- Every E8 coroot key completes the actual dominance walk
at the constructor's stored step count, by the positive-root bound. -/
theorem domWalk_complete_E8 (v : List ground.BPair) (hv : v.length = 8) :
    memberchar.lamRead sertables.tableE8 (domWalk sertables.tableE8 696729600 (poly.pnorm v)) := by
  apply domWalk_root_complete sertables.tableE8 sertables.fundE8
    sertables.fundShape_E8 sertables.gramRead_E8 sertables.simplePosRead_E8
    sertables.reflSquareRead_E8 sertables.permSquareRead_E8 sertables.permImageRead_E8
    sertables.rhoDotRead_E8 sertables.reflFormRead_E8 696729600 (by decide +kernel) v hv

/-- G2's displayed word image joins its dominant seed by a
natural simple fold. The coefficients are the margins of the
adjugate gap matrix applied to the seed. -/
theorem weylG2_foldTest (v : List ground.BPair) (hv : v.length = 2)
    (hp : ∀ i, i < 2 → ground.BPair.unit ≤ ground.getAt ground.BPair.unit v i)
    (p : List ground.BPair × Bool) (hm : p ∈ sertables.weylG2 v) :
    foldTest sertables.tableG2 (elim.vecAdd v (poly.neg p.1)) = true := by
  obtain ⟨j, hj, he⟩ := ground.mem_map_of _ _ p hm
  have hj' := ground.ltOfMemRange hj
  have hkey : p.1 = poly.pnorm (elim.matVec (sertables.weylMatG2 j) v) := (congrArg Prod.fst he).symm
  have hw := sertables.weylMatG2_shape j hj'
  have hK := sertables.weylFoldG2_read j hj'
  let K := sertables.weylFoldG2 j
  let u := elim.matVec K v
  let c := natsOf u
  have hKl : K.length = 2 := elim.sqAt_len hK.1
  have hKr : elim.rowsLen 2 K := elim.rowsLen_of_sqAt hK.1
  have hu : u.length = 2 := (elim.matVec_length K v).trans hKl
  have hc : c.length = 2 := (ground.length_map ground.BPair.marginN u).trans hu
  have hup : ∀ i, i < u.length → ground.BPair.unit ≤ ground.getAt ground.BPair.unit u i := by
    intro i hi
    rw [hu] at hi
    rw [elim.getAt_matVec K v i (by rw [hKl]; exact hi)]
    apply ground.leB_congr_right (ground.BPair.oneValue_symm (elim.dotN_read _ _))
    apply elim.dotP_unitLe
    intro q hq
    rw [elim.rowsLen_getAt K i hKr (by rw [hKl]; exact hi)] at hq
    exact ground.unitLeMul (hK.2.1 i hi q hq) (hp q hq)
  have hT : elim.sqAt (elim.transposeM sertables.tableG2.cartan) 2 := by decide +kernel
  have hTr := elim.rowsLen_of_sqAt hT
  have hfold : poly.oneValue (assembly.cartanFold sertables.tableG2 c)
      (elim.matVec (elim.matMul (elim.transposeM sertables.tableG2.cartan) K) v) :=
    poly.oneValue_trans (assembly.cartanFold_matVec sertables.tableG2 sertables.cartanSolve_G2.1 c hc)
      (poly.oneValue_trans (elim.matVec_congr _ _ _ (natV_natsOf u hup))
        (elim.matVec_comp _ K v 2 hKr hv (by rw [hKl]; exact hTr)))
  have hmul := elim.sqAt_matMul _ _ hT hK.1
  have hjoin : poly.oneValue (elim.vecAdd p.1 (assembly.cartanFold sertables.tableG2 c)) v := by
    rw [hkey]
    refine poly.oneValue_trans (elim.vecAdd_congr2 _ _ _ _ (poly.pnorm_length _)
      ((assembly.cartanFold_length sertables.tableG2 sertables.cartanSolve_G2.1 c).trans
        ((elim.matVec_length _ v).trans (elim.sqAt_len hmul)).symm)
      (poly.pnorm_oneValue _) hfold) ?_
    exact poly.oneValue_trans (poly.oneValue_symm (elim.matVec_add_free 2 _ _ v hw.2 (elim.rowsLen_of_sqAt hmul)))
      (poly.oneValue_trans (elim.matVec_matOne _ _ v hK.2.2) (elim.matVec_idMat 2 v hv))
  have hpw : p.1.length = 2 := (sertables.weylG2_shape v p hm).1
  apply foldTest_join sertables.tableG2 sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1
    sertables.cartanSolve_G2.2.2 v p.1 hv hpw c hc
  exact poly.pnorm_congr _ _ ((elim.length_vecAdd _ _ 2 hpw
    (assembly.cartanFold_length sertables.tableG2 sertables.cartanSolve_G2.1 c)).trans hv.symm) hjoin

/-- The actual G2 graded queue has decoded support witnesses at
every strictly dominant seed and every completed stored orbit. -/
theorem orbitFam_dom_G2 (v : List ground.BPair) (hv : v.length = 2)
    (hp : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit v i) :
    assembly.wDomAt sertables.tableG2 (orbitFam sertables.tableG2 16 v)
      ((orbitFam sertables.tableG2 16 v).map (fun p => foldWits sertables.tableG2 v p.1)) (poly.pnorm v) := by
  apply wDomAt_foldWits sertables.tableG2 sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1
    sertables.cartanSolve_G2.2.2 _ (orbitFam_shape sertables.tableG2 16 v hv) v hv
  intro p hm
  exact weylG2_foldTest v hv (fun i hi => ground.leB_of_lt (hp i hi)) p
    (orbitFam_sub sertables.tableG2 (sertables.weylG2 v) (sertables.weylG2_shape v)
      (assembly.weylG2_close v hv hp) 16 v (sertables.weylG2_seed v hv) p hm)

/-- Every dominant key in the actual regular G2 queue is its
seed's canonical key, including the weak chamber's boundary. -/
theorem orbitFam_dominant_key_G2 (v : List ground.BPair) (hv : v.length = 2)
    (hp : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit v i)
    (p : List ground.BPair × Bool) (hm : p ∈ orbitFam sertables.tableG2 16 v)
    (hpos : ∀ i, i < 2 → ground.BPair.unit ≤ ground.getAt ground.BPair.unit p.1 i) :
    p.1 = poly.pnorm v := by
  have hsub := orbitFam_sub sertables.tableG2 (sertables.weylG2 v) (sertables.weylG2_shape v)
    (assembly.weylG2_close v hv hp) 16 v (sertables.weylG2_seed v hv) p hm
  have he := sertables.weylG2_dominant_top v p.1 hv (fun i hi => ground.leB_of_lt (hp i hi))
    hpos p.2 hsub
  rw [(orbitFam_shape sertables.tableG2 16 v hv p hm).2] at he
  exact he

/-- Every strictly dominant key of the actual G2 queue is its
seed's canonical key, so the shifted alternant's regular read holds. -/
theorem orbitFam_reg_G2 (v : List ground.BPair) (hv : v.length = 2)
    (hp : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit v i) :
    assembly.wRegRead sertables.tableG2 (orbitFam sertables.tableG2 16 v) (poly.pnorm v) := by
  intro p hm hpos hne
  exact False.elim (hne (orbitFam_dominant_key_G2 v hv hp p hm
    (fun i hi => ground.leB_of_lt (hpos i hi))))

/-- G2's actual queue at a strictly dominant seed satisfies
the shape, graded closure and seed-count reads at stored fuel. -/
theorem orbitFam_reads_G2 (v : List ground.BPair) (hv : v.length = 2)
    (hp : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit v i) :
    sertables.wShapeRead sertables.tableG2 (orbitFam sertables.tableG2 16 v)
      ∧ assembly.wCloseRead sertables.tableG2 (orbitFam sertables.tableG2 16 v)
      ∧ assembly.wTopAt (orbitFam sertables.tableG2 16 v) (poly.pnorm v) := by
  apply orbitFam_reads_family sertables.tableG2 (sertables.weylG2 v)
    (sertables.weylG2_shape v) (assembly.weylG2_close v hv hp) (sertables.weylG2_regular v hv hp)
    (fun w hw hn i hi j hj he => assembly.reflF_G2_separate w hw hn i j hi hj he) 16 _ v
    (sertables.weylG2_seed v hv)
  exact Nat.le_trans (ground.length_dedupF_le _) (by rw [ground.length_map, sertables.weylG2_length]; decide +kernel)

/-- G2's actual regular graded queue has the displayed Weyl
family's count at every key and side, independently of its order. -/
theorem orbitFam_counts_G2 (v : List ground.BPair) (hv : v.length = 2)
    (hp : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit v i)
    (p : List ground.BPair × Bool) :
    ground.countOf p (orbitFam sertables.tableG2 16 v)
      = ground.countOf p (sertables.weylG2 v) := by
  have hr := orbitFam_reads_G2 v hv hp
  have hd := sertables.weylG2_regular v hv hp
  have hseed := sertables.weylG2_seed v hv
  have ht : assembly.wTopAt (sertables.weylG2 v) (poly.pnorm v) := by
    refine ⟨ground.countOf_distinct_map Prod.fst _ hd _ hseed, ?_⟩
    apply ground.countOf_zero_of_not_mem
    intro hodd
    have he := ground.map_inj_distinct Prod.fst _ hd _ _ hodd hseed rfl
    exact Bool.noConfusion (congrArg Prod.snd he)
  have hpin (q : List ground.BPair × Bool) (hq : q ∈ sertables.weylG2 v)
      (hpos : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit q.1 i) :
      q.1 = poly.pnorm v := by
    have he := sertables.weylG2_dominant_top v q.1 hv (fun i hi => ground.leB_of_lt (hp i hi))
      (fun i hi => ground.leB_of_lt (hpos i hi)) q.2 hq
    rw [(sertables.weylG2_shape v q hq).2] at he
    exact he
  apply regular_counts sertables.tableG2 sertables.reflSquareRead_G2 16 _ _ _
    hr.1 (sertables.weylG2_shape v) (orbit_complete_G2 v hv).2.2 hd
    hr.2.1 (assembly.weylG2_close v hv hp) (poly.pnorm v) hr.2.2 ht _ hpin p.1 p.2
  · intro w hw he
    have hl := (domWalk_complete_G2 w hw).2.1
    rw [he] at hl
    exact Nat.noConfusion hl
  · intro q hq hpos
    exact orbitFam_dominant_key_G2 v hv hp q hq (fun i hi => ground.leB_of_lt (hpos i hi))

/-- G2's actual stored queues exchange principal degrees at
their seeds' two form slots, the reversed-word count identity. -/
theorem orbitFam_dmap_exchange_G2 (x y : List ground.BPair)
    (hx : x.length = 2) (hy : y.length = 2)
    (hpx : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit x i)
    (hpy : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit y i)
    (p : Nat × Bool) :
    ground.countOf p (weyldim.dmap sertables.fundG2 (sertables.dotB sertables.fundG2 x y)
      y (orbitFam sertables.tableG2 16 x))
      = ground.countOf p (weyldim.dmap sertables.fundG2 (sertables.dotB sertables.fundG2 y x)
        x (orbitFam sertables.tableG2 16 y)) := by
  rw [weyldim.dmap_counts _ _ _ _ _ (orbitFam_counts_G2 x hx hpx) p,
    weyldim.dmap_counts _ _ _ _ _ (orbitFam_counts_G2 y hy hpy) p]
  exact weyldim.dmap_exchange_G2 x y hx hy p

/-- G2's computed shifted orbit has all five alternant reads
at every natural label, with its support witnesses decoded by
the actual Cartan solve. -/
theorem orbitFam_character_G2 (b : List Nat) (hb : b.length = 2) :
    sertables.wShapeRead sertables.tableG2 (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
      ∧ assembly.wCloseRead sertables.tableG2 (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
      ∧ assembly.wDomAt sertables.tableG2 (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
        ((orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)).map
          (fun p => foldWits sertables.tableG2 (shiftV sertables.tableG2 b) p.1)) (shiftV sertables.tableG2 b)
      ∧ assembly.wTopAt (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)) (shiftV sertables.tableG2 b)
      ∧ assembly.wRegRead sertables.tableG2 (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
        (shiftV sertables.tableG2 b) := by
  have hv := shiftV_length sertables.tableG2 b hb
  have hp := shiftV_pos sertables.tableG2 b hb
  have hr := orbitFam_reads_G2 _ hv hp
  have hd := orbitFam_dom_G2 _ hv hp
  have hreg := orbitFam_reg_G2 _ hv hp
  have hn : poly.pnorm (shiftV sertables.tableG2 b) = shiftV sertables.tableG2 b := poly.pnorm_pnorm _
  rw [hn] at hr hd hreg
  exact ⟨hr.1, hr.2.1, hd, hr.2.2, hreg⟩

/-- At a natural shifted target the regular G2 queue reads the
even singleton at its own shifted seed, and the vacant count at
all other dominant labels. -/
theorem orbitFam_dominant_count_G2 (a c : List Nat) (ha : a.length = 2) (hc : c.length = 2)
    (side : Bool) :
    assembly.wCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 a))
      (shiftV sertables.tableG2 c) side = if c = a then (if side then 0 else 1) else 0 := by
  have hv := shiftV_length sertables.tableG2 a ha
  have hp := shiftV_pos sertables.tableG2 a ha
  have hw := orbitFam_character_G2 a ha
  have hpin (p : List ground.BPair × Bool)
      (hm : p ∈ orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 a))
      (hpos : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit p.1 i) :
      p.1 = shiftV sertables.tableG2 a := by
    have he := orbitFam_dominant_key_G2 _ hv hp p hm (fun i hi => ground.leB_of_lt (hpos i hi))
    rw [show poly.pnorm (shiftV sertables.tableG2 a) = shiftV sertables.tableG2 a
      from poly.pnorm_pnorm _] at he
    exact he
  rw [assembly.wCount_dominant sertables.tableG2 _ hw.1 (orbit_complete_G2 _ hv).2.2 hw.2.1
    (shiftV sertables.tableG2 a) hw.2.2.2.1 hpin (shiftV sertables.tableG2 c)
    (fun i hi => ground.leB_of_lt (shiftV_pos sertables.tableG2 c hc i hi)) side]
  by_cases he : c = a
  · rw [if_pos he, he, if_pos rfl]
  · rw [if_neg he, if_neg (fun h => he (shiftV_inj sertables.tableG2 c a hc ha h))]

/-- The G2 character identity uses the actual stored-fuel rho
and shifted orbits at every label. Its only family inputs are
the block's shape, symmetry, support, top and trace reads. -/
theorem identityRead_G2 (b : List Nat) (hb : b.length = 2)
    (L : List (List ground.BPair)) (wits : List (List Nat))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (hd : memberchar.supportRead sertables.tableG2 L wits (natV b))
    (ht : memberchar.topRead L (natV b))
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L (natV b))
    (y : List ground.BPair) :
    memberchar.identityAt (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L
      (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)) y := by
  have hzero := orbitFam_character_G2 [0, 0] rfl
  have hshift := orbitFam_character_G2 b hb
  have hlam := lamRead_natV sertables.tableG2 b hb
  rw [natV_pnorm] at hlam
  apply memberchar.identityRead sertables.tableG2 sertables.fundG2 _ _ L wits (natV b) _ _
    sertables.fundShape_G2 sertables.gramRead_G2 sertables.gramSymRead_G2 sertables.simplePosRead_G2
    sertables.reflSquareRead_G2 sertables.permSquareRead_G2 sertables.permImageRead_G2
    sertables.rhoDotRead_G2 sertables.reflFormRead_G2
    hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2.1 hm hs hd ht hlam
    hshift.1 hshift.2.1 hshift.2.2.1 hshift.2.2.2.1 hshift.2.2.2.2 hr y

/-- G2's actual multiplicity producer satisfies the character
identity whenever the mathematical block family has the trace
reads. The two alternants are the actual stored-fuel queues. -/
theorem multFam_identity_G2 (b : List Nat) (hb : b.length = 2)
    (L : List (List ground.BPair)) (wits : List (List Nat))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (hd : memberchar.supportRead sertables.tableG2 L wits (natV b))
    (ht : memberchar.topRead L (natV b))
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L (natV b))
    (y : List ground.BPair) :
    memberchar.identityAt (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
      (multFam sertables.tableG2 sertables.fundG2.gram 16 b)
      (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)) y := by
  have hseed : (sertables.rhoV sertables.tableG2, false) ∈ orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2) := by
    have h := orbitFam_seed sertables.tableG2 16 (sertables.rhoV sertables.tableG2)
      (orbit_complete_G2 _ rfl).2.1
    rw [assembly.pnorm_rhoV] at h
    exact h
  have hrec : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L (poly.pnorm (natV b)) := by
    rw [natV_pnorm]; exact hr
  have h := multFam_reads_G2 b hb _ L hm hs wits hd ht hseed hrec
  apply identityRead_G2 b hb _ _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 _ y
  have h' := h.2.2.2.2
  rw [natV_pnorm] at h'
  exact h'

/-- G2's Weyl product is exactly the count of a mathematical
block family at every label. The principal degrees use the actual
stored queues and exchange at the reversed words. -/
theorem dimM_family_G2 (lam : List Nat) (hlam : lam.length = 2)
    (L : List (List ground.BPair)) (wits : List (List Nat))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (hd : memberchar.supportRead sertables.tableG2 L wits (natV lam))
    (ht : memberchar.topRead L (natV lam))
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L (natV lam)) :
    dimM sertables.tableG2 lam = L.length := by
  have hz := orbitFam_character_G2 [0, 0] rfl
  have hzero : shiftV sertables.tableG2 [0, 0] = sertables.rhoV sertables.tableG2 := rfl
  rw [hzero] at hz
  have hzt : assembly.wTopRead sertables.tableG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) := by
    change assembly.wTopAt _ (poly.pnorm (sertables.rhoV sertables.tableG2))
    rw [assembly.pnorm_rhoV]
    exact hz.2.2.2.1
  have hl := orbitFam_character_G2 lam hlam
  have hnat := lamRead_natV sertables.tableG2 lam hlam
  rw [natV_pnorm] at hnat
  have hp : ∀ i, i < 2 → ground.BPair.unit < ground.getAt ground.BPair.unit
      (sertables.rhoV sertables.tableG2) i := by decide +kernel
  have hw : ∀ p ∈ sertables.weylG2 (sertables.rhoV sertables.tableG2),
      ground.BPair.unit ≤ sertables.dotB sertables.fundG2 (sertables.rhoV sertables.tableG2)
        (sertables.rhoV sertables.tableG2) + sertables.dotB sertables.fundG2 p.1
          (sertables.rhoV sertables.tableG2) := by decide +kernel
  have hex := orbitFam_dmap_exchange_G2 (shiftV sertables.tableG2 lam)
    (sertables.rhoV sertables.tableG2) (shiftV_length sertables.tableG2 lam hlam) rfl
    (shiftV_pos sertables.tableG2 lam hlam) hp
  have hdim := weyldim.memberRead sertables.tableG2 sertables.fundG2
    _ _ L wits (natV lam) _ _
    sertables.fundShape_G2 sertables.gramRead_G2 sertables.gramSymRead_G2 sertables.simplePosRead_G2
    sertables.reflSquareRead_G2 sertables.permSquareRead_G2 sertables.permImageRead_G2
    sertables.rhoDotRead_G2 sertables.reflFormRead_G2 hz.1 hz.2.1 hz.2.2.1 hzt
    hm hs hd ht hnat hl.1 hl.2.1 hl.2.2.1 hl.2.2.2.1 hl.2.2.2.2 hr
    (fun p hp' => hw p (orbitFam_sub sertables.tableG2 _ (sertables.weylG2_shape _)
      (assembly.weylG2_close _ rfl hp) 16 _ (sertables.weylG2_seed _ rfl) p hp'))
    (memberchar.supportRead_shift_G2 L wits (natV lam) hnat.1 hm hs hd)
    (fun p _ => hex p) (fun p _ => hex p)
  have hgap (v : List Nat) (hv : v.length = 2) (j : Nat) (hj : j < 6) :
      ground.BPair.marginN (sertables.dotB sertables.fundG2 (sertables.posCorootV sertables.tableG2 j) (natV v))
        = serstable.gapAt sertables.tableG2 v j := by
    unfold natV
    rw [ground.BPair.marginN_congr (serstable.gapAt_dotB sertables.tableG2 sertables.fundG2
      sertables.fundShape_G2 sertables.gramRead_G2 j hj v hv), ground.BPair.marginN_ofNat]
    exact Nat.one_mul _
  have hrho : sertables.rhoV sertables.tableG2 = natV [1, 1] := rfl
  have hshift : weyldim.lamrho sertables.tableG2 (natV lam)
      = natV (lam.map (fun n => n + 1)) := shiftV_natV sertables.tableG2 lam hlam
  rw [hrho, hshift] at hdim
  have hnroots : sertables.tableG2.posFolds.length = 6 := rfl
  rw [hnroots] at hdim
  have hprod (v : List Nat) (hv : v.length = 2) :
      ground.famFold Nat.mul 1
        (fun j => ground.BPair.marginN (sertables.dotB sertables.fundG2
          (sertables.posCorootV sertables.tableG2 j) (natV v))) (List.range 6)
        = ground.prodOver (serstable.gapAt sertables.tableG2 v) (List.range 6) :=
    ground.famFold_congr_members Nat.mul 1 _ _ (List.range 6)
      (fun j hj => hgap v hv j (ground.ltOfMem hj))
  rw [hprod [1, 1] rfl, hprod _ ((ground.length_map _ lam).trans hlam)] at hdim
  unfold dimM
  change ground.prodOver (serstable.gapAt sertables.tableG2 (lam.map (fun n => n + 1))) (List.range 6)
    / ground.prodOver (serstable.gapAt sertables.tableG2 [1, 1]) (List.range 6) = L.length
  rw [← hdim]
  exact ground.divMulSelf _ _ (by decide +kernel)

/-- The actual G2 multiplicity family's count is its Weyl-product
dimension whenever the mathematical block has its stated reads. -/
theorem dimM_multFam_G2 (lam : List Nat) (hlam : lam.length = 2)
    (L : List (List ground.BPair)) (wits : List (List Nat))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (hd : memberchar.supportRead sertables.tableG2 L wits (natV lam))
    (ht : memberchar.topRead L (natV lam))
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L (natV lam)) :
    dimM sertables.tableG2 lam = (multFam sertables.tableG2 sertables.fundG2.gram 16 lam).length := by
  have hseed := orbitFam_seed sertables.tableG2 16 (sertables.rhoV sertables.tableG2)
    (orbit_complete_G2 _ rfl).2.1
  rw [assembly.pnorm_rhoV] at hseed
  have hrec : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L (poly.pnorm (natV lam)) := by
    rw [natV_pnorm]; exact hr
  have hc := multFam_read_G2 lam hlam _ L hm hs wits hd ht hseed hrec
  exact (dimM_family_G2 lam hlam L wits hm hs hd ht hr).trans
    (ground.length_eq_of_countOf _ L hc).symm

/-- G2's actual Weyl-product dimension is positive at every
natural coroot label of the member's width. -/
theorem dimM_pos_G2 (m : List Nat) (hm : m.length = 2) :
    0 < dimM sertables.tableG2 m :=
  dimM_pos sertables.tableG2 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableG2 sertables.fundG2
      sertables.fundShape_G2 sertables.gramRead_G2 sertables.rhoDotRead_G2) m hm

/-- G2's unit dimension is one at its displayed root table. -/
theorem dimM_unit_G2 : dimM sertables.tableG2 (List.replicate 2 0) = 1 :=
  dimM_unit sertables.tableG2 (serstable.gapAt_rho_pos_of_fund sertables.tableG2 sertables.fundG2
      sertables.fundShape_G2 sertables.gramRead_G2 sertables.rhoDotRead_G2)

/-- F4's actual Weyl-product dimension is positive at every
natural coroot label of the member's width. -/
theorem dimM_pos_F4 (m : List Nat) (hm : m.length = 4) :
    0 < dimM sertables.tableF4 m :=
  dimM_pos sertables.tableF4 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableF4 sertables.fundF4
      sertables.fundShape_F4 sertables.gramRead_F4 sertables.rhoDotRead_F4) m hm

/-- F4's unit dimension is one at its displayed root table. -/
theorem dimM_unit_F4 : dimM sertables.tableF4 (List.replicate 4 0) = 1 :=
  dimM_unit sertables.tableF4 (serstable.gapAt_rho_pos_of_fund sertables.tableF4 sertables.fundF4
      sertables.fundShape_F4 sertables.gramRead_F4 sertables.rhoDotRead_F4)

/-- E6's actual Weyl-product dimension is positive at every
natural coroot label of the member's width. -/
theorem dimM_pos_E6 (m : List Nat) (hm : m.length = 6) :
    0 < dimM sertables.tableE6 m :=
  dimM_pos sertables.tableE6 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableE6 sertables.fundE6
      sertables.fundShape_E6 sertables.gramRead_E6 sertables.rhoDotRead_E6) m hm

/-- E6's unit dimension is one at its displayed root table. -/
theorem dimM_unit_E6 : dimM sertables.tableE6 (List.replicate 6 0) = 1 :=
  dimM_unit sertables.tableE6 (serstable.gapAt_rho_pos_of_fund sertables.tableE6 sertables.fundE6
      sertables.fundShape_E6 sertables.gramRead_E6 sertables.rhoDotRead_E6)

/-- E7's actual Weyl-product dimension is positive at every
natural coroot label of the member's width. -/
theorem dimM_pos_E7 (m : List Nat) (hm : m.length = 7) :
    0 < dimM sertables.tableE7 m :=
  dimM_pos sertables.tableE7 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableE7 sertables.fundE7
      sertables.fundShape_E7 sertables.gramRead_E7 sertables.rhoDotRead_E7) m hm

/-- E7's unit dimension is one at its displayed root table. -/
theorem dimM_unit_E7 : dimM sertables.tableE7 (List.replicate 7 0) = 1 :=
  dimM_unit sertables.tableE7 (serstable.gapAt_rho_pos_of_fund sertables.tableE7 sertables.fundE7
      sertables.fundShape_E7 sertables.gramRead_E7 sertables.rhoDotRead_E7)

/-- E8's actual Weyl-product dimension is positive at every
natural coroot label of the member's width. -/
theorem dimM_pos_E8 (m : List Nat) (hm : m.length = 8) :
    0 < dimM sertables.tableE8 m :=
  dimM_pos sertables.tableE8 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableE8 sertables.fundE8
      sertables.fundShape_E8 sertables.gramRead_E8 sertables.rhoDotRead_E8) m hm

/-- E8's unit dimension is one at its displayed root table. -/
theorem dimM_unit_E8 : dimM sertables.tableE8 (List.replicate 8 0) = 1 :=
  dimM_unit sertables.tableE8 (serstable.gapAt_rho_pos_of_fund sertables.tableE8 sertables.fundE8
      sertables.fundShape_E8 sertables.gramRead_E8 sertables.rhoDotRead_E8)

/-- B's Weyl-product dimension is positive at every rank
and every rank-width natural label. -/
theorem dimM_pos_B (l : Nat) (m : List Nat) (hm : m.length = l) :
    0 < dimM (sertables.tableB l) m :=
  dimM_pos (sertables.tableB l) (ground.length_mapRange _ l) (serstable.gapAt_rho_pos_B l) m hm

/-- B's unit dimension reads one at every rank. -/
theorem dimM_unit_B (l : Nat) : dimM (sertables.tableB l) (List.replicate l 0) = 1 :=
  dimM_unit (sertables.tableB l) (serstable.gapAt_rho_pos_B l)

/-- C's Weyl-product dimension is positive at every rank
and every rank-width natural label. -/
theorem dimM_pos_C (l : Nat) (m : List Nat) (hm : m.length = l) :
    0 < dimM (sertables.tableC l) m :=
  dimM_pos (sertables.tableC l) (ground.length_mapRange _ l) (serstable.gapAt_rho_pos_C l) m hm

/-- C's unit dimension reads one at every rank. -/
theorem dimM_unit_C (l : Nat) : dimM (sertables.tableC l) (List.replicate l 0) = 1 :=
  dimM_unit (sertables.tableC l) (serstable.gapAt_rho_pos_C l)

/-- D's Weyl-product dimension is positive at every rank
and every rank-width natural label. -/
theorem dimM_pos_D (l : Nat) (m : List Nat) (hm : m.length = l) :
    0 < dimM (sertables.tableD l) m :=
  dimM_pos (sertables.tableD l) (ground.length_replicate _ _) (serstable.gapAt_rho_pos_D l) m hm

/-- D's unit dimension reads one at every rank. -/
theorem dimM_unit_D (l : Nat) : dimM (sertables.tableD l) (List.replicate l 0) = 1 :=
  dimM_unit (sertables.tableD l) (serstable.gapAt_rho_pos_D l)

/-- A nonunit G2 label has Weyl-product dimension at least
two, with its occupied simple factor providing the strict read. -/
theorem dimM_ge_two_G2 (m : List Nat) (hm : m.length = 2)
    (hne : m ≠ List.replicate 2 0) : 2 ≤ dimM sertables.tableG2 m := by
  apply dimM_ge_two sertables.tableG2 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableG2 sertables.fundG2
      sertables.fundShape_G2 sertables.gramRead_G2 sertables.rhoDotRead_G2) _ m hm hne
  intro i hi
  rw [← sertables.simplePosRead_G2 i hi]
  exact ground.mem_getAt [] _ _ (assembly.simplePos_lt sertables.tableG2 sertables.fundG2
    sertables.fundShape_G2 hi)

/-- A nonunit F4 label has Weyl-product dimension at least
two, with its occupied simple factor providing the strict read. -/
theorem dimM_ge_two_F4 (m : List Nat) (hm : m.length = 4)
    (hne : m ≠ List.replicate 4 0) : 2 ≤ dimM sertables.tableF4 m := by
  apply dimM_ge_two sertables.tableF4 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableF4 sertables.fundF4
      sertables.fundShape_F4 sertables.gramRead_F4 sertables.rhoDotRead_F4) _ m hm hne
  intro i hi
  rw [← sertables.simplePosRead_F4 i hi]
  exact ground.mem_getAt [] _ _ (assembly.simplePos_lt sertables.tableF4 sertables.fundF4
    sertables.fundShape_F4 hi)

/-- A nonunit E6 label has Weyl-product dimension at least
two, with its occupied simple factor providing the strict read. -/
theorem dimM_ge_two_E6 (m : List Nat) (hm : m.length = 6)
    (hne : m ≠ List.replicate 6 0) : 2 ≤ dimM sertables.tableE6 m := by
  apply dimM_ge_two sertables.tableE6 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableE6 sertables.fundE6
      sertables.fundShape_E6 sertables.gramRead_E6 sertables.rhoDotRead_E6) _ m hm hne
  intro i hi
  rw [← sertables.simplePosRead_E6 i hi]
  exact ground.mem_getAt [] _ _ (assembly.simplePos_lt sertables.tableE6 sertables.fundE6
    sertables.fundShape_E6 hi)

/-- A nonunit E7 label has Weyl-product dimension at least
two, with its occupied simple factor providing the strict read. -/
theorem dimM_ge_two_E7 (m : List Nat) (hm : m.length = 7)
    (hne : m ≠ List.replicate 7 0) : 2 ≤ dimM sertables.tableE7 m := by
  apply dimM_ge_two sertables.tableE7 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableE7 sertables.fundE7
      sertables.fundShape_E7 sertables.gramRead_E7 sertables.rhoDotRead_E7) _ m hm hne
  intro i hi
  rw [← sertables.simplePosRead_E7 i hi]
  exact ground.mem_getAt [] _ _ (assembly.simplePos_lt sertables.tableE7 sertables.fundE7
    sertables.fundShape_E7 hi)

/-- A nonunit E8 label has Weyl-product dimension at least
two, with its occupied simple factor providing the strict read. -/
theorem dimM_ge_two_E8 (m : List Nat) (hm : m.length = 8)
    (hne : m ≠ List.replicate 8 0) : 2 ≤ dimM sertables.tableE8 m := by
  apply dimM_ge_two sertables.tableE8 (by decide +kernel)
    (serstable.gapAt_rho_pos_of_fund sertables.tableE8 sertables.fundE8
      sertables.fundShape_E8 sertables.gramRead_E8 sertables.rhoDotRead_E8) _ m hm hne
  intro i hi
  rw [← sertables.simplePosRead_E8 i hi]
  exact ground.mem_getAt [] _ _ (assembly.simplePos_lt sertables.tableE8 sertables.fundE8
    sertables.fundShape_E8 hi)

/-- The B product has dimension at least two at every
nonunit coroot label in the series' domain. -/
theorem dimM_ge_two_B (l : Nat) (m : List Nat) (hm : m.length = l)
    (hne : m ≠ List.replicate l 0) : 2 ≤ dimM (sertables.tableB l) m :=
  dimM_ge_two (sertables.tableB l) (ground.length_mapRange _ l) (serstable.gapAt_rho_pos_B l)
    (sertables.simpleFold_mem_B l) m hm hne

/-- The C product has dimension at least two at every
nonunit coroot label in the series' domain. -/
theorem dimM_ge_two_C (l : Nat) (m : List Nat) (hm : m.length = l)
    (hne : m ≠ List.replicate l 0) : 2 ≤ dimM (sertables.tableC l) m :=
  dimM_ge_two (sertables.tableC l) (ground.length_mapRange _ l) (serstable.gapAt_rho_pos_C l)
    (sertables.simpleFold_mem_C l) m hm hne

/-- The D product has dimension at least two at every
nonunit coroot label in the series' domain. -/
theorem dimM_ge_two_D (l : Nat) (hl : 2 ≤ l) (m : List Nat) (hm : m.length = l)
    (hne : m ≠ List.replicate l 0) : 2 ≤ dimM (sertables.tableD l) m :=
  dimM_ge_two (sertables.tableD l) (ground.length_replicate _ _) (serstable.gapAt_rho_pos_D l)
    (fun i hi => sertables.simpleFold_mem_D l i hl hi) m hm hne

/-- The B queue at a strictly dominant seed satisfies the shape,
graded closure and seed-count reads at the stored step count. -/
theorem orbitFam_reads_B (l : Nat) (hl : 0 < l) (v : List ground.BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → ground.BPair.unit < ground.getAt ground.BPair.unit v i) :
    sertables.wShapeRead (sertables.tableB l) (orbitFam (sertables.tableB l) (fusion.wFuel l) v)
      ∧ assembly.wCloseRead (sertables.tableB l) (orbitFam (sertables.tableB l) (fusion.wFuel l) v)
      ∧ assembly.wTopAt (orbitFam (sertables.tableB l) (fusion.wFuel l) v) (poly.pnorm v) :=
  orbitFam_reads_family (sertables.tableB l) (sertables.serWeylB l v)
    (sertables.serWeylB_shape l hl v) (assembly.serWeylB_close l hl v hv hp)
    (sertables.serWeylB_regular l hl v hv hp)
    (fun w hw hn i hi j hj he => assembly.reflF_B_separate l w hw hn i j hi hj he)
    (fusion.wFuel l) (fusion.serWeylB_fuel l v).2 v (sertables.serWeylB_seed l v hv hl)

/-- The C queue at a strictly dominant seed satisfies the shape,
graded closure and seed-count reads at the stored step count. -/
theorem orbitFam_reads_C (l : Nat) (hl : 0 < l) (v : List ground.BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → ground.BPair.unit < ground.getAt ground.BPair.unit v i) :
    sertables.wShapeRead (sertables.tableC l) (orbitFam (sertables.tableC l) (fusion.wFuel l) v)
      ∧ assembly.wCloseRead (sertables.tableC l) (orbitFam (sertables.tableC l) (fusion.wFuel l) v)
      ∧ assembly.wTopAt (orbitFam (sertables.tableC l) (fusion.wFuel l) v) (poly.pnorm v) :=
  orbitFam_reads_family (sertables.tableC l) (sertables.serWeylC l v)
    (sertables.serWeylC_shape l hl v) (assembly.serWeylC_close l hl v hv hp)
    (sertables.serWeylC_regular l hl v hv hp)
    (fun w hw hn i hi j hj he => assembly.reflF_C_separate l w hw hn i j hi hj he)
    (fusion.wFuel l) (fusion.serWeylC_fuel l v).2 v (sertables.serWeylC_seed l v hv hl)

/-- The D queue at a strictly dominant seed satisfies the shape,
graded closure and seed-count reads at the stored step count. -/
theorem orbitFam_reads_D (l : Nat) (hl : 2 ≤ l) (v : List ground.BPair) (hv : v.length = l)
    (hp : ∀ i, i < l → ground.BPair.unit < ground.getAt ground.BPair.unit v i) :
    sertables.wShapeRead (sertables.tableD l) (orbitFam (sertables.tableD l) (fusion.wFuel l) v)
      ∧ assembly.wCloseRead (sertables.tableD l) (orbitFam (sertables.tableD l) (fusion.wFuel l) v)
      ∧ assembly.wTopAt (orbitFam (sertables.tableD l) (fusion.wFuel l) v) (poly.pnorm v) :=
  orbitFam_reads_family (sertables.tableD l) (sertables.serWeylD l v)
    (sertables.serWeylD_shape l (Nat.lt_of_lt_of_le (by decide : 0 < 2) hl) v) (assembly.serWeylD_close l hl v hv hp)
    (sertables.serWeylD_regular l hl v hv hp)
    (fun w hw hn i hi j hj he => assembly.reflF_D_separate l w hw hn i j hi hj he)
    (fusion.wFuel l) (fusion.serWeylD_fuel l v).2 v (sertables.serWeylD_seed l v hv hl)

/-- C's dominance walk returns a dominant member of the displayed
orbit at the constructor's stored step count. -/
theorem domWalk_complete_C (l : Nat) (hl : 0 < l) (v : List ground.BPair) (hv : v.length = l) :
    domWalk (sertables.tableC l) (fusion.wFuel l) (poly.pnorm v)
        ∈ (sertables.serWeylC l v).map Prod.fst
      ∧ memberchar.lamRead (sertables.tableC l)
        (domWalk (sertables.tableC l) (fusion.wFuel l) (poly.pnorm v)) :=
  domWalk_finite_family (sertables.tableC l) (sertables.serWeylC l v)
    (sertables.serWeylC_shape l hl v) (assembly.serWeylC_closed l v)
    (fun w => elim.dotP (sertables.coordsC w) (sertables.coordsC (sertables.rhoV (sertables.tableC l))))
    (assembly.reflF_C_rho_rise l) (fusion.wFuel l) (fusion.serWeylC_fuel l v).1 v
    (sertables.serWeylC_seed l v hv hl)

/-- B's dominance walk returns a dominant member of the displayed
orbit at the constructor's stored step count. -/
theorem domWalk_complete_B (l : Nat) (hl : 0 < l) (v : List ground.BPair) (hv : v.length = l) :
    domWalk (sertables.tableB l) (fusion.wFuel l) (poly.pnorm v)
        ∈ (sertables.serWeylB l v).map Prod.fst
      ∧ memberchar.lamRead (sertables.tableB l)
        (domWalk (sertables.tableB l) (fusion.wFuel l) (poly.pnorm v)) :=
  domWalk_finite_family (sertables.tableB l) (sertables.serWeylB l v)
    (sertables.serWeylB_shape l hl v) (assembly.serWeylB_closed l v hv)
    (fun w => elim.dotP (sertables.coordsB w) (sertables.coordsB (sertables.rhoV (sertables.tableB l))))
    (assembly.reflF_B_rho_rise l) (fusion.wFuel l) (fusion.serWeylB_fuel l v).1 v
    (sertables.serWeylB_seed l v hv hl)

/-- D's dominance walk returns a dominant member of the displayed
orbit at the constructor's stored step count. -/
theorem domWalk_complete_D (l : Nat) (hl : 2 ≤ l) (v : List ground.BPair) (hv : v.length = l) :
    domWalk (sertables.tableD l) (fusion.wFuel l) (poly.pnorm v)
        ∈ (sertables.serWeylD l v).map Prod.fst
      ∧ memberchar.lamRead (sertables.tableD l)
        (domWalk (sertables.tableD l) (fusion.wFuel l) (poly.pnorm v)) :=
  domWalk_finite_family (sertables.tableD l) (sertables.serWeylD l v)
    (sertables.serWeylD_shape l (Nat.lt_of_lt_of_le (by decide : 0 < 2) hl) v) (assembly.serWeylD_closed l hl v hv)
    (fun w => elim.dotP (sertables.coordsD w) (sertables.coordsD (sertables.rhoV (sertables.tableD l))))
    (assembly.reflF_D_rho_rise l hl) (fusion.wFuel l) (fusion.serWeylD_fuel l v).1 v
    (sertables.serWeylD_seed l v hv hl)

/-- The actual B multiplicity family is reflection-invariant
at its stored fuel, for every top label. -/
theorem multFam_sym_B (l : Nat) (hl : 0 < l) (G : elim.Mat) (lam : List Nat) :
    memberchar.symRead (sertables.tableB l) (multFam (sertables.tableB l) G (fusion.wFuel l) lam) := by
  apply multFam_sym (sertables.tableB l) G (fusion.wFuel l) lam (sertables.reflSquareRead_B l)
  intro p hp
  exact orbitSet_sym_B l hl (natV p.1) ((ground.length_map ground.BPair.ofNat p.1).trans
    (domFam_width (sertables.tableB l) G (fusion.wFuel l) lam p hp))

/-- The actual B full family is determined by its dominant
table's reads, with all orbit and walk conditions at stored fuel. -/
theorem multFam_read_B (l : Nat) (hl : 0 < l) (G : elim.Mat) (lam : List Nat)
    (L : List (List ground.BPair)) (hmsh : memberchar.mShapeRead (sertables.tableB l) L)
    (hsym : memberchar.symRead (sertables.tableB l) L)
    (hcount : ∀ m, lookupN m (domFam (sertables.tableB l) G (fusion.wFuel l) lam)
      = ground.countOf (natV m) L) (v : List ground.BPair) :
    ground.countOf v (multFam (sertables.tableB l) G (fusion.wFuel l) lam) = ground.countOf v L := by
  apply multFam_read (sertables.tableB l) G (fusion.wFuel l) lam (sertables.reflSquareRead_B l)
    _ L hmsh hsym hcount _ _ v
  · intro w hw he
    have h := (domWalk_complete_B l hl w hw).2.1
    rw [he] at h
    have hpos : 0 < l := hl
    change 0 = l at h
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  · intro p hp
    exact orbitSet_sym_B l hl (natV p.1) ((ground.length_map ground.BPair.ofNat p.1).trans
      (domFam_width (sertables.tableB l) G (fusion.wFuel l) lam p hp))
  · intro p hp
    exact orbitSet_dom_B l hl p.1 (domFam_width (sertables.tableB l) G (fusion.wFuel l) lam p hp)

/-- The actual C multiplicity family is reflection-invariant
at its stored fuel, for every top label. -/
theorem multFam_sym_C (l : Nat) (hl : 0 < l) (G : elim.Mat) (lam : List Nat) :
    memberchar.symRead (sertables.tableC l) (multFam (sertables.tableC l) G (fusion.wFuel l) lam) := by
  apply multFam_sym (sertables.tableC l) G (fusion.wFuel l) lam (sertables.reflSquareRead_C l)
  intro p hp
  exact orbitSet_sym_C l hl (natV p.1) ((ground.length_map ground.BPair.ofNat p.1).trans
    (domFam_width (sertables.tableC l) G (fusion.wFuel l) lam p hp))

/-- The actual C full family is determined by its dominant
table's reads, with all orbit and walk conditions at stored fuel. -/
theorem multFam_read_C (l : Nat) (hl : 0 < l) (G : elim.Mat) (lam : List Nat)
    (L : List (List ground.BPair)) (hmsh : memberchar.mShapeRead (sertables.tableC l) L)
    (hsym : memberchar.symRead (sertables.tableC l) L)
    (hcount : ∀ m, lookupN m (domFam (sertables.tableC l) G (fusion.wFuel l) lam)
      = ground.countOf (natV m) L) (v : List ground.BPair) :
    ground.countOf v (multFam (sertables.tableC l) G (fusion.wFuel l) lam) = ground.countOf v L := by
  apply multFam_read (sertables.tableC l) G (fusion.wFuel l) lam (sertables.reflSquareRead_C l)
    _ L hmsh hsym hcount _ _ v
  · intro w hw he
    have h := (domWalk_complete_C l hl w hw).2.1
    rw [he] at h
    have hpos : 0 < l := hl
    change 0 = l at h
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  · intro p hp
    exact orbitSet_sym_C l hl (natV p.1) ((ground.length_map ground.BPair.ofNat p.1).trans
      (domFam_width (sertables.tableC l) G (fusion.wFuel l) lam p hp))
  · intro p hp
    exact orbitSet_dom_C l hl p.1 (domFam_width (sertables.tableC l) G (fusion.wFuel l) lam p hp)

/-- The actual D multiplicity family is reflection-invariant
at its stored fuel, for every top label. -/
theorem multFam_sym_D (l : Nat) (hl : 2 ≤ l) (G : elim.Mat) (lam : List Nat) :
    memberchar.symRead (sertables.tableD l) (multFam (sertables.tableD l) G (fusion.wFuel l) lam) := by
  apply multFam_sym (sertables.tableD l) G (fusion.wFuel l) lam (sertables.reflSquareRead_D l)
  intro p hp
  exact orbitSet_sym_D l hl (natV p.1) ((ground.length_map ground.BPair.ofNat p.1).trans
    (domFam_width (sertables.tableD l) G (fusion.wFuel l) lam p hp))

/-- The actual D full family is determined by its dominant
table's reads, with all orbit and walk conditions at stored fuel. -/
theorem multFam_read_D (l : Nat) (hl : 2 ≤ l) (G : elim.Mat) (lam : List Nat)
    (L : List (List ground.BPair)) (hmsh : memberchar.mShapeRead (sertables.tableD l) L)
    (hsym : memberchar.symRead (sertables.tableD l) L)
    (hcount : ∀ m, lookupN m (domFam (sertables.tableD l) G (fusion.wFuel l) lam)
      = ground.countOf (natV m) L) (v : List ground.BPair) :
    ground.countOf v (multFam (sertables.tableD l) G (fusion.wFuel l) lam) = ground.countOf v L := by
  apply multFam_read (sertables.tableD l) G (fusion.wFuel l) lam (sertables.reflSquareRead_D l)
    _ L hmsh hsym hcount _ _ v
  · intro w hw he
    have h := (domWalk_complete_D l hl w hw).2.1
    rw [he] at h
    have hpos : 0 < l := Nat.lt_of_lt_of_le (by decide +kernel : 0 < 2) hl
    change 0 = l at h
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  · intro p hp
    exact orbitSet_sym_D l hl (natV p.1) ((ground.length_map ground.BPair.ofNat p.1).trans
      (domFam_width (sertables.tableD l) G (fusion.wFuel l) lam p hp))
  · intro p hp
    exact orbitSet_dom_D l hl p.1 (domFam_width (sertables.tableD l) G (fusion.wFuel l) lam p hp)

/-- At B's stored fuel, every larger fuel reads the same
multiplicity family, fusion counts, fusion rows and dual labels. -/
theorem fuel_more_B (l : Nat) (hl : 0 < l) (G : elim.Mat) (extra : Nat)
    (a b c : List Nat) (ha : a.length = l) (hc : c.length = l) :
    multFam (sertables.tableB l) G ((fusion.wFuel l) + extra) a = multFam (sertables.tableB l) G (fusion.wFuel l) a
      ∧ countM (sertables.tableB l) G ((fusion.wFuel l) + extra) a b c = countM (sertables.tableB l) G (fusion.wFuel l) a b c
      ∧ rowM (sertables.tableB l) G ((fusion.wFuel l) + extra) a b = rowM (sertables.tableB l) G (fusion.wFuel l) a b
      ∧ dualM (sertables.tableB l) ((fusion.wFuel l) + extra) a = dualM (sertables.tableB l) (fusion.wFuel l) a := by
  have hwalk : ∀ v : List ground.BPair, v.length = l →
      domWalk (sertables.tableB l) (fusion.wFuel l) (poly.pnorm v) ≠ [] := by
    intro v hv he
    have h := (domWalk_complete_B l hl v hv).2.1
    rw [he] at h
    change 0 = l at h
    have hpos : 0 < l := hl
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  have horbit : ∀ v : List ground.BPair, v.length = l →
      orbitSet (sertables.tableB l) (fusion.wFuel l) v ≠ [] := fun v hv => (orbit_complete_B l hl v hv).1.1
  exact ⟨multFam_more (sertables.tableB l) G (fusion.wFuel l) extra hwalk horbit a,
    countM_more (sertables.tableB l) G (fusion.wFuel l) extra hwalk horbit a b c hc,
    rowM_more (sertables.tableB l) G (fusion.wFuel l) extra hwalk horbit a b,
    dualM_more (sertables.tableB l) (fusion.wFuel l) extra hwalk a ha⟩

/-- At C's stored fuel, every larger fuel reads the same
multiplicity family, fusion counts, fusion rows and dual labels. -/
theorem fuel_more_C (l : Nat) (hl : 0 < l) (G : elim.Mat) (extra : Nat)
    (a b c : List Nat) (ha : a.length = l) (hc : c.length = l) :
    multFam (sertables.tableC l) G ((fusion.wFuel l) + extra) a = multFam (sertables.tableC l) G (fusion.wFuel l) a
      ∧ countM (sertables.tableC l) G ((fusion.wFuel l) + extra) a b c = countM (sertables.tableC l) G (fusion.wFuel l) a b c
      ∧ rowM (sertables.tableC l) G ((fusion.wFuel l) + extra) a b = rowM (sertables.tableC l) G (fusion.wFuel l) a b
      ∧ dualM (sertables.tableC l) ((fusion.wFuel l) + extra) a = dualM (sertables.tableC l) (fusion.wFuel l) a := by
  have hwalk : ∀ v : List ground.BPair, v.length = l →
      domWalk (sertables.tableC l) (fusion.wFuel l) (poly.pnorm v) ≠ [] := by
    intro v hv he
    have h := (domWalk_complete_C l hl v hv).2.1
    rw [he] at h
    change 0 = l at h
    have hpos : 0 < l := hl
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  have horbit : ∀ v : List ground.BPair, v.length = l →
      orbitSet (sertables.tableC l) (fusion.wFuel l) v ≠ [] := fun v hv => (orbit_complete_C l hl v hv).1.1
  exact ⟨multFam_more (sertables.tableC l) G (fusion.wFuel l) extra hwalk horbit a,
    countM_more (sertables.tableC l) G (fusion.wFuel l) extra hwalk horbit a b c hc,
    rowM_more (sertables.tableC l) G (fusion.wFuel l) extra hwalk horbit a b,
    dualM_more (sertables.tableC l) (fusion.wFuel l) extra hwalk a ha⟩

/-- At D's stored fuel, every larger fuel reads the same
multiplicity family, fusion counts, fusion rows and dual labels. -/
theorem fuel_more_D (l : Nat) (hl : 2 ≤ l) (G : elim.Mat) (extra : Nat)
    (a b c : List Nat) (ha : a.length = l) (hc : c.length = l) :
    multFam (sertables.tableD l) G ((fusion.wFuel l) + extra) a = multFam (sertables.tableD l) G (fusion.wFuel l) a
      ∧ countM (sertables.tableD l) G ((fusion.wFuel l) + extra) a b c = countM (sertables.tableD l) G (fusion.wFuel l) a b c
      ∧ rowM (sertables.tableD l) G ((fusion.wFuel l) + extra) a b = rowM (sertables.tableD l) G (fusion.wFuel l) a b
      ∧ dualM (sertables.tableD l) ((fusion.wFuel l) + extra) a = dualM (sertables.tableD l) (fusion.wFuel l) a := by
  have hwalk : ∀ v : List ground.BPair, v.length = l →
      domWalk (sertables.tableD l) (fusion.wFuel l) (poly.pnorm v) ≠ [] := by
    intro v hv he
    have h := (domWalk_complete_D l hl v hv).2.1
    rw [he] at h
    change 0 = l at h
    have hpos : 0 < l := Nat.lt_of_lt_of_le (by decide +kernel : 0 < 2) hl
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  have horbit : ∀ v : List ground.BPair, v.length = l →
      orbitSet (sertables.tableD l) (fusion.wFuel l) v ≠ [] := fun v hv => (orbit_complete_D l hl v hv).1.1
  exact ⟨multFam_more (sertables.tableD l) G (fusion.wFuel l) extra hwalk horbit a,
    countM_more (sertables.tableD l) G (fusion.wFuel l) extra hwalk horbit a b c hc,
    rowM_more (sertables.tableD l) G (fusion.wFuel l) extra hwalk horbit a b,
    dualM_more (sertables.tableD l) (fusion.wFuel l) extra hwalk a ha⟩

/-- At G2's stored fuel, every larger fuel reads the same
multiplicity family, fusion counts, fusion rows and dual labels. -/
theorem fuel_more_G2 (G : elim.Mat) (extra : Nat)
    (a b c : List Nat) (ha : a.length = 2) (hc : c.length = 2) :
    multFam sertables.tableG2 G (16 + extra) a = multFam sertables.tableG2 G 16 a
      ∧ countM sertables.tableG2 G (16 + extra) a b c = countM sertables.tableG2 G 16 a b c
      ∧ rowM sertables.tableG2 G (16 + extra) a b = rowM sertables.tableG2 G 16 a b
      ∧ dualM sertables.tableG2 (16 + extra) a = dualM sertables.tableG2 16 a := by
  have hwalk : ∀ v : List ground.BPair, v.length = 2 →
      domWalk sertables.tableG2 16 (poly.pnorm v) ≠ [] := by
    intro v hv he
    have h := (domWalk_complete_G2 v hv).2.1
    rw [he] at h
    change 0 = 2 at h
    have hpos : 0 < 2 := by decide +kernel
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  have horbit : ∀ v : List ground.BPair, v.length = 2 →
      orbitSet sertables.tableG2 16 v ≠ [] := fun v hv => (orbit_complete_G2 v hv).1.1
  exact ⟨multFam_more sertables.tableG2 G 16 extra hwalk horbit a,
    countM_more sertables.tableG2 G 16 extra hwalk horbit a b c hc,
    rowM_more sertables.tableG2 G 16 extra hwalk horbit a b,
    dualM_more sertables.tableG2 16 extra hwalk a ha⟩

/-- B's actual fusion count at stored fuel is the graded
convolution with its actual shifted orbit, at every label. -/
theorem countM_conv_B (l : Nat) (hl : 0 < l) (G : elim.Mat) (a b c : List Nat)
    (hb : b.length = l) (hc : c.length = l) :
    countM (sertables.tableB l) G (fusion.wFuel l) a b c =
      memberchar.convCount (orbitFam (sertables.tableB l) (fusion.wFuel l) (shiftV (sertables.tableB l) b))
        (multFam (sertables.tableB l) G (fusion.wFuel l) a) (shiftV (sertables.tableB l) c) false
      - memberchar.convCount (orbitFam (sertables.tableB l) (fusion.wFuel l) (shiftV (sertables.tableB l) b))
        (multFam (sertables.tableB l) G (fusion.wFuel l) a) (shiftV (sertables.tableB l) c) true := by
  have hbv := shiftV_length (sertables.tableB l) b hb
  have hbp := shiftV_pos (sertables.tableB l) b hb
  have hs := (sertables.serWeylB_shape l hl (shiftV (sertables.tableB l) b))
  refine countM_orbit_conv (sertables.tableB l) G (fusion.wFuel l) ?_ (sertables.reflSquareRead_B l) a b c hc
    (sertables.serWeylB l (shiftV (sertables.tableB l) b)) hs (sertables.serWeylB_regular l hl _ hbv hbp) (assembly.serWeylB_close l hl _ hbv hbp) ?_ ?_
    (fun w hw hn i hi j hj he => assembly.reflF_B_separate l w hw hn i j hi hj he) ?_
  · intro v hv he
    have h := (domWalk_complete_B l hl v hv).2.1
    rw [he] at h
    change 0 = l at h
    have hpos : 0 < l := hl
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  · have h := sertables.serWeylB_seed l _ hbv hl
    rw [show poly.pnorm (shiftV _ b) = shiftV _ b from poly.pnorm_pnorm _] at h
    exact h
  · intro p hp hpos
    have h := sertables.serWeylB_strict_top l hl _ p.1 hbv (hs p hp).1 hbp hpos p.2 hp
    rw [(hs p hp).2, show poly.pnorm (shiftV _ b) = shiftV _ b from poly.pnorm_pnorm _] at h
    exact h
  · exact (fusion.serWeylB_fuel l _).2

/-- C's actual fusion count at stored fuel is the graded
convolution with its actual shifted orbit, at every label. -/
theorem countM_conv_C (l : Nat) (hl : 0 < l) (G : elim.Mat) (a b c : List Nat)
    (hb : b.length = l) (hc : c.length = l) :
    countM (sertables.tableC l) G (fusion.wFuel l) a b c =
      memberchar.convCount (orbitFam (sertables.tableC l) (fusion.wFuel l) (shiftV (sertables.tableC l) b))
        (multFam (sertables.tableC l) G (fusion.wFuel l) a) (shiftV (sertables.tableC l) c) false
      - memberchar.convCount (orbitFam (sertables.tableC l) (fusion.wFuel l) (shiftV (sertables.tableC l) b))
        (multFam (sertables.tableC l) G (fusion.wFuel l) a) (shiftV (sertables.tableC l) c) true := by
  have hbv := shiftV_length (sertables.tableC l) b hb
  have hbp := shiftV_pos (sertables.tableC l) b hb
  have hs := (sertables.serWeylC_shape l hl (shiftV (sertables.tableC l) b))
  refine countM_orbit_conv (sertables.tableC l) G (fusion.wFuel l) ?_ (sertables.reflSquareRead_C l) a b c hc
    (sertables.serWeylC l (shiftV (sertables.tableC l) b)) hs (sertables.serWeylC_regular l hl _ hbv hbp) (assembly.serWeylC_close l hl _ hbv hbp) ?_ ?_
    (fun w hw hn i hi j hj he => assembly.reflF_C_separate l w hw hn i j hi hj he) ?_
  · intro v hv he
    have h := (domWalk_complete_C l hl v hv).2.1
    rw [he] at h
    change 0 = l at h
    have hpos : 0 < l := hl
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  · have h := sertables.serWeylC_seed l _ hbv hl
    rw [show poly.pnorm (shiftV _ b) = shiftV _ b from poly.pnorm_pnorm _] at h
    exact h
  · intro p hp hpos
    have h := sertables.serWeylC_strict_top l hl _ p.1 hbv (hs p hp).1 hbp hpos p.2 hp
    rw [(hs p hp).2, show poly.pnorm (shiftV _ b) = shiftV _ b from poly.pnorm_pnorm _] at h
    exact h
  · exact (fusion.serWeylC_fuel l _).2

/-- D's actual fusion count at stored fuel is the graded
convolution with its actual shifted orbit, at every label. -/
theorem countM_conv_D (l : Nat) (hl : 2 ≤ l) (G : elim.Mat) (a b c : List Nat)
    (hb : b.length = l) (hc : c.length = l) :
    countM (sertables.tableD l) G (fusion.wFuel l) a b c =
      memberchar.convCount (orbitFam (sertables.tableD l) (fusion.wFuel l) (shiftV (sertables.tableD l) b))
        (multFam (sertables.tableD l) G (fusion.wFuel l) a) (shiftV (sertables.tableD l) c) false
      - memberchar.convCount (orbitFam (sertables.tableD l) (fusion.wFuel l) (shiftV (sertables.tableD l) b))
        (multFam (sertables.tableD l) G (fusion.wFuel l) a) (shiftV (sertables.tableD l) c) true := by
  have hbv := shiftV_length (sertables.tableD l) b hb
  have hbp := shiftV_pos (sertables.tableD l) b hb
  have hs := (sertables.serWeylD_shape l (Nat.lt_of_lt_of_le (by decide +kernel : 0 < 2) hl) (shiftV (sertables.tableD l) b))
  refine countM_orbit_conv (sertables.tableD l) G (fusion.wFuel l) ?_ (sertables.reflSquareRead_D l) a b c hc
    (sertables.serWeylD l (shiftV (sertables.tableD l) b)) hs (sertables.serWeylD_regular l hl _ hbv hbp) (assembly.serWeylD_close l hl _ hbv hbp) ?_ ?_
    (fun w hw hn i hi j hj he => assembly.reflF_D_separate l w hw hn i j hi hj he) ?_
  · intro v hv he
    have h := (domWalk_complete_D l hl v hv).2.1
    rw [he] at h
    change 0 = l at h
    have hpos : 0 < l := Nat.lt_of_lt_of_le (by decide +kernel : 0 < 2) hl
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  · have h := sertables.serWeylD_seed l _ hbv hl
    rw [show poly.pnorm (shiftV _ b) = shiftV _ b from poly.pnorm_pnorm _] at h
    exact h
  · intro p hp hpos
    have h := sertables.serWeylD_strict_top l hl _ p.1 hbv (hs p hp).1 hbp hpos p.2 hp
    rw [(hs p hp).2, show poly.pnorm (shiftV _ b) = shiftV _ b from poly.pnorm_pnorm _] at h
    exact h
  · exact (fusion.serWeylD_fuel l _).2

/-- G2's actual fusion count at stored fuel is the graded
convolution with its actual shifted orbit, at every label. -/
theorem countM_conv_G2 (G : elim.Mat) (a b c : List Nat)
    (hb : b.length = 2) (hc : c.length = 2) :
    countM sertables.tableG2 G 16 a b c =
      memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
        (multFam sertables.tableG2 G 16 a) (shiftV sertables.tableG2 c) false
      - memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
        (multFam sertables.tableG2 G 16 a) (shiftV sertables.tableG2 c) true := by
  have hbv := shiftV_length sertables.tableG2 b hb
  have hbp := shiftV_pos sertables.tableG2 b hb
  have hs := sertables.weylG2_shape (shiftV sertables.tableG2 b)
  refine countM_orbit_conv sertables.tableG2 G 16 ?_ sertables.reflSquareRead_G2 a b c hc
    (sertables.weylG2 (shiftV sertables.tableG2 b)) hs (sertables.weylG2_regular _ hbv hbp) (assembly.weylG2_close _ hbv hbp) ?_ ?_
    (fun w hw hn i hi j hj he => assembly.reflF_G2_separate w hw hn i j hi hj he) ?_
  · intro v hv he
    have h := (domWalk_complete_G2 v hv).2.1
    rw [he] at h
    change 0 = 2 at h
    have hpos : 0 < 2 := by decide +kernel
    rw [← h] at hpos
    exact Nat.lt_irrefl 0 hpos
  · have h := sertables.weylG2_seed _ hbv
    rw [show poly.pnorm (shiftV _ b) = shiftV _ b from poly.pnorm_pnorm _] at h
    exact h
  · intro p hp hpos
    have h := sertables.weylG2_dominant_top _ p.1 hbv (fun i hi => ground.leB_of_lt (hbp i hi)) (fun i hi => ground.leB_of_lt (hpos i hi)) p.2 hp
    rw [(hs p hp).2, show poly.pnorm (shiftV _ b) = shiftV _ b from poly.pnorm_pnorm _] at h
    exact h
  · exact Nat.le_trans (ground.length_dedupF_le _) (by rw [ground.length_map, sertables.weylG2_length]; decide +kernel)

/-- G2's implemented fusion count is the occurrence count of
channel tops in a stated tensor-product exhaustion. Every orbit
and fundamental-data read is at the member's actual constructors;
the channel families enter through their block and trace reads. -/
theorem countM_exhaustion_G2 (a b c : List Nat) (hb : b.length = 2) (hc : c.length = 2)
    (Lb : List (List ground.BPair)) (wb : List (List Nat))
    (hmb : memberchar.mShapeRead sertables.tableG2 Lb) (hsb : memberchar.symRead sertables.tableG2 Lb)
    (hdb : memberchar.supportRead sertables.tableG2 Lb wb (natV b)) (htb : memberchar.topRead Lb (natV b))
    (hrb : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) Lb (natV b))
    (cs : List (List Nat)) (Ls : List (List (List ground.BPair))) (ws : List (List (List Nat)))
    (hlen : Ls.length = cs.length)
    (hch : ∀ k, k < cs.length →
      (ground.getAt [] cs k).length = 2
        ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] Ls k) (ground.getAt [] ws k)
          (natV (ground.getAt [] cs k))
        ∧ memberchar.topRead (ground.getAt [] Ls k) (natV (ground.getAt [] cs k))
        ∧ memberchar.recRead sertables.tableG2 sertables.fundG2
          (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
          (ground.getAt [] Ls k) (natV (ground.getAt [] cs k)))
    (hexh : ∀ v, ground.countOf v (steinberg.prodFam (multFam sertables.tableG2 sertables.fundG2.gram 16 a) Lb)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) Ls) :
    countM sertables.tableG2 sertables.fundG2.gram 16 a b c = ground.countOf c cs := by
  let Ws := cs.map (fun d => orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 d))
  let wWs := cs.map (fun d => (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 d)).map
    (fun p => foldWits sertables.tableG2 (shiftV sertables.tableG2 d) p.1))
  have hz := orbitFam_character_G2 [0, 0] rfl
  have hzero : shiftV sertables.tableG2 [0, 0] = sertables.rhoV sertables.tableG2 := rfl
  rw [hzero] at hz
  have hzt : assembly.wTopRead sertables.tableG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) := by
    change assembly.wTopAt _ (poly.pnorm (sertables.rhoV sertables.tableG2))
    rw [assembly.pnorm_rhoV]
    exact hz.2.2.2.1
  have hbr := orbitFam_character_G2 b hb
  have hlb := lamRead_natV sertables.tableG2 b hb
  have hlc := lamRead_natV sertables.tableG2 c hc
  rw [natV_pnorm] at hlb hlc
  have hr : steinberg.memberAt sertables.tableG2 (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b))
      (multFam sertables.tableG2 sertables.fundG2.gram 16 a) (cs.map natV) (natV c) := by
    apply steinberg.memberRead sertables.tableG2 sertables.fundG2 _ _ Lb wb (natV b)
      _ _ _ Ls ws (cs.map natV) Ws wWs (natV c)
      sertables.fundShape_G2 sertables.gramRead_G2 sertables.gramSymRead_G2 sertables.simplePosRead_G2
      sertables.reflSquareRead_G2 sertables.permSquareRead_G2 sertables.permImageRead_G2
      sertables.rhoDotRead_G2 sertables.reflFormRead_G2 hz.1 hz.2.1 hz.2.2.1 hzt
      hmb hsb hdb htb hlb hrb hbr.1 hbr.2.1 hbr.2.2.1 hbr.2.2.2.1 hbr.2.2.2.2
      (multFam_shape sertables.tableG2 sertables.fundG2.gram 16 a) _ _
      (fun v _ => hexh v) (fun _ _ v _ => hexh v) hlc
    · rw [ground.length_map]; exact hlen
    · intro k hk
      rw [ground.length_map] at hk
      have h := hch k hk
      have hd := orbitFam_character_G2 (ground.getAt [] cs k) h.1
      have hlam := lamRead_natV sertables.tableG2 (ground.getAt [] cs k) h.1
      rw [natV_pnorm] at hlam
      change memberchar.mShapeRead _ _ ∧ memberchar.symRead _ _ ∧ memberchar.supportRead _ _ _ _
        ∧ memberchar.topRead _ _ ∧ memberchar.lamRead _ _ ∧ memberchar.recRead _ _ _ _ _
        ∧ sertables.wShapeRead _ (ground.getAt [] (cs.map _) k)
        ∧ assembly.wCloseRead _ (ground.getAt [] (cs.map _) k)
        ∧ assembly.wDomAt _ (ground.getAt [] (cs.map _) k) (ground.getAt [] (cs.map _) k) _
        ∧ assembly.wTopAt (ground.getAt [] (cs.map _) k) _
        ∧ assembly.wRegRead _ (ground.getAt [] (cs.map _) k) _
      rw [ground.getAt_map [] [] natV cs k hk,
        ground.getAt_map [] [] (fun d => orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 d)) cs k hk,
        ground.getAt_map [] [] (fun d => (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 d)).map
          (fun p => foldWits sertables.tableG2 (shiftV sertables.tableG2 d) p.1)) cs k hk]
      exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hlam, h.2.2.2.2.2,
        hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩
  rw [countM_conv_G2 sertables.fundG2.gram a b c hb hc]
  change ground.countOf (natV c) (cs.map natV) + memberchar.convCount _ _ (shiftV sertables.tableG2 c) true
    = memberchar.convCount _ _ (shiftV sertables.tableG2 c) false at hr
  rw [← hr, ground.addSubSelfR, countOf_natV_map]

/-- Exchanging G2's tensor factors preserves the implemented
fusion count when the two mathematical blocks and their common
product exhaustion satisfy the character reads. -/
theorem countM_comm_G2 (a b c : List Nat) (ha : a.length = 2) (hb : b.length = 2) (hc : c.length = 2)
    (La Lb : List (List ground.BPair)) (wa wb : List (List Nat))
    (hma : memberchar.mShapeRead sertables.tableG2 La) (hsa : memberchar.symRead sertables.tableG2 La)
    (hda : memberchar.supportRead sertables.tableG2 La wa (natV a)) (hta : memberchar.topRead La (natV a))
    (hra : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) La (natV a))
    (hmb : memberchar.mShapeRead sertables.tableG2 Lb) (hsb : memberchar.symRead sertables.tableG2 Lb)
    (hdb : memberchar.supportRead sertables.tableG2 Lb wb (natV b)) (htb : memberchar.topRead Lb (natV b))
    (hrb : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) Lb (natV b))
    (cs : List (List Nat)) (Ls : List (List (List ground.BPair))) (ws : List (List (List Nat)))
    (hlen : Ls.length = cs.length)
    (hch : ∀ k, k < cs.length →
      (ground.getAt [] cs k).length = 2
        ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] Ls k) (ground.getAt [] ws k)
          (natV (ground.getAt [] cs k))
        ∧ memberchar.topRead (ground.getAt [] Ls k) (natV (ground.getAt [] cs k))
        ∧ memberchar.recRead sertables.tableG2 sertables.fundG2
          (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
          (ground.getAt [] Ls k) (natV (ground.getAt [] cs k)))
    (hexh : ∀ v, ground.countOf v (steinberg.prodFam La Lb)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) Ls) :
    countM sertables.tableG2 sertables.fundG2.gram 16 a b c
      = countM sertables.tableG2 sertables.fundG2.gram 16 b a c := by
  have hseed : (sertables.rhoV sertables.tableG2, false) ∈ orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2) := by
    have h := orbitFam_seed sertables.tableG2 16 (sertables.rhoV sertables.tableG2) (orbit_complete_G2 _ rfl).2.1
    rw [assembly.pnorm_rhoV] at h
    exact h
  have hra' : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) La (poly.pnorm (natV a)) := by
    rw [natV_pnorm]; exact hra
  have hrb' : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) Lb (poly.pnorm (natV b)) := by
    rw [natV_pnorm]; exact hrb
  have hca := multFam_read_G2 a ha _ La hma hsa wa hda hta hseed hra'
  have hcb := multFam_read_G2 b hb _ Lb hmb hsb wb hdb htb hseed hrb'
  have hab := countM_exhaustion_G2 a b c hb hc Lb wb hmb hsb hdb htb hrb cs Ls ws hlen hch
    (fun v => (steinberg.prodFam_counts _ La Lb Lb hca (fun _ => rfl) v).trans (hexh v))
  have hba := countM_exhaustion_G2 b a c ha hc La wa hma hsa hda hta hra cs Ls ws hlen hch
    (fun v => (steinberg.prodFam_counts _ Lb La La hcb (fun _ => rfl) v).trans
      ((steinberg.prodFam_comm Lb La v).trans (hexh v)))
  exact hab.trans hba.symm

/-- The computed G2 row is the support of the product's block
counts at a naturally supported channel exhaustion. -/
theorem rowM_exhaustion_G2 (a b c : List Nat) (ha : a.length = 2) (hb : b.length = 2) (hc : c.length = 2)
    (Lb : List (List ground.BPair)) (wb : List (List Nat))
    (hmb : memberchar.mShapeRead sertables.tableG2 Lb) (hsb : memberchar.symRead sertables.tableG2 Lb)
    (hdb : memberchar.supportRead sertables.tableG2 Lb wb (natV b)) (htb : memberchar.topRead Lb (natV b))
    (hrb : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) Lb (natV b))
    (cs : List (List Nat)) (Ls : List (List (List ground.BPair))) (ws : List (List (List Nat)))
    (hlen : Ls.length = cs.length)
    (hch : ∀ k, k < cs.length →
      (ground.getAt [] cs k).length = 2
        ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] Ls k) (ground.getAt [] ws k)
          (natV (ground.getAt [] cs k))
        ∧ memberchar.topRead (ground.getAt [] Ls k) (natV (ground.getAt [] cs k))
        ∧ memberchar.recRead sertables.tableG2 sertables.fundG2
          (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
          (ground.getAt [] Ls k) (natV (ground.getAt [] cs k)))
    (hexh : ∀ v, ground.countOf v (steinberg.prodFam (multFam sertables.tableG2 sertables.fundG2.gram 16 a) Lb)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) Ls)
    (topWits : List (List Nat))
    (htops : memberchar.supportRead sertables.tableG2 (cs.map natV) topWits (natV (List.zipWith Nat.add a b))) :
    (0 < countM sertables.tableG2 sertables.fundG2.gram 16 a b c ↔
      0 < ground.countOf c (rowM sertables.tableG2 sertables.fundG2.gram 16 a b))
      ∧ ground.countOf c (rowM sertables.tableG2 sertables.fundG2.gram 16 a b) ≤ 1 := by
  apply rowM_supported sertables.tableG2 sertables.fundG2 sertables.fundShape_G2
    sertables.simplePosRead_G2 sertables.rhoDotRead_G2 [[4, 6], [6, 12]] rfl (by decide +kernel)
    sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2
    16 a b ha hb (cs.map natV) topWits htops _ c hc
  intro d hd
  rw [countM_exhaustion_G2 a b d hb hd Lb wb hmb hsb hdb htb hrb cs Ls ws hlen hch hexh,
    countOf_natV_map]

/-- G2's dimension-weighted actual row reads the product of the
Weyl dimensions at every naturally supported tensor exhaustion.
The channel dimensions are their block families' counts. -/
theorem dimM_exhaustion_G2 (a b : List Nat) (ha : a.length = 2) (hb : b.length = 2)
    (La Lb : List (List ground.BPair)) (wa wb : List (List Nat))
    (hma : memberchar.mShapeRead sertables.tableG2 La) (hsa : memberchar.symRead sertables.tableG2 La)
    (hda : memberchar.supportRead sertables.tableG2 La wa (natV a)) (hta : memberchar.topRead La (natV a))
    (hra : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) La (natV a))
    (hmb : memberchar.mShapeRead sertables.tableG2 Lb) (hsb : memberchar.symRead sertables.tableG2 Lb)
    (hdb : memberchar.supportRead sertables.tableG2 Lb wb (natV b)) (htb : memberchar.topRead Lb (natV b))
    (hrb : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) Lb (natV b))
    (cs : List (List Nat)) (Ls : List (List (List ground.BPair))) (ws : List (List (List Nat)))
    (hlen : Ls.length = cs.length)
    (hch : ∀ k, k < cs.length →
      (ground.getAt [] cs k).length = 2
        ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] Ls k) (ground.getAt [] ws k)
          (natV (ground.getAt [] cs k))
        ∧ memberchar.topRead (ground.getAt [] Ls k) (natV (ground.getAt [] cs k))
        ∧ memberchar.recRead sertables.tableG2 sertables.fundG2
          (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
          (ground.getAt [] Ls k) (natV (ground.getAt [] cs k)))
    (hexh : ∀ v, ground.countOf v (steinberg.prodFam La Lb)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) Ls)
    (topWits : List (List Nat))
    (htops : memberchar.supportRead sertables.tableG2 (cs.map natV) topWits
      (natV (List.zipWith Nat.add a b))) :
    ground.famFold Nat.add 0
      (fun c => countM sertables.tableG2 sertables.fundG2.gram 16 a b c * dimM sertables.tableG2 c)
      (rowM sertables.tableG2 sertables.fundG2.gram 16 a b)
      = dimM sertables.tableG2 a * dimM sertables.tableG2 b := by
  have hseed := orbitFam_seed sertables.tableG2 16 (sertables.rhoV sertables.tableG2)
    (orbit_complete_G2 _ rfl).2.1
  rw [assembly.pnorm_rhoV] at hseed
  have hrnorm : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) La (poly.pnorm (natV a)) := by
    rw [natV_pnorm]; exact hra
  have hca := multFam_read_G2 a ha _ La hma hsa wa hda hta hseed hrnorm
  have hexactual (v : List ground.BPair) :
      ground.countOf v (steinberg.prodFam (multFam sertables.tableG2 sertables.fundG2.gram 16 a) Lb)
        = ground.famFold Nat.add 0 (fun L => ground.countOf v L) Ls :=
    (steinberg.prodFam_counts _ La Lb Lb hca (fun _ => rfl) v).trans (hexh v)
  have hcount (c : List Nat) (hc : c.length = 2) :
      countM sertables.tableG2 sertables.fundG2.gram 16 a b c = ground.countOf c cs :=
    countM_exhaustion_G2 a b c hb hc Lb wb hmb hsb hdb htb hrb cs Ls ws hlen hch hexactual
  have hrow (c : List Nat) (hp : 0 < ground.countOf c cs) :
      ground.countOf c (rowM sertables.tableG2 sertables.fundG2.gram 16 a b) = 1 := by
    obtain ⟨k, hk, he⟩ := ground.getAt_of_mem ([] : List Nat) (ground.mem_of_countOf_pos c cs hp)
    have hc : c.length = 2 := by rw [← he]; exact (hch k hk).1
    have hh := rowM_exhaustion_G2 a b c ha hb hc Lb wb hmb hsb hdb htb hrb
      cs Ls ws hlen hch hexactual topWits htops
    have hm : 0 < countM sertables.tableG2 sertables.fundG2.gram 16 a b c := by
      rw [hcount c hc]; exact hp
    exact Nat.le_antisymm hh.2 (hh.1.mp hm)
  have hdim (k : Nat) (hk : k < cs.length) :
      (ground.getAt [] Ls k).length = dimM sertables.tableG2 (ground.getAt [] cs k) := by
    have h := hch k hk
    exact (dimM_family_G2 _ h.1 _ _ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2).symm
  have hprod := steinberg.prodFam_dimension ([] : List Nat) (dimM sertables.tableG2)
    (multFam sertables.tableG2 sertables.fundG2.gram 16 a) Lb cs
    (rowM sertables.tableG2 sertables.fundG2.gram 16 a b) Ls hlen hdim hexactual hrow
  have hfold : ground.famFold Nat.add 0
      (fun c => countM sertables.tableG2 sertables.fundG2.gram 16 a b c * dimM sertables.tableG2 c)
      (rowM sertables.tableG2 sertables.fundG2.gram 16 a b)
      = ground.famFold Nat.add 0 (fun c => ground.countOf c cs * dimM sertables.tableG2 c)
        (rowM sertables.tableG2 sertables.fundG2.gram 16 a b) := by
    apply ground.famFold_congr_members
    intro c hc
    rw [hcount c (rowM_mem sertables.tableG2 sertables.fundG2.gram 16 a b c
      (ground.mem_of_countOf_pos _ _ hc)).1]
  rw [← dimM_multFam_G2 a ha La wa hma hsa hda hta hra,
    ← dimM_family_G2 b hb Lb wb hmb hsb hdb htb hrb] at hprod
  exact hfold.trans hprod

/-- G2's actual unit family at stored fuel is its one zero
content, the unit block's one line (`lem:lowerspan`). -/
theorem multFam_unit_G2 : multFam sertables.tableG2 sertables.fundG2.gram 16 [0, 0]
    = [[ground.BPair.unit, ground.BPair.unit]] :=
  multFam_unit sertables.tableG2 sertables.fundG2.gram 15 sertables.cartanSolve_G2.1
    sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2

/-- G2's actual left-unit fusion count is the label equality
read at every width-matched pair of labels. -/
theorem countM_unit_left_G2 (b c : List Nat) (hb : b.length = 2) (hc : c.length = 2) :
    countM sertables.tableG2 sertables.fundG2.gram 16 [0, 0] b c = if c = b then 1 else 0 :=
  countM_unit_left sertables.tableG2 sertables.fundG2.gram 16 [0, 0] multFam_unit_G2 b c hb hc

/-- G2's actual left-unit row is its second label alone, at
every label of the member's width. -/
theorem rowM_unit_left_G2 (b : List Nat) (hb : b.length = 2) :
    rowM sertables.tableG2 sertables.fundG2.gram 16 [0, 0] b = [b] := by
  apply rowM_unit_left sertables.tableG2 sertables.fundG2.gram 16 multFam_unit_G2 b hb
  exact domKeys_top sertables.tableG2 [[4, 6], [6, 12]] rfl (by decide +kernel)
    sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2 b hb

/-- G2's computed fusion count reads any valid first block
family in the actual shifted orbit convolution. -/
theorem countM_family_G2 (a b c : List Nat) (ha : a.length = 2) (hb : b.length = 2) (hc : c.length = 2)
    (W : List (List ground.BPair × Bool)) (L : List (List ground.BPair))
    (hmsh : memberchar.mShapeRead sertables.tableG2 L) (hsym : memberchar.symRead sertables.tableG2 L)
    (wits : List (List Nat)) (hsupp : memberchar.supportRead sertables.tableG2 L wits (natV a))
    (htop : memberchar.topRead L (natV a)) (hseed : (sertables.rhoV sertables.tableG2, false) ∈ W)
    (hrec : memberchar.recRead sertables.tableG2 sertables.fundG2 W L (poly.pnorm (natV a))) :
    countM sertables.tableG2 sertables.fundG2.gram 16 a b c =
      memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)) L (shiftV sertables.tableG2 c) false
        - memberchar.convCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)) L (shiftV sertables.tableG2 c) true := by
  have hcounts := multFam_read_G2 a ha W L hmsh hsym wits hsupp htop hseed hrec
  rw [countM_conv_G2 sertables.fundG2.gram a b c hb hc,
    memberchar.convCount_counts _ _ L hcounts _ false, memberchar.convCount_counts _ _ L hcounts _ true]

/-- Steinberg's additive channel identity identifies the actual
G2 count at its stored fuel, with the first block's mathematical
family and its trace reads explicit. -/
theorem countM_channel_G2 (a b c : List Nat) (ha : a.length = 2) (hb : b.length = 2) (hc : c.length = 2)
    (W : List (List ground.BPair × Bool)) (L : List (List ground.BPair))
    (hmsh : memberchar.mShapeRead sertables.tableG2 L) (hsym : memberchar.symRead sertables.tableG2 L)
    (wits : List (List Nat)) (hsupp : memberchar.supportRead sertables.tableG2 L wits (natV a))
    (htop : memberchar.topRead L (natV a)) (hseed : (sertables.rhoV sertables.tableG2, false) ∈ W)
    (hrec : memberchar.recRead sertables.tableG2 sertables.fundG2 W L (poly.pnorm (natV a)))
    (tops : List (List ground.BPair))
    (hr : steinberg.memberAt sertables.tableG2 (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 b)) L tops (natV c)) :
    countM sertables.tableG2 sertables.fundG2.gram 16 a b c = ground.countOf (natV c) tops := by
  rw [countM_family_G2 a b c ha hb hc W L hmsh hsym wits hsupp htop hseed hrec]
  change ground.countOf (natV c) tops + memberchar.convCount _ L (shiftV sertables.tableG2 c) true
    = memberchar.convCount _ L (shiftV sertables.tableG2 c) false at hr
  rw [← hr, ground.addSubSelfR]

/-- The actual G2 count at the Cartan sum is one. Natural
support forces the two factors' top keys to be the only pair
joining to that target. -/
theorem countM_cartan_G2 (a b : List Nat) (ha : a.length = 2) (hb : b.length = 2)
    (W : List (List ground.BPair × Bool)) (L : List (List ground.BPair))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (wits : List (List Nat)) (hd : memberchar.supportRead sertables.tableG2 L wits (natV a))
    (ht : memberchar.topRead L (natV a)) (hseed : (sertables.rhoV sertables.tableG2, false) ∈ W)
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2 W L (poly.pnorm (natV a))) :
    countM sertables.tableG2 sertables.fundG2.gram 16 a b (List.zipWith Nat.add a b) = 1 := by
  have hw := orbitFam_character_G2 b hb
  have hlam := lamRead_natV sertables.tableG2 a ha
  rw [natV_pnorm] at hlam
  have htop := memberchar.convTopAt sertables.tableG2 sertables.fundG2 _ _ L wits
    (natV a) (shiftV sertables.tableG2 b) (shiftV_length sertables.tableG2 b hb)
    sertables.fundShape_G2 sertables.simplePosRead_G2 sertables.rhoDotRead_G2
    hw.1 hw.2.2.1 hw.2.2.2.1 hm hd ht hlam
  rw [countM_family_G2 a b _ ha hb (ground.length_zipWith Nat.add a b 2 ha hb)
    W L hm hs wits hd ht hseed hr, shiftV_join sertables.tableG2 a b ha hb,
    htop.1, htop.2]

/-- The actual G2 right-unit count is equality at every target,
by the character identity and its dominant graded singleton. -/
theorem countM_unit_right_G2 (a c : List Nat) (ha : a.length = 2) (hc : c.length = 2)
    (L : List (List ground.BPair)) (wits : List (List Nat))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (hd : memberchar.supportRead sertables.tableG2 L wits (natV a))
    (ht : memberchar.topRead L (natV a))
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L (natV a)) :
    countM sertables.tableG2 sertables.fundG2.gram 16 a [0, 0] c = if c = a then 1 else 0 := by
  have hchar := multFam_identity_G2 a ha L wits hm hs hd ht hr (shiftV sertables.tableG2 c)
  have hodd : assembly.wCount (orbitFam sertables.tableG2 16 (shiftV sertables.tableG2 a))
      (shiftV sertables.tableG2 c) true = 0 := by
    rw [orbitFam_dominant_count_G2 a c ha hc true]
    by_cases he : c = a
    · rw [if_pos he]; rfl
    · rw [if_neg he]
  change memberchar.convCount _ _ _ false + assembly.wCount _ _ true
    = memberchar.convCount _ _ _ true + assembly.wCount _ _ false at hchar
  rw [hodd, orbitFam_dominant_count_G2 a c ha hc false, Nat.add_zero] at hchar
  rw [countM_conv_G2 sertables.fundG2.gram a [0, 0] c rfl hc]
  change memberchar.convCount (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
      (multFam sertables.tableG2 sertables.fundG2.gram 16 a) (shiftV sertables.tableG2 c) false
    - memberchar.convCount (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
      (multFam sertables.tableG2 sertables.fundG2.gram 16 a) (shiftV sertables.tableG2 c) true = _
  rw [hchar, ground.addSubSelfL]
  rfl

/-- G2's actual right-unit row is its first label alone, from
its block's character reads at every canonical label. -/
theorem rowM_unit_right_G2 (a : List Nat) (ha : a.length = 2)
    (L : List (List ground.BPair)) (wits : List (List Nat))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (hd : memberchar.supportRead sertables.tableG2 L wits (natV a))
    (ht : memberchar.topRead L (natV a))
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2
      (orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L (natV a)) :
    rowM sertables.tableG2 sertables.fundG2.gram 16 a [0, 0] = [a] := by
  have hadd : List.zipWith Nat.add a [0, 0] = a := by
    change List.zipWith (fun x y => x + y) a [0, 0] = a
    rw [ground.zipWith_add_comm]
    exact ground.zipWith_zero_left 2 a ha
  apply rowM_single sertables.tableG2 sertables.fundG2.gram 16 a [0, 0] a
  · rw [hadd]
    exact domKeys_top sertables.tableG2 [[4, 6], [6, 12]] rfl (by decide +kernel)
      sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2 a ha
  · intro c hmem
    exact countM_unit_right_G2 a c ha (domKeys_length _ _ _ c hmem) L wits hm hs hd ht hr

/-- The B trace numerator has no starved moved walk at the
stored fuel, for every rank-width label and accumulator. -/
theorem numAt_complete_B (l : Nat) (hl : 0 < l) (G : elim.Mat)
    (acc : List (List Nat × Nat)) (rdTop : Nat) (m : List Nat) (hm : m.length = l) :
    ∃ n, numAt (sertables.tableB l) G (fusion.wFuel l) acc rdTop m = some n := by
  apply numAt_complete (sertables.tableB l) G (fusion.wFuel l) ?_ acc rdTop m hm
  intro v hv he
  have h := (domWalk_complete_B l hl v hv).2.1
  rw [he] at h
  exact Nat.ne_of_gt hl h.symm

/-- The C trace numerator has no starved moved walk at the
stored fuel, for every rank-width label and accumulator. -/
theorem numAt_complete_C (l : Nat) (hl : 0 < l) (G : elim.Mat)
    (acc : List (List Nat × Nat)) (rdTop : Nat) (m : List Nat) (hm : m.length = l) :
    ∃ n, numAt (sertables.tableC l) G (fusion.wFuel l) acc rdTop m = some n := by
  apply numAt_complete (sertables.tableC l) G (fusion.wFuel l) ?_ acc rdTop m hm
  intro v hv he
  have h := (domWalk_complete_C l hl v hv).2.1
  rw [he] at h
  exact Nat.ne_of_gt hl h.symm

/-- The D trace numerator has no starved moved walk at the
stored fuel, for every rank-width label and accumulator. -/
theorem numAt_complete_D (l : Nat) (hl : 2 ≤ l) (G : elim.Mat)
    (acc : List (List Nat × Nat)) (rdTop : Nat) (m : List Nat) (hm : m.length = l) :
    ∃ n, numAt (sertables.tableD l) G (fusion.wFuel l) acc rdTop m = some n := by
  apply numAt_complete (sertables.tableD l) G (fusion.wFuel l) ?_ acc rdTop m hm
  intro v hv he
  have h := (domWalk_complete_D l hl v hv).2.1
  rw [he] at h
  exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hl) h.symm

/-- The G2 trace numerator returns its finite balance fold at
the stored fuel, for every label and accumulator of the stated shape. -/
theorem numAt_complete_G2 (G : elim.Mat) (acc : List (List Nat × Nat))
    (rdTop : Nat) (m : List Nat) (hm : m.length = 2) :
    ∃ n, numAt sertables.tableG2 G 16 acc rdTop m = some n := by
  apply numAt_complete sertables.tableG2 G 16 ?_ acc rdTop m hm
  intro v hv he
  have h := (domWalk_complete_G2 v hv).2.1
  rw [he] at h
  exact Nat.noConfusion h

/-- The F4 trace numerator returns its finite balance fold at
the stored fuel, for every label and accumulator of the stated shape. -/
theorem numAt_complete_F4 (G : elim.Mat) (acc : List (List Nat × Nat))
    (rdTop : Nat) (m : List Nat) (hm : m.length = 4) :
    ∃ n, numAt sertables.tableF4 G 1200 acc rdTop m = some n := by
  apply numAt_complete sertables.tableF4 G 1200 ?_ acc rdTop m hm
  intro v hv he
  have h := (domWalk_complete_F4 v hv).1
  rw [he] at h
  exact Nat.noConfusion h

/-- The E6 trace numerator returns its finite balance fold at
the stored fuel, for every label and accumulator of the stated shape. -/
theorem numAt_complete_E6 (G : elim.Mat) (acc : List (List Nat × Nat))
    (rdTop : Nat) (m : List Nat) (hm : m.length = 6) :
    ∃ n, numAt sertables.tableE6 G 52000 acc rdTop m = some n := by
  apply numAt_complete sertables.tableE6 G 52000 ?_ acc rdTop m hm
  intro v hv he
  have h := (domWalk_complete_E6 v hv).1
  rw [he] at h
  exact Nat.noConfusion h

/-- The E7 trace numerator returns its finite balance fold at
the stored fuel, for every label and accumulator of the stated shape. -/
theorem numAt_complete_E7 (G : elim.Mat) (acc : List (List Nat × Nat))
    (rdTop : Nat) (m : List Nat) (hm : m.length = 7) :
    ∃ n, numAt sertables.tableE7 G 2903040 acc rdTop m = some n := by
  apply numAt_complete sertables.tableE7 G 2903040 ?_ acc rdTop m hm
  intro v hv he
  have h := (domWalk_complete_E7 v hv).1
  rw [he] at h
  exact Nat.noConfusion h

/-- The E8 trace numerator returns its finite balance fold at
the stored fuel, for every label and accumulator of the stated shape. -/
theorem numAt_complete_E8 (G : elim.Mat) (acc : List (List Nat × Nat))
    (rdTop : Nat) (m : List Nat) (hm : m.length = 8) :
    ∃ n, numAt sertables.tableE8 G 696729600 acc rdTop m = some n := by
  apply numAt_complete sertables.tableE8 G 696729600 ?_ acc rdTop m hm
  intro v hv he
  have h := (domWalk_complete_E8 v hv).1
  rw [he] at h
  exact Nat.noConfusion h

/-- The B dominance walk from any key of a strictly dominant
seed's orbit returns that seed at its canonical representative. -/
theorem domWalk_to_B (l : Nat) (hl : 0 < l) (top v : List ground.BPair)
    (htop : top.length = l)
    (hpos : ∀ i, i < l → ground.BPair.unit < ground.getAt ground.BPair.unit top i)
    (hmem : poly.pnorm v ∈ (sertables.serWeylB l top).map Prod.fst) :
    domWalk (sertables.tableB l) (fusion.wFuel l) (poly.pnorm v) = poly.pnorm top := by
  have hs := sertables.serWeylB_shape l hl top
  apply domWalk_eq_of_top (sertables.tableB l) (sertables.serWeylB l top) hs
    (sertables.serWeylB_regular l hl top htop hpos) (assembly.serWeylB_close l hl top htop hpos)
    top ?_ (fusion.wFuel l) v
    (domWalk_finite_family_keys (sertables.tableB l) (sertables.serWeylB l top) hs
      (assembly.serWeylB_closed l top htop)
      (fun w => elim.dotP (sertables.coordsB w) (sertables.coordsB (sertables.rhoV (sertables.tableB l))))
      (assembly.reflF_B_rho_rise l) (fusion.wFuel l) (fusion.serWeylB_fuel l top).1 v hmem)
  intro p hp hstrict
  exact sertables.serWeylB_strict_top l hl top p.1 htop (hs p hp).1 hpos hstrict p.2 hp

/-- The C dominance walk from any key of a strictly dominant
seed's orbit returns that seed at its canonical representative. -/
theorem domWalk_to_C (l : Nat) (hl : 0 < l) (top v : List ground.BPair)
    (htop : top.length = l)
    (hpos : ∀ i, i < l → ground.BPair.unit < ground.getAt ground.BPair.unit top i)
    (hmem : poly.pnorm v ∈ (sertables.serWeylC l top).map Prod.fst) :
    domWalk (sertables.tableC l) (fusion.wFuel l) (poly.pnorm v) = poly.pnorm top := by
  have hs := sertables.serWeylC_shape l hl top
  apply domWalk_eq_of_top (sertables.tableC l) (sertables.serWeylC l top) hs
    (sertables.serWeylC_regular l hl top htop hpos) (assembly.serWeylC_close l hl top htop hpos)
    top ?_ (fusion.wFuel l) v
    (domWalk_finite_family_keys (sertables.tableC l) (sertables.serWeylC l top) hs
      (assembly.serWeylC_closed l top)
      (fun w => elim.dotP (sertables.coordsC w) (sertables.coordsC (sertables.rhoV (sertables.tableC l))))
      (assembly.reflF_C_rho_rise l) (fusion.wFuel l) (fusion.serWeylC_fuel l top).1 v hmem)
  intro p hp hstrict
  exact sertables.serWeylC_strict_top l hl top p.1 htop (hs p hp).1 hpos hstrict p.2 hp

/-- The D dominance walk from any key of a strictly dominant
seed's orbit returns that seed at its canonical representative. -/
theorem domWalk_to_D (l : Nat) (hl : 2 ≤ l) (top v : List ground.BPair)
    (htop : top.length = l)
    (hpos : ∀ i, i < l → ground.BPair.unit < ground.getAt ground.BPair.unit top i)
    (hmem : poly.pnorm v ∈ (sertables.serWeylD l top).map Prod.fst) :
    domWalk (sertables.tableD l) (fusion.wFuel l) (poly.pnorm v) = poly.pnorm top := by
  have hs := sertables.serWeylD_shape l (Nat.lt_of_lt_of_le (by decide : 0 < 2) hl) top
  apply domWalk_eq_of_top (sertables.tableD l) (sertables.serWeylD l top) hs
    (sertables.serWeylD_regular l hl top htop hpos) (assembly.serWeylD_close l hl top htop hpos)
    top ?_ (fusion.wFuel l) v
    (domWalk_finite_family_keys (sertables.tableD l) (sertables.serWeylD l top) hs
      (assembly.serWeylD_closed l hl top htop)
      (fun w => elim.dotP (sertables.coordsD w) (sertables.coordsD (sertables.rhoV (sertables.tableD l))))
      (assembly.reflF_D_rho_rise l hl) (fusion.wFuel l) (fusion.serWeylD_fuel l top).1 v hmem)
  intro p hp hstrict
  exact sertables.serWeylD_strict_top l hl top p.1 htop (hs p hp).1 hpos hstrict p.2 hp

/-- The B shifted dual walk returns its original rank-width
label at the stored step count. -/
theorem dualM_B (l : Nat) (hl : 0 < l) (a : List Nat) (ha : a.length = l) :
    dualM (sertables.tableB l) (fusion.wFuel l) a = a := by
  have hw := shiftV_length (sertables.tableB l) a ha
  have hwalk := domWalk_to_B l hl (shiftV (sertables.tableB l) a)
    (poly.neg (shiftV (sertables.tableB l) a)) hw (shiftV_pos (sertables.tableB l) a ha)
    (sertables.serWeylB_neg_seed l hl _ hw)
  change (natsOf (domWalk (sertables.tableB l) (fusion.wFuel l)
    (poly.pnorm (poly.neg (shiftV (sertables.tableB l) a))))).map (fun n => n - 1) = a
  rw [hwalk, show poly.pnorm (shiftV (sertables.tableB l) a) = shiftV (sertables.tableB l) a
    from poly.pnorm_pnorm _]
  exact shiftV_unshift (sertables.tableB l) a ha

/-- The C shifted dual walk returns its original rank-width
label at the stored step count. -/
theorem dualM_C (l : Nat) (hl : 0 < l) (a : List Nat) (ha : a.length = l) :
    dualM (sertables.tableC l) (fusion.wFuel l) a = a := by
  have hw := shiftV_length (sertables.tableC l) a ha
  have hwalk := domWalk_to_C l hl (shiftV (sertables.tableC l) a)
    (poly.neg (shiftV (sertables.tableC l) a)) hw (shiftV_pos (sertables.tableC l) a ha)
    (sertables.serWeylC_neg_seed l hl _ hw)
  change (natsOf (domWalk (sertables.tableC l) (fusion.wFuel l)
    (poly.pnorm (poly.neg (shiftV (sertables.tableC l) a))))).map (fun n => n - 1) = a
  rw [hwalk, show poly.pnorm (shiftV (sertables.tableC l) a) = shiftV (sertables.tableC l) a
    from poly.pnorm_pnorm _]
  exact shiftV_unshift (sertables.tableC l) a ha

/-- The D shifted dual walk fixes the label at even width and
exchanges the final two coroots at odd width. -/
theorem dualM_D (k : Nat) (a : List Nat) (ha : a.length = k + 2) :
    dualM (sertables.tableD (k + 2)) (fusion.wFuel (k + 2)) a
      = if (k + 2) % 2 = 0 then a else ground.adjSwap k a := by
  let t := sertables.tableD (k + 2)
  let S := shiftV t a
  have hS : S.length = k + 2 := shiftV_length t a ha
  have hpos : ∀ i, i < k + 2 → ground.BPair.unit < ground.getAt ground.BPair.unit S i := shiftV_pos t a ha
  have hl : 2 ≤ k + 2 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
  have hnorm : poly.pnorm S = S := poly.pnorm_pnorm _
  by_cases heven : (k + 2) % 2 = 0
  · rw [if_pos heven]
    have hwalk := domWalk_to_D (k + 2) hl S (poly.neg S) hS hpos
      (sertables.serWeylD_neg_seed_even (k + 2) hl heven S hS)
    change (natsOf (domWalk t (fusion.wFuel (k + 2)) (poly.pnorm (poly.neg S)))).map (fun n => n - 1) = a
    rw [hwalk, hnorm]
    exact shiftV_unshift t a ha
  · rw [if_neg heven]
    have hodd : (k + 2) % 2 = 1 := by
      have h : ∀ r, r < 2 → r ≠ 0 → r = 1 := by decide +kernel
      exact h _ (Nat.mod_lt _ (by decide)) heven
    have hk : k + 1 < S.length := by rw [hS]; exact Nat.lt_succ_self _
    have ht : (ground.adjSwap k S).length = k + 2 := (ground.length_adjSwap k S).trans hS
    have htp : ∀ i, i < k + 2 → ground.BPair.unit < ground.getAt ground.BPair.unit (ground.adjSwap k S) i := by
      intro i hi
      rw [ground.getAt_adjSwap ground.BPair.unit k S hk i]
      exact hpos _ (ground.swapIx_lt (Nat.lt_trans (Nat.lt_succ_self k) (Nat.lt_succ_self (k + 1)))
        (Nat.lt_succ_self (k + 1)) i hi)
    have hwalk := domWalk_to_D (k + 2) hl (ground.adjSwap k S) (poly.neg S) ht htp
      (sertables.serWeylD_neg_seed_odd k hodd S hS)
    have htn : poly.pnorm (ground.adjSwap k S) = ground.adjSwap k S := by
      change (ground.adjSwap k S).map ground.BPair.norm = _
      rw [← ground.adjSwap_map]
      exact congrArg (ground.adjSwap k) hnorm
    change (natsOf (domWalk t (fusion.wFuel (k + 2)) (poly.pnorm (poly.neg S)))).map (fun n => n - 1) = _
    rw [hwalk, htn]
    change ((ground.adjSwap k S).map ground.BPair.marginN).map (fun n => n - 1) = _
    rw [← ground.adjSwap_map, ← ground.adjSwap_map]
    exact congrArg (ground.adjSwap k) (shiftV_unshift t a ha)

/-- D's dimension is fixed by the exchange of its final two
coroot coordinates, at the positive-root gap product. -/
theorem dimM_forkSwap_D (k : Nat) (a : List Nat) (ha : a.length = k + 2) :
    dimM (sertables.tableD (k + 2)) (ground.adjSwap k a) = dimM (sertables.tableD (k + 2)) a := by
  unfold dimM
  rw [← ground.adjSwap_map,
    serstable.gapProd_forkSwap_D k (a.map (fun n => n + 1)) ((ground.length_map _ a).trans ha)]

/-- G2's stored lowering span starts with its top. Every
later member joins the top at an occupied natural simple fold. -/
theorem blockSpanT_top_tail_G2 (sig : List Bool) (top : slotpower.SVec sig.length)
    (lam : List Nat) (hlam : lam.length = 2)
    (hk : slotpower.keysRead memtable.genG2.keys top) (ho : top.val ≠ [])
    (ht : slotpower.homogRead memtable.genG2 sig top (natV lam)) :
    ∃ tail, slotpower.blockSpanT memtable.genG2 sig top = top :: tail ∧
      ∀ v ∈ tail, ∃ c : List Nat, c.length = 2 ∧ c ≠ [0, 0] ∧
        poly.pnorm (elim.vecAdd (slotpower.weightV memtable.genG2 sig v)
          (assembly.cartanFold sertables.tableG2 c)) = natV lam := by
  let P := fun v : slotpower.SVec sig.length =>
    slotpower.keysRead memtable.genG2.keys v ∧
      ∃ nu : List ground.BPair, ∃ c : List Nat,
        nu.length = 2 ∧ poly.pnorm nu = nu ∧ c.length = 2
        ∧ slotpower.homogRead memtable.genG2 sig v nu
        ∧ poly.pnorm (elim.vecAdd nu (assembly.cartanFold sertables.tableG2 c)) = natV lam
  let R := fun v : slotpower.SVec sig.length => ∃ c : List Nat,
    c.length = 2 ∧ c ≠ [0, 0] ∧
      poly.pnorm (elim.vecAdd (slotpower.weightV memtable.genG2 sig v)
        (assembly.cartanFold sertables.tableG2 c)) = natV lam
  have hnat : (natV lam).length = 2 := (ground.length_map _ lam).trans hlam
  have hseed : P top := by
    refine ⟨hk, natV lam, [0, 0], hnat, natV_pnorm lam, rfl, ht, ?_⟩
    exact assembly.foldNull_key sertables.tableG2 [0, 0] (by decide +kernel)
      (by decide +kernel) (natV lam) hnat (natV_pnorm lam)
  have hstep : ∀ v, P v → ∀ i, i < memtable.genG2.rank →
      (slotpower.lowerT memtable.genG2 sig i v).val ≠ [] →
      P (slotpower.lowerT memtable.genG2 sig i v) ∧ R (slotpower.lowerT memtable.genG2 sig i v) := by
    intro v hv i hi hnon
    obtain ⟨hvk, nu, c, hnu, hcanon, hc, hhom, hjoin⟩ := hv
    let r := ground.getAt [] sertables.tableG2.cartan i
    let next := poly.pnorm (elim.vecAdd nu (poly.neg r))
    have hr : r.length = 2 := elim.rowsLen_getAt sertables.tableG2.cartan i
      (elim.rowsLen_of_sqAt sertables.cartanSolve_G2.1)
      (by rw [elim.sqAt_len sertables.cartanSolve_G2.1]; exact hi)
    have hn : next.length = 2 := (poly.pnorm_length _).trans
      (elim.length_vecAdd nu (poly.neg r) 2 hnu ((poly.length_neg r).trans hr))
    have hhom' := slotpower.homogRead_lowerT_G2 sig i hi v nu hvk hhom
    have hjoin' := assembly.cartanFold_lower_join sertables.tableG2 sertables.cartanSolve_G2.1
      (natV lam) nu hnu hcanon c hc i hi hjoin
    have hne : ground.bumpAt i c ≠ [0, 0] := by
      intro he
      have h := congrArg (fun w => ground.getAt 0 w i) he
      change ground.getAt 0 (ground.bumpAt i c) i = ground.getAt 0 (List.replicate 2 0) i at h
      rw [ground.getAt_bumpAt_self i c (by rw [hc]; exact hi), ground.getAt_replicate_zero] at h
      exact Nat.noConfusion h
    refine ⟨⟨slotpower.keysRead_lowerT memtable.genG2 sig i
      (memtable.genG2_actionKeys i hi).1 (memtable.genG2_actionKeys i hi).2 v hvk,
      next, ground.bumpAt i c, hn, poly.pnorm_pnorm _, (ground.length_bumpAt i c).trans hc,
      hhom', hjoin'⟩, ground.bumpAt i c, (ground.length_bumpAt i c).trans hc, hne, ?_⟩
    rw [slotpower.weightV_homog memtable.genG2 sig _ next hhom' hnon]
    exact hjoin'
  have hpair : ¬ (slotpower.pairT memtable.genG2 (slotpower.unitWtRead memtable.genG2) top top).oneValue ground.BPair.unit := by
    have hu : slotpower.unitWtRead memtable.genG2 = true := by decide +kernel
    rw [hu]
    exact ground.offOfUnitLt (slotpower.pairT_self_pos memtable.genG2 top ho)
  obtain ⟨tail, he, htail⟩ := slotpower.blockSpanT_tail memtable.genG2 sig top memtable.genG2_symmWt
    hpair P R hseed hstep
  exact ⟨tail, he, fun v hv => (htail v hv).2⟩

/-- Every member of G2's stored lowering span has a natural
simple-root witness back to its homogeneous top. -/
theorem blockSpanT_support_G2 (sig : List Bool) (top : slotpower.SVec sig.length)
    (lam : List Nat) (hlam : lam.length = 2)
    (hk : slotpower.keysRead memtable.genG2.keys top) (ho : top.val ≠ [])
    (ht : slotpower.homogRead memtable.genG2 sig top (natV lam)) :
    ∀ v ∈ slotpower.blockSpanT memtable.genG2 sig top,
      ∃ c : List Nat, c.length = 2 ∧
        poly.pnorm (elim.vecAdd (slotpower.weightV memtable.genG2 sig v)
          (assembly.cartanFold sertables.tableG2 c)) = natV lam := by
  obtain ⟨tail, he, htail⟩ := blockSpanT_top_tail_G2 sig top lam hlam hk ho ht
  intro v hv
  rw [he] at hv
  cases hv with
  | head =>
    refine ⟨[0, 0], rfl, ?_⟩
    rw [slotpower.weightV_homog memtable.genG2 sig top (natV lam) ht ho]
    exact assembly.foldNull_key sertables.tableG2 [0, 0] (by decide +kernel) (by decide +kernel)
      (natV lam) ((ground.length_map _ lam).trans hlam) (natV_pnorm lam)
  | tail _ hv =>
    obtain ⟨c, hc, _, hjoin⟩ := htail v hv
    exact ⟨c, hc, hjoin⟩

/-- The stored G2 lowering span has exactly one occurrence
of its top weight. An occupied simple fold cannot return to it. -/
theorem blockSpanT_top_count_G2 (sig : List Bool) (top : slotpower.SVec sig.length)
    (lam : List Nat) (hlam : lam.length = 2)
    (hk : slotpower.keysRead memtable.genG2.keys top) (ho : top.val ≠ [])
    (ht : slotpower.homogRead memtable.genG2 sig top (natV lam)) :
    ground.countOf (natV lam) ((slotpower.blockSpanT memtable.genG2 sig top).map
      (slotpower.weightV memtable.genG2 sig)) = 1 := by
  obtain ⟨tail, he, htail⟩ := blockSpanT_top_tail_G2 sig top lam hlam hk ho ht
  have hnat : (natV lam).length = 2 := (ground.length_map _ lam).trans hlam
  have hzero : poly.pnorm (elim.vecAdd (natV lam) (assembly.cartanFold sertables.tableG2 [0, 0]))
      = natV lam := assembly.foldNull_key sertables.tableG2 [0, 0] (by decide +kernel)
        (by decide +kernel) (natV lam) hnat (natV_pnorm lam)
  have hz : ground.countOf (natV lam) (tail.map (slotpower.weightV memtable.genG2 sig)) = 0 := by
    apply ground.countOf_zero_of_not_mem
    intro hm
    obtain ⟨v, hv, hw⟩ := ground.mem_map_of _ _ _ hm
    obtain ⟨c, hc, hne, hjoin⟩ := htail v hv
    rw [hw] at hjoin
    have h1 := foldWits_eq sertables.tableG2 sertables.cartanSolve_G2.1
      sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2 (natV lam) (natV lam) hnat hnat
      c hc (hjoin.trans (natV_pnorm lam).symm)
    have h0 := foldWits_eq sertables.tableG2 sertables.cartanSolve_G2.1
      sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2 (natV lam) (natV lam) hnat hnat
      [0, 0] rfl (hzero.trans (natV_pnorm lam).symm)
    exact hne (h1.symm.trans h0)
  rw [he]
  change ground.countOf (natV lam) (slotpower.weightV memtable.genG2 sig top
    :: tail.map (slotpower.weightV memtable.genG2 sig)) = 1
  rw [slotpower.weightV_homog memtable.genG2 sig top (natV lam) ht ho, ground.countOf_head, hz]

/-- Every actual G2 block-family key joins its label at a
natural simple-root fold, the witness read through the stored
lowering span and the actual tensor top. -/
theorem blockWeights_join_G2 (a : List Nat) (ha : a.length = 2) :
    ∀ nu ∈ fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a,
      ∃ c : List Nat, c.length = 2 ∧
        poly.pnorm (elim.vecAdd nu (assembly.cartanFold sertables.tableG2 c)) = natV a := by
  let tops := fiber.fundTops memtable.genG2 [none, some (0, 0)]
  obtain ⟨t, htt, htk, htw⟩ := fiber.topOf_weight_G2 a ha
  obtain ⟨u, htu, huo⟩ := fiber.topOf_occupied_G2 a ha
  have hut : u = t := Option.some.inj (htu.symm.trans htt)
  rw [hut] at huo
  have hdegree := fiber.topOf_degree tops a t htt
  intro nu hnu
  obtain ⟨v, hv, hvnu⟩ := ground.mem_map_of _ _ nu hnu
  rw [fiber.blockAt_top memtable.genG2 tops a t htt] at hv
  obtain ⟨w, hw, hwv⟩ := ground.mem_map_of _ _ v hv
  obtain ⟨z, hz, hzw⟩ := ground.mem_map_of _ _ w hw
  have hsp := blockSpanT_support_G2 (List.replicate t.1 false)
    (slotpower.castV (ground.length_replicate false t.1).symm t.2) a ha htk huo htw z hz
  obtain ⟨c, hc, hjoin⟩ := hsp
  refine ⟨c, hc, ?_⟩
  rw [← hvnu, ← hwv, ← hzw]
  change poly.pnorm (elim.vecAdd (slotpower.weightV memtable.genG2
    (List.replicate (fiber.degOf tops a) false) z) (assembly.cartanFold sertables.tableG2 c)) = natV a
  rw [← hdegree]
  exact hjoin

/-- The actual G2 block family contains its label once,
the stored lowering span's one top-content line. -/
theorem blockWeights_topRead_G2 (a : List Nat) (ha : a.length = 2) :
    memberchar.topRead
      (fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a)
      (natV a) := by
  let tops := fiber.fundTops memtable.genG2 [none, some (0, 0)]
  obtain ⟨t, ht, hk, hw⟩ := fiber.topOf_weight_G2 a ha
  obtain ⟨u, hu, ho⟩ := fiber.topOf_occupied_G2 a ha
  have hut : u = t := Option.some.inj (hu.symm.trans ht)
  rw [hut] at ho
  have hdegree := fiber.topOf_degree tops a t ht
  unfold memberchar.topRead fiber.blockWeights
  rw [fiber.blockAt_top memtable.genG2 tops a t ht, ground.map_map]
  have hmap : ((slotpower.blockSpanW memtable.genG2 t.1 false t.2).map
      (fun v => slotpower.weightV memtable.genG2 (List.replicate (fiber.degOf tops a) false)
        (slotpower.castV hdegree v)))
      = (slotpower.blockSpanW memtable.genG2 t.1 false t.2).map
          (slotpower.weightV memtable.genG2 (List.replicate t.1 false)) := by
    apply ground.map_congr_all
    intro v
    change slotpower.weightV memtable.genG2 (List.replicate (fiber.degOf tops a) false) v = _
    rw [← hdegree]
  rw [hmap]
  unfold slotpower.blockSpanW
  rw [ground.map_map]
  exact blockSpanT_top_count_G2 (List.replicate t.1 false)
    (slotpower.castV (ground.length_replicate false t.1).symm t.2) a ha hk ho hw

/-- The actual G2 family passes the support read at the
computed natural witnesses, for every label of width two. -/
theorem blockWeights_support_G2 (a : List Nat) (ha : a.length = 2) :
    memberchar.supportRead sertables.tableG2
      (fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a)
      ((fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a).map
        (foldWits sertables.tableG2 (natV a))) (natV a) := by
  let L := fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a
  refine ⟨ground.length_map _ _, ?_⟩
  intro k hk
  have hmem : ground.getAt [] L k ∈ L := ground.mem_getAt [] L k hk
  have hshape := fiber.blockWeights_shape_G2 a ha _ hmem
  obtain ⟨c, hc, hjoin⟩ := blockWeights_join_G2 a ha _ hmem
  have hnat : (natV a).length = 2 := (ground.length_map _ a).trans ha
  have hp := foldTest_join sertables.tableG2 sertables.cartanSolve_G2.1
    sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2 (natV a) _ hnat hshape.1 c hc
      (hjoin.trans (natV_pnorm a).symm)
  rw [ground.getAt_map [] [] (foldWits sertables.tableG2 (natV a)) L k hk]
  exact (foldWits_read sertables.tableG2 sertables.cartanSolve_G2.1
    sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2 (natV a) _ hnat hshape.1 hp).2.trans
      (natV_pnorm a)

/-- Every actual G2 block-family member has rho height at
or below its label's, through the computed natural support read. -/
theorem blockWeights_height_G2 (a : List Nat) (ha : a.length = 2)
    (nu : List ground.BPair)
    (hnu : nu ∈ fiber.blockWeights memtable.genG2 (fiber.fundTops memtable.genG2 [none, some (0, 0)]) a) :
    sertables.dotB sertables.fundG2 nu (sertables.rhoV sertables.tableG2)
      ≤ sertables.dotB sertables.fundG2 (natV a) (sertables.rhoV sertables.tableG2) :=
  memberchar.supportRead_height sertables.tableG2 sertables.fundG2 sertables.fundShape_G2
    sertables.simplePosRead_G2 sertables.rhoDotRead_G2 _ _ (natV a)
    ((ground.length_map _ a).trans ha) (blockWeights_support_G2 a ha) nu
    (ground.countOf_pos_of_mem hnu)

end memberdata

namespace fusion

/-- The B interface's dual has the rank's width at every input
label, through the completed shifted dominance walk. -/
theorem dual_length_dataB (l : Nat) (hl : 0 < l) (a : List Nat) :
    ((dataB l).dual a).length = l := by
  change (memberdata.dualM (sertables.tableB l) (wFuel l) (memberdata.padN l a)).length = l
  exact memberdata.dualM_length_complete (sertables.tableB l) (wFuel l)
    (fun v hv => (memberdata.domWalk_complete_B l hl v hv).2)
    (memberdata.padN l a) (memberdata.padN_length l a)

/-- The C interface's dual has the rank's width at every input
label, through the completed shifted dominance walk. -/
theorem dual_length_dataC (l : Nat) (hl : 0 < l) (a : List Nat) :
    ((dataC l).dual a).length = l := by
  change (memberdata.dualM (sertables.tableC l) (wFuel l) (memberdata.padN l a)).length = l
  exact memberdata.dualM_length_complete (sertables.tableC l) (wFuel l)
    (fun v hv => (memberdata.domWalk_complete_C l hl v hv).2)
    (memberdata.padN l a) (memberdata.padN_length l a)

/-- The D interface's dual has the rank's width at every input
label, through the completed shifted dominance walk. -/
theorem dual_length_dataD (l : Nat) (hl : 2 ≤ l) (a : List Nat) :
    ((dataD l).dual a).length = l := by
  change (memberdata.dualM (sertables.tableD l) (wFuel l) (memberdata.padN l a)).length = l
  exact memberdata.dualM_length_complete (sertables.tableD l) (wFuel l)
    (fun v hv => (memberdata.domWalk_complete_D l hl v hv).2)
    (memberdata.padN l a) (memberdata.padN_length l a)

/-- Every B interface label is its own dual at the rank padding. -/
theorem dual_dataB (l : Nat) (hl : 0 < l) (a : List Nat) :
    (dataB l).dual a = memberdata.padN l a :=
  memberdata.dualM_B l hl (memberdata.padN l a) (memberdata.padN_length l a)

/-- The B interface's dual applied twice returns the rank padding. -/
theorem dual_invol_dataB (l : Nat) (hl : 0 < l) (a : List Nat) :
    (dataB l).dual ((dataB l).dual a) = memberdata.padN l a := by
  rw [dual_dataB l hl, dual_dataB l hl,
    memberdata.padN_of_length l (memberdata.padN l a) (memberdata.padN_length l a)]

/-- The B interface's dual preserves the cleared Casimir. -/
theorem casDualLaw_dataB (l : Nat) (hl : 0 < l) (a : List Nat) : casDualLaw (dataB l) a := by
  change (dataB l).c2N ((dataB l).dual a) = (dataB l).c2N a
  rw [dual_dataB l hl]
  change memberdata.c2M (sertables.tableB l) (memberdata.gramOf (sertables.tableB l))
    (memberdata.padN l (memberdata.padN l a)) = _
  rw [memberdata.padN_of_length l (memberdata.padN l a) (memberdata.padN_length l a)]
  rfl

/-- The B interface's dual preserves the dimension. -/
theorem dimDualLaw_dataB (l : Nat) (hl : 0 < l) (a : List Nat) : dimDualLaw (dataB l) a := by
  change (dataB l).dim ((dataB l).dual a) = (dataB l).dim a
  rw [dual_dataB l hl]
  change memberdata.dimM (sertables.tableB l) (memberdata.padN l (memberdata.padN l a)) = _
  rw [memberdata.padN_of_length l (memberdata.padN l a) (memberdata.padN_length l a)]
  rfl

/-- Every C interface label is its own dual at the rank padding. -/
theorem dual_dataC (l : Nat) (hl : 0 < l) (a : List Nat) :
    (dataC l).dual a = memberdata.padN l a :=
  memberdata.dualM_C l hl (memberdata.padN l a) (memberdata.padN_length l a)

/-- The C interface's dual applied twice returns the rank padding. -/
theorem dual_invol_dataC (l : Nat) (hl : 0 < l) (a : List Nat) :
    (dataC l).dual ((dataC l).dual a) = memberdata.padN l a := by
  rw [dual_dataC l hl, dual_dataC l hl,
    memberdata.padN_of_length l (memberdata.padN l a) (memberdata.padN_length l a)]

/-- The C interface's dual preserves the cleared Casimir. -/
theorem casDualLaw_dataC (l : Nat) (hl : 0 < l) (a : List Nat) : casDualLaw (dataC l) a := by
  change (dataC l).c2N ((dataC l).dual a) = (dataC l).c2N a
  rw [dual_dataC l hl]
  change memberdata.c2M (sertables.tableC l) (memberdata.gramOf (sertables.tableC l))
    (memberdata.padN l (memberdata.padN l a)) = _
  rw [memberdata.padN_of_length l (memberdata.padN l a) (memberdata.padN_length l a)]
  rfl

/-- The C interface's dual preserves the dimension. -/
theorem dimDualLaw_dataC (l : Nat) (hl : 0 < l) (a : List Nat) : dimDualLaw (dataC l) a := by
  change (dataC l).dim ((dataC l).dual a) = (dataC l).dim a
  rw [dual_dataC l hl]
  change memberdata.dimM (sertables.tableC l) (memberdata.padN l (memberdata.padN l a)) = _
  rw [memberdata.padN_of_length l (memberdata.padN l a) (memberdata.padN_length l a)]
  rfl

/-- The D interface dual fixes the padded label at even rank and
exchanges its final two coroots at odd rank. -/
theorem dual_dataD (l : Nat) (hl : 2 ≤ l) (a : List Nat) :
    (dataD l).dual a = if l % 2 = 0 then memberdata.padN l a
      else ground.adjSwap (l - 2) (memberdata.padN l a) := by
  obtain ⟨k, hk⟩ := Nat.le.dest hl
  rw [Nat.add_comm 2 k] at hk
  rw [← hk, ground.addSubSelfR]
  exact memberdata.dualM_D k (memberdata.padN (k + 2) a) (memberdata.padN_length (k + 2) a)

/-- Applying the D interface's dual twice returns the padded
label, the final exchange being its own involution. -/
theorem dual_invol_dataD (l : Nat) (hl : 2 ≤ l) (a : List Nat) :
    (dataD l).dual ((dataD l).dual a) = memberdata.padN l a := by
  rw [dual_dataD l hl, dual_dataD l hl]
  by_cases heven : l % 2 = 0
  · rw [if_pos heven, if_pos heven, memberdata.padN_of_length l (memberdata.padN l a) (memberdata.padN_length l a)]
  · rw [if_neg heven, if_neg heven, memberdata.padN_of_length l _
      ((ground.length_adjSwap (l - 2) _).trans (memberdata.padN_length l a)), ground.adjSwap_adjSwap]

/-- The D interface's dual preserves the dimension at every rank. -/
theorem dimDualLaw_dataD (l : Nat) (hl : 2 ≤ l) (a : List Nat) : dimDualLaw (dataD l) a := by
  change (dataD l).dim ((dataD l).dual a) = (dataD l).dim a
  rw [dual_dataD l hl]
  by_cases heven : l % 2 = 0
  · rw [if_pos heven]
    change memberdata.dimM (sertables.tableD l) (memberdata.padN l (memberdata.padN l a)) = _
    rw [memberdata.padN_of_length l (memberdata.padN l a) (memberdata.padN_length l a)]
    rfl
  · rw [if_neg heven]
    change memberdata.dimM (sertables.tableD l) (memberdata.padN l (ground.adjSwap (l - 2) (memberdata.padN l a)))
      = memberdata.dimM (sertables.tableD l) (memberdata.padN l a)
    rw [memberdata.padN_of_length l _ ((ground.length_adjSwap (l - 2) _).trans (memberdata.padN_length l a))]
    obtain ⟨k, hk⟩ := Nat.le.dest hl
    rw [Nat.add_comm 2 k] at hk
    rw [← hk, ground.addSubSelfR]
    exact memberdata.dimM_forkSwap_D k _ (memberdata.padN_length (k + 2) a)

/-- The D dual preserves the computed cleared Casimir at every
padded label, including the odd-rank exchange. -/
theorem casDualLaw_dataD (l : Nat) (hl : 2 ≤ l) (a : List Nat) : casDualLaw (dataD l) a := by
  change (dataD l).c2N ((dataD l).dual a) = (dataD l).c2N a
  rw [dual_dataD l hl]
  by_cases heven : l % 2 = 0
  · rw [if_pos heven]
    change memberdata.c2M (sertables.tableD l) (memberdata.gramOf (sertables.tableD l))
      (memberdata.padN l (memberdata.padN l a)) = _
    rw [memberdata.padN_of_length l (memberdata.padN l a) (memberdata.padN_length l a)]
    rfl
  · rw [if_neg heven]
    change memberdata.c2M (sertables.tableD l) (memberdata.gramOf (sertables.tableD l))
      (memberdata.padN l (ground.adjSwap (l - 2) (memberdata.padN l a)))
      = memberdata.c2M (sertables.tableD l) (memberdata.gramOf (sertables.tableD l)) (memberdata.padN l a)
    rw [memberdata.padN_of_length l _ ((ground.length_adjSwap (l - 2) _).trans (memberdata.padN_length l a))]
    obtain ⟨k, hk⟩ := Nat.le.dest hl
    rw [Nat.add_comm 2 k] at hk
    rw [← hk, ground.addSubSelfR]
    exact memberdata.c2M_forkSwap_D k _ (memberdata.padN_length (k + 2) a)

private theorem classFold_zero (l n : Nat) :
    (List.range n).foldl (fun s i => s + (i + 1) * ground.getAt 0 (List.replicate l 0) i) 0 = 0 := by
  rw [ground.foldlSum, Nat.zero_add,
    ground.famFold_congr_all Nat.add 0 _ (fun _ => 0)
      (fun i => by rw [ground.getAt_replicate_self, Nat.mul_zero]),
    ground.famFold_const, Nat.mul_zero]

/-- The odd D class code of the exchanged label is the additive
inverse of the original code in the four-class cycle. -/
theorem clsDOdd_forkSwap (k : Nat) (a : List Nat) (ha : a.length = k + 2) :
    (clsDOdd (k + 2) (ground.adjSwap k a) + clsDOdd (k + 2) a) % 4 = 0 := by
  have hk : k + 1 < a.length := by rw [ha]; exact Nat.lt_succ_self _
  have hf : (List.range k).foldl (fun s i => s + (i + 1) * ground.getAt 0 (ground.adjSwap k a) i) 0
      = (List.range k).foldl (fun s i => s + (i + 1) * ground.getAt 0 a i) 0 := by
    rw [ground.foldlSum, ground.foldlSum]
    apply congrArg (Nat.add 0)
    apply ground.famFold_congr_members
    intro i hi
    have hit := ground.ltOfMem hi
    rw [ground.getAt_adjSwap_ne 0 k a i (Nat.ne_of_lt hit)
      (Nat.ne_of_lt (Nat.lt_trans hit (Nat.lt_succ_self k)))]
  unfold clsDOdd
  rw [ground.addSubSelfR, show k + 2 - 1 = k + 1 from rfl, hf,
    ground.getAt_adjSwap_fst 0 k a hk, ground.getAt_adjSwap_snd 0 k a hk, ground.modAdd]
  have he (w x y : Nat) : (2 * w + y + 3 * x) + (2 * w + x + 3 * y) = 4 * (w + (x + y)) := by
    rw [Nat.add_assoc (2 * w) y (3 * x), Nat.add_assoc (2 * w) x (3 * y),
      Nat.add_add_add_comm (2 * w) (y + 3 * x) (2 * w) (x + 3 * y),
      Nat.add_add_add_comm y (3 * x) x (3 * y), Nat.add_comm y x,
      ← Nat.mul_add 3 x y, Nat.add_comm (x + y) (3 * (x + y)),
      ← Nat.succ_mul 3 (x + y), ← ground.mulAddR 2 2 w, ← Nat.mul_add 4 w (x + y)]
  rw [he, Nat.mul_comm 4, ground.modMulSelf]

/-- B's dual class joins its original class to the unit parity. -/
theorem clsDualLaw_dataB (l : Nat) (hl : 0 < l) (a : List Nat) : clsDualLaw (dataB l) a := by
  change (dataB l).clsAdd ((dataB l).cls ((dataB l).dual a)) ((dataB l).cls a) = (dataB l).cls (dataB l).unit
  rw [dual_dataB l hl]
  change (clsB l (memberdata.padN l (memberdata.padN l a)) + clsB l (memberdata.padN l a)) % 2
    = clsB l (memberdata.padN l (List.replicate l 0))
  rw [memberdata.padN_of_length l _ (memberdata.padN_length l a),
    memberdata.padN_of_length l _ (ground.length_replicate 0 l),
    ← Nat.two_mul, Nat.mul_comm 2, ground.modMulSelf]
  unfold clsB
  rw [ground.getAt_replicate_self]

/-- C's dual class joins its original class to the unit box parity. -/
theorem clsDualLaw_dataC (l : Nat) (hl : 0 < l) (a : List Nat) : clsDualLaw (dataC l) a := by
  change (dataC l).clsAdd ((dataC l).cls ((dataC l).dual a)) ((dataC l).cls a) = (dataC l).cls (dataC l).unit
  rw [dual_dataC l hl]
  change (clsC (memberdata.padN l (memberdata.padN l a)) + clsC (memberdata.padN l a)) % 2
    = clsC (memberdata.padN l (List.replicate l 0))
  rw [memberdata.padN_of_length l _ (memberdata.padN_length l a),
    memberdata.padN_of_length l _ (ground.length_replicate 0 l),
    ← Nat.two_mul, Nat.mul_comm 2, ground.modMulSelf]
  unfold clsC
  rw [classFold_zero]

/-- D's dual class joins its original class to the unit: each
class is its own inverse at even rank, while the final exchange
reverses the four-class cycle at odd rank. -/
theorem clsDualLaw_dataD (l : Nat) (hl : 2 ≤ l) (a : List Nat) : clsDualLaw (dataD l) a := by
  change (dataD l).clsAdd ((dataD l).cls ((dataD l).dual a)) ((dataD l).cls a) = (dataD l).cls (dataD l).unit
  rw [dual_dataD l hl]
  by_cases heven : l % 2 = 0
  · rw [if_pos heven]
    unfold dataD dataOf
    rw [ground.eqBeqOf heven]
    change 2 * ((clsDEven l (memberdata.padN l (memberdata.padN l a)) / 2
        + clsDEven l (memberdata.padN l a) / 2) % 2)
      + (clsDEven l (memberdata.padN l (memberdata.padN l a)) + clsDEven l (memberdata.padN l a)) % 2
        = clsDEven l (memberdata.padN l (List.replicate l 0))
    rw [memberdata.padN_of_length l _ (memberdata.padN_length l a),
      memberdata.padN_of_length l _ (ground.length_replicate 0 l)]
    have hz (n : Nat) : (n + n) % 2 = 0 := by
      rw [← Nat.two_mul, Nat.mul_comm 2, ground.modMulSelf]
    rw [hz, hz]
    unfold clsDEven
    rw [classFold_zero, ground.getAt_replicate_self, ground.getAt_replicate_self]
  · rw [if_neg heven]
    unfold dataD dataOf
    rw [ground.neBeqOf heven]
    change (clsDOdd l (memberdata.padN l (ground.adjSwap (l - 2) (memberdata.padN l a)))
      + clsDOdd l (memberdata.padN l a)) % 4 = clsDOdd l (memberdata.padN l (List.replicate l 0))
    rw [memberdata.padN_of_length l _ ((ground.length_adjSwap (l - 2) _).trans (memberdata.padN_length l a)),
      memberdata.padN_of_length l _ (ground.length_replicate 0 l)]
    have hz : clsDOdd l (List.replicate l 0) = 0 := by
      unfold clsDOdd
      rw [classFold_zero, ground.getAt_replicate_self, ground.getAt_replicate_self]
    rw [hz]
    obtain ⟨k, hk⟩ := Nat.le.dest hl
    rw [Nat.add_comm 2 k] at hk
    rw [← hk, ground.addSubSelfR]
    exact clsDOdd_forkSwap k _ (memberdata.padN_length (k + 2) a)

/-- G2's interface unit row reads every canonical label once. -/
theorem unitRowLaw_dataG2 (b : List Nat) (hb : b.length = 2) : unitRowLaw dataG2 b := by
  change memberdata.rowM sertables.tableG2 sertables.fundG2.gram 16
    (memberdata.padN 2 [0, 0]) (memberdata.padN 2 b) = [b]
  rw [memberdata.padN_of_length 2 [0, 0] rfl, memberdata.padN_of_length 2 b hb]
  exact memberdata.rowM_unit_left_G2 b hb

/-- F4's interface unit row holds at every canonical label,
using the structural unit-family proof at its stored fuel. -/
theorem unitRowLaw_dataF4 (b : List Nat) (hb : b.length = 4) : unitRowLaw dataF4 b := by
  apply unitRowLaw_dataOf sertables.tableF4
    (sertables.adjF4.map (fun r => List.zipWith Nat.mul r sertables.tableF4.lenNums))
    (by decide +kernel) (by decide +kernel) sertables.cartanSolve_F4.1
    sertables.cartanSolve_F4.2.1 sertables.cartanSolve_F4.2.2 1199
    dataF4.cls dataF4.clsAdd dataF4.clsFloorN dataF4.pres b hb

/-- E6's interface unit row holds at every canonical label,
using the structural unit-family proof at its stored fuel. -/
theorem unitRowLaw_dataE6 (b : List Nat) (hb : b.length = 6) : unitRowLaw dataE6 b := by
  apply unitRowLaw_dataOf sertables.tableE6
    (sertables.adjE6.map (fun r => List.zipWith Nat.mul r sertables.tableE6.lenNums))
    (by decide +kernel) (by decide +kernel) sertables.cartanSolve_E6.1
    sertables.cartanSolve_E6.2.1 sertables.cartanSolve_E6.2.2 51999
    dataE6.cls dataE6.clsAdd dataE6.clsFloorN dataE6.pres b hb

/-- E7's interface unit row holds at every canonical label,
using the structural unit-family proof at its stored fuel. -/
theorem unitRowLaw_dataE7 (b : List Nat) (hb : b.length = 7) : unitRowLaw dataE7 b := by
  apply unitRowLaw_dataOf sertables.tableE7
    (sertables.adjE7.map (fun r => List.zipWith Nat.mul r sertables.tableE7.lenNums))
    (by decide +kernel) (by decide +kernel) sertables.cartanSolve_E7.1
    sertables.cartanSolve_E7.2.1 sertables.cartanSolve_E7.2.2 2903039
    dataE7.cls dataE7.clsAdd dataE7.clsFloorN dataE7.pres b hb

/-- E8's interface unit row holds at every canonical label,
using the structural unit-family proof at its stored fuel. -/
theorem unitRowLaw_dataE8 (b : List Nat) (hb : b.length = 8) : unitRowLaw dataE8 b := by
  apply unitRowLaw_dataOf sertables.tableE8
    (sertables.adjE8.map (fun r => List.zipWith Nat.mul r sertables.tableE8.lenNums))
    (by decide +kernel) (by decide +kernel) sertables.cartanSolve_E8.1
    sertables.cartanSolve_E8.2.1 sertables.cartanSolve_E8.2.2 696729599
    dataE8.cls dataE8.clsAdd dataE8.clsFloorN dataE8.pres b hb


/-- G2's left unit count is its interface equality read at
every label spelling, including padded inputs. -/
theorem unitCount_dataG2 (a b : List Nat) :
    dataG2.count dataG2.unit a b = if dataG2.eqL a b then 1 else 0 := by
  apply unitCount_dataOf sertables.tableG2 sertables.fundG2.gram
    sertables.cartanSolve_G2.1 sertables.cartanSolve_G2.2.1 sertables.cartanSolve_G2.2.2
    15 dataG2.cls dataG2.clsAdd dataG2.clsFloorN dataG2.pres a b

/-- F4's left unit count is its interface equality read at
every label spelling, including padded inputs. -/
theorem unitCount_dataF4 (a b : List Nat) :
    dataF4.count dataF4.unit a b = if dataF4.eqL a b then 1 else 0 := by
  apply unitCount_dataOf sertables.tableF4 (sertables.gramRows sertables.tableF4 sertables.adjF4)
    sertables.cartanSolve_F4.1 sertables.cartanSolve_F4.2.1 sertables.cartanSolve_F4.2.2
    1199 dataF4.cls dataF4.clsAdd dataF4.clsFloorN dataF4.pres a b

/-- E6's left unit count is its interface equality read at
every label spelling, including padded inputs. -/
theorem unitCount_dataE6 (a b : List Nat) :
    dataE6.count dataE6.unit a b = if dataE6.eqL a b then 1 else 0 := by
  apply unitCount_dataOf sertables.tableE6 (sertables.gramRows sertables.tableE6 sertables.adjE6)
    sertables.cartanSolve_E6.1 sertables.cartanSolve_E6.2.1 sertables.cartanSolve_E6.2.2
    51999 dataE6.cls dataE6.clsAdd dataE6.clsFloorN dataE6.pres a b

/-- E7's left unit count is its interface equality read at
every label spelling, including padded inputs. -/
theorem unitCount_dataE7 (a b : List Nat) :
    dataE7.count dataE7.unit a b = if dataE7.eqL a b then 1 else 0 := by
  apply unitCount_dataOf sertables.tableE7 (sertables.gramRows sertables.tableE7 sertables.adjE7)
    sertables.cartanSolve_E7.1 sertables.cartanSolve_E7.2.1 sertables.cartanSolve_E7.2.2
    2903039 dataE7.cls dataE7.clsAdd dataE7.clsFloorN dataE7.pres a b

/-- E8's left unit count is its interface equality read at
every label spelling, including padded inputs. -/
theorem unitCount_dataE8 (a b : List Nat) :
    dataE8.count dataE8.unit a b = if dataE8.eqL a b then 1 else 0 := by
  apply unitCount_dataOf sertables.tableE8 (sertables.gramRows sertables.tableE8 sertables.adjE8)
    sertables.cartanSolve_E8.1 sertables.cartanSolve_E8.2.1 sertables.cartanSolve_E8.2.2
    696729599 dataE8.cls dataE8.clsAdd dataE8.clsFloorN dataE8.pres a b


/-- The G2 interface's dimension identity at mathematical block
families and their naturally supported tensor exhaustion. -/
theorem dimLaw_dataG2 (a b : List Nat) (ha : a.length = 2) (hb : b.length = 2)
    (La Lb : List (List ground.BPair)) (wa wb : List (List Nat))
    (hma : memberchar.mShapeRead sertables.tableG2 La) (hsa : memberchar.symRead sertables.tableG2 La)
    (hda : memberchar.supportRead sertables.tableG2 La wa (memberdata.natV a)) (hta : memberchar.topRead La (memberdata.natV a))
    (hra : memberchar.recRead sertables.tableG2 sertables.fundG2
      (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) La (memberdata.natV a))
    (hmb : memberchar.mShapeRead sertables.tableG2 Lb) (hsb : memberchar.symRead sertables.tableG2 Lb)
    (hdb : memberchar.supportRead sertables.tableG2 Lb wb (memberdata.natV b)) (htb : memberchar.topRead Lb (memberdata.natV b))
    (hrb : memberchar.recRead sertables.tableG2 sertables.fundG2
      (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) Lb (memberdata.natV b))
    (cs : List (List Nat)) (Ls : List (List (List ground.BPair))) (ws : List (List (List Nat)))
    (hlen : Ls.length = cs.length)
    (hch : ∀ k, k < cs.length →
      (ground.getAt [] cs k).length = 2
        ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] Ls k) (ground.getAt [] ws k)
          (memberdata.natV (ground.getAt [] cs k))
        ∧ memberchar.topRead (ground.getAt [] Ls k) (memberdata.natV (ground.getAt [] cs k))
        ∧ memberchar.recRead sertables.tableG2 sertables.fundG2
          (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
          (ground.getAt [] Ls k) (memberdata.natV (ground.getAt [] cs k)))
    (hexh : ∀ v, ground.countOf v (steinberg.prodFam La Lb)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) Ls)
    (topWits : List (List Nat))
    (htops : memberchar.supportRead sertables.tableG2 (cs.map memberdata.natV) topWits
      (memberdata.natV (List.zipWith Nat.add a b))) : dimLaw dataG2 a b := by
  change (memberdata.rowM sertables.tableG2 sertables.fundG2.gram 16
    (memberdata.padN 2 a) (memberdata.padN 2 b)).foldl
      (fun acc c => acc + memberdata.countM sertables.tableG2 sertables.fundG2.gram 16
        (memberdata.padN 2 a) (memberdata.padN 2 b) (memberdata.padN 2 c)
          * memberdata.dimM sertables.tableG2 (memberdata.padN 2 c)) 0
    = memberdata.dimM sertables.tableG2 (memberdata.padN 2 a)
      * memberdata.dimM sertables.tableG2 (memberdata.padN 2 b)
  rw [memberdata.padN_of_length 2 a ha, memberdata.padN_of_length 2 b hb,
    ground.foldlSum, Nat.zero_add]
  have hfold : ground.famFold Nat.add 0
      (fun c => memberdata.countM sertables.tableG2 sertables.fundG2.gram 16 a b (memberdata.padN 2 c)
        * memberdata.dimM sertables.tableG2 (memberdata.padN 2 c))
      (memberdata.rowM sertables.tableG2 sertables.fundG2.gram 16 a b)
      = ground.famFold Nat.add 0
        (fun c => memberdata.countM sertables.tableG2 sertables.fundG2.gram 16 a b c
          * memberdata.dimM sertables.tableG2 c)
        (memberdata.rowM sertables.tableG2 sertables.fundG2.gram 16 a b) := by
    apply ground.famFold_congr_members
    intro c hc
    rw [memberdata.padN_of_length 2 c (memberdata.rowM_mem sertables.tableG2 sertables.fundG2.gram
      16 a b c (ground.mem_of_countOf_pos _ _ hc)).1]
  rw [hfold]
  exact memberdata.dimM_exhaustion_G2 a b ha hb La Lb wa wb hma hsa hda hta hra
    hmb hsb hdb htb hrb cs Ls ws hlen hch hexh topWits htops

/-- The G2 interface's Cartan count at the first factor's
mathematical block reads and every canonical second label. -/
theorem cartanLaw_dataG2 (a b : List Nat) (ha : a.length = 2) (hb : b.length = 2)
    (W : List (List ground.BPair × Bool)) (L : List (List ground.BPair))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (wits : List (List Nat)) (hd : memberchar.supportRead sertables.tableG2 L wits (memberdata.natV a))
    (ht : memberchar.topRead L (memberdata.natV a)) (hseed : (sertables.rhoV sertables.tableG2, false) ∈ W)
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2 W L (poly.pnorm (memberdata.natV a))) : cartanLaw dataG2 a b := by
  change memberdata.countM sertables.tableG2 sertables.fundG2.gram 16
    (memberdata.padN 2 a) (memberdata.padN 2 b)
    (memberdata.padN 2 (List.zipWith Nat.add (memberdata.padN 2 a) (memberdata.padN 2 b))) = 1
  rw [memberdata.padN_of_length 2 a ha, memberdata.padN_of_length 2 b hb,
    memberdata.padN_of_length 2 _ (ground.length_zipWith Nat.add a b 2 ha hb)]
  exact memberdata.countM_cartan_G2 a b ha hb W L hm hs wits hd ht hseed hr

/-- G2's right-unit interface count reads padded label equality
at the first block's mathematical character data. -/
theorem rightUnitCount_dataG2 (a c : List Nat)
    (L : List (List ground.BPair)) (wits : List (List Nat))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (hd : memberchar.supportRead sertables.tableG2 L wits (memberdata.natV (memberdata.padN 2 a)))
    (ht : memberchar.topRead L (memberdata.natV (memberdata.padN 2 a)))
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2
      (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L
      (memberdata.natV (memberdata.padN 2 a))) :
    dataG2.count a dataG2.unit c = if dataG2.eqL a c then 1 else 0 := by
  change memberdata.countM sertables.tableG2 sertables.fundG2.gram 16
    (memberdata.padN 2 a) [0, 0] (memberdata.padN 2 c)
      = if memberdata.padN 2 a == memberdata.padN 2 c then 1 else 0
  rw [memberdata.countM_unit_right_G2 _ _ (memberdata.padN_length 2 a) (memberdata.padN_length 2 c)
    L wits hm hs hd ht hr]
  by_cases he : memberdata.padN 2 c = memberdata.padN 2 a
  · rw [if_pos he, he, ground.listEqBeq]; rfl
  · rw [if_neg he, if_neg (fun h => he (ground.listBeqEq h).symm)]

/-- G2's right-unit interface row is its canonical label alone. -/
theorem rightUnitRow_dataG2 (a : List Nat) (ha : a.length = 2)
    (L : List (List ground.BPair)) (wits : List (List Nat))
    (hm : memberchar.mShapeRead sertables.tableG2 L) (hs : memberchar.symRead sertables.tableG2 L)
    (hd : memberchar.supportRead sertables.tableG2 L wits (memberdata.natV a))
    (ht : memberchar.topRead L (memberdata.natV a))
    (hr : memberchar.recRead sertables.tableG2 sertables.fundG2
      (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) L (memberdata.natV a)) :
    dataG2.row a dataG2.unit = [a] := by
  change memberdata.rowM sertables.tableG2 sertables.fundG2.gram 16 (memberdata.padN 2 a) [0, 0] = [a]
  rw [memberdata.padN_of_length 2 a ha]
  exact memberdata.rowM_unit_right_G2 a ha L wits hm hs hd ht hr

/-- G2's interface count exchanges its two factors at their
mathematical block reads and common tensor exhaustion. -/
theorem commLaw_dataG2 (a b c : List Nat) (ha : a.length = 2) (hb : b.length = 2) (hc : c.length = 2)
    (La Lb : List (List ground.BPair)) (wa wb : List (List Nat))
    (hma : memberchar.mShapeRead sertables.tableG2 La) (hsa : memberchar.symRead sertables.tableG2 La)
    (hda : memberchar.supportRead sertables.tableG2 La wa (memberdata.natV a)) (hta : memberchar.topRead La (memberdata.natV a))
    (hra : memberchar.recRead sertables.tableG2 sertables.fundG2
      (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) La (memberdata.natV a))
    (hmb : memberchar.mShapeRead sertables.tableG2 Lb) (hsb : memberchar.symRead sertables.tableG2 Lb)
    (hdb : memberchar.supportRead sertables.tableG2 Lb wb (memberdata.natV b)) (htb : memberchar.topRead Lb (memberdata.natV b))
    (hrb : memberchar.recRead sertables.tableG2 sertables.fundG2
      (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) Lb (memberdata.natV b))
    (cs : List (List Nat)) (Ls : List (List (List ground.BPair))) (ws : List (List (List Nat)))
    (hlen : Ls.length = cs.length)
    (hch : ∀ k, k < cs.length →
      (ground.getAt [] cs k).length = 2
        ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] Ls k) (ground.getAt [] ws k)
          (memberdata.natV (ground.getAt [] cs k))
        ∧ memberchar.topRead (ground.getAt [] Ls k) (memberdata.natV (ground.getAt [] cs k))
        ∧ memberchar.recRead sertables.tableG2 sertables.fundG2
          (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
          (ground.getAt [] Ls k) (memberdata.natV (ground.getAt [] cs k)))
    (hexh : ∀ v, ground.countOf v (steinberg.prodFam La Lb)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) Ls) : commLaw dataG2 a b c := by
  change memberdata.countM sertables.tableG2 sertables.fundG2.gram 16
    (memberdata.padN 2 a) (memberdata.padN 2 b) (memberdata.padN 2 c)
      = memberdata.countM sertables.tableG2 sertables.fundG2.gram 16
        (memberdata.padN 2 b) (memberdata.padN 2 a) (memberdata.padN 2 c)
  rw [memberdata.padN_of_length 2 a ha, memberdata.padN_of_length 2 b hb, memberdata.padN_of_length 2 c hc]
  exact memberdata.countM_comm_G2 a b c ha hb hc La Lb wa wb hma hsa hda hta hra
    hmb hsb hdb htb hrb cs Ls ws hlen hch hexh

/-- G2's interface row contains exactly its positive counts,
once per target, at a naturally supported tensor exhaustion. -/
theorem rowLaw_dataG2 (a b c : List Nat) (ha : a.length = 2) (hb : b.length = 2) (hc : c.length = 2)
    (Lb : List (List ground.BPair)) (wb : List (List Nat))
    (hmb : memberchar.mShapeRead sertables.tableG2 Lb) (hsb : memberchar.symRead sertables.tableG2 Lb)
    (hdb : memberchar.supportRead sertables.tableG2 Lb wb (memberdata.natV b)) (htb : memberchar.topRead Lb (memberdata.natV b))
    (hrb : memberchar.recRead sertables.tableG2 sertables.fundG2
      (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2)) Lb (memberdata.natV b))
    (cs : List (List Nat)) (Ls : List (List (List ground.BPair))) (ws : List (List (List Nat)))
    (hlen : Ls.length = cs.length)
    (hch : ∀ k, k < cs.length →
      (ground.getAt [] cs k).length = 2
        ∧ memberchar.mShapeRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.symRead sertables.tableG2 (ground.getAt [] Ls k)
        ∧ memberchar.supportRead sertables.tableG2 (ground.getAt [] Ls k) (ground.getAt [] ws k)
          (memberdata.natV (ground.getAt [] cs k))
        ∧ memberchar.topRead (ground.getAt [] Ls k) (memberdata.natV (ground.getAt [] cs k))
        ∧ memberchar.recRead sertables.tableG2 sertables.fundG2
          (memberdata.orbitFam sertables.tableG2 16 (sertables.rhoV sertables.tableG2))
          (ground.getAt [] Ls k) (memberdata.natV (ground.getAt [] cs k)))
    (hexh : ∀ v, ground.countOf v (steinberg.prodFam (memberdata.multFam sertables.tableG2 sertables.fundG2.gram 16 a) Lb)
      = ground.famFold Nat.add 0 (fun L => ground.countOf v L) Ls)
    (topWits : List (List Nat))
    (htops : memberchar.supportRead sertables.tableG2 (cs.map memberdata.natV) topWits (memberdata.natV (List.zipWith Nat.add a b))) : rowLaw dataG2 a b c := by
  change (0 < memberdata.countM sertables.tableG2 sertables.fundG2.gram 16
      (memberdata.padN 2 a) (memberdata.padN 2 b) (memberdata.padN 2 c) ↔
    0 < ground.countOf c (memberdata.rowM sertables.tableG2 sertables.fundG2.gram 16
      (memberdata.padN 2 a) (memberdata.padN 2 b))) ∧
    ground.countOf c (memberdata.rowM sertables.tableG2 sertables.fundG2.gram 16
      (memberdata.padN 2 a) (memberdata.padN 2 b)) ≤ 1
  rw [memberdata.padN_of_length 2 a ha, memberdata.padN_of_length 2 b hb, memberdata.padN_of_length 2 c hc]
  exact memberdata.rowM_exhaustion_G2 a b c ha hb hc Lb wb hmb hsb hdb htb hrb
    cs Ls ws hlen hch hexh topWits htops

end fusion
