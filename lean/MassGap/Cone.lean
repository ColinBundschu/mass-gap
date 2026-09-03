import MassGap.Restoration
import MassGap.Divisorid
/-!
`lem:cone` — the cone read: the jump family's momentum structure at
the corner is isotropic at degree two.

The decimated determinant's root locus is the fiber symbol's own on
the decimation's validity cells: at a level point where the
designated pivot's evaluated minor sits off the unit, the cleared
deflation's evaluated determinant reads the unit exactly where the
pencil's own does (`locus_defl`) — the deflation's cleared
evaluation is the evaluated blocks' own deflation
(`cellcount.evalPC_pdefl` at the pivot's block reads,
`cellcount.pivotReads`), `thm:divisorid`(i)'s Schur factor reads
the re-blocked pencil's determinant at the pivot
(`divisorid.deflRoot`), and the re-blocked pencil's determinant is
the pencil's own at the places' permutation (`elim.detL_reindex`,
`def:elim`'s exchanged reads), the key bounds and the joined
length the permutation's own reads (`places.perm_member_reads`).

The symbol's momentum reading enters as a polynomial-valued family
over `thm:restoration`'s momentum grids at one argument — per
monomial of the momentum coordinates the level polynomial at that
monomial — and the two settling moves read at it (`bdInvP`: a grid
of odd coordinate total reads the sum's unit, the reflection, and a
transposed grid reads one value, the transposition), the chord
polynomials' permutation invariance with their momentum reading's
evenness at the deck relation's exchanged roots; the profile read
is the two moves through degree four (`profRead`).  The read
lifts to `thm:restoration`'s invariance at every coefficient key
(`coef_inv`), and the theorem's degree reads follow at the
polynomial carrier: at degree two the family reads the isotropic
square, the level polynomial at `K_1²`'s grid scaled by the
square's own indicator at every grid of the box (`deg2_iso` at
`restoration.deg2_span`); the odd degrees read the sum's unit at
every grid (`odd_vac` at `restoration.oddDeg_vanish`); and at
degree four the doubled family reads the two direction data, the
cross monomial's and the quartic's level polynomials (`deg4_dir`
at `restoration.deg4_span`), the quartic off the isotropic span at
every direction count from two (`restoration.deg4_indep`,
`restoration.quartic_breaks`); the profile's three reads join at
`cone_read`.

The located coefficient per root: at a located root of the unit
monomial's symbol `S₀` — `lem:stage`'s extension at its bracket and
its isolation at half `thm:windowsep`'s separation, the root simple
there — the derivative's unit witness `u S₀' + v S = c` clears at
the extension's monic `S` (`stage.witnessRead`), the root read
bundling the bracket, the isolation, the root and the witness
(`rootRead`); the coefficient is the quotient at the witness, its
cofactor the isotropic coefficient's polynomial against the witness
reduced at the extension and swapped memberwise (`locCoef`), one
stage element per root over the clearing `c`, at the identity
`ā S₀' + c S₂` read equal members by the reduction (`locCoef_read`:
`S₂ u S₀'` against `S₂ (c + (v S)ˇ)`, the quotient's multiple of
`S` at the sum's unit under the descent's naming identity and its
uniqueness, `poly.div_identity`, `poly.div_unique`); at the profile
the symbol at the unit monomial's grid is the root's polynomial and
the symbol at the square's grid the coefficient's (`prof_coef`).
-/

namespace cone
open ground poly

/-- The unit monomial's grid at one argument: every coordinate at
the vacant exponent. -/
def vacG (d : Nat) : List (List Nat) := [List.replicate d 0]

/-- The isotropic square's first monomial, `K_1²`'s grid at one
argument (`restoration.ipGrid` at the repeated argument and the
first coordinate). -/
def isoG (d : Nat) : List (List Nat) := restoration.ipGrid 1 d 0 0 0

/-- The two settling moves at a polynomial-valued family over the
momentum grids of one argument, a stated direction count and
degree: at every grid of the box a coordinate of odd total reads
the family at the sum's unit (the reflection), and a transposed
grid reads one value with the grid (the transposition) —
`thm:restoration`'s invariance at the symbol's level polynomials. -/
def bdInvP (d D : Nat) (F : List (List Nat) → Poly) : Prop :=
  ((restoration.momBox 1 d D).all (fun g =>
    ((List.range d).all (fun i =>
      restoration.dirTot i g % 2 == 0 || decide (unitTail (F g))))
    && ((List.range d).all (fun i => (List.range d).all (fun j =>
      !decide (i < j)
        || decide (oneValue (F (restoration.swapDirs i j g)) (F g))))))) = true

instance (d D : Nat) (F : List (List Nat) → Poly) :
    Decidable (bdInvP d D F) :=
  inferInstanceAs (Decidable (_ = _))

/-- The symbol's momentum profile: the two settling moves at every
degree through four. -/
def profRead (d : Nat) (F : List (List Nat) → Poly) : Prop :=
  bdInvP d 1 F ∧ bdInvP d 2 F ∧ bdInvP d 3 F ∧ bdInvP d 4 F

instance (d : Nat) (F : List (List Nat) → Poly) :
    Decidable (profRead d F) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The profile's invariance lifts to every coefficient key: the
family of one key's coefficients is `thm:restoration`'s invariant
family at the box. -/
theorem coef_inv (d D : Nat) (F : List (List Nat) → Poly)
    (h : bdInvP d D F) (k : Nat) :
    restoration.bdInvAt 1 d D (fun g => getAt BPair.unit (F g) k) := by
  refine restoration.bdInvAt_intro 1 d D _ ?_ ?_
  · intro g hg i hi
    have hread := ground.all_of_mem _ (restoration.momBox 1 d D) h g
      (ground.mem_of_countOf_pos g _ hg)
    have hs := ground.andSplitB hread
    have h1 := ground.all_range_read d hs.1 i hi
    cases hpar : (restoration.dirTot i g % 2 == 0) with
    | true => rfl
    | false =>
      rw [hpar] at h1
      have h2 : decide (unitTail (F g)) = true := h1
      rw [decide_eq_true (getAt_unitTail (of_decide_eq_true h2) k)]
      rfl
  · intro g hg i j hij hj
    have hread := ground.all_of_mem _ (restoration.momBox 1 d D) h g
      (ground.mem_of_countOf_pos g _ hg)
    have hs := ground.andSplitB hread
    have h1 := ground.all_range_read d hs.2 i (Nat.lt_trans hij hj)
    have h2 := ground.all_range_read d h1 j hj
    rw [decide_eq_true hij] at h2
    have h3 : decide (oneValue (F (restoration.swapDirs i j g)) (F g))
        = true := h2
    exact oneValue_getAt k (of_decide_eq_true h3)

/-- The degree-two read is the isotropic square: at every grid of
the degree-two box the family reads the level polynomial at
`K_1²`'s grid scaled by the square's own indicator, the sum's unit
at the cross monomials (`thm:restoration`'s rings-coincide clause
at the symbol). -/
theorem deg2_iso (d : Nat) (F : List (List Nat) → Poly)
    (h : bdInvP d 2 F) (g : List (List Nat))
    (hg : 0 < ground.countOf g (restoration.momBox 1 d 2)) :
    oneValue (F g)
      (scaleP (restoration.ipFam 1 d 0 0 g) (F (isoG d))) := by
  refine ov_of_getAt (fun k => ?_)
  have h1 := restoration.deg2_span 1 d (fun g => getAt BPair.unit (F g) k)
    (coef_inv d 2 F h k) g hg
  have h2 : (getAt BPair.unit (F g) k).oneValue
      (BPair.unit
        + getAt BPair.unit (F (isoG d)) k * restoration.ipFam 1 d 0 0 g) :=
    h1
  refine BPair.oneValue_trans h2 ?_
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
  exact BPair.oneValue_symm (getAt_scaleP _ _ k)

/-- The odd degrees read the sum's unit at every grid of their box:
the momentum reading is even in each coordinate. -/
theorem odd_vac (d D : Nat) (hD : D % 2 = 1) (F : List (List Nat) → Poly)
    (h : bdInvP d D F) (g : List (List Nat))
    (hg : 0 < ground.countOf g (restoration.momBox 1 d D)) :
    unitTail (F g) :=
  unitTail_of_getAt (fun k =>
    restoration.oddDeg_vanish 1 d D hD _ (coef_inv d D F h k) g hg)

/-- The degree-four read is the two direction data: at every grid
of the degree-four box the doubled family reads the cross
monomial's level polynomial scaled by the grid's splitting count
joined to the quartic's doubled polynomial against the cross
polynomial's swap, scaled by the quartic's own indicator
(`thm:restoration`'s degree-four clause at the symbol). -/
theorem deg4_dir (d : Nat) (F : List (List Nat) → Poly)
    (h : bdInvP d 4 F) (g : List (List Nat))
    (hg : 0 < ground.countOf g (restoration.momBox 1 d 4)) :
    oneValue (add (F g) (F g))
      (add (scaleP (restoration.prodIP 1 d 0 0 0 0 g)
          (F (restoration.crossG d 0 1)))
        (scaleP (restoration.quFam 1 d 0 g)
          (add (add (F (restoration.quGrid 1 d 0 0))
              (F (restoration.quGrid 1 d 0 0)))
            (neg (F (restoration.crossG d 0 1)))))) := by
  refine ov_of_getAt (fun k => ?_)
  have h1 := restoration.deg4_span d (fun g => getAt BPair.unit (F g) k)
    (coef_inv d 4 F h k) g hg
  refine BPair.oneValue_trans (getAt_add (F g) (F g) k) ?_
  refine BPair.oneValue_trans h1 ?_
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (getAt_add _ _ k) ?_
  refine BPair.add_congr ?_ ?_
  · refine BPair.oneValue_trans (getAt_scaleP _ _ k) ?_
    exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
  · refine BPair.oneValue_trans (getAt_scaleP _ _ k) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
    refine BPair.mul_congr_left ?_
    refine BPair.oneValue_trans (getAt_add _ _ k) ?_
    refine BPair.add_congr (getAt_add _ _ k) ?_
    rw [getAt_neg]
    exact BPair.oneValue_refl _

/-- The cone read at the profile: the degree-two families read the
isotropic square, the odd degrees read the sum's unit, and the
degree-four families read the direction data — the loci isotropic
at degree two with the direction reads two momentum degrees
down. -/
theorem cone_read (d : Nat) (F : List (List Nat) → Poly)
    (h : profRead d F) :
    (∀ g : List (List Nat), 0 < ground.countOf g (restoration.momBox 1 d 2) →
      oneValue (F g)
        (scaleP (restoration.ipFam 1 d 0 0 g) (F (isoG d))))
    ∧ (∀ g : List (List Nat), 0 < ground.countOf g (restoration.momBox 1 d 1) →
        unitTail (F g))
    ∧ (∀ g : List (List Nat), 0 < ground.countOf g (restoration.momBox 1 d 3) →
        unitTail (F g))
    ∧ (∀ g : List (List Nat), 0 < ground.countOf g (restoration.momBox 1 d 4) →
        oneValue (add (F g) (F g))
          (add (scaleP (restoration.prodIP 1 d 0 0 0 0 g)
              (F (restoration.crossG d 0 1)))
            (scaleP (restoration.quFam 1 d 0 g)
              (add (add (F (restoration.quGrid 1 d 0 0))
                  (F (restoration.quGrid 1 d 0 0)))
                (neg (F (restoration.crossG d 0 1))))))) :=
  ⟨fun g hg => deg2_iso d F h.2.1 g hg,
   fun g hg => odd_vac d 1 rfl F h.1 g hg,
   fun g hg => odd_vac d 3 rfl F h.2.2.1 g hg,
   fun g hg => deg4_dir d F h.2.2.2 g hg⟩

/-! The located coefficient per root: `lem:stage`'s extension at a
root of the unit monomial's symbol with the derivative's unit
witness, and the cofactor at the witness. -/

/-- The located coefficient's cofactor at a root: the isotropic
coefficient's polynomial against the derivative's unit witness
reduced at the extension and swapped memberwise, the coefficient
this cofactor over the witness's clearing. -/
def locCoef (E : stage.Ext) (S2 u : Poly) : Poly :=
  neg (div E.pol (mul S2 u)).2

/-- The root read: the extension's bracket with its isolation at
half the separation, the unit monomial's symbol at the root, and
the derivative's unit witness cleared at the extension's monic. -/
def rootRead (E : stage.Ext) (S0 u v : Poly) (c : BPair) (wn wd : Pos) :
    Prop :=
  stage.bracketRead E ∧ stage.isolRead E wn wd ∧ stage.reduceRead E S0
  ∧ stage.witnessRead E (deriv S0) u v c

instance (E : stage.Ext) (S0 u v : Poly) (c : BPair) (wn wd : Pos) :
    Decidable (rootRead E S0 u v c wn wd) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A member's swap withdraws from a sum holding the member. -/
private theorem swap_add_mid (x y z : BPair) :
    (x.swap + (y + x + z)).oneValue (y + z) := by
  rw [BPair.add_comm x.swap, BPair.add_right_comm y x z,
    BPair.add_assoc (y + z) x, BPair.add_comm x x.swap, ← BPair.add_assoc]
  exact BPair.add_swap_self (y + z) x

/-- A polynomial's negation withdraws from a sum holding the
polynomial. -/
private theorem neg_add_mid (X Y Z : Poly) :
    oneValue (add (neg X) (add (add Y X) Z)) (add Y Z) :=
  ov_of_getAt (fun k => by
    refine BPair.oneValue_trans (getAt_add _ _ k) ?_
    rw [getAt_neg]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (getAt_add _ _ k)
          (BPair.add_congr (getAt_add _ _ k) (BPair.oneValue_refl _)))) ?_
    refine BPair.oneValue_trans (swap_add_mid _ _ _) ?_
    exact BPair.oneValue_symm (getAt_add _ _ k))

/-- The located coefficient's identity: at the derivative's unit
witness the cofactor against the derivative joined to the
clearing's multiple of the isotropic polynomial reads equal members
at the root, `ā S₀' + c S₂` the extension's multiple by the
descent's naming identity and its uniqueness. -/
theorem locCoef_read (E : stage.Ext) (S0 S2 u v : Poly) (c : BPair)
    (hw : stage.witnessRead E (deriv S0) u v c) :
    stage.reduceRead E
      (add (mul (locCoef E S2 u) (deriv S0)) (scaleP c S2)) := by
  have hdiv := div_identity E.pol (mul S2 u)
  have hc : oneValue (scaleP c S2)
      (add (mul S2 (mul u (deriv S0)))
        (mul S2 (mul v (monic E.pol)))) :=
    oneValue_trans (scaleP_single c S2)
      (oneValue_trans (mul_congr S2 (oneValue_symm hw.2)) (mul_sum S2 _ _))
  have h1 : oneValue (mul S2 (mul u (deriv S0)))
      (add (mul (mul (monic E.pol) (div E.pol (mul S2 u)).1) (deriv S0))
        (mul (div E.pol (mul S2 u)).2 (deriv S0))) :=
    oneValue_trans (oneValue_symm (mul_assoc S2 u (deriv S0)))
      (oneValue_trans (mul_congr_left (oneValue_symm hdiv) (deriv S0))
        (sum_mul _ _ (deriv S0)))
  have h2 : oneValue (mul S2 (mul v (monic E.pol)))
      (mul (monic E.pol) (mul S2 v)) :=
    oneValue_trans (oneValue_symm (mul_assoc S2 v (monic E.pol)))
      (mul_comm _ _)
  have h3 : oneValue
      (mul (mul (monic E.pol) (div E.pol (mul S2 u)).1) (deriv S0))
      (mul (monic E.pol) (mul (div E.pol (mul S2 u)).1 (deriv S0))) :=
    mul_assoc _ _ _
  have h4 : oneValue (mul (locCoef E S2 u) (deriv S0))
      (neg (mul (div E.pol (mul S2 u)).2 (deriv S0))) :=
    neg_prod_left _ _
  have hP : oneValue (add (mul (locCoef E S2 u) (deriv S0)) (scaleP c S2))
      (mul (monic E.pol)
        (add (mul (div E.pol (mul S2 u)).1 (deriv S0)) (mul S2 v))) := by
    refine oneValue_trans (add_congr h4
      (oneValue_trans hc
        (add_congr (oneValue_trans h1 (add_congr h3 (oneValue_refl _)))
          h2))) ?_
    refine oneValue_trans (neg_add_mid _ _ _) ?_
    exact oneValue_symm (mul_sum _ _ _)
  have hR := (div_unique E.pol
    (add (mul (locCoef E S2 u) (deriv S0)) (scaleP c S2))
    (add (mul (div E.pol (mul S2 u)).1 (deriv S0)) (mul S2 v))
    (List.replicate E.pol.length BPair.unit)
    (ground.length_replicate _ _)
    (oneValue_trans (add_unitTail _ (unitTail_replicate _))
      (oneValue_symm hP))).2
  exact unitTail_oneValue_right (unitTail_replicate _) hR

/-- The located coefficient at the profile: the root read at the
symbol's unit-monomial polynomial gives the cofactor's identity at
the symbol's square polynomial, one stage element per root of the
jump family's momentum profile. -/
theorem prof_coef (d : Nat) (F : List (List Nat) → Poly) (E : stage.Ext)
    (u v : Poly) (c : BPair) (wn wd : Pos)
    (h : rootRead E (F (vacG d)) u v c wn wd) :
    stage.reduceRead E
      (add (mul (locCoef E (F (isoG d)) u) (deriv (F (vacG d))))
        (scaleP c (F (isoG d)))) :=
  locCoef_read E (F (vacG d)) (F (isoG d)) u v c h.2.2.2

/-! The decimated determinant's root locus at the validity cells:
the cleared deflation's evaluated determinant and the pencil's own
read the unit together wherever the designated pivot's evaluated
minor sits off it. -/

/-- The decimated determinant's root locus is the fiber symbol's
own: at a level point where the designated pivot's evaluated minor
sits off the unit, the cleared deflation's evaluated determinant
reads the unit exactly where the pencil's own does — the
deflation's cleared evaluation the evaluated blocks' deflation,
`thm:divisorid`(i)'s Schur factor at the re-blocked pencil, and the
re-blocked pencil's determinant the pencil's own at the places'
permutation, the pivot and trailing keys one member of the
permutations. -/
theorem locus_defl {o : Nat} (S : split.PMat) (K : Nat)
    (idx rest : List Nat) (ln : BPair) (c : Pos)
    (hsh : cellcount.pShapeAt S o K) (hsym : split.pSymAt S o)
    (hk : idx.length = 1 ∨ idx.length = 2)
    (hperm : 0 < ground.countOf (idx ++ rest) (places.perms o))
    (hpiv : ¬ (elim.minor
      (elim.selM idx idx (cellcount.evalPC S ln c K))).oneValue
        BPair.unit) :
    (elim.minor (cellcount.evalPC (cellcount.pdefl idx rest S) ln c
        ((2 * idx.length + 1) * K))).oneValue BPair.unit
      ↔ (elim.minor (cellcount.evalPC S ln c K)).oneValue BPair.unit := by
  obtain ⟨hsgl, _, hbnd, _⟩ := places.perm_member_reads hperm
  have hidx : (idx.all (fun i => Nat.blt i o)) = true :=
    ground.all_of_getAt 0 _ idx (fun p hp => ground.ltBlt (hbnd _
      (ground.countOf_append_left _ rest
        (ground.countOf_pos_of_mem (ground.mem_getAt 0 idx p hp)))))
  have hrest : (rest.all (fun j => Nat.blt j o)) = true :=
    ground.all_of_getAt 0 _ rest (fun p hp => ground.ltBlt (hbnd _
      (ground.countOf_append_right _ idx
        (ground.countOf_pos_of_mem (ground.mem_getAt 0 rest p hp)))))
  have hlen : idx.length + rest.length = o := by
    rw [← ground.length_append]; exact hsgl
  have hdefl := cellcount.evalPC_pdefl (o := o) S K idx rest ln c hsh hsym hk
    hidx hrest
  have hMsq : elim.sqAt (cellcount.evalPC S ln c K) o :=
    cellcount.evalPC_sqAt hsh ln c
  have hMsym : elim.matOneValue (elim.transposeM (cellcount.evalPC S ln c K))
      (cellcount.evalPC S ln c K) :=
    elim.matOne_symm (cellcount.evalPC_symAt S o K ln c hsh hsym)
  obtain ⟨hPsq, hBl, hBr, hQsq, hCwl, hCwr, hPs, hPw, hTBl, hCt, hJoin, hJsq⟩ :=
    cellcount.pivotReads _ idx rest o hMsq hMsym hk hidx hrest
  have hroot := divisorid.deflRoot (k := idx.length) (m := rest.length)
    _ _ _ _ hPsq hBl hBr hQsq hCwl hCwr hPs hPw hpiv
  -- the cleared deflation's evaluated determinant is the evaluated
  -- blocks' deflation's
  have hDsq : elim.sqAt (cellcount.evalPC (cellcount.pdefl idx rest S) ln c
      ((2 * idx.length + 1) * K)) rest.length :=
    cellcount.evalPC_sqAt (cellcount.pShape_pdefl S o K idx rest hsh hk) ln c
  have hdet1 : (elim.minor (cellcount.evalPC (cellcount.pdefl idx rest S) ln c
        ((2 * idx.length + 1) * K))).oneValue
      (elim.minor (inertia.deflMat
        (elim.selM idx idx (cellcount.evalPC S ln c K))
        (elim.selM idx rest (cellcount.evalPC S ln c K))
        (elim.selM rest rest (cellcount.evalPC S ln c K))
        (elim.matMul
          (cellcount.adj2v idx.length
            (elim.selM idx idx (cellcount.evalPC S ln c K)))
          (elim.selM idx rest (cellcount.evalPC S ln c K))))) := by
    refine BPair.oneValue_trans (elim.minor_detL _
      (elim.rowsLen_cast (elim.sqAt_len hDsq).symm
        (elim.rowsLen_of_sqAt hDsq))) ?_
    refine BPair.oneValue_trans (elim.detL_congr_letters _ _
      (elim.matOne_length hdefl) (fun a ha b _ =>
        poly.oneValue_getAt b (ground.matched_entry [] hdefl a ha))) ?_
    refine BPair.oneValue_symm (elim.minor_detL _ ?_)
    have hsq := inertia.sqAt_deflMat
      (elim.selM idx idx (cellcount.evalPC S ln c K)) _ _ _ rest.length
      hTBl hCt (elim.sqAt_len hQsq) (elim.rowsLen_of_sqAt hQsq)
    exact elim.rowsLen_cast (elim.sqAt_len hsq).symm
      (elim.rowsLen_of_sqAt hsq)
  -- the re-blocked pencil's determinant is the pencil's own
  have hSl : (elim.selM (idx ++ rest) (idx ++ rest)
      (cellcount.evalPC S ln c K)).length = o := by
    rw [elim.length_selM]; exact hsgl
  have hdet2 : (elim.minor (inertia.blockJoin
        (elim.selM idx idx (cellcount.evalPC S ln c K))
        (elim.selM idx rest (cellcount.evalPC S ln c K))
        (elim.selM rest rest (cellcount.evalPC S ln c K)))).oneValue
      (elim.minor (cellcount.evalPC S ln c K)) := by
    refine BPair.oneValue_trans (elim.minor_detL _
      (elim.rowsLen_cast (elim.sqAt_len hJsq).symm
        (elim.rowsLen_of_sqAt hJsq))) ?_
    refine BPair.oneValue_trans (elim.detL_congr_letters _ _
      (elim.matOne_length (elim.matOne_symm hJoin)) (fun a ha b _ =>
        poly.oneValue_getAt b
          (ground.matched_entry [] (elim.matOne_symm hJoin) a ha))) ?_
    refine BPair.oneValue_trans (elim.detL_reindex o _ _ (idx ++ rest) hperm
      (elim.sqAt_len hMsq) hSl (fun i j hi hj => ?_)) ?_
    · have hi' : i < (idx ++ rest).length := by rw [hsgl]; exact hi
      have hj' : j < (idx ++ rest).length := by rw [hsgl]; exact hj
      show (ground.getAt BPair.unit (ground.getAt []
        (elim.selMO BPair.unit (idx ++ rest) (idx ++ rest)
          (cellcount.evalPC S ln c K)) i) j).oneValue _
      rw [elim.getAt_selMO BPair.unit (idx ++ rest) (idx ++ rest) _ i j hi' hj']
      exact BPair.oneValue_refl _
    · exact BPair.oneValue_symm (elim.minor_detL _
        (elim.rowsLen_cast (elim.sqAt_len hMsq).symm
          (elim.rowsLen_of_sqAt hMsq)))
  exact (BPair.unit_iff hdet1).trans (hroot.trans (BPair.unit_iff hdet2))

end cone
