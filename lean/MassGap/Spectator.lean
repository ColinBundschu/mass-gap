import MassGap.Greenprod
import MassGap.Deckfactor
import MassGap.Split
/-!
`lem:spectator` — the spectator law at two slab families on one
split.  Clause (i): the tail pivots are equal outright beyond the
perturbation (`tailShareRead`, the recursions on equal data from an
equal seed), and the deviation sits in the boundary-direction
pivots alone, the exact sandwich `D_{i+1} = T_iᵀ D_i T'_i` at the
two families' transfer factors (`devQ` the deviation's cleared
datum, `sandwichStep` the one-step read, `sandwichRead` the family
bundle at the shared-data guards) — re-convergence and the Green
products' falloff the one identity, stated twice; the reversed slab
order reads the identity at the tail witnesses, the head pivots equal
below the perturbation slab (`headShareRead`) and the tail deviation
sandwiched down to the head at the tail transfer factors
(`tailSandwichRead`, the one step `sandwichStep` at the witnesses'
places exchanged).  Clause (ii): the
caps propagate geometrically — a transfer factor's certificate
`Tᵀ Gᵢ T ⪯ λ² Gᵢ₊₁` at a cleared pair and the gram's slab blocks
(`contractRead`), a deviation's
two-sided cap at `c G` (`capQ` at `lem:inertia`'s two splits), and
the step's conclusion `2 D_{i+1}` two-sided at
`c (λ² + λ'²) G_{i+1}`, the cap's block the deeper slab's and the
conclusion's its own (`capStepRead`, the two splits at `u + v` and
`u + v̌` the derivation's).  The two clauses' identities are
derived theorems beside their reads: the sandwich at the two head
steps on one slab datum, the joins read against each other at the
one load-bearing symmetry — the witnessed pivot's own — with the
shared summand withdrawn at its swap pair and the witness clearing
riding the goal's own (`sandwich_of_steps`); and the step's price
at the vector level, the cap's two splits at the cross-cleared
combination and its swapped partner collecting the doubled
sandwiched deviation at the committed step read's own constants
(`cap_step_price` at the polarization tier), the committed splits
transported to the vector reads by the bridges (`contract_all`,
`cap_hi`, `cap_lo`).  Clause (iii): the bulk pivot is the
deck-interior solvent — the deck polynomial the determinant of the
quadratic site datum (`deckPMat`, `deckPoly`, its deck symmetry
`lem:deckfactor`'s read), the solvent identity `Bᵀ X² + B = A X`
(`solventRead`), the pivot-identity pair `Y X = B`, `Y + Bᵀ X = A`
(`pivotPairRead`) with the pivot map's step `Y♯ = A + Bᵀ T`
(`pivotStepRead`), and the exact factorization `U = U₁ U₂` at the
cleared factors `z Bᵀ + Bᵀ X - A` and `z - X` (`facSplitRead` at
`split.pmatMul`); the scalar instance is
the walk pencil's bulk datum, the error law
`e_{L+1} = z² e_L + z e_L e_{L+1}` the sandwich's own read there.
The ball certificate carries three counts at a located center —
the pivot map's step there, the transfer factor's contraction at
`λ` pricing the solvent's roots inside, the floor
`Ŷ ⪰ (y0 + ρ) G` (`floorRead`) and the center defect capped at
`ρ0` — beside the modulus data, `λ∘` at `y0 λ∘ = λ (y0 + ρ)` and
`ρ0 + μ ρ ≤ ρ` at `μ = λ∘²` (`ballRead` at `contractRead` and
`capQ`); the ball's membership walk reads each pivot square at the
stated order with its deviation from the center capped two-sidedly
at `ρ G` (`ballList`), and a ball member's every split reads the
upper side — the floor with the cap price the member's form at or
above the sum's unit at every vector, the gram's own positive
read the cap's (`ball_psd`), and the member prices its form at
the floor outright, at or beyond `y0`'s multiple of the gram's
(`ball_floor`, `lem:cornerpivot`(vii)'s handover seed); and the
cap chain iterates clause (ii)'s step down the recursion-named
brackets at the gram list's own slab blocks (`capWalk`).  The
companion kernels over stored towers with the graph read's tower
sign are the emitted certificates' tier at their recorded
consumers (`thm:decimation`(iii)'s deck divisors,
`lem:cornerpivot`(vii)'s block chains, `thm:groundreads`'
windows). -/

namespace spectator
open ground poly elim inertia greenprod

/-- The transposed cleared datum. -/
def transposeQ (a : MatQ) : MatQ := (transposeM a.1, a.2)

/-- The deviation's cleared datum, the site structure at two
pivots. -/
def devQ (Y' Y : MatQ) : MatQ := addQ Y' (swapQ Y)

/-- The doubled datum, the cap display's left side. -/
def doubleQ (a : MatQ) : MatQ := (matScale 2 a.1, a.2)

/-- The sandwich's one step: `D_{i+1} = T_iᵀ D_i T'_i` at the two
families' transfer factors, the shapes at the boundary's two
orders. -/
def sandwichStep (C C' Y1' Y1 Y0' Y0 : MatQ) (n n' : Nat) : Prop :=
  rectAt C.1 n n' ∧ rectAt C'.1 n n'
  ∧ sqAt Y1'.1 n' ∧ sqAt Y1.1 n' ∧ sqAt Y0'.1 n ∧ sqAt Y0.1 n
  ∧ oneValueQ (devQ Y1' Y1)
      (mulQ (transposeQ (transfer C)) (mulQ (devQ Y0' Y0) (transfer C')))

instance (C C' Y1' Y1 Y0' Y0 : MatQ) (n n' : Nat) :
    Decidable (sandwichStep C C' Y1' Y1 Y0' Y0 n n') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ oneValueQ _ _))

/-- A left factor's positive rescaling rides out of the product,
the balance-weight passage at the clearing's own pair. -/
private theorem mulScaleL (w : Pos) (A B : Mat) :
    matOneValue (matMul (matScale w A) B) (matScale w (matMul A B)) :=
  matOne_trans
    (matMul_congrL (matScale w A) (matScaleB (BPair.ofPos w) A) B
      (matScale_scaleB w A))
    (matOne_trans (matMul_scaleL (BPair.ofPos w) A B)
      (matOne_symm (matScale_scaleB w (matMul A B))))

/-- A right factor's positive rescaling rides out of the product,
the balance-weight passage at the clearing's own pair. -/
private theorem mulScaleR (w : Pos) (n : Nat) (A B : Mat)
    (hB : rowsLen n B) :
    matOneValue (matMul A (matScale w B)) (matScale w (matMul A B)) :=
  matOne_trans
    (matMul_congrR_of A (matScale w B) (matScaleB (BPair.ofPos w) B)
      (transposeM_congrM n _ _ (rowsLen_mapRows _ B n hB)
        (rowsLen_scaleB _ n B hB)
        ((length_matScale w B).trans (length_scaleB _ B).symm)
        (matScale_scaleB w B)))
    (matOne_trans (matMul_scaleR (BPair.ofPos w) n A B hB)
      (matOne_symm (matScale_scaleB w (matMul A B))))

/-- The join's move-across: a summand crosses the read at its own
swap, the swap pair withdrawing at the sum's unit. -/
private theorem addMove {o : Nat} (X U V : Mat) (hX : sqAt X o)
    (hU : sqAt U o) (hV : sqAt V o)
    (h : matOneValue (matAdd X U) V) :
    matOneValue U (matAdd V (matSwap X)) := by
  have hXr := rowsLen_of_sqAt hX
  have hUr := rowsLen_of_sqAt hU
  have hSr : rowsLen o (matSwap X) :=
    rowsLen_mapRows BPair.swap X o hXr
  have h1 : matOneValue (matAdd (matAdd (matSwap X) X) U) U :=
    matAdd_nullL _ U (matNull_swap_add (matOne_refl X))
      ((length_matAdd (matSwap X) X (length_matSwap X)).trans
        ((length_matSwap X).trans
          ((sqAt_len hX).trans (sqAt_len hU).symm)))
      (rowsLen_matAdd o _ _ hSr hXr) hUr
  have h2 : matOneValue (matAdd (matSwap X) (matAdd X U))
      (matAdd (matSwap X) V) :=
    matAdd_cong2 o _ _ _ _ hSr (rowsLen_matAdd o X U hXr hUr) hSr
      (rowsLen_of_sqAt hV) (matOne_refl (matSwap X)) h
  have h3 := matOne_symm h1
  rw [matAdd_assoc (matSwap X) X U] at h3
  have h4 := matOne_trans h3 h2
  rw [matAdd_comm (matSwap X) V] at h4
  exact h4

/-- A zero-width matrix's key-list exchange is vacant. -/
private theorem transNil : ∀ (M : Mat), rowsLen 0 M →
    transposeM M = []
  | [], _ => rfl
  | r :: t, h =>
    List.length_eq_zero_iff.mp
      (length_transposeM (r :: t) h (Nat.succ_pos t.length))

private theorem posN1 (a b c d e f : Pos) :
    (d * (e * f)) * (a * (b * c)) = (f * (e * (b * c))) * (a * d) := by
  rw [ground.mul_left_comm (d * (e * f)) a (b * c),
    ground.mul_assoc d (e * f) (b * c),
    ← ground.mul_assoc a d ((e * f) * (b * c)),
    ground.mul_comm (a * d) ((e * f) * (b * c)),
    ground.mul_assoc e f (b * c),
    ground.mul_left_comm e f (b * c)]

private theorem posN2 (a b d e f : Pos) :
    (d * (e * f)) * (b * (a * d)) = (d * (f * (b * (a * d)))) * e := by
  rw [← ground.mul_assoc d e f,
    ground.mul_assoc (d * e) f (b * (a * d)),
    ground.mul_right_comm d e (f * (b * (a * d)))]

private theorem posN3 (a b c d e f : Pos) :
    (f * (e * (b * c))) * (a * d) = ((a * d) * (e * (b * c))) * f := by
  rw [ground.mul_comm (f * (e * (b * c))) (a * d),
    ground.mul_left_comm (a * d) f (e * (b * c)),
    ground.mul_comm f ((a * d) * (e * (b * c)))]

private theorem posN4 (a b c d e f : Pos) :
    (d * (f * (b * (a * d)))) * (e * c)
      = ((a * d) * (e * (b * c))) * (f * d) := by
  rw [ground.mul_comm d (f * (b * (a * d))),
    ground.mul_assoc f (b * (a * d)) d,
    ground.mul_left_comm f (b * (a * d)) d,
    ground.mul_right_comm (b * (a * d)) (f * d) (e * c),
    ground.mul_assoc b (a * d) (e * c),
    ground.mul_left_comm b (a * d) (e * c),
    ground.mul_left_comm b e c]

private theorem posN5 (a b c d e : Pos) :
    (d * (d * ((b * a) * c))) * e = ((a * d) * (e * (b * c))) * d := by
  rw [ground.mul_comm (d * (d * ((b * a) * c))) e,
    ground.mul_left_comm e d (d * ((b * a) * c)),
    ground.mul_comm d (e * (d * ((b * a) * c))),
    ground.mul_comm d ((b * a) * c),
    ground.mul_assoc b a c,
    ground.mul_left_comm b a c,
    ground.mul_right_comm a (b * c) d,
    ground.mul_left_comm e (a * d) (b * c)]

private theorem posN6 (a b c d f : Pos) :
    (d * (d * ((b * a) * c))) * f = (d * (f * (b * (a * d)))) * c := by
  rw [ground.mul_right_comm d (d * ((b * a) * c)) f,
    ground.mul_comm d ((b * a) * c),
    ground.mul_right_comm (b * a) c d,
    ← ground.mul_assoc (d * f) ((b * a) * d) c,
    ground.mul_assoc d f ((b * a) * d),
    ground.mul_assoc b a d]

/-- Clause (i)'s sandwich, derived: at the two head steps on one
slab datum — the joins `Y1 + Bᵀ C = A` and `Y1' + Bᵀ C' = A` at
the witnesses `Y0 C = B` and `Y0' C' = B` — the images' deviation
is the transfer sandwich, the two recursions' joins read against
each other at the pivots' symmetry. -/
theorem sandwich_of_steps {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ)
    (A B : Mat)
    (hC : rectAt C.1 n n') (hC' : rectAt C'.1 n n')
    (hY0 : sqAt Y0.1 n) (hY0' : sqAt Y0'.1 n)
    (hY1 : sqAt Y1.1 n') (hY1' : sqAt Y1'.1 n')
    (hA : sqAt A n') (hB : rectAt B n n')
    (hsym0 : matOneValue (transposeM Y0.1) Y0.1)
    (hw : oneValueQ (mulQ Y0 C) (ofM B))
    (hw' : oneValueQ (mulQ Y0' C') (ofM B))
    (hj : oneValueQ (addQ Y1 (mulQ (ofM (transposeM B)) C)) (ofM A))
    (hj' : oneValueQ (addQ Y1' (mulQ (ofM (transposeM B)) C')) (ofM A)) :
    oneValueQ (devQ Y1' Y1)
      (mulQ (transposeQ (transfer C)) (mulQ (devQ Y0' Y0) (transfer C'))) := by
  cases n' with
  | zero =>
    have hY1'nil : Y1'.1 = [] :=
      List.length_eq_zero_iff.mp (sqAt_len hY1')
    show matOneValue
      (matScale (C.2 * (Y0'.2 * Y0.2 * C'.2))
        (matAdd (matScale Y1.2 Y1'.1)
          (matScale Y1'.2 (matSwap Y1.1))))
      (matScale (Y1'.2 * Y1.2)
        (matMul (transposeM (matSwap C.1))
          (matMul
            (matAdd (matScale Y0.2 Y0'.1)
              (matScale Y0'.2 (matSwap Y0.1)))
            (matSwap C'.1))))
    rw [hY1'nil,
      transNil (matSwap C.1)
        (rowsLen_mapRows BPair.swap C.1 0 (rectAt_rows hC))]
    exact True.intro
  | succ k =>
    cases n with
    | zero =>
      have hj0 : matOneValue
          (matScale Pos.one
            (matAdd (matScale (Pos.one * C.2) Y1.1)
              (matScale Y1.2 (matMul (transposeM B) C.1))))
          (matScale (Y1.2 * (Pos.one * C.2)) A) := hj
      rw [List.length_eq_zero_iff.mp (rectAt_len hB),
        show transposeM ([] : Mat) = [] from rfl,
        show matMul ([] : Mat) C.1 = [] from rfl,
        show matScale Y1.2 ([] : Mat) = [] from rfl,
        matAdd_nil_right (matScale (Pos.one * C.2) Y1.1),
        show matScale Pos.one ([] : Mat) = [] from rfl] at hj0
      exact Nat.noConfusion
        (show (0 : Nat) = k + 1 from
          (matOne_length hj0).trans
            ((length_matScale (Y1.2 * (Pos.one * C.2)) A).trans
              (sqAt_len hA)))
    | succ m =>
      -- the shape reads
      have hCl : C.1.length = m + 1 := rectAt_len hC
      have hCr : rowsLen (k + 1) C.1 := rectAt_rows hC
      have hC'l : C'.1.length = m + 1 := rectAt_len hC'
      have hC'r : rowsLen (k + 1) C'.1 := rectAt_rows hC'
      have hBl : B.length = m + 1 := rectAt_len hB
      have hBr : rowsLen (k + 1) B := rectAt_rows hB
      have hY0l : Y0.1.length = m + 1 := sqAt_len hY0
      have hY0r : rowsLen (m + 1) Y0.1 := rowsLen_of_sqAt hY0
      have hY0'l : Y0'.1.length = m + 1 := sqAt_len hY0'
      have hY0'r : rowsLen (m + 1) Y0'.1 := rowsLen_of_sqAt hY0'
      have hY1l : Y1.1.length = k + 1 := sqAt_len hY1
      have hY1r : rowsLen (k + 1) Y1.1 := rowsLen_of_sqAt hY1
      have hY1'l : Y1'.1.length = k + 1 := sqAt_len hY1'
      have hY1'r : rowsLen (k + 1) Y1'.1 := rowsLen_of_sqAt hY1'
      have hAl : A.length = k + 1 := sqAt_len hA
      have hAr : rowsLen (k + 1) A := rowsLen_of_sqAt hA
      have hTCl : (transposeM C.1).length = k + 1 :=
        length_transposeM C.1 hCr (by rw [hCl]; exact Nat.succ_pos m)
      have hTCr : rowsLen (m + 1) (transposeM C.1) :=
        rowsLen_cast hCl (rowsLen_transposeM C.1)
      have hTC'l : (transposeM C'.1).length = k + 1 :=
        length_transposeM C'.1 hC'r
          (by rw [hC'l]; exact Nat.succ_pos m)
      have hTBl : (transposeM B).length = k + 1 :=
        length_transposeM B hBr (by rw [hBl]; exact Nat.succ_pos m)
      have hTBr : rowsLen (m + 1) (transposeM B) :=
        rowsLen_cast hBl (rowsLen_transposeM B)
      have hWl : (matMul (transposeM B) C.1).length = k + 1 :=
        (length_matMul (transposeM B) C.1).trans hTBl
      have hWr : rowsLen (k + 1) (matMul (transposeM B) C.1) :=
        rowsLen_cast hTCl (rowsLen_matMul (transposeM B) C.1)
      have hW'l : (matMul (transposeM B) C'.1).length = k + 1 :=
        (length_matMul (transposeM B) C'.1).trans hTBl
      have hW'r : rowsLen (k + 1) (matMul (transposeM B) C'.1) :=
        rowsLen_cast hTC'l (rowsLen_matMul (transposeM B) C'.1)
      -- the witnesses and the joins, cleared
      have hwA : matOneValue (matScale Pos.one (matMul Y0.1 C.1))
          (matScale (Y0.2 * C.2) B) := hw
      rw [matScale_one] at hwA
      have hwA' : matOneValue (matScale Pos.one (matMul Y0'.1 C'.1))
          (matScale (Y0'.2 * C'.2) B) := hw'
      rw [matScale_one] at hwA'
      have hjA : matOneValue
          (matScale Pos.one
            (matAdd (matScale (Pos.one * C.2) Y1.1)
              (matScale Y1.2 (matMul (transposeM B) C.1))))
          (matScale (Y1.2 * (Pos.one * C.2)) A) := hj
      rw [matScale_one, ground.one_mul C.2] at hjA
      have hj'A : matOneValue
          (matScale Pos.one
            (matAdd (matScale (Pos.one * C'.2) Y1'.1)
              (matScale Y1'.2 (matMul (transposeM B) C'.1))))
          (matScale (Y1'.2 * (Pos.one * C'.2)) A) := hj'
      rw [matScale_one, ground.one_mul C'.2] at hj'A
      -- the deviation datum against the primed factor, expanded
      have hS1r : rowsLen (m + 1) (matScale Y0.2 Y0'.1) :=
        rowsLen_mapRows _ Y0'.1 (m + 1) hY0'r
      have hS2r : rowsLen (m + 1) (matScale Y0'.2 (matSwap Y0.1)) :=
        rowsLen_mapRows _ (matSwap Y0.1) (m + 1)
          (rowsLen_mapRows BPair.swap Y0.1 (m + 1) hY0r)
      have hg1 := matMul_addL (m + 1) C'.1
        (rowsLen_cast hC'l (rowsLen_transposeM C'.1))
        (matScale Y0.2 Y0'.1) (matScale Y0'.2 (matSwap Y0.1))
        hS1r hS2r
      have hg2 := matOne_trans (mulScaleL Y0.2 Y0'.1 C'.1)
        (matScale_matOne Y0.2 hwA')
      rw [matScale_matScale (Y0'.2 * C'.2) Y0.2 B] at hg2
      have hg4 := mulScaleL Y0'.2 (matSwap Y0.1) C'.1
      rw [matMul_swapL Y0.1 C'.1] at hg4
      have hr1 : rowsLen (k + 1)
          (matMul (matScale Y0.2 Y0'.1) C'.1) :=
        rowsLen_cast hTC'l
          (rowsLen_matMul (matScale Y0.2 Y0'.1) C'.1)
      have hr2 : rowsLen (k + 1)
          (matMul (matScale Y0'.2 (matSwap Y0.1)) C'.1) :=
        rowsLen_cast hTC'l
          (rowsLen_matMul (matScale Y0'.2 (matSwap Y0.1)) C'.1)
      have hr3 : rowsLen (k + 1)
          (matScale (Y0.2 * (Y0'.2 * C'.2)) B) :=
        rowsLen_mapRows _ B (k + 1) hBr
      have hr4 : rowsLen (k + 1)
          (matScale Y0'.2 (matSwap (matMul Y0.1 C'.1))) :=
        rowsLen_mapRows _ (matSwap (matMul Y0.1 C'.1)) (k + 1)
          (rowsLen_mapRows BPair.swap (matMul Y0.1 C'.1) (k + 1)
            (rowsLen_cast hTC'l (rowsLen_matMul Y0.1 C'.1)))
      have hD := matOne_trans hg1
        (matAdd_cong2 (k + 1) _ _ _ _ hr1 hr2 hr3 hr4 hg2 hg4)
      -- the head factor multiplied through
      have hPl : (matScale (Y0.2 * (Y0'.2 * C'.2)) B).length = m + 1 :=
        (length_matScale _ _).trans hBl
      have hQl : (matScale Y0'.2
          (matSwap (matMul Y0.1 C'.1))).length = m + 1 :=
        (length_matScale _ _).trans
          ((length_matSwap (matMul Y0.1 C'.1)).trans
            ((length_matMul Y0.1 C'.1).trans hY0l))
      have hDl : (matMul
          (matAdd (matScale Y0.2 Y0'.1)
            (matScale Y0'.2 (matSwap Y0.1))) C'.1).length = m + 1 :=
        (length_matMul _ C'.1).trans
          ((length_matAdd _ _
            (((length_matScale _ _).trans hY0'l).trans
              (((length_matScale _ _).trans
                ((length_matSwap Y0.1).trans hY0l)).symm))).trans
            ((length_matScale _ _).trans hY0'l))
      have hcongR := matMul_congrR (transposeM C.1)
        (matMul
          (matAdd (matScale Y0.2 Y0'.1)
            (matScale Y0'.2 (matSwap Y0.1))) C'.1)
        (matAdd (matScale (Y0.2 * (Y0'.2 * C'.2)) B)
          (matScale Y0'.2 (matSwap (matMul Y0.1 C'.1))))
        (rowsLen_cast hTC'l
          (rowsLen_matMul
            (matAdd (matScale Y0.2 Y0'.1)
              (matScale Y0'.2 (matSwap Y0.1))) C'.1))
        (rowsLen_matAdd (k + 1) _ _ hr3 hr4) hDl
        ((length_matAdd _ _ (hPl.trans hQl.symm)).trans hPl)
        (Nat.succ_pos m) hD
      have haddR := matMul_addR
        (matScale (Y0.2 * (Y0'.2 * C'.2)) B)
        (matScale Y0'.2 (matSwap (matMul Y0.1 C'.1)))
        hr3 hr4 (hPl.trans hQl.symm)
        (by rw [hPl]; exact Nat.succ_pos m)
        (transposeM C.1) (rowsLen_cast hPl.symm hTCr)
      -- the two summands' reads
      have hT1 := mulScaleR (Y0.2 * (Y0'.2 * C'.2)) (k + 1)
        (transposeM C.1) B hBr
      have hq3b1 := matMul_congrR (transposeM C.1) Y0.1
        (transposeM Y0.1) hY0r
        (rowsLen_cast hY0l (rowsLen_transposeM Y0.1)) hY0l
        (transposeLen Y0.1 hY0r hY0l) (Nat.succ_pos m)
        (matOne_symm hsym0)
      have hq3b2 := transposeM_matMul Y0.1 C.1 hY0r hCr hY0l hCl
        (Nat.succ_pos m) (Nat.succ_pos m)
      have hq3b3 := transposeM_congrM (k + 1) (matMul Y0.1 C.1)
        (matScale (Y0.2 * C.2) B)
        (rowsLen_cast hTCl (rowsLen_matMul Y0.1 C.1))
        (rowsLen_mapRows _ B (k + 1) hBr)
        (((length_matMul Y0.1 C.1).trans hY0l).trans
          (((length_matScale (Y0.2 * C.2) B).trans hBl).symm))
        hwA
      have hq3b4 := transposeM_matScale (Y0.2 * C.2) (k + 1) B hBr
      have hq3b := matOne_trans hq3b1
        (matOne_trans (matOne_symm hq3b2)
          (matOne_trans hq3b3 hq3b4))
      have hq3a := matMul_assoc (transposeM C.1) Y0.1 C'.1
        hTCr hY0r hC'r hY0l hC'l (Nat.succ_pos m) (Nat.succ_pos m)
      have hq3 := matOne_trans (matOne_symm hq3a)
        (matOne_trans
          (matMul_congrL (matMul (transposeM C.1) Y0.1)
            (matScale (Y0.2 * C.2) (transposeM B)) C'.1 hq3b)
          (mulScaleL (Y0.2 * C.2) (transposeM B) C'.1))
      have hSwr : rowsLen (k + 1) (matSwap (matMul Y0.1 C'.1)) :=
        rowsLen_mapRows BPair.swap (matMul Y0.1 C'.1) (k + 1)
          (rowsLen_cast hTC'l (rowsLen_matMul Y0.1 C'.1))
      have hT2 := mulScaleR Y0'.2 (k + 1) (transposeM C.1)
        (matSwap (matMul Y0.1 C'.1)) hSwr
      rw [matMul_swap (transposeM C.1) (matMul Y0.1 C'.1)] at hT2
      have hT2b := matOne_trans hT2
        (matScale_matOne Y0'.2 (matSwap_congr hq3))
      rw [← matScale_matSwap (Y0.2 * C.2)
          (matMul (transposeM B) C'.1),
        matScale_matScale (Y0.2 * C.2) Y0'.2
          (matSwap (matMul (transposeM B) C'.1))] at hT2b
      -- the expanded product collected
      have hTPl : (transposeM
          (matScale (Y0.2 * (Y0'.2 * C'.2)) B)).length = k + 1 :=
        length_transposeM _ hr3 (by rw [hPl]; exact Nat.succ_pos m)
      have hTQl : (transposeM (matScale Y0'.2
          (matSwap (matMul Y0.1 C'.1)))).length = k + 1 :=
        length_transposeM _ hr4 (by rw [hQl]; exact Nat.succ_pos m)
      have hrT1 : rowsLen (k + 1)
          (matScale (Y0.2 * (Y0'.2 * C'.2))
            (matMul (transposeM C.1) B)) :=
        rowsLen_mapRows _ (matMul (transposeM C.1) B) (k + 1)
          (rowsLen_cast hTBl (rowsLen_matMul (transposeM C.1) B))
      have hrT2 : rowsLen (k + 1)
          (matScale (Y0'.2 * (Y0.2 * C.2))
            (matSwap (matMul (transposeM B) C'.1))) :=
        rowsLen_mapRows _ (matSwap (matMul (transposeM B) C'.1))
          (k + 1)
          (rowsLen_mapRows BPair.swap (matMul (transposeM B) C'.1)
            (k + 1) hW'r)
      have hMain0 := matOne_trans (matOne_trans hcongR haddR)
        (matAdd_cong2 (k + 1)
          (matMul (transposeM C.1)
            (matScale (Y0.2 * (Y0'.2 * C'.2)) B))
          (matMul (transposeM C.1)
            (matScale Y0'.2 (matSwap (matMul Y0.1 C'.1))))
          (matScale (Y0.2 * (Y0'.2 * C'.2))
            (matMul (transposeM C.1) B))
          (matScale (Y0'.2 * (Y0.2 * C.2))
            (matSwap (matMul (transposeM B) C'.1)))
          (rowsLen_cast hTPl
            (rowsLen_matMul (transposeM C.1)
              (matScale (Y0.2 * (Y0'.2 * C'.2)) B)))
          (rowsLen_cast hTQl
            (rowsLen_matMul (transposeM C.1)
              (matScale Y0'.2 (matSwap (matMul Y0.1 C'.1)))))
          hrT1 hrT2 hT1 hT2b)
      -- the join's move-across at the primed data, the withdrawn
      -- swap pair
      have hX1l : (matScale C.2 Y1.1).length = k + 1 :=
        (length_matScale C.2 Y1.1).trans hY1l
      have hX1r : rowsLen (k + 1) (matScale C.2 Y1.1) :=
        rowsLen_mapRows _ Y1.1 (k + 1) hY1r
      have hMRr : rowsLen (k + 1) (matScale (Y1.2 * C.2) A) :=
        rowsLen_mapRows _ A (k + 1) hAr
      have hX1'l : (matScale C'.2 Y1'.1).length = k + 1 :=
        (length_matScale C'.2 Y1'.1).trans hY1'l
      have hX1'r : rowsLen (k + 1) (matScale C'.2 Y1'.1) :=
        rowsLen_mapRows _ Y1'.1 (k + 1) hY1'r
      have hMJ' := addMove (matScale C'.2 Y1'.1)
        (matScale Y1'.2 (matMul (transposeM B) C'.1))
        (matScale (Y1'.2 * C'.2) A) (sqAt_of hX1'l hX1'r)
        (sqAt_of ((length_matScale _ _).trans hW'l)
          (rowsLen_mapRows _ (matMul (transposeM B) C'.1) (k + 1)
            hW'r))
        (sqAt_of ((length_matScale (Y1'.2 * C'.2) A).trans hAl)
          (rowsLen_mapRows _ A (k + 1) hAr))
        hj'A
      -- the unprimed join's move-across at the plain witness product
      have hMJT := addMove (matScale C.2 Y1.1)
        (matScale Y1.2 (matMul (transposeM B) C.1))
        (matScale (Y1.2 * C.2) A) (sqAt_of hX1l hX1r)
        (sqAt_of ((length_matScale _ _).trans hWl)
          (rowsLen_mapRows _ (matMul (transposeM B) C.1) (k + 1) hWr))
        (sqAt_of ((length_matScale (Y1.2 * C.2) A).trans hAl) hMRr)
        hjA
      -- the transfer product's cleared symmetry: at the witness
      -- clearing the swapped product reads the join's own,
      -- `hq3b`'s unprimed instance chained through the witness
      have hwAssoc := matMul_assoc (transposeM C.1) Y0.1 C.1
        hTCr hY0r hCr hY0l hCl (Nat.succ_pos m) (Nat.succ_pos m)
      have hw4 := matMul_congrR (transposeM C.1)
        (matScale (Y0.2 * C.2) B) (matMul Y0.1 C.1)
        (rowsLen_mapRows _ B (k + 1) hBr)
        (rowsLen_cast hTCl (rowsLen_matMul Y0.1 C.1))
        ((length_matScale (Y0.2 * C.2) B).trans hBl)
        ((length_matMul Y0.1 C.1).trans hY0l)
        (Nat.succ_pos m) (matOne_symm hwA)
      have hw2 := matMul_congrL (matMul (transposeM C.1) Y0.1)
        (matScale (Y0.2 * C.2) (transposeM B)) C.1 hq3b
      have hWs : matOneValue
          (matScale (Y0.2 * C.2) (matMul (transposeM C.1) B))
          (matScale (Y0.2 * C.2) (matMul (transposeM B) C.1)) :=
        matOne_trans
          (matOne_symm
            (mulScaleR (Y0.2 * C.2) (k + 1) (transposeM C.1) B hBr))
          (matOne_trans hw4
            (matOne_trans (matOne_symm hwAssoc)
              (matOne_trans hw2
                (mulScaleL (Y0.2 * C.2) (transposeM B) C.1))))
      -- the goal's clearing rides in at the witness clearing's
      -- extra factor and the joins substitute
      have hMain1 := matScale_matOne (C.2 * (Y1'.2 * Y1.2)) hMain0
      rw [matScale_matAdd (C.2 * (Y1'.2 * Y1.2))
          (matScale (Y0.2 * (Y0'.2 * C'.2))
            (matMul (transposeM C.1) B))
          (matScale (Y0'.2 * (Y0.2 * C.2))
            (matSwap (matMul (transposeM B) C'.1))),
        matScale_matScale (Y0.2 * (Y0'.2 * C'.2))
          (C.2 * (Y1'.2 * Y1.2)) (matMul (transposeM C.1) B),
        posN1 Y0.2 Y0'.2 C'.2 C.2 Y1'.2 Y1.2,
        ← matScale_matScale (Y0.2 * C.2)
          (Y1.2 * (Y1'.2 * (Y0'.2 * C'.2)))
          (matMul (transposeM C.1) B),
        matScale_matScale (Y0'.2 * (Y0.2 * C.2))
          (C.2 * (Y1'.2 * Y1.2))
          (matSwap (matMul (transposeM B) C'.1)),
        posN2 Y0.2 Y0'.2 C.2 Y1'.2 Y1.2,
        ← matScale_matScale Y1'.2
          ((C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2)))))
          (matSwap (matMul (transposeM B) C'.1)),
        matScale_matSwap Y1'.2 (matMul (transposeM B) C'.1),
        matScale_matSwap (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
          (matScale Y1'.2 (matMul (transposeM B) C'.1))] at hMain1
      have hWsQ := matScale_matOne (Y1.2 * (Y1'.2 * (Y0'.2 * C'.2)))
        hWs
      rw [matScale_matScale (Y0.2 * C.2)
          (Y1.2 * (Y1'.2 * (Y0'.2 * C'.2)))
          (matMul (transposeM B) C.1),
        posN3 Y0.2 Y0'.2 C'.2 C.2 Y1'.2 Y1.2,
        ← matScale_matScale Y1.2
          ((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
          (matMul (transposeM B) C.1)] at hWsQ
      have hSub1 := matOne_trans hWsQ
        (matScale_matOne ((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
          hMJT)
      have hSub2 := matSwap_congr
        (matScale_matOne (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2)))) hMJ')
      have hStep := matAdd_cong2 (k + 1)
        (matScale (Y1.2 * (Y1'.2 * (Y0'.2 * C'.2)))
          (matScale (Y0.2 * C.2) (matMul (transposeM C.1) B)))
        (matSwap (matScale (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
          (matScale Y1'.2 (matMul (transposeM B) C'.1))))
        (matScale ((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
          (matAdd (matScale (Y1.2 * C.2) A)
            (matSwap (matScale C.2 Y1.1))))
        (matSwap (matScale (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
          (matAdd (matScale (Y1'.2 * C'.2) A)
            (matSwap (matScale C'.2 Y1'.1)))))
        (rowsLen_mapRows _
          (matScale (Y0.2 * C.2) (matMul (transposeM C.1) B)) (k + 1)
          (rowsLen_mapRows _ (matMul (transposeM C.1) B) (k + 1)
            (rowsLen_cast hTBl
              (rowsLen_matMul (transposeM C.1) B))))
        (rowsLen_mapRows BPair.swap
          (matScale (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
            (matScale Y1'.2 (matMul (transposeM B) C'.1))) (k + 1)
          (rowsLen_mapRows _
            (matScale Y1'.2 (matMul (transposeM B) C'.1)) (k + 1)
            (rowsLen_mapRows _ (matMul (transposeM B) C'.1) (k + 1)
              hW'r)))
        (rowsLen_mapRows _
          (matAdd (matScale (Y1.2 * C.2) A)
            (matSwap (matScale C.2 Y1.1))) (k + 1)
          (rowsLen_matAdd (k + 1) _ _ hMRr
            (rowsLen_mapRows BPair.swap (matScale C.2 Y1.1) (k + 1)
              hX1r)))
        (rowsLen_mapRows BPair.swap
          (matScale (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
            (matAdd (matScale (Y1'.2 * C'.2) A)
              (matSwap (matScale C'.2 Y1'.1)))) (k + 1)
          (rowsLen_mapRows _
            (matAdd (matScale (Y1'.2 * C'.2) A)
              (matSwap (matScale C'.2 Y1'.1))) (k + 1)
            (rowsLen_matAdd (k + 1) _ _
              (rowsLen_mapRows _ A (k + 1) hAr)
              (rowsLen_mapRows BPair.swap (matScale C'.2 Y1'.1)
                (k + 1) hX1'r))))
        hSub1 hSub2
      have hFin := matOne_trans hMain1 hStep
      rw [matScale_matAdd ((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
          (matScale (Y1.2 * C.2) A) (matSwap (matScale C.2 Y1.1)),
        matScale_matScale (Y1.2 * C.2)
          ((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2))) A,
        matScale_matSwap ((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
          (matScale C.2 Y1.1),
        matScale_matScale C.2
          ((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2))) Y1.1,
        matScale_matAdd (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
          (matScale (Y1'.2 * C'.2) A)
          (matSwap (matScale C'.2 Y1'.1)),
        matScale_matScale (Y1'.2 * C'.2)
          (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2)))) A,
        matScale_matSwap (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
          (matScale C'.2 Y1'.1),
        matScale_matScale C'.2
          (C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2)))) Y1'.1,
        matSwap_matAdd
          (matScale ((C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
            * (Y1'.2 * C'.2)) A)
          (matSwap (matScale ((C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
            * C'.2) Y1'.1)),
        matSwap_matSwap
          (matScale ((C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2))))
            * C'.2) Y1'.1),
        posN4 Y0.2 Y0'.2 C'.2 C.2 Y1'.2 Y1.2,
        matAdd_shuffle
          (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
            * (Y1.2 * C.2)) A)
          (matSwap (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
            * C.2) Y1.1))
          (matSwap
            (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
              * (Y1.2 * C.2)) A))
          (matScale ((C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2)))) * C'.2)
            Y1'.1)] at hFin
      -- the shared summand withdraws at its own swap
      have hsAl : (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
          * (Y1.2 * C.2)) A).length = k + 1 :=
        (length_matScale _ _).trans hAl
      have hRestl : (matAdd
          (matSwap (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
            * C.2) Y1.1))
          (matScale ((C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2)))) * C'.2)
            Y1'.1)).length = k + 1 :=
        (length_matAdd _ _
          (((length_matSwap _).trans
            ((length_matScale _ _).trans hY1l)).trans
            (((length_matScale _ _).trans hY1'l).symm))).trans
          ((length_matSwap _).trans
            ((length_matScale _ _).trans hY1l))
      have hNull := matAdd_nullL
        (matAdd
          (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
            * (Y1.2 * C.2)) A)
          (matSwap (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
            * (Y1.2 * C.2)) A)))
        (matAdd
          (matSwap (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
            * C.2) Y1.1))
          (matScale ((C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2)))) * C'.2)
            Y1'.1))
        (matNull_add_swap
          (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
            * (Y1.2 * C.2)) A))
        (((length_matAdd _ _
            (hsAl.trans
              (((length_matSwap _).trans hsAl).symm))).trans
          hsAl).trans hRestl.symm)
        (rowsLen_matAdd (k + 1) _ _
          (rowsLen_mapRows _ A (k + 1) hAr)
          (rowsLen_mapRows BPair.swap
            (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2)))
              * (Y1.2 * C.2)) A) (k + 1)
            (rowsLen_mapRows _ A (k + 1) hAr)))
        (rowsLen_matAdd (k + 1) _ _
          (rowsLen_mapRows BPair.swap
            (matScale (((Y0.2 * C.2) * (Y1'.2 * (Y0'.2 * C'.2))) * C.2)
              Y1.1) (k + 1)
            (rowsLen_mapRows _ Y1.1 (k + 1) hY1r))
          (rowsLen_mapRows _ Y1'.1 (k + 1) hY1'r))
      have hAlmost := matOne_trans hFin hNull
      -- the goal's left side at the extra clearing is the collected
      -- read outright
      have hLeft : matScale C.2
          (matScale (C.2 * (Y0'.2 * Y0.2 * C'.2))
            (matAdd (matScale Y1.2 Y1'.1)
              (matScale Y1'.2 (matSwap Y1.1))))
          = matAdd
            (matSwap (matScale (((Y0.2 * C.2)
              * (Y1'.2 * (Y0'.2 * C'.2))) * C.2) Y1.1))
            (matScale ((C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2)))) * C'.2)
              Y1'.1) := by
        rw [matScale_matScale (C.2 * (Y0'.2 * Y0.2 * C'.2)) C.2
            (matAdd (matScale Y1.2 Y1'.1)
              (matScale Y1'.2 (matSwap Y1.1))),
          matScale_matAdd (C.2 * (C.2 * (Y0'.2 * Y0.2 * C'.2)))
            (matScale Y1.2 Y1'.1) (matScale Y1'.2 (matSwap Y1.1)),
          matScale_matScale Y1.2 (C.2 * (C.2 * (Y0'.2 * Y0.2 * C'.2)))
            Y1'.1,
          matScale_matScale Y1'.2 (C.2 * (C.2 * (Y0'.2 * Y0.2 * C'.2)))
            (matSwap Y1.1),
          matScale_matSwap ((C.2 * (C.2 * (Y0'.2 * Y0.2 * C'.2)))
            * Y1'.2) Y1.1,
          posN5 Y0.2 Y0'.2 C'.2 C.2 Y1'.2,
          posN6 Y0.2 Y0'.2 C'.2 C.2 Y1.2,
          matAdd_comm
            (matScale ((C.2 * (Y1.2 * (Y0'.2 * (Y0.2 * C.2)))) * C'.2)
              Y1'.1)
            (matSwap (matScale (((Y0.2 * C.2)
              * (Y1'.2 * (Y0'.2 * C'.2))) * C.2) Y1.1))]
      show matOneValue
        (matScale (C.2 * (Y0'.2 * Y0.2 * C'.2))
          (matAdd (matScale Y1.2 Y1'.1)
            (matScale Y1'.2 (matSwap Y1.1))))
        (matScale (Y1'.2 * Y1.2)
          (matMul (transposeM (matSwap C.1))
            (matMul
              (matAdd (matScale Y0.2 Y0'.1)
                (matScale Y0'.2 (matSwap Y0.1)))
              (matSwap C'.1))))
      rw [matMul_swap, transposeM_swap, matMul_swapL, matMul_swap,
        matSwap_matSwap]
      refine matOne_unscale C.2 (k + 1)
        (matScale (C.2 * (Y0'.2 * Y0.2 * C'.2))
          (matAdd (matScale Y1.2 Y1'.1)
            (matScale Y1'.2 (matSwap Y1.1))))
        (matScale (Y1'.2 * Y1.2)
          (matMul (transposeM C.1)
            (matMul
              (matAdd (matScale Y0.2 Y0'.1)
                (matScale Y0'.2 (matSwap Y0.1))) C'.1)))
        ((length_matScale _ _).trans
          ((length_matAdd _ _
            (((length_matScale _ _).trans hY1'l).trans
              (((length_matScale _ _).trans
                ((length_matSwap _).trans hY1l)).symm))).trans
            ((length_matScale _ _).trans hY1'l)))
        (rowsLen_mapRows _ _ (k + 1)
          (rowsLen_matAdd (k + 1) _ _
            (rowsLen_mapRows _ Y1'.1 (k + 1) hY1'r)
            (rowsLen_mapRows _ (matSwap Y1.1) (k + 1)
              (rowsLen_mapRows BPair.swap Y1.1 (k + 1) hY1r))))
        ((length_matScale _ _).trans
          ((length_matMul _ _).trans hTCl))
        (rowsLen_mapRows _ _ (k + 1)
          (rowsLen_matMul_of (transposeM C.1)
             (matMul (matAdd (matScale Y0.2 Y0'.1) (matScale Y0'.2 (matSwap Y0.1))) C'.1)
             (fun _ => (by rw [hDl]; exact Nat.succ_pos m))
             (rowsLen_cast hTC'l (rowsLen_matMul (matAdd (matScale Y0.2 Y0'.1) (matScale Y0'.2 (matSwap Y0.1))) C'.1))))
        ?_
      rw [hLeft, matScale_matScale (Y1'.2 * Y1.2) C.2
        (matMul (transposeM C.1)
          (matMul
            (matAdd (matScale Y0.2 Y0'.1)
              (matScale Y0'.2 (matSwap Y0.1))) C'.1))]
      exact matOne_symm hAlmost

/-- Clause (i)'s tail read: the two tail recursions with the pivots
equal outright beyond the perturbation slab. -/
def tailShareRead (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 : Nat) (ns : List Nat) : Prop :=
  tailRead diag off Xs Rs ns
  ∧ tailRead diag' off' Xs' Rs' ns
  ∧ ((List.range Xs.length).all (fun i =>
      Nat.ble i w0 || decide (oneValueQ (ground.getAt dM Xs' i)
        (ground.getAt dM Xs i)))) = true

instance (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 : Nat) (ns : List Nat) :
    Decidable (tailShareRead diag off diag' off' Xs Rs Xs' Rs' w0 ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _))

/-- The sandwich's family bundle: the two head recursions, the
shared data beyond the perturbation slab, and the telescoping
steps. -/
def sandwichRead (diag off diag' off' : List Mat)
    (Ys Cs Ys' Cs' : List MatQ) (w0 : Nat) (ns : List Nat) : Prop :=
  headRead diag off Ys Cs ns
  ∧ headRead diag' off' Ys' Cs' ns
  ∧ ((List.range diag.length).all (fun i =>
      Nat.ble i w0 || decide (matOneValue (ground.getAt [] diag' i)
        (ground.getAt [] diag i)))) = true
  ∧ ((List.range off.length).all (fun i =>
      decide (i < w0) || decide (matOneValue (ground.getAt [] off' i)
        (ground.getAt [] off i)))) = true
  ∧ ((List.range (Cs.length - w0)).all (fun k => decide
      (sandwichStep (ground.getAt dM Cs (w0 + k))
        (ground.getAt dM Cs' (w0 + k))
        (ground.getAt dM Ys' (w0 + k + 1))
        (ground.getAt dM Ys (w0 + k + 1))
        (ground.getAt dM Ys' (w0 + k))
        (ground.getAt dM Ys (w0 + k))
        (ground.getAt 0 ns (w0 + k))
        (ground.getAt 0 ns (w0 + k + 1))))) = true

instance (diag off diag' off' : List Mat) (Ys Cs Ys' Cs' : List MatQ)
    (w0 : Nat) (ns : List Nat) :
    Decidable (sandwichRead diag off diag' off' Ys Cs Ys' Cs' w0 ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _ ∧ _ = _ ∧ _ = _))

/-- The reversed slab order's head read: the two head recursions with
the pivots equal outright below the perturbation slab. -/
def headShareRead (diag off diag' off' : List Mat)
    (Ys Cs Ys' Cs' : List MatQ) (w0 : Nat) (ns : List Nat) : Prop :=
  headRead diag off Ys Cs ns
  ∧ headRead diag' off' Ys' Cs' ns
  ∧ ((List.range Ys.length).all (fun i =>
      Nat.ble w0 i || decide (oneValueQ (ground.getAt dM Ys' i)
        (ground.getAt dM Ys i)))) = true

instance (diag off diag' off' : List Mat)
    (Ys Cs Ys' Cs' : List MatQ) (w0 : Nat) (ns : List Nat) :
    Decidable (headShareRead diag off diag' off' Ys Cs Ys' Cs' w0 ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _))

/-- The reversed slab order's sandwich bundle: the two tail recursions,
the shared data below the perturbation slab, and the telescoping
steps `E_i = Ť_{i+1}ᵀ E_{i+1} Ť'_{i+1}` down to the head at the tail
witnesses' transfer factors. -/
def tailSandwichRead (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 : Nat) (ns : List Nat) : Prop :=
  tailRead diag off Xs Rs ns
  ∧ tailRead diag' off' Xs' Rs' ns
  ∧ ((List.range diag.length).all (fun i =>
      Nat.ble w0 i || decide (matOneValue (ground.getAt [] diag' i)
        (ground.getAt [] diag i)))) = true
  ∧ ((List.range off.length).all (fun i =>
      Nat.ble w0 i || decide (matOneValue (ground.getAt [] off' i)
        (ground.getAt [] off i)))) = true
  ∧ ((List.range w0).all (fun k => decide
      (sandwichStep (ground.getAt dM Rs k)
        (ground.getAt dM Rs' k)
        (ground.getAt dM Xs' k)
        (ground.getAt dM Xs k)
        (ground.getAt dM Xs' (k + 1))
        (ground.getAt dM Xs (k + 1))
        (ground.getAt 0 ns (k + 1))
        (ground.getAt 0 ns k)))) = true

instance (diag off diag' off' : List Mat) (Xs Rs Xs' Rs' : List MatQ)
    (w0 : Nat) (ns : List Nat) :
    Decidable (tailSandwichRead diag off diag' off' Xs Rs Xs' Rs' w0 ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _ ∧ _ = _ ∧ _ = _))

/-- The transfer factor's contraction certificate at the slab
split's two grams: `Tᵀ Gi T ⪯ λ² Gs` at a cleared pair
`λ = [ln : ld]`, the image's form against its own slab's gram
priced at the source's, the datum and its split at the source's
order — the factor rectangular at the slabs' own orders, a square
slab's read the one-gram instance. -/
def contractRead {o : Nat} (T : MatQ) (Gi Gsr : Mat) (ln ld : Pos)
    (sp : Split o) : Prop :=
  sqAt Gi T.1.length ∧ rowsLen o T.1 ∧ sqAt Gsr o
  ∧ splitRead (siteDatum (matScale (ln * ln * (T.2 * T.2)) Gsr)
      (matScale (ld * ld) (matMul (transposeM T.1) (matMul Gi T.1)))) sp
  ∧ psdAt sp

instance {o : Nat} (T : MatQ) (Gi Gsr : Mat) (ln ld : Pos) (sp : Split o) :
    Decidable (contractRead T Gi Gsr ln ld sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The contraction read at every vector: the transfer image's
deeper form priced at the modulus against the headward one, the
split's transport at the congruence. -/
theorem contract_all {o : Nat} (T : MatQ) (Gi Gsr : Mat)
    (ln ld : Pos) (sp : Split o)
    (h : contractRead T Gi Gsr ln ld sp) :
    ∀ u : List BPair, u.length = o →
      (quadForm Gi (matVec T.1 u)).scale (ld * ld)
        ≤ (quadForm Gsr u).scale (ln * ln * (T.2 * T.2)) := by
  intro u hu
  obtain ⟨hGi, hTr, hGsr, hsp, hpsd⟩ := h
  obtain ⟨T1, T2⟩ := T
  cases T1 with
  | nil =>
    have hnil : siteDatum
        (matScale (ln * ln * (T2 * T2)) Gsr)
        (matScale (ld * ld)
          (matMul (transposeM ([] : Mat)) (matMul Gi []))) = [] := by
      show matAdd (matScale (ln * ln * (T2 * T2)) Gsr)
        (matSwap (matScale (ld * ld) (matMul ([] : Mat) (matMul Gi [])))) = []
      exact matAdd_nil_right (matScale (ln * ln * (T2 * T2)) Gsr)
    rw [hnil] at hsp
    have ho : o = 0 := (sqAt_len hsp.1).symm
    have hun : u = [] := List.length_eq_zero_iff.mp (hu.trans ho)
    rw [hun]
    show BPair.unit.scale (ld * ld)
      ≤ BPair.unit.scale (ln * ln * (T2 * T2))
    exact ground.leB_congr_right (ground.unitScale (ln * ln * (T2 * T2)))
      (ground.leB_congr_left (ground.unitScale (ld * ld))
        (ground.leB_refl BPair.unit))
  | cons r t =>
    have hpos : 0 < (r :: t).length := Nat.succ_pos t.length
    have hTlen : (transposeM (r :: t)).length = o :=
      length_transposeM (r :: t) hTr hpos
    have hGiL : Gi.length = (r :: t).length := sqAt_len hGi
    have hInner : rowsLen o (matMul Gi (r :: t)) :=
      rowsLen_matMul_of Gi (r :: t) (fun _ => hpos) hTr
    have hInnerLen : (matMul Gi (r :: t)).length = (r :: t).length :=
      (length_matMul Gi (r :: t)).trans hGiL
    have hOuter : rowsLen o
        (matMul (transposeM (r :: t)) (matMul Gi (r :: t))) :=
      rowsLen_matMul_of (transposeM (r :: t)) (matMul Gi (r :: t))
        (fun _ => by rw [hInnerLen]; exact hpos) hInner
    have hOuterLen :
        (matMul (transposeM (r :: t)) (matMul Gi (r :: t))).length = o :=
      (length_matMul (transposeM (r :: t)) (matMul Gi (r :: t))).trans
        hTlen
    have hSA : sqAt (matScale (ld * ld)
        (matMul (transposeM (r :: t)) (matMul Gi (r :: t)))) o :=
      sqAt_of ((length_matScale _ _).trans hOuterLen)
        (rowsLen_mapRows _ _ o hOuter)
    have hSB : sqAt (matScale (ln * ln * (T2 * T2)) Gsr) o :=
      sqAt_of ((length_matScale _ _).trans (sqAt_len hGsr))
        (rowsLen_mapRows _ _ o (rowsLen_of_sqAt hGsr))
    have hUnit : BPair.unit ≤ quadForm
        (siteDatum (matScale (ln * ln * (T2 * T2)) Gsr)
          (matScale (ld * ld)
            (matMul (transposeM (r :: t)) (matMul Gi (r :: t))))) u :=
      ground.leB_of_not_lt (psd_all _ sp hsp hpsd u hu)
    have h1 := ground.leB_of_unit_add
      (ground.leB_congr_right (quadForm_site_sq hSB hSA hu) hUnit)
    rw [BPair.swap_swap] at h1
    have h2 := ground.leB_congr_right
      (quadForm_scale (ln * ln * (T2 * T2)) Gsr u)
      (ground.leB_congr_left
        (quadForm_scale (ld * ld)
          (matMul (transposeM (r :: t)) (matMul Gi (r :: t))) u) h1)
    exact ground.leB_congr_left
      (BPair.scale_congr (ld * ld)
        (BPair.oneValue_symm
          (congQuad Gi (r :: t) (r :: t).length o hGi hTr rfl u hu))) h2


/-- A cleared datum's two-sided cap at `[cn : cd] G`, the two
splits `lem:inertia`'s witnesses. -/
def capQ {o : Nat} (D : MatQ) (G : Mat) (cn cd : Pos)
    (spU spL : Split o) : Prop :=
  capAt (matScale cd D.1) (matScale (cn * D.2) G) spU spL

instance {o : Nat} (D : MatQ) (G : Mat) (cn cd : Pos)
    (spU spL : Split o) : Decidable (capQ D G cn cd spU spL) :=
  inferInstanceAs (Decidable (capAt _ _ _ _))

/-- The cap's upper read at every vector, the split's transport. -/
theorem cap_hi {o : Nat} (D : MatQ) (G : Mat) (cn cd : Pos)
    (spU spL : Split o) (h : capQ D G cn cd spU spL) :
    ∀ w : List BPair, w.length = o →
      (quadForm D.1 w).scale cd
        ≤ (quadForm G w).scale (cn * D.2) := by
  intro w hw
  obtain ⟨hS, hC, hsU, hpU, _, _⟩ := h
  have hUnit : BPair.unit ≤ quadForm
      (siteDatum (matScale (cn * D.2) G) (matScale cd D.1)) w :=
    ground.leB_of_not_lt (psd_all _ spU hsU hpU w hw)
  have h1 := ground.leB_of_unit_add
    (ground.leB_congr_right (quadForm_site_sq hC hS hw) hUnit)
  rw [BPair.swap_swap] at h1
  exact ground.leB_congr_right (quadForm_scale (cn * D.2) G w)
    (ground.leB_congr_left (quadForm_scale cd D.1 w) h1)

/-- The cap's lower read at every vector, the split's transport. -/
theorem cap_lo {o : Nat} (D : MatQ) (G : Mat) (cn cd : Pos)
    (spU spL : Split o) (h : capQ D G cn cd spU spL) :
    ∀ w : List BPair, w.length = o →
      ((quadForm G w).scale (cn * D.2)).swap
        ≤ (quadForm D.1 w).scale cd := by
  intro w hw
  obtain ⟨hS, hC, _, _, hsL, hpL⟩ := h
  have hUnit : BPair.unit ≤ quadForm
      (matAdd (matScale (cn * D.2) G) (matScale cd D.1)) w :=
    ground.leB_of_not_lt (psd_all _ spL hsL hpL w hw)
  have h1 := ground.leB_of_unit_add
    (ground.leB_congr_right
      (BPair.oneValue_trans (quadForm_add_sq hC hS hw)
        (BPair.oneValue_of_eq
          (BPair.add_comm (quadForm (matScale (cn * D.2) G) w)
            (quadForm (matScale cd D.1) w)))) hUnit)
  exact ground.leB_congr_right (quadForm_scale cd D.1 w)
    (ground.leB_congr_left
      (ground.swap_congr (quadForm_scale (cn * D.2) G w)) h1)

/-- Clause (ii)'s step: the sandwich's step at the two contraction
certificates and the deviation's cap propagates to the doubled next
deviation at `c (λ² + λ'²) G_{i+1}`, the geometric read, each display's
gram its own slab's block — the deviation's cap at the deeper
block, the doubled next at the headward block. -/
def capStepRead {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ)
    (Gd Gh : Mat) (cn cd ln ld ln' ld' : Pos) (sp1 sp2 : Split n')
    (spU spL : Split n) (spU' spL' : Split n') : Prop :=
  sandwichStep C C' Y1' Y1 Y0' Y0 n n'
  ∧ contractRead (transfer C) Gd Gh ln ld sp1
  ∧ contractRead (transfer C') Gd Gh ln' ld' sp2
  ∧ capQ (devQ Y0' Y0) Gd cn cd spU spL
  ∧ capQ (doubleQ (devQ Y1' Y1)) Gh
      (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld)))
      (cd * (ld * ld * (ld' * ld'))) spU' spL'

instance {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ) (Gd Gh : Mat)
    (cn cd ln ld ln' ld' : Pos) (sp1 sp2 : Split n')
    (spU spL : Split n) (spU' spL' : Split n') :
    Decidable (capStepRead C C' Y1' Y1 Y0' Y0 Gd Gh cn cd ln ld
      ln' ld' sp1 sp2 spU spL spU' spL') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The pairing at two cleared-weighted vectors carries both
weights out at the balance weighting. -/
private theorem crossScaled (M : Mat) (x y : List BPair)
    (wx wy : Pos) :
    (dotN (elim.vecScale (BPair.ofPos wx) x)
        (matVec M (elim.vecScale (BPair.ofPos wy) y))).oneValue
      ((dotN x (matVec M y)).scale (wy * wx)) := by
  refine BPair.oneValue_trans
    (dotN_vecScale_pair M (BPair.ofPos wx) (BPair.ofPos wy) x y) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos wy))
      (BPair.ofPos_scale wx (dotN x (matVec M y)))) ?_
  refine BPair.oneValue_trans
    (BPair.ofPos_scale wy ((dotN x (matVec M y)).scale wx)) ?_
  rw [BPair.scale_scale, ground.mul_comm wx wy]
  exact BPair.oneValue_refl _

/-- The form's polarization expansion at two weighted vectors: the
two diagonal reads at squared weights beside the two cross reads at
the mixed weight. -/
private theorem quadPol (M : Mat) {n : Nat} (hMr : rowsLen n M)
    (hMl : M.length = n) (x y : List BPair)
    (hx : x.length = n) (hy : y.length = n) (wx wy : Pos) :
    (quadForm M (vecAdd (elim.vecScale (BPair.ofPos wx) x)
        (elim.vecScale (BPair.ofPos wy) y))).oneValue
      (((dotN x (matVec M x)).scale (wx * wx)
          + (dotN x (matVec M y)).scale (wy * wx))
        + ((dotN y (matVec M x)).scale (wx * wy)
          + (dotN y (matVec M y)).scale (wy * wy))) := by
  refine BPair.oneValue_trans
    (quadAdd M n hMr hMl (elim.vecScale (BPair.ofPos wx) x)
      (elim.vecScale (BPair.ofPos wy) y)
      ((length_vecScale (BPair.ofPos wx) x).trans hx)
      ((length_vecScale (BPair.ofPos wy) y).trans hy)) ?_
  exact BPair.add_congr
    (BPair.add_congr (crossScaled M x x wx wx) (crossScaled M x y wx wy))
    (BPair.add_congr (crossScaled M y x wy wx) (crossScaled M y y wy wy))

/-- The polarization expansion at the partner combination, the
second weight entering at the memberwise swap: the diagonal reads
stand and the two cross reads walk to their partners. -/
private theorem quadPolSwap (M : Mat) {n : Nat} (hMr : rowsLen n M)
    (hMl : M.length = n) (x y : List BPair)
    (hx : x.length = n) (hy : y.length = n) (wx wy : Pos) :
    (quadForm M (vecAdd (elim.vecScale (BPair.ofPos wx) x)
        ((elim.vecScale (BPair.ofPos wy) y).map BPair.swap))).oneValue
      (((dotN x (matVec M x)).scale (wx * wx)
          + ((dotN x (matVec M y)).scale (wy * wx)).swap)
        + (((dotN y (matVec M x)).scale (wx * wy)).swap
          + (dotN y (matVec M y)).scale (wy * wy))) := by
  refine BPair.oneValue_trans
    (quadAdd M n hMr hMl (elim.vecScale (BPair.ofPos wx) x)
      ((elim.vecScale (BPair.ofPos wy) y).map BPair.swap)
      ((length_vecScale (BPair.ofPos wx) x).trans hx)
      ((ground.length_map BPair.swap
          (elim.vecScale (BPair.ofPos wy) y)).trans
        ((length_vecScale (BPair.ofPos wy) y).trans hy))) ?_
  rw [dotN_matVec_swapMap M (elim.vecScale (BPair.ofPos wy) y),
    matVec_swapArg (elim.vecScale (BPair.ofPos wy) y) M,
    dotN_swap (elim.vecScale (BPair.ofPos wx) x)
      (matVec M (elim.vecScale (BPair.ofPos wy) y)),
    dotN_swapLeft (elim.vecScale (BPair.ofPos wy) y)
      (matVec M (elim.vecScale (BPair.ofPos wx) x))]
  exact BPair.add_congr
    (BPair.add_congr (crossScaled M x x wx wx)
      (ground.swap_congr (crossScaled M x y wx wy)))
    (BPair.add_congr (ground.swap_congr (crossScaled M y x wy wx))
      (crossScaled M y y wy wy))

/-- The two split reads' collection at opposed partner weights: the
diagonal reads withdraw at their own swap pairs and the four cross
reads collect. -/
private theorem fourCollect (A B C D : BPair) :
    (((A + C) + (D + B)) + ((A.swap + C) + (D + B.swap))).oneValue
      ((C + D) + (C + D)) := by
  have hAA : (A + A.swap).oneValue BPair.unit := by
    rw [BPair.add_comm A A.swap]
    exact BPair.swap_add_null (BPair.oneValue_refl A)
  have hBB : (B + B.swap).oneValue BPair.unit := by
    rw [BPair.add_comm B B.swap]
    exact BPair.swap_add_null (BPair.oneValue_refl B)
  rw [BPair.add_add_comm (A + C) (D + B) (A.swap + C) (D + B.swap),
    BPair.add_add_comm A C A.swap C,
    BPair.add_add_comm D B D B.swap]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr hAA (BPair.oneValue_refl (C + C)))
      (BPair.add_congr (BPair.oneValue_refl (D + D)) hBB)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.unit_add (C + C)) (BPair.add_unit (D + D)))
    ?_
  exact BPair.oneValue_of_eq (BPair.add_add_comm C C D D)

/-- The two split reads' collection at shared weights: the cross
reads withdraw at their own swap pairs and the diagonal reads
collect. -/
private theorem fourCollectG (A B C D : BPair) :
    (((A + C) + (D + B)) + ((A + C.swap) + (D.swap + B))).oneValue
      ((A + B) + (A + B)) := by
  have hCC : (C + C.swap).oneValue BPair.unit := by
    rw [BPair.add_comm C C.swap]
    exact BPair.swap_add_null (BPair.oneValue_refl C)
  have hDD : (D + D.swap).oneValue BPair.unit := by
    rw [BPair.add_comm D D.swap]
    exact BPair.swap_add_null (BPair.oneValue_refl D)
  rw [BPair.add_add_comm (A + C) (D + B) (A + C.swap) (D.swap + B),
    BPair.add_add_comm A C A C.swap,
    BPair.add_add_comm D B D.swap B]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (BPair.oneValue_refl (A + A)) hCC)
      (BPair.add_congr hDD (BPair.oneValue_refl (B + B)))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.add_unit (A + A)) (BPair.unit_add (B + B)))
    ?_
  exact BPair.oneValue_of_eq (BPair.add_add_comm A A B B)

private theorem posP1 (e q l m : Pos) :
    e * (q * (l * m)) = l * (e * (q * m)) := by
  rw [ground.mul_left_comm q l m, ground.mul_left_comm e l (q * m)]

private theorem posP2 (e q l m : Pos) :
    e * (q * (l * m)) = m * (e * (q * l)) := by
  rw [ground.mul_comm l m]
  exact posP1 e q m l

private theorem posMswap (p p' d : Pos) :
    (p' * p) * (p' * (d * p)) = (p * p') * (p * (d * p')) := by
  rw [ground.mul_comm p' p, ground.mul_left_comm p' d p,
    ground.mul_left_comm p d p', ground.mul_comm p' p]

private theorem posMainA (p p' x c d m : Pos) :
    (x * (p * p)) * ((p' * p') * ((c * d) * m))
      = (c * (x * m)) * ((p * p') * (p * (d * p'))) := by
  rw [ground.mul_left_comm (p' * p') (c * d) m,
    ground.mul_left_comm (x * (p * p)) (c * d) ((p' * p') * m),
    ground.mul_assoc c d ((x * (p * p)) * ((p' * p') * m)),
    ground.mul_mul_comm' x (p * p) (p' * p') m,
    ground.mul_mul_comm' p p p' p',
    ground.mul_left_comm p d p',
    ground.mul_left_comm (p * p') d (p * p'),
    ground.mul_assoc c (x * m) (d * ((p * p') * (p * p'))),
    ground.mul_left_comm (x * m) d ((p * p') * (p * p'))]

private theorem posMainB (p p' x c d l : Pos) :
    (x * (p' * p')) * ((p * p) * ((c * d) * l))
      = (c * (x * l)) * ((p * p') * (p * (d * p'))) :=
  (posMainA p' p x c d l).trans
    (congrArg (fun z => (c * (x * l)) * z) (posMswap p p' d))

private theorem posMain (p p' x x' l m c d : Pos) :
    (x * (p * p)) * ((p' * p') * ((c * d) * m))
      + (x' * (p' * p')) * ((p * p) * ((c * d) * l))
      = c * (x * m + x' * l) * ((p * p') * (p * (d * p'))) := by
  rw [ground.mul_assoc c (x * m + x' * l) ((p * p') * (p * (d * p'))),
    ground.right_distrib (x * m) (x' * l) ((p * p') * (p * (d * p'))),
    ground.left_distrib c ((x * m) * ((p * p') * (p * (d * p'))))
      ((x' * l) * ((p * p') * (p * (d * p')))),
    ← ground.mul_assoc c (x * m) ((p * p') * (p * (d * p'))),
    ← ground.mul_assoc c (x' * l) ((p * p') * (p * (d * p'))),
    posMainA p p' x c d m, posMainB p p' x' c d l]

private theorem posFin2 (a t u v : Pos) :
    a * (t * (u * v)) = (v * t) * (u * a) := by
  rw [ground.mul_left_comm t u v, ground.mul_left_comm a u (t * v),
    ground.mul_left_comm a t v, ground.mul_comm a v,
    ground.mul_assoc v t (u * a), ground.mul_left_comm t u a,
    ground.mul_left_comm v u (t * a), ground.mul_left_comm v t a]

/-- The two cap reads' collection at abstract members: the split
at the partner combination joins the plain one, the diagonal
reads withdrawing at their swap pairs on the capped side and the
cross reads on the pricing side, the shared doubling cancelled. -/
private theorem collectStep (A B C D AG BG CG DG : BPair) (cd w : Pos)
    (h1 : ((A + C) + (D + B)).scale cd ≤ ((AG + CG) + (DG + BG)).scale w)
    (h2 : (((AG + CG.swap) + (DG.swap + BG)).scale w).swap
      ≤ ((A + C.swap) + (D.swap + B)).scale cd) :
    (C + D).scale cd ≤ (AG + BG).scale w := by
  have h2' := ground.leB_swap h2
  rw [BPair.swap_swap] at h2'
  have hSum := ground.leB_add h1 h2'
  rw [← BPair.scale_swap ((A + C.swap) + (D.swap + B)) cd,
    ← BPair.scale_add ((A + C) + (D + B))
      ((A + C.swap) + (D.swap + B)).swap cd,
    ← BPair.scale_add ((AG + CG) + (DG + BG))
      ((AG + CG.swap) + (DG.swap + BG)) w,
    ← BPair.swap_add (A + C.swap) (D.swap + B),
    ← BPair.swap_add A C.swap, ← BPair.swap_add D.swap B,
    BPair.swap_swap C, BPair.swap_swap D] at hSum
  have hColl := ground.leB_congr_right
    (BPair.scale_congr w (fourCollectG AG BG CG DG))
    (ground.leB_congr_left
      (BPair.scale_congr cd (fourCollect A B C D)) hSum)
  rw [← BPair.scale_two (C + D), ← BPair.scale_two (AG + BG),
    BPair.scale_scale (C + D) 2 cd, BPair.scale_scale (AG + BG) 2 w,
    ground.mul_comm 2 cd, ground.mul_comm 2 w,
    ← BPair.scale_scale (C + D) cd 2,
    ← BPair.scale_scale (AG + BG) w 2] at hColl
  exact ground.leB_of_scale hColl

/-- The polarization's two-sided core: the deviation's two-sided
cap read at the cross-cleared combination and its partner, the
diagonal deviation reads withdrawing between the two splits and
the gram's cross reads between the two sides — the doubled cross
read priced two-sidedly at the two scaled diagonal gram reads, the
shared doubling cancelled. -/
private theorem polarCore {n : Nat} (Dm Gd : Mat) (D2 cn cd : Pos)
    (hDsq : sqAt Dm n) (hGsq : sqAt Gd n)
    (hsymD : matOneValue (transposeM Dm) Dm)
    (hDhi : ∀ w : List BPair, w.length = n →
      (quadForm Dm w).scale cd ≤ (quadForm Gd w).scale (cn * D2))
    (hDlo : ∀ w : List BPair, w.length = n →
      ((quadForm Gd w).scale (cn * D2)).swap
        ≤ (quadForm Dm w).scale cd)
    (a b : List BPair) (ha : a.length = n) (hb : b.length = n)
    (wa wb : Pos) :
    (((dotN a (matVec Dm b)).scale (wb * wa)
          + (dotN a (matVec Dm b)).scale (wb * wa)).scale cd
        ≤ ((dotN a (matVec Gd a)).scale (wa * wa)
            + (dotN b (matVec Gd b)).scale (wb * wb)).scale (cn * D2))
    ∧ ((((dotN a (matVec Dm b)).scale (wb * wa)
          + (dotN a (matVec Dm b)).scale (wb * wa)).swap).scale cd
        ≤ ((dotN a (matVec Gd a)).scale (wa * wa)
            + (dotN b (matVec Gd b)).scale (wb * wb)).scale (cn * D2)) := by
  have hDr : rowsLen n Dm := rowsLen_of_sqAt hDsq
  have hDl : Dm.length = n := sqAt_len hDsq
  have hGr : rowsLen n Gd := rowsLen_of_sqAt hGsq
  have hGl : Gd.length = n := sqAt_len hGsq
  have hp : (elim.vecScale (BPair.ofPos wa) a).length = n :=
    (length_vecScale (BPair.ofPos wa) a).trans ha
  have hq : (elim.vecScale (BPair.ofPos wb) b).length = n :=
    (length_vecScale (BPair.ofPos wb) b).trans hb
  have hq' : ((elim.vecScale (BPair.ofPos wb) b).map BPair.swap).length
      = n :=
    (ground.length_map BPair.swap (elim.vecScale (BPair.ofPos wb) b)).trans
      hq
  have hw1 : (vecAdd (elim.vecScale (BPair.ofPos wa) a)
      (elim.vecScale (BPair.ofPos wb) b)).length = n :=
    length_vecAdd _ _ n hp hq
  have hw2 : (vecAdd (elim.vecScale (BPair.ofPos wa) a)
      ((elim.vecScale (BPair.ofPos wb) b).map BPair.swap)).length = n :=
    length_vecAdd _ _ n hp hq'
  have hflip : ((dotN b (matVec Dm a)).scale (wa * wb)).oneValue
      ((dotN a (matVec Dm b)).scale (wb * wa)) :=
    BPair.oneValue_trans
      (BPair.scale_congr (wa * wb)
        (dotN_sym_flip Dm n hDr hDl hsymD a b ha hb))
      (BPair.oneValue_of_eq
        (congrArg (fun z => (dotN a (matVec Dm b)).scale z)
          (ground.mul_comm wa wb)))
  have eD1 : (quadForm Dm (vecAdd (elim.vecScale (BPair.ofPos wa) a)
      (elim.vecScale (BPair.ofPos wb) b))).oneValue
      (((dotN a (matVec Dm a)).scale (wa * wa)
          + (dotN a (matVec Dm b)).scale (wb * wa))
        + ((dotN a (matVec Dm b)).scale (wb * wa)
          + (dotN b (matVec Dm b)).scale (wb * wb))) :=
    BPair.oneValue_trans (quadPol Dm hDr hDl a b ha hb wa wb)
      (BPair.add_congr
        (BPair.oneValue_refl _)
        (BPair.add_congr hflip (BPair.oneValue_refl _)))
  have eD2 : (quadForm Dm (vecAdd (elim.vecScale (BPair.ofPos wa) a)
      ((elim.vecScale (BPair.ofPos wb) b).map BPair.swap))).oneValue
      (((dotN a (matVec Dm a)).scale (wa * wa)
          + ((dotN a (matVec Dm b)).scale (wb * wa)).swap)
        + (((dotN a (matVec Dm b)).scale (wb * wa)).swap
          + (dotN b (matVec Dm b)).scale (wb * wb))) :=
    BPair.oneValue_trans (quadPolSwap Dm hDr hDl a b ha hb wa wb)
      (BPair.add_congr
        (BPair.oneValue_refl _)
        (BPair.add_congr (ground.swap_congr hflip)
          (BPair.oneValue_refl _)))
  have eG1 := quadPol Gd hGr hGl a b ha hb wa wb
  have eG2 := quadPolSwap Gd hGr hGl a b ha hb wa wb
  constructor
  · exact collectStep
      ((dotN a (matVec Dm a)).scale (wa * wa))
      ((dotN b (matVec Dm b)).scale (wb * wb))
      ((dotN a (matVec Dm b)).scale (wb * wa))
      ((dotN a (matVec Dm b)).scale (wb * wa))
      ((dotN a (matVec Gd a)).scale (wa * wa))
      ((dotN b (matVec Gd b)).scale (wb * wb))
      ((dotN a (matVec Gd b)).scale (wb * wa))
      ((dotN b (matVec Gd a)).scale (wa * wb)) cd (cn * D2)
      (ground.leB_congr (BPair.scale_congr cd eD1)
        (BPair.scale_congr (cn * D2) eG1) (hDhi _ hw1))
      (ground.leB_congr
        (ground.swap_congr (BPair.scale_congr (cn * D2) eG2))
        (BPair.scale_congr cd eD2) (hDlo _ hw2))
  · exact collectStep
      ((dotN a (matVec Dm a)).scale (wa * wa))
      ((dotN b (matVec Dm b)).scale (wb * wb))
      (((dotN a (matVec Dm b)).scale (wb * wa)).swap)
      (((dotN a (matVec Dm b)).scale (wb * wa)).swap)
      ((dotN a (matVec Gd a)).scale (wa * wa))
      ((dotN b (matVec Gd b)).scale (wb * wb))
      (((dotN a (matVec Gd b)).scale (wb * wa)).swap)
      (((dotN b (matVec Gd a)).scale (wa * wb)).swap) cd (cn * D2)
      (ground.leB_congr (BPair.scale_congr cd eD2)
        (BPair.scale_congr (cn * D2) eG2) (hDhi _ hw2))
      (ground.leB_congr
        (ground.swap_congr (BPair.scale_congr (cn * D2) eG1))
        (BPair.scale_congr cd eD1) (hDlo _ hw1))

/-- Clause (ii)'s step, derived at the vector level: the sandwich's
step with the two transfer contractions and the deviation's
two-sided cap — `capStepRead`'s leading conjuncts — price the
doubled sandwiched deviation two-sidedly at the step's collected
weights against the headward gram, the cap's two splits at the
cross-cleared sum and its swapped partner, the polarization's own
read. -/
theorem cap_step_price {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ)
    (Gd Gh : Mat) (cn cd ln ld ln' ld' : Pos)
    (sp1 sp2 : Split n') (spU spL : Split n)
    (hstep : sandwichStep C C' Y1' Y1 Y0' Y0 n n')
    (hc1 : contractRead (transfer C) Gd Gh ln ld sp1)
    (hc2 : contractRead (transfer C') Gd Gh ln' ld' sp2)
    (hcap : capQ (devQ Y0' Y0) Gd cn cd spU spL) :
    (∀ u : List BPair, u.length = n' →
      (quadForm (matScale 2 (devQ Y1' Y1).1) u).scale
          (cd * (ld * ld * (ld' * ld')))
        ≤ (quadForm Gh u).scale
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
            * (devQ Y1' Y1).2))
    ∧ (∀ u : List BPair, u.length = n' →
      ((quadForm Gh u).scale
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
            * (devQ Y1' Y1).2)).swap
        ≤ (quadForm (matScale 2 (devQ Y1' Y1).1) u).scale
          (cd * (ld * ld * (ld' * ld')))) := by
  obtain ⟨hC, hC', _, _, _, _, hs⟩ := hstep
  have hcap' : capAt (matScale cd (devQ Y0' Y0).1)
      (matScale (cn * (devQ Y0' Y0).2) Gd) spU spL := hcap
  obtain ⟨hSd, hCd, _, _, _, _⟩ := hcap'
  have hD : sqAt (devQ Y0' Y0).1 n := sqAt_matScale_reflect cd _ hSd
  have hGd : sqAt Gd n :=
    sqAt_matScale_reflect (cn * (devQ Y0' Y0).2) _ hCd
  have hDr0 : rowsLen n (devQ Y0' Y0).1 := rowsLen_of_sqAt hD
  have hDl0 : (devQ Y0' Y0).1.length = n := sqAt_len hD
  have hsymD : matOneValue (transposeM (devQ Y0' Y0).1)
      (devQ Y0' Y0).1 :=
    matOne_unscale cd n _ _ (transposeLen _ hDr0 hDl0)
      (rowsLen_cast hDl0 (rowsLen_transposeM _)) hDl0 hDr0
      (matOne_trans
        (matOne_symm (transposeM_matScale cd n (devQ Y0' Y0).1 hDr0))
        (sym_of_capAt _ _ spU spL hcap))
  have hDhi := cap_hi (devQ Y0' Y0) Gd cn cd spU spL hcap
  have hDlo := cap_lo (devQ Y0' Y0) Gd cn cd spU spL hcap
  have hcon : ∀ u : List BPair, u.length = n' →
      (quadForm Gd (matVec (transfer C).1 u)).scale (ld * ld)
        ≤ (quadForm Gh u).scale (ln * ln * (C.2 * C.2)) :=
    contract_all (transfer C) Gd Gh ln ld sp1 hc1
  have hcon' : ∀ u : List BPair, u.length = n' →
      (quadForm Gd (matVec (transfer C').1 u)).scale (ld' * ld')
        ≤ (quadForm Gh u).scale (ln' * ln' * (C'.2 * C'.2)) :=
    contract_all (transfer C') Gd Gh ln' ld' sp2 hc2
  have main : ∀ u : List BPair, u.length = n' →
      ((quadForm (matScale 2 (devQ Y1' Y1).1) u).scale
          (cd * (ld * ld * (ld' * ld')))
        ≤ (quadForm Gh u).scale
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
            * (devQ Y1' Y1).2))
      ∧ (((quadForm Gh u).scale
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
            * (devQ Y1' Y1).2)).swap
        ≤ (quadForm (matScale 2 (devQ Y1' Y1).1) u).scale
          (cd * (ld * ld * (ld' * ld')))) := by
    intro u hu
    -- the shape reads
    have hTr : rowsLen n' (transfer C).1 :=
      rowsLen_mapRows BPair.swap C.1 n' (rectAt_rows hC)
    have hTl : (transfer C).1.length = n :=
      (length_matSwap C.1).trans (rectAt_len hC)
    have hT'r : rowsLen n' (transfer C').1 :=
      rowsLen_mapRows BPair.swap C'.1 n' (rectAt_rows hC')
    have hT'l : (transfer C').1.length = n :=
      (length_matSwap C'.1).trans (rectAt_len hC')
    have hDl : (devQ Y0' Y0).1.length = n := sqAt_len hD
    have hDr : rowsLen n (devQ Y0' Y0).1 := rowsLen_of_sqAt hD
    have ha : (matVec (transfer C).1 u).length = n :=
      (matVec_length _ u).trans hTl
    have hb : (matVec (transfer C').1 u).length = n :=
      (matVec_length _ u).trans hT'l
    have hWr : rowsLen n'
        (matMul (devQ Y0' Y0).1 (transfer C').1) :=
      rowsLen_matMul_of (devQ Y0' Y0).1 (transfer C').1
        (fun hp => by rw [hT'l, ← hDl]; exact hp) hT'r
    have hWl : (matMul (devQ Y0' Y0).1 (transfer C').1).length = n :=
      (length_matMul _ _).trans hDl
    -- the sandwich's clearing, spelled at the cross-scaled matrices
    have hsM : matOneValue
        (matScale (C.2 * ((devQ Y0' Y0).2 * C'.2)) (devQ Y1' Y1).1)
        (matScale (devQ Y1' Y1).2
          (matMul (transposeM (transfer C).1)
            (matMul (devQ Y0' Y0).1 (transfer C').1))) := hs
    -- the tie: the next deviation's cleared form at `u` is the
    -- cross form of the two transfer images at the deeper datum
    have tie : ((quadForm (devQ Y1' Y1).1 u).scale
        (C.2 * ((devQ Y0' Y0).2 * C'.2))).oneValue
        ((dotN (matVec (transfer C).1 u)
          (matVec (devQ Y0' Y0).1
            (matVec (transfer C').1 u))).scale (devQ Y1' Y1).2) := by
      refine BPair.oneValue_trans
        (BPair.oneValue_symm
          (quadForm_scale (C.2 * ((devQ Y0' Y0).2 * C'.2))
            (devQ Y1' Y1).1 u)) ?_
      refine BPair.oneValue_trans
        (dotN_matVec_congrM _ _ u u hsM) ?_
      refine BPair.oneValue_trans
        (quadForm_scale (devQ Y1' Y1).2
          (matMul (transposeM (transfer C).1)
            (matMul (devQ Y0' Y0).1 (transfer C').1)) u) ?_
      refine BPair.scale_congr (devQ Y1' Y1).2 ?_
      refine BPair.oneValue_trans
        (dotN_congrR u _ _ (poly.oneValue_symm
          (matVec_comp (transposeM (transfer C).1)
            (matMul (devQ Y0' Y0).1 (transfer C').1) u n' hWr hu
            (rowsLen_cast (hTl.trans hWl.symm)
              (rowsLen_transposeM (transfer C).1))))) ?_
      refine BPair.oneValue_trans
        (dotN_transpose_flip (transfer C).1 n' hTr u
          (matVec (matMul (devQ Y0' Y0).1 (transfer C').1) u) hu
          ((matVec_length _ u).trans (hWl.trans hTl.symm))) ?_
      refine BPair.oneValue_trans
        (dotN_comm (matVec (matMul (devQ Y0' Y0).1 (transfer C').1) u)
          (matVec (transfer C).1 u)) ?_
      exact dotN_congrR (matVec (transfer C).1 u) _ _
        (poly.oneValue_symm
          (matVec_comp (devQ Y0' Y0).1 (transfer C').1 u n' hT'r hu
            (rowsLen_cast hT'l.symm hDr)))
    -- the polarization's two-sided core at the two images
    have core := polarCore (devQ Y0' Y0).1 Gd (devQ Y0' Y0).2 cn cd
      hD hGd hsymD hDhi hDlo
      (matVec (transfer C).1 u) (matVec (transfer C').1 u) ha hb
      C'.2 C.2
    -- the contractions price the collected read
    have price : ∀ z : BPair,
        z.scale cd
          ≤ ((dotN (matVec (transfer C).1 u)
                (matVec Gd (matVec (transfer C).1 u))).scale
                  (C'.2 * C'.2)
              + (dotN (matVec (transfer C').1 u)
                (matVec Gd (matVec (transfer C').1 u))).scale
                  (C.2 * C.2)).scale (cn * (devQ Y0' Y0).2) →
        z.scale (cd * (ld * ld * (ld' * ld')))
          ≤ (quadForm Gh u).scale
              (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
                * ((C.2 * C'.2)
                  * (C.2 * ((devQ Y0' Y0).2 * C'.2)))) := by
      intro z hz
      have s1 := ground.leB_scale hz (ld * ld * (ld' * ld'))
      rw [BPair.scale_scale z cd (ld * ld * (ld' * ld')),
        BPair.scale_scale
          ((dotN (matVec (transfer C).1 u)
              (matVec Gd (matVec (transfer C).1 u))).scale
                (C'.2 * C'.2)
            + (dotN (matVec (transfer C').1 u)
              (matVec Gd (matVec (transfer C').1 u))).scale
                (C.2 * C.2))
          (cn * (devQ Y0' Y0).2) (ld * ld * (ld' * ld')),
        BPair.scale_add
          ((dotN (matVec (transfer C).1 u)
            (matVec Gd (matVec (transfer C).1 u))).scale
              (C'.2 * C'.2))
          ((dotN (matVec (transfer C').1 u)
            (matVec Gd (matVec (transfer C').1 u))).scale
              (C.2 * C.2))
          ((cn * (devQ Y0' Y0).2) * (ld * ld * (ld' * ld'))),
        BPair.scale_scale
          (dotN (matVec (transfer C).1 u)
            (matVec Gd (matVec (transfer C).1 u)))
          (C'.2 * C'.2)
          ((cn * (devQ Y0' Y0).2) * (ld * ld * (ld' * ld'))),
        BPair.scale_scale
          (dotN (matVec (transfer C').1 u)
            (matVec Gd (matVec (transfer C').1 u)))
          (C.2 * C.2)
          ((cn * (devQ Y0' Y0).2) * (ld * ld * (ld' * ld'))),
        posP1 (C'.2 * C'.2) (cn * (devQ Y0' Y0).2) (ld * ld)
          (ld' * ld'),
        posP2 (C.2 * C.2) (cn * (devQ Y0' Y0).2) (ld * ld)
          (ld' * ld'),
        ← BPair.scale_scale
          (dotN (matVec (transfer C).1 u)
            (matVec Gd (matVec (transfer C).1 u)))
          (ld * ld)
          ((C'.2 * C'.2) * ((cn * (devQ Y0' Y0).2) * (ld' * ld'))),
        ← BPair.scale_scale
          (dotN (matVec (transfer C').1 u)
            (matVec Gd (matVec (transfer C').1 u)))
          (ld' * ld')
          ((C.2 * C.2) * ((cn * (devQ Y0' Y0).2) * (ld * ld)))]
        at s1
      have s2 := ground.leB_trans s1 (ground.leB_add
        (ground.leB_scale (hcon u hu)
          ((C'.2 * C'.2) * ((cn * (devQ Y0' Y0).2) * (ld' * ld'))))
        (ground.leB_scale (hcon' u hu)
          ((C.2 * C.2) * ((cn * (devQ Y0' Y0).2) * (ld * ld)))))
      rw [BPair.scale_scale (quadForm Gh u) (ln * ln * (C.2 * C.2))
          ((C'.2 * C'.2) * ((cn * (devQ Y0' Y0).2) * (ld' * ld'))),
        BPair.scale_scale (quadForm Gh u) (ln' * ln' * (C'.2 * C'.2))
          ((C.2 * C.2) * ((cn * (devQ Y0' Y0).2) * (ld * ld))),
        ← BPair.scale_addW (quadForm Gh u)
          ((ln * ln * (C.2 * C.2))
            * ((C'.2 * C'.2) * ((cn * (devQ Y0' Y0).2) * (ld' * ld'))))
          ((ln' * ln' * (C'.2 * C'.2))
            * ((C.2 * C.2) * ((cn * (devQ Y0' Y0).2) * (ld * ld)))),
        posMain C.2 C'.2 (ln * ln) (ln' * ln') (ld * ld) (ld' * ld')
          cn (devQ Y0' Y0).2] at s2
      exact s2
    have masterA := price _ core.1
    have masterB := price _ core.2
    -- the tie's return and the shared clearing's cancellation
    have eChain : ((quadForm (matScale 2 (devQ Y1' Y1).1) u).scale
        ((cd * (ld * ld * (ld' * ld')))
          * ((C.2 * C'.2)
            * (C.2 * ((devQ Y0' Y0).2 * C'.2))))).oneValue
        (((dotN (matVec (transfer C).1 u)
            (matVec (devQ Y0' Y0).1
              (matVec (transfer C').1 u))).scale (C.2 * C'.2)
          + (dotN (matVec (transfer C).1 u)
            (matVec (devQ Y0' Y0).1
              (matVec (transfer C').1 u))).scale
                (C.2 * C'.2)).scale
          ((cd * (ld * ld * (ld' * ld'))) * (devQ Y1' Y1).2)) := by
      refine BPair.oneValue_trans
        (BPair.scale_congr
          ((cd * (ld * ld * (ld' * ld')))
            * ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2))))
          (quadForm_scale 2 (devQ Y1' Y1).1 u)) ?_
      rw [BPair.scale_scale (quadForm (devQ Y1' Y1).1 u) 2
          ((cd * (ld * ld * (ld' * ld')))
            * ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2)))),
        posP2 2 (cd * (ld * ld * (ld' * ld'))) (C.2 * C'.2)
          (C.2 * ((devQ Y0' Y0).2 * C'.2)),
        ← BPair.scale_scale (quadForm (devQ Y1' Y1).1 u)
          (C.2 * ((devQ Y0' Y0).2 * C'.2))
          (2 * ((cd * (ld * ld * (ld' * ld'))) * (C.2 * C'.2)))]
      refine BPair.oneValue_trans
        (BPair.scale_congr
          (2 * ((cd * (ld * ld * (ld' * ld'))) * (C.2 * C'.2)))
          tie) ?_
      rw [BPair.scale_scale
          (dotN (matVec (transfer C).1 u)
            (matVec (devQ Y0' Y0).1 (matVec (transfer C').1 u)))
          (devQ Y1' Y1).2
          (2 * ((cd * (ld * ld * (ld' * ld'))) * (C.2 * C'.2))),
        posFin2 (devQ Y1' Y1).2 2 (cd * (ld * ld * (ld' * ld')))
          (C.2 * C'.2),
        ← BPair.scale_scale
          (dotN (matVec (transfer C).1 u)
            (matVec (devQ Y0' Y0).1 (matVec (transfer C').1 u)))
          ((C.2 * C'.2) * 2)
          ((cd * (ld * ld * (ld' * ld'))) * (devQ Y1' Y1).2),
        ← BPair.scale_scale
          (dotN (matVec (transfer C).1 u)
            (matVec (devQ Y0' Y0).1 (matVec (transfer C').1 u)))
          (C.2 * C'.2) 2,
        BPair.scale_two
          ((dotN (matVec (transfer C).1 u)
            (matVec (devQ Y0' Y0).1
              (matVec (transfer C').1 u))).scale (C.2 * C'.2))]
      exact BPair.oneValue_refl _
    constructor
    · have hmA := ground.leB_scale masterA (devQ Y1' Y1).2
      rw [BPair.scale_scale
          ((dotN (matVec (transfer C).1 u)
              (matVec (devQ Y0' Y0).1
                (matVec (transfer C').1 u))).scale (C.2 * C'.2)
            + (dotN (matVec (transfer C).1 u)
              (matVec (devQ Y0' Y0).1
                (matVec (transfer C').1 u))).scale (C.2 * C'.2))
          (cd * (ld * ld * (ld' * ld'))) (devQ Y1' Y1).2,
        BPair.scale_scale (quadForm Gh u)
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
            * ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2))))
          (devQ Y1' Y1).2,
        ground.mul_right_comm
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld)))
          ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2)))
          (devQ Y1' Y1).2] at hmA
      refine ground.leB_of_scale
        (w := (C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2))) ?_
      rw [BPair.scale_scale (quadForm (matScale 2 (devQ Y1' Y1).1) u)
          (cd * (ld * ld * (ld' * ld')))
          ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2))),
        BPair.scale_scale (quadForm Gh u)
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
            * (devQ Y1' Y1).2)
          ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2)))]
      exact ground.leB_congr_left (BPair.oneValue_symm eChain) hmA
    · have hmB := ground.leB_scale masterB (devQ Y1' Y1).2
      rw [BPair.scale_scale
          (((dotN (matVec (transfer C).1 u)
              (matVec (devQ Y0' Y0).1
                (matVec (transfer C').1 u))).scale (C.2 * C'.2)
            + (dotN (matVec (transfer C).1 u)
              (matVec (devQ Y0' Y0).1
                (matVec (transfer C').1 u))).scale
                  (C.2 * C'.2)).swap)
          (cd * (ld * ld * (ld' * ld'))) (devQ Y1' Y1).2,
        BPair.scale_scale (quadForm Gh u)
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
            * ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2))))
          (devQ Y1' Y1).2,
        ground.mul_right_comm
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld)))
          ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2)))
          (devQ Y1' Y1).2] at hmB
      have hsw := ground.leB_swap hmB
      rw [BPair.scale_swap
          ((dotN (matVec (transfer C).1 u)
              (matVec (devQ Y0' Y0).1
                (matVec (transfer C').1 u))).scale (C.2 * C'.2)
            + (dotN (matVec (transfer C).1 u)
              (matVec (devQ Y0' Y0).1
                (matVec (transfer C').1 u))).scale (C.2 * C'.2))
          ((cd * (ld * ld * (ld' * ld'))) * (devQ Y1' Y1).2),
        BPair.swap_swap] at hsw
      refine ground.leB_of_scale
        (w := (C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2))) ?_
      rw [BPair.scale_swap
          ((quadForm Gh u).scale
            (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
              * (devQ Y1' Y1).2))
          ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2))),
        BPair.scale_scale (quadForm Gh u)
          (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld))
            * (devQ Y1' Y1).2)
          ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2))),
        BPair.scale_scale (quadForm (matScale 2 (devQ Y1' Y1).1) u)
          (cd * (ld * ld * (ld' * ld')))
          ((C.2 * C'.2) * (C.2 * ((devQ Y0' Y0).2 * C'.2)))]
      exact ground.leB_congr_right (BPair.oneValue_symm eChain) hsw
  exact ⟨fun u hu => (main u hu).1, fun u hu => (main u hu).2⟩

/-! Clause (iii): the deck polynomial, the solvent, the pivot
identities, and the exact factorization. -/

private def entryAt (m : Mat) (i j : Nat) : BPair :=
  ground.getAt BPair.unit (ground.getAt [] m i) j

/-- The quadratic site datum's polynomial matrix,
`Bᵀ z² - A z + B` entrywise. -/
def deckPMat (A B : Mat) : split.PMat :=
  ground.matOf A.length A.length (fun i j =>
    [entryAt B i j, (entryAt A i j).swap, entryAt B j i])

/-- The deck polynomial, the quadratic site datum's determinant,
its deck symmetry `lem:deckfactor`'s read. -/
def deckPoly (A B : Mat) : Poly := split.pminor (deckPMat A B)

/-- The solvent identity `Bᵀ X² + B = A X` at the cleared
solvent. -/
def solventRead (X : MatQ) (A B : Mat) (n : Nat) : Prop :=
  sqAt X.1 n ∧ sqAt A n ∧ sqAt B n
  ∧ oneValueQ (addQ (mulQ (transposeQ (ofM B)) (mulQ X X)) (ofM B))
      (mulQ (ofM A) X)

instance (X : MatQ) (A B : Mat) (n : Nat) :
    Decidable (solventRead X A B n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ oneValueQ _ _))

/-- The pivot-identity pair `Y X = B`, `Y + Bᵀ X = A`. -/
def pivotPairRead (Y X : MatQ) (A B : Mat) (n : Nat) : Prop :=
  sqAt Y.1 n ∧ sqAt X.1 n ∧ sqAt A n ∧ sqAt B n
  ∧ oneValueQ (mulQ Y X) (ofM B)
  ∧ oneValueQ (addQ Y (mulQ (transposeQ (ofM B)) X)) (ofM A)

instance (Y X : MatQ) (A B : Mat) (n : Nat) :
    Decidable (pivotPairRead Y X A B n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The pivot map's step: the witness at `Y C = B` with the image
`Y♯ = A + Bᵀ T` at the transfer factor. -/
def pivotStepRead (Y C Ynext : MatQ) (A B : Mat) (n : Nat) : Prop :=
  sqAt Y.1 n ∧ sqAt C.1 n ∧ sqAt Ynext.1 n ∧ sqAt A n ∧ sqAt B n
  ∧ oneValueQ (mulQ Y C) (ofM B)
  ∧ oneValueQ Ynext
      (addQ (ofM A) (mulQ (ofM (transposeM B)) (transfer C)))

instance (Y C Ynext : MatQ) (A B : Mat) (n : Nat) :
    Decidable (pivotStepRead Y C Ynext A B n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The exact factorization `U = U₁ U₂` at the cleared factors:
`X₂ U₁ = z X₂ Bᵀ + Bᵀ X₁ - X₂ A` and `X₂ U₂ = z X₂ - X₁`, the
product against the quadratic site datum at the clearing's
square. -/
def facSplitRead (X : MatQ) (A B : Mat) (n : Nat) : Prop :=
  sqAt X.1 n ∧ sqAt A n ∧ sqAt B n
  ∧ split.pmatOneValue
    (split.pmatMul
      (ground.matOf A.length A.length (fun i j =>
        [entryAt (matAdd (matMul (transposeM B) X.1)
           (matSwap (matScale X.2 A))) i j,
         entryAt (matScale X.2 (transposeM B)) i j]))
      (ground.matOf A.length A.length (fun i j =>
        [(entryAt X.1 i j).swap,
         if i == j then BPair.ofPos X.2 else BPair.unit])))
    ((deckPMat A B).map (fun r => r.map (fun p =>
      p.map (fun x => x.scale (X.2 * X.2)))))

instance (X : MatQ) (A B : Mat) (n : Nat) :
    Decidable (facSplitRead X A B n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ split.pmatOneValue _ _))

/-- The ball center's floor `Ŷ ⪰ (y0 + ρ) G` at the cleared
scales, one split. -/
def floorRead {o : Nat} (Yc : MatQ) (G : Mat)
    (y0n y0d rn rd : Pos) (spF : Split o) : Prop :=
  splitRead (siteDatum (matScale (y0d * rd) Yc.1)
    (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) spF
  ∧ psdAt spF

instance {o : Nat} (Yc : MatQ) (G : Mat) (y0n y0d rn rd : Pos)
    (spF : Split o) :
    Decidable (floorRead Yc G y0n y0d rn rd spF) :=
  inferInstanceAs (Decidable (_ ∧ _ = _))

/-- The ball certificate's three counts at a located center — the
pivot map's step at the center, the transfer factor's contraction
at `λ`, the floor at `y0 + ρ`, the center defect capped at `ρ0` —
with the modulus data: `λ∘` at `y0 λ∘ = λ (y0 + ρ)` and
`ρ0 + μ ρ ≤ ρ` at `μ = λ∘²`, the cross-multiplied reads, the
modulus below one at the occupied `ρ0`'s own margin. -/
def ballRead {o : Nat} (Yc Cc Ysh : MatQ) (A B G : Mat)
    (ln ld y0n y0d rn rd r0n r0d lcn lcd : Pos)
    (spC spF spU spL : Split o) : Prop :=
  pivotStepRead Yc Cc Ysh A B o
  ∧ contractRead (transfer Cc) G G ln ld spC
  ∧ floorRead Yc G y0n y0d rn rd spF
  ∧ capQ (devQ Ysh Yc) G r0n r0d spU spL
  ∧ y0n * (lcn * (ld * rd)) = ln * ((y0n * rd + rn * y0d) * lcd)
  ∧ r0n * ((lcd * lcd) * rd) + (lcn * lcn) * (rn * r0d)
      ≤ rn * (r0d * (lcd * lcd))

instance {o : Nat} (Yc Cc Ysh : MatQ) (A B G : Mat)
    (ln ld y0n y0d rn rd r0n r0d lcn lcd : Pos)
    (spC spF spU spL : Split o) :
    Decidable (ballRead Yc Cc Ysh A B G ln ld y0n y0d rn rd
      r0n r0d lcn lcd spC spF spU spL) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ = _ ∧ _ ≤ _))

/-- The ball's membership walk: each pivot square at the stated
order with its deviation from the center capped two-sidedly at
`ρ G`, one shape read and one cap pair per pivot. -/
def ballList {o : Nat} (Yc : MatQ) (G : Mat) (rn rd : Pos) :
    List MatQ → List (Split o × Split o) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | X :: Xs, sp :: sps =>
      sqAt X.1 o
      ∧ capQ (devQ X Yc) G rn rd sp.1 sp.2
      ∧ ballList Yc G rn rd Xs sps

def decBallList {o : Nat} (Yc : MatQ) (G : Mat) (rn rd : Pos) :
    ∀ (Xs : List MatQ) (sps : List (Split o × Split o)),
    Decidable (ballList Yc G rn rd Xs sps)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | _ :: Xs, _ :: sps =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ inferInstance
          (decBallList Yc G rn rd Xs sps))

instance {o : Nat} (Yc : MatQ) (G : Mat) (rn rd : Pos)
    (Xs : List MatQ) (sps : List (Split o × Split o)) :
    Decidable (ballList Yc G rn rd Xs sps) :=
  decBallList Yc G rn rd Xs sps

/-- Clause (ii)'s iteration: the cap steps walked down the chain
at the recursion-named brackets, each step's out cap the next
step's stated pair and the gram list walking the slabs' own blocks
beside the reversed factors, the bracket at depth `i` named and
geometric.  Each certificate carries the step's order pair — the
deeper then the headward — the two certified pairs, the two
contraction splits at the headward order, the in cap's pair at the
deeper, and the out cap's at the headward. -/
def capWalk : List Mat → Pos → Pos → MatQ → MatQ →
    List MatQ → List MatQ → List MatQ → List MatQ →
    List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2) →
    Prop
  | _, _, _, _, _, [], [], [], [], [] => True
  | _, _, _, _, _, [], [], [], [], _ :: _ => False
  | _, _, _, _, _, [], [], [], _ :: _, _ => False
  | _, _, _, _, _, [], [], _ :: _, _, _ => False
  | _, _, _, _, _, [], _ :: _, _, _, _ => False
  | _, _, _, _, _, _ :: _, [], _, _, _ => False
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _ => False
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _ => False
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [] => False
  | Gs, cn, cd, Y0', Y0, C :: Cs, C' :: Cs', Y1 :: Ys, Y1' :: Ys',
      ⟨_, lam, lam', sp1, sp2, spU, spL, spU', spL'⟩ :: certs =>
      capStepRead C C' Y1' Y1 Y0' Y0 (ground.getAt [] Gs 0)
        (ground.getAt [] Gs 1) cn cd lam.1 lam.2 lam'.1 lam'.2
        sp1 sp2 spU spL spU' spL'
      ∧ capWalk (Gs.drop 1)
          (cn * (lam.1 * lam.1 * (lam'.2 * lam'.2)
            + lam'.1 * lam'.1 * (lam.2 * lam.2)))
          (2 * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2))))
          Y1' Y1 Cs Cs' Ys Ys' certs

def decCapWalk : ∀ (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
      (Cs Cs' Ys Ys' : List MatQ)
      (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
        × Split p.2 × Split p.2 × Split p.1 × Split p.1
        × Split p.2 × Split p.2)),
    Decidable (capWalk Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs)
  | _, _, _, _, _, [], [], [], [], [] => isTrue trivial
  | _, _, _, _, _, [], [], [], [], _ :: _ => isFalse (fun h => h)
  | _, _, _, _, _, [], [], [], _ :: _, _ => isFalse (fun h => h)
  | _, _, _, _, _, [], [], _ :: _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, [], _ :: _, _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, [], _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [] =>
      isFalse (fun h => h)
  | _, _, _, _, _, _ :: Cs, _ :: Cs', _ :: Ys, _ :: Ys',
      ⟨_, _, _, _, _, _, _, _, _⟩ :: certs =>
      @instDecidableAnd _ _ inferInstance
        (decCapWalk _ _ _ _ _ Cs Cs' Ys Ys' certs)

instance (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
    (Cs Cs' Ys Ys' : List MatQ)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2)) :
    Decidable (capWalk Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs) :=
  decCapWalk Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs

/-- The tied sandwich's step at the reversed slab order:
`E_i = Ř_{i+1}ᵀ E_{i+1} Ř'_{i+1} + δ·1` at the tail witnesses'
transfer factors, the tie's datum riding each step, the shapes at
the boundary's two orders. -/
def driftStep (dn : BPair) (C C' Y1' Y1 Y0' Y0 : MatQ) (n n' : Nat) :
    Prop :=
  rectAt C.1 n n' ∧ rectAt C'.1 n n'
  ∧ sqAt Y1'.1 n' ∧ sqAt Y1.1 n' ∧ sqAt Y0'.1 n ∧ sqAt Y0.1 n
  ∧ oneValueQ (devQ Y1' Y1)
      (addQ
        (mulQ (transposeQ (transfer C))
          (mulQ (devQ Y0' Y0) (transfer C')))
        (matScaleB dn (idMat n'), Pos.one))

instance (dn : BPair) (C C' Y1' Y1 Y0' Y0 : MatQ) (n n' : Nat) :
    Decidable (driftStep dn C C' Y1' Y1 Y0' Y0 n n') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ oneValueQ _ _))

/-- Clause (ii)'s step at the tie: the two contraction certificates
and the deviation's cap propagate to the doubled next deviation at
`c (λ² + λ'²) G_{i+1} + 2 s G_{i+1}`, each display's gram its own
slab's block — the deviation's cap at the deeper block, the tie
datum's identity capped two-sidedly at `s G_{i+1}` at the headward
block joining the step's display, the two splits' own polarization
at the identity's datum. -/
def driftCapStep {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ)
    (Gd Gh : Mat) (dn : BPair) (cn cd sn sd ln ld ln' ld' : Pos)
    (sp1 sp2 : Split n') (spU spL : Split n) (spU' spL' : Split n')
    (spS spS' : Split n') : Prop :=
  driftStep dn C C' Y1' Y1 Y0' Y0 n n'
  ∧ contractRead (transfer C) Gd Gh ln ld sp1
  ∧ contractRead (transfer C') Gd Gh ln' ld' sp2
  ∧ capQ ((matScaleB dn (idMat n')), Pos.one) Gh sn sd spS spS'
  ∧ capQ (devQ Y0' Y0) Gd cn cd spU spL
  ∧ capQ (doubleQ (devQ Y1' Y1)) Gh
      (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld)) * sd
        + 2 * (sn * (cd * (ld * ld * (ld' * ld')))))
      (cd * (ld * ld * (ld' * ld')) * sd) spU' spL'

instance {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ) (Gd Gh : Mat)
    (dn : BPair) (cn cd sn sd ln ld ln' ld' : Pos)
    (sp1 sp2 : Split n') (spU spL : Split n) (spU' spL' : Split n')
    (spS spS' : Split n') :
    Decidable (driftCapStep C C' Y1' Y1 Y0' Y0 Gd Gh dn cn cd sn sd
      ln ld ln' ld' sp1 sp2 spU spL spU' spL' spS spS') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The step updates folded over the certificates: the seed's
geometric read joined to the tie datum's fold, one summand per
step. -/
def driftFold : Pos → Pos → Pos → Pos →
    List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2) →
    Pos × Pos
  | cn, cd, _, _, [] => (cn, cd)
  | cn, cd, sn, sd, ⟨_, lam, lam', _⟩ :: cs =>
      driftFold
        (cn * (lam.1 * lam.1 * (lam'.2 * lam'.2)
            + lam'.1 * lam'.1 * (lam.2 * lam.2)) * sd
          + 2 * (sn * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2)))))
        (2 * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2)) * sd)) sn sd cs

/-- Clause (ii)'s iteration at the tie: the tied cap steps walked
down the chain at the recursion-named brackets, each step's out cap
the next step's stated pair and the gram list walking the slabs'
own blocks beside the reversed factors, the bracket at depth `i`
the seed's geometric read joined to the tie datum's fold over the
steps' certificates.  Each certificate carries the step's order
pair — the deeper then the headward — the two certified pairs, the
two contraction splits at the headward order, the in cap's pair at
the deeper, the out cap's at the headward, and the tie datum's two
splits at the headward. -/
def driftWalk (dn : BPair) (sn sd : Pos) :
    List Mat → Pos → Pos → MatQ → MatQ →
    List MatQ → List MatQ → List MatQ → List MatQ →
    List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2) →
    Prop
  | _, _, _, _, _, [], [], [], [], [] => True
  | _, _, _, _, _, [], [], [], [], _ :: _ => False
  | _, _, _, _, _, [], [], [], _ :: _, _ => False
  | _, _, _, _, _, [], [], _ :: _, _, _ => False
  | _, _, _, _, _, [], _ :: _, _, _, _ => False
  | _, _, _, _, _, _ :: _, [], _, _, _ => False
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _ => False
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _ => False
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [] => False
  | Gs, cn, cd, Y0', Y0, C :: Cs, C' :: Cs', Y1 :: Ys, Y1' :: Ys',
      ⟨_, lam, lam', sp1, sp2, spU, spL, spU', spL', spS, spS'⟩
        :: certs =>
      driftCapStep C C' Y1' Y1 Y0' Y0 (ground.getAt [] Gs 0)
        (ground.getAt [] Gs 1) dn cn cd sn sd lam.1 lam.2 lam'.1 lam'.2
        sp1 sp2 spU spL spU' spL' spS spS'
      ∧ driftWalk dn sn sd (Gs.drop 1)
          (cn * (lam.1 * lam.1 * (lam'.2 * lam'.2)
              + lam'.1 * lam'.1 * (lam.2 * lam.2)) * sd
            + 2 * (sn * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2)))))
          (2 * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2)) * sd))
          Y1' Y1 Cs Cs' Ys Ys' certs

def decDriftWalk (dn : BPair) (sn sd : Pos) :
    ∀ (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
      (Cs Cs' Ys Ys' : List MatQ)
      (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
        × Split p.2 × Split p.2 × Split p.1 × Split p.1
        × Split p.2 × Split p.2 × Split p.2 × Split p.2)),
    Decidable (driftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs)
  | _, _, _, _, _, [], [], [], [], [] => isTrue trivial
  | _, _, _, _, _, [], [], [], [], _ :: _ => isFalse (fun h => h)
  | _, _, _, _, _, [], [], [], _ :: _, _ => isFalse (fun h => h)
  | _, _, _, _, _, [], [], _ :: _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, [], _ :: _, _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, [], _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [] =>
      isFalse (fun h => h)
  | _, _, _, _, _, _ :: Cs, _ :: Cs', _ :: Ys, _ :: Ys',
      ⟨_, _, _, _, _, _, _, _, _, _, _⟩ :: certs =>
      @instDecidableAnd _ _ inferInstance
        (decDriftWalk dn sn sd _ _ _ _ _ Cs Cs' Ys Ys' certs)

instance (dn : BPair) (sn sd : Pos) (Gs : List Mat) (cn cd : Pos)
    (Y0' Y0 : MatQ) (Cs Cs' Ys Ys' : List MatQ)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2)) :
    Decidable (driftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs) :=
  decDriftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs

/-- The two windows at their own roots' site data at one shared
clearing: the couplings equal and the diagonals tied at the roots'
drift below the perturbation slab, the two tail recursions, the
tied steps, and the tied walk from the slab down to the
observable's depth at the gram list's own slab blocks. -/
def driftShareRead (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 j : Nat) (ns : List Nat)
    (dn : BPair) (cn cd sn sd : Pos) (Gs : List Mat)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2)) :
    Prop :=
  greenprod.tailRead diag off Xs Rs ns
  ∧ greenprod.tailRead diag' off' Xs' Rs' ns
  ∧ ((List.range off.length).all (fun i =>
      Nat.ble w0 i || decide (matOneValue (ground.getAt [] off' i)
        (ground.getAt [] off i)))) = true
  ∧ ((List.range diag.length).all (fun i =>
      Nat.ble w0 i || decide (matOneValue (ground.getAt [] diag' i)
        (matAdd (ground.getAt [] diag i)
          (matScaleB dn (idMat (ground.getAt 0 ns i))))))) = true
  ∧ ((List.range diag.length).all (fun k =>
      Nat.ble w0 k || decide
      (driftStep dn (ground.getAt greenprod.dM Rs k)
        (ground.getAt greenprod.dM Rs' k)
        (ground.getAt greenprod.dM Xs' k)
        (ground.getAt greenprod.dM Xs k)
        (ground.getAt greenprod.dM Xs' (k + 1))
        (ground.getAt greenprod.dM Xs (k + 1))
        (ground.getAt 0 ns (k + 1))
        (ground.getAt 0 ns k)))) = true
  ∧ driftWalk dn sn sd Gs cn cd (ground.getAt greenprod.dM Xs' w0)
      (ground.getAt greenprod.dM Xs w0)
      ((Rs.take w0).drop j).reverse ((Rs'.take w0).drop j).reverse
      ((Xs.take w0).drop j).reverse ((Xs'.take w0).drop j).reverse certs

instance (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 j : Nat) (ns : List Nat)
    (dn : BPair) (cn cd sn sd : Pos) (Gs : List Mat)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2)) :
    Decidable (driftShareRead diag off diag' off' Xs Rs Xs' Rs'
      w0 j ns dn cn cd sn sd Gs certs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _ ∧ _ = _ ∧ _ = _ ∧ _))

/-- The doubled datum's cap reads the datum's own at the doubled
clearing. -/
private theorem capQ_double {o : Nat} (D : MatQ) (G : Mat)
    (cn cd : Pos) (spU spL : Split o)
    (h : capQ (doubleQ D) G cn cd spU spL) :
    capQ D G cn (2 * cd) spU spL := by
  have h' : capAt (matScale cd (matScale 2 D.1))
      (matScale (cn * D.2) G) spU spL := h
  rw [matScale_matScale 2 cd D.1, ground.mul_comm cd 2] at h'
  exact h'

/-- The tied walk's lists at the certificate count. -/
theorem driftWalk_len (dn : BPair) (sn sd : Pos) :
    ∀ (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
      (Cs Cs' Ys Ys' : List MatQ)
      (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
        × Split p.2 × Split p.2 × Split p.1 × Split p.1
        × Split p.2 × Split p.2 × Split p.2 × Split p.2)),
    driftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs →
    Cs.length = certs.length ∧ Cs'.length = certs.length
      ∧ Ys.length = certs.length ∧ Ys'.length = certs.length
  | _, _, _, _, _, [], [], [], [], [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | _, _, _, _, _, [], [], [], [], _ :: _, h => False.elim h
  | _, _, _, _, _, [], [], [], _ :: _, _, h => False.elim h
  | _, _, _, _, _, [], [], _ :: _, _, _, h => False.elim h
  | _, _, _, _, _, [], _ :: _, _, _, _, h => False.elim h
  | _, _, _, _, _, _ :: _, [], _, _, _, h => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _, h => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _, h => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [], h => False.elim h
  | _, _, _, _, _, _ :: Cs, _ :: Cs', _ :: Ys, _ :: Ys', _ :: certs, h =>
      have ih := driftWalk_len dn sn sd _ _ _ _ _ Cs Cs' Ys Ys' certs h.2
      ⟨congrArg (fun m => m + 1) ih.1, congrArg (fun m => m + 1) ih.2.1,
        congrArg (fun m => m + 1) ih.2.2.1,
        congrArg (fun m => m + 1) ih.2.2.2⟩

/-- The tied walk's fold-out: at an occupied certificate list the
walk caps the last step's deviation two-sidedly at the folded
pair over the walk's last block, the seed's geometric read joined
to the tie datum's fold over the steps' certificates. -/
theorem driftWalk_last (dn : BPair) (sn sd : Pos) :
    ∀ (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
      (Cs Cs' Ys Ys' : List MatQ)
      (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
        × Split p.2 × Split p.2 × Split p.1 × Split p.1
        × Split p.2 × Split p.2 × Split p.2 × Split p.2)),
    driftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs →
    0 < certs.length →
    ∃ (k : Nat) (spU spL : Split k),
      capQ (devQ (ground.getAt greenprod.dM Ys' (certs.length - 1))
          (ground.getAt greenprod.dM Ys (certs.length - 1)))
        (ground.getAt [] Gs certs.length)
        (driftFold cn cd sn sd certs).1 (driftFold cn cd sn sd certs).2
        spU spL
  | _, _, _, _, _, [], [], [], [], [], _, hocc =>
      absurd hocc (Nat.not_lt_zero 0)
  | _, _, _, _, _, [], [], [], [], _ :: _, h, _ => False.elim h
  | _, _, _, _, _, [], [], [], _ :: _, _, h, _ => False.elim h
  | _, _, _, _, _, [], [], _ :: _, _, _, h, _ => False.elim h
  | _, _, _, _, _, [], _ :: _, _, _, _, h, _ => False.elim h
  | _, _, _, _, _, _ :: _, [], _, _, _, h, _ => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _, h, _ => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _, h, _ => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [], h, _ =>
      False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _,
      [⟨p, _, _, _, _, _, _, spU', spL', _, _⟩], h, _ =>
      ⟨p.2, spU', spL',
        capQ_double _ _ _ _ spU' spL' h.1.2.2.2.2.2⟩
  | Gs, _, _, _, _, _ :: Cs, _ :: Cs', Y1 :: Ys, Y1' :: Ys',
      cert :: c2 :: rest, h, _ => by
      have hrec := driftWalk_last dn sn sd (Gs.drop 1) _ _ Y1' Y1
        Cs Cs' Ys Ys' (c2 :: rest) h.2 (Nat.succ_pos rest.length)
      have e1 : ground.getAt greenprod.dM Ys' ((c2 :: rest).length - 1)
          = ground.getAt greenprod.dM (Y1' :: Ys')
              ((cert :: c2 :: rest).length - 1) := rfl
      have e2 : ground.getAt greenprod.dM Ys ((c2 :: rest).length - 1)
          = ground.getAt greenprod.dM (Y1 :: Ys)
              ((cert :: c2 :: rest).length - 1) := rfl
      have hadd : 1 + (c2 :: rest).length = (c2 :: rest).length + 1 :=
        (Nat.succ_add 0 (c2 :: rest).length).trans
          (congrArg Nat.succ (Nat.zero_add (c2 :: rest).length))
      have e3 : ground.getAt ([] : Mat) (Gs.drop 1) (c2 :: rest).length
          = ground.getAt ([] : Mat) Gs ((c2 :: rest).length + 1) :=
        (ground.getAt_drop ([] : Mat) 1 Gs (c2 :: rest).length).trans
          (congrArg (ground.getAt ([] : Mat) Gs) hadd)
      rw [e1, e2, e3] at hrec
      exact hrec

/-- The bundle's walk caps the depth-`j` pivot deviation
two-sidedly at the accumulated pair, `thm:groundreads`(iii)'s
bracket read at the observable's depth; the bridge from the
reversed walk's last place down to depth `j` reads the walk's own
list counts. -/
theorem driftShare_cap (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 j : Nat) (ns : List Nat)
    (dn : BPair) (cn cd sn sd : Pos) (Gs : List Mat)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2))
    (h : driftShareRead diag off diag' off' Xs Rs Xs' Rs'
      w0 j ns dn cn cd sn sd Gs certs)
    (hocc : 0 < certs.length) (hjw : j < w0) :
    ∃ (k : Nat) (spU spL : Split k),
      capQ (devQ (ground.getAt greenprod.dM Xs' j)
          (ground.getAt greenprod.dM Xs j))
        (ground.getAt [] Gs certs.length)
        (driftFold cn cd sn sd certs).1 (driftFold cn cd sn sd certs).2
        spU spL := by
  match certs, h, hocc with
  | c :: cs, h, _ =>
    have hw := h.2.2.2.2.2
    have hlen := driftWalk_len dn sn sd Gs cn cd
      (ground.getAt greenprod.dM Xs' w0) (ground.getAt greenprod.dM Xs w0)
      ((Rs.take w0).drop j).reverse ((Rs'.take w0).drop j).reverse
      ((Xs.take w0).drop j).reverse ((Xs'.take w0).drop j).reverse
      (c :: cs) hw
    have hlast := driftWalk_last dn sn sd Gs cn cd
      (ground.getAt greenprod.dM Xs' w0) (ground.getAt greenprod.dM Xs w0)
      ((Rs.take w0).drop j).reverse ((Rs'.take w0).drop j).reverse
      ((Xs.take w0).drop j).reverse ((Xs'.take w0).drop j).reverse
      (c :: cs) hw (Nat.succ_pos cs.length)
    have hl : ((Xs.take w0).drop j).length = cs.length + 1 :=
      (ground.length_reverse ((Xs.take w0).drop j)).symm.trans hlen.2.2.1
    have hl' : ((Xs'.take w0).drop j).length = cs.length + 1 :=
      (ground.length_reverse ((Xs'.take w0).drop j)).symm.trans
        hlen.2.2.2
    have eX : ground.getAt greenprod.dM ((Xs.take w0).drop j).reverse
        cs.length = ground.getAt greenprod.dM Xs j :=
      (ground.getAt_reverse greenprod.dM ((Xs.take w0).drop j)
        cs.length 0 hl.symm).trans
        ((ground.getAt_drop greenprod.dM j (Xs.take w0) 0).trans
          (ground.getAt_take greenprod.dM w0 Xs j hjw))
    have eX' : ground.getAt greenprod.dM ((Xs'.take w0).drop j).reverse
        cs.length = ground.getAt greenprod.dM Xs' j :=
      (ground.getAt_reverse greenprod.dM ((Xs'.take w0).drop j)
        cs.length 0 hl'.symm).trans
        ((ground.getAt_drop greenprod.dM j (Xs'.take w0) 0).trans
          (ground.getAt_take greenprod.dM w0 Xs' j hjw))
    obtain ⟨k, spU, spL, hc⟩ := hlast
    refine ⟨k, spU, spL, ?_⟩
    rw [← eX, ← eX']
    exact hc

/-! The ball's positivity: the center's floor with the deviation's
two-sided cap price a member's form at or above the sum's unit at
every vector, the three positive reads collected at one scaled
value identity over the form folds. -/

private theorem swap_scale (x : BPair) (w : Pos) :
    (x.scale w).swap = x.swap.scale w := rfl

private theorem pairNull (x : BPair) (w : Pos) :
    (x.swap.scale w + x.scale w).oneValue BPair.unit := by
  rw [← swap_scale]
  exact BPair.swap_add_null (BPair.oneValue_refl (x.scale w))

private theorem pairNull' (x : BPair) (w : Pos) :
    (x.scale w + x.swap.scale w).oneValue BPair.unit := by
  rw [BPair.add_comm]
  exact pairNull x w

private theorem posPb (X2 rd y0d : Pos) :
    X2 * rd * y0d = y0d * rd * X2 := by
  rw [ground.mul_right_comm X2 rd y0d, ground.mul_comm X2 y0d,
    ground.mul_right_comm y0d X2 rd]

private theorem posPc1 (rn X2 Yc2 y0d : Pos) :
    rn * (X2 * Yc2) * y0d = Yc2 * (rn * y0d) * X2 := by
  rw [← ground.mul_assoc rn X2 Yc2, ground.mul_right_comm rn X2 Yc2,
    ground.mul_right_comm (rn * Yc2) X2 y0d,
    ground.mul_right_comm rn Yc2 y0d, ground.mul_comm (rn * y0d) Yc2]

private theorem posPd (Yc2 y0n y0d rn rd X2 : Pos) :
    Yc2 * (y0n * rd + rn * y0d) * X2
      = Yc2 * (y0n * rd) * X2 + Yc2 * (rn * y0d) * X2 := by
  rw [ground.left_distrib Yc2 (y0n * rd) (rn * y0d),
    ground.right_distrib (Yc2 * (y0n * rd)) (Yc2 * (rn * y0d)) X2]

/-- The three scaled positive reads collect to the member's scaled
form: the center terms withdraw pairwise at the memberwise swap. -/
private theorem ballCombine (a b c : BPair)
    (X2 Yc2 y0n y0d rn rd : Pos) :
    ((c.scale (rn * (X2 * Yc2))
        + (a.scale Yc2 + b.swap.scale X2).scale rd).scale y0d
      + ((b.scale (y0d * rd)
          + (c.scale (Yc2 * (y0n * rd + rn * y0d))).swap).scale X2
        + c.scale (Yc2 * (y0n * rd) * X2))).oneValue
    (a.scale (Yc2 * rd * y0d)) := by
  rw [BPair.scale_add (a.scale Yc2) (b.swap.scale X2) rd,
    BPair.scale_scale a Yc2 rd, BPair.scale_scale b.swap X2 rd,
    BPair.scale_add (c.scale (rn * (X2 * Yc2)))
      (a.scale (Yc2 * rd) + b.swap.scale (X2 * rd)) y0d,
    BPair.scale_add (a.scale (Yc2 * rd)) (b.swap.scale (X2 * rd)) y0d,
    BPair.scale_scale c (rn * (X2 * Yc2)) y0d,
    BPair.scale_scale a (Yc2 * rd) y0d,
    BPair.scale_scale b.swap (X2 * rd) y0d,
    swap_scale c (Yc2 * (y0n * rd + rn * y0d)),
    BPair.scale_add (b.scale (y0d * rd))
      (c.swap.scale (Yc2 * (y0n * rd + rn * y0d))) X2,
    BPair.scale_scale b (y0d * rd) X2,
    BPair.scale_scale c.swap (Yc2 * (y0n * rd + rn * y0d)) X2,
    posPd Yc2 y0n y0d rn rd X2,
    ground.BPair.scale_addW c.swap (Yc2 * (y0n * rd) * X2) (Yc2 * (rn * y0d) * X2),
    posPb X2 rd y0d, posPc1 rn X2 Yc2 y0d]
  rw [BPair.add_left_comm (c.scale (Yc2 * (rn * y0d) * X2))
      (a.scale (Yc2 * rd * y0d)) (b.swap.scale (y0d * rd * X2)),
    BPair.add_assoc (a.scale (Yc2 * rd * y0d))
      (c.scale (Yc2 * (rn * y0d) * X2) + b.swap.scale (y0d * rd * X2))
      (b.scale (y0d * rd * X2)
        + (c.swap.scale (Yc2 * (y0n * rd) * X2)
          + c.swap.scale (Yc2 * (rn * y0d) * X2))
        + c.scale (Yc2 * (y0n * rd) * X2)),
    BPair.add_comm (c.swap.scale (Yc2 * (y0n * rd) * X2))
      (c.swap.scale (Yc2 * (rn * y0d) * X2)),
    ← BPair.add_assoc (b.scale (y0d * rd * X2))
      (c.swap.scale (Yc2 * (rn * y0d) * X2))
      (c.swap.scale (Yc2 * (y0n * rd) * X2)),
    BPair.add_assoc
      (b.scale (y0d * rd * X2) + c.swap.scale (Yc2 * (rn * y0d) * X2))
      (c.swap.scale (Yc2 * (y0n * rd) * X2))
      (c.scale (Yc2 * (y0n * rd) * X2)),
    ← BPair.add_assoc
      (c.scale (Yc2 * (rn * y0d) * X2) + b.swap.scale (y0d * rd * X2))
      (b.scale (y0d * rd * X2) + c.swap.scale (Yc2 * (rn * y0d) * X2))
      (c.swap.scale (Yc2 * (y0n * rd) * X2)
        + c.scale (Yc2 * (y0n * rd) * X2)),
    BPair.add_comm (b.scale (y0d * rd * X2))
      (c.swap.scale (Yc2 * (rn * y0d) * X2)),
    BPair.add_add_comm (c.scale (Yc2 * (rn * y0d) * X2))
      (b.swap.scale (y0d * rd * X2))
      (c.swap.scale (Yc2 * (rn * y0d) * X2))
      (b.scale (y0d * rd * X2))]
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_refl (a.scale (Yc2 * rd * y0d)))
    (BPair.oneValue_trans (BPair.add_congr
      (BPair.oneValue_trans (BPair.add_congr
        (pairNull' c (Yc2 * (rn * y0d) * X2))
        (pairNull b (y0d * rd * X2)))
        (BPair.unit_add BPair.unit))
      (pairNull c (Yc2 * (y0n * rd) * X2)))
      (BPair.unit_add BPair.unit))) ?_
  exact BPair.add_unit (a.scale (Yc2 * rd * y0d))

private theorem rowsLen_unmapScale (w : Pos) (n : Nat) : ∀ M : Mat,
    rowsLen n (matScale w M) → rowsLen n M
  | [], _ => trivial
  | r :: t, h =>
    ⟨(ground.length_map _ r).symm.trans h.1,
     rowsLen_unmapScale w n t h.2⟩

/-- The deviation datum's form expansion: the cleared deviation's
quadratic read is the member's form at the center's clearing
against the center's swapped form at the member's, the two scaled
rows' own sum. -/
private theorem devExpand (X Yc : MatQ) (u : List BPair)
    (hXl : X.1.length = u.length) (hXr : rowsLen u.length X.1)
    (hYl : Yc.1.length = u.length) (hYr : rowsLen u.length Yc.1) :
    (quadForm (devQ X Yc).1 u).oneValue
      ((quadForm X.1 u).scale Yc.2
        + ((quadForm Yc.1 u).swap).scale X.2) := by
  refine BPair.oneValue_trans
    (quadForm_add (matScale Yc.2 X.1) (matScale X.2 (matSwap Yc.1)) u
      ((length_matScale Yc.2 X.1).trans hXl)
      (rowsLen_mapRows (fun x => x.scale Yc.2) X.1 u.length hXr)
      ((length_matScale X.2 (matSwap Yc.1)).trans
        ((length_matSwap Yc.1).trans hYl))
      (rowsLen_mapRows (fun x => x.scale X.2) (matSwap Yc.1)
        u.length (rowsLen_mapRows BPair.swap Yc.1 u.length hYr))) ?_
  exact BPair.add_congr (quadForm_scale Yc.2 X.1 u)
    (BPair.oneValue_trans (quadForm_scale X.2 (matSwap Yc.1) u)
      (BPair.scale_congr X.2 (quadForm_swap Yc.1 u)))

/-- The cap datum's form expansion: the capped sum's quadratic
read collects the gram's scaled form with the deviation's own
expansion at the stated clearing. -/
private theorem capExpand (X Yc : MatQ) (G : Mat) (rn rd : Pos)
    (u : List BPair)
    (hXl : X.1.length = u.length) (hXr : rowsLen u.length X.1)
    (hYl : Yc.1.length = u.length) (hYr : rowsLen u.length Yc.1)
    (hGl : G.length = u.length) (hGr : rowsLen u.length G) :
    (quadForm (matAdd (matScale (rn * (devQ X Yc).2) G)
        (matScale rd (devQ X Yc).1)) u).oneValue
      ((quadForm G u).scale (rn * (X.2 * Yc.2))
        + ((quadForm X.1 u).scale Yc.2
          + ((quadForm Yc.1 u).swap).scale X.2).scale rd) := by
  have hDl : (devQ X Yc).1.length = u.length := by
    show (matAdd (matScale Yc.2 X.1)
      (matScale X.2 (matSwap Yc.1))).length = u.length
    rw [length_matAdd (matScale Yc.2 X.1)
        (matScale X.2 (matSwap Yc.1))
        ((length_matScale Yc.2 X.1).trans (hXl.trans
          (((length_matScale X.2 (matSwap Yc.1)).trans
            ((length_matSwap Yc.1).trans hYl)).symm))),
      length_matScale]
    exact hXl
  have hDr : rowsLen u.length (devQ X Yc).1 := by
    show rowsLen u.length (matAdd (matScale Yc.2 X.1)
      (matScale X.2 (matSwap Yc.1)))
    exact rowsLen_matAdd u.length _ _
      (rowsLen_mapRows (fun x => x.scale Yc.2) X.1 u.length hXr)
      (rowsLen_mapRows (fun x => x.scale X.2) (matSwap Yc.1)
        u.length (rowsLen_mapRows BPair.swap Yc.1 u.length hYr))
  refine BPair.oneValue_trans
    (quadForm_add (matScale (rn * (devQ X Yc).2) G)
      (matScale rd (devQ X Yc).1) u
      ((length_matScale (rn * (devQ X Yc).2) G).trans hGl)
      (rowsLen_mapRows (fun x => x.scale (rn * (devQ X Yc).2)) G
        u.length hGr)
      ((length_matScale rd (devQ X Yc).1).trans hDl)
      (rowsLen_mapRows (fun x => x.scale rd) (devQ X Yc).1
        u.length hDr)) ?_
  exact BPair.add_congr
    (quadForm_scale (rn * (X.2 * Yc.2)) G u)
    (BPair.oneValue_trans (quadForm_scale rd (devQ X Yc).1 u)
      (BPair.scale_congr rd (devExpand X Yc u hXl hXr hYl hYr)))

/-- The floor datum's form expansion: the site's quadratic read is
the center's scaled form against the gram's swapped one at the
floor's collected weight. -/
private theorem floorExpand (Yc : MatQ) (G : Mat)
    (y0n y0d rn rd : Pos) (u : List BPair)
    (hYl : Yc.1.length = u.length) (hYr : rowsLen u.length Yc.1)
    (hGl : G.length = u.length) (hGr : rowsLen u.length G) :
    (quadForm (siteDatum (matScale (y0d * rd) Yc.1)
        (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u).oneValue
      ((quadForm Yc.1 u).scale (y0d * rd)
        + ((quadForm G u).scale
            (Yc.2 * (y0n * rd + rn * y0d))).swap) := by
  refine BPair.oneValue_trans
    (quadForm_add (matScale (y0d * rd) Yc.1)
      (matSwap (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u
      ((length_matScale (y0d * rd) Yc.1).trans hYl)
      (rowsLen_mapRows (fun x => x.scale (y0d * rd)) Yc.1
        u.length hYr)
      ((length_matSwap _).trans
        ((length_matScale (Yc.2 * (y0n * rd + rn * y0d)) G).trans
          hGl))
      (rowsLen_mapRows BPair.swap _ u.length
        (rowsLen_mapRows (fun x => x.scale
          (Yc.2 * (y0n * rd + rn * y0d))) G u.length hGr))) ?_
  exact BPair.add_congr (quadForm_scale (y0d * rd) Yc.1 u)
    (BPair.oneValue_trans
      (quadForm_swap (matScale (Yc.2 * (y0n * rd + rn * y0d)) G) u)
      (ground.swap_congr
        (quadForm_scale (Yc.2 * (y0n * rd + rn * y0d)) G u)))

/-- The gram's positive read off the cap alone: the two split
reads' forms join, the deviation withdrawing at the memberwise
swap, so the gram's form sits at or above the sum's unit at every
vector. -/
private theorem gramLe {o : Nat} (X Yc : MatQ) (G : Mat)
    (rn rd : Pos) (spU spL : Split o)
    (hcap : capQ (devQ X Yc) G rn rd spU spL)
    (u : List BPair) (hu : u.length = o) :
    BPair.unit ≤ quadForm G u := by
  have hSl : (matScale rd (devQ X Yc).1).length = u.length := by
    rw [hu]; exact sqAt_len hcap.1
  have hSr : rowsLen u.length (matScale rd (devQ X Yc).1) := by
    rw [hu]; exact rowsLen_of_sqAt hcap.1
  have hCl : (matScale (rn * (devQ X Yc).2) G).length = u.length := by
    rw [hu]; exact sqAt_len hcap.2.1
  have hCr : rowsLen u.length (matScale (rn * (devQ X Yc).2) G) := by
    rw [hu]; exact rowsLen_of_sqAt hcap.2.1
  have h1 : BPair.unit ≤ quadForm
      (siteDatum (matScale (rn * (devQ X Yc).2) G)
        (matScale rd (devQ X Yc).1)) u :=
    ground.leB_of_not_lt
      (psd_all _ spU hcap.2.2.1 hcap.2.2.2.1 u hu)
  have h2 : BPair.unit ≤ quadForm
      (matAdd (matScale (rn * (devQ X Yc).2) G)
        (matScale rd (devQ X Yc).1)) u :=
    ground.leB_of_not_lt
      (psd_all _ spL hcap.2.2.2.2.1 hcap.2.2.2.2.2 u hu)
  have e1 : (quadForm (siteDatum (matScale (rn * (devQ X Yc).2) G)
      (matScale rd (devQ X Yc).1)) u).oneValue
      (quadForm (matScale (rn * (devQ X Yc).2) G) u
        + (quadForm (matScale rd (devQ X Yc).1) u).swap) := by
    refine BPair.oneValue_trans
      (quadForm_add (matScale (rn * (devQ X Yc).2) G)
        (matSwap (matScale rd (devQ X Yc).1)) u hCl hCr
        ((length_matSwap _).trans hSl)
        (rowsLen_mapRows BPair.swap _ _ hSr)) ?_
    exact BPair.add_congr (BPair.oneValue_refl _)
      (quadForm_swap (matScale rd (devQ X Yc).1) u)
  have e2 : (quadForm (matAdd (matScale (rn * (devQ X Yc).2) G)
      (matScale rd (devQ X Yc).1)) u).oneValue
      (quadForm (matScale (rn * (devQ X Yc).2) G) u
        + quadForm (matScale rd (devQ X Yc).1) u) :=
    quadForm_add _ _ u hCl hCr hSl hSr
  have hsum : BPair.unit ≤
      (quadForm G u).scale (rn * (devQ X Yc).2)
        + (quadForm G u).scale (rn * (devQ X Yc).2) := by
    refine ground.leB_congr_right ?_ (ground.unitLeAdd h1 h2)
    refine BPair.oneValue_trans (BPair.add_congr e1 e2) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq
      (BPair.add_add_comm
        (quadForm (matScale (rn * (devQ X Yc).2) G) u)
        ((quadForm (matScale rd (devQ X Yc).1) u).swap)
        (quadForm (matScale (rn * (devQ X Yc).2) G) u)
        (quadForm (matScale rd (devQ X Yc).1) u))) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.add_congr (quadForm_scale (rn * (devQ X Yc).2) G u)
        (quadForm_scale (rn * (devQ X Yc).2) G u))
      (BPair.swap_add_null (BPair.oneValue_refl
        (quadForm (matScale rd (devQ X Yc).1) u)))) ?_
    exact BPair.add_unit _
  exact ground.unitLeOfScale (ground.leB_congr_right
    (BPair.oneValue_of_eq (ground.BPair.scale_addW (quadForm G u)
      (rn * (devQ X Yc).2) (rn * (devQ X Yc).2)).symm) hsum)

/-- A ball member's every split reads the upper side: the center's
floor with the deviation's two-sided cap price the member's form at
or above the sum's unit at every vector, so an occupied count's
witness is refused; the center's shape is the frame, the consumers'
own pivot read, and the gram's positivity is the cap's own
(`gramLe`). -/
theorem ball_psd {o : Nat} (X Yc : MatQ) (G : Mat)
    (y0n y0d rn rd : Pos) (spF spU spL sp : Split o)
    (hYc : sqAt Yc.1 o)
    (hF : floorRead Yc G y0n y0d rn rd spF)
    (hcap : capQ (devQ X Yc) G rn rd spU spL)
    (hsp : splitRead X.1 sp) : psdAt sp := by
  cases Nat.eq_zero_or_pos (revAt sp) with
  | inl h0 => exact h0
  | inr hpos =>
    obtain ⟨u, hu, hlt⟩ := rev_witness X.1 sp hsp hpos
    have hXl : X.1.length = u.length := by rw [hu]; exact sqAt_len hsp.1
    have hXr : rowsLen u.length X.1 := by
      rw [hu]; exact rowsLen_of_sqAt hsp.1
    have hYl : Yc.1.length = u.length := by rw [hu]; exact sqAt_len hYc
    have hYr : rowsLen u.length Yc.1 := by
      rw [hu]; exact rowsLen_of_sqAt hYc
    have hGsq : sqAt G o :=
      sqAt_of ((length_matScale (rn * (devQ X Yc).2) G).symm.trans
          (sqAt_len hcap.2.1))
        (rowsLen_unmapScale (rn * (devQ X Yc).2) o G
          (rowsLen_of_sqAt hcap.2.1))
    have hGl : G.length = u.length := by rw [hu]; exact sqAt_len hGsq
    have hGr : rowsLen u.length G := by
      rw [hu]; exact rowsLen_of_sqAt hGsq
    have hle1 : BPair.unit ≤ quadForm
        (matAdd (matScale (rn * (devQ X Yc).2) G)
          (matScale rd (devQ X Yc).1)) u :=
      ground.leB_of_not_lt
        (psd_all _ spL hcap.2.2.2.2.1 hcap.2.2.2.2.2 u hu)
    have hle2 : BPair.unit ≤ quadForm
        (siteDatum (matScale (y0d * rd) Yc.1)
          (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u :=
      ground.leB_of_not_lt (psd_all _ spF hF.1 hF.2 u hu)
    have hle3 : BPair.unit ≤ quadForm G u :=
      gramLe X Yc G rn rd spU spL hcap u hu
    have eCap := capExpand X Yc G rn rd u hXl hXr hYl hYr hGl hGr
    have eFloor := floorExpand Yc G y0n y0d rn rd u hYl hYr hGl hGr
    have hT : BPair.unit ≤
        (quadForm (matAdd (matScale (rn * (devQ X Yc).2) G)
            (matScale rd (devQ X Yc).1)) u).scale y0d
        + ((quadForm (siteDatum (matScale (y0d * rd) Yc.1)
            (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u).scale X.2
          + (quadForm G u).scale (Yc.2 * (y0n * rd) * X.2)) :=
      ground.unitLeAdd (ground.unitLeScale y0d hle1)
        (ground.unitLeAdd (ground.unitLeScale X.2 hle2)
          (ground.unitLeScale (Yc.2 * (y0n * rd) * X.2) hle3))
    have eT : ((quadForm (matAdd (matScale (rn * (devQ X Yc).2) G)
            (matScale rd (devQ X Yc).1)) u).scale y0d
        + ((quadForm (siteDatum (matScale (y0d * rd) Yc.1)
            (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u).scale X.2
          + (quadForm G u).scale (Yc.2 * (y0n * rd) * X.2))).oneValue
        ((quadForm X.1 u).scale (Yc.2 * rd * y0d)) := by
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.scale_congr y0d eCap)
        (BPair.add_congr (BPair.scale_congr X.2 eFloor)
          (BPair.oneValue_refl _))) ?_
      exact ballCombine (quadForm X.1 u) (quadForm Yc.1 u)
        (quadForm G u) X.2 Yc.2 y0n y0d rn rd
    exact absurd (ground.scaleLtUnit (Yc.2 * rd * y0d) hlt)
      (ground.leB_not_lt (ground.leB_congr_right eT hT))

/-- The floor collection: the cap read's scaled sum against the
floor read's is the member's scaled form joined to the gram's
swapped one — `ballCombine`'s read with the gram's positivity term
withdrawn at its own swap pair. -/
private theorem floorCombine (a b c : BPair)
    (X2 Yc2 y0n y0d rn rd : Pos) :
    ((c.scale (rn * (X2 * Yc2))
        + (a.scale Yc2 + b.swap.scale X2).scale rd).scale y0d
      + (b.scale (y0d * rd)
          + (c.scale (Yc2 * (y0n * rd + rn * y0d))).swap).scale
            X2).oneValue
    (a.scale (Yc2 * rd * y0d)
      + (c.scale (Yc2 * (y0n * rd) * X2)).swap) := by
  have hnull : (c.scale (Yc2 * (y0n * rd) * X2)
      + (c.scale (Yc2 * (y0n * rd) * X2)).swap).oneValue
      BPair.unit := by
    rw [BPair.add_comm]
    exact BPair.swap_add_null (BPair.oneValue_refl _)
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) hnull)
      (BPair.add_unit _))) ?_
  rw [← BPair.add_assoc
    ((c.scale (rn * (X2 * Yc2))
        + (a.scale Yc2 + b.swap.scale X2).scale rd).scale y0d
      + (b.scale (y0d * rd)
          + (c.scale (Yc2 * (y0n * rd + rn * y0d))).swap).scale X2)
    (c.scale (Yc2 * (y0n * rd) * X2))
    ((c.scale (Yc2 * (y0n * rd) * X2)).swap),
    BPair.add_assoc
    ((c.scale (rn * (X2 * Yc2))
        + (a.scale Yc2 + b.swap.scale X2).scale rd).scale y0d)
    ((b.scale (y0d * rd)
        + (c.scale (Yc2 * (y0n * rd + rn * y0d))).swap).scale X2)
    (c.scale (Yc2 * (y0n * rd) * X2))]
  exact BPair.add_congr (ballCombine a b c X2 Yc2 y0n y0d rn rd)
    (BPair.oneValue_refl _)

/-- A ball member prices its form at the floor: the deviation's
cap withdraws against the center's floor at the gram's read, the
member's form at or beyond `y0`'s multiple of the gram's at every
vector, the cleared spelling at the carriers' second data
(`lem:cornerpivot`(vii)'s handover seed, the dominance tail's
entry read). -/
theorem ball_floor {o : Nat} (X Yc : MatQ) (G : Mat)
    (y0n y0d rn rd : Pos) (spF spU spL : Split o)
    (hX : sqAt X.1 o) (hYc : sqAt Yc.1 o)
    (hF : floorRead Yc G y0n y0d rn rd spF)
    (hcap : capQ (devQ X Yc) G rn rd spU spL) :
    ∀ u : List BPair, u.length = o →
      (quadForm G u).scale (y0n * X.2)
        ≤ (quadForm X.1 u).scale y0d := by
  intro u hu
  have hXl : X.1.length = u.length := by rw [hu]; exact sqAt_len hX
  have hXr : rowsLen u.length X.1 := by
    rw [hu]; exact rowsLen_of_sqAt hX
  have hYl : Yc.1.length = u.length := by rw [hu]; exact sqAt_len hYc
  have hYr : rowsLen u.length Yc.1 := by
    rw [hu]; exact rowsLen_of_sqAt hYc
  have hGsq : sqAt G o :=
    sqAt_of ((length_matScale (rn * (devQ X Yc).2) G).symm.trans
        (sqAt_len hcap.2.1))
      (rowsLen_unmapScale (rn * (devQ X Yc).2) o G
        (rowsLen_of_sqAt hcap.2.1))
  have hGl : G.length = u.length := by rw [hu]; exact sqAt_len hGsq
  have hGr : rowsLen u.length G := by
    rw [hu]; exact rowsLen_of_sqAt hGsq
  have hle1 : BPair.unit ≤ quadForm
      (matAdd (matScale (rn * (devQ X Yc).2) G)
        (matScale rd (devQ X Yc).1)) u :=
    ground.leB_of_not_lt
      (psd_all _ spL hcap.2.2.2.2.1 hcap.2.2.2.2.2 u hu)
  have hle2 : BPair.unit ≤ quadForm
      (siteDatum (matScale (y0d * rd) Yc.1)
        (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u :=
    ground.leB_of_not_lt (psd_all _ spF hF.1 hF.2 u hu)
  have hS2 : BPair.unit ≤ (quadForm X.1 u).scale (Yc.2 * rd * y0d)
      + ((quadForm G u).scale (Yc.2 * (y0n * rd) * X.2)).swap :=
    ground.leB_congr_right
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.scale_congr y0d
            (capExpand X Yc G rn rd u hXl hXr hYl hYr hGl hGr))
          (BPair.scale_congr X.2
            (floorExpand Yc G y0n y0d rn rd u hYl hYr hGl hGr)))
        (floorCombine (quadForm X.1 u) (quadForm Yc.1 u)
          (quadForm G u) X.2 Yc.2 y0n y0d rn rd))
      (ground.unitLeAdd (ground.unitLeScale y0d hle1)
        (ground.unitLeScale X.2 hle2))
  have hk : (quadForm G u).scale (Yc.2 * (y0n * rd) * X.2)
      ≤ (quadForm X.1 u).scale (Yc.2 * rd * y0d) := by
    have h := ground.leB_of_unit_add hS2
    rw [BPair.swap_swap] at h
    exact h
  have e1 : Yc.2 * (y0n * rd) * X.2 = y0n * X.2 * (Yc.2 * rd) := by
    rw [ground.mul_comm Yc.2 (y0n * rd),
      ground.mul_assoc (y0n * rd) Yc.2 X.2,
      ground.mul_comm Yc.2 X.2,
      ← ground.mul_assoc (y0n * rd) X.2 Yc.2,
      ground.mul_assoc y0n rd X.2, ground.mul_comm rd X.2,
      ← ground.mul_assoc y0n X.2 rd,
      ground.mul_assoc (y0n * X.2) rd Yc.2,
      ground.mul_comm rd Yc.2]
  have e2 : Yc.2 * rd * y0d = y0d * (Yc.2 * rd) :=
    ground.mul_comm (Yc.2 * rd) y0d
  rw [e1, e2] at hk
  refine ground.leB_of_scale (w := Yc.2 * rd) ?_
  rw [BPair.scale_scale, BPair.scale_scale]
  exact hk

end spectator
