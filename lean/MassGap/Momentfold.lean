import MassGap.Groundreads

/-!
`lem:momentfold` — the moment folds.  On a band-one head at the dual
representative the ground enters every datum read through two moment
streams, the squares against a stated weight family (`rhoStream`) and
the consecutive products against it (`cStream`), each one fold over
the depth range with the off-range keys vacant; `dStream` is the
second-bond fold the closure reduces.  The ground's recurrence
`b_m ψ_m + b_{m+1} ψ_{m+2} = A_{m+1} ψ_{m+1}` — the eigen-identity's
row read, the diagonal at the ground root cross-added — enters as the
structural walk `recRows`, seeded at the sum's unit (`recRead`), the
degenerate shapes refused arm by arm; the head row and the interior
rows read back off the walk (`rowHead`, `rowAt`, the off-range keys
absorbing at the vacancies, so `rowAt` holds at every key).

Clause (i), the fold identities, exact at every scale: folding the
recurrence against `ψ_m W(m)` reads `c[bW] + c[bW⁺] = ρ[AW]`
(`fold_sq`, at the shifted weight `W⁺(m) = W(m+1)`); the fold against
`ψ_{m+1} W(m)` reads the second identity at the shifted weights, the
second-bond fold against the down-shift's square read (`fold_bond`,
the down-shift `wShift` vacant at the head key); and the second-bond
term reduces by one further fold of the recurrence (`bond2_reduce`),
so every correlator beyond the two streams re-enters them and the
family closes on `ρ` and `c` alone, one identity per weight.

Clause (ii)'s monomial layer.  The moments are the streams at the
monomial weights (`mrho`, `mc`, `md`), with the boundary square
(`bSq`) and the far edge's weighted read (`edgeAt`); the corner
diagonal enters through its quadratic profile, one read per key
(`profWalk`, `diagProf`, `prof_at`), and the bond through its
constant read (`constBond`, `bond_at`).  The up-shifted monomial
expands over the Pascal counts (`cShift1`; `dShift2` at the two-step
shift with the doubled base's powers, `ground.bpow_binom`'s reads),
a constant bond withdraws from a stream at its scale (`cBond`,
`dBondUp`; `rhoBond` at the far edge's own summand, the bond's one
vacant key), the down-shift collapses onto the down-shifted weight
(`wCollapse`) and the down-shifted monomial reads the moment itself
(`wMono_succ`, with the boundary square joining at the vacant power
`wMono_zero`); the profile expands a diagonal-weighted stream onto
three neighboring moments (`profRho`, `profC`), the raised-key read
at the shifted profile's constants (`profCUp`).

Clause (ii)'s rows.  Folding the recurrence at the monomial weights
reads the graded rows: the square fold's row relates three
neighboring square moments to the bond moments over the Pascal
counts (`fa_row`); the reduction's row reads the second-bond and
square moments against the raised-key profile with the far edge's
read (`d_row`, at the plain-bond second-bond withdrawal `dBond`);
the bond fold's rows at the up-shifted monomials read the two-step
Pascal expansion against the profile's expansion, the boundary
square joining at the vacant height (`fb_row_zero`, `fb_row_succ`);
and the second fold's reduction withdraws its top weight, one row
per height relating the bond moments at or below the height's
successor to the square moments below it with the boundary square
and the far edge's reads (`fbd_row_zero`, `fbd_row_succ`).  The
truncated moment vector is the two streams' reads through a stated
degree with the boundary square (`momVec`), and a commutator's
ground read is of equal members, two symmetric data's composed
actions pairing at one value in either order (`commGround`), which
is why the folds rather than commutators close the system.

Clause (ii)'s square system.  The identities at weights through the
stated degree, with the base reads and the boundary square, are one
square linear system for the truncated moment vector: the rows
accumulate from the identities' own term lists at the vector's
width, the four base rows reading the base data, the fold
identities' rows the sum's unit, and the reduced second fold's rows
the far edge's balance partners at the Pascal edge folds, the
shared top weight withdrawing across each reduced row's two sides
(`momSys`, `momRhs`, the shape reads `momSys_len` and
`momSys_rowsLen`, and the read `momSys_read`, every row derived
from its identity).

Clause (iii), the truncation cap.  The stream splits at a stated
depth into its truncated fold and its tail (`tailStream`,
`tail_split`, the beyond-length keys vacant), a tail whose members
decay at a stated pair sits at the pair's gap at or below its first
member (`tail_capped`, `ground.widthSum`'s telescope at the span's
own list), and each member so sits (`edge_capped`); the square
stream's tail is priced at the certificates' decay of the weighted
squares (`tail_price`) and the far edge's read at the decay
composed along the keys between (`edge_price`); the per-step decay
composes from the transfer certificate against the turning read at
the stated degree (`turn_step`), one comparison per step at the
shared clearing withdrawn.

Clause (iv), the scale comparison.  The adjugate's action against a
list's own action pins a vector at the determinant's scale
(`det_pin`, `def:elim`'s adjugate identity read at a vector), so two
solved systems at one shape compare: at the coefficients' site datum
at the shared shape and the data's difference at the shared width,
the solutions' difference at the first determinant's scale reads the
adjugate's action at those differences (`scale_compare`), one read
per moment with the widths the differences' own.

Clause (v)'s datum, width and block arms.  A single-region datum
read is a stream read at its banded weights: the width-one datum
reads the square stream at the diagonal weights with the doubled
bond stream at the bonds' (`datum_read`), the chain form read
collected at the streams with the beyond-band weight vacant, and
two scales' datum reads at one shape differ at the first
determinant's scale by the cofactor reads at the coefficient
differences (`datum_close`), the two-scale comparison read at the
datum fold.  A product read's two-scale width
is priced by the factors' caps against the factors' own widths
(`prodWidth`), and an assembled read, the product joined to its
connected datum, closes at the parts' widths with the connected
reads' caps (`assemble_close`), the magnitude carrier
`thm:windowsep`'s.  On a block chain the recurrence's rows fold
against the components at a stated weight family: the diagonal's
quadratic reads at the squared clearings join the bond reads at the
weight and at its raised shift to the sum's unit (`rhoBlock`,
`cBlock`, `blockFold_sq` at the cleared-pair read
`ground.qOneValue`, `def:ground`'s composite display),
`lem:greenprod`(iii)'s row read at the kernel sides, the band-one
clauses' block twin.
-/

namespace momentfold
open ground

/-- The weight family's down-shift: vacant at the head key, the
prior key's read beyond it. -/
def wShift (W : Nat → BPair) : Nat → BPair
  | 0 => BPair.unit
  | t + 1 => W t

/-- The square stream: the ground's squares against a stated weight
family, one summand per depth with the off-range keys vacant. -/
def rhoStream (psi : List BPair) (W : Nat → BPair) : BPair :=
  ground.bsum (fun k => W k
    * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
    (List.range psi.length)

/-- The bond stream: the consecutive products against the weight
family. -/
def cStream (psi : List BPair) (W : Nat → BPair) : BPair :=
  ground.bsum (fun k => W k
    * (ground.getAt BPair.unit psi k
      * ground.getAt BPair.unit psi (k + 1)))
    (List.range psi.length)

/-- The second-bond fold, the correlator the closure reduces. -/
def dStream (psi : List BPair) (W : Nat → BPair) : BPair :=
  ground.bsum (fun k => W k
    * (ground.getAt BPair.unit psi k
      * ground.getAt BPair.unit psi (k + 2)))
    (List.range psi.length)

/-- The recurrence walk: per depth the row read
`A_k ψ_k ~ b_{k-1} ψ_{k-1} + b_k ψ_{k+1}` with the incoming bond
product the accumulated seed, the last row at the accumulated seed
alone, and the degenerate shapes refused. -/
def recRows : BPair → List BPair → List BPair → List BPair → Prop
  | _, [], _, _ => False
  | p, [a], [], [x] => (a * x).oneValue p
  | _, [_], [], [] => False
  | _, [_], [], _ :: _ :: _ => False
  | _, [_], _ :: _, _ => False
  | _, _ :: _ :: _, [], _ => False
  | _, _ :: _ :: _, _ :: _, [] => False
  | _, _ :: _ :: _, _ :: _, [_] => False
  | p, a :: a' :: as, b :: bs, x :: x' :: xs =>
      (a * x).oneValue (p + b * x')
      ∧ recRows (b * x) (a' :: as) bs (x' :: xs)

def decRecRows : ∀ (p : BPair) (a b psi : List BPair),
    Decidable (recRows p a b psi)
  | _, [], _, _ => isFalse (fun h => h)
  | _, [_], [], [_] => inferInstanceAs (Decidable (BPair.oneValue _ _))
  | _, [_], [], [] => isFalse (fun h => h)
  | _, [_], [], _ :: _ :: _ => isFalse (fun h => h)
  | _, [_], _ :: _, _ => isFalse (fun h => h)
  | _, _ :: _ :: _, [], _ => isFalse (fun h => h)
  | _, _ :: _ :: _, _ :: _, [] => isFalse (fun h => h)
  | _, _ :: _ :: _, _ :: _, [_] => isFalse (fun h => h)
  | _, _ :: a' :: as, _ :: bs, _ :: x' :: xs =>
      @instDecidableAnd _ _ inferInstance
        (decRecRows _ (a' :: as) bs (x' :: xs))

instance (p : BPair) (a b psi : List BPair) :
    Decidable (recRows p a b psi) := decRecRows p a b psi

/-- The ground's recurrence: the walk at the unit seed. -/
def recRead (a b psi : List BPair) : Prop :=
  recRows BPair.unit a b psi

instance (a b psi : List BPair) : Decidable (recRead a b psi) :=
  decRecRows BPair.unit a b psi

/-! The three streams at a list split off its head key: the head
summand joined to the shorter list's stream at the raised weight. -/

/-- The square stream at a list split off its head key. -/
private theorem rhoStream_cons (x : BPair) (xs : List BPair)
    (W : Nat → BPair) :
    rhoStream (x :: xs) W
      = W 0 * (x * x) + rhoStream xs (fun k => W (k + 1)) :=
  ground.foldB_range_cons _ xs.length

/-- The bond stream at a list split off its head key. -/
private theorem cStream_cons (x : BPair) (xs : List BPair)
    (W : Nat → BPair) :
    cStream (x :: xs) W
      = W 0 * (x * ground.getAt BPair.unit xs 0)
        + cStream xs (fun k => W (k + 1)) :=
  ground.foldB_range_cons _ xs.length

/-- The second-bond stream at a list split off its head key. -/
private theorem dStream_cons (x : BPair) (xs : List BPair)
    (W : Nat → BPair) :
    dStream (x :: xs) W
      = W 0 * (x * ground.getAt BPair.unit xs 1)
        + dStream xs (fun k => W (k + 1)) :=
  ground.foldB_range_cons _ xs.length

/-- At a one-member list the square stream reads the head key's
weight against the head square. -/
private theorem rhoOne (x : BPair) (W : Nat → BPair) :
    (rhoStream [x] W).oneValue (W 0 * (x * x)) :=
  BPair.oneValue_trans (BPair.oneValue_of_eq (rhoStream_cons x [] W))
    (BPair.add_unit _)

/-- At a one-member list the bond stream is vacant: its one summand
pairs the head against the key beyond the list. -/
private theorem cOne (x : BPair) (W : Nat → BPair) :
    (cStream [x] W).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.oneValue_of_eq (cStream_cons x [] W))
    (BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_unit x))
        (BPair.oneValue_refl _))
      (BPair.oneValue_trans (BPair.add_congr (BPair.mul_unit _)
        (BPair.oneValue_refl _)) (BPair.add_unit _)))

/-- At a one-member list the second-bond stream is vacant. -/
private theorem dOne (x : BPair) (W : Nat → BPair) :
    (dStream [x] W).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.oneValue_of_eq (dStream_cons x [] W))
    (BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_unit x))
        (BPair.oneValue_refl _))
      (BPair.oneValue_trans (BPair.add_congr (BPair.mul_unit _)
        (BPair.oneValue_refl _)) (BPair.add_unit _)))

/-- The seed term at the sum's unit is vacant. -/
private theorem seedUnit (W : Nat → BPair) (g : BPair) :
    (W 0 * (BPair.unit * g)).oneValue BPair.unit :=
  BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl (W 0)) (BPair.unit_mul g))
    (BPair.mul_unit (W 0))

/-- The five-summand regrouping the square fold's collection takes:
the two bond heads join their own tails. -/
private theorem sqCollect (P Q S Z1 Z2 : BPair) :
    P + Q + (S + (Z1 + Z2)) = P + (Q + Z1 + (S + Z2)) := by
  rw [BPair.add_assoc P Q (S + (Z1 + Z2)), BPair.add_assoc Q Z1 (S + Z2),
    BPair.add_left_comm S Z1 Z2]

/-- The five-summand regrouping the bond fold's collection takes:
the second-bond head joins its own tail and the square head joins
its. -/
private theorem bondCollect (P Q S D Z : BPair) :
    P + Q + (S + (D + Z)) = P + (S + D + (Q + Z)) := by
  rw [BPair.add_assoc P Q (S + (D + Z)), BPair.add_left_comm Q S (D + Z),
    BPair.add_left_comm Q D Z, BPair.add_assoc S D (Q + Z)]

/-! The walk's reads: the two lengths, the head row at the
accumulated seed, and the interior rows at every key. -/

/-- The walk's head row at the accumulated seed. -/
private theorem headRow : ∀ (p : BPair) (a b psi : List BPair),
    recRows p a b psi →
    (ground.getAt BPair.unit a 0 * ground.getAt BPair.unit psi 0).oneValue
      (p + ground.getAt BPair.unit b 0 * ground.getAt BPair.unit psi 1)
  | _, [], _, _, h => False.elim h
  | p, [_], [], [_], h =>
      BPair.oneValue_trans h (BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl p)
            (BPair.unit_mul BPair.unit))
          (BPair.add_unit p)))
  | _, [_], [], [], h => False.elim h
  | _, [_], [], _ :: _ :: _, h => False.elim h
  | _, [_], _ :: _, _, h => False.elim h
  | _, _ :: _ :: _, [], _, h => False.elim h
  | _, _ :: _ :: _, _ :: _, [], h => False.elim h
  | _, _ :: _ :: _, _ :: _, [_], h => False.elim h
  | _, _ :: _ :: _, _ :: _, _ :: _ :: _, h => h.1

/-- The walk's interior rows at every key, the off-range keys
absorbing at the vacancies. -/
private theorem rowAll : ∀ (p : BPair) (a b psi : List BPair),
    recRows p a b psi → ∀ k : Nat,
    (ground.getAt BPair.unit a (k + 1)
      * ground.getAt BPair.unit psi (k + 1)).oneValue
      (ground.getAt BPair.unit b k * ground.getAt BPair.unit psi k
        + ground.getAt BPair.unit b (k + 1)
          * ground.getAt BPair.unit psi (k + 2))
  | _, [], _, _, h, _ => False.elim h
  | _, [_], [], [x], _, k =>
      BPair.oneValue_trans (BPair.unit_mul BPair.unit)
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.add_congr
              (BPair.unit_mul (ground.getAt BPair.unit [x] k))
              (BPair.unit_mul BPair.unit))
            (BPair.add_unit BPair.unit)))
  | _, [_], [], [], h, _ => False.elim h
  | _, [_], [], _ :: _ :: _, h, _ => False.elim h
  | _, [_], _ :: _, _, h, _ => False.elim h
  | _, _ :: _ :: _, [], _, h, _ => False.elim h
  | _, _ :: _ :: _, _ :: _, [], h, _ => False.elim h
  | _, _ :: _ :: _, _ :: _, [_], h, _ => False.elim h
  | _, _ :: a' :: as, _ :: bs, _ :: x' :: xs, h, 0 =>
      headRow _ (a' :: as) bs (x' :: xs) h.2
  | _, _ :: a' :: as, _ :: bs, _ :: x' :: xs, h, k + 1 =>
      rowAll _ (a' :: as) bs (x' :: xs) h.2 k

/-- The walk's ground count is its diagonal count. -/
private theorem lenAgo : ∀ (p : BPair) (a b psi : List BPair),
    recRows p a b psi → psi.length = a.length
  | _, [], _, _, h => False.elim h
  | _, [_], [], [_], _ => rfl
  | _, [_], [], [], h => False.elim h
  | _, [_], [], _ :: _ :: _, h => False.elim h
  | _, [_], _ :: _, _, h => False.elim h
  | _, _ :: _ :: _, [], _, h => False.elim h
  | _, _ :: _ :: _, _ :: _, [], h => False.elim h
  | _, _ :: _ :: _, _ :: _, [_], h => False.elim h
  | _, _ :: a' :: as, _ :: bs, _ :: x' :: xs, h =>
      congrArg (fun n => n + 1) (lenAgo _ (a' :: as) bs (x' :: xs) h.2)

/-- The walk's bond count is one below its diagonal count. -/
private theorem lenBgo : ∀ (p : BPair) (a b psi : List BPair),
    recRows p a b psi → b.length + 1 = a.length
  | _, [], _, _, h => False.elim h
  | _, [_], [], [_], _ => rfl
  | _, [_], [], [], h => False.elim h
  | _, [_], [], _ :: _ :: _, h => False.elim h
  | _, [_], _ :: _, _, h => False.elim h
  | _, _ :: _ :: _, [], _, h => False.elim h
  | _, _ :: _ :: _, _ :: _, [], h => False.elim h
  | _, _ :: _ :: _, _ :: _, [_], h => False.elim h
  | _, _ :: a' :: as, _ :: bs, _ :: x' :: xs, h =>
      congrArg (fun n => n + 1) (lenBgo _ (a' :: as) bs (x' :: xs) h.2)

/-- The recurrence's ground count is its diagonal count. -/
theorem recRead_lenA (a b psi : List BPair) (h : recRead a b psi) :
    psi.length = a.length := lenAgo BPair.unit a b psi h

/-- The recurrence's bond count is one below its diagonal count. -/
theorem recRead_lenB (a b psi : List BPair) (h : recRead a b psi) :
    b.length + 1 = a.length := lenBgo BPair.unit a b psi h

/-- The recurrence's head row: the head diagonal against the head
ground reads the head bond against the next ground, the seed at the
sum's unit absorbing. -/
theorem rowHead (a b psi : List BPair) (h : recRead a b psi) :
    (ground.getAt BPair.unit a 0 * ground.getAt BPair.unit psi 0).oneValue
      (ground.getAt BPair.unit b 0 * ground.getAt BPair.unit psi 1) :=
  BPair.oneValue_trans (headRow BPair.unit a b psi h)
    (BPair.unit_add _)

/-- The recurrence at every interior key: the diagonal at the raised
key against its ground reads the two flanking bonds against their own
grounds, the off-range keys vacant. -/
theorem rowAt (a b psi : List BPair) (h : recRead a b psi) (k : Nat) :
    (ground.getAt BPair.unit a (k + 1)
      * ground.getAt BPair.unit psi (k + 1)).oneValue
      (ground.getAt BPair.unit b k * ground.getAt BPair.unit psi k
        + ground.getAt BPair.unit b (k + 1)
          * ground.getAt BPair.unit psi (k + 2)) :=
  rowAll BPair.unit a b psi h k

/-- The square fold at an accumulated seed: the square stream against
the diagonal weight reads the seed term at the head ground joined to
the two bond streams. -/
private theorem foldSqGo : ∀ (p : BPair) (a b psi : List BPair),
    recRows p a b psi → ∀ W : Nat → BPair,
    (rhoStream psi (fun k => ground.getAt BPair.unit a k * W k)).oneValue
      (W 0 * (p * ground.getAt BPair.unit psi 0)
        + (cStream psi (fun k => ground.getAt BPair.unit b k * W k)
          + cStream psi (fun k => ground.getAt BPair.unit b k * W (k + 1))))
  | _, [], _, _, h, _ => False.elim h
  | p, [a0], [], [x], h, W =>
      BPair.oneValue_trans
        (BPair.oneValue_trans (rhoOne x _)
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.mul_mul_mul_comm a0 (W 0) x x))
            (BPair.oneValue_trans (BPair.mul_congr_left h)
              (BPair.oneValue_of_eq (BPair.mul_left_comm p (W 0) x)))))
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.oneValue_refl (W 0 * (p * x)))
              (BPair.oneValue_trans
                (BPair.add_congr (cOne x _) (cOne x _))
                (BPair.add_unit BPair.unit)))
            (BPair.add_unit (W 0 * (p * x)))))
  | _, [_], [], [], h, _ => False.elim h
  | _, [_], [], _ :: _ :: _, h, _ => False.elim h
  | _, [_], _ :: _, _, h, _ => False.elim h
  | _, _ :: _ :: _, [], _, h, _ => False.elim h
  | _, _ :: _ :: _, _ :: _, [], h, _ => False.elim h
  | _, _ :: _ :: _, _ :: _, [_], h, _ => False.elim h
  | p, a0 :: a1 :: as, b0 :: bs, x0 :: x1 :: xs, h, W => by
      have ih := foldSqGo (b0 * x0) (a1 :: as) bs (x1 :: xs) h.2
        (fun k => W (k + 1))
      have hLdec : rhoStream (x0 :: x1 :: xs)
            (fun k => ground.getAt BPair.unit (a0 :: a1 :: as) k * W k)
          = a0 * W 0 * (x0 * x0)
            + rhoStream (x1 :: xs)
              (fun k => ground.getAt BPair.unit (a1 :: as) k * W (k + 1)) :=
        rhoStream_cons _ _ _
      have hC1 : cStream (x0 :: x1 :: xs)
            (fun k => ground.getAt BPair.unit (b0 :: bs) k * W k)
          = b0 * W 0 * (x0 * x1)
            + cStream (x1 :: xs)
              (fun k => ground.getAt BPair.unit bs k * W (k + 1)) :=
        cStream_cons _ _ _
      have hC2 : cStream (x0 :: x1 :: xs)
            (fun k => ground.getAt BPair.unit (b0 :: bs) k * W (k + 1))
          = b0 * W 1 * (x0 * x1)
            + cStream (x1 :: xs)
              (fun k => ground.getAt BPair.unit bs k * W (k + 2)) :=
        cStream_cons _ _ _
      have hExp : (p + b0 * x1) * (W 0 * x0)
          = W 0 * (p * x0) + b0 * W 0 * (x0 * x1) := by
        rw [BPair.right_distrib, BPair.mul_left_comm p (W 0) x0,
          BPair.mul_mul_mul_comm b0 x1 (W 0) x0, BPair.mul_comm x1 x0]
      have hHead : (a0 * W 0 * (x0 * x0)).oneValue
          (W 0 * (p * x0) + b0 * W 0 * (x0 * x1)) :=
        BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.mul_mul_mul_comm a0 (W 0) x0 x0))
          (BPair.oneValue_trans (BPair.mul_congr_left h.1)
            (BPair.oneValue_of_eq hExp))
      have hSh : W 1 * (b0 * x0 * x1) = b0 * W 1 * (x0 * x1) :=
        (BPair.mul_left_comm (W 1) (b0 * x0) x1).trans
          (BPair.mul_mul_mul_comm b0 (W 1) x0 x1).symm
      have hIh : (rhoStream (x1 :: xs)
            (fun k =>
              ground.getAt BPair.unit (a1 :: as) k * W (k + 1))).oneValue
          (b0 * W 1 * (x0 * x1)
            + (cStream (x1 :: xs)
                (fun k => ground.getAt BPair.unit bs k * W (k + 1))
              + cStream (x1 :: xs)
                (fun k => ground.getAt BPair.unit bs k * W (k + 2)))) :=
        BPair.oneValue_trans ih
          (BPair.add_congr (BPair.oneValue_of_eq hSh) (BPair.oneValue_refl _))
      rw [hLdec, hC1, hC2]
      exact BPair.oneValue_trans (BPair.add_congr hHead hIh)
        (BPair.oneValue_of_eq (sqCollect (W 0 * (p * x0))
          (b0 * W 0 * (x0 * x1)) (b0 * W 1 * (x0 * x1))
          (cStream (x1 :: xs)
            (fun k => ground.getAt BPair.unit bs k * W (k + 1)))
          (cStream (x1 :: xs)
            (fun k => ground.getAt BPair.unit bs k * W (k + 2)))))

/-- The bond fold at an accumulated seed: the bond stream against the
diagonal weight reads the seed term at the next ground joined to the
second-bond stream and the down-shifted square stream. -/
private theorem foldBondGo : ∀ (p : BPair) (a b psi : List BPair),
    recRows p a b psi → ∀ W : Nat → BPair,
    (cStream psi (fun k => ground.getAt BPair.unit a k * W k)).oneValue
      (W 0 * (p * ground.getAt BPair.unit psi 1)
        + (dStream psi (fun k => ground.getAt BPair.unit b k * W (k + 1))
          + rhoStream psi
              (wShift (fun t => ground.getAt BPair.unit b t * W t))))
  | _, [], _, _, h, _ => False.elim h
  | _, [_], [], [_], _, _ =>
      BPair.oneValue_trans (cOne _ _)
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.add_congr
              (BPair.oneValue_trans
                (BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_unit _))
                (BPair.mul_unit _))
              (BPair.oneValue_trans
                (BPair.add_congr (dOne _ _)
                  (BPair.oneValue_trans (rhoOne _ _) (BPair.unit_mul _)))
                (BPair.add_unit BPair.unit)))
            (BPair.add_unit BPair.unit)))
  | _, [_], [], [], h, _ => False.elim h
  | _, [_], [], _ :: _ :: _, h, _ => False.elim h
  | _, [_], _ :: _, _, h, _ => False.elim h
  | _, _ :: _ :: _, [], _, h, _ => False.elim h
  | _, _ :: _ :: _, _ :: _, [], h, _ => False.elim h
  | _, _ :: _ :: _, _ :: _, [_], h, _ => False.elim h
  | p, a0 :: a1 :: as, b0 :: bs, x0 :: x1 :: xs, h, W => by
      have ih := foldBondGo (b0 * x0) (a1 :: as) bs (x1 :: xs) h.2
        (fun k => W (k + 1))
      have hLdec : cStream (x0 :: x1 :: xs)
            (fun k => ground.getAt BPair.unit (a0 :: a1 :: as) k * W k)
          = a0 * W 0 * (x0 * x1)
            + cStream (x1 :: xs)
              (fun k => ground.getAt BPair.unit (a1 :: as) k * W (k + 1)) :=
        cStream_cons _ _ _
      have hD : dStream (x0 :: x1 :: xs)
            (fun k => ground.getAt BPair.unit (b0 :: bs) k * W (k + 1))
          = b0 * W 1 * (x0 * ground.getAt BPair.unit xs 0)
            + dStream (x1 :: xs)
              (fun k => ground.getAt BPair.unit bs k * W (k + 2)) :=
        dStream_cons _ _ _
      have hRho : rhoStream (x0 :: x1 :: xs)
            (wShift (fun t =>
              ground.getAt BPair.unit (b0 :: bs) t * W t))
          = BPair.unit * (x0 * x0)
            + rhoStream (x1 :: xs)
              (fun k => ground.getAt BPair.unit (b0 :: bs) k * W k) :=
        rhoStream_cons _ _ _
      have hRho2 : rhoStream (x1 :: xs)
            (fun k => ground.getAt BPair.unit (b0 :: bs) k * W k)
          = b0 * W 0 * (x1 * x1)
            + rhoStream xs
              (fun k => ground.getAt BPair.unit bs k * W (k + 1)) :=
        rhoStream_cons _ _ _
      have hRp : rhoStream (x1 :: xs)
            (wShift (fun t => ground.getAt BPair.unit bs t * W (t + 1)))
          = BPair.unit * (x1 * x1)
            + rhoStream xs
              (fun k => ground.getAt BPair.unit bs k * W (k + 1)) :=
        rhoStream_cons _ _ _
      have hRpU : (rhoStream (x1 :: xs)
            (wShift (fun t =>
              ground.getAt BPair.unit bs t * W (t + 1)))).oneValue
          (rhoStream xs
            (fun k => ground.getAt BPair.unit bs k * W (k + 1))) :=
        BPair.oneValue_trans (BPair.oneValue_of_eq hRp)
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.unit_mul (x1 * x1))
              (BPair.oneValue_refl _))
            (BPair.unit_add _))
      have hExp : (p + b0 * x1) * (W 0 * x1)
          = W 0 * (p * x1) + b0 * W 0 * (x1 * x1) := by
        rw [BPair.right_distrib, BPair.mul_left_comm p (W 0) x1,
          BPair.mul_mul_mul_comm b0 x1 (W 0) x1]
      have hHead : (a0 * W 0 * (x0 * x1)).oneValue
          (W 0 * (p * x1) + b0 * W 0 * (x1 * x1)) :=
        BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.mul_mul_mul_comm a0 (W 0) x0 x1))
          (BPair.oneValue_trans (BPair.mul_congr_left h.1)
            (BPair.oneValue_of_eq hExp))
      have hSh : W 1 * (b0 * x0 * ground.getAt BPair.unit xs 0)
          = b0 * W 1 * (x0 * ground.getAt BPair.unit xs 0) :=
        (BPair.mul_left_comm (W 1) (b0 * x0)
            (ground.getAt BPair.unit xs 0)).trans
          (BPair.mul_mul_mul_comm b0 (W 1) x0
            (ground.getAt BPair.unit xs 0)).symm
      have hIh : (cStream (x1 :: xs)
            (fun k =>
              ground.getAt BPair.unit (a1 :: as) k * W (k + 1))).oneValue
          (b0 * W 1 * (x0 * ground.getAt BPair.unit xs 0)
            + (dStream (x1 :: xs)
                (fun k => ground.getAt BPair.unit bs k * W (k + 2))
              + rhoStream xs
                (fun k => ground.getAt BPair.unit bs k * W (k + 1)))) :=
        BPair.oneValue_trans ih
          (BPair.add_congr (BPair.oneValue_of_eq hSh)
            (BPair.add_congr (BPair.oneValue_refl _) hRpU))
      rw [hLdec, hD, hRho, hRho2]
      refine BPair.oneValue_trans (BPair.add_congr hHead hIh) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (bondCollect (W 0 * (p * x1))
          (b0 * W 0 * (x1 * x1))
          (b0 * W 1 * (x0 * ground.getAt BPair.unit xs 0))
          (dStream (x1 :: xs)
            (fun k => ground.getAt BPair.unit bs k * W (k + 2)))
          (rhoStream xs
            (fun k => ground.getAt BPair.unit bs k * W (k + 1))))) ?_
      exact BPair.oneValue_symm
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.oneValue_trans
              (BPair.add_congr (BPair.unit_mul (x0 * x0))
                (BPair.oneValue_refl _))
              (BPair.unit_add _))))

/-- The square fold: the recurrence folded against the ground at a
stated weight reads the two bond streams, the second at the raised
weight, against the square stream at the diagonal weight. -/
theorem fold_sq (a b psi : List BPair) (h : recRead a b psi)
    (W : Nat → BPair) :
    (cStream psi (fun k => ground.getAt BPair.unit b k * W k)
      + cStream psi (fun k => ground.getAt BPair.unit b k * W (k + 1))).oneValue
      (rhoStream psi (fun k => ground.getAt BPair.unit a k * W k)) :=
  BPair.oneValue_symm
    (BPair.oneValue_trans (foldSqGo BPair.unit a b psi h W)
      (BPair.oneValue_trans
        (BPair.add_congr (seedUnit W _) (BPair.oneValue_refl _))
        (BPair.unit_add _)))

/-- The bond fold: the recurrence folded against the raised ground
reads the second-bond stream at the raised weight and the
down-shifted square stream against the bond stream at the diagonal
weight. -/
theorem fold_bond (a b psi : List BPair) (h : recRead a b psi)
    (W : Nat → BPair) :
    (dStream psi (fun k => ground.getAt BPair.unit b k * W (k + 1))
      + rhoStream psi
          (wShift (fun t => ground.getAt BPair.unit b t * W t))).oneValue
      (cStream psi (fun k => ground.getAt BPair.unit a k * W k)) :=
  BPair.oneValue_symm
    (BPair.oneValue_trans (foldBondGo BPair.unit a b psi h W)
      (BPair.oneValue_trans
        (BPair.add_congr (seedUnit W _) (BPair.oneValue_refl _))
        (BPair.unit_add _)))

/-- The interior row multiplied through by the ground at the key
against the weight: the second-bond summand and the square summand
read the bond summand at the raised diagonal. -/
private theorem bondTerm (a b psi : List BPair) (h : recRead a b psi)
    (W : Nat → BPair) (k : Nat) :
    (ground.getAt BPair.unit b (k + 1) * W k
        * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi (k + 2))
      + ground.getAt BPair.unit b k * W k
        * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi k)).oneValue
      (ground.getAt BPair.unit a (k + 1) * W k
        * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi (k + 1))) := by
  have eL : ground.getAt BPair.unit a (k + 1) * W k
        * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi (k + 1))
      = ground.getAt BPair.unit a (k + 1) * ground.getAt BPair.unit psi (k + 1)
        * (W k * ground.getAt BPair.unit psi k) := by
    rw [BPair.mul_comm (ground.getAt BPair.unit psi k)
        (ground.getAt BPair.unit psi (k + 1)),
      BPair.mul_mul_mul_comm (ground.getAt BPair.unit a (k + 1)) (W k)
        (ground.getAt BPair.unit psi (k + 1)) (ground.getAt BPair.unit psi k)]
  have eR : (ground.getAt BPair.unit b k * ground.getAt BPair.unit psi k
        + ground.getAt BPair.unit b (k + 1)
          * ground.getAt BPair.unit psi (k + 2))
        * (W k * ground.getAt BPair.unit psi k)
      = ground.getAt BPair.unit b (k + 1) * W k
          * (ground.getAt BPair.unit psi k
            * ground.getAt BPair.unit psi (k + 2))
        + ground.getAt BPair.unit b k * W k
          * (ground.getAt BPair.unit psi k
            * ground.getAt BPair.unit psi k) := by
    rw [BPair.right_distrib,
      BPair.mul_mul_mul_comm (ground.getAt BPair.unit b k)
        (ground.getAt BPair.unit psi k) (W k) (ground.getAt BPair.unit psi k),
      BPair.mul_mul_mul_comm (ground.getAt BPair.unit b (k + 1))
        (ground.getAt BPair.unit psi (k + 2)) (W k)
        (ground.getAt BPair.unit psi k),
      BPair.mul_comm (ground.getAt BPair.unit psi (k + 2))
        (ground.getAt BPair.unit psi k),
      BPair.add_comm (ground.getAt BPair.unit b k * W k
          * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
        (ground.getAt BPair.unit b (k + 1) * W k
          * (ground.getAt BPair.unit psi k
            * ground.getAt BPair.unit psi (k + 2)))]
  exact BPair.oneValue_symm
    (BPair.oneValue_trans (BPair.oneValue_of_eq eL)
      (BPair.oneValue_trans (BPair.mul_congr_left (rowAt a b psi h k))
        (BPair.oneValue_of_eq eR)))

/-- The second-bond reduction: one further fold of the recurrence
sends the second-bond stream and the square stream at the bond weight
onto the bond stream at the raised diagonal, so the family closes on
the square and bond streams alone. -/
theorem bond2_reduce (a b psi : List BPair) (h : recRead a b psi)
    (W : Nat → BPair) :
    (dStream psi (fun k => ground.getAt BPair.unit b (k + 1) * W k)
      + rhoStream psi (fun k => ground.getAt BPair.unit b k * W k)).oneValue
      (cStream psi (fun k => ground.getAt BPair.unit a (k + 1) * W k)) := by
  have hsplit : (dStream psi (fun k => ground.getAt BPair.unit b (k + 1) * W k)
      + rhoStream psi (fun k => ground.getAt BPair.unit b k * W k)).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun k => ground.getAt BPair.unit b (k + 1) * W k
            * (ground.getAt BPair.unit psi k
              * ground.getAt BPair.unit psi (k + 2))
          + ground.getAt BPair.unit b k * W k
            * (ground.getAt BPair.unit psi k
              * ground.getAt BPair.unit psi k))
        (List.range psi.length)) :=
    BPair.oneValue_symm (ground.foldB_add _ _ (List.range psi.length))
  exact BPair.oneValue_trans hsplit
    (ground.foldB_congr_members _ _ (List.range psi.length)
      (fun k _ => bondTerm a b psi h W k))

/-- A commutator's ground read is of equal members: two symmetric
data's composed actions against a vector pair the vector at one
value in either order, each pairing walked across the symmetry —
the folds rather than commutators close the system. -/
theorem commGround {n : Nat} (M N : elim.Mat)
    (hM : elim.sqAt M n) (hN : elim.sqAt N n)
    (hsM : elim.matOneValue (elim.transposeM M) M)
    (hsN : elim.matOneValue (elim.transposeM N) N)
    (psi : List BPair) (hpsi : psi.length = n) :
    (elim.dotP psi (elim.matVec M (elim.matVec N psi))).oneValue
      (elim.dotP psi (elim.matVec N (elim.matVec M psi))) := by
  have hNl : (elim.matVec N psi).length = n :=
    (elim.matVec_length N psi).trans (elim.sqAt_len hN)
  have hMl : (elim.matVec M psi).length = n :=
    (elim.matVec_length M psi).trans (elim.sqAt_len hM)
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (elim.dotP_matVec_sym M hM hsM psi (elim.matVec N psi) hpsi hNl)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (elim.dotP_comm (elim.matVec M psi)
      (elim.matVec N psi))) ?_
  exact elim.dotP_matVec_sym N hN hsN psi (elim.matVec M psi) hpsi hMl

/-- The square stream at the monomial weight: the ground's squares
against the key's own power, one moment per height. -/
def mrho (psi : List BPair) (j : Nat) : BPair :=
  rhoStream psi (fun k => ground.bpow (BPair.ofNat k) j)

/-- The bond stream at the monomial weight: the consecutive products
against the key's power. -/
def mc (psi : List BPair) (j : Nat) : BPair :=
  cStream psi (fun k => ground.bpow (BPair.ofNat k) j)

/-- The second-bond stream at the monomial weight. -/
def md (psi : List BPair) (j : Nat) : BPair :=
  dStream psi (fun k => ground.bpow (BPair.ofNat k) j)

/-- The head ground's square, the boundary square the vacant power's
moment joins. -/
def bSq (psi : List BPair) : BPair :=
  ground.getAt BPair.unit psi 0 * ground.getAt BPair.unit psi 0

/-- The far edge's weighted read: the top key's power against the top
ground's square. -/
def edgeAt (psi : List BPair) (t : Nat) : BPair :=
  ground.bpow (BPair.ofNat (psi.length - 1)) t
    * (ground.getAt BPair.unit psi (psi.length - 1)
      * ground.getAt BPair.unit psi (psi.length - 1))

/-- The quadratic profile's walk: per depth the diagonal entry reads the
profile at the key, the keys ascending from the walk's seed. -/
def profWalk (p2 p1 p0 : BPair) : Nat → List BPair → Prop
  | _, [] => True
  | k, x :: t =>
      x.oneValue (p2 * BPair.ofNat (k * k) + (p1 * BPair.ofNat k + p0))
      ∧ profWalk p2 p1 p0 (k + 1) t

/-- The profile walk's decision, the entry read's fold. -/
def decProfWalk (p2 p1 p0 : BPair) : ∀ (k : Nat) (l : List BPair),
    Decidable (profWalk p2 p1 p0 k l)
  | _, [] => isTrue trivial
  | k, _ :: t =>
      @instDecidableAnd _ _ inferInstance (decProfWalk p2 p1 p0 (k + 1) t)

instance (p2 p1 p0 : BPair) (k : Nat) (l : List BPair) :
    Decidable (profWalk p2 p1 p0 k l) := decProfWalk p2 p1 p0 k l

/-- The diagonal at a quadratic profile: the walk from the head key. -/
def diagProf (a : List BPair) (p2 p1 p0 : BPair) : Prop :=
  profWalk p2 p1 p0 0 a

instance (a : List BPair) (p2 p1 p0 : BPair) :
    Decidable (diagProf a p2 p1 p0) := decProfWalk p2 p1 p0 0 a

/-- The bond list at one datum: every entry reads that datum. -/
def constBond (b : List BPair) (β : BPair) : Prop :=
  poly.oneValue b (List.replicate b.length β)

instance (b : List BPair) (β : BPair) : Decidable (constBond b β) :=
  poly.decOneValue _ _

/-- The profile walk's entry read at every key below its count, the
walk's seed key joined to the key. -/
private theorem profAtGo (p2 p1 p0 : BPair) : ∀ (m : Nat) (l : List BPair),
    profWalk p2 p1 p0 m l → ∀ k : Nat, k < l.length →
    (ground.getAt BPair.unit l k).oneValue
      (p2 * BPair.ofNat ((m + k) * (m + k)) + (p1 * BPair.ofNat (m + k) + p0))
  | _, [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | _, _ :: _, h, 0, _ => h.1
  | m, _ :: t, h, k + 1, hk => by
      have ih := profAtGo p2 p1 p0 (m + 1) t h.2 k (Nat.lt_of_succ_lt_succ hk)
      have hEq : m + 1 + k = m + (k + 1) := Nat.succ_add m k
      rw [hEq] at ih
      exact ih

/-- The profiled diagonal at every key below its count: the entry reads
the profile's quadratic at that key. -/
theorem prof_at (a : List BPair) (p2 p1 p0 : BPair)
    (h : diagProf a p2 p1 p0) (k : Nat) (hk : k < a.length) :
    (ground.getAt BPair.unit a k).oneValue
      (p2 * BPair.ofNat (k * k) + (p1 * BPair.ofNat k + p0)) := by
  have ih := profAtGo p2 p1 p0 0 a h k hk
  have hEq : 0 + k = k := Nat.zero_add k
  rw [hEq] at ih
  exact ih

/-- The constant bond at every key below its count: the entry reads the
stated datum. -/
theorem bond_at (b : List BPair) (β : BPair) (h : constBond b β)
    (k : Nat) (hk : k < b.length) :
    (ground.getAt BPair.unit b k).oneValue β :=
  BPair.oneValue_trans (poly.oneValue_getAt k h)
    (BPair.oneValue_of_eq
      (ground.getAt_replicate BPair.unit β b.length k hk))
/-- The raised key's power expands over the Pascal counts against the
key's own powers. -/
private theorem powUpOne (k j : Nat) :
    (ground.bpow (BPair.ofNat (k + 1)) j).oneValue
      (ground.bsum (fun t => BPair.ofNat (ground.pasc j t)
        * ground.bpow (BPair.ofNat k) t) (List.range (j + 1))) :=
  BPair.oneValue_trans (ground.bpow_congr (BPair.ofNat_succ k) j)
    (BPair.oneValue_trans (ground.bpow_binom (BPair.ofNat k) (BPair.ofNat 1) j)
      (ground.foldB_congr_members _ _ (List.range (j + 1)) (fun t _ =>
        BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _)
              (ground.bpow_one (j - t)))
            (BPair.mul_one_read _)))))

/-- The twice-raised key's power expands over the Pascal counts, the
doubled base's complementary powers joining each count. -/
private theorem powUpTwo (k j : Nat) :
    (ground.bpow (BPair.ofNat (k + 2)) j).oneValue
      (ground.bsum (fun t => BPair.ofNat (ground.pasc j t)
          * ground.bpow (BPair.ofNat 2) (j - t)
          * ground.bpow (BPair.ofNat k) t) (List.range (j + 1))) :=
  BPair.oneValue_trans (ground.bpow_congr (BPair.ofNat_add k 2) j)
    (BPair.oneValue_trans (ground.bpow_binom (BPair.ofNat k) (BPair.ofNat 2) j)
      (ground.foldB_congr_members _ _ (List.range (j + 1)) (fun t _ =>
        BPair.oneValue_of_eq
          ((congrArg (fun z => BPair.ofNat (ground.pasc j t) * z)
              (BPair.mul_comm (ground.bpow (BPair.ofNat k) t)
                (ground.bpow (BPair.ofNat 2) (j - t)))).trans
            (BPair.mul_assoc (BPair.ofNat (ground.pasc j t))
              (ground.bpow (BPair.ofNat 2) (j - t))
              (ground.bpow (BPair.ofNat k) t)).symm))))

/-- The fold over a key range of an inner fold against a per-key datum
exchanges its two ranges, the inner weight moving out of the inner
fold. -/
private theorem weightSwap (R : Nat → BPair) (A : Nat → Nat → BPair)
    (C : Nat → BPair) (n m : Nat) :
    (ground.bsum (fun k =>
        ground.bsum (fun t => C t * A k t) (List.range m) * R k)
      (List.range n)).oneValue
      (ground.bsum (fun t =>
        C t * ground.bsum (fun k => A k t * R k) (List.range n))
        (List.range m)) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members
      (fun k => ground.bsum (fun t => C t * A k t) (List.range m) * R k)
      (fun k => ground.bsum (fun t => C t * (A k t * R k)) (List.range m))
      (List.range n) (fun k _ => ?_)) ?_
  · refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm _ (R k))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (ground.foldB_mul_left (R k) (fun t => C t * A k t) (List.range m))) ?_
    exact ground.foldB_congr_members _ _ (List.range m) (fun t _ =>
      BPair.oneValue_of_eq
        ((BPair.mul_left_comm (R k) (C t) (A k t)).trans
          (congrArg (fun z => C t * z) (BPair.mul_comm (R k) (A k t)))))
  · refine BPair.oneValue_trans
      (ground.bsum_swap (fun k t => C t * (A k t * R k))
        (List.range n) (List.range m)) ?_
    exact ground.foldB_congr_members _ _ (List.range m) (fun t _ =>
      ground.foldB_mul_left (C t) (fun k => A k t * R k) (List.range n))

/-- The up-shifted monomial in the bond stream expands over the Pascal
counts: the stream at the raised key's power reads the counts against
the streams at the powers below. -/
theorem cShift1 (psi : List BPair) (G : Nat → BPair) (j : Nat) :
    (cStream psi (fun k => G k * ground.bpow (BPair.ofNat (k + 1)) j)).oneValue
      (ground.bsum (fun t => BPair.ofNat (ground.pasc j t)
        * cStream psi (fun k => G k * ground.bpow (BPair.ofNat k) t))
        (List.range (j + 1))) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members
      (fun k => G k * ground.bpow (BPair.ofNat (k + 1)) j
        * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi (k + 1)))
      (fun k => ground.bsum (fun t => BPair.ofNat (ground.pasc j t)
            * ground.bpow (BPair.ofNat k) t) (List.range (j + 1))
        * (G k * (ground.getAt BPair.unit psi k
            * ground.getAt BPair.unit psi (k + 1))))
      (List.range psi.length) (fun k _ => ?_)) ?_
  · exact BPair.oneValue_trans
      (BPair.oneValue_of_eq
        ((BPair.mul_assoc (G k) _ _).trans (BPair.mul_left_comm (G k) _ _)))
      (BPair.mul_congr_left (powUpOne k j))
  · refine BPair.oneValue_trans
      (weightSwap (fun k => G k * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi (k + 1)))
        (fun k t => ground.bpow (BPair.ofNat k) t)
        (fun t => BPair.ofNat (ground.pasc j t)) psi.length (j + 1)) ?_
    exact ground.foldB_congr_members _ _ (List.range (j + 1)) (fun t _ =>
      BPair.mul_congr (BPair.oneValue_refl _)
        (ground.foldB_congr_members _ _ (List.range psi.length) (fun k _ =>
          BPair.oneValue_of_eq
            ((BPair.mul_left_comm _ (G k) _).trans
              (BPair.mul_assoc (G k) _ _).symm))))

/-- The two-step up-shift in the second-bond stream expands over the
Pascal counts, the doubled base's complementary power joining each
count. -/
theorem dShift2 (psi : List BPair) (G : Nat → BPair) (j : Nat) :
    (dStream psi (fun k => G k * ground.bpow (BPair.ofNat (k + 2)) j)).oneValue
      (ground.bsum (fun t => BPair.ofNat (ground.pasc j t)
        * (ground.bpow (BPair.ofNat 2) (j - t)
          * dStream psi (fun k => G k * ground.bpow (BPair.ofNat k) t)))
        (List.range (j + 1))) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members
      (fun k => G k * ground.bpow (BPair.ofNat (k + 2)) j
        * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi (k + 2)))
      (fun k => ground.bsum (fun t => BPair.ofNat (ground.pasc j t)
            * ground.bpow (BPair.ofNat 2) (j - t)
            * ground.bpow (BPair.ofNat k) t) (List.range (j + 1))
        * (G k * (ground.getAt BPair.unit psi k
            * ground.getAt BPair.unit psi (k + 2))))
      (List.range psi.length) (fun k _ => ?_)) ?_
  · exact BPair.oneValue_trans
      (BPair.oneValue_of_eq
        ((BPair.mul_assoc (G k) _ _).trans (BPair.mul_left_comm (G k) _ _)))
      (BPair.mul_congr_left (powUpTwo k j))
  · refine BPair.oneValue_trans
      (weightSwap (fun k => G k * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi (k + 2)))
        (fun k t => ground.bpow (BPair.ofNat k) t)
        (fun t => BPair.ofNat (ground.pasc j t)
          * ground.bpow (BPair.ofNat 2) (j - t)) psi.length (j + 1)) ?_
    exact ground.foldB_congr_members _ _ (List.range (j + 1)) (fun t _ =>
      BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.mul_congr (BPair.oneValue_refl _)
            (ground.foldB_congr_members _ _ (List.range psi.length)
              (fun k _ => BPair.oneValue_of_eq
                ((BPair.mul_left_comm _ (G k) _).trans
                  (BPair.mul_assoc (G k) _ _).symm))))))
/-- A constant bond withdraws from a stream over a stated key range at
its own datum, the keys beyond the bond's count vacant on both sides. -/
private theorem bondStream (b : List BPair) (β : BPair) (hb : constBond b β)
    (V Q : Nat → BPair) (i : Nat → Nat) (n : Nat)
    (hoff : ∀ k, k < n → b.length ≤ i k → (Q k).oneValue BPair.unit) :
    (ground.bsum (fun k => ground.getAt BPair.unit b (i k) * V k * Q k)
      (List.range n)).oneValue
      (β * ground.bsum (fun k => V k * Q k) (List.range n)) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members
      (fun k => ground.getAt BPair.unit b (i k) * V k * Q k)
      (fun k => β * (V k * Q k)) (List.range n) (fun k hk => ?_))
    (ground.foldB_mul_left β (fun k => V k * Q k) (List.range n))
  refine dite (i k < b.length) (fun hi => ?_) (fun hi => ?_)
  · exact BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.mul_congr_left (bond_at b β hb (i k) hi)))
      (BPair.oneValue_of_eq (BPair.mul_assoc β (V k) (Q k)))
  · have hge : b.length ≤ i k := Nat.le_of_not_lt hi
    have hQ := hoff k (ground.ltOfMem hk) hge
    exact BPair.oneValue_trans
      (BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.mul_congr_left
          (BPair.oneValue_of_eq
            (ground.getAt_over BPair.unit b (i k) hge))))
        (BPair.oneValue_trans (BPair.mul_congr_left (BPair.unit_mul (V k)))
          (BPair.unit_mul (Q k))))
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl β)
            (BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl (V k)) hQ)
              (BPair.mul_unit (V k))))
          (BPair.mul_unit β)))

/-- A constant bond withdraws from the bond stream at its own datum. -/
theorem cBond (b psi : List BPair) (β : BPair) (hb : constBond b β)
    (hlen : b.length + 1 = psi.length) (V : Nat → BPair) :
    (cStream psi (fun k => ground.getAt BPair.unit b k * V k)).oneValue
      (β * cStream psi V) :=
  bondStream b β hb V
    (fun k => ground.getAt BPair.unit psi k
      * ground.getAt BPair.unit psi (k + 1))
    (fun k => k) psi.length
    (fun k _ hge =>
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_of_eq (ground.getAt_over BPair.unit psi (k + 1)
            (Nat.le_trans (Nat.le_of_eq hlen.symm) (Nat.succ_le_succ hge)))))
        (BPair.mul_unit _))

/-- A constant bond at the raised key withdraws from the second-bond
stream at its own datum. -/
theorem dBondUp (b psi : List BPair) (β : BPair) (hb : constBond b β)
    (hlen : b.length + 1 = psi.length) (V : Nat → BPair) :
    (dStream psi (fun k => ground.getAt BPair.unit b (k + 1) * V k)).oneValue
      (β * dStream psi V) :=
  bondStream b β hb V
    (fun k => ground.getAt BPair.unit psi k
      * ground.getAt BPair.unit psi (k + 2))
    (fun k => k + 1) psi.length
    (fun k _ hge =>
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_of_eq (ground.getAt_over BPair.unit psi (k + 2)
            (Nat.le_trans (Nat.le_of_eq hlen.symm) (Nat.succ_le_succ hge)))))
        (BPair.mul_unit _))

/-- A constant bond withdraws from the square stream at its own datum,
the far edge's summand rejoining at the bond's one vacant key. -/
theorem rhoBond (b psi : List BPair) (β : BPair) (hb : constBond b β)
    (hlen : b.length + 1 = psi.length) (V : Nat → BPair) :
    (rhoStream psi (fun k => ground.getAt BPair.unit b k * V k)
      + β * (V (psi.length - 1)
        * (ground.getAt BPair.unit psi (psi.length - 1)
          * ground.getAt BPair.unit psi (psi.length - 1)))).oneValue
      (β * rhoStream psi V) := by
  show (ground.bsum (fun k => ground.getAt BPair.unit b k * V k
        * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
      (List.range psi.length)
    + β * (V (psi.length - 1)
      * (ground.getAt BPair.unit psi (psi.length - 1)
        * ground.getAt BPair.unit psi (psi.length - 1)))).oneValue
    (β * ground.bsum (fun k => V k
      * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
      (List.range psi.length))
  rw [← hlen]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (ground.famFold_range_ext
        (fun k => ground.getAt BPair.unit b k * V k
          * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
        b.length
        (fun j hj => BPair.oneValue_trans
          (BPair.mul_congr_left (BPair.mul_congr_left
            (BPair.oneValue_of_eq (ground.getAt_over BPair.unit b j hj))))
          (BPair.oneValue_trans
            (BPair.mul_congr_left (BPair.unit_mul (V j)))
            (BPair.unit_mul _)))
        1)
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (bondStream b β hb V
        (fun k => ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi k)
        (fun k => k) b.length
        (fun k hk hge => absurd (Nat.lt_of_lt_of_le hk hge) (Nat.lt_irrefl k)))
      (BPair.oneValue_refl _)) ?_
  exact BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.left_distrib β _ _).symm)
    (BPair.mul_congr (BPair.oneValue_refl β)
      (BPair.oneValue_symm
        (ground.foldB_range_snoc
          (fun k => V k
            * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
          b.length)))

/-- The down-shift of a bond-weighted family: its square stream reads the
bond's datum against the square stream at the family's own down-shift. -/
theorem wCollapse (b psi : List BPair) (β : BPair) (hb : constBond b β)
    (hlen : b.length + 1 = psi.length) (V : Nat → BPair) :
    (rhoStream psi
      (wShift (fun t => ground.getAt BPair.unit b t * V t))).oneValue
      (β * rhoStream psi (wShift V)) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members
      (fun m => wShift (fun t => ground.getAt BPair.unit b t * V t) m
        * (ground.getAt BPair.unit psi m * ground.getAt BPair.unit psi m))
      (fun m => β * (wShift V m
        * (ground.getAt BPair.unit psi m * ground.getAt BPair.unit psi m)))
      (List.range psi.length) (fun m hm => ?_))
    (ground.foldB_mul_left β
      (fun m => wShift V m
        * (ground.getAt BPair.unit psi m * ground.getAt BPair.unit psi m))
      (List.range psi.length))
  cases m with
  | zero =>
      exact BPair.oneValue_trans (BPair.unit_mul _)
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl β) (BPair.unit_mul _))
            (BPair.mul_unit β)))
  | succ t =>
      have hlt : t < b.length := by
        have hin : t + 1 < psi.length := ground.ltOfMem hm
        rw [← hlen] at hin
        exact Nat.lt_of_succ_lt_succ hin
      exact BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.mul_congr_left (bond_at b β hb t hlt)))
        (BPair.oneValue_of_eq (BPair.mul_assoc β (V t) _))
/-- The down-shift of the up-shifted monomial at a raised power reads the
moment itself, the head key's vacancy meeting the vacant base's power. -/
theorem wMono_succ (psi : List BPair) (j : Nat) :
    (rhoStream psi
      (wShift (fun t => ground.bpow (BPair.ofNat (t + 1)) (j + 1)))).oneValue
      (mrho psi (j + 1)) := by
  refine ground.foldB_congr_members
    (fun m => wShift (fun t => ground.bpow (BPair.ofNat (t + 1)) (j + 1)) m
      * (ground.getAt BPair.unit psi m * ground.getAt BPair.unit psi m))
    (fun m => ground.bpow (BPair.ofNat m) (j + 1)
      * (ground.getAt BPair.unit psi m * ground.getAt BPair.unit psi m))
    (List.range psi.length) (fun m _ => ?_)
  cases m with
  | zero =>
      exact BPair.oneValue_trans (BPair.unit_mul _)
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.mul_congr_left
              (BPair.oneValue_trans (BPair.norm_oneValue _)
                (BPair.unit_mul _)))
            (BPair.unit_mul _)))
  | succ t => exact BPair.oneValue_refl _

/-- At the vacant power the down-shifted monomial's stream joined to the
boundary square reads the moment. -/
theorem wMono_zero (psi : List BPair) :
    (rhoStream psi (wShift (fun t => ground.bpow (BPair.ofNat (t + 1)) 0))
      + bSq psi).oneValue (mrho psi 0) := by
  match psi with
  | [] =>
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.unit_mul BPair.unit))
        (BPair.add_unit _)
  | x :: xs =>
      have hL : rhoStream (x :: xs)
            (wShift (fun t => ground.bpow (BPair.ofNat (t + 1)) 0))
          = BPair.unit * (x * x)
            + rhoStream xs (fun k => ground.bpow (BPair.ofNat (k + 1)) 0) :=
        rhoStream_cons _ _ _
      have hR : mrho (x :: xs) 0
          = ground.bpow (BPair.ofNat 0) 0 * (x * x)
            + rhoStream xs (fun k => ground.bpow (BPair.ofNat (k + 1)) 0) :=
        rhoStream_cons _ _ _
      rw [hL, hR]
      exact BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.unit_mul (x * x)) (BPair.oneValue_refl _))
            (BPair.unit_add _))
          (BPair.oneValue_refl (x * x)))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.add_comm _ (x * x)))
          (BPair.add_congr
            (BPair.oneValue_symm
              (BPair.oneValue_trans
                (BPair.oneValue_of_eq (BPair.mul_comm _ (x * x)))
                (BPair.mul_one_read (x * x))))
            (BPair.oneValue_refl _)))
/-- The key's square against the key's power reads the power twice
raised. -/
private theorem powSquare (m j : Nat) :
    (BPair.ofNat (m * m) * ground.bpow (BPair.ofNat m) j).oneValue
      (ground.bpow (BPair.ofNat m) (j + 2)) :=
  BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_mul m m))
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm
            (ground.bpow_succ_read (BPair.ofNat m) j)))
        (BPair.oneValue_symm
          (ground.bpow_succ_read (BPair.ofNat m) (j + 1)))))

/-- A three-summand head distributes through two further factors. -/
private theorem sumThreeMul (X Y Z B P : BPair) :
    (X + (Y + Z)) * B * P = X * B * P + (Y * B * P + Z * B * P) := by
  rw [BPair.right_distrib X (Y + Z) B, BPair.right_distrib Y Z B,
    BPair.right_distrib (X * B) (Y * B + Z * B) P,
    BPair.right_distrib (Y * B) (Z * B) P]

/-- The profiled summand expands onto the three neighboring powers at the
profile's constants. -/
private theorem profTerm (p2 p1 p0 : BPair) (m j : Nat) (P : BPair) :
    ((p2 * BPair.ofNat (m * m) + (p1 * BPair.ofNat m + p0))
        * ground.bpow (BPair.ofNat m) j * P).oneValue
      (p2 * (ground.bpow (BPair.ofNat m) (j + 2) * P)
        + (p1 * (ground.bpow (BPair.ofNat m) (j + 1) * P)
          + p0 * (ground.bpow (BPair.ofNat m) j * P))) :=
  BPair.oneValue_trans (BPair.oneValue_of_eq (sumThreeMul _ _ _ _ _))
    (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.mul_assoc p2 _ _))
            (BPair.mul_congr (BPair.oneValue_refl p2) (powSquare m j))))
        (BPair.oneValue_of_eq (BPair.mul_assoc p2 _ P)))
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.mul_congr_left
            (BPair.oneValue_trans
              (BPair.oneValue_of_eq (BPair.mul_assoc p1 _ _))
              (BPair.mul_congr (BPair.oneValue_refl p1)
                (BPair.oneValue_symm
                  (ground.bpow_succ_read (BPair.ofNat m) j)))))
          (BPair.oneValue_of_eq (BPair.mul_assoc p1 _ P)))
        (BPair.oneValue_of_eq (BPair.mul_assoc p0 _ P))))

/-- A stream whose summands read the three-power expansion splits into
the three moments at their own constants. -/
private theorem profSplit (q2 q1 q0 : BPair) (P : Nat → BPair) (j n : Nat)
    (F : Nat → BPair)
    (hpt : ∀ m, m < n → (F m).oneValue
      (q2 * (ground.bpow (BPair.ofNat m) (j + 2) * P m)
        + (q1 * (ground.bpow (BPair.ofNat m) (j + 1) * P m)
          + q0 * (ground.bpow (BPair.ofNat m) j * P m)))) :
    (ground.bsum F (List.range n)).oneValue
      (q2 * ground.bsum (fun m => ground.bpow (BPair.ofNat m) (j + 2) * P m)
          (List.range n)
        + (q1 * ground.bsum
              (fun m => ground.bpow (BPair.ofNat m) (j + 1) * P m)
              (List.range n)
          + q0 * ground.bsum (fun m => ground.bpow (BPair.ofNat m) j * P m)
              (List.range n))) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members F
      (fun m => q2 * (ground.bpow (BPair.ofNat m) (j + 2) * P m)
        + (q1 * (ground.bpow (BPair.ofNat m) (j + 1) * P m)
          + q0 * (ground.bpow (BPair.ofNat m) j * P m)))
      (List.range n) (fun m hm => hpt m (ground.ltOfMem hm))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_add
      (fun m => q2 * (ground.bpow (BPair.ofNat m) (j + 2) * P m))
      (fun m => q1 * (ground.bpow (BPair.ofNat m) (j + 1) * P m)
        + q0 * (ground.bpow (BPair.ofNat m) j * P m))
      (List.range n)) ?_
  exact BPair.add_congr
    (ground.foldB_mul_left q2
      (fun m => ground.bpow (BPair.ofNat m) (j + 2) * P m) (List.range n))
    (BPair.oneValue_trans
      (ground.foldB_add
        (fun m => q1 * (ground.bpow (BPair.ofNat m) (j + 1) * P m))
        (fun m => q0 * (ground.bpow (BPair.ofNat m) j * P m))
        (List.range n))
      (BPair.add_congr
        (ground.foldB_mul_left q1
          (fun m => ground.bpow (BPair.ofNat m) (j + 1) * P m)
          (List.range n))
        (ground.foldB_mul_left q0
          (fun m => ground.bpow (BPair.ofNat m) j * P m) (List.range n))))

/-- The square stream against a profiled diagonal expands onto three
neighboring moments at the profile's constants. -/
theorem profRho (a psi : List BPair) (p2 p1 p0 : BPair)
    (h : diagProf a p2 p1 p0) (hlen : psi.length = a.length) (j : Nat) :
    (rhoStream psi
      (fun k => ground.getAt BPair.unit a k
        * ground.bpow (BPair.ofNat k) j)).oneValue
      (p2 * mrho psi (j + 2) + (p1 * mrho psi (j + 1) + p0 * mrho psi j)) :=
  profSplit p2 p1 p0
    (fun m => ground.getAt BPair.unit psi m * ground.getAt BPair.unit psi m)
    j psi.length
    (fun m => ground.getAt BPair.unit a m * ground.bpow (BPair.ofNat m) j
      * (ground.getAt BPair.unit psi m * ground.getAt BPair.unit psi m))
    (fun m hm =>
      BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.mul_congr_left
          (prof_at a p2 p1 p0 h m (by rw [← hlen]; exact hm))))
        (profTerm p2 p1 p0 m j _))

/-- The bond stream against a profiled diagonal expands onto three
neighboring bond moments at the profile's constants. -/
theorem profC (a psi : List BPair) (p2 p1 p0 : BPair)
    (h : diagProf a p2 p1 p0) (hlen : psi.length = a.length) (j : Nat) :
    (cStream psi
      (fun k => ground.getAt BPair.unit a k
        * ground.bpow (BPair.ofNat k) j)).oneValue
      (p2 * mc psi (j + 2) + (p1 * mc psi (j + 1) + p0 * mc psi j)) :=
  profSplit p2 p1 p0
    (fun m => ground.getAt BPair.unit psi m
      * ground.getAt BPair.unit psi (m + 1))
    j psi.length
    (fun m => ground.getAt BPair.unit a m * ground.bpow (BPair.ofNat m) j
      * (ground.getAt BPair.unit psi m * ground.getAt BPair.unit psi (m + 1)))
    (fun m hm =>
      BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.mul_congr_left
          (prof_at a p2 p1 p0 h m (by rw [← hlen]; exact hm))))
        (profTerm p2 p1 p0 m j _))

/-- The shifted profile's middle constant distributes over the key. -/
private theorem upCoeff (p2 p1 c : BPair) :
    (p2 + p2 + p1) * c = p2 * c + p2 * c + p1 * c := by
  rw [BPair.right_distrib (p2 + p2) p1 c, BPair.right_distrib p2 p2 c]

/-- The seven-summand regrouping the shifted profile's collection takes. -/
private theorem upRegroup (A B D E F G : BPair) :
    A + (B + (B + D)) + (E + F + G)
      = A + (B + B + E + (D + F + G)) := by
  rw [BPair.add_assoc A (B + (B + D)) (E + F + G),
    BPair.add_assoc B (B + D) (E + F + G),
    BPair.add_assoc B D (E + F + G),
    BPair.add_assoc E F G,
    BPair.add_assoc (B + B) E (D + F + G),
    BPair.add_assoc B B (E + (D + F + G)),
    BPair.add_assoc D F G,
    BPair.add_left_comm D E (F + G)]

/-- The shifted profile's head distributes over its summands. -/
private theorem upExpand (p2 p1 p0 c cc u : BPair) :
    p2 * (cc + (c + (c + u))) + (p1 * (c + u) + p0)
      = p2 * cc + (p2 * c + (p2 * c + p2 * u)) + (p1 * c + p1 * u + p0) := by
  rw [BPair.left_distrib p2 cc (c + (c + u)), BPair.left_distrib p2 c (c + u),
    BPair.left_distrib p2 c u, BPair.left_distrib p1 c u]

/-- The shifted profile's summands collect at the shifted constants. -/
private theorem upCollect (p2 p1 p0 c cc : BPair) :
    p2 * cc + (p2 * c + (p2 * c + p2)) + (p1 * c + p1 + p0)
      = p2 * cc + ((p2 + p2 + p1) * c + (p2 + p1 + p0)) := by
  rw [upCoeff p2 p1 c]
  exact upRegroup (p2 * cc) (p2 * c) p2 (p1 * c) p1 p0

/-- The quadratic profile at the raised key is the profile at the key
with the constants shifted: the squared constant joins twice at the
linear place and once at the constant place. -/
private theorem quadShift (p2 p1 p0 : BPair) (k : Nat) :
    (p2 * BPair.ofNat ((k + 1) * (k + 1))
        + (p1 * BPair.ofNat (k + 1) + p0)).oneValue
      (p2 * BPair.ofNat (k * k)
        + ((p2 + p2 + p1) * BPair.ofNat k + (p2 + p1 + p0))) := by
  have h1 : (k + 1) * (k + 1) = k * (k + 1) + (k + 1) := Nat.succ_mul k (k + 1)
  have h2 : k * (k + 1) = k * k + k := Nat.mul_succ k k
  have hnat : (k + 1) * (k + 1) = k * k + (k + (k + 1)) := by
    rw [h1, h2, Nat.add_assoc (k * k) k (k + 1)]
  have hofn : (BPair.ofNat ((k + 1) * (k + 1))).oneValue
      (BPair.ofNat (k * k)
        + (BPair.ofNat k + (BPair.ofNat k + BPair.ofNat 1))) := by
    rw [hnat]
    exact BPair.oneValue_trans (BPair.ofNat_add (k * k) (k + (k + 1)))
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.ofNat_add k (k + 1))
          (BPair.add_congr (BPair.oneValue_refl _) (BPair.ofNat_succ k))))
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl p2) hofn)
      (BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl p1)
        (BPair.ofNat_succ k)) (BPair.oneValue_refl p0))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (upExpand p2 p1 p0 (BPair.ofNat k)
      (BPair.ofNat (k * k)) (BPair.ofNat 1))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.mul_ofNat_one p2))))
      (BPair.add_congr
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.mul_ofNat_one p1))
        (BPair.oneValue_refl p0))) ?_
  exact BPair.oneValue_of_eq
    (upCollect p2 p1 p0 (BPair.ofNat k) (BPair.ofNat (k * k)))

/-- The bond stream against the profiled diagonal at the raised key
expands onto three neighboring bond moments at the shifted constants,
the top key's pair vacant. -/
theorem profCUp (a psi : List BPair) (p2 p1 p0 : BPair)
    (h : diagProf a p2 p1 p0) (hlen : psi.length = a.length) (t : Nat) :
    (cStream psi
      (fun k => ground.getAt BPair.unit a (k + 1)
        * ground.bpow (BPair.ofNat k) t)).oneValue
      (p2 * mc psi (t + 2)
        + ((p2 + p2 + p1) * mc psi (t + 1)
          + (p2 + p1 + p0) * mc psi t)) :=
  profSplit p2 (p2 + p2 + p1) (p2 + p1 + p0)
    (fun m => ground.getAt BPair.unit psi m
      * ground.getAt BPair.unit psi (m + 1))
    t psi.length
    (fun m => ground.getAt BPair.unit a (m + 1)
      * ground.bpow (BPair.ofNat m) t
      * (ground.getAt BPair.unit psi m * ground.getAt BPair.unit psi (m + 1)))
    (fun m _ => by
      refine dite (m + 1 < a.length) (fun hup => ?_) (fun hup => ?_)
      · exact BPair.oneValue_trans
          (BPair.mul_congr_left (BPair.mul_congr_left
            (BPair.oneValue_trans (prof_at a p2 p1 p0 h (m + 1) hup)
              (quadShift p2 p1 p0 m))))
          (profTerm p2 (p2 + p2 + p1) (p2 + p1 + p0) m t _)
      · have hP : (ground.getAt BPair.unit psi m
            * ground.getAt BPair.unit psi (m + 1)).oneValue BPair.unit :=
          BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_of_eq
                (ground.getAt_over BPair.unit psi (m + 1)
                  (Nat.le_trans (Nat.le_of_eq hlen)
                    (Nat.le_of_not_lt hup)))))
            (BPair.mul_unit _)
        have hq : ∀ q B : BPair,
            (q * (B * (ground.getAt BPair.unit psi m
              * ground.getAt BPair.unit psi (m + 1)))).oneValue BPair.unit :=
          fun q B =>
            BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl q)
                (BPair.oneValue_trans
                  (BPair.mul_congr (BPair.oneValue_refl B) hP)
                  (BPair.mul_unit B)))
              (BPair.mul_unit q)
        exact BPair.oneValue_trans
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _) hP) (BPair.mul_unit _))
          (BPair.oneValue_symm
            (BPair.oneValue_trans
              (BPair.add_congr (hq _ _)
                (BPair.add_congr (hq _ _) (hq _ _)))
              (BPair.oneValue_trans
                (BPair.add_congr (BPair.oneValue_refl BPair.unit)
                  (BPair.add_unit BPair.unit))
                (BPair.add_unit BPair.unit)))))


/-- A constant bond withdraws from the second-bond stream at its own
datum, the two keys beyond the bond's count meeting the ground's own
vacancy. -/
theorem dBond (b psi : List BPair) (β : BPair) (hb : constBond b β)
    (hlen : b.length + 1 = psi.length) (V : Nat → BPair) :
    (dStream psi (fun k => ground.getAt BPair.unit b k * V k)).oneValue
      (β * dStream psi V) :=
  bondStream b β hb V
    (fun k => ground.getAt BPair.unit psi k
      * ground.getAt BPair.unit psi (k + 2))
    (fun k => k) psi.length
    (fun k _ hge =>
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_of_eq (ground.getAt_over BPair.unit psi (k + 2)
            (Nat.le_trans (Nat.le_of_eq hlen.symm)
              (Nat.succ_le_succ (Nat.le_succ_of_le hge))))))
        (BPair.mul_unit _))

/-- The square fold's row at the monomial weight: the three
neighboring square moments at the profile's constants read the bond
moment at the height joined to the Pascal expansion of the bond
moments at or below it, both at the bond's own datum. -/
theorem fa_row (a b psi : List BPair) (p2 p1 p0 β : BPair)
    (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) (j : Nat) :
    (p2 * mrho psi (j + 2) + (p1 * mrho psi (j + 1) + p0 * mrho psi j)).oneValue
      (β * mc psi j
        + β * ground.bsum (fun t => BPair.ofNat (ground.pasc j t) * mc psi t)
          (List.range (j + 1))) := by
  have hlenA : psi.length = a.length := recRead_lenA a b psi h
  have hlenB : b.length + 1 = psi.length :=
    (recRead_lenB a b psi h).trans hlenA.symm
  have hLo : (cStream psi (fun k => ground.getAt BPair.unit b k
        * ground.bpow (BPair.ofNat k) j)).oneValue (β * mc psi j) :=
    cBond b psi β hb hlenB (fun k => ground.bpow (BPair.ofNat k) j)
  have hHi : (cStream psi (fun k => ground.getAt BPair.unit b k
        * ground.bpow (BPair.ofNat (k + 1)) j)).oneValue
      (β * ground.bsum (fun t => BPair.ofNat (ground.pasc j t) * mc psi t)
        (List.range (j + 1))) := by
    refine BPair.oneValue_trans
      (cShift1 psi (fun k => ground.getAt BPair.unit b k) j) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun t => β * (BPair.ofNat (ground.pasc j t) * mc psi t))
        (List.range (j + 1)) (fun t _ => ?_)) ?_
    · exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (cBond b psi β hb hlenB (fun k => ground.bpow (BPair.ofNat k) t)))
        (BPair.oneValue_of_eq
          (BPair.mul_left_comm (BPair.ofNat (ground.pasc j t)) β (mc psi t)))
    · exact ground.foldB_mul_left β
        (fun t => BPair.ofNat (ground.pasc j t) * mc psi t)
        (List.range (j + 1))
  exact BPair.oneValue_trans
    (BPair.oneValue_symm
      (BPair.oneValue_trans
        (fold_sq a b psi h (fun k => ground.bpow (BPair.ofNat k) j))
        (profRho a psi p2 p1 p0 hp hlenA j)))
    (BPair.add_congr hLo hHi)

/-- The second-bond reduction's row at the monomial weight: the
second-bond and square moments at the bond's datum read the raised
key's profile against three neighboring bond moments, the far edge's
own read joining. -/
theorem d_row (a b psi : List BPair) (p2 p1 p0 β : BPair)
    (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) (t : Nat) :
    (β * md psi t + β * mrho psi t).oneValue
      (p2 * mc psi (t + 2)
        + ((p2 + p2 + p1) * mc psi (t + 1) + (p2 + p1 + p0) * mc psi t)
        + β * edgeAt psi t) := by
  have hlenA : psi.length = a.length := recRead_lenA a b psi h
  have hlenB : b.length + 1 = psi.length :=
    (recRead_lenB a b psi h).trans hlenA.symm
  have hD : (dStream psi (fun k => ground.getAt BPair.unit b (k + 1)
        * ground.bpow (BPair.ofNat k) t)).oneValue (β * md psi t) :=
    dBondUp b psi β hb hlenB (fun k => ground.bpow (BPair.ofNat k) t)
  have hR : (rhoStream psi (fun k => ground.getAt BPair.unit b k
        * ground.bpow (BPair.ofNat k) t)
      + β * edgeAt psi t).oneValue (β * mrho psi t) :=
    rhoBond b psi β hb hlenB (fun k => ground.bpow (BPair.ofNat k) t)
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_symm hD) (BPair.oneValue_symm hR)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
  exact BPair.add_congr
    (BPair.oneValue_trans
      (bond2_reduce a b psi h (fun k => ground.bpow (BPair.ofNat k) t))
      (profCUp a psi p2 p1 p0 hp hlenA t))
    (BPair.oneValue_refl _)

/-- The bond fold's row at the vacant height: the second-bond and
square moments at the bond's datum read the profile's three
neighboring bond moments with the boundary square joining at the
bond's datum. -/
theorem fb_row_zero (a b psi : List BPair) (p2 p1 p0 β : BPair)
    (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) :
    (β * md psi 0 + β * mrho psi 0).oneValue
      (p2 * mc psi 2 + (p1 * mc psi 1 + p0 * mc psi 0) + β * bSq psi) := by
  have hlenA : psi.length = a.length := recRead_lenA a b psi h
  have hlenB : b.length + 1 = psi.length :=
    (recRead_lenB a b psi h).trans hlenA.symm
  have hD : (dStream psi (fun k => ground.getAt BPair.unit b k
        * ground.bpow (BPair.ofNat (k + 1 + 1)) 0)).oneValue (β * md psi 0) :=
    dBond b psi β hb hlenB (fun k => ground.bpow (BPair.ofNat (k + 1 + 1)) 0)
  have hR : (rhoStream psi (wShift (fun t => ground.getAt BPair.unit b t
        * ground.bpow (BPair.ofNat (t + 1)) 0))
      + β * bSq psi).oneValue (β * mrho psi 0) :=
    BPair.oneValue_trans
      (BPair.add_congr
        (wCollapse b psi β hb hlenB
          (fun t => ground.bpow (BPair.ofNat (t + 1)) 0))
        (BPair.oneValue_refl _))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.left_distrib β _ _).symm)
        (BPair.mul_congr (BPair.oneValue_refl β) (wMono_zero psi)))
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_symm hD) (BPair.oneValue_symm hR)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
  exact BPair.add_congr
    (BPair.oneValue_trans
      (fold_bond a b psi h (fun k => ground.bpow (BPair.ofNat (k + 1)) 0))
      (profC a psi p2 p1 p0 hp hlenA 0))
    (BPair.oneValue_refl _)

/-- The bond fold's row at a raised height: the Pascal expansion of
the second-bond moments at the doubled base's complementary powers,
joined to the square moment at the height, reads the Pascal expansion
of the profile's three neighboring bond moments, every term at the
bond's own datum. -/
theorem fb_row_succ (a b psi : List BPair) (p2 p1 p0 β : BPair)
    (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) (j : Nat) :
    (β * ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t))
        (List.range (j + 2))
      + β * mrho psi (j + 1)).oneValue
      (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2) + (p1 * mc psi (s + 1) + p0 * mc psi s)))
        (List.range (j + 2))) := by
  have hlenA : psi.length = a.length := recRead_lenA a b psi h
  have hlenB : b.length + 1 = psi.length :=
    (recRead_lenB a b psi h).trans hlenA.symm
  have hD : (dStream psi (fun k => ground.getAt BPair.unit b k
        * ground.bpow (BPair.ofNat (k + 1 + 1)) (j + 1))).oneValue
      (β * ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t))
        (List.range (j + 2))) := by
    refine BPair.oneValue_trans
      (dShift2 psi (fun k => ground.getAt BPair.unit b k) (j + 1)) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun t => β * (BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t)))
        (List.range (j + 2)) (fun t _ => ?_)) ?_
    · refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.mul_congr (BPair.oneValue_refl _)
            (dBond b psi β hb hlenB
              (fun k => ground.bpow (BPair.ofNat k) t)))) ?_
      exact BPair.oneValue_of_eq
        ((congrArg (fun z => BPair.ofNat (ground.pasc (j + 1) t) * z)
            (BPair.mul_left_comm (ground.bpow (BPair.ofNat 2) (j + 1 - t)) β
              (md psi t))).trans
          (BPair.mul_left_comm (BPair.ofNat (ground.pasc (j + 1) t)) β
            (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t)))
    · exact ground.foldB_mul_left β
        (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t))
        (List.range (j + 2))
  have hR : (rhoStream psi (wShift (fun t => ground.getAt BPair.unit b t
        * ground.bpow (BPair.ofNat (t + 1)) (j + 1)))).oneValue
      (β * mrho psi (j + 1)) :=
    BPair.oneValue_trans
      (wCollapse b psi β hb hlenB
        (fun t => ground.bpow (BPair.ofNat (t + 1)) (j + 1)))
      (BPair.mul_congr (BPair.oneValue_refl β) (wMono_succ psi j))
  have hC : (cStream psi (fun k => ground.getAt BPair.unit a k
        * ground.bpow (BPair.ofNat (k + 1)) (j + 1))).oneValue
      (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2) + (p1 * mc psi (s + 1) + p0 * mc psi s)))
        (List.range (j + 2))) :=
    BPair.oneValue_trans
      (cShift1 psi (fun k => ground.getAt BPair.unit a k) (j + 1))
      (ground.foldB_congr_members _ _ (List.range (j + 2)) (fun s _ =>
        BPair.mul_congr (BPair.oneValue_refl _)
          (profC a psi p2 p1 p0 hp hlenA s)))
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_symm hD) (BPair.oneValue_symm hR))
    (BPair.oneValue_trans
      (fold_bond a b psi h (fun k => ground.bpow (BPair.ofNat (k + 1)) (j + 1)))
      hC)

/-- The second fold's row at the vacant height: the raised key's
profile against three neighboring bond moments with the far edge's
read reads the profile's own three at the boundary square. -/
theorem fbd_row_zero (a b psi : List BPair) (p2 p1 p0 β : BPair)
    (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) :
    (p2 * mc psi 2
      + ((p2 + p2 + p1) * mc psi 1 + (p2 + p1 + p0) * mc psi 0)
      + β * edgeAt psi 0).oneValue
      (p2 * mc psi 2 + (p1 * mc psi 1 + p0 * mc psi 0) + β * bSq psi) :=
  BPair.oneValue_trans
    (BPair.oneValue_symm (d_row a b psi p2 p1 p0 β h hp hb 0))
    (fb_row_zero a b psi p2 p1 p0 β h hp hb)

/-- The second fold's row at a raised height: the square moment at
the height joined to the Pascal expansion of the raised key's profile
with the far edge's reads reads the Pascal expansion of the
profile's three neighboring bond moments against the Pascal
expansion of the square moments below the height, the second-bond
moments withdrawn. -/
theorem fbd_row_succ (a b psi : List BPair) (p2 p1 p0 β : BPair)
    (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) (j : Nat) :
    (β * mrho psi (j + 1)
      + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (p2 * mc psi (t + 2)
              + ((p2 + p2 + p1) * mc psi (t + 1) + (p2 + p1 + p0) * mc psi t)
              + β * edgeAt psi t)))
          (List.range (j + 2))).oneValue
      (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2) + (p1 * mc psi (s + 1) + p0 * mc psi s)))
        (List.range (j + 2))
        + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * (β * mrho psi t)))
          (List.range (j + 2))) := by
  have hA : (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)
            + ((p2 + p2 + p1) * mc psi (t + 1) + (p2 + p1 + p0) * mc psi t)
            + β * edgeAt psi t)))
        (List.range (j + 2))).oneValue
      (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * md psi t + β * mrho psi t)))
        (List.range (j + 2))) :=
    ground.foldB_congr_members _ _ (List.range (j + 2)) (fun t _ =>
      BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (d_row a b psi p2 p1 p0 β h hp hb t))))
  have hB : (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * md psi t + β * mrho psi t)))
        (List.range (j + 2))).oneValue
      (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * (β * md psi t)))
          (List.range (j + 2))
        + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * (β * mrho psi t)))
          (List.range (j + 2))) :=
    BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun t => BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * (β * md psi t))
          + BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * (β * mrho psi t)))
        (List.range (j + 2)) (fun t _ =>
          BPair.oneValue_of_eq
            ((congrArg (fun z => BPair.ofNat (ground.pasc (j + 1) t) * z)
                (BPair.left_distrib (ground.bpow (BPair.ofNat 2) (j + 1 - t))
                  (β * md psi t) (β * mrho psi t))).trans
              (BPair.left_distrib (BPair.ofNat (ground.pasc (j + 1) t)) _ _))))
      (ground.foldB_add _ _ (List.range (j + 2)))
  have hM : (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * (β * md psi t)))
        (List.range (j + 2))).oneValue
      (β * ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t))
        (List.range (j + 2))) :=
    BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun t => β * (BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t)))
        (List.range (j + 2)) (fun t _ =>
          BPair.oneValue_of_eq
            ((congrArg (fun z => BPair.ofNat (ground.pasc (j + 1) t) * z)
                (BPair.mul_left_comm (ground.bpow (BPair.ofNat 2) (j + 1 - t))
                  β (md psi t))).trans
              (BPair.mul_left_comm (BPair.ofNat (ground.pasc (j + 1) t)) β
                (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t)))))
      (ground.foldB_mul_left β
        (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t))
        (List.range (j + 2)))
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans hA
        (BPair.oneValue_trans hB (BPair.add_congr hM (BPair.oneValue_refl _)))))
    ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      ((BPair.add_assoc _ _ _).symm.trans
        (congrArg (fun z => z + ground.bsum
            (fun t => BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * (β * mrho psi t)))
            (List.range (j + 2)))
          (BPair.add_comm (β * mrho psi (j + 1))
            (β * ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * md psi t))
              (List.range (j + 2))))))) ?_
  exact BPair.add_congr (fb_row_succ a b psi p2 p1 p0 β h hp hb j)
    (BPair.oneValue_refl _)

/-- The truncated moment vector: the square moments and the bond
moments through a stated height with the boundary square. -/
def momVec (psi : List BPair) (K : Nat) : List BPair :=
  (List.range (K + 1)).map (fun j => mrho psi j)
    ++ ((List.range (K + 1)).map (fun j => mc psi j) ++ [bSq psi])

/-! Clause (ii)'s square system: the rows accumulated from the
identities' own term lists, the truncated moment vector's entry
reads, and the system's read at the vector — the identities at
weights through the stated degree with the base reads, one square
linear system. -/

/-- The vacant row at a stated width. -/
private def padRow : Nat → List BPair
  | 0 => []
  | n + 1 => BPair.unit :: padRow n

private theorem padRow_len : ∀ n : Nat, (padRow n).length = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (padRow_len n)

private theorem dotP_padRow : ∀ (n : Nat) (v : List BPair),
    (elim.dotP (padRow n) v).oneValue BPair.unit
  | 0, _ => BPair.oneValue_refl _
  | n + 1, [] => BPair.oneValue_of_eq (elim.dotP_nil_right _)
  | n + 1, c :: v => by
    show (BPair.unit * c + elim.dotP (padRow n) v).oneValue BPair.unit
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul c) (dotP_padRow n v))
      (BPair.unit_add BPair.unit)

/-- The row with a datum joined at a stated key, the beyond-width
key vacant. -/
private def addAt : List BPair → Nat → BPair → List BPair
  | [], _, _ => []
  | y :: r, 0, x => (x + y) :: r
  | y :: r, k + 1, x => y :: addAt r k x

private theorem addAt_len : ∀ (r : List BPair) (k : Nat) (x : BPair),
    (addAt r k x).length = r.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: r, k + 1, x => congrArg Nat.succ (addAt_len r k x)

/-- The joined key's pairing: the datum against the vector's entry
at the key joins the row's own pairing. -/
private theorem dotP_addAt : ∀ (r v : List BPair) (k : Nat) (x : BPair),
    k < r.length →
    (elim.dotP (addAt r k x) v).oneValue
      (x * ground.getAt BPair.unit v k + elim.dotP r v)
  | [], _, k, _, hk => absurd hk (Nat.not_lt_zero k)
  | y :: r, [], 0, x, _ => by
    rw [elim.dotP_nil_right, elim.dotP_nil_right]
    exact BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.mul_unit x) (BPair.oneValue_refl _))
        (BPair.unit_add BPair.unit))
  | y :: r, [], k + 1, x, _ => by
    rw [elim.dotP_nil_right, elim.dotP_nil_right]
    exact BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.mul_unit x) (BPair.oneValue_refl _))
        (BPair.unit_add BPair.unit))
  | y :: r, c :: v, 0, x, _ => by
    show ((x + y) * c + elim.dotP r v).oneValue
      (x * c + (y * c + elim.dotP r v))
    rw [BPair.mul_comm (x + y) c, BPair.left_distrib c x y,
      BPair.mul_comm c x, BPair.mul_comm c y]
    exact BPair.oneValue_of_eq
      (BPair.add_assoc (x * c) (y * c) (elim.dotP r v))
  | y :: r, c :: v, k + 1, x, hk => by
    show (y * c + elim.dotP (addAt r k x) v).oneValue
      (x * ground.getAt BPair.unit v k + (y * c + elim.dotP r v))
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (y * c))
        (dotP_addAt r v k x (Nat.lt_of_succ_lt_succ hk))) ?_
    exact BPair.oneValue_of_eq
      (BPair.add_left_comm (y * c)
        (x * ground.getAt BPair.unit v k) (elim.dotP r v))

/-- The row accumulated from a term list: each term's datum joined
at its key over the vacant row. -/
private def rowAcc (n : Nat) : List (Nat × BPair) → List BPair
  | [] => padRow n
  | t :: ts => addAt (rowAcc n ts) t.1 t.2

private theorem rowAcc_len (n : Nat) :
    ∀ ts : List (Nat × BPair), (rowAcc n ts).length = n
  | [] => padRow_len n
  | _ :: ts => (addAt_len _ _ _).trans (rowAcc_len n ts)

private theorem keysLt_mapRange (n : Nat) (g : Nat → Nat)
    (c : Nat → BPair) : ∀ m : Nat, (∀ t, t < m → g t < n) →
      ground.keysBelow n ((List.range m).map (fun t => (g t, c t)))
  | 0, _ => trivial
  | m + 1, h => by
    rw [ground.range_succ m, ground.map_append]
    exact ground.keysBelow_append n _ _
      (keysLt_mapRange n g c m
        (fun t ht => h t (Nat.lt_succ_of_lt ht)))
      ⟨h m (Nat.lt_succ_self m), trivial⟩

/-- The accumulated row's pairing reads the term fold, each term's
datum against the vector's entry at its key. -/
private theorem dotP_rowAcc (n : Nat) (v : List BPair) :
    ∀ ts : List (Nat × BPair), ground.keysBelow n ts →
      (elim.dotP (rowAcc n ts) v).oneValue
        (ground.bsum (fun p : Nat × BPair =>
          p.2 * ground.getAt BPair.unit v p.1) ts + BPair.unit)
  | [], _ =>
    BPair.oneValue_symm
      (BPair.oneValue_trans (BPair.unit_add BPair.unit)
        (BPair.oneValue_symm (dotP_padRow n v)))
  | t :: ts, h => by
    refine BPair.oneValue_trans
      (dotP_addAt (rowAcc n ts) v t.1 t.2
        (by rw [rowAcc_len n ts]; exact h.1)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (dotP_rowAcc n v ts h.2)) ?_
    exact BPair.oneValue_of_eq
      (BPair.add_assoc (t.2 * ground.getAt BPair.unit v t.1) _ _).symm

/-- The moment vector's square-moment entry. -/
private theorem momVec_rho (psi : List BPair) (K i : Nat)
    (h : i < K + 1) :
    ground.getAt BPair.unit (momVec psi K) i = mrho psi i := by
  show ground.getAt BPair.unit
    ((List.range (K + 1)).map (fun j => mrho psi j) ++ _) i = _
  rw [ground.getAt_append, ground.length_mapRange, if_pos h,
    ground.getAt_map_range, if_pos h]

/-- The moment vector's bond-moment entry. -/
private theorem momVec_c (psi : List BPair) (K t : Nat)
    (h : t < K + 1) :
    ground.getAt BPair.unit (momVec psi K) (K + 1 + t) = mc psi t := by
  show ground.getAt BPair.unit
    ((List.range (K + 1)).map (fun j => mrho psi j)
      ++ ((List.range (K + 1)).map (fun j => mc psi j) ++ [bSq psi]))
    (K + 1 + t) = _
  rw [ground.getAt_append, ground.length_mapRange,
    if_neg (fun hlt => absurd
      (Nat.lt_of_le_of_lt (Nat.le_add_right (K + 1) t) hlt)
      (Nat.lt_irrefl (K + 1))),
    ground.addSubSelfL (K + 1) t, ground.getAt_append,
    ground.length_mapRange, if_pos h, ground.getAt_map_range, if_pos h]

/-- The moment vector's boundary-square entry. -/
private theorem momVec_b (psi : List BPair) (K : Nat) :
    ground.getAt BPair.unit (momVec psi K) (K + 1 + (K + 1))
      = bSq psi := by
  show ground.getAt BPair.unit
    ((List.range (K + 1)).map (fun j => mrho psi j)
      ++ ((List.range (K + 1)).map (fun j => mc psi j) ++ [bSq psi]))
    (K + 1 + (K + 1)) = _
  rw [ground.getAt_append, ground.length_mapRange,
    if_neg (fun hlt => absurd
      (Nat.lt_of_le_of_lt (Nat.le_add_right (K + 1) (K + 1)) hlt)
      (Nat.lt_irrefl (K + 1))),
    ground.addSubSelfL (K + 1) (K + 1), ground.getAt_append,
    ground.length_mapRange, if_neg (Nat.lt_irrefl (K + 1)),
    ground.subLe (K + 1) (K + 1) (Nat.le_refl (K + 1))]
  rfl

/-- A fold of balance partners is the fold's own partner. -/
private theorem swapFold {α : Type} (g : α → BPair) :
    ∀ l : List α,
      ground.bsum (fun x => (g x).swap) l = (ground.bsum g l).swap
  | [] => rfl
  | a :: l => by
    show (g a).swap + ground.bsum (fun x => (g x).swap) l = _
    rw [swapFold g l, BPair.swap_add]
    rfl

/-- The base row at a stated key reads the vector's entry there. -/
private theorem baseRow_read (v : List BPair) (n key : Nat)
    (hkey : key < n) :
    (elim.dotN (rowAcc n [(key, BPair.ofPos Pos.one)]) v).oneValue
      (ground.getAt BPair.unit v key) := by
  refine BPair.oneValue_trans (elim.dotN_read _ v) ?_
  refine BPair.oneValue_trans
    (dotP_rowAcc n v [(key, BPair.ofPos Pos.one)] ⟨hkey, trivial⟩) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.ofPos_one_mul (ground.getAt BPair.unit v key))
          (BPair.oneValue_refl BPair.unit))
        (BPair.add_unit (ground.getAt BPair.unit v key)))
      (BPair.oneValue_refl BPair.unit)) ?_
  exact BPair.add_unit (ground.getAt BPair.unit v key)

/-- The two sides of an identity withdraw across a row's fold: a
fold reading one side joined to the other's balance partner reads
the sum's unit. -/
private theorem rowNull {D X Y : BPair} (hD : D.oneValue (X + Y.swap))
    (h : X.oneValue Y) : D.oneValue BPair.unit :=
  BPair.oneValue_trans hD
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm X Y.swap))
      (BPair.swap_add_null (BPair.oneValue_symm h)))

/-- The FA row's term list at a monomial weight: the profile's
three square-moment data against the bond fold's balance partners,
`fa_row`'s two sides at the accumulated row. -/
private def faTerms (K j : Nat) (p2 p1 p0 β : BPair) :
    List (Nat × BPair) :=
  (j + 2, p2) :: (j + 1, p1) :: (j, p0) :: (K + 1 + j, β.swap)
    :: (List.range (j + 1)).map (fun t =>
      (K + 1 + t, (β * BPair.ofNat (ground.pasc j t)).swap))

private theorem faTerms_keys (K j : Nat) (p2 p1 p0 β : BPair)
    (hj : j + 2 ≤ K) :
    ground.keysBelow (K + 1 + (K + 1 + 1)) (faTerms K j p2 p1 p0 β) := by
  have hKn : K < K + 1 + (K + 1 + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self K)
      (Nat.le_add_right (K + 1) (K + 1 + 1))
  have hrho : ∀ i : Nat, i ≤ j + 2 →
      i < K + 1 + (K + 1 + 1) := fun i hi =>
    Nat.lt_of_le_of_lt (Nat.le_trans hi hj) hKn
  have hcap : ∀ t : Nat, t < j + 2 →
      K + 1 + t < K + 1 + (K + 1 + 1) := fun t ht =>
    Nat.add_lt_add_left
      (Nat.lt_of_lt_of_le ht
        (Nat.le_trans hj (Nat.le_add_right K 2))) (K + 1)
  exact ⟨hrho (j + 2) (Nat.le_refl _),
    hrho (j + 1) (Nat.le_succ _),
    hrho j (Nat.le_of_succ_le (Nat.le_succ _)),
    hcap j (Nat.lt_succ_of_le (Nat.le_succ j)),
    keysLt_mapRange _ (fun t => K + 1 + t) _ (j + 1)
      (fun t ht => hcap t (Nat.lt_succ_of_lt ht))⟩

/-- The FA row reads the sum's unit against the moment vector,
`fa_row`'s two sides withdrawing across the accumulated row. -/
private theorem faRow_read (a b psi : List BPair)
    (p2 p1 p0 β : BPair) (K j : Nat)
    (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) (hj : j + 2 ≤ K) :
    (elim.dotN
      (rowAcc (K + 1 + (K + 1 + 1)) (faTerms K j p2 p1 p0 β))
      (momVec psi K)).oneValue BPair.unit := by
  have hj2 : j + 2 < K + 1 := Nat.lt_succ_of_le hj
  have hj1 : j + 1 < K + 1 :=
    Nat.lt_succ_of_le (Nat.le_of_succ_le hj)
  have hj0 : j < K + 1 :=
    Nat.lt_succ_of_le (Nat.le_of_succ_le (Nat.le_of_succ_le hj))
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (dotP_rowAcc _ _ _ (faTerms_keys K j p2 p1 p0 β hj)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr ?_ (BPair.oneValue_refl BPair.unit))
    (BPair.unit_add BPair.unit)
  show (p2 * ground.getAt BPair.unit (momVec psi K) (j + 2)
    + (p1 * ground.getAt BPair.unit (momVec psi K) (j + 1)
      + (p0 * ground.getAt BPair.unit (momVec psi K) j
        + (β.swap * ground.getAt BPair.unit (momVec psi K) (K + 1 + j)
          + ground.bsum (fun p : Nat × BPair =>
              p.2 * ground.getAt BPair.unit (momVec psi K) p.1)
            ((List.range (j + 1)).map (fun t =>
              (K + 1 + t,
                (β * BPair.ofNat (ground.pasc j t)).swap))))))).oneValue
    BPair.unit
  rw [momVec_rho psi K (j + 2) hj2, momVec_rho psi K (j + 1) hj1,
    momVec_rho psi K j hj0, momVec_c psi K j hj0,
    BPair.swap_mul β (mc psi j), ground.bsum_map]
  have hmap : (ground.bsum (fun t =>
      (β * BPair.ofNat (ground.pasc j t)).swap
        * ground.getAt BPair.unit (momVec psi K) (K + 1 + t))
      (List.range (j + 1))).oneValue
      ((β * ground.bsum (fun t =>
        BPair.ofNat (ground.pasc j t) * mc psi t)
        (List.range (j + 1))).swap) := by
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun t => (β * (BPair.ofNat (ground.pasc j t)
          * mc psi t)).swap)
        (List.range (j + 1)) (fun t ht => BPair.oneValue_of_eq (by
          rw [BPair.swap_mul,
            momVec_c psi K t
              (Nat.lt_of_lt_of_le (ground.ltOfMem ht) (Nat.le_of_lt hj1)),
            BPair.mul_assoc]))) ?_
    exact BPair.oneValue_trans
      (BPair.oneValue_of_eq (swapFold
        (fun t => β * (BPair.ofNat (ground.pasc j t) * mc psi t))
        (List.range (j + 1))))
      (ground.swap_congr
        (ground.foldB_mul_left β
          (fun t => BPair.ofNat (ground.pasc j t) * mc psi t)
          (List.range (j + 1))))
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.add_congr (BPair.oneValue_refl _) hmap)))) ?_
  exact rowNull
    (BPair.oneValue_of_eq (by
      rw [BPair.swap_add (β * mc psi j)
          (β * ground.bsum (fun t =>
            BPair.ofNat (ground.pasc j t) * mc psi t)
            (List.range (j + 1))),
        ← BPair.add_assoc (p1 * mrho psi (j + 1)) (p0 * mrho psi j),
        ← BPair.add_assoc (p2 * mrho psi (j + 2))]))
    (fa_row a b psi p2 p1 p0 β h hp hb j)

/-- The reduced second fold's row at the vacant height, its term
list: the raised profile's two surviving bond-moment data against
the plain profile's balance partners with the boundary square's,
the top weight withdrawn (`fbd_row_zero`'s two sides less the
shared top). -/
private def fbdTermsZero (K : Nat) (p2 p1 p0 β : BPair) :
    List (Nat × BPair) :=
  [(K + 1 + 1, p2 + p2 + p1), (K + 1, p2 + p1 + p0),
   (K + 1 + 1, p1.swap), (K + 1, p0.swap),
   (K + 1 + (K + 1), β.swap)]

private theorem fbdTermsZero_keys (K : Nat) (p2 p1 p0 β : BPair) :
    ground.keysBelow (K + 1 + (K + 1 + 1)) (fbdTermsZero K p2 p1 p0 β) := by
  have h1 : K + 1 + 1 < K + 1 + (K + 1 + 1) :=
    Nat.add_lt_add_left
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1)
        (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le K)))) (K + 1)
  have h0 : K + 1 < K + 1 + (K + 1 + 1) := by
    show K + 1 + 0 < K + 1 + (K + 1 + 1)
    exact Nat.add_lt_add_left (Nat.succ_pos (K + 1)) (K + 1)
  have hb : K + 1 + (K + 1) < K + 1 + (K + 1 + 1) :=
    Nat.add_lt_add_left (Nat.lt_succ_self (K + 1)) (K + 1)
  exact ⟨h1, h0, h1, h0, hb, trivial⟩

/-- The reduced second fold's row at the vacant height reads the
far edge's balance partner against the moment vector, the shared
top withdrawing across `fbd_row_zero`'s two sides. -/
private theorem fbdRowZero_read (a b psi : List BPair)
    (p2 p1 p0 β : BPair) (K : Nat)
    (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) (hK : 1 ≤ K) :
    (elim.dotN
      (rowAcc (K + 1 + (K + 1 + 1)) (fbdTermsZero K p2 p1 p0 β))
      (momVec psi K)).oneValue ((β * edgeAt psi 0).swap) := by
  have h1 : 1 < K + 1 := Nat.lt_succ_of_le hK
  have h0 : 0 < K + 1 := Nat.succ_pos K
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (dotP_rowAcc _ _ _ (fbdTermsZero_keys K p2 p1 p0 β)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr ?_ (BPair.oneValue_refl BPair.unit))
    (BPair.add_unit ((β * edgeAt psi 0).swap))
  show ((p2 + p2 + p1) * ground.getAt BPair.unit (momVec psi K)
      (K + 1 + 1)
    + ((p2 + p1 + p0) * ground.getAt BPair.unit (momVec psi K) (K + 1)
      + (p1.swap * ground.getAt BPair.unit (momVec psi K) (K + 1 + 1)
        + (p0.swap * ground.getAt BPair.unit (momVec psi K) (K + 1)
          + (β.swap * ground.getAt BPair.unit (momVec psi K)
              (K + 1 + (K + 1))
            + BPair.unit))))).oneValue ((β * edgeAt psi 0).swap)
  have hc1 : ground.getAt BPair.unit (momVec psi K) (K + 1 + 1)
      = mc psi 1 := momVec_c psi K 1 h1
  have hc0 : ground.getAt BPair.unit (momVec psi K) (K + 1)
      = mc psi 0 := by
    show ground.getAt BPair.unit (momVec psi K) (K + 1 + 0) = mc psi 0
    exact momVec_c psi K 0 h0
  rw [hc1, hc0, momVec_b psi K, BPair.swap_mul p1 (mc psi 1),
    BPair.swap_mul p0 (mc psi 0), BPair.swap_mul β (bSq psi)]
  have hid : ((p2 + p2 + p1) * mc psi 1 + (p2 + p1 + p0) * mc psi 0
      + β * edgeAt psi 0).oneValue
      (p1 * mc psi 1 + p0 * mc psi 0 + β * bSq psi) := by
    refine BPair.add_cancel (c := p2 * mc psi 2) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (by
      rw [BPair.add_comm ((p2 + p2 + p1) * mc psi 1
          + (p2 + p1 + p0) * mc psi 0 + β * edgeAt psi 0)
          (p2 * mc psi 2),
        ← BPair.add_assoc (p2 * mc psi 2)
          ((p2 + p2 + p1) * mc psi 1 + (p2 + p1 + p0) * mc psi 0)
          (β * edgeAt psi 0)])) ?_
    refine BPair.oneValue_trans
      (fbd_row_zero a b psi p2 p1 p0 β h hp hb) ?_
    refine BPair.oneValue_of_eq (by
      rw [BPair.add_assoc (p2 * mc psi 2)
          (p1 * mc psi 1 + p0 * mc psi 0) (β * bSq psi),
        BPair.add_comm (p2 * mc psi 2)
          (p1 * mc psi 1 + p0 * mc psi 0 + β * bSq psi)])
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.add_unit ((β * bSq psi).swap)))))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (by
    rw [← BPair.add_assoc ((p2 + p2 + p1) * mc psi 1)
      ((p2 + p1 + p0) * mc psi 0)
      ((p1 * mc psi 1).swap + ((p0 * mc psi 0).swap
        + (β * bSq psi).swap))])) ?_
  refine BPair.swap_of_add_unit ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (by
    rw [BPair.add_assoc ((p2 + p2 + p1) * mc psi 1
        + (p2 + p1 + p0) * mc psi 0)
        ((p1 * mc psi 1).swap + ((p0 * mc psi 0).swap
          + (β * bSq psi).swap))
        (β * edgeAt psi 0),
      BPair.add_comm ((p1 * mc psi 1).swap + ((p0 * mc psi 0).swap
        + (β * bSq psi).swap)) (β * edgeAt psi 0),
      ← BPair.add_assoc ((p2 + p2 + p1) * mc psi 1
        + (p2 + p1 + p0) * mc psi 0) (β * edgeAt psi 0)
        ((p1 * mc psi 1).swap + ((p0 * mc psi 0).swap
          + (β * bSq psi).swap))])) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr hid (BPair.oneValue_of_eq
      (congrArg BPair.swap
        (BPair.add_assoc (p1 * mc psi 1) (p0 * mc psi 0)
          (β * bSq psi)).symm))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq
    (BPair.add_comm (p1 * mc psi 1 + p0 * mc psi 0 + β * bSq psi)
      ((p1 * mc psi 1 + p0 * mc psi 0 + β * bSq psi).swap))) ?_
  exact BPair.swap_add_null (BPair.oneValue_refl _)

/-- The reduced second fold's row at a raised height, its term
list: the Pascal expansions of the raised profile's surviving
bond-moment data against the plain profile's and the down-shifted
square moments' balance partners, the top weight withdrawn
(`fbd_row_succ`'s two sides less the shared top). -/
private def fbdTermsSucc (K j : Nat) (p2 p1 p0 β : BPair) :
    List (Nat × BPair) :=
  (j + 1, β)
    :: ((List.range (j + 1)).map (fun t =>
        (K + 1 + (t + 2),
          BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * p2)))
      ++ ((List.range (j + 2)).map (fun t =>
          (K + 1 + (t + 1),
            BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * (p2 + p2 + p1))))
        ++ ((List.range (j + 2)).map (fun t =>
            (K + 1 + t,
              BPair.ofNat (ground.pasc (j + 1) t)
                * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                  * (p2 + p1 + p0))))
          ++ ((List.range (j + 1)).map (fun s =>
              (K + 1 + (s + 2),
                (BPair.ofNat (ground.pasc (j + 1) s) * p2).swap))
            ++ ((List.range (j + 2)).map (fun s =>
                (K + 1 + (s + 1),
                  (BPair.ofNat (ground.pasc (j + 1) s) * p1).swap))
              ++ ((List.range (j + 2)).map (fun s =>
                  (K + 1 + s,
                    (BPair.ofNat (ground.pasc (j + 1) s) * p0).swap))
                ++ (List.range (j + 2)).map (fun t =>
                    (t,
                      (BPair.ofNat (ground.pasc (j + 1) t)
                        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                          * β)).swap))))))))

private theorem fbdTermsSucc_keys (K j : Nat) (p2 p1 p0 β : BPair)
    (hj : j + 2 ≤ K) :
    ground.keysBelow (K + 1 + (K + 1 + 1)) (fbdTermsSucc K j p2 p1 p0 β) := by
  have hcap : ∀ u : Nat, u ≤ j + 3 →
      K + 1 + u < K + 1 + (K + 1 + 1) := fun u hu =>
    Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt
        (Nat.le_trans hu (Nat.succ_le_succ hj))
        (Nat.lt_succ_self (K + 1))) (K + 1)
  have hrho : ∀ t : Nat, t < j + 2 →
      t < K + 1 + (K + 1 + 1) := fun t ht =>
    Nat.lt_of_lt_of_le
      (Nat.lt_of_lt_of_le ht (Nat.succ_le_succ
        (Nat.le_of_succ_le hj)))
      (Nat.le_trans (Nat.le_add_right (K + 1) 0)
        (Nat.add_le_add_left (Nat.zero_le (K + 1 + 1)) (K + 1)))
  refine ⟨hrho (j + 1) (Nat.lt_succ_self (j + 1)),
    ground.keysBelow_append _ _ _
      (keysLt_mapRange _ (fun t => K + 1 + (t + 2)) _ (j + 1)
        (fun t ht => hcap (t + 2)
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.le_of_lt ht)))))
      (ground.keysBelow_append _ _ _
        (keysLt_mapRange _ (fun t => K + 1 + (t + 1)) _ (j + 2)
          (fun t ht => hcap (t + 1)
            (Nat.succ_le_succ (Nat.le_of_lt_succ
              (Nat.lt_succ_of_lt ht)))))
        (ground.keysBelow_append _ _ _
          (keysLt_mapRange _ (fun t => K + 1 + t) _ (j + 2)
            (fun t ht => hcap t
              (Nat.le_of_lt (Nat.lt_of_lt_of_le ht
                (Nat.le_succ (j + 2))))))
          (ground.keysBelow_append _ _ _
            (keysLt_mapRange _ (fun s => K + 1 + (s + 2)) _ (j + 1)
              (fun s hs => hcap (s + 2)
                (Nat.succ_le_succ (Nat.succ_le_succ
                  (Nat.le_of_lt hs)))))
            (ground.keysBelow_append _ _ _
              (keysLt_mapRange _ (fun s => K + 1 + (s + 1)) _ (j + 2)
                (fun s hs => hcap (s + 1)
                  (Nat.succ_le_succ (Nat.le_of_lt_succ
                    (Nat.lt_succ_of_lt hs)))))
              (ground.keysBelow_append _ _ _
                (keysLt_mapRange _ (fun s => K + 1 + s) _ (j + 2)
                  (fun s hs => hcap s
                    (Nat.le_of_lt (Nat.lt_of_lt_of_le hs
                      (Nat.le_succ (j + 2))))))
                (keysLt_mapRange _ (fun t => t) _ (j + 2) hrho))))))⟩

/-- Three factors regroup past a fourth. -/
private theorem mulAssoc2 (a b c d : BPair) :
    (a * (b * c)) * d = a * (b * (c * d)) := by
  rw [BPair.mul_assoc a (b * c) d, BPair.mul_assoc b c d]

/-- A swapped coefficient's product collects to the product's
partner. -/
private theorem swapCoef (a c d : BPair) :
    ((a * c).swap) * d = (a * (c * d)).swap := by
  rw [BPair.swap_mul, BPair.mul_assoc]

/-- The reduced second fold's row at a raised height reads the
Pascal edge fold's balance partner against the moment vector, the
shared top withdrawing across `fbd_row_succ`'s two sides. -/
private theorem fbdRowSucc_read (a b psi : List BPair)
    (p2 p1 p0 β : BPair) (K j : Nat)
    (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) (hj : j + 2 ≤ K) :
    (elim.dotN
      (rowAcc (K + 1 + (K + 1 + 1)) (fbdTermsSucc K j p2 p1 p0 β))
      (momVec psi K)).oneValue
      ((ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * edgeAt psi t))) (List.range (j + 2))).swap) := by
  have hcK : ∀ u : Nat, u ≤ j + 2 → u < K + 1 := fun u hu =>
    Nat.lt_succ_of_le (Nat.le_trans hu hj)
  -- the seven fold reads at the moment spellings
  have hA2 : BPair.oneValue (ground.bsum (fun p : Nat × BPair =>
      p.2 * ground.getAt BPair.unit (momVec psi K) p.1)
      ((List.range (j + 1)).map (fun t =>
        (K + 1 + (t + 2), BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * p2)))))
      (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)))) (List.range (j + 1))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (ground.bsum_map _ _ (List.range (j + 1)))) ?_
    exact ground.foldB_congr_members _ _ (List.range (j + 1))
      (fun t ht => BPair.oneValue_of_eq (by
        rw [momVec_c psi K (t + 2)
            (hcK (t + 2) (Nat.succ_le_succ (Nat.succ_le_succ
              (Nat.le_of_lt_succ (ground.ltOfMem ht))))),
          mulAssoc2]))
  have hB1 : BPair.oneValue (ground.bsum (fun p : Nat × BPair =>
      p.2 * ground.getAt BPair.unit (momVec psi K) p.1)
      ((List.range (j + 2)).map (fun t =>
        (K + 1 + (t + 1), BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (p2 + p2 + p1))))))
      (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p2 + p1) * mc psi (t + 1)))) (List.range (j + 2))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (ground.bsum_map _ _ (List.range (j + 2)))) ?_
    exact ground.foldB_congr_members _ _ (List.range (j + 2))
      (fun t ht => BPair.oneValue_of_eq (by
        rw [momVec_c psi K (t + 1)
            (hcK (t + 1) (Nat.succ_le_succ (Nat.le_of_lt_succ
              (ground.ltOfMem ht)))),
          mulAssoc2]))
  have hC0 : BPair.oneValue (ground.bsum (fun p : Nat × BPair =>
      p.2 * ground.getAt BPair.unit (momVec psi K) p.1)
      ((List.range (j + 2)).map (fun t =>
        (K + 1 + t, BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (p2 + p1 + p0))))))
      (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (ground.bsum_map _ _ (List.range (j + 2)))) ?_
    exact ground.foldB_congr_members _ _ (List.range (j + 2))
      (fun t ht => BPair.oneValue_of_eq (by
        rw [momVec_c psi K t
            (hcK t (Nat.le_of_lt (Nat.lt_of_lt_of_le
              (ground.ltOfMem ht) (Nat.le_refl (j + 2))))),
          mulAssoc2]))
  have hG2 : BPair.oneValue (ground.bsum (fun p : Nat × BPair =>
      p.2 * ground.getAt BPair.unit (momVec psi K) p.1)
      ((List.range (j + 1)).map (fun s =>
        (K + 1 + (s + 2),
          (BPair.ofNat (ground.pasc (j + 1) s) * p2).swap))))
      ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))).swap) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (ground.bsum_map _ _ (List.range (j + 1)))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun s => (BPair.ofNat (ground.pasc (j + 1) s)
          * (p2 * mc psi (s + 2))).swap)
        (List.range (j + 1)) (fun s hs => BPair.oneValue_of_eq (by
          rw [swapCoef, momVec_c psi K (s + 2)
            (hcK (s + 2) (Nat.succ_le_succ (Nat.succ_le_succ
              (Nat.le_of_lt_succ (ground.ltOfMem hs)))))]))) ?_
    exact BPair.oneValue_of_eq (swapFold _ (List.range (j + 1)))
  have hG1 : BPair.oneValue (ground.bsum (fun p : Nat × BPair =>
      p.2 * ground.getAt BPair.unit (momVec psi K) p.1)
      ((List.range (j + 2)).map (fun s =>
        (K + 1 + (s + 1),
          (BPair.ofNat (ground.pasc (j + 1) s) * p1).swap))))
      ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))).swap) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (ground.bsum_map _ _ (List.range (j + 2)))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun s => (BPair.ofNat (ground.pasc (j + 1) s)
          * (p1 * mc psi (s + 1))).swap)
        (List.range (j + 2)) (fun s hs => BPair.oneValue_of_eq (by
          rw [swapCoef, momVec_c psi K (s + 1)
            (hcK (s + 1) (Nat.succ_le_succ (Nat.le_of_lt_succ
              (ground.ltOfMem hs))))]))) ?_
    exact BPair.oneValue_of_eq (swapFold _ (List.range (j + 2)))
  have hG0 : BPair.oneValue (ground.bsum (fun p : Nat × BPair =>
      p.2 * ground.getAt BPair.unit (momVec psi K) p.1)
      ((List.range (j + 2)).map (fun s =>
        (K + 1 + s,
          (BPair.ofNat (ground.pasc (j + 1) s) * p0).swap))))
      ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))).swap) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (ground.bsum_map _ _ (List.range (j + 2)))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun s => (BPair.ofNat (ground.pasc (j + 1) s)
          * (p0 * mc psi s)).swap)
        (List.range (j + 2)) (fun s hs => BPair.oneValue_of_eq (by
          rw [swapCoef, momVec_c psi K s
            (hcK s (Nat.le_of_lt (Nat.lt_of_lt_of_le
              (ground.ltOfMem hs) (Nat.le_refl (j + 2)))))]))) ?_
    exact BPair.oneValue_of_eq (swapFold _ (List.range (j + 2)))
  have hRF : BPair.oneValue (ground.bsum (fun p : Nat × BPair =>
      p.2 * ground.getAt BPair.unit (momVec psi K) p.1)
      ((List.range (j + 2)).map (fun t =>
        (t, (BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t) * β)).swap))))
      ((ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))).swap) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (ground.bsum_map _ _ (List.range (j + 2)))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun t => (BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (β * mrho psi t))).swap)
        (List.range (j + 2)) (fun t ht => BPair.oneValue_of_eq (by
          rw [BPair.swap_mul,
            momVec_rho psi K t
              (hcK t (Nat.le_of_lt (Nat.lt_of_lt_of_le
                (ground.ltOfMem ht) (Nat.le_refl (j + 2))))),
            mulAssoc2]))) ?_
    exact BPair.oneValue_of_eq (swapFold _ (List.range (j + 2)))
  -- the identity's two sides distributed, the tops peeled
  have hL : (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
      * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
        * (p2 * mc psi (t + 2)
          + ((p2 + p2 + p1) * mc psi (t + 1)
            + (p2 + p1 + p0) * mc psi t)
          + β * edgeAt psi t))) (List.range (j + 2))).oneValue
      ((ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (p2 * mc psi (t + 2)))) (List.range (j + 2))
        + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
              * ((p2 + p2 + p1) * mc psi (t + 1)))) (List.range (j + 2))
          + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
              * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2))))
        + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (β * edgeAt psi t))) (List.range (j + 2))) := by
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun t => (BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
              * (p2 * mc psi (t + 2)))
          + (BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * ((p2 + p2 + p1) * mc psi (t + 1)))
            + BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * ((p2 + p1 + p0) * mc psi t))))
          + BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
              * (β * edgeAt psi t)))
        (List.range (j + 2)) (fun t _ => BPair.oneValue_of_eq (by
          rw [BPair.left_distrib
              (ground.bpow (BPair.ofNat 2) (j + 1 - t))
              (p2 * mc psi (t + 2)
                + ((p2 + p2 + p1) * mc psi (t + 1)
                  + (p2 + p1 + p0) * mc psi t))
              (β * edgeAt psi t),
            BPair.left_distrib
              (ground.bpow (BPair.ofNat 2) (j + 1 - t))
              (p2 * mc psi (t + 2))
              ((p2 + p2 + p1) * mc psi (t + 1)
                + (p2 + p1 + p0) * mc psi t),
            BPair.left_distrib
              (ground.bpow (BPair.ofNat 2) (j + 1 - t))
              ((p2 + p2 + p1) * mc psi (t + 1))
              ((p2 + p1 + p0) * mc psi t),
            BPair.left_distrib (BPair.ofNat (ground.pasc (j + 1) t))
              (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                  * (p2 * mc psi (t + 2))
                + (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                    * ((p2 + p2 + p1) * mc psi (t + 1))
                  + ground.bpow (BPair.ofNat 2) (j + 1 - t)
                    * ((p2 + p1 + p0) * mc psi t)))
              (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * (β * edgeAt psi t)),
            BPair.left_distrib (BPair.ofNat (ground.pasc (j + 1) t))
              (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * (p2 * mc psi (t + 2)))
              (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                  * ((p2 + p2 + p1) * mc psi (t + 1))
                + ground.bpow (BPair.ofNat 2) (j + 1 - t)
                  * ((p2 + p1 + p0) * mc psi t)),
            BPair.left_distrib (BPair.ofNat (ground.pasc (j + 1) t))
              (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * ((p2 + p2 + p1) * mc psi (t + 1)))
              (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * ((p2 + p1 + p0) * mc psi t))]))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_add _ _ (List.range (j + 2))) ?_
    refine BPair.add_congr ?_ (BPair.oneValue_refl _)
    refine BPair.oneValue_trans
      (ground.foldB_add _ _ (List.range (j + 2))) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    exact ground.foldB_add _ _ (List.range (j + 2))
  have hGdist : (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
      * (p2 * mc psi (s + 2)
        + (p1 * mc psi (s + 1) + p0 * mc psi s)))
      (List.range (j + 2))).oneValue
      (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
          * (p2 * mc psi (s + 2))) (List.range (j + 2))
        + (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
            * (p1 * mc psi (s + 1))) (List.range (j + 2))
          + ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
            * (p0 * mc psi s)) (List.range (j + 2)))) := by
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun s => BPair.ofNat (ground.pasc (j + 1) s)
            * (p2 * mc psi (s + 2))
          + (BPair.ofNat (ground.pasc (j + 1) s)
              * (p1 * mc psi (s + 1))
            + BPair.ofNat (ground.pasc (j + 1) s)
              * (p0 * mc psi s)))
        (List.range (j + 2)) (fun s _ => BPair.oneValue_of_eq (by
          rw [BPair.left_distrib (BPair.ofNat (ground.pasc (j + 1) s))
              (p2 * mc psi (s + 2))
              (p1 * mc psi (s + 1) + p0 * mc psi s),
            BPair.left_distrib (BPair.ofNat (ground.pasc (j + 1) s))
              (p1 * mc psi (s + 1)) (p0 * mc psi s)]))) ?_
    refine BPair.oneValue_trans
      (ground.foldB_add _ _ (List.range (j + 2))) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    exact ground.foldB_add _ _ (List.range (j + 2))
  have hsnocA : (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
      * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
        * (p2 * mc psi (t + 2)))) (List.range (j + 2))).oneValue
      (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)))) (List.range (j + 1))
        + BPair.ofNat (ground.pasc (j + 1) (j + 1))
          * (ground.bpow (BPair.ofNat 2) (j + 1 - (j + 1))
            * (p2 * mc psi (j + 1 + 2)))) :=
    ground.foldB_range_snoc
      (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)))) (j + 1)
  have hsnocG : (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
      * (p2 * mc psi (s + 2))) (List.range (j + 2))).oneValue
      (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))
        + BPair.ofNat (ground.pasc (j + 1) (j + 1))
          * (p2 * mc psi (j + 1 + 2))) :=
    ground.foldB_range_snoc
      (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (j + 1)
  have htop : (BPair.ofNat (ground.pasc (j + 1) (j + 1))
      * (ground.bpow (BPair.ofNat 2) (j + 1 - (j + 1))
        * (p2 * mc psi (j + 1 + 2)))).oneValue
      (BPair.ofNat (ground.pasc (j + 1) (j + 1))
        * (p2 * mc psi (j + 1 + 2))) := by
    rw [ground.subLe (j + 1) (j + 1) (Nat.le_refl (j + 1))]
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.ofPos_one_mul (p2 * mc psi (j + 1 + 2)))
  have hLHS : (β * mrho psi (j + 1)
      + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)
            + ((p2 + p2 + p1) * mc psi (t + 1)
              + (p2 + p1 + p0) * mc psi t)
            + β * edgeAt psi t))) (List.range (j + 2))).oneValue
      (((β * mrho psi (j + 1)
        + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
              * (p2 * mc psi (t + 2)))) (List.range (j + 1))
          + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * ((p2 + p2 + p1) * mc psi (t + 1))))
              (List.range (j + 2))
            + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2)))))
        + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (β * edgeAt psi t))) (List.range (j + 2)))
        + BPair.ofNat (ground.pasc (j + 1) (j + 1))
          * (ground.bpow (BPair.ofNat 2) (j + 1 - (j + 1))
            * (p2 * mc psi (j + 1 + 2)))) := by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) hL) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr
          (BPair.add_congr hsnocA (BPair.oneValue_refl _))
          (BPair.oneValue_refl _))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.add_right_comm
        (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (p2 * mc psi (t + 2)))) (List.range (j + 1)))
        (BPair.ofNat (ground.pasc (j + 1) (j + 1))
          * (ground.bpow (BPair.ofNat 2) (j + 1 - (j + 1))
            * (p2 * mc psi (j + 1 + 2))))
        (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
              * ((p2 + p2 + p1) * mc psi (t + 1)))) (List.range (j + 2))
          + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
              * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2)))]
    rw [BPair.add_right_comm
        (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
              * (p2 * mc psi (t + 2)))) (List.range (j + 1))
          + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * ((p2 + p2 + p1) * mc psi (t + 1))))
              (List.range (j + 2))
            + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2))))
        (BPair.ofNat (ground.pasc (j + 1) (j + 1))
          * (ground.bpow (BPair.ofNat 2) (j + 1 - (j + 1))
            * (p2 * mc psi (j + 1 + 2))))
        (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (β * edgeAt psi t))) (List.range (j + 2)))]
    rw [← BPair.add_assoc (β * mrho psi (j + 1))]
    rw [← BPair.add_assoc (β * mrho psi (j + 1))]
  have hRHS : (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
      * (p2 * mc psi (s + 2)
        + (p1 * mc psi (s + 1) + p0 * mc psi s)))
      (List.range (j + 2))
      + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))).oneValue
      ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
          * (p2 * mc psi (s + 2))) (List.range (j + 1))
        + (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
            * (p1 * mc psi (s + 1))) (List.range (j + 2))
          + (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
              * (p0 * mc psi s)) (List.range (j + 2))
            + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * (β * mrho psi t))) (List.range (j + 2)))))
        + BPair.ofNat (ground.pasc (j + 1) (j + 1))
          * (ground.bpow (BPair.ofNat 2) (j + 1 - (j + 1))
            * (p2 * mc psi (j + 1 + 2)))) := by
    refine BPair.oneValue_trans
      (BPair.add_congr hGdist (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.add_congr hsnocG (BPair.oneValue_refl _))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq ?_)
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm htop))
    rw [BPair.add_right_comm
        (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
          * (p2 * mc psi (s + 2))) (List.range (j + 1)))
        (BPair.ofNat (ground.pasc (j + 1) (j + 1))
          * (p2 * mc psi (j + 1 + 2)))
        (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
            * (p1 * mc psi (s + 1))) (List.range (j + 2))
          + ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
            * (p0 * mc psi s)) (List.range (j + 2)))]
    rw [BPair.add_right_comm
        (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
            * (p2 * mc psi (s + 2))) (List.range (j + 1))
          + (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
              * (p1 * mc psi (s + 1))) (List.range (j + 2))
            + ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
              * (p0 * mc psi s)) (List.range (j + 2))))
        (BPair.ofNat (ground.pasc (j + 1) (j + 1))
          * (p2 * mc psi (j + 1 + 2)))
        (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (β * mrho psi t))) (List.range (j + 2)))]
    rw [BPair.add_assoc
        (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
          * (p2 * mc psi (s + 2))) (List.range (j + 1)))
        (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
            * (p1 * mc psi (s + 1))) (List.range (j + 2))
          + ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
            * (p0 * mc psi s)) (List.range (j + 2)))
        (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (β * mrho psi t))) (List.range (j + 2)))]
    rw [BPair.add_assoc
        (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
          * (p1 * mc psi (s + 1))) (List.range (j + 2)))
        (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
          * (p0 * mc psi s)) (List.range (j + 2)))
        (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
          * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
            * (β * mrho psi t))) (List.range (j + 2)))]
  have hcanc := BPair.add_cancel
    (BPair.oneValue_trans (BPair.oneValue_symm hLHS)
      (BPair.oneValue_trans
        (fbd_row_succ a b psi p2 p1 p0 β h hp hb j) hRHS))
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (dotP_rowAcc _ _ _ (fbdTermsSucc_keys K j p2 p1 p0 β hj)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr ?_ (BPair.oneValue_refl BPair.unit))
    (BPair.add_unit _)
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_of_eq (congrArg (fun z => β * z)
        (momVec_rho psi K (j + 1)
          (hcK (j + 1) (Nat.le_succ (j + 1))))))
      (BPair.oneValue_trans
        (BPair.oneValue_trans
          (ground.famFold_append_ov ground.bpairFoldLaws _ _ _)
          (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.oneValue_trans
              (ground.famFold_append_ov ground.bpairFoldLaws _ _ _)
              (BPair.add_congr (BPair.oneValue_refl _)
                (BPair.oneValue_trans
                  (ground.famFold_append_ov ground.bpairFoldLaws _ _ _)
                  (BPair.add_congr (BPair.oneValue_refl _)
                    (BPair.oneValue_trans
                      (ground.famFold_append_ov ground.bpairFoldLaws _ _ _)
                      (BPair.add_congr (BPair.oneValue_refl _)
                        (BPair.oneValue_trans
                          (ground.famFold_append_ov
                            ground.bpairFoldLaws _ _ _)
                          (BPair.add_congr (BPair.oneValue_refl _)
                            (ground.famFold_append_ov
                              ground.bpairFoldLaws _ _ _)))))))))))
        (BPair.add_congr hA2
          (BPair.add_congr hB1
            (BPair.add_congr hC0
              (BPair.add_congr hG2
                (BPair.add_congr hG1
                  (BPair.add_congr hG0 hRF)))))))) ?_
  refine BPair.swap_of_add_unit ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (show
      (β * mrho psi (j + 1)
        + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)))) (List.range (j + 1))
          + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p2 + p1) * mc psi (t + 1)))) (List.range (j + 2))
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2))
              + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))).swap
        + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))).swap
          + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))).swap
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))).swap)))))))
      + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * edgeAt psi t))) (List.range (j + 2))
      = ((β * mrho psi (j + 1)
          + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)))) (List.range (j + 1))
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p2 + p1) * mc psi (t + 1)))) (List.range (j + 2))
              + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2)))))
        + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * edgeAt psi t))) (List.range (j + 2)))
        + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))).swap
        + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))).swap
          + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))).swap
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))).swap))) from by
      rw [← BPair.add_assoc
          (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p2 + p1) * mc psi (t + 1)))) (List.range (j + 2)))
          (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2)))
          ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))).swap
        + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))).swap
          + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))).swap
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))).swap))),
        ← BPair.add_assoc
          (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)))) (List.range (j + 1)))
          (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p2 + p1) * mc psi (t + 1)))) (List.range (j + 2))
            + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2)))
          ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))).swap
        + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))).swap
          + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))).swap
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))).swap))),
        ← BPair.add_assoc (β * mrho psi (j + 1))
          (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)))) (List.range (j + 1))
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p2 + p1) * mc psi (t + 1)))) (List.range (j + 2))
              + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2))))
          ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))).swap
        + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))).swap
          + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))).swap
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))).swap))),
        BPair.add_right_comm
          (β * mrho psi (j + 1)
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (p2 * mc psi (t + 2)))) (List.range (j + 1))
              + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p2 + p1) * mc psi (t + 1)))) (List.range (j + 2))
                + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * ((p2 + p1 + p0) * mc psi t))) (List.range (j + 2)))))
          ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))).swap
        + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))).swap
          + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))).swap
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))).swap)))
          (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * edgeAt psi t))) (List.range (j + 2)))])) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr hcanc (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq
    (BPair.add_comm
      (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))
        + (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))
          + (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))
            + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2)))))
      ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))).swap
        + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))).swap
          + ((ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))).swap
            + (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))).swap))))) ?_
  exact BPair.swap_add_null (BPair.oneValue_refl
    (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p2 * mc psi (s + 2))) (List.range (j + 1))
        + (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p1 * mc psi (s + 1))) (List.range (j + 2))
          + (ground.bsum (fun s => BPair.ofNat (ground.pasc (j + 1) s)
        * (p0 * mc psi s)) (List.range (j + 2))
            + ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
        * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
          * (β * mrho psi t))) (List.range (j + 2))))))

/-- Two entrywise reads at one leading count join at the lists' own
join. -/
private theorem polyOV_append : ∀ (u u' w w' : List BPair),
    u.length = u'.length →
    poly.oneValue u u' → poly.oneValue w w' →
    poly.oneValue (u ++ w) (u' ++ w')
  | [], [], _, _, _, _, hw => hw
  | [], _ :: _, _, _, hl, _, _ => Nat.noConfusion hl
  | _ :: _, [], _, _, hl, _, _ => Nat.noConfusion hl
  | _ :: u, _ :: u', w, w', hl, hu, hw =>
    ⟨hu.1, polyOV_append u u' w w' (Nat.succ.inj hl) hu.2 hw⟩

/-- A mapped row family's action reads the mapped values, one row
read per key. -/
private theorem matVec_mapRange (mk : Nat → List BPair)
    (rhs : Nat → BPair) (v : List BPair) :
    ∀ m : Nat, (∀ i, i < m → (elim.dotN (mk i) v).oneValue (rhs i)) →
      poly.oneValue (elim.matVec ((List.range m).map mk) v)
        ((List.range m).map rhs)
  | 0, _ => trivial
  | m + 1, h => by
    rw [ground.range_succ m, ground.map_append, ground.map_append,
      elim.matVec_append]
    refine polyOV_append _ _ _ _ ?_
      (matVec_mapRange mk rhs v m
        (fun i hi => h i (Nat.lt_succ_of_lt hi)))
      ⟨h m (Nat.lt_succ_self m), trivial⟩
    rw [elim.matVec_length, ground.length_mapRange,
      ground.length_mapRange]

/-- The joined row list's entry reads split at the join, the
action's own map. -/
private theorem mapDotN_append (v : List BPair) :
    ∀ A B : elim.Mat,
      (A ++ B).map (fun r => elim.dotN r v)
        = A.map (fun r => elim.dotN r v)
          ++ B.map (fun r => elim.dotN r v)
  | [], _ => rfl
  | r :: A, B =>
    congrArg (fun t => elim.dotN r v :: t) (mapDotN_append v A B)

/-- A mapped row family reads a stated width at every row. -/
private theorem rowsLen_mapRange {n : Nat} (mk : Nat → List BPair) :
    ∀ m : Nat, (∀ i, (mk i).length = n) →
      elim.rowsLen n ((List.range m).map mk)
  | 0, _ => trivial
  | m + 1, h => by
    rw [ground.range_succ m, ground.map_append]
    exact elim.rowsLen_append _ (rowsLen_mapRange mk m h) ⟨h m, trivial⟩

/-- Clause (ii)'s square system at a stated degree: the four base
rows, the fold identities' rows at monomial weights through the
degree, and the reduced second fold's rows through the degree, one
row list at the truncated moment vector's width, its entries the
profile and bond data at the Pascal reads. -/
def momSys (K : Nat) (p2 p1 p0 β : BPair) : elim.Mat :=
  rowAcc (K + 1 + (K + 1 + 1)) [(0, BPair.ofPos Pos.one)]
    :: rowAcc (K + 1 + (K + 1 + 1)) [(1, BPair.ofPos Pos.one)]
    :: rowAcc (K + 1 + (K + 1 + 1)) [(K + 1, BPair.ofPos Pos.one)]
    :: rowAcc (K + 1 + (K + 1 + 1))
        [(K + 1 + (K + 1), BPair.ofPos Pos.one)]
    :: ((List.range (K - 1)).map (fun j =>
        rowAcc (K + 1 + (K + 1 + 1)) (faTerms K j p2 p1 p0 β))
      ++ (rowAcc (K + 1 + (K + 1 + 1)) (fbdTermsZero K p2 p1 p0 β)
        :: (List.range (K - 1)).map (fun j =>
            rowAcc (K + 1 + (K + 1 + 1)) (fbdTermsSucc K j p2 p1 p0 β))))

/-- The system's data side: the four base reads, the fold rows'
unit reads, and the reduced rows' far-edge reads, the balance
partners at the Pascal edge folds. -/
def momRhs (psi : List BPair) (β : BPair) (K : Nat) : List BPair :=
  mrho psi 0 :: mrho psi 1 :: mc psi 0 :: bSq psi
    :: ((List.range (K - 1)).map (fun _ => BPair.unit)
      ++ ((β * edgeAt psi 0).swap
        :: (List.range (K - 1)).map (fun j =>
            (ground.bsum (fun t => BPair.ofNat (ground.pasc (j + 1) t)
              * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
                * (β * edgeAt psi t))) (List.range (j + 2))).swap)))

/-- The system's row count is the moment vector's width. -/
theorem momSys_len (K : Nat) (p2 p1 p0 β : BPair) (hK : 1 ≤ K) :
    (momSys K p2 p1 p0 β).length = K + 1 + (K + 1 + 1) := by
  obtain ⟨K1, hK1⟩ := Nat.le.dest hK
  show ((List.range (K - 1)).map (fun j =>
      rowAcc (K + 1 + (K + 1 + 1)) (faTerms K j p2 p1 p0 β))
    ++ (rowAcc (K + 1 + (K + 1 + 1)) (fbdTermsZero K p2 p1 p0 β)
      :: (List.range (K - 1)).map (fun j =>
        rowAcc (K + 1 + (K + 1 + 1))
          (fbdTermsSucc K j p2 p1 p0 β)))).length + 1 + 1 + 1 + 1
    = K + 1 + (K + 1 + 1)
  rw [ground.length_append, ground.length_mapRange]
  show K - 1 + (((List.range (K - 1)).map (fun j =>
      rowAcc (K + 1 + (K + 1 + 1))
        (fbdTermsSucc K j p2 p1 p0 β))).length + 1) + 1 + 1 + 1 + 1
    = K + 1 + (K + 1 + 1)
  rw [ground.length_mapRange, ← hK1, ground.addSubSelfL 1 K1]
  rw [Nat.add_comm 1 K1]
  show K1 + K1 + 1 + 1 + 1 + 1 + 1 = K1 + 1 + 1 + (K1 + 1 + 1 + 1)
  rw [Nat.succ_add (K1 + 1) (K1 + 1 + 1 + 1),
    Nat.succ_add K1 (K1 + 1 + 1 + 1)]
  rfl

/-- The system's rows read the moment vector's width. -/
theorem momSys_rowsLen (K : Nat) (p2 p1 p0 β : BPair) :
    elim.rowsLen (K + 1 + (K + 1 + 1)) (momSys K p2 p1 p0 β) := by
  refine ⟨rowAcc_len _ _, rowAcc_len _ _, rowAcc_len _ _,
    rowAcc_len _ _, ?_⟩
  refine elim.rowsLen_append _
    (rowsLen_mapRange _ (K - 1) (fun _ => rowAcc_len _ _)) ?_
  exact ⟨rowAcc_len _ _,
    rowsLen_mapRange _ (K - 1) (fun _ => rowAcc_len _ _)⟩

/-- The system's read at the truncated moment vector: the four base
rows read the base data, the fold identities' rows the sum's unit,
and the reduced second fold's rows the far edge's balance partners,
`fa_row` and the reduced rows withdrawing across the accumulated
rows — the identities at weights through the stated degree with the
base reads, one square linear system for the truncated moment
vector. -/
theorem momSys_read (a b psi : List BPair) (p2 p1 p0 β : BPair)
    (K : Nat) (h : recRead a b psi) (hp : diagProf a p2 p1 p0)
    (hb : constBond b β) (hK : 1 ≤ K) :
    poly.oneValue (elim.matVec (momSys K p2 p1 p0 β) (momVec psi K))
      (momRhs psi β K) := by
  obtain ⟨K1, hK1⟩ := Nat.le.dest hK
  have hjb : ∀ i : Nat, i < K - 1 → i + 2 ≤ K := fun i hi => by
    rw [← hK1, ground.addSubSelfL 1 K1] at hi
    rw [← hK1, Nat.add_comm 1 K1]
    exact Nat.succ_le_succ hi
  have hKn : K + 1 + (K + 1) < K + 1 + (K + 1 + 1) :=
    Nat.add_lt_add_left (Nat.lt_succ_self (K + 1)) (K + 1)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact BPair.oneValue_trans
      (baseRow_read (momVec psi K) (K + 1 + (K + 1 + 1)) 0
        (Nat.lt_of_lt_of_le (Nat.succ_pos K)
          (Nat.le_add_right (K + 1) (K + 1 + 1))))
      (BPair.oneValue_of_eq (momVec_rho psi K 0 (Nat.succ_pos K)))
  · exact BPair.oneValue_trans
      (baseRow_read (momVec psi K) (K + 1 + (K + 1 + 1)) 1
        (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hK)
          (Nat.le_add_right (K + 1) (K + 1 + 1))))
      (BPair.oneValue_of_eq
        (momVec_rho psi K 1 (Nat.lt_succ_of_le hK)))
  · refine BPair.oneValue_trans
      (baseRow_read (momVec psi K) (K + 1 + (K + 1 + 1)) (K + 1)
        (Nat.lt_of_lt_of_le
          (Nat.lt_succ_of_le (Nat.le_add_right (K + 1) 0))
          (Nat.add_le_add_left
            (Nat.succ_le_succ (Nat.zero_le (K + 1))) (K + 1)))) ?_
    refine BPair.oneValue_of_eq ?_
    show ground.getAt BPair.unit (momVec psi K) (K + 1 + 0) = mc psi 0
    exact momVec_c psi K 0 (Nat.succ_pos K)
  · exact BPair.oneValue_trans
      (baseRow_read (momVec psi K) (K + 1 + (K + 1 + 1))
        (K + 1 + (K + 1)) hKn)
      (BPair.oneValue_of_eq (momVec_b psi K))
  · rw [mapDotN_append (momVec psi K)]
    refine polyOV_append _ _ _ _ ?_
      (matVec_mapRange _ (fun _ => BPair.unit) (momVec psi K) (K - 1)
        (fun i hi => faRow_read a b psi p2 p1 p0 β K i h hp hb
          (hjb i hi))) ?_
    · rw [ground.length_map, ground.length_mapRange,
        ground.length_mapRange]
    exact ⟨fbdRowZero_read a b psi p2 p1 p0 β K h hp hb hK,
      matVec_mapRange _
        (fun j => (ground.bsum (fun t =>
          BPair.ofNat (ground.pasc (j + 1) t)
            * (ground.bpow (BPair.ofNat 2) (j + 1 - t)
              * (β * edgeAt psi t))) (List.range (j + 2))).swap)
        (momVec psi K) (K - 1)
        (fun i hi => fbdRowSucc_read a b psi p2 p1 p0 β K i h hp hb
          (hjb i hi))⟩

/-- The tail fold: the square stream's summands from a stated depth
on, one summand per key at or beyond that depth. -/
def tailStream (psi : List BPair) (W : Nat → BPair) (M : Nat) : BPair :=
  ground.bsum (fun t => W (M + t)
    * (ground.getAt BPair.unit psi (M + t)
      * ground.getAt BPair.unit psi (M + t)))
    (List.range (psi.length - M))

/-- The square stream splits at a stated depth into the fold over
the keys below it and the tail from it on, the beyond-length keys
vacant. -/
theorem tail_split (psi : List BPair) (W : Nat → BPair) (M : Nat) :
    (rhoStream psi W).oneValue
      (ground.bsum (fun k => W k
        * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
        (List.range M)
        + tailStream psi W M) := by
  cases Nat.le_total M psi.length with
  | inl hM =>
    have hg : M + (psi.length - M) = psi.length := ground.natAddSubCancel hM
    show (ground.bsum (fun k => W k
        * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
        (List.range psi.length)).oneValue _
    rw [← hg, ground.range_split M (psi.length - M)]
    refine BPair.oneValue_trans
      (ground.famFold_append_ov ground.bpairFoldLaws _ (List.range M) _) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    show (ground.bsum (fun k => W k
        * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
        ((List.range (psi.length - M)).map (fun c => M + c))).oneValue
      (tailStream psi W M)
    rw [ground.bsum_map]
    exact BPair.oneValue_refl _
  | inr hM =>
    have hvac : psi.length - M = 0 := ground.subLe psi.length M hM
    have hg : psi.length + (M - psi.length) = M := ground.natAddSubCancel hM
    show (ground.bsum (fun k => W k
        * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
        (List.range psi.length)).oneValue
      (ground.bsum (fun k => W k
        * (ground.getAt BPair.unit psi k * ground.getAt BPair.unit psi k))
        (List.range M)
        + ground.bsum (fun t => W (M + t)
          * (ground.getAt BPair.unit psi (M + t)
            * ground.getAt BPair.unit psi (M + t)))
          (List.range (psi.length - M)))
    rw [hvac, ← hg, ground.range_split psi.length (M - psi.length)]
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (ground.famFold_append_ov ground.bpairFoldLaws _
        (List.range psi.length) _)
      (BPair.oneValue_refl BPair.unit)) ?_
    refine BPair.oneValue_trans (BPair.add_unit _) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.oneValue_refl _) ?_) (BPair.add_unit _)
    show (ground.bsum (fun k => W k
        * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi k))
        ((List.range (M - psi.length)).map
          (fun c => psi.length + c))).oneValue BPair.unit
    rw [ground.bsum_map]
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _ (fun _ => BPair.unit)
        (List.range (M - psi.length)) (fun c _ => ?_)) ?_
    · refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (W (psi.length + c)))
          (BPair.mul_congr
            (BPair.oneValue_of_eq
              (ground.getAt_over BPair.unit psi (psi.length + c)
                (Nat.le_add_right psi.length c)))
            (BPair.oneValue_of_eq
              (ground.getAt_over BPair.unit psi (psi.length + c)
                (Nat.le_add_right psi.length c))))) ?_
      exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.unit_mul BPair.unit))
        (BPair.mul_unit (W (psi.length + c)))
    · exact ground.foldB_nullRange (fun _ => BPair.unit)
        (M - psi.length) (fun _ _ => BPair.oneValue_refl _)

/-- The tail list at a family: the members from a stated key along a
stated span, one per key. -/
private def wsOf (F : Nat → BPair) : Nat → Nat → List BPair
  | 0, M => [F M]
  | T + 1, M => F M :: wsOf F T (M + 1)

/-- The tail list reads the rate's decay at the family's own
steps. -/
private theorem wsOf_rate (F : Nat → BPair) (qn qd : Pos) :
    ∀ (T M : Nat),
      (∀ m : Nat, M ≤ m → m < M + T →
        (F (m + 1)).scale qd ≤ (F m).scale qn) →
      ground.widthRate qn qd (wsOf F T M)
  | 0, _, _ => trivial
  | T + 1, M, h => by
    have hs : (M + 1) + T = M + (T + 1) := Nat.succ_add M T
    have hd : (F (M + 1)).scale qd ≤ (F M).scale qn :=
      h M (Nat.le_refl M)
        (Nat.lt_succ_of_le (Nat.le_add_right M T))
    have ht : ground.widthRate qn qd (wsOf F T (M + 1)) :=
      wsOf_rate F qn qd T (M + 1) (fun m hm hmT =>
        h m (Nat.le_of_succ_le hm) (by rw [← hs]; exact hmT))
    cases T with
    | zero => exact ⟨hd, trivial⟩
    | succ T' => exact ⟨hd, ht⟩

/-- The tail list's last member is the family's at the span's
end. -/
private theorem wsOf_last (F : Nat → BPair) :
    ∀ (T M : Nat), BPair.unit ≤ F (M + T) →
      ground.unitLast (wsOf F T M)
  | 0, M, h => h
  | T + 1, M, h => by
    have ht : ground.unitLast (wsOf F T (M + 1)) :=
      wsOf_last F T (M + 1)
        (by rw [Nat.succ_add M T]; exact h)
    cases T with
    | zero => exact ht
    | succ T' => exact ht

/-- The tail list folds as the family's own range fold. -/
private theorem wsOf_sum (F : Nat → BPair) :
    ∀ (T M : Nat),
      (ground.bsum id (wsOf F T M)).oneValue
        (ground.bsum (fun t => F (M + t)) (List.range (T + 1)))
  | 0, M =>
    BPair.oneValue_symm (BPair.oneValue_of_eq
      (ground.foldB_range_cons (fun t => F (M + t)) 0))
  | T + 1, M => by
    show (F M + ground.bsum id (wsOf F T (M + 1))).oneValue _
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (F M))
        (BPair.oneValue_trans (wsOf_sum F T (M + 1))
          (ground.foldB_congr_members _
            (fun j => F (M + (j + 1))) (List.range (T + 1))
            (fun j _ => BPair.oneValue_of_eq
              (congrArg F (Nat.succ_add M j)))))) ?_
    exact BPair.oneValue_symm (BPair.oneValue_of_eq
      (ground.foldB_range_cons (fun t => F (M + t)) (T + 1)))

/-- The tail's cap: a family whose members decay at the pair
`qn : qd` along a stated span, its last member at or above the
sum's unit, folds at the pair's gap to at or below its first member
at the pair's second member — `ground.widthSum`'s telescope at the
span's own list. -/
theorem tail_capped (F : Nat → BPair) (M T : Nat)
    (qn g qd : Pos) (hg : qn + g = qd)
    (hlast : BPair.unit ≤ F (M + T))
    (hstep : ∀ m : Nat, M ≤ m → m < M + T →
      (F (m + 1)).scale qd ≤ (F m).scale qn) :
    (ground.bsum (fun t => F (M + t)) (List.range (T + 1))).scale g
      ≤ (F M).scale qd := by
  have hs := ground.widthSum qn g qd hg (wsOf F T M)
    (wsOf_rate F qn qd T M hstep) (wsOf_last F T M hlast)
  have hh : ground.getAt BPair.unit (wsOf F T M) 0 = F M := by
    cases T with
    | zero => rfl
    | succ T' => rfl
  rw [hh] at hs
  exact ground.leB_congr_left (BPair.scale_congr g (wsOf_sum F T M)) hs

/-- A datum at or above the sum's unit grows with its clearing: the
gap's own rescaling joins the read as a summand. -/
private theorem scaleWiden {x : BPair} (hx : BPair.unit ≤ x) {a b c : Pos}
    (h : a + b = c) : x.scale b ≤ x.scale c :=
  ground.leB_congr_right
    (BPair.oneValue_of_eq
      ((BPair.scale_addW x a b).symm.trans (congrArg (fun w => x.scale w) h)))
    (ground.leB_congr_left (BPair.unit_add (x.scale b))
      (ground.leB_add (ground.unitLeScale a hx) (ground.leB_refl (x.scale b))))

/-- Every member along a stated span sits at or below the span's
first member at the pair's second member, the decay composed along
the keys between and each step's member widened at the gap. -/
private theorem edgeCapGo (F : Nat → BPair) (M m : Nat)
    (qn g qd : Pos) (hg : qn + g = qd)
    (hpos : ∀ k : Nat, M ≤ k → k ≤ m → BPair.unit ≤ F k)
    (hstep : ∀ k : Nat, M ≤ k → k < m →
      (F (k + 1)).scale qd ≤ (F k).scale qn) :
    ∀ i : Nat, M + i ≤ m → (F (M + i)).scale qd ≤ (F M).scale qd
  | 0, _ => ground.leB_refl ((F M).scale qd)
  | i + 1, hi =>
    ground.leB_trans
      (ground.leB_trans
        (hstep (M + i) (Nat.le_add_right M i) hi)
        (scaleWiden
          (hpos (M + i) (Nat.le_add_right M i)
            (Nat.le_of_succ_le hi))
          ((ground.add_comm g qn).trans hg)))
      (edgeCapGo F M m qn g qd hg hpos hstep i
        (Nat.le_of_succ_le hi))

/-- The far member's read: a member at or beyond the step key sits,
at the pair's gap, at or below the key's member at the pair's second
member. -/
theorem edge_capped (F : Nat → BPair) (M m : Nat) (hMm : M ≤ m)
    (qn g qd : Pos) (hg : qn + g = qd)
    (hpos : ∀ k : Nat, M ≤ k → k ≤ m → BPair.unit ≤ F k)
    (hstep : ∀ k : Nat, M ≤ k → k < m →
      (F (k + 1)).scale qd ≤ (F k).scale qn) :
    (F m).scale g ≤ (F M).scale qd := by
  obtain ⟨i, hi⟩ := Nat.le.dest hMm
  rw [← hi]
  refine ground.leB_trans
    (scaleWiden (hpos (M + i) (Nat.le_add_right M i)
      (by rw [hi]; exact Nat.le_refl m)) hg) ?_
  exact edgeCapGo F M m qn g qd hg hpos hstep i
    (by rw [hi]; exact Nat.le_refl m)

/-- Clause (iii)'s priced tail: at the certificates' decay of the
weighted squares from a stated depth on and the weights' reads at
or above the sum's unit there, the square stream's tail sits, at
the decay pair's gap, at or below the depth's own weighted square
at the pair's second member. -/
theorem tail_price (psi : List BPair) (W : Nat → BPair) (M : Nat)
    (qn g qd : Pos) (hg : qn + g = qd)
    (hW : ∀ m : Nat, M ≤ m → BPair.unit ≤ W m)
    (hstep : ∀ m : Nat, M ≤ m → m + 1 < psi.length →
      (W (m + 1) * (ground.getAt BPair.unit psi (m + 1)
          * ground.getAt BPair.unit psi (m + 1))).scale qd
        ≤ (W m * (ground.getAt BPair.unit psi m
          * ground.getAt BPair.unit psi m)).scale qn) :
    (tailStream psi W M).scale g
      ≤ (W M * (ground.getAt BPair.unit psi M
          * ground.getAt BPair.unit psi M)).scale qd := by
  have hpos : ∀ m : Nat, M ≤ m → BPair.unit ≤ W m
      * (ground.getAt BPair.unit psi m
        * ground.getAt BPair.unit psi m) :=
    fun m hm =>
      ground.leB_congr_left (BPair.unit_mul BPair.unit)
        (ground.leB_mul_mono (ground.leB_refl BPair.unit)
          (hW m hm) (hW m hm)
          (ground.unitLeSq (ground.getAt BPair.unit psi m)))
  cases hT : psi.length - M with
  | zero =>
    show (ground.bsum (fun t => W (M + t)
        * (ground.getAt BPair.unit psi (M + t)
          * ground.getAt BPair.unit psi (M + t)))
        (List.range (psi.length - M))).scale g ≤ _
    rw [hT]
    exact ground.leB_congr_left (ground.unitScale g)
      (ground.unitLeScale qd (hpos M (Nat.le_refl M)))
  | succ T =>
    have hMle : M ≤ psi.length := by
      cases Nat.le_total M psi.length with
      | inl h => exact h
      | inr h =>
        exact absurd ((ground.subLe psi.length M h).symm.trans hT)
          (fun he => Nat.noConfusion he)
    have hlen : M + (T + 1) = psi.length := by
      rw [← ground.natAddSubCancel hMle, hT]
    show (ground.bsum (fun t => W (M + t)
        * (ground.getAt BPair.unit psi (M + t)
          * ground.getAt BPair.unit psi (M + t)))
        (List.range (psi.length - M))).scale g ≤ _
    rw [hT]
    refine tail_capped
      (fun m => W m * (ground.getAt BPair.unit psi m
        * ground.getAt BPair.unit psi m)) M T qn g qd hg
      (hpos (M + T) (Nat.le_add_right M T))
      (fun m hm hmT => hstep m hm ?_)
    rw [← hlen]
    exact Nat.succ_le_succ hmT

/-- Clause (ii)'s far-edge price: the far edge's read at a monomial
weight sits, at the decay pair's gap, at or below a stated depth's
weighted square at the pair's second member, the decay composed
along the keys between. -/
theorem edge_price (psi : List BPair) (t M : Nat)
    (hM : M + 1 ≤ psi.length)
    (qn g qd : Pos) (hg : qn + g = qd)
    (hstep : ∀ k : Nat, M ≤ k → k + 1 + 1 ≤ psi.length →
      (ground.bpow (BPair.ofNat (k + 1)) t
          * (ground.getAt BPair.unit psi (k + 1)
            * ground.getAt BPair.unit psi (k + 1))).scale qd
        ≤ (ground.bpow (BPair.ofNat k) t
          * (ground.getAt BPair.unit psi k
            * ground.getAt BPair.unit psi k)).scale qn) :
    (edgeAt psi t).scale g
      ≤ (ground.bpow (BPair.ofNat M) t
        * (ground.getAt BPair.unit psi M
          * ground.getAt BPair.unit psi M)).scale qd := by
  obtain ⟨c, hc⟩ := Nat.le.dest hM
  have hlen : psi.length = (M + c) + 1 :=
    hc.symm.trans (Nat.succ_add M c)
  have hend : psi.length - 1 = M + c := by
    rw [hlen]
    exact (Nat.succ_sub_succ (M + c) 0).trans (Nat.sub_zero (M + c))
  have hpos : ∀ k : Nat, M ≤ k → k ≤ psi.length - 1 →
      BPair.unit ≤ ground.bpow (BPair.ofNat k) t
        * (ground.getAt BPair.unit psi k
          * ground.getAt BPair.unit psi k) :=
    fun k _ _ =>
      ground.leB_congr_left (BPair.unit_mul BPair.unit)
        (ground.leB_mul_mono (ground.leB_refl BPair.unit)
          (ground.unitLeBpow (ground.unitLeOfNat k) t)
          (ground.unitLeBpow (ground.unitLeOfNat k) t)
          (ground.unitLeSq (ground.getAt BPair.unit psi k)))
  show (ground.bpow (BPair.ofNat (psi.length - 1)) t
      * (ground.getAt BPair.unit psi (psi.length - 1)
        * ground.getAt BPair.unit psi (psi.length - 1))).scale g ≤ _
  refine edge_capped
    (fun k => ground.bpow (BPair.ofNat k) t
      * (ground.getAt BPair.unit psi k
        * ground.getAt BPair.unit psi k))
    M (psi.length - 1)
    (by rw [hend]; exact Nat.le_add_right M c)
    qn g qd hg hpos
    (fun k hk hkm => hstep k hk ?_)
  rw [hlen]
  refine Nat.succ_le_succ ?_
  rw [hend] at hkm
  exact hkm

/-- The per-step decay: the transfer certificate at the degree's
clearing pair against the turning read at the stated degree reads one
step of the decay, the shared clearing `ln·ln·ld·ld` withdrawn from
both sides, every compared datum at or beyond the sum's unit, the
clause's stated gram side. -/
theorem turn_step (x y u v : BPair) (ln ld qn qd : Pos)
    (hcert : x.scale (ld * ld) ≤ y.scale (ln * ln))
    (hturn : u.scale (ln * ln * qd) ≤ v.scale (ld * ld * qn))
    (hx : BPair.unit ≤ x) (hu : BPair.unit ≤ u)
    (hy : BPair.unit ≤ y) (hv : BPair.unit ≤ v) :
    (u * x).scale qd ≤ (v * y).scale qn := by
  have hprod : u.scale (ln * ln * qd) * x.scale (ld * ld)
      ≤ v.scale (ld * ld * qn) * y.scale (ln * ln) :=
    ground.leB_trans
      (ground.leB_mul_mono (ground.unitLeScale (ld * ld) hx)
        (ground.unitLeScale (ln * ln * qd) hu)
        (ground.leB_refl (u.scale (ln * ln * qd))) hcert)
      (ground.leB_mul_mono (ground.unitLeScale (ln * ln) hy)
        (ground.unitLeScale (ld * ld * qn) hv) hturn
        (ground.leB_refl (y.scale (ln * ln))))
  have e1 : ln * ln * qd * (ld * ld) = qd * (ln * ln * (ld * ld)) := by
    rw [ground.mul_right_comm (ln * ln) qd (ld * ld),
      ground.mul_comm (ln * ln * (ld * ld)) qd]
  have e2 : ld * ld * qn * (ln * ln) = qn * (ln * ln * (ld * ld)) := by
    rw [ground.mul_right_comm (ld * ld) qn (ln * ln),
      ground.mul_comm (ld * ld * (ln * ln)) qn,
      ground.mul_comm (ld * ld) (ln * ln)]
  refine ground.leB_of_scale (w := ln * ln * (ld * ld)) ?_
  rw [BPair.scale_scale, BPair.scale_scale, ← e1, ← e2,
    BPair.scale_mul, BPair.scale_mul]
  exact hprod

/-! Clause (iv), the scale comparison: the adjugate's action against
a list's own action at a vector, and the two solved systems' reads at
one shape. -/

/-- The adjugate's action against a list's own action pins a vector
at the determinant's scale: the adjugate identity's action read
(`inertia.adjM_col_read`) at the vector, the determinant's scaled
identity acting as the scale itself (`def:elim`'s adjugate identity
read at a vector). -/
theorem det_pin {n : Nat} (S : elim.Mat) (hsq : elim.sqAt S n)
    (z : List BPair) (hz : z.length = n) :
    poly.oneValue (elim.matVec (elim.matMul (elim.adjM S) S) z)
      (elim.vecScale (elim.detL S) z) :=
  poly.oneValue_trans
    (elim.matVec_matOne _ _ z (inertia.adjM_col_read S hsq))
    (inertia.scaleId_act (elim.detL S) n z hz)

/-- Two solved systems at one shape compare at the first
determinant's scale: at the coefficients' site datum at the shared
shape and the data's difference at the shared width, the solutions'
difference at that scale reads the adjugate's action at the data
difference joined to the site difference's own action, one read per
moment. -/
theorem scale_compare {n : Nat} (S S' D : elim.Mat)
    (hsq : elim.sqAt S n) (hsq' : elim.sqAt S' n) (hsqD : elim.sqAt D n)
    (hD : elim.matOneValue S (elim.matAdd S' D))
    (v v' w w' dw : List BPair)
    (hv : poly.oneValue (elim.matVec S v) w)
    (hv' : poly.oneValue (elim.matVec S' v') w')
    (hdw : poly.oneValue w (poly.add w' dw))
    (hlv : v.length = n) (hlv' : v'.length = n) (hldw : dw.length = n) :
    poly.oneValue
      (elim.vecScale (elim.detL S)
        (elim.vecAdd v (v'.map BPair.swap)))
      (elim.matVec (elim.adjM S)
        (elim.vecAdd dw ((elim.matVec D v').map BPair.swap))) := by
  have hSl : S.length = n := elim.sqAt_len hsq
  have hSr : elim.rowsLen n S := elim.rowsLen_of_sqAt hsq
  have hS'r : elim.rowsLen n S' := elim.rowsLen_of_sqAt hsq'
  have hDr : elim.rowsLen n D := elim.rowsLen_of_sqAt hsqD
  have hDl : D.length = n := elim.sqAt_len hsqD
  have hswl : (v'.map BPair.swap).length = n :=
    (ground.length_map BPair.swap v').trans hlv'
  have hzl : (elim.vecAdd v (v'.map BPair.swap)).length = n :=
    elim.length_vecAdd v _ n hlv hswl
  have hSv : (elim.matVec S v).length = n :=
    (elim.matVec_length S v).trans hSl
  have hSv' : (elim.matVec S v').length = n :=
    (elim.matVec_length S v').trans hSl
  have hS'v' : (elim.matVec S' v').length = n :=
    (elim.matVec_length S' v').trans (elim.sqAt_len hsq')
  have hDv' : (elim.matVec D v').length = n :=
    (elim.matVec_length D v').trans hDl
  have hsplit : poly.oneValue (elim.matVec S v')
      (elim.vecAdd (elim.matVec S' v') (elim.matVec D v')) :=
    poly.oneValue_trans (elim.matVec_matOne S (elim.matAdd S' D) v' hD)
      (elim.matVec_add_free n S' D v' hS'r hDr)
  have hact : poly.oneValue
      (elim.matVec S (elim.vecAdd v (v'.map BPair.swap)))
      (elim.vecAdd dw ((elim.matVec D v').map BPair.swap)) := by
    refine poly.oneValue_trans
      (elim.matVec_vecAdd_free S v (v'.map BPair.swap)
        (hlv.trans hswl.symm)) ?_
    rw [elim.matVec_swapArg v' S]
    refine poly.oneValue_of_entries _ _ ?_ ?_
    · rw [elim.length_vecAdd (elim.matVec S v) _ n hSv
          ((ground.length_map BPair.swap _).trans hSv'),
        elim.length_vecAdd dw _ n hldw
          ((ground.length_map BPair.swap _).trans hDv')]
    · intro t ht
      rw [elim.length_vecAdd (elim.matVec S v) _ n hSv
          ((ground.length_map BPair.swap _).trans hSv')] at ht
      rw [elim.getAt_vecAdd (elim.matVec S v) _ t
          (by rw [hSv]; exact ht)
          (by rw [ground.length_map, hSv']; exact ht),
        elim.getAt_vecAdd dw _ t (by rw [hldw]; exact ht)
          (by rw [ground.length_map, hDv']; exact ht),
        ground.getAt_map BPair.unit BPair.unit BPair.swap
          (elim.matVec S v') t (by rw [hSv']; exact ht),
        ground.getAt_map BPair.unit BPair.unit BPair.swap
          (elim.matVec D v') t (by rw [hDv']; exact ht)]
      have hA : (ground.getAt BPair.unit (elim.matVec S v) t).oneValue
          (ground.getAt BPair.unit w' t + ground.getAt BPair.unit dw t) :=
        BPair.oneValue_trans (poly.oneValue_getAt t hv)
          (BPair.oneValue_trans (poly.oneValue_getAt t hdw)
            (poly.getAt_add w' dw t))
      have hB : (ground.getAt BPair.unit (elim.matVec S v') t).oneValue
          (ground.getAt BPair.unit w' t
            + ground.getAt BPair.unit (elim.matVec D v') t) := by
        refine BPair.oneValue_trans (poly.oneValue_getAt t hsplit) ?_
        rw [elim.getAt_vecAdd (elim.matVec S' v') (elim.matVec D v') t
          (by rw [hS'v']; exact ht) (by rw [hDv']; exact ht)]
        exact BPair.add_congr (poly.oneValue_getAt t hv')
          (BPair.oneValue_refl _)
      refine BPair.oneValue_trans
        (BPair.add_congr hA (ground.swap_congr hB)) ?_
      rw [← BPair.swap_add, BPair.add_add_comm]
      refine BPair.oneValue_trans
        (BPair.add_congr ?_ (BPair.oneValue_refl _)) (BPair.unit_add _)
      exact BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.swap_add_null (BPair.oneValue_refl _))
  refine poly.oneValue_trans
    (poly.oneValue_symm (det_pin S hsq _ hzl)) ?_
  exact poly.oneValue_trans
    (elim.matVec_matMul (elim.adjM S) S n hSr _ hzl)
    (elim.matVec_congr (elim.adjM S) _ _ hact)

/-! Clause (v)'s datum arm: a single-region datum read is a stream
read at banded weights — the width-one datum's form read at the
chain (`lem:greenprod`(iv)) collected at the two streams — and its
scale closure is clause (iv)'s comparison at the datum fold. -/

/-- The single-region datum read: the width-one datum's form at the
ground reads the square stream at the diagonal entries' weights
joined to the doubled bond stream at the bonds', the chain form
read collected at the streams with the beyond-band weight
vacant. -/
theorem datum_read (diag off psi : List BPair)
    (hl : diag.length = psi.length)
    (ho : off.length + 1 = diag.length) :
    (inertia.quadForm
        (greenprod.assemble (diag.map (fun a => [[a]]))
          (off.map (fun b => [[b]]))) psi).oneValue
      (rhoStream psi (ground.getAt BPair.unit diag)
        + BPair.ofNat 2
          * cStream psi (ground.getAt BPair.unit off)) := by
  refine BPair.oneValue_trans
    (greenprod.chainQuad diag off psi hl ho) ?_
  refine BPair.add_congr (BPair.oneValue_refl _)
    (BPair.mul_congr (BPair.oneValue_refl _) ?_)
  exact BPair.oneValue_symm
    (ground.foldRange_le _ off.length psi.length
      (Nat.le_of_succ_le
        (Nat.le_of_eq (hl.symm.trans ho.symm).symm))
      (fun j hj => BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.oneValue_of_eq (ground.getAt_over BPair.unit off j hj)))
        (BPair.unit_mul _)))

/-- Clause (v)'s scale closure: two scales' datum reads at one
shape differ at the first determinant's scale by the elimination's
cofactor reads at the coefficient differences, the two-scale
comparison (`scale_compare`) read at the datum fold, one read per
weight vector. -/
theorem datum_close {n : Nat} (S S' D : elim.Mat)
    (hsq : elim.sqAt S n) (hsq' : elim.sqAt S' n)
    (hsqD : elim.sqAt D n)
    (hD : elim.matOneValue S (elim.matAdd S' D))
    (v v' w w' dw c : List BPair)
    (hv : poly.oneValue (elim.matVec S v) w)
    (hv' : poly.oneValue (elim.matVec S' v') w')
    (hdw : poly.oneValue w (poly.add w' dw))
    (hlv : v.length = n) (hlv' : v'.length = n)
    (hldw : dw.length = n) :
    (elim.detL S * (elim.dotP c v + (elim.dotP c v').swap)).oneValue
      (elim.dotP c
        (elim.matVec (elim.adjM S)
          (elim.vecAdd dw
            ((elim.matVec D v').map BPair.swap)))) := by
  refine BPair.oneValue_trans ?_
    (elim.dotP_oneValue_right c _ _
      (scale_compare S S' D hsq hsq' hsqD hD v v' w w' dw hv hv' hdw
        hlv hlv' hldw))
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (elim.dotP_vecScale_right c (elim.vecAdd v (v'.map BPair.swap))
      (elim.detL S)) ?_
  refine BPair.mul_congr (BPair.oneValue_refl _) ?_
  refine BPair.oneValue_trans
    (elim.dotP_vecAdd_right c v (v'.map BPair.swap)
      ((hlv.trans hlv'.symm).trans
        (ground.length_map BPair.swap v').symm)) ?_
  exact BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_of_eq (elim.dotP_swapMap c v'))

/-! Clause (v)'s width arms: a product read's two-scale width and
the assembled read's closure, both at `thm:windowsep`'s magnitude
carrier. -/

/-- A product read's two-scale width: at a cap on the second
factor's magnitude and a cap on the first factor's partner, the two
products' difference sits at or below those caps against the
factors' own widths, the identity
`xX ⊖ yY ~ X(x ⊖ y) + y(X ⊖ Y)` splitting the difference. -/
theorem prodWidth (x X y Y cX cy : BPair)
    (hcX : windowsep.mag X ≤ cX) (hcy : windowsep.mag y ≤ cy) :
    windowsep.mag (x * X + (y * Y).swap)
      ≤ cX * windowsep.mag (x + y.swap)
        + cy * windowsep.mag (X + Y.swap) := by
  have hid : (X * (x + y.swap) + y * (X + Y.swap)).oneValue
      (x * X + (y * Y).swap) := by
    rw [BPair.left_distrib X x y.swap, BPair.left_distrib y X Y.swap,
      BPair.mul_swap X y, BPair.mul_swap y Y,
      BPair.mul_comm X x, BPair.mul_comm y X,
      BPair.add_assoc (x * X) ((X * y).swap) (X * y + (y * Y).swap),
      BPair.add_comm (X * y) ((y * Y).swap)]
    exact BPair.add_congr (BPair.oneValue_refl (x * X))
      (BPair.add_swap_cancel (X * y).swap ((y * Y).swap))
  have hX : BPair.unit ≤ cX :=
    ground.leB_trans (windowsep.unitLe_mag X) hcX
  have hy : BPair.unit ≤ cy :=
    ground.leB_trans (windowsep.unitLe_mag y) hcy
  refine ground.leB_congr_left (windowsep.mag_congr hid) ?_
  refine ground.leB_trans
    (windowsep.mag_add_le (X * (x + y.swap)) (y * (X + Y.swap))) ?_
  refine ground.leB_add ?_ ?_
  · exact ground.leB_congr_left
      (BPair.oneValue_symm (windowsep.mag_mul X (x + y.swap)))
      (ground.leB_mul_mono (windowsep.unitLe_mag (x + y.swap)) hX hcX
        (ground.leB_refl _))
  · exact ground.leB_congr_left
      (BPair.oneValue_symm (windowsep.mag_mul y (X + Y.swap)))
      (ground.leB_mul_mono (windowsep.unitLe_mag (X + Y.swap)) hy hcy
        (ground.leB_refl _))

/-- The assembled read's closure: a product joined to its connected
datum, two such assemblies' difference at or below the parts' widths
against the caps on the second product factor and on the first
factor's partner, the connected data's own caps joining at the
sum. -/
theorem assemble_close (r1 r2 r1' r2' e e' c2 c1 w1 w2 ce ce' : BPair)
    (hc2 : windowsep.mag r2 ≤ c2) (hc1 : windowsep.mag r1' ≤ c1)
    (hw1 : windowsep.mag (r1 + r1'.swap) ≤ w1)
    (hw2 : windowsep.mag (r2 + r2'.swap) ≤ w2)
    (hce : windowsep.mag e ≤ ce) (hce' : windowsep.mag e' ≤ ce') :
    windowsep.mag ((r1 * r2 + e) + (r1' * r2' + e').swap)
      ≤ c2 * w1 + (c1 * w2 + (ce + ce')) := by
  have hsplit : ((r1 * r2 + (r1' * r2').swap) + (e + e'.swap)).oneValue
      ((r1 * r2 + e) + (r1' * r2' + e').swap) := by
    rw [← BPair.swap_add (r1' * r2') e',
      BPair.add_add_comm (r1 * r2) ((r1' * r2').swap) e (e'.swap),
      BPair.add_add_comm (r1 * r2) e ((r1' * r2').swap) (e'.swap)]
    exact BPair.oneValue_refl _
  have h2 : BPair.unit ≤ c2 :=
    ground.leB_trans (windowsep.unitLe_mag r2) hc2
  have h1 : BPair.unit ≤ c1 :=
    ground.leB_trans (windowsep.unitLe_mag r1') hc1
  refine ground.leB_congr_left (windowsep.mag_congr hsplit) ?_
  refine ground.leB_trans
    (windowsep.mag_add_le (r1 * r2 + (r1' * r2').swap) (e + e'.swap)) ?_
  refine ground.leB_congr_right
    (BPair.oneValue_of_eq
      (BPair.add_assoc (c2 * w1) (c1 * w2) (ce + ce'))) ?_
  refine ground.leB_add ?_ ?_
  · refine ground.leB_trans (prodWidth r1 r2 r1' r2' c2 c1 hc2 hc1) ?_
    exact ground.leB_add
      (ground.leB_mulR h2 hw1) (ground.leB_mulR h1 hw2)
  · refine ground.leB_trans (windowsep.mag_add_le e (e'.swap)) ?_
    exact ground.leB_add hce
      (ground.leB_congr_left
        (BPair.oneValue_of_eq (windowsep.mag_swap e').symm) hce')

/-! Clause (v)'s block arms: the block chain's rows folded against
the components at a stated weight family.  The folds are cleared
data — a balance datum at its stated positive clearing — joined at
the cross-multiplied numerators (`BPair.addQ`) and read at the
cross-multiplied comparison (`ground.qOneValue`), the joined
read's arithmetic `def:ground`'s own. -/

/-- The pairing against a componentwise sum splits at every pair of
widths, the longer summand's tail riding. -/
private theorem dotP_polyAdd : ∀ r u w : List BPair,
    (elim.dotP r (poly.add u w)).oneValue
      (elim.dotP r u + elim.dotP r w)
  | [], _, _ => BPair.oneValue_symm (BPair.unit_add BPair.unit)
  | a :: r, [], _ => by
      show (elim.dotP (a :: r) _).oneValue
        (elim.dotP (a :: r) [] + elim.dotP (a :: r) _)
      rw [elim.dotP_nil_right (a :: r)]
      exact BPair.oneValue_symm (BPair.unit_add _)
  | a :: r, c :: u, [] => by
      show (elim.dotP (a :: r) (c :: u)).oneValue
        (elim.dotP (a :: r) (c :: u) + elim.dotP (a :: r) [])
      rw [elim.dotP_nil_right (a :: r)]
      exact BPair.oneValue_symm (BPair.add_unit _)
  | a :: r, c :: u, b :: w => by
      show (a * (c + b) + elim.dotP r (poly.add u w)).oneValue
        (a * c + elim.dotP r u + (a * b + elim.dotP r w))
      rw [BPair.left_distrib a c b]
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl (a * c + a * b))
          (dotP_polyAdd r u w))
        (BPair.oneValue_of_eq
          (BPair.add_add_comm (a * c) (a * b)
            (elim.dotP r u) (elim.dotP r w)))

/-- The pairing against a cleared vector carries the clearing out
of the fold: the positive rescaling read entrywise as the balance
carrier's scale, the scale withdrawn through the pairing. -/
private theorem dotP_scaleQ (c : Pos) (r v : List BPair) :
    (elim.dotP r (greenprod.vecScale c v)).oneValue
      ((elim.dotP r v).scale c) :=
  BPair.oneValue_trans
    (elim.dotP_oneValue_right r _ _ (greenprod.vecScale_ofPos c v))
    (BPair.oneValue_trans (elim.dotP_vecScale_right r v (BPair.ofPos c))
      (BPair.ofPos_scale c (elim.dotP r v)))

/-- The pairing against a cleared sum reads the two pairings at the
cross-multiplied clearings. -/
private theorem dotP_vAddQ (r : List BPair) (a b : greenprod.VecQ) :
    (elim.dotP r (greenprod.vAddQ a b).1).oneValue
      ((elim.dotP r a.1).scale b.2 + (elim.dotP r b.1).scale a.2) :=
  BPair.oneValue_trans
    (dotP_polyAdd r (greenprod.vecScale b.2 a.1)
      (greenprod.vecScale a.2 b.1))
    (BPair.add_congr (dotP_scaleQ b.2 r a.1) (dotP_scaleQ a.2 r b.1))

/-- A row read against a vector at a side with unit entries: the
accumulated datum's pairing at the row's clearing joins the row
datum's pairing at the accumulator's clearing to the sum's unit. -/
private theorem rowDot (r : List BPair) (p X w : greenprod.VecQ)
    (hrow : greenprod.vOneValueQ (greenprod.vAddQ p X) w)
    (hw : poly.unitTail w.1) :
    ((elim.dotP r p.1).scale X.2
      + (elim.dotP r X.1).scale p.2).oneValue BPair.unit := by
  have hd : (elim.dotP r
      (greenprod.vecScale w.2 (greenprod.vAddQ p X).1)).oneValue
      (elim.dotP r (greenprod.vecScale (p.2 * X.2) w.1)) :=
    elim.dotP_oneValue_right r _ _ hrow
  have hR : (elim.dotP r
      (greenprod.vecScale (p.2 * X.2) w.1)).oneValue BPair.unit :=
    elim.dotP_null_tail_right r _
      (poly.oneValue_unitTail
        (greenprod.vecScale_ofPos (p.2 * X.2) w.1)
        (elim.unitTail_vecScale _ w.1 hw))
  have hL : (elim.dotP r
      (greenprod.vecScale w.2 (greenprod.vAddQ p X).1)).oneValue
      (((elim.dotP r p.1).scale X.2
        + (elim.dotP r X.1).scale p.2).scale w.2) :=
    BPair.oneValue_trans (dotP_scaleQ w.2 r _)
      (BPair.scale_congr w.2 (dotP_vAddQ r p X))
  refine BPair.scale_cancel (w := w.2) ?_
  exact BPair.oneValue_trans
    (BPair.oneValue_trans (BPair.oneValue_symm hL)
      (BPair.oneValue_trans hd hR))
    (BPair.oneValue_symm (BPair.unit_scale w.2))

/-- The bond's two-sided read: the upper component against the
transposed block's action reads the lower component against the
block's own, at the slab pair's shape. -/
private theorem bondSwap (B : elim.Mat) (u u' : greenprod.VecQ)
    (k k' : Nat) (hB : elim.rectAt B k k') (hu : u.1.length = k)
    (hu' : u'.1.length = k') :
    (elim.dotN u'.1 (elim.matVec (elim.transposeM B) u.1)).oneValue
      (elim.dotN u.1 (elim.matVec B u'.1)) := by
  have hy : u.1.length = B.length := by
    rw [greenprod.rectAt_len hB]
    exact hu
  have h := elim.dotP_matVec_transpose k' B u'.1 u.1
    (greenprod.rectAt_rows hB) hu' hy
  exact BPair.oneValue_trans (elim.dotN_read u'.1 _)
    (BPair.oneValue_trans (BPair.oneValue_symm h)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (elim.dotP_comm (elim.matVec B u'.1) u.1))
        (BPair.oneValue_symm (elim.dotN_read u.1 _))))

/-- The step's accumulated seed reads the bond datum at the raised
weight, the transpose walked and the clearings exchanged. -/
private theorem seedTie (W0 : BPair) (B : elim.Mat)
    (u u' : greenprod.VecQ) (k k' : Nat) (hB : elim.rectAt B k k')
    (hu : u.1.length = k) (hu' : u'.1.length = k') :
    qOneValue (W0 * elim.dotN u'.1 (elim.matVec (elim.transposeM B) u.1),
        u'.2 * u.2)
      (W0 * elim.dotN u.1 (elim.matVec B u'.1), u.2 * u'.2) := by
  show ((W0 * elim.dotN u'.1
      (elim.matVec (elim.transposeM B) u.1)).scale (u.2 * u'.2)).oneValue
    ((W0 * elim.dotN u.1 (elim.matVec B u'.1)).scale (u'.2 * u.2))
  rw [ground.mul_comm u'.2 u.2]
  exact BPair.scale_congr (u.2 * u'.2)
    (BPair.mul_congr (BPair.oneValue_refl W0)
      (bondSwap B u u' k k' hB hu hu'))

/-- The last slab's joined numerator at the weighted row: the seed
and the diagonal's quadratic read the row's own combination at the
component's clearing. -/
private theorem baseTie (W0 dp qA : BPair) (p2 u2 : Pos) :
    (W0 * (dp.scale u2 + qA.scale p2)).scale u2
      = (W0 * dp).scale (u2 * u2) + (W0 * qA).scale (u2 * p2) := by
  rw [BPair.left_distrib, BPair.mul_scale, BPair.mul_scale,
    BPair.scale_add, BPair.scale_scale, BPair.scale_scale,
    ground.mul_comm p2 u2]

/-- An interior slab's joined numerator at the weighted row: the
seed, the diagonal's quadratic and the bond read the row's own
combination at the component's clearing squared. -/
private theorem headTie (W0 dp qA cB : BPair) (p2 u2 u'2 : Pos) :
    (W0 * (dp.scale (u2 * u'2)
        + (qA.scale u'2 + cB.scale u2).scale p2)).scale (u2 * u2)
      = (W0 * dp).scale (u2 * u2 * (u2 * u'2))
        + ((W0 * qA).scale (u2 * u'2)
          + (W0 * cB).scale (u2 * u2)).scale (u2 * p2) := by
  have e1 : u2 * u'2 * (u2 * u2) = u2 * u2 * (u2 * u'2) := by
    rw [ground.mul_mul_mul_comm u2 u'2 u2 u2, ground.mul_comm u'2 u2]
  have e2 : u'2 * (p2 * (u2 * u2)) = u2 * u'2 * (u2 * p2) := by
    rw [← ground.mul_assoc u'2 p2 (u2 * u2),
      ground.mul_comm (u'2 * p2) (u2 * u2),
      ground.mul_mul_mul_comm u2 u'2 u2 p2]
  have e3 : u2 * (p2 * (u2 * u2)) = u2 * u2 * (u2 * p2) := by
    rw [← ground.mul_assoc u2 p2 (u2 * u2),
      ground.mul_comm (u2 * p2) (u2 * u2)]
  rw [BPair.left_distrib, BPair.mul_scale, BPair.scale_add,
    BPair.mul_scale, BPair.left_distrib, BPair.mul_scale,
    BPair.mul_scale, BPair.scale_add, BPair.scale_add,
    BPair.scale_scale, BPair.scale_scale, BPair.scale_scale,
    BPair.scale_scale, BPair.scale_scale, BPair.scale_add,
    BPair.scale_scale, BPair.scale_scale, e1, e2, e3]

/-- The last slab's two weighted summands read the vacant cleared
datum at the row's own vanishing combination. -/
private theorem baseNull (W0 dp qA : BPair) (p2 u2 : Pos)
    (hG : (dp.scale u2 + qA.scale p2).oneValue BPair.unit) :
    qOneValue (BPair.addQ (W0 * dp, u2 * p2) (W0 * qA, u2 * u2))
      (BPair.unit, Pos.one) := by
  refine qOneValue_unit ?_
  show ((W0 * dp).scale (u2 * u2)
    + (W0 * qA).scale (u2 * p2)).oneValue BPair.unit
  rw [← baseTie W0 dp qA p2 u2]
  exact BPair.oneValue_trans
    (BPair.scale_congr u2
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl W0) hG)
        (BPair.mul_unit W0)))
    (BPair.unit_scale u2)

/-- An interior slab's three weighted summands read the vacant
cleared datum at the row's own vanishing combination. -/
private theorem headNull (W0 dp qA cB : BPair) (p2 u2 u'2 : Pos)
    (hG : (dp.scale (u2 * u'2)
        + (qA.scale u'2 + cB.scale u2).scale p2).oneValue BPair.unit) :
    qOneValue (BPair.addQ (W0 * dp, u2 * p2)
        (BPair.addQ (W0 * qA, u2 * u2) (W0 * cB, u2 * u'2)))
      (BPair.unit, Pos.one) := by
  refine qOneValue_unit ?_
  show ((W0 * dp).scale (u2 * u2 * (u2 * u'2))
    + ((W0 * qA).scale (u2 * u'2)
      + (W0 * cB).scale (u2 * u2)).scale (u2 * p2)).oneValue BPair.unit
  rw [← headTie W0 dp qA cB p2 u2 u'2]
  exact BPair.oneValue_trans
    (BPair.scale_congr (u2 * u2)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl W0) hG)
        (BPair.mul_unit W0)))
    (BPair.unit_scale (u2 * u2))

/-- The block square fold: the diagonal blocks' quadratic reads
against the weight family, one summand per slab at the component's
squared clearing, the off-range slabs vacant. -/
def rhoBlock (W : Nat → BPair) :
    List elim.Mat → List greenprod.VecQ → BPair × Pos
  | [], _ => (BPair.unit, Pos.one)
  | _ :: _, [] => (BPair.unit, Pos.one)
  | A :: diag, u :: us =>
      BPair.addQ (W 0 * inertia.quadForm A u.1, u.2 * u.2)
        (rhoBlock (fun k => W (k + 1)) diag us)

/-- The block bond fold: the off-diagonal blocks' consecutive reads
against the weight family, one summand per bond at the neighbor
pair's clearing, the off-range slabs vacant. -/
def cBlock (W : Nat → BPair) :
    List elim.Mat → List greenprod.VecQ → BPair × Pos
  | [], _ => (BPair.unit, Pos.one)
  | _ :: _, [] => (BPair.unit, Pos.one)
  | _ :: _, [_] => (BPair.unit, Pos.one)
  | B :: off, u :: u' :: us =>
      BPair.addQ (W 0 * elim.dotN u.1 (elim.matVec B u'.1), u.2 * u'.2)
        (cBlock (fun k => W (k + 1)) off (u' :: us))

/-- The walk's accumulated seed read against the leading component
at the leading weight, vacant where no slab remains. -/
private def seedQ (W : Nat → BPair) (p : greenprod.VecQ) :
    List greenprod.VecQ → BPair × Pos
  | [] => (BPair.unit, Pos.one)
  | u :: _ => (W 0 * elim.dotN u.1 p.1, u.2 * p.2)

/-- At a vacant accumulator the seed reads the sum's unit. -/
private theorem seedQ_nil (W : Nat → BPair) (p : greenprod.VecQ)
    (hp : p.1 = []) : ∀ us : List greenprod.VecQ,
    (seedQ W p us).1.oneValue BPair.unit
  | [] => BPair.oneValue_refl _
  | u :: _ => by
      show (W 0 * elim.dotN u.1 p.1).oneValue BPair.unit
      rw [hp]
      have hd : (elim.dotN u.1 ([] : List BPair)).oneValue BPair.unit := by
        rw [← elim.dotP_nil_right u.1]
        exact elim.dotN_read u.1 []
      exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (W 0)) hd)
        (BPair.mul_unit (W 0))

/-- The block fold at an accumulated seed: the seed joined to the
square fold and to the two bond folds — at the weight and at its
raised shift — reads the vacant cleared datum, the walk's rows
consumed slab by slab against the components and the interior seeds
the transposed bonds' own actions. -/
private theorem blockFoldGo : ∀ (p : greenprod.VecQ)
    (diag off : List elim.Mat) (us ws : List greenprod.VecQ)
    (ns : List Nat), greenprod.slabShape diag off ns →
    greenprod.vShape us ns →
    greenprod.solveRows p diag off us ws →
    greenprod.sidesUnit ws → ∀ W : Nat → BPair,
    qOneValue (BPair.addQ (seedQ W p us)
        (BPair.addQ (rhoBlock W diag us)
          (BPair.addQ (cBlock W off us)
            (cBlock (fun k => W (k + 1)) off us))))
      (BPair.unit, Pos.one)
  | _, [], _, _, _, _, _, _, h, _, _ => False.elim h
  | p, [A], [], [u], [w], _, _, _, hrow, hker, W => by
      have hGp : ((elim.dotP u.1 p.1).scale u.2
          + (elim.dotP u.1 (elim.matVec A u.1)).scale p.2).oneValue
          BPair.unit :=
        rowDot u.1 p (greenprod.appM A u) w hrow hker.1
      have hGn : ((elim.dotN u.1 p.1).scale u.2
          + (inertia.quadForm A u.1).scale p.2).oneValue BPair.unit :=
        BPair.oneValue_trans
          (BPair.add_congr
            (BPair.scale_congr u.2 (elim.dotN_read u.1 p.1))
            (BPair.scale_congr p.2
              (elim.dotN_read u.1 (elim.matVec A u.1))))
          hGp
      exact qOneValue_trans
        (BPair.addQ_congr (qOneValue_refl (seedQ W p [u]))
          (qOneValue_trans
            (BPair.addQ_congr
              (BPair.addQ_unitR (W 0 * inertia.quadForm A u.1, u.2 * u.2))
              (BPair.addQ_unitL (BPair.unit, Pos.one)))
            (BPair.addQ_unitR (W 0 * inertia.quadForm A u.1, u.2 * u.2))))
        (baseNull (W 0) (elim.dotN u.1 p.1) (inertia.quadForm A u.1)
          p.2 u.2 hGn)
  | _, [_], [], [_], [], _, _, _, h, _, _ => False.elim h
  | _, [_], [], [_], _ :: _ :: _, _, _, _, h, _, _ => False.elim h
  | _, [_], [], [], _, _, _, _, h, _, _ => False.elim h
  | _, [_], [], _ :: _ :: _, _, _, _, _, h, _, _ => False.elim h
  | _, [_], _ :: _, _, _, _, _, _, h, _, _ => False.elim h
  | _, _ :: _ :: _, [], _, _, _, _, _, h, _, _ => False.elim h
  | _, _ :: _ :: _, _ :: _, [], _, _, _, _, h, _, _ => False.elim h
  | _, _ :: _ :: _, _ :: _, [_], _, _, _, _, h, _, _ => False.elim h
  | _, _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _, h, _, _ =>
      False.elim h
  | p, A :: A' :: As, B :: Bs, u :: u' :: us', w :: ws', ns,
      hslab, hv, hrow, hker, W => by
      match ns, hslab, hv with
      | [], hs, _ => exact False.elim hs
      | [_], hs, _ => exact False.elim hs
      | k :: k' :: ns', hs, hvv =>
        have hGp : ((elim.dotP u.1 p.1).scale (u.2 * u'.2)
            + ((elim.dotP u.1 (elim.matVec A u.1)).scale u'.2
              + (elim.dotP u.1 (elim.matVec B u'.1)).scale u.2).scale
                p.2).oneValue BPair.unit :=
          BPair.oneValue_trans
            (BPair.add_congr (BPair.oneValue_refl _)
              (BPair.scale_congr p.2
                (BPair.oneValue_symm
                  (dotP_vAddQ u.1 (greenprod.appM A u)
                    (greenprod.appM B u')))))
            (rowDot u.1 p
              (greenprod.vAddQ (greenprod.appM A u) (greenprod.appM B u'))
              w hrow.1 hker.1)
        have hGn : ((elim.dotN u.1 p.1).scale (u.2 * u'.2)
            + ((inertia.quadForm A u.1).scale u'.2
              + (elim.dotN u.1 (elim.matVec B u'.1)).scale u.2).scale
                p.2).oneValue BPair.unit :=
          BPair.oneValue_trans
            (BPair.add_congr
              (BPair.scale_congr (u.2 * u'.2) (elim.dotN_read u.1 p.1))
              (BPair.scale_congr p.2
                (BPair.add_congr
                  (BPair.scale_congr u'.2
                    (elim.dotN_read u.1 (elim.matVec A u.1)))
                  (BPair.scale_congr u.2
                    (elim.dotN_read u.1 (elim.matVec B u'.1))))))
            hGp
        have hIh := blockFoldGo (greenprod.appM (elim.transposeM B) u)
          (A' :: As) Bs (u' :: us') ws' (k' :: ns') hs.2.2.2 hvv.2
          hrow.2 hker.2 (fun j => W (j + 1))
        have hTie : qOneValue
            (W (0 + 1) * elim.dotN u'.1
                (elim.matVec (elim.transposeM B) u.1), u'.2 * u.2)
            (W (0 + 1) * elim.dotN u.1 (elim.matVec B u'.1),
              u.2 * u'.2) :=
          seedTie (W (0 + 1)) B u u' k k' hs.2.2.1 hvv.1 hvv.2.1
        exact qOneValue_trans
          (BPair.addQ_shuffle (seedQ W p (u :: u' :: us'))
            (W 0 * inertia.quadForm A u.1, u.2 * u.2)
            (rhoBlock (fun j => W (j + 1)) (A' :: As) (u' :: us'))
            (W 0 * elim.dotN u.1 (elim.matVec B u'.1), u.2 * u'.2)
            (cBlock (fun j => W (j + 1)) Bs (u' :: us'))
            (W (0 + 1) * elim.dotN u.1 (elim.matVec B u'.1), u.2 * u'.2)
            (cBlock (fun j => W (j + 1 + 1)) Bs (u' :: us')))
          (qOneValue_trans
            (BPair.addQ_congr
              (headNull (W 0) (elim.dotN u.1 p.1)
                (inertia.quadForm A u.1)
                (elim.dotN u.1 (elim.matVec B u'.1)) p.2 u.2 u'.2 hGn)
              (qOneValue_trans (BPair.addQ_congr (qOneValue_symm hTie) (qOneValue_refl _)) hIh))
            (BPair.addQ_unitL (BPair.unit, Pos.one)))

/-- The block chain's square fold: at a solved block-tridiagonal
read whose every slab side has unit entries, the square fold against
a weight family joins the two bond folds — at that weight and at its
raised shift — to the vacant cleared datum, one identity per weight
family. -/
theorem blockFold_sq (diag off : List elim.Mat)
    (us ws : List greenprod.VecQ) (ns : List Nat)
    (h : greenprod.solveRead diag off us ws ns)
    (hker : greenprod.sidesUnit ws) (W : Nat → BPair) :
    qOneValue (BPair.addQ (rhoBlock W diag us)
        (BPair.addQ (cBlock W off us)
          (cBlock (fun k => W (k + 1)) off us)))
      (BPair.unit, Pos.one) := by
  refine qOneValue_trans (qOneValue_symm ?_)
    (blockFoldGo _ diag off us ws ns h.1 h.2.1 h.2.2.2 hker W)
  exact qOneValue_trans
    (BPair.addQ_congr (qOneValue_unit (seedQ_nil W _ rfl us)) (qOneValue_refl _))
    (BPair.addQ_unitL _)


end momentfold
