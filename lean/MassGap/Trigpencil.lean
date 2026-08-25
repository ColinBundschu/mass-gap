import MassGap.Fiberdec
import MassGap.Deckfactor
/-!
`thm:trigpencil` — the fiber family is a bounded chord pencil.  The
momentum-fiber pencil enters each graded block through finitely
many translation powers, the power bounded by the grade's spatial
support (`lem:stableentries`), and each transpose-paired read is a
deck-family polynomial at the chord (`def:deck`), so the chain
object is one algebraic family over the `(t; [α:β])` base with
integral chord data.  Its carrier here is `lem:fiberdec`'s output,
the fiber pencil as a polynomial matrix in the chord variable
(`fiberdec.fiberPencilRead`'s own `split.PMat`).

This tier owns the theorem's three reads at stated data.  The
\emph{fiber symbol} is the family's characteristic polynomial, the
pair `(k : A(z))`'s site-datum determinant — `lem:split`'s own
first-row fold at polynomial entries (`split.pminor`).  It is
`pminor` and not `split.charPoly` that this tier applies, and the
two are not a duplicated pair: `charPoly H G` builds the pencil
matrix from a *level pair* (`split.zMat H G`) and takes its minor,
while `symbolRead`'s carrier is `lem:fiberdec`'s output — a
`split.PMat` already congruenced off the block's own descent, with
no level pair behind it to rebuild.  The shared step is the minor
itself, and both spell it at the one owner.  The tex's symbol is
the two-variable `S(z; k, r)`, and its carrier is the iterated
polynomial carrier (`poly.PPoly`, `def:poly`'s displayed reads
over the balance-pair polynomials, the coefficient carrier
`def:elim`'s Sylvester tier names): the level pair's site datum
over a chord-entried pencil (`split.ppzMat`) with the symbol its
first-row fold (`split.ppminor`), read at `symbolAt` — occupied
at the stated outer degree with the keys beyond it at the sum's
unit and every coefficient within the stated inner bound, the
finite Newton polytope's own display at the two variables, each
conjunct a read of the value; the
residue enters at stated instances, `lem:genericlift`'s
polynomial-pair tier its symbolic read.  The one-variable
`symbolRead` reads the display at a one-variable pencil, and the
two meet at the symbol's boundary coefficients — the constant
reads the chord pencil's own determinant at the even order and
the leading reads the gram's, the batteries' pins.  The \emph{bounded degree per grade} is the
per-grade degree bound on the pencil's rows (`gradeBoundRead`, one
bound per grade where `lem:cellcount`'s `pShapeAt` carries one
clearing power for the whole pencil).  The \emph{deck symmetry} is
`thm:pairpencil`'s consequence: the fiber is the momentum fiber of
a symmetric pair pencil, so a separation's block is the reversed
separation's transpose (`psymRead`, the entry at a key pair
reading the entry at the swapped pair) and the symbol carries the
deck symmetry with it — `lem:deckfactor`'s deck-symmetric datum at
the stated half-degree (`deckSymmetryRead` at
`deckfactor.deckSymRead`).

The three are decidable at stated data and the batteries decide
them at a committed fiber pencil, the deck-symmetric pencil
`lem:deckfactor`'s own assembly builds at side three with the
chord monomial off the diagonal.  Every conjunct is a read of the
determinant's value, so at a square list each `Decidable` instance
decides through the descent's read (`elim.pdetD`, `elim.ppdetD`),
the walk against the fold at the `_eq` transport — the fold stays
the definition, the descent computes.
-/

namespace trigpencil
open ground poly elim inertia

/-- The finite Newton polytope's display at a stated symbol: the
outer degree occupied with the keys beyond it at the sum's unit,
and every coefficient's keys beyond the inner bound at it — each
conjunct a read of the value. -/
def symbolDisp (D : poly.PPoly) (dOut dIn : Nat) : Prop :=
  ¬ poly.unitTail (ground.getAt [] D dOut)
  ∧ poly.ppUnitTail (D.drop (dOut + 1))
  ∧ ((D.take (dOut + 1)).all (fun p => decide
      (poly.unitTail (p.drop (dIn + 1))))) = true

instance (D : poly.PPoly) (dOut dIn : Nat) :
    Decidable (symbolDisp D dOut dIn) :=
  inferInstanceAs (Decidable (¬ _ ∧ _ ∧ _ = _))

/-- The inner bound's fold reads every coefficient of a tail. -/
private theorem dispAll_ut (dIn : Nat) : ∀ {B : poly.PPoly},
    poly.ppUnitTail B →
    (B.all (fun p => decide
      (poly.unitTail (p.drop (dIn + 1))))) = true
  | [], _ => rfl
  | c :: B, h => by
    show (decide (poly.unitTail (c.drop (dIn + 1)))
      && B.all (fun p => decide
        (poly.unitTail (p.drop (dIn + 1))))) = true
    rw [decide_eq_true
        (show poly.unitTail (c.drop (dIn + 1)) from
          poly.utDropO ground.bpairOps ground.bpairRead (dIn + 1)
            (poly.utOfNilO ground.bpairOps ground.bpairRead h.1)),
      dispAll_ut dIn h.2]
    rfl

/-- The inner bound's fold moves across the iterated one-value
read. -/
private theorem dispAll_congr (dIn : Nat) : ∀ {A B : poly.PPoly},
    poly.ppOneValue A B →
    ((A.all (fun p => decide
        (poly.unitTail (p.drop (dIn + 1))))) = true
     ↔ (B.all (fun p => decide
        (poly.unitTail (p.drop (dIn + 1))))) = true)
  | [], [], _ => Iff.rfl
  | [], _ :: _, h => ⟨fun _ => dispAll_ut dIn h, fun _ => rfl⟩
  | _ :: _, [], h =>
    ⟨fun _ => rfl,
     fun _ => dispAll_ut dIn
       (poly.utOfNilO poly.polyOps poly.polyRead h)⟩
  | c :: A, d :: B, h => by
    have hc : poly.unitTail (c.drop (dIn + 1))
        ↔ poly.unitTail (d.drop (dIn + 1)) :=
      ⟨fun hu => poly.unitTail_oneValue_right hu
        (poly.lovDropO ground.bpairOps ground.bpairRead
          (dIn + 1) h.1),
       fun hu => poly.oneValue_unitTail
        (poly.lovDropO ground.bpairOps ground.bpairRead
          (dIn + 1) h.1) hu⟩
    have hI := dispAll_congr dIn h.2
    show (decide (poly.unitTail (c.drop (dIn + 1)))
        && A.all (fun p => decide
          (poly.unitTail (p.drop (dIn + 1))))) = true
      ↔ (decide (poly.unitTail (d.drop (dIn + 1)))
        && B.all (fun p => decide
          (poly.unitTail (p.drop (dIn + 1))))) = true
    constructor
    · intro hab
      have hs := ground.andSplitB hab
      rw [decide_eq_true (hc.mp (of_decide_eq_true hs.1)),
        hI.mp hs.2]
      rfl
    · intro hab
      have hs := ground.andSplitB hab
      rw [decide_eq_true (hc.mpr (of_decide_eq_true hs.1)),
        hI.mpr hs.2]
      rfl

/-- The display is a read of the value: it moves across the
iterated one-value read. -/
private theorem symbolDisp_congr {D D' : poly.PPoly}
    (h : poly.ppOneValue D D') (dOut dIn : Nat) :
    symbolDisp D dOut dIn ↔ symbolDisp D' dOut dIn := by
  have hg := poly.ppOneValue_getAt dOut h
  have hd := poly.lovDropO poly.polyOps poly.polyRead (dOut + 1) h
  have ht := dispAll_congr dIn
    (poly.lovTakeO poly.polyOps poly.polyRead (dOut + 1) h)
  constructor
  · intro x
    refine ⟨fun hw => x.1 (poly.oneValue_unitTail hg hw), ?_,
      ht.mp x.2.2⟩
    exact poly.ppUnitTail_ppOneValue_right x.2.1 hd
  · intro x
    refine ⟨fun hw => x.1 (poly.unitTail_oneValue_right hw hg), ?_,
      ht.mpr x.2.2⟩
    exact poly.ppOneValue_ppUnitTail hd x.2.1

/-- The fiber symbol at the two-variable carrier: the site datum's
determinant (`split.ppminor`) at the polytope's display, occupied
at the stated outer degree with every coefficient within the
stated inner bound. -/
def symbolAt (Z : split.PPMat) (dOut dIn : Nat) : Prop :=
  symbolDisp (split.ppminor Z) dOut dIn

instance (Z : split.PPMat) (dOut dIn : Nat) :
    Decidable (symbolAt Z dOut dIn) :=
  match elim.decRowsLen Z.length Z with
  | isTrue hsq =>
    decidable_of_iff _
      (symbolDisp_congr (elim.ppdetD_eq Z hsq) dOut dIn)
  | isFalse _ =>
    inferInstanceAs (Decidable (symbolDisp (split.ppminor Z) dOut dIn))

/-- The polytope's display at a one-variable symbol: occupied at
the stated degree with the keys beyond it at the sum's unit. -/
def symbolDispP (p : poly.Poly) (d : Nat) : Prop :=
  ¬ (ground.getAt BPair.unit p d).oneValue BPair.unit
  ∧ poly.unitTail (p.drop (d + 1))

instance (p : poly.Poly) (d : Nat) : Decidable (symbolDispP p d) :=
  inferInstanceAs (Decidable (¬ _ ∧ _))

/-- The one-variable display is a read of the value. -/
private theorem symbolDispP_congr {p p' : poly.Poly}
    (h : poly.oneValue p p') (d : Nat) :
    symbolDispP p d ↔ symbolDispP p' d := by
  have hg := poly.oneValue_getAt d h
  have hd := poly.lovDropO ground.bpairOps ground.bpairRead
    (d + 1) h
  constructor
  · intro x
    exact ⟨fun hw => x.1 (BPair.oneValue_trans hg hw),
      poly.unitTail_oneValue_right x.2 hd⟩
  · intro x
    exact ⟨fun hw => x.1
      (BPair.oneValue_trans (BPair.oneValue_symm hg) hw),
      poly.oneValue_unitTail hd x.2⟩

/-- The fiber symbol's read at a stated pencil: the pencil's
determinant (`split.pminor`) at the polytope's one-variable
display. -/
def symbolRead (S : split.PMat) (d : Nat) : Prop :=
  symbolDispP (split.pminor S) d

instance (S : split.PMat) (d : Nat) : Decidable (symbolRead S d) :=
  match elim.decRowsLen S.length S with
  | isTrue hsq =>
    decidable_of_iff _ (symbolDispP_congr (elim.pdetD_eq S hsq) d)
  | isFalse _ =>
    inferInstanceAs (Decidable (symbolDispP (split.pminor S) d))

/-- The bounded-degree-per-grade read: the pencil's row at a grade
carries entries of degree within that grade's own bound — each
entry's keys beyond the bound at the sum's unit, a read of the
value — one bound per grade at the grade's spatial support. -/
def gradeBoundRead (S : split.PMat) (bounds : List Nat) : Prop :=
  S.length = bounds.length
  ∧ ((List.range S.length).all (fun i =>
      (ground.getAt ([] : List Poly) S i).all (fun p => decide
        (poly.unitTail
          (p.drop (ground.getAt 0 bounds i + 1)))))) = true

instance (S : split.PMat) (bounds : List Nat) :
    Decidable (gradeBoundRead S bounds) :=
  inferInstanceAs (Decidable (_ = _ ∧ _ = _))

/-- The pencil's own symmetry at the polynomial carrier: the entry
at a key pair reads the entry at the swapped pair, a separation's
block the reversed separation's transpose
(`thm:pairpencil`). -/
def psymRead (S : split.PMat) (o : Nat) : Prop :=
  ((List.range o).all (fun i => (List.range o).all (fun j =>
    decide (poly.oneValue
      (ground.getAt ([] : List BPair) (ground.getAt [] S i) j)
      (ground.getAt ([] : List BPair) (ground.getAt [] S j) i))))) = true

instance (S : split.PMat) (o : Nat) : Decidable (psymRead S o) :=
  inferInstanceAs (Decidable (_ = _))

/-- The symbol's deck symmetry: the pencil's own symmetry with
`lem:deckfactor`'s deck-symmetric datum at the stated half-degree,
the symbol reading its own reversal. -/
def deckSymmetryRead (S : split.PMat) (o m : Nat) : Prop :=
  psymRead S o ∧ deckfactor.deckSymRead (split.pminor S) m

/-- The deck read transports to the descent's read at a square
list: every conjunct of `deckSymRead` is a read of the value. -/
private theorem deckSym_walk (S : split.PMat) (m : Nat)
    (hsq : elim.rowsLen S.length S) :
    deckfactor.deckSymRead (split.pminor S) m ↔
    deckfactor.deckSymRead (elim.pdetD S) m := by
  have hov : poly.oneValue (elim.pdetD S) (split.pminor S) :=
    elim.pdetD_eq S hsq
  have hg : ∀ k, (ground.getAt BPair.unit (elim.pdetD S) k).oneValue
      (ground.getAt BPair.unit (split.pminor S) k) :=
    fun k => poly.oneValue_getAt k hov
  have hd : poly.oneValue ((elim.pdetD S).drop (2 * m + 1))
      ((split.pminor S).drop (2 * m + 1)) :=
    poly.lovDropO ground.bpairOps ground.bpairRead (2 * m + 1) hov
  constructor
  · intro h
    refine ⟨fun hw => h.1
      (BPair.oneValue_trans (BPair.oneValue_symm (hg 0)) hw), ?_, ?_⟩
    · exact poly.unitTail_oneValue_right h.2.1 (poly.oneValue_symm hd)
    · refine ground.all_range_intro (2 * m + 1) (fun i hi => ?_)
      have hf := of_decide_eq_true
        (ground.all_range_read (2 * m + 1) h.2.2 i hi)
      exact decide_eq_true (BPair.oneValue_trans (hg i)
        (BPair.oneValue_trans hf
          (BPair.oneValue_symm (hg (2 * m - i)))))
  · intro h
    refine ⟨fun hf => h.1 (BPair.oneValue_trans (hg 0) hf), ?_, ?_⟩
    · exact poly.unitTail_oneValue_right h.2.1 hd
    · refine ground.all_range_intro (2 * m + 1) (fun i hi => ?_)
      have hw := of_decide_eq_true
        (ground.all_range_read (2 * m + 1) h.2.2 i hi)
      exact decide_eq_true (BPair.oneValue_trans
        (BPair.oneValue_symm (hg i))
        (BPair.oneValue_trans hw (hg (2 * m - i))))

instance (S : split.PMat) (o m : Nat) :
    Decidable (deckSymmetryRead S o m) :=
  match elim.decRowsLen S.length S with
  | isTrue hsq =>
    decidable_of_iff
      (psymRead S o ∧ deckfactor.deckSymRead (elim.pdetD S) m)
      ⟨fun h => ⟨h.1, (deckSym_walk S m hsq).mpr h.2⟩,
       fun h => ⟨h.1, (deckSym_walk S m hsq).mp h.2⟩⟩
  | isFalse _ =>
    inferInstanceAs (Decidable
      (psymRead S o ∧ deckfactor.deckSymRead (split.pminor S) m))

end trigpencil
