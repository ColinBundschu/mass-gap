import MassGap.Stagesplit
import MassGap.Inertia
/-!
`lem:hermitesign` — the located sign is a count.  The carrier is
the squarefree polynomial's remainder lists at its below-top list,
and the remainder multiplication at a polynomial is the matrix
whose column `j` is the remainder of `f x^j` (`remMulMat` at
`xpow`), the trace its diagonal fold (`traceM`, with `traceRem` the
one-pass read, the coherence a battery pin).  The Hermite pairing
`H_p[i,j] = tr M_{x^{i+j} p}` is `hermite`, every entry one
elimination read over the ground.  The definite block's additive
identity `4 tr(M_{xp})² = 4 tr(M_p) tr(M_{x²p})
+ ((2a + hb)² + g b²) g` at a factor's pair data and the value's
remainder `a + b x` is the decidable read `defBlockRead`
(`lem:stagesplit`'s `QDatum`), settled at the three remainders `1`,
`x`, `1 + x`, the batteries'.  The bracket's pencil at composite
endpoints `[ln : c]`, `[ln' : c]` enters cleared by the shared
clearing's square, `(c² H_{x²p} + ln ln' H_p : c (ln + ln')
H_{xp})`'s site datum (`pencilB`), and the counts close on the
stated reads at `lem:inertia`'s splits: the located sign's two
natural identities at the isolating bracket — `p` on its upper side
exactly at `rank H_p + 2 rev 𝖡 = rank 𝖡 + 2 rev H_p + 2`
(`sideUpperRead`, the isolation `lem:stage`'s at half the
separation), and on its lower at the exchanged join
(`sideLowerRead`) — and the segment count at the unit weight over
any endpoint pair off the roots, `rev H₁ + # = rev 𝖡`
(`segCountRead`), the isolating bracket the one-root instance; at
a polynomial off the squarefree site the pairings read its distinct
roots, the multiplicities positive weights at the roots' moment
folds, so the segment count reads the distinct roots inside
(`lem:deckfactor`'s band read the instance at the deck symbol).  The
CRT split of the pairing over a stated factor list — the trace
additive over the blocks, a linear block the value's side read and
a definite block the identity's — is the derivation tier at its
recorded consumers (`lem:deckfactor`'s band read the arriving
instance, `thm:SO`'s located signs at stored towers), the counts'
reads the displays above.
-/

namespace hermitesign
open ground poly elim inertia

/-- The monomial at a natural key. -/
def xpow (j : Nat) : Poly :=
  List.replicate j BPair.unit ++ [BPair.ofPos .one]

/-- The remainder multiplication at a polynomial: the matrix whose
column `j` is the remainder of `f x^j` at the below-top list. -/
def remMulMat (s f : Poly) : Mat :=
  transposeM ((List.range s.length).map (fun j =>
    (poly.div s (poly.mul f (xpow j))).2))

/-- The matrix trace, the diagonal fold. -/
def traceM (m : Mat) : BPair :=
  (List.range m.length).foldl (fun a i =>
    (a + ground.getAt BPair.unit (ground.getAt [] m i) i).norm)
    BPair.unit

/-- The remainder multiplication's trace at one pass, the columns'
diagonal reads folded; the coherence with `traceM` at `remMulMat`
is the check module's pin. -/
def traceRem (s f : Poly) : BPair :=
  (List.range s.length).foldl (fun a j =>
    (a + ground.getAt BPair.unit
      ((poly.div s (poly.mul f (xpow j))).2) j).norm) BPair.unit

/-- The Hermite pairing `H_p[i,j] = tr M_{x^{i+j} p}` at the
below-top list, every entry one elimination read. -/
def hermite (s p : Poly) : Mat :=
  ground.matOf s.length s.length
    (fun i j => traceRem s (poly.mul p (xpow (i + j))))

/-- The definite block's additive identity at a factor's pair data
`(h, q)` with gap `g` and the value's remainder `a + b x`:
`4 tr(M_{xp})² = 4 tr(M_p) tr(M_{x²p}) + ((2a + hb)² + g b²) g`,
one quadratic-form identity in the remainder. -/
def defBlockRead (D : stagesplit.QDatum) (a b : BPair) : Prop :=
  BPair.oneValue
    (BPair.ofNat 4
      * (traceRem [D.q, D.h.swap] (poly.mul [a, b] (xpow 1))
        * traceRem [D.q, D.h.swap] (poly.mul [a, b] (xpow 1))))
    (BPair.ofNat 4
      * (traceRem [D.q, D.h.swap] [a, b]
        * traceRem [D.q, D.h.swap] (poly.mul [a, b] (xpow 2)))
      + ((BPair.ofNat 2 * a + D.h * b) * (BPair.ofNat 2 * a + D.h * b)
        + D.g * (b * b)) * D.g)

instance (D : stagesplit.QDatum) (a b : BPair) :
    Decidable (defBlockRead D a b) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- The bracket's pencil at composite endpoints `[ln : c]` and
`[ln' : c]`, cleared by the shared clearing's square: the site
datum of `(c² H_{x²p} + ln ln' H_p : c (ln + ln') H_{xp})`. -/
def pencilB (s p : Poly) (ln ln' : BPair) (c : Pos) : Mat :=
  siteDatum
    (matAdd (matScale (c * c) (hermite s (poly.mul p (xpow 2))))
      (matScaleB (ln * ln') (hermite s p)))
    (matScaleB ((ln + ln').scale c) (hermite s (poly.mul p (xpow 1))))

/-- The value's upper side at the located root: the isolating
bracket at half the separation with endpoints off the roots, the
two splits, and the closing identity
`rank H_p + 2 rev 𝖡 = rank 𝖡 + 2 rev H_p + 2`. -/
def sideUpperRead {o1 o2 : Nat} (s p : Poly) (ln ln' : BPair)
    (c wn wd : Pos) (spH : Split o1) (spB : Split o2) : Prop :=
  stage.isolRead ⟨s, ⟨ln, c⟩, ⟨ln', c⟩⟩ wn wd
  ∧ ¬ (stage.evalC (poly.monic s) ⟨ln, c⟩).oneValue stage.unitC
  ∧ ¬ (stage.evalC (poly.monic s) ⟨ln', c⟩).oneValue stage.unitC
  ∧ splitRead (hermite s p) spH
  ∧ splitRead (pencilB s p ln ln' c) spB
  ∧ rankAt spH + 2 * revAt spB = rankAt spB + 2 * revAt spH + 2

instance {o1 o2 : Nat} (s p : Poly) (ln ln' : BPair) (c wn wd : Pos)
    (spH : Split o1) (spB : Split o2) :
    Decidable (sideUpperRead s p ln ln' c wn wd spH spB) :=
  inferInstanceAs (Decidable (_ ∧ ¬ _ ∧ ¬ _ ∧ _ ∧ _ ∧ _ = _))

/-- The value's lower side at the located root, the exchanged
join: `rank H_p + 2 rev 𝖡 + 2 = rank 𝖡 + 2 rev H_p`. -/
def sideLowerRead {o1 o2 : Nat} (s p : Poly) (ln ln' : BPair)
    (c wn wd : Pos) (spH : Split o1) (spB : Split o2) : Prop :=
  stage.isolRead ⟨s, ⟨ln, c⟩, ⟨ln', c⟩⟩ wn wd
  ∧ ¬ (stage.evalC (poly.monic s) ⟨ln, c⟩).oneValue stage.unitC
  ∧ ¬ (stage.evalC (poly.monic s) ⟨ln', c⟩).oneValue stage.unitC
  ∧ splitRead (hermite s p) spH
  ∧ splitRead (pencilB s p ln ln' c) spB
  ∧ rankAt spH + 2 * revAt spB + 2 = rankAt spB + 2 * revAt spH

instance {o1 o2 : Nat} (s p : Poly) (ln ln' : BPair) (c wn wd : Pos)
    (spH : Split o1) (spB : Split o2) :
    Decidable (sideLowerRead s p ln ln' c wn wd spH spB) :=
  inferInstanceAs (Decidable (_ ∧ ¬ _ ∧ ¬ _ ∧ _ ∧ _ ∧ _ = _))

/-- The segment count at the unit weight over any endpoint pair off
the roots: every real root inside the closed segment adds one
reversal to the bracket pencil beyond `H₁`'s,
`rev H₁ + # = rev 𝖡`, the isolating bracket the one-root
instance. -/
def segCountRead {o1 o2 : Nat} (s : Poly) (ln ln' : BPair) (c : Pos)
    (k : Nat) (spH : Split o1) (spB : Split o2) : Prop :=
  ln < ln'
  ∧ ¬ (stage.evalC (poly.monic s) ⟨ln, c⟩).oneValue stage.unitC
  ∧ ¬ (stage.evalC (poly.monic s) ⟨ln', c⟩).oneValue stage.unitC
  ∧ splitRead (hermite s poly.one) spH
  ∧ splitRead (pencilB s poly.one ln ln' c) spB
  ∧ revAt spH + k = revAt spB

instance {o1 o2 : Nat} (s : Poly) (ln ln' : BPair) (c : Pos)
    (k : Nat) (spH : Split o1) (spB : Split o2) :
    Decidable (segCountRead s ln ln' c k spH spB) :=
  inferInstanceAs (Decidable (_ ∧ ¬ _ ∧ ¬ _ ∧ _ ∧ _ ∧ _ = _))

end hermitesign
