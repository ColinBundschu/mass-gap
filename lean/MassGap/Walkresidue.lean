import MassGap.Excess
/-!
`thm:walkresidue` — the walk residue: the tower pairing
`φ_m = [m r : m(m+r)] = [r : m+r]` with its complement
`ψ_m = [m : m+r]` joining to one, the reads `splitRead` and
`pairRead`; the summand identity `[1:m] = [1:m+r] + [r : m(m+r)]`,
`summandRead`; the coefficientwise record at the `Ψ`-level, the
finite telescope exact at every `M`,
`Σ_{m≤M} [r : m(m+r)] + Σ_{j=M+1}^{M+r} [1:j] = H_r`, `teleRead`
at the successor spelling `r = g + 1`; and the value read
`A(1) = H_r`, the ruler's excess over the walk at one,
`excessRead` at `def:excess`'s evaluation against the ground's
harmonic fold.  The recursions `R' = 1 + u R'` and
`F' = u^r + u F'` read coefficientwise as `def:excess`'s
`geomRead` at their occupied degrees; the general telescope over
every `M` is the stated read's quantifier, its instances the
check module's pins, the induction landing with the restatement's
consumers — where the divisor pair's list reads (`F'`'s least
occupied degree at the residue with the pole order one) and the
`r = 1` discrimination sentence (the exponent's integrality with
the two agreeing objects separating at `r = 2`) land beside it.
-/

namespace walkresidue
open ground

/-- The tower pairing `φ_m = [r : m+r]`, the row-weight part over
the whole. -/
def phi (r m : Pos) : Pair := ⟨r, m + r⟩

/-- The pairing's complement `ψ_m = [m : m+r]`. -/
def psi (r m : Pos) : Pair := ⟨m, m + r⟩

/-- `φ_m + ψ_m = 1`, the one-value read. -/
def pairRead (r m : Pos) : Prop :=
  (phi r m + psi r m).oneValue (Pair.ofPos Pos.one)

instance (r m : Pos) : Decidable (pairRead r m) :=
  inferInstanceAs (Decidable (_ = _))

/-- The Casimir split `φ_m = [m r : m (m + r)]`, the square part
against the whole. -/
def splitRead (r m : Pos) : Prop :=
  (phi r m).oneValue ⟨m * r, m * (m + r)⟩

instance (r m : Pos) : Decidable (splitRead r m) :=
  inferInstanceAs (Decidable (_ = _))

/-- The summand identity `[1:m] = [1:m+r] + [r : m(m+r)]`. -/
def summandRead (r m : Pos) : Prop :=
  (⟨Pos.one, m⟩ : Pair).oneValue (⟨Pos.one, m + r⟩ + ⟨r, m * (m + r)⟩)

instance (r m : Pos) : Decidable (summandRead r m) :=
  inferInstanceAs (Decidable (_ = _))

/-- The finite telescope at a stated `M`, exact:
`Σ_{m≤M} [r : m(m+r)] + Σ_{j=M+1}^{M+r} [1:j] = H_r` at the
successor spelling `r = g + 1`, the tail's first term the fold's
seed. -/
def teleRead (g M : Nat) : Prop :=
  (((List.range M).foldl (fun acc i =>
      acc + ⟨posOfSucc g, posOfSucc i * (posOfSucc i + posOfSucc g)⟩)
    ((List.range g).foldl (fun acc i =>
      acc + ⟨Pos.one, posOfSucc (M + 1 + i)⟩)
      (⟨Pos.one, posOfSucc M⟩ : Pair)))).oneValue
    (harmonic (posOfSucc g))

instance (g M : Nat) : Decidable (teleRead g M) :=
  inferInstanceAs (Decidable (_ = _))

/-- The value read `A(1) = H_r`: the ruler's excess over the walk
at one, `def:excess`'s evaluation against the harmonic fold, at
the successor spelling `r = g + 1`. -/
def excessRead (g : Nat) : Prop :=
  (excess.evalOne g).oneValue (harmonic (posOfSucc g))

instance (g : Nat) : Decidable (excessRead g) :=
  inferInstanceAs (Decidable (_ = _))

end walkresidue
