import MassGap.Channels
/-!
`con:xfusion` — the X-sector is adjoint fusion: `χ_X = χ_adj`, the
sector's data the fusion matrix and the weight-free Casimir, and
every anchor a read of that pair.  The two anchors read here in
closed form, general in the residue: `c₁`, the adjoint's
multiplicity in its own square, the walk's base and the θ row's
count — `2` at `r ≥ 2` (`c1_eq`, `lem:channels`' fast count at the
θ row, the generic residues at `channels.countAt_rowTheta` with
the low residues decided) and `1` at `r = 1` (`c1_one`, the run
vacant there) — and the vacuum's multiplicity, one at the unit
channel at every residue (`vacMult_eq`).  `thm:xdata` reads the
pair as its two integer coefficients; its structural identities
are `lem:channels`' closure reads, pinned beside these; the module
energy `E₀ = 4` is `prop:E0`'s, the pencil layer's.
-/

namespace xfusion
open ground places

/-- The walk's base: the adjoint's multiplicity in its own square,
the fast count at the matched-degree θ class. -/
def c1 (d : Nat) : Nat :=
  channels.countAt d (ground.bumpAt (d - 1) (adjchar.theta d))

/-- The vacuum's multiplicity: the fast count at the unit channel,
the matched degree's full columns. -/
def vacMult (d : Nat) : Nat :=
  channels.countAt d (ground.bumpAt (d - 1)
    (ground.bumpAt (d - 1) (List.replicate d 0)))

/-- The walk's base at every residue beyond one: the θ row's count
is `2`, the residue's count at the identity against the run's
exchanges — the fast count at the θ row, the generic residues
`channels.countAt_rowTheta`'s read with the low residues
decided. -/
theorem c1_eq : ∀ d : Nat, 3 ≤ d → c1 d = 2 := by
  intro d hd
  obtain ⟨g, hg⟩ := Nat.le.dest hd
  have hd3 : d = 3 + g := hg.symm
  subst hd3
  match g with
  | 0 => decide
  | 1 => decide
  | h + 2 =>
    have he : 3 + (h + 2) = h + 5 := by
      rw [Nat.add_comm 3 (h + 2), Nat.add_assoc h 2 3]
    rw [he]
    exact channels.countAt_rowTheta h

/-- The walk's base at the first member: one, the run vacant at
`r = 1`. -/
theorem c1_one : c1 2 = 1 := by decide +kernel

/-- The vacuum's multiplicity at every residue: one at the unit
channel, the generic residues `channels.countAt_rowUnit`'s read
with the low residues decided. -/
theorem vacMult_eq : ∀ d : Nat, 2 ≤ d → vacMult d = 1 := by
  intro d hd
  obtain ⟨g, hg⟩ := Nat.le.dest hd
  have hd2 : d = 2 + g := hg.symm
  subst hd2
  match g with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | h + 3 =>
    have he : 2 + (h + 3) = h + 5 := by
      rw [Nat.add_comm 2 (h + 3), Nat.add_assoc h 3 2]
    rw [he]
    exact channels.countAt_rowUnit h

end xfusion
