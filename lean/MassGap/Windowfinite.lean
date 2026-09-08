import MassGap.Carrier
/-!
`prop:windowfinite` — a window is finite-dimensional, and its
dimension is a count computed from the structure constants: at a
region of finitely many links the index is a finite list
(`carrier.idx`, the enumeration's own shape), each fiber's
dimension the touched vertices' multiplicity product
(`fibProd`), and
\[ dim Sect(Λ, C) = 1 + Σ_{a ∈ Idx} Π_{v ∈ touched(a)} vmult(v,a), \]
the display's read `dimSect`, one count off the interface.  The
finiteness derivation (the labels of bounded content finitely
many at `C₂(λ) ≥ ⟨λ,λ⟩`) is the below-cutoff enumeration's own
shape at the instantiation (`fusion.dataA`'s degree window at the
cleared bracket's growth); the instances at stated regions are
the check module's pins; the window's enumeration bound is
`c2hat.degree_le_dfQ`, the cleared read clearing the count's
multiple of the degree.
-/

namespace windowfinite
open ground fusion lattice

/-- One fiber's dimension: the touched vertices' multiplicity
product. -/
def fibProd {L : Type} (F : Data L) (R : Region) (a : List L) : Nat :=
  ground.prodOver (carrier.vmult F R a) (carrier.touched F R a)

/-- The window dimension's count: one at the unit line with the
fibers' multiplicity products over the index. -/
def dimSect {L : Type} (F : Data L) (R : Region) (C : Nat) : Nat :=
  1 + (carrier.idx F R C).foldl (fun acc a => acc + fibProd F R a) 0


/-- The dimension display at a stated enumeration:
`prop:windowfinite`'s count read off the committed index, the
fold's value the display's own. -/
theorem dimSect_at {L : Type} (F : Data L) (R : Region) (C n : Nat)
    (l : List (List L)) (hl : carrier.idx F R C = l)
    (hn : 1 + l.foldl (fun acc a => acc + fibProd F R a) 0 = n) :
    dimSect F R C = n := by
  show 1 + (carrier.idx F R C).foldl
    (fun acc a => acc + fibProd F R a) 0 = n
  rw [hl]
  exact hn

end windowfinite
