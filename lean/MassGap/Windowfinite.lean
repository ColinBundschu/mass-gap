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
the check module's pins; `degree_le_dfQ` is the window's
enumeration bound, the cleared read clearing the count's multiple
of the degree.
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


/-- The fold's floor at an initial value: the accumulating sum sits
at or beyond its seed. -/
private theorem foldl_add_init (f : Nat → Nat) :
    ∀ (t : List Nat) (a : Nat),
    a ≤ t.foldl (fun acc y => acc + f y) a
  | [], _ => Nat.le_refl _
  | y :: t, a =>
    Nat.le_trans (Nat.le_add_right a (f y))
      (foldl_add_init f t (a + f y))

/-- The fold's floor at a member: the accumulating sum clears any
one member's term over the seed. -/
private theorem foldl_add_ge (f : Nat → Nat) :
    ∀ (t : List Nat) (a q : Nat), q < t.length →
    f (ground.getAt 0 t q) + a
      ≤ t.foldl (fun acc y => acc + f y) a
  | [], _, q, hq => absurd hq (Nat.not_lt_zero q)
  | y :: t, a, 0, _ => by
    show f y + a ≤ t.foldl (fun acc y => acc + f y) (a + f y)
    rw [Nat.add_comm (f y) a]
    exact foldl_add_init f t (a + f y)
  | y :: t, a, q + 1, hq => by
    show f (ground.getAt 0 t q) + a
      ≤ t.foldl (fun acc y => acc + f y) (a + f y)
    exact Nat.le_trans
      (Nat.add_le_add_left (Nat.le_add_right a (f y)) _)
      (foldl_add_ge f t (a + f y) q (Nat.lt_of_succ_lt_succ hq))

/-- The row total sits at or below the pair-gap fold at a vacant
last entry: each row's pair against the vacant last row reads the
row itself. -/
private theorem sum_le_rho2 : ∀ (l : List Nat) (r : Nat),
    l.length = r + 1 → ground.getAt 0 l r = 0 →
    ground.sumNat l ≤ c2hat.rho2 l
  | [x], 0, _, h0 => by
    have hx : x = 0 := h0
    rw [hx]
    exact Nat.le_refl _
  | [_], r + 1, hlen, _ =>
    absurd (Nat.succ.inj hlen) (fun h => Nat.noConfusion h)
  | _ :: _ :: _, 0, hlen, _ =>
    absurd (Nat.succ.inj hlen) (fun h => Nat.noConfusion h)
  | x :: y :: t, r + 1, hlen, h0 => by
    have hlen' : (y :: t).length = r + 1 := Nat.succ.inj hlen
    have h0' : ground.getAt 0 (y :: t) r = 0 := h0
    have hih : ground.sumNat (y :: t) ≤ c2hat.rho2 (y :: t) :=
      sum_le_rho2 (y :: t) r hlen' h0'
    have hhead : x ≤ (y :: t).foldl
        (fun acc z => acc + (x - z)) 0 := by
      have h1 := foldl_add_ge (fun z => x - z) (y :: t) 0 r
        (by rw [hlen']; exact Nat.lt_succ_self r)
      rw [h0'] at h1
      exact h1
    show Nat.add x (ground.sumNat (y :: t))
      ≤ (y :: t).foldl (fun acc z => acc + (x - z)) 0
        + c2hat.rho2 (y :: t)
    exact Nat.add_le_add hhead hih

/-- The degree window: the cleared Casimir read clears the count's
multiple of a reduced shape's box total, each row's pair against
the vacant last row reading the row itself inside the root fold
(`prop:windowfinite`'s "the fold reads at or beyond the degree, so
`d_f Q(λ)` clears `d_f k`"). -/
theorem degree_le_dfQ (s : places.Shape) (r : Nat)
    (hlen : s.length = r + 1)
    (hred : ground.getAt 0 s r = 0) :
    s.length * places.degree s ≤ c2hat.dfQ s := by
  have hrl : (places.rowList s).length = r + 1 := by
    rw [places.length_rowList, hlen]
  have hlast : ground.getAt 0 (places.rowList s) r = 0 := by
    rw [places.rowList_last s r hlen]
    exact hred
  have h1 : ground.sumNat (places.rowList s)
      ≤ c2hat.rho2 (places.rowList s) :=
    sum_le_rho2 (places.rowList s) r hrl hlast
  show s.length * ground.sumNat (places.rowList s)
    ≤ c2hat.sqGaps (places.rowList s)
      + s.length * c2hat.rho2 (places.rowList s)
  exact Nat.le_trans (Nat.mul_le_mul_left s.length h1)
    (Nat.le_add_left _ _)

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
