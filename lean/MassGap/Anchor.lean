import MassGap.Adjchar
import MassGap.C2hat
/-!
`prop:anchor` — the charged anchor for the `X`-chain: the charged
tower is the `mθ`-string, the Cartan powers of the highest root,
and its label is `towerShape`, `mθ = (2m, m^c)` at `c + 2 = d_f`
— the adjoint's column multiset with every occupancy scaled by the
tower's index.  The residue is the pairing's own read at the
highest root: the row-weight fold reads `⟨θ, 2ρ⟩ = 2 r` against the
pair-square fold at `2 d_f`, and `def:c2hat`'s constructed witness
`d_f Q(λ) = Σ_{p<q} ⟨λ_p : λ_q⟩² + d_f ⟨λ, 2ρ⟩` is homogeneous in
the rows, degree two and degree one, so the tower reads off `θ`'s
two folds:
`d_f Q(mθ) = m² · 2 d_f + m d_f · 2 r = 2 d_f m (m + r)`
(`tower_dfQ`).  Against `2 d_f²` this is the tower law
`ĉ₂(mθ) = [m (m + r) : r + 1]`, the display cross-multiplied at
`towerRead`, an `l(l+1)` in shape; at `r = 1` it is `[m² + m : 2]`,
the integer-spin tower's weight-free read.  The member-table route
(`con:sertables`' one fold, `C₂(mθ) = m² ⟨θ, θ⟩ + m ⟨θ, 2ρ⟩`) and
the tower matrix `J` arrive with their own consumers
(`prop:row`); the `m = 2` read is `lem:channels`' `2θ` entry.
-/

namespace anchor
open ground places

/-- The tower label's column multiset: `mθ = (2m, m^c)`'s columns are
`m` copies of `θ`'s, the occupancy map at the factor. -/
def towerShape (d m : Nat) : Shape := (adjchar.theta d).map (· * m)

/-- The tower at index one is the adjoint's own shape. -/
theorem towerShape_one (d : Nat) : towerShape d 1 = adjchar.theta d := by
  show (adjchar.theta d).map (fun n => n * 1) = adjchar.theta d
  rw [ground.map_congr_all (fun n => n * 1) (fun n => n)
      (fun x => Nat.mul_one x) (adjchar.theta d),
    ground.map_id (adjchar.theta d)]

/-! `θ`'s two folds at the reduced shape: the pair squares at
`2 d_f` and the row weights at `2 r`, the residue doubled. -/

/-- `θ`'s pair-square fold is the doubled fundamental count, the
square identity's read at `q(θ) = r + 3` and `k = d_f`. -/
private theorem sqGaps_theta (g : Nat) :
    c2hat.sqGaps (rowList (adjchar.theta (g + 2))) = 2 * (g + 2) := by
  have hblk : c2hat.sqGaps (List.replicate g 1 ++ [0])
      = g * 1 + 0 := by
    rw [c2hat.sqGaps_replicate_app 1 g [0]]
    rfl
  have hhead : ([0] : List Nat).foldl
      (fun acc y => acc + (2 - y) * (2 - y)) (0 + g * 1) = g + 4 := by
    show 0 + g * 1 + 4 = g + 4
    rw [Nat.mul_one g, Nat.zero_add g]
  rw [adjchar.rowList_theta g]
  show (List.replicate g 1 ++ [0]).foldl
        (fun acc y => acc + (2 - y) * (2 - y)) 0
      + c2hat.sqGaps (List.replicate g 1 ++ [0])
    = 2 * (g + 2)
  rw [ground.foldl_append (fun acc y => acc + (2 - y) * (2 - y))
      (List.replicate g 1) [0] 0,
    c2hat.sqFold_replicate 2 1 g 0, hhead, hblk, Nat.mul_one g,
    Nat.add_zero g, Nat.left_distrib 2 g 2, Nat.two_mul g,
    Nat.add_assoc g g 4, Nat.add_comm (g + 4) g]

/-- `θ`'s row-weight fold is the residue doubled,
`⟨θ, 2ρ⟩ = 2 r`: the top row's read over the run's equal
members. -/
private theorem rho2_theta (g : Nat) :
    c2hat.rho2 (rowList (adjchar.theta (g + 2))) = 2 * (g + 1) := by
  have hblk : c2hat.rho2 (List.replicate g 1 ++ [0]) = g * 1 + 0 := by
    rw [c2hat.rho2_replicate_app 1 g [0]]
    rfl
  have hhead : ([0] : List Nat).foldl
      (fun acc y => acc + (2 - y)) (0 + g * 1) = g + 2 := by
    show 0 + g * 1 + 2 = g + 2
    rw [Nat.mul_one g, Nat.zero_add g]
  rw [adjchar.rowList_theta g]
  show (List.replicate g 1 ++ [0]).foldl (fun acc y => acc + (2 - y)) 0
      + c2hat.rho2 (List.replicate g 1 ++ [0])
    = 2 * (g + 1)
  rw [ground.foldl_append (fun acc y => acc + (2 - y))
      (List.replicate g 1) [0] 0,
    c2hat.gapFold_replicate 2 1 g 0, hhead, hblk, Nat.mul_one g,
    Nat.add_zero g, Nat.left_distrib 2 g 1, Nat.two_mul g,
    Nat.mul_one 2, Nat.add_assoc g g 2, Nat.add_comm (g + 2) g]

/-- The two homogeneous folds collect at the tower's display. -/
private theorem towerRing (a m e : Nat) :
    m * m * (2 * a) + a * (m * (2 * e)) = 2 * a * (m * (m + e)) := by
  have hb : a * (m * (2 * e)) = 2 * a * (m * e) := by
    rw [← ground.mulAssoc m 2 e, Nat.mul_comm m 2,
      ground.mulAssoc 2 m e, ← ground.mulAssoc a 2 (m * e),
      Nat.mul_comm a 2, ground.mulAssoc 2 a (m * e)]
  rw [hb, Nat.mul_comm (m * m) (2 * a), Nat.left_distrib m m e,
    Nat.left_distrib (2 * a) (m * m) (m * e)]

/-- The tower's cleared traceless read, `prop:anchor`'s two folds at
the homogeneity: `d_f Q(mθ) = 2 d_f m (m + r)` — the pair squares
`2 d_f` and the row weights `2r` at `m = 1`, each fold homogeneous of
its degree in the rows. -/
theorem tower_dfQ : ∀ d m : Nat, 2 ≤ d →
    c2hat.dfQ (towerShape d m) = 2 * d * (m * (m + (d - 1))) := by
  intro d m hd
  have hg := Nat.le.dest hd
  match hg with
  | ⟨g, hgd⟩ =>
    have hdg : d = g + 2 := by rw [← hgd, Nat.add_comm 2 g]
    rw [hdg]
    show c2hat.sqGaps (rowList ((adjchar.theta (g + 2)).map (· * m)))
        + ((adjchar.theta (g + 2)).map (· * m)).length
          * c2hat.rho2 (rowList ((adjchar.theta (g + 2)).map (· * m)))
      = 2 * (g + 2) * (m * (m + (g + 2 - 1)))
    rw [places.rowList_scale m (adjchar.theta (g + 2)),
      c2hat.sqGaps_scale m (rowList (adjchar.theta (g + 2))),
      c2hat.rho2_scale m (rowList (adjchar.theta (g + 2))),
      sqGaps_theta g, rho2_theta g, ground.length_map,
      adjchar.length_theta (g + 2)]
    show m * m * (2 * (g + 2)) + (g + 2) * (m * (2 * (g + 1)))
      = 2 * (g + 2) * (m * (m + (g + 1)))
    exact towerRing (g + 2) m (g + 1)

/-- The tower law's display, cross-multiplied:
`ĉ₂(mθ) = [m (m + r) : r + 1]` at `ĉ₂ = [d_f Q : 2 d_f²]`. -/
theorem towerRead : ∀ d m : Nat, 2 ≤ d →
    c2hat.dfQ (towerShape d m) * d = m * (m + (d - 1)) * (2 * (d * d)) := by
  intro d m hd
  rw [tower_dfQ d m hd,
    ground.mulAssoc 2 d (m * (m + (d - 1))),
    ground.mulAssoc 2 (d * (m * (m + (d - 1)))) d,
    ground.mulAssoc d (m * (m + (d - 1))) d,
    Nat.mul_comm (m * (m + (d - 1))) d,
    ← ground.mulAssoc d d (m * (m + (d - 1))),
    Nat.mul_comm (m * (m + (d - 1))) (2 * (d * d)),
    ground.mulAssoc 2 (d * d) (m * (m + (d - 1)))]

end anchor
