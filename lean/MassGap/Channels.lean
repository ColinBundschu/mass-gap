import MassGap.Adjchar
import MassGap.Weyldim
import MassGap.C2hat
import MassGap.Anchor
/-!
`lem:channels` — the adjoint square's channels: the blocks of
`θ ⊗ θ` are the six labels — the unit, `θ` at the walk's parameter
`c₁`, `2θ`, the dual pair `2ω₁ + ω₂*` and `ω₂ + 2ω₁*`, and
`ω₂ + ω₂*` — each entering at its stated threshold (the dual pair
at `r ≥ 2`, the last row at `r ≥ 3`), with the two closure
identities `Σ m d = r²(r+2)²` and `Σ m d ĉ₂ = 2 r²(r+2)²`.  The
rows are `rows`, the matched-degree column multisets with their
multiplicities; the count is `countAt`, `cor:steinberg`'s fold at
`lem:adjchar`'s content read — span-free, which is what opens the
committed residues beyond the degenerations.  The fold stands at a
general second slot as `adjCount`, the graded gap at the first
factor `θ` against any second factor, `countAt` its reading at
`θ` itself; the two multiplicity reads agree at every arising tie
(`sumsWith_agree`), the formula-side fold the definitional span
occupancy at the adjoint.  The whole list is
one decidable read per residue, `tableRead`: over every shape at
the matched degree the fast count reads the table's occupancy.
The closures are the cleared reads `dimClosure` and `casClosure`
at `cor:weyldim`'s dimensions and `def:c2hat`'s cleared Casimir.
The Casimir column closes in closed form at every residue
(`rows_dfQ`): the unit at the kernel point, `θ` at `2 d_f²`, `2θ`
at the tower law's `m = 2` read `2d² + 2d(d+2)` — the stored shape
is the tower label there (`row2Theta_towerShape`;
`prop:anchor`) — the dual pair at `4 d_f²`, and `ω₂ + ω₂*` at
`2d² + 2d(d−2)`, each row's row list evaluated against
`def:c2hat`'s two folds with the full columns read as the class
read.
The dimension column closes in closed form at every residue as
well (`rows_dim`): each row's display is a descending run at its
own floor with the head's raises above it and the lowest entries
beneath, `cor:weyldim`'s telescope reads the run's factorials
against the tail's folds, and the naming identity (`weyldim.readAll`)
clears the unit display's product — the unit line, the adjoint's
`d_f² − 1`, `2θ` at `[(r+1)² r (r+4) : 4]`, the dual pair at
`[g r (r+2)(r+3) : 4]` and `ω₂ + ω₂*` at `[(r+1)² (r+2) w : 4]`.
Folding the two columns against those closed forms closes the two
identities at every residue (`dimClosureAll`, `casClosureAll`): the
self-dual outer rows collect at the residue's crossed pair, the dual
pair enters twice at its gap witness, and the weights' tie
`(r+4) + g = 2 d_f` closes the Casimir fold.
The general theorem `readAll` closes the table at every residue:
the tie classification reads the unit-monomial content at the
identity permutation, a letter-pair move at each adjacent exchange
of the run's unit gaps, and one of the five modifications at a
letter-pair move of the identity alignment — so the `θ` row's two
graded sums are the residue's count against the run's exchanges,
its fast count the walk's parameter, each modification's count one
at its own identity contribution, and every further shape of the
width the fold's unit at both sums.  The low residues are their own
decided reads.
-/

namespace channels
open ground places

/-- The unit channel's stored shape, two full columns. -/
def rowUnit (d : Nat) : Shape :=
  ground.bumpAt (d - 1) (ground.bumpAt (d - 1) (List.replicate d 0))

/-- The `θ` row's stored shape, the adjoint with one full column. -/
def rowTheta (d : Nat) : Shape :=
  ground.bumpAt (d - 1) (adjchar.theta d)

/-- The `2θ` row's stored shape, `(4, 2^a)`'s column multiset. -/
def rowTwoTheta (d : Nat) : Shape :=
  ground.bumpAt 0 (ground.bumpAt 0
    (ground.bumpAt (d - 2) (ground.bumpAt (d - 2) (List.replicate d 0))))

/-- `2ω₁ + ω₂*`'s stored shape, `(3, 1^b)` with one full column. -/
def rowDualA (d : Nat) : Shape :=
  ground.bumpAt (d - 1) (ground.bumpAt 0 (ground.bumpAt 0
    (ground.bumpAt (d - 3) (List.replicate d 0))))

/-- `ω₂ + 2ω₁*`'s stored shape, `(3, 3, 2^b)`'s column multiset. -/
def rowDualB (d : Nat) : Shape :=
  ground.bumpAt 1 (ground.bumpAt (d - 2)
    (ground.bumpAt (d - 2) (List.replicate d 0)))

/-- `ω₂ + ω₂*`'s stored shape, `(2, 2, 1^e)` with one full column. -/
def rowOmega (d : Nat) : Shape :=
  ground.bumpAt (d - 1) (ground.bumpAt 1
    (ground.bumpAt (d - 3) (List.replicate d 0)))

/-- The channel rows at the matched degree `2 d_f`: the six labels'
column multisets with their multiplicities, each row entering at
its stated threshold, the θ row's count the walk's parameter. -/
def rows (d : Nat) : List (Shape × Nat) :=
  [ (rowUnit d, 1),
    (rowTheta d, if d == 2 then 1 else 2),
    (rowTwoTheta d, 1) ]
  ++ (if 3 ≤ d then [ (rowDualA d, 1), (rowDualB d, 1) ] else [])
  ++ (if 4 ≤ d then [ (rowOmega d, 1) ] else [])

/-- The table's occupancy read at a matched-degree shape. -/
def rowRead (d : Nat) (c : Shape) : Nat :=
  (rows d).foldl (fun acc r => if r.1 = c then acc + r.2 else acc) 0

/-- The fast count at the adjoint's content formula, the general
second slot: `cor:steinberg`'s fold at `lem:adjchar`'s content
read, the graded gap at the first factor `θ`. -/
def adjCount (d : Nat) (s c : Shape) : Nat :=
  let p := steinberg.sumsWith (adjchar.multRead d) d s c
  p.1 - p.2

/-- The two multiplicity reads agree at every arising tie: the
formula-side fold is the definitional one (`lem:adjchar`'s read at
the contents of the degree, the further gaps vacant on both
sides). -/
theorem sumsWith_agree (d : Nat) (lam c : Shape)
    (hd : 2 ≤ d) (hcd : c.length = d) :
    steinberg.gradedSums (adjchar.theta d) lam c
      = steinberg.sumsWith (adjchar.multRead d) d lam c := by
  have htl : (adjchar.theta d).length = d := by
    show (ground.bumpAt 0 (ground.bumpAt (d - 2)
      (List.replicate d 0))).length = d
    rw [ground.length_bumpAt, ground.length_bumpAt,
      ground.length_replicate]
  show steinberg.sumsWith (blockcount.occupancyAt
      (blockcount.blockSpan (adjchar.theta d)))
      (adjchar.theta d).length lam c
    = steinberg.sumsWith (adjchar.multRead d) d lam c
  rw [htl]
  refine ground.foldl_congr _ _ (fun acc p => ?_)
    (places.perms d) ((0, 0) : Nat × Nat)
  cases htie : ground.tieGap (places.display c)
      (places.expo (places.display lam) p) with
  | none => rfl
  | some m =>
    have hml : m.length = d := by
      obtain ⟨hml', _, _⟩ := ground.tieGap_reads _ _ m htie
      rw [hml', length_display]
      exact hcd
    show (if parity p
        then (acc.1, acc.2 + blockcount.occupancyAt
          (blockcount.blockSpan (adjchar.theta d)) m)
        else (acc.1 + blockcount.occupancyAt
          (blockcount.blockSpan (adjchar.theta d)) m, acc.2))
      = (if parity p
        then (acc.1, acc.2 + adjchar.multRead d m)
        else (acc.1 + adjchar.multRead d m, acc.2))
    rw [adjchar.occupancy d hd m hml]

/-- The fusion count at the adjoint square through the fast reads:
`cor:steinberg`'s fold at `lem:adjchar`'s content read, the general
slot at `θ` itself. -/
def countAt (d : Nat) (c : Shape) : Nat :=
  adjCount d (adjchar.theta d) c

/-- `lem:channels`' whole list at a residue, one decidable read:
over every shape at the matched degree the fast count reads the
table's occupancy. -/
def tableRead (d : Nat) : Prop :=
  ((allShapes d (2 * d)).all (fun c =>
    countAt d c == rowRead d c)) = true

instance (d : Nat) : Decidable (tableRead d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The first closure identity, cleared: `Σ m d = (d_f² - 1)²`. -/
def dimClosure (d : Nat) : Prop :=
  (rows d).foldl (fun acc r => acc + r.2 * weyldim.dimOf r.1) 0
    = (d * d - 1) * (d * d - 1)

instance (d : Nat) : Decidable (dimClosure d) :=
  inferInstanceAs (Decidable (_ = _))

/-- The second closure identity, cleared at the Casimir's second
member: `Σ m d · d_f Q = 4 d_f² (d_f² - 1)²`. -/
def casClosure (d : Nat) : Prop :=
  (rows d).foldl
    (fun acc r => acc + r.2 * weyldim.dimOf r.1 * c2hat.dfQ r.1) 0
    = 4 * (d * d) * ((d * d - 1) * (d * d - 1))

instance (d : Nat) : Decidable (casClosure d) :=
  inferInstanceAs (Decidable (_ = _))

/-! The closed-form Casimir column (`lem:channels`' table): each
row's cleared read at its own closed form, the `2θ` entry the tower
law's `m = 2` read (`prop:anchor`), the `θ` entry its `m = 1` read,
and the remaining rows their own row-list evaluations — `dfQ` a
class read at the full columns. -/

/-- The vacant family is fixed by the doubling map. -/
private theorem map_replicate_zero_two : ∀ n : Nat,
    (List.replicate n 0).map (fun k => k * 2) = List.replicate n 0
  | 0 => rfl
  | n + 1 => congrArg (List.cons 0) (map_replicate_zero_two n)

/-- The doubled occupancy at a raised key is the key raised twice. -/
private theorem map_bumpAt_two : ∀ (i : Nat) (l : List Nat),
    (ground.bumpAt i l).map (fun n => n * 2)
      = ground.bumpAt i (ground.bumpAt i (l.map (fun n => n * 2)))
  | i, [] => by
    have h : ground.bumpAt i ([] : List Nat) = [] := ground.bumpAt_nil i
    rw [h]
    show ([] : List Nat) = ground.bumpAt i (ground.bumpAt i [])
    rw [h, h]
  | 0, a :: t => by
    show (a + 1) * 2 :: t.map (fun n => n * 2)
      = (a * 2 + 1 + 1) :: t.map (fun n => n * 2)
    rw [ground.mulAddR a 1 2, Nat.one_mul 2,
      Nat.add_assoc (a * 2) 1 1]
  | i + 1, a :: t =>
    congrArg (List.cons (a * 2)) (map_bumpAt_two i t)

/-- The `2θ` row's stored shape is the tower's at `m = 2`, the
tex's own `m = 2` read of the tower law. -/
theorem row2Theta_towerShape : ∀ d : Nat,
    ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (d - 2)
      (ground.bumpAt (d - 2) (List.replicate d 0))))
      = anchor.towerShape d 2 := by
  intro d
  show ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (d - 2)
      (ground.bumpAt (d - 2) (List.replicate d 0))))
    = (ground.bumpAt 0
        (ground.bumpAt (d - 2) (List.replicate d 0))).map
      (fun n => n * 2)
  rw [map_bumpAt_two 0 (ground.bumpAt (d - 2) (List.replicate d 0)),
    map_bumpAt_two (d - 2) (List.replicate d 0),
    map_replicate_zero_two d]

/-! The column's arithmetic joins: the cleared read collects its
two folds at each row's own gap witness. -/

/-- The join at a row whose pair squares read `6 d_f` and whose row
weights fall six short of `4 d_f`. -/
private theorem joinQ (n q : Nat) (hq : q + 6 = 4 * n) :
    6 * n + n * q = 4 * (n * n) := by
  rw [Nat.add_comm (6 * n) (n * q), Nat.mul_comm 6 n,
    ← Nat.left_distrib n q 6, hq, ← ground.mulAssoc n 4 n,
    Nat.mul_comm n 4, ground.mulAssoc 4 n n]

/-- The last row's join at its own gap witness `w + 2 = r`. -/
private theorem joinQ6 (m : Nat) :
    4 * (m + 2) + (m + 2) * (4 * m)
      = 2 * ((m + 2) * (m + 2)) + 2 * ((m + 2) * m) := by
  have hl : 4 * (m + 2) + (m + 2) * (4 * m) = (m + 2) * (4 + 4 * m) := by
    rw [Nat.mul_comm 4 (m + 2), ← Nat.left_distrib (m + 2) 4 (4 * m)]
  have hd : 2 * (m + 2 + m) = 4 + 4 * m := by
    rw [Nat.left_distrib 2 (m + 2) m, Nat.left_distrib 2 m 2,
      Nat.add_assoc (2 * m) (2 * 2) (2 * m),
      Nat.add_comm (2 * 2) (2 * m),
      ← Nat.add_assoc (2 * m) (2 * m) (2 * 2),
      ← ground.mulAddR 2 2 m, Nat.add_comm (4 * m) 4]
  have hr : 2 * ((m + 2) * (m + 2)) + 2 * ((m + 2) * m)
      = (m + 2) * (4 + 4 * m) := by
    rw [← Nat.left_distrib 2 ((m + 2) * (m + 2)) ((m + 2) * m),
      ← Nat.left_distrib (m + 2) (m + 2) m,
      ← ground.mulAssoc 2 (m + 2) (m + 2 + m),
      Nat.mul_comm 2 (m + 2), ground.mulAssoc (m + 2) 2 (m + 2 + m), hd]
  rw [hl, hr]

/-- The `2θ` row's display against the tower law's `m = 2` value. -/
private theorem join2Theta (n : Nat) :
    2 * n * (2 * (n + 1)) = 2 * (n * n) + 2 * (n * (n + 2)) := by
  have hd : 2 * (n + 1) = n + (n + 2) := by
    rw [Nat.left_distrib 2 n 1, Nat.mul_one 2, Nat.two_mul n,
      Nat.add_assoc n n 2]
  rw [ground.mulAssoc 2 n (2 * (n + 1)), hd,
    ← Nat.left_distrib 2 (n * n) (n * (n + 2)),
    ← Nat.left_distrib n n (n + 2)]

/-- The doubled row collects at its head. -/
private theorem twoRow (a b : Nat) : a + (a + b) = 2 * a + b := by
  rw [← Nat.add_assoc a a b, ← Nat.two_mul a]

/-! The row lists' two folds at the four evaluated rows. -/

private theorem sq4 (k : Nat) :
    c2hat.sqGaps (3 :: (List.replicate k 1 ++ List.replicate 2 0))
      = 6 * (k + 3) := by
  show (List.replicate k 1 ++ List.replicate 2 0).foldl
        (fun acc y => acc + (3 - y) * (3 - y)) 0
      + c2hat.sqGaps (List.replicate k 1 ++ List.replicate 2 0)
    = 6 * (k + 3)
  rw [ground.foldl_append (fun acc y => acc + (3 - y) * (3 - y))
      (List.replicate k 1) (List.replicate 2 0) 0,
    c2hat.sqFold_replicate 3 1 k 0,
    c2hat.sqGaps_replicate_app 1 k (List.replicate 2 0)]
  show 0 + k * 4 + 9 + 9 + (k * 2 + 0) = 6 * (k + 3)
  rw [Nat.zero_add (k * 4), Nat.add_zero (k * 2), Nat.mul_comm k 4,
    Nat.mul_comm k 2, Nat.left_distrib 6 k 3]
  show 4 * k + 18 + 2 * k = 6 * k + 18
  rw [Nat.add_right_comm (4 * k) 18 (2 * k), ← ground.mulAddR 4 2 k]

private theorem rh4 (k : Nat) :
    c2hat.rho2 (3 :: (List.replicate k 1 ++ List.replicate 2 0))
      = 4 * k + 6 := by
  show (List.replicate k 1 ++ List.replicate 2 0).foldl
        (fun acc y => acc + (3 - y)) 0
      + c2hat.rho2 (List.replicate k 1 ++ List.replicate 2 0)
    = 4 * k + 6
  rw [ground.foldl_append (fun acc y => acc + (3 - y))
      (List.replicate k 1) (List.replicate 2 0) 0,
    c2hat.gapFold_replicate 3 1 k 0,
    c2hat.rho2_replicate_app 1 k (List.replicate 2 0)]
  show 0 + k * 2 + 3 + 3 + (k * 2 + 0) = 4 * k + 6
  rw [Nat.zero_add (k * 2), Nat.add_zero (k * 2), Nat.mul_comm k 2]
  show 2 * k + 6 + 2 * k = 4 * k + 6
  rw [Nat.add_right_comm (2 * k) 6 (2 * k), ← ground.mulAddR 2 2 k]

private theorem sq5 (k : Nat) :
    c2hat.sqGaps (3 :: 3 :: (List.replicate k 2 ++ List.replicate 1 0))
      = 6 * (k + 3) := by
  show (List.replicate k 2 ++ List.replicate 1 0).foldl
        (fun acc y => acc + (3 - y) * (3 - y)) 0
      + ((List.replicate k 2 ++ List.replicate 1 0).foldl
          (fun acc y => acc + (3 - y) * (3 - y)) 0
        + c2hat.sqGaps (List.replicate k 2 ++ List.replicate 1 0))
    = 6 * (k + 3)
  rw [ground.foldl_append (fun acc y => acc + (3 - y) * (3 - y))
      (List.replicate k 2) (List.replicate 1 0) 0,
    c2hat.sqFold_replicate 3 2 k 0,
    c2hat.sqGaps_replicate_app 2 k (List.replicate 1 0)]
  show 0 + k * 1 + 9 + (0 + k * 1 + 9 + (k * 4 + 0)) = 6 * (k + 3)
  rw [Nat.zero_add (k * 1), Nat.add_zero (k * 4), Nat.mul_one k,
    twoRow (k + 9) (k * 4), Nat.left_distrib 2 k 9,
    Nat.mul_comm k 4, Nat.add_right_comm (2 * k) (2 * 9) (4 * k),
    ← ground.mulAddR 2 4 k, Nat.left_distrib 6 k 3]

private theorem rh5 (k : Nat) :
    c2hat.rho2 (3 :: 3 :: (List.replicate k 2 ++ List.replicate 1 0))
      = 4 * k + 6 := by
  show (List.replicate k 2 ++ List.replicate 1 0).foldl
        (fun acc y => acc + (3 - y)) 0
      + ((List.replicate k 2 ++ List.replicate 1 0).foldl
          (fun acc y => acc + (3 - y)) 0
        + c2hat.rho2 (List.replicate k 2 ++ List.replicate 1 0))
    = 4 * k + 6
  rw [ground.foldl_append (fun acc y => acc + (3 - y))
      (List.replicate k 2) (List.replicate 1 0) 0,
    c2hat.gapFold_replicate 3 2 k 0,
    c2hat.rho2_replicate_app 2 k (List.replicate 1 0)]
  show 0 + k * 1 + 3 + (0 + k * 1 + 3 + (k * 2 + 0)) = 4 * k + 6
  rw [Nat.zero_add (k * 1), Nat.add_zero (k * 2), Nat.mul_one k,
    twoRow (k + 3) (k * 2), Nat.left_distrib 2 k 3,
    Nat.mul_comm k 2, Nat.add_right_comm (2 * k) (2 * 3) (2 * k),
    ← ground.mulAddR 2 2 k]

private theorem sq6 (k : Nat) :
    c2hat.sqGaps (2 :: 2 :: (List.replicate k 1 ++ List.replicate 2 0))
      = 4 * (k + 4) := by
  show (List.replicate k 1 ++ List.replicate 2 0).foldl
        (fun acc y => acc + (2 - y) * (2 - y)) 0
      + ((List.replicate k 1 ++ List.replicate 2 0).foldl
          (fun acc y => acc + (2 - y) * (2 - y)) 0
        + c2hat.sqGaps (List.replicate k 1 ++ List.replicate 2 0))
    = 4 * (k + 4)
  rw [ground.foldl_append (fun acc y => acc + (2 - y) * (2 - y))
      (List.replicate k 1) (List.replicate 2 0) 0,
    c2hat.sqFold_replicate 2 1 k 0,
    c2hat.sqGaps_replicate_app 1 k (List.replicate 2 0)]
  show 0 + k * 1 + 4 + 4 + (0 + k * 1 + 4 + 4 + (k * 2 + 0)) = 4 * (k + 4)
  rw [Nat.zero_add (k * 1), Nat.add_zero (k * 2), Nat.mul_one k,
    Nat.add_assoc k 4 4, twoRow (k + (4 + 4)) (k * 2),
    Nat.left_distrib 2 k (4 + 4), Nat.mul_comm k 2,
    Nat.add_right_comm (2 * k) (2 * (4 + 4)) (2 * k),
    ← ground.mulAddR 2 2 k, Nat.left_distrib 4 k 4]

private theorem rh6 (k : Nat) :
    c2hat.rho2 (2 :: 2 :: (List.replicate k 1 ++ List.replicate 2 0))
      = 4 * (k + 2) := by
  show (List.replicate k 1 ++ List.replicate 2 0).foldl
        (fun acc y => acc + (2 - y)) 0
      + ((List.replicate k 1 ++ List.replicate 2 0).foldl
          (fun acc y => acc + (2 - y)) 0
        + c2hat.rho2 (List.replicate k 1 ++ List.replicate 2 0))
    = 4 * (k + 2)
  rw [ground.foldl_append (fun acc y => acc + (2 - y))
      (List.replicate k 1) (List.replicate 2 0) 0,
    c2hat.gapFold_replicate 2 1 k 0,
    c2hat.rho2_replicate_app 1 k (List.replicate 2 0)]
  show 0 + k * 1 + 2 + 2 + (0 + k * 1 + 2 + 2 + (k * 2 + 0)) = 4 * (k + 2)
  rw [Nat.zero_add (k * 1), Nat.add_zero (k * 2), Nat.mul_one k,
    Nat.add_assoc k 2 2, twoRow (k + (2 + 2)) (k * 2),
    Nat.left_distrib 2 k (2 + 2), Nat.mul_comm k 2,
    Nat.add_right_comm (2 * k) (2 * (2 + 2)) (2 * k),
    ← ground.mulAddR 2 2 k, Nat.left_distrib 4 k 2]

/-! The reduced shapes' split families and their rows: each row's
stored shape at one occupied key over a vacant family, with the row
list read off it. -/

/-- The `2θ` row's stored shape at the split families. -/
private theorem shapeTwoTheta (h : Nat) :
    ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (h + 5 - 2)
      (ground.bumpAt (h + 5 - 2) (List.replicate (h + 5) 0))))
      = 2 :: (List.replicate (h + 2) 0 ++ 2 :: List.replicate 1 0) := by
  have hsp : (List.replicate (h + 5) 0 : List Nat)
      = List.replicate (h + 3) 0 ++ 0 :: List.replicate 1 0 :=
    places.replicate_split 0 (h + 3) 1
  show ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (h + 3)
      (ground.bumpAt (h + 3) (List.replicate (h + 5) 0))))
    = 2 :: (List.replicate (h + 2) 0 ++ 2 :: List.replicate 1 0)
  rw [hsp, places.bumpAt_split (h + 3) 0 (List.replicate 1 0),
    places.bumpAt_split (h + 3) (0 + 1) (List.replicate 1 0)]
  rfl

/-- The `2θ` row's rows: the doubled head over the run of doubled
rows with the trailing vacancy. -/
private theorem rowListTwoTheta (h : Nat) :
    places.rowList
      (2 :: (List.replicate (h + 2) 0 ++ 2 :: List.replicate 1 0))
      = 4 :: (List.replicate (h + 3) 2 ++ List.replicate 1 0) := by
  show (2 + ground.sumNat
        (List.replicate (h + 2) 0 ++ 2 :: List.replicate 1 0))
      :: places.rowList
        (List.replicate (h + 2) 0 ++ 2 :: List.replicate 1 0)
    = 4 :: (List.replicate (h + 3) 2 ++ List.replicate 1 0)
  rw [places.sumNat_pointAt (h + 2) 1 2,
    places.rowList_pointAt (h + 2) 1 2]

/-- The dual pair's first member: the stored shape at the split
families. -/
private theorem shapeDualA (h : Nat) :
    ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (h + 5 - 3)
      (List.replicate (h + 5) 0)))
      = 2 :: (List.replicate (h + 1) 0 ++ 1 :: List.replicate 2 0) := by
  have hsp : (List.replicate (h + 5) 0 : List Nat)
      = List.replicate (h + 2) 0 ++ 0 :: List.replicate 2 0 :=
    places.replicate_split 0 (h + 2) 2
  show ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (h + 2)
      (List.replicate (h + 5) 0)))
    = 2 :: (List.replicate (h + 1) 0 ++ 1 :: List.replicate 2 0)
  rw [hsp, places.bumpAt_split (h + 2) 0 (List.replicate 2 0)]
  rfl

/-- The dual pair's first member: its rows. -/
private theorem rowListDualA (h : Nat) :
    places.rowList
      (2 :: (List.replicate (h + 1) 0 ++ 1 :: List.replicate 2 0))
      = 3 :: (List.replicate (h + 2) 1 ++ List.replicate 2 0) := by
  show (2 + ground.sumNat
        (List.replicate (h + 1) 0 ++ 1 :: List.replicate 2 0))
      :: places.rowList
        (List.replicate (h + 1) 0 ++ 1 :: List.replicate 2 0)
    = 3 :: (List.replicate (h + 2) 1 ++ List.replicate 2 0)
  rw [places.sumNat_pointAt (h + 1) 2 1,
    places.rowList_pointAt (h + 1) 2 1]

/-- The dual pair's second member: the stored shape at the split
families. -/
private theorem shapeDualB (h : Nat) :
    ground.bumpAt 1 (ground.bumpAt (h + 5 - 2)
      (ground.bumpAt (h + 5 - 2) (List.replicate (h + 5) 0)))
      = 0 :: 1 :: (List.replicate (h + 1) 0
        ++ 2 :: List.replicate 1 0) := by
  have hsp : (List.replicate (h + 5) 0 : List Nat)
      = List.replicate (h + 3) 0 ++ 0 :: List.replicate 1 0 :=
    places.replicate_split 0 (h + 3) 1
  show ground.bumpAt 1 (ground.bumpAt (h + 3)
      (ground.bumpAt (h + 3) (List.replicate (h + 5) 0)))
    = 0 :: 1 :: (List.replicate (h + 1) 0 ++ 2 :: List.replicate 1 0)
  rw [hsp, places.bumpAt_split (h + 3) 0 (List.replicate 1 0),
    places.bumpAt_split (h + 3) (0 + 1) (List.replicate 1 0)]
  rfl

/-- The dual pair's second member: its rows. -/
private theorem rowListDualB (h : Nat) :
    places.rowList
      (0 :: 1 :: (List.replicate (h + 1) 0 ++ 2 :: List.replicate 1 0))
      = 3 :: 3 :: (List.replicate (h + 2) 2 ++ List.replicate 1 0) := by
  show (0 + (1 + ground.sumNat
        (List.replicate (h + 1) 0 ++ 2 :: List.replicate 1 0)))
      :: (1 + ground.sumNat
          (List.replicate (h + 1) 0 ++ 2 :: List.replicate 1 0))
      :: places.rowList
          (List.replicate (h + 1) 0 ++ 2 :: List.replicate 1 0)
    = 3 :: 3 :: (List.replicate (h + 2) 2 ++ List.replicate 1 0)
  rw [places.sumNat_pointAt (h + 1) 1 2,
    places.rowList_pointAt (h + 1) 1 2]

/-- The `ω₂ + ω₂*` row: the stored shape at the split families. -/
private theorem shapeOmega (h : Nat) :
    ground.bumpAt 1 (ground.bumpAt (h + 5 - 3) (List.replicate (h + 5) 0))
      = 0 :: 1 :: (List.replicate h 0 ++ 1 :: List.replicate 2 0) := by
  have hsp : (List.replicate (h + 5) 0 : List Nat)
      = List.replicate (h + 2) 0 ++ 0 :: List.replicate 2 0 :=
    places.replicate_split 0 (h + 2) 2
  show ground.bumpAt 1 (ground.bumpAt (h + 2) (List.replicate (h + 5) 0))
    = 0 :: 1 :: (List.replicate h 0 ++ 1 :: List.replicate 2 0)
  rw [hsp, places.bumpAt_split (h + 2) 0 (List.replicate 2 0)]
  rfl

/-- The `ω₂ + ω₂*` row: its rows. -/
private theorem rowListOmega (h : Nat) :
    places.rowList
      (0 :: 1 :: (List.replicate h 0 ++ 1 :: List.replicate 2 0))
      = 2 :: 2 :: (List.replicate (h + 1) 1 ++ List.replicate 2 0) := by
  show (0 + (1 + ground.sumNat
        (List.replicate h 0 ++ 1 :: List.replicate 2 0)))
      :: (1 + ground.sumNat (List.replicate h 0 ++ 1 :: List.replicate 2 0))
      :: places.rowList (List.replicate h 0 ++ 1 :: List.replicate 2 0)
    = 2 :: 2 :: (List.replicate (h + 1) 1 ++ List.replicate 2 0)
  rw [places.sumNat_pointAt h 2 1, places.rowList_pointAt h 2 1]

/-! The six rows' cleared reads, each at its own closed form. -/

/-- The unit channel sits at the Casimir's kernel point: the two
full columns leave the vacant shape's read. -/
private theorem row1 (d : Nat) : c2hat.dfQ (rowUnit d) = 0 := by
  show c2hat.dfQ (ground.bumpAt (d - 1)
    (ground.bumpAt (d - 1) (List.replicate d 0))) = 0
  have hz : (List.replicate d 0 : List Nat).length = d :=
    ground.length_replicate 0 d
  have hb : (ground.bumpAt (d - 1) (List.replicate d 0)).length = d := by
    rw [ground.length_bumpAt, hz]
  have k1 := c2hat.dfQ_full (ground.bumpAt (d - 1) (List.replicate d 0))
  rw [hb] at k1
  have k2 := c2hat.dfQ_full (List.replicate d 0 : List Nat)
  rw [hz] at k2
  rw [k1, k2, c2hat.dfQ_replicate_zero d]

/-- The `θ` row reads `2 d_f²`, the tower law's `m = 1` value at
the full column's class read. -/
private theorem row2 (h : Nat) :
    c2hat.dfQ (rowTheta (h + 5)) = 2 * ((h + 5) * (h + 5)) := by
  show c2hat.dfQ (ground.bumpAt (h + 5 - 1) (adjchar.theta (h + 5)))
    = 2 * ((h + 5) * (h + 5))
  have ht : (adjchar.theta (h + 5)).length = h + 5 :=
    adjchar.length_theta (h + 5)
  have k1 := c2hat.dfQ_full (adjchar.theta (h + 5))
  rw [ht] at k1
  have hone : anchor.towerShape (h + 5) 1 = adjchar.theta (h + 5) :=
    anchor.towerShape_one (h + 5)
  have k2 := anchor.tower_dfQ (h + 5) 1 (Nat.le_add_left 2 (h + 3))
  rw [hone] at k2
  have h12 : 1 + (h + 5 - 1) = h + 5 := by
    show 1 + (h + 4) = h + 5
    rw [Nat.add_comm 1 (h + 4)]
  rw [k1, k2, Nat.one_mul (1 + (h + 5 - 1)), h12,
    ground.mulAssoc 2 (h + 5) (h + 5)]

/-- The `2θ` row reads the tower law's `m = 2` value with the
distance join displayed. -/
private theorem row3 (h : Nat) :
    c2hat.dfQ (rowTwoTheta (h + 5))
      = 2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 5 + 2)) := by
  show c2hat.dfQ (ground.bumpAt 0 (ground.bumpAt 0
      (ground.bumpAt (h + 5 - 2) (ground.bumpAt (h + 5 - 2)
        (List.replicate (h + 5) 0)))))
    = 2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 5 + 2))
  have hd : 2 + (h + 5 - 1) = h + 5 + 1 := by
    show 2 + (h + 4) = h + 5 + 1
    rw [Nat.add_comm 2 (h + 4)]
  rw [row2Theta_towerShape (h + 5),
    anchor.tower_dfQ (h + 5) 2 (Nat.le_add_left 2 (h + 3)), hd]
  exact join2Theta (h + 5)

/-- The dual pair's first member reads `4 d_f²` at the row list
`(4, 2^{d_f - 3}, 1, 1)`. -/
private theorem row4 (h : Nat) :
    c2hat.dfQ (rowDualA (h + 5)) = 4 * ((h + 5) * (h + 5)) := by
  show c2hat.dfQ (ground.bumpAt (h + 5 - 1) (ground.bumpAt 0
      (ground.bumpAt 0 (ground.bumpAt (h + 5 - 3)
        (List.replicate (h + 5) 0)))))
    = 4 * ((h + 5) * (h + 5))
  have hz : (List.replicate (h + 5) 0 : List Nat).length = h + 5 :=
    ground.length_replicate 0 (h + 5)
  have hlen : (ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (h + 5 - 3)
      (List.replicate (h + 5) 0)))).length = h + 5 := by
    rw [ground.length_bumpAt, ground.length_bumpAt,
      ground.length_bumpAt, hz]
  have k1 := c2hat.dfQ_full (ground.bumpAt 0 (ground.bumpAt 0
      (ground.bumpAt (h + 5 - 3) (List.replicate (h + 5) 0))))
  rw [hlen] at k1
  have hin := shapeDualA h
  have hrow := rowListDualA h
  have hlen2 : (2 :: (List.replicate (h + 1) 0
      ++ 1 :: List.replicate 2 0)).length = h + 5 := by
    rw [← hin, hlen]
  rw [k1, hin]
  show c2hat.sqGaps (places.rowList
        (2 :: (List.replicate (h + 1) 0 ++ 1 :: List.replicate 2 0)))
      + (2 :: (List.replicate (h + 1) 0
          ++ 1 :: List.replicate 2 0)).length
        * c2hat.rho2 (places.rowList
          (2 :: (List.replicate (h + 1) 0 ++ 1 :: List.replicate 2 0)))
    = 4 * ((h + 5) * (h + 5))
  rw [hrow, hlen2, sq4 (h + 2), rh4 (h + 2)]
  exact joinQ (h + 5) (4 * (h + 2) + 6) (by
    rw [Nat.add_assoc (4 * (h + 2)) 6 6, Nat.left_distrib 4 h 2,
      Nat.left_distrib 4 h 5, Nat.add_assoc (4 * h) (4 * 2) (6 + 6)])

/-- The dual pair's second member reads `4 d_f²` at the row list
`(3, 3, 2^{d_f - 3}, 0)`, the balance partner's own. -/
private theorem row5 (h : Nat) :
    c2hat.dfQ (rowDualB (h + 5)) = 4 * ((h + 5) * (h + 5)) := by
  show c2hat.dfQ (ground.bumpAt 1 (ground.bumpAt (h + 5 - 2)
      (ground.bumpAt (h + 5 - 2) (List.replicate (h + 5) 0))))
    = 4 * ((h + 5) * (h + 5))
  have hz : (List.replicate (h + 5) 0 : List Nat).length = h + 5 :=
    ground.length_replicate 0 (h + 5)
  have hlen : (ground.bumpAt 1 (ground.bumpAt (h + 5 - 2)
      (ground.bumpAt (h + 5 - 2) (List.replicate (h + 5) 0)))).length
      = h + 5 := by
    rw [ground.length_bumpAt, ground.length_bumpAt,
      ground.length_bumpAt, hz]
  have hin := shapeDualB h
  have hrow := rowListDualB h
  have hlen2 : (0 :: 1 :: (List.replicate (h + 1) 0
      ++ 2 :: List.replicate 1 0)).length = h + 5 := by
    rw [← hin, hlen]
  rw [hin]
  show c2hat.sqGaps (places.rowList
        (0 :: 1 :: (List.replicate (h + 1) 0 ++ 2 :: List.replicate 1 0)))
      + (0 :: 1 :: (List.replicate (h + 1) 0
          ++ 2 :: List.replicate 1 0)).length
        * c2hat.rho2 (places.rowList
          (0 :: 1 :: (List.replicate (h + 1) 0
            ++ 2 :: List.replicate 1 0)))
    = 4 * ((h + 5) * (h + 5))
  rw [hrow, hlen2, sq5 (h + 2), rh5 (h + 2)]
  exact joinQ (h + 5) (4 * (h + 2) + 6) (by
    rw [Nat.add_assoc (4 * (h + 2)) 6 6, Nat.left_distrib 4 h 2,
      Nat.left_distrib 4 h 5, Nat.add_assoc (4 * h) (4 * 2) (6 + 6)])

/-- The last row reads `2 d_f² + 2 d_f (d_f - 2)` at the row list
`(3, 3, 2^{d_f - 4}, 1, 1)`, its gap witness `w + 2 = r`. -/
private theorem row6 (h : Nat) :
    c2hat.dfQ (rowOmega (h + 5))
      = 2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 5 - 2)) := by
  show c2hat.dfQ (ground.bumpAt (h + 5 - 1) (ground.bumpAt 1
      (ground.bumpAt (h + 5 - 3) (List.replicate (h + 5) 0))))
    = 2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 5 - 2))
  have hz : (List.replicate (h + 5) 0 : List Nat).length = h + 5 :=
    ground.length_replicate 0 (h + 5)
  have hlen : (ground.bumpAt 1 (ground.bumpAt (h + 5 - 3)
      (List.replicate (h + 5) 0))).length = h + 5 := by
    rw [ground.length_bumpAt, ground.length_bumpAt, hz]
  have k1 := c2hat.dfQ_full (ground.bumpAt 1
      (ground.bumpAt (h + 5 - 3) (List.replicate (h + 5) 0)))
  rw [hlen] at k1
  have hin := shapeOmega h
  have hrow := rowListOmega h
  have hlen2 : (0 :: 1 :: (List.replicate h 0
      ++ 1 :: List.replicate 2 0)).length = h + 5 := by
    rw [← hin, hlen]
  rw [k1, hin]
  show c2hat.sqGaps (places.rowList
        (0 :: 1 :: (List.replicate h 0 ++ 1 :: List.replicate 2 0)))
      + (0 :: 1 :: (List.replicate h 0 ++ 1 :: List.replicate 2 0)).length
        * c2hat.rho2 (places.rowList
          (0 :: 1 :: (List.replicate h 0 ++ 1 :: List.replicate 2 0)))
    = 2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 5 - 2))
  rw [hrow, hlen2, sq6 (h + 1), rh6 (h + 1)]
  exact joinQ6 (h + 3)

/-- The six rows' cleared Casimir column at every residue, each entry
its closed form with the distance join displayed: the unit at the
kernel point, `θ` at the adjoint's `2 d_f²`, `2θ` at the tower's
`m = 2` read `2d² + 2d(d+2)`, the dual pair at `2·2d²`, and
`ω₂ + ω₂*` at `2d² + 2d(d−2)`. -/
theorem rows_dfQ : ∀ d : Nat, 2 ≤ d →
    (rows d).map (fun p => c2hat.dfQ p.1)
      = [0, 2 * (d * d), 2 * (d * d) + 2 * (d * (d + 2))]
        ++ (if 3 ≤ d then [4 * (d * d), 4 * (d * d)] else [])
        ++ (if 4 ≤ d then [2 * (d * d) + 2 * (d * (d - 2))] else []) := by
  intro d hd
  have hg := Nat.le.dest hd
  match hg with
  | ⟨g, hgd⟩ =>
    have hdg : d = g + 2 := by rw [← hgd, Nat.add_comm 2 g]
    rw [hdg]
    match g with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | h + 3 =>
      show [c2hat.dfQ (rowUnit (h + 5)),
            c2hat.dfQ (rowTheta (h + 5)),
            c2hat.dfQ (rowTwoTheta (h + 5)),
            c2hat.dfQ (rowDualA (h + 5)),
            c2hat.dfQ (rowDualB (h + 5)),
            c2hat.dfQ (rowOmega (h + 5))]
        = [0, 2 * ((h + 5) * (h + 5)),
           2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 5 + 2)),
           4 * ((h + 5) * (h + 5)), 4 * ((h + 5) * (h + 5)),
           2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 5 - 2))]
      rw [row1 (h + 5), row2 h, row3 h, row4 h, row5 h, row6 h]

/-- The `2θ` distance's positivity at every residue: the column's
second summand occupied, the gap `[r+3 : r+1]` at its
cross-multiplied witness `2r+4 = (r+1)+(r+3)`. -/
theorem dist2Theta_pos : ∀ d : Nat, 2 ≤ d → 0 < 2 * (d * (d + 2)) := by
  intro d hd
  match d, hd with
  | dd + 2, _ =>
    exact Nat.mul_pos (Nat.succ_pos 1)
      (Nat.mul_pos (Nat.succ_pos (dd + 1)) (Nat.succ_pos (dd + 3)))

/-- The `ω₂ + ω₂*` distance's positivity at its row's residues: the
gap `[g : r+1]` at `g + 1 = r`, its cross-multiplied witness
`2r = (r+1)+g`. -/
theorem distOmega_pos : ∀ d : Nat, 4 ≤ d → 0 < 2 * (d * (d - 2)) := by
  intro d hd
  match d, hd with
  | dd + 4, _ =>
    exact Nat.mul_pos (Nat.succ_pos 1)
      (Nat.mul_pos (Nat.succ_pos (dd + 3)) (Nat.succ_pos (dd + 1)))


/-! The dimension tier (`cor:weyldim`'s telescopes at the stored
shapes): each row's display is a descending run at its own floor
with the head's raises above it and the lowest entries beneath, the
gap product reads the run's factorials against the tail's folds,
and the naming identity clears the unit product — the six closed
forms are `rows_dim`, and the folds over them close the two
identities (`dimClosureAll`, `casClosureAll`), the self-dual outer
rows collecting at the residue's crossed pair and the dual pair
entering twice at its gap witness. -/

/-- A full column's rows at a stated length. -/
private theorem rowList_top (s : Shape) (n : Nat) (hn : s.length = n) :
    places.rowList (ground.bumpAt (n - 1) s)
      = (places.rowList s).map (fun x => x + 1) := by
  rw [← hn]
  exact places.rowList_full s

/-- The unit channel's display is the run two above the unit
floor. -/
private theorem dispUnit (h : Nat) :
    places.display (rowUnit (h + 5)) = weyldim.descRun 3 (h + 5) := by
  show places.display (ground.bumpAt (h + 5 - 1) (ground.bumpAt (h + 5 - 1)
    (List.replicate (h + 5) 0))) = weyldim.descRun 3 (h + 5)
  have hz : (List.replicate (h + 5) 0 : List Nat).length = h + 5 :=
    ground.length_replicate 0 (h + 5)
  have hb : (ground.bumpAt (h + 5 - 1) (List.replicate (h + 5) 0)).length
      = h + 5 := by
    rw [ground.length_bumpAt, hz]
  have hb2 : (ground.bumpAt (h + 5 - 1) (ground.bumpAt (h + 5 - 1)
      (List.replicate (h + 5) 0))).length = h + 5 := by
    rw [ground.length_bumpAt, hb]
  have hrow : places.rowList (ground.bumpAt (h + 5 - 1)
      (ground.bumpAt (h + 5 - 1) (List.replicate (h + 5) 0)))
      = List.replicate (h + 5) 2 := by
    rw [rowList_top _ (h + 5) hb, rowList_top _ (h + 5) hz,
      places.rowList_replicate_zero (h + 5),
      ground.map_replicate (fun x => x + 1) 0 (h + 5),
      ground.map_replicate (fun x => x + 1) 1 (h + 5)]
  rw [weylchar.display_zip, hb2, hrow, weyldim.unitDisp_descRun (h + 5),
    weyldim.zipWith_descRun 2 1 (h + 5)]


/-- The `θ` row's display: the raised head over the run at four
with the row's own floor. -/
private theorem dispTheta (h : Nat) :
    places.display (rowTheta (h + 5))
      = (h + 8) :: (weyldim.descRun 4 (h + 3) ++ [2]) := by
  show places.display (ground.bumpAt (h + 5 - 1) (adjchar.theta (h + 5)))
    = (h + 8) :: (weyldim.descRun 4 (h + 3) ++ [2])
  have ht : (adjchar.theta (h + 5)).length = h + 5 :=
    adjchar.length_theta (h + 5)
  have hb : (ground.bumpAt (h + 5 - 1) (adjchar.theta (h + 5))).length
      = h + 5 := by
    rw [ground.length_bumpAt, ht]
  have hrow : places.rowList
      (ground.bumpAt (h + 5 - 1) (adjchar.theta (h + 5)))
      = 3 :: (List.replicate (h + 3) 2 ++ [1]) := by
    rw [rowList_top _ (h + 5) ht,
      show places.rowList (adjchar.theta (h + 5))
        = 2 :: (List.replicate (h + 3) 1 ++ [0])
        from adjchar.rowList_theta (h + 3)]
    show (2 + 1) :: (List.replicate (h + 3) 1 ++ [0]).map (fun x => x + 1)
      = 3 :: (List.replicate (h + 3) 2 ++ [1])
    rw [ground.map_append (fun x => x + 1) (List.replicate (h + 3) 1) [0],
      ground.map_replicate (fun x => x + 1) 1 (h + 3)]
    rfl
  have hdr : weyldim.descRun 1 (h + 5)
      = (h + 5) :: (weyldim.descRun 2 (h + 3) ++ [1]) := by
    have e1 : weyldim.descRun 1 (h + 4)
        = weyldim.descRun 2 (h + 3) ++ [1] :=
      weyldim.descRun_snoc 1 (h + 3)
    show (h + 4 + 1) :: weyldim.descRun 1 (h + 4) = _
    rw [e1]
  rw [weylchar.display_zip, hb, hrow, weyldim.unitDisp_descRun (h + 5),
    hdr]
  show (3 + (h + 5)) :: List.zipWith (fun l u => l + u)
      (List.replicate (h + 3) 2 ++ [1])
      (weyldim.descRun 2 (h + 3) ++ [1])
    = (h + 8) :: (weyldim.descRun 4 (h + 3) ++ [2])
  rw [ground.zipWith_append (fun l u => l + u) (List.replicate (h + 3) 2)
      [1] (weyldim.descRun 2 (h + 3)) [1]
      (by rw [ground.length_replicate, weyldim.length_descRun]),
    weyldim.zipWith_descRun 2 2 (h + 3), Nat.add_comm 3 (h + 5)]
  rfl

/-- The `2θ` row's display. -/
private theorem dispTwoTheta (h : Nat) :
    places.display (rowTwoTheta (h + 5))
      = (h + 9) :: (weyldim.descRun 4 (h + 3) ++ [1]) := by
  show places.display (ground.bumpAt 0 (ground.bumpAt 0
      (ground.bumpAt (h + 5 - 2) (ground.bumpAt (h + 5 - 2)
        (List.replicate (h + 5) 0)))))
    = (h + 9) :: (weyldim.descRun 4 (h + 3) ++ [1])
  have hlen : (2 :: (List.replicate (h + 2) 0
      ++ 2 :: List.replicate 1 0) : Shape).length = h + 5 := by
    rw [← shapeTwoTheta h, ground.length_bumpAt, ground.length_bumpAt,
      ground.length_bumpAt, ground.length_bumpAt,
      ground.length_replicate]
  have hdr : weyldim.descRun 1 (h + 5)
      = (h + 5) :: (weyldim.descRun 2 (h + 3) ++ [1]) := by
    have e1 : weyldim.descRun 1 (h + 4)
        = weyldim.descRun 2 (h + 3) ++ [1] :=
      weyldim.descRun_snoc 1 (h + 3)
    show (h + 4 + 1) :: weyldim.descRun 1 (h + 4) = _
    rw [e1]
  rw [shapeTwoTheta h, weylchar.display_zip, hlen, rowListTwoTheta h,
    weyldim.unitDisp_descRun (h + 5), hdr]
  show (4 + (h + 5)) :: List.zipWith (fun l u => l + u)
      (List.replicate (h + 3) 2 ++ List.replicate 1 0)
      (weyldim.descRun 2 (h + 3) ++ [1])
    = (h + 9) :: (weyldim.descRun 4 (h + 3) ++ [1])
  rw [ground.zipWith_append (fun l u => l + u) (List.replicate (h + 3) 2)
      (List.replicate 1 0) (weyldim.descRun 2 (h + 3)) [1]
      (by rw [ground.length_replicate, weyldim.length_descRun]),
    weyldim.zipWith_descRun 2 2 (h + 3), Nat.add_comm 4 (h + 5)]
  rfl

/-- The dual pair's first member: its display. -/
private theorem dispDualA (h : Nat) :
    places.display (rowDualA (h + 5))
      = (h + 9) :: (weyldim.descRun 5 (h + 2) ++ [3, 2]) := by
  show places.display (ground.bumpAt (h + 5 - 1) (ground.bumpAt 0
      (ground.bumpAt 0 (ground.bumpAt (h + 5 - 3)
        (List.replicate (h + 5) 0)))))
    = (h + 9) :: (weyldim.descRun 5 (h + 2) ++ [3, 2])
  have hin : (2 :: (List.replicate (h + 1) 0
      ++ 1 :: List.replicate 2 0) : Shape).length = h + 5 := by
    rw [← shapeDualA h, ground.length_bumpAt, ground.length_bumpAt,
      ground.length_bumpAt, ground.length_replicate]
  have hlen : (ground.bumpAt (h + 5 - 1) (2 :: (List.replicate (h + 1) 0
      ++ 1 :: List.replicate 2 0))).length = h + 5 := by
    rw [ground.length_bumpAt, hin]
  have hdr : weyldim.descRun 1 (h + 5)
      = (h + 5) :: (weyldim.descRun 3 (h + 2) ++ [2, 1]) := by
    have e1 : weyldim.descRun 1 (h + 4)
        = weyldim.descRun 2 (h + 3) ++ [1] :=
      weyldim.descRun_snoc 1 (h + 3)
    have e2 : weyldim.descRun 2 (h + 3)
        = weyldim.descRun 3 (h + 2) ++ [2] :=
      weyldim.descRun_snoc 2 (h + 2)
    show (h + 4 + 1) :: weyldim.descRun 1 (h + 4) = _
    rw [e1, e2, ground.append_assoc (weyldim.descRun 3 (h + 2)) [2] [1]]
    rfl
  rw [shapeDualA h, weylchar.display_zip, hlen,
    rowList_top _ (h + 5) hin, rowListDualA h,
    weyldim.unitDisp_descRun (h + 5), hdr]
  show (3 + 1 + (h + 5)) :: List.zipWith (fun l u => l + u)
      ((List.replicate (h + 2) 1 ++ List.replicate 2 0).map
        (fun x => x + 1))
      (weyldim.descRun 3 (h + 2) ++ [2, 1])
    = (h + 9) :: (weyldim.descRun 5 (h + 2) ++ [3, 2])
  rw [ground.map_append (fun x => x + 1) (List.replicate (h + 2) 1)
      (List.replicate 2 0),
    ground.map_replicate (fun x => x + 1) 1 (h + 2),
    ground.map_replicate (fun x => x + 1) 0 2,
    ground.zipWith_append (fun l u => l + u) (List.replicate (h + 2) 2)
      (List.replicate 2 1) (weyldim.descRun 3 (h + 2)) [2, 1]
      (by rw [ground.length_replicate, weyldim.length_descRun]),
    weyldim.zipWith_descRun 2 3 (h + 2), Nat.add_comm 4 (h + 5)]
  rfl

/-- The dual pair's second member: its display. -/
private theorem dispDualB (h : Nat) :
    places.display (rowDualB (h + 5))
      = (h + 8) :: (h + 7) :: (weyldim.descRun 4 (h + 2) ++ [1]) := by
  show places.display (ground.bumpAt 1 (ground.bumpAt (h + 5 - 2)
      (ground.bumpAt (h + 5 - 2) (List.replicate (h + 5) 0))))
    = (h + 8) :: (h + 7) :: (weyldim.descRun 4 (h + 2) ++ [1])
  have hlen : (0 :: 1 :: (List.replicate (h + 1) 0
      ++ 2 :: List.replicate 1 0) : Shape).length = h + 5 := by
    rw [← shapeDualB h, ground.length_bumpAt, ground.length_bumpAt,
      ground.length_bumpAt, ground.length_replicate]
  have hdr : weyldim.descRun 1 (h + 5)
      = (h + 5) :: (h + 4) :: (weyldim.descRun 2 (h + 2) ++ [1]) := by
    have e1 : weyldim.descRun 1 (h + 3)
        = weyldim.descRun 2 (h + 2) ++ [1] :=
      weyldim.descRun_snoc 1 (h + 2)
    show (h + 4 + 1) :: (h + 3 + 1) :: weyldim.descRun 1 (h + 3) = _
    rw [e1]
  rw [shapeDualB h, weylchar.display_zip, hlen, rowListDualB h,
    weyldim.unitDisp_descRun (h + 5), hdr]
  show (3 + (h + 5)) :: (3 + (h + 4)) :: List.zipWith (fun l u => l + u)
      (List.replicate (h + 2) 2 ++ List.replicate 1 0)
      (weyldim.descRun 2 (h + 2) ++ [1])
    = (h + 8) :: (h + 7) :: (weyldim.descRun 4 (h + 2) ++ [1])
  rw [ground.zipWith_append (fun l u => l + u) (List.replicate (h + 2) 2)
      (List.replicate 1 0) (weyldim.descRun 2 (h + 2)) [1]
      (by rw [ground.length_replicate, weyldim.length_descRun]),
    weyldim.zipWith_descRun 2 2 (h + 2), Nat.add_comm 3 (h + 5),
    Nat.add_comm 3 (h + 4)]
  rfl

/-- The `ω₂ + ω₂*` row: its display. -/
private theorem dispOmega (h : Nat) :
    places.display (rowOmega (h + 5))
      = (h + 8) :: (h + 7) :: (weyldim.descRun 5 (h + 1) ++ [3, 2]) := by
  show places.display (ground.bumpAt (h + 5 - 1) (ground.bumpAt 1
      (ground.bumpAt (h + 5 - 3) (List.replicate (h + 5) 0))))
    = (h + 8) :: (h + 7) :: (weyldim.descRun 5 (h + 1) ++ [3, 2])
  have hin : (0 :: 1 :: (List.replicate h 0
      ++ 1 :: List.replicate 2 0) : Shape).length = h + 5 := by
    rw [← shapeOmega h, ground.length_bumpAt, ground.length_bumpAt,
      ground.length_replicate]
  have hlen : (ground.bumpAt (h + 5 - 1) (0 :: 1 :: (List.replicate h 0
      ++ 1 :: List.replicate 2 0))).length = h + 5 := by
    rw [ground.length_bumpAt, hin]
  have hdr : weyldim.descRun 1 (h + 5)
      = (h + 5) :: (h + 4) :: (weyldim.descRun 3 (h + 1) ++ [2, 1]) := by
    have e1 : weyldim.descRun 1 (h + 3)
        = weyldim.descRun 2 (h + 2) ++ [1] :=
      weyldim.descRun_snoc 1 (h + 2)
    have e2 : weyldim.descRun 2 (h + 2)
        = weyldim.descRun 3 (h + 1) ++ [2] :=
      weyldim.descRun_snoc 2 (h + 1)
    show (h + 4 + 1) :: (h + 3 + 1) :: weyldim.descRun 1 (h + 3) = _
    rw [e1, e2, ground.append_assoc (weyldim.descRun 3 (h + 1)) [2] [1]]
    rfl
  rw [shapeOmega h, weylchar.display_zip, hlen,
    rowList_top _ (h + 5) hin, rowListOmega h,
    weyldim.unitDisp_descRun (h + 5), hdr]
  show (2 + 1 + (h + 5)) :: (2 + 1 + (h + 4))
      :: List.zipWith (fun l u => l + u)
        ((List.replicate (h + 1) 1 ++ List.replicate 2 0).map
          (fun x => x + 1))
        (weyldim.descRun 3 (h + 1) ++ [2, 1])
    = (h + 8) :: (h + 7) :: (weyldim.descRun 5 (h + 1) ++ [3, 2])
  rw [ground.map_append (fun x => x + 1) (List.replicate (h + 1) 1)
      (List.replicate 2 0),
    ground.map_replicate (fun x => x + 1) 1 (h + 1),
    ground.map_replicate (fun x => x + 1) 0 2,
    ground.zipWith_append (fun l u => l + u) (List.replicate (h + 1) 2)
      (List.replicate 2 1) (weyldim.descRun 3 (h + 1)) [2, 1]
      (by rw [ground.length_replicate, weyldim.length_descRun]),
    weyldim.zipWith_descRun 2 3 (h + 1), Nat.add_comm 3 (h + 5),
    Nat.add_comm 3 (h + 4)]
  rfl

/-! The tie classification (`lem:channels`' proof): the fold's
contributions at `lem:adjchar`'s content read, one permutation
class per row.  The `θ` display carries the doubled gap at its
head, one value per key over the run and the unit at the last key;
the all-ones tie forces the identity permutation with the `θ`
row's display, a letter-pair move off the identity forces the
adjacent exchange at a unit gap of that display, and a letter-pair
move at the identity forces one of the five modifications. -/

/-- The θ display's entry reads: the head at the doubled gap. -/
private theorem yTheta_head (d : Nat) (hd : 2 ≤ d) :
    ground.getAt 0 (places.display (adjchar.theta d)) 0 = d + 2 := by
  obtain ⟨g, hg⟩ := Nat.le.dest hd
  have hd2 : d = g + 2 := by
    rw [← hg, Nat.add_comm 2 g]
  subst hd2
  have hlen : (adjchar.theta (g + 2)).length = g + 2 :=
    adjchar.length_theta (g + 2)
  rw [places.getAt_display (adjchar.theta (g + 2)) 0
      (by rw [hlen]; exact Nat.succ_pos (g + 1)),
    adjchar.rowList_theta g, hlen]
  show 2 + (g + 2) = g + 2 + 2
  exact Nat.add_comm 2 (g + 2)

/-- The θ display's run entries, one value per key. -/
private theorem yTheta_mid (d i : Nat) (h1 : 1 ≤ i)
    (h2 : i + 1 < d) :
    ground.getAt 0 (places.display (adjchar.theta d)) i + i = d + 1 := by
  obtain ⟨s, hs⟩ := Nat.le.dest h1
  have hi2 : i = s + 1 := by
    rw [← hs, Nat.add_comm 1 s]
  subst hi2
  obtain ⟨g, hg⟩ := Nat.le.dest (show 2 ≤ d from
    Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le s)))
      (Nat.le_of_lt h2))
  have hd2 : d = g + 2 := by
    rw [← hg, Nat.add_comm 2 g]
  subst hd2
  have hsg : s < g :=
    Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h2)
  have hlen : (adjchar.theta (g + 2)).length = g + 2 :=
    adjchar.length_theta (g + 2)
  have hidx : s + 1 < (adjchar.theta (g + 2)).length := by
    rw [hlen]
    exact Nat.lt_of_succ_lt h2
  rw [places.getAt_display (adjchar.theta (g + 2)) (s + 1) hidx,
    adjchar.rowList_theta g, hlen,
    show ground.getAt 0 (2 :: (List.replicate g 1 ++ [0])) (s + 1) = 1
      from by
        show ground.getAt 0 (List.replicate g 1 ++ [0]) s = 1
        rw [ground.getAt_append 0 (List.replicate g 1) [0] s,
          if_pos (show s < (List.replicate g 1).length from by
            rw [ground.length_replicate]
            exact hsg)]
        exact ground.getAt_replicate 0 1 g s hsg,
    Nat.add_assoc 1 (g + 2 - (s + 1)) (s + 1),
    Nat.add_comm (g + 2 - (s + 1)) (s + 1),
    ground.natAddSubCancel (Nat.le_of_lt (Nat.lt_of_succ_lt h2)),
    Nat.add_comm 1 (g + 2)]

/-- The θ display's last entry, the unit. -/
private theorem yTheta_last (d : Nat) (hd : 2 ≤ d) :
    ground.getAt 0 (places.display (adjchar.theta d)) (d - 1) = 1 := by
  obtain ⟨g, hg⟩ := Nat.le.dest hd
  have hd2 : d = g + 2 := by
    rw [← hg, Nat.add_comm 2 g]
  subst hd2
  have hlen : (adjchar.theta (g + 2)).length = g + 2 :=
    adjchar.length_theta (g + 2)
  show ground.getAt 0 (places.display (adjchar.theta (g + 2))) (g + 1) = 1
  rw [places.getAt_display (adjchar.theta (g + 2)) (g + 1)
      (by rw [hlen]; exact Nat.lt_succ_self (g + 1)),
    adjchar.rowList_theta g, hlen,
    show ground.getAt 0 (2 :: (List.replicate g 1 ++ [0])) (g + 1) = 0
      from by
        show ground.getAt 0 (List.replicate g 1 ++ [0]) g = 0
        have hx := ground.getAt_append_add 0 (List.replicate g 1) [0] 0
        rw [ground.length_replicate, Nat.add_zero] at hx
        exact hx,
    Nat.zero_add]
  exact ground.addSubSelfL (g + 1) 1

/-- The θ row's display is the θ display raised by the full
column. -/
private theorem dispY (d : Nat) :
    places.display (rowTheta d)
      = (places.display (adjchar.theta d)).map (fun x => x + 1) := by
  have h := places.display_full (adjchar.theta d)
  rw [adjchar.length_theta d] at h
  exact h

/-- A descending run's entry read over a joined tail: the key joins
the entry to the run's top. -/
private theorem runJoin (A K : Nat) (post : List Nat) (s : Nat)
    (hs : s < K) :
    s + ground.getAt 0 (weyldim.descRun A K ++ post) s + 1 = K + A := by
  rw [ground.getAt_append 0 (weyldim.descRun A K) post s,
    if_pos (show s < (weyldim.descRun A K).length from by
      rw [weyldim.length_descRun]
      exact hs)]
  exact weyldim.getAt_descRun A K s hs

/-- A descending run's joined tail reads its own entries. -/
private theorem runTail (A K : Nat) (post : List Nat) (r : Nat) :
    ground.getAt 0 (weyldim.descRun A K ++ post) (K + r)
      = ground.getAt 0 post r := by
  have hx := ground.getAt_append_add 0 (weyldim.descRun A K) post r
  rw [weyldim.length_descRun] at hx
  exact hx

/-- Two entries at one key and one joined value are one entry. -/
private theorem joinCancel (t A B V : Nat) (hA : t + A + 1 = V)
    (hB : t + B + 1 = V) : A = B :=
  ground.addCancelL t (ground.addCancelR 1 (hA.trans hB.symm))

/-- The tie's entry read at the identity permutation: the target's
entry is the move's own against the θ display. -/
private theorem rangeEntry (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (t : Nat) (ht : t < h + 5) :
    ground.getAt 0 (places.display c) t
      = ground.getAt 0 m t
        + ground.getAt 0 (places.display (adjchar.theta (h + 5))) t := by
  obtain ⟨_, hzl, hent⟩ := ground.tieGap_reads _ _ _ htie
  refine (hent t ?_).symm
  rw [← hzl, places.length_display, adjchar.length_theta]
  exact ht

/-- The target's head entry at the identity permutation. -/
private theorem rangeHead (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m) :
    ground.getAt 0 (places.display c) 0
      = ground.getAt 0 m 0 + (h + 7) := by
  rw [rangeEntry h c m htie 0 (Nat.succ_pos (h + 4)),
    yTheta_head (h + 5)
      (Nat.le_trans (by decide +kernel : (2 : Nat) ≤ 5) (Nat.le_add_left 5 h))]

/-- The target's run entries at the identity permutation, one join
per key. -/
private theorem rangeMid (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (t : Nat) (ha : 1 ≤ t) (hb : t + 1 < h + 5) :
    t + ground.getAt 0 (places.display c) t + 1
      = ground.getAt 0 m t + (h + 7) := by
  rw [rangeEntry h c m htie t (Nat.lt_of_succ_lt hb),
    Nat.add_comm t (ground.getAt 0 m t
      + ground.getAt 0 (places.display (adjchar.theta (h + 5))) t),
    Nat.add_assoc (ground.getAt 0 m t)
      (ground.getAt 0 (places.display (adjchar.theta (h + 5))) t) t,
    yTheta_mid (h + 5) t ha hb,
    Nat.add_assoc (ground.getAt 0 m t) (h + 5 + 1) 1]

/-- The target's last entry at the identity permutation. -/
private theorem rangeLast (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m) :
    ground.getAt 0 (places.display c) (h + 4)
      = ground.getAt 0 m (h + 4) + 1 := by
  rw [rangeEntry h c m htie (h + 4) (Nat.lt_succ_self (h + 4)),
    show ground.getAt 0 (places.display (adjchar.theta (h + 5))) (h + 4)
      = 1 from yTheta_last (h + 5)
        (Nat.le_trans (by decide +kernel : (2 : Nat) ≤ 5) (Nat.le_add_left 5 h))]

/-! The fold evaluation (`lem:channels`' general theorem): the tie
classification's contributions collected, one row at a time.  The
`θ` row's two graded sums are the residue's count against the run's
adjacent exchanges — the identity permutation reads the
unit-monomial content and each unit gap of the `θ` display reads a
letter-pair move at one — while the five modifications contribute
at the identity alone, and every shape off the table's rows reads
the fold's unit at both sums. -/

/-- The θ row's tie at the identity is the unit-monomial content. -/
private theorem tieTheta (d : Nat) :
    ground.tieGap (places.display (rowTheta d))
      (places.display (adjchar.theta d))
      = some (List.replicate d 1) := by
  have hyl : (places.display (adjchar.theta d)).length = d := by
    rw [places.length_display, adjchar.length_theta]
  have hYl : (places.display (rowTheta d)).length = d := by
    rw [dispY d, ground.length_map, hyl]
  refine ground.tieGap_make _ _ _ ?_ ?_ ?_
  · rw [ground.length_replicate, hYl]
  · rw [hyl, hYl]
  · intro i hi
    rw [hYl] at hi
    rw [ground.getAt_replicate 0 1 d i hi, dispY d,
      ground.getAt_map 0 0 (fun x => x + 1)
        (places.display (adjchar.theta d)) i (by rw [hyl]; exact hi)]
    exact Nat.add_comm 1 _

/-- The θ row's identity contribution, the residue's count. -/
private theorem rowTieTheta (h : Nat) :
    weylchar.multAtGap (adjchar.multRead (h + 5))
      (places.display (rowTheta (h + 5)))
      (places.display (adjchar.theta (h + 5))) = h + 4 := by
  show (match ground.tieGap (places.display (rowTheta (h + 5)))
      (places.display (adjchar.theta (h + 5))) with
    | some nu => adjchar.multRead (h + 5) nu
    | none => 0) = h + 4
  rw [tieTheta (h + 5)]
  show adjchar.multRead (h + 5) (List.replicate (h + 5) 1) = h + 4
  rw [adjchar.multRead_ones (h + 5)]
  rfl

/-- An adjacent exchange at a run key contributes one: the tie is
the letter-pair move at the exchanged places. -/
private theorem tieSwapMult (h k : Nat) (h1 : 1 ≤ k)
    (h2 : k ≤ h + 2) :
    weylchar.multAtGap (adjchar.multRead (h + 5))
      (places.display (rowTheta (h + 5)))
      (places.expo (places.display (adjchar.theta (h + 5)))
        (ground.adjSwap k (List.range (h + 5)))) = 1 := by
  obtain ⟨s, hs⟩ := Nat.le.dest h2
  have hks : k + (s + 3) = h + 5 := by
    rw [← Nat.add_assoc, hs]
  have hk1 : k + 1 < h + 5 :=
    Nat.lt_of_le_of_lt (Nat.succ_le_succ h2)
      (Nat.lt_succ_of_lt (Nat.lt_succ_self (h + 3)))
  have hk2 : k + 1 + 1 < h + 5 :=
    Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.succ_le_succ h2))
      (Nat.lt_succ_self (h + 4))
  have hyl : (places.display (adjchar.theta (h + 5))).length = h + 5 := by
    rw [places.length_display, adjchar.length_theta]
  have hYl : (places.display (rowTheta (h + 5))).length = h + 5 := by
    rw [dispY (h + 5), ground.length_map, hyl]
  have hrep : (List.replicate k (1 : Nat)).length = k :=
    ground.length_replicate 1 k
  have hMl : (List.replicate k 1 ++ 2 :: 0 :: List.replicate (s + 1) 1
      : List Nat).length = h + 5 := by
    rw [ground.length_append, hrep]
    show k + ((List.replicate (s + 1) (1 : Nat)).length + 1 + 1) = h + 5
    rw [ground.length_replicate]
    exact hks
  have hgap : ground.getAt 0 (places.display (adjchar.theta (h + 5))) k
      = ground.getAt 0 (places.display (adjchar.theta (h + 5))) (k + 1)
        + 1 := by
    have e1 := yTheta_mid (h + 5) k h1 hk1
    have e2 := yTheta_mid (h + 5) (k + 1) (Nat.le_succ_of_le h1) hk2
    refine ground.addCancelR k ?_
    rw [e1, ← e2,
      Nat.add_assoc
        (ground.getAt 0 (places.display (adjchar.theta (h + 5))) (k + 1))
        1 k,
      Nat.add_comm 1 k]
  have htie : ground.tieGap (places.display (rowTheta (h + 5)))
      (places.expo (places.display (adjchar.theta (h + 5)))
        (ground.adjSwap k (List.range (h + 5))))
      = some (List.replicate k 1 ++ 2 :: 0 :: List.replicate (s + 1) 1) := by
    refine ground.tieGap_make _ _ _ ?_ ?_ ?_
    · rw [hMl, hYl]
    · show (places.expo (places.display (adjchar.theta (h + 5)))
        (ground.adjSwap k (List.range (h + 5)))).length
        = (places.display (rowTheta (h + 5))).length
      show ((ground.adjSwap k (List.range (h + 5))).map
          (ground.getAt 0 (places.display (adjchar.theta (h + 5))))).length
        = (places.display (rowTheta (h + 5))).length
      rw [ground.length_map, ground.length_adjSwap, ground.length_range,
        hYl]
    · intro i hi
      rw [hYl] at hi
      rw [places.getAt_expo (places.display (adjchar.theta (h + 5)))
          (ground.adjSwap k (List.range (h + 5))) i
          (by rw [ground.length_adjSwap, ground.length_range]; exact hi),
        ground.getAt_adjSwap_range (h + 5) k i hk1 hi,
        ground.getAt_swapWit k (s + 1) i
          (by rw [show k + (s + 1 + 2) = h + 5 from hks]; exact hi),
        dispY (h + 5),
        ground.getAt_map 0 0 (fun x => x + 1)
          (places.display (adjchar.theta (h + 5))) i
          (by rw [hyl]; exact hi)]
      by_cases hik : i = k
      · rw [if_pos hik, if_pos hik, hik, hgap]
        exact Nat.add_comm 2 _
      · rw [if_neg hik, if_neg hik]
        by_cases hik2 : i = k + 1
        · rw [if_pos hik2, if_pos hik2, hik2, hgap, Nat.zero_add]
        · rw [if_neg hik2, if_neg hik2]
          exact Nat.add_comm 1 _
  have hc0 : ground.countOf 0
      (List.replicate k 1 ++ 2 :: 0 :: List.replicate (s + 1) 1) = 1 := by
    rw [ground.countOf_append, ground.countOf_replicate_ne 0 1 (by decide +kernel) k,
      ground.countOf_head_ne (show (0 : Nat) ≠ 2 by decide +kernel),
      ground.countOf_head, ground.countOf_replicate_ne 0 1 (by decide +kernel) (s + 1)]
  have hc2 : ground.countOf 2
      (List.replicate k 1 ++ 2 :: 0 :: List.replicate (s + 1) 1) = 1 := by
    rw [ground.countOf_append, ground.countOf_replicate_ne 2 1 (by decide +kernel) k,
      ground.countOf_head, ground.countOf_head_ne
        (show (2 : Nat) ≠ 0 by decide +kernel),
      ground.countOf_replicate_ne 2 1 (by decide +kernel) (s + 1)]
  have hc1 : ground.countOf 1
      (List.replicate k 1 ++ 2 :: 0 :: List.replicate (s + 1) 1) + 2
      = h + 5 := by
    rw [ground.countOf_append, ground.countOf_replicate 1 k,
      ground.countOf_head_ne (show (1 : Nat) ≠ 2 by decide +kernel),
      ground.countOf_head_ne (show (1 : Nat) ≠ 0 by decide +kernel),
      ground.countOf_replicate 1 (s + 1)]
    rw [← hks, Nat.add_assoc k (s + 1) 2]
  show (match ground.tieGap (places.display (rowTheta (h + 5)))
      (places.expo (places.display (adjchar.theta (h + 5)))
        (ground.adjSwap k (List.range (h + 5)))) with
    | some nu => adjchar.multRead (h + 5) nu
    | none => 0) = 1
  rw [htie]
  exact adjchar.multRead_move (h + 5) _ hMl hc0 hc2 hc1

/-- A descending run's entry at a stated value: the key's join
names it. -/
private theorem descAt (a k i : Nat) (hi : i < k) (v : Nat)
    (hv : i + v + 1 = k + a) :
    ground.getAt 0 (weyldim.descRun a k) i = v :=
  ground.addCancelL i (ground.addCancelR 1
    ((weyldim.getAt_descRun a k i hi).trans hv.symm))

/-- A joined run's entry at a stated value, the tail passive. -/
private theorem runAt (a k : Nat) (post : List Nat) (i : Nat)
    (hi : i < k) (v : Nat) (hv : i + v + 1 = k + a) :
    ground.getAt 0 (weyldim.descRun a k ++ post) i = v :=
  ground.addCancelL i (ground.addCancelR 1
    ((runJoin a k post i hi).trans hv.symm))

/-- The unit channel's head entry. -/
private theorem headUnit (h : Nat) :
    ground.getAt 0 (places.display (rowUnit (h + 5))) 0 = h + 7 := by
  rw [dispUnit h]
  exact descAt 3 (h + 5) 0 (Nat.succ_pos (h + 4)) (h + 7)
    (by rw [Nat.zero_add])

/-- The `θ` row's head entry. -/
private theorem headTheta (h : Nat) :
    ground.getAt 0 (places.display (rowTheta (h + 5))) 0 = h + 8 := by
  rw [dispTheta h]
  rfl

/-- The `2θ` row's head entry. -/
private theorem headTwoTheta (h : Nat) :
    ground.getAt 0 (places.display (rowTwoTheta (h + 5))) 0 = h + 9 := by
  rw [dispTwoTheta h]
  rfl

/-- The dual pair's first member: its head entry. -/
private theorem headDualA (h : Nat) :
    ground.getAt 0 (places.display (rowDualA (h + 5))) 0 = h + 9 := by
  rw [dispDualA h]
  rfl

/-- The dual pair's second member: its head entry. -/
private theorem headDualB (h : Nat) :
    ground.getAt 0 (places.display (rowDualB (h + 5))) 0 = h + 8 := by
  rw [dispDualB h]
  rfl

/-- The `ω₂ + ω₂*` row: its head entry. -/
private theorem headOmega (h : Nat) :
    ground.getAt 0 (places.display (rowOmega (h + 5))) 0 = h + 8 := by
  rw [dispOmega h]
  rfl

/-- The `θ` row's second entry, the run's top. -/
private theorem entTheta (h : Nat) :
    ground.getAt 0 (places.display (rowTheta (h + 5))) 1 = h + 6 := by
  rw [dispTheta h]
  show ground.getAt 0 (weyldim.descRun 4 (h + 3) ++ [2]) 0 = h + 6
  exact runAt 4 (h + 3) [2] 0 (Nat.succ_pos (h + 2)) (h + 6)
    (by rw [Nat.zero_add])

/-- The dual pair's second member: its second entry. -/
private theorem entDualB (h : Nat) :
    ground.getAt 0 (places.display (rowDualB (h + 5))) 1 = h + 7 := by
  rw [dispDualB h]
  rfl

/-- The `ω₂ + ω₂*` row: its second entry. -/
private theorem entOmega (h : Nat) :
    ground.getAt 0 (places.display (rowOmega (h + 5))) 1 = h + 7 := by
  rw [dispOmega h]
  rfl

/-- The `2θ` row's lowest entry. -/
private theorem lastTwoTheta (h : Nat) :
    ground.getAt 0 (places.display (rowTwoTheta (h + 5))) (h + 4) = 1 := by
  rw [dispTwoTheta h]
  show ground.getAt 0 (weyldim.descRun 4 (h + 3) ++ [1]) (h + 3) = 1
  exact runTail 4 (h + 3) [1] 0

/-- The dual pair's first member: its lowest entry. -/
private theorem lastDualA (h : Nat) :
    ground.getAt 0 (places.display (rowDualA (h + 5))) (h + 4) = 2 := by
  rw [dispDualA h]
  show ground.getAt 0 (weyldim.descRun 5 (h + 2) ++ [3, 2]) (h + 3) = 2
  exact runTail 5 (h + 2) [3, 2] 1

/-- The dual pair's second member: its lowest entry. -/
private theorem lastDualB (h : Nat) :
    ground.getAt 0 (places.display (rowDualB (h + 5))) (h + 4) = 1 := by
  rw [dispDualB h]
  show ground.getAt 0 (weyldim.descRun 4 (h + 2) ++ [1]) (h + 2) = 1
  exact runTail 4 (h + 2) [1] 0

/-- The `ω₂ + ω₂*` row: its lowest entry. -/
private theorem lastOmega (h : Nat) :
    ground.getAt 0 (places.display (rowOmega (h + 5))) (h + 4) = 2 := by
  rw [dispOmega h]
  show ground.getAt 0 (weyldim.descRun 5 (h + 1) ++ [3, 2]) (h + 2) = 2
  exact runTail 5 (h + 1) [3, 2] 1

/-- Two shapes parting at one display entry are distinct. -/
private theorem neOfDisp (x y : places.Shape) (k a b : Nat)
    (hx : ground.getAt 0 (places.display x) k = a)
    (hy : ground.getAt 0 (places.display y) k = b)
    (hab : ¬ a = b) : ¬ x = y := by
  intro he
  refine hab ?_
  rw [← hx, ← hy, he]

/-- A shared summand carries a refusal. -/
private theorem addNe (a b c : Nat) (hbc : ¬ b = c) : ¬ a + b = a + c :=
  fun he => hbc (ground.addCancelL a he)

/-! The table's rows are pairwise distinct: the head entry parts
the unit row from the rest and the two raised heads from the three
at the adjoint's, the second entry parts the `θ` row from the
lowered pair, and the lowest entry parts the last two pairs. -/

private theorem neUnitTheta (h : Nat) :
    ¬ rowUnit (h + 5) = rowTheta (h + 5) :=
  neOfDisp _ _ 0 (h + 7) (h + 8) (headUnit h) (headTheta h)
    (addNe h 7 8 (by decide +kernel))

private theorem neUnitTwoTheta (h : Nat) :
    ¬ rowUnit (h + 5) = rowTwoTheta (h + 5) :=
  neOfDisp _ _ 0 (h + 7) (h + 9) (headUnit h) (headTwoTheta h)
    (addNe h 7 9 (by decide +kernel))

private theorem neUnitDualA (h : Nat) :
    ¬ rowUnit (h + 5) = rowDualA (h + 5) :=
  neOfDisp _ _ 0 (h + 7) (h + 9) (headUnit h) (headDualA h)
    (addNe h 7 9 (by decide +kernel))

private theorem neUnitDualB (h : Nat) :
    ¬ rowUnit (h + 5) = rowDualB (h + 5) :=
  neOfDisp _ _ 0 (h + 7) (h + 8) (headUnit h) (headDualB h)
    (addNe h 7 8 (by decide +kernel))

private theorem neUnitOmega (h : Nat) :
    ¬ rowUnit (h + 5) = rowOmega (h + 5) :=
  neOfDisp _ _ 0 (h + 7) (h + 8) (headUnit h) (headOmega h)
    (addNe h 7 8 (by decide +kernel))

private theorem neThetaTwoTheta (h : Nat) :
    ¬ rowTheta (h + 5) = rowTwoTheta (h + 5) :=
  neOfDisp _ _ 0 (h + 8) (h + 9) (headTheta h) (headTwoTheta h)
    (addNe h 8 9 (by decide +kernel))

private theorem neThetaDualA (h : Nat) :
    ¬ rowTheta (h + 5) = rowDualA (h + 5) :=
  neOfDisp _ _ 0 (h + 8) (h + 9) (headTheta h) (headDualA h)
    (addNe h 8 9 (by decide +kernel))

private theorem neThetaDualB (h : Nat) :
    ¬ rowTheta (h + 5) = rowDualB (h + 5) :=
  neOfDisp _ _ 1 (h + 6) (h + 7) (entTheta h) (entDualB h)
    (addNe h 6 7 (by decide +kernel))

private theorem neThetaOmega (h : Nat) :
    ¬ rowTheta (h + 5) = rowOmega (h + 5) :=
  neOfDisp _ _ 1 (h + 6) (h + 7) (entTheta h) (entOmega h)
    (addNe h 6 7 (by decide +kernel))

private theorem neTwoThetaDualA (h : Nat) :
    ¬ rowTwoTheta (h + 5) = rowDualA (h + 5) :=
  neOfDisp _ _ (h + 4) 1 2 (lastTwoTheta h) (lastDualA h) (by decide +kernel)

private theorem neTwoThetaDualB (h : Nat) :
    ¬ rowTwoTheta (h + 5) = rowDualB (h + 5) :=
  neOfDisp _ _ 0 (h + 9) (h + 8) (headTwoTheta h) (headDualB h)
    (addNe h 9 8 (by decide +kernel))

private theorem neTwoThetaOmega (h : Nat) :
    ¬ rowTwoTheta (h + 5) = rowOmega (h + 5) :=
  neOfDisp _ _ 0 (h + 9) (h + 8) (headTwoTheta h) (headOmega h)
    (addNe h 9 8 (by decide +kernel))

private theorem neDualADualB (h : Nat) :
    ¬ rowDualA (h + 5) = rowDualB (h + 5) :=
  neOfDisp _ _ 0 (h + 9) (h + 8) (headDualA h) (headDualB h)
    (addNe h 9 8 (by decide +kernel))

private theorem neDualAOmega (h : Nat) :
    ¬ rowDualA (h + 5) = rowOmega (h + 5) :=
  neOfDisp _ _ 0 (h + 9) (h + 8) (headDualA h) (headOmega h)
    (addNe h 9 8 (by decide +kernel))

private theorem neDualBOmega (h : Nat) :
    ¬ rowDualB (h + 5) = rowOmega (h + 5) :=
  neOfDisp _ _ (h + 4) 1 2 (lastDualB h) (lastOmega h) (by decide +kernel)

/-- The row lengths at the matched degree. -/
private theorem lenRowUnit (h : Nat) : (rowUnit (h + 5)).length = h + 5 := by
  show (ground.bumpAt (h + 5 - 1) (ground.bumpAt (h + 5 - 1)
    (List.replicate (h + 5) 0))).length = h + 5
  rw [ground.length_bumpAt, ground.length_bumpAt, ground.length_replicate]

private theorem lenRowTheta (h : Nat) :
    (rowTheta (h + 5)).length = h + 5 := by
  show (ground.bumpAt (h + 5 - 1) (adjchar.theta (h + 5))).length = h + 5
  rw [ground.length_bumpAt, adjchar.length_theta]

private theorem lenRowTwoTheta (h : Nat) :
    (rowTwoTheta (h + 5)).length = h + 5 := by
  show (ground.bumpAt 0 (ground.bumpAt 0 (ground.bumpAt (h + 5 - 2)
    (ground.bumpAt (h + 5 - 2) (List.replicate (h + 5) 0))))).length
      = h + 5
  rw [ground.length_bumpAt, ground.length_bumpAt, ground.length_bumpAt,
    ground.length_bumpAt, ground.length_replicate]

private theorem lenRowDualA (h : Nat) :
    (rowDualA (h + 5)).length = h + 5 := by
  show (ground.bumpAt (h + 5 - 1) (ground.bumpAt 0 (ground.bumpAt 0
    (ground.bumpAt (h + 5 - 3) (List.replicate (h + 5) 0))))).length
      = h + 5
  rw [ground.length_bumpAt, ground.length_bumpAt, ground.length_bumpAt,
    ground.length_bumpAt, ground.length_replicate]

private theorem lenRowDualB (h : Nat) :
    (rowDualB (h + 5)).length = h + 5 := by
  show (ground.bumpAt 1 (ground.bumpAt (h + 5 - 2)
    (ground.bumpAt (h + 5 - 2) (List.replicate (h + 5) 0)))).length
      = h + 5
  rw [ground.length_bumpAt, ground.length_bumpAt, ground.length_bumpAt,
    ground.length_replicate]

private theorem lenRowOmega (h : Nat) :
    (rowOmega (h + 5)).length = h + 5 := by
  show (ground.bumpAt (h + 5 - 1) (ground.bumpAt 1
    (ground.bumpAt (h + 5 - 3) (List.replicate (h + 5) 0)))).length
      = h + 5
  rw [ground.length_bumpAt, ground.length_bumpAt, ground.length_bumpAt,
    ground.length_replicate]

/-- The matched degree carries the adjoint's own bound. -/
private theorem twoLe (h : Nat) : 2 ≤ h + 5 :=
  Nat.le_trans (by decide +kernel : (2 : Nat) ≤ 5) (Nat.le_add_left 5 h)

/-- The θ display's head at the matched degree. -/
private theorem yHead (h : Nat) :
    ground.getAt 0 (places.display (adjchar.theta (h + 5))) 0 = h + 7 :=
  yTheta_head (h + 5) (twoLe h)

/-- The θ display's lowest entry at the matched degree. -/
private theorem yLast (h : Nat) :
    ground.getAt 0 (places.display (adjchar.theta (h + 5))) (h + 4) = 1 :=
  yTheta_last (h + 5) (twoLe h)

/-- The θ display's second entry at the matched degree. -/
private theorem ySecond (h : Nat) :
    ground.getAt 0 (places.display (adjchar.theta (h + 5))) 1 = h + 5 :=
  ground.addCancelR 1 (yTheta_mid (h + 5) 1 (Nat.le_refl 1)
    (Nat.lt_of_lt_of_le (by decide +kernel : (2 : Nat) < 5) (Nat.le_add_left 5 h)))

/-- The θ display's entry one above the lowest. -/
private theorem yFourth (h : Nat) :
    ground.getAt 0 (places.display (adjchar.theta (h + 5))) (h + 3) = 3 :=
  ground.addCancelR (h + 3)
    ((yTheta_mid (h + 5) (h + 3)
        (Nat.succ_le_succ (Nat.zero_le (h + 2)))
        (Nat.lt_succ_self (h + 4))).trans
      (Nat.add_comm 3 (h + 3)).symm)

/-! The five modifications, factored: the move's indicator witness
with its counts, the tie against a display at the witness's case
read, the identity tie's target read entrywise, and one per-row
case read serving the identification and the contribution at
once. -/

/-- The move's indicator witness: the raised place at two, the
lowered at the fold's unit, every further place one. -/
private def moveWit (d i j : Nat) : List Nat :=
  (List.range d).map (fun t => if t = i then 2 else if t = j then 0 else 1)

/-- The witness's length is the width. -/
private theorem lenMoveWit (d i j : Nat) : (moveWit d i j).length = d :=
  ground.length_mapRange _ d

/-- The witness's entry reads. -/
private theorem getAt_moveWit (d i j t : Nat) (ht : t < d) :
    ground.getAt 0 (moveWit d i j) t
      = (if t = i then 2 else if t = j then 0 else 1) := by
  show ground.getAt 0 ((List.range d).map
    (fun t => if t = i then 2 else if t = j then 0 else 1)) t = _
  rw [ground.getAt_map 0 0 _ (List.range d) t
      (by rw [ground.length_range]; exact ht),
    ground.getAt_range d t ht]

/-- The witness's counts: the vacancy and the double once each with
the units at the remainder, the three guards partitioning the
width. -/
private theorem countMoveWit (d i j : Nat) (hi : i < d) (hj : j < d)
    (hij : ¬ i = j) :
    ground.countOf 0 (moveWit d i j) = 1
      ∧ ground.countOf 2 (moveWit d i j) = 1
      ∧ ground.countOf 1 (moveWit d i j) + 2 = d := by
  have h2 : ground.countOf 2 (moveWit d i j) = 1 := by
    have hcg : ∀ t : Nat,
        (if (2 : Nat) = (if t = i then 2 else if t = j then 0 else 1)
          then (1 : Nat) else 0)
        = (if i = t then (1 : Nat) else 0) := by
      intro t
      by_cases hti : t = i
      · rw [if_pos hti, if_pos (show (2 : Nat) = 2 from rfl),
          if_pos hti.symm]
      · rw [if_neg hti]
        by_cases htj : t = j
        · rw [if_pos htj,
            if_neg (show ¬ (2 : Nat) = 0 from fun he =>
              Nat.noConfusion he),
            if_neg (fun he => hti he.symm)]
        · rw [if_neg htj,
            if_neg (show ¬ (2 : Nat) = 1 from fun he =>
              Nat.noConfusion (Nat.succ.inj he)),
            if_neg (fun he => hti he.symm)]
    show ground.countOf 2 ((List.range d).map
      (fun t => if t = i then 2 else if t = j then 0 else 1)) = 1
    rw [ground.countOf_map_famFold 2 _ (List.range d),
      ground.famFold_congr_all Nat.add 0 _ _ hcg (List.range d),
      ← ground.countOf_fold i (List.range d),
      ground.countOf_range_one hi]
  have h0 : ground.countOf 0 (moveWit d i j) = 1 := by
    have hcg : ∀ t : Nat,
        (if (0 : Nat) = (if t = i then 2 else if t = j then 0 else 1)
          then (1 : Nat) else 0)
        = (if j = t then (1 : Nat) else 0) := by
      intro t
      by_cases hti : t = i
      · rw [if_pos hti,
          if_neg (show ¬ (0 : Nat) = 2 from fun he =>
            Nat.noConfusion he),
          if_neg (fun he => hij (he.trans hti).symm)]
      · rw [if_neg hti]
        by_cases htj : t = j
        · rw [if_pos htj, if_pos (show (0 : Nat) = 0 from rfl),
            if_pos htj.symm]
        · rw [if_neg htj,
            if_neg (show ¬ (0 : Nat) = 1 from fun he =>
              Nat.noConfusion he),
            if_neg (fun he => htj he.symm)]
    show ground.countOf 0 ((List.range d).map
      (fun t => if t = i then 2 else if t = j then 0 else 1)) = 1
    rw [ground.countOf_map_famFold 0 _ (List.range d),
      ground.famFold_congr_all Nat.add 0 _ _ hcg (List.range d),
      ← ground.countOf_fold j (List.range d),
      ground.countOf_range_one hj]
  refine ⟨h0, h2, ?_⟩
  have hsum : ∀ t : Nat,
      ((if (1 : Nat) = (if t = i then 2 else if t = j then 0 else 1)
          then (1 : Nat) else 0)
        + ((if (2 : Nat) = (if t = i then 2 else if t = j then 0 else 1)
            then (1 : Nat) else 0)
          + (if (0 : Nat) = (if t = i then 2 else if t = j then 0 else 1)
              then (1 : Nat) else 0))) = 1 := by
    intro t
    by_cases hti : t = i
    · rw [if_pos hti]
      rfl
    · rw [if_neg hti]
      by_cases htj : t = j
      · rw [if_pos htj]
        rfl
      · rw [if_neg htj]
        rfl
  have hone : ground.famFold Nat.add 0
      (fun t =>
        (if (1 : Nat) = (if t = i then 2 else if t = j then 0 else 1)
          then (1 : Nat) else 0)
        + ((if (2 : Nat) = (if t = i then 2 else if t = j then 0 else 1)
            then (1 : Nat) else 0)
          + (if (0 : Nat) = (if t = i then 2 else if t = j then 0 else 1)
              then (1 : Nat) else 0)))
      (List.range d) = d := by
    rw [ground.famFold_congr_all Nat.add 0 _ (fun _ => (1 : Nat))
        hsum (List.range d),
      ground.famFold_length (List.range d), ground.length_range]
  rw [ground.famFold_add_split, ground.famFold_add_split] at hone
  rw [← ground.countOf_map_famFold 1 _ (List.range d),
    ← ground.countOf_map_famFold 2 _ (List.range d),
    ← ground.countOf_map_famFold 0 _ (List.range d)] at hone
  have h2' : ground.countOf 2 ((List.range d).map
      (fun t => if t = i then 2 else if t = j then 0 else 1)) = 1 := h2
  have h0' : ground.countOf 0 ((List.range d).map
      (fun t => if t = i then 2 else if t = j then 0 else 1)) = 1 := h0
  rw [h2', h0'] at hone
  exact hone

/-- The tie at the identity against a display at the witness's case
read: the entries close the move witness. -/
private theorem tieOfCase (h i j : Nat) (X : places.Shape)
    (hXl : X.length = h + 5)
    (hXd : ∀ t, t < h + 5 → ground.getAt 0 (places.display X) t
      = (if t = i then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t + 2
        else if t = j then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        else ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
          + 1)) :
    ground.tieGap (places.display X)
        (places.display (adjchar.theta (h + 5)))
      = some (moveWit (h + 5) i j) := by
  refine ground.tieGap_make _ _ _ ?_ ?_ ?_
  · rw [lenMoveWit, places.length_display, hXl]
  · rw [places.length_display, adjchar.length_theta,
      places.length_display, hXl]
  · intro t ht
    rw [places.length_display, hXl] at ht
    rw [getAt_moveWit (h + 5) i j t ht, hXd t ht]
    by_cases hti : t = i
    · rw [if_pos hti, if_pos hti]
      exact Nat.add_comm 2 _
    · rw [if_neg hti, if_neg hti]
      by_cases htj : t = j
      · rw [if_pos htj, if_pos htj, Nat.zero_add]
      · rw [if_neg htj, if_neg htj]
        exact Nat.add_comm 1 _

/-- A row's identity contribution at its case read: one, the move
witness's own multiplicity. -/
private theorem rowTieOf (h i j : Nat) (hi : i < h + 5)
    (hj : j < h + 5) (hij : ¬ i = j) (X : places.Shape)
    (hXl : X.length = h + 5)
    (hXd : ∀ t, t < h + 5 → ground.getAt 0 (places.display X) t
      = (if t = i then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t + 2
        else if t = j then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        else ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
          + 1)) :
    weylchar.multAtGap (adjchar.multRead (h + 5)) (places.display X)
      (places.display (adjchar.theta (h + 5))) = 1 := by
  obtain ⟨hc0, hc2, hc1⟩ := countMoveWit (h + 5) i j hi hj hij
  show (match ground.tieGap (places.display X)
      (places.display (adjchar.theta (h + 5))) with
    | some nu => adjchar.multRead (h + 5) nu
    | none => 0) = 1
  rw [tieOfCase h i j X hXl hXd]
  exact adjchar.multRead_move (h + 5) _ (lenMoveWit (h + 5) i j) hc0 hc2 hc1

/-- The identity tie with the move data reads the target's display
entrywise: the raised place two above the θ display, the lowered at
it, every further place its successor. -/
private theorem modOf (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (i j : Nat) (h2 : ground.getAt 0 m i = 2)
    (h0 : ground.getAt 0 m j = 0)
    (h1 : ∀ k, k < h + 5 → ¬ k = i → ¬ k = j
      → ground.getAt 0 m k = 1)
    (t : Nat) (ht : t < h + 5) :
    ground.getAt 0 (places.display c) t
      = (if t = i then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t + 2
        else if t = j then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        else ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
          + 1) := by
  obtain ⟨_, hzl, hent⟩ := ground.tieGap_reads _ _ _ htie
  have hcd : (places.display c).length = h + 5 := by
    rw [← hzl, places.length_display, adjchar.length_theta]
  have he := (hent t (by rw [hcd]; exact ht)).symm
  by_cases hti : t = i
  · rw [if_pos hti, he, hti, h2]
    exact Nat.add_comm 2 _
  · rw [if_neg hti]
    by_cases htj : t = j
    · rw [if_pos htj, he, htj, h0, Nat.zero_add]
    · rw [if_neg htj, he, h1 t ht hti htj]
      exact Nat.add_comm 1 _

/-- The identification at a case read: the target is the row whose
display carries the modification. -/
private theorem idOf (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (i j : Nat) (h2 : ground.getAt 0 m i = 2)
    (h0 : ground.getAt 0 m j = 0)
    (h1 : ∀ k, k < h + 5 → ¬ k = i → ¬ k = j
      → ground.getAt 0 m k = 1)
    (X : places.Shape) (hXl : X.length = h + 5)
    (hXd : ∀ t, t < h + 5 → ground.getAt 0 (places.display X) t
      = (if t = i then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t + 2
        else if t = j then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        else ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
          + 1)) :
    c = X := by
  obtain ⟨_, hzl, _⟩ := ground.tieGap_reads _ _ _ htie
  have hcd : (places.display c).length = h + 5 := by
    rw [← hzl, places.length_display, adjchar.length_theta]
  refine places.display_inj c X (ground.getAt_ext 0 _ _ ?_ ?_)
  · rw [hcd, places.length_display, hXl]
  · intro t ht
    rw [hcd] at ht
    rw [modOf h c m htie i j h2 h0 h1 t ht, hXd t ht]

/-- The unit channel's case read: the head lowered, the last key
raised, the run at the successors. -/
private theorem caseUnit (h : Nat) : ∀ t, t < h + 5 →
    ground.getAt 0 (places.display (rowUnit (h + 5))) t
      = (if t = h + 4 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t + 2
        else if t = 0 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        else ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
          + 1) := by
  intro t ht
  rw [dispUnit h]
  by_cases h4 : t = h + 4
  · rw [if_pos h4, h4, yLast h]
    exact descAt 3 (h + 5) (h + 4) (Nat.lt_succ_self (h + 4)) 3 rfl
  · rw [if_neg h4]
    cases t with
    | zero =>
      rw [if_pos rfl, yHead h]
      exact descAt 3 (h + 5) 0 (Nat.succ_pos (h + 4)) (h + 7)
        (by rw [Nat.zero_add])
    | succ s =>
      rw [if_neg (fun he => Nat.noConfusion he)]
      have hlt : s + 1 < h + 4 :=
        match Nat.lt_or_ge (s + 1) (h + 4) with
        | .inl hx => hx
        | .inr hx => absurd (Nat.le_antisymm (Nat.le_of_lt_succ ht) hx) h4
      have hm := yTheta_mid (h + 5) (s + 1)
        (Nat.succ_le_succ (Nat.zero_le s)) (Nat.succ_lt_succ hlt)
      refine joinCancel (s + 1) _ _ (h + 5 + 3)
        (weyldim.getAt_descRun 3 (h + 5) (s + 1) ht) ?_
      rw [← Nat.add_assoc (s + 1)
          (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
            (s + 1)) 1,
        Nat.add_comm (s + 1)
          (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
            (s + 1))]
      exact congrArg (fun x => x + 1 + 1) hm

/-- The `2θ` row's case read: the head raised, the last key
lowered, the run at the successors. -/
private theorem caseTwoTheta (h : Nat) : ∀ t, t < h + 5 →
    ground.getAt 0 (places.display (rowTwoTheta (h + 5))) t
      = (if t = 0 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t + 2
        else if t = h + 4 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        else ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
          + 1) := by
  intro t ht
  rw [dispTwoTheta h]
  cases t with
  | zero =>
    rw [if_pos rfl, yHead h]
    rfl
  | succ s =>
    rw [if_neg (fun he => Nat.noConfusion he)]
    by_cases h4 : s + 1 = h + 4
    · rw [if_pos h4, h4, yLast h]
      show ground.getAt 0 (weyldim.descRun 4 (h + 3) ++ [1]) (h + 3) = 1
      exact runTail 4 (h + 3) [1] 0
    · rw [if_neg h4]
      have hlt : s + 1 < h + 4 :=
        match Nat.lt_or_ge (s + 1) (h + 4) with
        | .inl hx => hx
        | .inr hx => absurd (Nat.le_antisymm (Nat.le_of_lt_succ ht) hx) h4
      have hm := yTheta_mid (h + 5) (s + 1)
        (Nat.succ_le_succ (Nat.zero_le s)) (Nat.succ_lt_succ hlt)
      show ground.getAt 0 (weyldim.descRun 4 (h + 3) ++ [1]) s
        = ground.getAt 0 (places.display (adjchar.theta (h + 5))) (s + 1)
          + 1
      refine joinCancel s _ _ (h + 3 + 4)
        (runJoin 4 (h + 3) [1] s (Nat.lt_of_succ_lt_succ hlt)) ?_
      rw [← Nat.add_assoc s
          (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
            (s + 1)) 1,
        Nat.add_comm s
          (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
            (s + 1)),
        Nat.add_assoc
          (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
            (s + 1)) s 1]
      exact congrArg (fun x => x + 1) hm

/-- The dual pair's first member: the head raised, the fourth
value's key lowered, the run and the lowest key at the
successors. -/
private theorem caseDualA (h : Nat) : ∀ t, t < h + 5 →
    ground.getAt 0 (places.display (rowDualA (h + 5))) t
      = (if t = 0 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t + 2
        else if t = h + 3 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        else ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
          + 1) := by
  intro t ht
  rw [dispDualA h]
  cases t with
  | zero =>
    rw [if_pos rfl, yHead h]
    rfl
  | succ s =>
    rw [if_neg (fun he => Nat.noConfusion he)]
    by_cases h3 : s + 1 = h + 3
    · rw [if_pos h3, h3]
      have hm := yTheta_mid (h + 5) (h + 3)
        (Nat.le_add_left 1 (h + 2))
        (Nat.lt_succ_self (h + 4))
      have hy3 : ground.getAt 0
          (places.display (adjchar.theta (h + 5))) (h + 3) = 3 := by
        refine ground.addCancelR (h + 3) ?_
        rw [hm, Nat.add_comm 3 (h + 3)]
      rw [hy3]
      show ground.getAt 0 (weyldim.descRun 5 (h + 2) ++ [3, 2]) (h + 2) = 3
      exact runTail 5 (h + 2) [3, 2] 0
    · rw [if_neg h3]
      by_cases h4 : s + 1 = h + 4
      · rw [h4, yLast h]
        show ground.getAt 0 (weyldim.descRun 5 (h + 2) ++ [3, 2]) (h + 3)
          = 1 + 1
        exact runTail 5 (h + 2) [3, 2] 1
      · have hlt4 : s + 1 < h + 4 :=
          match Nat.lt_or_ge (s + 1) (h + 4) with
          | .inl hx => hx
          | .inr hx =>
            absurd (Nat.le_antisymm (Nat.le_of_lt_succ ht) hx) h4
        have hlt : s + 1 < h + 3 :=
          match Nat.lt_or_ge (s + 1) (h + 3) with
          | .inl hx => hx
          | .inr hx =>
            absurd (Nat.le_antisymm (Nat.le_of_lt_succ hlt4) hx) h3
        have hm := yTheta_mid (h + 5) (s + 1)
          (Nat.succ_le_succ (Nat.zero_le s)) (Nat.succ_lt_succ hlt4)
        show ground.getAt 0 (weyldim.descRun 5 (h + 2) ++ [3, 2]) s
          = ground.getAt 0 (places.display (adjchar.theta (h + 5)))
              (s + 1) + 1
        refine joinCancel s _ _ (h + 2 + 5)
          (runJoin 5 (h + 2) [3, 2] s (Nat.lt_of_succ_lt_succ hlt)) ?_
        rw [← Nat.add_assoc s
            (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
              (s + 1)) 1,
          Nat.add_comm s
            (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
              (s + 1)),
          Nat.add_assoc
            (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
              (s + 1)) s 1]
        exact congrArg (fun x => x + 1) hm

/-- The dual pair's second member: the second key raised, the last
lowered, the head and the run at the successors. -/
private theorem caseDualB (h : Nat) : ∀ t, t < h + 5 →
    ground.getAt 0 (places.display (rowDualB (h + 5))) t
      = (if t = 1 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t + 2
        else if t = h + 4 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        else ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
          + 1) := by
  intro t ht
  rw [dispDualB h]
  cases t with
  | zero =>
    rw [if_neg (fun he => Nat.noConfusion he),
      if_neg (fun he => Nat.noConfusion he), yHead h]
    rfl
  | succ s =>
    cases s with
    | zero =>
      rw [if_pos rfl, ySecond h]
      rfl
    | succ s2 =>
      rw [if_neg (fun he => Nat.noConfusion (Nat.succ.inj he))]
      by_cases h4 : s2 + 2 = h + 4
      · rw [if_pos h4, h4, yLast h]
        show ground.getAt 0 (weyldim.descRun 4 (h + 2) ++ [1]) (h + 2) = 1
        exact runTail 4 (h + 2) [1] 0
      · rw [if_neg h4]
        have hlt : s2 + 2 < h + 4 :=
          match Nat.lt_or_ge (s2 + 2) (h + 4) with
          | .inl hx => hx
          | .inr hx =>
            absurd (Nat.le_antisymm (Nat.le_of_lt_succ ht) hx) h4
        have hm := yTheta_mid (h + 5) (s2 + 2)
          (Nat.le_add_left 1 (s2 + 1)) (Nat.succ_lt_succ hlt)
        show ground.getAt 0 (weyldim.descRun 4 (h + 2) ++ [1]) s2
          = ground.getAt 0 (places.display (adjchar.theta (h + 5)))
              (s2 + 2) + 1
        refine joinCancel s2 _ _ (h + 2 + 4)
          (runJoin 4 (h + 2) [1] s2
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt))) ?_
        rw [← Nat.add_assoc s2
            (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
              (s2 + 2)) 1,
          Nat.add_comm s2
            (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
              (s2 + 2)),
          Nat.add_assoc
            (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
              (s2 + 2)) s2 1]
        exact hm

/-- The `ω₂ + ω₂*` row: the second key raised, the fourth value's
key lowered, the head, the run and the lowest key at the
successors. -/
private theorem caseOmega (h : Nat) : ∀ t, t < h + 5 →
    ground.getAt 0 (places.display (rowOmega (h + 5))) t
      = (if t = 1 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t + 2
        else if t = h + 3 then
          ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        else ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
          + 1) := by
  intro t ht
  rw [dispOmega h]
  cases t with
  | zero =>
    rw [if_neg (fun he => Nat.noConfusion he),
      if_neg (fun he => Nat.noConfusion he), yHead h]
    rfl
  | succ s =>
    cases s with
    | zero =>
      rw [if_pos rfl, ySecond h]
      rfl
    | succ s2 =>
      rw [if_neg (fun he => Nat.noConfusion (Nat.succ.inj he))]
      by_cases h3 : s2 + 2 = h + 3
      · rw [if_pos h3, h3]
        have hm := yTheta_mid (h + 5) (h + 3)
          (Nat.le_add_left 1 (h + 2))
          (Nat.lt_succ_self (h + 4))
        have hy3 : ground.getAt 0
            (places.display (adjchar.theta (h + 5))) (h + 3) = 3 := by
          refine ground.addCancelR (h + 3) ?_
          rw [hm, Nat.add_comm 3 (h + 3)]
        rw [hy3]
        show ground.getAt 0 (weyldim.descRun 5 (h + 1) ++ [3, 2]) (h + 1)
          = 3
        exact runTail 5 (h + 1) [3, 2] 0
      · rw [if_neg h3]
        by_cases h4 : s2 + 2 = h + 4
        · rw [h4, yLast h]
          show ground.getAt 0 (weyldim.descRun 5 (h + 1) ++ [3, 2]) (h + 2)
            = 1 + 1
          exact runTail 5 (h + 1) [3, 2] 1
        · have hlt4 : s2 + 2 < h + 4 :=
            match Nat.lt_or_ge (s2 + 2) (h + 4) with
            | .inl hx => hx
            | .inr hx =>
              absurd (Nat.le_antisymm (Nat.le_of_lt_succ ht) hx) h4
          have hlt : s2 + 2 < h + 3 :=
            match Nat.lt_or_ge (s2 + 2) (h + 3) with
            | .inl hx => hx
            | .inr hx =>
              absurd (Nat.le_antisymm (Nat.le_of_lt_succ hlt4) hx) h3
          have hm := yTheta_mid (h + 5) (s2 + 2)
            (Nat.le_add_left 1 (s2 + 1)) (Nat.succ_lt_succ hlt4)
          show ground.getAt 0 (weyldim.descRun 5 (h + 1) ++ [3, 2]) s2
            = ground.getAt 0 (places.display (adjchar.theta (h + 5)))
                (s2 + 2) + 1
          refine joinCancel s2 _ _ (h + 1 + 5)
            (runJoin 5 (h + 1) [3, 2] s2
              (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt))) ?_
          rw [← Nat.add_assoc s2
              (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
                (s2 + 2)) 1,
            Nat.add_comm s2
              (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
                (s2 + 2)),
            Nat.add_assoc
              (ground.getAt 0 (places.display (adjchar.theta (h + 5)))
                (s2 + 2)) s2 1]
          exact hm

/-- The unit channel's row at its move: the vacant head, the run's
own entries and the doubled last key. -/
private theorem idUnit (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (h2 : ground.getAt 0 m (h + 4) = 2)
    (h0 : ground.getAt 0 m 0 = 0)
    (h1 : ∀ k, k < h + 5 → ¬ k = h + 4 → ¬ k = 0
      → ground.getAt 0 m k = 1) :
    c = rowUnit (h + 5) :=
  idOf h c m htie (h + 4) 0 h2 h0 h1 (rowUnit (h + 5)) (lenRowUnit h)
    (caseUnit h)

/-- The `2θ` row at its move: the doubled head, the run's own
entries and the vacant last key. -/
private theorem idTwoTheta (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (h2 : ground.getAt 0 m 0 = 2)
    (h0 : ground.getAt 0 m (h + 4) = 0)
    (h1 : ∀ k, k < h + 5 → ¬ k = 0 → ¬ k = h + 4
      → ground.getAt 0 m k = 1) :
    c = rowTwoTheta (h + 5) :=
  idOf h c m htie 0 (h + 4) h2 h0 h1 (rowTwoTheta (h + 5))
    (lenRowTwoTheta h) (caseTwoTheta h)

/-- The dual pair's first member at its move: the doubled head with
the fourth value's key vacant. -/
private theorem idDualA (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (h2 : ground.getAt 0 m 0 = 2)
    (h0 : ground.getAt 0 m (h + 3) = 0)
    (h1 : ∀ k, k < h + 5 → ¬ k = 0 → ¬ k = h + 3
      → ground.getAt 0 m k = 1) :
    c = rowDualA (h + 5) :=
  idOf h c m htie 0 (h + 3) h2 h0 h1 (rowDualA (h + 5))
    (lenRowDualA h) (caseDualA h)

/-- The dual pair's second member at its move: the doubled second
key with the last vacant. -/
private theorem idDualB (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (h2 : ground.getAt 0 m 1 = 2)
    (h0 : ground.getAt 0 m (h + 4) = 0)
    (h1 : ∀ k, k < h + 5 → ¬ k = 1 → ¬ k = h + 4
      → ground.getAt 0 m k = 1) :
    c = rowDualB (h + 5) :=
  idOf h c m htie 1 (h + 4) h2 h0 h1 (rowDualB (h + 5))
    (lenRowDualB h) (caseDualB h)

/-- The `ω₂ + ω₂*` row at its move: the doubled second key with the
fourth value's key vacant. -/
private theorem idOmega (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (h2 : ground.getAt 0 m 1 = 2)
    (h0 : ground.getAt 0 m (h + 3) = 0)
    (h1 : ∀ k, k < h + 5 → ¬ k = 1 → ¬ k = h + 3
      → ground.getAt 0 m k = 1) :
    c = rowOmega (h + 5) :=
  idOf h c m htie 1 (h + 3) h2 h0 h1 (rowOmega (h + 5))
    (lenRowOmega h) (caseOmega h)

/-- A letter-pair-move tie at the identity forces one of the five
modifications: the raised place at the head, the second key or the
last, the lowered at the head, the fourth value's key or the last,
every further pair breaking the target's descent at the run. -/
private theorem tieMoveRange (h : Nat) (c : places.Shape) (m : List Nat)
    (htie : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) = some m)
    (i : Nat) (hi : i < h + 5) (j : Nat)
    (hj : j < h + 5) (hij : ¬ i = j)
    (h2 : ground.getAt 0 m i = 2) (h0 : ground.getAt 0 m j = 0)
    (h1 : ∀ k, k < h + 5 → ¬ k = i → ¬ k = j
      → ground.getAt 0 m k = 1) :
    c = rowUnit (h + 5) ∨ c = rowTwoTheta (h + 5)
      ∨ c = rowDualA (h + 5) ∨ c = rowDualB (h + 5)
      ∨ c = rowOmega (h + 5) := by
  obtain ⟨_, hzl0, _⟩ := ground.tieGap_reads _ _ _ htie
  have hcl : c.length = h + 5 := by
    rw [← places.length_display c, ← hzl0, places.length_display,
      adjchar.length_theta]
  have hstep : ∀ t, 1 ≤ t → t + 1 < h + 4 →
      ground.getAt 0 m (t + 1) ≤ ground.getAt 0 m t := by
    intro t ha hb
    have hb5 : t + 1 < h + 5 := Nat.lt_succ_of_lt hb
    have hb5' : t + 1 + 1 < h + 5 := Nat.succ_lt_succ hb
    have hy1 : ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        + t = h + 5 + 1 := yTheta_mid (h + 5) t ha hb5
    have hy2 : ground.getAt 0
          (places.display (adjchar.theta (h + 5))) (t + 1) + (t + 1)
        = h + 5 + 1 :=
      yTheta_mid (h + 5) (t + 1) (Nat.le_succ_of_le ha) hb5'
    have hYY : ground.getAt 0 (places.display (adjchar.theta (h + 5))) t
        = ground.getAt 0
            (places.display (adjchar.theta (h + 5))) (t + 1) + 1 := by
      refine ground.addCancelR t ?_
      rw [hy1, ← hy2, Nat.add_assoc (ground.getAt 0
          (places.display (adjchar.theta (h + 5))) (t + 1)) 1 t,
        Nat.add_comm 1 t]
    have hdc := places.display_desc c t (by rw [hcl]; exact hb5)
    rw [rangeEntry h c m htie (t + 1) hb5,
      rangeEntry h c m htie t (Nat.lt_of_succ_lt hb5), hYY,
      Nat.add_comm (ground.getAt 0
        (places.display (adjchar.theta (h + 5))) (t + 1)) 1,
      ← Nat.add_assoc (ground.getAt 0 m t) 1 (ground.getAt 0
        (places.display (adjchar.theta (h + 5))) (t + 1))] at hdc
    exact Nat.le_of_lt_succ (Nat.lt_of_add_lt_add_right hdc)
  have hicl : i = 0 ∨ i = 1 ∨ i = h + 4 := by
    cases i with
    | zero => exact Or.inl rfl
    | succ s0 =>
      cases s0 with
      | zero => exact Or.inr (Or.inl rfl)
      | succ s =>
        cases Nat.lt_or_ge (s + 1 + 1) (h + 4) with
        | inl hlt =>
          have hb : s + 1 < h + 5 :=
            Nat.lt_trans (Nat.lt_succ_self (s + 1)) (Nat.lt_succ_of_lt hlt)
          have hle := hstep (s + 1) (Nat.succ_le_succ (Nat.zero_le s)) hlt
          rw [h2] at hle
          have heq : ground.getAt 0 m (s + 1) = 2 :=
            Nat.le_antisymm
              (places.moveCap (h + 5) m (s + 1 + 1) j h2 h0 h1 (s + 1) hb) hle
          exact absurd
            (places.movePlaceTwo (h + 5) m (s + 1 + 1) j h0 h1 (s + 1) hb heq).symm
            (Nat.succ_ne_self (s + 1))
        | inr hge =>
          exact Or.inr (Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hi) hge))
  have hjcl : j = 0 ∨ j = h + 3 ∨ j = h + 4 := by
    cases j with
    | zero => exact Or.inl rfl
    | succ s =>
      cases Nat.lt_or_ge (s + 1) (h + 3) with
      | inl hlt =>
        have hle := hstep (s + 1) (Nat.succ_le_succ (Nat.zero_le s))
          (Nat.succ_lt_succ hlt)
        rw [h0] at hle
        have hz : ground.getAt 0 m (s + 1 + 1) = 0 :=
          Nat.eq_zero_of_le_zero hle
        have hb : s + 1 + 1 < h + 5 :=
          Nat.lt_succ_of_lt (Nat.succ_lt_succ hlt)
        exact absurd
          (places.movePlaceZero (h + 5) m i (s + 1) h2 h1 (s + 1 + 1) hb hz)
          (Nat.succ_ne_self (s + 1))
      | inr hge =>
        cases Nat.eq_or_lt_of_le hge with
        | inl he => exact Or.inr (Or.inl he.symm)
        | inr hlt =>
          exact Or.inr (Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hj) hlt))
  cases hicl with
  | inl hI =>
    subst hI
    cases hjcl with
    | inl hJ => exact absurd hJ.symm hij
    | inr hJ2 =>
      cases hJ2 with
      | inl hJ =>
        subst hJ
        exact Or.inr (Or.inr (Or.inl (idDualA h c m htie h2 h0 h1)))
      | inr hJ =>
        subst hJ
        exact Or.inr (Or.inl (idTwoTheta h c m htie h2 h0 h1))
  | inr hI2 =>
    cases hI2 with
    | inl hI =>
      subst hI
      cases hjcl with
      | inl hJ =>
        subst hJ
        have e0 : ground.getAt 0 (places.display c) 0 = h + 7 := by
          rw [rangeHead h c m htie, h0, Nat.zero_add]
        have e1 : ground.getAt 0 (places.display c) 1 = h + 7 := by
          refine joinCancel 1 _ _ (h + 9) ?_ ?_
          · rw [rangeMid h c m htie 1 (Nat.le_refl 1)
                (Nat.lt_of_lt_of_le (by decide +kernel : (2 : Nat) < 5)
                  (Nat.le_add_left 5 h)),
              h2, Nat.add_comm 2 (h + 7)]
          · rw [Nat.add_comm 1 (h + 7)]
        have hdc := places.display_desc c 0 (by
          rw [hcl]
          exact Nat.lt_of_lt_of_le (by decide +kernel : (1 : Nat) < 5)
            (Nat.le_add_left 5 h))
        rw [e1, e0] at hdc
        exact absurd hdc (Nat.lt_irrefl (h + 7))
      | inr hJ2 =>
        cases hJ2 with
        | inl hJ =>
          subst hJ
          exact Or.inr (Or.inr (Or.inr (Or.inr
            (idOmega h c m htie h2 h0 h1))))
        | inr hJ =>
          subst hJ
          exact Or.inr (Or.inr (Or.inr (Or.inl
            (idDualB h c m htie h2 h0 h1))))
    | inr hI =>
      subst hI
      cases hjcl with
      | inl hJ =>
        subst hJ
        exact Or.inl (idUnit h c m htie h2 h0 h1)
      | inr hJ2 =>
        cases hJ2 with
        | inl hJ =>
          subst hJ
          have e3 : ground.getAt 0 (places.display c) (h + 3) = 3 := by
            refine joinCancel (h + 3) _ _ (h + 7) ?_ ?_
            · rw [rangeMid h c m htie (h + 3)
                  (Nat.succ_le_succ (Nat.zero_le (h + 2)))
                  (Nat.lt_succ_self (h + 4)),
                h0, Nat.zero_add]
            · rfl
          have e4 : ground.getAt 0 (places.display c) (h + 4) = 3 := by
            rw [rangeLast h c m htie, h2]
          have hdc := places.display_desc c (h + 3) (by
            rw [hcl]
            exact Nat.lt_succ_self (h + 4))
          rw [e4, e3] at hdc
          exact absurd hdc (Nat.lt_irrefl 3)
        | inr hJ => exact absurd hJ.symm hij

/-- The unit channel's identity contribution, one: the tie is the
letter-pair move at the head and the lowest key. -/
private theorem rowTieUnit (h : Nat) :
    weylchar.multAtGap (adjchar.multRead (h + 5))
      (places.display (rowUnit (h + 5)))
      (places.display (adjchar.theta (h + 5))) = 1 :=
  rowTieOf h (h + 4) 0 (Nat.lt_succ_self (h + 4))
    (Nat.succ_pos (h + 4)) (fun he => Nat.noConfusion he)
    (rowUnit (h + 5)) (lenRowUnit h) (caseUnit h)

/-- The `2θ` row's identity contribution, one. -/
private theorem rowTieTwoTheta (h : Nat) :
    weylchar.multAtGap (adjchar.multRead (h + 5))
      (places.display (rowTwoTheta (h + 5)))
      (places.display (adjchar.theta (h + 5))) = 1 :=
  rowTieOf h 0 (h + 4) (Nat.succ_pos (h + 4))
    (Nat.lt_succ_self (h + 4)) (fun he => Nat.noConfusion he)
    (rowTwoTheta (h + 5)) (lenRowTwoTheta h) (caseTwoTheta h)

/-- The dual pair's first member: its identity contribution,
one. -/
private theorem rowTieDualA (h : Nat) :
    weylchar.multAtGap (adjchar.multRead (h + 5))
      (places.display (rowDualA (h + 5)))
      (places.display (adjchar.theta (h + 5))) = 1 :=
  rowTieOf h 0 (h + 3) (Nat.succ_pos (h + 4))
    (Nat.lt_succ_of_lt (Nat.lt_succ_self (h + 3)))
    (fun he => Nat.noConfusion he)
    (rowDualA (h + 5)) (lenRowDualA h) (caseDualA h)

/-- The dual pair's second member: its identity contribution,
one. -/
private theorem rowTieDualB (h : Nat) :
    weylchar.multAtGap (adjchar.multRead (h + 5))
      (places.display (rowDualB (h + 5)))
      (places.display (adjchar.theta (h + 5))) = 1 :=
  rowTieOf h 1 (h + 4)
    (Nat.lt_of_lt_of_le (by decide +kernel : (1 : Nat) < 5)
      (Nat.le_add_left 5 h))
    (Nat.lt_succ_self (h + 4))
    (fun he => Nat.noConfusion (Nat.succ.inj he))
    (rowDualB (h + 5)) (lenRowDualB h) (caseDualB h)

/-- The `ω₂ + ω₂*` row: its identity contribution, one. -/
private theorem rowTieOmega (h : Nat) :
    weylchar.multAtGap (adjchar.multRead (h + 5))
      (places.display (rowOmega (h + 5)))
      (places.display (adjchar.theta (h + 5))) = 1 :=
  rowTieOf h 1 (h + 3)
    (Nat.lt_of_lt_of_le (by decide +kernel : (1 : Nat) < 5)
      (Nat.le_add_left 5 h))
    (Nat.lt_succ_of_lt (Nat.lt_succ_self (h + 3)))
    (fun he => Nat.noConfusion (Nat.succ.inj he))
    (rowOmega (h + 5)) (lenRowOmega h) (caseOmega h)

/-- The identity permutation reads the θ display back. -/
private theorem expoRange (h : Nat) :
    places.expo (places.display (adjchar.theta (h + 5)))
        (List.range (h + 5))
      = places.display (adjchar.theta (h + 5)) :=
  ground.range_map_getAt 0 (h + 5)
    (places.display (adjchar.theta (h + 5)))
    (by rw [places.length_display, adjchar.length_theta])

/-- The identity permutation sits in the enumeration. -/
private theorem permRange (h : Nat) :
    0 < ground.countOf (List.range (h + 5)) (places.perms (h + 5)) := by
  rw [places.countRangePerms (h + 5)]
  exact Nat.succ_pos 0

/-- The identity permutation's step at a row: the even side gains
the row's own identity contribution. -/
private theorem stepAt (h : Nat) (c : places.Shape)
    (hone : weylchar.multAtGap (adjchar.multRead (h + 5))
      (places.display c) (places.display (adjchar.theta (h + 5))) = 1)
    (acc : Nat × Nat) :
    (match ground.tieGap (places.display c)
        (places.expo (places.display (adjchar.theta (h + 5)))
          (List.range (h + 5))) with
      | none => acc
      | some m =>
        if places.parity (List.range (h + 5)) then
          (acc.1, acc.2 + adjchar.multRead (h + 5) m)
        else (acc.1 + adjchar.multRead (h + 5) m, acc.2))
      = (acc.1 + 1, acc.2) := by
  rw [expoRange h, places.parity_range (h + 5)]
  cases hg : ground.tieGap (places.display c)
      (places.display (adjchar.theta (h + 5))) with
  | none =>
    have hr : (match ground.tieGap (places.display c)
        (places.display (adjchar.theta (h + 5))) with
      | some nu => adjchar.multRead (h + 5) nu
      | none => 0) = 1 := hone
    rw [hg] at hr
    exact Nat.noConfusion hr
  | some m =>
    have hr : (match ground.tieGap (places.display c)
        (places.display (adjchar.theta (h + 5))) with
      | some nu => adjchar.multRead (h + 5) nu
      | none => 0) = 1 := hone
    rw [hg] at hr
    show ((acc.1 + adjchar.multRead (h + 5) m, acc.2) : Nat × Nat)
      = (acc.1 + 1, acc.2)
    rw [show adjchar.multRead (h + 5) m = 1 from hr]

/-- A permutation off the identity keeps the accumulating pass at
a target off the `θ` row: both arms of the content read force the
`θ` row's own display. -/
private theorem stepOff (h : Nat) (c : places.Shape)
    (hne : ¬ c = rowTheta (h + 5))
    (p : List Nat) (hpm : p ∈ places.perms (h + 5))
    (hpr : ¬ p = List.range (h + 5)) (acc : Nat × Nat) :
    (match ground.tieGap (places.display c)
        (places.expo (places.display (adjchar.theta (h + 5))) p) with
      | none => acc
      | some m =>
        if places.parity p then
          (acc.1, acc.2 + adjchar.multRead (h + 5) m)
        else (acc.1 + adjchar.multRead (h + 5) m, acc.2))
      = acc := by
  have hp : 0 < ground.countOf p (places.perms (h + 5)) :=
    ground.countOf_pos_of_mem hpm
  cases hg : ground.tieGap (places.display c)
      (places.expo (places.display (adjchar.theta (h + 5))) p) with
  | none => rfl
  | some m =>
    have hz : adjchar.multRead (h + 5) m = 0 := by
      match Nat.eq_zero_or_pos (adjchar.multRead (h + 5) m) with
      | .inl hz0 => exact hz0
      | .inr hpos =>
        have hdisp : places.display c
            = (places.display (adjchar.theta (h + 5))).map
                (fun x => x + 1) := by
          cases adjchar.multRead_cases (h + 5) m hpos with
          | inl harm =>
            exact (places.tieOnes (h + 5) (adjchar.theta (h + 5)) c
              (adjchar.length_theta (h + 5)) p hp m hg harm.2.1).2
          | inr harm =>
            obtain ⟨i, hi, j, hj, hij, h2, h0, h1⟩ := harm.2.1
            obtain ⟨_, _, _, _, hd⟩ :=
              places.tieMove (h + 5) (adjchar.theta (h + 5)) c
                (adjchar.length_theta (h + 5)) p hp hpr m hg i j h2 h0 h1
            exact hd
        exact absurd (places.display_inj c (rowTheta (h + 5))
          (hdisp.trans (dispY (h + 5)).symm)) hne
    show (if places.parity p then
        (acc.1, acc.2 + adjchar.multRead (h + 5) m)
      else (acc.1 + adjchar.multRead (h + 5) m, acc.2)) = acc
    rw [hz]
    cases places.parity p with
    | true =>
      show ((acc.1, acc.2 + 0) : Nat × Nat) = acc
      rw [Nat.add_zero]
    | false =>
      show ((acc.1 + 0, acc.2) : Nat × Nat) = acc
      rw [Nat.add_zero]

/-- A modification's fast count is one: the identity permutation
is the one contributor and its contribution the tie's own. -/
private theorem countOne (h : Nat) (c : places.Shape)
    (hne : ¬ c = rowTheta (h + 5))
    (hone : weylchar.multAtGap (adjchar.multRead (h + 5))
      (places.display c) (places.display (adjchar.theta (h + 5))) = 1) :
    countAt (h + 5) c = 1 := by
  have hsum : steinberg.sumsWith (adjchar.multRead (h + 5)) (h + 5)
      (adjchar.theta (h + 5)) c = (1, 0) := by
    show (places.perms (h + 5)).foldl
        (fun acc p =>
          match ground.tieGap (places.display c)
            (places.expo (places.display (adjchar.theta (h + 5))) p) with
          | none => acc
          | some m =>
            if places.parity p then
              (acc.1, acc.2 + adjchar.multRead (h + 5) m)
            else (acc.1 + adjchar.multRead (h + 5) m, acc.2))
        (0, 0) = (1, 0)
    rw [ground.foldl_pick _ (List.range (h + 5))
      (fun acc => (acc.1 + 1, acc.2)) (stepAt h c hone)
      (places.perms (h + 5))
      (fun p hpm hpr acc => stepOff h c hne p hpm hpr acc)
      (places.countRangePerms (h + 5)) (0, 0)]
  show (steinberg.sumsWith (adjchar.multRead (h + 5)) (h + 5)
        (adjchar.theta (h + 5)) c).1
      - (steinberg.sumsWith (adjchar.multRead (h + 5)) (h + 5)
        (adjchar.theta (h + 5)) c).2 = 1
  rw [hsum]
  rfl

/-- The fast count at the unit channel is one, the vacuum's
multiplicity at every generic residue. -/
theorem countAt_rowUnit (h : Nat) :
    countAt (h + 5) (rowUnit (h + 5)) = 1 :=
  countOne h (rowUnit (h + 5)) (neUnitTheta h) (rowTieUnit h)

/-- The further modifications' fast counts, each at one. -/
private theorem countRowTwoTheta (h : Nat) :
    countAt (h + 5) (rowTwoTheta (h + 5)) = 1 :=
  countOne h (rowTwoTheta (h + 5))
    (fun he => neThetaTwoTheta h he.symm) (rowTieTwoTheta h)

private theorem countRowDualA (h : Nat) :
    countAt (h + 5) (rowDualA (h + 5)) = 1 :=
  countOne h (rowDualA (h + 5))
    (fun he => neThetaDualA h he.symm) (rowTieDualA h)

private theorem countRowDualB (h : Nat) :
    countAt (h + 5) (rowDualB (h + 5)) = 1 :=
  countOne h (rowDualB (h + 5))
    (fun he => neThetaDualB h he.symm) (rowTieDualB h)

private theorem countRowOmega (h : Nat) :
    countAt (h + 5) (rowOmega (h + 5)) = 1 :=
  countOne h (rowOmega (h + 5))
    (fun he => neThetaOmega h he.symm) (rowTieOmega h)

/-- The fast count at a shape off the table's rows is the fold's
unit: every tie's classification lands on a row. -/
private theorem countOff (h : Nat) (c : places.Shape)
    (n1 : ¬ c = rowUnit (h + 5)) (n2 : ¬ c = rowTheta (h + 5))
    (n3 : ¬ c = rowTwoTheta (h + 5)) (n4 : ¬ c = rowDualA (h + 5))
    (n5 : ¬ c = rowDualB (h + 5)) (n6 : ¬ c = rowOmega (h + 5)) :
    countAt (h + 5) c = 0 := by
  have hat : ∀ acc : Nat × Nat,
      (match ground.tieGap (places.display c)
          (places.expo (places.display (adjchar.theta (h + 5)))
            (List.range (h + 5))) with
        | none => acc
        | some m =>
          if places.parity (List.range (h + 5)) then
            (acc.1, acc.2 + adjchar.multRead (h + 5) m)
          else (acc.1 + adjchar.multRead (h + 5) m, acc.2))
        = acc := by
    intro acc
    rw [expoRange h, places.parity_range (h + 5)]
    cases hg : ground.tieGap (places.display c)
        (places.display (adjchar.theta (h + 5))) with
    | none => rfl
    | some m =>
      have hz : adjchar.multRead (h + 5) m = 0 := by
        match Nat.eq_zero_or_pos (adjchar.multRead (h + 5) m) with
        | .inl hz0 => exact hz0
        | .inr hpos =>
          cases adjchar.multRead_cases (h + 5) m hpos with
          | inl harm =>
            have hg' : ground.tieGap (places.display c)
                (places.expo (places.display (adjchar.theta (h + 5)))
                  (List.range (h + 5))) = some m := by
              rw [expoRange h]
              exact hg
            have hd := (places.tieOnes (h + 5) (adjchar.theta (h + 5)) c
              (adjchar.length_theta (h + 5)) (List.range (h + 5))
              (permRange h) m hg' harm.2.1).2
            exact absurd (places.display_inj c (rowTheta (h + 5))
              (hd.trans (dispY (h + 5)).symm)) n2
          | inr harm =>
            obtain ⟨i, hi, j, hj, hij, h2, h0, h1⟩ := harm.2.1
            cases tieMoveRange h c m hg i hi j hj hij h2 h0 h1 with
            | inl he => exact absurd he n1
            | inr r2 =>
              cases r2 with
              | inl he => exact absurd he n3
              | inr r3 =>
                cases r3 with
                | inl he => exact absurd he n4
                | inr r4 =>
                  cases r4 with
                  | inl he => exact absurd he n5
                  | inr he => exact absurd he n6
      show ((acc.1 + adjchar.multRead (h + 5) m, acc.2) : Nat × Nat) = acc
      rw [hz, Nat.add_zero]
  have hsum : steinberg.sumsWith (adjchar.multRead (h + 5)) (h + 5)
      (adjchar.theta (h + 5)) c = (0, 0) := by
    show (places.perms (h + 5)).foldl
        (fun acc p =>
          match ground.tieGap (places.display c)
            (places.expo (places.display (adjchar.theta (h + 5))) p) with
          | none => acc
          | some m =>
            if places.parity p then
              (acc.1, acc.2 + adjchar.multRead (h + 5) m)
            else (acc.1 + adjchar.multRead (h + 5) m, acc.2))
        (0, 0) = (0, 0)
    rw [ground.foldl_pick _ (List.range (h + 5)) (fun acc => acc) hat
      (places.perms (h + 5))
      (fun p hpm hpr acc => stepOff h c n2 p hpm hpr acc)
      (places.countRangePerms (h + 5)) (0, 0)]
  show (steinberg.sumsWith (adjchar.multRead (h + 5)) (h + 5)
        (adjchar.theta (h + 5)) c).1
      - (steinberg.sumsWith (adjchar.multRead (h + 5)) (h + 5)
        (adjchar.theta (h + 5)) c).2 = 0
  rw [hsum]
  rfl

/-- The run's adjacent exchanges, one per unit gap of the `θ`
display. -/
private def swapList (h : Nat) : List (List Nat) :=
  (List.range (h + 2)).map (fun t => ground.adjSwap (t + 1)
    (List.range (h + 5)))

/-- The exchange list holds each of its members at its own key's
count. -/
private theorem swapCount (h t0 : Nat) (ht0 : t0 < h + 2) :
    ∀ (L : List Nat), (∀ x, 0 < ground.countOf x L → x < h + 2) →
      ground.countOf (ground.adjSwap (t0 + 1) (List.range (h + 5)))
          (L.map (fun t => ground.adjSwap (t + 1) (List.range (h + 5))))
        = ground.countOf t0 L
  | [], _ => rfl
  | b :: t, hb => by
    have hbb : b < h + 2 :=
      hb b (by rw [ground.countOf_head]; exact Nat.succ_pos _)
    have hrec := swapCount h t0 ht0 t
      (fun x hx => hb x (ground.countOf_cons_pos hx))
    have h1 : t0 + 1 + 1 < h + 5 :=
      Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ ht0))
        (Nat.le_succ (h + 4))
    have h2 : b + 1 + 1 < h + 5 :=
      Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ hbb))
        (Nat.le_succ (h + 4))
    show ground.countOf (ground.adjSwap (t0 + 1) (List.range (h + 5)))
        (ground.adjSwap (b + 1) (List.range (h + 5))
          :: t.map (fun t => ground.adjSwap (t + 1) (List.range (h + 5))))
      = ground.countOf t0 (b :: t)
    rw [ground.countOf_cons, ground.countOf_cons, hrec]
    by_cases he : t0 = b
    · rw [if_pos he, if_pos (congrArg
        (fun z => ground.adjSwap (z + 1) (List.range (h + 5))) he)]
    · rw [if_neg he, if_neg (fun hq => he (Nat.succ.inj
        (ground.adjSwap_range_inj (h + 5) (t0 + 1) (b + 1) h1 h2 hq)))]

/-- The exchange list's member count, one at every key of the
run. -/
private theorem swapListCount (h t : Nat) (ht : t < h + 2) :
    ground.countOf (ground.adjSwap (t + 1) (List.range (h + 5)))
      (swapList h) = 1 := by
  show ground.countOf (ground.adjSwap (t + 1) (List.range (h + 5)))
    ((List.range (h + 2)).map (fun q => ground.adjSwap (q + 1)
      (List.range (h + 5)))) = 1
  rw [swapCount h t ht (List.range (h + 2)) (fun _ hx => ground.ltOfMem hx),
    ground.countOf_range_one ht]

/-- An exchange list member names its key. -/
private theorem swapMember (h : Nat) (p : List Nat)
    (hm : 0 < ground.countOf p (swapList h)) :
    ∃ t, t < h + 2 ∧ p = ground.adjSwap (t + 1) (List.range (h + 5)) := by
  have hmem : p ∈ (List.range (h + 2)).map
      (fun t => ground.adjSwap (t + 1) (List.range (h + 5))) :=
    ground.mem_of_countOf_pos p (swapList h) hm
  obtain ⟨t, ht, hft⟩ := ground.mem_map_of
    (fun t => ground.adjSwap (t + 1) (List.range (h + 5)))
    (List.range (h + 2)) p hmem
  exact ⟨t, ground.ltOfMemRange ht, hft.symm⟩

/-- A unit gap of the `θ` display sits at the run: the head's
doubled gap and the last key's own refuse it. -/
private theorem gapAtRun (h k : Nat) (hk : k + 1 < h + 5)
    (hgap : ground.getAt 0 (places.display (adjchar.theta (h + 5))) k
      = ground.getAt 0 (places.display (adjchar.theta (h + 5))) (k + 1)
        + 1) : 1 ≤ k ∧ k ≤ h + 2 := by
  have hk0 : ¬ k = 0 := by
    intro he
    rw [he, yHead h, show (0 : Nat) + 1 = 1 from rfl, ySecond h] at hgap
    exact absurd (ground.addCancelL h (show h + 7 = h + 6 from hgap))
      (by decide +kernel)
  refine ⟨Nat.pos_of_ne_zero hk0, ?_⟩
  cases Nat.lt_or_ge k (h + 3) with
  | inl hlt => exact Nat.le_of_lt_succ hlt
  | inr hge =>
    have hke : k = h + 3 :=
      Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hk)) hge
    have hgv : ground.getAt 0
          (places.display (adjchar.theta (h + 5))) (h + 3)
        = ground.getAt 0
            (places.display (adjchar.theta (h + 5))) (h + 4) + 1 := by
      rw [hke] at hgap
      exact hgap
    rw [yFourth h, yLast h] at hgv
    exact absurd hgv (by decide +kernel)

/-- The two graded sums at the θ row: the residue's count on the
even side against the run's exchanges on the odd. -/
private theorem sumsTheta (h : Nat) :
    steinberg.sumsWith (adjchar.multRead (h + 5)) (h + 5)
      (adjchar.theta (h + 5)) (rowTheta (h + 5)) = (h + 4, h + 2) := by
  have hstepE : ∀ p ∈ places.perms (h + 5), p ≠ List.range (h + 5) →
      (if places.parity p = false then
        weylchar.multAtGap (adjchar.multRead (h + 5))
          (places.display (rowTheta (h + 5)))
          (places.expo (places.display (adjchar.theta (h + 5))) p)
      else 0) = 0 := by
    intro p hpm hpr
    by_cases hpar : places.parity p = false
    · rw [if_pos hpar]
      have hp : 0 < ground.countOf p (places.perms (h + 5)) :=
        ground.countOf_pos_of_mem hpm
      match Nat.eq_zero_or_pos (weylchar.multAtGap (adjchar.multRead (h + 5))
          (places.display (rowTheta (h + 5)))
          (places.expo (places.display (adjchar.theta (h + 5))) p)) with
      | .inl hz => exact hz
      | .inr hpos =>
        obtain ⟨m, hg, hmpos⟩ := weylchar.multAtGap_pos (adjchar.multRead (h + 5)) _ _ hpos
        cases adjchar.multRead_cases (h + 5) m hmpos with
        | inl harm =>
          exact absurd (places.tieOnes (h + 5) (adjchar.theta (h + 5))
            (rowTheta (h + 5)) (adjchar.length_theta (h + 5))
            p hp m hg harm.2.1).1 hpr
        | inr harm =>
          obtain ⟨i, hi, j, hj, hij, h2, h0, h1⟩ := harm.2.1
          obtain ⟨k, hk1, _, hpk, _⟩ :=
            places.tieMove (h + 5) (adjchar.theta (h + 5))
              (rowTheta (h + 5)) (adjchar.length_theta (h + 5)) p hp hpr
              m hg i j h2 h0 h1
          rw [hpk, places.parity_adjSwap_range (h + 5) k hk1] at hpar
          exact Bool.noConfusion hpar
    · rw [if_neg hpar]
  have heven : ground.famFold Nat.add 0
      (fun p => if places.parity p = false then
        weylchar.multAtGap (adjchar.multRead (h + 5))
          (places.display (rowTheta (h + 5)))
          (places.expo (places.display (adjchar.theta (h + 5))) p)
      else 0) (places.perms (h + 5)) = h + 4 := by
    rw [ground.famFold_off _ (List.range (h + 5)) (places.perms (h + 5))
        hstepE,
      places.countRangePerms (h + 5), places.parity_range (h + 5),
      if_pos rfl, expoRange h, rowTieTheta h, Nat.one_mul]
  have hstepO : ∀ p, 0 < ground.countOf p (places.perms (h + 5)) →
      (if places.parity p = true then
        weylchar.multAtGap (adjchar.multRead (h + 5))
          (places.display (rowTheta (h + 5)))
          (places.expo (places.display (adjchar.theta (h + 5))) p)
      else 0) = ground.countOf p (swapList h) := by
    intro p hp
    by_cases hpar : places.parity p = true
    · rw [if_pos hpar]
      by_cases hmem : 0 < ground.countOf p (swapList h)
      · obtain ⟨t, ht, hpt⟩ := swapMember h p hmem
        rw [hpt, swapListCount h t ht]
        exact tieSwapMult h (t + 1) (Nat.succ_le_succ (Nat.zero_le t))
          (Nat.succ_le_succ (Nat.le_of_lt_succ ht))
      · have hz : ground.countOf p (swapList h) = 0 :=
          match Nat.eq_zero_or_pos (ground.countOf p (swapList h)) with
          | .inl hz0 => hz0
          | .inr hp0 => absurd hp0 hmem
        rw [hz]
        match Nat.eq_zero_or_pos
            (weylchar.multAtGap (adjchar.multRead (h + 5))
              (places.display (rowTheta (h + 5)))
              (places.expo (places.display (adjchar.theta (h + 5))) p)) with
        | .inl hz0 => exact hz0
        | .inr hpos =>
          obtain ⟨m, hg, hmpos⟩ := weylchar.multAtGap_pos (adjchar.multRead (h + 5)) _ _ hpos
          by_cases hpr : p = List.range (h + 5)
          · rw [hpr, places.parity_range (h + 5)] at hpar
            exact Bool.noConfusion hpar
          · cases adjchar.multRead_cases (h + 5) m hmpos with
            | inl harm =>
              exact absurd (places.tieOnes (h + 5) (adjchar.theta (h + 5))
                (rowTheta (h + 5)) (adjchar.length_theta (h + 5))
                p hp m hg harm.2.1).1 hpr
            | inr harm =>
              obtain ⟨i, hi, j, hj, hij, h2, h0, h1⟩ := harm.2.1
              obtain ⟨k, hk1, hgk, hpk, _⟩ :=
                places.tieMove (h + 5) (adjchar.theta (h + 5))
                  (rowTheta (h + 5)) (adjchar.length_theta (h + 5)) p hp
                  hpr m hg i j h2 h0 h1
              obtain ⟨hk1le, hk2le⟩ := gapAtRun h k hk1 hgk
              cases k with
              | zero => exact absurd hk1le (Nat.lt_irrefl 0)
              | succ k0 =>
                refine absurd ?_ hmem
                rw [hpk, swapListCount h k0
                  (Nat.lt_of_succ_le hk2le)]
                exact Nat.succ_pos 0
    · rw [if_neg hpar]
      have hz : ground.countOf p (swapList h) = 0 :=
        match Nat.eq_zero_or_pos (ground.countOf p (swapList h)) with
        | .inl hz0 => hz0
        | .inr hp0 => by
          obtain ⟨t, ht, hpt⟩ := swapMember h p hp0
          rw [hpt, places.parity_adjSwap_range (h + 5) (t + 1)
            (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ ht))
              (Nat.le_succ (h + 4)))] at hpar
          exact absurd rfl hpar
      rw [hz]
  have hodd : ground.famFold Nat.add 0
      (fun p => if places.parity p = true then
        weylchar.multAtGap (adjchar.multRead (h + 5))
          (places.display (rowTheta (h + 5)))
          (places.expo (places.display (adjchar.theta (h + 5))) p)
      else 0) (places.perms (h + 5)) = h + 2 := by
    rw [ground.famFold_congr_members Nat.add 0 _
        (fun p => ground.countOf p (swapList h)) (places.perms (h + 5))
        hstepO,
      ground.famFold_countSwap (places.perms (h + 5)) (swapList h),
      ground.famFold_congr_members Nat.add 0 _ (fun _ => (1 : Nat))
        (swapList h) (fun s hs => by
          obtain ⟨t, ht, hst⟩ := swapMember h s hs
          rw [hst, places.countOf_adjSwap_perms (h + 5) (t + 1)]),
      ground.famFold_length (swapList h)]
    exact ground.length_mapRange _ (h + 2)
  rw [steinberg.sumsWith_split (adjchar.multRead (h + 5)) (h + 5)
    (adjchar.theta (h + 5)) (rowTheta (h + 5)), heven, hodd]

/-- The fast count at the θ row is the walk's parameter: the
residue's count at the identity against the run's exchanges,
`con:xfusion`'s base `c₁` at every generic residue. -/
theorem countAt_rowTheta (h : Nat) :
    countAt (h + 5) (rowTheta (h + 5)) = 2 := by
  show (steinberg.sumsWith (adjchar.multRead (h + 5)) (h + 5)
        (adjchar.theta (h + 5)) (rowTheta (h + 5))).1
      - (steinberg.sumsWith (adjchar.multRead (h + 5)) (h + 5)
        (adjchar.theta (h + 5)) (rowTheta (h + 5))).2 = 2
  rw [sumsTheta h]
  show h + 4 - (h + 2) = 2
  rw [show h + 4 = h + 2 + 2 from rfl, ground.addSubSelfL (h + 2) 2]

/-- The table's rows at the matched degree, both thresholds passed
and the `θ` row at the walk's parameter. -/
private theorem rowsList (h : Nat) :
    rows (h + 5) = [(rowUnit (h + 5), 1), (rowTheta (h + 5), 2),
      (rowTwoTheta (h + 5), 1), (rowDualA (h + 5), 1),
      (rowDualB (h + 5), 1), (rowOmega (h + 5), 1)] := rfl

/-- A guarded accumulation carries its weight additively. -/
private theorem iteAdd (P : Prop) [Decidable P] (a m : Nat) :
    (if P then a + m else a) = a + (if P then m else 0) := by
  by_cases hP : P
  · rw [if_pos hP, if_pos hP]
  · rw [if_neg hP, if_neg hP, Nat.add_zero]

/-- The occupancy fold's step at one row. -/
private theorem foldRowStep (c : places.Shape) (a : Nat)
    (r : places.Shape × Nat) (l : List (places.Shape × Nat)) :
    (r :: l).foldl (fun acc q => if q.1 = c then acc + q.2 else acc) a
      = l.foldl (fun acc q => if q.1 = c then acc + q.2 else acc)
          (a + if r.1 = c then r.2 else 0) := by
  show l.foldl (fun acc q => if q.1 = c then acc + q.2 else acc)
      (if r.1 = c then a + r.2 else a) = _
  rw [iteAdd (r.1 = c) a r.2]

/-- The table's occupancy read at the matched degree, one term per
row. -/
private theorem rowReadSum (h : Nat) (c : places.Shape) :
    rowRead (h + 5) c
      = (if rowUnit (h + 5) = c then 1 else 0)
        + (if rowTheta (h + 5) = c then 2 else 0)
        + (if rowTwoTheta (h + 5) = c then 1 else 0)
        + (if rowDualA (h + 5) = c then 1 else 0)
        + (if rowDualB (h + 5) = c then 1 else 0)
        + (if rowOmega (h + 5) = c then 1 else 0) := by
  show (rows (h + 5)).foldl
    (fun acc r => if r.1 = c then acc + r.2 else acc) 0 = _
  rw [rowsList h, foldRowStep, foldRowStep, foldRowStep, foldRowStep,
    foldRowStep, foldRowStep]
  show 0 + (if rowUnit (h + 5) = c then 1 else 0)
      + (if rowTheta (h + 5) = c then 2 else 0)
      + (if rowTwoTheta (h + 5) = c then 1 else 0)
      + (if rowDualA (h + 5) = c then 1 else 0)
      + (if rowDualB (h + 5) = c then 1 else 0)
      + (if rowOmega (h + 5) = c then 1 else 0) = _
  rw [Nat.zero_add]

/-- The six occupancy evaluations: the `θ` row at the walk's
parameter, the five modifications at one, and every further shape
of the width at the fold's unit. -/
private theorem rowReadUnit (h : Nat) :
    rowRead (h + 5) (rowUnit (h + 5)) = 1 := by
  rw [rowReadSum h (rowUnit (h + 5)),
    if_pos (show rowUnit (h + 5) = rowUnit (h + 5) from rfl),
    if_neg (Ne.symm (neUnitTheta h)), if_neg (Ne.symm (neUnitTwoTheta h)),
    if_neg (Ne.symm (neUnitDualA h)), if_neg (Ne.symm (neUnitDualB h)),
    if_neg (Ne.symm (neUnitOmega h))]

private theorem rowReadTheta (h : Nat) :
    rowRead (h + 5) (rowTheta (h + 5)) = 2 := by
  rw [rowReadSum h (rowTheta (h + 5)), if_neg (neUnitTheta h),
    if_pos (show rowTheta (h + 5) = rowTheta (h + 5) from rfl),
    if_neg (Ne.symm (neThetaTwoTheta h)), if_neg (Ne.symm (neThetaDualA h)),
    if_neg (Ne.symm (neThetaDualB h)), if_neg (Ne.symm (neThetaOmega h))]

private theorem rowReadTwoTheta (h : Nat) :
    rowRead (h + 5) (rowTwoTheta (h + 5)) = 1 := by
  rw [rowReadSum h (rowTwoTheta (h + 5)), if_neg (neUnitTwoTheta h),
    if_neg (neThetaTwoTheta h),
    if_pos (show rowTwoTheta (h + 5) = rowTwoTheta (h + 5) from rfl),
    if_neg (Ne.symm (neTwoThetaDualA h)),
    if_neg (Ne.symm (neTwoThetaDualB h)),
    if_neg (Ne.symm (neTwoThetaOmega h))]

private theorem rowReadDualA (h : Nat) :
    rowRead (h + 5) (rowDualA (h + 5)) = 1 := by
  rw [rowReadSum h (rowDualA (h + 5)), if_neg (neUnitDualA h),
    if_neg (neThetaDualA h), if_neg (neTwoThetaDualA h),
    if_pos (show rowDualA (h + 5) = rowDualA (h + 5) from rfl),
    if_neg (Ne.symm (neDualADualB h)), if_neg (Ne.symm (neDualAOmega h))]

private theorem rowReadDualB (h : Nat) :
    rowRead (h + 5) (rowDualB (h + 5)) = 1 := by
  rw [rowReadSum h (rowDualB (h + 5)), if_neg (neUnitDualB h),
    if_neg (neThetaDualB h), if_neg (neTwoThetaDualB h),
    if_neg (neDualADualB h),
    if_pos (show rowDualB (h + 5) = rowDualB (h + 5) from rfl),
    if_neg (Ne.symm (neDualBOmega h))]

private theorem rowReadOmega (h : Nat) :
    rowRead (h + 5) (rowOmega (h + 5)) = 1 := by
  rw [rowReadSum h (rowOmega (h + 5)), if_neg (neUnitOmega h),
    if_neg (neThetaOmega h), if_neg (neTwoThetaOmega h),
    if_neg (neDualAOmega h), if_neg (neDualBOmega h),
    if_pos (show rowOmega (h + 5) = rowOmega (h + 5) from rfl)]

private theorem rowReadOff (h : Nat) (c : places.Shape)
    (n1 : ¬ c = rowUnit (h + 5)) (n2 : ¬ c = rowTheta (h + 5))
    (n3 : ¬ c = rowTwoTheta (h + 5)) (n4 : ¬ c = rowDualA (h + 5))
    (n5 : ¬ c = rowDualB (h + 5)) (n6 : ¬ c = rowOmega (h + 5)) :
    rowRead (h + 5) c = 0 := by
  rw [rowReadSum h c, if_neg (Ne.symm n1), if_neg (Ne.symm n2),
    if_neg (Ne.symm n3), if_neg (Ne.symm n4), if_neg (Ne.symm n5),
    if_neg (Ne.symm n6)]

/-- The fast count reads the table's occupancy at every shape of
the width. -/
private theorem pointwise (h : Nat) (c : places.Shape) :
    countAt (h + 5) c = rowRead (h + 5) c := by
  by_cases n1 : c = rowUnit (h + 5)
  · rw [n1, countAt_rowUnit h, rowReadUnit h]
  · by_cases n2 : c = rowTheta (h + 5)
    · rw [n2, countAt_rowTheta h, rowReadTheta h]
    · by_cases n3 : c = rowTwoTheta (h + 5)
      · rw [n3, countRowTwoTheta h, rowReadTwoTheta h]
      · by_cases n4 : c = rowDualA (h + 5)
        · rw [n4, countRowDualA h, rowReadDualA h]
        · by_cases n5 : c = rowDualB (h + 5)
          · rw [n5, countRowDualB h, rowReadDualB h]
          · by_cases n6 : c = rowOmega (h + 5)
            · rw [n6, countRowOmega h, rowReadOmega h]
            · rw [countOff h c n1 n2 n3 n4 n5 n6,
                rowReadOff h c n1 n2 n3 n4 n5 n6]

/-- The whole list at a generic residue: every shape at the matched
degree reads its own row. -/
private theorem readGen (h : Nat) : tableRead (h + 5) := by
  show ((places.allShapes (h + 5) (2 * (h + 5))).all
    (fun c => countAt (h + 5) c == rowRead (h + 5) c)) = true
  refine ground.all_of_getAt ([] : places.Shape) _
    (places.allShapes (h + 5) (2 * (h + 5))) (fun k _ => ?_)
  exact ground.eqBeqOf (pointwise h _)

/-- `lem:channels`' general theorem: the whole list at every
residue — over every shape at the matched degree the fast count
reads the table's occupancy, `cor:steinberg` at the adjoint square:
the identity permutation reads the unit-monomial content at the
residue's count against one odd adjacent exchange per unit gap of
the run, the five modifications each at count one on the even side,
and the low residues their own decided reads. -/
theorem readAll : ∀ d : Nat, 2 ≤ d → tableRead d := by
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
    exact readGen h

/-- The `θ` and `2θ` rows' tail fold at the single lowest entry. -/
private theorem gapRunTwo : ∀ k : Nat,
    weyldim.gapRun [2] 4 k = ground.factorial (k + 1)
  | 0 => rfl
  | k + 1 => by
    show weyldim.gapRun [2] 4 k * ((k + 4 - 2) * 1)
      = ground.factorial (k + 1 + 1)
    rw [gapRunTwo k, Nat.mul_one]
    show ground.factorial (k + 1) * (k + 2) = (k + 2) * ground.factorial (k + 1)
    rw [Nat.mul_comm]

/-- The `2θ` and dual pair's tail fold at the vacant lowest
entry. -/
private theorem gapRunOne : ∀ k : Nat,
    weyldim.gapRun [1] 4 k * 2 = ground.factorial (k + 2)
  | 0 => rfl
  | k + 1 => by
    show weyldim.gapRun [1] 4 k * ((k + 4 - 1) * 1) * 2
      = ground.factorial (k + 1 + 2)
    rw [Nat.mul_one]
    show weyldim.gapRun [1] 4 k * (k + 3) * 2 = ground.factorial (k + 3)
    rw [ground.mulAssoc (weyldim.gapRun [1] 4 k) (k + 3) 2,
      Nat.mul_comm (k + 3) 2,
      ← ground.mulAssoc (weyldim.gapRun [1] 4 k) 2 (k + 3), gapRunOne k]
    show ground.factorial (k + 2) * (k + 3)
      = (k + 3) * ground.factorial (k + 2)
    rw [Nat.mul_comm]

/-- The four-factor product's swap. -/
private theorem mulSwap4 (A B p q : Nat) :
    A * B * (p * q) = p * A * (q * B) := by
  rw [ground.mulAssoc A B (p * q), ← ground.mulAssoc B p q,
    Nat.mul_comm B p, ground.mulAssoc p B q,
    mulLeftComm A p (B * q), Nat.mul_comm B q,
    ← ground.mulAssoc p A (q * B)]

/-- The dual pair's and `ω₂ + ω₂*`'s tail fold at the two lowest
entries. -/
private theorem gapRunPair : ∀ k : Nat,
    weyldim.gapRun [3, 2] 5 k * 2
      = ground.factorial (k + 1) * ground.factorial (k + 2)
  | 0 => rfl
  | k + 1 => by
    show weyldim.gapRun [3, 2] 5 k * ((k + 5 - 3) * ((k + 5 - 2) * 1)) * 2
      = ground.factorial (k + 1 + 1) * ground.factorial (k + 1 + 2)
    rw [Nat.mul_one]
    show weyldim.gapRun [3, 2] 5 k * ((k + 2) * (k + 3)) * 2
      = (k + 2) * ground.factorial (k + 1)
        * ((k + 3) * ground.factorial (k + 2))
    rw [ground.mulAssoc (weyldim.gapRun [3, 2] 5 k) ((k + 2) * (k + 3)) 2,
      Nat.mul_comm ((k + 2) * (k + 3)) 2,
      ← ground.mulAssoc (weyldim.gapRun [3, 2] 5 k) 2 ((k + 2) * (k + 3)),
      gapRunPair k]
    exact mulSwap4 (ground.factorial (k + 1)) (ground.factorial (k + 2))
      (k + 2) (k + 3)

/-- The cleared dimension read: the naming identity's product
withdrawn at the unit display's own. -/
private theorem dimClear (s : Shape) (n c p : Nat) (hn : s.length = n)
    (hg : c * weyldim.gapProd (places.display s)
      = p * weyldim.gapProd (places.unitDisp n)) :
    c * weyldim.dimOf s = p := by
  refine Nat.eq_of_mul_eq_mul_right (weyldim.gapProdU_pos s) ?_
  have hr : weyldim.dimOf s * weyldim.gapProd
      (places.display (List.replicate s.length 0))
      = weyldim.gapProd (places.display s) := weyldim.readAll s
  show c * weyldim.dimOf s * weyldim.gapProd
      (places.display (List.replicate s.length 0))
    = p * weyldim.gapProd (places.display (List.replicate s.length 0))
  rw [ground.mulAssoc c (weyldim.dimOf s), hr, hn]
  exact hg

/-- The unit display's gap product, peeled to the `θ` rows'
run. -/
private theorem unitNF3 (h : Nat) :
    weyldim.gapProd (places.unitDisp (h + 5))
      = ground.factorial (h + 4) * (ground.factorial (h + 3)
        * weyldim.gapProd (weyldim.descRun 1 (h + 3))) := by
  have u1 : weyldim.gapProd (weyldim.descRun 1 (h + 5))
      = ground.factorial (h + 4)
        * weyldim.gapProd (weyldim.descRun 1 (h + 4)) :=
    weyldim.gapProd_descRun_succ 1 (h + 4)
  have u2 : weyldim.gapProd (weyldim.descRun 1 (h + 4))
      = ground.factorial (h + 3)
        * weyldim.gapProd (weyldim.descRun 1 (h + 3)) :=
    weyldim.gapProd_descRun_succ 1 (h + 3)
  rw [weyldim.unitDisp_descRun (h + 5), u1, u2]

/-- The adjoint's cleared dimension at the crossed pair. -/
private theorem adjSq (h : Nat) :
    (h + 5) * (h + 5) - 1 = (h + 4) * (h + 6) := by
  rw [show (h + 5) * (h + 5) = (h + 4) * (h + 6) + 1
      from ground.sqJoin (h + 4)]
  exact ground.addSubSelfR ((h + 4) * (h + 6)) 1

/-- The `θ` row's product shuffle. -/
private theorem arithTheta (p q B G : Nat) :
    4 * (p * B * q * (G * (p * B))) = 4 * (p * q) * (p * B * (B * G)) := by
  repeat rw [ground.mulAssoc]
  rw [mulLeftComm B q (G * (p * B)), mulLeftComm G p B,
    mulLeftComm B p (G * B), Nat.mul_comm G B]

/-- The `θ` row's cleared gap product. -/
private theorem gapRowTheta (h : Nat) :
    4 * weyldim.gapProd ((h + 8) :: (weyldim.descRun 4 (h + 3) ++ [2]))
      = 4 * ((h + 5) * (h + 5) - 1)
        * weyldim.gapProd (places.unitDisp (h + 5)) := by
  have hA : weyldim.gapHead (h + 8) (weyldim.descRun 4 (h + 3))
      = ground.factorial (h + 4) := by
    have h1 : weyldim.gapHead (h + 8) (weyldim.descRun 4 (h + 3)) * 1
        = ground.factorial (h + 4) := weyldim.gapHead_descRun 4 (h + 3) 1
    rw [Nat.mul_one] at h1
    exact h1
  have hB : weyldim.gapHead (h + 8) [2] = h + 6 := by
    show (h + 8 - 2) * 1 = h + 6
    rw [Nat.mul_one]
    rfl
  have hf : ground.factorial (h + 4)
      = (h + 4) * ground.factorial (h + 3) := rfl
  rw [weyldim.gapProd_cons, weyldim.gapHead_append,
    weyldim.gapProd_descRun_app [2] 4 (h + 3),
    weyldim.gapProd_descRun 4 1 (h + 3), gapRunTwo (h + 3), hA, hB,
    unitNF3 h, adjSq h]
  show 4 * (ground.factorial (h + 4) * (h + 6)
      * (weyldim.gapProd (weyldim.descRun 1 (h + 3))
        * (1 * ground.factorial (h + 4))))
    = 4 * ((h + 4) * (h + 6)) * (ground.factorial (h + 4)
      * (ground.factorial (h + 3)
        * weyldim.gapProd (weyldim.descRun 1 (h + 3))))
  rw [Nat.one_mul (ground.factorial (h + 4)), hf]
  exact arithTheta (h + 4) (h + 6) (ground.factorial (h + 3))
    (weyldim.gapProd (weyldim.descRun 1 (h + 3)))

/-- The unit channel's cleared gap product. -/
private theorem gapRowUnit (h : Nat) :
    4 * weyldim.gapProd (weyldim.descRun 3 (h + 5))
      = 4 * weyldim.gapProd (places.unitDisp (h + 5)) := by
  rw [weyldim.unitDisp_descRun (h + 5),
    weyldim.gapProd_descRun 3 1 (h + 5)]

/-- The four's clearing at a row's two halved folds. -/
private theorem clear4 (X Y q G : Nat) :
    4 * (X * q * (G * (1 * Y))) = X * 2 * (Y * 2 * (q * G)) := by
  show 2 * 2 * (X * q * (G * (1 * Y))) = X * 2 * (Y * 2 * (q * G))
  rw [Nat.one_mul Y]
  repeat rw [ground.mulAssoc]
  rw [mulLeftComm 2 X (q * (G * Y)), mulLeftComm 2 X (2 * (q * (G * Y))),
    Nat.mul_comm G Y, mulLeftComm q Y G, mulLeftComm 2 Y (q * G)]

/-- The `2θ` row's product shuffle. -/
private theorem arithTwoTheta (a b c F G : Nat) :
    a * (b * F) * (a * (b * F) * (c * G))
      = a * a * (b * c) * (b * F * (F * G)) := by
  repeat rw [ground.mulAssoc]
  rw [mulLeftComm F a (b * (F * (c * G))),
    mulLeftComm b a (F * (b * (F * (c * G)))),
    mulLeftComm F b (F * (c * G)), mulLeftComm F c G,
    mulLeftComm F c (F * G), mulLeftComm b c (F * (F * G))]

/-- The `2θ` row's cleared gap product. -/
private theorem gapRowTwoTheta (h : Nat) :
    4 * weyldim.gapProd ((h + 9) :: (weyldim.descRun 4 (h + 3) ++ [1]))
      = (h + 5) * (h + 5) * ((h + 4) * (h + 8))
        * weyldim.gapProd (places.unitDisp (h + 5)) := by
  have hX : weyldim.gapHead (h + 9) (weyldim.descRun 4 (h + 3)) * 2
      = ground.factorial (h + 5) := weyldim.gapHead_descRun 4 (h + 3) 2
  have hB : weyldim.gapHead (h + 9) [1] = h + 8 := by
    show (h + 9 - 1) * 1 = h + 8
    rw [Nat.mul_one]
    rfl
  have hY : weyldim.gapRun [1] 4 (h + 3) * 2 = ground.factorial (h + 5) :=
    gapRunOne (h + 3)
  have hf5 : ground.factorial (h + 5)
      = (h + 5) * ground.factorial (h + 4) := rfl
  have hf4 : ground.factorial (h + 4)
      = (h + 4) * ground.factorial (h + 3) := rfl
  rw [weyldim.gapProd_cons, weyldim.gapHead_append,
    weyldim.gapProd_descRun_app [1] 4 (h + 3),
    weyldim.gapProd_descRun 4 1 (h + 3), hB, unitNF3 h]
  show 4 * (weyldim.gapHead (h + 9) (weyldim.descRun 4 (h + 3)) * (h + 8)
      * (weyldim.gapProd (weyldim.descRun 1 (h + 3))
        * (1 * weyldim.gapRun [1] 4 (h + 3))))
    = (h + 5) * (h + 5) * ((h + 4) * (h + 8))
      * (ground.factorial (h + 4) * (ground.factorial (h + 3)
        * weyldim.gapProd (weyldim.descRun 1 (h + 3))))
  rw [clear4 (weyldim.gapHead (h + 9) (weyldim.descRun 4 (h + 3)))
      (weyldim.gapRun [1] 4 (h + 3)) (h + 8)
      (weyldim.gapProd (weyldim.descRun 1 (h + 3))), hX, hY, hf5, hf4]
  exact arithTwoTheta (h + 5) (h + 4) (h + 8) (ground.factorial (h + 3))
    (weyldim.gapProd (weyldim.descRun 1 (h + 3)))

/-- The unit display's gap product, peeled to the dual pair's
run. -/
private theorem unitNF2 (h : Nat) :
    weyldim.gapProd (places.unitDisp (h + 5))
      = ground.factorial (h + 4) * (ground.factorial (h + 3)
        * (ground.factorial (h + 2)
          * weyldim.gapProd (weyldim.descRun 1 (h + 2)))) := by
  have u3 : weyldim.gapProd (weyldim.descRun 1 (h + 3))
      = ground.factorial (h + 2)
        * weyldim.gapProd (weyldim.descRun 1 (h + 2)) :=
    weyldim.gapProd_descRun_succ 1 (h + 2)
  rw [unitNF3 h, u3]

/-- The unit display's gap product, peeled to the `ω₂ + ω₂*` row's
run. -/
private theorem unitNF1 (h : Nat) :
    weyldim.gapProd (places.unitDisp (h + 5))
      = ground.factorial (h + 4) * (ground.factorial (h + 3)
        * (ground.factorial (h + 2) * (ground.factorial (h + 1)
          * weyldim.gapProd (weyldim.descRun 1 (h + 1))))) := by
  have u2 : weyldim.gapProd (weyldim.descRun 1 (h + 2))
      = ground.factorial (h + 1)
        * weyldim.gapProd (weyldim.descRun 1 (h + 1)) :=
    weyldim.gapProd_descRun_succ 1 (h + 1)
  rw [unitNF2 h, u2]

/-- The four's clearing with the head's own gaps to the front. -/
private theorem clear4q (X Y q G : Nat) :
    4 * (X * q * (G * (1 * Y))) = q * (X * 2 * (Y * 2 * G)) := by
  rw [clear4 X Y q G]
  repeat rw [ground.mulAssoc]
  rw [mulLeftComm 2 q G, mulLeftComm Y q (2 * G),
    mulLeftComm 2 q (Y * (2 * G)),
    mulLeftComm X q (2 * (Y * (2 * G)))]

/-- The dual pair's cleared dimension at the head's gaps. -/
private theorem polyDual (b c q r : Nat) :
    c * (b * (q * r)) = q * (r * (c * b)) := by
  rw [mulLeftComm b q r, mulLeftComm c q (b * r), Nat.mul_comm b r,
    mulLeftComm c r b]

/-- The dual pair's first member: its product shuffle. -/
private theorem arithDualA (b c F q r G : Nat) :
    q * (r * (b * (c * (F * (c * (F * (b * (c * (F * G))))))))) 
      = q * (r * (c * (b * (b * (c * (F * (c * (F * (F * G))))))))) := by
  rw [mulLeftComm b c (F * (c * (F * (b * (c * (F * G)))))),
    mulLeftComm F b (c * (F * G)), mulLeftComm c b (F * (c * (F * G))),
    mulLeftComm F b (c * (F * (c * (F * G)))),
    mulLeftComm F c (F * (c * (F * G))), mulLeftComm F c (F * G)]

/-- The dual pair's first member: its cleared gap product. -/
private theorem gapRowDualA (h : Nat) :
    4 * weyldim.gapProd ((h + 9) :: (weyldim.descRun 5 (h + 2) ++ [3, 2]))
      = (h + 3) * ((h + 4) * ((h + 6) * (h + 7)))
        * weyldim.gapProd (places.unitDisp (h + 5)) := by
  have hX : weyldim.gapHead (h + 9) (weyldim.descRun 5 (h + 2)) * 2
      = ground.factorial (h + 4) := weyldim.gapHead_descRun 5 (h + 2) 2
  have hB : weyldim.gapHead (h + 9) [3, 2] = (h + 6) * (h + 7) := by
    show (h + 9 - 3) * ((h + 9 - 2) * 1) = (h + 6) * (h + 7)
    rw [Nat.mul_one]
    rfl
  have hY : weyldim.gapRun [3, 2] 5 (h + 2) * 2
      = ground.factorial (h + 3) * ground.factorial (h + 4) :=
    gapRunPair (h + 2)
  have hf4 : ground.factorial (h + 4)
      = (h + 4) * ground.factorial (h + 3) := rfl
  have hf3 : ground.factorial (h + 3)
      = (h + 3) * ground.factorial (h + 2) := rfl
  rw [weyldim.gapProd_cons, weyldim.gapHead_append,
    weyldim.gapProd_descRun_app [3, 2] 5 (h + 2),
    weyldim.gapProd_descRun 5 1 (h + 2), hB, unitNF2 h]
  show 4 * (weyldim.gapHead (h + 9) (weyldim.descRun 5 (h + 2))
      * ((h + 6) * (h + 7))
      * (weyldim.gapProd (weyldim.descRun 1 (h + 2))
        * (1 * weyldim.gapRun [3, 2] 5 (h + 2))))
    = (h + 3) * ((h + 4) * ((h + 6) * (h + 7)))
      * (ground.factorial (h + 4) * (ground.factorial (h + 3)
        * (ground.factorial (h + 2)
          * weyldim.gapProd (weyldim.descRun 1 (h + 2)))))
  rw [polyDual (h + 4) (h + 3) (h + 6) (h + 7),
    clear4q (weyldim.gapHead (h + 9) (weyldim.descRun 5 (h + 2)))
      (weyldim.gapRun [3, 2] 5 (h + 2)) ((h + 6) * (h + 7))
      (weyldim.gapProd (weyldim.descRun 1 (h + 2))), hX, hY, hf4, hf3]
  repeat rw [ground.mulAssoc]
  exact arithDualA (h + 4) (h + 3) (ground.factorial (h + 2)) (h + 6) (h + 7)
    (weyldim.gapProd (weyldim.descRun 1 (h + 2)))

/-- The four's clearing at a row with two leading entries. -/
private theorem clear4b (X Z p q W G : Nat) :
    4 * (1 * (X * p) * (W * q * (G * (1 * Z))))
      = q * (p * (X * 2 * (Z * 2 * (W * G)))) := by
  rw [Nat.one_mul (X * p), Nat.one_mul Z]
  show 2 * 2 * (X * p * (W * q * (G * Z)))
    = q * (p * (X * 2 * (Z * 2 * (W * G))))
  repeat rw [ground.mulAssoc]
  rw [mulLeftComm W q (G * Z), mulLeftComm p q (W * (G * Z)),
    mulLeftComm X q (p * (W * (G * Z))),
    mulLeftComm 2 q (X * (p * (W * (G * Z)))),
    mulLeftComm 2 q (2 * (X * (p * (W * (G * Z))))),
    mulLeftComm X p (W * (G * Z)), mulLeftComm 2 p (X * (W * (G * Z))),
    mulLeftComm 2 p (2 * (X * (W * (G * Z)))),
    mulLeftComm 2 X (W * (G * Z)), mulLeftComm 2 X (2 * (W * (G * Z))),
    Nat.mul_comm G Z, mulLeftComm W Z G, mulLeftComm 2 Z (W * G)]

/-- The dual pair's second member: its product shuffle. -/
private theorem arithDualB (b c F q p G : Nat) :
    q * (p * (b * (c * (F * (b * (c * (F * (c * (F * G)))))))))
      = q * (p * (c * (b * (b * (c * (F * (c * (F * (F * G))))))))) := by
  rw [mulLeftComm b c (F * (b * (c * (F * (c * (F * G)))))),
    mulLeftComm F b (c * (F * (c * (F * G)))),
    mulLeftComm F c (F * (c * (F * G))), mulLeftComm F c (F * G)]

/-- The dual pair's second member: its cleared gap product. -/
private theorem gapRowDualB (h : Nat) :
    4 * weyldim.gapProd ((h + 8) :: (h + 7)
        :: (weyldim.descRun 4 (h + 2) ++ [1]))
      = (h + 3) * ((h + 4) * ((h + 6) * (h + 7)))
        * weyldim.gapProd (places.unitDisp (h + 5)) := by
  have hone : h + 8 - (h + 7) = 1 := ground.addSubSelfL (h + 7) 1
  have hX : weyldim.gapHead (h + 8) (weyldim.descRun 4 (h + 2)) * 2
      = ground.factorial (h + 4) := weyldim.gapHead_descRun 4 (h + 2) 2
  have hW : weyldim.gapHead (h + 7) (weyldim.descRun 4 (h + 2))
      = ground.factorial (h + 3) := by
    have h1 : weyldim.gapHead (h + 7) (weyldim.descRun 4 (h + 2)) * 1
        = ground.factorial (h + 3) := weyldim.gapHead_descRun 4 (h + 2) 1
    rw [Nat.mul_one] at h1
    exact h1
  have hB8 : weyldim.gapHead (h + 8) [1] = h + 7 := by
    show (h + 8 - 1) * 1 = h + 7
    rw [Nat.mul_one]
    rfl
  have hB7 : weyldim.gapHead (h + 7) [1] = h + 6 := by
    show (h + 7 - 1) * 1 = h + 6
    rw [Nat.mul_one]
    rfl
  have hZ : weyldim.gapRun [1] 4 (h + 2) * 2 = ground.factorial (h + 4) :=
    gapRunOne (h + 2)
  have hf4 : ground.factorial (h + 4)
      = (h + 4) * ground.factorial (h + 3) := rfl
  have hf3 : ground.factorial (h + 3)
      = (h + 3) * ground.factorial (h + 2) := rfl
  rw [weyldim.gapProd_cons (h + 8), weyldim.gapProd_cons (h + 7),
    weyldim.gapHead_cons (h + 8) (h + 7),
    weyldim.gapProd_descRun_app [1] 4 (h + 2),
    weyldim.gapProd_descRun 4 1 (h + 2),
    weyldim.gapHead_append (h + 7) (weyldim.descRun 4 (h + 2)) [1],
    weyldim.gapHead_append (h + 8) (weyldim.descRun 4 (h + 2)) [1],
    hB7, hB8, hW, hone, unitNF2 h,
    polyDual (h + 4) (h + 3) (h + 6) (h + 7)]
  show 4 * (1 * (weyldim.gapHead (h + 8) (weyldim.descRun 4 (h + 2))
        * (h + 7))
      * (ground.factorial (h + 3) * (h + 6)
        * (weyldim.gapProd (weyldim.descRun 1 (h + 2))
          * (1 * weyldim.gapRun [1] 4 (h + 2)))))
    = (h + 6) * ((h + 7) * ((h + 3) * (h + 4)))
      * (ground.factorial (h + 4) * (ground.factorial (h + 3)
        * (ground.factorial (h + 2)
          * weyldim.gapProd (weyldim.descRun 1 (h + 2)))))
  rw [clear4b (weyldim.gapHead (h + 8) (weyldim.descRun 4 (h + 2)))
      (weyldim.gapRun [1] 4 (h + 2)) (h + 7) (h + 6)
      (ground.factorial (h + 3))
      (weyldim.gapProd (weyldim.descRun 1 (h + 2))), hX, hZ, hf4, hf3]
  repeat rw [ground.mulAssoc]
  exact arithDualB (h + 4) (h + 3) (ground.factorial (h + 2)) (h + 6) (h + 7)
    (weyldim.gapProd (weyldim.descRun 1 (h + 2)))

/-- The `ω₂ + ω₂*` row's product shuffle. -/
private theorem arithOmega (v a u P w Q G : Nat) :
    v * (a * (a * (u * (P * (w * (Q * (P * (w * (Q * G))))))))) 
      = a * (a * (u * (w * (v * (P * (P * (w * (Q * (Q * G))))))))) := by
  rw [mulLeftComm v a (a * (u * (P * (w * (Q * (P * (w * (Q * G)))))))),
    mulLeftComm v a (u * (P * (w * (Q * (P * (w * (Q * G))))))),
    mulLeftComm v u (P * (w * (Q * (P * (w * (Q * G)))))),
    mulLeftComm P w (Q * (P * (w * (Q * G)))),
    mulLeftComm v w (P * (Q * (P * (w * (Q * G))))),
    mulLeftComm Q P (w * (Q * G)), mulLeftComm Q w (Q * G)]

/-- The `ω₂ + ω₂*` row's cleared gap product. -/
private theorem gapRowOmega (h : Nat) :
    4 * weyldim.gapProd ((h + 8) :: (h + 7)
        :: (weyldim.descRun 5 (h + 1) ++ [3, 2]))
      = (h + 5) * (h + 5) * ((h + 6) * (h + 2))
        * weyldim.gapProd (places.unitDisp (h + 5)) := by
  have hone : h + 8 - (h + 7) = 1 := ground.addSubSelfL (h + 7) 1
  have hX : weyldim.gapHead (h + 8) (weyldim.descRun 5 (h + 1)) * 2
      = ground.factorial (h + 3) := weyldim.gapHead_descRun 5 (h + 1) 2
  have hW : weyldim.gapHead (h + 7) (weyldim.descRun 5 (h + 1))
      = ground.factorial (h + 2) := by
    have h1 : weyldim.gapHead (h + 7) (weyldim.descRun 5 (h + 1)) * 1
        = ground.factorial (h + 2) := weyldim.gapHead_descRun 5 (h + 1) 1
    rw [Nat.mul_one] at h1
    exact h1
  have hB8 : weyldim.gapHead (h + 8) [3, 2] = (h + 5) * (h + 6) := by
    show (h + 8 - 3) * ((h + 8 - 2) * 1) = (h + 5) * (h + 6)
    rw [Nat.mul_one]
    rfl
  have hB7 : weyldim.gapHead (h + 7) [3, 2] = (h + 4) * (h + 5) := by
    show (h + 7 - 3) * ((h + 7 - 2) * 1) = (h + 4) * (h + 5)
    rw [Nat.mul_one]
    rfl
  have hZ : weyldim.gapRun [3, 2] 5 (h + 1) * 2
      = ground.factorial (h + 2) * ground.factorial (h + 3) :=
    gapRunPair (h + 1)
  have hf4 : ground.factorial (h + 4)
      = (h + 4) * ground.factorial (h + 3) := rfl
  have hf2 : ground.factorial (h + 2)
      = (h + 2) * ground.factorial (h + 1) := rfl
  rw [weyldim.gapProd_cons (h + 8), weyldim.gapProd_cons (h + 7),
    weyldim.gapHead_cons (h + 8) (h + 7),
    weyldim.gapProd_descRun_app [3, 2] 5 (h + 1),
    weyldim.gapProd_descRun 5 1 (h + 1),
    weyldim.gapHead_append (h + 7) (weyldim.descRun 5 (h + 1)) [3, 2],
    weyldim.gapHead_append (h + 8) (weyldim.descRun 5 (h + 1)) [3, 2],
    hB7, hB8, hW, hone, unitNF1 h]
  show 4 * (1 * (weyldim.gapHead (h + 8) (weyldim.descRun 5 (h + 1))
        * ((h + 5) * (h + 6)))
      * (ground.factorial (h + 2) * ((h + 4) * (h + 5))
        * (weyldim.gapProd (weyldim.descRun 1 (h + 1))
          * (1 * weyldim.gapRun [3, 2] 5 (h + 1)))))
    = (h + 5) * (h + 5) * ((h + 6) * (h + 2))
      * (ground.factorial (h + 4) * (ground.factorial (h + 3)
        * (ground.factorial (h + 2) * (ground.factorial (h + 1)
          * weyldim.gapProd (weyldim.descRun 1 (h + 1))))))
  rw [clear4b (weyldim.gapHead (h + 8) (weyldim.descRun 5 (h + 1)))
      (weyldim.gapRun [3, 2] 5 (h + 1)) ((h + 5) * (h + 6))
      ((h + 4) * (h + 5)) (ground.factorial (h + 2))
      (weyldim.gapProd (weyldim.descRun 1 (h + 1))), hX, hZ, hf4, hf2]
  repeat rw [ground.mulAssoc]
  exact arithOmega (h + 4) (h + 5) (h + 6) (ground.factorial (h + 3)) (h + 2)
    (ground.factorial (h + 1))
    (weyldim.gapProd (weyldim.descRun 1 (h + 1)))

/-- The unit channel's cleared dimension. -/
private theorem dimUnit (h : Nat) :
    4 * weyldim.dimOf (rowUnit (h + 5)) = 4 := by
  refine dimClear _ (h + 5) 4 4 (lenRowUnit h) ?_
  rw [dispUnit h]
  exact gapRowUnit h

/-- The `θ` row's cleared dimension. -/
private theorem dimTheta (h : Nat) :
    4 * weyldim.dimOf (rowTheta (h + 5)) = 4 * ((h + 5) * (h + 5) - 1) := by
  refine dimClear _ (h + 5) 4 (4 * ((h + 5) * (h + 5) - 1))
    (lenRowTheta h) ?_
  rw [dispTheta h]
  exact gapRowTheta h

/-- The `2θ` row's cleared dimension. -/
private theorem dimTwoTheta (h : Nat) :
    4 * weyldim.dimOf (rowTwoTheta (h + 5)) = (h + 5) * (h + 5) * ((h + 4) * (h + 8)) := by
  refine dimClear _ (h + 5) 4 ((h + 5) * (h + 5) * ((h + 4) * (h + 8)))
    (lenRowTwoTheta h) ?_
  rw [dispTwoTheta h]
  exact gapRowTwoTheta h

/-- The dual pair's first member: its cleared dimension. -/
private theorem dimDualA (h : Nat) :
    4 * weyldim.dimOf (rowDualA (h + 5)) = (h + 3) * ((h + 4) * ((h + 6) * (h + 7))) := by
  refine dimClear _ (h + 5) 4 ((h + 3) * ((h + 4) * ((h + 6) * (h + 7))))
    (lenRowDualA h) ?_
  rw [dispDualA h]
  exact gapRowDualA h

/-- The dual pair's second member: its cleared dimension. -/
private theorem dimDualB (h : Nat) :
    4 * weyldim.dimOf (rowDualB (h + 5)) = (h + 3) * ((h + 4) * ((h + 6) * (h + 7))) := by
  refine dimClear _ (h + 5) 4 ((h + 3) * ((h + 4) * ((h + 6) * (h + 7))))
    (lenRowDualB h) ?_
  rw [dispDualB h]
  exact gapRowDualB h

/-- The `ω₂ + ω₂*` row's cleared dimension. -/
private theorem dimOmega (h : Nat) :
    4 * weyldim.dimOf (rowOmega (h + 5)) = (h + 5) * (h + 5) * ((h + 6) * (h + 2)) := by
  refine dimClear _ (h + 5) 4 ((h + 5) * (h + 5) * ((h + 6) * (h + 2)))
    (lenRowOmega h) ?_
  rw [dispOmega h]
  exact gapRowOmega h

/-- The six rows' cleared dimension column at every residue,
`cor:weyldim`'s telescopes at the stored shapes: the unit line, the
adjoint's `d_f² − 1`, `2θ` at `[(r+1)² r (r+4) : 4]`, the dual pair at
`[g r (r+2)(r+3) : 4]` over `g + 1 = r`, and `ω₂ + ω₂*` at
`[(r+1)² (r+2) w : 4]` over `w + 2 = r`, each entry cleared at the
one factor four. -/
theorem rows_dim : ∀ d : Nat, 2 ≤ d →
    (rows d).map (fun p => 4 * weyldim.dimOf p.1)
      = [4, 4 * (d * d - 1), d * d * ((d - 1) * (d + 3))]
        ++ (if 3 ≤ d then
            [(d - 2) * ((d - 1) * ((d + 1) * (d + 2))),
             (d - 2) * ((d - 1) * ((d + 1) * (d + 2)))] else [])
        ++ (if 4 ≤ d then [d * d * ((d + 1) * (d - 3))] else []) := by
  intro d hd
  have hg := Nat.le.dest hd
  match hg with
  | ⟨g, hgd⟩ =>
    have hdg : d = g + 2 := by rw [← hgd, Nat.add_comm 2 g]
    rw [hdg]
    match g with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | h + 3 =>
      show [4 * weyldim.dimOf (rowUnit (h + 5)),
            4 * weyldim.dimOf (rowTheta (h + 5)),
            4 * weyldim.dimOf (rowTwoTheta (h + 5)),
            4 * weyldim.dimOf (rowDualA (h + 5)),
            4 * weyldim.dimOf (rowDualB (h + 5)),
            4 * weyldim.dimOf (rowOmega (h + 5))]
        = [4, 4 * ((h + 5) * (h + 5) - 1),
           (h + 5) * (h + 5) * ((h + 4) * (h + 8)),
           (h + 3) * ((h + 4) * ((h + 6) * (h + 7))),
           (h + 3) * ((h + 4) * ((h + 6) * (h + 7))),
           (h + 5) * (h + 5) * ((h + 6) * (h + 2))]
      rw [dimUnit h, dimTheta h, dimTwoTheta h, dimDualA h, dimDualB h,
        dimOmega h]

/-- The crossed pair's expansion at a shifted head. -/
private theorem lin2 (a b h : Nat) :
    (h + a) * (h + b) = h * h + (a + b) * h + a * b := by
  rw [← ground.crossMul h a b, Nat.left_distrib h (h + a) b,
    Nat.left_distrib h h a, ground.mulAddR a b h, Nat.mul_comm h a,
    Nat.mul_comm h b, ← Nat.add_assoc (h * h) (a * h) (b * h)]

/-- The dual pair's gap witness against the residue's own crossed
pair. -/
private theorem gapW (h : Nat) :
    (h + 3) * (h + 7) + 3 = (h + 4) * (h + 6) := by
  rw [lin2 3 7 h, lin2 4 6 h]

/-- The self-dual outer rows' crossed pairs join the doubled
residue. -/
private theorem gapAB (h : Nat) :
    (h + 4) * (h + 8) + (h + 6) * (h + 2) + 4
      = 2 * ((h + 4) * (h + 6)) := by
  have hA : (h + 4) * (h + 8) = (h + 4) * (h + 6) + 2 * (h + 4) := by
    show (h + 4) * ((h + 6) + 2) = (h + 4) * (h + 6) + 2 * (h + 4)
    rw [Nat.left_distrib (h + 4) (h + 6) 2, Nat.mul_comm (h + 4) 2]
  have hB : (h + 4) * (h + 6) = (h + 6) * (h + 2) + 2 * (h + 6) := by
    rw [Nat.mul_comm (h + 4) (h + 6)]
    show (h + 6) * ((h + 2) + 2) = (h + 6) * (h + 2) + 2 * (h + 6)
    rw [Nat.left_distrib (h + 6) (h + 2) 2, Nat.mul_comm (h + 6) 2]
  have hcore : 2 * (h + 4) + ((h + 6) * (h + 2) + 4)
      = (h + 4) * (h + 6) := by
    rw [hB, Nat.add_left_comm (2 * (h + 4)) ((h + 6) * (h + 2)) 4,
      show 2 * (h + 4) + 4 = 2 * (h + 6) from by
        show 2 * (h + 4) + 4 = 2 * ((h + 4) + 2)
        rw [Nat.left_distrib 2 (h + 4) 2]]
  rw [hA]
  repeat rw [Nat.add_assoc]
  rw [hcore, Nat.two_mul ((h + 4) * (h + 6))]

/-- The dual pair's dimension collects at the residue's crossed
pair. -/
private theorem pcollect (b c u r : Nat) :
    c * (b * (u * r)) = c * r * (b * u) := by
  rw [ground.mulAssoc c r (b * u), Nat.mul_comm u r, mulLeftComm b r u]

/-- The six rows' fold at the cleared column. -/
private theorem sixClear (a b c e f g : Nat) :
    4 * (0 + 1 * a + 2 * b + 1 * c + 1 * e + 1 * f + 1 * g)
      = 4 * a + 2 * (4 * b) + 4 * c + 4 * e + 4 * f + 4 * g := by
  repeat rw [Nat.left_distrib]
  rw [Nat.mul_zero 4, Nat.zero_add, Nat.one_mul a, Nat.one_mul c,
    Nat.one_mul e, Nat.one_mul f, Nat.one_mul g, mulLeftComm 4 2 b]

/-- The first closure identity's collected read: the unit line, the
adjoint's doubled count, the self-dual outer rows at the residue's
crossed pair and the dual pair at its gap witness. -/
private theorem closeDim (V A B W : Nat) (hAB : A + B + 4 = 2 * V)
    (hW : W + 3 = V) :
    4 + 2 * (4 * V) + (V + 1) * A + W * V + W * V + (V + 1) * B
      = 4 * (V * V) := by
  refine ground.addCancelR ((V + 1) * 4 + V * 6) ?_
  have e1 : (V + 1) * A + ((V + 1) * B + ((V + 1) * 4
      + (W * V + (W * V + V * 6)))) = (V + 1) * (2 * V)
        + (W * V + (W * V + V * 6)) := by
    rw [← Nat.add_assoc ((V + 1) * A) ((V + 1) * B),
      ← Nat.add_assoc ((V + 1) * A + (V + 1) * B) ((V + 1) * 4),
      ← Nat.left_distrib (V + 1) A B,
      ← Nat.left_distrib (V + 1) (A + B) 4, hAB]
  have e2 : W * V + (W * V + V * 6) = 2 * (V * V) := by
    rw [← Nat.add_assoc, ← ground.mulAddR W W V, Nat.mul_comm V 6,
      ← ground.mulAddR (W + W) 6 V,
      show W + W + 6 = (W + 3) + (W + 3) from by
        repeat rw [Nat.add_assoc]
        rw [Nat.add_left_comm 3 W 3],
      hW, ← Nat.two_mul V, ground.mulAssoc 2 V V]
  repeat rw [Nat.add_assoc]
  rw [Nat.add_left_comm (W * V) ((V + 1) * B) ((V + 1) * 4 + V * 6),
    Nat.add_left_comm (W * V) ((V + 1) * B) (W * V + ((V + 1) * 4 + V * 6)),
    Nat.add_left_comm (W * V) ((V + 1) * 4) (V * 6),
    Nat.add_left_comm (W * V) ((V + 1) * 4) (W * V + V * 6), e1, e2]
  rw [← ground.mulAssoc 2 4 V, ground.mulAddR V 1 (2 * V),
    Nat.one_mul (2 * V), mulLeftComm V 2 V, ground.mulAddR V 1 4,
    Nat.one_mul 4, Nat.mul_comm V 4, Nat.mul_comm V 6]
  repeat rw [Nat.add_assoc]
  rw [← Nat.add_assoc (2 * (V * V)) (2 * V) (2 * (V * V)),
    Nat.add_comm (2 * (V * V) + 2 * V) (2 * (V * V)),
    ← Nat.add_assoc (2 * (V * V)) (2 * (V * V)) (2 * V),
    ← ground.mulAddR 2 2 (V * V),
    Nat.add_left_comm (2 * 4 * V) ((2 + 2) * (V * V)) (2 * V),
    ← ground.mulAddR (2 * 4) 2 V,
    Nat.add_left_comm (4 * V) 4 (6 * V), ← ground.mulAddR 4 6 V,
    Nat.add_left_comm 4 ((2 + 2) * (V * V)) ((2 * 4 + 2) * V)]

/-- The first closure identity at every residue,
`Σ m d = r² (r+2)²`: the fold over the six rows' closed forms. -/
theorem dimClosureAll : ∀ d : Nat, 2 ≤ d → dimClosure d := by
  intro d hd
  have hg := Nat.le.dest hd
  match hg with
  | ⟨g, hgd⟩ =>
    have hdg : d = g + 2 := by rw [← hgd, Nat.add_comm 2 g]
    rw [hdg]
    match g with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | h + 3 =>
      have hsq5 : (h + 5) * (h + 5) = (h + 4) * (h + 6) + 1 := ground.sqJoin (h + 4)
      show (rows (h + 5)).foldl
          (fun acc r => acc + r.2 * weyldim.dimOf r.1) 0
        = ((h + 5) * (h + 5) - 1) * ((h + 5) * (h + 5) - 1)
      refine Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 3) ?_
      show 4 * (0
          + 1 * weyldim.dimOf (rowUnit (h + 5))
          + 2 * weyldim.dimOf (rowTheta (h + 5))
          + 1 * weyldim.dimOf (rowTwoTheta (h + 5))
          + 1 * weyldim.dimOf (rowDualA (h + 5))
          + 1 * weyldim.dimOf (rowDualB (h + 5))
          + 1 * weyldim.dimOf (rowOmega (h + 5)))
        = 4 * (((h + 5) * (h + 5) - 1) * ((h + 5) * (h + 5) - 1))
      rw [sixClear, dimUnit h, dimTheta h, dimTwoTheta h, dimDualA h,
        dimDualB h, dimOmega h, adjSq h, hsq5,
        pcollect (h + 4) (h + 3) (h + 6) (h + 7)]
      exact closeDim ((h + 4) * (h + 6)) ((h + 4) * (h + 8))
        ((h + 6) * (h + 2)) ((h + 3) * (h + 7)) (gapAB h) (gapW h)

/-- The `2θ` row's Casimir entry at the residue's crossed pair. -/
private theorem casQ3 (h : Nat) :
    2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 7))
      = 4 * ((h + 5) * (h + 6)) := by
  rw [← Nat.left_distrib 2 ((h + 5) * (h + 5)) ((h + 5) * (h + 7)),
    ← Nat.left_distrib (h + 5) (h + 5) (h + 7),
    show h + 5 + (h + 7) = 2 * (h + 6) from by
      rw [Nat.two_mul (h + 6), Nat.add_add_add_comm h 5 h 7,
        Nat.add_add_add_comm h 6 h 6],
    mulLeftComm (h + 5) 2 (h + 6), ← ground.mulAssoc 2 2 ((h + 5) * (h + 6))]

/-- The `ω₂ + ω₂*` row's Casimir entry at the residue's crossed
pair. -/
private theorem casQ6 (h : Nat) :
    2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 3))
      = 4 * ((h + 5) * (h + 4)) := by
  rw [← Nat.left_distrib 2 ((h + 5) * (h + 5)) ((h + 5) * (h + 3)),
    ← Nat.left_distrib (h + 5) (h + 5) (h + 3),
    show h + 5 + (h + 3) = 2 * (h + 4) from by
      rw [Nat.two_mul (h + 4), Nat.add_add_add_comm h 5 h 3,
        Nat.add_add_add_comm h 4 h 4],
    mulLeftComm (h + 5) 2 (h + 4), ← ground.mulAssoc 2 2 ((h + 5) * (h + 4))]

/-- The six rows' Casimir-weighted fold at the cleared column. -/
private theorem sixClearQ (a b c e f g qa qb qc qe qf qg : Nat) :
    4 * (0 + 1 * a * qa + 2 * b * qb + 1 * c * qc + 1 * e * qe
        + 1 * f * qf + 1 * g * qg)
      = 4 * a * qa + 2 * (4 * b * qb) + 4 * c * qc + 4 * e * qe
        + 4 * f * qf + 4 * g * qg := by
  repeat rw [Nat.left_distrib]
  rw [Nat.mul_zero 4, Nat.zero_add, Nat.one_mul a, Nat.one_mul c,
    Nat.one_mul e, Nat.one_mul f, Nat.one_mul g]
  repeat rw [← ground.mulAssoc]

/-- The `2θ` row's Casimir collection at the residue's crossed
pair. -/
private theorem casP3 (Z b u a x : Nat) :
    Z * (b * a) * (4 * (x * u)) = 4 * (a * (Z * (b * u * x))) := by
  repeat rw [ground.mulAssoc]
  rw [mulLeftComm a 4 (x * u), mulLeftComm b 4 (a * (x * u)),
    mulLeftComm Z 4 (b * (a * (x * u))), mulLeftComm b a (x * u),
    mulLeftComm Z a (b * (x * u)), Nat.mul_comm x u]

/-- The `ω₂ + ω₂*` row's Casimir collection at the residue's
crossed pair. -/
private theorem casP6 (Z u c a x : Nat) :
    Z * (u * c) * (4 * (x * a)) = 4 * (c * (Z * (a * u * x))) := by
  repeat rw [ground.mulAssoc]
  rw [mulLeftComm c 4 (x * a), mulLeftComm u 4 (c * (x * a)),
    mulLeftComm Z 4 (u * (c * (x * a))), mulLeftComm u c (x * a),
    mulLeftComm Z c (u * (x * a)), Nat.mul_comm x a,
    mulLeftComm u a x]

/-- The self-dual outer rows' weights join at the doubled
residue. -/
private theorem pairSum (p q C x : Nat) (hs : p + q = 2 * x) :
    4 * (p * C) + 4 * (q * C) = 8 * (x * C) := by
  rw [← Nat.left_distrib 4 (p * C) (q * C), ← ground.mulAddR p q C, hs,
    ground.mulAssoc 2 x C, ← ground.mulAssoc 4 2 (x * C)]

/-- The self-dual outer rows' weight tie. -/
private theorem gapTie (h : Nat) : h + 8 + (h + 2) = 2 * (h + 5) := by
  rw [Nat.two_mul (h + 5), Nat.add_add_add_comm h 8 h 2,
    Nat.add_add_add_comm h 5 h 5]

/-- The second closure identity's collected read: the adjoint's
doubled count, the self-dual outer rows at their common factor and
the dual pair's weighted read twice its count. -/
private theorem closeCas (V W Z : Nat) (hZ : V + 1 = Z) (hW : W + 3 = V) :
    4 * 0 + (2 * (4 * V * (2 * Z)) + (W * V * (4 * Z)
      + (W * V * (4 * Z) + 8 * (Z * (V * Z)))))
      = 4 * (4 * Z * (V * V)) := by
  have key : 2 + (W + Z) = 2 * V := by
    rw [← hZ, ← hW, Nat.left_distrib 2 W 3, ← Nat.add_assoc W W 4,
      ← Nat.two_mul W, Nat.add_left_comm 2 (2 * W) 4]
  have t1 : 2 * (4 * V * (2 * Z)) = 8 * (V * Z) * 2 := by
    rw [ground.mulAssoc 4 V (2 * Z), mulLeftComm V 2 Z,
      ← ground.mulAssoc 4 2 (V * Z), Nat.mul_comm 2 (4 * 2 * (V * Z))]
  have t2 : W * V * (4 * Z) = 4 * (W * (V * Z)) := by
    rw [ground.mulAssoc W V (4 * Z), mulLeftComm V 4 Z,
      mulLeftComm W 4 (V * Z)]
  rw [Nat.mul_zero 4, Nat.zero_add, t1, t2,
    ← Nat.add_assoc (4 * (W * (V * Z))) (4 * (W * (V * Z)))
      (8 * (Z * (V * Z))),
    ← ground.mulAddR 4 4 (W * (V * Z)),
    Nat.mul_comm W (V * Z), ← ground.mulAssoc (4 + 4) (V * Z) W,
    Nat.mul_comm Z (V * Z), ← ground.mulAssoc 8 (V * Z) Z,
    ← Nat.left_distrib ((4 + 4) * (V * Z)) W Z]
  show 8 * (V * Z) * 2 + 8 * (V * Z) * (W + Z) = 4 * (4 * Z * (V * V))
  rw [← Nat.left_distrib (8 * (V * Z)) 2 (W + Z), key,
    ground.mulAssoc 8 (V * Z) (2 * V), ground.mulAssoc V Z (2 * V),
    mulLeftComm Z 2 V, mulLeftComm V 2 (Z * V),
    ← ground.mulAssoc 8 2 (V * (Z * V)),
    ground.mulAssoc 4 Z (V * V), ← ground.mulAssoc 4 4 (Z * (V * V)),
    mulLeftComm V Z V]

/-- The second closure identity at every residue,
`Σ m d ĉ₂ = 2 r² (r+2)²` at the cleared column. -/
theorem casClosureAll : ∀ d : Nat, 2 ≤ d → casClosure d := by
  intro d hd
  have hg := Nat.le.dest hd
  match hg with
  | ⟨g, hgd⟩ =>
    have hdg : d = g + 2 := by rw [← hgd, Nat.add_comm 2 g]
    rw [hdg]
    match g with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | h + 3 =>
      have hsq5 : (h + 5) * (h + 5) = (h + 4) * (h + 6) + 1 := ground.sqJoin (h + 4)
      have q3 : c2hat.dfQ (rowTwoTheta (h + 5))
          = 2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 7)) := row3 h
      have q6 : c2hat.dfQ (rowOmega (h + 5))
          = 2 * ((h + 5) * (h + 5)) + 2 * ((h + 5) * (h + 3)) := row6 h
      show (rows (h + 5)).foldl
          (fun acc r => acc + r.2 * weyldim.dimOf r.1 * c2hat.dfQ r.1) 0
        = 4 * ((h + 5) * (h + 5))
          * (((h + 5) * (h + 5) - 1) * ((h + 5) * (h + 5) - 1))
      refine Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 3) ?_
      show 4 * (0
          + 1 * weyldim.dimOf (rowUnit (h + 5))
            * c2hat.dfQ (rowUnit (h + 5))
          + 2 * weyldim.dimOf (rowTheta (h + 5))
            * c2hat.dfQ (rowTheta (h + 5))
          + 1 * weyldim.dimOf (rowTwoTheta (h + 5))
            * c2hat.dfQ (rowTwoTheta (h + 5))
          + 1 * weyldim.dimOf (rowDualA (h + 5))
            * c2hat.dfQ (rowDualA (h + 5))
          + 1 * weyldim.dimOf (rowDualB (h + 5))
            * c2hat.dfQ (rowDualB (h + 5))
          + 1 * weyldim.dimOf (rowOmega (h + 5))
            * c2hat.dfQ (rowOmega (h + 5)))
        = 4 * (4 * ((h + 5) * (h + 5))
          * (((h + 5) * (h + 5) - 1) * ((h + 5) * (h + 5) - 1)))
      rw [sixClearQ, row1 (h + 5), row2 h, q3, row4 h, row5 h, q6,
        dimUnit h, dimTheta h, dimTwoTheta h, dimDualA h, dimDualB h,
        dimOmega h, casQ3 h, casQ6 h, adjSq h, hsq5,
        pcollect (h + 4) (h + 3) (h + 6) (h + 7),
        casP3 ((h + 4) * (h + 6) + 1) (h + 4) (h + 6) (h + 8) (h + 5),
        casP6 ((h + 4) * (h + 6) + 1) (h + 6) (h + 2) (h + 4) (h + 5)]
      repeat rw [Nat.add_assoc]
      rw [Nat.add_left_comm
          (4 * ((h + 8) * (((h + 4) * (h + 6) + 1)
            * ((h + 4) * (h + 6) * (h + 5)))))
          ((h + 3) * (h + 7) * ((h + 4) * (h + 6))
            * (4 * ((h + 4) * (h + 6) + 1)))
          ((h + 3) * (h + 7) * ((h + 4) * (h + 6))
            * (4 * ((h + 4) * (h + 6) + 1))
            + 4 * ((h + 2) * (((h + 4) * (h + 6) + 1)
              * ((h + 4) * (h + 6) * (h + 5))))),
        Nat.add_left_comm
          (4 * ((h + 8) * (((h + 4) * (h + 6) + 1)
            * ((h + 4) * (h + 6) * (h + 5)))))
          ((h + 3) * (h + 7) * ((h + 4) * (h + 6))
            * (4 * ((h + 4) * (h + 6) + 1)))
          (4 * ((h + 2) * (((h + 4) * (h + 6) + 1)
            * ((h + 4) * (h + 6) * (h + 5))))),
        pairSum (h + 8) (h + 2)
          (((h + 4) * (h + 6) + 1) * ((h + 4) * (h + 6) * (h + 5)))
          (h + 5) (gapTie h),
        mulLeftComm (h + 5) ((h + 4) * (h + 6) + 1)
          ((h + 4) * (h + 6) * (h + 5)),
        mulLeftComm (h + 5) ((h + 4) * (h + 6)) (h + 5), hsq5]
      exact closeCas ((h + 4) * (h + 6)) ((h + 3) * (h + 7))
        ((h + 4) * (h + 6) + 1) rfl (gapW h)

end channels
