import MassGap.Sertables
import MassGap.C2hat
import MassGap.Adjchar
import MassGap.Anchor
/-!
`lem:casfloor` — the member floors as computed reads off the tables:
an end content enters at its cleared fold, the display
`e μ = Σ_k b_k α_k` at a fold key `e` with the coroot identities
`Σ_k b_k α_k(α_j^∨) = e μ(α_j^∨)` the display's witness
(`corootRead`; the fixed members' folds the adjugate rows), and the
Casimir is the fold's form read at the halved products,
`2 lenDen e ⟨μ, μ+2ρ⟩ = Σ_k (b_k + e ϱ_k) μ(α_k^∨) lenNums_k` at the
root fold's key sums `ϱ` (`c2Num`, the display's second fold over the
positive list collected columnwise), read against
`C₂(θ) = 2 (r+1)` at the cleared second member (`c2Den`, the form and
residue reads', the θ entries' one value the batteries' own
coherence pin).  A displayed evaluation is the cross-multiplied read
`c2Read`, and the member's floor is the trichotomy fold's least over
its list (`floorRead`), the lists the statement's — the series' end
contents with `θ` at its own fold (`endsB`, `endsC`, `endsD`, the
dominant roots' reads joining the fold), and a fixed member's
fundamentals at the adjugate rows (`endsG2` … `endsE8`).  The
`A`-series reads at the shapes: the endpoint display
`d_f Q(ω_j) = j g_j (r+2)` at the complement gap is `endpointRead`,
proven general (`endpointAll`), with the fold route's coherence at
the shared instances the check module's crown pins.  The descent
lands at the shapes: the box move's fall identity at the crossed
display (`boxFall` — the join's read at the fixed degree, over
`def:c2hat`'s square identity and the row-weight fold's linear
join) with the strict fall (`fallStrict`), `θ`'s class read
`d_f Q(θ) = 2 d_f²` (`thetaRead`), and the general floor over
every nonunit label: a reduced occupied shape reads
`r (r+2) ≤ d_f Q(λ)` with equality at `f` and `f̄` alone
(`floorAll`, `floorSharp`), the walk a strong induction on the
fall's own measure — a one-column row list reads the endpoint
display, a head at two or beyond moves at the last row of length
two or more against one past the last occupied row, the
raised-last-key step re-enters through the lowered family, and the
unit exit reads `θ`'s value.  The member-table descents (the
series' coordinate moves, the fixed members' coroot moves) land
with `thm:memberchar`'s member consumers; a window's floor read is
its below-cutoff enumeration's own (`lem:freeend`'s
`belowFloor`).  The descent refines per class: the box move and
the full lowering both keep the degree's remainder at the
fundamental count, so a walk seeded off the unit class never exits
at the unit and ends at the unit family of its own class, every
reduced shape at the nonunit class `c` reading the endpoint
display `c (d_f − c) (r + 2) ≤ d_f Q(λ)` (`classFloor`).  At the
unit class itself the walk exits where the seeded walk cannot: an
occupied reduced shape whose degree reads the unit class reads
`2 d_f² ≤ d_f Q(λ)` (`unitClassFloor`), the unit-reaching step's
own value — a constant row list moved by one box, `θ`'s class, at
`d_f Q(θ) = 2 d_f²`.
-/

namespace casfloor
open ground gentable

/-- The root fold `2ρ = Σ_α α` at its simple coefficients, the
positive folds' columnwise sum. -/
def rhoFold (t : Table) : List Nat :=
  t.posFolds.foldl (fun acc f => List.zipWith (fun a b => a + b) acc f)
    (List.replicate t.rank 0)

set_option genInjectivity false in
/-- An end content's cleared-fold datum: the fold `b`, the fold key
`e`, and the coroot list `μ(α_j^∨)`, the display's data. -/
structure EndFold where
  fold : List Nat
  key : Nat
  coroot : List Nat

private def corootB (t : Table) (E : EndFold) : Bool :=
  (List.range t.rank).all (fun j =>
    decide ((corootAt t E.fold j).oneValue
      (BPair.ofNat (E.key * getAt 0 E.coroot j))))

/-- The cleared fold's witness: the coroot identities
`Σ_k b_k α_k(α_j^∨) = e μ(α_j^∨)` at every key. -/
def corootRead (t : Table) (E : EndFold) : Prop := corootB t E = true

instance (t : Table) (E : EndFold) : Decidable (corootRead t E) :=
  inferInstanceAs (Decidable (_ = _))

/-- A member list's witness read, one coroot witness per entry. -/
def endsRead (t : Table) (ends : List EndFold) : Prop :=
  (ends.all (corootB t)) = true

instance (t : Table) (ends : List EndFold) :
    Decidable (endsRead t ends) :=
  inferInstanceAs (Decidable (_ = _))

/-- The Casimir's cleared count at the fold, the form read's display:
`2 lenDen e ⟨μ, μ+2ρ⟩ = Σ_k (b_k + e ϱ_k) μ(α_k^∨) lenNums_k`. -/
def c2Num (t : Table) (E : EndFold) : Nat :=
  let rho := rhoFold t
  (List.range t.rank).foldl (fun acc k =>
    acc + (getAt 0 E.fold k + E.key * getAt 0 rho k)
      * getAt 0 E.coroot k * getAt 0 t.lenNums k) 0

/-- The count's second member, `2 lenDen e C₂(θ)` at
`C₂(θ) = 2 (r+1)`, the form and residue reads'. -/
def c2Den (t : Table) (E : EndFold) : Nat :=
  2 * t.lenDen * E.key * (2 * residue t + 2)

/-- A displayed evaluation's read: `ĉ₂(μ) = [p : q]`, the
cross-multiplied identity. -/
def c2Read (t : Table) (E : EndFold) (p q : Nat) : Prop :=
  q * c2Num t E = p * c2Den t E

instance (t : Table) (E : EndFold) (p q : Nat) :
    Decidable (c2Read t E p q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The member's floor at its list: the displayed pair at or below
every entry and attained, the trichotomy fold's least. -/
def floorRead (t : Table) (ends : List EndFold) (p q : Nat) : Prop :=
  (let vals := ends.map (fun E => (c2Num t E, c2Den t E))
   (vals.all (fun v => p * v.2 ≤ q * v.1))
     && (vals.any (fun v => p * v.2 == q * v.1))) = true

instance (t : Table) (ends : List EndFold) (p q : Nat) :
    Decidable (floorRead t ends p q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The `B` member's list at `ℓ = g + 2`: the vector at `b_k = 1`,
key one; the spinor at the index list, key two; and `θ` at its
own fold, key one, the first member's short-key coroot two. -/
def endsB (g : Nat) : List EndFold :=
  [⟨List.replicate (g + 2) 1, 1, unitAt (g + 2) 0⟩,
   ⟨(List.range (g + 2)).map (· + 1), 2, unitAt (g + 2) (g + 1)⟩,
   ⟨sertables.sumFoldB (g + 2) 0 1, 1,
    if g == 0 then [0, 2] else 0 :: 1 :: List.replicate g 0⟩]

/-- The `C` member's list at `ℓ = g + 3`: the first fundamental at
twos with one at the last key, key two; the short dominant root at
its own fold, key one; and `θ` at its own fold, key one. -/
def endsC (g : Nat) : List EndFold :=
  [⟨List.replicate (g + 2) 2 ++ [1], 2, unitAt (g + 3) 0⟩,
   ⟨sertables.sumFoldC (g + 3) 0 1, 1, unitAt (g + 3) 1⟩,
   ⟨sertables.longFold (g + 3) 0, 1, 2 :: List.replicate (g + 2) 0⟩]

/-- The `D` member's list at `ℓ = g + 4`: the vector at twos with
one on the last two keys, key two; the two spinors at the index list
with the exchanged tail pairs, key two at even rank and key four at
the doubled list at odd; and `θ` at its own fold, key one. -/
def endsD (g : Nat) : List EndFold :=
  [⟨List.replicate (g + 2) 2 ++ [1, 1], 2, unitAt (g + 4) 0⟩] ++
  (if (g + 4) % 2 == 0 then
    [⟨((List.range (g + 2)).map (· + 1)) ++ [(g + 4) / 2, (g + 2) / 2],
      2, unitAt (g + 4) (g + 2)⟩,
     ⟨((List.range (g + 2)).map (· + 1)) ++ [(g + 2) / 2, (g + 4) / 2],
      2, unitAt (g + 4) (g + 3)⟩]
   else
    [⟨((List.range (g + 2)).map (fun k => 2 * (k + 1))) ++ [g + 4, g + 2],
      4, unitAt (g + 4) (g + 2)⟩,
     ⟨((List.range (g + 2)).map (fun k => 2 * (k + 1))) ++ [g + 2, g + 4],
      4, unitAt (g + 4) (g + 3)⟩]) ++
  [⟨sertables.sumFoldD (g + 4) 0 1, 1, unitAt (g + 4) 1⟩]

/-- A fixed member's list: the fundamentals at the adjugate rows'
folds, one per key at the member's fold key. -/
def endsFixed (rows : List (List Nat)) (e : Nat) : List EndFold :=
  (List.range rows.length).map (fun i =>
    ⟨getAt [] rows i, e, unitAt rows.length i⟩)

def endsG2 : List EndFold := endsFixed sertables.adjG2 1
def endsF4 : List EndFold := endsFixed sertables.adjF4 1
def endsE6 : List EndFold := endsFixed sertables.adjE6 3
def endsE7 : List EndFold := endsFixed sertables.adjE7 2
def endsE8 : List EndFold := endsFixed sertables.adjE8 1

/-- The fundamental's shape at the `A`-series, one column at the
length `j`. -/
def fundShape (j g : Nat) : places.Shape :=
  (List.range (j + g)).map (fun k => if k + 1 == j then 1 else 0)

/-- The `A`-series' endpoint display,
`d_f Q(ω_j) = j g_j (r+2)` at the complement gap `j + g_j = d_f`. -/
def endpointRead (j g : Nat) : Prop :=
  c2hat.dfQ (fundShape j g) = j * g * (j + g + 1)

instance (j g : Nat) : Decidable (endpointRead j g) :=
  inferInstanceAs (Decidable (_ = _))

/-! The descent's row-level kit (`lem:casfloor`'s proof): the walk
runs at the row lists, every sorted list a row list, the shape
carrier re-entered at the public theorems. -/

/-- The successor's square against the doubled member. -/
private theorem sqUp (a : Nat) : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
  rw [mulAddR a 1 (a + 1), Nat.left_distrib a a 1, Nat.mul_one a,
    Nat.one_mul (a + 1), Nat.two_mul a, Nat.add_assoc (a * a) a (a + 1),
    Nat.add_assoc (a * a) (a + a) 1, Nat.add_assoc a a 1]

/-- The three-term regrouping at a moved unit. -/
private theorem sqShift (x y w : Nat) :
    x + y + 1 + w = x + w + y + 1 := by
  rw [Nat.add_assoc (x + y) 1 w, Nat.add_assoc x y (1 + w),
    Nat.add_comm 1 w, Nat.add_assoc (x + w) y 1, Nat.add_assoc x w (y + 1),
    Nat.add_left_comm w y 1]

/-- The cleared traceless read at a row list, `dfQ`'s carrier. -/
private def qRows (l : List Nat) : Nat :=
  c2hat.sqGaps l + l.length * c2hat.rho2 l

/-- The key-weighted total: each entry against its own key. -/
private def wSum : List Nat → Nat
  | [] => 0
  | _ :: t => ground.sumNat t + wSum t

/-- The count of leading entries at or above two. -/
private def big2 : List Nat → Nat
  | [] => 0
  | x :: t => if 2 ≤ x then big2 t + 1 else 0

/-- The count of leading occupied entries. -/
private def posLen : List Nat → Nat
  | [] => 0
  | x :: t => if 0 < x then posLen t + 1 else 0

/-- The four-term regrouping at the paired outer members. -/
private theorem swap4 (a b c d : Nat) :
    a + b + c + d = (a + d) + (b + c) := by
  rw [Nat.add_right_comm (a + b) c d, Nat.add_right_comm a b d,
    Nat.add_assoc]

/-- The edit moves the key-weighted total by the entry's move at
the key's weight. -/
private theorem wSum_editAt (f : Nat → Nat) :
    ∀ (k : Nat) (l : List Nat), k < l.length →
      wSum (ground.editAt f k l) + ground.getAt 0 l k * k
        = wSum l + f (ground.getAt 0 l k) * k
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, a :: t, _ => by
    show ground.sumNat t + wSum t + a * 0
      = ground.sumNat t + wSum t + f a * 0
    rw [Nat.mul_zero, Nat.mul_zero]
  | k + 1, a :: t, h => by
    show ground.sumNat (ground.editAt f k t) + wSum (ground.editAt f k t)
        + ground.getAt 0 t k * (k + 1)
      = ground.sumNat t + wSum t + f (ground.getAt 0 t k) * (k + 1)
    have hk : k < t.length := Nat.lt_of_succ_lt_succ h
    have hs := ground.sumNat_editAt f k t hk
    have hw := wSum_editAt f k t hk
    rw [Nat.mul_succ, Nat.mul_succ, ← Nat.add_assoc, ← Nat.add_assoc,
      swap4 (ground.sumNat (ground.editAt f k t))
        (wSum (ground.editAt f k t)) (ground.getAt 0 t k * k)
        (ground.getAt 0 t k),
      swap4 (ground.sumNat t) (wSum t) (f (ground.getAt 0 t k) * k)
        (f (ground.getAt 0 t k)),
      hs, Nat.add_comm (wSum (ground.editAt f k t)) (ground.getAt 0 t k * k),
      Nat.add_comm (ground.getAt 0 t k * k) (wSum (ground.editAt f k t)),
      hw]

/-- The bump raises the key-weighted total by its own key. -/
private theorem wSum_bumpAt : ∀ (k : Nat) (l : List Nat),
    k < l.length → wSum (ground.bumpAt k l) = wSum l + k
  := fun k l h => by
    refine ground.addCancelR (ground.getAt 0 l k * k) ?_
    refine (wSum_editAt (fun x => x + 1) k l h).trans ?_
    rw [Nat.succ_mul, Nat.add_assoc,
      Nat.add_comm (ground.getAt 0 l k * k) k, ← Nat.add_assoc]

/-- The drop lowers the key-weighted total by its own key. -/
private theorem wSum_dipAt : ∀ (k : Nat) (l : List Nat),
    0 < ground.getAt 0 l k → wSum (dipAt k l) + k = wSum l
  := fun k l h => by
    have hlen : k < l.length := by
      match Nat.lt_or_ge k l.length with
      | .inl hl => exact hl
      | .inr hge =>
        rw [ground.getAt_over 0 l k hge] at h
        exact absurd h (Nat.lt_irrefl 0)
    refine ground.addCancelR ((ground.getAt 0 l k - 1) * k) ?_
    have hgen := wSum_editAt (fun x => x - 1) k l hlen
    rw [Nat.add_right_comm (wSum (dipAt k l)) k
        ((ground.getAt 0 l k - 1) * k),
      Nat.add_assoc (wSum (dipAt k l)) ((ground.getAt 0 l k - 1) * k) k,
      show (ground.getAt 0 l k - 1) * k + k = ground.getAt 0 l k * k from by
        rw [← Nat.succ_mul]
        exact congrArg (fun z => z * k) (ground.subAdd h)]
    exact hgen

/-- The edit moves the squares' fold by the entry's square move. -/
private theorem sumSq_editAt (f : Nat → Nat) :
    ∀ (k : Nat) (l : List Nat), k < l.length →
      c2hat.sumSq (ground.editAt f k l)
          + ground.getAt 0 l k * ground.getAt 0 l k
        = c2hat.sumSq l
          + f (ground.getAt 0 l k) * f (ground.getAt 0 l k)
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, a :: t, _ => by
    show f a * f a + c2hat.sumSq t + a * a
      = a * a + c2hat.sumSq t + f a * f a
    exact ground.addSwapEnds (f a * f a) (c2hat.sumSq t) (a * a)
  | k + 1, a :: t, h => by
    show a * a + c2hat.sumSq (ground.editAt f k t)
        + ground.getAt 0 t k * ground.getAt 0 t k
      = a * a + c2hat.sumSq t
        + f (ground.getAt 0 t k) * f (ground.getAt 0 t k)
    rw [Nat.add_assoc (a * a) (c2hat.sumSq (ground.editAt f k t))
        (ground.getAt 0 t k * ground.getAt 0 t k),
      sumSq_editAt f k t (Nat.lt_of_succ_lt_succ h), Nat.add_assoc]

/-- The bump raises the squares' fold by the doubled entry and one. -/
private theorem sumSq_bumpAt : ∀ (k : Nat) (l : List Nat),
    k < l.length →
    c2hat.sumSq (ground.bumpAt k l)
      = c2hat.sumSq l + 2 * ground.getAt 0 l k + 1
  := fun k l h => by
    refine ground.addCancelR
      (ground.getAt 0 l k * ground.getAt 0 l k) ?_
    refine (sumSq_editAt (fun x => x + 1) k l h).trans ?_
    rw [sqUp (ground.getAt 0 l k),
      sqShift (c2hat.sumSq l) (2 * ground.getAt 0 l k)
        (ground.getAt 0 l k * ground.getAt 0 l k),
      ← Nat.add_assoc (c2hat.sumSq l)
        (ground.getAt 0 l k * ground.getAt 0 l k
          + 2 * ground.getAt 0 l k) 1,
      ← Nat.add_assoc (c2hat.sumSq l)
        (ground.getAt 0 l k * ground.getAt 0 l k)
        (2 * ground.getAt 0 l k)]

/-- The drop lowers the squares' fold by the doubled entry less one. -/
private theorem sumSq_dipAt : ∀ (k : Nat) (l : List Nat),
    0 < ground.getAt 0 l k →
    c2hat.sumSq (dipAt k l) + 2 * ground.getAt 0 l k
      = c2hat.sumSq l + 1
  := fun k l h => by
    have hlen : k < l.length := by
      match Nat.lt_or_ge k l.length with
      | .inl hl => exact hl
      | .inr hge =>
        rw [ground.getAt_over 0 l k hge] at h
        exact absurd h (Nat.lt_irrefl 0)
    have hb : ground.getAt 0 l k - 1 + 1 = ground.getAt 0 l k :=
      ground.subAdd h
    have hgen := sumSq_editAt (fun x => x - 1) k l hlen
    rw [(congrArg (fun z => z * z) hb).symm.trans
        (sqUp (ground.getAt 0 l k - 1))] at hgen
    have hY : c2hat.sumSq (ground.editAt (fun x => x - 1) k l)
        + 2 * (ground.getAt 0 l k - 1) + 1 = c2hat.sumSq l :=
      ground.addCancelR
        ((ground.getAt 0 l k - 1) * (ground.getAt 0 l k - 1)) (by
          rw [sqShift (c2hat.sumSq (ground.editAt (fun x => x - 1) k l))
              (2 * (ground.getAt 0 l k - 1))
              ((ground.getAt 0 l k - 1) * (ground.getAt 0 l k - 1)),
            Nat.add_assoc
              (c2hat.sumSq (ground.editAt (fun x => x - 1) k l))
              ((ground.getAt 0 l k - 1) * (ground.getAt 0 l k - 1))
              (2 * (ground.getAt 0 l k - 1)),
            Nat.add_assoc
              (c2hat.sumSq (ground.editAt (fun x => x - 1) k l))
              ((ground.getAt 0 l k - 1) * (ground.getAt 0 l k - 1)
                + 2 * (ground.getAt 0 l k - 1)) 1]
          exact hgen)
    have h2 : 2 * ground.getAt 0 l k
        = 2 * (ground.getAt 0 l k - 1) + 2 :=
      (congrArg (fun z => 2 * z) hb).symm.trans (by
        rw [Nat.left_distrib 2 (ground.getAt 0 l k - 1) 1, Nat.mul_one])
    show c2hat.sumSq (ground.editAt (fun x => x - 1) k l)
        + 2 * ground.getAt 0 l k = c2hat.sumSq l + 1
    rw [h2, ← hY, ← Nat.add_assoc
        (c2hat.sumSq (ground.editAt (fun x => x - 1) k l))
        (2 * (ground.getAt 0 l k - 1)) 2,
      Nat.add_assoc
        (c2hat.sumSq (ground.editAt (fun x => x - 1) k l)
          + 2 * (ground.getAt 0 l k - 1)) 1 1]

/-- The head's gap fold at a dominating head: the cons's gap sum
against the tail's total. -/
private theorem rho2_cons (x : Nat) (t : List Nat)
    (hdom : ∀ q, q < t.length → ground.getAt 0 t q ≤ x) :
    c2hat.rho2 (x :: t) + ground.sumNat t
      = t.length * x + c2hat.rho2 t := by
  show t.foldl (fun acc y => acc + (x - y)) 0 + c2hat.rho2 t
      + ground.sumNat t
    = t.length * x + c2hat.rho2 t
  rw [Nat.add_right_comm (t.foldl (fun acc y => acc + (x - y)) 0)
      (c2hat.rho2 t) (ground.sumNat t), ground.gapFold_total x t hdom]

/-- The gap fold against the key-weighted total at a weak descent:
the pair gaps join the doubled key weights at the counted total. -/
private theorem rhoJoin : ∀ (x : Nat) (t : List Nat),
    (∀ p, p + 1 < (x :: t).length →
      ground.getAt 0 (x :: t) (p + 1) ≤ ground.getAt 0 (x :: t) p) →
    c2hat.rho2 (x :: t) + 2 * wSum (x :: t)
      = t.length * ground.sumNat (x :: t)
  | x, [], _ => by
    show 0 + 2 * 0 = 0 * ground.sumNat [x]
    rw [Nat.mul_zero 2, Nat.zero_mul (ground.sumNat [x])]
  | x, y :: t, hdesc => by
    have hdt : ∀ p, p + 1 < (y :: t).length →
        ground.getAt 0 (y :: t) (p + 1) ≤ ground.getAt 0 (y :: t) p :=
      fun p hp => hdesc (p + 1) (Nat.succ_lt_succ hp)
    have hc : c2hat.rho2 (x :: y :: t) + ground.sumNat (y :: t)
        = (t.length + 1) * x + c2hat.rho2 (y :: t) :=
      rho2_cons x (y :: t) (headDom x (y :: t) hdesc)
    have hih := rhoJoin y t hdt
    show c2hat.rho2 (x :: y :: t)
        + 2 * (ground.sumNat (y :: t) + wSum (y :: t))
      = (t.length + 1) * (x + ground.sumNat (y :: t))
    rw [Nat.left_distrib 2 (ground.sumNat (y :: t)) (wSum (y :: t)),
      Nat.two_mul (ground.sumNat (y :: t)),
      Nat.add_assoc (ground.sumNat (y :: t)) (ground.sumNat (y :: t))
        (2 * wSum (y :: t)),
      ← Nat.add_assoc (c2hat.rho2 (x :: y :: t)) (ground.sumNat (y :: t))
        (ground.sumNat (y :: t) + 2 * wSum (y :: t)),
      hc, Nat.add_assoc ((t.length + 1) * x) (c2hat.rho2 (y :: t))
        (ground.sumNat (y :: t) + 2 * wSum (y :: t)),
      Nat.add_left_comm (c2hat.rho2 (y :: t)) (ground.sumNat (y :: t))
        (2 * wSum (y :: t)), hih,
      Nat.left_distrib (t.length + 1) x (ground.sumNat (y :: t)),
      mulAddR t.length 1 (ground.sumNat (y :: t)),
      Nat.one_mul (ground.sumNat (y :: t)),
      Nat.add_comm (t.length * ground.sumNat (y :: t))
        (ground.sumNat (y :: t))]

/-- The cleared read is a class read: a full column moves every row
by one and the gaps are fixed. -/
private theorem qRows_shift (l : List Nat) :
    qRows (List.map (fun x => x + 1) l) = qRows l := by
  show c2hat.sqGaps (l.map (fun x => x + 1))
      + (l.map (fun x => x + 1)).length
        * c2hat.rho2 (l.map (fun x => x + 1))
    = c2hat.sqGaps l + l.length * c2hat.rho2 l
  rw [c2hat.sqGaps_shift l, c2hat.rho2_shift l, ground.length_map]

/-- The leading count at or above two is a prefix count. -/
private theorem big2_le_length : ∀ l : List Nat, big2 l ≤ l.length
  | [] => Nat.le_refl 0
  | x :: t => by
    show (if 2 ≤ x then big2 t + 1 else 0) ≤ t.length + 1
    by_cases hx : 2 ≤ x
    · rw [if_pos hx]
      exact Nat.succ_le_succ (big2_le_length t)
    · rw [if_neg hx]
      exact Nat.zero_le (t.length + 1)

/-- The leading occupied count is a prefix count. -/
private theorem posLen_le_length : ∀ l : List Nat, posLen l ≤ l.length
  | [] => Nat.le_refl 0
  | x :: t => by
    show (if 0 < x then posLen t + 1 else 0) ≤ t.length + 1
    by_cases hx : 0 < x
    · rw [if_pos hx]
      exact Nat.succ_le_succ (posLen_le_length t)
    · rw [if_neg hx]
      exact Nat.zero_le (t.length + 1)

set_option linter.unusedVariables false in
/-- The leading count at or above two reads the entries: a key sits
below it exactly at an entry of two or more. -/
private theorem big2_read : ∀ (l : List Nat)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (p : Nat), p < l.length →
    (p < big2 l ↔ 2 ≤ ground.getAt 0 l p)
  | [], _, p, h => absurd h (Nat.not_lt_zero p)
  | x :: _, _, 0, _ => by
    show 0 < (if 2 ≤ x then big2 _ + 1 else 0) ↔ 2 ≤ x
    by_cases hx : 2 ≤ x
    · rw [if_pos hx]
      exact Iff.intro (fun _ => hx) (fun _ => Nat.succ_pos _)
    · rw [if_neg hx]
      exact Iff.intro (fun hlt => absurd hlt (Nat.lt_irrefl 0))
        (fun h2 => absurd h2 hx)
  | x :: t, hdesc, q + 1, h => by
    have hdt : ∀ p, p + 1 < t.length →
        ground.getAt 0 t (p + 1) ≤ ground.getAt 0 t p :=
      fun p hp => hdesc (p + 1) (Nat.succ_lt_succ hp)
    have hq : q < t.length := Nat.lt_of_succ_lt_succ h
    show q + 1 < (if 2 ≤ x then big2 t + 1 else 0)
      ↔ 2 ≤ ground.getAt 0 t q
    by_cases hx : 2 ≤ x
    · rw [if_pos hx]
      exact Iff.intro
        (fun hlt => (big2_read t hdt q hq).mp (Nat.lt_of_succ_lt_succ hlt))
        (fun h2 => Nat.succ_lt_succ ((big2_read t hdt q hq).mpr h2))
    · rw [if_neg hx]
      exact Iff.intro (fun hlt => absurd hlt (Nat.not_lt_zero (q + 1)))
        (fun h2 => absurd
          (Nat.le_trans h2 (headDom x t hdesc q hq)) hx)

set_option linter.unusedVariables false in
/-- The leading occupied count reads the entries: a key sits below
it exactly at an occupied entry. -/
private theorem posLen_read : ∀ (l : List Nat)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (p : Nat), p < l.length →
    (p < posLen l ↔ 0 < ground.getAt 0 l p)
  | [], _, p, h => absurd h (Nat.not_lt_zero p)
  | x :: _, _, 0, _ => by
    show 0 < (if 0 < x then posLen _ + 1 else 0) ↔ 0 < x
    by_cases hx : 0 < x
    · rw [if_pos hx]
      exact Iff.intro (fun _ => hx) (fun _ => Nat.succ_pos _)
    · rw [if_neg hx]
      exact Iff.intro (fun hlt => absurd hlt (Nat.lt_irrefl 0))
        (fun h2 => absurd h2 hx)
  | x :: t, hdesc, q + 1, h => by
    have hdt : ∀ p, p + 1 < t.length →
        ground.getAt 0 t (p + 1) ≤ ground.getAt 0 t p :=
      fun p hp => hdesc (p + 1) (Nat.succ_lt_succ hp)
    have hq : q < t.length := Nat.lt_of_succ_lt_succ h
    show q + 1 < (if 0 < x then posLen t + 1 else 0)
      ↔ 0 < ground.getAt 0 t q
    by_cases hx : 0 < x
    · rw [if_pos hx]
      exact Iff.intro
        (fun hlt =>
          (posLen_read t hdt q hq).mp (Nat.lt_of_succ_lt_succ hlt))
        (fun h2 => Nat.succ_lt_succ ((posLen_read t hdt q hq).mpr h2))
    · rw [if_neg hx]
      exact Iff.intro (fun hlt => absurd hlt (Nat.not_lt_zero (q + 1)))
        (fun h2 => absurd
          (Nat.lt_of_lt_of_le h2 (headDom x t hdesc q hq)) hx)

/-- A vacant head at a weak descent leaves every entry vacant. -/
private theorem allZero : ∀ (l : List Nat),
    (∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) →
    ground.getAt 0 l 0 = 0 → l = List.replicate l.length 0
  | [], _, _ => rfl
  | x :: t, hdesc, h0 => by
    have hdt : ∀ p, p + 1 < t.length →
        ground.getAt 0 t (p + 1) ≤ ground.getAt 0 t p :=
      fun p hp => hdesc (p + 1) (Nat.succ_lt_succ hp)
    have hx : x = 0 := h0
    have ht0 : ground.getAt 0 t 0 = 0 := by
      cases t with
      | nil => rfl
      | cons y u =>
        have hy : ground.getAt 0 (y :: u) 0 ≤ x :=
          headDom x (y :: u) hdesc 0 (Nat.succ_pos u.length)
        rw [hx] at hy
        exact Nat.le_zero.mp hy
    show x :: t = 0 :: List.replicate t.length 0
    rw [hx]
    exact congrArg (fun u => 0 :: u) (allZero t hdt ht0)

/-- A vacant head at a weak descent leaves the total vacant. -/
private theorem sumNat_zero_of_headZero : ∀ (l : List Nat),
    (∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) →
    ground.getAt 0 l 0 = 0 → ground.sumNat l = 0 := by
  intro l hdesc h0
  rw [allZero l hdesc h0, ground.sumNat_replicate_zero l.length]

/-- A head at or below one at a weak descent names the unit family:
the leading units against the trailing vacancies. -/
private theorem ones_of_headLe : ∀ (l : List Nat),
    (∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) →
    ground.getAt 0 l 0 ≤ 1 →
    l = ground.onesRows (posLen l) (l.length - posLen l)
  | [], _, _ => rfl
  | x :: t, hdesc, h1 => by
    have hdt : ∀ p, p + 1 < t.length →
        ground.getAt 0 t (p + 1) ≤ ground.getAt 0 t p :=
      fun p hp => hdesc (p + 1) (Nat.succ_lt_succ hp)
    have ht1 : ground.getAt 0 t 0 ≤ x := by
      cases t with
      | nil => exact Nat.zero_le x
      | cons y u => exact headDom x (y :: u) hdesc 0 (Nat.succ_pos u.length)
    cases x with
    | zero =>
      have ht0 : ground.getAt 0 t 0 = 0 := Nat.le_zero.mp ht1
      show (0 : Nat) :: t = 0 :: List.replicate t.length 0
      exact congrArg (fun u => 0 :: u) (allZero t hdt ht0)
    | succ b =>
      cases b with
      | succ c =>
        exact absurd (Nat.le_of_succ_le_succ h1) (Nat.not_succ_le_zero c)
      | zero =>
        have hsub : t.length + 1 - (posLen t + 1) = t.length - posLen t :=
          Nat.succ_sub_succ t.length (posLen t)
        show (1 : Nat) :: t
          = 1 :: ground.onesRows (posLen t) (t.length + 1 - (posLen t + 1))
        rw [hsub]
        exact congrArg (fun u => 1 :: u) (ones_of_headLe t hdt ht1)

/-- The raise undoes the drop at an occupied family. -/
private theorem map_dip_bump : ∀ (l : List Nat),
    (∀ p, p < l.length → 0 < ground.getAt 0 l p) →
    List.map (fun x => x + 1) (List.map (fun x => x - 1) l) = l
  | [], _ => rfl
  | x :: t, hpos => by
    have hx : 0 < x := hpos 0 (Nat.succ_pos t.length)
    cases x with
    | zero => exact absurd hx (Nat.lt_irrefl 0)
    | succ b =>
      show (b + 1) :: List.map (fun x => x + 1)
          (List.map (fun x => x - 1) t)
        = (b + 1) :: t
      exact congrArg (fun u => (b + 1) :: u)
        (map_dip_bump t (fun p hp => hpos (p + 1) (Nat.succ_lt_succ hp)))

/-- The row list's head is the shape's total. -/
private theorem rowHead_read : ∀ s : places.Shape, s ≠ [] →
    ground.getAt 0 (places.rowList s) 0 = ground.sumNat s
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

/-- The row list's last entry is the shape's own. -/
private theorem rowLast_read : ∀ (s : places.Shape) (r : Nat),
    s.length = r + 1 →
    ground.getAt 0 (places.rowList s) r = ground.getAt 0 s r
  | [], _, h => nomatch h
  | _ :: t, 0, h => by
    cases t with
    | nil => rfl
    | cons _ u => exact Nat.noConfusion (Nat.succ.inj h)
  | _ :: t, r + 1, h => rowLast_read t r (Nat.succ.inj h)

/-- The unit family's gap fold is the crossed count: the unit
block pairs at no gap among itself and reads each vacancy once. -/
private theorem rho2_ones (j g : Nat) :
    c2hat.rho2 (ground.onesRows j g) = j * g := by
  show c2hat.rho2 (List.replicate j 1 ++ List.replicate g 0) = j * g
  rw [c2hat.rho2_replicate_app 1 j (List.replicate g 0),
    c2hat.gapFold_replicate 1 0 g 0, c2hat.rho2_zeros g]
  show j * (0 + g * 1) + 0 = j * g
  rw [Nat.zero_add (g * 1), Nat.mul_one g, Nat.add_zero (j * g)]

/-- The unit family's squared gap fold is the crossed count. -/
private theorem sqGaps_ones (j g : Nat) :
    c2hat.sqGaps (ground.onesRows j g) = j * g := by
  show c2hat.sqGaps (List.replicate j 1 ++ List.replicate g 0) = j * g
  rw [c2hat.sqGaps_replicate_app 1 j (List.replicate g 0),
    c2hat.sqFold_replicate 1 0 g 0, c2hat.sqGaps_zeros g]
  show j * (0 + g * 1) + 0 = j * g
  rw [Nat.zero_add (g * 1), Nat.mul_one g, Nat.add_zero (j * g)]

/-- The unit family's cleared read, the endpoint's own value. -/
private theorem qRows_ones : ∀ j g : Nat,
    qRows (ground.onesRows j g) = j * g * (j + g + 1) := by
  intro j g
  show c2hat.sqGaps (ground.onesRows j g)
      + (ground.onesRows j g).length * c2hat.rho2 (ground.onesRows j g)
    = j * g * (j + g + 1)
  rw [sqGaps_ones j g, rho2_ones j g, ground.length_onesRows j g,
    Nat.left_distrib (j * g) (j + g) 1, Nat.mul_one (j * g),
    Nat.mul_comm (j + g) (j * g), Nat.add_comm (j * g) (j * g * (j + g))]


/-- The Boolean equality drops a shared successor. -/
private theorem beqSucc (a b : Nat) : (a + 1 == b + 1) = (a == b) := by
  by_cases h : a = b
  · rw [ground.eqBeqOf (congrArg (fun n => n + 1) h), ground.eqBeqOf h]
  · rw [ground.neBeqOf (fun he => h (Nat.succ.inj he)), ground.neBeqOf h]

/-- The fundamental's shape reads at a raised key: the column moves
one place deeper. -/
private theorem fund_cons (j g : Nat) :
    fundShape (j + 1) g
      = (if 1 == j + 1 then 1 else 0) :: fundShape j g := by
  have hr : List.range (j + 1 + g)
      = 0 :: (List.range (j + g)).map (fun k => k + 1) := by
    rw [Nat.add_right_comm j 1 g]
    exact ground.range_cons (j + g)
  show (List.range (j + 1 + g)).map
      (fun k => if k + 1 == j + 1 then 1 else 0)
    = (if 1 == j + 1 then 1 else 0)
      :: (List.range (j + g)).map (fun k => if k + 1 == j then 1 else 0)
  rw [hr]
  show (if 1 == j + 1 then 1 else 0)
      :: ((List.range (j + g)).map (fun k => k + 1)).map
        (fun k => if k + 1 == j + 1 then 1 else 0)
    = (if 1 == j + 1 then 1 else 0)
      :: (List.range (j + g)).map (fun k => if k + 1 == j then 1 else 0)
  rw [ground.map_map (fun k => k + 1)
    (fun k => if k + 1 == j + 1 then 1 else 0) (List.range (j + g))]
  exact congrArg (fun u => (if 1 == j + 1 then 1 else 0) :: u)
    (ground.map_congr_all _ _
      (fun x => by rw [beqSucc (x + 1) j]) (List.range (j + g)))

/-- The vacant map at a shifted key names the vacant family. -/
private theorem mapIf0 : ∀ l : List Nat,
    l.map (fun k => if k + 1 == 0 then 1 else 0)
      = List.replicate l.length 0
  | [] => rfl
  | _ :: t => congrArg (fun u => 0 :: u) (mapIf0 t)

/-- The vacant fundamental is the vacant family. -/
private theorem fund_zero (g : Nat) :
    fundShape 0 g = List.replicate g 0 := by
  show (List.range (0 + g)).map (fun k => if k + 1 == 0 then 1 else 0)
    = List.replicate g 0
  rw [Nat.zero_add g, mapIf0 (List.range g), ground.length_range g]

/-- The fundamental's shape carries one box. -/
private theorem sumNat_fund : ∀ j g : Nat,
    ground.sumNat (fundShape (j + 1) g) = 1
  | 0, g => by
    have h1 : fundShape 1 g = 1 :: fundShape 0 g := fund_cons 0 g
    show ground.sumNat (fundShape 1 g) = 1
    rw [h1, fund_zero g]
    show 1 + ground.sumNat (List.replicate g 0) = 1
    rw [ground.sumNat_replicate_zero g]
  | j + 1, g => by
    have hs : fundShape (j + 2) g = 0 :: fundShape (j + 1) g :=
      fund_cons (j + 1) g
    show ground.sumNat (fundShape (j + 2) g) = 1
    rw [hs]
    show 0 + ground.sumNat (fundShape (j + 1) g) = 1
    rw [Nat.zero_add, sumNat_fund j g]

/-- The fundamental's row list is the unit family. -/
private theorem rowList_fund : ∀ j g : Nat,
    places.rowList (fundShape j g) = ground.onesRows j g
  | 0, g => by
    show places.rowList (fundShape 0 g) = List.replicate g 0
    rw [fund_zero g, places.rowList_replicate_zero g]
  | 1, g => by
    have h1 : fundShape 1 g = 1 :: fundShape 0 g := fund_cons 0 g
    show places.rowList (fundShape 1 g) = 1 :: List.replicate g 0
    rw [h1, fund_zero g]
    show (1 + ground.sumNat (List.replicate g 0))
        :: places.rowList (List.replicate g 0) = 1 :: List.replicate g 0
    rw [ground.sumNat_replicate_zero g, Nat.add_zero 1, places.rowList_replicate_zero g]
  | j + 2, g => by
    have hs : fundShape (j + 2) g = 0 :: fundShape (j + 1) g :=
      fund_cons (j + 1) g
    show places.rowList (fundShape (j + 2) g) = 1 :: ground.onesRows (j + 1) g
    rw [hs]
    show (0 + ground.sumNat (fundShape (j + 1) g))
        :: places.rowList (fundShape (j + 1) g) = 1 :: ground.onesRows (j + 1) g
    rw [sumNat_fund j g, Nat.zero_add 1, rowList_fund (j + 1) g]

/-- The fundamental's shape has the complement gap's length. -/
private theorem length_fund (j g : Nat) :
    (fundShape j g).length = j + g :=
  ground.length_mapRange _ (j + g)

/-- The endpoint display at every key pair,
`d_f Q(ω_j) = j g_j (r+2)` at the complement gap `j + g_j = d_f`,
proven general. -/
theorem endpointAll (j g : Nat) : endpointRead j g := by
  have hlen : (fundShape j g).length = (ground.onesRows j g).length := by
    rw [length_fund j g, ground.length_onesRows j g]
  show c2hat.sqGaps (places.rowList (fundShape j g))
      + (fundShape j g).length
        * c2hat.rho2 (places.rowList (fundShape j g))
    = j * g * (j + g + 1)
  rw [rowList_fund j g, hlen]
  exact qRows_ones j g

/-- The complement pair's product is at least its total's
successor. -/
private theorem endpointLeast : ∀ a b : Nat,
    (a + b) + 1 ≤ (a + 1) * (b + 1) := by
  intro a b
  rw [mulAddR a 1 (b + 1), Nat.left_distrib a b 1, Nat.mul_one a,
    Nat.one_mul (b + 1), Nat.add_assoc a b 1,
    Nat.add_assoc (a * b) a (b + 1)]
  exact Nat.le_add_left (a + (b + 1)) (a * b)

/-- The least is attained only at a vacant member. -/
private theorem endpointLeast_eq : ∀ a b : Nat,
    (a + 1) * (b + 1) = (a + b) + 1 → a = 0 ∨ b = 0 := by
  intro a b h
  rw [mulAddR a 1 (b + 1), Nat.left_distrib a b 1, Nat.mul_one a,
    Nat.one_mul (b + 1), Nat.add_assoc (a * b) a (b + 1),
    Nat.add_assoc a b 1] at h
  have h0 : a * b = 0 :=
    addCancelR (a + (b + 1))
      (by rw [Nat.zero_add (a + (b + 1))]; exact h)
  cases a with
  | zero => exact Or.inl rfl
  | succ a' =>
    cases b with
    | zero => exact Or.inr rfl
    | succ b' => exact Nat.noConfusion h0

/-! The box move's fall (`lem:casfloor`'s descent): the chained
descent, the edit's length reads, and the rows-level fall identity
at one lowered row and one raised row. -/

/-- The doubled successor against the moved unit. -/
private theorem twoSucc (n : Nat) : 2 * (n + 1) = 2 * n + 1 + 1 := by
  rw [Nat.left_distrib 2 n 1, Nat.mul_one 2]

/-- The gap join at an occupied family, the cons form's read carried
to the whole list. -/
private theorem rhoJoin' (l : List Nat) (hpos : 0 < l.length)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) :
    c2hat.rho2 l + 2 * wSum l + ground.sumNat l
      = l.length * ground.sumNat l := by
  cases l with
  | nil => exact absurd hpos (Nat.lt_irrefl 0)
  | cons x t =>
    have hj := rhoJoin x t hdesc
    show c2hat.rho2 (x :: t) + 2 * wSum (x :: t) + ground.sumNat (x :: t)
      = (t.length + 1) * ground.sumNat (x :: t)
    rw [hj, mulAddR t.length 1 (ground.sumNat (x :: t)),
      Nat.one_mul (ground.sumNat (x :: t))]

/-- The four-term shift at a doubled member. -/
private theorem shift4 (a b c : Nat) :
    a + b + (c + (c + 1)) = a + 2 * c + b + 1 := by
  rw [← Nat.add_assoc c c 1, ← Nat.two_mul c,
    ← Nat.add_assoc (a + b) (2 * c) 1, Nat.add_right_comm a b (2 * c)]

/-- The five-term shift at a doubled member. -/
private theorem shift5 (a b c e : Nat) :
    a + b + (c + 1 + c) + e = a + 2 * c + (b + e) + 1 := by
  rw [Nat.add_right_comm c 1 c, ← Nat.two_mul c,
    ← Nat.add_assoc (a + b) (2 * c) 1,
    Nat.add_right_comm (a + b + 2 * c) 1 e,
    Nat.add_right_comm a b (2 * c), Nat.add_assoc (a + 2 * c) b e]

/-- The rows-level fall at one box move: a family joined to another
at one lowered key and one raised key, the crossed display at the
places' gap. -/
private theorem qRowsFall (l m : List Nat) (i g : Nat)
    (hlen : m.length = l.length) (hj : i + g < l.length)
    (hdl : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hdm : ∀ p, p + 1 < m.length →
      ground.getAt 0 m (p + 1) ≤ ground.getAt 0 m p)
    (hi : ground.getAt 0 m i + 1 = ground.getAt 0 l i)
    (hg : ground.getAt 0 m (i + g)
        = ground.getAt 0 l (i + g) + 1)
    (hoff : ∀ p, p < l.length → p ≠ i → p ≠ i + g →
      ground.getAt 0 m p = ground.getAt 0 l p) :
    qRows l + l.length
        * (ground.getAt 0 l (i + g) + ground.getAt 0 m (i + g))
      = qRows m + l.length
        * (ground.getAt 0 l i + ground.getAt 0 m i)
        + 2 * l.length * g := by
  cases g with
  | zero =>
    exfalso
    have hg0 : ground.getAt 0 m i = ground.getAt 0 l i + 1 := hg
    have hc : ground.getAt 0 l i + 1 + 1 = ground.getAt 0 l i := by
      rw [← hg0]; exact hi
    have hlt : ground.getAt 0 l i < ground.getAt 0 l i + 1 + 1 :=
      Nat.lt_succ_of_lt (Nat.lt_succ_self _)
    rw [hc] at hlt
    exact absurd hlt (Nat.lt_irrefl _)
  | succ g' =>
    have hup : i < i + (g' + 1) := Nat.lt_succ_of_le (Nat.le_add_right i g')
    have hne : i + (g' + 1) ≠ i :=
      fun h => Nat.lt_irrefl i (Nat.lt_of_lt_of_eq hup h)
    have hpos : 0 < ground.getAt 0 l i := hi ▸ Nat.succ_pos _
    have hDlen : (dipAt i l).length = l.length := length_dipAt i l
    have hjD : i + (g' + 1) < (dipAt i l).length := by rw [hDlen]; exact hj
    have hm : m = ground.bumpAt (i + (g' + 1)) (dipAt i l) := by
      refine ground.getAt_ext 0 _ _ ?_ ?_
      · rw [hlen, length_bumpAt, hDlen]
      · intro p hp
        by_cases hpi : p = i
        · rw [hpi, getAt_bumpAt_ne (i + (g' + 1)) (dipAt i l) i
            (fun h => hne h.symm)]
          exact addCancelR 1
            (hi.trans (getAt_dipAt_self i l hpos).symm)
        · by_cases hpj : p = i + (g' + 1)
          · rw [hpj, getAt_bumpAt_self (i + (g' + 1)) (dipAt i l) hjD,
              getAt_dipAt_ne i l (i + (g' + 1)) hne]
            exact hg
          · rw [getAt_bumpAt_ne (i + (g' + 1)) (dipAt i l) p hpj,
              getAt_dipAt_ne i l p hpi]
            exact hoff p (hlen ▸ hp) hpi hpj
    have hsum : ground.sumNat m = ground.sumNat l := by
      rw [hm, ground.sumNat_bumpAt (i + (g' + 1)) (dipAt i l) hjD,
        ground.sumNat_dipAt i l hpos]
    have hwm : wSum m = wSum (dipAt i l) + (i + (g' + 1)) := by
      rw [hm, wSum_bumpAt (i + (g' + 1)) (dipAt i l) hjD]
    have hwd : wSum (dipAt i l) + i = wSum l := wSum_dipAt i l hpos
    have hw : wSum m + i = wSum l + (i + (g' + 1)) := by
      rw [hwm, Nat.add_right_comm (wSum (dipAt i l)) (i + (g' + 1)) i, hwd]
    have hwg : wSum m = wSum l + (g' + 1) := by
      apply addCancelR i
      rw [hw, Nat.add_comm i (g' + 1), ← Nat.add_assoc (wSum l) (g' + 1) i]
    have hposl : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
    have hposm : 0 < m.length := by rw [hlen]; exact hposl
    have hjl := rhoJoin' l hposl hdl
    have hjm := rhoJoin' m hposm hdm
    rw [hlen, hsum] at hjm
    have h1 : c2hat.rho2 l + 2 * wSum l = c2hat.rho2 m + 2 * wSum m :=
      addCancelR (ground.sumNat l) (hjl.trans hjm.symm)
    rw [hwg, Nat.left_distrib 2 (wSum l) (g' + 1),
      Nat.add_comm (2 * wSum l) (2 * (g' + 1)),
      ← Nat.add_assoc (c2hat.rho2 m) (2 * (g' + 1)) (2 * wSum l)] at h1
    have hr : c2hat.rho2 l = c2hat.rho2 m + 2 * (g' + 1) :=
      addCancelR (2 * wSum l) h1
    have hsm : c2hat.sumSq m
        = c2hat.sumSq (dipAt i l)
          + 2 * ground.getAt 0 l (i + (g' + 1)) + 1 := by
      rw [hm, sumSq_bumpAt (i + (g' + 1)) (dipAt i l) hjD,
        getAt_dipAt_ne i l (i + (g' + 1)) hne]
    have hsd : c2hat.sumSq (dipAt i l) + 2 * ground.getAt 0 l i
        = c2hat.sumSq l + 1 := sumSq_dipAt i l hpos
    rw [← hi, twoSucc (ground.getAt 0 m i),
      ← Nat.add_assoc (c2hat.sumSq (dipAt i l))
        (2 * ground.getAt 0 m i + 1) 1,
      ← Nat.add_assoc (c2hat.sumSq (dipAt i l))
        (2 * ground.getAt 0 m i) 1] at hsd
    have hsd' : c2hat.sumSq (dipAt i l) + 2 * ground.getAt 0 m i + 1
        = c2hat.sumSq l := addCancelR 1 hsd
    have hs : c2hat.sumSq m + 2 * ground.getAt 0 m i
        = c2hat.sumSq l + 2 * ground.getAt 0 l (i + (g' + 1)) := by
      rw [hsm, sqShift (c2hat.sumSq (dipAt i l))
          (2 * ground.getAt 0 l (i + (g' + 1))) (2 * ground.getAt 0 m i),
        Nat.add_right_comm (c2hat.sumSq (dipAt i l)
          + 2 * ground.getAt 0 m i)
          (2 * ground.getAt 0 l (i + (g' + 1))) 1, hsd']
    have hkey : c2hat.sumSq l + c2hat.rho2 l
          + (ground.getAt 0 l (i + (g' + 1))
             + ground.getAt 0 m (i + (g' + 1)))
        = c2hat.sumSq m + c2hat.rho2 m
          + (ground.getAt 0 l i + ground.getAt 0 m i) + 2 * (g' + 1) := by
      rw [hr, hg, ← hi,
        shift4 (c2hat.sumSq l) (c2hat.rho2 m + 2 * (g' + 1))
          (ground.getAt 0 l (i + (g' + 1))),
        shift5 (c2hat.sumSq m) (c2hat.rho2 m) (ground.getAt 0 m i)
          (2 * (g' + 1)), hs]
    have hmul : l.length * (c2hat.sumSq l + c2hat.rho2 l
          + (ground.getAt 0 l (i + (g' + 1))
             + ground.getAt 0 m (i + (g' + 1))))
        = l.length * (c2hat.sumSq m + c2hat.rho2 m
          + (ground.getAt 0 l i + ground.getAt 0 m i) + 2 * (g' + 1)) :=
      congrArg (fun z => l.length * z) hkey
    have hA : l.length * c2hat.sumSq l
        = ground.sumNat l * ground.sumNat l + c2hat.sqGaps l :=
      c2hat.squareRows l hdl
    have hB : l.length * c2hat.sumSq m
        = ground.sumNat l * ground.sumNat l + c2hat.sqGaps m := by
      have hq := c2hat.squareRows m hdm
      rw [hlen, hsum] at hq
      exact hq
    have hG : l.length * (2 * (g' + 1)) = 2 * l.length * (g' + 1) := by
      rw [← mulAssoc l.length 2 (g' + 1), Nat.mul_comm l.length 2]
    rw [Nat.left_distrib l.length (c2hat.sumSq l + c2hat.rho2 l)
        (ground.getAt 0 l (i + (g' + 1))
          + ground.getAt 0 m (i + (g' + 1))),
      Nat.left_distrib l.length (c2hat.sumSq l) (c2hat.rho2 l),
      Nat.left_distrib l.length
        (c2hat.sumSq m + c2hat.rho2 m
          + (ground.getAt 0 l i + ground.getAt 0 m i)) (2 * (g' + 1)),
      Nat.left_distrib l.length (c2hat.sumSq m + c2hat.rho2 m)
        (ground.getAt 0 l i + ground.getAt 0 m i),
      Nat.left_distrib l.length (c2hat.sumSq m) (c2hat.rho2 m),
      hA, hB, hG,
      Nat.add_assoc (ground.sumNat l * ground.sumNat l) (c2hat.sqGaps l)
        (l.length * c2hat.rho2 l),
      Nat.add_assoc (ground.sumNat l * ground.sumNat l)
        (c2hat.sqGaps l + l.length * c2hat.rho2 l)
        (l.length * (ground.getAt 0 l (i + (g' + 1))
          + ground.getAt 0 m (i + (g' + 1)))),
      Nat.add_assoc (ground.sumNat l * ground.sumNat l) (c2hat.sqGaps m)
        (l.length * c2hat.rho2 m),
      Nat.add_assoc (ground.sumNat l * ground.sumNat l)
        (c2hat.sqGaps m + l.length * c2hat.rho2 m)
        (l.length * (ground.getAt 0 l i + ground.getAt 0 m i)),
      Nat.add_assoc (ground.sumNat l * ground.sumNat l)
        (c2hat.sqGaps m + l.length * c2hat.rho2 m
          + l.length * (ground.getAt 0 l i + ground.getAt 0 m i))
        (2 * l.length * (g' + 1))] at hmul
    show c2hat.sqGaps l + l.length * c2hat.rho2 l
        + l.length * (ground.getAt 0 l (i + (g' + 1))
          + ground.getAt 0 m (i + (g' + 1)))
      = c2hat.sqGaps m + m.length * c2hat.rho2 m
        + l.length * (ground.getAt 0 l i + ground.getAt 0 m i)
        + 2 * l.length * (g' + 1)
    rw [hlen]
    exact addCancelL _ hmul

/-- The product carries a strict order at an occupied left member,
the hand-rolled read. -/
private theorem mulLtLeft : ∀ (d : Nat), 0 < d → ∀ {x y : Nat},
    x < y → d * x < d * y := by
  intro d hd x y h
  cases d with
  | zero => exact absurd hd (Nat.lt_irrefl 0)
  | succ c =>
    have h1 : (c + 1) * (x + 1) ≤ (c + 1) * y := Nat.mul_le_mul_left (c + 1) h
    have h2 : (c + 1) * x < (c + 1) * (x + 1) := by
      rw [Nat.left_distrib (c + 1) x 1, Nat.mul_one (c + 1)]
      exact Nat.lt_succ_of_le (Nat.le_add_right ((c + 1) * x) c)
    exact Nat.lt_of_lt_of_le h2 h1

/-- The fall is strict at the rows: the box move lowers the cleared
read. -/
private theorem qRowsFall_lt (l m : List Nat) (i g : Nat)
    (hlen : m.length = l.length) (hj : i + g < l.length)
    (hdl : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hdm : ∀ p, p + 1 < m.length →
      ground.getAt 0 m (p + 1) ≤ ground.getAt 0 m p)
    (hi : ground.getAt 0 m i + 1 = ground.getAt 0 l i)
    (hg : ground.getAt 0 m (i + g)
        = ground.getAt 0 l (i + g) + 1)
    (hoff : ∀ p, p < l.length → p ≠ i → p ≠ i + g →
      ground.getAt 0 m p = ground.getAt 0 l p) :
    qRows m < qRows l := by
  cases g with
  | zero =>
    exfalso
    have hg0 : ground.getAt 0 m i = ground.getAt 0 l i + 1 := hg
    have hc : ground.getAt 0 l i + 1 + 1 = ground.getAt 0 l i := by
      rw [← hg0]; exact hi
    have hlt : ground.getAt 0 l i < ground.getAt 0 l i + 1 + 1 :=
      Nat.lt_succ_of_lt (Nat.lt_succ_self _)
    rw [hc] at hlt
    exact absurd hlt (Nat.lt_irrefl _)
  | succ g' =>
    have hfall := qRowsFall l m i (g' + 1) hlen hj hdl hdm hi hg hoff
    have hjm : i + (g' + 1) < m.length := by rw [hlen]; exact hj
    have hdown : ground.getAt 0 m (i + (g' + 1)) ≤ ground.getAt 0 m i :=
      ground.descLe m i (i + (g' + 1)) hdm (Nat.le_add_right i (g' + 1)) hjm
    have hstep : ground.getAt 0 l (i + (g' + 1))
        < ground.getAt 0 m (i + (g' + 1)) := by
      rw [hg]; exact Nat.lt_succ_self _
    have hlg : ground.getAt 0 l (i + (g' + 1)) < ground.getAt 0 m i :=
      Nat.lt_of_lt_of_le hstep hdown
    have hAB : ground.getAt 0 l (i + (g' + 1))
          + ground.getAt 0 m (i + (g' + 1))
        < ground.getAt 0 l i + ground.getAt 0 m i := by
      rw [hg, ← hi, ← Nat.add_assoc (ground.getAt 0 l (i + (g' + 1)))
          (ground.getAt 0 l (i + (g' + 1))) 1,
        Nat.add_right_comm (ground.getAt 0 m i) 1 (ground.getAt 0 m i)]
      exact Nat.succ_lt_succ (Nat.add_lt_add hlg hlg)
    have hd : 0 < l.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hj
    have hlt2 : l.length * (ground.getAt 0 l (i + (g' + 1))
          + ground.getAt 0 m (i + (g' + 1)))
        < l.length * (ground.getAt 0 l i + ground.getAt 0 m i)
          + 2 * l.length * (g' + 1) :=
      Nat.lt_of_lt_of_le (mulLtLeft l.length hd hAB) (Nat.le_add_right _ _)
    have h3 := Nat.add_lt_add_left hlt2 (qRows m)
    rw [← Nat.add_assoc (qRows m)
        (l.length * (ground.getAt 0 l i + ground.getAt 0 m i))
        (2 * l.length * (g' + 1)), ← hfall] at h3
    exact Nat.lt_of_add_lt_add_right h3

/-- The entry at a key at or past the length reads the stated
default. -/
private theorem getAt_default : ∀ (l : List Nat) (p : Nat),
    l.length ≤ p → ground.getAt 0 l p = 0
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: t, p + 1, h => getAt_default t p (Nat.le_of_succ_le_succ h)

/-- The box move's fall identity (`lem:casfloor`): two shapes
joined at one row pair, `λ + e_b = μ + e_a` entrywise at the rows,
read the crossed display `d_f Q(λ) + d_f (λ_b + μ_b) = d_f Q(μ) +
d_f (λ_a + μ_a) + 2 d_f g` at the places' gap `g`; the rows' weak
descent is the shape carrier's own, and the raised key sits inside
the display by the raise's own read. -/
theorem boxFall (s t : places.Shape) (i g : Nat)
    (hlen : t.length = s.length)
    (hi : ground.getAt 0 (places.rowList t) i + 1
        = ground.getAt 0 (places.rowList s) i)
    (hg : ground.getAt 0 (places.rowList t) (i + g)
        = ground.getAt 0 (places.rowList s) (i + g) + 1)
    (hoff : ∀ p, p < s.length → p ≠ i → p ≠ i + g →
      ground.getAt 0 (places.rowList t) p
        = ground.getAt 0 (places.rowList s) p) :
    c2hat.dfQ s + s.length
        * (ground.getAt 0 (places.rowList s) (i + g)
           + ground.getAt 0 (places.rowList t) (i + g))
      = c2hat.dfQ t + s.length
        * (ground.getAt 0 (places.rowList s) i
           + ground.getAt 0 (places.rowList t) i)
        + 2 * s.length * g := by
  have hj : i + g < s.length := by
    cases Nat.lt_or_ge (i + g) s.length with
    | inl h => exact h
    | inr h =>
      rw [getAt_default (places.rowList t) (i + g)
          (by rw [places.length_rowList, hlen]; exact h),
        getAt_default (places.rowList s) (i + g)
          (by rw [places.length_rowList]; exact h)] at hg
      exact Nat.noConfusion hg
  have hls : (places.rowList s).length = s.length := places.length_rowList s
  have hlt : (places.rowList t).length = t.length := places.length_rowList t
  have hml : (places.rowList t).length = (places.rowList s).length := by
    rw [hls, hlt, hlen]
  have hjr : i + g < (places.rowList s).length := by rw [hls]; exact hj
  have hds : ∀ p, p + 1 < (places.rowList s).length →
      ground.getAt 0 (places.rowList s) (p + 1)
        ≤ ground.getAt 0 (places.rowList s) p :=
    fun p hp => places.rowList_le s p (by rw [← hls]; exact hp)
  have hdt : ∀ p, p + 1 < (places.rowList t).length →
      ground.getAt 0 (places.rowList t) (p + 1)
        ≤ ground.getAt 0 (places.rowList t) p :=
    fun p hp => places.rowList_le t p (by rw [← hlt]; exact hp)
  have hoffr : ∀ p, p < (places.rowList s).length → p ≠ i → p ≠ i + g →
      ground.getAt 0 (places.rowList t) p
        = ground.getAt 0 (places.rowList s) p :=
    fun p hp => hoff p (by rw [← hls]; exact hp)
  have hQs : qRows (places.rowList s) = c2hat.dfQ s := by
    show c2hat.sqGaps (places.rowList s)
        + (places.rowList s).length * c2hat.rho2 (places.rowList s)
      = c2hat.sqGaps (places.rowList s)
        + s.length * c2hat.rho2 (places.rowList s)
    rw [hls]
  have hQt : qRows (places.rowList t) = c2hat.dfQ t := by
    show c2hat.sqGaps (places.rowList t)
        + (places.rowList t).length * c2hat.rho2 (places.rowList t)
      = c2hat.sqGaps (places.rowList t)
        + t.length * c2hat.rho2 (places.rowList t)
    rw [hlt]
  have hfall := qRowsFall (places.rowList s) (places.rowList t) i g
    hml hjr hds hdt hi hg hoffr
  rw [hls, hQs, hQt] at hfall
  exact hfall

/-- The fall is strict: `Q` descends along every box move
(`lem:casfloor`). -/
theorem fallStrict (s t : places.Shape) (i g : Nat)
    (hlen : t.length = s.length)
    (hi : ground.getAt 0 (places.rowList t) i + 1
        = ground.getAt 0 (places.rowList s) i)
    (hg : ground.getAt 0 (places.rowList t) (i + g)
        = ground.getAt 0 (places.rowList s) (i + g) + 1)
    (hoff : ∀ p, p < s.length → p ≠ i → p ≠ i + g →
      ground.getAt 0 (places.rowList t) p
        = ground.getAt 0 (places.rowList s) p) :
    c2hat.dfQ t < c2hat.dfQ s := by
  have hj : i + g < s.length := by
    cases Nat.lt_or_ge (i + g) s.length with
    | inl h => exact h
    | inr h =>
      rw [getAt_default (places.rowList t) (i + g)
          (by rw [places.length_rowList, hlen]; exact h),
        getAt_default (places.rowList s) (i + g)
          (by rw [places.length_rowList]; exact h)] at hg
      exact Nat.noConfusion hg
  have hls : (places.rowList s).length = s.length := places.length_rowList s
  have hlt : (places.rowList t).length = t.length := places.length_rowList t
  have hml : (places.rowList t).length = (places.rowList s).length := by
    rw [hls, hlt, hlen]
  have hjr : i + g < (places.rowList s).length := by rw [hls]; exact hj
  have hds : ∀ p, p + 1 < (places.rowList s).length →
      ground.getAt 0 (places.rowList s) (p + 1)
        ≤ ground.getAt 0 (places.rowList s) p :=
    fun p hp => places.rowList_le s p (by rw [← hls]; exact hp)
  have hdt : ∀ p, p + 1 < (places.rowList t).length →
      ground.getAt 0 (places.rowList t) (p + 1)
        ≤ ground.getAt 0 (places.rowList t) p :=
    fun p hp => places.rowList_le t p (by rw [← hlt]; exact hp)
  have hoffr : ∀ p, p < (places.rowList s).length → p ≠ i → p ≠ i + g →
      ground.getAt 0 (places.rowList t) p
        = ground.getAt 0 (places.rowList s) p :=
    fun p hp => hoff p (by rw [← hls]; exact hp)
  have hQs : qRows (places.rowList s) = c2hat.dfQ s := by
    show c2hat.sqGaps (places.rowList s)
        + (places.rowList s).length * c2hat.rho2 (places.rowList s)
      = c2hat.sqGaps (places.rowList s)
        + s.length * c2hat.rho2 (places.rowList s)
    rw [hls]
  have hQt : qRows (places.rowList t) = c2hat.dfQ t := by
    show c2hat.sqGaps (places.rowList t)
        + (places.rowList t).length * c2hat.rho2 (places.rowList t)
      = c2hat.sqGaps (places.rowList t)
        + t.length * c2hat.rho2 (places.rowList t)
    rw [hlt]
  have hstrict := qRowsFall_lt (places.rowList s) (places.rowList t) i g
    hml hjr hds hdt hi hg hoffr
  rw [hQs, hQt] at hstrict
  exact hstrict

/-! The move pack: the box move `l ↦ bumpAt j (dipAt i l)` at the
last key at or above two and the first vacant key, its entry reads,
its descent, and the exit shapes. -/

/-- The last key at or above two sits below the length. -/
private theorem mv_ilen (l : List Nat) (i : Nat) (hbig : big2 l = i + 1) :
    i < l.length := by
  have h := big2_le_length l
  rw [hbig] at h
  exact h

/-- The last key at or above two reads at or above two. -/
private theorem mv_two (l : List Nat) (i : Nat)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hbig : big2 l = i + 1) : 2 ≤ ground.getAt 0 l i :=
  (big2_read l hdesc i (mv_ilen l i hbig)).mp
    (by rw [hbig]; exact Nat.lt_succ_self i)

/-- The lowered key sits strictly below the raised one. -/
private theorem mv_lt (l : List Nat) (i j : Nat)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hbig : big2 l = i + 1) (hpos : posLen l = j) : i < j := by
  have hil := mv_ilen l i hbig
  have h0 : 0 < ground.getAt 0 l i :=
    Nat.lt_of_lt_of_le (Nat.succ_pos 1) (mv_two l i hdesc hbig)
  rw [← hpos]
  exact (posLen_read l hdesc i hil).mpr h0

/-- The raised key sits below the length at a vacant last entry. -/
private theorem mv_jlen (l : List Nat) (k j : Nat) (hk : l.length = k + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l k = 0) (hpos : posLen l = j) :
    j < l.length := by
  have hkl : k < l.length := by rw [hk]; exact Nat.lt_succ_self k
  have hle : posLen l ≤ k := by
    cases Nat.lt_or_ge k (posLen l) with
    | inl h =>
      exact absurd ((posLen_read l hdesc k hkl).mp h)
        (by rw [hred]; exact Nat.lt_irrefl 0)
    | inr h => exact h
  rw [← hpos, hk]
  exact Nat.lt_succ_of_le hle

/-- The move's lowered key reads its entry dropped. -/
private theorem mv_hi (l : List Nat) (i j : Nat)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hbig : big2 l = i + 1) (hpos : posLen l = j) :
    ground.getAt 0 (ground.bumpAt j (dipAt i l)) i + 1
      = ground.getAt 0 l i := by
  have hij : i < j := mv_lt l i j hdesc hbig hpos
  have h2 := mv_two l i hdesc hbig
  rw [getAt_bumpAt_ne j (dipAt i l) i (Nat.ne_of_lt hij)]
  exact getAt_dipAt_self i l (Nat.le_trans (Nat.le_succ 1) h2)

/-- The move's raised key reads its entry raised. -/
private theorem mv_hg (l : List Nat) (k i j : Nat) (hk : l.length = k + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l k = 0) (hbig : big2 l = i + 1)
    (hpos : posLen l = j) :
    ground.getAt 0 (ground.bumpAt j (dipAt i l)) j
      = ground.getAt 0 l j + 1 := by
  have hjl : j < l.length := mv_jlen l k j hk hdesc hred hpos
  have hjD : j < (dipAt i l).length := by rw [length_dipAt]; exact hjl
  have hij : i < j := mv_lt l i j hdesc hbig hpos
  rw [getAt_bumpAt_self j (dipAt i l) hjD,
    getAt_dipAt_ne i l j (Nat.ne_of_lt hij).symm]

/-- The keys beyond the move read the family's own entries. -/
private theorem mv_off (l : List Nat) (i j : Nat) :
    ∀ p, p ≠ i → p ≠ j →
      ground.getAt 0 (ground.bumpAt j (dipAt i l)) p
        = ground.getAt 0 l p := by
  intro p hpi hpj
  rw [getAt_bumpAt_ne j (dipAt i l) p hpj, getAt_dipAt_ne i l p hpi]

/-- The move keeps the weak descent. -/
private theorem mv_desc (l : List Nat) (k i j : Nat) (hk : l.length = k + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l k = 0) (hbig : big2 l = i + 1)
    (hpos : posLen l = j) :
    ∀ p, p + 1 < (ground.bumpAt j (dipAt i l)).length →
      ground.getAt 0 (ground.bumpAt j (dipAt i l)) (p + 1)
        ≤ ground.getAt 0 (ground.bumpAt j (dipAt i l)) p := by
  have hij : i < j := mv_lt l i j hdesc hbig hpos
  have hjl : j < l.length := mv_jlen l k j hk hdesc hred hpos
  have h2 : 2 ≤ ground.getAt 0 l i := mv_two l i hdesc hbig
  have hmi : ground.getAt 0 (ground.bumpAt j (dipAt i l)) i + 1
      = ground.getAt 0 l i := mv_hi l i j hdesc hbig hpos
  have hmj : ground.getAt 0 (ground.bumpAt j (dipAt i l)) j
      = ground.getAt 0 l j + 1 := mv_hg l k i j hk hdesc hred hbig hpos
  have hmi1 : 1 ≤ ground.getAt 0 (ground.bumpAt j (dipAt i l)) i := by
    rw [← hmi] at h2
    exact Nat.le_of_succ_le_succ h2
  have hzj : ground.getAt 0 l j = 0 := by
    cases hx : ground.getAt 0 l j with
    | zero => rfl
    | succ b =>
      exfalso
      have hlt : j < posLen l :=
        (posLen_read l hdesc j hjl).mpr (by rw [hx]; exact Nat.succ_pos b)
      rw [hpos] at hlt
      exact Nat.lt_irrefl j hlt
  have hmlen : (ground.bumpAt j (dipAt i l)).length = l.length := by
    rw [length_bumpAt, length_dipAt]
  intro p hp
  rw [hmlen] at hp
  by_cases hpi : p = i
  · rw [hpi] at hp ⊢
    by_cases hij1 : i + 1 = j
    · rw [hij1, hmj, hzj]
      exact hmi1
    · have hne1 : i + 1 ≠ i :=
        fun h => Nat.lt_irrefl i (Nat.lt_of_lt_of_eq (Nat.lt_succ_self i) h)
      rw [mv_off l i j (i + 1) hne1 hij1]
      have hle1 : ground.getAt 0 l (i + 1) ≤ 1 := by
        cases Nat.lt_or_ge (ground.getAt 0 l (i + 1)) 2 with
        | inl h => exact Nat.le_of_lt_succ h
        | inr h =>
          exfalso
          have hb := (big2_read l hdesc (i + 1) hp).mpr h
          rw [hbig] at hb
          exact Nat.lt_irrefl (i + 1) hb
      exact Nat.le_trans hle1 hmi1
  · by_cases hpj : p = j
    · rw [hpj] at hp ⊢
      have hne2 : j + 1 ≠ i :=
        fun h => Nat.lt_irrefl i
          (Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt hij) h)
      have hne3 : j + 1 ≠ j :=
        fun h => Nat.lt_irrefl j (Nat.lt_of_lt_of_eq (Nat.lt_succ_self j) h)
      rw [mv_off l i j (j + 1) hne2 hne3, hmj, hzj]
      have hstep := hdesc j hp
      rw [hzj] at hstep
      exact Nat.le_trans hstep (Nat.zero_le _)
    · by_cases hq : p + 1 = i
      · rw [hq, mv_off l i j p hpi hpj]
        have hstep := hdesc p hp
        rw [hq] at hstep
        have h4 : ground.getAt 0 (ground.bumpAt j (dipAt i l)) i
            ≤ ground.getAt 0 l i := by
          rw [← hmi]; exact Nat.le_succ _
        exact Nat.le_trans h4 hstep
      · by_cases hq2 : p + 1 = j
        · rw [hq2, hmj, hzj, mv_off l i j p hpi hpj]
          have hpltj : p < j := by rw [← hq2]; exact Nat.lt_succ_self p
          have hpl : p < l.length := Nat.lt_trans hpltj hjl
          exact (posLen_read l hdesc p hpl).mp (by rw [hpos]; exact hpltj)
        · rw [mv_off l i j (p + 1) hq hq2, mv_off l i j p hpi hpj]
          exact hdesc p hp

/-- The move at the last key fills every entry. -/
private theorem mv_full (l : List Nat) (k i j : Nat) (hk : l.length = k + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l k = 0) (hbig : big2 l = i + 1)
    (hpos : posLen l = j) (hjk : j = k) :
    ∀ p, p < l.length →
      0 < ground.getAt 0 (ground.bumpAt j (dipAt i l)) p := by
  intro p hp
  by_cases hpi : p = i
  · rw [hpi]
    have h2 := mv_two l i hdesc hbig
    rw [← mv_hi l i j hdesc hbig hpos] at h2
    exact Nat.le_of_succ_le_succ h2
  · by_cases hpj : p = j
    · rw [hpj, mv_hg l k i j hk hdesc hred hbig hpos]
      exact Nat.succ_pos _
    · rw [mv_off l i j p hpi hpj]
      have hpk1 : p < k + 1 := by rw [← hk]; exact hp
      have hpk : p < k :=
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hpk1)
          (fun h => hpj (by rw [h, hjk]))
      have hpltj : p < j := by rw [hjk]; exact hpk
      exact (posLen_read l hdesc p hp).mp (by rw [hpos]; exact hpltj)

/-- The move short of the last key keeps the last entry vacant. -/
private theorem mv_tail_last (l : List Nat) (k i j : Nat)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l k = 0) (hbig : big2 l = i + 1)
    (hpos : posLen l = j) (hjk : j < k) :
    ground.getAt 0 (ground.bumpAt j (dipAt i l)) k = 0 := by
  have hij : i < j := mv_lt l i j hdesc hbig hpos
  rw [mv_off l i j k (Nat.ne_of_lt (Nat.lt_trans hij hjk)).symm
    (Nat.ne_of_lt hjk).symm]
  exact hred

/-- The move keeps the head occupied. -/
private theorem mv_head (l : List Nat) (i j : Nat)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hhead : 2 ≤ ground.getAt 0 l 0) (hbig : big2 l = i + 1)
    (hpos : posLen l = j) :
    0 < ground.getAt 0 (ground.bumpAt j (dipAt i l)) 0 := by
  by_cases h0 : i = 0
  · have h2 := mv_two l i hdesc hbig
    rw [← mv_hi l i j hdesc hbig hpos] at h2
    rw [h0] at h2 ⊢
    exact Nat.le_of_succ_le_succ h2
  · have hij : i < j := mv_lt l i j hdesc hbig hpos
    have hne0j : (0 : Nat) ≠ j := by
      intro h
      have hcon : i < 0 := by rw [h]; exact hij
      exact absurd hcon (Nat.not_lt_zero i)
    rw [mv_off l i j 0 (fun h => h0 h.symm) hne0j]
    exact Nat.lt_of_lt_of_le (Nat.succ_pos 1) hhead

/-! The unit exit: the move's family at every entry one, the walk's
last step, read against the endpoint's own value. -/

/-- A vacant total leaves every entry vacant. -/
private theorem sumNat_zero_getAt : ∀ (l : List Nat) (p : Nat),
    ground.sumNat l = 0 → ground.getAt 0 l p = 0
  | [], _, _ => rfl
  | x :: t, 0, h => by
    show x = 0
    exact Nat.eq_zero_of_add_eq_zero_right
      (show x + ground.sumNat t = 0 from h)
  | x :: t, p + 1, h => by
    show ground.getAt 0 t p = 0
    exact sumNat_zero_getAt t p
      (Nat.eq_zero_of_add_eq_zero_left (show x + ground.sumNat t = 0 from h))

/-- The vacant family's cleared read is vacant. -/
private theorem qRows_rep (n : Nat) : qRows (List.replicate n 0) = 0 := by
  show c2hat.sqGaps (List.replicate n 0)
      + (List.replicate n 0).length * c2hat.rho2 (List.replicate n 0) = 0
  rw [c2hat.sqGaps_zeros n, c2hat.rho2_zeros n, Nat.mul_zero]

/-- A family vacant at every key has a vacant cleared read. -/
private theorem qRows_zeros : ∀ (l : List Nat),
    (∀ p, p < l.length → ground.getAt 0 l p = 0) → qRows l = 0 := by
  intro l h
  have hl : l = List.replicate l.length 0 :=
    ground.replicate_of_zeros l h
  have hq := qRows_rep l.length
  rw [← hl] at hq
  exact hq

/-- An occupied total at a weak descent leaves the head occupied. -/
private theorem headPos_of_sum : ∀ (l : List Nat),
    (∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) →
    ground.sumNat l ≠ 0 → 0 < ground.getAt 0 l 0 := by
  intro l hdesc hs
  cases hx : ground.getAt 0 l 0 with
  | zero => exact absurd (sumNat_zero_of_headZero l hdesc hx) hs
  | succ b => exact Nat.succ_pos b

/-- The lowered family reads its entries dropped. -/
private theorem getAt_map_pred : ∀ (l : List Nat) (p : Nat),
    p < l.length →
    ground.getAt 0 (List.map (fun x => x - 1) l) p
      = ground.getAt 0 l p - 1 :=
  fun l p h => ground.getAt_map 0 0 (fun x => x - 1) l p h

/-- The full lowering keeps the weak descent. -/
private theorem descMap_pred : ∀ (l : List Nat),
    (∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) →
    ∀ p, p + 1 < (List.map (fun x => x - 1) l).length →
      ground.getAt 0 (List.map (fun x => x - 1) l) (p + 1)
        ≤ ground.getAt 0 (List.map (fun x => x - 1) l) p := by
  intro l hdesc p hp
  rw [ground.length_map] at hp
  rw [getAt_map_pred l (p + 1) hp,
    getAt_map_pred l p (Nat.lt_of_succ_lt hp)]
  exact Nat.sub_le_sub_right (hdesc p hp) 1

/-- The full lowering is a class read at an occupied family. -/
private theorem qRows_pred : ∀ (l : List Nat),
    (∀ p, p < l.length → 0 < ground.getAt 0 l p) →
    qRows (List.map (fun x => x - 1) l) = qRows l := by
  intro l hpos
  have h := qRows_shift (List.map (fun x => x - 1) l)
  rw [map_dip_bump l hpos] at h
  exact h.symm

/-- The walk's unit exit: a move whose lowered family is vacant sits
at the endpoint's own value. -/
private theorem unitExit (l : List Nat) (k i : Nat)
    (hk : l.length = k + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l k = 0)
    (hhead : 2 ≤ ground.getAt 0 l 0)
    (hbig : big2 l = i + 1)
    (hpos : posLen l = k)
    (hz : ground.sumNat (List.map (fun x => x - 1)
      (ground.bumpAt k (dipAt i l))) = 0) :
    qRows l = 2 * l.length * l.length := by
  have hmlen : (ground.bumpAt k (dipAt i l)).length = l.length := by
    rw [length_bumpAt, length_dipAt]
  have hfull := mv_full l k i k hk hdesc hred hbig hpos rfl
  have hone : ∀ p, p < l.length →
      ground.getAt 0 (ground.bumpAt k (dipAt i l)) p = 1 := by
    intro p hp
    have hz0 := sumNat_zero_getAt _ p hz
    rw [getAt_map_pred _ p (by rw [hmlen]; exact hp)] at hz0
    have hp0 := hfull p hp
    cases hx : ground.getAt 0 (ground.bumpAt k (dipAt i l)) p with
    | zero => rw [hx] at hp0; exact absurd hp0 (Nat.lt_irrefl 0)
    | succ b =>
      rw [hx] at hz0
      rw [show b = 0 from hz0]
  have hkl : k < l.length := by rw [hk]; exact Nat.lt_succ_self k
  have h0l : 0 < l.length := by rw [hk]; exact Nat.succ_pos k
  have hi0 : i = 0 := by
    by_cases h : i = 0
    · exact h
    · exfalso
      have hik : i < k := mv_lt l i k hdesc hbig hpos
      have hne0k : (0 : Nat) ≠ k := by
        intro hzk
        exact absurd (show i < 0 by rw [hzk]; exact hik) (Nat.not_lt_zero i)
      have h0 := hone 0 h0l
      rw [mv_off l i k 0 (fun he => h he.symm) hne0k] at h0
      rw [h0] at hhead
      exact absurd hhead (Nat.not_succ_le_self 1)
  subst hi0
  have hmk : ground.getAt 0 (ground.bumpAt k (dipAt 0 l)) k = 1 := hone k hkl
  have hm0 : ground.getAt 0 (ground.bumpAt k (dipAt 0 l)) 0 = 1 := hone 0 h0l
  have hl0 : ground.getAt 0 l 0 = 2 := by
    rw [← mv_hi l 0 k hdesc hbig hpos, hm0]
  have hqm : qRows (ground.bumpAt k (dipAt 0 l)) = 0 := by
    rw [← qRows_pred _ (fun p hp => hfull p (by rw [← hmlen]; exact hp))]
    exact qRows_zeros _ (fun p _ => sumNat_zero_getAt _ p hz)
  have hfall := qRowsFall l (ground.bumpAt k (dipAt 0 l)) 0 k hmlen
    (by rw [Nat.zero_add k, hk]; exact Nat.lt_succ_self k) hdesc
    (mv_desc l k 0 k hk hdesc hred hbig hpos)
    (mv_hi l 0 k hdesc hbig hpos)
    (by rw [Nat.zero_add k]; exact mv_hg l k 0 k hk hdesc hred hbig hpos)
    (fun p _ hpi hpj =>
      mv_off l 0 k p hpi (fun he => hpj (by rw [Nat.zero_add k]; exact he)))
  rw [Nat.zero_add k, hred, hmk, hm0, hl0, hqm, Nat.zero_add 1,
    Nat.mul_one l.length, Nat.left_distrib l.length 2 1,
    Nat.mul_one l.length,
    Nat.zero_add (l.length * 2 + l.length)] at hfall
  have hexp : 2 * l.length * l.length = 2 * l.length * k + 2 * l.length := by
    rw [hk, Nat.left_distrib (2 * (k + 1)) k 1, Nat.mul_one (2 * (k + 1))]
  rw [hexp]
  apply addCancelR l.length
  rw [hfall, Nat.mul_comm l.length 2,
    Nat.add_comm (2 * l.length + l.length) (2 * l.length * k),
    Nat.add_assoc (2 * l.length * k) (2 * l.length) l.length]

/-! `θ`'s own read: the unit-reaching step's value, the adjoint's
reduced shape at its row list. -/

/-- `θ`'s class read, `d_f Q(θ) = 2 d_f²`: the unit-reaching step's
own value (`lem:casfloor`), the tower law's `m = 1` instance
(`prop:anchor`). -/
theorem thetaRead (g : Nat) :
    c2hat.dfQ (adjchar.theta (g + 2)) = 2 * (g + 2) * (g + 2) := by
  have h := anchor.tower_dfQ (g + 2) 1 (Nat.le_add_left 2 g)
  rw [anchor.towerShape_one (g + 2)] at h
  rw [h]
  show 2 * (g + 2) * (1 * (1 + (g + 1))) = 2 * (g + 2) * (g + 2)
  rw [Nat.one_mul (1 + (g + 1)), Nat.add_comm 1 (g + 1)]

/-! The floor's walk (`lem:casfloor`): the strong induction on the
fall's own measure.  A reduced occupied row list at head one is a
one-column list, the endpoint read; at head two or beyond it
moves, the target's measure strictly below, the raised-last-key
step re-entering through the lowered family with the unit exit
reading `θ`'s value. -/

private theorem floorShuffle (x y : Nat) :
    x + x + (y + y) + 2 = x + y + (x + y + 2) := by
  rw [Nat.add_assoc x x (y + y), ← Nat.add_assoc x y y,
    Nat.add_comm (x + y) y, ← Nat.add_assoc x y (x + y),
    Nat.add_assoc (x + y) (x + y) 2]

private theorem floorGap (r : Nat) :
    2 * (r + 1) * (r + 1) = r * (r + 2) + (r * r + 2 * r + 2) := by
  rw [mulAssoc 2 (r + 1) (r + 1), sqUp r,
    Nat.left_distrib 2 (r * r + 2 * r) 1, Nat.mul_one 2,
    Nat.left_distrib 2 (r * r) (2 * r), Nat.two_mul (r * r),
    Nat.two_mul (2 * r), Nat.left_distrib r r 2, Nat.mul_comm r 2]
  exact floorShuffle (r * r) (2 * r)

/-- An occupied one-column row list is the unit family at its
occupied keys: the head at most one forces every occupied key to
one, the occupied count within the residue, the vacant tail its
complement. -/
private theorem onesSplit (r : Nat) (l : List Nat)
    (hlen : l.length = r + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l r = 0)
    (hocc : 0 < ground.getAt 0 l 0)
    (h1 : ground.getAt 0 l 0 ≤ 1) :
    ∃ a b : Nat, l = ground.onesRows (a + 1) (b + 1)
      ∧ a + 1 + (b + 1) = r + 1 := by
  cases hj : posLen l with
  | zero =>
    have h0 : 0 < posLen l :=
      (posLen_read l hdesc 0 (by rw [hlen]; exact Nat.succ_pos r)).mpr hocc
    rw [hj] at h0
    exact absurd h0 (Nat.lt_irrefl 0)
  | succ a =>
    have hones := ones_of_headLe l hdesc h1
    rw [hj] at hones
    have hler : posLen l ≤ r := by
      cases Nat.lt_or_ge r (posLen l) with
      | inl h =>
        exact absurd
          ((posLen_read l hdesc r
            (by rw [hlen]; exact Nat.lt_succ_self r)).mp h)
          (by rw [hred]; exact Nat.lt_irrefl 0)
      | inr h => exact h
    rw [hj] at hler
    have hjg : a + 1 + (l.length - (a + 1)) = l.length := by
      rw [← hj]
      exact ground.natAddSubCancel (posLen_le_length l)
    cases hg2 : l.length - (a + 1) with
    | zero =>
      rw [hg2, Nat.add_zero] at hjg
      rw [hjg, hlen] at hler
      exact absurd hler (Nat.not_succ_le_self r)
    | succ b =>
      rw [hg2] at hones hjg
      rw [hlen] at hjg
      exact ⟨a, b, hones, hjg⟩

/-- The endpoint case: a one-column row list reads the display
`j g_j (r + 2)` at or above the floor, the equality at the two
attained keys alone. -/
private theorem floorOnes (r : Nat) (l : List Nat)
    (hlen : l.length = r + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l r = 0)
    (hocc : 0 < ground.getAt 0 l 0)
    (h1 : ground.getAt 0 l 0 ≤ 1) :
    r * (r + 2) ≤ qRows l ∧
      (qRows l = r * (r + 2) →
        l = ground.onesRows 1 r ∨ l = ground.onesRows r 1) := by
  match onesSplit r l hlen hdesc hred hocc h1 with
  | ⟨a, b, hones, hjg⟩ =>
    have hab : a + b + 1 = r := by
      have h2 : a + b + 1 + 1 = r + 1 := by
        rw [← hjg, Nat.add_assoc a 1 (b + 1),
          Nat.add_comm 1 (b + 1), ← Nat.add_assoc a (b + 1) 1,
          ← Nat.add_assoc a b 1]
      exact Nat.succ.inj h2
    have hval : qRows l = (a + 1) * (b + 1) * (r + 2) := by
      rw [hones, qRows_ones (a + 1) (b + 1)]
      rw [show a + 1 + (b + 1) + 1 = r + 2 from congrArg (· + 1) hjg]
    constructor
    · rw [hval]
      have hle : r ≤ (a + 1) * (b + 1) := by
        rw [← hab]
        exact endpointLeast a b
      exact Nat.mul_le_mul_right (r + 2) hle
    · intro heq
      rw [hval] at heq
      have hjgr : (a + 1) * (b + 1) = r :=
        Nat.eq_of_mul_eq_mul_right (Nat.succ_pos (r + 1)) heq
      cases endpointLeast_eq a b (hjgr.trans hab.symm) with
      | inl ha =>
        rw [ha] at hones hab
        rw [Nat.zero_add] at hones hab
        rw [hab] at hones
        exact Or.inl hones
      | inr hb0 =>
        rw [hb0] at hones hab
        rw [Nat.add_zero] at hab
        rw [Nat.zero_add] at hones
        rw [hab] at hones
        exact Or.inr hones

/-- The box move's walk data at one bundle: the moved family keeps
the length, the descent and the last key's read, drops the square
fold strictly, and its move key sits within the residue. -/
private theorem mvStep (r i : Nat) (l : List Nat)
    (hlen : l.length = r + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l r = 0)
    (hb : big2 l = i + 1) :
    (ground.bumpAt (posLen l) (dipAt i l)).length = l.length
    ∧ (∀ p, p + 1 < (ground.bumpAt (posLen l) (dipAt i l)).length →
        ground.getAt 0 (ground.bumpAt (posLen l) (dipAt i l)) (p + 1)
          ≤ ground.getAt 0 (ground.bumpAt (posLen l) (dipAt i l)) p)
    ∧ ground.getAt 0 (ground.bumpAt (posLen l) (dipAt i l))
          (posLen l)
        = ground.getAt 0 l (posLen l) + 1
    ∧ qRows (ground.bumpAt (posLen l) (dipAt i l)) < qRows l
    ∧ posLen l ≤ r := by
  have hij : i < posLen l := mv_lt l i (posLen l) hdesc hb rfl
  have hjl : posLen l < l.length :=
    mv_jlen l r (posLen l) hlen hdesc hred rfl
  have hgap : i + (posLen l - i) = posLen l :=
    ground.natAddSubCancel (Nat.le_of_lt hij)
  have hmlen : (ground.bumpAt (posLen l) (dipAt i l)).length
      = l.length := by rw [length_bumpAt, length_dipAt]
  have hmdesc := mv_desc l r i (posLen l) hlen hdesc hred hb rfl
  have hmi := mv_hi l i (posLen l) hdesc hb rfl
  have hmg := mv_hg l r i (posLen l) hlen hdesc hred hb rfl
  have hqlt : qRows (ground.bumpAt (posLen l) (dipAt i l))
      < qRows l :=
    qRowsFall_lt l (ground.bumpAt (posLen l) (dipAt i l)) i
      (posLen l - i) hmlen
      (by rw [hgap]; exact hjl) hdesc hmdesc hmi
      (by rw [hgap]; exact hmg)
      (fun p _ hpi hpj =>
        mv_off l i (posLen l) p hpi (by rw [hgap] at hpj; exact hpj))
  have hler : posLen l ≤ r := by
    cases Nat.lt_or_ge r (posLen l) with
    | inl h =>
      exact absurd
        ((posLen_read l hdesc r
    (by rw [hlen]; exact Nat.lt_succ_self r)).mp h)
        (by rw [hred]; exact Nat.lt_irrefl 0)
    | inr h => exact h
  exact ⟨hmlen, hmdesc, hmg, hqlt, hler⟩

private theorem floorRows : ∀ (n r : Nat) (l : List Nat),
    qRows l < n → l.length = r + 1 →
    (∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) →
    ground.getAt 0 l r = 0 → 0 < ground.getAt 0 l 0 →
    r * (r + 2) ≤ qRows l ∧
      (qRows l = r * (r + 2) →
        l = ground.onesRows 1 r ∨ l = ground.onesRows r 1) := by
  intro n
  induction n with
  | zero =>
    intro r l hn _ _ _ _
    exact absurd hn (Nat.not_lt_zero _)
  | succ n' ih =>
    intro r l hn hlen hdesc hred hocc
    cases Nat.lt_or_ge (ground.getAt 0 l 0) 2 with
    | inl h1 =>
      exact floorOnes r l hlen hdesc hred hocc (Nat.le_of_lt_succ h1)
    | inr hhead =>
      have hbigpos : 0 < big2 l :=
        (big2_read l hdesc 0 (by rw [hlen]; exact Nat.succ_pos r)).mpr
          hhead
      cases hb : big2 l with
      | zero => rw [hb] at hbigpos; exact absurd hbigpos (Nat.lt_irrefl 0)
      | succ i =>
        match mvStep r i l hlen hdesc hred hb with
        | ⟨hmlen, hmdesc, hmg, hqlt, hler⟩ =>
        cases Nat.lt_or_ge (posLen l) r with
        | inl hjr =>
          have hres := ih r (ground.bumpAt (posLen l) (dipAt i l))
            (Nat.lt_of_lt_of_le hqlt (Nat.le_of_lt_succ hn))
            (hmlen.trans hlen) hmdesc
            (mv_tail_last l r i (posLen l) hdesc hred hb rfl hjr)
            (mv_head l i (posLen l) hdesc hhead hb rfl)
          refine ⟨Nat.le_of_lt (Nat.lt_of_le_of_lt hres.1 hqlt),
            fun heq => ?_⟩
          rw [heq] at hqlt
          exact absurd (Nat.lt_of_le_of_lt hres.1 hqlt) (Nat.lt_irrefl _)
        | inr hrj =>
          have hjr : posLen l = r := Nat.le_antisymm hler hrj
          rw [hjr] at hmlen hmdesc hmg hqlt
          by_cases hz : ground.sumNat (List.map (fun x => x - 1)
              (ground.bumpAt r (dipAt i l))) = 0
          · have hql : qRows l = 2 * l.length * l.length :=
              unitExit l r i hlen hdesc hred hhead hb hjr hz
            rw [hlen] at hql
            constructor
            · rw [hql, floorGap r]
              exact Nat.le_add_right _ _
            · intro heq
              rw [heq, floorGap r] at hql
              have h0 : (0 : Nat) = r * r + 2 * r + 2 :=
                addCancelL (r * (r + 2))
                  (by rw [Nat.add_zero]; exact hql)
              exact Nat.noConfusion h0
          · have hfull := mv_full l r i (posLen l) hlen hdesc hred hb
              rfl hjr
            rw [hjr] at hfull
            have hfull' : ∀ p,
                p < (ground.bumpAt r (dipAt i l)).length →
                0 < ground.getAt 0 (ground.bumpAt r (dipAt i l)) p :=
              fun p hp => hfull p (by rw [← hmlen]; exact hp)
            have hd' := descMap_pred (ground.bumpAt r (dipAt i l)) hmdesc
            have hlast : ground.getAt 0 (List.map (fun x => x - 1)
                (ground.bumpAt r (dipAt i l))) r = 0 := by
              rw [getAt_map_pred (ground.bumpAt r (dipAt i l)) r
                (by rw [hmlen, hlen]; exact Nat.lt_succ_self r)]
              rw [hmg, hred]
            have hres := ih r
              (List.map (fun x => x - 1) (ground.bumpAt r (dipAt i l)))
              (by rw [qRows_pred (ground.bumpAt r (dipAt i l)) hfull']
                  exact Nat.lt_of_lt_of_le hqlt (Nat.le_of_lt_succ hn))
              (by rw [ground.length_map, hmlen, hlen])
              hd' hlast
              (headPos_of_sum
                (List.map (fun x => x - 1) (ground.bumpAt r (dipAt i l)))
                hd' hz)
            have hqlt' : qRows (List.map (fun x => x - 1)
                (ground.bumpAt r (dipAt i l))) < qRows l := by
              rw [qRows_pred (ground.bumpAt r (dipAt i l)) hfull']
              exact hqlt
            refine ⟨Nat.le_of_lt (Nat.lt_of_le_of_lt hres.1 hqlt'),
              fun heq => ?_⟩
            rw [heq] at hqlt'
            exact absurd (Nat.lt_of_le_of_lt hres.1 hqlt')
              (Nat.lt_irrefl _)

/-- The descent's move, produced: at a reduced weakly-descending
row list holding an entry at or beyond two, the box move at the
last such key against the leading occupied count's own key — the
moved list kept weakly descending at the stated length, the two
moved keys' reads the fall identity's own binders, and the moved
keys ordered inside the reduced range (`lem:casfloor`'s moves, the
producer the floor walk's own step). -/
theorem boxMove (r : Nat) (l : List Nat)
    (hlen : l.length = r + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l r = 0)
    (k : Nat) (hk : k < l.length) (hk2 : 2 ≤ ground.getAt 0 l k) :
    ∃ i g, 0 < g ∧ i + g ≤ r
      ∧ 2 ≤ ground.getAt 0 l i
      ∧ (ground.bumpAt (i + g) (dipAt i l)).length = l.length
      ∧ (∀ p, p + 1 < (ground.bumpAt (i + g) (dipAt i l)).length →
          ground.getAt 0 (ground.bumpAt (i + g) (dipAt i l)) (p + 1)
            ≤ ground.getAt 0 (ground.bumpAt (i + g) (dipAt i l)) p)
      ∧ ground.getAt 0 (ground.bumpAt (i + g) (dipAt i l)) i + 1
          = ground.getAt 0 l i
      ∧ ground.getAt 0 (ground.bumpAt (i + g) (dipAt i l)) (i + g)
          = ground.getAt 0 l (i + g) + 1
      ∧ (∀ p, ¬ p = i → ¬ p = i + g →
          ground.getAt 0 (ground.bumpAt (i + g) (dipAt i l)) p
            = ground.getAt 0 l p) := by
  have hbigpos : 0 < big2 l :=
    Nat.lt_of_le_of_lt (Nat.zero_le k) ((big2_read l hdesc k hk).mpr hk2)
  match hb : big2 l with
  | 0 => exact absurd (hb ▸ hbigpos) (Nat.lt_irrefl 0)
  | i + 1 =>
    have hstep := mvStep r i l hlen hdesc hred hb
    have hij : i < posLen l := mv_lt l i (posLen l) hdesc hb rfl
    have hgap : i + (posLen l - i) = posLen l :=
      ground.natAddSubCancel (Nat.le_of_lt hij)
    have hgpos : 0 < posLen l - i := by
      match hg : posLen l - i with
      | 0 =>
        rw [hg, Nat.add_zero] at hgap
        exact absurd hgap (Nat.ne_of_lt hij)
      | n + 1 => exact Nat.succ_pos n
    have hil : i < l.length := mv_ilen l i hb
    have h2i : 2 ≤ ground.getAt 0 l i := mv_two l i hdesc hb
    refine ⟨i, posLen l - i, hgpos, ?_, h2i, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hgap]
      exact hstep.2.2.2.2
    · rw [hgap]
      exact hstep.1
    · rw [hgap]
      exact hstep.2.1
    · rw [hgap]
      have hne : ¬ i = posLen l := Nat.ne_of_lt hij
      rw [ground.getAt_bumpAt_ne (posLen l) (dipAt i l) i hne,
        ground.getAt_dipAt i l]
      exact ground.subAdd
        (Nat.le_trans (Nat.le_succ 1) h2i)
    · rw [hgap]
      exact hstep.2.2.1
    · intro p hpi hpg
      rw [hgap] at hpg ⊢
      rw [ground.getAt_bumpAt_ne (posLen l) (dipAt i l) p hpg,
        ground.getAt_dipAt_ne i l p hpi]

/-- Every nonunit label sits at or above the floor: a reduced
occupied shape at `d_f = r + 1` reads `r (r + 2) ≤ d_f Q(λ)`, the
cleared comparison of `ĉ₂(λ) ≥ ĉ₂(f) = [r (r + 2) : 2 d_f²]` at
the shared second member (`lem:casfloor`). -/
theorem floorAll (r : Nat) (s : places.Shape)
    (hlen : s.length = r + 1) (hred : ground.getAt 0 s r = 0)
    (hocc : 0 < ground.sumNat s) :
    r * (r + 2) ≤ c2hat.dfQ s := by
  have hq : c2hat.dfQ s = qRows (places.rowList s) := by
    show c2hat.sqGaps (places.rowList s)
        + s.length * c2hat.rho2 (places.rowList s)
      = c2hat.sqGaps (places.rowList s)
        + (places.rowList s).length * c2hat.rho2 (places.rowList s)
    rw [places.length_rowList]
  have hne : s ≠ [] := by
    intro h
    rw [h] at hlen
    exact Nat.noConfusion hlen
  rw [hq]
  exact (floorRows (qRows (places.rowList s) + 1) r (places.rowList s)
    (Nat.lt_succ_self _)
    ((places.length_rowList s).trans hlen)
    (fun p hp => places.rowList_le s p
      (by rw [places.length_rowList] at hp; exact hp))
    ((rowLast_read s r hlen).trans hred)
    (by rw [rowHead_read s hne]; exact hocc)).1

/-- The floor's equality sits at `f` and `f̄` alone
(`lem:casfloor`; the attained direction is `endpointAll`'s two
instances). -/
theorem floorSharp (r : Nat) (s : places.Shape)
    (hlen : s.length = r + 1) (hred : ground.getAt 0 s r = 0)
    (hocc : 0 < ground.sumNat s)
    (heq : c2hat.dfQ s = r * (r + 2)) :
    s = fundShape 1 r ∨ s = fundShape r 1 := by
  have hq : c2hat.dfQ s = qRows (places.rowList s) := by
    show c2hat.sqGaps (places.rowList s)
        + s.length * c2hat.rho2 (places.rowList s)
      = c2hat.sqGaps (places.rowList s)
        + (places.rowList s).length * c2hat.rho2 (places.rowList s)
    rw [places.length_rowList]
  have hne : s ≠ [] := by
    intro h
    rw [h] at hlen
    exact Nat.noConfusion hlen
  cases (floorRows (qRows (places.rowList s) + 1) r (places.rowList s)
      (Nat.lt_succ_self _)
      ((places.length_rowList s).trans hlen)
      (fun p hp => places.rowList_le s p
        (by rw [places.length_rowList] at hp; exact hp))
      ((rowLast_read s r hlen).trans hred)
      (by rw [rowHead_read s hne]; exact hocc)).2
      (by rw [← hq]; exact heq) with
  | inl h =>
    exact Or.inl (places.rowList_inj s (fundShape 1 r)
      (h.trans (rowList_fund 1 r).symm))
  | inr h =>
    exact Or.inr (places.rowList_inj s (fundShape r 1)
      (h.trans (rowList_fund r 1).symm))

/-! The per-class floor (`lem:chargedcell`(ii)'s endpoint read):
the descent refined at the class.  The box move and the full
lowering both keep the degree's remainder at the fundamental
count, so a walk seeded off the unit class never exits at the unit
— the unit exit reads the degree at one full column, class zero —
and ends at the unit family of its own class, whose value is the
endpoint display `c (d_f − c) (r + 2)`. -/


/-- The unit family's total is its occupied block's count. -/
private theorem sumNat_ones : ∀ j g : Nat,
    ground.sumNat (ground.onesRows j g) = j
  | 0, g => by
    show ground.sumNat (List.replicate 0 1 ++ List.replicate g 0) = 0
    exact ground.sumNat_replicate_zero g
  | j + 1, g => by
    show 1 + ground.sumNat (List.replicate j 1 ++ List.replicate g 0)
      = j + 1
    rw [show ground.sumNat (List.replicate j 1 ++ List.replicate g 0)
        = j from sumNat_ones j g, Nat.add_comm 1 j]

/-- The full lowering withdraws one box per key at an occupied
family. -/
private theorem sumNat_pred_add : ∀ (l : List Nat),
    (∀ p, p < l.length → 0 < ground.getAt 0 l p) →
    ground.sumNat (List.map (fun x => x - 1) l) + l.length
      = ground.sumNat l
  | [], _ => rfl
  | x :: t, hpos => by
    have hx : 0 < x := hpos 0 (Nat.succ_pos t.length)
    have hih := sumNat_pred_add t
      (fun p hp => hpos (p + 1) (Nat.succ_lt_succ hp))
    cases x with
    | zero => exact absurd hx (Nat.lt_irrefl 0)
    | succ b =>
      show b + ground.sumNat (List.map (fun x => x - 1) t)
          + (t.length + 1)
        = b + 1 + ground.sumNat t
      rw [← hih, Nat.add_add_add_comm b 1
          (ground.sumNat (List.map (fun x => x - 1) t)) t.length,
        Nat.add_comm 1 t.length]


/-- The endpoint case at a stated class: a one-column row list of
class `c` is the unit family at `c` occupied keys, whose cleared
read is the endpoint display itself. -/
private theorem floorOnesCls (r c : Nat) (l : List Nat)
    (hlen : l.length = r + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l r = 0)
    (h1 : ground.getAt 0 l 0 ≤ 1)
    (hcls : ground.sumNat l % (r + 1) = c) (hc : 0 < c) :
    c * (r + 1 - c) * (r + 2) ≤ qRows l := by
  have hocc : 0 < ground.getAt 0 l 0 := by
    cases hx : ground.getAt 0 l 0 with
    | zero =>
      exfalso
      have hz : (0 : Nat) = c := by
        rw [← hcls, sumNat_zero_of_headZero l hdesc hx,
          ground.modZeroLeft (r + 1)]
      rw [← hz] at hc
      exact absurd hc (Nat.lt_irrefl 0)
    | succ b => exact Nat.succ_pos b
  match onesSplit r l hlen hdesc hred hocc h1 with
  | ⟨a, b, hones, hjg⟩ =>
    have hle1 : a + 1 ≤ r + 1 := by
      rw [← hjg]
      exact Nat.le_add_right (a + 1) (b + 1)
    have hler : a + 1 ≤ r := by
      refine Nat.le_of_lt_succ ?_
      show a + 1 < r + 1
      rw [← hjg]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos b)
    have hca : c = a + 1 := by
      rw [← hcls, hones, sumNat_ones (a + 1) (b + 1)]
      exact ground.modOfLt (a + 1) (r + 1) (Nat.lt_succ_of_le hler)
    have hsub : r + 1 - (a + 1) = b + 1 :=
      ground.addCancelL (a + 1)
        ((ground.natAddSubCancel hle1).trans hjg.symm)
    have hval : qRows l = (a + 1) * (b + 1) * (r + 2) := by
      rw [hones, qRows_ones (a + 1) (b + 1)]
      rw [show a + 1 + (b + 1) + 1 = r + 2 from congrArg (· + 1) hjg]
    have hfin : c * (r + 1 - c) * (r + 2) = qRows l := by
      rw [hca, hsub, hval]
    exact Nat.le_of_eq hfin


/-- An occupied one-column row list refuses the unit class: its
occupied count sits within the residue and above the vacuum, so
its degree's remainder is its own occupied read. -/
private theorem floorOnesUnit (r : Nat) (l : List Nat)
    (hlen : l.length = r + 1)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p)
    (hred : ground.getAt 0 l r = 0)
    (hocc : 0 < ground.getAt 0 l 0)
    (h1 : ground.getAt 0 l 0 ≤ 1)
    (hcls : ground.sumNat l % (r + 1) = 0) : False := by
  match onesSplit r l hlen hdesc hred hocc h1 with
  | ⟨a, b, hones, hjg⟩ =>
    have hler : a + 1 ≤ r := by
      refine Nat.le_of_lt_succ ?_
      show a + 1 < r + 1
      rw [← hjg]
      exact Nat.lt_add_of_pos_right (Nat.succ_pos b)
    have hsum : ground.sumNat l = a + 1 := by
      rw [hones]
      exact sumNat_ones (a + 1) (b + 1)
    rw [hsum, ground.modOfLt (a + 1) (r + 1)
      (Nat.lt_succ_of_le hler)] at hcls
    exact Nat.noConfusion hcls

/-- The per-class walk, one strong induction at both arms: the box
move and the full lowering both keep the degree's remainder at the
fundamental count, so a walk at a nonunit class ends at the unit
family of its own class while one at the unit class exits at the
unit label — the endpoint reading the class's one-column value and
the exit the unit-reaching step's own `2 d_f²`. -/
private theorem floorRowsAt : ∀ (n r c : Nat) (l : List Nat),
    qRows l < n → l.length = r + 1 →
    (∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) →
    ground.getAt 0 l r = 0 →
    ground.sumNat l % (r + 1) = c → 0 < ground.getAt 0 l 0 →
    (if c == 0 then 2 * ((r + 1) * (r + 1))
      else c * (r + 1 - c) * (r + 2)) ≤ qRows l := by
  intro n
  induction n with
  | zero =>
    intro r c l hn _ _ _ _ _
    exact absurd hn (Nat.not_lt_zero _)
  | succ n' ih =>
    intro r c l hn hlen hdesc hred hcls hocc
    cases Nat.lt_or_ge (ground.getAt 0 l 0) 2 with
    | inl h1 =>
      cases c with
      | zero =>
        exact (floorOnesUnit r l hlen hdesc hred hocc
          (Nat.le_of_lt_succ h1) hcls).elim
      | succ c' =>
        show (c' + 1) * (r + 1 - (c' + 1)) * (r + 2) ≤ qRows l
        exact floorOnesCls r (c' + 1) l hlen hdesc hred
          (Nat.le_of_lt_succ h1) hcls (Nat.succ_pos c')
    | inr hhead =>
      have hbigpos : 0 < big2 l :=
        (big2_read l hdesc 0 (by rw [hlen]; exact Nat.succ_pos r)).mpr
          hhead
      cases hb : big2 l with
      | zero => rw [hb] at hbigpos; exact absurd hbigpos (Nat.lt_irrefl 0)
      | succ i =>
        match mvStep r i l hlen hdesc hred hb with
        | ⟨hmlen, hmdesc, hmg, hqlt, hler⟩ =>
        have hjl : posLen l < l.length :=
          mv_jlen l r (posLen l) hlen hdesc hred rfl
        have hocci : 0 < ground.getAt 0 l i :=
          Nat.lt_of_lt_of_le (Nat.succ_pos 1) (mv_two l i hdesc hb)
        have hsum : ground.sumNat (ground.bumpAt (posLen l) (dipAt i l))
            = ground.sumNat l := ground.sumNat_move i (posLen l) l hocci hjl
        cases Nat.lt_or_ge (posLen l) r with
        | inl hjr =>
          have hres := ih r c (ground.bumpAt (posLen l) (dipAt i l))
            (Nat.lt_of_lt_of_le hqlt (Nat.le_of_lt_succ hn))
            (hmlen.trans hlen) hmdesc
            (mv_tail_last l r i (posLen l) hdesc hred hb rfl hjr)
            (by rw [hsum]; exact hcls)
            (mv_head l i (posLen l) hdesc hhead hb rfl)
          exact Nat.le_of_lt (Nat.lt_of_le_of_lt hres hqlt)
        | inr hrj =>
          have hjr : posLen l = r := Nat.le_antisymm hler hrj
          rw [hjr] at hmlen hmdesc hmg hqlt hsum
          have hfull := mv_full l r i (posLen l) hlen hdesc hred hb
            rfl hjr
          rw [hjr] at hfull
          have hfull' : ∀ p,
              p < (ground.bumpAt r (dipAt i l)).length →
              0 < ground.getAt 0 (ground.bumpAt r (dipAt i l)) p :=
            fun p hp => hfull p (by rw [← hmlen]; exact hp)
          have hpa := sumNat_pred_add (ground.bumpAt r (dipAt i l)) hfull'
          rw [hmlen, hlen, hsum] at hpa
          by_cases hz : ground.sumNat (List.map (fun x => x - 1)
              (ground.bumpAt r (dipAt i l))) = 0
          · cases c with
            | zero =>
              have hql : qRows l = 2 * l.length * l.length :=
                unitExit l r i hlen hdesc hred hhead hb hjr hz
              show 2 * ((r + 1) * (r + 1)) ≤ qRows l
              exact Nat.le_of_eq
                (by rw [hql, hlen, mulAssoc 2 (r + 1) (r + 1)])
            | succ c' =>
              exfalso
              rw [hz, Nat.zero_add] at hpa
              have h0 : (r + 1) % (r + 1) = 0 := by
                have hm := ground.modMulSelf 1 (r + 1)
                rw [Nat.one_mul] at hm
                exact hm
              rw [← hpa, h0] at hcls
              exact Nat.noConfusion hcls
          · have hd' := descMap_pred (ground.bumpAt r (dipAt i l)) hmdesc
            have hlast : ground.getAt 0 (List.map (fun x => x - 1)
                (ground.bumpAt r (dipAt i l))) r = 0 := by
              rw [getAt_map_pred (ground.bumpAt r (dipAt i l)) r
                (by rw [hmlen, hlen]; exact Nat.lt_succ_self r)]
              rw [hmg, hred]
            have hclsp : ground.sumNat (List.map (fun x => x - 1)
                (ground.bumpAt r (dipAt i l))) % (r + 1) = c := by
              rw [← hcls, ← hpa,
                show ground.sumNat (List.map (fun x => x - 1)
                      (ground.bumpAt r (dipAt i l))) + (r + 1)
                    = ground.sumNat (List.map (fun x => x - 1)
                      (ground.bumpAt r (dipAt i l))) + 1 * (r + 1)
                  from by rw [Nat.one_mul]]
              exact (ground.modAddMul _ 1 (r + 1)).symm
            have hqlt' : qRows (List.map (fun x => x - 1)
                (ground.bumpAt r (dipAt i l))) < qRows l := by
              rw [qRows_pred (ground.bumpAt r (dipAt i l)) hfull']
              exact hqlt
            have hres := ih r c
              (List.map (fun x => x - 1) (ground.bumpAt r (dipAt i l)))
              (Nat.lt_of_lt_of_le hqlt' (Nat.le_of_lt_succ hn))
              (by rw [ground.length_map, hmlen, hlen])
              hd' hlast hclsp
              (headPos_of_sum
                (List.map (fun x => x - 1) (ground.bumpAt r (dipAt i l)))
                hd' hz)
            exact Nat.le_of_lt (Nat.lt_of_le_of_lt hres hqlt')

/-- Every shape reads its class's endpoint floor: a reduced shape
at `d_f = r + 1` whose degree sits at the nonunit class `c` reads
`c (d_f − c) (r + 2) ≤ d_f Q(λ)`, the descent refined per class
(`lem:chargedcell`(ii)). -/
theorem classFloor (r c : Nat) (s : places.Shape)
    (hlen : s.length = r + 1) (hred : ground.getAt 0 s r = 0)
    (hcls : places.degree s % (r + 1) = c) :
    c * (r + 1 - c) * (r + 2) ≤ c2hat.dfQ s := by
  cases hc : c with
  | zero =>
    rw [Nat.zero_mul, Nat.zero_mul]
    exact Nat.zero_le _
  | succ c' =>
    have hq : c2hat.dfQ s = qRows (places.rowList s) := by
      show c2hat.sqGaps (places.rowList s)
          + s.length * c2hat.rho2 (places.rowList s)
        = c2hat.sqGaps (places.rowList s)
          + (places.rowList s).length * c2hat.rho2 (places.rowList s)
      rw [places.length_rowList]
    have hdescl : ∀ p, p + 1 < (places.rowList s).length →
        ground.getAt 0 (places.rowList s) (p + 1)
          ≤ ground.getAt 0 (places.rowList s) p :=
      fun p hp => places.rowList_le s p
        (by rw [places.length_rowList] at hp; exact hp)
    have hclsl : ground.sumNat (places.rowList s) % (r + 1)
        = c' + 1 := by
      rw [← hc]
      exact hcls
    have hne0 : ground.sumNat (places.rowList s) ≠ 0 := by
      intro h0
      rw [h0, ground.modZeroLeft (r + 1)] at hclsl
      exact Nat.noConfusion hclsl
    rw [hq]
    show (if (c' + 1) == 0 then 2 * ((r + 1) * (r + 1))
      else (c' + 1) * (r + 1 - (c' + 1)) * (r + 2))
      ≤ qRows (places.rowList s)
    exact floorRowsAt (qRows (places.rowList s) + 1) r (c' + 1)
      (places.rowList s) (Nat.lt_succ_self _)
      ((places.length_rowList s).trans hlen) hdescl
      ((rowLast_read s r hlen).trans hred) hclsl
      (headPos_of_sum (places.rowList s) hdescl hne0)

/-- The class floors clear the fundamental's: at a nonunit class
within the residue the endpoint display sits at or above the
fundamental loop's own read, the display's second arm
(`lem:chargedcell`(ii)). -/
theorem classFloor_fund (r c : Nat) (hc : 0 < c) (hcr : c ≤ r) :
    r * (r + 2) ≤ c * (r + 1 - c) * (r + 2) := by
  refine Nat.mul_le_mul_right (r + 2) ?_
  match c, hc with
  | a + 1, _ =>
    match Nat.le.dest hcr with
    | ⟨b, hb⟩ =>
      have hgap : r + 1 - (a + 1) = b + 1 := by
        rw [← hb, Nat.add_assoc (a + 1) b 1,
          ground.addSubSelfL (a + 1) (b + 1)]
      rw [hgap, ← hb, Nat.add_right_comm a 1 b]
      exact endpointLeast a b

/-- The unit class's own floor: a reduced occupied shape at
`d_f = r + 1` whose degree reads the unit class clears
`2 d_f² ≤ d_f Q(λ)`, the walk's unit-reaching step — a constant row
list moved by one box, `θ`'s class, at `d_f Q(θ) = 2 d_f²`
(`lem:casfloor`) — and the consumer's least nonunit read at the
unit class (`lem:chargedcell`(iii)). -/
theorem unitClassFloor (r : Nat) (s : places.Shape)
    (hlen : s.length = r + 1)
    (hred : ground.getAt 0 s r = 0)
    (hcls : places.degree s % (r + 1) = 0)
    (hocc : 0 < ground.sumNat s) :
    2 * ((r + 1) * (r + 1)) ≤ c2hat.dfQ s := by
  have hq : c2hat.dfQ s = qRows (places.rowList s) := by
    show c2hat.sqGaps (places.rowList s)
        + s.length * c2hat.rho2 (places.rowList s)
      = c2hat.sqGaps (places.rowList s)
        + (places.rowList s).length * c2hat.rho2 (places.rowList s)
    rw [places.length_rowList]
  have hne : s ≠ [] := by
    intro h
    rw [h] at hlen
    exact Nat.noConfusion hlen
  rw [hq]
  show (if (0 : Nat) == 0 then 2 * ((r + 1) * (r + 1))
    else 0 * (r + 1 - 0) * (r + 2)) ≤ qRows (places.rowList s)
  exact floorRowsAt (qRows (places.rowList s) + 1) r 0
    (places.rowList s) (Nat.lt_succ_self _)
    ((places.length_rowList s).trans hlen)
    (fun p hp => places.rowList_le s p
      (by rw [places.length_rowList] at hp; exact hp))
    ((rowLast_read s r hlen).trans hred) hcls
    (by rw [rowHead_read s hne]; exact hocc)

end casfloor
