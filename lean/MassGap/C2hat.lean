import MassGap.Places
/-!
`def:c2hat` — the weight-free Casimir read: `ĉ₂(λ) = [d_f Q(λ) :
2 d_f²]` at the join `k² + d_f Q(λ) = d_f q(λ) + d_f ⟨λ, 2ρ⟩`, with
the constructed witness `d_f Q(λ) = Σ_{p<q} ⟨λ_p : λ_q⟩² +
d_f ⟨λ, 2ρ⟩`.  The computation `dfQ` is the witness display on the
sorted rows — the row pairs' squared gaps with the count-weighted
gap fold, subtraction the sorted rows' own gaps — and the square
identity `d_f q(λ) = k² + Σ_{p<q} ⟨λ_p : λ_q⟩²` is the stated
decidable read `squareRead`, the join's collection, proven at
every shape (`squareAll`) through the row-level identity at a
weakly descending list (`squareRows`, the sorted rows
`con:places`' own), its instances the check module's pins.  `dfQ`
is a class read: a full column moves every row by one and the gaps
are fixed (`dfQ_full`, over the folds' invariance `rho2_shift` and
`sqGaps_shift`), and the vacant shape reads vacant
(`dfQ_replicate_zero`).  The fold kit the row displays consume: a
constant block's gaps and squared gaps (`gapFold_replicate`,
`sqFold_replicate`), a constant block prefix's two folds
(`rho2_replicate_app`, `sqGaps_replicate_app` — the block's members
pair at no gap among themselves, each reading the tail once) with
the vacant family's (`rho2_zeros`, `sqGaps_zeros`), and the rows'
homogeneity at a scaled label, `⟨m u : m v⟩ = m ⟨u : v⟩`
(`rho2_scale` at degree one, `sqGaps_scale` at degree two).  The
consumers read the cleared data: `lem:casfloor`'s floor and
`prop:anchor`'s tower at `dfQ` against the one factor, the pair
display's form-line reading `prop:form`'s own site.
-/

namespace c2hat
open ground places

/-- The gap fold over the sorted rows: `Σ_{p<q} ⟨λ_p : λ_q⟩`, each
gap the sorted pair's own. -/
def rho2 : List Nat → Nat
  | [] => 0
  | x :: t => t.foldl (fun acc y => acc + (x - y)) 0 + rho2 t

/-- The squared-gap fold over the sorted rows:
`Σ_{p<q} ⟨λ_p : λ_q⟩²`. -/
def sqGaps : List Nat → Nat
  | [] => 0
  | x :: t => t.foldl (fun acc y => acc + (x - y) * (x - y)) 0 + sqGaps t

/-- The row squares' fold, the standard square `q(λ)`. -/
def sumSq : List Nat → Nat
  | [] => 0
  | x :: t => x * x + sumSq t

/-- The cleared traceless read `d_f Q(λ)`, the constructed
witness's display: the row pairs' squared gaps with the
count-weighted gap fold. -/
def dfQ (s : Shape) : Nat :=
  sqGaps (rowList s) + s.length * rho2 (rowList s)

/-- The square identity `d_f q(λ) = k² + Σ_{p<q} ⟨λ_p : λ_q⟩²`,
the join's collection, decidable. -/
def squareRead (s : Shape) : Prop :=
  s.length * sumSq (rowList s)
    = degree s * degree s + sqGaps (rowList s)

instance instC2hat1 (s : Shape) : Decidable (squareRead s) :=
  inferInstanceAs (Decidable (_ = _))

/-! The fold kit: the constant block's gaps, the block prefix's
two folds, the rows' homogeneity at a scaled label, and the class
read at a full column. -/

/-- A constant block reads one gap per member. -/
theorem gapFold_replicate (x c : Nat) : ∀ k a : Nat,
    (List.replicate k c).foldl (fun acc y => acc + (x - y)) a
      = a + k * (x - c)
  | 0, a => by
    show a = a + 0 * (x - c)
    rw [Nat.zero_mul (x - c), Nat.add_zero a]
  | k + 1, a => by
    show (List.replicate k c).foldl (fun acc y => acc + (x - y)) (a + (x - c))
      = a + (k + 1) * (x - c)
    rw [gapFold_replicate x c k (a + (x - c)),
      ground.mulAddR k 1 (x - c), Nat.one_mul (x - c),
      Nat.add_assoc a (x - c) (k * (x - c)),
      Nat.add_comm (x - c) (k * (x - c)),
      ← Nat.add_assoc a (k * (x - c)) (x - c)]

/-- A constant block reads one squared gap per member. -/
theorem sqFold_replicate (x c : Nat) : ∀ k a : Nat,
    (List.replicate k c).foldl
        (fun acc y => acc + (x - y) * (x - y)) a
      = a + k * ((x - c) * (x - c))
  | 0, a => by
    show a = a + 0 * ((x - c) * (x - c))
    rw [Nat.zero_mul ((x - c) * (x - c)), Nat.add_zero a]
  | k + 1, a => by
    show (List.replicate k c).foldl
        (fun acc y => acc + (x - y) * (x - y)) (a + (x - c) * (x - c))
      = a + (k + 1) * ((x - c) * (x - c))
    rw [sqFold_replicate x c k (a + (x - c) * (x - c)),
      ground.mulAddR k 1 ((x - c) * (x - c)),
      Nat.one_mul ((x - c) * (x - c)),
      Nat.add_assoc a ((x - c) * (x - c)) (k * ((x - c) * (x - c))),
      Nat.add_comm ((x - c) * (x - c)) (k * ((x - c) * (x - c))),
      ← Nat.add_assoc a (k * ((x - c) * (x - c))) ((x - c) * (x - c))]

/-- The gap fold over a constant block prefix: the block's members
pair at no gap among themselves, each reading the tail once. -/
theorem rho2_replicate_app (c : Nat) : ∀ (k : Nat) (t : List Nat),
    rho2 (List.replicate k c ++ t)
      = k * t.foldl (fun acc y => acc + (c - y)) 0 + rho2 t
  | 0, t => by rw [Nat.zero_mul, Nat.zero_add]; rfl
  | k + 1, t => by
    have hb : (List.replicate k c ++ t).foldl
        (fun acc y => acc + (c - y)) 0
      = t.foldl (fun acc y => acc + (c - y)) 0 := by
      rw [ground.foldl_append (fun acc y => acc + (c - y))
          (List.replicate k c) t 0,
        gapFold_replicate c c k 0, Nat.sub_self c, Nat.mul_zero,
        Nat.add_zero 0]
    show (List.replicate k c ++ t).foldl (fun acc y => acc + (c - y)) 0
        + rho2 (List.replicate k c ++ t)
      = (k + 1) * t.foldl (fun acc y => acc + (c - y)) 0 + rho2 t
    rw [hb, rho2_replicate_app c k t, ground.mulAddR k 1
        (t.foldl (fun acc y => acc + (c - y)) 0),
      Nat.one_mul (t.foldl (fun acc y => acc + (c - y)) 0),
      Nat.add_left_comm (t.foldl (fun acc y => acc + (c - y)) 0)
        (k * t.foldl (fun acc y => acc + (c - y)) 0) (rho2 t),
      Nat.add_assoc (k * t.foldl (fun acc y => acc + (c - y)) 0)
        (t.foldl (fun acc y => acc + (c - y)) 0) (rho2 t)]

/-- The squared gap fold over a constant block prefix. -/
theorem sqGaps_replicate_app (c : Nat) : ∀ (k : Nat) (t : List Nat),
    sqGaps (List.replicate k c ++ t)
      = k * t.foldl (fun acc y => acc + (c - y) * (c - y)) 0 + sqGaps t
  | 0, t => by rw [Nat.zero_mul, Nat.zero_add]; rfl
  | k + 1, t => by
    have hb : (List.replicate k c ++ t).foldl
        (fun acc y => acc + (c - y) * (c - y)) 0
      = t.foldl (fun acc y => acc + (c - y) * (c - y)) 0 := by
      rw [ground.foldl_append (fun acc y => acc + (c - y) * (c - y))
          (List.replicate k c) t 0,
        sqFold_replicate c c k 0, Nat.sub_self c, Nat.zero_mul 0,
        Nat.mul_zero k, Nat.add_zero 0]
    show (List.replicate k c ++ t).foldl
          (fun acc y => acc + (c - y) * (c - y)) 0
        + sqGaps (List.replicate k c ++ t)
      = (k + 1) * t.foldl (fun acc y => acc + (c - y) * (c - y)) 0
        + sqGaps t
    rw [hb, sqGaps_replicate_app c k t, ground.mulAddR k 1
        (t.foldl (fun acc y => acc + (c - y) * (c - y)) 0),
      Nat.one_mul (t.foldl (fun acc y => acc + (c - y) * (c - y)) 0),
      Nat.add_left_comm
        (t.foldl (fun acc y => acc + (c - y) * (c - y)) 0)
        (k * t.foldl (fun acc y => acc + (c - y) * (c - y)) 0) (sqGaps t),
      Nat.add_assoc
        (k * t.foldl (fun acc y => acc + (c - y) * (c - y)) 0)
        (t.foldl (fun acc y => acc + (c - y) * (c - y)) 0) (sqGaps t)]

/-- A constant block's gap fold is vacant: its members pair at no
gap. -/
theorem rho2_replicate (c : Nat) : ∀ k : Nat,
    rho2 (List.replicate k c) = 0
  | 0 => rfl
  | k + 1 => by
    show (List.replicate k c).foldl (fun acc y => acc + (c - y)) 0
        + rho2 (List.replicate k c) = 0
    rw [
      gapFold_replicate c c k 0,
      Nat.sub_self c,
      Nat.mul_zero,
      Nat.add_zero,
      rho2_replicate c k]

/-- The vacant family's gap fold is vacant. -/
theorem rho2_zeros (g : Nat) : rho2 (List.replicate g 0) = 0 :=
  rho2_replicate 0 g

/-- The vacant family's squared gap fold is vacant. -/
theorem sqGaps_zeros : ∀ g : Nat, sqGaps (List.replicate g 0) = 0
  | 0 => rfl
  | g + 1 => by
    show (List.replicate g 0).foldl
        (fun acc y => acc + (0 - y) * (0 - y)) 0
        + sqGaps (List.replicate g 0) = 0
    rw [sqFold_replicate 0 0 g 0, sqGaps_zeros g]
    rfl

/-- The gap fold is homogeneous of degree one in the rows:
`⟨m u : m v⟩ = m ⟨u : v⟩`. -/
theorem rho2_scale (m : Nat) : ∀ l : List Nat,
    rho2 (l.map (fun z => z * m)) = m * rho2 l
  | [] => by
    show (0 : Nat) = m * 0
    rw [Nat.mul_zero m]
  | x :: t => by
    have hf : ∀ a : Nat, (t.map (fun z => z * m)).foldl
        (fun acc y => acc + (x * m - y)) (a * m)
      = (t.foldl (fun acc y => acc + (x - y)) a) * m := by
      induction t with
      | nil => intro a; rfl
      | cons y u ih =>
        intro a
        show (u.map (fun z => z * m)).foldl
            (fun acc z => acc + (x * m - z)) (a * m + (x * m - y * m))
          = (u.foldl (fun acc z => acc + (x - z)) (a + (x - y))) * m
        rw [← ground.subMulR x y m, ← ground.mulAddR a (x - y) m]
        exact ih (a + (x - y))
    show (t.map (fun z => z * m)).foldl (fun acc y => acc + (x * m - y)) 0
        + rho2 (t.map (fun z => z * m))
      = m * (t.foldl (fun acc y => acc + (x - y)) 0 + rho2 t)
    have hf0 := hf 0
    rw [Nat.zero_mul m] at hf0
    rw [hf0, rho2_scale m t, Nat.left_distrib m
        (t.foldl (fun acc y => acc + (x - y)) 0) (rho2 t),
      Nat.mul_comm (t.foldl (fun acc y => acc + (x - y)) 0) m]

/-- The squared gap fold is homogeneous of degree two in the rows:
`⟨m u : m v⟩² = m² ⟨u : v⟩²`. -/
theorem sqGaps_scale (m : Nat) : ∀ l : List Nat,
    sqGaps (l.map (fun z => z * m)) = m * m * sqGaps l
  | [] => by
    show (0 : Nat) = m * m * 0
    rw [Nat.mul_zero (m * m)]
  | x :: t => by
    have hf : ∀ a : Nat, (t.map (fun z => z * m)).foldl
        (fun acc y => acc + (x * m - y) * (x * m - y)) (a * (m * m))
      = (t.foldl (fun acc y => acc + (x - y) * (x - y)) a) * (m * m) := by
      induction t with
      | nil => intro a; rfl
      | cons y u ih =>
        intro a
        have hsq : (x * m - y * m) * (x * m - y * m)
            = ((x - y) * (x - y)) * (m * m) := by
          rw [← ground.subMulR x y m, ground.mulAssoc (x - y) m
              ((x - y) * m), ← ground.mulAssoc m (x - y) m,
            Nat.mul_comm m (x - y), ground.mulAssoc (x - y) m m,
            ← ground.mulAssoc (x - y) (x - y) (m * m)]
        show (u.map (fun z => z * m)).foldl
            (fun acc z => acc + (x * m - z) * (x * m - z))
            (a * (m * m) + (x * m - y * m) * (x * m - y * m))
          = (u.foldl (fun acc z => acc + (x - z) * (x - z))
              (a + (x - y) * (x - y))) * (m * m)
        rw [hsq, ← ground.mulAddR a ((x - y) * (x - y)) (m * m)]
        exact ih (a + (x - y) * (x - y))
    show (t.map (fun z => z * m)).foldl
          (fun acc y => acc + (x * m - y) * (x * m - y)) 0
        + sqGaps (t.map (fun z => z * m))
      = m * m * (t.foldl (fun acc y => acc + (x - y) * (x - y)) 0
          + sqGaps t)
    have hf0 := hf 0
    rw [Nat.zero_mul (m * m)] at hf0
    rw [hf0, sqGaps_scale m t, Nat.left_distrib (m * m)
        (t.foldl (fun acc y => acc + (x - y) * (x - y)) 0) (sqGaps t),
      Nat.mul_comm (t.foldl (fun acc y => acc + (x - y) * (x - y)) 0)
        (m * m)]

/-- The gap fold is fixed by the full raise. -/
theorem rho2_shift : ∀ l : List Nat,
    rho2 (l.map (fun z => z + 1)) = rho2 l
  | [] => rfl
  | x :: t => by
    have hf : ∀ a : Nat, (t.map (fun z => z + 1)).foldl
        (fun acc y => acc + (x + 1 - y)) a
      = t.foldl (fun acc y => acc + (x - y)) a := by
      induction t with
      | nil => intro _; rfl
      | cons y u ih =>
        intro a
        show (u.map (fun z => z + 1)).foldl
            (fun acc z => acc + (x + 1 - z)) (a + (x + 1 - (y + 1)))
          = u.foldl (fun acc z => acc + (x - z)) (a + (x - y))
        rw [Nat.succ_sub_succ x y]
        exact ih (a + (x - y))
    show (t.map (fun z => z + 1)).foldl (fun acc y => acc + (x + 1 - y)) 0
        + rho2 (t.map (fun z => z + 1))
      = t.foldl (fun acc y => acc + (x - y)) 0 + rho2 t
    rw [hf 0, rho2_shift t]

/-- The squared gap fold is fixed by the full raise. -/
theorem sqGaps_shift : ∀ l : List Nat,
    sqGaps (l.map (fun z => z + 1)) = sqGaps l
  | [] => rfl
  | x :: t => by
    have hf : ∀ a : Nat, (t.map (fun z => z + 1)).foldl
        (fun acc y => acc + (x + 1 - y) * (x + 1 - y)) a
      = t.foldl (fun acc y => acc + (x - y) * (x - y)) a := by
      induction t with
      | nil => intro _; rfl
      | cons y u ih =>
        intro a
        show (u.map (fun z => z + 1)).foldl
            (fun acc z => acc + (x + 1 - z) * (x + 1 - z))
            (a + (x + 1 - (y + 1)) * (x + 1 - (y + 1)))
          = u.foldl (fun acc z => acc + (x - z) * (x - z))
            (a + (x - y) * (x - y))
        rw [Nat.succ_sub_succ x y]
        exact ih (a + (x - y) * (x - y))
    show (t.map (fun z => z + 1)).foldl
          (fun acc y => acc + (x + 1 - y) * (x + 1 - y)) 0
        + sqGaps (t.map (fun z => z + 1))
      = t.foldl (fun acc y => acc + (x - y) * (x - y)) 0 + sqGaps t
    rw [hf 0, sqGaps_shift t]

/-- The cleared read is a class read: a full column moves every row
by one and the gaps are fixed. -/
theorem dfQ_full (s : Shape) :
    dfQ (ground.bumpAt (s.length - 1) s) = dfQ s := by
  show sqGaps (rowList (ground.bumpAt (s.length - 1) s))
      + (ground.bumpAt (s.length - 1) s).length
        * rho2 (rowList (ground.bumpAt (s.length - 1) s))
    = sqGaps (rowList s) + s.length * rho2 (rowList s)
  rw [places.rowList_full s, sqGaps_shift (rowList s),
    rho2_shift (rowList s), ground.length_bumpAt (s.length - 1) s]

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
      have h1 := ground.getAt_le_sumNat ((y :: t).map (fun z => x - z)) r
      rw [ground.getAt_map 0 0 (fun z => x - z) (y :: t) r
          (by rw [hlen']; exact Nat.lt_succ_self r), h0'] at h1
      have h2 : ground.sumNat ((y :: t).map (fun z => x - z))
          = ground.famFold Nat.add 0 (fun z => x - z) (y :: t) :=
        ground.famFold_map Nat.add 0 (fun v => v) (fun z => x - z) (y :: t)
      rw [h2] at h1
      rw [ground.foldlSum (fun z => x - z) (y :: t) 0, Nat.zero_add]
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

/-- The vacant shape's cleared read is vacant. -/
theorem dfQ_replicate_zero (n : Nat) :
    dfQ (List.replicate n 0) = 0 := by
  show sqGaps (rowList (List.replicate n 0))
      + (List.replicate n 0).length * rho2 (rowList (List.replicate n 0))
    = 0
  rw [places.rowList_replicate_zero n, sqGaps_zeros n, rho2_zeros n,
    Nat.mul_zero]

/-! The square identity's kit: the additive regroupings, the gap
join at an ordered pair, and the head fold's collection. -/

/-- The six-term regrouping at the crossed pair. -/
private theorem shuffleB (a b b' c f g : Nat) :
    a + b + (b' + c) + (f + g) = a + (f + (b + b')) + (c + g) := by
  rw [Nat.add_assoc a b (b' + c), Nat.add_assoc a (b + (b' + c)) (f + g),
    Nat.add_assoc b (b' + c) (f + g), Nat.add_assoc b' c (f + g),
    Nat.add_left_comm c f g, Nat.add_left_comm b' f (c + g),
    Nat.add_left_comm b f (b' + (c + g)),
    Nat.add_assoc a (f + (b + b')) (c + g),
    Nat.add_assoc f (b + b') (c + g), Nat.add_assoc b b' (c + g)]

/-- The square's regrouping at the doubled pair. -/
private theorem sqShuffle (a b c : Nat) :
    c + (a + b + (a + b)) = a + b + (b + c) + a := by
  rw [Nat.add_assoc a b (a + b), Nat.add_left_comm b a b,
    Nat.add_left_comm c a (a + (b + b)), Nat.add_left_comm c a (b + b),
    Nat.add_left_comm c b b, Nat.add_comm c b, Nat.add_assoc a b (b + c),
    Nat.add_comm (a + (b + (b + c))) a]

/-- The gap's square against the crossed product at a named gap. -/
private theorem gapRing (y d : Nat) :
    d * d + 2 * ((y + d) * y) = (y + d) * (y + d) + y * y := by
  rw [mulAddR y d y, mulAddR y d (y + d), Nat.left_distrib y y d,
    Nat.left_distrib d y d, Nat.mul_comm y d, Nat.two_mul (y * y + d * y)]
  exact sqShuffle (y * y) (d * y) (d * d)

/-- The gap's square joins the crossed product at an ordered pair. -/
private theorem gapSq {x y : Nat} (h : y ≤ x) :
    (x - y) * (x - y) + 2 * (x * y) = x * x + y * y := by
  have hd : y + (x - y) = x := ground.natAddSubCancel h
  have hk := gapRing y (x - y)
  rw [hd] at hk
  exact hk

/-- The head's gap fold against the crossed total at a dominating
head: the squared gaps join the doubled products. -/
private theorem headSq (x : Nat) : ∀ (t : List Nat),
    (∀ q, q < t.length → ground.getAt 0 t q ≤ x) →
    t.foldl (fun acc y => acc + (x - y) * (x - y)) 0
        + 2 * (x * sumNat t)
      = t.length * (x * x) + sumSq t
  | [], _ => by
    show 0 + 2 * (x * 0) = 0 * (x * x) + 0
    rw [Nat.zero_mul (x * x), Nat.mul_zero x, Nat.mul_zero 2]
  | y :: t, hdom => by
    have hyx : y ≤ x := hdom 0 (Nat.succ_pos t.length)
    have hih := headSq x t (fun q hq => hdom (q + 1) (Nat.succ_lt_succ hq))
    have hs : t.foldl (fun acc z => acc + (x - z) * (x - z))
          (0 + (x - y) * (x - y))
        = 0 + (x - y) * (x - y)
          + t.foldl (fun acc z => acc + (x - z) * (x - z)) 0 :=
      ground.foldlSeed (fun z => (x - z) * (x - z)) t (0 + (x - y) * (x - y))
    show t.foldl (fun acc z => acc + (x - z) * (x - z))
          (0 + (x - y) * (x - y))
        + 2 * (x * (y + sumNat t))
      = (t.length + 1) * (x * x) + (y * y + sumSq t)
    rw [hs, Nat.zero_add ((x - y) * (x - y)),
      Nat.left_distrib x y (sumNat t),
      Nat.left_distrib 2 (x * y) (x * sumNat t), Nat.add_add_add_comm,
      gapSq hyx, hih, mulAddR t.length 1 (x * x), Nat.one_mul (x * x),
      addJoinHeadFront (x * x) (y * y) (t.length * (x * x)) (sumSq t)]

/-- The cons step's collection: the head's square against the tail's
own identity at the head fold's read. -/
private theorem consSquare (l x s q g f : Nat)
    (hih : l * q = s * s + g)
    (hhead : f + 2 * (x * s) = l * (x * x) + q) :
    (l + 1) * (x * x + q) = (x + s) * (x + s) + (f + g) := by
  rw [mulAddR l 1 (x * x + q), Nat.one_mul (x * x + q),
    Nat.left_distrib l (x * x) q, mulAddR x s (x + s),
    Nat.left_distrib x x s, Nat.left_distrib s x s, Nat.mul_comm s x,
    shuffleB (x * x) (x * s) (x * s) (s * s) f g,
    ← Nat.two_mul (x * s), hhead, ← hih,
    addJoinHeadOut (l * (x * x)) (l * q) (x * x) q]

/-- The square identity at a weakly descending list: the length
against the squares' fold reads the total's square with the pair
gaps' squares, `def:c2hat`'s collection. -/
theorem squareRows (l : List Nat)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) :
    l.length * sumSq l = sumNat l * sumNat l + sqGaps l := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have hih := ih (fun p hp => hdesc (p + 1) (Nat.succ_lt_succ hp))
    have hhead := headSq x t (headDom x t hdesc)
    exact consSquare t.length x (sumNat t) (sumSq t) (sqGaps t)
      (t.foldl (fun acc y => acc + (x - y) * (x - y)) 0) hih hhead

/-- The square identity at every shape, the stated read proven:
the row list is weakly descending, `con:places`' sorted rows. -/
theorem squareAll (s : places.Shape) : c2hat.squareRead s := by
  show s.length * sumSq (rowList s)
    = degree s * degree s + sqGaps (rowList s)
  rw [← places.length_rowList s]
  exact squareRows (rowList s) (fun p hp =>
    places.rowList_le s p (by rw [← places.length_rowList s]; exact hp))

/-- The gap fold at the list's place pairs (`def:c2hat`). -/
theorem rho2_pairs : ∀ l : List Nat,
    rho2 l = famFold Nat.add 0
      (fun p => getAt 0 l p.1 - getAt 0 l p.2) (pairsOf l.length)
  | [] => rfl
  | x :: t => by
    show t.foldl (fun acc y => acc + (x - y)) 0 + rho2 t
      = famFold Nat.add 0
        (fun p => getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2)
        (pairsOf (t.length + 1))
    rw [ground.foldlSum (fun y => x - y) t 0, Nat.zero_add,
      ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
        _ (pairsOf (t.length + 1))
        ((List.range t.length).map (fun k => ((0, k + 1) : Nat × Nat))
          ++ (pairsOf t.length).map
            (fun p => ((p.1 + 1, p.2 + 1) : Nat × Nat)))
        (places.countOf_pairs_split t.length),
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun p : Nat × Nat => getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2) _ _,
      ground.famFold_map Nat.add 0
        (fun p : Nat × Nat => getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2)
        (fun k => ((0, k + 1) : Nat × Nat)) (List.range t.length),
      ground.famFold_map Nat.add 0
        (fun p : Nat × Nat => getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2)
        (fun p => ((p.1 + 1, p.2 + 1) : Nat × Nat)) (pairsOf t.length), rho2_pairs t]
    change famFold Nat.add 0 (fun y => x - y) t
        + famFold Nat.add 0 (fun p => getAt 0 t p.1 - getAt 0 t p.2)
          (pairsOf t.length)
      = famFold Nat.add 0 (fun k => x - (getAt 0 t k))
          (List.range t.length)
        + famFold Nat.add 0 (fun p => getAt 0 t p.1 - getAt 0 t p.2)
          (pairsOf t.length)
    rw [ground.famFold_getAt Nat.add 0 (fun y => x - y) 0 t t.length rfl]

/-- The squared-gap fold at the list's place pairs (`def:c2hat`). -/
theorem sqGaps_pairs : ∀ l : List Nat,
    sqGaps l = famFold Nat.add 0
      (fun p => (getAt 0 l p.1 - getAt 0 l p.2) * (getAt 0 l p.1 - getAt 0 l p.2)) (pairsOf l.length)
  | [] => rfl
  | x :: t => by
    show t.foldl (fun acc y => acc + (x - y) * (x - y)) 0 + sqGaps t
      = famFold Nat.add 0
        (fun p => (getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2) * (getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2))
        (pairsOf (t.length + 1))
    rw [ground.foldlSum (fun y => (x - y) * (x - y)) t 0, Nat.zero_add,
      ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
        _ (pairsOf (t.length + 1))
        ((List.range t.length).map (fun k => ((0, k + 1) : Nat × Nat))
          ++ (pairsOf t.length).map
            (fun p => ((p.1 + 1, p.2 + 1) : Nat × Nat)))
        (places.countOf_pairs_split t.length),
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
        (fun p : Nat × Nat => (getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2) * (getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2)) _ _,
      ground.famFold_map Nat.add 0
        (fun p : Nat × Nat => (getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2) * (getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2))
        (fun k => ((0, k + 1) : Nat × Nat)) (List.range t.length),
      ground.famFold_map Nat.add 0
        (fun p : Nat × Nat => (getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2) * (getAt 0 (x :: t) p.1 - getAt 0 (x :: t) p.2))
        (fun p => ((p.1 + 1, p.2 + 1) : Nat × Nat)) (pairsOf t.length), sqGaps_pairs t]
    change famFold Nat.add 0 (fun y => (x - y) * (x - y)) t
        + famFold Nat.add 0 (fun p => (getAt 0 t p.1 - getAt 0 t p.2) * (getAt 0 t p.1 - getAt 0 t p.2))
          (pairsOf t.length)
      = famFold Nat.add 0 (fun k => (x - (getAt 0 t k)) * (x - (getAt 0 t k)))
          (List.range t.length)
        + famFold Nat.add 0 (fun p => (getAt 0 t p.1 - getAt 0 t p.2) * (getAt 0 t p.1 - getAt 0 t p.2))
          (pairsOf t.length)
    rw [ground.famFold_getAt Nat.add 0 (fun y => (x - y) * (x - y)) 0 t t.length rfl]

end c2hat
