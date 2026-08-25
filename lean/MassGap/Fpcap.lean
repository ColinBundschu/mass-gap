import MassGap.Fusion
import MassGap.Certconstruct
/-!
`lem:fpcap` — the fusion form's two-sided dimension cap at the
eigen-identity's rows.  The multiplication's matrix at a stated
window index is `fusionMat`, its entry `M[x, y] = N^x_{λ y}` against
the orthonormal characters, the count entries the interface's own;
the symmetry read (`symAt`) and the eigen row's window read
(`rowCap`) are the hypotheses the interface supplies, the tex's
`prop:repring` third read and the dimension identity's window
comparison.  Every window hypothesis here is spelled as its own
decidable read — the Boolean fold over the window's key range,
`def:ground`'s reads being decidable at every argument — so `symAt`,
`rowCap`, `compRead` and the window's two further reads (`dimPos`,
the letters' occupied dimensions; `distinctAt`, the letters
pairwise distinct at the index's equality, `lem:loopcap`'s
consumer) are one datum apiece, decided at a stated window, with
`ground.all_range_read` the pointwise decode the proofs consume.
The two caps are the quadratic form's sides at the
window's vectors: `capUpper` the form at or below `d_λ` against the
gram, `capLower` the summed form at or above the sum's unit.  The
composition read (`compRead`) is the display's window carrier — the
squared fundamental's entry identity
`Σ_c N^c_{f x} N^c_{f y} = N^x_{θ y} + δ_{xy}` — its Gram the
shifted term's lower side at `lem:loopcap`, which reads the form's
double index fold off `quadFold` here.

The layers this proof rides live at their owners.  `def:ground`
carries the balance carrier's index fold `bsum` with its scalar
passes, pointwise splits, nested exchange, memberwise swap and
delta pick, the additive left fold `foldlSum`, and the balance
order `≤` with its `leB_*` kit and the comparison fold `bsum_le`;
`con:places` carries the key-range reads (`range_map_getAt`,
`famFold_getAt`, `ltOfMem`); `def:elim` carries the pairing's own —
the count pair `mulPairNat` and the pairing folds as index folds
(`dotP_fold`, `selfFold`), shared with `lem:loopcap`'s Gram route,
which closes on the same tier's one-sided read `dotN_self_side`.
`def:ground` carries besides the square's own
at-or-above-the-unit read (`unitLeSq`, off `sq_side`).  What stays
here is everything the fusion matrix shapes.

The proof is the tex's two-squares pricing collected fraction-free
by the co-product weights: at an index pair the entry prices
`2 N_{ij} d_i d_j x_i x_j` two-sidedly by
`N_{ij} (d_j² x_i² + d_i² x_j²)` — the balance carrier's square at
its one-sided read (`ground.sq_side`) — and the two sides clear by the
window's co-products (`ground.prodOver` the full product against
its withdrawn-key read, `ground.prodOver_pick`), the weight `D_i D_j`
an integer at every pair, the diagonal included.  The first halves
collect over the second index at the row read; the second halves
collect over the first index through the folds' exchange at the
symmetry, so each side reads `d_λ D² Σ x_i²` and the comparison
divides by the co-product's square.  The zero-dimension corner
genuinely breaks the cap — a vanishing window dimension carries an
off-diagonal count past the bound — and `hdim`, the tex's own exact
positive eigenvector clause, is where the division's positivity
comes from.
-/

namespace fpcap
open ground fusion elim

/-- The multiplication's matrix at a stated window index:
`M[x, y] = N^x_{λ y}` against the orthonormal characters, the
count entries the interface's own. -/
def fusionMat {L : Type} (F : Data L) (lam : L) (ls : List L) :
    Mat :=
  ls.map (fun x => ls.map (fun y => BPair.ofNat (F.count lam y x)))

/-- The window's symmetry read at a self-dual letter, the
hypothesis `prop:repring`'s third read supplies: the count fold's
own datum over the window's key pairs. -/
def symAt {L : Type} (F : Data L) (lam : L) (ls : List L) : Prop :=
  ((List.range ls.length).all (fun i =>
    (List.range ls.length).all (fun j =>
      F.count lam (ground.getAt F.unit ls i)
          (ground.getAt F.unit ls j)
        == F.count lam (ground.getAt F.unit ls j)
          (ground.getAt F.unit ls i)))) = true

instance {L : Type} (F : Data L) (lam : L) (ls : List L) :
    Decidable (symAt F lam ls) :=
  inferInstanceAs (Decidable (_ = _))

/-- The eigen row's window read: the compression's partial fold at
or below the row's read, the dimension identity's window comparison,
one comparison per window key. -/
def rowCap {L : Type} (F : Data L) (lam : L) (ls : List L) : Prop :=
  ((List.range ls.length).all (fun i =>
    ls.foldl (fun acc x =>
        acc + F.count lam (ground.getAt F.unit ls i) x * F.dim x) 0
      ≤ F.dim lam * F.dim (ground.getAt F.unit ls i))) = true

instance {L : Type} (F : Data L) (lam : L) (ls : List L) :
    Decidable (rowCap F lam ls) :=
  inferInstanceAs (Decidable (_ = _))

/-- The window's dimension read: every window letter's dimension
occupied, the tex's exact positive eigenvector clause. -/
def dimPos {L : Type} (F : Data L) (ls : List L) : Prop :=
  ((List.range ls.length).all (fun i =>
    0 < F.dim (ground.getAt F.unit ls i))) = true

instance {L : Type} (F : Data L) (ls : List L) :
    Decidable (dimPos F ls) :=
  inferInstanceAs (Decidable (_ = _))

/-- The window's index read: the letters pairwise distinct, the
label equality reading the key equality at every pair. -/
def distinctAt {L : Type} (F : Data L) (ls : List L) : Prop :=
  ((List.range ls.length).all (fun i =>
    (List.range ls.length).all (fun j =>
      F.eqL (ground.getAt F.unit ls i) (ground.getAt F.unit ls j)
        == (i == j)))) = true

instance {L : Type} (F : Data L) (ls : List L) :
    Decidable (distinctAt F ls) :=
  inferInstanceAs (Decidable (_ = _))

/-- The symmetry read's pointwise decode at a window key pair. -/
private theorem symRead {L : Type} {F : Data L} {lam : L}
    {ls : List L} (h : symAt F lam ls) (i j : Nat)
    (hi : i < ls.length) (hj : j < ls.length) :
    F.count lam (ground.getAt F.unit ls i) (ground.getAt F.unit ls j)
      = F.count lam (ground.getAt F.unit ls j)
        (ground.getAt F.unit ls i) :=
  ground.beqEqOf (ground.all_range_read ls.length
    (ground.all_range_read ls.length h i hi) j hj)

/-- The dimension read's pointwise decode at a window key. -/
private theorem dimRead {L : Type} {F : Data L} {ls : List L}
    (h : dimPos F ls) (i : Nat) (hi : i < ls.length) :
    0 < F.dim (ground.getAt F.unit ls i) :=
  of_decide_eq_true (ground.all_range_read ls.length h i hi)

/-! The window's co-products: the full product over the index
family and the product with one key's factor withdrawn — the
fraction-free clearing's weights, an integer at every index pair,
the diagonal included. -/

/-! The count-level rearrangements the clearing reads, hand-rolled
off `ground.mulMulMulComm` and the product's commutativity. -/

/-- The four-factor exchange at the outer members. -/
private theorem natMul4' (a b c d : Nat) :
    a * b * (c * d) = a * d * (b * c) := by
  rw [Nat.mul_comm c d]
  exact ground.mulMulMulComm a b d c

/-! The entry pricing: a square at or above the sum's unit prices
the cross product two-sidedly, the tex's two squares. -/

/-- The pricing at abstract members: the cross product's doubling
sits at or below the squares' sum, the scaled square's floor. -/
private theorem pricingAbs (A : Nat) (p q : BPair) :
    BPair.ofNat A * (p * q + p * q)
      ≤ BPair.ofNat A * (p * p + q * q) :=
  ground.leB_crossSq (ground.unitLeOfNat A) p q

/-- The pricing the other way: the doubled cross product's swap
sits at or below the squares' sum. -/
private theorem pricingAbsNeg (A : Nat) (p q : BPair) :
    (BPair.ofNat A * (p * q + p * q)).swap
      ≤ BPair.ofNat A * (p * p + q * q) :=
  ground.leB_crossSqSwap (ground.unitLeOfNat A) p q

/-- Two count scalars compose. -/
private theorem mulScalarNat (A c : Nat) (z : BPair) :
    (BPair.ofNat A * (BPair.ofNat c * z)).oneValue
      (BPair.ofNat (A * c) * z) := by
  rw [← BPair.mul_assoc]
  exact BPair.mul_congr_left
    (BPair.oneValue_symm (BPair.ofNat_mul A c))

/-- A count against a product of scaled data. -/
private theorem scalePair (A c e : Nat) (x y : BPair) :
    (BPair.ofNat A * ((BPair.ofNat c * x) * (BPair.ofNat e * y))).oneValue
      (BPair.ofNat (A * (c * e)) * (x * y)) :=
  BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _) (mulPairNat c e x y))
    (mulScalarNat A (c * e) (x * y))

/-- The priced cross product at the count weights. -/
private theorem priceL (A a b : Nat) (x y : BPair) :
    (BPair.ofNat A * ((BPair.ofNat a * x) * (BPair.ofNat b * y)
        + (BPair.ofNat a * x) * (BPair.ofNat b * y))).oneValue
      (BPair.ofNat (A * (a * b) + A * (a * b)) * (x * y)) := by
  rw [BPair.left_distrib]
  refine BPair.oneValue_trans
    (BPair.add_congr (scalePair A a b x y) (scalePair A a b x y)) ?_
  rw [← BPair.right_distrib]
  exact BPair.mul_congr_left
    (BPair.oneValue_symm (BPair.ofNat_add (A * (a * b)) (A * (a * b))))

/-- The priced squares at the count weights. -/
private theorem priceR (A a b : Nat) (x y : BPair) :
    (BPair.ofNat A * ((BPair.ofNat a * x) * (BPair.ofNat a * x)
        + (BPair.ofNat b * y) * (BPair.ofNat b * y))).oneValue
      (BPair.ofNat (A * (a * a)) * (x * x)
        + BPair.ofNat (A * (b * b)) * (y * y)) := by
  rw [BPair.left_distrib]
  exact BPair.add_congr (scalePair A a a x x) (scalePair A b b y y)

/-- The entry's two-squares pricing: the doubled cross product at
or below the weighted squares' sum. -/
private theorem pricing (A a b : Nat) (x y : BPair) :
    BPair.ofNat (A * (a * b) + A * (a * b)) * (x * y)
      ≤ BPair.ofNat (A * (a * a)) * (x * x)
        + BPair.ofNat (A * (b * b)) * (y * y) :=
  leB_congr (priceL A a b x y) (priceR A a b x y)
    (pricingAbs A (BPair.ofNat a * x) (BPair.ofNat b * y))

/-- The entry's pricing the other way: the doubled cross product's
swap at or below the weighted squares' sum. -/
private theorem pricingNeg (A a b : Nat) (x y : BPair) :
    (BPair.ofNat (A * (a * b) + A * (a * b)) * (x * y)).swap
      ≤ BPair.ofNat (A * (a * a)) * (x * x)
        + BPair.ofNat (A * (b * b)) * (y * y) :=
  leB_congr (swap_congr (priceL A a b x y)) (priceR A a b x y)
    (pricingAbsNeg A (BPair.ofNat a * x) (BPair.ofNat b * y))

/-- An occupied count keeps the strict order. -/
private theorem mulNat_lt (k : Nat) (hk : 0 < k) {x y : BPair}
    (h : x < y) : BPair.ofNat k * x < BPair.ofNat k * y := by
  match k, hk with
  | 0, hk => exact absurd hk (Nat.lt_irrefl 0)
  | k + 1, _ =>
    exact BPair.lt_congr
      (BPair.oneValue_symm (BPair.ofPos_scale (posOfSucc k) x))
      (BPair.oneValue_symm (BPair.ofPos_scale (posOfSucc k) y))
      (BPair.scale_lt (posOfSucc k) h)

/-! The collection: the priced entries collect by the eigen row's
read at the second index and, through the nested folds' exchange at
the symmetry, by the row read at the first — each side the row cap
against the co-product's square. -/

/-- The priced entries' collection at the two row reads. -/
private theorem collect (n dl D : Nat) (co : Nat → Nat)
    (NN : Nat → Nat → Nat) (dd : Nat → Nat) (xx : Nat → BPair)
    (g : Nat → Nat → BPair)
    (hsym : ∀ i j, i < n → j < n → NN i j = NN j i)
    (hrow : ∀ i, i < n → ground.famFold Nat.add 0
      (fun j => NN i j * dd j) (List.range n) ≤ dl * dd i)
    (hco : ∀ i, i < n → co i * dd i = D)
    (hprice : ∀ i j, i < n → j < n →
      g i j
        ≤ BPair.ofNat (co i * D * (NN i j * dd j)) * (xx i * xx i)
          + BPair.ofNat (co j * D * (NN i j * dd i))
            * (xx j * xx j)) :
    bsum (fun i => bsum (fun j => g i j) (List.range n))
        (List.range n)
      ≤ BPair.ofNat (dl * (D * D))
          * bsum (fun i => xx i * xx i) (List.range n)
        + BPair.ofNat (dl * (D * D))
          * bsum (fun i => xx i * xx i) (List.range n) := by
  have hT1 : ∀ i, i < n →
      bsum (fun j => BPair.ofNat (co i * D * (NN i j * dd j))
        * (xx i * xx i)) (List.range n)
      ≤ BPair.ofNat (dl * (D * D)) * (xx i * xx i) := by
    intro i hi
    refine leB_congr (BPair.oneValue_symm
      (bsum_scalar (fun j => co i * D * (NN i j * dd j))
        (xx i * xx i) (List.range n))) (BPair.oneValue_refl _) ?_
    refine leB_scale_mono ?_ (ground.unitLeSq (xx i))
    rw [← ground.famFold_mul (co i * D) (fun j => NN i j * dd j)
      (List.range n)]
    refine Nat.le_trans
      (Nat.mul_le_mul_left (co i * D) (hrow i hi)) ?_
    have hEq : co i * D * (dl * dd i) = dl * (D * D) := by
      rw [natMul4' (co i) D dl (dd i), hco i hi,
        ← ground.mulAssoc D D dl, Nat.mul_comm (D * D) dl]
    rw [hEq]
    exact Nat.le.refl
  have hT2 : ∀ j, j < n →
      bsum (fun i => BPair.ofNat (co j * D * (NN i j * dd i))
        * (xx j * xx j)) (List.range n)
      ≤ BPair.ofNat (dl * (D * D)) * (xx j * xx j) := by
    intro j hj
    refine leB_congr (BPair.oneValue_symm
      (bsum_scalar (fun i => co j * D * (NN i j * dd i))
        (xx j * xx j) (List.range n))) (BPair.oneValue_refl _) ?_
    refine leB_scale_mono ?_ (ground.unitLeSq (xx j))
    rw [← ground.famFold_mul (co j * D) (fun i => NN i j * dd i)
      (List.range n)]
    have hcongr : ground.famFold Nat.add 0
        (fun i => NN i j * dd i) (List.range n)
        = ground.famFold Nat.add 0
          (fun i => NN j i * dd i) (List.range n) :=
      ground.famFold_congr_members Nat.add 0 _ _ (List.range n)
        (fun x hx => by rw [hsym x j (ground.ltOfMem hx) hj])
    rw [hcongr]
    refine Nat.le_trans
      (Nat.mul_le_mul_left (co j * D) (hrow j hj)) ?_
    have hEq : co j * D * (dl * dd j) = dl * (D * D) := by
      rw [natMul4' (co j) D dl (dd j), hco j hj,
        ← ground.mulAssoc D D dl, Nat.mul_comm (D * D) dl]
    rw [hEq]
    exact Nat.le.refl
  have step1 := bsum_le
    (fun i => bsum (fun j => g i j) (List.range n))
    (fun i => bsum (fun j =>
      BPair.ofNat (co i * D * (NN i j * dd j)) * (xx i * xx i)
        + BPair.ofNat (co j * D * (NN i j * dd i))
          * (xx j * xx j)) (List.range n))
    (List.range n)
    (fun i hi => bsum_le _ _ (List.range n)
      (fun j hj => hprice i j (ground.ltOfMem hi) (ground.ltOfMem hj)))
  have step2 := BPair.oneValue_trans
    (foldB_congr_members
      (fun i => bsum (fun j =>
        BPair.ofNat (co i * D * (NN i j * dd j)) * (xx i * xx i)
          + BPair.ofNat (co j * D * (NN i j * dd i))
            * (xx j * xx j)) (List.range n))
      (fun i => bsum (fun j =>
          BPair.ofNat (co i * D * (NN i j * dd j)) * (xx i * xx i))
          (List.range n)
        + bsum (fun j =>
          BPair.ofNat (co j * D * (NN i j * dd i)) * (xx j * xx j))
          (List.range n))
      (List.range n) (fun i _ => foldB_add _ _ (List.range n)))
    (foldB_add _ _ (List.range n))
  have step3 : bsum (fun i => bsum (fun j =>
        BPair.ofNat (co i * D * (NN i j * dd j)) * (xx i * xx i))
        (List.range n)) (List.range n)
      ≤ BPair.ofNat (dl * (D * D))
        * bsum (fun i => xx i * xx i) (List.range n) :=
    leB_congr_right
      (foldB_mul_left _ _ (List.range n))
      (bsum_le _ _ (List.range n) (fun i hi => hT1 i (ground.ltOfMem hi)))
  have step4 : bsum (fun i => bsum (fun j =>
        BPair.ofNat (co j * D * (NN i j * dd i)) * (xx j * xx j))
        (List.range n)) (List.range n)
      ≤ BPair.ofNat (dl * (D * D))
        * bsum (fun i => xx i * xx i) (List.range n) := by
    refine leB_congr (BPair.oneValue_symm
      (bsum_swap (fun i j =>
        BPair.ofNat (co j * D * (NN i j * dd i)) * (xx j * xx j))
        (List.range n) (List.range n))) (BPair.oneValue_refl _) ?_
    exact leB_congr_right
      (foldB_mul_left _ _ (List.range n))
      (bsum_le _ _ (List.range n) (fun j hj => hT2 j (ground.ltOfMem hj)))
  exact leB_trans (leB_congr_right step2 step1) (leB_add step3 step4)

/-- The clearing scalar passes into the double fold. -/
private theorem pushScalar (W n : Nat) (NN : Nat → Nat → Nat)
    (xx : Nat → BPair) :
    (BPair.ofNat W * bsum (fun i => bsum (fun j =>
        BPair.ofNat (NN i j) * (xx i * xx j)) (List.range n))
      (List.range n)).oneValue
      (bsum (fun i => bsum (fun j =>
        BPair.ofNat (W * NN i j) * (xx i * xx j)) (List.range n))
        (List.range n)) := by
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (foldB_mul_left _ _ (List.range n))) ?_
  refine foldB_congr_members _ _ (List.range n) (fun i _ => ?_)
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (foldB_mul_left _ _ (List.range n))) ?_
  exact foldB_congr_members _ _ (List.range n)
    (fun j _ => mulScalarNat W (NN i j) (xx i * xx j))

/-- The two collected sides rejoin the clearing scalar. -/
private theorem doubleScalar (n dl D : Nat) (xx : Nat → BPair) :
    (BPair.ofNat (dl * (D * D))
        * bsum (fun i => xx i * xx i) (List.range n)
      + BPair.ofNat (dl * (D * D))
        * bsum (fun i => xx i * xx i) (List.range n)).oneValue
      (BPair.ofNat (D * D + D * D)
        * (BPair.ofNat dl
          * bsum (fun i => xx i * xx i) (List.range n))) := by
  have hnat : dl * (D * D) + dl * (D * D) = (D * D + D * D) * dl := by
    rw [mulAddR (D * D) (D * D) dl, Nat.mul_comm (D * D) dl]
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
    (mulScalarNat (D * D + D * D) dl
      (bsum (fun i => xx i * xx i) (List.range n))))
  rw [← BPair.right_distrib]
  refine BPair.mul_congr_left ?_
  rw [← hnat]
  exact BPair.oneValue_symm
    (BPair.ofNat_add (dl * (D * D)) (dl * (D * D)))

/-- The entry's three count identities at the withdrawn factors:
the cross weight reads the co-product's square, and each square's
weight reads the row fold's own scalar. -/
private theorem coefEq (D : Nat) (co : Nat → Nat)
    (NN : Nat → Nat → Nat) (dd : Nat → Nat) (i j : Nat)
    (hi : co i * dd i = D) (hj : co j * dd j = D) :
    (NN i j * (co i * co j) * (dd j * dd i)
        + NN i j * (co i * co j) * (dd j * dd i)
      = (D * D + D * D) * NN i j)
    ∧ (NN i j * (co i * co j) * (dd j * dd j)
      = co i * D * (NN i j * dd j))
    ∧ (NN i j * (co i * co j) * (dd i * dd i)
      = co j * D * (NN i j * dd i)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ground.mulAssoc (NN i j) (co i * co j) (dd j * dd i),
      natMul4' (co i) (co j) (dd j) (dd i), hi, hj,
      mulAddR (D * D) (D * D) (NN i j),
      Nat.mul_comm (D * D) (NN i j)]
  · rw [ground.mulAssoc (NN i j) (co i * co j) (dd j * dd j),
      natMul4' (co i) (co j) (dd j) (dd j), hj,
      natMul4' (co i) D (NN i j) (dd j),
      Nat.mul_comm (NN i j) (co i * dd j * D),
      ground.mulAssoc (co i * dd j) D (NN i j)]
  · rw [ground.mulAssoc (NN i j) (co i * co j) (dd i * dd i),
      natMul4' (co i) (co j) (dd i) (dd i), hi,
      natMul4' (co j) D (NN i j) (dd i),
      Nat.mul_comm D (co j * dd i),
      Nat.mul_comm (NN i j) (co j * dd i * D),
      ground.mulAssoc (co j * dd i) D (NN i j)]

/-- The entry's priced comparison at the withdrawn factors. -/
private theorem priceEntry (D : Nat) (co : Nat → Nat)
    (NN : Nat → Nat → Nat) (dd : Nat → Nat) (xx : Nat → BPair)
    (i j : Nat) (hi : co i * dd i = D) (hj : co j * dd j = D) :
    BPair.ofNat ((D * D + D * D) * NN i j) * (xx i * xx j)
      ≤ BPair.ofNat (co i * D * (NN i j * dd j)) * (xx i * xx i)
        + BPair.ofNat (co j * D * (NN i j * dd i))
          * (xx j * xx j) := by
  obtain ⟨e1, e2, e3⟩ := coefEq D co NN dd i j hi hj
  have hp := pricing (NN i j * (co i * co j)) (dd j) (dd i)
    (xx i) (xx j)
  rw [e1, e2, e3] at hp
  exact hp

/-- The entry's priced comparison the other way. -/
private theorem priceEntryNeg (D : Nat) (co : Nat → Nat)
    (NN : Nat → Nat → Nat) (dd : Nat → Nat) (xx : Nat → BPair)
    (i j : Nat) (hi : co i * dd i = D) (hj : co j * dd j = D) :
    (BPair.ofNat ((D * D + D * D) * NN i j)
        * (xx i * xx j)).swap
      ≤ BPair.ofNat (co i * D * (NN i j * dd j)) * (xx i * xx i)
        + BPair.ofNat (co j * D * (NN i j * dd i))
          * (xx j * xx j) := by
  obtain ⟨e1, e2, e3⟩ := coefEq D co NN dd i j hi hj
  have hp := pricingNeg (NN i j * (co i * co j)) (dd j) (dd i)
    (xx i) (xx j)
  rw [e1, e2, e3] at hp
  exact hp

/-- The clearing's occupancy: the co-product's doubled square. -/
private theorem clearPos {D : Nat} (hD : 0 < D) :
    0 < D * D + D * D :=
  Nat.lt_of_lt_of_le (Nat.mul_pos hD hD) (Nat.le_add_right _ _)

/-- The cap's upper side at the abstract co-products. -/
private theorem coreUpperAt (n dl D : Nat) (co : Nat → Nat)
    (NN : Nat → Nat → Nat) (dd : Nat → Nat) (xx : Nat → BPair)
    (hsym : ∀ i j, i < n → j < n → NN i j = NN j i)
    (hrow : ∀ i, i < n → ground.famFold Nat.add 0
      (fun j => NN i j * dd j) (List.range n) ≤ dl * dd i)
    (hco : ∀ i, i < n → co i * dd i = D) (hD : 0 < D) :
    ¬ (BPair.ofNat dl * bsum (fun i => xx i * xx i) (List.range n)
        < bsum (fun i => bsum (fun j => BPair.ofNat (NN i j)
            * (xx i * xx j)) (List.range n)) (List.range n)) := by
  intro hlt
  refine leB_not_lt ?_
    (mulNat_lt (D * D + D * D) (clearPos hD) hlt)
  exact leB_congr (BPair.oneValue_symm (pushScalar (D * D + D * D)
      n NN xx))
    (doubleScalar n dl D xx)
    (collect n dl D co NN dd xx
      (fun i j => BPair.ofNat ((D * D + D * D) * NN i j)
        * (xx i * xx j))
      hsym hrow hco (fun i j hi hj =>
        priceEntry D co NN dd xx i j (hco i hi) (hco j hj)))

/-- The cap's lower side at the abstract co-products. -/
private theorem coreLowerAt (n dl D : Nat) (co : Nat → Nat)
    (NN : Nat → Nat → Nat) (dd : Nat → Nat) (xx : Nat → BPair)
    (hsym : ∀ i j, i < n → j < n → NN i j = NN j i)
    (hrow : ∀ i, i < n → ground.famFold Nat.add 0
      (fun j => NN i j * dd j) (List.range n) ≤ dl * dd i)
    (hco : ∀ i, i < n → co i * dd i = D) (hD : 0 < D) :
    ¬ (BPair.ofNat dl * bsum (fun i => xx i * xx i) (List.range n)
        + bsum (fun i => bsum (fun j => BPair.ofNat (NN i j)
            * (xx i * xx j)) (List.range n)) (List.range n)
        < BPair.unit) := by
  intro hlt
  have hmul' : BPair.ofNat (D * D + D * D)
        * (BPair.ofNat dl * bsum (fun i => xx i * xx i)
          (List.range n))
      + BPair.ofNat (D * D + D * D)
        * bsum (fun i => bsum (fun j => BPair.ofNat (NN i j)
            * (xx i * xx j)) (List.range n)) (List.range n)
      < BPair.unit :=
    BPair.lt_congr (BPair.oneValue_of_eq (BPair.left_distrib _ _ _))
      (BPair.mul_unit _)
      (mulNat_lt (D * D + D * D) (clearPos hD) hlt)
  refine leB_not_lt ?_ hmul'
  refine leB_unit_add ?_
  have hswapEq : (bsum (fun i => bsum (fun j =>
        BPair.ofNat ((D * D + D * D) * NN i j) * (xx i * xx j))
        (List.range n)) (List.range n)).swap
      = bsum (fun i => bsum (fun j =>
        (BPair.ofNat ((D * D + D * D) * NN i j)
          * (xx i * xx j)).swap) (List.range n))
        (List.range n) :=
    ((fold_swap (fun i => bsum (fun j =>
        BPair.ofNat ((D * D + D * D) * NN i j) * (xx i * xx j))
        (List.range n)) (List.range n)).symm).trans
      (ground.famFold_congr_all BPair.add BPair.unit _ _
        (fun i => (fold_swap (fun j =>
          BPair.ofNat ((D * D + D * D) * NN i j) * (xx i * xx j))
          (List.range n)).symm) (List.range n))
  refine leB_congr ?_ (doubleScalar n dl D xx)
    (collect n dl D co NN dd xx
      (fun i j => (BPair.ofNat ((D * D + D * D) * NN i j)
        * (xx i * xx j)).swap)
      hsym hrow hco (fun i j hi hj =>
        priceEntryNeg D co NN dd xx i j (hco i hi) (hco j hj)))
  rw [← hswapEq]
  exact swap_congr (BPair.oneValue_symm
    (pushScalar (D * D + D * D) n NN xx))

/-- The cap's upper side at the window's own co-products. -/
private theorem coreUpper (n dl : Nat) (NN : Nat → Nat → Nat)
    (dd : Nat → Nat) (xx : Nat → BPair)
    (hsym : ∀ i j, i < n → j < n → NN i j = NN j i)
    (hrow : ∀ i, i < n → ground.famFold Nat.add 0
      (fun j => NN i j * dd j) (List.range n) ≤ dl * dd i)
    (hpos : ∀ i, i < n → 0 < dd i) :
    ¬ (BPair.ofNat dl * bsum (fun i => xx i * xx i) (List.range n)
        < bsum (fun i => bsum (fun j => BPair.ofNat (NN i j)
            * (xx i * xx j)) (List.range n)) (List.range n)) :=
  coreUpperAt n dl (ground.prodOver dd (List.range n))
    (fun i => ground.prodOver (fun x => if x = i then 1 else dd x)
      (List.range n)) NN dd xx hsym hrow
    (fun i hi => ground.prodOver_pick dd i (List.range n)
      (ground.countOf_range_one hi))
    (ground.prodOver_pos dd (List.range n)
      (fun i hi => hpos i (ground.ltOfMem hi)))

/-- The cap's lower side at the window's own co-products. -/
private theorem coreLower (n dl : Nat) (NN : Nat → Nat → Nat)
    (dd : Nat → Nat) (xx : Nat → BPair)
    (hsym : ∀ i j, i < n → j < n → NN i j = NN j i)
    (hrow : ∀ i, i < n → ground.famFold Nat.add 0
      (fun j => NN i j * dd j) (List.range n) ≤ dl * dd i)
    (hpos : ∀ i, i < n → 0 < dd i) :
    ¬ (BPair.ofNat dl * bsum (fun i => xx i * xx i) (List.range n)
        + bsum (fun i => bsum (fun j => BPair.ofNat (NN i j)
            * (xx i * xx j)) (List.range n)) (List.range n)
        < BPair.unit) :=
  coreLowerAt n dl (ground.prodOver dd (List.range n))
    (fun i => ground.prodOver (fun x => if x = i then 1 else dd x)
      (List.range n)) NN dd xx hsym hrow
    (fun i hi => ground.prodOver_pick dd i (List.range n)
      (ground.countOf_range_one hi))
    (ground.prodOver_pos dd (List.range n)
      (fun i hi => hpos i (ground.ltOfMem hi)))

/-! The index bridge: the window's form as the double index fold at
the counts, over `def:elim`'s pairing folds (`dotP_fold`,
`selfFold`), `con:places`' key-range reads (the family list's
read-back `range_map_getAt`, the family fold `famFold_getAt`) and
`def:ground`'s reading of the interface's own left folds
(`foldlSum`). -/

/-- The form as the double index fold at the window's counts, the
loop window's Gram route the further consumer (`lem:loopcap`). -/
theorem quadFold {L : Type} (F : Data L) (lam : L)
    (ls : List L) (u : List BPair) (hu : u.length = ls.length) :
    (inertia.quadForm (fusionMat F lam ls) u).oneValue
      (bsum (fun i => bsum (fun j =>
        BPair.ofNat (F.count lam (ground.getAt F.unit ls j)
            (ground.getAt F.unit ls i))
          * (ground.getAt BPair.unit u i
            * ground.getAt BPair.unit u j)) (List.range ls.length))
        (List.range ls.length)) := by
  have hrows : ∀ x : L,
      (ls.map (fun y => BPair.ofNat (F.count lam y x))).length
        = ls.length := fun x => ground.length_map _ ls
  have hvec : (elim.matVec (fusionMat F lam ls) u).length
      = ls.length := by
    show ((fusionMat F lam ls).map
      (fun r => elim.dotN r u)).length = ls.length
    rw [ground.length_map]
    exact ground.length_map _ ls
  refine BPair.oneValue_trans
    (elim.dotN_dotP u (elim.matVec (fusionMat F lam ls) u)) ?_
  rw [dotP_fold ls.length u (elim.matVec (fusionMat F lam ls) u)
    hu hvec]
  refine foldB_congr_members _ _ (List.range ls.length) (fun i hi => ?_)
  have hin : i < ls.length := ground.ltOfMem hi
  have hgi : ground.getAt BPair.unit
        (elim.matVec (fusionMat F lam ls) u) i
      = elim.dotN (ls.map (fun y => BPair.ofNat
          (F.count lam y (ground.getAt F.unit ls i)))) u := by
    show ground.getAt BPair.unit ((fusionMat F lam ls).map
      (fun r => elim.dotN r u)) i = _
    rw [show (fusionMat F lam ls).map (fun r => elim.dotN r u)
        = ls.map (fun x => elim.dotN
          (ls.map (fun y => BPair.ofNat (F.count lam y x))) u) from
      ground.map_map _ _ ls]
    exact ground.getAt_map F.unit BPair.unit _ ls i hin
  rw [hgi]
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (elim.dotN_dotP _ u)
        (BPair.oneValue_of_eq (dotP_fold ls.length _ u
          (hrows _) hu)))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (foldB_mul_left _ _ (List.range ls.length))) ?_
  refine foldB_congr_members _ _ (List.range ls.length) (fun j hj => ?_)
  rw [ground.getAt_map F.unit BPair.unit
    (fun y => BPair.ofNat
      (F.count lam y (ground.getAt F.unit ls i))) ls j (ground.ltOfMem hj)]
  exact BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)

/-- The eigen row's window read as the index fold at the
symmetry. -/
private theorem rowFold {L : Type} (F : Data L) (lam : L)
    (ls : List L) (hsym : symAt F lam ls) (hrow : rowCap F lam ls) :
    ∀ i, i < ls.length → ground.famFold Nat.add 0
      (fun j => F.count lam (ground.getAt F.unit ls j)
          (ground.getAt F.unit ls i)
        * F.dim (ground.getAt F.unit ls j)) (List.range ls.length)
      ≤ F.dim lam * F.dim (ground.getAt F.unit ls i) := by
  intro i hi
  have h0 := of_decide_eq_true
    (ground.all_range_read ls.length hrow i hi)
  rw [foldlSum (fun x => F.count lam (ground.getAt F.unit ls i) x
      * F.dim x) ls 0, Nat.zero_add,
    ← ground.famFold_getAt Nat.add 0 _ F.unit ls ls.length rfl]
    at h0
  have hcongr : ground.famFold Nat.add 0
      (fun j => F.count lam (ground.getAt F.unit ls j)
          (ground.getAt F.unit ls i)
        * F.dim (ground.getAt F.unit ls j)) (List.range ls.length)
      = ground.famFold Nat.add 0
      (fun j => F.count lam (ground.getAt F.unit ls i)
          (ground.getAt F.unit ls j)
        * F.dim (ground.getAt F.unit ls j))
        (List.range ls.length) :=
    ground.famFold_congr_members Nat.add 0 _ _ (List.range ls.length)
      (fun x hx => by rw [symRead hsym i x hi (ground.ltOfMem hx)])
  rw [hcongr]
  exact h0

/-- The fusion form at or below the dimension against the gram:
`N_λ ⪯ d_λ` at the eigen-identity's rows (`lem:fpcap`). -/
theorem capUpper {L : Type} (F : Data L) (lam : L) (ls : List L)
    (hsym : symAt F lam ls) (hrow : rowCap F lam ls)
    (hdim : dimPos F ls)
    (u : List BPair) (hu : u.length = ls.length) :
    ¬ (BPair.ofNat (F.dim lam) * dotN u u
        < inertia.quadForm (fusionMat F lam ls) u) :=
  fun hlt => coreUpper ls.length (F.dim lam)
    (fun i j => F.count lam (ground.getAt F.unit ls j)
      (ground.getAt F.unit ls i))
    (fun i => F.dim (ground.getAt F.unit ls i))
    (fun i => ground.getAt BPair.unit u i)
    (fun i j hi hj => (symRead hsym i j hi hj).symm)
    (rowFold F lam ls hsym hrow) (dimRead hdim)
    (BPair.lt_congr
      (BPair.mul_congr (BPair.oneValue_refl _)
        (selfFold u ls.length hu))
      (quadFold F lam ls u hu) hlt)

/-- The summed form at or above the sum's unit:
`d_λ + N_λ` positive semidefinite (`lem:fpcap`). -/
theorem capLower {L : Type} (F : Data L) (lam : L) (ls : List L)
    (hsym : symAt F lam ls) (hrow : rowCap F lam ls)
    (hdim : dimPos F ls)
    (u : List BPair) (hu : u.length = ls.length) :
    ¬ (BPair.ofNat (F.dim lam) * dotN u u
          + inertia.quadForm (fusionMat F lam ls) u
        < BPair.unit) :=
  fun hlt => coreLower ls.length (F.dim lam)
    (fun i j => F.count lam (ground.getAt F.unit ls j)
      (ground.getAt F.unit ls i))
    (fun i => F.dim (ground.getAt F.unit ls i))
    (fun i => ground.getAt BPair.unit u i)
    (fun i j hi hj => (symRead hsym i j hi hj).symm)
    (rowFold F lam ls hsym hrow) (dimRead hdim)
    (BPair.lt_congr
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (selfFold u ls.length hu))
        (quadFold F lam ls u hu))
      (BPair.oneValue_refl BPair.unit) hlt)

/-- The composition read at a stated window with its intermediate
list: the squared fundamental's entry identity
`Σ_c N^c_{f x} N^c_{f y} = N^x_{θ y} + δ_{xy}`, the display's
window carrier (`lem:fpcap`; `lem:adjchar` with `prop:repring`'s
dual read the interface's suppliers). -/
def compRead {L : Type} (F : Data L) (f : L) (ls cs : List L) :
    Prop :=
  ((List.range ls.length).all (fun i =>
    (List.range ls.length).all (fun j =>
      cs.foldl (fun acc c =>
          acc + F.count f (ground.getAt F.unit ls i) c
            * F.count f (ground.getAt F.unit ls j) c) 0
        == F.count F.theta (ground.getAt F.unit ls j)
            (ground.getAt F.unit ls i)
          + (if F.eqL (ground.getAt F.unit ls i)
                (ground.getAt F.unit ls j) then 1 else 0)))) = true

instance {L : Type} (F : Data L) (f : L) (ls cs : List L) :
    Decidable (compRead F f ls cs) :=
  inferInstanceAs (Decidable (_ = _))

end fpcap
