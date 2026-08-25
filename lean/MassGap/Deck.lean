import MassGap.Poly
/-!
`def:deck` — the deck relation at a variable `y` is the monic
quadratic `y² + 1 = w y` at the chord `w`, its shift read
`y^j + y^{j+2} = w y^{j+1}` the relation's own multiple, and a root
pair is two data at product one joining to the chord.  The deck
families are the polynomials in the chord at the relation's
recursion, `p_j + p_{j+2} = w p_{j+1}` and `Q_j + Q_{j+2} =
w Q_{j+1}`, over the balance-pair carrier at the seeds `p₁ = w`,
`p₂ + 2 = w²`, `Q₁ = 1`, `Q₂ = w` (`pFam`, `qFam`: the two-seed
recursion at one accumulator pass, the index the positive
carrier's).  The relation's remainder carrier is the pair
`a(w) + b(w) y` at the reduction `y² = w y + 1̌`, the arithmetic
the displayed sum and cross product (`DElem` at `dAdd`, `dMul`,
`dSwap`, `dPow`, `yE`/`oneE` the variable and the unit, `dNull` the
equal-members read), and the column reads close on it: the plus
read `y^{2b} + 1 = y^b p_b(w)` (`plusRead`) and the word read
`⟨y^{2b} : 1⟩ = ⟨y² : 1⟩ y^e Q_b(w)` at `e + 1 = b` (`wordRead`),
one decidable identity per key with the general induction on the
shift read at the recorded consumers (`thm:trigpencil`'s symbol,
`lem:fiberdec`'s momenta, `con:sertables`' chord minors).  At a
root pair the plus read collects to the matched powers' sum `z^b + z'^b = p_b(w)`, the
cleared read at a shared clearing: the product-one and chord joins
with the powers' fold against the family's cleared evaluation
(`pairRead` at `poly.evalClear`).

The families' doubling identity closes the module,
`p_L = ⟨x:2⟩ P_L² + 2` at `2m+1 = L` (`pFamN_pSum`,
`lem:fiberdec`'s display).  Its route is the recursion's own
algebra over the polynomial carrier: the family read from the tex's
seed `p₀ = 2` (`pFamN`), the relation's recursion at every key
(`pFamN_rec`), the partial sum's read `⟨x:2⟩ P_m + p_m = p_{m+1}`
(`chordTwo_pSum`, the telescope written additively at the linear
factor `chordTwo`), and the two product families
`p_j p_j = p_{2j} + 2` and `p_j p_{j+1} = p_{2j+1} + w`
(`deckProducts`, one joint induction at the recursion's own
two-step state).  Every step is remainder-list arithmetic at the
relation, the subtraction the memberwise swap.

The residue's wrap identities close the module on it.  The
congruence's read at a stated multiple is `pCong`, one decidable
identity per witness, and the class read modulo the symbol is that
witness's existence; on it the powers wrap at `2m+1 = L`: `p_L = 2`
(`pFamN_side`), `p_{L-b} = p_b` (`pFamN_wrapDown`) and
`p_{L+b} = p_b` (`pFamN_wrapUp`), each a general theorem over the
indices, with a located root's own reads their evaluations
(`pCong_eval`) — `lem:fiberdec`'s wrap sentence.  The residue tier
sits on the same class: `redP` is the division remainder by the
symbol's monic display, `monicRead` that display's own divisor
read, and the bridge carries the two spellings onto one class —
every polynomial is congruent to its residue at the quotient's own
multiple (`redP_pCong`), congruent members read one residue
(`redP_congr`), and one residue value is itself a stated-multiple
witness (`pCong_of_redP`).  `monicRead` is the value read, a
repair: the symbol's top coefficient sits at a drifted
representative from `m = 3` on (the partial sums' componentwise
additions), so an equality spelling of the divisor read refuses
every side beyond seven while the value read holds at every side
probed — the read at the representative was the gauge's, the class
read the carrier's own.  The display is monic at every side
outright — `pSum_monic` is `monicRead` at every `m`, `def:deck`'s
own parity induction: the families' lengths and top entries run
through the recursion one parity per step from the seeds, and the
partial sums keep the top at the last family joined — so the
bridge, the vector form and the membership reads stand
binder-free.

The band's two linear ends close the module.  Each remainder is the
Horner read at its divisor's own root (`poly.div_linear_eval`): at
the monic `⟨x : 2⟩` the deck symbol leaves the side `2m+1 = L`
(`divTwo`) and at the partner `⟨x : 2̌⟩` it leaves the depth's parity
member, the product's unit at an even depth and its balance partner
at an odd one (`parityMember`, `pFamN_partner`, `pSum_partner`,
`divPartner`); the two quotients multiply to the band's Gram witness
(`gramCof`), and each divisor against its own quotient reads the
swapped remainder at the symbol's own multiple (`cofTwo_pCong`,
`cofPartner_pCong`).
-/

namespace deck
open ground poly

/-- The chord's monomial, the families' variable. -/
def wPoly : Poly := [BPair.unit, BPair.ofPos .one]

/-- The `p`-family's accumulator pair at a key, the recursion's two
running members `(p_b, p_{b+1})` at the seeds `p₁ = w`,
`p₂ + 2 = w²`. -/
private def pPair (b : Pos) : Poly × Poly :=
  ground.peanoRec (motive := fun _ => Poly × Poly)
    ([BPair.unit, BPair.ofPos .one],
     [⟨1, 3⟩, BPair.unit, ⟨2, 1⟩])
    (fun _ pr => (pr.2,
      poly.add (poly.mul wPoly pr.2) (pr.1.map BPair.swap))) b

/-- The `p`-family at the seeds `p₁ = w`, `p₂ + 2 = w²`: each later
member the join's datum, `p_{j+2} = w p_{j+1} + p̌_j`, one
accumulator pass. -/
def pFam (b : Pos) : Poly := (pPair b).1

/-- The `Q`-family at the seeds `Q₁ = 1`, `Q₂ = w`, the same
recursion. -/
def qFam (b : Pos) : Poly :=
  (ground.peanoRec (motive := fun _ => Poly × Poly)
    (poly.one, wPoly)
    (fun _ pr => (pr.2,
      poly.add (poly.mul wPoly pr.2) (pr.1.map BPair.swap))) b).1

/-- The relation's remainder carrier, `a(w) + b(w) y` at the
reduction `y² = w y + 1̌`. -/
abbrev DElem := Poly × Poly

/-- The componentwise sum. -/
def dAdd (x y : DElem) : DElem :=
  (poly.add x.1 y.1, poly.add x.2 y.2)

/-- The memberwise swap, componentwise. -/
def dSwap (x : DElem) : DElem :=
  (x.1.map BPair.swap, x.2.map BPair.swap)

/-- The cross product at the reduction:
`(a + b y)(a' + b' y) = (a a' + (b b')̌) + (a b' + a' b + w b b') y`. -/
def dMul (x y : DElem) : DElem :=
  (poly.add (poly.mul x.1 y.1) ((poly.mul x.2 y.2).map BPair.swap),
   poly.add (poly.add (poly.mul x.1 y.2) (poly.mul x.2 y.1))
     (poly.mul wPoly (poly.mul x.2 y.2)))

/-- The variable's element. -/
def yE : DElem := ([], poly.one)

/-- The product's unit. -/
def oneE : DElem := (poly.one, [])

/-- The word power at the reduction. -/
def dPow (x : DElem) : Nat → DElem
  | 0 => oneE
  | k + 1 => dMul x (dPow x k)

/-- Every coefficient reads the sum's unit. -/
def dNull (x : DElem) : Prop :=
  poly.unitTail x.1 ∧ poly.unitTail x.2

instance (x : DElem) : Decidable (dNull x) :=
  @instDecidableAnd _ _ (poly.decUnitTail _) (poly.decUnitTail _)

/-- The plus read `y^{2b} + 1 = y^b p_b(w)` at the key `b`, the
successor spelling `b = bp + 1`: one identity per key, the
families' column read. -/
def plusRead (bp : Nat) : Prop :=
  dNull (dAdd (dAdd (dPow yE (2 * (bp + 1))) oneE)
    (dSwap (dMul (dPow yE (bp + 1))
      ((pFam (ground.posOfSucc bp)), []))))

instance (bp : Nat) : Decidable (plusRead bp) :=
  inferInstanceAs (Decidable (dNull _))

/-- The word read `⟨y^{2b} : 1⟩ = ⟨y² : 1⟩ y^e Q_b(w)` at the join
`e + 1 = b`, the geometric telescope's column. -/
def wordRead (e : Nat) : Prop :=
  dNull (dAdd (dAdd (dPow yE (2 * (e + 1))) (dSwap oneE))
    (dSwap (dMul (dMul (dAdd (dPow yE 2) (dSwap oneE)) (dPow yE e))
      ((qFam (ground.posOfSucc e)), []))))

instance (e : Nat) : Decidable (wordRead e) :=
  inferInstanceAs (Decidable (dNull _))

/-- The root pair's collected read at a shared clearing: the
product-one join `zn zn' = c²`, the chord join `zn + zn' = wn`, and
the matched powers' sum against the family's cleared evaluation,
`z^b + z'^b = p_b(w)` at `w = [wn : c]` cleared by the key's
power. -/
def pairRead (zn zn' wn : BPair) (c : Pos) (bp : Nat) : Prop :=
  BPair.oneValue (zn * zn') (BPair.ofPos (c * c))
  ∧ BPair.oneValue (zn + zn') wn
  ∧ BPair.oneValue
      (ground.bpow zn (bp + 1) + ground.bpow zn' (bp + 1))
      (poly.evalClear (pFam (ground.posOfSucc bp)) wn c (bp + 1))

instance (zn zn' wn : BPair) (c : Pos) (bp : Nat) :
    Decidable (pairRead zn zn' wn c bp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! The geometric word's deck symbol and its reads at the chord `2`
(`lem:fiberdec`'s division display): the symbol is the `p`-family's
partial sum with the product's unit, and at the chord `2` every
family member reads `2`, so the symbol reads the side. -/

/-- The geometric word's deck symbol `P_L := 1 + Σ_{j≤m} p_j` at
`2m+1 = L`, monic of degree `m` at the `p`-family's partial
sums. -/
def pSum : Nat → Poly
  | 0 => poly.one
  | m + 1 => poly.add (pSum m) (pFam (ground.posOfSucc m))

private theorem eval_swapMap : ∀ (p : Poly) (x : BPair),
    (poly.eval (p.map BPair.swap) x).oneValue (poly.eval p x).swap
  | [], _ => BPair.oneValue_refl _
  | c :: p, x => by
    show (c.swap + x * poly.eval (p.map BPair.swap) x).oneValue
      (c + x * poly.eval p x).swap
    rw [← BPair.swap_add c (x * poly.eval p x),
      ← BPair.mul_swap x (poly.eval p x)]
    exact BPair.add_congr (BPair.oneValue_refl c.swap)
      (BPair.mul_congr (BPair.oneValue_refl x) (eval_swapMap p x))

private theorem step_two {a b : Poly}
    (ha : (poly.eval a (BPair.ofNat 2)).oneValue (BPair.ofNat 2))
    (hb : (poly.eval b (BPair.ofNat 2)).oneValue (BPair.ofNat 2)) :
    (poly.eval (poly.add (poly.mul wPoly b) (a.map BPair.swap))
      (BPair.ofNat 2)).oneValue (BPair.ofNat 2) :=
  BPair.oneValue_trans
    (poly.eval_add (poly.mul wPoly b) (a.map BPair.swap) (BPair.ofNat 2))
    (BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (poly.eval_mul wPoly b (BPair.ofNat 2))
          (BPair.mul_congr
            (show (poly.eval wPoly (BPair.ofNat 2)).oneValue
              (BPair.ofNat 2) by decide +kernel) hb))
        (BPair.oneValue_trans (eval_swapMap a (BPair.ofNat 2))
          (ground.swap_congr ha)))
      (show ((BPair.ofNat 2 * BPair.ofNat 2) + (BPair.ofNat 2).swap).oneValue
        (BPair.ofNat 2) by decide +kernel))

private theorem pPair_two : ∀ b : Pos,
    (poly.eval (pPair b).1 (BPair.ofNat 2)).oneValue (BPair.ofNat 2)
    ∧ (poly.eval (pPair b).2 (BPair.ofNat 2)).oneValue (BPair.ofNat 2) :=
  ground.peanoRec
    (motive := fun b =>
      (poly.eval (pPair b).1 (BPair.ofNat 2)).oneValue (BPair.ofNat 2)
      ∧ (poly.eval (pPair b).2 (BPair.ofNat 2)).oneValue (BPair.ofNat 2))
    ⟨by decide +kernel, by decide +kernel⟩
    (fun _ ih => ⟨ih.2, step_two ih.1 ih.2⟩)

/-- The `p`-family at the chord `2`: every key reads `2`, the
recursion's own read from the seeds. -/
theorem pFam_two (b : Pos) :
    (poly.eval (pFam b) (BPair.ofNat 2)).oneValue (BPair.ofNat 2) :=
  (pPair_two b).1

/-- The deck symbol at the chord `2` reads the side, `P_L(2) = L` at
`2m+1 = L`: the word's value on the unit fiber. -/
theorem pSum_two : ∀ m : Nat,
    (poly.eval (pSum m) (BPair.ofNat 2)).oneValue
      (BPair.ofNat (2 * m + 1))
  | 0 => by decide +kernel
  | m + 1 =>
    BPair.oneValue_symm (BPair.oneValue_trans
      (show (BPair.ofNat (2 * (m + 1) + 1)).oneValue
          (BPair.ofNat (2 * m + 1) + BPair.ofNat 2) from
        BPair.ofNat_add (2 * m + 1) 2)
      (BPair.oneValue_symm (BPair.oneValue_trans
        (poly.eval_add (pSum m) (pFam (ground.posOfSucc m))
          (BPair.ofNat 2))
        (BPair.add_congr (pSum_two m) (pFam_two (ground.posOfSucc m))))))

/-- The division display at the monic `⟨x : 2⟩`: the deck symbol
leaves its Horner read there, `P_L = q ⟨x:2⟩ + L`, the remainder the
side `2m+1 = L` (`def:poly`'s division at a linear factor). -/
def divTwoRead (m : Nat) : Prop :=
  poly.oneValue (poly.div [(BPair.ofNat 2).swap] (pSum m)).2
    [BPair.ofNat (2 * m + 1)]

instance (m : Nat) : Decidable (divTwoRead m) := poly.decOneValue _ _

/-- The division display at the monic `⟨x : 2⟩` holds at every side:
the remainder is the Horner read at that divisor's own root
(`poly.div_linear_eval`), and the deck symbol's value at the chord
`2` is the side `2m+1 = L` (`pSum_two`). -/
theorem divTwo (m : Nat) : divTwoRead m := by
  exact poly.oneValue_trans
    (poly.div_linear_eval ((BPair.ofNat 2).swap) (pSum m))
    ⟨pSum_two m, trivial⟩

/-! The families' doubling identity, `lem:fiberdec`'s display
\[
  p_L(x) \;=\; \langle x\!:\!2\rangle\,P_L(x)^2 + 2
  \qquad\text{at } 2m+1 = L .
\]
The route is the recursion's own algebra over the polynomial
carrier (`def:poly`): the family read from the tex's seed
`p₀ = 2` (`pFamN`), the relation's recursion at every key
`p_b + p_{b+2} = w p_{b+1}` (`pFamN_rec`, the seeds' own step), the
partial sum's read `⟨x:2⟩ P_m + p_m = p_{m+1}` (`chordTwo_pSum`,
the telescope written additively), and the two product families
`p_j p_j = p_{2j} + 2`, `p_j p_{j+1} = p_{2j+1} + w`
(`deckProducts`, one joint induction at the recursion's own
two-step state).  Every step is remainder-list arithmetic at the
relation, the subtraction the memberwise swap. -/

/-- The `p`-family at the tex's own seed `p₀ = 2`, the positive
carrier's family riding above it. -/
def pFamN : Nat → Poly
  | 0 => [BPair.ofNat 2]
  | b + 1 => pFam (ground.posOfSucc b)

/-- The monic linear factor `⟨x : 2⟩` at the chord `2`, the
division display's own divisor (`def:poly`'s monic spelling). -/
def chordTwo : Poly := poly.monic [(BPair.ofNat 2).swap]

/-- A summand against its memberwise swap clears from a sum. -/
private theorem cancel_neg (A W : Poly) :
    poly.oneValue (poly.add A (poly.add W (poly.neg A))) W :=
  poly.oneValue_trans
    (poly.add_congr (poly.oneValue_refl A) (poly.add_comm W (poly.neg A)))
    (poly.oneValue_trans (poly.add_join A (poly.neg A) W)
      (poly.unitTail_add (poly.add_neg A) W))

/-- The relation's recursion at every key of the seeded family,
`p_b + p_{b+2} = w p_{b+1}` (`def:deck`'s display). -/
theorem pFamN_rec : ∀ b : Nat,
    poly.oneValue (poly.add (pFamN b) (pFamN (b + 2)))
      (poly.mul wPoly (pFamN (b + 1)))
  | 0 => by decide +kernel
  | c + 1 =>
    cancel_neg (pPair (ground.posOfSucc c)).1
      (poly.mul wPoly (pPair (ground.posOfSucc c)).2)

private theorem mapUnit_tail : ∀ p : Poly,
    poly.unitTail (p.map (fun d => BPair.unit * d))
  | [] => trivial
  | c :: p => ⟨BPair.unit_mul c, mapUnit_tail p⟩

/-- The chord variable multiplies as the one-key shift. -/
theorem mulX_read (p : Poly) :
    poly.oneValue (poly.mul wPoly p) (BPair.unit :: p) := by
  show poly.oneValue
    (poly.add (p.map (fun d => BPair.unit * d))
      (BPair.unit :: poly.mul [BPair.ofPos .one] p))
    (BPair.unit :: p)
  refine poly.oneValue_trans
    (poly.unitTail_add (mapUnit_tail p) _) ?_
  exact ⟨BPair.oneValue_refl BPair.unit, poly.one_mul p⟩

/-- The chord monomial splits at the linear factor: `⟨x:2⟩ q + q + q
= w q`, the division display's own read carried onto a factor. -/
theorem chordTwo_join (q : Poly) :
    poly.oneValue (poly.add (poly.mul chordTwo q) (poly.add q q))
      (poly.mul wPoly q) :=
  poly.oneValue_symm (poly.oneValue_trans
    (poly.mul_congr_left
      (show poly.oneValue wPoly
        (poly.add chordTwo
          (poly.add poly.one poly.one)) by decide +kernel) q)
    (poly.oneValue_trans (poly.sum_mul chordTwo _ q)
      (poly.add_congr (poly.oneValue_refl _)
        (poly.oneValue_trans
          (poly.sum_mul poly.one poly.one q)
          (poly.add_congr (poly.one_mul q) (poly.one_mul q))))))

/-- The partial sum's read at the linear factor,
`⟨x:2⟩ P_m + p_m = p_{m+1}`: the geometric telescope written
additively over the balance pairs. -/
theorem chordTwo_pSum : ∀ m : Nat,
    poly.oneValue (poly.add (poly.mul chordTwo (pSum m)) (pFamN m))
      (pFamN (m + 1))
  | 0 => by decide +kernel
  | m + 1 => by
    refine poly.add_cancel
      (a := poly.add (pFamN m) (poly.add (pFamN (m + 1)) (pFamN (m + 1))))
      (a' := poly.add (pFamN m) (poly.add (pFamN (m + 1)) (pFamN (m + 1))))
      ?_ (poly.oneValue_refl _)
    refine poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl _)
        (poly.add_congr (poly.mul_sum chordTwo (pSum m) (pFamN (m + 1)))
          (poly.oneValue_refl _))) ?_
    refine poly.oneValue_trans
      (poly.add_shuffle (pFamN m)
        (poly.add (pFamN (m + 1)) (pFamN (m + 1)))
        (poly.add (poly.mul chordTwo (pSum m))
          (poly.mul chordTwo (pFamN (m + 1)))) (pFamN (m + 1))) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.add_join (pFamN m) (poly.mul chordTwo (pSum m))
          (poly.mul chordTwo (pFamN (m + 1)))) (poly.oneValue_refl _)) ?_
    refine poly.oneValue_trans
      (poly.oneValue_symm
        (poly.add_join (poly.add (pFamN m) (poly.mul chordTwo (pSum m)))
          (poly.mul chordTwo (pFamN (m + 1)))
          (poly.add (poly.add (pFamN (m + 1)) (pFamN (m + 1)))
            (pFamN (m + 1))))) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.oneValue_trans
          (poly.add_comm (pFamN m) (poly.mul chordTwo (pSum m)))
          (chordTwo_pSum m))
        (poly.oneValue_trans
          (poly.add_join (poly.mul chordTwo (pFamN (m + 1)))
            (poly.add (pFamN (m + 1)) (pFamN (m + 1))) (pFamN (m + 1)))
          (poly.add_congr (chordTwo_join (pFamN (m + 1)))
            (poly.oneValue_refl _)))) ?_
    refine poly.oneValue_trans
      (poly.add_left_comm (pFamN (m + 1))
        (poly.mul wPoly (pFamN (m + 1))) (pFamN (m + 1))) ?_
    exact poly.oneValue_symm (poly.oneValue_trans
      (poly.add_swap3 (pFamN m)
        (poly.add (pFamN (m + 1)) (pFamN (m + 1))) (pFamN (m + 2)))
      (poly.add_congr (pFamN_rec m) (poly.oneValue_refl _)))

/-- The chord monomial against the constant `2`, the doubling's own
scale. -/
private theorem wPoly_two :
    poly.oneValue (poly.mul wPoly [BPair.ofNat 2])
      (poly.add wPoly wPoly) := by decide +kernel

/-- The families' two product reads, one joint induction at the
recursion's own two-step state: the square
`p_j p_j = p_{2j} + 2` and the neighbour cross
`p_j p_{j+1} = p_{2j+1} + p_1`, the plus read's own instances at a
root pair (`def:deck`) carried on the polynomial carrier.  The
state is the triple `(square at j, cross at j, square at j+1)`: the
cross at the successor reads the recursion against the square, and
the square at the second successor reads the recursion twice with
the cross beside it. -/
theorem deckProducts : ∀ j : Nat,
    poly.oneValue (poly.mul (pFamN j) (pFamN j))
        (poly.add (pFamN (2 * j)) [BPair.ofNat 2])
    ∧ poly.oneValue (poly.mul (pFamN j) (pFamN (j + 1)))
        (poly.add (pFamN (2 * j + 1)) wPoly)
    ∧ poly.oneValue (poly.mul (pFamN (j + 1)) (pFamN (j + 1)))
        (poly.add (pFamN (2 * (j + 1))) [BPair.ofNat 2])
  | 0 => ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  | j + 1 => by
    have hA0 := (deckProducts j).1
    have hB0 := (deckProducts j).2.1
    have hA1 : poly.oneValue (poly.mul (pFamN (j + 1)) (pFamN (j + 1)))
        (poly.add (pFamN (2 * j + 2)) [BPair.ofNat 2]) :=
      (deckProducts j).2.2
    -- the cross read at the successor
    have hmul : poly.oneValue
        (poly.add (poly.mul (pFamN j) (pFamN (j + 1)))
          (poly.mul (pFamN (j + 2)) (pFamN (j + 1))))
        (poly.add (poly.add (pFamN (2 * j + 1)) (pFamN (2 * j + 3)))
          (poly.add wPoly wPoly)) :=
      poly.oneValue_trans
        (poly.oneValue_symm
          (poly.sum_mul (pFamN j) (pFamN (j + 2)) (pFamN (j + 1))))
        (poly.oneValue_trans
          (poly.mul_congr_left (pFamN_rec j) (pFamN (j + 1)))
          (poly.oneValue_trans
            (poly.mul_assoc wPoly (pFamN (j + 1)) (pFamN (j + 1)))
            (poly.oneValue_trans (poly.mul_congr wPoly hA1)
              (poly.oneValue_trans
                (poly.mul_sum wPoly (pFamN (2 * j + 2)) [BPair.ofNat 2])
                (poly.add_congr
                  (poly.oneValue_symm (pFamN_rec (2 * j + 1)))
                  wPoly_two)))))
    have hCross : poly.oneValue
        (poly.mul (pFamN (j + 1)) (pFamN (j + 2)))
        (poly.add (pFamN (2 * j + 3)) wPoly) :=
      poly.oneValue_trans
        (poly.mul_comm (pFamN (j + 1)) (pFamN (j + 2)))
        (poly.add_cancel
          (poly.oneValue_trans
            (poly.add_congr (poly.oneValue_symm hB0) (poly.oneValue_refl _))
            (poly.oneValue_trans hmul
              (poly.add_shuffle (pFamN (2 * j + 1)) (pFamN (2 * j + 3))
                wPoly wPoly)))
          (poly.oneValue_refl _))
    -- the square read two steps on, at the cross beside the recursion
    have hstar : poly.oneValue
        (poly.add [BPair.ofNat 2] (poly.mul (pFamN (j + 2)) (pFamN j)))
        (poly.add (pFamN (2 * j + 2)) (poly.mul wPoly wPoly)) :=
      poly.add_cancel
        (poly.oneValue_trans
          (poly.oneValue_trans
            (poly.add_join (pFamN (2 * j)) [BPair.ofNat 2]
              (poly.mul (pFamN (j + 2)) (pFamN j)))
            (poly.add_congr (poly.oneValue_symm hA0)
              (poly.oneValue_refl _)))
          (poly.oneValue_trans
            (poly.oneValue_trans
              (poly.oneValue_symm
                (poly.sum_mul (pFamN j) (pFamN (j + 2)) (pFamN j)))
              (poly.oneValue_trans
                (poly.mul_congr_left (pFamN_rec j) (pFamN j))
                (poly.oneValue_trans
                  (poly.mul_assoc wPoly (pFamN (j + 1)) (pFamN j))
                  (poly.oneValue_trans
                    (poly.mul_congr wPoly
                      (poly.mul_comm (pFamN (j + 1)) (pFamN j)))
                    (poly.oneValue_trans (poly.mul_congr wPoly hB0)
                      (poly.oneValue_trans
                        (poly.mul_sum wPoly (pFamN (2 * j + 1)) wPoly)
                        (poly.add_congr
                          (poly.oneValue_symm (pFamN_rec (2 * j)))
                          (poly.oneValue_refl _))))))))
            (poly.oneValue_symm
              (poly.add_join (pFamN (2 * j)) (pFamN (2 * j + 2))
                (poly.mul wPoly wPoly)))))
        (poly.oneValue_refl _)
    have h2 : poly.oneValue
        (poly.add (poly.mul (pFamN j) (pFamN (j + 2)))
          (poly.mul (pFamN (j + 2)) (pFamN (j + 2))))
        (poly.add (poly.add (pFamN (2 * j + 2)) (pFamN (2 * j + 4)))
          (poly.mul wPoly wPoly)) :=
      poly.oneValue_trans
        (poly.oneValue_symm
          (poly.sum_mul (pFamN j) (pFamN (j + 2)) (pFamN (j + 2))))
        (poly.oneValue_trans
          (poly.mul_congr_left (pFamN_rec j) (pFamN (j + 2)))
          (poly.oneValue_trans
            (poly.mul_assoc wPoly (pFamN (j + 1)) (pFamN (j + 2)))
            (poly.oneValue_trans (poly.mul_congr wPoly hCross)
              (poly.oneValue_trans
                (poly.mul_sum wPoly (pFamN (2 * j + 3)) wPoly)
                (poly.add_congr
                  (poly.oneValue_symm (pFamN_rec (2 * j + 2)))
                  (poly.oneValue_refl _))))))
    have hSq2 : poly.oneValue
        (poly.mul (pFamN (j + 2)) (pFamN (j + 2)))
        (poly.add (pFamN (2 * j + 4)) [BPair.ofNat 2]) :=
      poly.add_cancel
        (poly.oneValue_trans
          (poly.add_congr (poly.oneValue_symm hstar) (poly.oneValue_refl _))
          (poly.oneValue_trans
            (poly.oneValue_symm
              (poly.add_join [BPair.ofNat 2]
                (poly.mul (pFamN (j + 2)) (pFamN j))
                (poly.mul (pFamN (j + 2)) (pFamN (j + 2)))))
            (poly.oneValue_trans
              (poly.add_congr (poly.oneValue_refl _)
                (poly.oneValue_trans
                  (poly.add_congr
                    (poly.mul_comm (pFamN (j + 2)) (pFamN j))
                    (poly.oneValue_refl _))
                  h2))
              (poly.oneValue_trans
                (poly.add_left_comm [BPair.ofNat 2]
                  (poly.add (pFamN (2 * j + 2)) (pFamN (2 * j + 4)))
                  (poly.mul wPoly wPoly))
                (poly.oneValue_trans
                  (poly.add_congr (poly.oneValue_refl _)
                    (poly.add_comm [BPair.ofNat 2] (poly.mul wPoly wPoly)))
                  (poly.oneValue_symm
                    (poly.add_shuffle (pFamN (2 * j + 2))
                      (poly.mul wPoly wPoly) (pFamN (2 * j + 4))
                      [BPair.ofNat 2])))))))
        (poly.oneValue_refl _)
    exact ⟨hA1, hCross, hSq2⟩

/-- The deck families' doubling identity, `lem:fiberdec`'s display:
`p_L = ⟨x:2⟩ P_L² + 2` at `2m+1 = L`, one identity of the families
over the free chord, both members polynomials on the balance-pair
carrier. -/
theorem pFamN_pSum : ∀ m : Nat,
    poly.oneValue (pFamN (2 * m + 1))
      (poly.add
        (poly.mul chordTwo (poly.mul (pSum m) (pSum m)))
        [BPair.ofNat 2])
  | 0 => by decide +kernel
  | m + 1 => by
    have hA1 : poly.oneValue
        (poly.mul (pFamN (m + 1)) (pFamN (m + 1)))
        (poly.add (pFamN (2 * m + 2)) [BPair.ofNat 2]) :=
      (deckProducts m).2.2
    have hB0 := (deckProducts m).2.1
    -- the cross term against the partial sum's read
    have hV : poly.oneValue
        (poly.add (poly.mul chordTwo
            (poly.mul (pSum m) (pFamN (m + 1))))
          (poly.mul (pFamN m) (pFamN (m + 1))))
        (poly.mul (pFamN (m + 1)) (pFamN (m + 1))) :=
      poly.oneValue_trans
        (poly.add_congr
          (poly.oneValue_symm
            (poly.mul_assoc chordTwo (pSum m) (pFamN (m + 1))))
          (poly.oneValue_refl _))
        (poly.oneValue_trans
          (poly.oneValue_symm
            (poly.sum_mul (poly.mul chordTwo (pSum m)) (pFamN m)
              (pFamN (m + 1))))
          (poly.mul_congr_left (chordTwo_pSum m) (pFamN (m + 1))))
    -- the square's expansion at the successor's partial sum
    have hExp : poly.oneValue
        (poly.mul chordTwo (poly.mul (pSum (m + 1)) (pSum (m + 1))))
        (poly.add
          (poly.add (poly.mul chordTwo (poly.mul (pSum m) (pSum m)))
            (poly.mul chordTwo
              (poly.mul (pSum m) (pFamN (m + 1)))))
          (poly.add
            (poly.mul chordTwo (poly.mul (pSum m) (pFamN (m + 1))))
            (poly.mul chordTwo
              (poly.mul (pFamN (m + 1)) (pFamN (m + 1)))))) :=
      poly.oneValue_trans
        (poly.mul_congr chordTwo
          (poly.oneValue_trans
            (poly.sum_mul (pSum m) (pFamN (m + 1)) (pSum (m + 1)))
            (poly.add_congr
              (poly.mul_sum (pSum m) (pSum m) (pFamN (m + 1)))
              (poly.oneValue_trans
                (poly.mul_sum (pFamN (m + 1)) (pSum m) (pFamN (m + 1)))
                (poly.add_congr
                  (poly.mul_comm (pFamN (m + 1)) (pSum m))
                  (poly.oneValue_refl _))))))
        (poly.oneValue_trans
          (poly.mul_sum chordTwo
            (poly.add (poly.mul (pSum m) (pSum m))
              (poly.mul (pSum m) (pFamN (m + 1))))
            (poly.add (poly.mul (pSum m) (pFamN (m + 1)))
              (poly.mul (pFamN (m + 1)) (pFamN (m + 1)))))
          (poly.add_congr
            (poly.mul_sum chordTwo (poly.mul (pSum m) (pSum m))
              (poly.mul (pSum m) (pFamN (m + 1))))
            (poly.mul_sum chordTwo
              (poly.mul (pSum m) (pFamN (m + 1)))
              (poly.mul (pFamN (m + 1)) (pFamN (m + 1))))))
    refine poly.add_cancel
      (a := poly.add (poly.mul (pFamN m) (pFamN (m + 1)))
        (poly.mul (pFamN m) (pFamN (m + 1))))
      (a' := poly.add (poly.mul (pFamN m) (pFamN (m + 1)))
        (poly.mul (pFamN m) (pFamN (m + 1))))
      ?_ (poly.oneValue_refl _)
    -- both members collect to `p_{2m+1} + w p_{m+1}²`
    refine poly.oneValue_trans
      (poly.oneValue_trans
        (poly.add_congr (poly.add_congr hB0 hB0) (poly.oneValue_refl _))
        (poly.oneValue_trans
          (poly.add_congr
            (poly.add_shuffle (pFamN (2 * m + 1)) wPoly
              (pFamN (2 * m + 1)) wPoly) (poly.oneValue_refl _))
          (poly.oneValue_trans
            (poly.oneValue_symm
              (poly.add_join
                (poly.add (pFamN (2 * m + 1)) (pFamN (2 * m + 1)))
                (poly.add wPoly wPoly) (pFamN (2 * m + 3))))
            (poly.oneValue_symm
              (poly.add_join (pFamN (2 * m + 1)) (pFamN (2 * m + 1))
                (poly.add (poly.add wPoly wPoly)
                  (pFamN (2 * m + 3)))))))) ?_
    refine poly.oneValue_symm (poly.oneValue_trans
      (poly.add_left_comm
        (poly.add (poly.mul (pFamN m) (pFamN (m + 1)))
          (poly.mul (pFamN m) (pFamN (m + 1))))
        (poly.mul chordTwo (poly.mul (pSum (m + 1)) (pSum (m + 1))))
        [BPair.ofNat 2]) ?_)
    refine poly.oneValue_trans
      (poly.add_congr hExp
        (poly.add_comm
          (poly.add (poly.mul (pFamN m) (pFamN (m + 1)))
            (poly.mul (pFamN m) (pFamN (m + 1)))) [BPair.ofNat 2])) ?_
    refine poly.oneValue_trans
      (poly.add_shuffle
        (poly.add (poly.mul chordTwo (poly.mul (pSum m) (pSum m)))
          (poly.mul chordTwo (poly.mul (pSum m) (pFamN (m + 1)))))
        (poly.add (poly.mul chordTwo
            (poly.mul (pSum m) (pFamN (m + 1))))
          (poly.mul chordTwo
            (poly.mul (pFamN (m + 1)) (pFamN (m + 1)))))
        [BPair.ofNat 2]
        (poly.add (poly.mul (pFamN m) (pFamN (m + 1)))
          (poly.mul (pFamN m) (pFamN (m + 1))))) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.add_swap3 (poly.mul chordTwo (poly.mul (pSum m) (pSum m)))
          (poly.mul chordTwo (poly.mul (pSum m) (pFamN (m + 1))))
          [BPair.ofNat 2])
        (poly.add_shuffle
          (poly.mul chordTwo (poly.mul (pSum m) (pFamN (m + 1))))
          (poly.mul chordTwo
            (poly.mul (pFamN (m + 1)) (pFamN (m + 1))))
          (poly.mul (pFamN m) (pFamN (m + 1)))
          (poly.mul (pFamN m) (pFamN (m + 1))))) ?_
    refine poly.oneValue_trans
      (poly.add_shuffle
        (poly.add (poly.mul chordTwo (poly.mul (pSum m) (pSum m)))
          [BPair.ofNat 2])
        (poly.mul chordTwo (poly.mul (pSum m) (pFamN (m + 1))))
        (poly.add (poly.mul chordTwo
            (poly.mul (pSum m) (pFamN (m + 1))))
          (poly.mul (pFamN m) (pFamN (m + 1))))
        (poly.add (poly.mul chordTwo
            (poly.mul (pFamN (m + 1)) (pFamN (m + 1))))
          (poly.mul (pFamN m) (pFamN (m + 1))))) ?_
    refine poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl _)
        (poly.add_left_comm
          (poly.mul chordTwo (poly.mul (pSum m) (pFamN (m + 1))))
          (poly.mul chordTwo
            (poly.mul (pFamN (m + 1)) (pFamN (m + 1))))
          (poly.mul (pFamN m) (pFamN (m + 1))))) ?_
    refine poly.oneValue_trans
      (poly.add_shuffle
        (poly.add (poly.mul chordTwo (poly.mul (pSum m) (pSum m)))
          [BPair.ofNat 2])
        (poly.add (poly.mul chordTwo
            (poly.mul (pSum m) (pFamN (m + 1))))
          (poly.mul (pFamN m) (pFamN (m + 1))))
        (poly.mul chordTwo
          (poly.mul (pFamN (m + 1)) (pFamN (m + 1))))
        (poly.add (poly.mul chordTwo
            (poly.mul (pSum m) (pFamN (m + 1))))
          (poly.mul (pFamN m) (pFamN (m + 1))))) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.add_congr (poly.oneValue_symm (pFamN_pSum m))
          (poly.oneValue_refl _))
        (poly.add_congr hV hV)) ?_
    refine poly.oneValue_trans
      (poly.oneValue_symm
        (poly.add_join (pFamN (2 * m + 1))
          (poly.mul chordTwo
            (poly.mul (pFamN (m + 1)) (pFamN (m + 1))))
          (poly.add (poly.mul (pFamN (m + 1)) (pFamN (m + 1)))
            (poly.mul (pFamN (m + 1)) (pFamN (m + 1)))))) ?_
    refine poly.add_congr (poly.oneValue_refl _) ?_
    refine poly.oneValue_trans
      (chordTwo_join (poly.mul (pFamN (m + 1)) (pFamN (m + 1)))) ?_
    refine poly.oneValue_trans
      (poly.mul_congr wPoly hA1)
      (poly.oneValue_trans
        (poly.mul_sum wPoly (pFamN (2 * m + 2)) [BPair.ofNat 2])
        (poly.oneValue_trans
          (poly.add_congr
            (poly.oneValue_symm (pFamN_rec (2 * m + 1))) wPoly_two)
          (poly.oneValue_trans
            (poly.oneValue_symm
              (poly.add_join (pFamN (2 * m + 1)) (pFamN (2 * m + 3))
                (poly.add wPoly wPoly)))
            (poly.add_congr (poly.oneValue_refl _)
              (poly.add_comm (pFamN (2 * m + 3))
                (poly.add wPoly wPoly))))))

/-! The residue's wrap identities at the deck symbol,
`lem:fiberdec`'s wrap sentence.  The congruence's read at a
stated multiple is `pCong`, one decidable identity per witness, and
the class read `a = b` modulo the symbol is that witness's own
existence — a class read with the left scaling and the
clearing of a congruent summand; at a located root of `P_L` a
congruence is an equality of values (`pCong_eval`), the tex's
located-root read.  On it the powers wrap at `2m+1 = L`:
`p_{L-b} = p_b` (`pFamN_wrapDown`, its index read
`pFamN_wrapIndex`) and `p_{L+b} = p_b` (`pFamN_wrapUp`), with
`p_L = 2` the doubling display's own read there (`pFamN_side`).
The route is the recursion run at the residue — the telescope
`⟨x:2⟩ P_L + p_m = p_{m+1}` (`chordTwo_pSum`) is the lower wrap's
seed, `p_L = ⟨x:2⟩ P_L² + 2` (`pFamN_pSum`) the upper wrap's, and
the relation `p_b + p_{b+2} = w p_{b+1}` carries a running pair of
keys one step at a time in each direction, the congruent summand
clearing at every step. -/

/-- The congruence's read at a stated multiple: the two members
differ by that multiple of `P_L`, one decidable identity per
witness; the class read is the witness's own existence. -/
def pCong (m : Nat) (c a b : Poly) : Prop :=
  poly.oneValue a (poly.add b (poly.mul (pSum m) c))

instance (m : Nat) (c a b : Poly) : Decidable (pCong m c a b) :=
  poly.decOneValue _ _

/-- A class read is a congruence, the multiple the null
polynomial. -/
theorem pCong_of (m : Nat) {a b : Poly} (h : poly.oneValue a b) :
    ∃ c, pCong m c a b :=
  ⟨[], poly.oneValue_trans h
    (poly.oneValue_symm (poly.add_unitTail b (poly.mul_nil (pSum m))))⟩

/-- The congruence is symmetric, the multiple's memberwise swap its
witness. -/
theorem pCong_symm {m : Nat} {a b : Poly} :
    (∃ c, pCong m c a b) → ∃ c, pCong m c b a
  | ⟨c, h⟩ =>
    ⟨poly.neg c,
      poly.oneValue_symm (poly.oneValue_trans
        (poly.add_congr h (poly.oneValue_refl (poly.mul (pSum m) (poly.neg c))))
        (poly.oneValue_trans
          (poly.oneValue_symm (poly.add_join b (poly.mul (pSum m) c)
            (poly.mul (pSum m) (poly.neg c))))
          (poly.add_unitTail b
            (poly.oneValue_unitTail
              (poly.oneValue_symm (poly.mul_sum (pSum m) c (poly.neg c)))
              (poly.mul_unitTail (pSum m) (poly.add_neg c))))))⟩

/-- The congruence is transitive, the multiples joining. -/
theorem pCong_trans {m : Nat} {a b e : Poly} :
    (∃ c, pCong m c a b) → (∃ c, pCong m c b e) → ∃ c, pCong m c a e
  | ⟨c, h1⟩, ⟨d, h2⟩ =>
    ⟨poly.add d c,
      poly.oneValue_trans h1
        (poly.oneValue_trans
          (poly.add_congr h2 (poly.oneValue_refl (poly.mul (pSum m) c)))
          (poly.oneValue_trans
            (poly.oneValue_symm
              (poly.add_join e (poly.mul (pSum m) d) (poly.mul (pSum m) c)))
            (poly.add_congr (poly.oneValue_refl e)
              (poly.oneValue_symm (poly.mul_sum (pSum m) d c)))))⟩

/-- The congruence scales on the left. -/
theorem pCong_mulL {m : Nat} (w : Poly) {a b : Poly} :
    (∃ c, pCong m c a b) → ∃ c, pCong m c (poly.mul w a) (poly.mul w b)
  | ⟨c, h⟩ =>
    ⟨poly.mul w c,
      poly.oneValue_trans (poly.mul_congr w h)
        (poly.oneValue_trans (poly.mul_sum w b (poly.mul (pSum m) c))
          (poly.add_congr (poly.oneValue_refl _)
            (poly.oneValue_trans
              (poly.oneValue_symm (poly.mul_assoc w (pSum m) c))
              (poly.oneValue_trans
                (poly.mul_congr_left (poly.mul_comm w (pSum m)) c)
                (poly.mul_assoc (pSum m) w c)))))⟩

/-- A congruent summand clears from both members. -/
private theorem pCong_cancelL {m : Nat} {s a s' b : Poly}
    (h : ∃ c, pCong m c (poly.add s a) (poly.add s' b))
    (hs : ∃ c, pCong m c s s') : ∃ c, pCong m c a b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := pCong_symm hs
  refine ⟨poly.add d c, poly.add_cancel (a := s) (a' := s) ?_
    (poly.oneValue_refl s)⟩
  refine poly.oneValue_trans hc ?_
  refine poly.oneValue_trans
    (poly.add_congr
      (poly.add_congr hd (poly.oneValue_refl b)) (poly.oneValue_refl _)) ?_
  refine poly.oneValue_trans
    (poly.add_congr
      (poly.oneValue_symm (poly.add_join s (poly.mul (pSum m) d) b))
      (poly.oneValue_refl _)) ?_
  refine poly.oneValue_trans
    (poly.oneValue_symm
      (poly.add_join s (poly.add (poly.mul (pSum m) d) b)
        (poly.mul (pSum m) c))) ?_
  refine poly.add_congr (poly.oneValue_refl s) ?_
  refine poly.oneValue_trans
    (poly.add_swap3 (poly.mul (pSum m) d) b (poly.mul (pSum m) c)) ?_
  exact poly.oneValue_trans
    (poly.add_comm (poly.add (poly.mul (pSum m) d) (poly.mul (pSum m) c)) b)
    (poly.add_congr (poly.oneValue_refl b)
      (poly.oneValue_symm (poly.mul_sum (pSum m) d c)))

/-- At a located root of the deck symbol a congruence is an
equality of values, the tex's own located-root read. -/
theorem pCong_eval {m : Nat} {a b : Poly} (h : ∃ c, pCong m c a b)
    (r : BPair)
    (hr : poly.isRoot (pSum m) r) :
    (poly.eval a r).oneValue (poly.eval b r) := by
  obtain ⟨c, hc⟩ := h
  refine BPair.oneValue_trans (poly.eval_congr hc r) ?_
  refine BPair.oneValue_trans
    (poly.eval_add b (poly.mul (pSum m) c) r) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (poly.eval_mul (pSum m) c r)
        (BPair.oneValue_trans
          (BPair.mul_congr hr (BPair.oneValue_refl (poly.eval c r)))
          (BPair.unit_mul (poly.eval c r))))) ?_
  exact BPair.add_unit _

/-! The residue's wrap identities at the deck symbol, `lem:fiberdec`'s
wrap sentence: the powers wrap at `2m+1 = L`, `p_{L-b} = p_b` and
`p_{L+b} = p_b` modulo `P_L`, with `p_L = 2` the doubling display's
own read there.  The route is the recursion run at the residue: the
telescope `⟨x:2⟩ P_L + p_m = p_{m+1}` (`chordTwo_pSum`) is the lower
wrap's own seed, the recursion `p_b + p_{b+2} = w p_{b+1}` carries
the pair one key at a time in each direction, and the congruent
summand clears at every step. -/

/-- The lower wrap's seed, the telescope read at the residue:
`p_{m+1} = p_m` modulo `P_L`, the keys `m` and `m+1 = L - m`. -/
private theorem pFamN_wrapSeed (m : Nat) :
    ∃ c, pCong m c (pFamN (m + 1)) (pFamN m) :=
  ⟨chordTwo,
    poly.oneValue_trans (poly.oneValue_symm (chordTwo_pSum m))
      (poly.oneValue_trans
        (poly.add_comm (poly.mul chordTwo (pSum m)) (pFamN m))
        (poly.add_congr (poly.oneValue_refl (pFamN m))
          (poly.mul_comm chordTwo (pSum m))))⟩

/-- The lower wrap's two running keys, one joint descent from the
seed: at `b + k = m` the keys `m + k + 1` and `m + k` read the keys
`b` and `b + 1` at the residue, the recursion run on both members
with the congruent summand clearing. -/
private theorem pFamN_wrapPair (m : Nat) : ∀ (k b : Nat), b + k = m →
    (∃ c, pCong m c (pFamN (m + k + 1)) (pFamN b))
    ∧ ∃ c, pCong m c (pFamN (m + k)) (pFamN (b + 1))
  | 0, b, hb => by
    have hbm : b = m := hb
    subst hbm
    exact ⟨pFamN_wrapSeed b, pCong_symm (pFamN_wrapSeed b)⟩
  | k + 1, b, hb => by
    have hb' : b + 1 + k = m := (Nat.succ_add b k).trans hb
    have ih := pFamN_wrapPair m k (b + 1) hb'
    refine ⟨?_, ih.1⟩
    refine pCong_cancelL (s' := pFamN (b + 2)) ?_ ih.2
    refine pCong_trans (pCong_of m (pFamN_rec (m + k))) ?_
    refine pCong_trans (pCong_mulL wPoly ih.1) ?_
    exact pCong_trans
      (pCong_of m (poly.oneValue_symm (pFamN_rec b)))
      (pCong_of m (poly.add_comm (pFamN b) (pFamN (b + 2))))

/-- The lower wrap at the residue, `p_{L-b} = p_b` modulo `P_L`:
at `b + k = m` the key `m + k + 1` is `L - b` at `2m+1 = L`
(`pFamN_wrapIndex`), and the family reads the key `b`'s own residue
there. -/
theorem pFamN_wrapDown (m k b : Nat) (h : b + k = m) :
    ∃ c, pCong m c (pFamN (m + k + 1)) (pFamN b) :=
  (pFamN_wrapPair m k b h).1

/-- The lower wrap's index read: the wrapped key joins its own at
the side, `(m + k + 1) + b = L` at `2m + 1 = L`. -/
theorem pFamN_wrapIndex (m k b : Nat) (h : b + k = m) :
    m + k + 1 + b = 2 * m + 1 := by
  rw [Nat.add_right_comm (m + k) 1 b, Nat.add_assoc m k b,
    Nat.add_comm k b, h, Nat.two_mul]

/-- The doubling display at the residue: `p_L = 2` modulo `P_L`,
the identity `p_L = ⟨x:2⟩ P_L² + 2` read at the divisor. -/
theorem pFamN_side (m : Nat) :
    ∃ c, pCong m c (pFamN (2 * m + 1)) (pFamN 0) :=
  ⟨poly.mul chordTwo (pSum m),
    poly.oneValue_trans (pFamN_pSum m)
      (poly.oneValue_trans
        (poly.add_comm (poly.mul chordTwo (poly.mul (pSum m) (pSum m)))
          [BPair.ofNat 2])
        (poly.add_congr (poly.oneValue_refl [BPair.ofNat 2])
          (poly.oneValue_trans
            (poly.oneValue_symm (poly.mul_assoc chordTwo (pSum m) (pSum m)))
            (poly.oneValue_trans
              (poly.mul_congr_left (poly.mul_comm chordTwo (pSum m)) (pSum m))
              (poly.mul_assoc (pSum m) chordTwo (pSum m))))))⟩

/-- The upper wrap's seed at the first key: `p_{L+1} = p_1` modulo
`P_L`, the recursion at the key `L - 1` against the side read. -/
private theorem pFamN_upSeed (m : Nat) :
    ∃ c, pCong m c (pFamN (2 * m + 2)) (pFamN 1) := by
  have hmm : m + m = 2 * m := (Nat.two_mul m).symm
  have hB : ∃ c, pCong m c (pFamN (2 * m)) (pFamN 1) := by
    have h := (pFamN_wrapPair m m 0 (Nat.zero_add m)).2
    rw [hmm] at h
    exact h
  refine pCong_cancelL (s' := pFamN 1) ?_ hB
  refine pCong_trans (pCong_of m (pFamN_rec (2 * m))) ?_
  refine pCong_trans (pCong_mulL wPoly (pFamN_side m)) ?_
  exact pCong_of m wPoly_two

/-- The upper wrap's two running keys, one joint ascent from the
side read: `p_{L+b} = p_b` and `p_{L+b+1} = p_{b+1}` at the residue,
the recursion carried key by key. -/
private theorem pFamN_wrapUpPair (m : Nat) : ∀ b : Nat,
    (∃ c, pCong m c (pFamN (2 * m + 1 + b)) (pFamN b))
    ∧ ∃ c, pCong m c (pFamN (2 * m + 1 + (b + 1))) (pFamN (b + 1))
  | 0 => ⟨pFamN_side m, pFamN_upSeed m⟩
  | b + 1 => by
    have ih := pFamN_wrapUpPair m b
    refine ⟨ih.2, ?_⟩
    refine pCong_cancelL (s' := pFamN b) ?_ ih.1
    refine pCong_trans (pCong_of m (pFamN_rec (2 * m + 1 + b))) ?_
    refine pCong_trans (pCong_mulL wPoly ih.2) ?_
    exact pCong_of m (poly.oneValue_symm (pFamN_rec b))

/-- The upper wrap at the residue, `p_{L+b} = p_b` modulo `P_L` at
every key. -/
theorem pFamN_wrapUp (m b : Nat) :
    ∃ c, pCong m c (pFamN (2 * m + 1 + b)) (pFamN b) :=
  (pFamN_wrapUpPair m b).1

/-- The wrap at the reflected join, `p_{L-b} = p_b` modulo `P_L`
read at every key pair joining to `L`, the wrap display
unrestricted: the lower key's own wrap reads both orders. -/
theorem pFamN_wrapRefl (m b k : Nat) (h : b + k = 2 * m + 1) :
    ∃ c, pCong m c (pFamN b) (pFamN k) := by
  cases Nat.lt_or_ge m b with
  | inl hlt =>
    obtain ⟨g, hg⟩ := Nat.le.dest hlt
    have h2 : m + 1 + (g + k) = m + 1 + m := by
      rw [← Nat.add_assoc (m + 1) g k, hg, h, Nat.two_mul,
        Nat.add_right_comm m m 1]
    have hgk : g + k = m := ground.addCancelL (m + 1) h2
    have hb : b = m + g + 1 := by
      rw [← hg, Nat.add_right_comm m 1 g]
    rw [hb]
    exact pFamN_wrapDown m g k (by rw [Nat.add_comm k g]; exact hgk)
  | inr hge =>
    obtain ⟨g, hg⟩ := Nat.le.dest hge
    have h2 : b + k = b + (g + (m + 1)) := by
      rw [h, ← Nat.add_assoc b g (m + 1), hg, Nat.two_mul,
        Nat.add_assoc m m 1]
    have hk2 : k = m + g + 1 := by
      rw [ground.addCancelL b h2, Nat.add_comm g (m + 1),
        Nat.add_right_comm m 1 g]
    rw [hk2]
    exact pCong_symm (pFamN_wrapDown m g b hg)

/-- The congruence joins on the left, the multiple carried whole. -/
theorem pCong_addL {m : Nat} (s : Poly) {a b : Poly} :
    (∃ c, pCong m c a b) →
    ∃ c, pCong m c (poly.add s a) (poly.add s b)
  | ⟨c, h⟩ =>
    ⟨c, poly.oneValue_trans (poly.add_congr (poly.oneValue_refl s) h)
      (poly.add_join s b (poly.mul (pSum m) c))⟩

/-- The congruence joins on both members, the one-sided join run
at each side across the sum's exchange. -/
theorem pCong_addBoth {m : Nat} {a a' b b' : Poly}
    (h1 : ∃ c, pCong m c a a') (h2 : ∃ c, pCong m c b b') :
    ∃ c, pCong m c (poly.add a b) (poly.add a' b') :=
  pCong_trans (pCong_addL a h2)
    (pCong_trans (pCong_of m (poly.add_comm a b'))
      (pCong_trans (pCong_addL b' h1)
        (pCong_of m (poly.add_comm b' a'))))

/-- The congruence multiplies on both members, the one-sided
scaling run at each factor across the product's exchange. -/
theorem pCong_mulBoth {m : Nat} {a a' b b' : Poly}
    (h1 : ∃ c, pCong m c a a') (h2 : ∃ c, pCong m c b b') :
    ∃ c, pCong m c (poly.mul a b) (poly.mul a' b') :=
  pCong_trans (pCong_mulL a h2)
    (pCong_trans (pCong_of m (poly.mul_comm a b'))
      (pCong_trans (pCong_mulL b' h1)
        (pCong_of m (poly.mul_comm b' a'))))

/-- The recursion read cyclically at the residue, interior keys:
`p_b + p_{b+2} = w p_{b+1}` modulo `P_L`, the relation's own
display as a class read. -/
theorem pFamN_cycMid (m b : Nat) :
    ∃ c, pCong m c (poly.add (pFamN b) (pFamN (b + 2)))
      (poly.mul wPoly (pFamN (b + 1))) :=
  pCong_of m (pFamN_rec b)

/-- The recursion read cyclically at the residue, the seed row:
`p_1 + p_{L-1} = w p_0` modulo `P_L` at the top key's wrap, the
last key spelled `2m` at `2m + 1 = L`. -/
theorem pFamN_cycBot (m : Nat) :
    ∃ c, pCong m c (poly.add (pFamN 1) (pFamN (2 * m)))
      (poly.mul wPoly (pFamN 0)) := by
  have hmm : m + m = 2 * m := (Nat.two_mul m).symm
  have hB : ∃ c, pCong m c (pFamN (2 * m)) (pFamN 1) := by
    have h := (pFamN_wrapPair m m 0 (Nat.zero_add m)).2
    rw [hmm] at h
    exact h
  refine pCong_trans (pCong_addL (pFamN 1) hB) ?_
  exact pCong_of m (by decide +kernel)

/-- The recursion read cyclically at the residue, the last row:
the join `p_L + p_{L-2} = w p_{L-1}` modulo `P_L`, its two wrapped
keys read at the reflected join against the seed's side read, the
recursion's display at the first key closing it; the last key is
spelled by its join `a + 1 = 2m`. -/
theorem pFamN_cycTop (m a : Nat) (h : a + 1 = 2 * m) :
    ∃ c, pCong m c (poly.add (pFamN (2 * m + 1)) (pFamN a))
      (poly.mul wPoly (pFamN (a + 1))) := by
  have hA : ∃ c, pCong m c (pFamN a) (pFamN 2) :=
    pFamN_wrapRefl m a 2 (by rw [← h])
  have hB : ∃ c, pCong m c (pFamN (a + 1)) (pFamN 1) :=
    pFamN_wrapRefl m (a + 1) 1 (by rw [h])
  refine pCong_trans (pCong_addL (pFamN (2 * m + 1)) hA) ?_
  refine pCong_trans (pCong_of m (poly.add_comm _ _)) ?_
  refine pCong_trans (pCong_addL (pFamN 2) (pFamN_side m)) ?_
  refine pCong_trans (pCong_of m (poly.add_comm _ _)) ?_
  refine pCong_trans (pCong_of m (pFamN_rec 0)) ?_
  exact pCong_mulL wPoly (pCong_symm hB)

/-- The residue at the deck symbol: `def:poly`'s division remainder
by the monic display of `P_L`. -/
def redP (m : Nat) (p : poly.Poly) : poly.Poly :=
  (poly.div ((pSum m).dropLast) p).2

/-- The deck symbol's monic display: its own lower part made monic
reads the symbol at one value, the residue's divisor read — a class
read, one value at every representative of the top. -/
def monicRead (m : Nat) : Prop :=
  poly.oneValue (poly.monic ((pSum m).dropLast)) (pSum m)

instance (m : Nat) : Decidable (monicRead m) :=
  poly.decOneValue _ _

/-! The display's own monicity, `def:deck`'s parity induction: the
symbol's length and top entry run through the recursion from the
seeds, one parity per step, and the partial sums carry the top at
the last family joined.  The counting kit below is that induction's
own plumbing — the sum's length at a dominating member, the entry
beyond a top, and the chord variable's one-key lift — and stays
private to it. -/

/-- The sum's length at a dominating first member. -/
private theorem addLenL : ∀ (p q : Poly), q.length ≤ p.length →
    (poly.add p q).length = p.length
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: _, [], _ => rfl
  | _ :: p, _ :: q, h => by
    show (poly.add p q).length + 1 = p.length + 1
    rw [addLenL p q (Nat.le_of_succ_le_succ h)]

/-- The sum's length at a dominating second member. -/
private theorem addLenR : ∀ (p q : Poly), p.length ≤ q.length →
    (poly.add p q).length = q.length
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (Nat.not_succ_le_zero _)
  | _ :: p, _ :: q, h => by
    show (poly.add p q).length + 1 = q.length + 1
    rw [addLenR p q (Nat.le_of_succ_le_succ h)]

/-- Above the first member's top the sum reads the second member's
own entry. -/
private theorem getAtAddOver : ∀ (p q : Poly) (k : Nat), p.length ≤ k →
    ground.getAt BPair.unit (poly.add p q) k = ground.getAt BPair.unit q k
  | [], _, _, _ => rfl
  | _ :: p, [], k, h => by
    show ground.getAt BPair.unit (poly.add (_ :: p) []) k = BPair.unit
    rw [poly.add_nil]
    exact ground.getAt_over BPair.unit _ k h
  | _ :: _, _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: p, _ :: q, k + 1, h =>
    getAtAddOver p q k (Nat.le_of_succ_le_succ h)

/-- The unit monomial's product keeps an occupied factor's own
length. -/
private theorem mulOne_len : ∀ (p : Poly), 1 ≤ p.length →
    (poly.mul poly.one p).length = p.length
  | [], h => absurd h (Nat.not_succ_le_zero _)
  | c :: t, _ =>
    (addLenL ((c :: t).map (fun d => BPair.ofPos Pos.one * d)) [BPair.unit]
      (by rw [ground.length_map]; exact Nat.succ_le_succ (Nat.zero_le _))).trans
      (ground.length_map _ (c :: t))

/-- The chord variable's product lifts an occupied factor's length
by one, the one-key shift's own count. -/
private theorem mulW_len (p : Poly) (h : 1 ≤ p.length) :
    (poly.mul wPoly p).length = p.length + 1 := by
  have hin : (poly.mul poly.one p).length + 1 = p.length + 1 := by
    rw [mulOne_len p h]
  refine Eq.trans (addLenR (p.map (fun d => BPair.unit * d))
    (BPair.unit :: poly.mul poly.one p) ?_) hin
  rw [ground.length_map]
  show p.length ≤ (poly.mul poly.one p).length + 1
  rw [mulOne_len p h]
  exact Nat.le_succ p.length

/-- The families' joint shape at a key: each running member's
length is its own degree read and each top entry reads the scalar
one, the recursion moving one parity per step from the seeds. -/
private theorem pPair_shape : ∀ n : Nat,
    ((pPair (ground.posOfSucc n)).1.length = n + 2
      ∧ (ground.getAt BPair.unit (pPair (ground.posOfSucc n)).1
          (n + 1)).oneValue (BPair.ofPos Pos.one))
    ∧ ((pPair (ground.posOfSucc n)).2.length = n + 3
      ∧ (ground.getAt BPair.unit (pPair (ground.posOfSucc n)).2
          (n + 2)).oneValue (BPair.ofPos Pos.one))
  | 0 => ⟨⟨rfl, by decide +kernel⟩, ⟨rfl, by decide +kernel⟩⟩
  | n + 1 => by
    have ih := pPair_shape n
    have hB : 1 ≤ (pPair (ground.posOfSucc n)).2.length := by
      rw [ih.2.1]
      exact Nat.succ_le_succ (Nat.zero_le _)
    have hlen : (poly.mul wPoly (pPair (ground.posOfSucc n)).2).length
        = n + 4 := by
      rw [mulW_len _ hB, ih.2.1]
    have hmap : ((pPair (ground.posOfSucc n)).1.map BPair.swap).length
        = n + 2 := by
      rw [ground.length_map]; exact ih.1.1
    refine ⟨⟨ih.2.1, ih.2.2⟩, ⟨?_, ?_⟩⟩
    · show (poly.add (poly.mul wPoly (pPair (ground.posOfSucc n)).2)
        ((pPair (ground.posOfSucc n)).1.map BPair.swap)).length = n + 4
      refine Eq.trans (addLenL _ _ ?_) hlen
      rw [hmap, hlen]
      exact Nat.le_succ_of_le (Nat.le_succ (n + 2))
    · show (ground.getAt BPair.unit
        (poly.add (poly.mul wPoly (pPair (ground.posOfSucc n)).2)
          ((pPair (ground.posOfSucc n)).1.map BPair.swap))
        (n + 3)).oneValue (BPair.ofPos Pos.one)
      refine BPair.oneValue_trans
        (poly.oneValue_getAt (n + 3)
          (poly.add_comm (poly.mul wPoly (pPair (ground.posOfSucc n)).2)
            ((pPair (ground.posOfSucc n)).1.map BPair.swap))) ?_
      rw [getAtAddOver _ _ (n + 3) (by rw [hmap]; exact Nat.le_succ (n + 2))]
      exact BPair.oneValue_trans
        (poly.oneValue_getAt (n + 3) (mulX_read (pPair (ground.posOfSucc n)).2))
        ih.2.2

/-- The deck symbol's own shape at every side: the partial sum's
length is its degree read and its top entry reads the scalar one,
the top sitting at the last family joined. -/
private theorem pSum_shape : ∀ m : Nat,
    (pSum m).length = m + 1
    ∧ (ground.getAt BPair.unit (pSum m) m).oneValue (BPair.ofPos Pos.one)
  | 0 => ⟨rfl, BPair.oneValue_refl _⟩
  | m + 1 => by
    have ih := pSum_shape m
    have hf := pPair_shape m
    have hle : (pSum m).length ≤ (pFam (ground.posOfSucc m)).length := by
      rw [ih.1, show (pFam (ground.posOfSucc m)).length = m + 2 from hf.1.1]
      exact Nat.le_succ (m + 1)
    refine ⟨?_, ?_⟩
    · show (poly.add (pSum m) (pFam (ground.posOfSucc m))).length = m + 2
      exact Eq.trans (addLenR _ _ hle) hf.1.1
    · show (ground.getAt BPair.unit
        (poly.add (pSum m) (pFam (ground.posOfSucc m))) (m + 1)).oneValue
        (BPair.ofPos Pos.one)
      rw [getAtAddOver _ _ (m + 1) (by rw [ih.1]; exact Nat.le_refl (m + 1))]
      exact hf.1.2

/-- The deck symbol's monic display holds at every side: the
families' tops read the scalar one through the recursion, one
parity per step from the seeds, and the partial sums keep the top
at the last family joined. -/
theorem pSum_monic (m : Nat) : monicRead m :=
  poly.monic_dropLast_oneValue (pSum m) m (pSum_shape m).1 (pSum_shape m).2

/-- The family's length at every key, the degree's successor
(`def:deck`: `p_b` monic of degree `b`, the recursion's running
pair reading its two degrees jointly). -/
theorem pFamN_len : ∀ b : Nat, (pFamN b).length = b + 1
  | 0 => rfl
  | b + 1 => (pPair_shape b).1.1

/-- The family's top reads the scalar one off the seed, the running
pair's unit tops (`def:deck`); the seed's own top is the scalar
two, its display's read. -/
theorem pFamN_top (b : Nat) :
    (ground.getAt BPair.unit (pFamN (b + 1)) (b + 1)).oneValue
      (BPair.ofPos Pos.one) :=
  (pPair_shape b).1.2

/-- The division display read as a congruence: every polynomial is
congruent to its residue at the deck symbol, the quotient the
stated multiple. -/
theorem redP_pCong (m : Nat) (p : Poly) :
    ∃ c, pCong m c p (redP m p) := by
  have hm' : poly.oneValue (poly.monic ((pSum m).dropLast)) (pSum m) :=
    pSum_monic m
  have h : poly.oneValue
      (poly.add (poly.mul (pSum m) (poly.div ((pSum m).dropLast) p).1)
        (poly.div ((pSum m).dropLast) p).2) p :=
    poly.oneValue_trans
      (poly.add_congr
        (poly.mul_congr_left (poly.oneValue_symm hm')
          (poly.div ((pSum m).dropLast) p).1)
        (poly.oneValue_refl (poly.div ((pSum m).dropLast) p).2))
      (poly.div_identity ((pSum m).dropLast) p)
  exact ⟨(poly.div ((pSum m).dropLast) p).1,
    poly.oneValue_trans (poly.oneValue_symm h)
      (poly.add_comm (poly.mul (pSum m) (poly.div ((pSum m).dropLast) p).1)
        (poly.div ((pSum m).dropLast) p).2)⟩

/-- The congruence collapses at the residue: two congruent
polynomials read one residue. -/
theorem redP_congr (m : Nat) {a b : Poly}
    (h : ∃ c, pCong m c a b) :
    poly.oneValue (redP m a) (redP m b) := by
  obtain ⟨c, hc⟩ := h
  have hm' : poly.oneValue (poly.monic ((pSum m).dropLast)) (pSum m) :=
    pSum_monic m
  have hb : poly.oneValue
      (poly.add (poly.mul (pSum m) (poly.div ((pSum m).dropLast) b).1)
        (poly.div ((pSum m).dropLast) b).2) b :=
    poly.oneValue_trans
      (poly.add_congr
        (poly.mul_congr_left (poly.oneValue_symm hm')
          (poly.div ((pSum m).dropLast) b).1)
        (poly.oneValue_refl (poly.div ((pSum m).dropLast) b).2))
      (poly.div_identity ((pSum m).dropLast) b)
  refine poly.oneValue_symm
    (poly.div_unique ((pSum m).dropLast) a
      (poly.add (poly.div ((pSum m).dropLast) b).1 c)
      (poly.div ((pSum m).dropLast) b).2
      (poly.div_len ((pSum m).dropLast) b) ?_).2
  refine poly.oneValue_trans
    (poly.add_congr
      (poly.mul_congr_left hm'
        (poly.add (poly.div ((pSum m).dropLast) b).1 c))
      (poly.oneValue_refl (poly.div ((pSum m).dropLast) b).2)) ?_
  refine poly.oneValue_trans
    (poly.add_congr
      (poly.mul_sum (pSum m) (poly.div ((pSum m).dropLast) b).1 c)
      (poly.oneValue_refl (poly.div ((pSum m).dropLast) b).2)) ?_
  refine poly.oneValue_trans
    (poly.add_swap3 (poly.mul (pSum m) (poly.div ((pSum m).dropLast) b).1)
      (poly.mul (pSum m) c) (poly.div ((pSum m).dropLast) b).2) ?_
  refine poly.oneValue_trans
    (poly.add_congr hb (poly.oneValue_refl (poly.mul (pSum m) c))) ?_
  exact poly.oneValue_symm hc

/-- The residue carries the memberwise swap: the division display
negated is the negated dividend's own display, so the negated
residue reads the residue of the negation. -/
theorem redP_neg (m : Nat) (p : Poly) :
    poly.oneValue (redP m (poly.neg p)) (poly.neg (redP m p)) := by
  have hlen : (poly.neg (poly.div ((pSum m).dropLast) p).2).length
      = ((pSum m).dropLast).length :=
    (ground.length_map BPair.swap (poly.div ((pSum m).dropLast) p).2).trans
      (poly.div_len ((pSum m).dropLast) p)
  have hid : poly.oneValue
      (poly.add (poly.mul (poly.monic ((pSum m).dropLast))
          (poly.neg (poly.div ((pSum m).dropLast) p).1))
        (poly.neg (poly.div ((pSum m).dropLast) p).2))
      (poly.neg p) := by
    rw [← poly.neg_prod, ← poly.neg_sum]
    exact poly.swapMap_oneValue (poly.div_identity ((pSum m).dropLast) p)
  exact poly.oneValue_symm
    (poly.div_unique ((pSum m).dropLast) (poly.neg p) _ _ hlen hid).2

/-- The congruence carries the memberwise swap, the multiple
swapped with it. -/
theorem pCong_neg (m : Nat) {a b : Poly} :
    (∃ c, pCong m c a b) →
    ∃ c, pCong m c (poly.neg a) (poly.neg b)
  | ⟨c, h⟩ => ⟨poly.neg c, by
      have hs : poly.oneValue (poly.neg a)
          (poly.neg (poly.add b (poly.mul (pSum m) c))) :=
        poly.swapMap_oneValue h
      rw [poly.neg_sum, poly.neg_prod] at hs
      exact hs⟩

/-- The last key drops off a nonempty list's own length. -/
private theorem dropLast_succ : ∀ (a : BPair) (l : Poly),
    (a :: l).dropLast.length = l.length
  | _, [] => rfl
  | _, b :: t => congrArg Nat.succ (dropLast_succ b t)

/-- The deck symbol's below-top list carries the depth's own
length. -/
theorem pSum_dropLast_len (m : Nat) :
    ((pSum m).dropLast).length = m := by
  have h : (pSum m).length = m + 1 := (pSum_shape m).1
  cases hp : pSum m with
  | nil =>
    rw [hp] at h
    exact Nat.noConfusion h
  | cons a l =>
    rw [hp] at h
    rw [dropLast_succ a l]
    exact Nat.succ.inj h

/-- A polynomial below the divisor's top is its own residue: the
division display reads the null quotient there, the remainder the
polynomial padded at the sum's unit. -/
theorem redP_short (m : Nat) (p : Poly) (h : p.length ≤ m) :
    poly.oneValue (redP m p) p := by
  have hs : ((pSum m).dropLast).length = m := pSum_dropLast_len m
  refine poly.oneValue_trans
    (poly.oneValue_symm
      (poly.div_unique ((pSum m).dropLast) p []
        (p ++ List.replicate (m - p.length) BPair.unit) ?_ ?_).2)
    (poly.append_unit p (poly.unitTail_replicate _))
  · rw [ground.length_append, ground.length_replicate,
      ground.natAddSubCancel h, hs]
  · exact poly.oneValue_trans
      (poly.unitTail_add (poly.mul_nil (poly.monic ((pSum m).dropLast)))
        (p ++ List.replicate (m - p.length) BPair.unit))
      (poly.append_unit p (poly.unitTail_replicate _))

/-- The residue reads the congruence back: one residue value is
itself a stated-multiple witness, so the two spellings read one
class. -/
theorem pCong_of_redP (m : Nat) {a b : Poly}
    (h : poly.oneValue (redP m a) (redP m b)) :
    ∃ c, pCong m c a b :=
  pCong_trans (redP_pCong m a)
    (pCong_trans (pCong_of m h) (pCong_symm (redP_pCong m b)))

/-! The band's partner end, `lem:fiberdec`'s second divided
cofactor.  The deck symbol's band closes at two linear divisors: the
chord's own `⟨x : 2⟩` with the side `2m+1 = L` its remainder
(`divTwo`), and the partner `⟨x : 2̌⟩` whose root is the chord's
balance partner.  There the family alternates — every key reads the
doubled parity member of its own depth (`pFamN_partner`) — and the
partial sums read that member itself, `P_L(2̌) = 1` at even depth and
its swap at odd (`pSum_partner`, `divPartner`).  The two ends'
quotients multiply to the band's Gram witness (`gramCof`), and each
divisor against its own quotient reads the swapped remainder at the
symbol's own multiple (`cofTwo_pCong`, `cofPartner_pCong`). -/

/-- The depth's parity member: the product's unit at an even depth
and its balance partner at an odd one, the two-step recursion the
alternation itself. -/
def parityMember : Nat → BPair
  | 0 => BPair.ofNat 1
  | 1 => (BPair.ofNat 1).swap
  | m + 2 => parityMember m

private theorem parityMember_alt : ∀ m : Nat,
    parityMember (m + 1) = (parityMember m).swap
  | 0 => rfl
  | 1 => rfl
  | m + 2 => parityMember_alt m

/-- The parity member alternates one depth at a time, the two-step
recursion read at every successor. -/
theorem parityMember_succ (m : Nat) :
    parityMember (m + 1) = (parityMember m).swap := parityMember_alt m

/-- The parity member is the product's unit or its balance
partner. -/
theorem parityMember_cases : ∀ k : Nat,
    parityMember k = BPair.ofNat 1 ∨
    parityMember k = (BPair.ofNat 1).swap
  | 0 => Or.inl rfl
  | k + 1 => by
    rw [parityMember_succ k]
    cases parityMember_cases k with
    | inl h => rw [h]; exact Or.inr rfl
    | inr h => rw [h, BPair.swap_swap]; exact Or.inl rfl

/-- The recursion's own arithmetic at the partner point: the chord's
value there against a doubled swapped member, joined to the swap of
the doubled member, reads that doubled member back. -/
private theorem partner_step_arith (e : BPair) :
    (((BPair.ofNat 2).swap * (BPair.ofNat 2 * e.swap))
      + (BPair.ofNat 2 * e).swap).oneValue (BPair.ofNat 2 * e) := by
  rw [← BPair.mul_swap (BPair.ofNat 2) e,
    ← BPair.mul_assoc (BPair.ofNat 2).swap (BPair.ofNat 2) e.swap,
    ← BPair.right_distrib ((BPair.ofNat 2).swap * BPair.ofNat 2)
      (BPair.ofNat 2) e.swap,
    ← BPair.swap_mul_swap (BPair.ofNat 2) e]
  exact BPair.mul_congr_left (by decide +kernel)

/-- The partial sum's own arithmetic at the partner point: a member
joined to the doubled swap of itself reads that swap. -/
private theorem pSum_step_arith (e : BPair) :
    (e + BPair.ofNat 2 * e.swap).oneValue e.swap := by
  have he : ((BPair.ofNat 1).swap * e.swap).oneValue e := by
    rw [BPair.swap_mul_swap (BPair.ofNat 1) e,
      BPair.mul_comm (BPair.ofNat 1) e]
    exact BPair.mul_ofNat_one e
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_symm he)
      (BPair.oneValue_refl (BPair.ofNat 2 * e.swap))) ?_
  rw [← BPair.right_distrib (BPair.ofNat 1).swap (BPair.ofNat 2) e.swap]
  refine BPair.oneValue_trans
    (BPair.mul_congr_left (x' := BPair.ofNat 1) (by decide +kernel)) ?_
  rw [BPair.mul_comm (BPair.ofNat 1) e.swap]
  exact BPair.mul_ofNat_one e.swap

/-- The recursion's step at the partner point: two running members
reading a doubled parity member and its swap join, at the relation's
own display, to that doubled member again. -/
private theorem step_partner {a b : Poly} {e : BPair}
    (ha : (poly.eval a ((BPair.ofNat 2).swap)).oneValue
      (BPair.ofNat 2 * e))
    (hb : (poly.eval b ((BPair.ofNat 2).swap)).oneValue
      (BPair.ofNat 2 * e.swap)) :
    (poly.eval (poly.add (poly.mul wPoly b) (a.map BPair.swap))
      ((BPair.ofNat 2).swap)).oneValue (BPair.ofNat 2 * e) :=
  BPair.oneValue_trans
    (poly.eval_add (poly.mul wPoly b) (a.map BPair.swap)
      ((BPair.ofNat 2).swap))
    (BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (poly.eval_mul wPoly b ((BPair.ofNat 2).swap))
          (BPair.mul_congr
            (show (poly.eval wPoly ((BPair.ofNat 2).swap)).oneValue
              ((BPair.ofNat 2).swap) by decide +kernel) hb))
        (BPair.oneValue_trans (eval_swapMap a ((BPair.ofNat 2).swap))
          (ground.swap_congr ha)))
      (partner_step_arith e))

/-- The family's two running keys at the partner point, one joint
induction from the seeds: each reads the doubled parity member of
its own depth. -/
private theorem pFamN_partnerPair : ∀ n : Nat,
    (poly.eval (pFamN (n + 1)) ((BPair.ofNat 2).swap)).oneValue
      (BPair.ofNat 2 * parityMember (n + 1))
    ∧ (poly.eval (pFamN (n + 2)) ((BPair.ofNat 2).swap)).oneValue
      (BPair.ofNat 2 * parityMember (n + 2))
  | 0 => ⟨by decide +kernel, by decide +kernel⟩
  | n + 1 => by
    have ih := pFamN_partnerPair n
    refine ⟨ih.2, ?_⟩
    have hb : (poly.eval (pFamN (n + 2)) ((BPair.ofNat 2).swap)).oneValue
        (BPair.ofNat 2 * (parityMember (n + 1)).swap) := by
      rw [← parityMember_succ (n + 1)]
      exact ih.2
    exact step_partner ih.1 hb

/-- The seeded family at the partner chord: every key reads the
doubled parity member of its own depth, the recursion's own read
from the seeds. -/
theorem pFamN_partner (b : Nat) :
    (poly.eval (pFamN b) ((BPair.ofNat 2).swap)).oneValue
      (BPair.ofNat 2 * parityMember b) := by
  cases b with
  | zero => decide
  | succ n => exact (pFamN_partnerPair n).1

private theorem pSum_partnerRec : ∀ m : Nat,
    (poly.eval (pSum m) ((BPair.ofNat 2).swap)).oneValue (parityMember m)
  | 0 => by decide +kernel
  | m + 1 => by
    refine BPair.oneValue_trans
      (poly.eval_add (pSum m) (pFam (ground.posOfSucc m))
        ((BPair.ofNat 2).swap)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (pSum_partnerRec m) (pFamN_partner (m + 1))) ?_
    rw [parityMember_succ m]
    exact pSum_step_arith (parityMember m)

/-- The deck symbol at the partner chord reads the depth's parity
member, the product's unit at an even depth and its balance partner
at an odd one. -/
theorem pSum_partner (m : Nat) :
    (poly.eval (pSum m) ((BPair.ofNat 2).swap)).oneValue (parityMember m) :=
  pSum_partnerRec m

/-- The monic linear factor at the band's partner end, the second
division display's own divisor (`def:poly`'s monic spelling). -/
def chordPartner : Poly := poly.monic [BPair.ofNat 2]

/-- The division display at the partner divisor: the deck symbol
leaves its Horner read there, `P_L = q ⟨x : 2̌⟩ + ε`, the remainder
the depth's parity member. -/
def divPartnerRead (m : Nat) : Prop :=
  poly.oneValue (poly.div [BPair.ofNat 2] (pSum m)).2 [parityMember m]

instance (m : Nat) : Decidable (divPartnerRead m) := poly.decOneValue _ _

/-- The partner division display holds at every side: the remainder
is the Horner read at that divisor's own root
(`poly.div_linear_eval`), and the symbol's value there is the
depth's parity member (`pSum_partner`). -/
theorem divPartner (m : Nat) : divPartnerRead m := by
  exact poly.oneValue_trans
    (poly.div_linear_eval (BPair.ofNat 2) (pSum m))
    ⟨pSum_partner m, trivial⟩

/-- The band's two divided cofactors joined: the quotients at the
chord `2` and at its partner multiplied, `lem:fiberdec`'s Gram
witness at the band's ends. -/
def gramCof (m : Nat) : Poly :=
  poly.mul (poly.div [(BPair.ofNat 2).swap] (pSum m)).1
    (poly.div [BPair.ofNat 2] (pSum m)).1

/-- The chord end's cofactor as a class read: the divisor against
its own quotient reads the side's memberwise swap at the symbol's
own multiple. -/
theorem cofTwo_pCong (m : Nat) :
    ∃ c, pCong m c
      (poly.mul chordTwo (poly.div [(BPair.ofNat 2).swap] (pSum m)).1)
      (poly.neg [BPair.ofNat (2 * m + 1)]) := by
  refine ⟨poly.one, ?_⟩
  have hid : poly.oneValue
      (poly.add (poly.mul chordTwo
        (poly.div [(BPair.ofNat 2).swap] (pSum m)).1)
        [BPair.ofNat (2 * m + 1)]) (pSum m) :=
    poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl _)
        (poly.oneValue_symm (divTwo m)))
      (poly.div_identity [(BPair.ofNat 2).swap] (pSum m))
  refine poly.oneValue_trans
    (poly.oneValue_symm
      (poly.add_unitTail
        (poly.mul chordTwo (poly.div [(BPair.ofNat 2).swap] (pSum m)).1)
        (poly.add_neg [BPair.ofNat (2 * m + 1)]))) ?_
  refine poly.oneValue_trans
    (poly.add_join
      (poly.mul chordTwo (poly.div [(BPair.ofNat 2).swap] (pSum m)).1)
      [BPair.ofNat (2 * m + 1)]
      (poly.neg [BPair.ofNat (2 * m + 1)])) ?_
  refine poly.oneValue_trans
    (poly.add_congr hid (poly.oneValue_refl _)) ?_
  refine poly.oneValue_trans
    (poly.add_comm (pSum m) (poly.neg [BPair.ofNat (2 * m + 1)])) ?_
  exact poly.add_congr (poly.oneValue_refl _)
    (poly.oneValue_symm
      (poly.oneValue_trans (poly.mul_comm (pSum m) poly.one)
        (poly.one_mul (pSum m))))

/-- The partner end's cofactor as a class read: the partner divisor
against its own quotient reads the parity member's memberwise swap
at the symbol's own multiple. -/
theorem cofPartner_pCong (m : Nat) :
    ∃ c, pCong m c
      (poly.mul chordPartner (poly.div [BPair.ofNat 2] (pSum m)).1)
      (poly.neg [parityMember m]) := by
  refine ⟨poly.one, ?_⟩
  have hid : poly.oneValue
      (poly.add (poly.mul chordPartner
        (poly.div [BPair.ofNat 2] (pSum m)).1)
        [parityMember m]) (pSum m) :=
    poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl _)
        (poly.oneValue_symm (divPartner m)))
      (poly.div_identity [BPair.ofNat 2] (pSum m))
  refine poly.oneValue_trans
    (poly.oneValue_symm
      (poly.add_unitTail
        (poly.mul chordPartner (poly.div [BPair.ofNat 2] (pSum m)).1)
        (poly.add_neg [parityMember m]))) ?_
  refine poly.oneValue_trans
    (poly.add_join
      (poly.mul chordPartner (poly.div [BPair.ofNat 2] (pSum m)).1)
      [parityMember m] (poly.neg [parityMember m])) ?_
  refine poly.oneValue_trans
    (poly.add_congr hid (poly.oneValue_refl _)) ?_
  refine poly.oneValue_trans
    (poly.add_comm (pSum m) (poly.neg [parityMember m])) ?_
  exact poly.add_congr (poly.oneValue_refl _)
    (poly.oneValue_symm
      (poly.oneValue_trans (poly.mul_comm (pSum m) poly.one)
        (poly.one_mul (pSum m))))

end deck
