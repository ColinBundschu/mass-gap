import MassGap.Chaininstances
import MassGap.Serstable
/-!
`lem:serdivisors` — the rank divisors of the chain's comparisons at
a `B`, `C` or `D` member (`lem:serstable`(iii)) close on the
depth-two sector closures at the member's class group
(`lem:chargedcell`(i)): 47 records at `B_ℓ` and at `C_ℓ` and 83 at
`D_ℓ`, the divisors read at the derived residue `r`
(`con:sertables`).

The sectors are the unit class's, based at `θ`, and one per nonunit
class, based at the class's end member (`lem:chargedcell`(ii)): the
spinor at `B_ℓ`, the first fundamental at `C_ℓ`, and the vector
with the two spinors at `D_ℓ`.  The exchange of the last two simple
letters relabels the `D` table, the last coordinate read to its
balance partner, fixing the form and the root fold and exchanging
the two spinor classes with each sector's base, so the spinor
pair's records are one displayed list — a word of odd box count at
`D_ℓ` read at the flipped base, the flip beyond every odd word's
keys at the domain ranks, so the folds read the ones list.

A sector's families are the base with an *added word*, the fusion
row's dominant sums at the member's `θ` content list
(`lem:serstable`(ii); `prop:row`), iterated twice from a charged
sector's base and once from `θ` at the unit sector's.  Each
family's *excess gap* is the form's bilinear read at the member's
displayed data (`con:gentable`'s additive form),
`C₂(β) + gap_W = C₂(β + W)` at `gap_W = ⟨W,W⟩ + 2⟨W,β⟩ + ⟨W,2ρ⟩`,
`β` the sector's base and `W` the added word: three folds over the
word's occupied keys, the square fold and the doubled base fold
rank-free — the word's own form square and its doubled dot against
the base's list — and the root fold the word against the displayed
key reads, linear in the rank, `4(ℓ − i) + 2` at `B`,
`2(ℓ + 1 − i)` at `C` and `4(ℓ − i)` at `D`, so every gap is one
linear read at the derived residue, positive at every domain rank.
`bfold` is that three-fold read at the sector's stored
coordinates: `dotN v v + 2 dotN v b` at the constant against
`keyT w v` withdrawn, the rank's coefficient the scale against the
word's total.  The unit sectors read instead against
`C₂(θ) = 2(r + 1)` (`prop:anchor`) through `lem:serstable`(i)'s
Casimir polynomials: the identity the unit tier decides is
`casNum = casDen + gap` at `B` and `D` and
`casNum = casDen + 2 gap` at `C`, `casDen` the adjoint's own
Casimir polynomial at `θ`'s word (`denB`, `denC`, `denD`).
The spinor sectors' members are *based* — `basedM` presents such a
family in the coroot coordinates as the added word's gaps at the
leading keys, a vacant run, and a tail datum one, at the last key
for the `B` words and the even-box `D` words and at the key before
it for the odd-box `D` words read at the flipped base — and the
based member's length, shifted-key and positivity reads
(`basedV_length`, `basedKap`, `basedRho_pos`) are its whole entry
into `lem:serstable`(ii)'s row-value tier.

The records enter in the *rank* coordinate `ℓ`, the residue's fold
`r = 2ℓ − 2` at `B`, `r = ℓ` at `C` and `r = 2ℓ − 3` at `D`, where
every domain is consecutive — every even residue from two at
`B_ℓ`, every residue from three at `C_ℓ` and every odd residue
from five at `D_ℓ` — the domain floors `ℓ = 2`, `3`, `4`.  `gapL`
carries a gap's `r`-display `(m, cu, cd)` to its `ℓ`-polynomial at
the series' fold, scaled by the tier's own `k`.

Per sector the records are the family gaps and the
*frontier-binding comparisons*, the balance pairs
`⟨gap_i : gap_j⟩` over the sector's family pairs (`places.pairsOf`
at the family count), six per unit list and twenty-eight per
charged sector; and per member the stencil cap `3 d_θ` at the
member's dimension fold (`prop:row`), `3ℓ(2ℓ + 1)` at `B_ℓ` and
`C_ℓ` and `3ℓ(2ℓ − 1)` at `D_ℓ`.  The joins `10 + 36 + 1` at `B_ℓ`
and `C_ℓ` and `10 + 2·36 + 1` at `D_ℓ` are the stated counts.

The *classification* is the equal-members reads of the displayed
divisors in the rank domains, seven, each one cross-multiplied
evaluation: at `B_2` the spinor word `e₁+e₂` against the four-key
word, at `B_3` the word `2e₁` against it; at `D_4` the unit
sector's `(2)` against the key-four pair at the gap `4`, the
spinor words `e₁+e₂+e₃` and `2e₁` at the merged level `18`, and
the vector's `(1,1,1)` against the five-key word; and at the
cleared ranks the two merged levels, the spinor words
`e₁+e₂+e₃+e₄` and `2e₁+e₂` at `D_6` at the gap `36` and the
vector's `(1,1,1,1,1)` and `(3)` at `D_7` at the gap `32`, each
root a located rank point whose tied pair reads its merged level
with the counts at the multiplicity (`lem:cellcount`'s boundary
clause).  A record's settled point is its clearance raised to the
leading-term radius' least clearing point where that sits past the
clearances — the two merged levels' comparisons with the eight
constant-heavy divisors of the settled-point tables — and the
raised windows' cleared ranks read the divisor's own leading side
at `chaininstances.rootsCert`'s cleared arm.

Each record carries `lem:chaininstances`' two reads:
`chaininstances.sideCert`, `lem:genericlift`'s side theorems'
hypothesis pair at the record's settled point, and
`chaininstances.rootsCert`, the window from the domain's floor
where the divisor's evaluation ties the sum's unit exactly at the
record's roots.  `recsReadB`, `recsReadC` and `recsReadD` join the
record count, the sectors' gap identities, and both certificates
over the whole list.

Per `B` sector the displayed families are the *occupied folds*: the
moved contents `nA`–`nH` are the displayed dominant sums' coroot
vectors, each exhibited on `con:sertables`' positive list by its
`_mem` read; each displayed family's witness edge reads the letter
fold at the vacant count, so the row's two graded counts part by
one; and the collision clause's strays, the unit sector's
short-move sums at `lem:serdivisors`' displayed reads, read it
occupied, the two counts tying at the flip's own letter.  The fold
values are pure data (`serstable.letterFoldVal`), so every edge
here is unconditional in the rank window.

Per `C` sector the same reads close on the leading sources: the
moved contents `cA`--`cH` are the displayed dominant sums' coroot
vectors on `con:sertables`' `C` positive list, each witness edge
(`edgeC_u1`--`edgeC_u4`, `edgeC_w1`--`edgeC_w8`) reads the letter
fold at the vacant count, and the collision reads (`strayC_u1`,
`strayC_w1`, `strayC_w2`, `strayC_w3`) read it occupied at the long
dipole, the moved pair's second key, the tex's `C` collision
clause's four ties, the family `(3,1,1)` entering through the
two-row source at `e₁ + e₃`.

Per `D` sector the same reads close on the three bases: the unit
sector's `θ`, the vector's leading words, and the spinor pair's two
flip presentations, the odd-box words read at the flipped base with
the tail datum one key in.  The moved contents `dA`--`dH` are the
displayed dominant sums' coroot vectors on `con:sertables`' `D`
positive list, each exhibited by its `_mem` read against the fork
geometry's own column — the chain's two neighbours below the fork,
the fork key's three joined keys, and each tip against the key three
below the rank.  Each displayed family's witness edge
(`edgeD_u1`--`edgeD_u4`, `edgeD_v1`--`edgeD_v8`,
`edgeD_s1`--`edgeD_s8`) reads the letter fold at the vacant count, so
the row's two graded counts part by one: the front letters part at
the column's magnitude cap or at the leading and interior narrow
windows, the run at `serstable.runVanishD`, and the three tail
letters — the fork and its two tips — at the tail's own refusals,
where the one surviving family is the narrow window sitting at the
tail keys and the moved content's occupied leading key parts from
its vacant column there.  At `D` every dominant target off the
identity's tie reads off the moved content list, so each displayed
family's fold is the vacant one across the whole rank window.
-/

namespace serdivisors
open ground

/-! ## The rank polynomials -/

/-- A linear rank polynomial `[⟨cu : cd⟩, slope]`. -/
def linP (cu cd s : Nat) : poly.Poly :=
  [⟨ground.posOfSucc cu, ground.posOfSucc cd⟩,
   ⟨ground.posOfSucc s, ground.posOfSucc 0⟩]

/-- The `B` adjoint clearing, `θ`'s own Casimir polynomial
`C₂(θ) = 2(2ℓ − 1)` at the word `(1,1)`. -/
def denB : poly.Poly := serstable.casPolyB [1, 1]
/-- The `C` adjoint clearing, `C₂(θ) = 4(ℓ + 1)` at the word
`(2)`. -/
def denC : poly.Poly := serstable.casPolyC [2]
/-- The `D` adjoint clearing, `C₂(θ) = 4(ℓ − 1)` at the word
`(1,1)`. -/
def denD : poly.Poly := serstable.casPolyD [1, 1]

/-- A gap's `ℓ`-polynomial from its `r`-display `(m, cu, cd)` at
the series' residue fold `r = rA·ℓ − rB`, scaled by `k`. -/
def gapL (k m cu cd rA rB : Nat) : poly.Poly :=
  linP (k * cu) (k * (cd + m * rB)) (k * (m * rA))

/-! ## The charged tier's three folds -/

/-- The dot fold at the shorter list's reach. -/
def dotN : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, y :: ys => x * y + dotN xs ys

/-- The root fold: the word against the displayed key reads. -/
def keyT (w : Nat → Nat) (v : List Nat) : Nat :=
  ((List.range v.length).map
    (fun i => ground.getAt 0 v i * w (i + 1))).foldl Nat.add 0

/-- The excess gap's three folds over the added word's occupied
keys: the square fold with the doubled base fold at the constant,
the root fold's key reads withdrawn, and the rank's coefficient
the scale against the word's total. -/
def bfold (v b : List Nat) (w : Nat → Nat) (s : Nat) : poly.Poly :=
  [⟨ground.posOfSucc (dotN v v + 2 * dotN v b),
    ground.posOfSucc (keyT w v)⟩,
   ⟨ground.posOfSucc (s * ground.sumNat v), ground.posOfSucc 0⟩]

/-- The `B` root fold's key reads, `4(ℓ − i) + 2` at the derived
residue's own scale. -/
def wB (i : Nat) : Nat := 4 * i - 2
/-- The `C` root fold's key reads, `2(ℓ + 1 − i)`. -/
def wC (i : Nat) : Nat := 2 * i - 2
/-- The `D` root fold's key reads, `4(ℓ − i)`. -/
def wD (i : Nat) : Nat := 4 * i

/-- The spinor bases' coordinate list, the ones at the word's
keys. -/
def basOnes : List Nat := [1, 1, 1, 1, 1]
/-- The `C` first fundamental's base list. -/
def basC : List Nat := [1]
/-- The `D` vector's base list. -/
def basV : List Nat := [2]

/-- The doubled word. -/
private def dbl (v : List Nat) : List Nat := v.map (fun x => 2 * x)

/-- The added word of a full family word: one withdrawn from the
head entry. -/
private def subE1 : List Nat → List Nat
  | [] => []
  | a :: t => (a - 1) :: t

/-- The `C` first fundamental's stored coordinates: the added
word. -/
def vC (word : List Nat) : List Nat := subE1 word
/-- The `D` vector's stored coordinates: the doubled added word. -/
def vV (word : List Nat) : List Nat := dbl (subE1 word)
/-- The spinor sectors' stored coordinates: the doubled word. -/
def vS (word : List Nat) : List Nat := dbl word

/-! ## The committed family tables -/

set_option genInjectivity false in
/-- A family's committed datum: the sector's stored word, the gap's
`r`-display `(m, cu, cd)`, and the reach clearance. -/
structure SFam where
  word : List Nat
  m : Nat
  cu : Nat
  cd : Nat
  cl : Nat

/-- The `B` unit sector: `(2)`, `(1,1,1,1)`, `(2,1,1)`,
`(2,2) = 2θ`. -/
def unitB : List SFam :=
  [⟨[2], 0, 4, 0, 3⟩, ⟨[1, 1, 1, 1], 2, 0, 6, 6⟩,
   ⟨[2, 1, 1], 2, 2, 0, 5⟩, ⟨[2, 2], 2, 6, 0, 4⟩]

/-- The `C` unit sector: `(1,1)`, `(2,2)`, `(3,1)`,
`(4) = 2θ`. -/
def unitC : List SFam :=
  [⟨[1, 1], 0, 0, 2, 4⟩, ⟨[2, 2], 2, 0, 0, 4⟩,
   ⟨[3, 1], 2, 2, 0, 4⟩, ⟨[4], 2, 6, 0, 3⟩]

/-- The `D` unit sector, the `B` list at the `D` residue fold. -/
def unitD : List SFam :=
  [⟨[2], 0, 4, 0, 3⟩, ⟨[1, 1, 1, 1], 2, 0, 6, 6⟩,
   ⟨[2, 1, 1], 2, 2, 0, 5⟩, ⟨[2, 2], 2, 6, 0, 4⟩]

/-- The spinor list, one table for `B_ℓ` and `D_ℓ`: the added
words `e₁`, `e₁+e₂`, `e₁+e₂+e₃`, `e₁+e₂+e₃+e₄`, `2e₁`, `2e₁+e₂`,
`2e₁+e₂+e₃`, `2e₁+2e₂`. -/
def spinFams : List SFam :=
  [⟨[1], 1, 3, 0, 3⟩, ⟨[1, 1], 2, 4, 0, 4⟩,
   ⟨[1, 1, 1], 3, 3, 0, 5⟩, ⟨[1, 1, 1, 1], 4, 0, 0, 6⟩,
   ⟨[2], 2, 8, 0, 3⟩, ⟨[2, 1], 3, 9, 0, 4⟩,
   ⟨[2, 1, 1], 4, 8, 0, 5⟩, ⟨[2, 2], 4, 12, 0, 4⟩]

/-- The `C` first fundamental's sector, the stored words the full
family words. -/
def omegaC : List SFam :=
  [⟨[1, 1, 1], 2, 0, 2, 5⟩, ⟨[2, 1], 2, 1, 0, 4⟩,
   ⟨[3], 2, 4, 0, 3⟩, ⟨[2, 2, 1], 4, 0, 0, 5⟩,
   ⟨[3, 1, 1], 4, 2, 0, 5⟩, ⟨[3, 2], 4, 4, 0, 4⟩,
   ⟨[4, 1], 4, 7, 0, 4⟩, ⟨[5], 4, 12, 0, 3⟩]

/-- The `D` vector's sector, the stored words the full family
words. -/
def vecD : List SFam :=
  [⟨[1, 1, 1], 2, 0, 2, 5⟩, ⟨[2, 1], 2, 4, 0, 4⟩,
   ⟨[3], 2, 10, 0, 3⟩, ⟨[1, 1, 1, 1, 1], 4, 0, 12, 7⟩,
   ⟨[2, 1, 1, 1], 4, 0, 2, 6⟩, ⟨[2, 2, 1], 4, 4, 0, 5⟩,
   ⟨[3, 1, 1], 4, 8, 0, 5⟩, ⟨[3, 2], 4, 12, 0, 4⟩]

/-! ## The based tier: the spinor sectors' members

A spinor-sector family's member reads in the coroot presentation as
the added word's gaps at the leading keys, a vacant run, and a tail
datum one — at the last key for the `B` words and the even-box `D`
words, at the key before it for the odd-box `D` words read at the
flipped base, the flip carrying the datum one key in.  The tier
carries `lem:serstable`(ii)'s row values to that member. -/

/-- The based member at the cleared rank, the coroot presentation:
the added word's gaps with the tail datum one at the key `j` places
before the rank's last. -/
def basedM (W : List Nat) (l j : Nat) : List Nat :=
  (List.range l).map (fun i =>
    (ground.getAt 0 W i - ground.getAt 0 W (i + 1))
      + (if i + 1 + j = l then 1 else 0))

/-- The based member as a key, the coroot presentation carried onto
the balance pairs. -/
def basedV (W : List Nat) (l j : Nat) : List ground.BPair :=
  (basedM W l j).map ground.BPair.ofNat

/-- The based member's shifted-key reads, the entrywise raise
by one. -/
def basedRho (W : List Nat) (l j : Nat) : List Nat :=
  (basedM W l j).map (· + 1)

/-- The based member sits at the cleared rank's order. -/
theorem basedM_length (W : List Nat) (l j : Nat) :
    (basedM W l j).length = l :=
  ground.length_mapRange _ l

/-- The based member's entry: the added word's gap against its own
successor, raised by one at the key `j` places before the last. -/
theorem basedM_entry (W : List Nat) (l j i : Nat) (hi : i < l) :
    ground.getAt 0 (basedM W l j) i
      = (ground.getAt 0 W i - ground.getAt 0 W (i + 1))
        + (if i + 1 + j = l then 1 else 0) := by
  show ground.getAt 0 ((List.range l).map (fun i =>
    (ground.getAt 0 W i - ground.getAt 0 W (i + 1))
      + (if i + 1 + j = l then 1 else 0))) i = _
  rw [ground.getAt_map_range 0 _ l i, if_pos hi]

/-- The based member's key sits at the cleared rank's order. -/
theorem basedV_length (W : List Nat) (l j : Nat) :
    (basedV W l j).length = l := by
  show ((basedM W l j).map ground.BPair.ofNat).length = l
  rw [ground.length_map, basedM_length]

/-- The shifted key's entry: the based member's own entry raised. -/
theorem basedRho_step (W : List Nat) (l j k : Nat) (hk : k < l) :
    ground.getAt 0 (basedRho W l j) k
      = ground.getAt 0 (basedM W l j) k + 1 := by
  show ground.getAt 0 ((basedM W l j).map (· + 1)) k = _
  exact ground.getAt_map 0 0 (· + 1) (basedM W l j) k
    (by rw [basedM_length]; exact hk)

/-- The based member's shifted-key entry is occupied. -/
theorem basedRho_pos (W : List Nat) (l j k : Nat) (hk : k < l) :
    1 ≤ ground.getAt 0 (basedRho W l j) k := by
  rw [basedRho_step W l j k hk]
  exact Nat.succ_le_succ (Nat.zero_le _)

/-- The based member's shifted key reads one across the run beyond
the word's reach, off the tail's datum key. -/
theorem basedRho_run (W : List Nat) (l j i : Nat)
    (hWi : W.length ≤ i) (hi : i < l) (hij : ¬ i + 1 + j = l) :
    ground.getAt 0 (basedRho W l j) i = 1 := by
  rw [basedRho_step W l j i hi, basedM_entry W l j i hi,
    ground.getAt_over 0 W i hWi, Nat.zero_sub, if_neg hij]

/-- The based member's shifted key reads two at the tail's datum
key, beyond the word's reach. -/
theorem basedRho_datum (W : List Nat) (l j i : Nat)
    (hWi : W.length ≤ i) (hi : i < l) (hij : i + 1 + j = l) :
    ground.getAt 0 (basedRho W l j) i = 2 := by
  rw [basedRho_step W l j i hi, basedM_entry W l j i hi,
    ground.getAt_over 0 W i hWi, Nat.zero_sub, if_pos hij]

/-- The based member's shifted key at a coordinate: the shifted-key
list's own entry (`lem:serstable`(ii)'s shifted key at the based
member's values against the `ρ` run). -/
theorem basedKap (t : gentable.Table) (W : List Nat) (l j : Nat)
    (hrk : t.rank = l) (i : Nat) (hi : i < t.rank) :
    (ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd (basedV W l j) (sertables.rhoV t)))
      i).oneValue
      (BPair.ofNat (ground.getAt 0 (basedRho W l j) i)) := by
  have hil : i < l := by rw [← hrk]; exact hi
  have hml : (basedV W l j).length = t.rank := by
    rw [basedV_length, hrk]
  have hrl : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hA : (elim.vecAdd (basedV W l j) (sertables.rhoV t)).length
      = t.rank := elim.length_vecAdd _ _ t.rank hml hrl
  show (ground.getAt BPair.unit
    ((elim.vecAdd (basedV W l j) (sertables.rhoV t)).map BPair.norm)
      i).oneValue _
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ i
      (by rw [hA]; exact hi),
    elim.getAt_vecAdd _ _ i (by rw [hml]; exact hi)
      (by rw [hrl]; exact hi),
    show ground.getAt BPair.unit (sertables.rhoV t) i = BPair.ofNat 1 from
      ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank i hi,
    show ground.getAt BPair.unit (basedV W l j) i
        = BPair.ofNat (ground.getAt 0 (basedM W l j) i) from
      ground.getAt_map 0 BPair.unit BPair.ofNat (basedM W l j) i
        (by rw [basedM_length]; exact hil),
    basedRho_step W l j i hil]
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_symm (BPair.ofNat_succ _))

/-! ## The two gap identities -/

/-- A unit family's gap identity: the Casimir numerator against the
adjoint clearing raised by the gap, `casNum = casDen + k·gap`. -/
def unitRead (cas : List Nat → poly.Poly) (den : poly.Poly)
    (k rA rB : Nat) (F : SFam) : Prop :=
  poly.oneValue (cas F.word)
    (poly.add den (gapL k F.m F.cu F.cd rA rB))

instance (cas : List Nat → poly.Poly) (den : poly.Poly)
    (k rA rB : Nat) (F : SFam) :
    Decidable (unitRead cas den k rA rB F) :=
  inferInstanceAs (Decidable (poly.oneValue _ _))

/-- A charged family's gap identity: the three folds at the
sector's stored coordinates against the displayed gap. -/
def chargedRead (mk : List Nat → List Nat) (b : List Nat)
    (w : Nat → Nat) (s k rA rB : Nat) (F : SFam) : Prop :=
  poly.oneValue (bfold (mk F.word) b w s)
    (gapL k F.m F.cu F.cd rA rB)

instance (mk : List Nat → List Nat) (b : List Nat) (w : Nat → Nat)
    (s k rA rB : Nat) (F : SFam) :
    Decidable (chargedRead mk b w s k rA rB F) :=
  inferInstanceAs (Decidable (poly.oneValue _ _))

/-! ## The record lists -/

/-- The family at a place. -/
private def famAt (L : List SFam) (i : Nat) : SFam :=
  ground.getAt ⟨[], 0, 0, 0, 0⟩ L i

/-- A family's unscaled gap polynomial at the series' residue
fold. -/
private def gd (F : SFam) (rA rB : Nat) : poly.Poly :=
  gapL 1 F.m F.cu F.cd rA rB

/-- A sector's classification lookup at a record's places. -/
private def rootsAt (T : List (Nat × Nat × Nat)) (i j : Nat) :
    List Nat :=
  (T.filter
    (fun t => decide (t.1 = i) && decide (t.2.1 = j))).map
    (fun t => t.2.2)

/-- The upper of two counts. -/
private def maxNat (x y : Nat) : Nat := if x ≤ y then y else x

/-- A comparison's settled point: the upper of the compared
clearances raised to the sector's settled-point table's entry, so
a table entry can only lift the point. -/
private def anAt (S : List (Nat × Nat × Nat)) (i j cl : Nat) : Nat :=
  maxNat cl
    (ground.getAt 0
      ((S.filter
        (fun t => decide (t.1 = i) && decide (t.2.1 = j))).map
        (fun t => t.2.2)) 0)

/-- A sector's records: the family gaps at their own clearances,
then the frontier-binding comparisons over `places.pairsOf` at the
family count. -/
private def sectorRecs (L : List SFam) (T S : List (Nat × Nat × Nat))
    (rA rB lo : Nat) : List chaininstances.Rec :=
  (List.range L.length).map
      (fun i =>
        let F := famAt L i
        ⟨gd F rA rB, lo, F.cl, anAt S i i F.cl, rootsAt T i i⟩)
    ++ (places.pairsOf L.length).map
      (fun pr =>
        let Fi := famAt L pr.1
        let Fj := famAt L pr.2
        ⟨poly.add (gd Fi rA rB) (poly.neg (gd Fj rA rB)),
         lo, maxNat Fi.cl Fj.cl,
         anAt S pr.1 pr.2 (maxNat Fi.cl Fj.cl), rootsAt T pr.1 pr.2⟩)

/-- The stencil cap at `B_ℓ`, the member's dimension fold
`3·d_θ = 3ℓ(2ℓ + 1)` at `d_θ = [(r+2)(r+3):2]` over the residue
fold `r = 2ℓ − 2`. -/
def capB : poly.Poly :=
  [⟨ground.posOfSucc 0, ground.posOfSucc 0⟩,
   ⟨ground.posOfSucc 3, ground.posOfSucc 0⟩,
   ⟨ground.posOfSucc 6, ground.posOfSucc 0⟩]

/-- The stencil cap at `C_ℓ`, the member's dimension fold
`3·d_θ = 3ℓ(2ℓ + 1)` at `d_θ = r(2r + 1)` over the residue fold
`r = ℓ`. -/
def capC : poly.Poly :=
  [⟨ground.posOfSucc 0, ground.posOfSucc 0⟩,
   ⟨ground.posOfSucc 3, ground.posOfSucc 0⟩,
   ⟨ground.posOfSucc 6, ground.posOfSucc 0⟩]

/-- The stencil cap at `D_ℓ`, `3ℓ(2ℓ − 1)`. -/
def capD : poly.Poly :=
  [⟨ground.posOfSucc 0, ground.posOfSucc 0⟩,
   ⟨ground.posOfSucc 0, ground.posOfSucc 3⟩,
   ⟨ground.posOfSucc 6, ground.posOfSucc 0⟩]

/-- The `B` spinor sector's classification: `e₁+e₂` against the
four-key word at `B_2`, and the four-key word against `2e₁` at
`B_3`. -/
def classBS : List (Nat × Nat × Nat) := [(1, 3, 2), (3, 4, 3)]

/-- The `D` unit sector's classification: `(2)` against the
key-four pair at `D_4`. -/
def classDU : List (Nat × Nat × Nat) := [(0, 1, 4)]

/-- The `D` vector sector's classification: `(1,1,1)` against the
five-key word at `D_4`, and `(3)` against it at `D_7`. -/
def classDV : List (Nat × Nat × Nat) := [(0, 3, 4), (2, 3, 7)]

/-- The `D` spinor sector's classification: `e₁+e₂+e₃` against
`2e₁` at `D_4`, and the four-key word against `2e₁+e₂` at
`D_6`. -/
def classDS : List (Nat × Nat × Nat) := [(2, 4, 4), (3, 5, 6)]

/-- The `D` vector sector's settled-point raise: the comparison
`((3), (1,1,1,1,1))` at eight, the divisor's radius past the
compared clearances. -/
def settDV : List (Nat × Nat × Nat) := [(2, 3, 8)]

/-- The `D` spinor sector's settled-point raise: the comparison
`(e₁+e₂+e₃+e₄, 2e₁+e₂)` at seven. -/
def settDS : List (Nat × Nat × Nat) := [(3, 5, 7)]

/-- The `B` spinor sector's settled-point raise: the comparison
`(e₁+e₂+e₃+e₄, 2e₁+e₂)` at seven, the radius past the
clearances. -/
def settBS : List (Nat × Nat × Nat) := [(3, 5, 7)]

/-- The `C` unit sector's settled-point raises: the `2θ` gap's
own point at four and the comparison `((1,1), (4))` at five. -/
def settCU : List (Nat × Nat × Nat) := [(3, 3, 4), (0, 3, 5)]

/-- The `C` first fundamental sector's settled-point raises: the
`(5)` gap's own point at four with the comparisons against the
constant-heavy words, `((1,1,1), (4,1))` at six, `((1,1,1), (5))`
at eight, `((2,1), (5))` at seven and `((3), (5))` at five. -/
def settCO : List (Nat × Nat × Nat) :=
  [(7, 7, 4), (0, 6, 6), (0, 7, 8), (1, 7, 7), (2, 7, 5)]

/-- The 47 records at `B_ℓ`: the unit sector's four gaps and six
comparisons, the spinor sector's eight and twenty-eight, and the
stencil cap settled from the domain floor two. -/
def recsB : List chaininstances.Rec :=
  sectorRecs unitB [] [] 2 2 2
    ++ sectorRecs spinFams classBS settBS 2 2 2
    ++ [⟨capB, 2, 2, 2, []⟩]

/-- The 47 records at `C_ℓ`, the classification vacant: the
`ω₁` list's one tie sits at the rank two, below the domain floor
three. -/
def recsC : List chaininstances.Rec :=
  sectorRecs unitC [] settCU 1 0 3
    ++ sectorRecs omegaC [] settCO 1 0 3
    ++ [⟨capC, 3, 3, 3, []⟩]

/-- The 83 records at `D_ℓ`: the unit sector, the vector sector,
the spinor sector's one displayed list, and the stencil cap. -/
def recsD : List chaininstances.Rec :=
  sectorRecs unitD classDU [] 2 3 4
    ++ sectorRecs vecD classDV settDV 2 3 4
    ++ sectorRecs spinFams classDS settDS 2 3 4
    ++ [⟨capD, 4, 4, 4, []⟩]

/-! ## The lemma's whole reads -/

/-- `B_ℓ`'s whole read: the record count, the unit sector's Casimir
identities and the spinor sector's three folds, and both
certificates over the record list. -/
def recsReadB : Prop :=
  recsB.length = 47
  ∧ (unitB.all (fun F =>
      decide (unitRead serstable.casPolyB denB 1 2 2 F))) = true
  ∧ (spinFams.all (fun F =>
      decide (chargedRead vS basOnes wB 4 4 2 2 F))) = true
  ∧ (recsB.all (fun R => decide (chaininstances.sideCert R))) = true
  ∧ (recsB.all (fun R => decide (chaininstances.rootsCert R))) = true

instance : Decidable recsReadB :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `C_ℓ`'s whole read, the unit tier's identity at the doubled
gap. -/
def recsReadC : Prop :=
  recsC.length = 47
  ∧ (unitC.all (fun F =>
      decide (unitRead serstable.casPolyC denC 2 1 0 F))) = true
  ∧ (omegaC.all (fun F =>
      decide (chargedRead vC basC wC 2 2 1 0 F))) = true
  ∧ (recsC.all (fun R => decide (chaininstances.sideCert R))) = true
  ∧ (recsC.all (fun R => decide (chaininstances.rootsCert R))) = true

instance : Decidable recsReadC :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `D_ℓ`'s whole read, the vector and spinor sectors both. -/
def recsReadD : Prop :=
  recsD.length = 83
  ∧ (unitD.all (fun F =>
      decide (unitRead serstable.casPolyD denD 1 2 3 F))) = true
  ∧ (vecD.all (fun F =>
      decide (chargedRead vV basV wD 4 4 2 3 F))) = true
  ∧ (spinFams.all (fun F =>
      decide (chargedRead vS basOnes wD 4 4 2 3 F))) = true
  ∧ (recsD.all (fun R => decide (chaininstances.sideCert R))) = true
  ∧ (recsD.all (fun R => decide (chaininstances.rootsCert R))) = true

instance : Decidable recsReadD :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## The `B` edge evaluations: the displayed families at the
occupied folds

Per `B` sector the displayed families are the occupied folds.  Each
displayed family's witness edge reads the letter fold at the vacant
count — the row's two graded counts part by one — and every
dominant sum off the displayed list reads it occupied, the two
counts tying, the open-last-key strays at the flip's own letter
(`lem:serstable`(ii)'s collision clause).  The fold values are pure
data (`serstable.letterFoldVal`), so every read here is
unconditional in the rank window: the assembly is
`ground.famFold_splitMid` with the run at `serstable.runVanishB`,
the front letters at the column kit's refutations and the tail at
the magnitude cap or the exhibited family. -/

/-! ### The count carrier's cross read -/

/-! ### The moved contents' carrier -/

/-- A moved content in the coroot presentation: the stated entry at
each key, memberwise normal. -/
private def nuOf (l : Nat) (f : Nat → BPair) : List BPair :=
  poly.pnorm ((List.range l).map f)

/-- A moved content sits at the rank's order. -/
private theorem nuOf_length (l : Nat) (f : Nat → BPair) :
    (nuOf l f).length = l := by
  show ((((List.range l).map f)).map BPair.norm).length = l
  rw [ground.length_map, ground.length_mapRange]

/-- A moved content's entry is the stated entry's representative. -/
private theorem nuOf_entry (l : Nat) (f : Nat → BPair) (k : Nat)
    (hk : k < l) :
    ground.getAt BPair.unit (nuOf l f) k = BPair.norm (f k) := by
  show ground.getAt BPair.unit (((List.range l).map f).map BPair.norm) k
    = BPair.norm (f k)
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ k
      (by rw [ground.length_mapRange]; exact hk),
    ground.getAt_map_range BPair.unit f l k, if_pos hk]

/-- The representative list's entry: the vector's own entry's
representative. -/
private theorem pnormEntry (P : poly.Poly) (k : Nat) (hk : k < P.length) :
    ground.getAt BPair.unit (poly.pnorm P) k
      = BPair.norm (ground.getAt BPair.unit P k) := by
  show ground.getAt BPair.unit (P.map BPair.norm) k = _
  exact ground.getAt_map BPair.unit BPair.unit BPair.norm P k hk

/-- The negated coroot vector's entry: the positive vector's own
entry swapped, memberwise normal. -/
private theorem negEntry (P : poly.Poly) (k : Nat) (hk : k < P.length) :
    ground.getAt BPair.unit (poly.pnorm (poly.neg P)) k
      = BPair.norm ((ground.getAt BPair.unit P k).swap) := by
  show ground.getAt BPair.unit ((P.map BPair.swap).map BPair.norm) k = _
  rw [ground.getAt_map BPair.unit BPair.unit BPair.norm _ k
      (by rw [ground.length_map]; exact hk),
    ground.getAt_map BPair.unit BPair.unit BPair.swap P k hk]

/-! ### The `B` positive list's memberships -/

/-- The difference family at an ordered pair joins the `B` positive
list. -/
private theorem memDiff (l a b : Nat) (hab : a < b) (hbl : b < l) :
    (List.range l).map (serstable.fDiff a b) ∈ sertables.foldsB l :=
  ground.mem_append_left _ (ground.mem_append_left _
    (show sertables.diffFold l a b
        ∈ (places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2) from
      ground.mem_map_to (fun p => sertables.diffFold l p.1 p.2)
        (ground.mem_of_countOf_pos (a, b) (places.pairsOf l)
          (places.pairs_complete l hab hbl))))

/-- The `B` sum family at an ordered pair joins the positive
list. -/
private theorem memSum (l a b : Nat) (hab : a < b) (hbl : b < l) :
    (List.range l).map (serstable.fSumB l a b) ∈ sertables.foldsB l := by
  rw [← serstable.fSumB_eq l a b]
  exact ground.mem_append_left _ (ground.mem_append_right _
    (ground.mem_map_to (fun p => sertables.sumFoldB l p.1 p.2)
      (ground.mem_of_countOf_pos (a, b) (places.pairsOf l)
        (places.pairs_complete l hab hbl))))

/-- The `B` short family at a coordinate joins the positive list. -/
private theorem memShort (l a : Nat) (hal : a < l) :
    (List.range l).map (serstable.fDiff a l) ∈ sertables.foldsB l :=
  ground.mem_append_right _
    (show sertables.shortFold l a ∈ (List.range l).map (sertables.shortFold l) from
      ground.mem_map_to (sertables.shortFold l) (ground.memRange hal))

/-! ### The exhibition engine: a moved content at a displayed
family -/

/-- A moved content whose entries read a positive coroot vector's,
entry for entry, is that vector: its θ count is one at any table
(`prop:row`'s θ list at `con:sertables`' positive folds). -/
private theorem thetaOneNormG (t : gentable.Table) (z : List BPair)
    (hzl : z.length = t.rank) (j : Nat) (hj : j < t.posFolds.length)
    (hent : ∀ k, k < t.rank → (ground.getAt BPair.unit z k).oneValue
      (ground.getAt BPair.unit (sertables.posCorootV t j) k))
    (k0 : Nat) (hk0 : k0 < t.rank)
    (hne : ¬ (ground.getAt BPair.unit z k0).oneValue BPair.unit) :
    row.thetaCount t (poly.pnorm z) = 1 := by
  have hPl : (sertables.posCorootV t j).length = t.rank :=
    sertables.posCorootV_length t j
  have heq : poly.pnorm z = poly.pnorm (sertables.posCorootV t j) := by
    refine ground.getAt_ext BPair.unit _ _
      (by rw [poly.pnorm_length, poly.pnorm_length, hzl, hPl])
      (fun k hk => ?_)
    rw [poly.pnorm_length, hzl] at hk
    rw [pnormEntry z k (by rw [hzl]; exact hk),
      pnormEntry (sertables.posCorootV t j) k (by rw [hPl]; exact hk)]
    exact BPair.norm_congr (hent k hk)
  have hne2 : ¬ poly.pnorm z
      = List.replicate t.rank BPair.unit := by
    intro hc
    refine hne ?_
    have h1 : ground.getAt BPair.unit (poly.pnorm z) k0 = BPair.unit := by
      rw [hc]
      exact ground.getAt_replicate BPair.unit BPair.unit t.rank k0 hk0
    rw [pnormEntry z k0 (by rw [hzl]; exact hk0)] at h1
    have h2 := BPair.norm_oneValue (ground.getAt BPair.unit z k0)
    rw [h1] at h2
    exact BPair.oneValue_symm h2
  show (if poly.pnorm z = List.replicate t.rank BPair.unit
      then t.rank
      else if ∃ i, i + 1 < t.posFolds.length + 1
          ∧ (poly.pnorm z = poly.pnorm (sertables.posCorootV t i)
             ∨ poly.pnorm z
              = poly.pnorm (poly.neg (sertables.posCorootV t i)))
        then 1 else 0) = 1
  rw [if_neg hne2, if_pos ⟨j, Nat.succ_lt_succ hj, Or.inl heq⟩]

/-- A moved content whose entries read a positive coroot vector's
memberwise swaps is that vector's balance partner: its θ count is
one at the positive list's negated limb, at any table. -/
private theorem thetaOneNormNegG (t : gentable.Table) (z : List BPair)
    (hzl : z.length = t.rank) (j : Nat) (hj : j < t.posFolds.length)
    (hent : ∀ k, k < t.rank → (ground.getAt BPair.unit z k).oneValue
      ((ground.getAt BPair.unit (sertables.posCorootV t j) k).swap))
    (k0 : Nat) (hk0 : k0 < t.rank)
    (hne : ¬ (ground.getAt BPair.unit z k0).oneValue BPair.unit) :
    row.thetaCount t (poly.pnorm z) = 1 := by
  have hPl : (sertables.posCorootV t j).length = t.rank :=
    sertables.posCorootV_length t j
  have heq : poly.pnorm z
      = poly.pnorm (poly.neg (sertables.posCorootV t j)) := by
    refine ground.getAt_ext BPair.unit _ _
      (by rw [poly.pnorm_length, poly.pnorm_length, poly.length_neg,
        hzl, hPl])
      (fun k hk => ?_)
    rw [poly.pnorm_length, hzl] at hk
    rw [pnormEntry z k (by rw [hzl]; exact hk),
      negEntry (sertables.posCorootV t j) k (by rw [hPl]; exact hk)]
    exact BPair.norm_congr (hent k hk)
  have hne2 : ¬ poly.pnorm z
      = List.replicate t.rank BPair.unit := by
    intro hc
    refine hne ?_
    have h1 : ground.getAt BPair.unit (poly.pnorm z) k0 = BPair.unit := by
      rw [hc]
      exact ground.getAt_replicate BPair.unit BPair.unit t.rank k0 hk0
    rw [pnormEntry z k0 (by rw [hzl]; exact hk0)] at h1
    have h2 := BPair.norm_oneValue (ground.getAt BPair.unit z k0)
    rw [h1] at h2
    exact BPair.oneValue_symm h2
  show (if poly.pnorm z = List.replicate t.rank BPair.unit
      then t.rank
      else if ∃ i, i + 1 < t.posFolds.length + 1
          ∧ (poly.pnorm z = poly.pnorm (sertables.posCorootV t i)
             ∨ poly.pnorm z
              = poly.pnorm (poly.neg (sertables.posCorootV t i)))
        then 1 else 0) = 1
  rw [if_neg hne2, if_pos ⟨j, Nat.succ_lt_succ hj, Or.inr heq⟩]

/-- A moved content whose count reads are the family's column reads,
key for key, is that family's coroot vector: its θ count is one
(`prop:row`'s θ list at `con:sertables`' positive folds). -/
private theorem thetaOneNorm (l : Nat) (F : Nat → Nat) (z : List BPair)
    (hzl : z.length = l)
    (hmem : (List.range l).map F ∈ sertables.foldsB l)
    (hent : ∀ k, k < l → (ground.getAt BPair.unit z k).oneValue
      (BPair.ofCounts (2 * F k) (serstable.nbB l F k)))
    (k0 : Nat) (hk0 : k0 < l)
    (hne : ¬ (ground.getAt BPair.unit z k0).oneValue BPair.unit) :
    row.thetaCount (sertables.tableB l) (poly.pnorm z) = 1 := by
  obtain ⟨j, hj, hje⟩ := ground.getAt_of_mem ([] : List Nat) hmem
  refine thetaOneNormG (sertables.tableB l) z hzl j hj
    (fun k hk => ?_) k0 hk0 hne
  refine BPair.oneValue_trans (BPair.oneValue_trans (hent k hk)
    (BPair.oneValue_symm (serstable.posCorootV_entry l j k F hk hje))) ?_
  rw [pnormEntry (sertables.posCorootV (sertables.tableB l) j) k
    (by rw [sertables.posCorootV_length]; exact hk)]
  exact BPair.norm_oneValue _

/-- A moved content at a displayed family's balance partner: its θ
count is one at the positive list's negated limb. -/
private theorem thetaOneNormNeg (l : Nat) (F : Nat → Nat) (z : List BPair)
    (hzl : z.length = l)
    (hmem : (List.range l).map F ∈ sertables.foldsB l)
    (hent : ∀ k, k < l → (ground.getAt BPair.unit z k).oneValue
      (BPair.ofCounts (serstable.nbB l F k) (2 * F k)))
    (k0 : Nat) (hk0 : k0 < l)
    (hne : ¬ (ground.getAt BPair.unit z k0).oneValue BPair.unit) :
    row.thetaCount (sertables.tableB l) (poly.pnorm z) = 1 := by
  obtain ⟨j, hj, hje⟩ := ground.getAt_of_mem ([] : List Nat) hmem
  refine thetaOneNormNegG (sertables.tableB l) z hzl j hj
    (fun k hk => ?_) k0 hk0 hne
  have hS : ((ground.getAt BPair.unit
      (poly.pnorm (sertables.posCorootV (sertables.tableB l) j))
        k).swap).oneValue
      (BPair.ofCounts (serstable.nbB l F k) (2 * F k)) := by
    rw [← ground.BPair.ofCounts_swap (2 * F k) (serstable.nbB l F k)]
    exact ground.swap_congr (serstable.posCorootV_entry l j k F hk hje)
  refine BPair.oneValue_trans (BPair.oneValue_trans (hent k hk)
    (BPair.oneValue_symm hS)) ?_
  rw [pnormEntry (sertables.posCorootV (sertables.tableB l) j) k
    (by rw [sertables.posCorootV_length]; exact hk)]
  exact ground.swap_congr (BPair.norm_oneValue _)


/-! ### The neighbour fold's three reads and the builder wrappers -/

/-- The neighbour fold at the leading key inside the rank. -/
private theorem nbHead (l : Nat) (F : Nat → Nat) (h : 1 < l) :
    serstable.nbB l F 0 = F 1 := by
  rw [serstable.nbB_zero, if_pos h]

/-- The neighbour fold away from the short last edge: the two
neighbours' sum. -/
private theorem nbMid (l : Nat) (F : Nat → Nat) (m : Nat)
    (h : ¬ m + 2 = l) : serstable.nbB l F (m + 1) = F m + F (m + 2) := by
  rw [serstable.nbB_succ, if_neg (fun hb => h (ground.beqEqOf hb))]

/-- The neighbour fold at the short last edge: the lower neighbour
doubled. -/
private theorem nbTop (l : Nat) (F : Nat → Nat) (m : Nat)
    (h : m + 2 = l) : serstable.nbB l F (m + 1) = 2 * F m := by
  rw [serstable.nbB_succ, if_pos (ground.eqBeqOf h)]

/-- A rank at or beyond a floor is that floor's own shift. -/
private theorem shiftOf {c l : Nat} (h : c ≤ l) : ∃ n, l = n + c := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  exact ⟨k, hk.symm.trans (Nat.add_comm c k)⟩

/-- A moved content spelled at its count reads exhibits the
displayed family: its θ count is one. -/
private theorem famOnePos (l : Nat) (F u v : Nat → Nat)
    (hmem : (List.range l).map F ∈ sertables.foldsB l)
    (hcol : ∀ k, k < l → u k + serstable.nbB l F k = 2 * F k + v k)
    (k0 : Nat) (hk0 : k0 < l) (hne : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableB l)
      (nuOf l (fun i => BPair.ofCounts (u i) (v i))) = 1 :=
  thetaOneNorm l F ((List.range l).map (fun i => BPair.ofCounts (u i) (v i)))
    (ground.length_mapRange _ l) hmem
    (fun k hk => by
      rw [ground.getAt_map_range BPair.unit _ l k, if_pos hk]
      exact BPair.ofCounts_crossed (hcol k hk))
    k0 hk0
    (by
      rw [ground.getAt_map_range BPair.unit _ l k0, if_pos hk0]
      exact fun hc => hne (BPair.ofCounts_unit.mp hc))

/-- A moved content at a displayed family's balance partner. -/
private theorem famOneNeg (l : Nat) (F u v : Nat → Nat)
    (hmem : (List.range l).map F ∈ sertables.foldsB l)
    (hcol : ∀ k, k < l → u k + 2 * F k = serstable.nbB l F k + v k)
    (k0 : Nat) (hk0 : k0 < l) (hne : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableB l)
      (nuOf l (fun i => BPair.ofCounts (u i) (v i))) = 1 :=
  thetaOneNormNeg l F
    ((List.range l).map (fun i => BPair.ofCounts (u i) (v i)))
    (ground.length_mapRange _ l) hmem
    (fun k hk => by
      rw [ground.getAt_map_range BPair.unit _ l k, if_pos hk]
      exact BPair.ofCounts_crossed (hcol k hk))
    k0 hk0
    (by
      rw [ground.getAt_map_range BPair.unit _ l k0, if_pos hk0]
      exact fun hc => hne (BPair.ofCounts_unit.mp hc))

/-! ### The moved contents at the leading keys -/

/-- The moved content `e₁ − e₂`, the `α₁` row. -/
def nA (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 0 then 2 else 0)
    (if i = 1 then 1 else 0))

/-- `e₁ − e₂` is the difference family at the leading pair. -/
theorem nA_mem (l : Nat) (hl : 3 ≤ l) :
    row.thetaCount (sertables.tableB l) (nA l) = 1 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2l : ¬ 2 = l :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 2) hl)
  have hF0 : serstable.fDiff 0 1 0 = 1 :=
    serstable.fDiff_in 0 1 0 (Nat.le_refl 0) (Nat.lt_succ_self 0)
  have hFs : ∀ m, serstable.fDiff 0 1 (m + 1) = 0 := fun m =>
    serstable.fDiff_hi 0 1 (m + 1)
      (fun hc => Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hc))
  refine famOnePos l (serstable.fDiff 0 1)
    (fun i => if i = 0 then 2 else 0) (fun i => if i = 1 then 1 else 0)
    (memDiff l 0 1 (Nat.lt_succ_self 0) h1l) (fun k _ => ?_) 0
    (Nat.lt_trans (Nat.lt_succ_self 0) h1l) (by decide +kernel)
  match k with
  | 0 =>
    show (if (0 : Nat) = 0 then 2 else 0) + serstable.nbB l (serstable.fDiff 0 1) 0
      = 2 * serstable.fDiff 0 1 0 + (if (0 : Nat) = 1 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
      nbHead l _ h1l, hFs 0, hF0]
  | 1 =>
    show (if (1 : Nat) = 0 then 2 else 0)
        + serstable.nbB l (serstable.fDiff 0 1) (0 + 1)
      = 2 * serstable.fDiff 0 1 1 + (if (1 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 0), if_pos rfl,
      nbMid l _ 0 h2l, hF0, hFs 0, hFs 1]
  | m + 2 =>
    show (if m + 2 = 0 then 2 else 0)
        + serstable.nbB l (serstable.fDiff 0 1) (m + 1 + 1)
      = 2 * serstable.fDiff 0 1 (m + 2) + (if m + 2 = 1 then 1 else 0)
    rw [if_neg (fun hc => Nat.noConfusion hc),
      if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)), hFs (m + 1)]
    by_cases ht : m + 3 = l
    · rw [nbTop l _ (m + 1) ht, hFs m]
    · rw [nbMid l _ (m + 1) ht, hFs m, hFs (m + 2)]

/-- The moved content `e₁`, the short family at the leading key. -/
def nB (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 0 then 1 else 0) 0)

/-- `e₁` is the short family at the leading coordinate. -/
theorem nB_mem (l : Nat) (hl : 3 ≤ l) :
    row.thetaCount (sertables.tableB l) (nB l) = 1 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h0l : 0 < l := Nat.lt_trans (Nat.lt_succ_self 0) h1l
  have hIn : ∀ k, k < l → serstable.fDiff 0 l k = 1 := fun k hk =>
    serstable.fDiff_in 0 l k (Nat.zero_le k) hk
  refine famOnePos l (serstable.fDiff 0 l)
    (fun i => if i = 0 then 1 else 0) (fun _ => 0)
    (memShort l 0 h0l) (fun k hk => ?_) 0 h0l (by decide +kernel)
  match k with
  | 0 =>
    show (if (0 : Nat) = 0 then 1 else 0)
        + serstable.nbB l (serstable.fDiff 0 l) 0
      = 2 * serstable.fDiff 0 l 0 + 0
    rw [if_pos rfl, nbHead l _ h1l, hIn 1 h1l, hIn 0 h0l]
  | m + 1 =>
    show (if m + 1 = 0 then 1 else 0)
        + serstable.nbB l (serstable.fDiff 0 l) (m + 1)
      = 2 * serstable.fDiff 0 l (m + 1) + 0
    rw [if_neg (fun hc => Nat.noConfusion hc), hIn (m + 1) hk]
    by_cases ht : m + 2 = l
    · rw [nbTop l _ m ht, hIn m (Nat.lt_of_succ_lt hk)]
    · rw [nbMid l _ m ht, hIn m (Nat.lt_of_succ_lt hk),
        hIn (m + 2) (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht)]

/-- The moved content `e₁ + e₂`, the sum family at the leading
pair. -/
def nC (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 1 then 1 else 0) 0)

/-- `e₁ + e₂` is the `B` sum family at the leading pair. -/
theorem nC_mem (l : Nat) (hl : 3 ≤ l) :
    row.thetaCount (sertables.tableB l) (nC l) = 1 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2l : 2 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2ne : ¬ 2 = l := Nat.ne_of_lt h2l
  have hF0 : serstable.fSumB l 0 1 0 = 1 :=
    serstable.fSumB_mid l 0 1 0 (Nat.le_refl 0) (Nat.lt_succ_self 0)
  have hFh : ∀ k, 1 ≤ k → k < l → serstable.fSumB l 0 1 k = 2 := fun k h1 h2 =>
    serstable.fSumB_hi l 0 1 k h1 h2
  refine famOnePos l (serstable.fSumB l 0 1)
    (fun i => if i = 1 then 1 else 0) (fun _ => 0)
    (memSum l 0 1 (Nat.lt_succ_self 0) h1l) (fun k hk => ?_) 1 h1l
    (by decide +kernel)
  match k with
  | 0 =>
    show (if (0 : Nat) = 1 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 0 1) 0
      = 2 * serstable.fSumB l 0 1 0 + 0
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 1), nbHead l _ h1l,
      hFh 1 (Nat.le_refl 1) h1l, hF0]
  | 1 =>
    show (if (1 : Nat) = 1 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 0 1) (0 + 1)
      = 2 * serstable.fSumB l 0 1 1 + 0
    rw [if_pos rfl, nbMid l _ 0 h2ne, hF0, hFh 2 (by decide +kernel) h2l,
      hFh 1 (Nat.le_refl 1) h1l]
  | m + 2 =>
    show (if m + 2 = 1 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 0 1) (m + 1 + 1)
      = 2 * serstable.fSumB l 0 1 (m + 2) + 0
    rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
      hFh (m + 2) (Nat.succ_le_succ (Nat.zero_le _)) hk]
    by_cases ht : m + 3 = l
    · rw [nbTop l _ (m + 1) ht,
        hFh (m + 1) (Nat.succ_le_succ (Nat.zero_le _)) (Nat.lt_of_succ_lt hk)]
    · rw [nbMid l _ (m + 1) ht,
        hFh (m + 1) (Nat.succ_le_succ (Nat.zero_le _)) (Nat.lt_of_succ_lt hk),
        hFh (m + 3) (Nat.succ_le_succ (Nat.zero_le _))
          (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht)]


/-- The moved content `e₁ + e₃`, the sum family at the pair
`(0, 2)`. -/
def nD (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 0 then 1 else if i = 2 then 1 else 0)
    (if i = 1 then 1 else 0))

/-- `e₁ + e₃` is the `B` sum family at the pair `(0, 2)`. -/
theorem nD_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableB l) (nD l) = 1 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2l : 2 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h3l : 3 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2n : ¬ 2 = l := Nat.ne_of_lt h2l
  have h3n : ¬ 3 = l := Nat.ne_of_lt h3l
  have hF0 : serstable.fSumB l 0 2 0 = 1 :=
    serstable.fSumB_mid l 0 2 0 (Nat.le_refl 0) (by decide +kernel)
  have hF1 : serstable.fSumB l 0 2 1 = 1 :=
    serstable.fSumB_mid l 0 2 1 (Nat.zero_le 1) (by decide +kernel)
  have hFh : ∀ k, 2 ≤ k → k < l → serstable.fSumB l 0 2 k = 2 := fun k h1 h2 =>
    serstable.fSumB_hi l 0 2 k h1 h2
  refine famOnePos l (serstable.fSumB l 0 2)
    (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
    (fun i => if i = 1 then 1 else 0)
    (memSum l 0 2 (by decide +kernel) h2l) (fun k hk => ?_) 0
    (Nat.lt_trans (Nat.lt_succ_self 0) h1l) (by decide +kernel)
  match k with
  | 0 =>
    show (if (0 : Nat) = 0 then 1 else if (0 : Nat) = 2 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 0 2) 0
      = 2 * serstable.fSumB l 0 2 0 + (if (0 : Nat) = 1 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
      nbHead l _ h1l, hF1, hF0]
  | 1 =>
    show (if (1 : Nat) = 0 then 1 else if (1 : Nat) = 2 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 0 2) (0 + 1)
      = 2 * serstable.fSumB l 0 2 1 + (if (1 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 0),
      if_neg (by decide +kernel : ¬ (1 : Nat) = 2), if_pos rfl,
      nbMid l _ 0 h2n, hF0, hFh 2 (Nat.le_refl 2) h2l, hF1]
  | 2 =>
    show (if (2 : Nat) = 0 then 1 else if (2 : Nat) = 2 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 0 2) (1 + 1)
      = 2 * serstable.fSumB l 0 2 2 + (if (2 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (2 : Nat) = 0), if_pos rfl,
      if_neg (by decide +kernel : ¬ (2 : Nat) = 1),
      nbMid l _ 1 h3n, hF1, hFh 3 (by decide +kernel) h3l,
      hFh 2 (Nat.le_refl 2) h2l]
  | m + 3 =>
    show (if m + 3 = 0 then 1 else if m + 3 = 2 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 0 2) (m + 2 + 1)
      = 2 * serstable.fSumB l 0 2 (m + 3) + (if m + 3 = 1 then 1 else 0)
    rw [if_neg (fun hc => Nat.noConfusion hc),
      if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
      if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
      hFh (m + 3) (Nat.le_add_left 2 (m + 1)) hk]
    by_cases ht : m + 4 = l
    · rw [nbTop l _ (m + 2) ht,
        hFh (m + 2) (Nat.le_add_left 2 m) (Nat.lt_of_succ_lt hk)]
    · rw [nbMid l _ (m + 2) ht,
        hFh (m + 2) (Nat.le_add_left 2 m) (Nat.lt_of_succ_lt hk),
        hFh (m + 4) (Nat.le_add_left 2 (m + 2))
          (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht)]

/-- The moved content `e₂ + e₃`, the sum family at the pair
`(1, 2)`. -/
def nE (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 2 then 1 else 0)
    (if i = 0 then 1 else 0))

/-- `e₂ + e₃` is the `B` sum family at the pair `(1, 2)`. -/
theorem nE_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableB l) (nE l) = 1 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2l : 2 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h3l : 3 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2n : ¬ 2 = l := Nat.ne_of_lt h2l
  have h3n : ¬ 3 = l := Nat.ne_of_lt h3l
  have hF0 : serstable.fSumB l 1 2 0 = 0 :=
    serstable.fSumB_lo l 1 2 0 (by decide +kernel) (by decide +kernel)
  have hF1 : serstable.fSumB l 1 2 1 = 1 :=
    serstable.fSumB_mid l 1 2 1 (Nat.le_refl 1) (by decide +kernel)
  have hFh : ∀ k, 2 ≤ k → k < l → serstable.fSumB l 1 2 k = 2 := fun k h1 h2 =>
    serstable.fSumB_hi l 1 2 k h1 h2
  refine famOnePos l (serstable.fSumB l 1 2)
    (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0)
    (memSum l 1 2 (Nat.lt_succ_self 1) h2l) (fun k hk => ?_) 0
    (Nat.lt_trans (Nat.lt_succ_self 0) h1l) (by decide +kernel)
  match k with
  | 0 =>
    show (if (0 : Nat) = 2 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 1 2) 0
      = 2 * serstable.fSumB l 1 2 0 + (if (0 : Nat) = 0 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 2), if_pos rfl,
      nbHead l _ h1l, hF1, hF0]
  | 1 =>
    show (if (1 : Nat) = 2 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 1 2) (0 + 1)
      = 2 * serstable.fSumB l 1 2 1 + (if (1 : Nat) = 0 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 2),
      if_neg (by decide +kernel : ¬ (1 : Nat) = 0),
      nbMid l _ 0 h2n, hF0, hFh 2 (Nat.le_refl 2) h2l, hF1]
  | 2 =>
    show (if (2 : Nat) = 2 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 1 2) (1 + 1)
      = 2 * serstable.fSumB l 1 2 2 + (if (2 : Nat) = 0 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (2 : Nat) = 0),
      nbMid l _ 1 h3n, hF1, hFh 3 (by decide +kernel) h3l,
      hFh 2 (Nat.le_refl 2) h2l]
  | m + 3 =>
    show (if m + 3 = 2 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 1 2) (m + 2 + 1)
      = 2 * serstable.fSumB l 1 2 (m + 3) + (if m + 3 = 0 then 1 else 0)
    rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
      if_neg (fun hc => Nat.noConfusion hc),
      hFh (m + 3) (Nat.le_add_left 2 (m + 1)) hk]
    by_cases ht : m + 4 = l
    · rw [nbTop l _ (m + 2) ht,
        hFh (m + 2) (Nat.le_add_left 2 m) (Nat.lt_of_succ_lt hk)]
    · rw [nbMid l _ (m + 2) ht,
        hFh (m + 2) (Nat.le_add_left 2 m) (Nat.lt_of_succ_lt hk),
        hFh (m + 4) (Nat.le_add_left 2 (m + 2))
          (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht)]

/-- The moved content `e₃ + e₄`, the sum family at the pair
`(2, 3)`. -/
def nF (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 3 then 1 else 0)
    (if i = 1 then 1 else 0))

/-- `e₃ + e₄` is the `B` sum family at the pair `(2, 3)`. -/
theorem nF_mem (l : Nat) (hl : 5 ≤ l) :
    row.thetaCount (sertables.tableB l) (nF l) = 1 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2l : 2 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h3l : 3 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h4l : 4 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2n : ¬ 2 = l := Nat.ne_of_lt h2l
  have h3n : ¬ 3 = l := Nat.ne_of_lt h3l
  have h4n : ¬ 4 = l := Nat.ne_of_lt h4l
  have hF0 : serstable.fSumB l 2 3 0 = 0 :=
    serstable.fSumB_lo l 2 3 0 (by decide +kernel) (by decide +kernel)
  have hF1 : serstable.fSumB l 2 3 1 = 0 :=
    serstable.fSumB_lo l 2 3 1 (by decide +kernel) (by decide +kernel)
  have hF2 : serstable.fSumB l 2 3 2 = 1 :=
    serstable.fSumB_mid l 2 3 2 (Nat.le_refl 2) (by decide +kernel)
  have hFh : ∀ k, 3 ≤ k → k < l → serstable.fSumB l 2 3 k = 2 := fun k h1 h2 =>
    serstable.fSumB_hi l 2 3 k h1 h2
  refine famOnePos l (serstable.fSumB l 2 3)
    (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0)
    (memSum l 2 3 (Nat.lt_succ_self 2) h3l) (fun k hk => ?_) 1 h1l
    (by decide +kernel)
  match k with
  | 0 =>
    show (if (0 : Nat) = 3 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 2 3) 0
      = 2 * serstable.fSumB l 2 3 0 + (if (0 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 3),
      if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
      nbHead l _ h1l, hF1, hF0]
  | 1 =>
    show (if (1 : Nat) = 3 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 2 3) (0 + 1)
      = 2 * serstable.fSumB l 2 3 1 + (if (1 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 3), if_pos rfl,
      nbMid l _ 0 h2n, hF0, hF2, hF1]
  | 2 =>
    show (if (2 : Nat) = 3 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 2 3) (1 + 1)
      = 2 * serstable.fSumB l 2 3 2 + (if (2 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (2 : Nat) = 3),
      if_neg (by decide +kernel : ¬ (2 : Nat) = 1),
      nbMid l _ 1 h3n, hF1, hFh 3 (Nat.le_refl 3) h3l, hF2]
  | 3 =>
    show (if (3 : Nat) = 3 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 2 3) (2 + 1)
      = 2 * serstable.fSumB l 2 3 3 + (if (3 : Nat) = 1 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (3 : Nat) = 1),
      nbMid l _ 2 h4n, hF2, hFh 4 (by decide +kernel) h4l,
      hFh 3 (Nat.le_refl 3) h3l]
  | m + 4 =>
    show (if m + 4 = 3 then 1 else 0)
        + serstable.nbB l (serstable.fSumB l 2 3) (m + 3 + 1)
      = 2 * serstable.fSumB l 2 3 (m + 4) + (if m + 4 = 1 then 1 else 0)
    rw [if_neg (fun hc => Nat.noConfusion
        (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))),
      if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
      hFh (m + 4) (Nat.le_add_left 3 (m + 1)) hk]
    by_cases ht : m + 5 = l
    · rw [nbTop l _ (m + 3) ht,
        hFh (m + 3) (Nat.le_add_left 3 m) (Nat.lt_of_succ_lt hk)]
    · rw [nbMid l _ (m + 3) ht,
        hFh (m + 3) (Nat.le_add_left 3 m) (Nat.lt_of_succ_lt hk),
        hFh (m + 5) (Nat.le_add_left 3 (m + 2))
          (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht)]

/-- The moved content `−e₂`, the short family at the second
coordinate read at its balance partner. -/
def nG (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 0 then 1 else 0)
    (if i = 1 then 1 else 0))

/-- `−e₂` is the short family at the second coordinate, negated. -/
theorem nG_mem (l : Nat) (hl : 3 ≤ l) :
    row.thetaCount (sertables.tableB l) (nG l) = 1 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2l : 2 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2n : ¬ 2 = l := Nat.ne_of_lt h2l
  have hF0 : serstable.fDiff 1 l 0 = 0 :=
    serstable.fDiff_lo 1 l 0 (by decide +kernel)
  have hIn : ∀ k, 1 ≤ k → k < l → serstable.fDiff 1 l k = 1 := fun k h1 h2 =>
    serstable.fDiff_in 1 l k h1 h2
  refine famOneNeg l (serstable.fDiff 1 l)
    (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0)
    (memShort l 1 h1l) (fun k hk => ?_) 0
    (Nat.lt_trans (Nat.lt_succ_self 0) h1l) (by decide +kernel)
  match k with
  | 0 =>
    show (if (0 : Nat) = 0 then 1 else 0) + 2 * serstable.fDiff 1 l 0
      = serstable.nbB l (serstable.fDiff 1 l) 0
        + (if (0 : Nat) = 1 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
      nbHead l _ h1l, hIn 1 (Nat.le_refl 1) h1l, hF0]
  | 1 =>
    show (if (1 : Nat) = 0 then 1 else 0) + 2 * serstable.fDiff 1 l 1
      = serstable.nbB l (serstable.fDiff 1 l) (0 + 1)
        + (if (1 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 0), if_pos rfl,
      nbMid l _ 0 h2n, hF0, hIn 2 (by decide +kernel) h2l,
      hIn 1 (Nat.le_refl 1) h1l]
  | m + 2 =>
    show (if m + 2 = 0 then 1 else 0) + 2 * serstable.fDiff 1 l (m + 2)
      = serstable.nbB l (serstable.fDiff 1 l) (m + 1 + 1)
        + (if m + 2 = 1 then 1 else 0)
    rw [if_neg (fun hc => Nat.noConfusion hc),
      if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
      hIn (m + 2) (Nat.le_add_left 1 (m + 1)) hk]
    by_cases ht : m + 3 = l
    · rw [nbTop l _ (m + 1) ht,
        hIn (m + 1) (Nat.le_add_left 1 m) (Nat.lt_of_succ_lt hk)]
    · rw [nbMid l _ (m + 1) ht,
        hIn (m + 1) (Nat.le_add_left 1 m) (Nat.lt_of_succ_lt hk),
        hIn (m + 3) (Nat.le_add_left 1 (m + 2))
          (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht)]

/-- The moved content `e₃`, the short family at the third
coordinate. -/
def nH (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 2 then 1 else 0)
    (if i = 1 then 1 else 0))

/-- `e₃` is the short family at the third coordinate. -/
theorem nH_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableB l) (nH l) = 1 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2l : 2 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h3l : 3 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2n : ¬ 2 = l := Nat.ne_of_lt h2l
  have h3n : ¬ 3 = l := Nat.ne_of_lt h3l
  have hF0 : serstable.fDiff 2 l 0 = 0 :=
    serstable.fDiff_lo 2 l 0 (by decide +kernel)
  have hF1 : serstable.fDiff 2 l 1 = 0 :=
    serstable.fDiff_lo 2 l 1 (by decide +kernel)
  have hIn : ∀ k, 2 ≤ k → k < l → serstable.fDiff 2 l k = 1 := fun k h1 h2 =>
    serstable.fDiff_in 2 l k h1 h2
  refine famOnePos l (serstable.fDiff 2 l)
    (fun i => if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0)
    (memShort l 2 h2l) (fun k hk => ?_) 1 h1l (by decide +kernel)
  match k with
  | 0 =>
    show (if (0 : Nat) = 2 then 1 else 0)
        + serstable.nbB l (serstable.fDiff 2 l) 0
      = 2 * serstable.fDiff 2 l 0 + (if (0 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 2),
      if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
      nbHead l _ h1l, hF1, hF0]
  | 1 =>
    show (if (1 : Nat) = 2 then 1 else 0)
        + serstable.nbB l (serstable.fDiff 2 l) (0 + 1)
      = 2 * serstable.fDiff 2 l 1 + (if (1 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 2), if_pos rfl,
      nbMid l _ 0 h2n, hF0, hIn 2 (Nat.le_refl 2) h2l, hF1]
  | 2 =>
    show (if (2 : Nat) = 2 then 1 else 0)
        + serstable.nbB l (serstable.fDiff 2 l) (1 + 1)
      = 2 * serstable.fDiff 2 l 2 + (if (2 : Nat) = 1 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (2 : Nat) = 1),
      nbMid l _ 1 h3n, hF1, hIn 3 (by decide +kernel) h3l,
      hIn 2 (Nat.le_refl 2) h2l]
  | m + 3 =>
    show (if m + 3 = 2 then 1 else 0)
        + serstable.nbB l (serstable.fDiff 2 l) (m + 2 + 1)
      = 2 * serstable.fDiff 2 l (m + 3) + (if m + 3 = 1 then 1 else 0)
    rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
      if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
      hIn (m + 3) (Nat.le_add_left 2 (m + 1)) hk]
    by_cases ht : m + 4 = l
    · rw [nbTop l _ (m + 2) ht,
        hIn (m + 2) (Nat.le_add_left 2 m) (Nat.lt_of_succ_lt hk)]
    · rw [nbMid l _ (m + 2) ht,
        hIn (m + 2) (Nat.le_add_left 2 m) (Nat.lt_of_succ_lt hk),
        hIn (m + 4) (Nat.le_add_left 2 (m + 2))
          (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) ht)]


/-! ### The term-vanishing devices: a raised content off the θ list -/

/-- The `B` positive list's family shapes (`serstable.foldsB_cases`'
case read). -/
private def famCase (l : Nat) (F : Nat → Nat) : Prop :=
  (∃ a b, a < b ∧ b < l ∧ F = serstable.fDiff a b)
  ∨ (∃ a b, a < b ∧ b < l ∧ F = serstable.fSumB l a b)
  ∨ (∃ a, a < l ∧ F = serstable.fDiff a l)

/-- A moved content off the unit family and off every positive
coroot vector's two limbs reads the vacant θ count, at any table. -/
private theorem termVanishG (t : gentable.Table) (x : List BPair)
    (hu : ∃ k, k < t.rank
      ∧ ¬ (ground.getAt BPair.unit x k).oneValue BPair.unit)
    (hoff : ∀ j, j < t.posFolds.length →
      ¬ x = poly.pnorm (sertables.posCorootV t j)
      ∧ ¬ x = poly.pnorm (poly.neg (sertables.posCorootV t j))) :
    row.thetaCount t x = 0 := by
  obtain ⟨k, hk, hku⟩ := hu
  have h1 : ¬ x = List.replicate t.rank BPair.unit := by
    intro hc
    refine hku ?_
    rw [hc, ground.getAt_replicate BPair.unit BPair.unit t.rank k hk]
    exact BPair.oneValue_refl _
  have h2 : ¬ ∃ j, j + 1 < t.posFolds.length + 1
      ∧ (x = poly.pnorm (sertables.posCorootV t j)
         ∨ x = poly.pnorm (poly.neg (sertables.posCorootV t j))) := by
    intro hex
    obtain ⟨j, hj, hor⟩ := hex
    obtain ⟨hp, hn⟩ := hoff j (Nat.lt_of_succ_lt_succ hj)
    match hor with
    | .inl he => exact hp he
    | .inr he => exact hn he
  show (if x = List.replicate t.rank BPair.unit
      then t.rank
      else if ∃ j, j + 1 < t.posFolds.length + 1
          ∧ (x = poly.pnorm (sertables.posCorootV t j)
             ∨ x = poly.pnorm (poly.neg (sertables.posCorootV t j)))
        then 1 else 0) = 0
  rw [if_neg h1, if_neg h2]

/-- Two counts at a magnitude past two read unequal. -/
private theorem magNe (p q : Nat) (hmag : q + 3 ≤ p ∨ p + 3 ≤ q) :
    ¬ p = q := by
  match hmag with
  | .inl h =>
    exact fun he => Nat.not_succ_le_self q
      (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right q 2))
        (by rw [← he] at h ⊢; exact h))
  | .inr h =>
    exact fun he => Nat.not_succ_le_self p
      (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_right p 2))
        (by rw [he] at h ⊢; exact h))

/-- An entry of magnitude past two refutes a crossed column read
whose two members sit within two of each other. -/
private theorem magRefute (p q c d : Nat) (hcr : p + d = c + q)
    (hlo : c ≤ d + 2) (hhi : d ≤ c + 2)
    (hmag : q + 3 ≤ p ∨ p + 3 ≤ q) : False := by
  match hmag with
  | .inl h =>
    refine Nat.not_succ_le_self (q + d + 2) ?_
    calc q + d + 2 + 1
        = q + 3 + d := by
          rw [Nat.add_right_comm (q + d) 2 1, Nat.add_right_comm q d 3]
      _ ≤ p + d := Nat.add_le_add_right h _
      _ = c + q := hcr
      _ ≤ d + 2 + q := Nat.add_le_add_right hlo q
      _ = q + d + 2 := by
          rw [Nat.add_comm (d + 2) q, Nat.add_assoc q d 2]
  | .inr h =>
    refine Nat.not_succ_le_self (c + p + 2) ?_
    calc c + p + 2 + 1
        = c + (p + 3) := by
          rw [Nat.add_assoc c p 2]
          exact Nat.add_assoc c (p + 2) 1
      _ ≤ c + q := Nat.add_le_add_left h _
      _ = p + d := hcr.symm
      _ ≤ p + (c + 2) := Nat.add_le_add_left hhi p
      _ = c + p + 2 := by
          rw [Nat.add_assoc c p 2, Nat.add_left_comm p c 2]

/-- The letter's vacant term: a raised content occupied somewhere
and parting from every family's column at some key, at either limb,
reads the vacant θ count. -/
private theorem termVanish (l : Nat) (x : List BPair)
    (hu : ∃ k, k < l ∧ ¬ (ground.getAt BPair.unit x k).oneValue BPair.unit)
    (hpos : ∀ F : Nat → Nat, famCase l F →
      ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue
        (BPair.ofCounts (2 * F y) (serstable.nbB l F y)))
    (hneg : ∀ F : Nat → Nat, famCase l F →
      ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue
        (BPair.ofCounts (serstable.nbB l F y) (2 * F y))) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  refine termVanishG (sertables.tableB l) x hu (fun j hj => ?_)
  have hjl : j < (sertables.foldsB l).length := hj
  obtain ⟨F, hfe, hcase⟩ := serstable.foldsB_cases l j hjl
  constructor
  · intro he
    obtain ⟨y, hy, hoff⟩ := hpos F hcase
    refine hoff ?_
    rw [he]
    exact serstable.posCorootV_entry l j y F hy hfe
  · intro he
    obtain ⟨y, hy, hoff⟩ := hneg F hcase
    refine hoff ?_
    rw [he]
    exact serstable.negCorootV_entry l j y F hy hfe

/-- A raised content whose entry at a key reads a magnitude past
two sits off the θ list: every `B` family's column stays within two
of its neighbour fold (`serstable.colB_magLe`). -/
private theorem termVanishMag (l k : Nat) (hk : k < l) (x : List BPair)
    (p q : Nat)
    (hx : (ground.getAt BPair.unit x k).oneValue (BPair.ofCounts p q))
    (hmag : q + 3 ≤ p ∨ p + 3 ≤ q) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  refine termVanish l x ⟨k, hk, fun hc => magNe p q hmag
      (BPair.ofCounts_unit.mp (BPair.oneValue_trans
        (BPair.oneValue_symm hx) hc))⟩
    (fun F hcase => ⟨k, hk, fun hc => ?_⟩)
    (fun F hcase => ⟨k, hk, fun hc => ?_⟩)
  · obtain ⟨hlo, hhi⟩ := serstable.colB_magLe F k l hk hcase
    exact magRefute p q (2 * F k) (serstable.nbB l F k)
      (ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx) hc))
      hlo hhi hmag
  · obtain ⟨hlo, hhi⟩ := serstable.colB_magLe F k l hk hcase
    exact magRefute p q (serstable.nbB l F k) (2 * F k)
      (ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx) hc))
      hhi hlo hmag

/-- The `B` sum family's entry against its two windows. -/
private theorem sumSplit (l a b k : Nat) :
    serstable.fSumB l a b k
      = serstable.fDiff a b k
        + (serstable.fDiff b l k + serstable.fDiff b l k) := rfl

/-- A two-key refutation: a content matching a column read at both
keys is impossible, so it parts from it at one of them. -/
private theorem pickOff2 (l : Nat) (x : List BPair) (G : Nat → BPair)
    (k0 k1 : Nat) (h0 : k0 < l) (h1 : k1 < l)
    (hall : (ground.getAt BPair.unit x k0).oneValue (G k0) →
      (ground.getAt BPair.unit x k1).oneValue (G k1) → False) :
    ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue (G y) := by
  by_cases c0 : (ground.getAt BPair.unit x k0).oneValue (G k0)
  · exact ⟨k1, h1, fun c1 => hall c0 c1⟩
  · exact ⟨k0, h0, c0⟩

/-- A raised content reading plus two at an interior letter's own
key sits at the narrow window `fDiff (m+1) (m+2)` or nowhere
(`serstable.fDiff_two`, `fSumB_two`, `fShort_two`,
`colB_notNegTwo`): parting from that window's column at any key
vacates the term. -/
private theorem termVanishTwo (l m : Nat) (hml : m + 2 < l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x (m + 1)).oneValue (BPair.ofCounts 2 0))
    (y : Nat) (hy : y < l)
    (hoff : ¬ (ground.getAt BPair.unit x y).oneValue
      (BPair.ofCounts (2 * serstable.fDiff (m + 1) (m + 2) y)
        (serstable.nbB l (serstable.fDiff (m + 1) (m + 2)) y))) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  have hm1l : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
  have hmne : ¬ m + 2 = l := Nat.ne_of_lt hml
  refine termVanish l x
    ⟨m + 1, hm1l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · refine pickOff2 l x
      (fun w => BPair.ofCounts (2 * F w) (serstable.nbB l F w))
      (m + 1) y hm1l hy (fun c1 c2 => ?_)
    refine hoff ?_
    have hFn : F = serstable.fDiff (m + 1) (m + 2) := by
      have hcr : 2 + serstable.nbB l F (m + 1) = 2 * F (m + 1) + 0 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) c1)
      rw [nbMid l F m hmne] at hcr
      have hnat : 2 * F (m + 1) = F m + F (m + 2) + 2 :=
        (Nat.add_zero (2 * F (m + 1))).symm.trans
          (hcr.symm.trans (Nat.add_comm 2 (F m + F (m + 2))))
      exact serstable.narrowOfTwoB l m F hml hcase hnat
    rw [hFn] at c2
    exact c2
  · refine ⟨m + 1, hm1l, fun hc => ?_⟩
    have hcr : 2 + 2 * F (m + 1) = serstable.nbB l F (m + 1) + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)
    rw [nbMid l F m hmne] at hcr
    exact serstable.colB_notNegTwo F m l hml hcase
      ((Nat.add_zero (F m + F (m + 2))).symm.trans
        (hcr.symm.trans (Nat.add_comm 2 (2 * F (m + 1)))))

/-- A raised content reading minus two at an interior letter's own
key sits at the narrow window's balance partner or nowhere. -/
private theorem termVanishNegTwo (l m : Nat) (hml : m + 2 < l)
    (x : List BPair)
    (h2 : (ground.getAt BPair.unit x (m + 1)).oneValue (BPair.ofCounts 0 2))
    (y : Nat) (hy : y < l)
    (hoff : ¬ (ground.getAt BPair.unit x y).oneValue
      (BPair.ofCounts (serstable.nbB l (serstable.fDiff (m + 1) (m + 2)) y)
        (2 * serstable.fDiff (m + 1) (m + 2) y))) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  have hm1l : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
  have hmne : ¬ m + 2 = l := Nat.ne_of_lt hml
  refine termVanish l x
    ⟨m + 1, hm1l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · refine ⟨m + 1, hm1l, fun hc => ?_⟩
    have hcr : 0 + serstable.nbB l F (m + 1) = 2 * F (m + 1) + 2 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)
    rw [nbMid l F m hmne] at hcr
    exact serstable.colB_notNegTwo F m l hml hcase
      ((Nat.zero_add (F m + F (m + 2))).symm.trans hcr)
  · refine pickOff2 l x
      (fun w => BPair.ofCounts (serstable.nbB l F w) (2 * F w))
      (m + 1) y hm1l hy (fun c1 c2 => ?_)
    refine hoff ?_
    have hFn : F = serstable.fDiff (m + 1) (m + 2) := by
      have hcr : 0 + 2 * F (m + 1) = serstable.nbB l F (m + 1) + 2 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) c1)
      rw [nbMid l F m hmne] at hcr
      have hcr2 : 2 * F (m + 1) = F m + F (m + 2) + 2 :=
        (Nat.zero_add (2 * F (m + 1))).symm.trans hcr
      exact serstable.narrowOfTwoB l m F hml hcase hcr2
    rw [hFn] at c2
    exact c2

/-- A window occupied at the leading key opens there. -/
private theorem dHeadOne {a b : Nat} (h : serstable.fDiff a b 0 = 1) :
    a = 0 ∧ 0 < b := by
  by_cases h1 : a ≤ 0
  · by_cases h2 : (0 : Nat) < b
    · exact ⟨Nat.le_antisymm h1 (Nat.zero_le a), h2⟩
    · exact absurd (h.symm.trans (serstable.fDiff_hi a b 0 h2))
        (by decide +kernel)
  · exact absurd (h.symm.trans (serstable.fDiff_lo a b 0 h1))
      (by decide +kernel)

/-- The leading pair's read: a family at or below one at the
leading key with its column reading two there opens at the leading
key and closes at the second. -/
private theorem headPair {f0 f1 : Nat} (hle : f0 ≤ 1)
    (h : 2 * f0 = f1 + 2) : f0 = 1 ∧ f1 = 0 := by
  cases f0 with
  | zero => exact absurd h (fun hc => Nat.noConfusion hc)
  | succ q =>
    have hq : q = 0 :=
      Nat.le_antisymm (Nat.le_of_succ_le_succ hle) (Nat.zero_le q)
    rw [hq] at h ⊢
    exact ⟨rfl, Nat.succ.inj (Nat.succ.inj h.symm)⟩

/-- Every `B` family sits at or below one at the leading key: the
sum family's upper window opens past it. -/
private theorem famHeadLe (l : Nat) (F : Nat → Nat) (hcase : famCase l F) :
    F 0 ≤ 1 := by
  match hcase with
  | .inl ⟨a, b, _, _, hF⟩ => rw [hF]; exact serstable.fDiff_le1 a b 0
  | .inr (.inl ⟨a, b, hab, _, hF⟩) =>
    rw [hF, sumSplit l a b 0,
      serstable.fDiff_lo b l 0 (fun hc =>
        Nat.not_lt_zero a (Nat.lt_of_lt_of_le hab hc))]
    exact serstable.fDiff_le1 a b 0
  | .inr (.inr ⟨a, _, hF⟩) => rw [hF]; exact serstable.fDiff_le1 a l 0

/-- A sum's leading summand is vacant when the sum is. -/
private theorem addZeroL {p q : Nat} (h : p + q = 0) : p = 0 := by
  cases q with
  | zero => exact h
  | succ r => exact Nat.noConfusion h

/-- A sum's trailing summand is vacant when the sum is. -/
private theorem addZeroR {p q : Nat} (h : p + q = 0) : q = 0 := by
  cases q with
  | zero => rfl
  | succ r => exact Nat.noConfusion h

/-- A content reading two at the leading key sits at the leading
narrow window `fDiff 0 1`: no other `B` family's column reads two
there. -/
private theorem headNarrow (l : Nat) (h1l : 1 < l) (F : Nat → Nat)
    (hcase : famCase l F) (hnat : 2 * F 0 = F 1 + 2) :
    F = serstable.fDiff 0 1 := by
  obtain ⟨hf0, hf1⟩ := headPair (famHeadLe l F hcase) hnat
  match hcase with
  | .inl ⟨a, b, _, _, hF⟩ =>
    rw [hF] at hf0 hf1
    obtain ⟨ha, hb⟩ := dHeadOne hf0
    have hb1 : b = 1 := by
      match Nat.lt_or_ge 1 b with
      | .inl hlt =>
        have hone : serstable.fDiff a b 1 = 1 :=
          serstable.fDiff_in a b 1 (by rw [ha]; exact Nat.zero_le 1) hlt
        rw [hf1] at hone
        exact absurd hone (by decide +kernel)
      | .inr hge => exact Nat.le_antisymm hge hb
    rw [hF, ha, hb1]
  | .inr (.inl ⟨a, b, hab, _, hF⟩) =>
    rw [hF, sumSplit l a b 0,
      serstable.fDiff_lo b l 0 (fun hc =>
        Nat.not_lt_zero a (Nat.lt_of_lt_of_le hab hc))] at hf0
    obtain ⟨ha, hb⟩ := dHeadOne hf0
    rw [hF, sumSplit l a b 1] at hf1
    have hd1 : serstable.fDiff a b 1 = 0 := addZeroL hf1
    have hbl1 : serstable.fDiff b l 1 = 0 := addZeroL (addZeroR hf1)
    match Nat.lt_or_ge 1 b with
    | .inl hlt =>
      have hone : serstable.fDiff a b 1 = 1 :=
        serstable.fDiff_in a b 1 (by rw [ha]; exact Nat.zero_le 1) hlt
      rw [hd1] at hone
      exact absurd hone (by decide +kernel)
    | .inr hge =>
      have hb1 : b = 1 := Nat.le_antisymm hge hb
      have hone : serstable.fDiff b l 1 = 1 :=
        serstable.fDiff_in b l 1 (by rw [hb1]; exact Nat.le_refl 1) h1l
      rw [hbl1] at hone
      exact absurd hone (by decide +kernel)
  | .inr (.inr ⟨a, _, hF⟩) =>
    rw [hF] at hf0 hf1
    obtain ⟨ha, _⟩ := dHeadOne hf0
    have hone : serstable.fDiff a l 1 = 1 :=
      serstable.fDiff_in a l 1 (by rw [ha]; exact Nat.zero_le 1) h1l
    rw [hf1] at hone
    exact absurd hone (by decide +kernel)

/-- No `B` family's column reads minus two at the leading key. -/
private theorem headRefuse (l : Nat) (F : Nat → Nat)
    (hcase : famCase l F) (hnat : F 1 = 2 * F 0 + 2) : False := by
  match hcase with
  | .inl ⟨a, b, _, _, hF⟩ =>
    rw [hF] at hnat
    have hle := serstable.fDiff_le1 a b 1
    rw [hnat] at hle
    exact Nat.not_succ_le_self 1
      (Nat.le_trans (Nat.le_add_left 2 (2 * serstable.fDiff a b 0)) hle)
  | .inr (.inr ⟨a, _, hF⟩) =>
    rw [hF] at hnat
    have hle := serstable.fDiff_le1 a l 1
    rw [hnat] at hle
    exact Nat.not_succ_le_self 1
      (Nat.le_trans (Nat.le_add_left 2 (2 * serstable.fDiff a l 0)) hle)
  | .inr (.inl ⟨a, b, hab, _, hF⟩) =>
    have hb0 : serstable.fDiff b l 0 = 0 :=
      serstable.fDiff_lo b l 0 (fun hc =>
        Nat.not_lt_zero a (Nat.lt_of_lt_of_le hab hc))
    rw [hF, sumSplit l a b 0, sumSplit l a b 1, hb0] at hnat
    by_cases ha : a = 0
    · have hb : 0 < b := by rw [← ha]; exact hab
      rw [ha, serstable.fDiff_in 0 b 0 (Nat.le_refl 0) hb] at hnat
      have hle3 : serstable.fDiff 0 b 1
          + (serstable.fDiff b l 1 + serstable.fDiff b l 1) ≤ 1 + (1 + 1) :=
        Nat.add_le_add (serstable.fDiff_le1 0 b 1) (Nat.add_le_add (serstable.fDiff_le1 b l 1) (serstable.fDiff_le1 b l 1))
      rw [hnat] at hle3
      exact absurd hle3 (by decide +kernel)
    · have hb2 : ¬ b ≤ 1 := fun hc =>
        ha (Nat.le_antisymm (Nat.le_of_lt_succ
          (Nat.lt_of_lt_of_le hab hc)) (Nat.zero_le a))
      rw [serstable.fDiff_lo a b 0 (fun hc =>
          ha (Nat.le_antisymm hc (Nat.zero_le a))),
        serstable.fDiff_lo b l 1 hb2] at hnat
      have hle1 : serstable.fDiff a b 1 + (0 + 0) ≤ 1 :=
        Nat.le_trans (Nat.le_of_eq (Nat.add_zero _)) (serstable.fDiff_le1 a b 1)
      rw [hnat] at hle1
      exact absurd hle1 (by decide +kernel)

/-- A raised content reading plus two at the leading key sits at
the leading narrow window or nowhere: parting from that window's
column at any key vacates the term. -/
private theorem termVanishHeadTwo (l : Nat) (hl : 3 ≤ l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x 0).oneValue (BPair.ofCounts 2 0))
    (y : Nat) (hy : y < l)
    (hoff : ¬ (ground.getAt BPair.unit x y).oneValue
      (BPair.ofCounts (2 * serstable.fDiff 0 1 y)
        (serstable.nbB l (serstable.fDiff 0 1) y))) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h0l : 0 < l := Nat.lt_trans (Nat.lt_succ_self 0) h1l
  refine termVanish l x
    ⟨0, h0l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · refine pickOff2 l x
      (fun w => BPair.ofCounts (2 * F w) (serstable.nbB l F w))
      0 y h0l hy (fun c1 c2 => ?_)
    refine hoff ?_
    have hFn : F = serstable.fDiff 0 1 := by
      have hcr : 2 + serstable.nbB l F 0 = 2 * F 0 + 0 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) c1)
      rw [nbHead l F h1l] at hcr
      exact headNarrow l h1l F hcase
        ((Nat.add_zero (2 * F 0)).symm.trans
          (hcr.symm.trans (Nat.add_comm 2 (F 1))))
    rw [hFn] at c2
    exact c2
  · refine ⟨0, h0l, fun hc => ?_⟩
    have hcr : 2 + 2 * F 0 = serstable.nbB l F 0 + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)
    rw [nbHead l F h1l] at hcr
    exact headRefuse l F hcase
      ((Nat.add_zero (F 1)).symm.trans
        (hcr.symm.trans (Nat.add_comm 2 (2 * F 0))))


/-! ### The raised contents and the fold's assembly -/

/-- Scaling a count pair scales its two counts. -/
private theorem mulCounts (c p q : Nat) :
    (BPair.ofNat c * BPair.ofCounts p q).oneValue
      (BPair.ofCounts (c * p) (c * q)) := by
  show (BPair.ofNat c * (BPair.ofNat p + (BPair.ofNat q).swap)).oneValue _
  rw [BPair.left_distrib, BPair.mul_swap]
  exact BPair.oneValue_symm (BPair.add_congr (BPair.ofNat_mul c p)
    (ground.swap_congr (BPair.ofNat_mul c q)))

/-- The `B` Cartan row's diagonal entry as a count pair. -/
private theorem cartDiag (l i : Nat) :
    (serstable.cartB l i i).oneValue (BPair.ofCounts 2 0) := by
  rw [serstable.cartBd l i]
  exact (by decide +kernel)

/-- The `B` Cartan row's upper neighbour away from the short
edge. -/
private theorem cartUp1 (l i : Nat) (h : ¬ i + 2 = l) :
    (serstable.cartB l i (i + 1)).oneValue (BPair.ofCounts 0 1) := by
  rw [serstable.cartBup1 l i h]
  exact (by decide +kernel)

/-- The `B` Cartan row's lower neighbour. -/
private theorem cartDn (l i : Nat) :
    (serstable.cartB l (i + 1) i).oneValue (BPair.ofCounts 0 1) := by
  rw [serstable.cartBdn l i]
  exact (by decide +kernel)

/-- The `B` Cartan row is vacant off the letter's three keys. -/
private theorem cartOff (l i j : Nat) (h1 : ¬ j = i) (h2 : ¬ j = i + 1)
    (h3 : ¬ j + 1 = i) :
    (serstable.cartB l i j).oneValue (BPair.ofCounts 0 0) := by
  rw [serstable.cartBoff l i j h1 h2 h3]
  exact (by decide +kernel)

/-- A letter's raised content at any table: the moved content
against the letter's Cartan row scaled by the shifted key. -/
private def raisedG (t : gentable.Table) (nu0 : List BPair)
    (c i : Nat) : List BPair :=
  poly.pnorm (elim.vecAdd nu0
    (elim.vecScale (BPair.ofNat c)
      (ground.getAt [] t.cartan i)))

/-- The letter fold's value is the fold of its letters' raised
contents, at any table. -/
private theorem foldValEqG (t : gentable.Table) (ρv : List Nat)
    (nu0 : List BPair) :
    serstable.letterFoldVal t ρv nu0
      = ground.famFold Nat.add 0
        (fun i => row.thetaCount t
          (raisedG t nu0 (ground.getAt 0 ρv i) i)) (List.range t.rank) := rfl

/-- A stray edge's floor at any table: one occupied letter bounds
the letter fold below. -/
private theorem foldOneAtG (t : gentable.Table) (i : Nat)
    (hi : i < t.rank) (ρv : List Nat) (nu0 : List BPair)
    (hone : row.thetaCount t
      (raisedG t nu0 (ground.getAt 0 ρv i) i) = 1) :
    1 ≤ serstable.letterFoldVal t ρv nu0 := by
  rw [foldValEqG t ρv nu0]
  exact Nat.le_trans (Nat.le_of_eq hone.symm)
    (ground.famFold_mem_le
      (fun k => row.thetaCount t
        (raisedG t nu0 (ground.getAt 0 ρv k) k))
      (List.range t.rank) i (ground.memRange hi))

/-- The raised content's count reads at a key, at any table: the
moved content's counts raised by the scaled Cartan entry's. -/
private theorem raisedCountG (t : gentable.Table) (u v : Nat → Nat)
    (c i y : Nat) (hy : y < t.rank)
    (hcl : (ground.getAt [] t.cartan i).length = t.rank) (p q : Nat)
    (hcart : (ground.getAt BPair.unit
      (ground.getAt [] t.cartan i) y).oneValue (BPair.ofCounts p q)) :
    (ground.getAt BPair.unit
      (raisedG t (nuOf t.rank (fun k => BPair.ofCounts (u k) (v k))) c i) y).oneValue
      (BPair.ofCounts (u y + c * p) (v y + c * q)) := by
  refine BPair.oneValue_trans
    (serstable.raisedAt t _ (nuOf_length t.rank _) c i hcl y hy) ?_
  rw [nuOf_entry t.rank _ y hy]
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.norm_oneValue _)
      (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hcart)
        (mulCounts c p q)))
    (BPair.oneValue_symm (BPair.ofCounts_add (u y) (v y) (c * p) (c * q)))

/-- The raised content's count reads at a key: the moved content's
counts raised by the scaled Cartan entry's. -/
private theorem raisedCount (l : Nat) (u v : Nat → Nat) (c i y : Nat)
    (hi : i < l) (hy : y < l) (p q : Nat)
    (hcart : (serstable.cartB l i y).oneValue (BPair.ofCounts p q)) :
    (ground.getAt BPair.unit
      (raisedG (sertables.tableB l) (nuOf l (fun k => BPair.ofCounts (u k) (v k))) c i) y).oneValue
      (BPair.ofCounts (u y + c * p) (v y + c * q)) := by
  refine raisedCountG (sertables.tableB l) u v c i y hy ?_ p q ?_
  · rw [serstable.cartB_eq l]
    exact ground.matOf_rowLength [] l l
      (fun p q => serstable.cartB l p q) i hi
  · have hcent : ground.getAt BPair.unit
        (ground.getAt [] (sertables.tableB l).cartan i) y
        = serstable.cartB l i y := by
      rw [serstable.cartB_eq l]
      exact ground.matOf_entry [] BPair.unit l l
        (fun p q => serstable.cartB l p q) i y hi hy
    rw [hcent]
    exact hcart

/-- A moved content is vacant at a key of equal counts. -/
private theorem nuVac (l : Nat) (u v : Nat → Nat) (k : Nat) (hk : k < l)
    (h : u k = v k) :
    (ground.getAt BPair.unit
      (nuOf l (fun i => BPair.ofCounts (u i) (v i))) k).oneValue
      BPair.unit := by
  rw [nuOf_entry l _ k hk]
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.ofCounts_unit.mpr h)

/-- A moved content is occupied at a key of unequal counts. -/
private theorem nuOcc (l : Nat) (u v : Nat → Nat) (k : Nat) (hk : k < l)
    (h : ¬ u k = v k) :
    ¬ (ground.getAt BPair.unit
      (nuOf l (fun i => BPair.ofCounts (u i) (v i))) k).oneValue
      BPair.unit := by
  rw [nuOf_entry l _ k hk]
  exact fun hc => h (BPair.ofCounts_unit.mp
    (BPair.oneValue_trans (BPair.oneValue_symm (BPair.norm_oneValue _)) hc))

/-- A witness edge's assembly at any table: a front window of `a`
letters, the run, and a tail window of `c` letters, each reading
the vacant θ count. -/
private theorem foldZeroG (t : gentable.Table) (a b c T : Nat)
    (ha : 1 ≤ a) (h : t.rank = a + b + c) (hT : T = a + b)
    (ρv : List Nat) (nu0 : List BPair)
    (hfront : ∀ i, i < a → row.thetaCount t
      (raisedG t nu0 (ground.getAt 0 ρv i) i) = 0)
    (hrun : ∀ m, a ≤ m + 1 → m + 1 < T → row.thetaCount t
      (raisedG t nu0 (ground.getAt 0 ρv (m + 1)) (m + 1)) = 0)
    (htail : ∀ x, x < c → row.thetaCount t
      (raisedG t nu0 (ground.getAt 0 ρv (T + x)) (T + x)) = 0) :
    serstable.letterFoldVal t ρv nu0 = 0 := by
  rw [hT] at hrun htail
  have hmid : ∀ i, a ≤ i → i < a + b → row.thetaCount t
      (raisedG t nu0 (ground.getAt 0 ρv i) i) = 0 := by
    intro i hai hib
    cases i with
    | zero =>
      exact absurd (Nat.le_trans ha hai) (Nat.not_succ_le_zero 0)
    | succ m =>
      exact hrun m hai hib
  rw [foldValEqG t ρv nu0,
    show (List.range t.rank) = List.range (a + b + c) from by rw [h],
    ground.famFold_splitMid _ a b c hmid,
    ground.famFold_rangeZero _ a hfront,
    ground.famFold_rangeZero _ c htail]

/-! ### The sources' shifted keys and the narrow columns' reads -/

/-- `θ`'s shifted key at the leading coordinate. -/
private theorem kapTh0 (l : Nat) (h : 0 < l) :
    ground.getAt 0 (serstable.memberRho [1, 1] l) 0 = 1 := by
  rw [serstable.memberRhoAt [1, 1] l 0 h]
  rfl

/-- `θ`'s shifted key at the second coordinate. -/
private theorem kapTh1 (l : Nat) (h : 1 < l) :
    ground.getAt 0 (serstable.memberRho [1, 1] l) 1 = 2 := by
  rw [serstable.memberRhoAt [1, 1] l 1 h]
  rfl

/-- `θ`'s shifted key across the run and the tail. -/
private theorem kapTh (l k : Nat) (hk2 : 2 ≤ k) (hk : k < l) :
    ground.getAt 0 (serstable.memberRho [1, 1] l) k = 1 :=
  serstable.memberRho_run [1, 1] l k hk2 hk

/-- The spinor base's shifted key across the run. -/
private theorem kapSp (l i : Nat) (hi : i < l) (hne : ¬ i + 1 = l) :
    ground.getAt 0 (basedRho [] l 0) i = 1 :=
  basedRho_run [] l 0 i (Nat.zero_le i) hi hne

/-- The spinor base's shifted key at the tail. -/
private theorem kapSpT (l q : Nat) (hi : q < l) (hq : q + 1 = l) :
    ground.getAt 0 (basedRho [] l 0) q = 2 :=
  basedRho_datum [] l 0 q (Nat.zero_le q) hi hq

/-- The once-raised base's shifted key at the leading key. -/
private theorem kapE1H (l : Nat) (hl : 2 ≤ l) :
    ground.getAt 0 (basedRho [1] l 0) 0 = 2 := by
  have h0 : 0 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have hne : ¬ (0 + 1 + 0 = l) := by
    intro hc
    rw [← hc] at hl
    exact absurd hl (by decide +kernel)
  rw [basedRho_step [1] l 0 0 h0, basedM_entry [1] l 0 0 h0, if_neg hne]
  rfl

/-- The once-raised base's shifted key across the run. -/
private theorem kapE1 (l i : Nat) (h1 : 1 ≤ i) (hi : i < l)
    (hne : ¬ i + 1 = l) : ground.getAt 0 (basedRho [1] l 0) i = 1 :=
  basedRho_run [1] l 0 i h1 hi hne

/-- The once-raised base's shifted key at the tail. -/
private theorem kapE1T (l q : Nat) (h1 : 1 ≤ q) (hi : q < l) (hq : q + 1 = l) :
    ground.getAt 0 (basedRho [1] l 0) q = 2 :=
  basedRho_datum [1] l 0 q h1 hi hq

/-- The twice-raised base's shifted key at the leading key. -/
private theorem kapE12H (l : Nat) (hl : 2 ≤ l) :
    ground.getAt 0 (basedRho [1, 1] l 0) 0 = 1 := by
  have h0 : 0 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have hne : ¬ (0 + 1 + 0 = l) := by
    intro hc
    rw [← hc] at hl
    exact absurd hl (by decide +kernel)
  rw [basedRho_step [1, 1] l 0 0 h0, basedM_entry [1, 1] l 0 0 h0, if_neg hne]
  rfl

/-- The twice-raised base's shifted key at the second key. -/
private theorem kapE12A (l : Nat) (hl : 3 ≤ l) :
    ground.getAt 0 (basedRho [1, 1] l 0) 1 = 2 := by
  have h1 : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have hne : ¬ (1 + 1 + 0 = l) := by
    intro hc
    rw [← hc] at hl
    exact absurd hl (by decide +kernel)
  rw [basedRho_step [1, 1] l 0 1 h1, basedM_entry [1, 1] l 0 1 h1, if_neg hne]
  rfl

/-- The twice-raised base's shifted key across the run. -/
private theorem kapE12 (l i : Nat) (h2 : 2 ≤ i) (hi : i < l)
    (hne : ¬ i + 1 = l) : ground.getAt 0 (basedRho [1, 1] l 0) i = 1 :=
  basedRho_run [1, 1] l 0 i h2 hi hne

/-- The twice-raised base's shifted key at the tail. -/
private theorem kapE12T (l q : Nat) (h2 : 2 ≤ q) (hi : q < l)
    (hq : q + 1 = l) : ground.getAt 0 (basedRho [1, 1] l 0) q = 2 :=
  basedRho_datum [1, 1] l 0 q h2 hi hq

/-- The narrow window's column below its own key reads minus
one. -/
private theorem narrowBelow (l m : Nat) (hml : m + 2 < l) :
    2 * serstable.fDiff (m + 1) (m + 2) m = 0
    ∧ serstable.nbB l (serstable.fDiff (m + 1) (m + 2)) m = 1 := by
  have hz : ∀ k, ¬ k = m + 1 → serstable.fDiff (m + 1) (m + 2) k = 0 := by
    intro k hk
    match Nat.lt_or_ge k (m + 1) with
    | .inl h =>
      exact serstable.fDiff_lo (m + 1) (m + 2) k (fun hc =>
        Nat.not_succ_le_self k (Nat.le_trans (Nat.succ_le_of_lt h) hc))
    | .inr h =>
      exact serstable.fDiff_hi (m + 1) (m + 2) k (fun hc =>
        hk (Nat.le_antisymm (Nat.le_of_lt_succ hc) h))
  have hone : serstable.fDiff (m + 1) (m + 2) (m + 1) = 1 :=
    serstable.fDiff_in (m + 1) (m + 2) (m + 1) (Nat.le_refl _)
      (Nat.lt_succ_self _)
  refine ⟨by rw [hz m (Nat.ne_of_lt (Nat.lt_succ_self m))], ?_⟩
  cases m with
  | zero =>
    rw [nbHead l _ (Nat.lt_trans (Nat.lt_succ_self 1) hml)]
    exact hone
  | succ q =>
    rw [nbMid l _ q (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self (q + 2)) hml)),
      hz q (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self q)
        (Nat.lt_succ_self (q + 1)))), hone]

/-- The leading narrow window's column at the second key reads
minus one. -/
private theorem headColOne (l : Nat) (h2l : ¬ 2 = l) :
    2 * serstable.fDiff 0 1 1 = 0
    ∧ serstable.nbB l (serstable.fDiff 0 1) 1 = 1 := by
  have hz : ∀ k, 1 ≤ k → serstable.fDiff 0 1 k = 0 := fun k hk =>
    serstable.fDiff_hi 0 1 k (fun hc =>
      Nat.not_succ_le_zero 0 (Nat.le_trans hk (Nat.le_of_lt_succ hc)))
  have h0 : serstable.fDiff 0 1 0 = 1 :=
    serstable.fDiff_in 0 1 0 (Nat.le_refl 0) (Nat.lt_succ_self 0)
  refine ⟨by rw [hz 1 (Nat.le_refl 1)], ?_⟩
  rw [nbMid l _ 0 h2l, h0, hz 2 (by decide +kernel)]

/-- The leading narrow window's column at the rank's last key is
vacant. -/
private theorem headColTail (l q : Nat) (h1q : 1 ≤ q) (hq : q + 2 = l) :
    2 * serstable.fDiff 0 1 (q + 1) = 0
    ∧ serstable.nbB l (serstable.fDiff 0 1) (q + 1) = 0 := by
  have hz : ∀ k, 1 ≤ k → serstable.fDiff 0 1 k = 0 := fun k hk =>
    serstable.fDiff_hi 0 1 k (fun hc =>
      Nat.not_succ_le_zero 0 (Nat.le_trans hk (Nat.le_of_lt_succ hc)))
  refine ⟨by rw [hz (q + 1) (Nat.le_succ_of_le h1q)], ?_⟩
  rw [nbTop l _ q hq, hz q h1q]

/-- The narrow-window device read at the key below the letter. -/
private theorem termTwoBelow (l m : Nat) (hml : m + 2 < l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x (m + 1)).oneValue (BPair.ofCounts 2 0))
    (A B : Nat)
    (hm : (ground.getAt BPair.unit x m).oneValue (BPair.ofCounts A B))
    (hne : ¬ A + 1 = 0 + B) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  obtain ⟨hz, ho⟩ := narrowBelow l m hml
  refine termVanishTwo l m hml x h2 m
    (Nat.lt_of_le_of_lt (Nat.le_add_right m 2) hml) (fun hc => hne ?_)
  rw [hz, ho] at hc
  exact ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hm) hc)

/-- The narrow-window device at the balance partner, read at the
key below the letter. -/
private theorem termNegTwoBelow (l m : Nat) (hml : m + 2 < l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x (m + 1)).oneValue (BPair.ofCounts 0 2))
    (A B : Nat)
    (hm : (ground.getAt BPair.unit x m).oneValue (BPair.ofCounts A B))
    (hne : ¬ A + 0 = 1 + B) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  obtain ⟨hz, ho⟩ := narrowBelow l m hml
  refine termVanishNegTwo l m hml x h2 m
    (Nat.lt_of_le_of_lt (Nat.le_add_right m 2) hml) (fun hc => hne ?_)
  rw [hz, ho] at hc
  exact ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hm) hc)

/-- The leading-window device read at the second key. -/
private theorem termHeadAtOne (l : Nat) (hl : 3 ≤ l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x 0).oneValue (BPair.ofCounts 2 0))
    (A B : Nat)
    (h1 : (ground.getAt BPair.unit x 1).oneValue (BPair.ofCounts A B))
    (hne : ¬ A + 1 = 0 + B) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2l : ¬ 2 = l :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 2) hl)
  obtain ⟨hz, ho⟩ := headColOne l h2l
  refine termVanishHeadTwo l hl x h2 1 h1l (fun hc => hne ?_)
  rw [hz, ho] at hc
  exact ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h1) hc)

/-- The leading-window device read at the rank's last key. -/
private theorem termHeadAtTail (l q : Nat) (hl : 3 ≤ l) (h1q : 1 ≤ q)
    (hq : q + 2 = l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x 0).oneValue (BPair.ofCounts 2 0))
    (A B : Nat)
    (ht : (ground.getAt BPair.unit x (q + 1)).oneValue (BPair.ofCounts A B))
    (hne : ¬ A + 0 = 0 + B) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  obtain ⟨hz, ho⟩ := headColTail l q h1q hq
  refine termVanishHeadTwo l hl x h2 (q + 1)
    (by rw [← hq]; exact Nat.lt_succ_self (q + 1)) (fun hc => hne ?_)
  rw [hz, ho] at hc
  exact ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm ht) hc)


/-! ### The tail's collision refusal -/

/-- Every `B` family sits at or below two: the sum family's two
windows are disjoint. -/
private theorem famCap (l : Nat) (F : Nat → Nat) (hcase : famCase l F)
    (k : Nat) : F k ≤ 2 := by
  match hcase with
  | .inl ⟨a, b, _, _, hF⟩ =>
    rw [hF]
    exact Nat.le_trans (serstable.fDiff_le1 a b k) (by decide +kernel)
  | .inr (.inr ⟨a, _, hF⟩) =>
    rw [hF]
    exact Nat.le_trans (serstable.fDiff_le1 a l k) (by decide +kernel)
  | .inr (.inl ⟨a, b, _, _, hF⟩) =>
    rw [hF, sumSplit l a b k]
    match Nat.lt_or_ge k b with
    | .inl hk =>
      rw [serstable.fDiff_lo b l k (fun hc =>
        Nat.not_succ_le_self k (Nat.le_trans (Nat.succ_le_of_lt hk) hc))]
      exact Nat.le_trans
        (Nat.add_le_add (serstable.fDiff_le1 a b k) (Nat.le_refl (0 + 0)))
        (by decide +kernel)
    | .inr hk =>
      rw [serstable.fDiff_hi a b k (fun hc =>
        Nat.not_succ_le_self k (Nat.le_trans (Nat.succ_le_of_lt hc) hk))]
      exact Nat.add_le_add (Nat.le_refl 0)
        (Nat.add_le_add (serstable.fDiff_le1 b l k) (serstable.fDiff_le1 b l k))

/-- A family occupied at two at a key at or below the rank's
second-last closes its upper window there, so its column reads two
at each of the rank's last two keys. -/
private theorem tailRefuse (l q k : Nat) (hq : q + 2 = l) (hkq : k ≤ q)
    (F : Nat → Nat) (hcase : famCase l F) (hk2 : F k = 2) :
    F (q + 1) = 2 ∧ F q = 2 := by
  have hql : q < l := by
    rw [← hq]
    exact Nat.lt_trans (Nat.lt_succ_self q) (Nat.lt_succ_self (q + 1))
  have hq1l : q + 1 < l := by
    rw [← hq]
    exact Nat.lt_succ_self (q + 1)
  match hcase with
  | .inl ⟨a, b, _, _, hF⟩ =>
    rw [hF] at hk2
    have hle := serstable.fDiff_le1 a b k
    rw [hk2] at hle
    exact absurd hle (by decide +kernel)
  | .inr (.inr ⟨a, _, hF⟩) =>
    rw [hF] at hk2
    have hle := serstable.fDiff_le1 a l k
    rw [hk2] at hle
    exact absurd hle (by decide +kernel)
  | .inr (.inl ⟨a, b, _, _, hF⟩) =>
    rw [hF, sumSplit l a b k] at hk2
    have hbk : b ≤ k := by
      match Nat.lt_or_ge k b with
      | .inl hlt =>
        rw [serstable.fDiff_lo b l k (fun hc =>
          Nat.not_succ_le_self k (Nat.le_trans (Nat.succ_le_of_lt hlt) hc))]
          at hk2
        have h2 : serstable.fDiff a b k = 2 :=
          (Nat.add_zero (serstable.fDiff a b k)).symm.trans hk2
        have hle := serstable.fDiff_le1 a b k
        rw [h2] at hle
        exact absurd hle (by decide +kernel)
      | .inr hge => exact hge
    have hbq : b ≤ q := Nat.le_trans hbk hkq
    refine ⟨?_, ?_⟩
    · rw [hF, sumSplit l a b (q + 1),
        serstable.fDiff_hi a b (q + 1) (fun hc =>
          Nat.not_succ_le_self (q + 1) (Nat.le_trans (Nat.succ_le_of_lt hc)
            (Nat.le_trans hbq (Nat.le_succ q)))),
        serstable.fDiff_in b l (q + 1)
          (Nat.le_trans hbq (Nat.le_succ q)) hq1l]
    · rw [hF, sumSplit l a b q,
        serstable.fDiff_hi a b q (fun hc =>
          Nat.not_succ_le_self q (Nat.le_trans (Nat.succ_le_of_lt hc) hbq)),
        serstable.fDiff_in b l q hbq hql]

/-- A four-key refutation: a content matching a column read at each
of four keys is impossible, so it parts from it at one of them. -/
private theorem pickOff (l : Nat) (x : List BPair) (G : Nat → BPair)
    (k0 k1 k2 k3 : Nat) (h0 : k0 < l) (h1 : k1 < l) (h2 : k2 < l)
    (h3 : k3 < l)
    (hall : (ground.getAt BPair.unit x k0).oneValue (G k0) →
      (ground.getAt BPair.unit x k1).oneValue (G k1) →
      (ground.getAt BPair.unit x k2).oneValue (G k2) →
      (ground.getAt BPair.unit x k3).oneValue (G k3) → False) :
    ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue (G y) := by
  by_cases c0 : (ground.getAt BPair.unit x k0).oneValue (G k0)
  · by_cases c1 : (ground.getAt BPair.unit x k1).oneValue (G k1)
    · by_cases c2 : (ground.getAt BPair.unit x k2).oneValue (G k2)
      · exact ⟨k3, h3, fun c3 => hall c0 c1 c2 c3⟩
      · exact ⟨k2, h2, c2⟩
    · exact ⟨k1, h1, c1⟩
  · exact ⟨k0, h0, c0⟩

/-- The tail letter's refusal: a raised content reading plus two at
the rank's last key against its stated reads at the leading three
keys sits off the θ list, the column recursion carried to the
family's fourth coordinate. -/
private theorem termVanishTail (l q : Nat) (hq : q + 2 = l) (hl : 4 ≤ l)
    (x : List BPair) (a0 b0 a1 b1 a2 b2 : Nat)
    (e0 : (ground.getAt BPair.unit x 0).oneValue (BPair.ofCounts a0 b0))
    (e1 : (ground.getAt BPair.unit x 1).oneValue (BPair.ofCounts a1 b1))
    (e2 : (ground.getAt BPair.unit x 2).oneValue (BPair.ofCounts a2 b2))
    (et : (ground.getAt BPair.unit x (q + 1)).oneValue (BPair.ofCounts 2 0))
    (hpos : ∀ F : Nat → Nat, famCase l F →
      a0 + F 1 = 2 * F 0 + b0 →
      a1 + (F 0 + F 2) = 2 * F 1 + b1 →
      a2 + (F 1 + F 3) = 2 * F 2 + b2 →
      2 + 2 * F q = 2 * F (q + 1) + 0 → False)
    (hneg : ∀ F : Nat → Nat, famCase l F →
      a0 + 2 * F 0 = F 1 + b0 →
      a1 + 2 * F 1 = (F 0 + F 2) + b1 →
      a2 + 2 * F 2 = (F 1 + F 3) + b2 →
      2 + 2 * F (q + 1) = 2 * F q + 0 → False) :
    row.thetaCount (sertables.tableB l) x = 0 := by
  have h0l : (0 : Nat) < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h1l : (1 : Nat) < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h2l : (2 : Nat) < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h3l : (3 : Nat) < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have hne2 : ¬ 2 = l := Nat.ne_of_lt h2l
  have hne3 : ¬ 3 = l := Nat.ne_of_lt h3l
  have hq1l : q + 1 < l := by
    rw [← hq]
    exact Nat.lt_succ_self (q + 1)
  refine termVanish l x
    ⟨q + 1, hq1l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm et) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · have k0 : serstable.nbB l F 0 = F 1 := nbHead l F h1l
    have k1 : serstable.nbB l F 1 = F 0 + F 2 := nbMid l F 0 hne2
    have k2 : serstable.nbB l F 2 = F 1 + F 3 := nbMid l F 1 hne3
    have kt : serstable.nbB l F (q + 1) = 2 * F q := nbTop l F q hq
    refine pickOff l x
      (fun y => BPair.ofCounts (2 * F y) (serstable.nbB l F y))
      0 1 2 (q + 1) h0l h1l h2l hq1l (fun c0 c1 c2 c3 => ?_)
    refine hpos F hcase ?_ ?_ ?_ ?_
    · have hx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm e0) c0)
      rw [k0] at hx
      exact hx
    · have hx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm e1) c1)
      rw [k1] at hx
      exact hx
    · have hx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm e2) c2)
      rw [k2] at hx
      exact hx
    · have hx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm et) c3)
      rw [kt] at hx
      exact hx
  · have k0 : serstable.nbB l F 0 = F 1 := nbHead l F h1l
    have k1 : serstable.nbB l F 1 = F 0 + F 2 := nbMid l F 0 hne2
    have k2 : serstable.nbB l F 2 = F 1 + F 3 := nbMid l F 1 hne3
    have kt : serstable.nbB l F (q + 1) = 2 * F q := nbTop l F q hq
    refine pickOff l x
      (fun y => BPair.ofCounts (serstable.nbB l F y) (2 * F y))
      0 1 2 (q + 1) h0l h1l h2l hq1l (fun c0 c1 c2 c3 => ?_)
    refine hneg F hcase ?_ ?_ ?_ ?_
    · have hx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm e0) c0)
      rw [k0] at hx
      exact hx
    · have hx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm e1) c1)
      rw [k1] at hx
      exact hx
    · have hx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm e2) c2)
      rw [k2] at hx
      exact hx
    · have hx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm et) c3)
      rw [kt] at hx
      exact hx


/-! ### The witness edges: the displayed families' vacant folds -/

/-- A strict order refutes its own reverse at-or-below read. -/
private theorem ltRefute {a b : Nat} (h : a ≤ b) (hb : b < a) : False :=
  Nat.not_succ_le_self b (Nat.le_trans (Nat.succ_le_of_lt hb) h)

/-- A literal sits off every shift past it. -/
private theorem litNe (c n d : Nat) (h : c < d) : ¬ c = n + d :=
  Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_left d n))

/-- A family's leading coordinate is vacant or one. -/
private theorem headCases (l : Nat) (F : Nat → Nat) (hcase : famCase l F) :
    F 0 = 0 ∨ F 0 = 1 := ground.leOneCases (famHeadLe l F hcase)

/-- A shifted key sits off the vacant read. -/
private theorem sucNe0 (m : Nat) : ¬ m + 1 = 0 := fun hc => Nat.noConfusion hc

/-- A twice-shifted key sits off the unit read. -/
private theorem sucNe1 (m : Nat) : ¬ m + 2 = 1 :=
  fun hc => Nat.noConfusion (Nat.succ.inj hc)

/-- The unit sector's witness edge at `θ + (e₁ − e₂)`: the letter
fold reads the vacant count, so the row's two graded counts part by
one. -/
theorem edgeB_u1 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l)
      (serstable.memberRho [1, 1] l) (nA l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 3 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 3 := Nat.succ_lt_succ (Nat.succ_pos _)
  have hT : n + 2 < n + 3 := Nat.lt_succ_self _
  refine foldZeroG (sertables.tableB (n + 3)) 2 n 1 (n + 2) (by decide +kernel)
    (by show n + 3 = 2 + n + 1; rw [Nat.add_comm 2 n])
    (by rw [Nat.add_comm 2 n])
    (serstable.memberRho [1, 1] (n + 3)) (nA (n + 3)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapTh0 (n + 3) h0]
      exact termVanishMag (n + 3) 0 h0 _ _ _
        (raisedCount (n + 3) (fun k => if k = 0 then 2 else 0)
          (fun k => if k = 1 then 1 else 0) 1 0 0 h0 h0 2 0
          (cartDiag (n + 3) 0))
        (Or.inl (by decide +kernel))
    | 1, _ =>
      rw [kapTh1 (n + 3) h1]
      exact termVanishMag (n + 3) 1 h1 _ _ _
        (raisedCount (n + 3) (fun k => if k = 0 then 2 else 0)
          (fun k => if k = 1 then 1 else 0) 2 1 1 h1 h1 2 0
          (cartDiag (n + 3) 1))
        (Or.inl (by decide +kernel))
    | m + 2, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 3 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 3 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h1m : 1 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapTh (n + 3) (m + 1) hm hm1]
    refine serstable.runVanishB (n + 3) m _ hml (nuOf_length (n + 3) _) ?_ 0 h0
      (Or.inl h1m) ?_
    · exact nuVac (n + 3) (fun k => if k = 0 then 2 else 0)
        (fun k => if k = 1 then 1 else 0) (m + 1) hm1
        (by rw [if_neg (fun hc => Nat.noConfusion hc),
          if_neg (fun hc => Nat.not_succ_le_zero 0
            (by rw [Nat.succ.inj hc] at h1m; exact h1m))])
    · exact nuOcc (n + 3) (fun k => if k = 0 then 2 else 0)
        (fun k => if k = 1 then 1 else 0) 0 h0 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 2)) (n + 2)) = 0
      rw [kapTh (n + 3) (n + 2) (Nat.le_add_left 2 n) hT]
      exact termHeadAtTail (n + 3) (n + 1) (Nat.le_add_left 3 n)
        (Nat.le_add_left 1 n) rfl _
        (BPair.oneValue_trans
          (raisedCount (n + 3) (fun k => if k = 0 then 2 else 0)
            (fun k => if k = 1 then 1 else 0) 1 (n + 2) 0 hT h0 0 0
            (cartOff (n + 3) (n + 2) 0 (fun hc => Nat.noConfusion hc)
              (fun hc => Nat.noConfusion hc)
              (fun hc => Nat.noConfusion (Nat.succ.inj hc))))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 3) (fun k => if k = 0 then 2 else 0)
          (fun k => if k = 1 then 1 else 0) 1 (n + 2) (n + 2) hT hT 2 0
          (cartDiag (n + 3) (n + 2)))
        (by rw [if_neg (sucNe0 (n + 1)), if_neg (sucNe1 n)]
            exact (by decide +kernel))
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))


/-- The spinor sector's witness edge at `spinor + e₁`. -/
theorem edgeB_s1 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l)
      (basedRho [] l 0) (nB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 3 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 3 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 3 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 n)
  have hT : n + 2 < n + 3 := Nat.lt_succ_self _
  refine foldZeroG (sertables.tableB (n + 3)) 2 n 1 (n + 2) (by decide +kernel)
    (by show n + 3 = 2 + n + 1; rw [Nat.add_comm 2 n])
    (by rw [Nat.add_comm 2 n])
    (basedRho [] (n + 3) 0) (nB (n + 3)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapSp (n + 3) 0 h0 (litNe 1 n 3 (by decide +kernel))]
      exact termVanishMag (n + 3) 0 h0 _ _ _
        (raisedCount (n + 3) (fun k => if k = 0 then 1 else 0)
          (fun _ => 0) 1 0 0 h0 h0 2 0 (cartDiag (n + 3) 0))
        (Or.inl (by decide +kernel))
    | 1, _ =>
      rw [kapSp (n + 3) 1 h1 (litNe 2 n 3 (by decide +kernel))]
      exact termTwoBelow (n + 3) 0 h2 _
        (BPair.oneValue_trans
          (raisedCount (n + 3) (fun k => if k = 0 then 1 else 0)
            (fun _ => 0) 1 1 1 h1 h1 2 0 (cartDiag (n + 3) 1))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 3) (fun k => if k = 0 then 1 else 0)
          (fun _ => 0) 1 1 0 h1 h0 0 1 (cartDn (n + 3) 0))
        (by decide +kernel)
    | m + 2, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 3 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 3 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h1m : 1 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapSp (n + 3) (m + 1) hm1 (Nat.ne_of_lt hml)]
    refine serstable.runVanishB (n + 3) m _ hml (nuOf_length (n + 3) _) ?_ 0 h0
      (Or.inl h1m) ?_
    · exact nuVac (n + 3) (fun k => if k = 0 then 1 else 0)
        (fun _ => 0) (m + 1) hm1 (by rw [if_neg (sucNe0 m)])
    · exact nuOcc (n + 3) (fun k => if k = 0 then 1 else 0)
        (fun _ => 0) 0 h0 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 2)) (n + 2)) = 0
      rw [kapSpT (n + 3) (n + 2) hT rfl]
      exact termVanishMag (n + 3) (n + 2) hT _ _ _
        (raisedCount (n + 3) (fun k => if k = 0 then 1 else 0)
          (fun _ => 0) 2 (n + 2) (n + 2) hT hT 2 0
          (cartDiag (n + 3) (n + 2)))
        (Or.inl (by rw [if_neg (sucNe0 (n + 1))]
                    exact (by decide +kernel)))
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))

/-- The spinor sector's witness edge at `e₁ + e₁`, the doubled
leading coordinate. -/
theorem edgeB_s3 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l)
      (basedRho [1] l 0) (nB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 3 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 3 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 3 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 n)
  have hT : n + 2 < n + 3 := Nat.lt_succ_self _
  have hl2 : 2 ≤ n + 3 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 3 n)
  refine foldZeroG (sertables.tableB (n + 3)) 2 n 1 (n + 2) (by decide +kernel)
    (by show n + 3 = 2 + n + 1; rw [Nat.add_comm 2 n])
    (by rw [Nat.add_comm 2 n])
    (basedRho [1] (n + 3) 0) (nB (n + 3)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapE1H (n + 3) hl2]
      exact termVanishMag (n + 3) 0 h0 _ _ _
        (raisedCount (n + 3) (fun k => if k = 0 then 1 else 0)
          (fun _ => 0) 2 0 0 h0 h0 2 0 (cartDiag (n + 3) 0))
        (Or.inl (by decide +kernel))
    | 1, _ =>
      rw [kapE1 (n + 3) 1 (Nat.le_refl 1) h1 (litNe 2 n 3 (by decide +kernel))]
      exact termTwoBelow (n + 3) 0 h2 _
        (BPair.oneValue_trans
          (raisedCount (n + 3) (fun k => if k = 0 then 1 else 0)
            (fun _ => 0) 1 1 1 h1 h1 2 0 (cartDiag (n + 3) 1))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 3) (fun k => if k = 0 then 1 else 0)
          (fun _ => 0) 1 1 0 h1 h0 0 1 (cartDn (n + 3) 0))
        (by decide +kernel)
    | m + 2, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 3 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 3 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h1m : 1 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapE1 (n + 3) (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hm1
      (Nat.ne_of_lt hml)]
    refine serstable.runVanishB (n + 3) m _ hml (nuOf_length (n + 3) _) ?_ 0 h0
      (Or.inl h1m) ?_
    · exact nuVac (n + 3) (fun k => if k = 0 then 1 else 0)
        (fun _ => 0) (m + 1) hm1 (by rw [if_neg (sucNe0 m)])
    · exact nuOcc (n + 3) (fun k => if k = 0 then 1 else 0)
        (fun _ => 0) 0 h0 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 2)) (n + 2)) = 0
      rw [kapE1T (n + 3) (n + 2) (Nat.le_add_left 1 (n + 1)) hT rfl]
      exact termVanishMag (n + 3) (n + 2) hT _ _ _
        (raisedCount (n + 3) (fun k => if k = 0 then 1 else 0)
          (fun _ => 0) 2 (n + 2) (n + 2) hT hT 2 0
          (cartDiag (n + 3) (n + 2)))
        (Or.inl (by rw [if_neg (sucNe0 (n + 1))]
                    exact (by decide +kernel)))
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))


/-- The spinor sector's witness edge at `spinor + (e₁ + e₂)`. -/
theorem edgeB_s2 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l) (basedRho [] l 0) (nC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 4 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 4 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have h3 : (3 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have hT3 : n + 3 < n + 4 := Nat.lt_succ_self _
  have hl2 : 2 ≤ n + 4 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 n)
  have hl3 : 3 ≤ n + 4 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 n)
  refine foldZeroG (sertables.tableB (n + 4)) 3 n 1 (n + 3) (by decide +kernel)
    (by show n + 4 = 3 + n + 1; rw [Nat.add_comm 3 n])
    (by rw [Nat.add_comm 3 n])
    (basedRho [] (n + 4) 0) (nC (n + 4)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapSp (n + 4) 0 h0 (litNe 1 n 4 (by decide +kernel))]
      exact termHeadAtOne (n + 4) hl3 _
        (BPair.oneValue_trans
          (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
            1 0 0 h0 h0 2 0 (cartDiag (n + 4) 0))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 0 1 h0 h1 0 1
          (cartUp1 (n + 4) 0 (litNe 2 n 4 (by decide +kernel))))
        (by decide +kernel)
    | 1, _ =>
      rw [kapSp (n + 4) 1 h1 (litNe 2 n 4 (by decide +kernel))]
      exact termVanishMag (n + 4) 1 h1 _ _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 1 1 h1 h1 2 0 (cartDiag (n + 4) 1))
        (Or.inl (by decide +kernel))
    | 2, _ =>
      rw [kapSp (n + 4) 2 h2 (litNe 3 n 4 (by decide +kernel))]
      exact termTwoBelow (n + 4) 1 h3 _
        (BPair.oneValue_trans
          (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
            1 2 2 h2 h2 2 0 (cartDiag (n + 4) 2))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 2 1 h2 h1 0 1 (cartDn (n + 4) 1))
        (by decide +kernel)
    | m + 3, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 4 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 4 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h2m : 2 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapSp (n + 4) (m + 1) hm1 (Nat.ne_of_lt hml)]
    refine serstable.runVanishB (n + 4) m _ hml (nuOf_length (n + 4) _) ?_ 1 h1
      (Or.inl h2m) ?_
    · exact nuVac (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        (m + 1) hm1 (by rw [if_neg (fun hc => Nat.not_succ_le_zero 1
          (by rw [Nat.succ.inj hc] at h2m; exact h2m))])
    · exact nuOcc (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        1 h1 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 3)) (n + 3)) = 0
      rw [kapSpT (n + 4) (n + 3) hT3 rfl]
      exact termVanishMag (n + 4) (n + 3) hT3 _ _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          2 (n + 3) (n + 3) hT3 hT3 2 0 (cartDiag (n + 4) (n + 3)))
        (Or.inl (by rw [if_neg (sucNe1 (n + 1))]
                    exact (by decide +kernel)))
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))

/-- The spinor sector's witness edge at `e₁ + (e₁ + e₂)`. -/
theorem edgeB_s4 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l) (basedRho [1] l 0) (nC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 4 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 4 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have h3 : (3 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have hT3 : n + 3 < n + 4 := Nat.lt_succ_self _
  have hl2 : 2 ≤ n + 4 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 n)
  have hl3 : 3 ≤ n + 4 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 n)
  refine foldZeroG (sertables.tableB (n + 4)) 3 n 1 (n + 3) (by decide +kernel)
    (by show n + 4 = 3 + n + 1; rw [Nat.add_comm 3 n])
    (by rw [Nat.add_comm 3 n])
    (basedRho [1] (n + 4) 0) (nC (n + 4)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapE1H (n + 4) hl2]
      exact termVanishMag (n + 4) 0 h0 _ _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          2 0 0 h0 h0 2 0 (cartDiag (n + 4) 0))
        (Or.inl (by decide +kernel))
    | 1, _ =>
      rw [kapE1 (n + 4) 1 (Nat.le_refl 1) h1 (litNe 2 n 4 (by decide +kernel))]
      exact termVanishMag (n + 4) 1 h1 _ _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 1 1 h1 h1 2 0 (cartDiag (n + 4) 1))
        (Or.inl (by decide +kernel))
    | 2, _ =>
      rw [kapE1 (n + 4) 2 (Nat.le_succ 1) h2 (litNe 3 n 4 (by decide +kernel))]
      exact termTwoBelow (n + 4) 1 h3 _
        (BPair.oneValue_trans
          (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
            1 2 2 h2 h2 2 0 (cartDiag (n + 4) 2))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 2 1 h2 h1 0 1 (cartDn (n + 4) 1))
        (by decide +kernel)
    | m + 3, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 4 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 4 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h2m : 2 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapE1 (n + 4) (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hm1 (Nat.ne_of_lt hml)]
    refine serstable.runVanishB (n + 4) m _ hml (nuOf_length (n + 4) _) ?_ 1 h1
      (Or.inl h2m) ?_
    · exact nuVac (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        (m + 1) hm1 (by rw [if_neg (fun hc => Nat.not_succ_le_zero 1
          (by rw [Nat.succ.inj hc] at h2m; exact h2m))])
    · exact nuOcc (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        1 h1 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 3)) (n + 3)) = 0
      rw [kapE1T (n + 4) (n + 3) (Nat.le_add_left 1 (n + 2)) hT3 rfl]
      exact termVanishMag (n + 4) (n + 3) hT3 _ _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          2 (n + 3) (n + 3) hT3 hT3 2 0 (cartDiag (n + 4) (n + 3)))
        (Or.inl (by rw [if_neg (sucNe1 (n + 1))]
                    exact (by decide +kernel)))
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))

/-- The spinor sector's witness edge at `(e₁ + e₂) + (e₁ + e₂)`, the doubled leading pair. -/
theorem edgeB_s7 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l) (basedRho [1, 1] l 0) (nC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 4 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 4 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have h3 : (3 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have hT3 : n + 3 < n + 4 := Nat.lt_succ_self _
  have hl2 : 2 ≤ n + 4 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 n)
  have hl3 : 3 ≤ n + 4 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 n)
  refine foldZeroG (sertables.tableB (n + 4)) 3 n 1 (n + 3) (by decide +kernel)
    (by show n + 4 = 3 + n + 1; rw [Nat.add_comm 3 n])
    (by rw [Nat.add_comm 3 n])
    (basedRho [1, 1] (n + 4) 0) (nC (n + 4)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapE12H (n + 4) hl2]
      exact termHeadAtOne (n + 4) hl3 _
        (BPair.oneValue_trans
          (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
            1 0 0 h0 h0 2 0 (cartDiag (n + 4) 0))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 0 1 h0 h1 0 1
          (cartUp1 (n + 4) 0 (litNe 2 n 4 (by decide +kernel))))
        (by decide +kernel)
    | 1, _ =>
      rw [kapE12A (n + 4) hl3]
      exact termVanishMag (n + 4) 1 h1 _ _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          2 1 1 h1 h1 2 0 (cartDiag (n + 4) 1))
        (Or.inl (by decide +kernel))
    | 2, _ =>
      rw [kapE12 (n + 4) 2 (Nat.le_refl 2) h2 (litNe 3 n 4 (by decide +kernel))]
      exact termTwoBelow (n + 4) 1 h3 _
        (BPair.oneValue_trans
          (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
            1 2 2 h2 h2 2 0 (cartDiag (n + 4) 2))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 2 1 h2 h1 0 1 (cartDn (n + 4) 1))
        (by decide +kernel)
    | m + 3, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 4 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 4 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h2m : 2 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapE12 (n + 4) (m + 1) (Nat.succ_le_succ (Nat.le_trans (Nat.le_succ 1) h2m)) hm1
      (Nat.ne_of_lt hml)]
    refine serstable.runVanishB (n + 4) m _ hml (nuOf_length (n + 4) _) ?_ 1 h1
      (Or.inl h2m) ?_
    · exact nuVac (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        (m + 1) hm1 (by rw [if_neg (fun hc => Nat.not_succ_le_zero 1
          (by rw [Nat.succ.inj hc] at h2m; exact h2m))])
    · exact nuOcc (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        1 h1 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 3)) (n + 3)) = 0
      rw [kapE12T (n + 4) (n + 3) (Nat.le_add_left 2 (n + 1)) hT3 rfl]
      exact termVanishMag (n + 4) (n + 3) hT3 _ _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          2 (n + 3) (n + 3) hT3 hT3 2 0 (cartDiag (n + 4) (n + 3)))
        (Or.inl (by rw [if_neg (sucNe1 (n + 1))]
                    exact (by decide +kernel)))
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))

/-- A leading unit cancels against a shifted read. -/
private theorem oneAddCancel {x c : Nat} (h : 1 + x = c + 1) : x = c :=
  Nat.succ.inj ((Nat.add_comm 1 x).symm.trans h)

/-- The unit sector's tail letter at `θ + (e₁ + e₂)`: the raised
content's leading reads carry the column recursion to the family's
third coordinate, which its tail read then refuses. -/
private theorem tailU2 (n : Nat) :
    row.thetaCount (sertables.tableB (n + 4))
      (raisedG (sertables.tableB (n + 4)) (nC (n + 4)) 1 (n + 3)) = 0 := by
  have h0 : (0 : Nat) < n + 4 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 4 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have hT3 : n + 3 < n + 4 := Nat.lt_succ_self _
  have hl4 : 4 ≤ n + 4 := Nat.le_add_left 4 n
  have e0 : (ground.getAt BPair.unit
      (raisedG (sertables.tableB (n + 4)) (nC (n + 4)) 1 (n + 3)) 0).oneValue
      (BPair.ofCounts 0 0) :=
    BPair.oneValue_trans
      (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        1 (n + 3) 0 hT3 h0 0 0
        (cartOff (n + 4) (n + 3) 0 (fun hc => Nat.noConfusion hc)
          (fun hc => Nat.noConfusion hc) (litNe 1 n 3 (by decide +kernel))))
      (BPair.ofCounts_crossed (by decide +kernel))
  have e1 : (ground.getAt BPair.unit
      (raisedG (sertables.tableB (n + 4)) (nC (n + 4)) 1 (n + 3)) 1).oneValue
      (BPair.ofCounts 1 0) :=
    BPair.oneValue_trans
      (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        1 (n + 3) 1 hT3 h1 0 0
        (cartOff (n + 4) (n + 3) 1 (litNe 1 n 3 (by decide +kernel))
          (litNe 1 n 4 (by decide +kernel))
          (litNe 2 n 3 (by decide +kernel))))
      (BPair.ofCounts_crossed (by decide +kernel))
  have et : (ground.getAt BPair.unit
      (raisedG (sertables.tableB (n + 4)) (nC (n + 4)) 1 (n + 3)) (n + 2 + 1)).oneValue
      (BPair.ofCounts 2 0) :=
    BPair.oneValue_trans
      (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        1 (n + 3) (n + 3) hT3 hT3 2 0 (cartDiag (n + 4) (n + 3)))
      (BPair.ofCounts_crossed (by rw [if_neg (sucNe1 (n + 1))]))
  match n with
  | 0 =>
    have e2 : (ground.getAt BPair.unit
        (raisedG (sertables.tableB (0 + 4)) (nC (0 + 4)) 1 (0 + 3)) 2).oneValue
        (BPair.ofCounts 0 1) :=
      BPair.oneValue_trans
        (raisedCount (0 + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 (0 + 3) 2 hT3 h2 0 1 (cartDn (0 + 4) 2))
        (BPair.ofCounts_crossed (by decide +kernel))
    refine termVanishTail (0 + 4) 2 rfl hl4 _ 0 0 1 0 0 1 e0 e1 e2 et
      (fun F hcase q0 q1 q2 q3 => ?_) (fun F hcase q0 q1 q2 q3 => ?_)
    · match headCases (0 + 4) F hcase with
      | .inl hf0 =>
        rw [hf0] at q0 q1
        have hf1 : F 1 = 0 := by rw [Nat.zero_add] at q0; exact q0
        rw [hf1] at q1
        exact ground.oneAddNeZero (0 + F 2) q1
      | .inr hf0 =>
        rw [hf0] at q0 q1
        have hf1 : F 1 = 2 := by rw [Nat.zero_add] at q0; exact q0
        rw [hf1] at q1
        have hf2 : F 2 = 2 := oneAddCancel (oneAddCancel q1)
        obtain ⟨ht1, ht0⟩ := tailRefuse (0 + 4) 2 2 rfl (Nat.le_refl 2)
          F hcase hf2
        rw [ht0, ht1] at q3
        exact absurd q3 (by decide +kernel)
    · match headCases (0 + 4) F hcase with
      | .inr hf0 =>
        rw [hf0] at q0 q1
        have hf1 : F 1 = 2 := by rw [Nat.add_zero] at q0; exact q0.symm
        rw [hf1] at q1
        have hf2 : F 2 = 4 := oneAddCancel q1.symm
        have hcap := famCap (0 + 4) F hcase 2
        rw [hf2] at hcap
        exact absurd hcap (by decide +kernel)
      | .inl hf0 =>
        rw [hf0] at q0 q1
        have hf1 : F 1 = 0 := by rw [Nat.add_zero] at q0; exact q0.symm
        rw [hf1] at q1 q2
        have hf2 : F 2 = 1 := by
          rw [Nat.add_zero, Nat.zero_add] at q1
          exact q1.symm
        rw [hf2] at q2 q3
        have hf3 : F 3 = 1 := by
          rw [Nat.zero_add (2 * 1), Nat.zero_add (F 3)] at q2
          exact Nat.succ.inj q2.symm
        rw [hf3] at q3
        exact absurd q3 (by decide +kernel)
  | j + 1 =>
    have e2 : (ground.getAt BPair.unit
        (raisedG (sertables.tableB (j + 1 + 4)) (nC (j + 1 + 4)) 1 (j + 1 + 3)) 2).oneValue
        (BPair.ofCounts 0 0) :=
      BPair.oneValue_trans
        (raisedCount (j + 1 + 4) (fun k => if k = 1 then 1 else 0)
          (fun _ => 0) 1 (j + 1 + 3) 2 hT3 h2 0 0
          (cartOff (j + 1 + 4) (j + 1 + 3) 2
            (litNe 2 (j + 1) 3 (by decide +kernel))
            (litNe 2 (j + 1) 4 (by decide +kernel))
            (litNe 3 j 4 (by decide +kernel))))
        (BPair.ofCounts_crossed (by decide +kernel))
    refine termVanishTail (j + 1 + 4) (j + 3) rfl hl4 _ 0 0 1 0 0 0
      e0 e1 e2 et (fun F hcase q0 q1 q2 q3 => ?_) (fun F hcase q0 q1 q2 q3 => ?_)
    · match headCases (j + 1 + 4) F hcase with
      | .inl hf0 =>
        rw [hf0] at q0 q1
        have hf1 : F 1 = 0 := by rw [Nat.zero_add] at q0; exact q0
        rw [hf1] at q1
        exact ground.oneAddNeZero (0 + F 2) q1
      | .inr hf0 =>
        rw [hf0] at q0 q1
        have hf1 : F 1 = 2 := by rw [Nat.zero_add] at q0; exact q0
        rw [hf1] at q1
        have hf2 : F 2 = 2 := oneAddCancel (oneAddCancel q1)
        obtain ⟨ht1, ht0⟩ := tailRefuse (j + 1 + 4) (j + 3) 2 rfl
          (Nat.le_add_left 2 (j + 1)) F hcase hf2
        rw [ht0, ht1] at q3
        exact absurd q3 (by decide +kernel)
    · match headCases (j + 1 + 4) F hcase with
      | .inr hf0 =>
        rw [hf0] at q0 q1
        have hf1 : F 1 = 2 := by rw [Nat.add_zero] at q0; exact q0.symm
        rw [hf1] at q1
        have hf2 : F 2 = 4 := oneAddCancel q1.symm
        have hcap := famCap (j + 1 + 4) F hcase 2
        rw [hf2] at hcap
        exact absurd hcap (by decide +kernel)
      | .inl hf0 =>
        rw [hf0] at q0 q1
        have hf1 : F 1 = 0 := by rw [Nat.add_zero] at q0; exact q0.symm
        rw [hf1] at q1 q2
        have hf2 : F 2 = 1 := by
          rw [Nat.add_zero, Nat.zero_add] at q1
          exact q1.symm
        rw [hf2] at q2
        have hf3 : F 3 = 2 := by
          rw [Nat.zero_add, Nat.add_zero, Nat.zero_add] at q2
          exact q2.symm
        obtain ⟨ht1, ht0⟩ := tailRefuse (j + 1 + 4) (j + 3) 3 rfl
          (Nat.le_add_left 3 j) F hcase hf3
        rw [ht0, ht1] at q3
        exact absurd q3 (by decide +kernel)

/-- The unit sector's witness edge at `θ + (e₁ + e₂)`. -/
theorem edgeB_u2 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l)
      (serstable.memberRho [1, 1] l) (nC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 4 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 4 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have h3 : (3 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have hT3 : n + 3 < n + 4 := Nat.lt_succ_self _
  have hl3 : 3 ≤ n + 4 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 n)
  refine foldZeroG (sertables.tableB (n + 4)) 3 n 1 (n + 3) (by decide +kernel)
    (by show n + 4 = 3 + n + 1; rw [Nat.add_comm 3 n])
    (by rw [Nat.add_comm 3 n])
    (serstable.memberRho [1, 1] (n + 4)) (nC (n + 4)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapTh0 (n + 4) h0]
      exact termHeadAtOne (n + 4) hl3 _
        (BPair.oneValue_trans
          (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
            1 0 0 h0 h0 2 0 (cartDiag (n + 4) 0))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 0 1 h0 h1 0 1
          (cartUp1 (n + 4) 0 (litNe 2 n 4 (by decide +kernel))))
        (by decide +kernel)
    | 1, _ =>
      rw [kapTh1 (n + 4) h1]
      exact termVanishMag (n + 4) 1 h1 _ _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          2 1 1 h1 h1 2 0 (cartDiag (n + 4) 1))
        (Or.inl (by decide +kernel))
    | 2, _ =>
      rw [kapTh (n + 4) 2 (Nat.le_refl 2) h2]
      exact termTwoBelow (n + 4) 1 h3 _
        (BPair.oneValue_trans
          (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
            1 2 2 h2 h2 2 0 (cartDiag (n + 4) 2))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
          1 2 1 h2 h1 0 1 (cartDn (n + 4) 1))
        (by decide +kernel)
    | m + 3, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 4 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 4 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h2m : 2 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapTh (n + 4) (m + 1) (Nat.le_trans (Nat.le_succ 2) hm) hm1]
    refine serstable.runVanishB (n + 4) m _ hml (nuOf_length (n + 4) _) ?_ 1 h1
      (Or.inl h2m) ?_
    · exact nuVac (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        (m + 1) hm1 (by rw [if_neg (fun hc => Nat.not_succ_le_zero 1
          (by rw [Nat.succ.inj hc] at h2m; exact h2m))])
    · exact nuOcc (n + 4) (fun k => if k = 1 then 1 else 0) (fun _ => 0)
        1 h1 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 3)) (n + 3)) = 0
      rw [kapTh (n + 4) (n + 3) (Nat.le_add_left 2 (n + 1)) hT3]
      exact tailU2 n
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))


/-- A shifted key sits off every literal below its own shift. -/
private theorem shiftNeLit (n c d : Nat) (h : d < c) : ¬ n + c = d :=
  fun hc => Nat.not_succ_le_self d (Nat.le_trans (Nat.succ_le_of_lt h)
    (Nat.le_trans (Nat.le_add_left c n) (Nat.le_of_eq hc)))

/-- The unit sector's tail letter at `θ + (e₁ + e₃)`. -/
private theorem tailU3 (n : Nat) :
    row.thetaCount (sertables.tableB (n + 5))
      (raisedG (sertables.tableB (n + 5)) (nD (n + 5)) 1 (n + 4)) = 0 := by
  have h0 : (0 : Nat) < n + 5 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 5 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 5 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 n)
  have hT4 : n + 4 < n + 5 := Nat.lt_succ_self _
  have hl4 : 4 ≤ n + 5 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 n)
  refine termVanishTail (n + 5) (n + 3) rfl hl4 _ 1 0 0 1 1 0
    (BPair.oneValue_trans
      (raisedCount (n + 5) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0)
        (fun k => if k = 1 then 1 else 0) 1 (n + 4) 0 hT4 h0 0 0
        (cartOff (n + 5) (n + 4) 0 (fun hc => Nat.noConfusion hc)
          (fun hc => Nat.noConfusion hc) (litNe 1 n 4 (by decide +kernel))))
      (BPair.ofCounts_crossed (by decide +kernel)))
    (BPair.oneValue_trans
      (raisedCount (n + 5) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0)
        (fun k => if k = 1 then 1 else 0) 1 (n + 4) 1 hT4 h1 0 0
        (cartOff (n + 5) (n + 4) 1 (litNe 1 n 4 (by decide +kernel))
          (litNe 1 n 5 (by decide +kernel))
          (litNe 2 n 4 (by decide +kernel))))
      (BPair.ofCounts_crossed (by decide +kernel)))
    (BPair.oneValue_trans
      (raisedCount (n + 5) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0)
        (fun k => if k = 1 then 1 else 0) 1 (n + 4) 2 hT4 h2 0 0
        (cartOff (n + 5) (n + 4) 2 (litNe 2 n 4 (by decide +kernel))
          (litNe 2 n 5 (by decide +kernel))
          (litNe 3 n 4 (by decide +kernel))))
      (BPair.ofCounts_crossed (by decide +kernel)))
    (BPair.oneValue_trans
      (raisedCount (n + 5) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0)
        (fun k => if k = 1 then 1 else 0) 1 (n + 4) (n + 4) hT4 hT4 2 0
        (cartDiag (n + 5) (n + 4)))
      (BPair.ofCounts_crossed
        (by rw [if_neg (shiftNeLit n 4 0 (by decide +kernel)),
          if_neg (shiftNeLit n 4 2 (by decide +kernel)),
          if_neg (shiftNeLit n 4 1 (by decide +kernel))])))
    (fun F hcase q0 q1 q2 q3 => ?_) (fun F hcase q0 q1 q2 q3 => ?_)
  · match headCases (n + 5) F hcase with
    | .inl hf0 =>
      rw [hf0] at q0
      exact ground.oneAddNeZero (F 1) q0
    | .inr hf0 =>
      rw [hf0] at q0 q1
      have hf1 : F 1 = 1 := oneAddCancel q0
      rw [hf1] at q1
      have hf2 : F 2 = 2 := by
        rw [Nat.zero_add] at q1
        exact oneAddCancel q1
      obtain ⟨ht1, ht0⟩ := tailRefuse (n + 5) (n + 3) 2 rfl
        (Nat.le_add_left 2 (n + 1)) F hcase hf2
      rw [ht0, ht1] at q3
      exact absurd q3 (by decide +kernel)
  · match headCases (n + 5) F hcase with
    | .inr hf0 =>
      rw [hf0] at q0
      have hf1 : F 1 = 3 := by rw [Nat.add_zero] at q0; exact q0.symm
      have hcap := famCap (n + 5) F hcase 1
      rw [hf1] at hcap
      exact absurd hcap (by decide +kernel)
    | .inl hf0 =>
      rw [hf0] at q0 q1
      have hf1 : F 1 = 1 := by rw [Nat.add_zero] at q0; exact q0.symm
      rw [hf1] at q1 q2
      have hf2 : F 2 = 1 := by
        rw [Nat.zero_add (2 * 1), Nat.zero_add (F 2)] at q1
        exact Nat.succ.inj q1.symm
      rw [hf2] at q2
      have hf3 : F 3 = 2 := by
        rw [Nat.add_zero] at q2
        exact oneAddCancel q2.symm
      obtain ⟨ht1, ht0⟩ := tailRefuse (n + 5) (n + 3) 3 rfl
        (Nat.le_add_left 3 n) F hcase hf3
      rw [ht0, ht1] at q3
      exact absurd q3 (by decide +kernel)


/-- The unit sector's witness edge at `θ + (e₁ + e₃)`. -/
theorem edgeB_u3 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l)
      (serstable.memberRho [1, 1] l) (nD l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 5 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 5 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 5 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 n)
  have hT4 : n + 4 < n + 5 := Nat.lt_succ_self _
  refine foldZeroG (sertables.tableB (n + 5)) 3 (n + 1) 1 (n + 4) (by decide +kernel)
    (by show n + 5 = 3 + (n + 1) + 1; rw [Nat.add_comm 3 (n + 1)])
    (by rw [Nat.add_comm 3 (n + 1)])
    (serstable.memberRho [1, 1] (n + 5)) (nD (n + 5)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapTh0 (n + 5) h0]
      exact termVanishMag ((n + 5)) 0 h0 _ _ _
        (raisedCount ((n + 5)) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          1 0 0 h0 h0 2 0 (cartDiag ((n + 5)) 0))
        (Or.inl (by decide +kernel))
    | 1, _ =>
      rw [kapTh1 (n + 5) h1]
      exact termVanishMag ((n + 5)) 1 h1 _ _ _
        (raisedCount ((n + 5)) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          2 1 1 h1 h1 2 0 (cartDiag ((n + 5)) 1))
        (Or.inl (by decide +kernel))
    | 2, _ =>
      rw [kapTh (n + 5) 2 (Nat.le_refl 2) h2]
      exact termVanishMag ((n + 5)) 2 h2 _ _ _
        (raisedCount ((n + 5)) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          1 2 2 h2 h2 2 0 (cartDiag ((n + 5)) 2))
        (Or.inl (by decide +kernel))
    | m + 3, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 5 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 5 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h2m : 2 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapTh (n + 5) (m + 1) (Nat.le_trans (Nat.le_succ 2) hm) hm1]
    refine serstable.runVanishB (n + 5) m _ hml (nuOf_length (n + 5) _) ?_ 0 h0
      (Or.inl (Nat.le_trans (Nat.le_succ 1) h2m)) ?_
    · exact nuVac (n + 5) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
        (m + 1) hm1 (by rw [if_neg (sucNe0 m),
          if_neg (fun hc => Nat.not_succ_le_self 1
            (by rw [Nat.succ.inj hc] at h2m; exact h2m)),
          if_neg (fun hc => Nat.not_succ_le_zero 1
            (by rw [Nat.succ.inj hc] at h2m; exact h2m))])
    · exact nuOcc (n + 5) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
        0 h0 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 4)) (n + 4)) = 0
      rw [kapTh (n + 5) (n + 4) (Nat.le_add_left 2 (n + 2)) hT4]
      exact tailU3 n
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))

/-- The spinor sector's witness edge at `(e₁ + e₂) + (e₁ + e₃)`. -/
theorem edgeB_s8 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l)
      (basedRho [1, 1] l 0) (nD l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 5 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 5 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 5 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 n)
  have hT4 : n + 4 < n + 5 := Nat.lt_succ_self _
  have hl2 : 2 ≤ n + 5 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 n)
  have hl3 : 3 ≤ n + 5 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 n)
  refine foldZeroG (sertables.tableB (n + 5)) 3 (n + 1) 1 (n + 4) (by decide +kernel)
    (by show n + 5 = 3 + (n + 1) + 1; rw [Nat.add_comm 3 (n + 1)])
    (by rw [Nat.add_comm 3 (n + 1)])
    (basedRho [1, 1] (n + 5) 0) (nD (n + 5)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapE12H (n + 5) hl2]
      exact termVanishMag ((n + 5)) 0 h0 _ _ _
        (raisedCount ((n + 5)) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          1 0 0 h0 h0 2 0 (cartDiag ((n + 5)) 0))
        (Or.inl (by decide +kernel))
    | 1, _ =>
      rw [kapE12A (n + 5) hl3]
      exact termVanishMag ((n + 5)) 1 h1 _ _ _
        (raisedCount ((n + 5)) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          2 1 1 h1 h1 2 0 (cartDiag ((n + 5)) 1))
        (Or.inl (by decide +kernel))
    | 2, _ =>
      rw [kapE12 (n + 5) 2 (Nat.le_refl 2) h2 (litNe 3 n 5 (by decide +kernel))]
      exact termVanishMag ((n + 5)) 2 h2 _ _ _
        (raisedCount ((n + 5)) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          1 2 2 h2 h2 2 0 (cartDiag ((n + 5)) 2))
        (Or.inl (by decide +kernel))
    | m + 3, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 5 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 5 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h2m : 2 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapE12 (n + 5) (m + 1)
      (Nat.succ_le_succ (Nat.le_trans (Nat.le_succ 1) h2m)) hm1
      (Nat.ne_of_lt hml)]
    refine serstable.runVanishB (n + 5) m _ hml (nuOf_length (n + 5) _) ?_ 0 h0
      (Or.inl (Nat.le_trans (Nat.le_succ 1) h2m)) ?_
    · exact nuVac (n + 5) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
        (m + 1) hm1 (by rw [if_neg (sucNe0 m),
          if_neg (fun hc => Nat.not_succ_le_self 1
            (by rw [Nat.succ.inj hc] at h2m; exact h2m)),
          if_neg (fun hc => Nat.not_succ_le_zero 1
            (by rw [Nat.succ.inj hc] at h2m; exact h2m))])
    · exact nuOcc (n + 5) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
        0 h0 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 4)) (n + 4)) = 0
      rw [kapE12T (n + 5) (n + 4) (Nat.le_add_left 2 (n + 2)) hT4 rfl]
      exact termVanishMag (n + 5) (n + 4) hT4 _ _ _
        (raisedCount (n + 5) (fun k => if k = 0 then 1 else if k = 2 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          2 (n + 4) (n + 4) hT4 hT4 2 0 (cartDiag (n + 5) (n + 4)))
        (Or.inl (by
          rw [if_neg (shiftNeLit n 4 0 (by decide +kernel)),
            if_neg (shiftNeLit n 4 2 (by decide +kernel)),
            if_neg (shiftNeLit n 4 1 (by decide +kernel))]
          exact (by decide +kernel)))
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))

/-- The spinor sector's witness edge at `e₁ + (e₂ + e₃)`. -/
theorem edgeB_s5 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l)
      (basedRho [1] l 0) (nE l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 5 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 5 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 5 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 n)
  have hT4 : n + 4 < n + 5 := Nat.lt_succ_self _
  have hl2 : 2 ≤ n + 5 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 n)
  refine foldZeroG (sertables.tableB (n + 5)) 3 (n + 1) 1 (n + 4) (by decide +kernel)
    (by show n + 5 = 3 + (n + 1) + 1; rw [Nat.add_comm 3 (n + 1)])
    (by rw [Nat.add_comm 3 (n + 1)])
    (basedRho [1] (n + 5) 0) (nE (n + 5)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapE1H (n + 5) hl2]
      exact termVanishMag ((n + 5)) 0 h0 _ _ _
        (raisedCount ((n + 5)) (fun k => if k = 2 then 1 else 0) (fun k => if k = 0 then 1 else 0)
          2 0 0 h0 h0 2 0 (cartDiag ((n + 5)) 0))
        (Or.inl (by decide +kernel))
    | 1, _ =>
      rw [kapE1 (n + 5) 1 (Nat.le_refl 1) h1 (litNe 2 n 5 (by decide +kernel))]
      exact termTwoBelow (n + 5) 0 h2 _
        (BPair.oneValue_trans
          (raisedCount (n + 5) (fun k => if k = 2 then 1 else 0) (fun k => if k = 0 then 1 else 0)
            1 1 1 h1 h1 2 0 (cartDiag (n + 5) 1))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 5) (fun k => if k = 2 then 1 else 0) (fun k => if k = 0 then 1 else 0)
          1 1 0 h1 h0 0 1 (cartDn (n + 5) 0))
        (by decide +kernel)
    | 2, _ =>
      rw [kapE1 (n + 5) 2 (Nat.le_succ 1) h2 (litNe 3 n 5 (by decide +kernel))]
      exact termVanishMag ((n + 5)) 2 h2 _ _ _
        (raisedCount ((n + 5)) (fun k => if k = 2 then 1 else 0) (fun k => if k = 0 then 1 else 0)
          1 2 2 h2 h2 2 0 (cartDiag ((n + 5)) 2))
        (Or.inl (by decide +kernel))
    | m + 3, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 5 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 5 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h2m : 2 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapE1 (n + 5) (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hm1
      (Nat.ne_of_lt hml)]
    refine serstable.runVanishB (n + 5) m _ hml (nuOf_length (n + 5) _) ?_ 0 h0
      (Or.inl (Nat.le_trans (Nat.le_succ 1) h2m)) ?_
    · exact nuVac (n + 5) (fun k => if k = 2 then 1 else 0) (fun k => if k = 0 then 1 else 0)
        (m + 1) hm1 (by rw [if_neg (fun hc => Nat.not_succ_le_self 1
            (by rw [Nat.succ.inj hc] at h2m; exact h2m)),
          if_neg (sucNe0 m)])
    · exact nuOcc (n + 5) (fun k => if k = 2 then 1 else 0) (fun k => if k = 0 then 1 else 0)
        0 h0 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 4)) (n + 4)) = 0
      rw [kapE1T (n + 5) (n + 4) (Nat.le_add_left 1 (n + 3)) hT4 rfl]
      exact termVanishMag (n + 5) (n + 4) hT4 _ _ _
        (raisedCount (n + 5) (fun k => if k = 2 then 1 else 0) (fun k => if k = 0 then 1 else 0)
          2 (n + 4) (n + 4) hT4 hT4 2 0 (cartDiag (n + 5) (n + 4)))
        (Or.inl (by
          rw [if_neg (shiftNeLit n 4 2 (by decide +kernel)),
            if_neg (shiftNeLit n 4 0 (by decide +kernel))]
          exact (by decide +kernel)))
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))


/-- The unit sector's tail letter at `θ + (e₃ + e₄)`. -/
private theorem tailU4 (n : Nat) :
    row.thetaCount (sertables.tableB (n + 6))
      (raisedG (sertables.tableB (n + 6)) (nF (n + 6)) 1 (n + 5)) = 0 := by
  have h0 : (0 : Nat) < n + 6 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 6 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 6 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 n)
  have hT5 : n + 5 < n + 6 := Nat.lt_succ_self _
  have hl4 : 4 ≤ n + 6 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 n)
  refine termVanishTail (n + 6) (n + 4) rfl hl4 _ 0 0 0 1 0 0
    (BPair.oneValue_trans
      (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 (n + 5) 0 hT5 h0 0 0
        (cartOff (n + 6) (n + 5) 0 (fun hc => Nat.noConfusion hc)
          (fun hc => Nat.noConfusion hc) (litNe 1 n 5 (by decide +kernel))))
      (BPair.ofCounts_crossed (by decide +kernel)))
    (BPair.oneValue_trans
      (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 (n + 5) 1 hT5 h1 0 0
        (cartOff (n + 6) (n + 5) 1 (litNe 1 n 5 (by decide +kernel))
          (litNe 1 n 6 (by decide +kernel))
          (litNe 2 n 5 (by decide +kernel))))
      (BPair.ofCounts_crossed (by decide +kernel)))
    (BPair.oneValue_trans
      (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 (n + 5) 2 hT5 h2 0 0
        (cartOff (n + 6) (n + 5) 2 (litNe 2 n 5 (by decide +kernel))
          (litNe 2 n 6 (by decide +kernel))
          (litNe 3 n 5 (by decide +kernel))))
      (BPair.ofCounts_crossed (by decide +kernel)))
    (BPair.oneValue_trans
      (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 (n + 5) (n + 5) hT5 hT5 2 0
        (cartDiag (n + 6) (n + 5)))
      (BPair.ofCounts_crossed
        (by rw [if_neg (shiftNeLit n 5 3 (by decide +kernel)),
          if_neg (shiftNeLit n 5 1 (by decide +kernel))])))
    (fun F hcase q0 q1 q2 q3 => ?_) (fun F hcase q0 q1 q2 q3 => ?_)
  · match headCases (n + 6) F hcase with
    | .inr hf0 =>
      rw [hf0] at q0 q1
      have hf1 : F 1 = 2 := by rw [Nat.zero_add] at q0; exact q0
      rw [hf1] at q1
      have hf2 : F 2 = 4 := by rw [Nat.zero_add] at q1; exact oneAddCancel q1
      have hcap := famCap (n + 6) F hcase 2
      rw [hf2] at hcap
      exact absurd hcap (by decide +kernel)
    | .inl hf0 =>
      rw [hf0] at q0 q1
      have hf1 : F 1 = 0 := by rw [Nat.zero_add] at q0; exact q0
      rw [hf1] at q1 q2
      have hf2 : F 2 = 1 := by
        rw [Nat.zero_add (0 + F 2), Nat.zero_add (F 2)] at q1
        exact q1
      rw [hf2] at q2
      have hf3 : F 3 = 2 := by
        rw [Nat.zero_add (0 + F 3), Nat.zero_add (F 3)] at q2
        exact q2
      obtain ⟨ht1, ht0⟩ := tailRefuse (n + 6) (n + 4) 3 rfl
        (Nat.le_add_left 3 (n + 1)) F hcase hf3
      rw [ht0, ht1] at q3
      exact absurd q3 (by decide +kernel)
  · match headCases (n + 6) F hcase with
    | .inl hf0 =>
      rw [hf0] at q0 q1
      have hf1 : F 1 = 0 := by rw [Nat.add_zero] at q0; exact q0.symm
      rw [hf1] at q1
      exact Nat.noConfusion q1.symm
    | .inr hf0 =>
      rw [hf0] at q0 q1
      have hf1 : F 1 = 2 := by rw [Nat.add_zero] at q0; exact q0.symm
      rw [hf1] at q1
      have hf2 : F 2 = 2 := by
        rw [Nat.zero_add] at q1
        exact oneAddCancel (Nat.succ.inj q1.symm)
      obtain ⟨ht1, ht0⟩ := tailRefuse (n + 6) (n + 4) 2 rfl
        (Nat.le_add_left 2 (n + 2)) F hcase hf2
      rw [ht0, ht1] at q3
      exact absurd q3 (by decide +kernel)

/-- The unit sector's witness edge at `θ + (e₃ + e₄)`. -/
theorem edgeB_u4 (l : Nat) (hl : 6 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l)
      (serstable.memberRho [1, 1] l) (nF l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 6 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 6 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 6 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 n)
  have h3 : (3 : Nat) < n + 6 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 n)
  have hT5 : n + 5 < n + 6 := Nat.lt_succ_self _
  refine foldZeroG (sertables.tableB (n + 6)) 4 (n + 1) 1 (n + 5) (by decide +kernel)
    (by show n + 6 = 4 + (n + 1) + 1; rw [Nat.add_comm 4 (n + 1)])
    (by rw [Nat.add_comm 4 (n + 1)])
    (serstable.memberRho [1, 1] (n + 6)) (nF (n + 6)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapTh0 (n + 6) h0]
      exact termNegTwoBelow (n + 6) 0 h2 _
        (BPair.oneValue_trans
          (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 0 1 h0 h1 0 1
            (cartUp1 (n + 6) 0 (litNe 2 n 6 (by decide +kernel))))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 0 0 h0 h0 2 0 (cartDiag (n + 6) 0))
        (by decide +kernel)
    | 1, _ =>
      rw [kapTh1 (n + 6) h1]
      exact termVanishMag (n + 6) 1 h1 _ _ _
        (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          2 1 1 h1 h1 2 0 (cartDiag (n + 6) 1))
        (Or.inl (by decide +kernel))
    | 2, _ =>
      rw [kapTh (n + 6) 2 (Nat.le_refl 2) h2]
      exact termNegTwoBelow (n + 6) 0 h2 _
        (BPair.oneValue_trans
          (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 2 1 h2 h1 0 1 (cartDn (n + 6) 1))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 2 0 h2 h0 0 0
          (cartOff (n + 6) 2 0 (fun hc => Nat.noConfusion hc)
            (fun hc => Nat.noConfusion hc)
            (fun hc => Nat.noConfusion (Nat.succ.inj hc))))
        (by decide +kernel)
    | 3, _ =>
      rw [kapTh (n + 6) 3 (Nat.le_succ 2) h3]
      exact termVanishMag (n + 6) 3 h3 _ _ _
        (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          1 3 3 h3 h3 2 0 (cartDiag (n + 6) 3))
        (Or.inl (by decide +kernel))
    | m + 4, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 4 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 6 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 6 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h3m : 3 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapTh (n + 6) (m + 1) (Nat.le_trans
      (show (2 : Nat) ≤ 4 by decide +kernel) hm) hm1]
    refine serstable.runVanishB (n + 6) m _ hml (nuOf_length (n + 6) _) ?_ 1 h1
      (Or.inl (Nat.le_trans (show (2 : Nat) ≤ 3 by decide +kernel) h3m)) ?_
    · exact nuVac (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
        (m + 1) hm1 (by rw [if_neg (fun hc => Nat.not_succ_le_self 2
            (by rw [Nat.succ.inj hc] at h3m; exact h3m)),
          if_neg (fun hc => Nat.not_succ_le_zero 2
            (by rw [Nat.succ.inj hc] at h3m; exact h3m))])
    · exact nuOcc (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
        1 h1 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 5)) (n + 5)) = 0
      rw [kapTh (n + 6) (n + 5) (Nat.le_add_left 2 (n + 3)) hT5]
      exact tailU4 n
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))

/-- The spinor sector's witness edge at `(e₁ + e₂) + (e₃ + e₄)`. -/
theorem edgeB_s6 (l : Nat) (hl : 6 ≤ l) :
    serstable.letterFoldVal (sertables.tableB l)
      (basedRho [1, 1] l 0) (nF l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0 : (0 : Nat) < n + 6 := Nat.succ_pos _
  have h1 : (1 : Nat) < n + 6 := Nat.succ_lt_succ (Nat.succ_pos _)
  have h2 : (2 : Nat) < n + 6 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 n)
  have h3 : (3 : Nat) < n + 6 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 n)
  have hT5 : n + 5 < n + 6 := Nat.lt_succ_self _
  have hl2 : 2 ≤ n + 6 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 n)
  have hl3 : 3 ≤ n + 6 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 n)
  refine foldZeroG (sertables.tableB (n + 6)) 4 (n + 1) 1 (n + 5) (by decide +kernel)
    (by show n + 6 = 4 + (n + 1) + 1; rw [Nat.add_comm 4 (n + 1)])
    (by rw [Nat.add_comm 4 (n + 1)])
    (basedRho [1, 1] (n + 6) 0) (nF (n + 6)) ?_ ?_ ?_
  · intro i hi
    match i, hi with
    | 0, _ =>
      rw [kapE12H (n + 6) hl2]
      exact termNegTwoBelow (n + 6) 0 h2 _
        (BPair.oneValue_trans
          (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 0 1 h0 h1 0 1
            (cartUp1 (n + 6) 0 (litNe 2 n 6 (by decide +kernel))))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 0 0 h0 h0 2 0 (cartDiag (n + 6) 0))
        (by decide +kernel)
    | 1, _ =>
      rw [kapE12A (n + 6) hl3]
      exact termVanishMag (n + 6) 1 h1 _ _ _
        (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          2 1 1 h1 h1 2 0 (cartDiag (n + 6) 1))
        (Or.inl (by decide +kernel))
    | 2, _ =>
      rw [kapE12 (n + 6) 2 (Nat.le_refl 2) h2 (litNe 3 n 6 (by decide +kernel))]
      exact termNegTwoBelow (n + 6) 0 h2 _
        (BPair.oneValue_trans
          (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 2 1 h2 h1 0 1 (cartDn (n + 6) 1))
          (BPair.ofCounts_crossed (by decide +kernel)))
        _ _
        (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0) 1 2 0 h2 h0 0 0
          (cartOff (n + 6) 2 0 (fun hc => Nat.noConfusion hc)
            (fun hc => Nat.noConfusion hc)
            (fun hc => Nat.noConfusion (Nat.succ.inj hc))))
        (by decide +kernel)
    | 3, _ =>
      rw [kapE12 (n + 6) 3 (Nat.le_succ 2) h3 (litNe 4 n 6 (by decide +kernel))]
      exact termVanishMag (n + 6) 3 h3 _ _ _
        (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          1 3 3 h3 h3 2 0 (cartDiag (n + 6) 3))
        (Or.inl (by decide +kernel))
    | m + 4, hm => exact absurd hm (fun hc => ltRefute (Nat.le_add_left 4 m) hc)
  · intro m hm hml0
    have hml : m + 2 < n + 6 := Nat.succ_lt_succ hml0
    have hm1 : m + 1 < n + 6 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hml
    have h3m : 3 ≤ m := Nat.le_of_succ_le_succ hm
    rw [kapE12 (n + 6) (m + 1) (Nat.le_trans
      (show (2 : Nat) ≤ 4 by decide +kernel) hm) hm1 (Nat.ne_of_lt hml)]
    refine serstable.runVanishB (n + 6) m _ hml (nuOf_length (n + 6) _) ?_ 1 h1
      (Or.inl (Nat.le_trans (show (2 : Nat) ≤ 3 by decide +kernel) h3m)) ?_
    · exact nuVac (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
        (m + 1) hm1 (by rw [if_neg (fun hc => Nat.not_succ_le_self 2
            (by rw [Nat.succ.inj hc] at h3m; exact h3m)),
          if_neg (fun hc => Nat.not_succ_le_zero 2
            (by rw [Nat.succ.inj hc] at h3m; exact h3m))])
    · exact nuOcc (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
        1 h1 (by decide +kernel)
  · intro x hx
    match x, hx with
    | 0, _ =>
      show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (n + 5)) (n + 5)) = 0
      rw [kapE12T (n + 6) (n + 5) (Nat.le_add_left 2 (n + 3)) hT5 rfl]
      exact termVanishMag (n + 6) (n + 5) hT5 _ _ _
        (raisedCount (n + 6) (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
          2 (n + 5) (n + 5) hT5 hT5 2 0 (cartDiag (n + 6) (n + 5)))
        (Or.inl (by
          rw [if_neg (shiftNeLit n 5 3 (by decide +kernel)),
            if_neg (shiftNeLit n 5 1 (by decide +kernel))]
          exact (by decide +kernel)))
    | r + 1, hx =>
      exact absurd hx (fun hc => Nat.not_succ_le_zero r
        (Nat.le_of_succ_le_succ hc))


/-! ### The moved contents at the trailing keys -/

/-- A key below the rank sits below the trailing pair or at one of
its two coordinates. -/
private theorem keySplit (n k : Nat) (hk : k < n + 2) :
    k < n ∨ k = n ∨ k = n + 1 := by
  match Nat.lt_or_ge k n with
  | .inl h => exact Or.inl h
  | .inr h =>
    match Nat.lt_or_ge k (n + 1) with
    | .inl h2 => exact Or.inr (Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h2) h))
    | .inr h2 =>
      exact Or.inr (Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hk) h2))

/-- A key sits two below its own double successor. -/
private theorem ltPlusTwo (a : Nat) : a < a + 2 :=
  ground.ltAddSucc a 1

/-- The representative list's θ count at a displayed family, read
through the representative. -/
private theorem thetaOnePnorm (l : Nat) (F : Nat → Nat) (z : List BPair)
    (hzl : z.length = l)
    (hmem : (List.range l).map F ∈ sertables.foldsB l)
    (hent : ∀ k, k < l → (ground.getAt BPair.unit (poly.pnorm z) k).oneValue
      (BPair.ofCounts (2 * F k) (serstable.nbB l F k)))
    (k0 : Nat) (hk0 : k0 < l)
    (hne : ¬ (ground.getAt BPair.unit (poly.pnorm z) k0).oneValue
      BPair.unit) :
    row.thetaCount (sertables.tableB l) (poly.pnorm z) = 1 := by
  refine thetaOneNorm l F z hzl hmem (fun k hk => ?_) k0 hk0 (fun hc => hne ?_)
  · have hR := pnormEntry z k (by rw [hzl]; exact hk)
    have h := hent k hk
    rw [hR] at h
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.norm_oneValue
        (ground.getAt BPair.unit z k))) h
  · rw [pnormEntry z k0 (by rw [hzl]; exact hk0)]
    exact BPair.oneValue_trans (BPair.norm_oneValue _) hc

/-- The representative list's θ count at a family's balance
partner. -/
private theorem thetaOnePnormNeg (l : Nat) (F : Nat → Nat) (z : List BPair)
    (hzl : z.length = l)
    (hmem : (List.range l).map F ∈ sertables.foldsB l)
    (hent : ∀ k, k < l → (ground.getAt BPair.unit (poly.pnorm z) k).oneValue
      (BPair.ofCounts (serstable.nbB l F k) (2 * F k)))
    (k0 : Nat) (hk0 : k0 < l)
    (hne : ¬ (ground.getAt BPair.unit (poly.pnorm z) k0).oneValue
      BPair.unit) :
    row.thetaCount (sertables.tableB l) (poly.pnorm z) = 1 := by
  refine thetaOneNormNeg l F z hzl hmem (fun k hk => ?_) k0 hk0
    (fun hc => hne ?_)
  · have hR := pnormEntry z k (by rw [hzl]; exact hk)
    have h := hent k hk
    rw [hR] at h
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.norm_oneValue
        (ground.getAt BPair.unit z k))) h
  · rw [pnormEntry z k0 (by rw [hzl]; exact hk0)]
    exact BPair.oneValue_trans (BPair.norm_oneValue _) hc

/-- The stray's tail letter at the positive limb: the raised
content sits at the hit family's column, so its term reads one. -/
private theorem strayTailPos (l q c : Nat) (hq : q + 2 = l)
    (u v F : Nat → Nat)
    (hmem : (List.range l).map F ∈ sertables.foldsB l)
    (hlow : ∀ k, k < q → u k + serstable.nbB l F k = 2 * F k + v k)
    (hmid : u q + serstable.nbB l F q = 2 * F q + (v q + c))
    (htop : u (q + 1) + c * 2 + serstable.nbB l F (q + 1)
      = 2 * F (q + 1) + v (q + 1))
    (hocc : ¬ u (q + 1) + c * 2 = v (q + 1)) :
    row.thetaCount (sertables.tableB l)
      (raisedG (sertables.tableB l) (nuOf l (fun j => BPair.ofCounts (u j) (v j))) c (q + 1))
      = 1 := by
  have hql : q < l := by
    rw [← hq]
    exact ltPlusTwo q
  have hq1l : q + 1 < l := by
    rw [← hq]
    exact Nat.lt_succ_self (q + 1)
  have hzl : (elim.vecAdd (nuOf l (fun j => BPair.ofCounts (u j) (v j)))
      (elim.vecScale (BPair.ofNat c)
        (ground.getAt [] (sertables.tableB l).cartan (q + 1)))).length = l := by
    refine elim.length_vecAdd _ _ l (nuOf_length l _) ?_
    rw [elim.length_vecScale, serstable.cartB_eq l]
    exact ground.matOf_rowLength [] l l (fun i j => serstable.cartB l i j)
      (q + 1) hq1l
  refine thetaOnePnorm l F _ hzl hmem (fun k hk => ?_) (q + 1) hq1l ?_
  · match keySplit q k (by rw [hq]; exact hk) with
    | .inl hlt =>
      refine BPair.oneValue_trans
        (raisedCount l u v c (q + 1) k hq1l hk 0 0
          (cartOff l (q + 1) k
            (Nat.ne_of_lt (Nat.lt_trans hlt (Nat.lt_succ_self q)))
            (Nat.ne_of_lt (Nat.lt_trans hlt (ltPlusTwo q)))
            (Nat.ne_of_lt (Nat.succ_lt_succ hlt))))
        (BPair.ofCounts_crossed ?_)
      rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
      exact hlow k hlt
    | .inr (.inl hkq) =>
      subst hkq
      refine BPair.oneValue_trans
        (raisedCount l u v c (k + 1) k hq1l hql 0 1
          (cartDn l k)) (BPair.ofCounts_crossed ?_)
      rw [Nat.mul_zero, Nat.mul_one, Nat.add_zero]
      exact hmid
    | .inr (.inr hkq) =>
      subst hkq
      refine BPair.oneValue_trans
        (raisedCount l u v c (q + 1) (q + 1) hq1l hq1l 2 0
          (cartDiag l (q + 1))) (BPair.ofCounts_crossed ?_)
      rw [Nat.mul_zero, Nat.add_zero]
      exact htop
  · refine fun hc => hocc (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm ?_) hc))
    exact raisedCount l u v c (q + 1) (q + 1) hq1l hq1l 2 0
      (cartDiag l (q + 1))

/-- The stray's tail letter at the negative limb. -/
private theorem strayTailNeg (l q c : Nat) (hq : q + 2 = l)
    (u v F : Nat → Nat)
    (hmem : (List.range l).map F ∈ sertables.foldsB l)
    (hlow : ∀ k, k < q → u k + 2 * F k = serstable.nbB l F k + v k)
    (hmid : u q + 2 * F q = serstable.nbB l F q + (v q + c))
    (htop : u (q + 1) + c * 2 + 2 * F (q + 1)
      = serstable.nbB l F (q + 1) + v (q + 1))
    (hocc : ¬ u (q + 1) + c * 2 = v (q + 1)) :
    row.thetaCount (sertables.tableB l)
      (raisedG (sertables.tableB l) (nuOf l (fun j => BPair.ofCounts (u j) (v j))) c (q + 1))
      = 1 := by
  have hql : q < l := by
    rw [← hq]
    exact ltPlusTwo q
  have hq1l : q + 1 < l := by
    rw [← hq]
    exact Nat.lt_succ_self (q + 1)
  have hzl : (elim.vecAdd (nuOf l (fun j => BPair.ofCounts (u j) (v j)))
      (elim.vecScale (BPair.ofNat c)
        (ground.getAt [] (sertables.tableB l).cartan (q + 1)))).length = l := by
    refine elim.length_vecAdd _ _ l (nuOf_length l _) ?_
    rw [elim.length_vecScale, serstable.cartB_eq l]
    exact ground.matOf_rowLength [] l l (fun i j => serstable.cartB l i j)
      (q + 1) hq1l
  refine thetaOnePnormNeg l F _ hzl hmem (fun k hk => ?_) (q + 1) hq1l ?_
  · match keySplit q k (by rw [hq]; exact hk) with
    | .inl hlt =>
      refine BPair.oneValue_trans
        (raisedCount l u v c (q + 1) k hq1l hk 0 0
          (cartOff l (q + 1) k
            (Nat.ne_of_lt (Nat.lt_trans hlt (Nat.lt_succ_self q)))
            (Nat.ne_of_lt (Nat.lt_trans hlt (ltPlusTwo q)))
            (Nat.ne_of_lt (Nat.succ_lt_succ hlt))))
        (BPair.ofCounts_crossed ?_)
      rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
      exact hlow k hlt
    | .inr (.inl hkq) =>
      subst hkq
      refine BPair.oneValue_trans
        (raisedCount l u v c (k + 1) k hq1l hql 0 1
          (cartDn l k)) (BPair.ofCounts_crossed ?_)
      rw [Nat.mul_zero, Nat.mul_one, Nat.add_zero]
      exact hmid
    | .inr (.inr hkq) =>
      subst hkq
      refine BPair.oneValue_trans
        (raisedCount l u v c (q + 1) (q + 1) hq1l hq1l 2 0
          (cartDiag l (q + 1))) (BPair.ofCounts_crossed ?_)
      rw [Nat.mul_zero, Nat.add_zero]
      exact htop
  · refine fun hc => hocc (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm ?_) hc))
    exact raisedCount l u v c (q + 1) (q + 1) hq1l hq1l 2 0
      (cartDiag l (q + 1))


/-- The stray at `θ + e₁`: the tail letter's raised content is the
sum family at `(0, ℓ − 1)`. -/
private theorem hitNB (p : Nat) :
    row.thetaCount (sertables.tableB (p + 3))
      (raisedG (sertables.tableB (p + 3)) (nB (p + 3)) 1 (p + 2)) = 1 := by
  have h1l : (1 : Nat) < p + 3 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 p)
  have hSm : ∀ j, j ≤ p + 1 → serstable.fSumB (p + 3) 0 (p + 2) j = 1 :=
    fun j hj => serstable.fSumB_mid (p + 3) 0 (p + 2) j (Nat.zero_le j)
      (Nat.succ_le_succ hj)
  have hSt : serstable.fSumB (p + 3) 0 (p + 2) (p + 2) = 2 :=
    serstable.fSumB_hi (p + 3) 0 (p + 2) (p + 2) (Nat.le_refl _)
      (Nat.lt_succ_self _)
  refine strayTailPos (p + 3) (p + 1) 1 rfl
    (fun i => if i = 0 then 1 else 0) (fun _ => 0)
    (serstable.fSumB (p + 3) 0 (p + 2))
    (memSum (p + 3) 0 (p + 2) (Nat.succ_pos _) (Nat.lt_succ_self _))
    (fun k hk => ?_) ?_ ?_
    (by rw [if_neg (sucNe0 (p + 1))]
        exact (by decide +kernel))
  · cases k with
    | zero =>
      rw [if_pos rfl, nbHead (p + 3) _ h1l,
        hSm 1 (Nat.succ_le_succ (Nat.zero_le p)), hSm 0 (Nat.zero_le _)]
    | succ r =>
      rw [if_neg (sucNe0 r),
        nbMid (p + 3) _ r (Nat.ne_of_lt (Nat.lt_of_le_of_lt
          (Nat.succ_le_of_lt hk) (ltPlusTwo (p + 1)))),
        hSm r (Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self r) hk)),
        hSm (r + 2) (Nat.succ_le_of_lt hk), hSm (r + 1) (Nat.le_of_lt hk)]
  · rw [if_neg (sucNe0 p),
      nbMid (p + 3) _ p (Nat.ne_of_lt (Nat.lt_succ_self (p + 2))),
      hSm p (Nat.le_succ p), hSt, hSm (p + 1) (Nat.le_refl _)]
  · rw [if_neg (sucNe0 (p + 1)), nbTop (p + 3) _ (p + 1) rfl,
      hSm (p + 1) (Nat.le_refl _), hSt]

/-- The stray at `θ + (−e₂)`: the tail letter's raised content is
the difference family at `(1, ℓ − 1)`, negated. -/
private theorem hitNG (p : Nat) :
    row.thetaCount (sertables.tableB (p + 3))
      (raisedG (sertables.tableB (p + 3)) (nG (p + 3)) 1 (p + 2)) = 1 := by
  have h1p2 : (1 : Nat) < p + 2 := Nat.succ_lt_succ (Nat.succ_pos p)
  have hp23 : p + 2 < p + 3 := Nat.lt_succ_self _
  have hLo : serstable.fDiff 1 (p + 2) 0 = 0 :=
    serstable.fDiff_lo 1 (p + 2) 0 (by decide +kernel)
  have hIn : ∀ j, 1 ≤ j → j < p + 2 → serstable.fDiff 1 (p + 2) j = 1 :=
    fun j h1 h2 => serstable.fDiff_in 1 (p + 2) j h1 h2
  have hHi : serstable.fDiff 1 (p + 2) (p + 2) = 0 :=
    serstable.fDiff_hi 1 (p + 2) (p + 2) (Nat.lt_irrefl (p + 2))
  refine strayTailNeg (p + 3) (p + 1) 1 rfl
    (fun i => if i = 0 then 1 else 0) (fun i => if i = 1 then 1 else 0)
    (serstable.fDiff 1 (p + 2))
    (memDiff (p + 3) 1 (p + 2) h1p2 hp23) (fun k hk => ?_) ?_ ?_
    (by rw [if_neg (show ¬ p + 1 + 1 = 0 from fun hc => Nat.noConfusion hc),
          if_neg (show ¬ p + 1 + 1 = 1 from fun hc =>
            Nat.noConfusion (Nat.succ.inj hc))]
        exact (by decide +kernel))
  · match k, hk with
    | 0, _ =>
      rw [if_pos rfl, if_neg (by decide +kernel : ¬ (0 : Nat) = 1), hLo,
        nbHead (p + 3) _ (Nat.lt_trans h1p2 hp23),
        hIn 1 (Nat.le_refl 1) h1p2]
    | 1, hk =>
      rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 0), if_pos rfl,
        hIn 1 (Nat.le_refl 1) h1p2,
        nbMid (p + 3) _ 0 (show ¬ 2 = p + 3 from fun hc =>
          Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
        hLo, hIn 2 (Nat.le_succ 1) (Nat.succ_lt_succ hk)]
    | t + 2, hk =>
      rw [if_neg (show ¬ t + 2 = 0 from fun hc => Nat.noConfusion hc),
        if_neg (show ¬ t + 2 = 1 from fun hc =>
          Nat.noConfusion (Nat.succ.inj hc)),
        hIn (t + 2) (Nat.succ_le_succ (Nat.zero_le (t + 1)))
          (Nat.lt_trans hk (Nat.lt_succ_self (p + 1))),
        nbMid (p + 3) _ (t + 1) (Nat.ne_of_lt (Nat.lt_of_le_of_lt
          (Nat.succ_le_of_lt hk) (ltPlusTwo (p + 1)))),
        hIn (t + 1) (Nat.succ_le_succ (Nat.zero_le t))
          (Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self (t + 1)) hk)
            (Nat.lt_succ_self (p + 1))),
        hIn (t + 3) (Nat.succ_le_succ (Nat.zero_le (t + 2)))
          (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk)
            (Nat.lt_succ_self (p + 1)))]
  · rw [if_neg (show ¬ p + 1 = 0 from fun hc => Nat.noConfusion hc),
      hIn (p + 1) (Nat.succ_le_succ (Nat.zero_le p)) (Nat.lt_succ_self (p + 1)),
      nbMid (p + 3) _ p (Nat.ne_of_lt (Nat.lt_succ_self (p + 2))), hHi]
    cases p with
    | zero => rw [if_pos rfl, hLo]
    | succ w =>
      rw [if_neg (show ¬ w + 1 + 1 = 1 from fun hc =>
          Nat.noConfusion (Nat.succ.inj hc)),
        hIn (w + 1) (Nat.succ_le_succ (Nat.zero_le w))
          (Nat.lt_trans (Nat.lt_succ_self (w + 1)) (Nat.lt_succ_self (w + 2)))]
  · rw [if_neg (show ¬ p + 1 + 1 = 0 from fun hc => Nat.noConfusion hc),
      if_neg (show ¬ p + 1 + 1 = 1 from fun hc =>
        Nat.noConfusion (Nat.succ.inj hc)), hHi,
      nbTop (p + 3) _ (p + 1) rfl,
      hIn (p + 1) (Nat.succ_le_succ (Nat.zero_le p)) (Nat.lt_succ_self (p + 1))]

/-- The stray at `θ + e₃`: the tail letter's raised content is the
sum family at `(2, ℓ − 1)`. -/
private theorem hitNH (p : Nat) :
    row.thetaCount (sertables.tableB (p + 4))
      (raisedG (sertables.tableB (p + 4)) (nH (p + 4)) 1 (p + 3)) = 1 := by
  have h1l : (1 : Nat) < p + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 p)
  have h2p3 : (2 : Nat) < p + 3 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 p)
  have hp34 : p + 3 < p + 4 := Nat.lt_succ_self _
  have hSlo : ∀ j, j < 2 → serstable.fSumB (p + 4) 2 (p + 3) j = 0 :=
    fun j hj => serstable.fSumB_lo (p + 4) 2 (p + 3) j
      (fun hc => Nat.not_succ_le_self j
        (Nat.le_trans (Nat.succ_le_of_lt hj) hc))
      (fun hc => Nat.not_succ_le_self j (Nat.le_trans
        (Nat.succ_le_of_lt (Nat.lt_trans hj h2p3)) hc))
  have hSm : ∀ j, 2 ≤ j → j ≤ p + 2 →
      serstable.fSumB (p + 4) 2 (p + 3) j = 1 :=
    fun j h1 h2 => serstable.fSumB_mid (p + 4) 2 (p + 3) j h1
      (Nat.succ_le_succ h2)
  have hSt : serstable.fSumB (p + 4) 2 (p + 3) (p + 3) = 2 :=
    serstable.fSumB_hi (p + 4) 2 (p + 3) (p + 3) (Nat.le_refl _)
      (Nat.lt_succ_self _)
  refine strayTailPos (p + 4) (p + 2) 1 rfl
    (fun i => if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0)
    (serstable.fSumB (p + 4) 2 (p + 3))
    (memSum (p + 4) 2 (p + 3) h2p3 hp34) (fun k hk => ?_) ?_ ?_
    (by rw [if_neg (show ¬ p + 2 + 1 = 2 from fun hc =>
            Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
          if_neg (show ¬ p + 2 + 1 = 1 from fun hc =>
            Nat.noConfusion (Nat.succ.inj hc))]
        exact (by decide +kernel))
  · match k, hk with
    | 0, _ =>
      rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 2),
        if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
        hSlo 0 (by decide +kernel), nbHead (p + 4) _ h1l,
        hSlo 1 (by decide +kernel)]
    | 1, hk =>
      rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 2), if_pos rfl,
        hSlo 1 (by decide +kernel),
        nbMid (p + 4) _ 0 (show ¬ 2 = p + 4 from fun hc =>
          Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
        hSlo 0 (by decide +kernel),
        hSm 2 (Nat.le_refl 2) (Nat.le_add_left 2 p)]
    | 2, hk =>
      rw [if_pos rfl, if_neg (by decide +kernel : ¬ (2 : Nat) = 1),
        hSm 2 (Nat.le_refl 2) (Nat.le_add_left 2 p),
        nbMid (p + 4) _ 1 (show ¬ 3 = p + 4 from fun hc =>
          Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))),
        hSlo 1 (by decide +kernel),
        hSm 3 (Nat.le_succ 2) (Nat.succ_le_of_lt hk)]
    | w + 3, hk =>
      rw [if_neg (show ¬ w + 3 = 2 from fun hc =>
          Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
        if_neg (show ¬ w + 3 = 1 from fun hc =>
          Nat.noConfusion (Nat.succ.inj hc)),
        hSm (w + 3) (Nat.le_add_left 2 (w + 1)) (Nat.le_of_lt hk),
        nbMid (p + 4) _ (w + 2) (Nat.ne_of_lt (Nat.lt_trans
          (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk)
            (Nat.lt_succ_self (p + 2))) (Nat.lt_succ_self (p + 3)))),
        hSm (w + 2) (Nat.le_add_left 2 w)
          (Nat.le_of_lt (Nat.lt_trans (Nat.lt_succ_self (w + 2)) hk)),
        hSm (w + 4) (Nat.le_add_left 2 (w + 2)) (Nat.succ_le_of_lt hk)]
  · rw [hSm (p + 2) (Nat.le_add_left 2 p) (Nat.le_refl _),
      if_neg (show ¬ p + 2 = 1 from fun hc =>
        Nat.noConfusion (Nat.succ.inj hc)),
      nbMid (p + 4) _ (p + 1) (Nat.ne_of_lt (Nat.lt_succ_self (p + 3))), hSt]
    cases p with
    | zero => rw [if_pos rfl, hSlo 1 (by decide +kernel)]
    | succ w =>
      rw [if_neg (show ¬ w + 1 + 2 = 2 from fun hc =>
          Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
        hSm (w + 1 + 1) (Nat.le_add_left 2 w) (Nat.le_succ (w + 1 + 1))]
  · rw [if_neg (show ¬ p + 2 + 1 = 2 from fun hc =>
        Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
      if_neg (show ¬ p + 2 + 1 = 1 from fun hc =>
        Nat.noConfusion (Nat.succ.inj hc)), hSt,
      nbTop (p + 4) _ (p + 2) rfl,
      hSm (p + 2) (Nat.le_add_left 2 p) (Nat.le_refl _)]

/-- The unit sector's stray at `θ + e₁`: the letter fold reads the occupied count, the two graded counts tying. -/
theorem strayB_c1 (l : Nat) (hl : 3 ≤ l) :
    1 ≤ serstable.letterFoldVal (sertables.tableB l) (serstable.memberRho [1, 1] l) (nB l) := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  refine foldOneAtG (sertables.tableB (n + 3)) (n + 2) (Nat.lt_succ_self _)
    (serstable.memberRho [1, 1] (n + 3)) (nB (n + 3)) ?_
  rw [kapTh (n + 3) (n + 2) (Nat.le_add_left 2 n) (Nat.lt_succ_self _)]
  exact hitNB n

/-- The unit sector's stray at `θ + (−e₂)`. -/
theorem strayB_c2 (l : Nat) (hl : 3 ≤ l) :
    1 ≤ serstable.letterFoldVal (sertables.tableB l) (serstable.memberRho [1, 1] l) (nG l) := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  refine foldOneAtG (sertables.tableB (n + 3)) (n + 2) (Nat.lt_succ_self _)
    (serstable.memberRho [1, 1] (n + 3)) (nG (n + 3)) ?_
  rw [kapTh (n + 3) (n + 2) (Nat.le_add_left 2 n) (Nat.lt_succ_self _)]
  exact hitNG n

/-- The unit sector's stray at `θ + e₃`. -/
theorem strayB_c3 (l : Nat) (hl : 4 ≤ l) :
    1 ≤ serstable.letterFoldVal (sertables.tableB l) (serstable.memberRho [1, 1] l) (nH l) := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  refine foldOneAtG (sertables.tableB (n + 4)) (n + 3) (Nat.lt_succ_self _)
    (serstable.memberRho [1, 1] (n + 4)) (nH (n + 4)) ?_
  rw [kapTh (n + 4) (n + 3) (Nat.le_add_left 2 (n + 1)) (Nat.lt_succ_self _)]
  exact hitNH n

/-- The difference family at an ordered pair joins the `C` positive
list. -/
private theorem memDiffC (l a b : Nat) (hab : a < b) (hbl : b < l) :
    (List.range l).map (serstable.fDiff a b) ∈ sertables.foldsC l :=
  ground.mem_append_left _ (ground.mem_append_left _
    (show sertables.diffFold l a b
        ∈ (places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2) from
      ground.mem_map_to (fun p => sertables.diffFold l p.1 p.2)
        (ground.mem_of_countOf_pos (a, b) (places.pairsOf l)
          (places.pairs_complete l hab hbl))))

/-- The `C` sum family at an ordered pair joins the positive
list. -/
private theorem memSumC (d a b : Nat) (hab : a < b) (hbl : b < d + 1) :
    (List.range (d + 1)).map (serstable.fSumC d a b)
      ∈ sertables.foldsC (d + 1) := by
  rw [← serstable.fSumC_eq d a b]
  exact ground.mem_append_left _ (ground.mem_append_right _
    (ground.mem_map_to (fun p => sertables.sumFoldC (d + 1) p.1 p.2)
      (ground.mem_of_countOf_pos (a, b) (places.pairsOf (d + 1))
        (places.pairs_complete (d + 1) hab hbl))))

/-- The `C` long family at a coordinate joins the positive list. -/
private theorem memLongC (d a : Nat) (hal : a < d + 1) :
    (List.range (d + 1)).map (serstable.fLong d a)
      ∈ sertables.foldsC (d + 1) := by
  rw [← serstable.fLong_eq d a]
  exact ground.mem_append_right _
    (show sertables.longFold (d + 1) a
        ∈ (List.range (d + 1)).map (sertables.longFold (d + 1)) from
      ground.mem_map_to (sertables.longFold (d + 1))
        (ground.memRange hal))

/-! ### The `C` exhibition engine -/

/-- A moved content whose count reads are a `C` family's column
reads, key for key, is that family's coroot vector: its θ count is
one (`prop:row`'s θ list at `con:sertables`' positive folds). -/
private theorem thetaOneNormC (l : Nat) (F : Nat → Nat) (z : List BPair)
    (hzl : z.length = l)
    (hmem : (List.range l).map F ∈ sertables.foldsC l)
    (hent : ∀ k, k < l → (ground.getAt BPair.unit z k).oneValue
      (BPair.ofCounts (2 * F k) (serstable.nbC l F k)))
    (k0 : Nat) (hk0 : k0 < l)
    (hne : ¬ (ground.getAt BPair.unit z k0).oneValue BPair.unit) :
    row.thetaCount (sertables.tableC l) (poly.pnorm z) = 1 := by
  obtain ⟨j, hj, hje⟩ := ground.getAt_of_mem ([] : List Nat) hmem
  refine thetaOneNormG (sertables.tableC l) z hzl j hj
    (fun k hk => ?_) k0 hk0 hne
  refine BPair.oneValue_trans (BPair.oneValue_trans (hent k hk)
    (BPair.oneValue_symm (serstable.posCorootV_entryC l j k F hk hje))) ?_
  rw [pnormEntry (sertables.posCorootV (sertables.tableC l) j) k
    (by rw [sertables.posCorootV_length]; exact hk)]
  exact BPair.norm_oneValue _

/-- A moved content at a displayed `C` family's balance partner:
its θ count is one at the positive list's negated limb. -/
private theorem thetaOneNormNegC (l : Nat) (F : Nat → Nat) (z : List BPair)
    (hzl : z.length = l)
    (hmem : (List.range l).map F ∈ sertables.foldsC l)
    (hent : ∀ k, k < l → (ground.getAt BPair.unit z k).oneValue
      (BPair.ofCounts (serstable.nbC l F k) (2 * F k)))
    (k0 : Nat) (hk0 : k0 < l)
    (hne : ¬ (ground.getAt BPair.unit z k0).oneValue BPair.unit) :
    row.thetaCount (sertables.tableC l) (poly.pnorm z) = 1 := by
  obtain ⟨j, hj, hje⟩ := ground.getAt_of_mem ([] : List Nat) hmem
  refine thetaOneNormNegG (sertables.tableC l) z hzl j hj
    (fun k hk => ?_) k0 hk0 hne
  have hS : ((ground.getAt BPair.unit
      (poly.pnorm (sertables.posCorootV (sertables.tableC l) j))
        k).swap).oneValue
      (BPair.ofCounts (serstable.nbC l F k) (2 * F k)) := by
    rw [← ground.BPair.ofCounts_swap (2 * F k) (serstable.nbC l F k)]
    exact ground.swap_congr (serstable.posCorootV_entryC l j k F hk hje)
  refine BPair.oneValue_trans (BPair.oneValue_trans (hent k hk)
    (BPair.oneValue_symm hS)) ?_
  rw [pnormEntry (sertables.posCorootV (sertables.tableC l) j) k
    (by rw [sertables.posCorootV_length]; exact hk)]
  exact ground.swap_congr (BPair.norm_oneValue _)

/-! ### The `C` neighbour fold's four reads and the builder
wrappers -/

/-- The `C` neighbour fold at the leading key inside the rank. -/
private theorem nbHeadC (l : Nat) (F : Nat → Nat) (h1 : 1 < l)
    (h2 : ¬ 2 = l) : serstable.nbC l F 0 = F 1 := by
  rw [serstable.nbC_zero,
    if_neg (fun hb => h2 (ground.beqEqOf hb)), if_pos h1]

/-- The `C` neighbour fold away from the last two keys: the two
neighbours' sum. -/
private theorem nbMidC (l : Nat) (F : Nat → Nat) (m : Nat)
    (h2 : ¬ m + 2 = l) (h3 : ¬ m + 3 = l) :
    serstable.nbC l F (m + 1) = F m + F (m + 2) := by
  rw [serstable.nbC_succ, if_neg (fun hb => h2 (ground.beqEqOf hb)),
    if_neg (fun hb => h3 (ground.beqEqOf hb))]

/-- The `C` neighbour fold one key below the last: the lower
neighbour beside the doubled upper one. -/
private theorem nbSubC (l : Nat) (F : Nat → Nat) (m : Nat)
    (h2 : ¬ m + 2 = l) (h3 : m + 3 = l) :
    serstable.nbC l F (m + 1) = F m + 2 * F (m + 2) := by
  rw [serstable.nbC_succ, if_neg (fun hb => h2 (ground.beqEqOf hb)),
    if_pos (ground.eqBeqOf h3)]

/-- The `C` neighbour fold at the last key: the lower neighbour
alone, the last coroot undoubled. -/
private theorem nbTopC (l : Nat) (F : Nat → Nat) (m : Nat)
    (h : m + 2 = l) : serstable.nbC l F (m + 1) = F m := by
  rw [serstable.nbC_succ, if_pos (ground.eqBeqOf h)]

/-- A moved content spelled at its count reads exhibits the
displayed `C` family: its θ count is one. -/
private theorem famOnePosC (l : Nat) (F u v : Nat → Nat)
    (hmem : (List.range l).map F ∈ sertables.foldsC l)
    (hcol : ∀ k, k < l → u k + serstable.nbC l F k = 2 * F k + v k)
    (k0 : Nat) (hk0 : k0 < l) (hne : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableC l)
      (nuOf l (fun i => BPair.ofCounts (u i) (v i))) = 1 :=
  thetaOneNormC l F ((List.range l).map (fun i => BPair.ofCounts (u i) (v i)))
    (ground.length_mapRange _ l) hmem
    (fun k hk => by
      rw [ground.getAt_map_range BPair.unit _ l k, if_pos hk]
      exact BPair.ofCounts_crossed (hcol k hk))
    k0 hk0
    (by
      rw [ground.getAt_map_range BPair.unit _ l k0, if_pos hk0]
      exact fun hc => hne (BPair.ofCounts_unit.mp hc))

/-- A moved content at a displayed `C` family's balance partner. -/
private theorem famOneNegC (l : Nat) (F u v : Nat → Nat)
    (hmem : (List.range l).map F ∈ sertables.foldsC l)
    (hcol : ∀ k, k < l → u k + 2 * F k = serstable.nbC l F k + v k)
    (k0 : Nat) (hk0 : k0 < l) (hne : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableC l)
      (nuOf l (fun i => BPair.ofCounts (u i) (v i))) = 1 :=
  thetaOneNormNegC l F
    ((List.range l).map (fun i => BPair.ofCounts (u i) (v i)))
    (ground.length_mapRange _ l) hmem
    (fun k hk => by
      rw [ground.getAt_map_range BPair.unit _ l k, if_pos hk]
      exact BPair.ofCounts_crossed (hcol k hk))
    k0 hk0
    (by
      rw [ground.getAt_map_range BPair.unit _ l k0, if_pos hk0]
      exact fun hc => hne (BPair.ofCounts_unit.mp hc))

/-! ### The `C` moved contents at the leading keys -/

/-- A thrice-shifted key sits off the two read. -/
private theorem sucNe2 (m : Nat) : ¬ m + 3 = 2 :=
  fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))

/-- A four-shifted key sits off the three read. -/
private theorem sucNe3 (m : Nat) : ¬ m + 4 = 3 :=
  fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))

/-- The moved content `e₁ + e₂`, the `C` sum family's leading
pair. -/
def cA (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 1 then 1 else 0) 0)

/-- `e₁ + e₂` is the `C` sum family at the leading pair. -/
theorem cA_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableC l) (cA l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h1l : (1 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  have hbd : (1 : Nat) ≤ n + 3 := Nat.le_add_left 1 (n + 2)
  have h1d : (1 : Nat) < n + 3 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 n)
  refine famOnePosC (n + 4) (serstable.fSumC (n + 3) 0 1)
    (fun k => if k = 1 then 1 else 0) (fun _ => 0)
    (memSumC (n + 3) 0 1 (Nat.lt_succ_self 0)
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)))
    (fun k hk => ?_) 1 h1l (by decide +kernel)
  match k, hk with
  | 0, _ =>
    show (if (0 : Nat) = 1 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 0 1) 0
      = 2 * serstable.fSumC (n + 3) 0 1 0 + 0
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
      nbHeadC (n + 4) _ h1l (litNe 2 n 4 (by decide +kernel)),
      serstable.fSumC_two (n + 3) 0 1 1 (Nat.le_refl 1) h1d,
      serstable.fSumC_mid (n + 3) 0 1 0 (Nat.le_refl 0)
        (Nat.lt_succ_self 0) hbd]
  | 1, _ =>
    show (if (1 : Nat) = 1 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 0 1) (0 + 1)
      = 2 * serstable.fSumC (n + 3) 0 1 1 + 0
    rw [if_pos rfl,
      nbMidC (n + 4) _ 0 (litNe 2 n 4 (by decide +kernel))
        (litNe 3 n 4 (by decide +kernel)),
      serstable.fSumC_mid (n + 3) 0 1 0 (Nat.le_refl 0)
        (Nat.lt_succ_self 0) hbd,
      serstable.fSumC_two (n + 3) 0 1 2 (by decide +kernel)
        (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 n)),
      serstable.fSumC_two (n + 3) 0 1 1 (Nat.le_refl 1) h1d]
  | m + 2, hm =>
    show (if m + 2 = 1 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 0 1) (m + 1 + 1)
      = 2 * serstable.fSumC (n + 3) 0 1 (m + 2) + 0
    rw [if_neg (sucNe1 m)]
    by_cases ht : m + 3 = n + 4
    · have hmd : n + 3 = m + 2 := (Nat.succ.inj ht).symm
      rw [nbTopC (n + 4) _ (m + 1) ht,
        serstable.fSumC_end (n + 3) 0 1 (m + 2) hbd hmd,
        serstable.fSumC_two (n + 3) 0 1 (m + 1)
          (Nat.le_add_left 1 m) (by rw [hmd]; exact Nat.lt_succ_self _)]
    · by_cases hs : m + 4 = n + 4
      · have hmd : n + 3 = m + 3 := (Nat.succ.inj hs).symm
        rw [nbSubC (n + 4) _ (m + 1) ht hs,
          serstable.fSumC_end (n + 3) 0 1 (m + 3) hbd hmd,
          serstable.fSumC_two (n + 3) 0 1 (m + 1) (Nat.le_add_left 1 m)
            (by rw [hmd]; exact ltPlusTwo _),
          serstable.fSumC_two (n + 3) 0 1 (m + 2) (Nat.le_add_left 1 (m + 1))
            (by rw [hmd]; exact Nat.lt_succ_self _)]
      · have hm3 : m + 3 < n + 4 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm) ht
        have hm4 : m + 4 < n + 4 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm3) hs
        have h3d : m + 3 < n + 3 := Nat.lt_of_succ_lt_succ hm4
        have h2d : m + 2 < n + 3 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 2)) h3d
        have h1dm : m + 1 < n + 3 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 1)) h2d
        rw [nbMidC (n + 4) _ (m + 1) ht hs,
          serstable.fSumC_two (n + 3) 0 1 (m + 1)
            (Nat.le_add_left 1 m) h1dm,
          serstable.fSumC_two (n + 3) 0 1 (m + 2) (Nat.le_add_left 1 (m + 1)) h2d,
          serstable.fSumC_two (n + 3) 0 1 (m + 3) (Nat.le_add_left 1 (m + 2)) h3d]

/-- The moved content `2e₂`, the `C` long family's head dipole. -/
def cB (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 1 then 2 else 0)
    (if i = 0 then 2 else 0))

/-- `2e₂` is the `C` long family at the second coordinate. -/
theorem cB_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableC l) (cB l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0l : (0 : Nat) < n + 4 := Nat.succ_pos _
  have had : (1 : Nat) ≤ n + 3 := Nat.le_add_left 1 (n + 2)
  have h1d : (1 : Nat) < n + 3 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 n)
  have h2d : (2 : Nat) < n + 3 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 n)
  refine famOnePosC (n + 4) (serstable.fLong (n + 3) 1)
    (fun k => if k = 1 then 2 else 0) (fun k => if k = 0 then 2 else 0)
    (memLongC (n + 3) 1
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)))
    (fun k hk => ?_) 0 h0l (by decide +kernel)
  match k, hk with
  | 0, _ =>
    show (if (0 : Nat) = 1 then 2 else 0)
        + serstable.nbC (n + 4) (serstable.fLong (n + 3) 1) 0
      = 2 * serstable.fLong (n + 3) 1 0 + (if (0 : Nat) = 0 then 2 else 0)
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 1), if_pos rfl,
      nbHeadC (n + 4) _ (Nat.lt_of_lt_of_le (by decide +kernel)
        (Nat.le_add_left 4 n)) (litNe 2 n 4 (by decide +kernel)),
      serstable.fLong_two (n + 3) 1 1 (Nat.le_refl 1) h1d,
      serstable.fLong_lo (n + 3) 1 0 (Nat.lt_succ_self 0) had]
  | 1, _ =>
    show (if (1 : Nat) = 1 then 2 else 0)
        + serstable.nbC (n + 4) (serstable.fLong (n + 3) 1) (0 + 1)
      = 2 * serstable.fLong (n + 3) 1 1 + (if (1 : Nat) = 0 then 2 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (1 : Nat) = 0),
      nbMidC (n + 4) _ 0 (litNe 2 n 4 (by decide +kernel))
        (litNe 3 n 4 (by decide +kernel)),
      serstable.fLong_lo (n + 3) 1 0 (Nat.lt_succ_self 0) had,
      serstable.fLong_two (n + 3) 1 2 (by decide +kernel) h2d,
      serstable.fLong_two (n + 3) 1 1 (Nat.le_refl 1) h1d]
  | m + 2, hm =>
    show (if m + 2 = 1 then 2 else 0)
        + serstable.nbC (n + 4) (serstable.fLong (n + 3) 1) (m + 1 + 1)
      = 2 * serstable.fLong (n + 3) 1 (m + 2)
        + (if m + 2 = 0 then 2 else 0)
    rw [if_neg (sucNe1 m), if_neg (sucNe0 (m + 1))]
    by_cases ht : m + 3 = n + 4
    · have hmd : n + 3 = m + 2 := (Nat.succ.inj ht).symm
      rw [nbTopC (n + 4) _ (m + 1) ht,
        serstable.fLong_end (n + 3) 1 (m + 2) hmd,
        serstable.fLong_two (n + 3) 1 (m + 1) (Nat.le_add_left 1 m)
          (by rw [hmd]; exact Nat.lt_succ_self _)]
    · by_cases hs : m + 4 = n + 4
      · have hmd : n + 3 = m + 3 := (Nat.succ.inj hs).symm
        rw [nbSubC (n + 4) _ (m + 1) ht hs,
          serstable.fLong_end (n + 3) 1 (m + 3) hmd,
          serstable.fLong_two (n + 3) 1 (m + 1) (Nat.le_add_left 1 m)
            (by rw [hmd]; exact ltPlusTwo _),
          serstable.fLong_two (n + 3) 1 (m + 2) (Nat.le_add_left 1 (m + 1))
            (by rw [hmd]; exact Nat.lt_succ_self _)]
      · have hm3 : m + 3 < n + 4 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm) ht
        have hm4 : m + 4 < n + 4 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm3) hs
        have h3d : m + 3 < n + 3 := Nat.lt_of_succ_lt_succ hm4
        have h2dm : m + 2 < n + 3 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 2)) h3d
        have h1dm : m + 1 < n + 3 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 1)) h2dm
        rw [nbMidC (n + 4) _ (m + 1) ht hs,
          serstable.fLong_two (n + 3) 1 (m + 1)
            (Nat.le_add_left 1 m) h1dm,
          serstable.fLong_two (n + 3) 1 (m + 2) (Nat.le_add_left 1 (m + 1)) h2dm,
          serstable.fLong_two (n + 3) 1 (m + 3) (Nat.le_add_left 1 (m + 2)) h3d]

/-- The moved content `2e₁`, the `C` long family's degenerate
head. -/
def cC (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 0 then 2 else 0) 0)

/-- `2e₁` is the `C` long family at the leading coordinate. -/
theorem cC_mem (l : Nat) (hl : 3 ≤ l) :
    row.thetaCount (sertables.tableC l) (cC l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0l : (0 : Nat) < n + 3 := Nat.succ_pos _
  have h1d : (1 : Nat) < n + 2 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 2 n)
  refine famOnePosC (n + 3) (serstable.fLong (n + 2) 0)
    (fun k => if k = 0 then 2 else 0) (fun _ => 0)
    (memLongC (n + 2) 0 (Nat.succ_pos _))
    (fun k hk => ?_) 0 h0l (by decide +kernel)
  match k, hk with
  | 0, _ =>
    show (if (0 : Nat) = 0 then 2 else 0)
        + serstable.nbC (n + 3) (serstable.fLong (n + 2) 0) 0
      = 2 * serstable.fLong (n + 2) 0 0 + 0
    rw [if_pos rfl,
      nbHeadC (n + 3) _ (Nat.lt_of_lt_of_le (by decide +kernel)
        (Nat.le_add_left 3 n)) (litNe 2 n 3 (by decide +kernel)),
      serstable.fLong_two (n + 2) 0 1 (Nat.zero_le 1) h1d,
      serstable.fLong_two (n + 2) 0 0 (Nat.le_refl 0)
        (Nat.succ_pos _)]
  | m + 1, hm =>
    show (if m + 1 = 0 then 2 else 0)
        + serstable.nbC (n + 3) (serstable.fLong (n + 2) 0) (m + 1)
      = 2 * serstable.fLong (n + 2) 0 (m + 1) + 0
    rw [if_neg (sucNe0 m)]
    by_cases ht : m + 2 = n + 3
    · have hmd : n + 2 = m + 1 := (Nat.succ.inj ht).symm
      rw [nbTopC (n + 3) _ m ht,
        serstable.fLong_end (n + 2) 0 (m + 1) hmd,
        serstable.fLong_two (n + 2) 0 m (Nat.zero_le m)
          (by rw [hmd]; exact Nat.lt_succ_self _)]
    · by_cases hs : m + 3 = n + 3
      · have hmd : n + 2 = m + 2 := (Nat.succ.inj hs).symm
        rw [nbSubC (n + 3) _ m ht hs,
          serstable.fLong_end (n + 2) 0 (m + 2) hmd,
          serstable.fLong_two (n + 2) 0 m (Nat.zero_le m)
            (by rw [hmd]; exact ltPlusTwo _),
          serstable.fLong_two (n + 2) 0 (m + 1) (Nat.zero_le _)
            (by rw [hmd]; exact Nat.lt_succ_self _)]
      · have hm2 : m + 2 < n + 3 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm) ht
        have hm3 : m + 3 < n + 3 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm2) hs
        have h2d : m + 2 < n + 2 := Nat.lt_of_succ_lt_succ hm3
        have h1dm : m + 1 < n + 2 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 1)) h2d
        have h0d : m < n + 2 :=
          Nat.lt_trans (Nat.lt_succ_self m) h1dm
        rw [nbMidC (n + 3) _ m ht hs,
          serstable.fLong_two (n + 2) 0 m (Nat.zero_le m) h0d,
          serstable.fLong_two (n + 2) 0 (m + 1) (Nat.zero_le _) h1dm,
          serstable.fLong_two (n + 2) 0 (m + 2) (Nat.zero_le _) h2d]

/-- The moved content `e₂ − e₁`, the difference family's balance
partner at the leading pair. -/
def cD (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 1 then 1 else 0)
    (if i = 0 then 2 else 0))

/-- `e₂ − e₁` is the difference family's balance partner at the
leading pair. -/
theorem cD_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableC l) (cD l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0l : (0 : Nat) < n + 4 := Nat.succ_pos _
  refine famOneNegC (n + 4) (serstable.fDiff 0 1)
    (fun k => if k = 1 then 1 else 0) (fun k => if k = 0 then 2 else 0)
    (memDiffC (n + 4) 0 1 (Nat.lt_succ_self 0)
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)))
    (fun k hk => ?_) 0 h0l (by decide +kernel)
  have hF0 : serstable.fDiff 0 1 0 = 1 :=
    serstable.fDiff_in 0 1 0 (Nat.le_refl 0) (Nat.lt_succ_self 0)
  have hFs : ∀ m, serstable.fDiff 0 1 (m + 1) = 0 := fun m =>
    serstable.fDiff_hi 0 1 (m + 1)
      (fun hc => Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hc))
  match k, hk with
  | 0, _ =>
    show (if (0 : Nat) = 1 then 1 else 0) + 2 * serstable.fDiff 0 1 0
      = serstable.nbC (n + 4) (serstable.fDiff 0 1) 0
        + (if (0 : Nat) = 0 then 2 else 0)
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 1), if_pos rfl,
      nbHeadC (n + 4) _ (Nat.lt_of_lt_of_le (by decide +kernel)
        (Nat.le_add_left 4 n)) (litNe 2 n 4 (by decide +kernel)),
      hF0, hFs 0]
  | 1, _ =>
    show (if (1 : Nat) = 1 then 1 else 0) + 2 * serstable.fDiff 0 1 1
      = serstable.nbC (n + 4) (serstable.fDiff 0 1) (0 + 1)
        + (if (1 : Nat) = 0 then 2 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (1 : Nat) = 0),
      nbMidC (n + 4) _ 0 (litNe 2 n 4 (by decide +kernel))
        (litNe 3 n 4 (by decide +kernel)),
      hF0, hFs 0, hFs 1]
  | m + 2, hm =>
    show (if m + 2 = 1 then 1 else 0) + 2 * serstable.fDiff 0 1 (m + 2)
      = serstable.nbC (n + 4) (serstable.fDiff 0 1) (m + 1 + 1)
        + (if m + 2 = 0 then 2 else 0)
    rw [if_neg (sucNe1 m), if_neg (sucNe0 (m + 1)), hFs (m + 1)]
    by_cases ht : m + 3 = n + 4
    · rw [nbTopC (n + 4) _ (m + 1) ht, hFs m]
    · by_cases hs : m + 4 = n + 4
      · rw [nbSubC (n + 4) _ (m + 1) ht hs, hFs m, hFs (m + 2)]
      · rw [nbMidC (n + 4) _ (m + 1) ht hs, hFs m, hFs (m + 2)]

/-- The moved content `e₂ + e₃`, the `C` sum family one pair in. -/
def cE (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 2 then 1 else 0)
    (if i = 0 then 1 else 0))

/-- `e₂ + e₃` is the `C` sum family at the second pair. -/
theorem cE_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableC l) (cE l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0l : (0 : Nat) < n + 4 := Nat.succ_pos _
  have hbd : (2 : Nat) ≤ n + 3 := Nat.le_add_left 2 (n + 1)
  have h2d : (2 : Nat) < n + 3 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 n)
  refine famOnePosC (n + 4) (serstable.fSumC (n + 3) 1 2)
    (fun k => if k = 2 then 1 else 0) (fun k => if k = 0 then 1 else 0)
    (memSumC (n + 3) 1 2 (Nat.lt_succ_self 1)
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)))
    (fun k hk => ?_) 0 h0l (by decide +kernel)
  match k, hk with
  | 0, _ =>
    show (if (0 : Nat) = 2 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 1 2) 0
      = 2 * serstable.fSumC (n + 3) 1 2 0 + (if (0 : Nat) = 0 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 2), if_pos rfl,
      nbHeadC (n + 4) _ (Nat.lt_of_lt_of_le (by decide +kernel)
        (Nat.le_add_left 4 n)) (litNe 2 n 4 (by decide +kernel)),
      serstable.fSumC_mid (n + 3) 1 2 1 (Nat.le_refl 1)
        (Nat.lt_succ_self 1) hbd,
      serstable.fSumC_lo (n + 3) 1 2 0 (Nat.lt_succ_self 0)
        (Nat.lt_succ_self 1) hbd]
  | 1, _ =>
    show (if (1 : Nat) = 2 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 1 2) (0 + 1)
      = 2 * serstable.fSumC (n + 3) 1 2 1 + (if (1 : Nat) = 0 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 2),
      if_neg (by decide +kernel : ¬ (1 : Nat) = 0),
      nbMidC (n + 4) _ 0 (litNe 2 n 4 (by decide +kernel))
        (litNe 3 n 4 (by decide +kernel)),
      serstable.fSumC_lo (n + 3) 1 2 0 (Nat.lt_succ_self 0)
        (Nat.lt_succ_self 1) hbd,
      serstable.fSumC_two (n + 3) 1 2 2 (Nat.le_refl 2) h2d,
      serstable.fSumC_mid (n + 3) 1 2 1 (Nat.le_refl 1)
        (Nat.lt_succ_self 1) hbd]
  | 2, _ =>
    show (if (2 : Nat) = 2 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 1 2) (1 + 1)
      = 2 * serstable.fSumC (n + 3) 1 2 2 + (if (2 : Nat) = 0 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (2 : Nat) = 0)]
    by_cases hs : (4 : Nat) = n + 4
    · have hn0 : n = 0 := (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
        (Nat.succ.inj hs)))).symm
      subst hn0
      rw [nbSubC 4 _ 1 (by decide +kernel) rfl,
        serstable.fSumC_mid 3 1 2 1 (Nat.le_refl 1)
          (Nat.lt_succ_self 1) hbd,
        serstable.fSumC_end 3 1 2 3 hbd rfl,
        serstable.fSumC_two 3 1 2 2 (Nat.le_refl 2) h2d]
    · have hn : ¬ n = 0 := fun hn0 => hs (by rw [hn0])
      have h3d : (3 : Nat) < n + 3 :=
        Nat.lt_of_lt_of_le (by decide +kernel)
          (Nat.add_le_add_right (Nat.succ_le_of_lt
            (Nat.pos_of_ne_zero hn)) 3)
      rw [nbMidC (n + 4) _ 1 (litNe 3 n 4 (by decide +kernel)) hs,
        serstable.fSumC_mid (n + 3) 1 2 1 (Nat.le_refl 1)
          (Nat.lt_succ_self 1) hbd,
        serstable.fSumC_two (n + 3) 1 2 3 (by decide +kernel) h3d,
        serstable.fSumC_two (n + 3) 1 2 2 (Nat.le_refl 2) h2d]
  | m + 3, hm =>
    show (if m + 3 = 2 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 1 2) (m + 2 + 1)
      = 2 * serstable.fSumC (n + 3) 1 2 (m + 3)
        + (if m + 3 = 0 then 1 else 0)
    rw [if_neg (sucNe2 m), if_neg (sucNe0 (m + 2))]
    by_cases ht : m + 4 = n + 4
    · have hmd : n + 3 = m + 3 := by
        rw [← Nat.succ.inj ht]
      rw [nbTopC (n + 4) _ (m + 2) ht,
        serstable.fSumC_end (n + 3) 1 2 (m + 3) hbd hmd,
        serstable.fSumC_two (n + 3) 1 2 (m + 2) (Nat.le_add_left 2 m)
          (by rw [hmd]; exact Nat.lt_succ_self _)]
    · by_cases hs : m + 5 = n + 4
      · have hmd : n + 3 = m + 4 := (Nat.succ.inj hs).symm
        rw [nbSubC (n + 4) _ (m + 2) ht hs,
          serstable.fSumC_end (n + 3) 1 2 (m + 4) hbd hmd,
          serstable.fSumC_two (n + 3) 1 2 (m + 2) (Nat.le_add_left 2 m)
            (by rw [hmd]; exact ltPlusTwo _),
          serstable.fSumC_two (n + 3) 1 2 (m + 3) (Nat.le_add_left 2 (m + 1))
            (by rw [hmd]; exact Nat.lt_succ_self _)]
      · have hm4 : m + 4 < n + 4 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm) ht
        have hm5 : m + 5 < n + 4 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm4) hs
        have h4d : m + 4 < n + 3 := Nat.lt_of_succ_lt_succ hm5
        have h3dm : m + 3 < n + 3 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 3)) h4d
        have h2dm : m + 2 < n + 3 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 2)) h3dm
        rw [nbMidC (n + 4) _ (m + 2) ht hs,
          serstable.fSumC_two (n + 3) 1 2 (m + 2)
            (Nat.le_add_left 2 m) h2dm,
          serstable.fSumC_two (n + 3) 1 2 (m + 3)
            (Nat.le_add_left 2 (m + 1)) h3dm,
          serstable.fSumC_two (n + 3) 1 2 (m + 4)
            (Nat.le_add_left 2 (m + 2)) h4d]

/-- The moved content `e₃ − e₁`, the difference family's balance
partner at the leading-to-third pair. -/
def cF (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 2 then 1 else 0)
    (if i = 0 then 1 else if i = 1 then 1 else 0))

/-- `e₃ − e₁` is the difference family's balance partner at the
pair `(0, 2)`. -/
theorem cF_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableC l) (cF l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0l : (0 : Nat) < n + 4 := Nat.succ_pos _
  refine famOneNegC (n + 4) (serstable.fDiff 0 2)
    (fun k => if k = 2 then 1 else 0)
    (fun k => if k = 0 then 1 else if k = 1 then 1 else 0)
    (memDiffC (n + 4) 0 2 (Nat.zero_lt_succ 1)
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)))
    (fun k hk => ?_) 0 h0l (by decide +kernel)
  have hF0 : serstable.fDiff 0 2 0 = 1 :=
    serstable.fDiff_in 0 2 0 (Nat.le_refl 0) (Nat.zero_lt_succ 1)
  have hF1 : serstable.fDiff 0 2 1 = 1 :=
    serstable.fDiff_in 0 2 1 (Nat.zero_le 1) (Nat.lt_succ_self 1)
  have hFs : ∀ m, serstable.fDiff 0 2 (m + 2) = 0 := fun m =>
    serstable.fDiff_hi 0 2 (m + 2)
      (fun hc => Nat.not_lt_zero m
        (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hc)))
  match k, hk with
  | 0, _ =>
    show (if (0 : Nat) = 2 then 1 else 0) + 2 * serstable.fDiff 0 2 0
      = serstable.nbC (n + 4) (serstable.fDiff 0 2) 0
        + (if (0 : Nat) = 0 then 1 else if (0 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 2), if_pos rfl,
      nbHeadC (n + 4) _ (Nat.lt_of_lt_of_le (by decide +kernel)
        (Nat.le_add_left 4 n)) (litNe 2 n 4 (by decide +kernel)),
      hF0, hF1]
  | 1, _ =>
    show (if (1 : Nat) = 2 then 1 else 0) + 2 * serstable.fDiff 0 2 1
      = serstable.nbC (n + 4) (serstable.fDiff 0 2) (0 + 1)
        + (if (1 : Nat) = 0 then 1 else if (1 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 2),
      if_neg (by decide +kernel : ¬ (1 : Nat) = 0), if_pos rfl,
      nbMidC (n + 4) _ 0 (litNe 2 n 4 (by decide +kernel))
        (litNe 3 n 4 (by decide +kernel)),
      hF0, hF1, hFs 0]
  | 2, _ =>
    show (if (2 : Nat) = 2 then 1 else 0) + 2 * serstable.fDiff 0 2 2
      = serstable.nbC (n + 4) (serstable.fDiff 0 2) (1 + 1)
        + (if (2 : Nat) = 0 then 1 else if (2 : Nat) = 1 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (2 : Nat) = 0),
      if_neg (by decide +kernel : ¬ (2 : Nat) = 1), hFs 0]
    by_cases hs : (4 : Nat) = n + 4
    · rw [nbSubC (n + 4) _ 1 (litNe 3 n 4 (by decide +kernel)) hs,
        hF1, hFs 1]
    · rw [nbMidC (n + 4) _ 1 (litNe 3 n 4 (by decide +kernel)) hs,
        hF1, hFs 1]
  | m + 3, _ =>
    show (if m + 3 = 2 then 1 else 0) + 2 * serstable.fDiff 0 2 (m + 3)
      = serstable.nbC (n + 4) (serstable.fDiff 0 2) (m + 2 + 1)
        + (if m + 3 = 0 then 1 else if m + 3 = 1 then 1 else 0)
    rw [if_neg (sucNe2 m), if_neg (sucNe0 (m + 2)),
      if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)), hFs (m + 1)]
    by_cases ht : m + 4 = n + 4
    · rw [nbTopC (n + 4) _ (m + 2) ht, hFs m]
    · by_cases hs : m + 5 = n + 4
      · rw [nbSubC (n + 4) _ (m + 2) ht hs, hFs m, hFs (m + 2)]
      · rw [nbMidC (n + 4) _ (m + 2) ht hs, hFs m, hFs (m + 2)]

/-- The moved content `e₃ + e₄`, the `C` sum family two pairs
in. -/
def cG (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 3 then 1 else 0)
    (if i = 1 then 1 else 0))

/-- `e₃ + e₄` is the `C` sum family at the third pair. -/
theorem cG_mem (l : Nat) (hl : 5 ≤ l) :
    row.thetaCount (sertables.tableC l) (cG l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h1l : (1 : Nat) < n + 5 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 n)
  have hbd : (3 : Nat) ≤ n + 4 := Nat.le_add_left 3 (n + 1)
  have hab : (2 : Nat) < 3 := Nat.lt_succ_self 2
  have h3d : (3 : Nat) < n + 4 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)
  refine famOnePosC (n + 5) (serstable.fSumC (n + 4) 2 3)
    (fun k => if k = 3 then 1 else 0) (fun k => if k = 1 then 1 else 0)
    (memSumC (n + 4) 2 3 hab
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 n)))
    (fun k hk => ?_) 1 h1l (by decide +kernel)
  match k, hk with
  | 0, _ =>
    show (if (0 : Nat) = 3 then 1 else 0)
        + serstable.nbC (n + 5) (serstable.fSumC (n + 4) 2 3) 0
      = 2 * serstable.fSumC (n + 4) 2 3 0 + (if (0 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 3),
      if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
      nbHeadC (n + 5) _ h1l (litNe 2 n 5 (by decide +kernel)),
      serstable.fSumC_lo (n + 4) 2 3 1 (Nat.lt_succ_self 1) hab hbd,
      serstable.fSumC_lo (n + 4) 2 3 0 (Nat.zero_lt_succ 1) hab hbd]
  | 1, _ =>
    show (if (1 : Nat) = 3 then 1 else 0)
        + serstable.nbC (n + 5) (serstable.fSumC (n + 4) 2 3) (0 + 1)
      = 2 * serstable.fSumC (n + 4) 2 3 1 + (if (1 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 3), if_pos rfl,
      nbMidC (n + 5) _ 0 (litNe 2 n 5 (by decide +kernel))
        (litNe 3 n 5 (by decide +kernel)),
      serstable.fSumC_lo (n + 4) 2 3 0 (Nat.zero_lt_succ 1) hab hbd,
      serstable.fSumC_mid (n + 4) 2 3 2 (Nat.le_refl 2)
        (Nat.lt_succ_self 2) hbd,
      serstable.fSumC_lo (n + 4) 2 3 1 (Nat.lt_succ_self 1) hab hbd]
  | 2, _ =>
    show (if (2 : Nat) = 3 then 1 else 0)
        + serstable.nbC (n + 5) (serstable.fSumC (n + 4) 2 3) (1 + 1)
      = 2 * serstable.fSumC (n + 4) 2 3 2 + (if (2 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (2 : Nat) = 3),
      if_neg (by decide +kernel : ¬ (2 : Nat) = 1),
      nbMidC (n + 5) _ 1 (litNe 3 n 5 (by decide +kernel))
        (litNe 4 n 5 (by decide +kernel)),
      serstable.fSumC_lo (n + 4) 2 3 1 (Nat.lt_succ_self 1) hab hbd,
      serstable.fSumC_two (n + 4) 2 3 3 (Nat.le_refl 3) h3d,
      serstable.fSumC_mid (n + 4) 2 3 2 (Nat.le_refl 2)
        (Nat.lt_succ_self 2) hbd]
  | 3, _ =>
    show (if (3 : Nat) = 3 then 1 else 0)
        + serstable.nbC (n + 5) (serstable.fSumC (n + 4) 2 3) (2 + 1)
      = 2 * serstable.fSumC (n + 4) 2 3 3 + (if (3 : Nat) = 1 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (3 : Nat) = 1)]
    by_cases hs : (5 : Nat) = n + 5
    · have hn0 : n = 0 := (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
        (Nat.succ.inj (Nat.succ.inj hs))))).symm
      subst hn0
      rw [nbSubC 5 _ 2 (by decide +kernel) rfl,
        serstable.fSumC_mid 4 2 3 2 (Nat.le_refl 2)
          (Nat.lt_succ_self 2) hbd,
        serstable.fSumC_end 4 2 3 4 hbd rfl,
        serstable.fSumC_two 4 2 3 3 (Nat.le_refl 3) h3d]
    · have hn : ¬ n = 0 := fun hn0 => hs (by rw [hn0])
      have h4d : (4 : Nat) < n + 4 :=
        Nat.lt_of_lt_of_le (by decide +kernel)
          (Nat.add_le_add_right (Nat.succ_le_of_lt
            (Nat.pos_of_ne_zero hn)) 4)
      rw [nbMidC (n + 5) _ 2 (litNe 4 n 5 (by decide +kernel)) hs,
        serstable.fSumC_mid (n + 4) 2 3 2 (Nat.le_refl 2)
          (Nat.lt_succ_self 2) hbd,
        serstable.fSumC_two (n + 4) 2 3 4 (by decide +kernel) h4d,
        serstable.fSumC_two (n + 4) 2 3 3 (Nat.le_refl 3) h3d]
  | m + 4, hm =>
    show (if m + 4 = 3 then 1 else 0)
        + serstable.nbC (n + 5) (serstable.fSumC (n + 4) 2 3) (m + 3 + 1)
      = 2 * serstable.fSumC (n + 4) 2 3 (m + 4)
        + (if m + 4 = 1 then 1 else 0)
    rw [if_neg (sucNe3 m),
      if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]
    by_cases ht : m + 5 = n + 5
    · have hmd : n + 4 = m + 4 := (Nat.succ.inj ht).symm
      rw [nbTopC (n + 5) _ (m + 3) ht,
        serstable.fSumC_end (n + 4) 2 3 (m + 4) hbd hmd,
        serstable.fSumC_two (n + 4) 2 3 (m + 3) (Nat.le_add_left 3 m)
          (by rw [hmd]; exact Nat.lt_succ_self _)]
    · by_cases hs : m + 6 = n + 5
      · have hmd : n + 4 = m + 5 := (Nat.succ.inj hs).symm
        rw [nbSubC (n + 5) _ (m + 3) ht hs,
          serstable.fSumC_end (n + 4) 2 3 (m + 5) hbd hmd,
          serstable.fSumC_two (n + 4) 2 3 (m + 3) (Nat.le_add_left 3 m)
            (by rw [hmd]; exact ltPlusTwo _),
          serstable.fSumC_two (n + 4) 2 3 (m + 4)
            (Nat.le_add_left 3 (m + 1))
            (by rw [hmd]; exact Nat.lt_succ_self _)]
      · have hm5 : m + 5 < n + 5 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm) ht
        have hm6 : m + 6 < n + 5 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm5) hs
        have h5d : m + 5 < n + 4 := Nat.lt_of_succ_lt_succ hm6
        have h4dm : m + 4 < n + 4 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 4)) h5d
        have h3dm : m + 3 < n + 4 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 3)) h4dm
        rw [nbMidC (n + 5) _ (m + 3) ht hs,
          serstable.fSumC_two (n + 4) 2 3 (m + 3)
            (Nat.le_add_left 3 m) h3dm,
          serstable.fSumC_two (n + 4) 2 3 (m + 4)
            (Nat.le_add_left 3 (m + 1)) h4dm,
          serstable.fSumC_two (n + 4) 2 3 (m + 5)
            (Nat.le_add_left 3 (m + 2)) h5d]

/-- The moved content `e₁ + e₃`, the `C` sum family at the split
pair. -/
def cH (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts
    (if i = 0 then 1 else if i = 2 then 1 else 0)
    (if i = 1 then 1 else 0))

/-- `e₁ + e₃` is the `C` sum family at the pair `(0, 2)`. -/
theorem cH_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableC l) (cH l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  have h0l : (0 : Nat) < n + 4 := Nat.succ_pos _
  have hbd : (2 : Nat) ≤ n + 3 := Nat.le_add_left 2 (n + 1)
  have hab : (0 : Nat) < 2 := Nat.zero_lt_succ 1
  have h2d : (2 : Nat) < n + 3 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 n)
  refine famOnePosC (n + 4) (serstable.fSumC (n + 3) 0 2)
    (fun k => if k = 0 then 1 else if k = 2 then 1 else 0)
    (fun k => if k = 1 then 1 else 0)
    (memSumC (n + 3) 0 2 hab
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 n)))
    (fun k hk => ?_) 0 h0l (by decide +kernel)
  match k, hk with
  | 0, _ =>
    show (if (0 : Nat) = 0 then 1 else if (0 : Nat) = 2 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 0 2) 0
      = 2 * serstable.fSumC (n + 3) 0 2 0 + (if (0 : Nat) = 1 then 1 else 0)
    rw [if_pos rfl, if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
      nbHeadC (n + 4) _ (Nat.lt_of_lt_of_le (by decide +kernel)
        (Nat.le_add_left 4 n)) (litNe 2 n 4 (by decide +kernel)),
      serstable.fSumC_mid (n + 3) 0 2 1 (Nat.zero_le 1)
        (Nat.lt_succ_self 1) hbd,
      serstable.fSumC_mid (n + 3) 0 2 0 (Nat.le_refl 0) hab hbd]
  | 1, _ =>
    show (if (1 : Nat) = 0 then 1 else if (1 : Nat) = 2 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 0 2) (0 + 1)
      = 2 * serstable.fSumC (n + 3) 0 2 1 + (if (1 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 0),
      if_neg (by decide +kernel : ¬ (1 : Nat) = 2), if_pos rfl,
      nbMidC (n + 4) _ 0 (litNe 2 n 4 (by decide +kernel))
        (litNe 3 n 4 (by decide +kernel)),
      serstable.fSumC_mid (n + 3) 0 2 0 (Nat.le_refl 0) hab hbd,
      serstable.fSumC_two (n + 3) 0 2 2 (Nat.le_refl 2) h2d,
      serstable.fSumC_mid (n + 3) 0 2 1 (Nat.zero_le 1)
        (Nat.lt_succ_self 1) hbd]
  | 2, _ =>
    show (if (2 : Nat) = 0 then 1 else if (2 : Nat) = 2 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 0 2) (1 + 1)
      = 2 * serstable.fSumC (n + 3) 0 2 2 + (if (2 : Nat) = 1 then 1 else 0)
    rw [if_neg (by decide +kernel : ¬ (2 : Nat) = 0), if_pos rfl,
      if_neg (by decide +kernel : ¬ (2 : Nat) = 1)]
    by_cases hs : (4 : Nat) = n + 4
    · have hn0 : n = 0 := (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
        (Nat.succ.inj hs)))).symm
      subst hn0
      rw [nbSubC 4 _ 1 (by decide +kernel) rfl,
        serstable.fSumC_mid 3 0 2 1 (Nat.zero_le 1)
          (Nat.lt_succ_self 1) hbd,
        serstable.fSumC_end 3 0 2 3 hbd rfl,
        serstable.fSumC_two 3 0 2 2 (Nat.le_refl 2) h2d]
    · have hn : ¬ n = 0 := fun hn0 => hs (by rw [hn0])
      have h3d : (3 : Nat) < n + 3 :=
        Nat.lt_of_lt_of_le (by decide +kernel)
          (Nat.add_le_add_right (Nat.succ_le_of_lt
            (Nat.pos_of_ne_zero hn)) 3)
      rw [nbMidC (n + 4) _ 1 (litNe 3 n 4 (by decide +kernel)) hs,
        serstable.fSumC_mid (n + 3) 0 2 1 (Nat.zero_le 1)
          (Nat.lt_succ_self 1) hbd,
        serstable.fSumC_two (n + 3) 0 2 3 (by decide +kernel) h3d,
        serstable.fSumC_two (n + 3) 0 2 2 (Nat.le_refl 2) h2d]
  | m + 3, hm =>
    show (if m + 3 = 0 then 1 else if m + 3 = 2 then 1 else 0)
        + serstable.nbC (n + 4) (serstable.fSumC (n + 3) 0 2) (m + 2 + 1)
      = 2 * serstable.fSumC (n + 3) 0 2 (m + 3)
        + (if m + 3 = 1 then 1 else 0)
    rw [if_neg (sucNe0 (m + 2)), if_neg (sucNe2 m),
      if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]
    by_cases ht : m + 4 = n + 4
    · have hmd : n + 3 = m + 3 := (Nat.succ.inj ht).symm
      rw [nbTopC (n + 4) _ (m + 2) ht,
        serstable.fSumC_end (n + 3) 0 2 (m + 3) hbd hmd,
        serstable.fSumC_two (n + 3) 0 2 (m + 2) (Nat.le_add_left 2 m)
          (by rw [hmd]; exact Nat.lt_succ_self _)]
    · by_cases hs : m + 5 = n + 4
      · have hmd : n + 3 = m + 4 := (Nat.succ.inj hs).symm
        rw [nbSubC (n + 4) _ (m + 2) ht hs,
          serstable.fSumC_end (n + 3) 0 2 (m + 4) hbd hmd,
          serstable.fSumC_two (n + 3) 0 2 (m + 2) (Nat.le_add_left 2 m)
            (by rw [hmd]; exact ltPlusTwo _),
          serstable.fSumC_two (n + 3) 0 2 (m + 3)
            (Nat.le_add_left 2 (m + 1))
            (by rw [hmd]; exact Nat.lt_succ_self _)]
      · have hm4 : m + 4 < n + 4 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm) ht
        have hm5 : m + 5 < n + 4 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hm4) hs
        have h4d : m + 4 < n + 3 := Nat.lt_of_succ_lt_succ hm5
        have h3dm : m + 3 < n + 3 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 3)) h4d
        have h2dm : m + 2 < n + 3 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 2)) h3dm
        rw [nbMidC (n + 4) _ (m + 2) ht hs,
          serstable.fSumC_two (n + 3) 0 2 (m + 2)
            (Nat.le_add_left 2 m) h2dm,
          serstable.fSumC_two (n + 3) 0 2 (m + 3)
            (Nat.le_add_left 2 (m + 1)) h3dm,
          serstable.fSumC_two (n + 3) 0 2 (m + 4)
            (Nat.le_add_left 2 (m + 2)) h4d]

/-! ### The `C` letter devices -/

/-- The `C` family classes, `foldsC_cases`' three arms. -/
private def famCaseC (l : Nat) (F : Nat → Nat) : Prop :=
  (∃ a b, a < b ∧ b < l ∧ F = serstable.fDiff a b)
  ∨ (∃ d a b, l = d + 1 ∧ a < b ∧ b < l ∧ F = serstable.fSumC d a b)
  ∨ (∃ d a, l = d + 1 ∧ a < l ∧ F = serstable.fLong d a)

/-- The letter's vacant term at `C`: a raised content occupied
somewhere and parting from every family's column at some key, at
either limb, reads the vacant θ count. -/
private theorem termVanishC (l : Nat) (x : List BPair)
    (hu : ∃ k, k < l ∧ ¬ (ground.getAt BPair.unit x k).oneValue BPair.unit)
    (hpos : ∀ F : Nat → Nat, famCaseC l F →
      ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue
        (BPair.ofCounts (2 * F y) (serstable.nbC l F y)))
    (hneg : ∀ F : Nat → Nat, famCaseC l F →
      ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue
        (BPair.ofCounts (serstable.nbC l F y) (2 * F y))) :
    row.thetaCount (sertables.tableC l) x = 0 := by
  refine termVanishG (sertables.tableC l) x hu (fun j hj => ?_)
  have hjl : j < (sertables.foldsC l).length := hj
  obtain ⟨F, hfe, hcase⟩ := serstable.foldsC_cases l j hjl
  constructor
  · intro he
    obtain ⟨y, hy, hoff⟩ := hpos F hcase
    refine hoff ?_
    rw [he]
    exact serstable.posCorootV_entryC l j y F hy hfe
  · intro he
    obtain ⟨y, hy, hoff⟩ := hneg F hcase
    refine hoff ?_
    rw [he]
    exact serstable.negCorootV_entryC l j y F hy hfe

/-- A raised content whose entry at a key reads a magnitude past
two sits off the `C` θ list: every `C` family's column stays within
two of its neighbour fold (`serstable.colC_magLe`). -/
private theorem termVanishMagC (l k : Nat) (hk : k < l) (x : List BPair)
    (p q : Nat)
    (hx : (ground.getAt BPair.unit x k).oneValue (BPair.ofCounts p q))
    (hmag : q + 3 ≤ p ∨ p + 3 ≤ q) :
    row.thetaCount (sertables.tableC l) x = 0 := by
  refine termVanishC l x ⟨k, hk, fun hc => magNe p q hmag
      (BPair.ofCounts_unit.mp (BPair.oneValue_trans
        (BPair.oneValue_symm hx) hc))⟩
    (fun F hcase => ⟨k, hk, fun hc => ?_⟩)
    (fun F hcase => ⟨k, hk, fun hc => ?_⟩)
  · obtain ⟨hlo, hhi⟩ := serstable.colC_magLe F k l hk hcase
    exact magRefute p q (2 * F k) (serstable.nbC l F k)
      (ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx) hc))
      hlo hhi hmag
  · obtain ⟨hlo, hhi⟩ := serstable.colC_magLe F k l hk hcase
    exact magRefute p q (serstable.nbC l F k) (2 * F k)
      (ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx) hc))
      hhi hlo hmag


/-- The `C` raised content's count reads at a key: the moved
content's counts raised by the scaled Cartan entry's. -/
private theorem raisedCountC (l : Nat) (u v : Nat → Nat) (c i y : Nat)
    (hi : i < l) (hy : y < l) (p q : Nat)
    (hcart : (serstable.cartC l i y).oneValue (BPair.ofCounts p q)) :
    (ground.getAt BPair.unit
      (raisedG (sertables.tableC l) (nuOf l (fun k => BPair.ofCounts (u k) (v k))) c i) y).oneValue
      (BPair.ofCounts (u y + c * p) (v y + c * q)) := by
  refine raisedCountG (sertables.tableC l) u v c i y hy ?_ p q ?_
  · rw [serstable.cartC_eq l]
    exact ground.matOf_rowLength [] l l
      (fun p q => serstable.cartC l p q) i hi
  · have hcent : ground.getAt BPair.unit
        (ground.getAt [] (sertables.tableC l).cartan i) y
        = serstable.cartC l i y := by
      rw [serstable.cartC_eq l]
      exact ground.matOf_entry [] BPair.unit l l
        (fun p q => serstable.cartC l p q) i y hi hy
    rw [hcent]
    exact hcart

/-- The `C` Cartan row's diagonal entry as a count pair. -/
private theorem cartDiagC (l i : Nat) :
    (serstable.cartC l i i).oneValue (BPair.ofCounts 2 0) := by
  rw [serstable.cartCd l i]
  exact (by decide +kernel)

/-- The `C` Cartan row's upper neighbour. -/
private theorem cartUpC (l i : Nat) :
    (serstable.cartC l i (i + 1)).oneValue (BPair.ofCounts 0 1) := by
  rw [serstable.cartCup l i]
  exact (by decide +kernel)

/-- The `C` Cartan row's lower neighbour off the long last edge. -/
private theorem cartDn1C (l i : Nat) (h : ¬ i + 2 = l) :
    (serstable.cartC l (i + 1) i).oneValue (BPair.ofCounts 0 1) := by
  rw [serstable.cartCdn1 l i h]
  exact (by decide +kernel)

/-- The `C` Cartan row is vacant off the letter's three keys. -/
private theorem cartOffC (l i j : Nat) (h1 : ¬ j = i) (h2 : ¬ j + 1 = i)
    (h3 : ¬ j = i + 1) :
    (serstable.cartC l i j).oneValue (BPair.ofCounts 0 0) := by
  rw [serstable.cartCoff l i j h1 h2 h3]
  exact (by decide +kernel)

/-! ### The `C` sources' shifted keys -/

/-- The `C` unit base's shifted key at the leading coordinate. -/
private theorem kapW2_0 (l : Nat) (h : 0 < l) :
    ground.getAt 0 (serstable.memberRho [2] l) 0 = 3 := by
  rw [serstable.memberRhoAt [2] l 0 h]
  rfl

/-- The `C` unit base's shifted key across the run and the tail. -/
private theorem kapW2 (l k : Nat) (hk1 : 1 ≤ k) (hk : k < l) :
    ground.getAt 0 (serstable.memberRho [2] l) k = 1 :=
  serstable.memberRho_run [2] l k hk1 hk

/-- The first fundamental's shifted key at the leading
coordinate. -/
private theorem kapW1_0 (l : Nat) (h : 0 < l) :
    ground.getAt 0 (serstable.memberRho [1] l) 0 = 2 := by
  rw [serstable.memberRhoAt [1] l 0 h]
  rfl

/-- The first fundamental's shifted key across the run and the
tail. -/
private theorem kapW1 (l k : Nat) (hk1 : 1 ≤ k) (hk : k < l) :
    ground.getAt 0 (serstable.memberRho [1] l) k = 1 :=
  serstable.memberRho_run [1] l k hk1 hk

/-- The one-row cube's shifted key at the leading coordinate. -/
private theorem kapW3_0 (l : Nat) (h : 0 < l) :
    ground.getAt 0 (serstable.memberRho [3] l) 0 = 4 := by
  rw [serstable.memberRhoAt [3] l 0 h]
  rfl

/-- The one-row cube's shifted key across the run and the tail. -/
private theorem kapW3 (l k : Nat) (hk1 : 1 ≤ k) (hk : k < l) :
    ground.getAt 0 (serstable.memberRho [3] l) k = 1 :=
  serstable.memberRho_run [3] l k hk1 hk

/-- The two-row source's shifted key at the leading coordinate. -/
private theorem kapW21_0 (l : Nat) (h : 0 < l) :
    ground.getAt 0 (serstable.memberRho [2, 1] l) 0 = 2 := by
  rw [serstable.memberRhoAt [2, 1] l 0 h]
  rfl

/-- The two-row source's shifted key at the second coordinate. -/
private theorem kapW21_1 (l : Nat) (h : 1 < l) :
    ground.getAt 0 (serstable.memberRho [2, 1] l) 1 = 2 := by
  rw [serstable.memberRhoAt [2, 1] l 1 h]
  rfl

/-- The two-row source's shifted key across the run and the
tail. -/
private theorem kapW21 (l k : Nat) (hk2 : 2 ≤ k) (hk : k < l) :
    ground.getAt 0 (serstable.memberRho [2, 1] l) k = 1 :=
  serstable.memberRho_run [2, 1] l k hk2 hk

/-- A difference window occupied at a key opens at or before it and
closes beyond it. -/
private theorem dIn {a b k : Nat} (h : serstable.fDiff a b k = 1) :
    a ≤ k ∧ k < b := by
  by_cases h1 : a ≤ k
  · by_cases h2 : k < b
    · exact ⟨h1, h2⟩
    · exact absurd (h.symm.trans (serstable.fDiff_hi a b k h2))
        (by decide +kernel)
  · exact absurd (h.symm.trans (serstable.fDiff_lo a b k h1))
      (by decide +kernel)

/-- A raised content reading plus two at an interior `C` letter's
own key sits at the narrow window, the long head or the negated
long at the key above, or nowhere: parting from each survivor's
column vacates the term. -/
private theorem termVanishTwoC (l m : Nat) (hml4 : m + 4 ≤ l)
    (x : List BPair)
    (h2 : (ground.getAt BPair.unit x (m + 1)).oneValue (BPair.ofCounts 2 0))
    (hoffD : ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue
      (BPair.ofCounts (2 * serstable.fDiff (m + 1) (m + 2) y)
        (serstable.nbC l (serstable.fDiff (m + 1) (m + 2)) y)))
    (hoffL : ∀ d, l = d + 1 →
      ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue
        (BPair.ofCounts (2 * serstable.fLong d (m + 1) y)
          (serstable.nbC l (serstable.fLong d (m + 1)) y)))
    (hoffNL : ∀ d, l = d + 1 →
      ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue
        (BPair.ofCounts (serstable.nbC l (serstable.fLong d (m + 2)) y)
          (2 * serstable.fLong d (m + 2) y))) :
    row.thetaCount (sertables.tableC l) x = 0 := by
  have hm2l : m + 2 < l :=
    Nat.lt_of_lt_of_le (ltPlusTwo (m + 2)) hml4
  have hm3l : m + 3 < l :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (m + 3)) hml4
  have hm1l : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
  have hne2 : ¬ m + 2 = l := Nat.ne_of_lt hm2l
  have hne3 : ¬ m + 3 = l := Nat.ne_of_lt hm3l
  refine termVanishC l x
    ⟨m + 1, hm1l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · by_cases c1 : (ground.getAt BPair.unit x (m + 1)).oneValue
        (BPair.ofCounts (2 * F (m + 1)) (serstable.nbC l F (m + 1)))
    · have hcr : 2 + serstable.nbC l F (m + 1) = 2 * F (m + 1) + 0 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) c1)
      rw [nbMidC l F m hne2 hne3] at hcr
      have hnat : 2 * F (m + 1) = F m + F (m + 2) + 2 :=
        (Nat.add_zero (2 * F (m + 1))).symm.trans
          (hcr.symm.trans (Nat.add_comm 2 (F m + F (m + 2))))
      match serstable.twoSplitC l m F hm3l hcase hnat with
      | .inl hF =>
        obtain ⟨y, hy, hoff⟩ := hoffD
        refine ⟨y, hy, ?_⟩
        rw [hF]
        exact hoff
      | .inr ⟨d, hld, hF⟩ =>
        obtain ⟨y, hy, hoff⟩ := hoffL d hld
        refine ⟨y, hy, ?_⟩
        rw [hF]
        exact hoff
    · exact ⟨m + 1, hm1l, c1⟩
  · by_cases c1 : (ground.getAt BPair.unit x (m + 1)).oneValue
        (BPair.ofCounts (serstable.nbC l F (m + 1)) (2 * F (m + 1)))
    · have hcr : 2 + 2 * F (m + 1) = serstable.nbC l F (m + 1) + 0 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) c1)
      rw [nbMidC l F m hne2 hne3] at hcr
      have hnat : F m + F (m + 2) = 2 * F (m + 1) + 2 :=
        (Nat.add_zero (F m + F (m + 2))).symm.trans
          (hcr.symm.trans (Nat.add_comm 2 (2 * F (m + 1))))
      obtain ⟨d, hld, hF⟩ := serstable.negTwoLongC l m F hm3l hcase hnat
      obtain ⟨y, hy, hoff⟩ := hoffNL d hld
      refine ⟨y, hy, ?_⟩
      rw [hF]
      exact hoff
    · exact ⟨m + 1, hm1l, c1⟩

/-- The last letter's refusal at `C`: a raised content reading the
tail dipole's plus two at the last key against a stated occupied
head entry sits off the θ list, the last column read at the
undoubled coroot. -/
private theorem termTailTopC (l q k0 p0 q0 : Nat) (hq : q + 2 = l)
    (hl5 : 5 ≤ l) (hk01 : k0 ≤ 1) (x : List BPair)
    (hx0 : (ground.getAt BPair.unit x k0).oneValue (BPair.ofCounts p0 q0))
    (hne0 : ¬ p0 = q0)
    (hxt : (ground.getAt BPair.unit x (q + 1)).oneValue
      (BPair.ofCounts 2 0)) :
    row.thetaCount (sertables.tableC l) x = 0 := by
  have hq3 : 3 ≤ q :=
    Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
      (show 5 ≤ q + 2 by rw [hq]; exact hl5))
  have hq1l : q + 1 < l := by
    rw [← hq]
    exact Nat.lt_succ_self (q + 1)
  have hk0l : k0 < l :=
    Nat.lt_of_le_of_lt hk01 (Nat.lt_of_lt_of_le (by decide +kernel) hl5)
  have h1l : (1 : Nat) < l :=
    Nat.lt_of_lt_of_le (by decide +kernel) hl5
  have hne2l : ¬ (2 : Nat) = l :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide +kernel) hl5)
  have hne3l : ¬ (3 : Nat) = l :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le (by decide +kernel) hl5)
  have hk0q1 : ∀ j, j ≤ 2 → j < q + 1 := fun j hj =>
    Nat.lt_of_le_of_lt hj (Nat.lt_of_lt_of_le (by decide +kernel)
      (Nat.succ_le_succ hq3))
  refine termVanishC l x
    ⟨q + 1, hq1l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm hxt) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · by_cases c1 : (ground.getAt BPair.unit x (q + 1)).oneValue
        (BPair.ofCounts (2 * F (q + 1)) (serstable.nbC l F (q + 1)))
    · have hcr : 2 + serstable.nbC l F (q + 1) = 2 * F (q + 1) + 0 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hxt) c1)
      rw [nbTopC l F q hq, Nat.add_zero] at hcr
      match hcase with
      | .inl ⟨a, b, hab, hbl, hF⟩ =>
        have hFt : F (q + 1) = 0 := by
          rw [hF]
          exact serstable.fDiff_hi a b (q + 1) (fun hc =>
            Nat.not_succ_le_self (q + 1)
              (Nat.le_trans (Nat.succ_le_of_lt hc)
                (by rw [← hq] at hbl; exact Nat.le_of_lt_succ hbl)))
        rw [hFt, Nat.mul_zero] at hcr
        exact absurd ((Nat.add_comm 2 (F q)).symm.trans hcr)
          (fun hc => Nat.noConfusion hc)
      | .inr (.inl ⟨d, a, b, hld, hab, hbl, hF⟩) =>
        have hdq : d = q + 1 := Nat.succ.inj (hld.symm.trans hq.symm)
        have hbd : b ≤ d := Nat.le_of_lt_succ (show b < d + 1 by rw [← hld]; exact hbl)
        have haq : a ≤ q := Nat.le_of_lt_succ
          (show a < q + 1 by rw [← hdq]; exact Nat.lt_of_lt_of_le hab hbd)
        have hFt : F (q + 1) = 1 := by
          rw [hF]
          exact serstable.fSumC_end d a b (q + 1) hbd hdq
        rw [hFt] at hcr
        have hq0 : F q = 0 := by
          have := hcr
          rw [Nat.add_comm 2 (F q)] at this
          exact Nat.succ.inj (Nat.succ.inj this)
        rw [hF] at hq0
        by_cases hbq : b ≤ q
        · exact absurd (hq0.symm.trans
            (serstable.fSumC_two d a b q hbq
              (by rw [hdq]; exact Nat.lt_succ_self q)))
            (by decide +kernel)
        · exact absurd (hq0.symm.trans
            (serstable.fSumC_mid d a b q haq
              (Nat.lt_of_not_le hbq) hbd))
            (by decide +kernel)
      | .inr (.inr ⟨d, a, hld, hal, hF⟩) =>
        have hdq : d = q + 1 := Nat.succ.inj (hld.symm.trans hq.symm)
        have had : a ≤ d := Nat.le_of_lt_succ (show a < d + 1 by rw [← hld]; exact hal)
        by_cases hadq : a = d
        · refine ⟨k0, hk0l, fun hc => ?_⟩
          have hcr0 : p0 + serstable.nbC l F k0 = 2 * F k0 + q0 :=
            ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx0) hc)
          have hlo : ∀ j, j ≤ 2 → F j = 0 := fun j hj => by
            rw [hF]
            refine serstable.fLong_lo d a j ?_ had
            rw [hadq, hdq]
            exact hk0q1 j hj
          have hnb : serstable.nbC l F k0 = 0 := by
            match k0, hk01 with
            | 0, _ =>
              rw [nbHeadC l F h1l hne2l, hlo 1 (by decide +kernel)]
            | 1, _ =>
              rw [nbMidC l F 0 hne2l hne3l, hlo 0 (Nat.zero_le 2),
                hlo 2 (Nat.le_refl 2)]
            | r + 2, hcc =>
              exact absurd hcc (fun hc => Nat.not_succ_le_self 1
                (Nat.le_trans (Nat.le_add_left 2 r) hc))
          rw [hnb, hlo k0 (Nat.le_trans hk01 (Nat.le_succ 1)),
            Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hcr0
          exact hne0 hcr0
        · have han : a ≤ q := Nat.le_of_lt_succ
            (show a < q + 1 by
              rw [← hdq]; exact Nat.lt_of_le_of_ne had hadq)
          have hFt : F (q + 1) = 1 := by
            rw [hF]
            exact serstable.fLong_end d a (q + 1) hdq
          rw [hFt] at hcr
          have hq0 : F q = 0 := by
            have := hcr
            rw [Nat.add_comm 2 (F q)] at this
            exact Nat.succ.inj (Nat.succ.inj this)
          rw [hF] at hq0
          exact absurd (hq0.symm.trans
            (serstable.fLong_two d a q han
              (by rw [hdq]; exact Nat.lt_succ_self q)))
            (by decide +kernel)
    · exact ⟨q + 1, hq1l, c1⟩
  · refine ⟨q + 1, hq1l, fun c1 => ?_⟩
    have hcr : 2 + 2 * F (q + 1) = serstable.nbC l F (q + 1) + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hxt) c1)
    rw [nbTopC l F q hq, Nat.add_zero] at hcr
    have hge : 2 ≤ F q :=
      Nat.le_trans (Nat.le_add_right 2 (2 * F (q + 1))) (Nat.le_of_eq hcr)
    match hcase with
    | .inl ⟨a, b, _, _, hF⟩ =>
      rw [hF] at hge
      exact Nat.not_succ_le_self 1 (Nat.le_trans hge (serstable.fDiff_le1 a b q))
    | .inr (.inl ⟨d, a, b, hld, hab, hbl, hF⟩) =>
      have hdq : d = q + 1 := Nat.succ.inj (hld.symm.trans hq.symm)
      have hbd : b ≤ d := Nat.le_of_lt_succ (show b < d + 1 by rw [← hld]; exact hbl)
      have hFt : F (q + 1) = 1 := by
        rw [hF]
        exact serstable.fSumC_end d a b (q + 1) hbd hdq
      rw [hFt] at hcr
      have hle : F q ≤ 2 := by
        rw [hF]
        by_cases hbq : b ≤ q
        · exact Nat.le_of_eq (serstable.fSumC_two d a b q hbq
            (by rw [hdq]; exact Nat.lt_succ_self q))
        · rw [serstable.fSumC_mid d a b q
            (Nat.le_of_lt_succ (show a < q + 1 by
              rw [← hdq]; exact Nat.lt_of_lt_of_le hab hbd))
            (Nat.lt_of_not_le hbq) hbd]
          exact by decide +kernel
      exact absurd (Nat.le_trans (Nat.le_of_eq hcr)
        (show F q + 0 ≤ 2 from hle)) (by decide +kernel)
    | .inr (.inr ⟨d, a, hld, hal, hF⟩) =>
      have hdq : d = q + 1 := Nat.succ.inj (hld.symm.trans hq.symm)
      have had : a ≤ d := Nat.le_of_lt_succ (show a < d + 1 by rw [← hld]; exact hal)
      have hFt : F (q + 1) = 1 := by
        rw [hF]
        exact serstable.fLong_end d a (q + 1) hdq
      rw [hFt] at hcr
      have hle : F q ≤ 2 := by
        rw [hF]
        by_cases haq : a ≤ q
        · exact Nat.le_of_eq (serstable.fLong_two d a q haq
            (by rw [hdq]; exact Nat.lt_succ_self q))
        · rw [serstable.fLong_lo d a q (Nat.lt_of_not_le haq) had]
          exact Nat.zero_le 2
      exact absurd (Nat.le_trans (Nat.le_of_eq hcr)
        (show F q + 0 ≤ 2 from hle)) (by decide +kernel)

/-- The second-last letter's refusal at `C`: a raised content
reading plus two at the key below the last, its neighbours at the
swapped one, against a stated occupied head entry sits off the θ
list, the doubled-upper column read at the long last edge. -/
private theorem termTailSubC (l m k0 p0 q0 : Nat) (hm : m + 5 = l)
    (hk01 : k0 ≤ 1) (x : List BPair)
    (hx0 : (ground.getAt BPair.unit x k0).oneValue (BPair.ofCounts p0 q0))
    (hne0 : ¬ p0 = q0)
    (hx2 : (ground.getAt BPair.unit x (m + 2)).oneValue
      (BPair.ofCounts 0 1))
    (hx3 : (ground.getAt BPair.unit x (m + 3)).oneValue
      (BPair.ofCounts 2 0))
    (hx4 : (ground.getAt BPair.unit x (m + 4)).oneValue
      (BPair.ofCounts 0 1)) :
    row.thetaCount (sertables.tableC l) x = 0 := by
  have hm3l : m + 3 < l := by
    rw [← hm]
    exact ltPlusTwo (m + 3)
  have hm4l : m + 4 < l := by
    rw [← hm]
    exact Nat.lt_succ_self (m + 4)
  have hm2l : m + 2 < l := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
  have hk0l : k0 < l :=
    Nat.lt_of_le_of_lt hk01 (by
      rw [← hm]
      exact Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 m))
  have h1l : (1 : Nat) < l := by
    rw [← hm]
    exact Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 m)
  have hne2l : ¬ (2 : Nat) = l := by
    rw [← hm]
    exact litNe 2 m 5 (by decide +kernel)
  have hne3l : ¬ (3 : Nat) = l := by
    rw [← hm]
    exact litNe 3 m 5 (by decide +kernel)
  have hnem3 : ¬ m + 3 = l := Nat.ne_of_lt hm3l
  have hnem4 : ¬ m + 4 = l := Nat.ne_of_lt hm4l
  refine termVanishC l x
    ⟨m + 3, hm3l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm hx3) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · by_cases c1 : (ground.getAt BPair.unit x (m + 3)).oneValue
        (BPair.ofCounts (2 * F (m + 3)) (serstable.nbC l F (m + 3)))
    · have hcr : 2 + serstable.nbC l F (m + 3) = 2 * F (m + 3) + 0 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx3) c1)
      rw [nbSubC l F (m + 2) hnem4 hm] at hcr
      have hnat : 2 * F (m + 3) = F (m + 2) + 2 * F (m + 4) + 2 :=
        (Nat.add_zero (2 * F (m + 3))).symm.trans
          (hcr.symm.trans (Nat.add_comm 2 (F (m + 2) + 2 * F (m + 4))))
      match hcase with
      | .inl ⟨a, b, hab, hbl, hF⟩ =>
        have hz4 : F (m + 4) = 0 := by
          rw [hF]
          exact serstable.fDiff_hi a b (m + 4) (fun hc =>
            Nat.not_succ_le_self (m + 4)
              (Nat.le_trans (Nat.succ_le_of_lt hc)
                (Nat.le_of_lt_succ (show b < m + 5 by
                  rw [hm]; exact hbl))))
        rw [hz4] at hnat
        match ground.leOneCases (show F (m + 3) ≤ 1 from by
            rw [hF]; exact serstable.fDiff_le1 a b (m + 3)) with
        | .inl h0 =>
          rw [h0] at hnat
          exact Nat.noConfusion (show F (m + 2) + 2 * 0 + 2 = 2 * 0
            from hnat.symm)
        | .inr h1 =>
          have hz2 : F (m + 2) = 0 := by
            rw [h1] at hnat
            have h2 : F (m + 2) + 2 * 0 + 2 = 2 * 1 := hnat.symm
            exact (Nat.add_zero (F (m + 2))).symm.trans
              (Nat.succ.inj (Nat.succ.inj h2))
          rw [hF] at h1 hz2
          obtain ⟨ham3, hm3b⟩ := dIn h1
          have hnale : ¬ a ≤ m + 2 := fun ha2 =>
            absurd (hz2.symm.trans (serstable.fDiff_in a b (m + 2) ha2
              (Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3b)))
              (by decide +kernel)
          have hae : a = m + 3 :=
            Nat.le_antisymm ham3 (Nat.succ_le_of_lt (Nat.lt_of_not_le hnale))
          have hbe : b = m + 4 :=
            Nat.le_antisymm
              (Nat.le_of_lt_succ (show b < m + 5 by rw [hm]; exact hbl))
              (Nat.succ_le_of_lt hm3b)
          refine ⟨k0, hk0l, fun hc => ?_⟩
          rw [hF, hae, hbe] at hc
          have hcx : p0 + serstable.nbC l
              (serstable.fDiff (m + 3) (m + 4)) k0
              = 2 * serstable.fDiff (m + 3) (m + 4) k0 + q0 :=
            ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx0) hc)
          have hlo : ∀ j, j ≤ 2 → serstable.fDiff (m + 3) (m + 4) j = 0 :=
            fun j hj => serstable.fDiff_lo (m + 3) (m + 4) j
              (fun hcj => Nat.not_succ_le_self 2
                (Nat.le_trans (Nat.le_trans (Nat.le_add_left 3 m) hcj) hj))
          have hnb : serstable.nbC l
              (serstable.fDiff (m + 3) (m + 4)) k0 = 0 := by
            match k0, hk01 with
            | 0, _ =>
              rw [nbHeadC l _ h1l hne2l, hlo 1 (by decide +kernel)]
            | 1, _ =>
              rw [nbMidC l _ 0 hne2l hne3l, hlo 0 (Nat.zero_le 2),
                hlo 2 (Nat.le_refl 2)]
            | r + 2, hcc =>
              exact absurd hcc (fun hc => Nat.not_succ_le_self 1
                (Nat.le_trans (Nat.le_add_left 2 r) hc))
          rw [hnb, hlo k0 (Nat.le_trans hk01 (Nat.le_succ 1)),
            Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hcx
          exact hne0 hcx
      | .inr (.inl ⟨d, a, b, hld, hab, hbl, hF⟩) =>
        have hdm : d = m + 4 := Nat.succ.inj (hld.symm.trans hm.symm)
        have hbd : b ≤ d :=
          Nat.le_of_lt_succ (show b < d + 1 by rw [← hld]; exact hbl)
        have hz4 : F (m + 4) = 1 := by
          rw [hF]
          exact serstable.fSumC_end d a b (m + 4) hbd hdm
        rw [hz4] at hnat
        by_cases hb3 : b ≤ m + 3
        · have h3v : F (m + 3) = 2 := by
            rw [hF]
            exact serstable.fSumC_two d a b (m + 3) hb3
              (by rw [hdm]; exact Nat.lt_succ_self (m + 3))
          rw [h3v] at hnat
          have hz2 : F (m + 2) = 0 := by
            have h2 : F (m + 2) + 2 * 1 + 2 = 2 * 2 := hnat.symm
            exact Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
              (Nat.succ.inj h2)))
          have hnale : ¬ a ≤ m + 2 := fun ha2 => by
            by_cases hb2 : b ≤ m + 2
            · have h2v : F (m + 2) = 2 := by
                rw [hF]
                exact serstable.fSumC_two d a b (m + 2) hb2
                  (by rw [hdm]; exact ltPlusTwo (m + 2))
              exact absurd (hz2.symm.trans h2v) (by decide +kernel)
            · have h2v : F (m + 2) = 1 := by
                rw [hF]
                exact serstable.fSumC_mid d a b (m + 2) ha2
                  (Nat.lt_of_not_le hb2) hbd
              exact absurd (hz2.symm.trans h2v) (by decide +kernel)
          exact absurd (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hab hb3))
            (fun hc => hnale hc)
        · have h3v : F (m + 3) = 1 := by
            rw [hF]
            exact serstable.fSumC_mid d a b (m + 3)
              (Nat.le_of_lt_succ (show a < m + 4 by
                rw [← hdm]
                exact Nat.lt_of_lt_of_le hab hbd))
              (Nat.lt_of_not_le hb3) hbd
          rw [h3v] at hnat
          exact absurd hnat.symm (by
            intro hc
            have h2 : F (m + 2) + 2 * 1 + 2 = 2 := hc
            exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h2)))
      | .inr (.inr ⟨d, a, hld, hal, hF⟩) =>
        have hdm : d = m + 4 := Nat.succ.inj (hld.symm.trans hm.symm)
        have had : a ≤ d :=
          Nat.le_of_lt_succ (show a < d + 1 by rw [← hld]; exact hal)
        have hz4 : F (m + 4) = 1 := by
          rw [hF]
          exact serstable.fLong_end d a (m + 4) hdm
        rw [hz4] at hnat
        by_cases ha3 : a ≤ m + 3
        · have h3v : F (m + 3) = 2 := by
            rw [hF]
            exact serstable.fLong_two d a (m + 3) ha3
              (by rw [hdm]; exact Nat.lt_succ_self (m + 3))
          rw [h3v] at hnat
          have hz2 : F (m + 2) = 0 := by
            have h2 : F (m + 2) + 2 * 1 + 2 = 2 * 2 := hnat.symm
            exact Nat.succ.inj (Nat.succ.inj (Nat.succ.inj
              (Nat.succ.inj h2)))
          have hnale : ¬ a ≤ m + 2 := fun ha2 => by
            have h2v : F (m + 2) = 2 := by
              rw [hF]
              exact serstable.fLong_two d a (m + 2) ha2
                (by rw [hdm]; exact ltPlusTwo (m + 2))
            exact absurd (hz2.symm.trans h2v) (by decide +kernel)
          have hae : a = m + 3 :=
            Nat.le_antisymm ha3 (Nat.succ_le_of_lt (Nat.lt_of_not_le hnale))
          refine ⟨m + 2, hm2l, fun hc => ?_⟩
          rw [hF, hae] at hc
          have hcx : 0 + serstable.nbC l
              (serstable.fLong d (m + 3)) (m + 2)
              = 2 * serstable.fLong d (m + 3) (m + 2) + 1 :=
            ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx2) hc)
          have hgv : serstable.fLong d (m + 3) (m + 2) = 0 :=
            serstable.fLong_lo d (m + 3) (m + 2) (Nat.lt_succ_self (m + 2))
              (by rw [hdm]; exact Nat.le_succ (m + 3))
          have hnbv : serstable.nbC l (serstable.fLong d (m + 3))
              (m + 2) = 2 := by
            rw [nbMidC l _ (m + 1) hnem3 hnem4,
              serstable.fLong_lo d (m + 3) (m + 1)
                (ltPlusTwo (m + 1))
                (by rw [hdm]; exact Nat.le_succ (m + 3)),
              serstable.fLong_two d (m + 3) (m + 3) (Nat.le_refl (m + 3))
                (by rw [hdm]; exact Nat.lt_succ_self (m + 3))]
          rw [hgv, hnbv, Nat.mul_zero] at hcx
          exact absurd hcx (by decide +kernel)
        · have h3v : F (m + 3) = 0 := by
            rw [hF]
            exact serstable.fLong_lo d a (m + 3) (Nat.lt_of_not_le ha3) had
          rw [h3v] at hnat
          exact absurd hnat (by
            intro hc
            exact Nat.noConfusion (show F (m + 2) + 2 * 1 + 2 = 0 from
              hc.symm))
    · exact ⟨m + 3, hm3l, c1⟩
  · by_cases c1 : (ground.getAt BPair.unit x (m + 3)).oneValue
        (BPair.ofCounts (serstable.nbC l F (m + 3)) (2 * F (m + 3)))
    · have hcr : 2 + 2 * F (m + 3) = serstable.nbC l F (m + 3) + 0 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx3) c1)
      rw [nbSubC l F (m + 2) hnem4 hm] at hcr
      have hnat : F (m + 2) + 2 * F (m + 4) = 2 * F (m + 3) + 2 :=
        (Nat.add_zero (F (m + 2) + 2 * F (m + 4))).symm.trans
          (hcr.symm.trans (Nat.add_comm 2 (2 * F (m + 3))))
      match hcase with
      | .inl ⟨a, b, hab, hbl, hF⟩ =>
        have hz4 : F (m + 4) = 0 := by
          rw [hF]
          exact serstable.fDiff_hi a b (m + 4) (fun hc =>
            Nat.not_succ_le_self (m + 4)
              (Nat.le_trans (Nat.succ_le_of_lt hc)
                (Nat.le_of_lt_succ (show b < m + 5 by
                  rw [hm]; exact hbl))))
        rw [hz4] at hnat
        have hge : 2 ≤ F (m + 2) + 2 * 0 :=
          Nat.le_trans (Nat.le_add_left 2 (2 * F (m + 3)))
            (Nat.le_of_eq hnat.symm)
        have hle1 : F (m + 2) + 2 * 0 ≤ 1 + 2 * 0 :=
          Nat.add_le_add (show F (m + 2) ≤ 1 from by
            rw [hF]; exact serstable.fDiff_le1 a b (m + 2)) (Nat.le_refl (2 * 0))
        exact absurd (Nat.le_trans hge hle1)
          (by decide +kernel)
      | .inr (.inl ⟨d, a, b, hld, hab, hbl, hF⟩) =>
        have hdm : d = m + 4 := Nat.succ.inj (hld.symm.trans hm.symm)
        have hbd : b ≤ d :=
          Nat.le_of_lt_succ (show b < d + 1 by rw [← hld]; exact hbl)
        have hz4 : F (m + 4) = 1 := by
          rw [hF]
          exact serstable.fSumC_end d a b (m + 4) hbd hdm
        rw [hz4] at hnat
        have heq : F (m + 2) = 2 * F (m + 3) := by
          have h2 : F (m + 2) + 2 = 2 * F (m + 3) + 2 := hnat
          exact Nat.succ.inj (Nat.succ.inj h2)
        by_cases hb3 : b ≤ m + 3
        · have h3v : F (m + 3) = 2 := by
            rw [hF]
            exact serstable.fSumC_two d a b (m + 3) hb3
              (by rw [hdm]; exact Nat.lt_succ_self (m + 3))
          have hle2 : F (m + 2) ≤ 2 := by
            rw [hF]
            by_cases hb2 : b ≤ m + 2
            · exact Nat.le_of_eq (serstable.fSumC_two d a b (m + 2) hb2
                (by rw [hdm]; exact ltPlusTwo (m + 2)))
            · by_cases ha2 : a ≤ m + 2
              · rw [serstable.fSumC_mid d a b (m + 2) ha2
                  (Nat.lt_of_not_le hb2) hbd]
                exact by decide +kernel
              · rw [serstable.fSumC_lo d a b (m + 2)
                  (Nat.lt_of_not_le ha2) hab hbd]
                exact Nat.zero_le 2
          rw [h3v] at heq
          rw [heq] at hle2
          exact absurd hle2 (by decide +kernel)
        · have h3v : F (m + 3) = 1 := by
            rw [hF]
            exact serstable.fSumC_mid d a b (m + 3)
              (Nat.le_of_lt_succ (show a < m + 4 by
                rw [← hdm]
                exact Nat.lt_of_lt_of_le hab hbd))
              (Nat.lt_of_not_le hb3) hbd
          rw [h3v] at heq
          have h2v : F (m + 2) = 2 := heq
          rw [hF] at h2v
          by_cases hb2 : b ≤ m + 2
          · exact absurd (Nat.le_trans hb2 (Nat.le_succ (m + 2))) hb3
          · by_cases ha2 : a ≤ m + 2
            · exact absurd ((serstable.fSumC_mid d a b (m + 2) ha2
                (Nat.lt_of_not_le hb2) hbd).symm.trans h2v)
                (by decide +kernel)
            · exact absurd ((serstable.fSumC_lo d a b (m + 2)
                (Nat.lt_of_not_le ha2) hab hbd).symm.trans h2v)
                (by decide +kernel)
      | .inr (.inr ⟨d, a, hld, hal, hF⟩) =>
        have hdm : d = m + 4 := Nat.succ.inj (hld.symm.trans hm.symm)
        have had : a ≤ d :=
          Nat.le_of_lt_succ (show a < d + 1 by rw [← hld]; exact hal)
        have hz4 : F (m + 4) = 1 := by
          rw [hF]
          exact serstable.fLong_end d a (m + 4) hdm
        rw [hz4] at hnat
        have heq : F (m + 2) = 2 * F (m + 3) := by
          have h2 : F (m + 2) + 2 = 2 * F (m + 3) + 2 := hnat
          exact Nat.succ.inj (Nat.succ.inj h2)
        by_cases ha3 : a ≤ m + 3
        · have h3v : F (m + 3) = 2 := by
            rw [hF]
            exact serstable.fLong_two d a (m + 3) ha3
              (by rw [hdm]; exact Nat.lt_succ_self (m + 3))
          have hle2 : F (m + 2) ≤ 2 := by
            rw [hF]
            by_cases ha2 : a ≤ m + 2
            · exact Nat.le_of_eq (serstable.fLong_two d a (m + 2) ha2
                (by rw [hdm]; exact ltPlusTwo (m + 2)))
            · rw [serstable.fLong_lo d a (m + 2)
                (Nat.lt_of_not_le ha2) had]
              exact Nat.zero_le 2
          rw [h3v] at heq
          rw [heq] at hle2
          exact absurd hle2 (by decide +kernel)
        · refine ⟨m + 4, hm4l, fun hc => ?_⟩
          have hae : a = d :=
            Nat.le_antisymm had (by
              rw [hdm]
              exact Nat.succ_le_of_lt (Nat.lt_of_not_le ha3))
          have hcx : 0 + 2 * F (m + 4)
              = serstable.nbC l F (m + 4) + 1 :=
            ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx4) hc)
          have hnbv : serstable.nbC l F (m + 4) = 0 := by
            rw [nbTopC l F (m + 3) hm, hF]
            exact serstable.fLong_lo d a (m + 3)
              (by rw [hae, hdm]; exact Nat.lt_succ_self (m + 3)) had
          rw [hz4, hnbv] at hcx
          exact absurd hcx (by decide +kernel)
    · exact ⟨m + 3, hm3l, c1⟩

/-! ### The `C` stray edges' hit letters -/

/-- The raised content's count reads before the representative:
the moved content's counts against the scaled Cartan entry's. -/
private theorem rawAtC (l : Nat) (u v : Nat → Nat) (c i y : Nat)
    (hi : i < l) (hy : y < l) (p q : Nat)
    (hcart : (serstable.cartC l i y).oneValue (BPair.ofCounts p q)) :
    (ground.getAt BPair.unit
      (elim.vecAdd (nuOf l (fun k => BPair.ofCounts (u k) (v k)))
        (elim.vecScale (BPair.ofNat c)
          (ground.getAt [] (sertables.tableC l).cartan i))) y).oneValue
      (BPair.ofCounts (u y + c * p) (v y + c * q)) := by
  have hcl : (ground.getAt [] (sertables.tableC l).cartan i).length = l := by
    rw [serstable.cartC_eq l]
    exact ground.matOf_rowLength [] l l (fun p q => serstable.cartC l p q) i hi
  have hsl : (elim.vecScale (BPair.ofNat c)
      (ground.getAt [] (sertables.tableC l).cartan i)).length = l := by
    rw [elim.length_vecScale]
    exact hcl
  have hcent : ground.getAt BPair.unit
      (ground.getAt [] (sertables.tableC l).cartan i) y
      = serstable.cartC l i y := by
    rw [serstable.cartC_eq l]
    exact ground.matOf_entry [] BPair.unit l l
      (fun p q => serstable.cartC l p q) i y hi hy
  rw [elim.getAt_vecAdd _ _ y (by rw [nuOf_length]; exact hy)
      (by rw [hsl]; exact hy),
    elim.getAt_vecScale _ _ y (by rw [hcl]; exact hy), hcent,
    nuOf_entry l _ y hy]
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.norm_oneValue _)
      (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hcart)
        (mulCounts c p q)))
    (BPair.oneValue_symm (BPair.ofCounts_add (u y) (v y) (c * p) (c * q)))

/-- The collision's hit letter at `e₂ + e₃`: the raised content is
the long dipole at the second coordinate, one θ count. -/
private theorem hitLongOne (k : Nat) :
    row.thetaCount (sertables.tableC (k + 6))
      (raisedG (sertables.tableC (k + 6)) (cE (k + 6)) 1 1) = 1 := by
  have h1l : (1 : Nat) < k + 6 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
  have hne2l : ¬ (2 : Nat) = k + 6 := litNe 2 k 6 (by decide +kernel)
  have hne3l : ¬ (3 : Nat) = k + 6 := litNe 3 k 6 (by decide +kernel)
  have h1d : (1 : Nat) < k + 5 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)
  have h2d : (2 : Nat) < k + 5 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)
  have h3d : (3 : Nat) < k + 5 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)
  have hlen : (elim.vecAdd (cE (k + 6))
      (elim.vecScale (BPair.ofNat 1)
        (ground.getAt [] (sertables.tableC (k + 6)).cartan 1))).length
      = k + 6 := by
    refine elim.length_vecAdd _ _ (k + 6) (nuOf_length _ _) ?_
    rw [elim.length_vecScale, serstable.cartC_eq (k + 6)]
    exact ground.matOf_rowLength [] (k + 6) (k + 6)
      (fun p q => serstable.cartC (k + 6) p q) 1 h1l
  refine thetaOneNormC (k + 6) (serstable.fLong (k + 5) 1) _ hlen
    (memLongC (k + 5) 1 h1l) (fun y hy => ?_) 1 h1l
    (fun hc => absurd (BPair.ofCounts_unit.mp (BPair.oneValue_trans
      (BPair.oneValue_symm (rawAtC (k + 6) _ _ 1 1 1 h1l h1l 2 0
        (cartDiagC (k + 6) 1))) hc)) (by decide +kernel))
  match y, hy with
  | 0, _ =>
    refine BPair.oneValue_trans (rawAtC (k + 6) _ _ 1 1 0 h1l
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)) 0 1
      (cartDn1C (k + 6) 0 hne2l)) (BPair.ofCounts_crossed ?_)
    rw [nbHeadC (k + 6) _ h1l hne2l,
      serstable.fLong_two (k + 5) 1 1 (Nat.le_refl 1) h1d,
      serstable.fLong_lo (k + 5) 1 0 (Nat.lt_succ_self 0)
        (Nat.le_add_left 1 (k + 4))]
    decide +kernel
  | 1, _ =>
    refine BPair.oneValue_trans (rawAtC (k + 6) _ _ 1 1 1 h1l h1l 2 0
      (cartDiagC (k + 6) 1)) (BPair.ofCounts_crossed ?_)
    rw [nbMidC (k + 6) _ 0 hne2l hne3l,
      serstable.fLong_lo (k + 5) 1 0 (Nat.lt_succ_self 0)
        (Nat.le_add_left 1 (k + 4)),
      serstable.fLong_two (k + 5) 1 2 (by decide +kernel) h2d,
      serstable.fLong_two (k + 5) 1 1 (Nat.le_refl 1) h1d]
    decide +kernel
  | 2, _ =>
    refine BPair.oneValue_trans (rawAtC (k + 6) _ _ 1 1 2 h1l
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)) 0 1
      (cartUpC (k + 6) 1)) (BPair.ofCounts_crossed ?_)
    rw [nbMidC (k + 6) _ 1 hne3l (litNe 4 k 6 (by decide +kernel)),
      serstable.fLong_two (k + 5) 1 1 (Nat.le_refl 1) h1d,
      serstable.fLong_two (k + 5) 1 3 (by decide +kernel) h3d,
      serstable.fLong_two (k + 5) 1 2 (by decide +kernel) h2d]
    decide +kernel
  | m + 3, hy =>
    refine BPair.oneValue_trans (rawAtC (k + 6) _ _ 1 1 (m + 3) h1l hy 0 0
      (cartOffC (k + 6) 1 (m + 3)
        (fun hc => Nat.noConfusion (Nat.succ.inj hc))
        (fun hc => Nat.noConfusion (Nat.succ.inj hc))
        (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))))
      (BPair.ofCounts_crossed ?_)
    by_cases ht : m + 4 = k + 6
    · have hmd : k + 5 = m + 3 := (Nat.succ.inj ht).symm
      rw [if_neg (sucNe2 m), if_neg (sucNe0 (m + 2)),
        nbTopC (k + 6) _ (m + 2) ht,
        serstable.fLong_end (k + 5) 1 (m + 3) hmd,
        serstable.fLong_two (k + 5) 1 (m + 2) (Nat.le_add_left 1 (m + 1))
          (by rw [hmd]; exact Nat.lt_succ_self (m + 2))]
    · by_cases hs : m + 5 = k + 6
      · have hmd : k + 5 = m + 4 := (Nat.succ.inj hs).symm
        rw [if_neg (sucNe2 m), if_neg (sucNe0 (m + 2)),
          nbSubC (k + 6) _ (m + 2) ht hs,
          serstable.fLong_end (k + 5) 1 (m + 4) hmd,
          serstable.fLong_two (k + 5) 1 (m + 2) (Nat.le_add_left 1 (m + 1))
            (by rw [hmd]; exact ltPlusTwo (m + 2)),
          serstable.fLong_two (k + 5) 1 (m + 3) (Nat.le_add_left 1 (m + 2))
            (by rw [hmd]; exact Nat.lt_succ_self (m + 3))]
      · have hm5 : m + 5 < k + 6 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt
            (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hy) ht)) hs
        have h4d : m + 4 < k + 5 := Nat.lt_of_succ_lt_succ hm5
        have h3dm : m + 3 < k + 5 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 3)) h4d
        have h2dm : m + 2 < k + 5 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 2)) h3dm
        rw [if_neg (sucNe2 m), if_neg (sucNe0 (m + 2)),
          nbMidC (k + 6) _ (m + 2) ht hs,
          serstable.fLong_two (k + 5) 1 (m + 2)
            (Nat.le_add_left 1 (m + 1)) h2dm,
          serstable.fLong_two (k + 5) 1 (m + 3)
            (Nat.le_add_left 1 (m + 2)) h3dm,
          serstable.fLong_two (k + 5) 1 (m + 4)
            (Nat.le_add_left 1 (m + 3)) h4d]

/-- The collision's hit letter at `e₃ + e₄`: the raised content is
the long dipole at the third coordinate, one θ count. -/
private theorem hitLongTwo (k : Nat) :
    row.thetaCount (sertables.tableC (k + 7))
      (raisedG (sertables.tableC (k + 7)) (cG (k + 7)) 1 2) = 1 := by
  have h2l : (2 : Nat) < k + 7 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
  have hne2l : ¬ (2 : Nat) = k + 7 := litNe 2 k 7 (by decide +kernel)
  have hne3l : ¬ (3 : Nat) = k + 7 := litNe 3 k 7 (by decide +kernel)
  have hne4l : ¬ (4 : Nat) = k + 7 := litNe 4 k 7 (by decide +kernel)
  have hne5l : ¬ (5 : Nat) = k + 7 := litNe 5 k 7 (by decide +kernel)
  have h2d : (2 : Nat) < k + 6 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
  have h3d : (3 : Nat) < k + 6 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
  have h4d : (4 : Nat) < k + 6 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
  have hlen : (elim.vecAdd (cG (k + 7))
      (elim.vecScale (BPair.ofNat 1)
        (ground.getAt [] (sertables.tableC (k + 7)).cartan 2))).length
      = k + 7 := by
    refine elim.length_vecAdd _ _ (k + 7) (nuOf_length _ _) ?_
    rw [elim.length_vecScale, serstable.cartC_eq (k + 7)]
    exact ground.matOf_rowLength [] (k + 7) (k + 7)
      (fun p q => serstable.cartC (k + 7) p q) 2 h2l
  refine thetaOneNormC (k + 7) (serstable.fLong (k + 6) 2) _ hlen
    (memLongC (k + 6) 2 h2l) (fun y hy => ?_) 2 h2l
    (fun hc => absurd (BPair.ofCounts_unit.mp (BPair.oneValue_trans
      (BPair.oneValue_symm (rawAtC (k + 7) _ _ 1 2 2 h2l h2l 2 0
        (cartDiagC (k + 7) 2))) hc)) (by decide +kernel))
  match y, hy with
  | 0, _ =>
    refine BPair.oneValue_trans (rawAtC (k + 7) _ _ 1 2 0 h2l
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)) 0 0
      (cartOffC (k + 7) 2 0 (fun hc => Nat.noConfusion hc)
        (fun hc => Nat.noConfusion (Nat.succ.inj hc))
        (fun hc => Nat.noConfusion hc))) (BPair.ofCounts_crossed ?_)
    rw [nbHeadC (k + 7) _ (Nat.lt_of_lt_of_le (by decide +kernel)
        (Nat.le_add_left 7 k)) hne2l,
      serstable.fLong_lo (k + 6) 2 1 (Nat.lt_succ_self 1)
        (Nat.le_add_left 2 (k + 4)),
      serstable.fLong_lo (k + 6) 2 0 (Nat.zero_lt_succ 1)
        (Nat.le_add_left 2 (k + 4))]
    decide +kernel
  | 1, _ =>
    refine BPair.oneValue_trans (rawAtC (k + 7) _ _ 1 2 1 h2l
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)) 0 1
      (cartDn1C (k + 7) 1 hne3l)) (BPair.ofCounts_crossed ?_)
    rw [nbMidC (k + 7) _ 0 hne2l hne3l,
      serstable.fLong_lo (k + 6) 2 0 (Nat.zero_lt_succ 1)
        (Nat.le_add_left 2 (k + 4)),
      serstable.fLong_two (k + 6) 2 2 (Nat.le_refl 2) h2d,
      serstable.fLong_lo (k + 6) 2 1 (Nat.lt_succ_self 1)
        (Nat.le_add_left 2 (k + 4))]
    decide +kernel
  | 2, _ =>
    refine BPair.oneValue_trans (rawAtC (k + 7) _ _ 1 2 2 h2l h2l 2 0
      (cartDiagC (k + 7) 2)) (BPair.ofCounts_crossed ?_)
    rw [nbMidC (k + 7) _ 1 hne3l hne4l,
      serstable.fLong_lo (k + 6) 2 1 (Nat.lt_succ_self 1)
        (Nat.le_add_left 2 (k + 4)),
      serstable.fLong_two (k + 6) 2 3 (by decide +kernel) h3d,
      serstable.fLong_two (k + 6) 2 2 (Nat.le_refl 2) h2d]
    decide +kernel
  | 3, _ =>
    refine BPair.oneValue_trans (rawAtC (k + 7) _ _ 1 2 3 h2l
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)) 0 1
      (cartUpC (k + 7) 2)) (BPair.ofCounts_crossed ?_)
    rw [nbMidC (k + 7) _ 2 hne4l hne5l,
      serstable.fLong_two (k + 6) 2 2 (Nat.le_refl 2) h2d,
      serstable.fLong_two (k + 6) 2 4 (by decide +kernel) h4d,
      serstable.fLong_two (k + 6) 2 3 (by decide +kernel) h3d]
    decide +kernel
  | m + 4, hy =>
    refine BPair.oneValue_trans (rawAtC (k + 7) _ _ 1 2 (m + 4) h2l hy 0 0
      (cartOffC (k + 7) 2 (m + 4)
        (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))
        (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))
        (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj
          (Nat.succ.inj hc))))))
      (BPair.ofCounts_crossed ?_)
    by_cases ht : m + 5 = k + 7
    · have hmd : k + 6 = m + 4 := (Nat.succ.inj ht).symm
      rw [if_neg (sucNe3 m),
        if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
        nbTopC (k + 7) _ (m + 3) ht,
        serstable.fLong_end (k + 6) 2 (m + 4) hmd,
        serstable.fLong_two (k + 6) 2 (m + 3) (Nat.le_add_left 2 (m + 1))
          (by rw [hmd]; exact Nat.lt_succ_self (m + 3))]
    · by_cases hs : m + 6 = k + 7
      · have hmd : k + 6 = m + 5 := (Nat.succ.inj hs).symm
        rw [if_neg (sucNe3 m),
          if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
          nbSubC (k + 7) _ (m + 3) ht hs,
          serstable.fLong_end (k + 6) 2 (m + 5) hmd,
          serstable.fLong_two (k + 6) 2 (m + 3) (Nat.le_add_left 2 (m + 1))
            (by rw [hmd]; exact ltPlusTwo (m + 3)),
          serstable.fLong_two (k + 6) 2 (m + 4) (Nat.le_add_left 2 (m + 2))
            (by rw [hmd]; exact Nat.lt_succ_self (m + 4))]
      · have hm6 : m + 6 < k + 7 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt
            (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hy) ht)) hs
        have h5d : m + 5 < k + 6 := Nat.lt_of_succ_lt_succ hm6
        have h4dm : m + 4 < k + 6 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 4)) h5d
        have h3dm : m + 3 < k + 6 :=
          Nat.lt_trans (Nat.lt_succ_self (m + 3)) h4dm
        rw [if_neg (sucNe3 m),
          if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
          nbMidC (k + 7) _ (m + 3) ht hs,
          serstable.fLong_two (k + 6) 2 (m + 3)
            (Nat.le_add_left 2 (m + 1)) h3dm,
          serstable.fLong_two (k + 6) 2 (m + 4)
            (Nat.le_add_left 2 (m + 2)) h4dm,
          serstable.fLong_two (k + 6) 2 (m + 5)
            (Nat.le_add_left 2 (m + 3)) h5d]

/-- The unit sector's collision at `θ + (e₂ + e₃)`: the letter fold
is occupied, the long dipole the hit, the tex's `C` collision
clause (`lem:serdivisors`). -/
theorem strayC_u1 (l : Nat) (hl : 3 ≤ l) :
    1 ≤ serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [2] l) (cE l) := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 =>
    refine foldOneAtG (sertables.tableC 3) 1 (by decide +kernel)
      _ (cE 3) ?_
    decide +kernel
  | 1 =>
    refine foldOneAtG (sertables.tableC 4) 1 (by decide +kernel)
      _ (cE 4) ?_
    decide +kernel
  | 2 =>
    refine foldOneAtG (sertables.tableC 5) 1 (by decide +kernel)
      _ (cE 5) ?_
    decide +kernel
  | k + 3 =>
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldOneAtG (sertables.tableC (k + 6)) 1 h1l _ (cE (k + 6)) ?_
    rw [kapW2 (k + 6) 1 (Nat.le_refl 1) h1l]
    exact hitLongOne k

/-- The charged sector's collision at `ω₁ + (e₂ + e₃)`: the direct
route to `(1,1,1)` is vacant, the word entering at the second
fusion (`lem:serdivisors`). -/
theorem strayC_w1 (l : Nat) (hl : 3 ≤ l) :
    1 ≤ serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [1] l) (cE l) := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 =>
    refine foldOneAtG (sertables.tableC 3) 1 (by decide +kernel)
      _ (cE 3) ?_
    decide +kernel
  | 1 =>
    refine foldOneAtG (sertables.tableC 4) 1 (by decide +kernel)
      _ (cE 4) ?_
    decide +kernel
  | 2 =>
    refine foldOneAtG (sertables.tableC 5) 1 (by decide +kernel)
      _ (cE 5) ?_
    decide +kernel
  | k + 3 =>
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldOneAtG (sertables.tableC (k + 6)) 1 h1l _ (cE (k + 6)) ?_
    rw [kapW1 (k + 6) 1 (Nat.le_refl 1) h1l]
    exact hitLongOne k

/-- The charged sector's further collision at `(2,1) + (e₃ + e₄)`:
the letter fold is occupied at the long dipole two coordinates
in. -/
theorem strayC_w2 (l : Nat) (hl : 4 ≤ l) :
    1 ≤ serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [2, 1] l) (cG l) := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 =>
    refine foldOneAtG (sertables.tableC 4) 2 (by decide +kernel)
      _ (cG 4) ?_
    decide +kernel
  | 1 =>
    refine foldOneAtG (sertables.tableC 5) 2 (by decide +kernel)
      _ (cG 5) ?_
    decide +kernel
  | 2 =>
    refine foldOneAtG (sertables.tableC 6) 2 (by decide +kernel)
      _ (cG 6) ?_
    decide +kernel
  | k + 3 =>
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    refine foldOneAtG (sertables.tableC (k + 7)) 2 h2l _ (cG (k + 7)) ?_
    rw [kapW21 (k + 7) 2 (Nat.le_refl 2) h2l]
    exact hitLongTwo k

/-- The one-row cube's vacant route at `(3) + (e₂ + e₃)`: the
collision closes the route, the family entering through the
two-row source. -/
theorem strayC_w3 (l : Nat) (hl : 3 ≤ l) :
    1 ≤ serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [3] l) (cE l) := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 =>
    refine foldOneAtG (sertables.tableC 3) 1 (by decide +kernel)
      _ (cE 3) ?_
    decide +kernel
  | 1 =>
    refine foldOneAtG (sertables.tableC 4) 1 (by decide +kernel)
      _ (cE 4) ?_
    decide +kernel
  | 2 =>
    refine foldOneAtG (sertables.tableC 5) 1 (by decide +kernel)
      _ (cE 5) ?_
    decide +kernel
  | k + 3 =>
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldOneAtG (sertables.tableC (k + 6)) 1 h1l _ (cE (k + 6)) ?_
    rw [kapW3 (k + 6) 1 (Nat.le_refl 1) h1l]
    exact hitLongOne k

/-! ### The `C` witness edges: the displayed families' vacant
folds -/

/-- A key at or below one sits off every key past a stated
floor. -/
private theorem neSmallBig (k0 c k : Nat) (hk0 : k0 + 1 ≤ c) :
    ¬ k0 = k + c := fun hc =>
  Nat.not_succ_le_self k0 (Nat.le_trans (Nat.le_trans hk0
    (Nat.le_add_left c k)) (Nat.le_of_eq hc.symm))

/-- The second-last letter's vacant term at a builder vacant on
the rank's last three keys. -/
private theorem tailSubAt (k k0 : Nat) (hk01 : k0 ≤ 1) (u v : Nat → Nat)
    (hu2 : u (k + 3) = 0) (hv2 : v (k + 3) = 0)
    (hu3 : u (k + 4) = 0) (hv3 : v (k + 4) = 0)
    (hu4 : u (k + 5) = 0) (hv4 : v (k + 5) = 0)
    (hne0 : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableC (k + 6))
      (raisedG (sertables.tableC (k + 6))
        (nuOf (k + 6) (fun i => BPair.ofCounts (u i) (v i)))
        1 (k + 4)) = 0 := by
  have h4l : k + 4 < k + 6 := ltPlusTwo (k + 4)
  have h5l : k + 5 < k + 6 := Nat.lt_succ_self (k + 5)
  have h3l : k + 3 < k + 6 := Nat.lt_trans (Nat.lt_succ_self (k + 3)) h4l
  have hk0l : k0 < k + 6 :=
    Nat.lt_of_le_of_lt hk01
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k))
  refine termTailSubC (k + 6) (k + 1) k0 (u k0) (v k0) rfl hk01 _
    ?_ hne0 ?_ ?_ ?_
  · refine BPair.oneValue_trans (raisedCountC (k + 6) u v 1 (k + 4) k0
      h4l hk0l 0 0 (cartOffC (k + 6) (k + 4) k0
        (neSmallBig k0 4 k (Nat.le_trans (Nat.succ_le_succ hk01)
          (by decide +kernel)))
        (neSmallBig (k0 + 1) 4 k (Nat.le_trans (Nat.succ_le_succ
          (Nat.succ_le_succ hk01)) (by decide +kernel)))
        (neSmallBig k0 5 k (Nat.le_trans (Nat.succ_le_succ hk01)
          (by decide +kernel)))))
      (BPair.ofCounts_crossed ?_)
    rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  · refine BPair.oneValue_trans (raisedCountC (k + 6) u v 1 (k + 4) (k + 3)
      h4l h3l 0 1 (cartDn1C (k + 6) (k + 3)
        (Nat.ne_of_lt (Nat.lt_succ_self (k + 5)))))
      (BPair.ofCounts_crossed ?_)
    rw [hu2, hv2]
  · refine BPair.oneValue_trans (raisedCountC (k + 6) u v 1 (k + 4) (k + 4)
      h4l h4l 2 0 (cartDiagC (k + 6) (k + 4)))
      (BPair.ofCounts_crossed ?_)
    rw [hu3, hv3]
  · refine BPair.oneValue_trans (raisedCountC (k + 6) u v 1 (k + 4) (k + 5)
      h4l h5l 0 1 (cartUpC (k + 6) (k + 4)))
      (BPair.ofCounts_crossed ?_)
    rw [hu4, hv4]

/-- The last letter's vacant term at a builder vacant on the
rank's last key. -/
private theorem tailTopAt (k k0 : Nat) (hk01 : k0 ≤ 1) (u v : Nat → Nat)
    (hu5 : u (k + 5) = 0) (hv5 : v (k + 5) = 0)
    (hne0 : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableC (k + 6))
      (raisedG (sertables.tableC (k + 6))
        (nuOf (k + 6) (fun i => BPair.ofCounts (u i) (v i)))
        1 (k + 5)) = 0 := by
  have h5l : k + 5 < k + 6 := Nat.lt_succ_self (k + 5)
  have hk0l : k0 < k + 6 :=
    Nat.lt_of_le_of_lt hk01
      (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k))
  refine termTailTopC (k + 6) (k + 4) k0 (u k0) (v k0) rfl
    (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hk01 _
    ?_ hne0 ?_
  · refine BPair.oneValue_trans (raisedCountC (k + 6) u v 1 (k + 5) k0
      h5l hk0l 0 0 (cartOffC (k + 6) (k + 5) k0
        (neSmallBig k0 5 k (Nat.le_trans (Nat.succ_le_succ hk01)
          (by decide +kernel)))
        (neSmallBig (k0 + 1) 5 k (Nat.le_trans (Nat.succ_le_succ
          (Nat.succ_le_succ hk01)) (by decide +kernel)))
        (neSmallBig k0 6 k (Nat.le_trans (Nat.succ_le_succ hk01)
          (by decide +kernel)))))
      (BPair.ofCounts_crossed ?_)
    rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  · refine BPair.oneValue_trans (raisedCountC (k + 6) u v 1 (k + 5) (k + 5)
      h5l h5l 2 0 (cartDiagC (k + 6) (k + 5)))
      (BPair.ofCounts_crossed ?_)
    rw [hu5, hv5]

/-- The unit sector's witness edge at `θ + (e₂ − e₁)`, the target `(1,1)` -/
theorem edgeC_u1 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [2] l) (cD l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 1 (k + 3) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 1 + (k + 3) + 2; rw [Nat.add_comm 1 (k + 3)])
      (by rw [Nat.add_comm 1 (k + 3)])
      (serstable.memberRho [2] (k + 6)) (cD (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW2_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun j => if j = 0 then 2 else 0) 3 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | r + 1, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 1 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW2 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 =>
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun j => if j = 0 then 2 else 0) 1 1 0 h1l h0l 0 1
            (cartDn1C (k + 6) 0 (litNe 2 k 6 (by decide +kernel))))
          (Or.inr (by decide +kernel))
      | r + 1 =>
        refine serstable.runVanishC (k + 6) (r + 1) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun j => if j = 0 then 2 else 0) (r + 2) hm1l
            (by rw [if_neg (sucNe1 r), if_neg (sucNe0 (r + 1))]))
          0 h0l (Or.inl (Nat.succ_pos r)) 
          (nuOcc (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun j => if j = 0 then 2 else 0) 0 h0l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW2 (k + 6) (k + 4) (Nat.le_add_left 1 (k + 3)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 0 (by decide +kernel) (fun j => if j = 1 then 1 else 0)
          (fun j => if j = 0 then 2 else 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 2))) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 3)))
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 4))) (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW2 (k + 6) (k + 5) (Nat.le_add_left 1 (k + 4)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 0 (by decide +kernel) (fun j => if j = 1 then 1 else 0)
          (fun j => if j = 0 then 2 else 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 4))) (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The unit sector's witness edge at `θ + 2e₂`, the target `(2,2)` -/
theorem edgeC_u2 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [2] l) (cB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 1 (k + 3) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 1 + (k + 3) + 2; rw [Nat.add_comm 1 (k + 3)])
      (by rw [Nat.add_comm 1 (k + 3)])
      (serstable.memberRho [2] (k + 6)) (cB (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW2_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 2 else 0)
            (fun j => if j = 0 then 2 else 0) 3 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | r + 1, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 1 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW2 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 =>
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 2 else 0)
            (fun j => if j = 0 then 2 else 0) 1 1 0 h1l h0l 0 1
            (cartDn1C (k + 6) 0 (litNe 2 k 6 (by decide +kernel))))
          (Or.inr (by decide +kernel))
      | r + 1 =>
        refine serstable.runVanishC (k + 6) (r + 1) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 1 then 2 else 0)
            (fun j => if j = 0 then 2 else 0) (r + 2) hm1l
            (by rw [if_neg (sucNe1 r), if_neg (sucNe0 (r + 1))]))
          0 h0l (Or.inl (Nat.succ_pos r)) 
          (nuOcc (k + 6) (fun j => if j = 1 then 2 else 0)
            (fun j => if j = 0 then 2 else 0) 0 h0l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW2 (k + 6) (k + 4) (Nat.le_add_left 1 (k + 3)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 0 (by decide +kernel) (fun j => if j = 1 then 2 else 0)
          (fun j => if j = 0 then 2 else 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 2))) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 3)))
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 4))) (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW2 (k + 6) (k + 5) (Nat.le_add_left 1 (k + 4)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 0 (by decide +kernel) (fun j => if j = 1 then 2 else 0)
          (fun j => if j = 0 then 2 else 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 4))) (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The unit sector's witness edge at `θ + (e₁ + e₂)`, the target `(3,1)` -/
theorem edgeC_u3 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [2] l) (cA l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 1 (k + 3) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 1 + (k + 3) + 2; rw [Nat.add_comm 1 (k + 3)])
      (by rw [Nat.add_comm 1 (k + 3)])
      (serstable.memberRho [2] (k + 6)) (cA (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW2_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 3 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | r + 1, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 1 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW2 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 =>
        exact termVanishMagC (k + 6) 1 h1l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 1 1 1 h1l h1l 2 0 (cartDiagC (k + 6) 1))
          (Or.inl (by decide +kernel))
      | 1 =>
        refine termVanishTwoC (k + 6) 1
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) _
          (BPair.oneValue_trans (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 1 2 2 h2l h2l 2 0 (cartDiagC (k + 6) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          ⟨1, h1l, fun hc => ?_⟩ (fun d hld => ?_) (fun d hld => ?_)
        · have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
              (fun _ => 0) 1 2 1 h2l h1l 0 1
              (cartDn1C (k + 6) 1 (litNe 3 k 6 (by decide +kernel))))) hc)
          rw [nbMidC (k + 6) _ 0 (litNe 2 k 6 (by decide +kernel))
              (litNe 3 k 6 (by decide +kernel)),
            serstable.fDiff_lo 2 3 0 (by decide +kernel),
            serstable.fDiff_in 2 3 2 (Nat.le_refl 2) (Nat.lt_succ_self 2),
            serstable.fDiff_lo 2 3 1 (by decide +kernel)] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨1, h1l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
              (fun _ => 0) 1 2 1 h2l h1l 0 1
              (cartDn1C (k + 6) 1 (litNe 3 k 6 (by decide +kernel))))) hc)
          rw [nbMidC (k + 6) _ 0 (litNe 2 k 6 (by decide +kernel))
              (litNe 3 k 6 (by decide +kernel)),
            serstable.fLong_lo (k + 5) 2 0 (by decide +kernel)
              (Nat.le_add_left 2 (k + 3)),
            serstable.fLong_two (k + 5) 2 2 (Nat.le_refl 2)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 2 1 (Nat.lt_succ_self 1)
              (Nat.le_add_left 2 (k + 3))] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨3, h3l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
              (fun _ => 0) 1 2 3 h2l h3l 0 1 (cartUpC (k + 6) 2))) hc)
          rw [nbMidC (k + 6) _ 2 (litNe 4 k 6 (by decide +kernel))
              (litNe 5 k 6 (by decide +kernel)),
            serstable.fLong_two (k + 5) 3 3 (Nat.le_refl 3)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 3 2 (Nat.lt_succ_self 2)
              (Nat.le_add_left 3 (k + 2)),
            serstable.fLong_two (k + 5) 3 4 (by decide +kernel)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k))]
            at hcx
          exact absurd hcx (by decide +kernel)
      | r + 2 =>
        refine serstable.runVanishC (k + 6) (r + 2) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) (r + 3) hm1l
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]))
          1 h1l (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 2 r))) 
          (nuOcc (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW2 (k + 6) (k + 4) (Nat.le_add_left 1 (k + 3)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 1 (by decide +kernel) (fun j => if j = 1 then 1 else 0)
          (fun _ => 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW2 (k + 6) (k + 5) (Nat.le_add_left 1 (k + 4)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 1 (by decide +kernel) (fun j => if j = 1 then 1 else 0)
          (fun _ => 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The unit sector's witness edge at `θ + 2e₁`, the target `(4)` -/
theorem edgeC_u4 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [2] l) (cC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | k + 3 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 1 (k + 3) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 1 + (k + 3) + 2; rw [Nat.add_comm 1 (k + 3)])
      (by rw [Nat.add_comm 1 (k + 3)])
      (serstable.memberRho [2] (k + 6)) (cC (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW2_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) 3 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | r + 1, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 1 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW2 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 =>
        refine termVanishTwoC (k + 6) 0
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) _
          (BPair.oneValue_trans (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) 1 1 1 h1l h1l 2 0 (cartDiagC (k + 6) 1))
            (BPair.ofCounts_crossed (by decide +kernel)))
          ⟨0, h0l, fun hc => ?_⟩ (fun d hld => ?_) (fun d hld => ?_)
        · have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
              (fun _ => 0) 1 1 0 h1l h0l 0 1
              (cartDn1C (k + 6) 0 (litNe 2 k 6 (by decide +kernel))))) hc)
          rw [nbHeadC (k + 6) _ h1l (litNe 2 k 6 (by decide +kernel)),
            serstable.fDiff_in 1 2 1 (Nat.le_refl 1) (Nat.lt_succ_self 1),
            serstable.fDiff_lo 1 2 0 (by decide +kernel)] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨0, h0l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
              (fun _ => 0) 1 1 0 h1l h0l 0 1
              (cartDn1C (k + 6) 0 (litNe 2 k 6 (by decide +kernel))))) hc)
          rw [nbHeadC (k + 6) _ h1l (litNe 2 k 6 (by decide +kernel)),
            serstable.fLong_two (k + 5) 1 1 (Nat.le_refl 1)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 1 0 (Nat.lt_succ_self 0)
              (Nat.le_add_left 1 (k + 4))] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨2, h2l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
              (fun _ => 0) 1 1 2 h1l h2l 0 1 (cartUpC (k + 6) 1))) hc)
          rw [nbMidC (k + 6) _ 1 (litNe 3 k 6 (by decide +kernel))
              (litNe 4 k 6 (by decide +kernel)),
            serstable.fLong_two (k + 5) 2 2 (Nat.le_refl 2)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 2 1 (Nat.lt_succ_self 1)
              (Nat.le_add_left 2 (k + 3)),
            serstable.fLong_two (k + 5) 2 3 (by decide +kernel)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k))]
            at hcx
          exact absurd hcx (by decide +kernel)
      | r + 1 =>
        refine serstable.runVanishC (k + 6) (r + 1) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) (r + 2) hm1l
            (by rw [if_neg (sucNe0 (r + 1))]))
          0 h0l (Or.inl (Nat.succ_pos r)) 
          (nuOcc (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) 0 h0l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW2 (k + 6) (k + 4) (Nat.le_add_left 1 (k + 3)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 0 (by decide +kernel) (fun j => if j = 0 then 2 else 0)
          (fun _ => 0) (if_neg (sucNe0 (k + 2))) rfl (if_neg (sucNe0 (k + 3))) rfl
          (if_neg (sucNe0 (k + 4))) rfl (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW2 (k + 6) (k + 5) (Nat.le_add_left 1 (k + 4)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 0 (by decide +kernel) (fun j => if j = 0 then 2 else 0)
          (fun _ => 0) (if_neg (sucNe0 (k + 4))) rfl (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The charged sector's witness edge at `(2,1) + (e₃ − e₁)`, the target `(1,1,1)`, the second-fusion route -/
theorem edgeC_w1 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [2, 1] l) (cF l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | k + 1 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 2 (k + 2) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 2 + (k + 2) + 2; rw [Nat.add_comm 2 (k + 2)])
      (by rw [Nat.add_comm 2 (k + 2)])
      (serstable.memberRho [2, 1] (k + 6)) (cF (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW21_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else if j = 1 then 1 else 0) 2 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapW21_1 (k + 6) h1l]
        exact termVanishMagC (k + 6) 1 h1l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else if j = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagC (k + 6) 1))
          (Or.inl (by decide +kernel))
      | r + 2, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 2 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW21 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 => exact absurd hm (by decide +kernel)
      | 1 =>
        exact termVanishMagC (k + 6) 2 h2l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else if j = 1 then 1 else 0) 1 2 2 h2l h2l 2 0 (cartDiagC (k + 6) 2))
          (Or.inl (by decide +kernel))
      | r + 2 =>
        refine serstable.runVanishC (k + 6) (r + 2) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else if j = 1 then 1 else 0) (r + 3) hm1l
            (by rw [if_neg (sucNe2 r), if_neg (sucNe0 (r + 2)),
            if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]))
          0 h0l (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 2 r))) 
          (nuOcc (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else if j = 1 then 1 else 0) 0 h0l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW21 (k + 6) (k + 4) (Nat.le_add_left 2 (k + 2)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 0 (by decide +kernel) (fun j => if j = 2 then 1 else 0)
          (fun j => if j = 0 then 1 else if j = 1 then 1 else 0) (if_neg (sucNe2 k)) ((if_neg (sucNe0 (k + 2))).trans
        (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))) (if_neg (sucNe2 (k + 1))) ((if_neg (sucNe0 (k + 3))).trans
        (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))))
          (if_neg (sucNe2 (k + 2))) ((if_neg (sucNe0 (k + 4))).trans
        (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))) (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW21 (k + 6) (k + 5) (Nat.le_add_left 2 (k + 3)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 0 (by decide +kernel) (fun j => if j = 2 then 1 else 0)
          (fun j => if j = 0 then 1 else if j = 1 then 1 else 0) (if_neg (sucNe2 (k + 2))) ((if_neg (sucNe0 (k + 4))).trans
        (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))) (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The charged sector's witness edge at `ω₁ + (e₁ + e₂)`, the target `(2,1)` -/
theorem edgeC_w2 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [1] l) (cA l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 1 (k + 3) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 1 + (k + 3) + 2; rw [Nat.add_comm 1 (k + 3)])
      (by rw [Nat.add_comm 1 (k + 3)])
      (serstable.memberRho [1] (k + 6)) (cA (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW1_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 2 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | r + 1, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 1 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW1 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 =>
        exact termVanishMagC (k + 6) 1 h1l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 1 1 1 h1l h1l 2 0 (cartDiagC (k + 6) 1))
          (Or.inl (by decide +kernel))
      | 1 =>
        refine termVanishTwoC (k + 6) 1
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) _
          (BPair.oneValue_trans (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 1 2 2 h2l h2l 2 0 (cartDiagC (k + 6) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          ⟨1, h1l, fun hc => ?_⟩ (fun d hld => ?_) (fun d hld => ?_)
        · have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
              (fun _ => 0) 1 2 1 h2l h1l 0 1
              (cartDn1C (k + 6) 1 (litNe 3 k 6 (by decide +kernel))))) hc)
          rw [nbMidC (k + 6) _ 0 (litNe 2 k 6 (by decide +kernel))
              (litNe 3 k 6 (by decide +kernel)),
            serstable.fDiff_lo 2 3 0 (by decide +kernel),
            serstable.fDiff_in 2 3 2 (Nat.le_refl 2) (Nat.lt_succ_self 2),
            serstable.fDiff_lo 2 3 1 (by decide +kernel)] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨1, h1l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
              (fun _ => 0) 1 2 1 h2l h1l 0 1
              (cartDn1C (k + 6) 1 (litNe 3 k 6 (by decide +kernel))))) hc)
          rw [nbMidC (k + 6) _ 0 (litNe 2 k 6 (by decide +kernel))
              (litNe 3 k 6 (by decide +kernel)),
            serstable.fLong_lo (k + 5) 2 0 (by decide +kernel)
              (Nat.le_add_left 2 (k + 3)),
            serstable.fLong_two (k + 5) 2 2 (Nat.le_refl 2)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 2 1 (Nat.lt_succ_self 1)
              (Nat.le_add_left 2 (k + 3))] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨3, h3l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
              (fun _ => 0) 1 2 3 h2l h3l 0 1 (cartUpC (k + 6) 2))) hc)
          rw [nbMidC (k + 6) _ 2 (litNe 4 k 6 (by decide +kernel))
              (litNe 5 k 6 (by decide +kernel)),
            serstable.fLong_two (k + 5) 3 3 (Nat.le_refl 3)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 3 2 (Nat.lt_succ_self 2)
              (Nat.le_add_left 3 (k + 2)),
            serstable.fLong_two (k + 5) 3 4 (by decide +kernel)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k))]
            at hcx
          exact absurd hcx (by decide +kernel)
      | r + 2 =>
        refine serstable.runVanishC (k + 6) (r + 2) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) (r + 3) hm1l
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]))
          1 h1l (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 2 r))) 
          (nuOcc (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW1 (k + 6) (k + 4) (Nat.le_add_left 1 (k + 3)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 1 (by decide +kernel) (fun j => if j = 1 then 1 else 0)
          (fun _ => 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW1 (k + 6) (k + 5) (Nat.le_add_left 1 (k + 4)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 1 (by decide +kernel) (fun j => if j = 1 then 1 else 0)
          (fun _ => 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The charged sector's witness edge at `ω₁ + 2e₁`, the target `(3)` -/
theorem edgeC_w3 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [1] l) (cC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | k + 3 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 1 (k + 3) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 1 + (k + 3) + 2; rw [Nat.add_comm 1 (k + 3)])
      (by rw [Nat.add_comm 1 (k + 3)])
      (serstable.memberRho [1] (k + 6)) (cC (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW1_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) 2 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | r + 1, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 1 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW1 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 =>
        refine termVanishTwoC (k + 6) 0
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) _
          (BPair.oneValue_trans (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) 1 1 1 h1l h1l 2 0 (cartDiagC (k + 6) 1))
            (BPair.ofCounts_crossed (by decide +kernel)))
          ⟨0, h0l, fun hc => ?_⟩ (fun d hld => ?_) (fun d hld => ?_)
        · have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
              (fun _ => 0) 1 1 0 h1l h0l 0 1
              (cartDn1C (k + 6) 0 (litNe 2 k 6 (by decide +kernel))))) hc)
          rw [nbHeadC (k + 6) _ h1l (litNe 2 k 6 (by decide +kernel)),
            serstable.fDiff_in 1 2 1 (Nat.le_refl 1) (Nat.lt_succ_self 1),
            serstable.fDiff_lo 1 2 0 (by decide +kernel)] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨0, h0l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
              (fun _ => 0) 1 1 0 h1l h0l 0 1
              (cartDn1C (k + 6) 0 (litNe 2 k 6 (by decide +kernel))))) hc)
          rw [nbHeadC (k + 6) _ h1l (litNe 2 k 6 (by decide +kernel)),
            serstable.fLong_two (k + 5) 1 1 (Nat.le_refl 1)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 1 0 (Nat.lt_succ_self 0)
              (Nat.le_add_left 1 (k + 4))] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨2, h2l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
              (fun _ => 0) 1 1 2 h1l h2l 0 1 (cartUpC (k + 6) 1))) hc)
          rw [nbMidC (k + 6) _ 1 (litNe 3 k 6 (by decide +kernel))
              (litNe 4 k 6 (by decide +kernel)),
            serstable.fLong_two (k + 5) 2 2 (Nat.le_refl 2)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 2 1 (Nat.lt_succ_self 1)
              (Nat.le_add_left 2 (k + 3)),
            serstable.fLong_two (k + 5) 2 3 (by decide +kernel)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k))]
            at hcx
          exact absurd hcx (by decide +kernel)
      | r + 1 =>
        refine serstable.runVanishC (k + 6) (r + 1) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) (r + 2) hm1l
            (by rw [if_neg (sucNe0 (r + 1))]))
          0 h0l (Or.inl (Nat.succ_pos r)) 
          (nuOcc (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) 0 h0l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW1 (k + 6) (k + 4) (Nat.le_add_left 1 (k + 3)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 0 (by decide +kernel) (fun j => if j = 0 then 2 else 0)
          (fun _ => 0) (if_neg (sucNe0 (k + 2))) rfl (if_neg (sucNe0 (k + 3))) rfl
          (if_neg (sucNe0 (k + 4))) rfl (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW1 (k + 6) (k + 5) (Nat.le_add_left 1 (k + 4)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 0 (by decide +kernel) (fun j => if j = 0 then 2 else 0)
          (fun _ => 0) (if_neg (sucNe0 (k + 4))) rfl (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The charged sector's witness edge at `(2,1) + (e₂ + e₃)`, the target `(2,2,1)` -/
theorem edgeC_w4 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [2, 1] l) (cE l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | k + 1 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 2 (k + 2) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 2 + (k + 2) + 2; rw [Nat.add_comm 2 (k + 2)])
      (by rw [Nat.add_comm 2 (k + 2)])
      (serstable.memberRho [2, 1] (k + 6)) (cE (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW21_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else 0) 2 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapW21_1 (k + 6) h1l]
        exact termVanishMagC (k + 6) 1 h1l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagC (k + 6) 1))
          (Or.inl (by decide +kernel))
      | r + 2, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 2 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW21 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 => exact absurd hm (by decide +kernel)
      | 1 =>
        exact termVanishMagC (k + 6) 2 h2l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else 0) 1 2 2 h2l h2l 2 0 (cartDiagC (k + 6) 2))
          (Or.inl (by decide +kernel))
      | r + 2 =>
        refine serstable.runVanishC (k + 6) (r + 2) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else 0) (r + 3) hm1l
            (by rw [if_neg (sucNe2 r), if_neg (sucNe0 (r + 2))]))
          0 h0l (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 2 r))) 
          (nuOcc (k + 6) (fun j => if j = 2 then 1 else 0)
            (fun j => if j = 0 then 1 else 0) 0 h0l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW21 (k + 6) (k + 4) (Nat.le_add_left 2 (k + 2)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 0 (by decide +kernel) (fun j => if j = 2 then 1 else 0)
          (fun j => if j = 0 then 1 else 0) (if_neg (sucNe2 k)) (if_neg (sucNe0 (k + 2))) (if_neg (sucNe2 (k + 1))) (if_neg (sucNe0 (k + 3)))
          (if_neg (sucNe2 (k + 2))) (if_neg (sucNe0 (k + 4))) (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW21 (k + 6) (k + 5) (Nat.le_add_left 2 (k + 3)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 0 (by decide +kernel) (fun j => if j = 2 then 1 else 0)
          (fun j => if j = 0 then 1 else 0) (if_neg (sucNe2 (k + 2))) (if_neg (sucNe0 (k + 4))) (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The charged sector's witness edge at `(2,1) + (e₁ + e₃)`, the target `(3,1,1)` -/
theorem edgeC_w5 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [2, 1] l) (cH l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | k + 1 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 2 (k + 2) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 2 + (k + 2) + 2; rw [Nat.add_comm 2 (k + 2)])
      (by rw [Nat.add_comm 2 (k + 2)])
      (serstable.memberRho [2, 1] (k + 6)) (cH (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW21_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 0 then 1 else if j = 2 then 1 else 0)
            (fun j => if j = 1 then 1 else 0) 2 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapW21_1 (k + 6) h1l]
        exact termVanishMagC (k + 6) 1 h1l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 0 then 1 else if j = 2 then 1 else 0)
            (fun j => if j = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagC (k + 6) 1))
          (Or.inl (by decide +kernel))
      | r + 2, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 2 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW21 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 => exact absurd hm (by decide +kernel)
      | 1 =>
        exact termVanishMagC (k + 6) 2 h2l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 0 then 1 else if j = 2 then 1 else 0)
            (fun j => if j = 1 then 1 else 0) 1 2 2 h2l h2l 2 0 (cartDiagC (k + 6) 2))
          (Or.inl (by decide +kernel))
      | r + 2 =>
        refine serstable.runVanishC (k + 6) (r + 2) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 0 then 1 else if j = 2 then 1 else 0)
            (fun j => if j = 1 then 1 else 0) (r + 3) hm1l
            (by rw [if_neg (sucNe0 (r + 2)), if_neg (sucNe2 r),
            if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]))
          0 h0l (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 2 r))) 
          (nuOcc (k + 6) (fun j => if j = 0 then 1 else if j = 2 then 1 else 0)
            (fun j => if j = 1 then 1 else 0) 0 h0l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW21 (k + 6) (k + 4) (Nat.le_add_left 2 (k + 2)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 0 (by decide +kernel) (fun j => if j = 0 then 1 else if j = 2 then 1 else 0)
          (fun j => if j = 1 then 1 else 0) ((if_neg (sucNe0 (k + 2))).trans (if_neg (sucNe2 k))) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) ((if_neg (sucNe0 (k + 3))).trans (if_neg (sucNe2 (k + 1)))) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
          ((if_neg (sucNe0 (k + 4))).trans (if_neg (sucNe2 (k + 2)))) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW21 (k + 6) (k + 5) (Nat.le_add_left 2 (k + 3)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 0 (by decide +kernel) (fun j => if j = 0 then 1 else if j = 2 then 1 else 0)
          (fun j => if j = 1 then 1 else 0) ((if_neg (sucNe0 (k + 4))).trans (if_neg (sucNe2 (k + 2)))) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The charged sector's witness edge at `(3) + 2e₂`, the target `(3,2)` -/
theorem edgeC_w6 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [3] l) (cB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 1 (k + 3) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 1 + (k + 3) + 2; rw [Nat.add_comm 1 (k + 3)])
      (by rw [Nat.add_comm 1 (k + 3)])
      (serstable.memberRho [3] (k + 6)) (cB (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW3_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 2 else 0)
            (fun j => if j = 0 then 2 else 0) 4 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | r + 1, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 1 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW3 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 =>
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 2 else 0)
            (fun j => if j = 0 then 2 else 0) 1 1 0 h1l h0l 0 1
            (cartDn1C (k + 6) 0 (litNe 2 k 6 (by decide +kernel))))
          (Or.inr (by decide +kernel))
      | r + 1 =>
        refine serstable.runVanishC (k + 6) (r + 1) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 1 then 2 else 0)
            (fun j => if j = 0 then 2 else 0) (r + 2) hm1l
            (by rw [if_neg (sucNe1 r), if_neg (sucNe0 (r + 1))]))
          0 h0l (Or.inl (Nat.succ_pos r)) 
          (nuOcc (k + 6) (fun j => if j = 1 then 2 else 0)
            (fun j => if j = 0 then 2 else 0) 0 h0l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW3 (k + 6) (k + 4) (Nat.le_add_left 1 (k + 3)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 0 (by decide +kernel) (fun j => if j = 1 then 2 else 0)
          (fun j => if j = 0 then 2 else 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 2))) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 3)))
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 4))) (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW3 (k + 6) (k + 5) (Nat.le_add_left 1 (k + 4)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 0 (by decide +kernel) (fun j => if j = 1 then 2 else 0)
          (fun j => if j = 0 then 2 else 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) (if_neg (sucNe0 (k + 4))) (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The charged sector's witness edge at `(3) + (e₁ + e₂)`, the target `(4,1)` -/
theorem edgeC_w7 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [3] l) (cA l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 1 (k + 3) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 1 + (k + 3) + 2; rw [Nat.add_comm 1 (k + 3)])
      (by rw [Nat.add_comm 1 (k + 3)])
      (serstable.memberRho [3] (k + 6)) (cA (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW3_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 4 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | r + 1, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 1 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW3 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 =>
        exact termVanishMagC (k + 6) 1 h1l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 1 1 1 h1l h1l 2 0 (cartDiagC (k + 6) 1))
          (Or.inl (by decide +kernel))
      | 1 =>
        refine termVanishTwoC (k + 6) 1
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) _
          (BPair.oneValue_trans (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 1 2 2 h2l h2l 2 0 (cartDiagC (k + 6) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          ⟨1, h1l, fun hc => ?_⟩ (fun d hld => ?_) (fun d hld => ?_)
        · have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
              (fun _ => 0) 1 2 1 h2l h1l 0 1
              (cartDn1C (k + 6) 1 (litNe 3 k 6 (by decide +kernel))))) hc)
          rw [nbMidC (k + 6) _ 0 (litNe 2 k 6 (by decide +kernel))
              (litNe 3 k 6 (by decide +kernel)),
            serstable.fDiff_lo 2 3 0 (by decide +kernel),
            serstable.fDiff_in 2 3 2 (Nat.le_refl 2) (Nat.lt_succ_self 2),
            serstable.fDiff_lo 2 3 1 (by decide +kernel)] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨1, h1l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
              (fun _ => 0) 1 2 1 h2l h1l 0 1
              (cartDn1C (k + 6) 1 (litNe 3 k 6 (by decide +kernel))))) hc)
          rw [nbMidC (k + 6) _ 0 (litNe 2 k 6 (by decide +kernel))
              (litNe 3 k 6 (by decide +kernel)),
            serstable.fLong_lo (k + 5) 2 0 (by decide +kernel)
              (Nat.le_add_left 2 (k + 3)),
            serstable.fLong_two (k + 5) 2 2 (Nat.le_refl 2)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 2 1 (Nat.lt_succ_self 1)
              (Nat.le_add_left 2 (k + 3))] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨3, h3l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 1 then 1 else 0)
              (fun _ => 0) 1 2 3 h2l h3l 0 1 (cartUpC (k + 6) 2))) hc)
          rw [nbMidC (k + 6) _ 2 (litNe 4 k 6 (by decide +kernel))
              (litNe 5 k 6 (by decide +kernel)),
            serstable.fLong_two (k + 5) 3 3 (Nat.le_refl 3)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 3 2 (Nat.lt_succ_self 2)
              (Nat.le_add_left 3 (k + 2)),
            serstable.fLong_two (k + 5) 3 4 (by decide +kernel)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k))]
            at hcx
          exact absurd hcx (by decide +kernel)
      | r + 2 =>
        refine serstable.runVanishC (k + 6) (r + 2) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) (r + 3) hm1l
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]))
          1 h1l (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 2 r))) 
          (nuOcc (k + 6) (fun j => if j = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW3 (k + 6) (k + 4) (Nat.le_add_left 1 (k + 3)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 1 (by decide +kernel) (fun j => if j = 1 then 1 else 0)
          (fun _ => 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW3 (k + 6) (k + 5) (Nat.le_add_left 1 (k + 4)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 1 (by decide +kernel) (fun j => if j = 1 then 1 else 0)
          (fun _ => 0) (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-- The charged sector's witness edge at `(3) + 2e₁`, the target `(5)` -/
theorem edgeC_w8 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableC l)
      (serstable.memberRho [3] l) (cC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | k + 3 =>
    have h0l : (0 : Nat) < k + 6 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h2l : (2 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    have h3l : (3 : Nat) < k + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 k)
    refine foldZeroG (sertables.tableC (k + 6)) 1 (k + 3) 2 (k + 4) (by decide +kernel)
      (by show k + 6 = 1 + (k + 3) + 2; rw [Nat.add_comm 1 (k + 3)])
      (by rw [Nat.add_comm 1 (k + 3)])
      (serstable.memberRho [3] (k + 6)) (cC (k + 6)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW3_0 (k + 6) h0l]
        exact termVanishMagC (k + 6) 0 h0l _ _ _
          (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) 4 0 0 h0l h0l 2 0
            (cartDiagC (k + 6) 0))
          (Or.inl (by decide +kernel))
      | r + 1, hi =>
        exact absurd hi (fun hc => ltRefute (Nat.le_add_left 1 r) hc)
    · intro m hm hml'
      have hm1l : m + 1 < k + 6 :=
        Nat.lt_trans hml' (Nat.add_lt_add_left (by decide +kernel) k)
      have hm3l : m + 3 < k + 6 := show m + 1 + 2 < k + 4 + 2 from
        Nat.add_lt_add_right hml' 2
      rw [kapW3 (k + 6) (m + 1) hm hm1l]
      match m with
      | 0 =>
        refine termVanishTwoC (k + 6) 0
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) _
          (BPair.oneValue_trans (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) 1 1 1 h1l h1l 2 0 (cartDiagC (k + 6) 1))
            (BPair.ofCounts_crossed (by decide +kernel)))
          ⟨0, h0l, fun hc => ?_⟩ (fun d hld => ?_) (fun d hld => ?_)
        · have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
              (fun _ => 0) 1 1 0 h1l h0l 0 1
              (cartDn1C (k + 6) 0 (litNe 2 k 6 (by decide +kernel))))) hc)
          rw [nbHeadC (k + 6) _ h1l (litNe 2 k 6 (by decide +kernel)),
            serstable.fDiff_in 1 2 1 (Nat.le_refl 1) (Nat.lt_succ_self 1),
            serstable.fDiff_lo 1 2 0 (by decide +kernel)] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨0, h0l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
              (fun _ => 0) 1 1 0 h1l h0l 0 1
              (cartDn1C (k + 6) 0 (litNe 2 k 6 (by decide +kernel))))) hc)
          rw [nbHeadC (k + 6) _ h1l (litNe 2 k 6 (by decide +kernel)),
            serstable.fLong_two (k + 5) 1 1 (Nat.le_refl 1)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 1 0 (Nat.lt_succ_self 0)
              (Nat.le_add_left 1 (k + 4))] at hcx
          exact absurd hcx (by decide +kernel)
        · have hd : d = k + 5 := (Nat.succ.inj hld).symm
          subst hd
          refine ⟨2, h2l, fun hc => ?_⟩
          have hcx := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm
            (raisedCountC (k + 6) (fun j => if j = 0 then 2 else 0)
              (fun _ => 0) 1 1 2 h1l h2l 0 1 (cartUpC (k + 6) 1))) hc)
          rw [nbMidC (k + 6) _ 1 (litNe 3 k 6 (by decide +kernel))
              (litNe 4 k 6 (by decide +kernel)),
            serstable.fLong_two (k + 5) 2 2 (Nat.le_refl 2)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k)),
            serstable.fLong_lo (k + 5) 2 1 (Nat.lt_succ_self 1)
              (Nat.le_add_left 2 (k + 3)),
            serstable.fLong_two (k + 5) 2 3 (by decide +kernel)
              (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 k))]
            at hcx
          exact absurd hcx (by decide +kernel)
      | r + 1 =>
        refine serstable.runVanishC (k + 6) (r + 1) _ hm3l (nuOf_length _ _)
          (nuVac (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) (r + 2) hm1l
            (by rw [if_neg (sucNe0 (r + 1))]))
          0 h0l (Or.inl (Nat.succ_pos r)) 
          (nuOcc (k + 6) (fun j => if j = 0 then 2 else 0)
            (fun _ => 0) 0 h0l (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW3 (k + 6) (k + 4) (Nat.le_add_left 1 (k + 3)) (ltPlusTwo (k + 4))]
        exact tailSubAt k 0 (by decide +kernel) (fun j => if j = 0 then 2 else 0)
          (fun _ => 0) (if_neg (sucNe0 (k + 2))) rfl (if_neg (sucNe0 (k + 3))) rfl
          (if_neg (sucNe0 (k + 4))) rfl (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW3 (k + 6) (k + 5) (Nat.le_add_left 1 (k + 4)) (Nat.lt_succ_self (k + 5))]
        exact tailTopAt k 0 (by decide +kernel) (fun j => if j = 0 then 2 else 0)
          (fun _ => 0) (if_neg (sucNe0 (k + 4))) rfl (by decide +kernel)
      | r + 2, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hc)))

/-! ### The `D` positive list's memberships -/

/-- The difference family at an ordered pair joins the `D`
positive list. -/
private theorem memDiffD (l a b : Nat) (hab : a < b) (hbl : b < l) :
    (List.range l).map (serstable.fDiff a b) ∈ sertables.foldsD l :=
  ground.mem_append_left _
    (show sertables.diffFold l a b
        ∈ (places.pairsOf l).map (fun p => sertables.diffFold l p.1 p.2) from
      ground.mem_map_to (fun p => sertables.diffFold l p.1 p.2)
        (ground.mem_of_countOf_pos (a, b) (places.pairsOf l)
          (places.pairs_complete l hab hbl)))

/-- The `D` sum family's generic member at a coordinate pair below
the fork joins the positive list. -/
private theorem memSumD (e a b : Nat) (hab : a < b) (hbe : b ≤ e) :
    (List.range (e + 2)).map (serstable.fSumD e a b)
      ∈ sertables.foldsD (e + 2) := by
  rw [← serstable.fSumD_eq e a b (fun hc => Nat.not_succ_le_self e
    (by rw [Nat.succ.inj hc] at hbe; exact hbe))]
  exact ground.mem_append_right _
    (ground.mem_map_to (fun p => sertables.sumFoldD (e + 2) p.1 p.2)
      (ground.mem_of_countOf_pos (a, b) (places.pairsOf (e + 2))
        (places.pairs_complete (e + 2) hab
          (Nat.lt_of_le_of_lt hbe
            (Nat.lt_trans (Nat.lt_succ_self e) (Nat.lt_succ_self (e + 1)))))))

/-! ### The `D` exhibition engine -/

/-- A moved content whose count reads are a `D` family's column
reads, key for key, is that family's coroot vector: its θ count is
one (`prop:row`'s θ list at `con:sertables`' positive folds). -/
private theorem thetaOneNormD (l : Nat) (F : Nat → Nat)
    (z : List BPair) (hzl : z.length = l)
    (hmem : (List.range l).map F ∈ sertables.foldsD l)
    (hent : ∀ k, k < l → (ground.getAt BPair.unit z k).oneValue
      (BPair.ofCounts (2 * F k) (serstable.nbD l F k)))
    (k0 : Nat) (hk0 : k0 < l)
    (hne : ¬ (ground.getAt BPair.unit z k0).oneValue BPair.unit) :
    row.thetaCount (sertables.tableD l) (poly.pnorm z) = 1 := by
  obtain ⟨j, hj, hje⟩ := ground.getAt_of_mem ([] : List Nat) hmem
  refine thetaOneNormG (sertables.tableD l) z hzl j hj
    (fun k hk => ?_) k0 hk0 hne
  refine BPair.oneValue_trans (BPair.oneValue_trans (hent k hk)
    (BPair.oneValue_symm
      (serstable.posCorootV_entryD l j k F hk hje))) ?_
  rw [pnormEntry (sertables.posCorootV (sertables.tableD l) j) k
    (by rw [sertables.posCorootV_length]; exact hk)]
  exact BPair.norm_oneValue _

/-! ### The `D` neighbour fold's four arms -/

/-- The `D` neighbour fold at the rank's last key: the key two
below. -/
private theorem nbDtopAt (l : Nat) (F : Nat → Nat) (j : Nat) (h : j + 1 = l) :
    serstable.nbD l F j = serstable.pv2D F j := by
  rw [serstable.nbD_eq, if_pos (ground.eqBeqOf h)]

/-- The `D` neighbour fold at the rank's second-last key: the key
one below. -/
private theorem nbDsubAt (l : Nat) (F : Nat → Nat) (j : Nat) (h : j + 2 = l) :
    serstable.nbD l F j = serstable.pvD F j := by
  rw [serstable.nbD_eq,
    if_neg (fun hb => Nat.ne_of_lt (Nat.lt_succ_self (j + 1))
      ((ground.beqEqOf hb).trans h.symm)),
    if_pos (ground.eqBeqOf h)]

/-- The `D` neighbour fold at the fork key: its three joined
keys. -/
private theorem nbDforkAt (l : Nat) (F : Nat → Nat) (j : Nat) (h : j + 3 = l) :
    serstable.nbD l F j = serstable.pvD F j + F (j + 1) + F (j + 2) := by
  rw [serstable.nbD_eq,
    if_neg (fun hb => Nat.ne_of_lt
      (Nat.lt_trans (Nat.lt_succ_self (j + 1)) (Nat.lt_succ_self (j + 2)))
      ((ground.beqEqOf hb).trans h.symm)),
    if_neg (fun hb => Nat.ne_of_lt (Nat.lt_succ_self (j + 2))
      ((ground.beqEqOf hb).trans h.symm)),
    if_pos (ground.eqBeqOf h)]

/-- The `D` neighbour fold along the chain below the fork: the two
neighbours' sum. -/
private theorem nbDchain (l : Nat) (F : Nat → Nat) (j : Nat) (h : j + 3 < l) :
    serstable.nbD l F j = serstable.pvD F j + F (j + 1) := by
  rw [serstable.nbD_eq,
    if_neg (fun hb => Nat.ne_of_lt
      (Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self (j + 1))
        (Nat.lt_succ_self (j + 2))) h) (ground.beqEqOf hb)),
    if_neg (fun hb => Nat.ne_of_lt
      (Nat.lt_trans (Nat.lt_succ_self (j + 2)) h) (ground.beqEqOf hb)),
    if_neg (fun hb => Nat.ne_of_lt h (ground.beqEqOf hb))]

/-- The `D` neighbour fold is vacant at a key whose four joined
reads are. -/
private theorem nbDvac (l : Nat) (F : Nat → Nat) (j : Nat)
    (h1 : ∀ i, i + 1 = j → F i = 0) (h2 : ∀ i, i + 2 = j → F i = 0)
    (h3 : F (j + 1) = 0) (h4 : F (j + 2) = 0) :
    serstable.nbD l F j = 0 := by
  have hp : serstable.pvD F j = 0 :=
    serstable.pvD_zeroOf F j (fun i hi => h1 i hi.symm)
  rw [serstable.nbD_eq]
  by_cases t1 : j + 1 = l
  · rw [if_pos (ground.eqBeqOf t1)]
    exact serstable.pv2D_zeroOf F j (fun i hi => h2 i hi.symm)
  · rw [if_neg (fun hb => t1 (ground.beqEqOf hb))]
    by_cases t2 : j + 2 = l
    · rw [if_pos (ground.eqBeqOf t2)]
      exact hp
    · rw [if_neg (fun hb => t2 (ground.beqEqOf hb))]
      by_cases t3 : j + 3 = l
      · rw [if_pos (ground.eqBeqOf t3), hp, h3, h4]
      · rw [if_neg (fun hb => t3 (ground.beqEqOf hb)), hp, h3]

/-- A moved content spelled at its `D` count reads exhibits the
displayed family: its θ count is one. -/
private theorem famOnePosD (l : Nat) (F u v : Nat → Nat)
    (hmem : (List.range l).map F ∈ sertables.foldsD l)
    (hcol : ∀ k, k < l → u k + serstable.nbD l F k = 2 * F k + v k)
    (k0 : Nat) (hk0 : k0 < l) (hne : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableD l)
      (nuOf l (fun i => BPair.ofCounts (u i) (v i))) = 1 :=
  thetaOneNormD l F
    ((List.range l).map (fun i => BPair.ofCounts (u i) (v i)))
    (ground.length_mapRange _ l) hmem
    (fun k hk => by
      rw [ground.getAt_map_range BPair.unit _ l k, if_pos hk]
      exact BPair.ofCounts_crossed (hcol k hk))
    k0 hk0
    (by
      rw [ground.getAt_map_range BPair.unit _ l k0, if_pos hk0]
      exact fun hc => hne (BPair.ofCounts_unit.mp hc))

/-! ### The `D` sum families' window reads -/

/-- The `D` sum family's column is vacant past its own window: the
plateau, the fork key and the two tips all read the doubled
entry. -/
private theorem sumColFar (q a b k : Nat) (hbq : b ≤ q + 1)
    (hbk : b + 1 ≤ k) (hk : k < q + 5) :
    serstable.nbD (q + 5) (serstable.fSumD (q + 3) a b) k
      = 2 * serstable.fSumD (q + 3) a b k := by
  have hbe : b ≤ q + 3 :=
    Nat.le_trans hbq (Nat.le_trans (Nat.le_succ (q + 1)) (Nat.le_succ (q + 2)))
  have hF1 : serstable.fSumD (q + 3) a b (q + 1) = 2 :=
    serstable.fSumD_two (q + 3) a b (q + 1) hbq
      (Nat.lt_trans (Nat.lt_succ_self (q + 1)) (Nat.lt_succ_self (q + 2)))
  have hF2 : serstable.fSumD (q + 3) a b (q + 2) = 2 :=
    serstable.fSumD_two (q + 3) a b (q + 2) (Nat.le_trans hbq (Nat.le_succ (q + 1)))
      (Nat.lt_succ_self (q + 2))
  have hF3 : serstable.fSumD (q + 3) a b (q + 3) = 1 :=
    serstable.fSumD_end (q + 3) a b (q + 3) hbe (Nat.le_refl (q + 3))
      (Nat.lt_trans (Nat.lt_succ_self (q + 3)) (Nat.lt_succ_self (q + 4)))
  have hF4 : serstable.fSumD (q + 3) a b (q + 4) = 1 :=
    serstable.fSumD_end (q + 3) a b (q + 4) hbe (Nat.le_succ (q + 3))
      (Nat.lt_succ_self (q + 4))
  by_cases t1 : k + 1 = q + 5
  · have hke : k = q + 4 := Nat.succ.inj t1
    rw [hke, nbDtopAt (q + 5) _ (q + 4) rfl,
      serstable.pv2D_succ2 (serstable.fSumD (q + 3) a b) (q + 2), hF2, hF4]
  · by_cases t2 : k + 2 = q + 5
    · have hke : k = q + 3 := Nat.succ.inj (Nat.succ.inj t2)
      rw [hke, nbDsubAt (q + 5) _ (q + 3) rfl,
        serstable.pvD_succ (serstable.fSumD (q + 3) a b) (q + 2), hF2, hF3]
    · by_cases t3 : k + 3 = q + 5
      · have hke : k = q + 2 := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj t3))
        rw [hke, nbDforkAt (q + 5) _ (q + 2) rfl,
          serstable.pvD_succ (serstable.fSumD (q + 3) a b) (q + 1),
          hF1, hF2, hF3, hF4]
      · have s1 : k + 1 < q + 5 := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) t1
        have s2 : k + 2 < q + 5 := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt s1) t2
        have s3 : k + 3 < q + 5 := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt s2) t3
        have hk2 : k < q + 2 := Nat.lt_of_succ_lt_succ
          (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ s3))
        match k, hbk, hk2, s3 with
        | 0, hbk, _, _ => exact absurd hbk (Nat.not_succ_le_zero b)
        | p + 1, hbk, hk2, s3 =>
          have hbp : b ≤ p := Nat.le_of_succ_le_succ hbk
          rw [nbDchain (q + 5) _ (p + 1) s3,
            serstable.pvD_succ (serstable.fSumD (q + 3) a b) p,
            serstable.fSumD_two (q + 3) a b p hbp
              (Nat.lt_trans (Nat.lt_succ_self p)
                (Nat.lt_trans hk2 (Nat.lt_succ_self (q + 2)))),
            serstable.fSumD_two (q + 3) a b (p + 1) (Nat.le_trans hbp (Nat.le_succ p))
              (Nat.lt_trans hk2 (Nat.lt_succ_self (q + 2))),
            serstable.fSumD_two (q + 3) a b (p + 2)
              (Nat.le_trans hbp
                (Nat.le_trans (Nat.le_succ p) (Nat.le_succ (p + 1))))
              (Nat.succ_lt_succ hk2)]

/-! ### The `D` moved contents at the leading keys -/

/-- The moved content `e₁ − e₂`, the `α₁` row. -/
def dA (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 0 then 2 else 0)
    (if i = 1 then 1 else 0))

/-- `e₁ − e₂` is the `D` difference family at the leading pair. -/
theorem dA_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableD l) (dA l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | j + 2 =>
    show row.thetaCount (sertables.tableD (j + 6)) (dA (j + 6)) = 1
    have h0 : (0 : Nat) < j + 6 := Nat.succ_pos _
    have h1 : (1 : Nat) < j + 6 := Nat.succ_lt_succ (Nat.succ_pos _)
    have hc0 : (0 : Nat) + 3 < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hc1 : (1 : Nat) + 3 < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hc2 : (2 : Nat) + 3 < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hF0 : serstable.fDiff 0 1 0 = 1 :=
      serstable.fDiff_in 0 1 0 (Nat.le_refl 0) (Nat.lt_succ_self 0)
    have hFs : ∀ m, serstable.fDiff 0 1 (m + 1) = 0 := fun m =>
      serstable.fDiff_hi 0 1 (m + 1)
        (fun hc => Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ hc))
    refine famOnePosD (j + 6) (serstable.fDiff 0 1)
      (fun i => if i = 0 then 2 else 0) (fun i => if i = 1 then 1 else 0)
      (memDiffD (j + 6) 0 1 (Nat.lt_succ_self 0) h1) (fun k hk => ?_) 0 h0
      (by decide +kernel)
    match k with
    | 0 =>
      show (if (0 : Nat) = 0 then 2 else 0)
          + serstable.nbD (j + 6) (serstable.fDiff 0 1) 0
        = 2 * serstable.fDiff 0 1 0 + (if (0 : Nat) = 1 then 1 else 0)
      rw [if_pos rfl, if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
        nbDchain (j + 6) _ 0 hc0, serstable.pvD_zero, hFs 0, hF0]
    | 1 =>
      show (if (1 : Nat) = 0 then 2 else 0)
          + serstable.nbD (j + 6) (serstable.fDiff 0 1) 1
        = 2 * serstable.fDiff 0 1 1 + (if (1 : Nat) = 1 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 0), if_pos rfl,
        nbDchain (j + 6) _ 1 hc1,
        serstable.pvD_succ (serstable.fDiff 0 1) 0, hF0, hFs 0, hFs 1]
    | 2 =>
      show (if (2 : Nat) = 0 then 2 else 0)
          + serstable.nbD (j + 6) (serstable.fDiff 0 1) 2
        = 2 * serstable.fDiff 0 1 2 + (if (2 : Nat) = 1 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (2 : Nat) = 0),
        if_neg (by decide +kernel : ¬ (2 : Nat) = 1),
        nbDchain (j + 6) _ 2 hc2,
        serstable.pvD_succ (serstable.fDiff 0 1) 1, hFs 0, hFs 1, hFs 2]
    | m + 3 =>
      show (if m + 3 = 0 then 2 else 0)
          + serstable.nbD (j + 6) (serstable.fDiff 0 1) (m + 3)
        = 2 * serstable.fDiff 0 1 (m + 3) + (if m + 3 = 1 then 1 else 0)
      rw [if_neg (fun hc => Nat.noConfusion hc),
        if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
        nbDvac (j + 6) _ (m + 3)
          (fun i hi => by
            rw [show i = m + 2 from Nat.succ.inj hi]; exact hFs (m + 1))
          (fun i hi => by
            rw [show i = m + 1 from Nat.succ.inj (Nat.succ.inj hi)]
            exact hFs m)
          (hFs (m + 3)) (hFs (m + 4)), hFs (m + 2)]

/-- The moved content `e₂ − e₁ + e₃`, the sum family at the leading
pair. -/
def dB (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 1 then 1 else 0) 0)

/-- `dB` is the `D` sum family at the leading pair. -/
theorem dB_mem (l : Nat) (hl : 4 ≤ l) :
    row.thetaCount (sertables.tableD l) (dB l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | j + 1 =>
    show row.thetaCount (sertables.tableD (j + 5)) (dB (j + 5)) = 1
    have h0 : (0 : Nat) < j + 5 := Nat.succ_pos _
    have h1 : (1 : Nat) < j + 5 := Nat.succ_lt_succ (Nat.succ_pos _)
    have hc0 : (0 : Nat) + 3 < j + 5 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 j)
    have hc1 : (1 : Nat) + 3 < j + 5 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 j)
    have hbe : (1 : Nat) ≤ j + 3 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 3 j)
    have hF0 : serstable.fSumD (j + 3) 0 1 0 = 1 :=
      serstable.fSumD_mid (j + 3) 0 1 0 (Nat.le_refl 0) (Nat.lt_succ_self 0) hbe
    have hF1 : serstable.fSumD (j + 3) 0 1 1 = 2 :=
      serstable.fSumD_two (j + 3) 0 1 1 (Nat.le_refl 1)
        (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 j))
    have hF2 : serstable.fSumD (j + 3) 0 1 2 = 2 :=
      serstable.fSumD_two (j + 3) 0 1 2 (by decide +kernel)
        (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 3 j))
    refine famOnePosD (j + 5) (serstable.fSumD (j + 3) 0 1)
      (fun i => if i = 1 then 1 else 0) (fun _ => 0)
      (memSumD (j + 3) 0 1 (Nat.lt_succ_self 0) hbe)
      (fun k hk => ?_) 1 h1 (by decide +kernel)
    match k, hk with
    | 0, _ =>
      show (if (0 : Nat) = 1 then 1 else 0)
          + serstable.nbD (j + 5) (serstable.fSumD (j + 3) 0 1) 0
        = 2 * serstable.fSumD (j + 3) 0 1 0 + 0
      rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
        nbDchain (j + 5) _ 0 hc0, serstable.pvD_zero, hF1, hF0]
    | 1, _ =>
      show (if (1 : Nat) = 1 then 1 else 0)
          + serstable.nbD (j + 5) (serstable.fSumD (j + 3) 0 1) 1
        = 2 * serstable.fSumD (j + 3) 0 1 1 + 0
      rw [if_pos rfl, nbDchain (j + 5) _ 1 hc1,
        serstable.pvD_succ (serstable.fSumD (j + 3) 0 1) 0, hF0, hF2, hF1]
    | m + 2, hk =>
      show (if m + 2 = 1 then 1 else 0)
          + serstable.nbD (j + 5) (serstable.fSumD (j + 3) 0 1) (m + 2)
        = 2 * serstable.fSumD (j + 3) 0 1 (m + 2) + 0
      rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
        sumColFar j 0 1 (m + 2)
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 1 j))
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))) hk]
      exact (Nat.zero_add _).trans (Nat.add_zero _).symm

/-- The moved content `e₁ − e₂ + e₃`, the sum family at the pair
`(0, 2)`. -/
def dC (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts
    (if i = 0 then 1 else if i = 2 then 1 else 0)
    (if i = 1 then 1 else 0))

/-- `dC` is the `D` sum family at the pair `(0, 2)`. -/
theorem dC_mem (l : Nat) (hl : 5 ≤ l) :
    row.thetaCount (sertables.tableD l) (dC l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | j + 1 =>
    show row.thetaCount (sertables.tableD (j + 6)) (dC (j + 6)) = 1
    have h0 : (0 : Nat) < j + 6 := Nat.succ_pos _
    have h1 : (1 : Nat) < j + 6 := Nat.succ_lt_succ (Nat.succ_pos _)
    have hc0 : (0 : Nat) + 3 < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hc1 : (1 : Nat) + 3 < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hc2 : (2 : Nat) + 3 < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hbe : (2 : Nat) ≤ j + 4 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 j)
    have h2e : (2 : Nat) < j + 4 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 j)
    have h3e : (3 : Nat) < j + 4 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 j)
    have hF0 : serstable.fSumD (j + 4) 0 2 0 = 1 :=
      serstable.fSumD_mid (j + 4) 0 2 0 (Nat.le_refl 0) (by decide +kernel) hbe
    have hF1 : serstable.fSumD (j + 4) 0 2 1 = 1 :=
      serstable.fSumD_mid (j + 4) 0 2 1 (Nat.zero_le 1) (by decide +kernel) hbe
    have hF2 : serstable.fSumD (j + 4) 0 2 2 = 2 :=
      serstable.fSumD_two (j + 4) 0 2 2 (Nat.le_refl 2) h2e
    have hF3 : serstable.fSumD (j + 4) 0 2 3 = 2 :=
      serstable.fSumD_two (j + 4) 0 2 3 (by decide +kernel) h3e
    refine famOnePosD (j + 6) (serstable.fSumD (j + 4) 0 2)
      (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
      (fun i => if i = 1 then 1 else 0)
      (memSumD (j + 4) 0 2 (by decide +kernel) hbe) (fun k hk => ?_) 0 h0
      (by decide +kernel)
    match k, hk with
    | 0, _ =>
      show (if (0 : Nat) = 0 then 1 else if (0 : Nat) = 2 then 1 else 0)
          + serstable.nbD (j + 6) (serstable.fSumD (j + 4) 0 2) 0
        = 2 * serstable.fSumD (j + 4) 0 2 0 + (if (0 : Nat) = 1 then 1 else 0)
      rw [if_pos rfl, if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
        nbDchain (j + 6) _ 0 hc0, serstable.pvD_zero, hF1, hF0]
    | 1, _ =>
      show (if (1 : Nat) = 0 then 1 else if (1 : Nat) = 2 then 1 else 0)
          + serstable.nbD (j + 6) (serstable.fSumD (j + 4) 0 2) 1
        = 2 * serstable.fSumD (j + 4) 0 2 1 + (if (1 : Nat) = 1 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 0),
        if_neg (by decide +kernel : ¬ (1 : Nat) = 2), if_pos rfl,
        nbDchain (j + 6) _ 1 hc1,
        serstable.pvD_succ (serstable.fSumD (j + 4) 0 2) 0, hF0, hF2, hF1]
    | 2, _ =>
      show (if (2 : Nat) = 0 then 1 else if (2 : Nat) = 2 then 1 else 0)
          + serstable.nbD (j + 6) (serstable.fSumD (j + 4) 0 2) 2
        = 2 * serstable.fSumD (j + 4) 0 2 2 + (if (2 : Nat) = 1 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (2 : Nat) = 0), if_pos rfl,
        if_neg (by decide +kernel : ¬ (2 : Nat) = 1),
        nbDchain (j + 6) _ 2 hc2,
        serstable.pvD_succ (serstable.fSumD (j + 4) 0 2) 1, hF1, hF3, hF2]
    | m + 3, hk =>
      show (if m + 3 = 0 then 1 else if m + 3 = 2 then 1 else 0)
          + serstable.nbD (j + 6) (serstable.fSumD (j + 4) 0 2) (m + 3)
        = 2 * serstable.fSumD (j + 4) 0 2 (m + 3) + (if m + 3 = 1 then 1 else 0)
      rw [if_neg (fun hc => Nat.noConfusion hc),
        if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
        if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
        sumColFar (j + 1) 0 2 (m + 3)
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 2 j))
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ
            (Nat.zero_le m)))) hk]
      exact (Nat.zero_add _).trans (Nat.add_zero _).symm

/-- The moved content `e₄ − e₂`, the sum family at the pair
`(2, 3)`. -/
def dD (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 3 then 1 else 0)
    (if i = 1 then 1 else 0))

/-- `dD` is the `D` sum family at the pair `(2, 3)`. -/
theorem dD_mem (l : Nat) (hl : 6 ≤ l) :
    row.thetaCount (sertables.tableD l) (dD l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | j + 1 =>
    show row.thetaCount (sertables.tableD (j + 7)) (dD (j + 7)) = 1
    have h1 : (1 : Nat) < j + 7 := Nat.succ_lt_succ (Nat.succ_pos _)
    have hc0 : (0 : Nat) + 3 < j + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 j)
    have hc1 : (1 : Nat) + 3 < j + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 j)
    have hc2 : (2 : Nat) + 3 < j + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 j)
    have hc3 : (3 : Nat) + 3 < j + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 j)
    have hbe : (3 : Nat) ≤ j + 5 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 j)
    have h3e : (3 : Nat) < j + 5 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 j)
    have h4e : (4 : Nat) < j + 5 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 j)
    have hF0 : serstable.fSumD (j + 5) 2 3 0 = 0 :=
      serstable.fSumD_lo (j + 5) 2 3 0 (by decide +kernel) (by decide +kernel) hbe
    have hF1 : serstable.fSumD (j + 5) 2 3 1 = 0 :=
      serstable.fSumD_lo (j + 5) 2 3 1 (by decide +kernel) (by decide +kernel) hbe
    have hF2 : serstable.fSumD (j + 5) 2 3 2 = 1 :=
      serstable.fSumD_mid (j + 5) 2 3 2 (Nat.le_refl 2) (by decide +kernel) hbe
    have hF3 : serstable.fSumD (j + 5) 2 3 3 = 2 :=
      serstable.fSumD_two (j + 5) 2 3 3 (Nat.le_refl 3) h3e
    have hF4 : serstable.fSumD (j + 5) 2 3 4 = 2 :=
      serstable.fSumD_two (j + 5) 2 3 4 (by decide +kernel) h4e
    refine famOnePosD (j + 7) (serstable.fSumD (j + 5) 2 3)
      (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0)
      (memSumD (j + 5) 2 3 (by decide +kernel) hbe) (fun k hk => ?_) 1 h1
      (by decide +kernel)
    match k, hk with
    | 0, _ =>
      show (if (0 : Nat) = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 2 3) 0
        = 2 * serstable.fSumD (j + 5) 2 3 0 + (if (0 : Nat) = 1 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 3),
        if_neg (by decide +kernel : ¬ (0 : Nat) = 1),
        nbDchain (j + 7) _ 0 hc0, serstable.pvD_zero, hF1, hF0]
    | 1, _ =>
      show (if (1 : Nat) = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 2 3) 1
        = 2 * serstable.fSumD (j + 5) 2 3 1 + (if (1 : Nat) = 1 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 3), if_pos rfl,
        nbDchain (j + 7) _ 1 hc1,
        serstable.pvD_succ (serstable.fSumD (j + 5) 2 3) 0, hF0, hF2, hF1]
    | 2, _ =>
      show (if (2 : Nat) = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 2 3) 2
        = 2 * serstable.fSumD (j + 5) 2 3 2 + (if (2 : Nat) = 1 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (2 : Nat) = 3),
        if_neg (by decide +kernel : ¬ (2 : Nat) = 1),
        nbDchain (j + 7) _ 2 hc2,
        serstable.pvD_succ (serstable.fSumD (j + 5) 2 3) 1, hF1, hF3, hF2]
    | 3, _ =>
      show (if (3 : Nat) = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 2 3) 3
        = 2 * serstable.fSumD (j + 5) 2 3 3 + (if (3 : Nat) = 1 then 1 else 0)
      rw [if_pos rfl, if_neg (by decide +kernel : ¬ (3 : Nat) = 1),
        nbDchain (j + 7) _ 3 hc3,
        serstable.pvD_succ (serstable.fSumD (j + 5) 2 3) 2, hF2, hF4, hF3]
    | m + 4, hk =>
      show (if m + 4 = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 2 3) (m + 4)
        = 2 * serstable.fSumD (j + 5) 2 3 (m + 4) + (if m + 4 = 1 then 1 else 0)
      rw [if_neg (fun hc => Nat.noConfusion
          (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))),
        if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)),
        sumColFar (j + 2) 2 3 (m + 4)
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 3 j))
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ
            (Nat.succ_le_succ (Nat.zero_le m))))) hk]
      exact (Nat.zero_add _).trans (Nat.add_zero _).symm

/-- The moved content `e₃ − e₁`, the sum family at the pair
`(1, 2)`. -/
def dE (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 2 then 1 else 0)
    (if i = 0 then 1 else 0))

/-- `dE` is the `D` sum family at the pair `(1, 2)`. -/
theorem dE_mem (l : Nat) (hl : 5 ≤ l) :
    row.thetaCount (sertables.tableD l) (dE l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | j + 1 =>
    show row.thetaCount (sertables.tableD (j + 6)) (dE (j + 6)) = 1
    have h0 : (0 : Nat) < j + 6 := Nat.succ_pos _
    have h1 : (1 : Nat) < j + 6 := Nat.succ_lt_succ (Nat.succ_pos _)
    have hc0 : (0 : Nat) + 3 < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hc1 : (1 : Nat) + 3 < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hc2 : (2 : Nat) + 3 < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hbe : (2 : Nat) ≤ j + 4 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 j)
    have h2e : (2 : Nat) < j + 4 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 j)
    have h3e : (3 : Nat) < j + 4 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 4 j)
    have hF0 : serstable.fSumD (j + 4) 1 2 0 = 0 :=
      serstable.fSumD_lo (j + 4) 1 2 0 (by decide +kernel) (by decide +kernel) hbe
    have hF1 : serstable.fSumD (j + 4) 1 2 1 = 1 :=
      serstable.fSumD_mid (j + 4) 1 2 1 (Nat.le_refl 1) (by decide +kernel) hbe
    have hF2 : serstable.fSumD (j + 4) 1 2 2 = 2 :=
      serstable.fSumD_two (j + 4) 1 2 2 (Nat.le_refl 2) h2e
    have hF3 : serstable.fSumD (j + 4) 1 2 3 = 2 :=
      serstable.fSumD_two (j + 4) 1 2 3 (by decide +kernel) h3e
    refine famOnePosD (j + 6) (serstable.fSumD (j + 4) 1 2)
      (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0)
      (memSumD (j + 4) 1 2 (Nat.lt_succ_self 1) hbe) (fun k hk => ?_) 0 h0
      (by decide +kernel)
    match k, hk with
    | 0, _ =>
      show (if (0 : Nat) = 2 then 1 else 0)
          + serstable.nbD (j + 6) (serstable.fSumD (j + 4) 1 2) 0
        = 2 * serstable.fSumD (j + 4) 1 2 0 + (if (0 : Nat) = 0 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 2), if_pos rfl,
        nbDchain (j + 6) _ 0 hc0, serstable.pvD_zero, hF1, hF0]
    | 1, _ =>
      show (if (1 : Nat) = 2 then 1 else 0)
          + serstable.nbD (j + 6) (serstable.fSumD (j + 4) 1 2) 1
        = 2 * serstable.fSumD (j + 4) 1 2 1 + (if (1 : Nat) = 0 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 2),
        if_neg (by decide +kernel : ¬ (1 : Nat) = 0),
        nbDchain (j + 6) _ 1 hc1,
        serstable.pvD_succ (serstable.fSumD (j + 4) 1 2) 0, hF0, hF2, hF1]
    | 2, _ =>
      show (if (2 : Nat) = 2 then 1 else 0)
          + serstable.nbD (j + 6) (serstable.fSumD (j + 4) 1 2) 2
        = 2 * serstable.fSumD (j + 4) 1 2 2 + (if (2 : Nat) = 0 then 1 else 0)
      rw [if_pos rfl, if_neg (by decide +kernel : ¬ (2 : Nat) = 0),
        nbDchain (j + 6) _ 2 hc2,
        serstable.pvD_succ (serstable.fSumD (j + 4) 1 2) 1, hF1, hF3, hF2]
    | m + 3, hk =>
      show (if m + 3 = 2 then 1 else 0)
          + serstable.nbD (j + 6) (serstable.fSumD (j + 4) 1 2) (m + 3)
        = 2 * serstable.fSumD (j + 4) 1 2 (m + 3) + (if m + 3 = 0 then 1 else 0)
      rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
        if_neg (fun hc => Nat.noConfusion hc),
        sumColFar (j + 1) 1 2 (m + 3)
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 2 j))
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ
            (Nat.zero_le m)))) hk]
      exact (Nat.zero_add _).trans (Nat.add_zero _).symm

/-- The moved content `e₁ − e₃ + e₄`, the sum family at the pair
`(0, 3)`. -/
def dF (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts
    (if i = 0 then 1 else if i = 3 then 1 else 0)
    (if i = 2 then 1 else 0))

/-- `dF` is the `D` sum family at the pair `(0, 3)`. -/
theorem dF_mem (l : Nat) (hl : 6 ≤ l) :
    row.thetaCount (sertables.tableD l) (dF l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | j + 1 =>
    show row.thetaCount (sertables.tableD (j + 7)) (dF (j + 7)) = 1
    have h0 : (0 : Nat) < j + 7 := Nat.succ_pos _
    have h1 : (1 : Nat) < j + 7 := Nat.succ_lt_succ (Nat.succ_pos _)
    have hc0 : (0 : Nat) + 3 < j + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 j)
    have hc1 : (1 : Nat) + 3 < j + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 j)
    have hc2 : (2 : Nat) + 3 < j + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 j)
    have hc3 : (3 : Nat) + 3 < j + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 j)
    have hbe : (3 : Nat) ≤ j + 5 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 j)
    have h3e : (3 : Nat) < j + 5 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 j)
    have h4e : (4 : Nat) < j + 5 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 5 j)
    have hF0 : serstable.fSumD (j + 5) 0 3 0 = 1 :=
      serstable.fSumD_mid (j + 5) 0 3 0 (Nat.le_refl 0) (by decide +kernel) hbe
    have hF1 : serstable.fSumD (j + 5) 0 3 1 = 1 :=
      serstable.fSumD_mid (j + 5) 0 3 1 (Nat.zero_le 1) (by decide +kernel) hbe
    have hF2 : serstable.fSumD (j + 5) 0 3 2 = 1 :=
      serstable.fSumD_mid (j + 5) 0 3 2 (Nat.zero_le 2) (by decide +kernel) hbe
    have hF3 : serstable.fSumD (j + 5) 0 3 3 = 2 :=
      serstable.fSumD_two (j + 5) 0 3 3 (Nat.le_refl 3) h3e
    have hF4 : serstable.fSumD (j + 5) 0 3 4 = 2 :=
      serstable.fSumD_two (j + 5) 0 3 4 (by decide +kernel) h4e
    refine famOnePosD (j + 7) (serstable.fSumD (j + 5) 0 3)
      (fun i => if i = 0 then 1 else if i = 3 then 1 else 0)
      (fun i => if i = 2 then 1 else 0)
      (memSumD (j + 5) 0 3 (by decide +kernel) hbe) (fun k hk => ?_) 0 h0
      (by decide +kernel)
    match k, hk with
    | 0, _ =>
      show (if (0 : Nat) = 0 then 1 else if (0 : Nat) = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 0 3) 0
        = 2 * serstable.fSumD (j + 5) 0 3 0 + (if (0 : Nat) = 2 then 1 else 0)
      rw [if_pos rfl, if_neg (by decide +kernel : ¬ (0 : Nat) = 2),
        nbDchain (j + 7) _ 0 hc0, serstable.pvD_zero, hF1, hF0]
    | 1, _ =>
      show (if (1 : Nat) = 0 then 1 else if (1 : Nat) = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 0 3) 1
        = 2 * serstable.fSumD (j + 5) 0 3 1 + (if (1 : Nat) = 2 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 0),
        if_neg (by decide +kernel : ¬ (1 : Nat) = 3),
        if_neg (by decide +kernel : ¬ (1 : Nat) = 2),
        nbDchain (j + 7) _ 1 hc1,
        serstable.pvD_succ (serstable.fSumD (j + 5) 0 3) 0, hF0, hF2, hF1]
    | 2, _ =>
      show (if (2 : Nat) = 0 then 1 else if (2 : Nat) = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 0 3) 2
        = 2 * serstable.fSumD (j + 5) 0 3 2 + (if (2 : Nat) = 2 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (2 : Nat) = 0),
        if_neg (by decide +kernel : ¬ (2 : Nat) = 3), if_pos rfl,
        nbDchain (j + 7) _ 2 hc2,
        serstable.pvD_succ (serstable.fSumD (j + 5) 0 3) 1, hF1, hF3, hF2]
    | 3, _ =>
      show (if (3 : Nat) = 0 then 1 else if (3 : Nat) = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 0 3) 3
        = 2 * serstable.fSumD (j + 5) 0 3 3 + (if (3 : Nat) = 2 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (3 : Nat) = 0), if_pos rfl,
        if_neg (by decide +kernel : ¬ (3 : Nat) = 2),
        nbDchain (j + 7) _ 3 hc3,
        serstable.pvD_succ (serstable.fSumD (j + 5) 0 3) 2, hF2, hF4, hF3]
    | m + 4, hk =>
      show (if m + 4 = 0 then 1 else if m + 4 = 3 then 1 else 0)
          + serstable.nbD (j + 7) (serstable.fSumD (j + 5) 0 3) (m + 4)
        = 2 * serstable.fSumD (j + 5) 0 3 (m + 4) + (if m + 4 = 2 then 1 else 0)
      rw [if_neg (fun hc => Nat.noConfusion hc),
        if_neg (fun hc => Nat.noConfusion
          (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))),
        if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
        sumColFar (j + 2) 0 3 (m + 4)
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 3 j))
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ
            (Nat.succ_le_succ (Nat.zero_le m))))) hk]
      exact (Nat.zero_add _).trans (Nat.add_zero _).symm

/-- The moved content `e₅ − e₃`, the sum family at the pair
`(3, 4)`. -/
def dG (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts (if i = 4 then 1 else 0)
    (if i = 2 then 1 else 0))

/-- `dG` is the `D` sum family at the pair `(3, 4)`. -/
theorem dG_mem (l : Nat) (hl : 7 ≤ l) :
    row.thetaCount (sertables.tableD l) (dG l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | j + 1 =>
    show row.thetaCount (sertables.tableD (j + 8)) (dG (j + 8)) = 1
    have h1 : (1 : Nat) < j + 8 := Nat.succ_lt_succ (Nat.succ_pos _)
    have h2 : (2 : Nat) < j + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 j)
    have hc0 : (0 : Nat) + 3 < j + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 j)
    have hc1 : (1 : Nat) + 3 < j + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 j)
    have hc2 : (2 : Nat) + 3 < j + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 j)
    have hc3 : (3 : Nat) + 3 < j + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 j)
    have hc4 : (4 : Nat) + 3 < j + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 j)
    have hbe : (4 : Nat) ≤ j + 6 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 j)
    have h4e : (4 : Nat) < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have h5e : (5 : Nat) < j + 6 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 6 j)
    have hF0 : serstable.fSumD (j + 6) 3 4 0 = 0 :=
      serstable.fSumD_lo (j + 6) 3 4 0 (by decide +kernel) (by decide +kernel) hbe
    have hF1 : serstable.fSumD (j + 6) 3 4 1 = 0 :=
      serstable.fSumD_lo (j + 6) 3 4 1 (by decide +kernel) (by decide +kernel) hbe
    have hF2 : serstable.fSumD (j + 6) 3 4 2 = 0 :=
      serstable.fSumD_lo (j + 6) 3 4 2 (by decide +kernel) (by decide +kernel) hbe
    have hF3 : serstable.fSumD (j + 6) 3 4 3 = 1 :=
      serstable.fSumD_mid (j + 6) 3 4 3 (Nat.le_refl 3) (by decide +kernel) hbe
    have hF4 : serstable.fSumD (j + 6) 3 4 4 = 2 :=
      serstable.fSumD_two (j + 6) 3 4 4 (Nat.le_refl 4) h4e
    have hF5 : serstable.fSumD (j + 6) 3 4 5 = 2 :=
      serstable.fSumD_two (j + 6) 3 4 5 (by decide +kernel) h5e
    refine famOnePosD (j + 8) (serstable.fSumD (j + 6) 3 4)
      (fun i => if i = 4 then 1 else 0) (fun i => if i = 2 then 1 else 0)
      (memSumD (j + 6) 3 4 (by decide +kernel) hbe) (fun k hk => ?_) 2 h2
      (by decide +kernel)
    match k, hk with
    | 0, _ =>
      show (if (0 : Nat) = 4 then 1 else 0)
          + serstable.nbD (j + 8) (serstable.fSumD (j + 6) 3 4) 0
        = 2 * serstable.fSumD (j + 6) 3 4 0 + (if (0 : Nat) = 2 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (0 : Nat) = 4),
        if_neg (by decide +kernel : ¬ (0 : Nat) = 2),
        nbDchain (j + 8) _ 0 hc0, serstable.pvD_zero, hF1, hF0]
    | 1, _ =>
      show (if (1 : Nat) = 4 then 1 else 0)
          + serstable.nbD (j + 8) (serstable.fSumD (j + 6) 3 4) 1
        = 2 * serstable.fSumD (j + 6) 3 4 1 + (if (1 : Nat) = 2 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (1 : Nat) = 4),
        if_neg (by decide +kernel : ¬ (1 : Nat) = 2),
        nbDchain (j + 8) _ 1 hc1,
        serstable.pvD_succ (serstable.fSumD (j + 6) 3 4) 0, hF0, hF2, hF1]
    | 2, _ =>
      show (if (2 : Nat) = 4 then 1 else 0)
          + serstable.nbD (j + 8) (serstable.fSumD (j + 6) 3 4) 2
        = 2 * serstable.fSumD (j + 6) 3 4 2 + (if (2 : Nat) = 2 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (2 : Nat) = 4), if_pos rfl,
        nbDchain (j + 8) _ 2 hc2,
        serstable.pvD_succ (serstable.fSumD (j + 6) 3 4) 1, hF1, hF3, hF2]
    | 3, _ =>
      show (if (3 : Nat) = 4 then 1 else 0)
          + serstable.nbD (j + 8) (serstable.fSumD (j + 6) 3 4) 3
        = 2 * serstable.fSumD (j + 6) 3 4 3 + (if (3 : Nat) = 2 then 1 else 0)
      rw [if_neg (by decide +kernel : ¬ (3 : Nat) = 4),
        if_neg (by decide +kernel : ¬ (3 : Nat) = 2),
        nbDchain (j + 8) _ 3 hc3,
        serstable.pvD_succ (serstable.fSumD (j + 6) 3 4) 2, hF2, hF4, hF3]
    | 4, _ =>
      show (if (4 : Nat) = 4 then 1 else 0)
          + serstable.nbD (j + 8) (serstable.fSumD (j + 6) 3 4) 4
        = 2 * serstable.fSumD (j + 6) 3 4 4 + (if (4 : Nat) = 2 then 1 else 0)
      rw [if_pos rfl, if_neg (by decide +kernel : ¬ (4 : Nat) = 2),
        nbDchain (j + 8) _ 4 hc4,
        serstable.pvD_succ (serstable.fSumD (j + 6) 3 4) 3, hF3, hF5, hF4]
    | m + 5, hk =>
      show (if m + 5 = 4 then 1 else 0)
          + serstable.nbD (j + 8) (serstable.fSumD (j + 6) 3 4) (m + 5)
        = 2 * serstable.fSumD (j + 6) 3 4 (m + 5) + (if m + 5 = 2 then 1 else 0)
      rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj
          (Nat.succ.inj (Nat.succ.inj hc))))),
        if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))),
        sumColFar (j + 3) 3 4 (m + 5)
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 j))
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ
            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m)))))) hk]
      exact (Nat.zero_add _).trans (Nat.add_zero _).symm

/-- The moved content `e₁ + e_{ℓ−1} − e_ℓ`, the difference family
at the leading key against the rank's last. -/
def dH (l : Nat) : List BPair :=
  nuOf l (fun i => BPair.ofCounts
    (if i = 0 then 1 else if i + 2 = l then 1 else 0)
    (if i + 1 = l then 1 else 0))

/-- `dH` is the `D` difference family at the leading key against
the rank's last. -/
theorem dH_mem (l : Nat) (hl : 3 ≤ l) :
    row.thetaCount (sertables.tableD l) (dH l) = 1 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | j + 1 =>
    show row.thetaCount (sertables.tableD (j + 4)) (dH (j + 4)) = 1
    have h0 : (0 : Nat) < j + 4 := Nat.succ_pos _
    have h1 : (1 : Nat) < j + 4 := Nat.succ_lt_succ (Nat.succ_pos _)
    have hlast : j + 3 < j + 4 := Nat.lt_succ_self _
    have hFin : ∀ i, i < j + 3 → serstable.fDiff 0 (j + 3) i = 1 :=
      fun i h => serstable.fDiff_in 0 (j + 3) i (Nat.zero_le i) h
    have hFhi : ∀ i, j + 3 ≤ i → serstable.fDiff 0 (j + 3) i = 0 :=
      fun i h => serstable.fDiff_hi 0 (j + 3) i (fun hc =>
        Nat.not_succ_le_self i (Nat.le_trans (Nat.succ_le_of_lt hc) h))
    have h45 : j + 1 < j + 3 :=
      Nat.lt_trans (Nat.lt_succ_self (j + 1)) (Nat.lt_succ_self (j + 2))
    have h55 : j + 2 < j + 3 := Nat.lt_succ_self (j + 2)
    have h35 : j < j + 3 := Nat.lt_trans (Nat.lt_succ_self (j)) h45
    refine famOnePosD (j + 4) (serstable.fDiff 0 (j + 3))
      (fun i => if i = 0 then 1 else if i + 2 = j + 4 then 1 else 0)
      (fun i => if i + 1 = j + 4 then 1 else 0)
      (memDiffD (j + 4) 0 (j + 3) (Nat.succ_pos _) hlast) (fun k hk => ?_) 0 h0
      (by rw [if_pos rfl, if_neg (litNe 1 j 4 (by decide +kernel))]
          exact (by decide +kernel))
    by_cases t1 : k + 1 = j + 4
    · have hke : k = j + 3 := Nat.succ.inj t1
      subst hke
      show (if j + 3 = 0 then 1 else if j + 3 + 2 = j + 4 then 1 else 0)
          + serstable.nbD (j + 4) (serstable.fDiff 0 (j + 3)) (j + 3)
        = 2 * serstable.fDiff 0 (j + 3) (j + 3)
          + (if j + 3 + 1 = j + 4 then 1 else 0)
      rw [if_neg (fun hc => Nat.noConfusion hc),
        if_neg (fun hc => Nat.ne_of_lt (Nat.lt_succ_self (j + 4)) hc.symm),
        if_pos rfl, nbDtopAt (j + 4) _ (j + 3) rfl,
        serstable.pv2D_succ2 (serstable.fDiff 0 (j + 3)) (j + 1),
        hFin (j + 1) h45, hFhi (j + 3) (Nat.le_refl _)]
    · by_cases t2 : k + 2 = j + 4
      · have hke : k = j + 2 := Nat.succ.inj (Nat.succ.inj t2)
        subst hke
        show (if j + 2 = 0 then 1 else if j + 2 + 2 = j + 4 then 1 else 0)
            + serstable.nbD (j + 4) (serstable.fDiff 0 (j + 3)) (j + 2)
          = 2 * serstable.fDiff 0 (j + 3) (j + 2)
            + (if j + 2 + 1 = j + 4 then 1 else 0)
        rw [if_neg (fun hc => Nat.noConfusion hc), if_pos rfl,
          if_neg (fun hc => Nat.ne_of_lt (Nat.lt_succ_self (j + 3)) hc),
          nbDsubAt (j + 4) _ (j + 2) rfl,
          serstable.pvD_succ (serstable.fDiff 0 (j + 3)) (j + 1),
          hFin (j + 1) h45, hFin (j + 2) h55]
      · by_cases t3 : k + 3 = j + 4
        · have hke : k = j + 1 :=
            Nat.succ.inj (Nat.succ.inj (Nat.succ.inj t3))
          subst hke
          show (if j + 1 = 0 then 1 else if j + 1 + 2 = j + 4 then 1 else 0)
              + serstable.nbD (j + 4) (serstable.fDiff 0 (j + 3)) (j + 1)
            = 2 * serstable.fDiff 0 (j + 3) (j + 1)
              + (if j + 1 + 1 = j + 4 then 1 else 0)
          rw [if_neg (fun hc => Nat.noConfusion hc),
            if_neg (fun hc => Nat.ne_of_lt (Nat.lt_succ_self (j + 3)) hc),
            if_neg (fun hc => Nat.ne_of_lt
              (Nat.lt_trans (Nat.lt_succ_self (j + 2))
                (Nat.lt_succ_self (j + 3))) hc),
            nbDforkAt (j + 4) _ (j + 1) rfl,
            serstable.pvD_succ (serstable.fDiff 0 (j + 3)) (j),
            hFin (j) h35, hFin (j + 2) h55,
            hFhi (j + 3) (Nat.le_refl _), hFin (j + 1) h45]
        · have s1 : k + 1 < j + 4 :=
            Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) t1
          have s2 : k + 2 < j + 4 :=
            Nat.lt_of_le_of_ne (Nat.succ_le_of_lt s1) t2
          have s3 : k + 3 < j + 4 :=
            Nat.lt_of_le_of_ne (Nat.succ_le_of_lt s2) t3
          match k, s3 with
          | 0, s3 =>
            show (if (0 : Nat) = 0 then 1
                else if (0 : Nat) + 2 = j + 4 then 1 else 0)
                + serstable.nbD (j + 4) (serstable.fDiff 0 (j + 3)) 0
              = 2 * serstable.fDiff 0 (j + 3) 0
                + (if (0 : Nat) + 1 = j + 4 then 1 else 0)
            rw [if_pos rfl, if_neg (litNe 1 j 4 (by decide +kernel)),
              nbDchain (j + 4) _ 0 s3, serstable.pvD_zero,
              hFin 1 (Nat.lt_of_lt_of_le (by decide +kernel)
                (Nat.le_add_left 3 j)),
              hFin 0 (Nat.lt_of_lt_of_le (by decide +kernel)
                (Nat.le_add_left 3 j))]
          | m + 1, s3 =>
            have hm3 : m + 3 < j + 3 := Nat.lt_of_succ_lt_succ s3
            have hm2 : m + 2 < j + 3 :=
              Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3
            have hm1 : m + 1 < j + 3 :=
              Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2
            have hm0 : m < j + 3 := Nat.lt_trans (Nat.lt_succ_self m) hm1
            show (if m + 1 = 0 then 1 else if m + 1 + 2 = j + 4 then 1 else 0)
                + serstable.nbD (j + 4) (serstable.fDiff 0 (j + 3)) (m + 1)
              = 2 * serstable.fDiff 0 (j + 3) (m + 1)
                + (if m + 1 + 1 = j + 4 then 1 else 0)
            rw [if_neg (fun hc => Nat.noConfusion hc),
              if_neg (fun hc => Nat.ne_of_lt
                (Nat.lt_trans hm3 (Nat.lt_succ_self (j + 3))) hc),
              if_neg (fun hc => Nat.ne_of_lt
                (Nat.lt_trans hm2 (Nat.lt_succ_self (j + 3))) hc),
              nbDchain (j + 4) _ (m + 1) s3,
              serstable.pvD_succ (serstable.fDiff 0 (j + 3)) m,
              hFin m hm0, hFin (m + 2) hm2, hFin (m + 1) hm1]

/-! ### The `D` letter devices -/

/-- The `D` family classes, `foldsD_cases`' three arms. -/
private def famCaseD (l : Nat) (F : Nat → Nat) : Prop :=
  (∃ a b, a < b ∧ b < l ∧ F = serstable.fDiff a b)
  ∨ (∃ e a b, l = e + 2 ∧ a < b ∧ b ≤ e ∧ F = serstable.fSumD e a b)
  ∨ (∃ e a, l = e + 2 ∧ a ≤ e ∧ F = serstable.fSumDt e a)

/-- The letter's vacant term at `D`: a raised content occupied
somewhere and parting from every family's column at some key, at
either limb, reads the vacant θ count. -/
private theorem termVanishD (l : Nat) (x : List BPair)
    (hu : ∃ k, k < l ∧ ¬ (ground.getAt BPair.unit x k).oneValue BPair.unit)
    (hpos : ∀ F : Nat → Nat, famCaseD l F →
      ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue
        (BPair.ofCounts (2 * F y) (serstable.nbD l F y)))
    (hneg : ∀ F : Nat → Nat, famCaseD l F →
      ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue
        (BPair.ofCounts (serstable.nbD l F y) (2 * F y))) :
    row.thetaCount (sertables.tableD l) x = 0 := by
  refine termVanishG (sertables.tableD l) x hu (fun j hj => ?_)
  have hjl : j < (sertables.foldsD l).length := hj
  obtain ⟨F, hfe, hcase⟩ := serstable.foldsD_cases l j hjl
  constructor
  · intro he
    obtain ⟨y, hy, hoff⟩ := hpos F hcase
    refine hoff ?_
    rw [he]
    exact serstable.posCorootV_entryD l j y F hy hfe
  · intro he
    obtain ⟨y, hy, hoff⟩ := hneg F hcase
    refine hoff ?_
    rw [he]
    exact serstable.negCorootV_entryD l j y F hy hfe

/-- A raised content whose entry at a key reads a magnitude past
two sits off the `D` θ list: every `D` family's column stays within
two of its neighbour fold (`serstable.colD_magLe`). -/
private theorem termVanishMagD (l k : Nat) (hk : k < l)
    (x : List BPair) (p q : Nat)
    (hx : (ground.getAt BPair.unit x k).oneValue (BPair.ofCounts p q))
    (hmag : q + 3 ≤ p ∨ p + 3 ≤ q) :
    row.thetaCount (sertables.tableD l) x = 0 := by
  refine termVanishD l x ⟨k, hk, fun hc => magNe p q hmag
      (BPair.ofCounts_unit.mp (BPair.oneValue_trans
        (BPair.oneValue_symm hx) hc))⟩
    (fun F hcase => ⟨k, hk, fun hc => ?_⟩)
    (fun F hcase => ⟨k, hk, fun hc => ?_⟩)
  · obtain ⟨hlo, hhi⟩ := serstable.colD_magLe F k l hk hcase
    exact magRefute p q (2 * F k) (serstable.nbD l F k)
      (ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx) hc))
      hlo hhi hmag
  · obtain ⟨hlo, hhi⟩ := serstable.colD_magLe F k l hk hcase
    exact magRefute p q (serstable.nbD l F k) (2 * F k)
      (ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx) hc))
      hhi hlo hmag

/-- A three-key refutation: a content matching a column read at
each of three keys is impossible, so it parts from it at one of
them. -/
private theorem pickOff3 (l : Nat) (x : List BPair) (G : Nat → BPair)
    (k0 k1 k2 : Nat) (h0 : k0 < l) (h1 : k1 < l) (h2 : k2 < l)
    (hall : (ground.getAt BPair.unit x k0).oneValue (G k0) →
      (ground.getAt BPair.unit x k1).oneValue (G k1) →
      (ground.getAt BPair.unit x k2).oneValue (G k2) → False) :
    ∃ y, y < l ∧ ¬ (ground.getAt BPair.unit x y).oneValue (G y) := by
  by_cases c0 : (ground.getAt BPair.unit x k0).oneValue (G k0)
  · by_cases c1 : (ground.getAt BPair.unit x k1).oneValue (G k1)
    · exact ⟨k2, h2, fun c2 => hall c0 c1 c2⟩
    · exact ⟨k1, h1, c1⟩
  · exact ⟨k0, h0, c0⟩

/-- The `D` raised content's count reads at a key: the moved
content's counts raised by the scaled Cartan entry's. -/
private theorem raisedCountD (l : Nat) (u v : Nat → Nat) (c i y : Nat)
    (hi : i < l) (hy : y < l) (p q : Nat)
    (hcart : (serstable.cartD l i y).oneValue (BPair.ofCounts p q)) :
    (ground.getAt BPair.unit
      (raisedG (sertables.tableD l)
        (nuOf l (fun k => BPair.ofCounts (u k) (v k))) c i) y).oneValue
      (BPair.ofCounts (u y + c * p) (v y + c * q)) := by
  refine raisedCountG (sertables.tableD l) u v c i y hy ?_ p q ?_
  · rw [serstable.cartD_eq l]
    exact ground.matOf_rowLength [] l l
      (fun p q => serstable.cartD l p q) i hi
  · have hcent : ground.getAt BPair.unit
        (ground.getAt [] (sertables.tableD l).cartan i) y
        = serstable.cartD l i y := by
      rw [serstable.cartD_eq l]
      exact ground.matOf_entry [] BPair.unit l l
        (fun p q => serstable.cartD l p q) i y hi hy
    rw [hcent]
    exact hcart

/-- The `D` Cartan row's diagonal entry as a count pair. -/
private theorem cartDiagD (l i : Nat) :
    (serstable.cartD l i i).oneValue (BPair.ofCounts 2 0) := by
  rw [serstable.cartDd l i]
  exact (by decide +kernel)

/-- The `D` Cartan row's upper neighbour along the chain. -/
private theorem cartUpD (l i : Nat) (h2 : ¬ i + 1 = l) (h3 : ¬ i + 2 = l) :
    (serstable.cartD l i (i + 1)).oneValue (BPair.ofCounts 0 1) := by
  rw [serstable.cartDup l i h2 h3]
  exact (by decide +kernel)

/-- The `D` Cartan row's lower neighbour along the chain. -/
private theorem cartDnD (l i : Nat) (h2 : ¬ i + 2 = l) (h3 : ¬ i + 1 = l) :
    (serstable.cartD l (i + 1) i).oneValue (BPair.ofCounts 0 1) := by
  rw [serstable.cartDdn l i h2 h3]
  exact (by decide +kernel)

/-- The `D` Cartan row at the fork key against the last key. -/
private theorem cartForkTD (l i j : Nat) (h1 : ¬ j = i) (h2 : ¬ i + 1 = l)
    (h3 : j + 1 = l) (h4 : i + 3 = l) :
    (serstable.cartD l i j).oneValue (BPair.ofCounts 0 1) := by
  rw [serstable.cartDforkT l i j h1 h2 h3 h4]
  exact (by decide +kernel)

/-- The `D` Cartan row is vacant off the letter's joined keys. -/
private theorem cartOffD (l i j : Nat) (h1 : ¬ j = i)
    (h2 : i + 1 = l → ¬ j + 3 = l)
    (h3 : ¬ i + 1 = l → j + 1 = l → ¬ i + 3 = l)
    (h4 : ¬ i + 1 = l → ¬ j + 1 = l → ¬ j + 1 = i)
    (h5 : ¬ i + 1 = l → ¬ j + 1 = l → ¬ j = i + 1) :
    (serstable.cartD l i j).oneValue (BPair.ofCounts 0 0) := by
  rw [serstable.cartDoff l i j h1 h2 h3 h4 h5]
  exact (by decide +kernel)

/-! ### The `D` families' caps and window steps -/

/-- The `D` sum family's generic member at its three windows. -/
private theorem sumSplitD (e a b k : Nat) :
    serstable.fSumD e a b k
      = serstable.fDiff a b k
        + ((serstable.fDiff b e k + serstable.fDiff b e k)
          + serstable.fDiff e (e + 2) k) := rfl

/-- The `D` sum family's last-coordinate member at its two
windows. -/
private theorem sumSplitDt (e a k : Nat) :
    serstable.fSumDt e a k
      = serstable.fDiff a e k + serstable.fDiff (e + 1) (e + 2) k := rfl

/-- The `D` sum family's generic member is occupied at the key
below its window's top. -/
private theorem dsumPrev (e a b k : Nat) (hab : a < b) (hbk : b ≤ k + 1)
    (hbe : b ≤ e) (hk : k < e) : 1 ≤ serstable.fSumD e a b k := by
  by_cases hbk2 : b ≤ k
  · exact Nat.le_trans (by decide +kernel)
      (Nat.le_of_eq (serstable.fSumD_two e a b k hbk2 hk).symm)
  · have hbk3 : b = k + 1 :=
      Nat.le_antisymm hbk (Nat.succ_le_of_lt (Nat.lt_of_not_le hbk2))
    have hab2 : a < k + 1 := by rw [← hbk3]; exact hab
    have hkb : k < b := by rw [hbk3]; exact Nat.lt_succ_self k
    exact Nat.le_of_eq
      (serstable.fSumD_mid e a b k (Nat.le_of_lt_succ hab2) hkb hbe).symm

/-- The `D` sum family's generic member carries its run value one
key up. -/
private theorem dsumStep (e a b k : Nat) (hab : a < b) (hbe : b ≤ e)
    (h2 : serstable.fSumD e a b k = 2) (hk1 : k + 1 < e) :
    serstable.fSumD e a b (k + 1) = 2 := by
  by_cases hbk : b ≤ k
  · exact serstable.fSumD_two e a b (k + 1) (Nat.le_trans hbk (Nat.le_succ k)) hk1
  · have hkb : k < b := Nat.lt_of_not_le hbk
    by_cases hak : a ≤ k
    · exact absurd (h2.symm.trans
          (serstable.fSumD_mid e a b k hak hkb hbe))
        (by decide +kernel)
    · exact absurd (h2.symm.trans
          (serstable.fSumD_lo e a b k (Nat.lt_of_not_le hak) hab hbe))
        (by decide +kernel)

/-! ### The `D` chain interior's plus-two devices -/

/-- A raised content reading plus two at an interior letter's own
key sits at the narrow window `fDiff (m+1) (m+2)` or nowhere: no
`D` family's column reads plus two at a chain key otherwise. -/
private theorem termVanishTwoD (l m : Nat) (hml : m + 4 < l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x (m + 1)).oneValue (BPair.ofCounts 2 0))
    (y : Nat) (hy : y < l)
    (hoff : ¬ (ground.getAt BPair.unit x y).oneValue
      (BPair.ofCounts (2 * serstable.fDiff (m + 1) (m + 2) y)
        (serstable.nbD l (serstable.fDiff (m + 1) (m + 2)) y))) :
    row.thetaCount (sertables.tableD l) x = 0 := by
  have hm3l : m + 3 < l := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
  have hm2l : m + 2 < l := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
  have hm1l : m + 1 < l := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
  refine termVanishD l x
    ⟨m + 1, hm1l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · refine pickOff2 l x
      (fun w => BPair.ofCounts (2 * F w) (serstable.nbD l F w))
      (m + 1) y hm1l hy (fun c1 c2 => ?_)
    refine hoff ?_
    have hFn : F = serstable.fDiff (m + 1) (m + 2) := by
      have hcr : 2 + serstable.nbD l F (m + 1) = 2 * F (m + 1) + 0 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) c1)
      rw [nbDchain l F (m + 1) hml, serstable.pvD_succ F m] at hcr
      have hnat : 2 * F (m + 1) = F m + F (m + 2) + 2 :=
        (Nat.add_zero (2 * F (m + 1))).symm.trans
          (hcr.symm.trans (Nat.add_comm 2 (F m + F (m + 2))))
      exact serstable.narrowOfTwoD l m F hml hcase hnat
    rw [hFn] at c2
    exact c2
  · refine ⟨m + 1, hm1l, fun hc => ?_⟩
    have hcr : 2 + 2 * F (m + 1) = serstable.nbD l F (m + 1) + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)
    rw [nbDchain l F (m + 1) hml, serstable.pvD_succ F m] at hcr
    have hnat : F m + F (m + 2) = 2 * F (m + 1) + 2 :=
      (Nat.add_zero (F m + F (m + 2))).symm.trans
        (hcr.symm.trans (Nat.add_comm 2 (2 * F (m + 1))))
    exact serstable.colD_notNegTwo l m F hml hcase hnat

/-- The narrow window's column below its own key reads minus one at
the `D` neighbour fold. -/
private theorem narrowBelowD (l m : Nat) (hml : m + 4 < l) :
    2 * serstable.fDiff (m + 1) (m + 2) m = 0
    ∧ serstable.nbD l (serstable.fDiff (m + 1) (m + 2)) m = 1 := by
  have hm3l : m + 3 < l := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
  have hz : ∀ k, ¬ k = m + 1 → serstable.fDiff (m + 1) (m + 2) k = 0 := by
    intro k hk
    match Nat.lt_or_ge k (m + 1) with
    | .inl h =>
      exact serstable.fDiff_lo (m + 1) (m + 2) k (fun hc =>
        Nat.not_succ_le_self k (Nat.le_trans (Nat.succ_le_of_lt h) hc))
    | .inr h =>
      exact serstable.fDiff_hi (m + 1) (m + 2) k (fun hc =>
        hk (Nat.le_antisymm (Nat.le_of_lt_succ hc) h))
  have hone : serstable.fDiff (m + 1) (m + 2) (m + 1) = 1 :=
    serstable.fDiff_in (m + 1) (m + 2) (m + 1) (Nat.le_refl _)
      (Nat.lt_succ_self _)
  refine ⟨by rw [hz m (Nat.ne_of_lt (Nat.lt_succ_self m))], ?_⟩
  rw [nbDchain l _ m hm3l,
    serstable.pvD_zeroOf (serstable.fDiff (m + 1) (m + 2)) m
      (fun i hi => hz i (by
        intro hx
        rw [hx] at hi
        exact absurd hi (Nat.ne_of_lt
          (Nat.lt_trans (Nat.lt_succ_self m) (Nat.lt_succ_self (m + 1)))))),
    hone]

/-- The interior plus-two device read at the key below the
letter. -/
private theorem termTwoBelowD (l m : Nat) (hml : m + 4 < l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x (m + 1)).oneValue (BPair.ofCounts 2 0))
    (A B : Nat)
    (hm : (ground.getAt BPair.unit x m).oneValue (BPair.ofCounts A B))
    (hne : ¬ A + 1 = 0 + B) :
    row.thetaCount (sertables.tableD l) x = 0 := by
  obtain ⟨hz, ho⟩ := narrowBelowD l m hml
  refine termVanishTwoD l m hml x h2 m
    (Nat.lt_of_le_of_lt (Nat.le_add_right m 4) hml) (fun hc => hne ?_)
  rw [hz, ho] at hc
  exact ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hm) hc)

/-- The interior plus-two device read at a key off the narrow
window's three: the window's column is vacant there, so an occupied
entry parts from it. -/
private theorem termTwoOffD (l m : Nat) (hml : m + 4 < l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x (m + 1)).oneValue (BPair.ofCounts 2 0))
    (y : Nat) (hy : y < l) (hy0 : ¬ y = m) (hy1 : ¬ y = m + 1)
    (hy2 : ¬ y = m + 2)
    (hocc : ¬ (ground.getAt BPair.unit x y).oneValue BPair.unit) :
    row.thetaCount (sertables.tableD l) x = 0 := by
  refine termVanishTwoD l m hml x h2 y hy (fun hc => hocc ?_)
  rw [← serstable.fDiffD_narrow_off m l y hml hy hy0 hy1 hy2] at hc
  exact BPair.oneValue_trans hc (BPair.ofCounts_unit.mpr rfl)

/-! ### The `D` leading key's plus-two device -/

/-- A content reading two at the leading key sits at the leading
narrow window `fDiff 0 1`: no other `D` family's column reads two
there. -/
private theorem headNarrowD (l : Nat) (hl : 4 ≤ l) (F : Nat → Nat)
    (hcase : famCaseD l F) (hnat : 2 * F 0 = F 1 + 2) :
    F = serstable.fDiff 0 1 := by
  match hcase with
  | .inl ⟨a, b, _, _, hF⟩ =>
    have hle : F 0 ≤ 1 := by rw [hF]; exact serstable.fDiff_le1 a b 0
    obtain ⟨hf0, hf1⟩ := headPair hle hnat
    rw [hF] at hf0 hf1
    obtain ⟨ha, hb⟩ := dHeadOne hf0
    have hb1 : b = 1 := by
      match Nat.lt_or_ge 1 b with
      | .inl hlt =>
        have hone : serstable.fDiff a b 1 = 1 :=
          serstable.fDiff_in a b 1 (by rw [ha]; exact Nat.zero_le 1) hlt
        rw [hf1] at hone
        exact absurd hone (by decide +kernel)
      | .inr hge => exact Nat.le_antisymm hge hb
    rw [hF, ha, hb1]
  | .inr (.inl ⟨e, a, b, hle', hab, hbe, hF⟩) =>
    have h2e : 2 ≤ e := by
      rw [hle'] at hl
      exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hl)
    have hb1 : 1 ≤ b :=
      Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le a) hab)
    have hbe0 : serstable.fDiff b e 0 = 0 :=
      serstable.fDiff_lo b e 0 (fun hc =>
        Nat.not_succ_le_zero 0 (Nat.le_trans hb1 hc))
    have hee0 : serstable.fDiff e (e + 2) 0 = 0 :=
      serstable.fDiff_lo e (e + 2) 0 (fun hc =>
        Nat.not_succ_le_zero 1 (Nat.le_trans h2e hc))
    have hF00 : F 0 = serstable.fDiff a b 0 := by
      rw [hF, sumSplitD e a b 0, hbe0, hee0]
      exact Nat.add_zero _
    have hle0 : F 0 ≤ 1 := by rw [hF00]; exact serstable.fDiff_le1 a b 0
    obtain ⟨hf0, hf1⟩ := headPair hle0 hnat
    rw [hF00] at hf0
    obtain ⟨ha, hb⟩ := dHeadOne hf0
    rw [hF, sumSplitD e a b 1] at hf1
    have hd1 : serstable.fDiff a b 1 = 0 := addZeroL hf1
    have hbe1 : serstable.fDiff b e 1 = 0 :=
      addZeroL (addZeroL (addZeroR hf1))
    have hb1' : b = 1 := by
      match Nat.lt_or_ge 1 b with
      | .inl hlt =>
        exact absurd (hd1.symm.trans (serstable.fDiff_in a b 1
          (by rw [ha]; exact Nat.zero_le 1) hlt)) (by decide +kernel)
      | .inr hge => exact Nat.le_antisymm hge hb
    exact absurd (hbe1.symm.trans (serstable.fDiff_in b e 1
      (by rw [hb1']; exact Nat.le_refl 1)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) h2e))) (by decide +kernel)
  | .inr (.inr ⟨e, a, hle', hae, hF⟩) =>
    have h2e : 2 ≤ e := by
      rw [hle'] at hl
      exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hl)
    have hee0 : serstable.fDiff (e + 1) (e + 2) 0 = 0 :=
      serstable.fDiff_lo (e + 1) (e + 2) 0 (fun hc =>
        Nat.not_succ_le_zero e hc)
    have hF00 : F 0 = serstable.fDiff a e 0 := by
      rw [hF, sumSplitDt e a 0, hee0]
      exact Nat.add_zero _
    have hle0 : F 0 ≤ 1 := by rw [hF00]; exact serstable.fDiff_le1 a e 0
    obtain ⟨hf0, hf1⟩ := headPair hle0 hnat
    rw [hF00] at hf0
    obtain ⟨ha, hb⟩ := dHeadOne hf0
    rw [hF, sumSplitDt e a 1] at hf1
    have hd1 : serstable.fDiff a e 1 = 0 := addZeroL hf1
    exact absurd (hd1.symm.trans (serstable.fDiff_in a e 1
      (by rw [ha]; exact Nat.zero_le 1)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) h2e))) (by decide +kernel)

/-- No `D` family's column reads minus two at the leading key. -/
private theorem headRefuseD (l : Nat) (hl : 4 ≤ l) (F : Nat → Nat)
    (hcase : famCaseD l F) (hnat : F 1 = 2 * F 0 + 2) : False := by
  match hcase with
  | .inl ⟨a, b, _, _, hF⟩ =>
    have hle := serstable.fDiff_le1 a b 1
    rw [← hF, hnat] at hle
    exact Nat.not_succ_le_self 1
      (Nat.le_trans (Nat.le_add_left 2 (2 * F 0)) hle)
  | .inr (.inl ⟨e, a, b, hle', hab, hbe, hF⟩) =>
    have h2e : 2 ≤ e := by
      rw [hle'] at hl
      exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hl)
    by_cases ha0 : a = 0
    · have hb : 0 < b := by rw [← ha0]; exact hab
      have hb1 : 1 ≤ b := hb
      have hF00 : F 0 = 1 := by
        rw [hF, sumSplitD e a b 0,
          serstable.fDiff_in a b 0 (by rw [ha0]; exact Nat.le_refl 0) hb,
          serstable.fDiff_lo b e 0 (fun hc =>
            Nat.not_succ_le_zero 0 (Nat.le_trans hb1 hc)),
          serstable.fDiff_lo e (e + 2) 0 (fun hc =>
            Nat.not_succ_le_zero 1 (Nat.le_trans h2e hc))]
      have hcap : F 1 ≤ 2 := by rw [hF]; exact serstable.fSumD_le2 e a b 1 hbe
      rw [hnat, hF00] at hcap
      exact absurd hcap (by decide +kernel)
    · have ha1 : 1 ≤ a := Nat.succ_le_of_lt
        (Nat.lt_of_le_of_ne (Nat.zero_le a) (fun hc => ha0 hc.symm))
      have hb2 : 2 ≤ b := Nat.le_trans (Nat.succ_le_succ ha1) hab
      have hbe1 : serstable.fDiff b e 1 = 0 :=
        serstable.fDiff_lo b e 1 (fun hc =>
          Nat.not_succ_le_self 1 (Nat.le_trans hb2 hc))
      have hee1 : serstable.fDiff e (e + 2) 1 = 0 :=
        serstable.fDiff_lo e (e + 2) 1 (fun hc =>
          Nat.not_succ_le_self 1 (Nat.le_trans h2e hc))
      have hF1 : F 1 = serstable.fDiff a b 1 := by
        rw [hF, sumSplitD e a b 1, hbe1, hee1]
        exact Nat.add_zero _
      have hle := serstable.fDiff_le1 a b 1
      rw [← hF1, hnat] at hle
      exact Nat.not_succ_le_self 1
        (Nat.le_trans (Nat.le_add_left 2 (2 * F 0)) hle)
  | .inr (.inr ⟨e, a, hle', hae, hF⟩) =>
    have h2e : 2 ≤ e := by
      rw [hle'] at hl
      exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hl)
    have hee1 : serstable.fDiff (e + 1) (e + 2) 1 = 0 :=
      serstable.fDiff_lo (e + 1) (e + 2) 1 (fun hc =>
        Nat.not_succ_le_self 1
          (Nat.le_trans (Nat.le_trans h2e (Nat.le_succ e)) hc))
    have hF1 : F 1 = serstable.fDiff a e 1 := by
      rw [hF, sumSplitDt e a 1, hee1]
      exact Nat.add_zero _
    have hle := serstable.fDiff_le1 a e 1
    rw [← hF1, hnat] at hle
    exact Nat.not_succ_le_self 1
      (Nat.le_trans (Nat.le_add_left 2 (2 * F 0)) hle)

/-- A raised content reading plus two at the leading key sits at
the leading narrow window or nowhere. -/
private theorem termVanishHeadTwoD (l : Nat) (hl : 4 ≤ l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x 0).oneValue (BPair.ofCounts 2 0))
    (y : Nat) (hy : y < l)
    (hoff : ¬ (ground.getAt BPair.unit x y).oneValue
      (BPair.ofCounts (2 * serstable.fDiff 0 1 y)
        (serstable.nbD l (serstable.fDiff 0 1) y))) :
    row.thetaCount (sertables.tableD l) x = 0 := by
  have h1l : 1 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have h0l : 0 < l := Nat.lt_trans (Nat.lt_succ_self 0) h1l
  have hc0 : (0 : Nat) + 3 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  refine termVanishD l x
    ⟨0, h0l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · refine pickOff2 l x
      (fun w => BPair.ofCounts (2 * F w) (serstable.nbD l F w))
      0 y h0l hy (fun c1 c2 => ?_)
    refine hoff ?_
    have hFn : F = serstable.fDiff 0 1 := by
      have hcr : 2 + serstable.nbD l F 0 = 2 * F 0 + 0 :=
        ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) c1)
      rw [nbDchain l F 0 hc0, serstable.pvD_zero, Nat.zero_add] at hcr
      exact headNarrowD l hl F hcase
        ((Nat.add_zero (2 * F 0)).symm.trans
          (hcr.symm.trans (Nat.add_comm 2 (F 1))))
    rw [hFn] at c2
    exact c2
  · refine ⟨0, h0l, fun hc => ?_⟩
    have hcr : 2 + 2 * F 0 = serstable.nbD l F 0 + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h2) hc)
    rw [nbDchain l F 0 hc0, serstable.pvD_zero, Nat.zero_add] at hcr
    exact headRefuseD l hl F hcase
      ((Nat.add_zero (F 1)).symm.trans
        (hcr.symm.trans (Nat.add_comm 2 (2 * F 0))))

/-- The leading narrow window's column at the second key reads
minus one. -/
private theorem headColOneD (l : Nat) (hl : 5 ≤ l) :
    2 * serstable.fDiff 0 1 1 = 0
    ∧ serstable.nbD l (serstable.fDiff 0 1) 1 = 1 := by
  have hz : ∀ k, 1 ≤ k → serstable.fDiff 0 1 k = 0 := fun k hk =>
    serstable.fDiff_hi 0 1 k (fun hc =>
      Nat.not_succ_le_zero 0 (Nat.le_trans hk (Nat.le_of_lt_succ hc)))
  have h0 : serstable.fDiff 0 1 0 = 1 :=
    serstable.fDiff_in 0 1 0 (Nat.le_refl 0) (Nat.lt_succ_self 0)
  have hc1 : (1 : Nat) + 3 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  refine ⟨by rw [hz 1 (Nat.le_refl 1)], ?_⟩
  rw [nbDchain l _ 1 hc1,
    serstable.pvD_succ (serstable.fDiff 0 1) 0, h0, hz 2 (by decide +kernel)]

/-- The leading narrow window's column is vacant past the second
key. -/
private theorem headColVacD (l y : Nat) (h2y : 2 ≤ y) (hy3 : y + 3 < l) :
    2 * serstable.fDiff 0 1 y = 0
    ∧ serstable.nbD l (serstable.fDiff 0 1) y = 0 := by
  have hz : ∀ k, 1 ≤ k → serstable.fDiff 0 1 k = 0 := fun k hk =>
    serstable.fDiff_hi 0 1 k (fun hc =>
      Nat.not_succ_le_zero 0 (Nat.le_trans hk (Nat.le_of_lt_succ hc)))
  refine ⟨by rw [hz y (Nat.le_trans (by decide +kernel) h2y)], ?_⟩
  rw [nbDchain l _ y hy3,
    serstable.pvD_zeroOf (serstable.fDiff 0 1) y (fun i hi => hz i
      (Nat.le_of_succ_le_succ (show 2 ≤ i + 1 by rw [← hi]; exact h2y))),
    hz (y + 1) (Nat.le_trans (Nat.le_trans (by decide +kernel) h2y)
      (Nat.le_succ y))]

/-- The leading-window device read at the second key. -/
private theorem headAtOneD (l : Nat) (hl : 5 ≤ l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x 0).oneValue (BPair.ofCounts 2 0))
    (A B : Nat)
    (h1 : (ground.getAt BPair.unit x 1).oneValue (BPair.ofCounts A B))
    (hne : ¬ A + 1 = 0 + B) :
    row.thetaCount (sertables.tableD l) x = 0 := by
  obtain ⟨hz, ho⟩ := headColOneD l hl
  refine termVanishHeadTwoD l (Nat.le_trans (by decide +kernel) hl) x h2 1
    (Nat.lt_of_lt_of_le (by decide +kernel) hl) (fun hc => hne ?_)
  rw [hz, ho] at hc
  exact ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm h1) hc)

/-- The leading-window device read at an occupied key past the
second. -/
private theorem headAtVacD (l y : Nat) (hl : 5 ≤ l) (h2y : 2 ≤ y)
    (hy3 : y + 3 < l) (x : List BPair)
    (h2 : (ground.getAt BPair.unit x 0).oneValue (BPair.ofCounts 2 0))
    (hocc : ¬ (ground.getAt BPair.unit x y).oneValue BPair.unit) :
    row.thetaCount (sertables.tableD l) x = 0 := by
  obtain ⟨hz, ho⟩ := headColVacD l y h2y hy3
  refine termVanishHeadTwoD l (Nat.le_trans (by decide +kernel) hl) x h2 y
    (Nat.lt_of_le_of_lt (Nat.le_add_right y 3) hy3) (fun hc => hocc ?_)
  rw [hz, ho] at hc
  exact BPair.oneValue_trans hc (BPair.ofCounts_unit.mpr rfl)

/-! ### The `D` tail letters: the fork and the two tips -/

/-- A doubled count reads two only at the unit count. -/
private theorem twoOne {n : Nat} (h : 2 * n = 2) : n = 1 := by
  match n with
  | 0 => exact absurd h (fun hc => Nat.noConfusion hc)
  | 1 => rfl
  | q + 2 =>
    exact absurd h (fun hc =>
      Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))

/-- A leading two cancels off a stated total. -/
private theorem twoPlus {X : Nat} (h : 2 + X = 2) : X = 0 :=
  ground.addCancelR 2 ((Nat.add_comm 2 X).symm.trans h)

/-- The `D` sum family's last-coordinate member vacant below the
fork is vacant at every key beneath. -/
private theorem dtLow (e a k j : Nat) (hk : k < e)
    (h0 : serstable.fSumDt e a k = 0) (hjk : j ≤ k) :
    serstable.fSumDt e a j = 0 := by
  rw [sumSplitDt e a k] at h0
  have hd : serstable.fDiff a e k = 0 := addZeroL h0
  have hna : ¬ a ≤ k := by
    intro hc
    exact absurd (hd.symm.trans (serstable.fDiff_in a e k hc hk))
      (by decide +kernel)
  rw [sumSplitDt e a j,
    serstable.fDiff_lo a e j (fun hc => hna (Nat.le_trans hc hjk)),
    serstable.fDiff_lo (e + 1) (e + 2) j (fun hc =>
      Nat.lt_irrefl e (Nat.lt_trans (Nat.le_trans hc hjk) hk))]

/-- The `D` Cartan row at a tail letter is vacant at the leading
keys. -/
private theorem cartTailOff (k i j : Nat) (h4i : k + 4 ≤ i)
    (hj3 : j + 3 ≤ k + 4) :
    (serstable.cartD (k + 7) i j).oneValue (BPair.ofCounts 0 0) := by
  have hj14 : j + 1 < k + 4 :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self (j + 1))
      (Nat.le_succ (j + 2))) hj3
  have hji : j + 1 < i := Nat.lt_of_lt_of_le hj14 h4i
  have hj7 : j + 3 < k + 7 :=
    Nat.lt_of_le_of_lt hj3
      (Nat.lt_trans (Nat.lt_succ_self (k + 4))
        (Nat.lt_trans (Nat.lt_succ_self (k + 5)) (Nat.lt_succ_self (k + 6))))
  have hj17 : j + 1 < k + 7 :=
    Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self (j + 1))
      (Nat.lt_succ_self (j + 2))) hj7
  exact cartOffD (k + 7) i j
    (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self j) hji))
    (fun _ hc => absurd hc (Nat.ne_of_lt hj7))
    (fun _ hc => absurd hc (Nat.ne_of_lt hj17))
    (fun _ _ => Nat.ne_of_lt hji)
    (fun _ _ => Nat.ne_of_lt
      (Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self j) hji)
        (Nat.lt_succ_self i)))

/-- The fork letter's refusal: a raised content reading plus two at
the fork against minus one at each tip, occupied at a leading key,
sits off the `D` θ list. -/
private theorem termForkD (k k0 p0 q0 : Nat) (hk03 : k0 + 3 ≤ k + 4)
    (x : List BPair)
    (hx0 : (ground.getAt BPair.unit x k0).oneValue (BPair.ofCounts p0 q0))
    (hne0 : ¬ p0 = q0)
    (hx4 : (ground.getAt BPair.unit x (k + 4)).oneValue (BPair.ofCounts 2 0))
    (hx5 : (ground.getAt BPair.unit x (k + 5)).oneValue (BPair.ofCounts 0 1))
    (hx6 : (ground.getAt BPair.unit x (k + 6)).oneValue (BPair.ofCounts 0 1)) :
    row.thetaCount (sertables.tableD (k + 7)) x = 0 := by
  have h1l : (1 : Nat) < k + 7 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
  have h6l : k + 6 < k + 7 := Nat.lt_succ_self (k + 6)
  have h5l : k + 5 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 5)) h6l
  have h4l : k + 4 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 4)) h5l
  have hk24 : k0 + 2 < k + 4 :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (k0 + 2)) hk03
  have hk14 : k0 + 1 < k + 4 := Nat.lt_trans (Nat.lt_succ_self (k0 + 1)) hk24
  have hk04 : k0 < k + 4 := Nat.lt_trans (Nat.lt_succ_self k0) hk14
  have hk0l : k0 < k + 7 := Nat.lt_trans hk04 h4l
  refine termVanishD (k + 7) x
    ⟨k + 4, h4l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm hx4) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · have nb6 : serstable.nbD (k + 7) F (k + 6) = F (k + 4) := by
      rw [nbDtopAt (k + 7) F (k + 6) rfl, serstable.pv2D_succ2 F (k + 4)]
    have nb5 : serstable.nbD (k + 7) F (k + 5) = F (k + 4) := by
      rw [nbDsubAt (k + 7) F (k + 5) rfl, serstable.pvD_succ F (k + 4)]
    have nb4 : serstable.nbD (k + 7) F (k + 4)
        = F (k + 3) + F (k + 5) + F (k + 6) := by
      rw [nbDforkAt (k + 7) F (k + 4) rfl, serstable.pvD_succ F (k + 3)]
    refine pickOff (k + 7) x
      (fun w => BPair.ofCounts (2 * F w) (serstable.nbD (k + 7) F w))
      (k + 6) (k + 5) (k + 4) k0 h6l h5l h4l hk0l (fun c6 c5 c4 c0 => ?_)
    have e6 : 0 + serstable.nbD (k + 7) F (k + 6) = 2 * F (k + 6) + 1 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx6) c6)
    have e5 : 0 + serstable.nbD (k + 7) F (k + 5) = 2 * F (k + 5) + 1 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx5) c5)
    have e4 : 2 + serstable.nbD (k + 7) F (k + 4) = 2 * F (k + 4) + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx4) c4)
    have e0 : p0 + serstable.nbD (k + 7) F k0 = 2 * F k0 + q0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx0) c0)
    rw [nb6, Nat.zero_add] at e6
    rw [nb5, Nat.zero_add] at e5
    rw [nb4, Nat.add_zero] at e4
    match hcase with
    | .inl ⟨a, b, hab, hbl, hF⟩ =>
      have hf6 : F (k + 6) = 0 := by
        rw [hF]
        exact serstable.fDiff_hi a b (k + 6) (fun hc =>
          Nat.not_succ_le_self (k + 6)
            (Nat.le_trans (Nat.succ_le_of_lt hc) (Nat.le_of_lt_succ hbl)))
      rw [hf6] at e6
      have hf4 : F (k + 4) = 1 := e6
      rw [hf4] at e5
      have hf5 : F (k + 5) = 0 := ground.twoMulZero (Nat.succ.inj e5).symm
      rw [hf4, hf5, hf6] at e4
      have hf3 : F (k + 3) = 0 := twoPlus e4
      rw [hF] at hf4 hf5 hf3
      obtain ⟨ha4, hb4⟩ := dIn hf4
      have haa : k + 4 ≤ a := by
        match Nat.lt_or_ge (k + 3) a with
        | .inl hlt => exact hlt
        | .inr hge =>
          exact absurd (hf3.symm.trans (serstable.fDiff_in a b (k + 3) hge
            (Nat.lt_trans (Nat.lt_succ_self (k + 3)) hb4))) (by decide +kernel)
      have ha : a = k + 4 := Nat.le_antisymm ha4 haa
      have hz : ∀ i, i < k + 4 → F i = 0 := by
        intro i hi
        rw [hF]
        refine serstable.fDiff_lo a b i (fun hc => ?_)
        rw [ha] at hc
        exact Nat.not_succ_le_self i
          (Nat.le_trans (Nat.succ_le_of_lt hi) hc)
      have nb0 : serstable.nbD (k + 7) F k0 = 0 :=
        nbDvac (k + 7) F k0
          (fun i hi => hz i (Nat.lt_trans
            (show i < k0 by rw [← hi]; exact Nat.lt_succ_self i) hk04))
          (fun i hi => hz i (Nat.lt_trans
            (show i < k0 by
              rw [← hi]
              exact Nat.lt_trans (Nat.lt_succ_self i)
                (Nat.lt_succ_self (i + 1))) hk04))
          (hz (k0 + 1) hk14) (hz (k0 + 2) hk24)
      rw [nb0, hz k0 hk04, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e0
      exact hne0 e0
    | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hbe' : b ≤ k + 5 := by rw [← he]; exact hbe
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumD_end (k + 5) a b (k + 6) hbe' (Nat.le_succ (k + 5))
          (Nat.lt_succ_self (k + 6))
      rw [hf6] at e6
      have hf4 : F (k + 4) = 3 := e6
      have hcap : F (k + 4) ≤ 2 := by
        rw [hF, he]
        exact serstable.fSumD_le2 (k + 5) a b (k + 4) hbe'
      rw [hf4] at hcap
      exact absurd hcap (by decide +kernel)
    | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumDt_top (k + 5) a (k + 6) rfl
      rw [hf6] at e6
      have hf4 : F (k + 4) = 3 := e6
      have hcap : F (k + 4) ≤ 1 := by
        rw [hF, he]
        exact serstable.fSumDt_le1 (k + 5) a (k + 4)
      rw [hf4] at hcap
      exact absurd hcap (by decide +kernel)
  · have nb6 : serstable.nbD (k + 7) F (k + 6) = F (k + 4) := by
      rw [nbDtopAt (k + 7) F (k + 6) rfl, serstable.pv2D_succ2 F (k + 4)]
    have nb5 : serstable.nbD (k + 7) F (k + 5) = F (k + 4) := by
      rw [nbDsubAt (k + 7) F (k + 5) rfl, serstable.pvD_succ F (k + 4)]
    have nb4 : serstable.nbD (k + 7) F (k + 4)
        = F (k + 3) + F (k + 5) + F (k + 6) := by
      rw [nbDforkAt (k + 7) F (k + 4) rfl, serstable.pvD_succ F (k + 3)]
    refine pickOff3 (k + 7) x
      (fun w => BPair.ofCounts (serstable.nbD (k + 7) F w) (2 * F w))
      (k + 6) (k + 5) (k + 4) h6l h5l h4l (fun c6 c5 c4 => ?_)
    have e6 : 0 + 2 * F (k + 6) = serstable.nbD (k + 7) F (k + 6) + 1 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx6) c6)
    have e5 : 0 + 2 * F (k + 5) = serstable.nbD (k + 7) F (k + 5) + 1 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx5) c5)
    have e4 : 2 + 2 * F (k + 4) = serstable.nbD (k + 7) F (k + 4) + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx4) c4)
    rw [nb6, Nat.zero_add] at e6
    rw [nb5, Nat.zero_add] at e5
    rw [nb4, Nat.add_zero] at e4
    match hcase with
    | .inl ⟨a, b, hab, hbl, hF⟩ =>
      have hf6 : F (k + 6) = 0 := by
        rw [hF]
        exact serstable.fDiff_hi a b (k + 6) (fun hc =>
          Nat.not_succ_le_self (k + 6)
            (Nat.le_trans (Nat.succ_le_of_lt hc) (Nat.le_of_lt_succ hbl)))
      rw [hf6] at e6
      have hz : (0 : Nat) = F (k + 4) + 1 := e6
      exact absurd hz (fun hc => Nat.noConfusion hc)
    | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hbe' : b ≤ k + 5 := by rw [← he]; exact hbe
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumD_end (k + 5) a b (k + 6) hbe' (Nat.le_succ (k + 5))
          (Nat.lt_succ_self (k + 6))
      have hf5 : F (k + 5) = 1 := by
        rw [hF, he]
        exact serstable.fSumD_end (k + 5) a b (k + 5) hbe' (Nat.le_refl (k + 5))
          (Nat.lt_trans (Nat.lt_succ_self (k + 5)) (Nat.lt_succ_self (k + 6)))
      rw [hf6] at e6
      have hf4 : F (k + 4) = 1 := (Nat.succ.inj (show (2 : Nat) = F (k + 4) + 1
        from e6)).symm
      rw [hf4, hf5, hf6] at e4
      have hf3 : F (k + 3) = 2 :=
        (Nat.succ.inj (Nat.succ.inj (show (4 : Nat)
          = F (k + 3) + 1 + 1 from e4))).symm
      rw [hF, he] at hf3
      have hstep : serstable.fSumD (k + 5) a b (k + 4) = 2 :=
        dsumStep (k + 5) a b (k + 3) hab hbe' hf3 (Nat.lt_succ_self (k + 4))
      rw [hF, he, hstep] at hf4
      exact absurd hf4 (by decide +kernel)
    | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hf5 : F (k + 5) = 0 := by
        rw [hF, he]
        exact serstable.fSumDt_gap (k + 5) a (k + 5) rfl
      rw [hf5] at e5
      have hz : (0 : Nat) = F (k + 4) + 1 := e5
      exact absurd hz (fun hc => Nat.noConfusion hc)

/-- The second-last letter's refusal: a raised content reading plus
two at the sub tip, vacant at the last key, occupied at a leading
key, sits off the `D` θ list. -/
private theorem termSubD (k k0 p0 q0 : Nat) (hk03 : k0 + 3 ≤ k + 4)
    (x : List BPair)
    (hx0 : (ground.getAt BPair.unit x k0).oneValue (BPair.ofCounts p0 q0))
    (hne0 : ¬ p0 = q0)
    (hx5 : (ground.getAt BPair.unit x (k + 5)).oneValue (BPair.ofCounts 2 0))
    (hx6 : (ground.getAt BPair.unit x (k + 6)).oneValue
      (BPair.ofCounts 0 0)) :
    row.thetaCount (sertables.tableD (k + 7)) x = 0 := by
  have h1l : (1 : Nat) < k + 7 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
  have h6l : k + 6 < k + 7 := Nat.lt_succ_self (k + 6)
  have h5l : k + 5 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 5)) h6l
  have h4l : k + 4 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 4)) h5l
  have hk24 : k0 + 2 < k + 4 :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (k0 + 2)) hk03
  have hk14 : k0 + 1 < k + 4 := Nat.lt_trans (Nat.lt_succ_self (k0 + 1)) hk24
  have hk04 : k0 < k + 4 := Nat.lt_trans (Nat.lt_succ_self k0) hk14
  have h45 : k + 4 < k + 5 := Nat.lt_succ_self (k + 4)
  have hk25 : k0 + 2 < k + 5 := Nat.lt_trans hk24 h45
  have hk15 : k0 + 1 < k + 5 := Nat.lt_trans hk14 h45
  have hk05 : k0 < k + 5 := Nat.lt_trans hk04 h45
  have hk0l : k0 < k + 7 := Nat.lt_trans hk04 h4l
  refine termVanishD (k + 7) x
    ⟨k + 5, h5l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm hx5) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · have nb6 : serstable.nbD (k + 7) F (k + 6) = F (k + 4) := by
      rw [nbDtopAt (k + 7) F (k + 6) rfl, serstable.pv2D_succ2 F (k + 4)]
    have nb5 : serstable.nbD (k + 7) F (k + 5) = F (k + 4) := by
      rw [nbDsubAt (k + 7) F (k + 5) rfl, serstable.pvD_succ F (k + 4)]
    refine pickOff3 (k + 7) x
      (fun w => BPair.ofCounts (2 * F w) (serstable.nbD (k + 7) F w))
      (k + 6) (k + 5) k0 h6l h5l hk0l (fun c6 c5 c0 => ?_)
    have e6 : 0 + serstable.nbD (k + 7) F (k + 6) = 2 * F (k + 6) + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx6) c6)
    have e5 : 2 + serstable.nbD (k + 7) F (k + 5) = 2 * F (k + 5) + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx5) c5)
    have e0 : p0 + serstable.nbD (k + 7) F k0 = 2 * F k0 + q0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx0) c0)
    rw [nb6, Nat.zero_add, Nat.add_zero] at e6
    rw [nb5, Nat.add_zero] at e5
    match hcase with
    | .inl ⟨a, b, hab, hbl, hF⟩ =>
      have hf6 : F (k + 6) = 0 := by
        rw [hF]
        exact serstable.fDiff_hi a b (k + 6) (fun hc =>
          Nat.not_succ_le_self (k + 6)
            (Nat.le_trans (Nat.succ_le_of_lt hc) (Nat.le_of_lt_succ hbl)))
      rw [hf6] at e6
      have hf4 : F (k + 4) = 0 := e6
      rw [hf4] at e5
      have hf5 : F (k + 5) = 1 :=
        twoOne (show 2 * F (k + 5) = 2 from e5.symm)
      rw [hF] at hf4 hf5
      obtain ⟨ha5, hb5⟩ := dIn hf5
      have haa : k + 5 ≤ a := by
        match Nat.lt_or_ge (k + 4) a with
        | .inl hlt => exact hlt
        | .inr hge =>
          exact absurd (hf4.symm.trans (serstable.fDiff_in a b (k + 4) hge
            (Nat.lt_trans (Nat.lt_succ_self (k + 4)) hb5))) (by decide +kernel)
      have ha : a = k + 5 := Nat.le_antisymm ha5 haa
      have hz : ∀ i, i < k + 5 → F i = 0 := by
        intro i hi
        rw [hF]
        refine serstable.fDiff_lo a b i (fun hc => ?_)
        rw [ha] at hc
        exact Nat.not_succ_le_self i (Nat.le_trans (Nat.succ_le_of_lt hi) hc)
      have nb0 : serstable.nbD (k + 7) F k0 = 0 :=
        nbDvac (k + 7) F k0
          (fun i hi => hz i (Nat.lt_trans
            (show i < k0 by rw [← hi]; exact Nat.lt_succ_self i) hk05))
          (fun i hi => hz i (Nat.lt_trans
            (show i < k0 by
              rw [← hi]
              exact Nat.lt_trans (Nat.lt_succ_self i)
                (Nat.lt_succ_self (i + 1))) hk05))
          (hz (k0 + 1) hk15) (hz (k0 + 2) hk25)
      rw [nb0, hz k0 hk05, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at e0
      exact hne0 e0
    | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hbe' : b ≤ k + 5 := by rw [← he]; exact hbe
      have hf5 : F (k + 5) = 1 := by
        rw [hF, he]
        exact serstable.fSumD_end (k + 5) a b (k + 5) hbe' (Nat.le_refl (k + 5))
          (Nat.lt_trans (Nat.lt_succ_self (k + 5)) (Nat.lt_succ_self (k + 6)))
      rw [hf5] at e5
      have hf4 : F (k + 4) = 0 := twoPlus e5
      rw [hF, he] at hf4
      have hpos : 1 ≤ serstable.fSumD (k + 5) a b (k + 4) :=
        dsumPrev (k + 5) a b (k + 4) hab hbe' hbe' (Nat.lt_succ_self (k + 4))
      rw [hf4] at hpos
      exact absurd hpos (by decide +kernel)
    | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hf5 : F (k + 5) = 0 := by
        rw [hF, he]
        exact serstable.fSumDt_gap (k + 5) a (k + 5) rfl
      rw [hf5] at e5
      have hz : F (k + 4) + 2 = 0 :=
        (Nat.add_comm 2 (F (k + 4))).symm.trans e5
      exact absurd hz (fun hc => Nat.noConfusion hc)
  · have nb5 : serstable.nbD (k + 7) F (k + 5) = F (k + 4) := by
      rw [nbDsubAt (k + 7) F (k + 5) rfl, serstable.pvD_succ F (k + 4)]
    refine ⟨k + 5, h5l, fun hc => ?_⟩
    have e5 : 2 + 2 * F (k + 5) = F (k + 4) := by
      have h := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx5) hc)
      rw [nb5] at h
      exact h.trans (Nat.add_zero _)
    match hcase with
    | .inl ⟨a, b, _, _, hF⟩ =>
      have hle1 : 2 + 2 * F (k + 5) ≤ 1 := by
        rw [e5, hF]
        exact serstable.fDiff_le1 a b (k + 4)
      exact Nat.not_succ_le_self 1
        (Nat.le_trans (Nat.le_add_right 2 (2 * F (k + 5))) hle1)
    | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hbe' : b ≤ k + 5 := by rw [← he]; exact hbe
      have hf5 : F (k + 5) = 1 := by
        rw [hF, he]
        exact serstable.fSumD_end (k + 5) a b (k + 5) hbe' (Nat.le_refl (k + 5))
          (Nat.lt_trans (Nat.lt_succ_self (k + 5)) (Nat.lt_succ_self (k + 6)))
      rw [hf5] at e5
      have hf4 : F (k + 4) = 4 := e5.symm
      have hcap : F (k + 4) ≤ 2 := by
        rw [hF, he]
        exact serstable.fSumD_le2 (k + 5) a b (k + 4) hbe'
      rw [hf4] at hcap
      exact absurd hcap (by decide +kernel)
    | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hf5 : F (k + 5) = 0 := by
        rw [hF, he]
        exact serstable.fSumDt_gap (k + 5) a (k + 5) rfl
      rw [hf5] at e5
      have hf4 : F (k + 4) = 2 := e5.symm
      have hcap : F (k + 4) ≤ 1 := by
        rw [hF, he]
        exact serstable.fSumDt_le1 (k + 5) a (k + 4)
      rw [hf4] at hcap
      exact absurd hcap (by decide +kernel)

/-- The last letter's refusal: a raised content reading plus two at
the top tip, occupied at a leading key, sits off the `D` θ list. -/
private theorem termTopD (k k0 p0 q0 : Nat) (hk03 : k0 + 3 ≤ k + 4)
    (x : List BPair)
    (hx0 : (ground.getAt BPair.unit x k0).oneValue (BPair.ofCounts p0 q0))
    (hne0 : ¬ p0 = q0)
    (hx6 : (ground.getAt BPair.unit x (k + 6)).oneValue
      (BPair.ofCounts 2 0)) :
    row.thetaCount (sertables.tableD (k + 7)) x = 0 := by
  have h1l : (1 : Nat) < k + 7 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
  have h6l : k + 6 < k + 7 := Nat.lt_succ_self (k + 6)
  have hk24 : k0 + 2 < k + 4 :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (k0 + 2)) hk03
  have hk14 : k0 + 1 < k + 4 := Nat.lt_trans (Nat.lt_succ_self (k0 + 1)) hk24
  have hk04 : k0 < k + 4 := Nat.lt_trans (Nat.lt_succ_self k0) hk14
  have hk0l : k0 < k + 7 :=
    Nat.lt_trans hk04 (Nat.lt_trans (Nat.lt_succ_self (k + 4))
      (Nat.lt_trans (Nat.lt_succ_self (k + 5)) h6l))
  refine termVanishD (k + 7) x
    ⟨k + 6, h6l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm hx6) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · have nb6 : serstable.nbD (k + 7) F (k + 6) = F (k + 4) := by
      rw [nbDtopAt (k + 7) F (k + 6) rfl, serstable.pv2D_succ2 F (k + 4)]
    refine pickOff2 (k + 7) x
      (fun w => BPair.ofCounts (2 * F w) (serstable.nbD (k + 7) F w))
      (k + 6) k0 h6l hk0l (fun c6 c0 => ?_)
    have e6 : 2 + serstable.nbD (k + 7) F (k + 6) = 2 * F (k + 6) + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx6) c6)
    have e0 : p0 + serstable.nbD (k + 7) F k0 = 2 * F k0 + q0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx0) c0)
    rw [nb6, Nat.add_zero] at e6
    match hcase with
    | .inl ⟨a, b, hab, hbl, hF⟩ =>
      have hf6 : F (k + 6) = 0 := by
        rw [hF]
        exact serstable.fDiff_hi a b (k + 6) (fun hc =>
          Nat.not_succ_le_self (k + 6)
            (Nat.le_trans (Nat.succ_le_of_lt hc) (Nat.le_of_lt_succ hbl)))
      rw [hf6] at e6
      have hz : F (k + 4) + 2 = 0 :=
        (Nat.add_comm 2 (F (k + 4))).symm.trans e6
      exact absurd hz (fun hc => Nat.noConfusion hc)
    | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hbe' : b ≤ k + 5 := by rw [← he]; exact hbe
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumD_end (k + 5) a b (k + 6) hbe' (Nat.le_succ (k + 5))
          (Nat.lt_succ_self (k + 6))
      rw [hf6] at e6
      have hf4 : F (k + 4) = 0 := twoPlus e6
      rw [hF, he] at hf4
      have hpos : 1 ≤ serstable.fSumD (k + 5) a b (k + 4) :=
        dsumPrev (k + 5) a b (k + 4) hab hbe' hbe' (Nat.lt_succ_self (k + 4))
      rw [hf4] at hpos
      exact absurd hpos (by decide +kernel)
    | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumDt_top (k + 5) a (k + 6) rfl
      rw [hf6] at e6
      have hf4 : F (k + 4) = 0 := twoPlus e6
      rw [hF, he] at hf4
      have hzF : ∀ i, i ≤ k + 4 → F i = 0 := by
        intro i hi
        rw [hF, he]
        exact dtLow (k + 5) a (k + 4) i (Nat.lt_succ_self (k + 4)) hf4 hi
      have nb0 : serstable.nbD (k + 7) F k0 = 0 :=
        nbDvac (k + 7) F k0
          (fun i hi => hzF i (Nat.le_of_lt (Nat.lt_trans
            (show i < k0 by rw [← hi]; exact Nat.lt_succ_self i) hk04)))
          (fun i hi => hzF i (Nat.le_of_lt (Nat.lt_trans
            (show i < k0 by
              rw [← hi]
              exact Nat.lt_trans (Nat.lt_succ_self i)
                (Nat.lt_succ_self (i + 1))) hk04)))
          (hzF (k0 + 1) (Nat.le_of_lt hk14)) (hzF (k0 + 2) (Nat.le_of_lt hk24))
      rw [nb0, hzF k0 (Nat.le_of_lt hk04), Nat.mul_zero, Nat.add_zero,
        Nat.zero_add] at e0
      exact hne0 e0
  · have nb6 : serstable.nbD (k + 7) F (k + 6) = F (k + 4) := by
      rw [nbDtopAt (k + 7) F (k + 6) rfl, serstable.pv2D_succ2 F (k + 4)]
    refine ⟨k + 6, h6l, fun hc => ?_⟩
    have e6 : 2 + 2 * F (k + 6) = F (k + 4) := by
      have h := ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx6) hc)
      rw [nb6] at h
      exact h.trans (Nat.add_zero _)
    match hcase with
    | .inl ⟨a, b, _, _, hF⟩ =>
      have hle1 : 2 + 2 * F (k + 6) ≤ 1 := by
        rw [e6, hF]
        exact serstable.fDiff_le1 a b (k + 4)
      exact Nat.not_succ_le_self 1
        (Nat.le_trans (Nat.le_add_right 2 (2 * F (k + 6))) hle1)
    | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hbe' : b ≤ k + 5 := by rw [← he]; exact hbe
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumD_end (k + 5) a b (k + 6) hbe' (Nat.le_succ (k + 5))
          (Nat.lt_succ_self (k + 6))
      rw [hf6] at e6
      have hf4 : F (k + 4) = 4 := e6.symm
      have hcap : F (k + 4) ≤ 2 := by
        rw [hF, he]
        exact serstable.fSumD_le2 (k + 5) a b (k + 4) hbe'
      rw [hf4] at hcap
      exact absurd hcap (by decide +kernel)
    | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumDt_top (k + 5) a (k + 6) rfl
      rw [hf6] at e6
      have hf4 : F (k + 4) = 4 := e6.symm
      have hcap : F (k + 4) ≤ 1 := by
        rw [hF, he]
        exact serstable.fSumDt_le1 (k + 5) a (k + 4)
      rw [hf4] at hcap
      exact absurd hcap (by decide +kernel)

/-- The flipped spinor base's fork letter: a raised content reading
minus two at the top tip against the occupied leading key sits off
the `D` θ list. -/
private theorem termForkS1 (k : Nat) (x : List BPair)
    (hx0 : (ground.getAt BPair.unit x 0).oneValue (BPair.ofCounts 1 0))
    (hx6 : (ground.getAt BPair.unit x (k + 6)).oneValue
      (BPair.ofCounts 0 2)) :
    row.thetaCount (sertables.tableD (k + 7)) x = 0 := by
  have h1l : (1 : Nat) < k + 7 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
  have h0l : (0 : Nat) < k + 7 := Nat.lt_trans (Nat.lt_succ_self 0) h1l
  have h6l : k + 6 < k + 7 := Nat.lt_succ_self (k + 6)
  have hc0 : (0 : Nat) + 3 < k + 7 :=
    Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
  have h1k4 : (1 : Nat) ≤ k + 4 :=
    Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)
  refine termVanishD (k + 7) x
    ⟨k + 6, h6l, fun hc => absurd (BPair.ofCounts_unit.mp
      (BPair.oneValue_trans (BPair.oneValue_symm hx6) hc)) (by decide +kernel)⟩
    (fun F hcase => ?_) (fun F hcase => ?_)
  · have nb6 : serstable.nbD (k + 7) F (k + 6) = F (k + 4) := by
      rw [nbDtopAt (k + 7) F (k + 6) rfl, serstable.pv2D_succ2 F (k + 4)]
    refine ⟨k + 6, h6l, fun hc => ?_⟩
    have e6 : 0 + serstable.nbD (k + 7) F (k + 6) = 2 * F (k + 6) + 2 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx6) hc)
    rw [nb6, Nat.zero_add] at e6
    match hcase with
    | .inl ⟨a, b, _, hbl, hF⟩ =>
      have hf6 : F (k + 6) = 0 := by
        rw [hF]
        exact serstable.fDiff_hi a b (k + 6) (fun hcc =>
          Nat.not_succ_le_self (k + 6)
            (Nat.le_trans (Nat.succ_le_of_lt hcc) (Nat.le_of_lt_succ hbl)))
      rw [hf6] at e6
      have hf4 : F (k + 4) = 2 := e6
      have hle1 : F (k + 4) ≤ 1 := by rw [hF]; exact serstable.fDiff_le1 a b (k + 4)
      rw [hf4] at hle1
      exact absurd hle1 (by decide +kernel)
    | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hbe' : b ≤ k + 5 := by rw [← he]; exact hbe
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumD_end (k + 5) a b (k + 6) hbe' (Nat.le_succ (k + 5))
          (Nat.lt_succ_self (k + 6))
      rw [hf6] at e6
      have hf4 : F (k + 4) = 4 := e6
      have hcap : F (k + 4) ≤ 2 := by
        rw [hF, he]
        exact serstable.fSumD_le2 (k + 5) a b (k + 4) hbe'
      rw [hf4] at hcap
      exact absurd hcap (by decide +kernel)
    | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumDt_top (k + 5) a (k + 6) rfl
      rw [hf6] at e6
      have hf4 : F (k + 4) = 4 := e6
      have hcap : F (k + 4) ≤ 1 := by
        rw [hF, he]
        exact serstable.fSumDt_le1 (k + 5) a (k + 4)
      rw [hf4] at hcap
      exact absurd hcap (by decide +kernel)
  · have nb6 : serstable.nbD (k + 7) F (k + 6) = F (k + 4) := by
      rw [nbDtopAt (k + 7) F (k + 6) rfl, serstable.pv2D_succ2 F (k + 4)]
    have nb0 : serstable.nbD (k + 7) F 0 = F 1 := by
      rw [nbDchain (k + 7) F 0 hc0, serstable.pvD_zero]
      exact Nat.zero_add _
    refine pickOff2 (k + 7) x
      (fun w => BPair.ofCounts (serstable.nbD (k + 7) F w) (2 * F w))
      (k + 6) 0 h6l h0l (fun c6 c0 => ?_)
    have e6 : 0 + 2 * F (k + 6) = serstable.nbD (k + 7) F (k + 6) + 2 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx6) c6)
    have e0 : 1 + 2 * F 0 = serstable.nbD (k + 7) F 0 + 0 :=
      ground.BPair.ofCounts_cross (BPair.oneValue_trans (BPair.oneValue_symm hx0) c0)
    rw [nb6, Nat.zero_add] at e6
    rw [nb0, Nat.add_zero] at e0
    match hcase with
    | .inl ⟨a, b, _, hbl, hF⟩ =>
      have hf6 : F (k + 6) = 0 := by
        rw [hF]
        exact serstable.fDiff_hi a b (k + 6) (fun hcc =>
          Nat.not_succ_le_self (k + 6)
            (Nat.le_trans (Nat.succ_le_of_lt hcc) (Nat.le_of_lt_succ hbl)))
      rw [hf6] at e6
      have hz : (0 : Nat) = F (k + 4) + 2 := e6
      exact absurd hz (fun hc => Nat.noConfusion hc)
    | .inr (.inl ⟨e, a, b, hle, hab, hbe, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hbe' : b ≤ k + 5 := by rw [← he]; exact hbe
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumD_end (k + 5) a b (k + 6) hbe' (Nat.le_succ (k + 5))
          (Nat.lt_succ_self (k + 6))
      rw [hf6] at e6
      have hf4 : F (k + 4) = 0 :=
        (Nat.succ.inj (Nat.succ.inj
          (show (2 : Nat) = F (k + 4) + 2 from e6))).symm
      rw [hF, he] at hf4
      have hpos : 1 ≤ serstable.fSumD (k + 5) a b (k + 4) :=
        dsumPrev (k + 5) a b (k + 4) hab hbe' hbe' (Nat.lt_succ_self (k + 4))
      rw [hf4] at hpos
      exact absurd hpos (by decide +kernel)
    | .inr (.inr ⟨e, a, hle, hae, hF⟩) =>
      have he : e = k + 5 := (Nat.succ.inj (Nat.succ.inj hle)).symm
      have hf6 : F (k + 6) = 1 := by
        rw [hF, he]
        exact serstable.fSumDt_top (k + 5) a (k + 6) rfl
      rw [hf6] at e6
      have hf4 : F (k + 4) = 0 :=
        (Nat.succ.inj (Nat.succ.inj
          (show (2 : Nat) = F (k + 4) + 2 from e6))).symm
      rw [hF, he] at hf4
      have hf1 : F 1 = 0 := by
        rw [hF, he]
        exact dtLow (k + 5) a (k + 4) 1 (Nat.lt_succ_self (k + 4)) hf4 h1k4
      rw [hf1] at e0
      have hz : 2 * F 0 + 1 = 0 :=
        (Nat.add_comm 1 (2 * F 0)).symm.trans e0
      exact absurd hz (fun hc => Nat.noConfusion hc)

/-- The fork letter's vacant term at a builder vacant on the rank's
last three keys. -/
private theorem tailForkD (k k0 : Nat) (hk03 : k0 + 3 ≤ k + 4)
    (u v : Nat → Nat)
    (hu4 : u (k + 4) = 0) (hv4 : v (k + 4) = 0)
    (hu5 : u (k + 5) = 0) (hv5 : v (k + 5) = 0)
    (hu6 : u (k + 6) = 0) (hv6 : v (k + 6) = 0)
    (hne0 : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableD (k + 7))
      (raisedG (sertables.tableD (k + 7))
        (nuOf (k + 7) (fun i => BPair.ofCounts (u i) (v i))) 1
            (k + 4)) = 0 := by
  have h6l : k + 6 < k + 7 := Nat.lt_succ_self (k + 6)
  have h5l : k + 5 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 5)) h6l
  have h4l : k + 4 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 4)) h5l
  have hk0l : k0 < k + 7 :=
    Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self k0)
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self (k0 + 1))
        (Nat.le_succ (k0 + 2))) hk03)) h4l
  refine termForkD k k0 (u k0) (v k0) hk03 _ ?_ hne0 ?_ ?_ ?_
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 4) k0 h4l hk0l 0 0
        (cartTailOff k (k + 4) k0 (Nat.le_refl (k + 4)) hk03))
      (BPair.ofCounts_crossed ?_)
    rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 4) (k + 4) h4l h4l 2 0
        (cartDiagD (k + 7) (k + 4)))
      (BPair.ofCounts_crossed ?_)
    rw [hu4, hv4]
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 4) (k + 5) h4l h5l 0 1
        (cartUpD (k + 7) (k + 4) (Nat.ne_of_lt h5l) (Nat.ne_of_lt h6l)))
      (BPair.ofCounts_crossed ?_)
    rw [hu5, hv5]
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 4) (k + 6) h4l h6l 0 1
        (cartForkTD (k + 7) (k + 4) (k + 6)
          (fun hc => Nat.ne_of_lt
            (Nat.lt_trans (Nat.lt_succ_self (k + 4)) (Nat.lt_succ_self (k + 5)))
            hc.symm)
          (Nat.ne_of_lt h5l) rfl rfl))
      (BPair.ofCounts_crossed ?_)
    rw [hu6, hv6]

/-- The sub-tip letter's vacant term at a builder vacant on the
rank's last two keys. -/
private theorem tailSubD (k k0 : Nat) (hk03 : k0 + 3 ≤ k + 4)
    (u v : Nat → Nat)
    (hu5 : u (k + 5) = 0) (hv5 : v (k + 5) = 0)
    (hu6 : u (k + 6) = 0) (hv6 : v (k + 6) = 0)
    (hne0 : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableD (k + 7))
      (raisedG (sertables.tableD (k + 7))
        (nuOf (k + 7) (fun i => BPair.ofCounts (u i) (v i))) 1
            (k + 5)) = 0 := by
  have h6l : k + 6 < k + 7 := Nat.lt_succ_self (k + 6)
  have h5l : k + 5 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 5)) h6l
  have h4l : k + 4 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 4)) h5l
  have hk0l : k0 < k + 7 :=
    Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self k0)
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self (k0 + 1))
        (Nat.le_succ (k0 + 2))) hk03)) h4l
  refine termSubD k k0 (u k0) (v k0) hk03 _ ?_ hne0 ?_ ?_
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 5) k0 h5l hk0l 0 0
        (cartTailOff k (k + 5) k0 (Nat.le_succ (k + 4)) hk03))
      (BPair.ofCounts_crossed ?_)
    rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 5) (k + 5) h5l h5l 2 0
        (cartDiagD (k + 7) (k + 5)))
      (BPair.ofCounts_crossed ?_)
    rw [hu5, hv5]
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 5) (k + 6) h5l h6l 0 0
        (cartOffD (k + 7) (k + 5) (k + 6)
          (fun hc => Nat.ne_of_lt (Nat.lt_succ_self (k + 5)) hc.symm)
          (fun hc => absurd hc (Nat.ne_of_lt h6l))
          (fun _ _ hc => Nat.ne_of_lt (Nat.lt_succ_self (k + 7)) hc.symm)
          (fun _ hcc => absurd rfl hcc)
          (fun _ hcc => absurd rfl hcc)))
      (BPair.ofCounts_crossed ?_)
    rw [hu6, hv6]

/-- The top-tip letter's vacant term at a builder vacant at the
rank's last key. -/
private theorem tailTopD (k k0 : Nat) (hk03 : k0 + 3 ≤ k + 4)
    (u v : Nat → Nat)
    (hu6 : u (k + 6) = 0) (hv6 : v (k + 6) = 0)
    (hne0 : ¬ u k0 = v k0) :
    row.thetaCount (sertables.tableD (k + 7))
      (raisedG (sertables.tableD (k + 7))
        (nuOf (k + 7) (fun i => BPair.ofCounts (u i) (v i))) 1
            (k + 6)) = 0 := by
  have h6l : k + 6 < k + 7 := Nat.lt_succ_self (k + 6)
  have h4l : k + 4 < k + 7 :=
    Nat.lt_trans (Nat.lt_succ_self (k + 4))
      (Nat.lt_trans (Nat.lt_succ_self (k + 5)) h6l)
  have hk0l : k0 < k + 7 :=
    Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self k0)
      (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self (k0 + 1))
        (Nat.le_succ (k0 + 2))) hk03)) h4l
  refine termTopD k k0 (u k0) (v k0) hk03 _ ?_ hne0 ?_
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 6) k0 h6l hk0l 0 0
        (cartTailOff k (k + 6) k0
          (Nat.le_trans (Nat.le_succ (k + 4)) (Nat.le_succ (k + 5))) hk03))
      (BPair.ofCounts_crossed ?_)
    rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 6) (k + 6) h6l h6l 2 0
        (cartDiagD (k + 7) (k + 6)))
      (BPair.ofCounts_crossed ?_)
    rw [hu6, hv6]

/-- The flipped spinor base's fork letter at its own tail
occupancy. -/
private theorem tailForkS1D (k : Nat) (u v : Nat → Nat)
    (hu0 : u 0 = 1) (hv0 : v 0 = 0)
    (hu6 : u (k + 6) = 0) (hv6 : v (k + 6) = 1) :
    row.thetaCount (sertables.tableD (k + 7))
      (raisedG (sertables.tableD (k + 7))
        (nuOf (k + 7) (fun i => BPair.ofCounts (u i) (v i))) 1
            (k + 4)) = 0 := by
  have h6l : k + 6 < k + 7 := Nat.lt_succ_self (k + 6)
  have h5l : k + 5 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 5)) h6l
  have h4l : k + 4 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (k + 4)) h5l
  have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
  refine termForkS1 k _ ?_ ?_
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 4) 0 h4l h0l 0 0
        (cartTailOff k (k + 4) 0 (Nat.le_refl (k + 4))
          (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))))
      (BPair.ofCounts_crossed ?_)
    rw [hu0, hv0]
  · refine BPair.oneValue_trans
      (raisedCountD (k + 7) u v 1 (k + 4) (k + 6) h4l h6l 0 1
        (cartForkTD (k + 7) (k + 4) (k + 6)
          (fun hc => Nat.ne_of_lt
            (Nat.lt_trans (Nat.lt_succ_self (k + 4)) (Nat.lt_succ_self (k + 5)))
            hc.symm)
          (Nat.ne_of_lt h5l) rfl rfl))
      (BPair.ofCounts_crossed ?_)
    rw [hu6, hv6]

/-! ### The `D` sources' shifted keys -/

/-- The vector's three-box word's shifted key at the leading
coordinate. -/
private theorem kapD111_0 (l : Nat) (h : 0 < l) :
    ground.getAt 0 (serstable.memberRho [1, 1, 1] l) 0 = 1 := by
  rw [serstable.memberRhoAt [1, 1, 1] l 0 h]
  rfl

/-- The vector's three-box word's shifted key at the second
coordinate. -/
private theorem kapD111_1 (l : Nat) (h : 1 < l) :
    ground.getAt 0 (serstable.memberRho [1, 1, 1] l) 1 = 1 := by
  rw [serstable.memberRhoAt [1, 1, 1] l 1 h]
  rfl

/-- The vector's three-box word's shifted key at the third
coordinate. -/
private theorem kapD111_2 (l : Nat) (h : 2 < l) :
    ground.getAt 0 (serstable.memberRho [1, 1, 1] l) 2 = 2 := by
  rw [serstable.memberRhoAt [1, 1, 1] l 2 h]
  rfl

/-- The vector's three-box word's shifted key across the run and
the tail. -/
private theorem kapD111 (l k : Nat) (hk3 : 3 ≤ k) (hk : k < l) :
    ground.getAt 0 (serstable.memberRho [1, 1, 1] l) k = 1 :=
  serstable.memberRho_run [1, 1, 1] l k hk3 hk

/-- The flipped spinor base's once-raised word's shifted key at the
leading key. -/
private theorem kapS1H (l : Nat) (hl : 3 ≤ l) :
    ground.getAt 0 (basedRho [1] l 1) 0 = 2 := by
  have h0 : 0 < l := Nat.lt_of_lt_of_le (by decide +kernel) hl
  have hne : ¬ (0 + 1 + 1 = l) := by
    intro hc
    rw [← hc] at hl
    exact absurd hl (by decide +kernel)
  rw [basedRho_step [1] l 1 0 h0, basedM_entry [1] l 1 0 h0, if_neg hne]
  rfl

/-- The flipped spinor base's once-raised word's shifted key across
the run. -/
private theorem kapS1 (l i : Nat) (h1 : 1 ≤ i) (hi : i < l)
    (hne : ¬ i + 2 = l) : ground.getAt 0 (basedRho [1] l 1) i = 1 :=
  basedRho_run [1] l 1 i h1 hi hne

/-- The flipped spinor base's once-raised word's shifted key at the
flipped datum. -/
private theorem kapS1T (l q : Nat) (h1 : 1 ≤ q) (hi : q < l)
    (hq : q + 2 = l) : ground.getAt 0 (basedRho [1] l 1) q = 2 :=
  basedRho_datum [1] l 1 q h1 hi hq


/-- The unit sector's witness edge at `θ + (e₁ − e₂)`: the letter fold reads the vacant count, so the row's two graded counts part by one. -/
theorem edgeD_u1 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [1, 1] l) (dA l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | k + 4 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [1, 1] (k + 7)) (dA (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (serstable.memberRho [1, 1] (k + 7)) (dA (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapTh0 (k + 7) h0l]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 2 else 0) (fun i => if i = 1 then 1 else 0) 1 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapTh1 (k + 7) h1l]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 2 else 0) (fun i => if i = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 1 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapTh (k + 7) (m + 1) hm hm1]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 0 h0l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 0 then 2 else 0)
          (fun i => if i = 1 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 7)
          (fun i => if i = 0 then 2 else 0)
          (fun i => if i = 1 then 1 else 0) 0 h0l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapTh (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 2 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapTh (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 2 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapTh (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 2 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The unit sector's witness edge at `θ + (e₂ − e₁ + e₃)`. -/
theorem edgeD_u2 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [1, 1] l) (dB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | k + 3 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [1, 1] (k + 7)) (dB (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl5 : (5 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (serstable.memberRho [1, 1] (k + 7)) (dB (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapTh0 (k + 7) h0l]
        exact headAtOneD (k + 7) hl5 _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 0 0 h0l h0l 2 0
              (cartDiagD (k + 7) 0))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 0 1 h0l h1l 0 1
            (cartUpD (k + 7) 0 (litNe 1 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 1, _ =>
        rw [kapTh1 (k + 7) h1l]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      rw [kapTh (k + 7) (m + 1) hm hm1]
      match m, hm, hml, hm1 with
      | 0, hm, _, _ => exact absurd hm (by decide +kernel)
      | 1, _, hml, _ =>
        exact termTwoBelowD (k + 7) 1 hml _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 2 h2l h2l 2 0 (cartDiagD (k + 7) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 1 h2l h1l 0 1
            (cartDnD (k + 7) 1 (litNe 3 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | r + 2, _, hml, hm1 =>
        refine serstable.runVanishD (k + 7) (r + 2) _ hml
            (nuOf_length (k + 7) _) ?_ 1 h1l
          (Or.inl (Nat.succ_lt_succ (Nat.succ_pos r))) ?_
        · exact nuVac (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0)
            (r + 2 + 1) hm1
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))])
        · exact nuOcc (k + 7)
            (fun i => if i = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapTh (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapTh (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapTh (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The unit sector's witness edge at `θ + (e₁ − e₂ + e₃)`. -/
theorem edgeD_u3 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [1, 1] l) (dC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [1, 1] (k + 7)) (dC (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 3 (k + 1) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 3 + (k + 1) + 3
        rw [Nat.add_comm 3 (k + 1)])
      (by
        show k + 4 = 3 + (k + 1)
        rw [Nat.add_comm 3 (k + 1)])
      (serstable.memberRho [1, 1] (k + 7)) (dC (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapTh0 (k + 7) h0l]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapTh1 (k + 7) h1l]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | 2, _ =>
        rw [kapTh (k + 7) 2 (by decide +kernel) h2l]
        exact termVanishMagD (k + 7) 2 h2l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 2 2 h2l h2l 2 0
            (cartDiagD (k + 7) 2))
          (Or.inl (by decide +kernel))
      | m + 3, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 2 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapTh (k + 7) (m + 1) (Nat.le_trans (by decide +kernel) hm) hm1]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 0 h0l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel)), if_neg (fun hc => absurd
                (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 7)
          (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) 0 h0l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapTh (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapTh (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapTh (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The unit sector's witness edge at `θ + (e₄ − e₂)`. -/
theorem edgeD_u4 (l : Nat) (hl : 6 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [1, 1] l) (dD l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | k + 1 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [1, 1] (k + 7)) (dD (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h3l : (3 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl5 : (5 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 4 k 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 4 + k + 3
        rw [Nat.add_comm 4 k])
      (by
        show k + 4 = 4 + k
        rw [Nat.add_comm 4 k])
      (serstable.memberRho [1, 1] (k + 7)) (dD (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapTh0 (k + 7) h0l]
        exact headAtOneD (k + 7) hl5 _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 0 0 h0l h0l 2 0
              (cartDiagD (k + 7) 0))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 0 1 h0l h1l 0 1
            (cartUpD (k + 7) 0 (litNe 1 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 1, _ =>
        rw [kapTh1 (k + 7) h1l]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | 2, _ =>
        rw [kapTh (k + 7) 2 (by decide +kernel) h2l]
        exact termTwoBelowD (k + 7) 1
          (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)) _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 2 2 h2l h2l 2 0
              (cartDiagD (k + 7) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 2 1 h2l h1l 0 1
            (cartDnD (k + 7) 1 (litNe 3 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 3, _ =>
        rw [kapTh (k + 7) 3 (by decide +kernel) h3l]
        exact termVanishMagD (k + 7) 3 h3l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 3 3 h3l h3l 2 0
            (cartDiagD (k + 7) 3))
          (Or.inl (by decide +kernel))
      | m + 4, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 4 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 3 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapTh (k + 7) (m + 1) (Nat.le_trans (by decide +kernel) hm) hm1]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 1 h1l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 3 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel)), if_neg (fun hc => absurd
                (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 7)
          (fun i => if i = 3 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) 1 h1l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapTh (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 3 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapTh (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 3 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapTh (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 3 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))



/-- The vector sector's witness edge at `vector + (e₂ − e₁ + e₃)`. -/
theorem edgeD_v1 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [1] l) (dB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | k + 3 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [1] (k + 7)) (dB (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (serstable.memberRho [1] (k + 7)) (dB (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW1_0 (k + 7) h0l]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapW1 (k + 7) 1 (by decide +kernel) h1l]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      rw [kapW1 (k + 7) (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hm1]
      match m, hm, hml, hm1 with
      | 0, hm, _, _ => exact absurd hm (by decide +kernel)
      | 1, _, hml, _ =>
        exact termTwoBelowD (k + 7) 1 hml _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 2 h2l h2l 2 0 (cartDiagD (k + 7) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 1 h2l h1l 0 1
            (cartDnD (k + 7) 1 (litNe 3 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | r + 2, _, hml, hm1 =>
        refine serstable.runVanishD (k + 7) (r + 2) _ hml
            (nuOf_length (k + 7) _) ?_ 1 h1l
          (Or.inl (Nat.succ_lt_succ (Nat.succ_pos r))) ?_
        · exact nuVac (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0)
            (r + 2 + 1) hm1
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))])
        · exact nuOcc (k + 7)
            (fun i => if i = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW1 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW1 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapW1 (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The vector sector's witness edge at `vector + (e₃ − e₁)`. -/
theorem edgeD_v2 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [1] l) (dE l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [1] (k + 7)) (dE (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 3 (k + 1) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 3 + (k + 1) + 3
        rw [Nat.add_comm 3 (k + 1)])
      (by
        show k + 4 = 3 + (k + 1)
        rw [Nat.add_comm 3 (k + 1)])
      (serstable.memberRho [1] (k + 7)) (dE (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW1_0 (k + 7) h0l]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0) 2 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapW1 (k + 7) 1 (by decide +kernel) h1l]
        exact termTwoBelowD (k + 7) 0
          (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)) _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0) 1 1 1 h1l h1l 2 0
              (cartDiagD (k + 7) 1))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0) 1 1 0 h1l h0l 0 1
            (cartDnD (k + 7) 0 (litNe 2 k 7 (by decide +kernel))
              (litNe 1 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 2, _ =>
        rw [kapW1 (k + 7) 2 (by decide +kernel) h2l]
        exact termVanishMagD (k + 7) 2 h2l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0) 1 2 2 h2l h2l 2 0
            (cartDiagD (k + 7) 2))
          (Or.inl (by decide +kernel))
      | m + 3, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 2 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapW1 (k + 7) (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hm1]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 0 h0l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 2 then 1 else 0)
          (fun i => if i = 0 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel)), if_neg (fun hc => Nat.noConfusion hc)])
      · exact nuOcc (k + 7)
          (fun i => if i = 2 then 1 else 0)
          (fun i => if i = 0 then 1 else 0) 0 h0l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW1 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 2 then 1 else 0)
            (fun i => if i = 0 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc))
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc)) (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW1 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 2 then 1 else 0)
            (fun i => if i = 0 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc)) (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapW1 (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 2 then 1 else 0)
            (fun i => if i = 0 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc)) (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The vector sector's witness edge at the leading word plus `e₁ − e₂`. -/
theorem edgeD_v3 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [2, 1] l) (dA l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | k + 4 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [2, 1] (k + 7)) (dA (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (serstable.memberRho [2, 1] (k + 7)) (dA (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW21_0 (k + 7) h0l]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 2 else 0) (fun i => if i = 1 then 1 else 0) 2 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapW21_1 (k + 7) h1l]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 2 else 0) (fun i => if i = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 1 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapW21 (k + 7) (m + 1) hm hm1]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 0 h0l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 0 then 2 else 0)
          (fun i => if i = 1 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 7)
          (fun i => if i = 0 then 2 else 0)
          (fun i => if i = 1 then 1 else 0) 0 h0l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW21 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 2 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW21 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 2 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapW21 (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 2 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The vector sector's witness edge at the leading word plus `e₂ − e₁ + e₃`. -/
theorem edgeD_v4 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [2, 1] l) (dB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | k + 3 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [2, 1] (k + 7)) (dB (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (serstable.memberRho [2, 1] (k + 7)) (dB (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW21_0 (k + 7) h0l]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapW21_1 (k + 7) h1l]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      rw [kapW21 (k + 7) (m + 1) hm hm1]
      match m, hm, hml, hm1 with
      | 0, hm, _, _ => exact absurd hm (by decide +kernel)
      | 1, _, hml, _ =>
        exact termTwoBelowD (k + 7) 1 hml _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 2 h2l h2l 2 0 (cartDiagD (k + 7) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 1 h2l h1l 0 1
            (cartDnD (k + 7) 1 (litNe 3 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | r + 2, _, hml, hm1 =>
        refine serstable.runVanishD (k + 7) (r + 2) _ hml
            (nuOf_length (k + 7) _) ?_ 1 h1l
          (Or.inl (Nat.succ_lt_succ (Nat.succ_pos r))) ?_
        · exact nuVac (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0)
            (r + 2 + 1) hm1
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))])
        · exact nuOcc (k + 7)
            (fun i => if i = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW21 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW21 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapW21 (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The vector sector's witness edge at the leading word plus `e₁ − e₂ + e₃`. -/
theorem edgeD_v5 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [2, 1] l) (dC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [2, 1] (k + 7)) (dC (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 3 (k + 1) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 3 + (k + 1) + 3
        rw [Nat.add_comm 3 (k + 1)])
      (by
        show k + 4 = 3 + (k + 1)
        rw [Nat.add_comm 3 (k + 1)])
      (serstable.memberRho [2, 1] (k + 7)) (dC (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapW21_0 (k + 7) h0l]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 2 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapW21_1 (k + 7) h1l]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | 2, _ =>
        rw [kapW21 (k + 7) 2 (by decide +kernel) h2l]
        exact termVanishMagD (k + 7) 2 h2l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 2 2 h2l h2l 2 0
            (cartDiagD (k + 7) 2))
          (Or.inl (by decide +kernel))
      | m + 3, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 2 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapW21 (k + 7) (m + 1) (Nat.le_trans (by decide +kernel) hm) hm1]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 0 h0l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel)), if_neg (fun hc => absurd
                (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 7)
          (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) 0 h0l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapW21 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapW21 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapW21 (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The vector sector's witness edge at the three-box word plus `e₂ − e₁ + e₃`. -/
theorem edgeD_v6 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [1, 1, 1] l) (dB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [1, 1, 1] (k + 7)) (dB (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl5 : (5 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (serstable.memberRho [1, 1, 1] (k + 7)) (dB (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapD111_0 (k + 7) h0l]
        exact headAtOneD (k + 7) hl5 _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 0 0 h0l h0l 2 0
              (cartDiagD (k + 7) 0))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 0 1 h0l h1l 0 1
            (cartUpD (k + 7) 0 (litNe 1 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 1, _ =>
        rw [kapD111_1 (k + 7) h1l]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      match m, hm, hml, hm1 with
      | 0, hm, _, _ => exact absurd hm (by decide +kernel)
      | 1, _, _, _ =>
        show row.thetaCount _ (raisedG _ _ (ground.getAt 0 _ 2) 2) = 0
        rw [kapD111_2 (k + 7) h2l]
        exact termVanishMagD (k + 7) 2 h2l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 2 2 h2l h2l 2 0
            (cartDiagD (k + 7) 2))
          (Or.inl (by decide +kernel))
      | r + 2, _, hml, hm1 =>
        rw [kapD111 (k + 7) (r + 2 + 1) (Nat.le_add_left 3 r) hm1]
        refine serstable.runVanishD (k + 7) (r + 2) _ hml
          (nuOf_length (k + 7) _) ?_ 1 h1l
          (Or.inl (Nat.succ_lt_succ (Nat.succ_pos r))) ?_
        · exact nuVac (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0)
            (r + 2 + 1) hm1
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))])
        · exact nuOcc (k + 7)
            (fun i => if i = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapD111 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapD111 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapD111 (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The vector sector's witness edge at the three-box word plus `e₁ − e₃ + e₄`. -/
theorem edgeD_v7 (l : Nat) (hl : 6 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [1, 1, 1] l) (dF l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | k + 1 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (serstable.memberRho [1, 1, 1] (k + 7)) (dF (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h3l : (3 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 4 k 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 4 + k + 3
        rw [Nat.add_comm 4 k])
      (by
        show k + 4 = 4 + k
        rw [Nat.add_comm 4 k])
      (serstable.memberRho [1, 1, 1] (k + 7)) (dF (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapD111_0 (k + 7) h0l]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 3 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapD111_1 (k + 7) h1l]
        exact termTwoBelowD (k + 7) 0
          (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)) _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 3 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 1 1 h1l h1l 2 0
              (cartDiagD (k + 7) 1))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 3 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 1 0 h1l h0l 0 1
            (cartDnD (k + 7) 0 (litNe 2 k 7 (by decide +kernel))
              (litNe 1 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 2, _ =>
        rw [kapD111_2 (k + 7) h2l]
        exact termVanishMagD (k + 7) 2 h2l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 3 then 1 else 0) (fun i => if i = 2 then 1 else 0) 2 2 2 h2l h2l 2 0
            (cartDiagD (k + 7) 2))
          (Or.inl (by decide +kernel))
      | 3, _ =>
        rw [kapD111 (k + 7) 3 (by decide +kernel) h3l]
        exact termVanishMagD (k + 7) 3 h3l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 3 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 3 3 h3l h3l 2 0
            (cartDiagD (k + 7) 3))
          (Or.inl (by decide +kernel))
      | m + 4, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 4 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 3 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapD111 (k + 7) (m + 1) (Nat.le_trans (by decide +kernel) hm) hm1]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 0 h0l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 0 then 1 else if i = 3 then 1 else 0)
          (fun i => if i = 2 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel)), if_neg (fun hc => absurd
                (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 7)
          (fun i => if i = 0 then 1 else if i = 3 then 1 else 0)
          (fun i => if i = 2 then 1 else 0) 0 h0l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapD111 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4]
        exact tailForkD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 3 then 1 else 0)
            (fun i => if i = 2 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapD111 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailSubD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 3 then 1 else 0)
            (fun i => if i = 2 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapD111 (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailTopD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 3 then 1 else 0)
            (fun i => if i = 2 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The vector sector's witness edge at the three-box word plus `e₅ − e₃`. -/
theorem edgeD_v8 (l : Nat) (hl : 7 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (serstable.memberRho [1, 1, 1] l) (dG l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | k + 1 =>
    show serstable.letterFoldVal (sertables.tableD (k + 8))
      (serstable.memberRho [1, 1, 1] (k + 8)) (dG (k + 8)) = 0
    have h0l : (0 : Nat) < k + 8 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 k)
    have h2l : (2 : Nat) < k + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 k)
    have h3l : (3 : Nat) < k + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 k)
    have h4l : (4 : Nat) < k + 8 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 k)
    have hl5 : (5 : Nat) ≤ k + 8 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 8 k)
    have hT7 : k + 7 < k + 8 := Nat.lt_succ_self _
    have hT6 : k + 6 < k + 8 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 6)) hT7
    have hT5 : k + 5 < k + 8 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    refine foldZeroG (sertables.tableD (k + 8)) 5 k 3 (k + 5)
      (by decide +kernel)
      (by
        show k + 8 = 5 + k + 3
        rw [Nat.add_comm 5 k])
      (by
        show k + 5 = 5 + k
        rw [Nat.add_comm 5 k])
      (serstable.memberRho [1, 1, 1] (k + 8)) (dG (k + 8)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapD111_0 (k + 8) h0l]
        exact headAtVacD (k + 8) 2 hl5 (by decide +kernel)
          (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 k)) _
          (BPair.oneValue_trans
            (raisedCountD (k + 8) (fun i => if i = 4 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 0 0 h0l h0l 2 0
              (cartDiagD (k + 8) 0))
            (BPair.ofCounts_crossed (by decide +kernel)))
          (fun hc => absurd (BPair.ofCounts_unit.mp
            (BPair.oneValue_trans (BPair.oneValue_symm
              (raisedCountD (k + 8) (fun i => if i = 4 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 0 2 h0l h2l 0 0
                (cartOffD (k + 8) 0 2 (by decide +kernel)
                  (fun hcc => absurd hcc (litNe 1 k 8 (by decide +kernel)))
                  (fun _ hcc => absurd hcc (litNe 3 k 8 (by decide +kernel)))
                  (fun _ _ => (by decide +kernel))
                  (fun _ _ => (by decide +kernel))))) hc)) (by decide +kernel))
      | 1, _ =>
        rw [kapD111_1 (k + 8) h1l]
        exact termTwoOffD (k + 8) 0
          (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 k)) _
          (BPair.oneValue_trans
            (raisedCountD (k + 8) (fun i => if i = 4 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 1 1 h1l h1l 2 0
              (cartDiagD (k + 8) 1))
            (BPair.ofCounts_crossed (by decide +kernel)))
          4 h4l (by decide +kernel) (by decide +kernel) (by decide +kernel)
          (fun hc => absurd (BPair.ofCounts_unit.mp
            (BPair.oneValue_trans (BPair.oneValue_symm
              (raisedCountD (k + 8) (fun i => if i = 4 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 1 4 h1l h4l 0 0
                (cartOffD (k + 8) 1 4 (by decide +kernel)
                  (fun hcc => absurd hcc (litNe 2 k 8 (by decide +kernel)))
                  (fun _ hcc => absurd hcc (litNe 5 k 8 (by decide +kernel)))
                  (fun _ _ => (by decide +kernel))
                  (fun _ _ => (by decide +kernel))))) hc)) (by decide +kernel))
      | 2, _ =>
        rw [kapD111_2 (k + 8) h2l]
        exact termVanishMagD (k + 8) 2 h2l _ _ _
          (raisedCountD (k + 8) (fun i => if i = 4 then 1 else 0) (fun i => if i = 2 then 1 else 0) 2 2 2 h2l h2l 2 0
            (cartDiagD (k + 8) 2))
          (Or.inl (by decide +kernel))
      | 3, _ =>
        rw [kapD111 (k + 8) 3 (by decide +kernel) h3l]
        exact termTwoBelowD (k + 8) 2
          (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 8 k)) _
          (BPair.oneValue_trans
            (raisedCountD (k + 8) (fun i => if i = 4 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 3 3 h3l h3l 2 0
              (cartDiagD (k + 8) 3))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 8) (fun i => if i = 4 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 3 2 h3l h2l 0 1
            (cartDnD (k + 8) 2 (litNe 4 k 8 (by decide +kernel))
              (litNe 3 k 8 (by decide +kernel))))
          (by decide +kernel)
      | 4, _ =>
        rw [kapD111 (k + 8) 4 (by decide +kernel) h4l]
        exact termVanishMagD (k + 8) 4 h4l _ _ _
          (raisedCountD (k + 8) (fun i => if i = 4 then 1 else 0) (fun i => if i = 2 then 1 else 0) 1 4 4 h4l h4l 2 0
            (cartDiagD (k + 8) 4))
          (Or.inl (by decide +kernel))
      | m + 5, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 5 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 8) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 8) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 8) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 8) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 4 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapD111 (k + 8) (m + 1) (Nat.le_trans (by decide +kernel) hm) hm1]
      refine serstable.runVanishD (k + 8) m _ hml (nuOf_length (k + 8) _) ?_ 2 h2l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 8)
          (fun i => if i = 4 then 1 else 0)
          (fun i => if i = 2 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel)), if_neg (fun hc => absurd
                (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 8)
          (fun i => if i = 4 then 1 else 0)
          (fun i => if i = 2 then 1 else 0) 2 h2l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapD111 (k + 8) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5]
        exact tailForkD (k + 1) 2 (Nat.le_add_left 5 k)
            (fun i => if i = 4 then 1 else 0)
            (fun i => if i = 2 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapD111 (k + 8) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6]
        exact tailSubD (k + 1) 2 (Nat.le_add_left 5 k)
            (fun i => if i = 4 then 1 else 0)
            (fun i => if i = 2 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 7)) (k + 7)) = 0
        rw [kapD111 (k + 8) (k + 7) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)) hT7]
        exact tailTopD (k + 1) 2 (Nat.le_add_left 5 k)
            (fun i => if i = 4 then 1 else 0)
            (fun i => if i = 2 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))



/-- The spinor sector's witness edge at the base plus the flipped
word `e₁`, the moved content occupied at the leading key and at the
two tips. -/
theorem edgeD_s1 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l) (basedRho [] l 0) (dH l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | k + 4 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (basedRho [] (k + 7) 0) (dH (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 1 (k + 3) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 1 + (k + 3) + 3
        rw [Nat.add_comm 1 (k + 3)])
      (by
        show k + 4 = 1 + (k + 3)
        rw [Nat.add_comm 1 (k + 3)])
      (basedRho [] (k + 7) 0) (dH (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapSp (k + 7) 0 h0l (litNe 1 k 7 (by decide +kernel))]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7)
            (fun i => if i = 0 then 1 else if i + 2 = k + 7 then 1 else 0)
            (fun i => if i + 1 = k + 7 then 1 else 0) 1 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by rw [if_neg (litNe 1 k 7 (by decide +kernel)), if_pos rfl]
                      exact (by decide +kernel)))
      | m + 1, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 1 m) hc)
    · intro m hm hml'
      have hml : m + 4 < k + 7 :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < k + 7 := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      rw [kapSp (k + 7) (m + 1) hm1 (Nat.ne_of_lt hm2l)]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_
        (k + 5) hT5 (Or.inr (Nat.succ_lt_succ hml')) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 0 then 1 else if i + 2 = k + 7 then 1 else 0)
          (fun i => if i + 1 = k + 7 then 1 else 0) (m + 1) hm1
          (by rw [if_neg (fun hc => Nat.noConfusion hc),
            if_neg (Nat.ne_of_lt hm3l), if_neg (Nat.ne_of_lt hm2l)])
      · exact nuOcc (k + 7)
          (fun i => if i = 0 then 1 else if i + 2 = k + 7 then 1 else 0)
          (fun i => if i + 1 = k + 7 then 1 else 0) (k + 5) hT5
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_pos rfl,
                if_neg (Nat.ne_of_lt hT6)]
              exact (by decide +kernel))
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapSp (k + 7) (k + 4) hT4 (Nat.ne_of_lt hT5)]
        exact tailForkS1D k
          (fun i => if i = 0 then 1 else if i + 2 = k + 7 then 1 else 0)
          (fun i => if i + 1 = k + 7 then 1 else 0) (if_pos rfl)
          (if_neg (litNe 1 k 7 (by decide +kernel)))
          (by rw [if_neg (fun hc => Nat.noConfusion hc),
            if_neg (fun hc => Nat.ne_of_lt (Nat.lt_succ_self (k + 7)) hc.symm)])
          (if_pos rfl)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapSp (k + 7) (k + 5) hT5 (Nat.ne_of_lt hT6)]
        exact termVanishMagD (k + 7) (k + 5) hT5 _ _ _
          (raisedCountD (k + 7)
            (fun i => if i = 0 then 1 else if i + 2 = k + 7 then 1 else 0)
            (fun i => if i + 1 = k + 7 then 1 else 0) 1 (k + 5) (k + 5)
            hT5 hT5 2 0 (cartDiagD (k + 7) (k + 5)))
          (Or.inl (by rw [if_neg (Nat.ne_of_lt hT6),
                        if_neg (fun hc => Nat.noConfusion hc), if_pos rfl]
                      exact (by decide +kernel)))
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapSpT (k + 7) (k + 6) hT6 rfl]
        exact termVanishMagD (k + 7) (k + 6) hT6 _ _ _
          (raisedCountD (k + 7)
            (fun i => if i = 0 then 1 else if i + 2 = k + 7 then 1 else 0)
            (fun i => if i + 1 = k + 7 then 1 else 0) 2 (k + 6) (k + 6)
            hT6 hT6 2 0 (cartDiagD (k + 7) (k + 6)))
          (Or.inl (by rw [if_pos rfl, if_neg (fun hc => Nat.noConfusion hc),
                        if_neg (fun hc =>
                          Nat.ne_of_lt (Nat.lt_succ_self (k + 7)) hc.symm)]
                      exact (by decide +kernel)))
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))

/-- The spinor sector's witness edge at the base plus `e₂ − e₁ + e₃`. -/
theorem edgeD_s2 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (basedRho [] l 0) (dB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | k + 3 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (basedRho [] (k + 7) 0) (dB (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl5 : (5 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (basedRho [] (k + 7) 0) (dB (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapSp (k + 7) 0 h0l (litNe 1 k 7 (by decide +kernel))]
        exact headAtOneD (k + 7) hl5 _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 0 0 h0l h0l 2 0
              (cartDiagD (k + 7) 0))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 0 1 h0l h1l 0 1
            (cartUpD (k + 7) 0 (litNe 1 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 1, _ =>
        rw [kapSp (k + 7) 1 h1l (litNe 2 k 7 (by decide +kernel))]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      rw [kapSp (k + 7) (m + 1) hm1 (Nat.ne_of_lt hm2l)]
      match m, hm, hml, hm1 with
      | 0, hm, _, _ => exact absurd hm (by decide +kernel)
      | 1, _, hml, _ =>
        exact termTwoBelowD (k + 7) 1 hml _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 2 h2l h2l 2 0 (cartDiagD (k + 7) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 1 h2l h1l 0 1
            (cartDnD (k + 7) 1 (litNe 3 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | r + 2, _, hml, hm1 =>
        refine serstable.runVanishD (k + 7) (r + 2) _ hml
            (nuOf_length (k + 7) _) ?_ 1 h1l
          (Or.inl (Nat.succ_lt_succ (Nat.succ_pos r))) ?_
        · exact nuVac (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0)
            (r + 2 + 1) hm1
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))])
        · exact nuOcc (k + 7)
            (fun i => if i = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapSp (k + 7) (k + 4) hT4 (Nat.ne_of_lt hT5)]
        exact tailForkD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapSp (k + 7) (k + 5) hT5 (Nat.ne_of_lt hT6)]
        exact tailSubD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapSpT (k + 7) (k + 6) hT6 rfl]
        exact termVanishMagD (k + 7) (k + 6) hT6 _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 (k + 6) (k + 6) hT6 hT6 2 0
            (cartDiagD (k + 7) (k + 6)))
          (Or.inl (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]
                      exact (by decide +kernel)))
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The flipped spinor base's witness edge at the once-raised word plus `e₂ − e₁ + e₃`. -/
theorem edgeD_s3 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (basedRho [1] l 1) (dB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | k + 3 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (basedRho [1] (k + 7) 1) (dB (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl3 : (3 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (basedRho [1] (k + 7) 1) (dB (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapS1H (k + 7) hl3]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapS1 (k + 7) 1 (by decide +kernel) h1l (litNe 3 k 7 (by decide +kernel))]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      rw [kapS1 (k + 7) (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hm1 (Nat.ne_of_lt hm3l)]
      match m, hm, hml, hm1 with
      | 0, hm, _, _ => exact absurd hm (by decide +kernel)
      | 1, _, hml, _ =>
        exact termTwoBelowD (k + 7) 1 hml _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 2 h2l h2l 2 0 (cartDiagD (k + 7) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 1 h2l h1l 0 1
            (cartDnD (k + 7) 1 (litNe 3 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | r + 2, _, hml, hm1 =>
        refine serstable.runVanishD (k + 7) (r + 2) _ hml
            (nuOf_length (k + 7) _) ?_ 1 h1l
          (Or.inl (Nat.succ_lt_succ (Nat.succ_pos r))) ?_
        · exact nuVac (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0)
            (r + 2 + 1) hm1
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))])
        · exact nuOcc (k + 7)
            (fun i => if i = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapS1 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4 (Nat.ne_of_lt hT6)]
        exact tailForkD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapS1T (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5 rfl]
        exact termVanishMagD (k + 7) (k + 5) hT5 _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 (k + 5) (k + 5) hT5 hT5 2 0
            (cartDiagD (k + 7) (k + 5)))
          (Or.inl (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]
                      exact (by decide +kernel)))
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapS1 (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6
          (fun hc => Nat.ne_of_lt (Nat.lt_succ_self (k + 7)) hc.symm)]
        exact tailTopD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The flipped spinor base's witness edge at the once-raised word plus `e₃ − e₁`. -/
theorem edgeD_s4 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (basedRho [1] l 1) (dE l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (basedRho [1] (k + 7) 1) (dE (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl3 : (3 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 3 (k + 1) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 3 + (k + 1) + 3
        rw [Nat.add_comm 3 (k + 1)])
      (by
        show k + 4 = 3 + (k + 1)
        rw [Nat.add_comm 3 (k + 1)])
      (basedRho [1] (k + 7) 1) (dE (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapS1H (k + 7) hl3]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0) 2 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapS1 (k + 7) 1 (by decide +kernel) h1l (litNe 3 k 7 (by decide +kernel))]
        exact termTwoBelowD (k + 7) 0
          (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)) _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0) 1 1 1 h1l h1l 2 0
              (cartDiagD (k + 7) 1))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0) 1 1 0 h1l h0l 0 1
            (cartDnD (k + 7) 0 (litNe 2 k 7 (by decide +kernel))
              (litNe 1 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 2, _ =>
        rw [kapS1 (k + 7) 2 (by decide +kernel) h2l (litNe 4 k 7 (by decide +kernel))]
        exact termVanishMagD (k + 7) 2 h2l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0) 1 2 2 h2l h2l 2 0
            (cartDiagD (k + 7) 2))
          (Or.inl (by decide +kernel))
      | m + 3, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 2 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapS1 (k + 7) (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hm1 (Nat.ne_of_lt hm3l)]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 0 h0l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 2 then 1 else 0)
          (fun i => if i = 0 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel)), if_neg (fun hc => Nat.noConfusion hc)])
      · exact nuOcc (k + 7)
          (fun i => if i = 2 then 1 else 0)
          (fun i => if i = 0 then 1 else 0) 0 h0l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapS1 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4 (Nat.ne_of_lt hT6)]
        exact tailForkD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 2 then 1 else 0)
            (fun i => if i = 0 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc))
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc)) (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapS1T (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5 rfl]
        exact termVanishMagD (k + 7) (k + 5) hT5 _ _ _
          (raisedCountD (k + 7) (fun i => if i = 2 then 1 else 0) (fun i => if i = 0 then 1 else 0) 2 (k + 5) (k + 5) hT5 hT5 2 0
            (cartDiagD (k + 7) (k + 5)))
          (Or.inl (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))]
                      exact (by decide +kernel)))
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapS1 (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6
          (fun hc => Nat.ne_of_lt (Nat.lt_succ_self (k + 7)) hc.symm)]
        exact tailTopD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 2 then 1 else 0)
            (fun i => if i = 0 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc))))
              (if_neg (fun hc => Nat.noConfusion hc)) (by decide +kernel)
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The spinor sector's witness edge at the twice-raised base plus `e₁ − e₂`. -/
theorem edgeD_s5 (l : Nat) (hl : 3 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (basedRho [1, 1] l 0) (dA l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | 3 => decide +kernel
  | k + 4 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (basedRho [1, 1] (k + 7) 0) (dA (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl2 : (2 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hl3 : (3 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (basedRho [1, 1] (k + 7) 0) (dA (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapE12H (k + 7) hl2]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 2 else 0) (fun i => if i = 1 then 1 else 0) 1 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapE12A (k + 7) hl3]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 2 else 0) (fun i => if i = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 1 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapE12 (k + 7) (m + 1) hm hm1 (Nat.ne_of_lt hm2l)]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 0 h0l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 0 then 2 else 0)
          (fun i => if i = 1 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 7)
          (fun i => if i = 0 then 2 else 0)
          (fun i => if i = 1 then 1 else 0) 0 h0l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapE12 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4 (Nat.ne_of_lt hT5)]
        exact tailForkD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 2 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapE12 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5 (Nat.ne_of_lt hT6)]
        exact tailSubD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 2 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion hc))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapE12T (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6 rfl]
        exact termVanishMagD (k + 7) (k + 6) hT6 _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 2 else 0) (fun i => if i = 1 then 1 else 0) 2 (k + 6) (k + 6) hT6 hT6 2 0
            (cartDiagD (k + 7) (k + 6)))
          (Or.inl (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)), if_neg (fun hc => Nat.noConfusion hc)]
                      exact (by decide +kernel)))
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The spinor sector's witness edge at the twice-raised base plus `e₂ − e₁ + e₃`. -/
theorem edgeD_s6 (l : Nat) (hl : 4 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (basedRho [1, 1] l 0) (dB l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | 2 => decide +kernel
  | k + 3 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (basedRho [1, 1] (k + 7) 0) (dB (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl2 : (2 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hl3 : (3 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hl5 : (5 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 2 (k + 2) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 2 + (k + 2) + 3
        rw [Nat.add_comm 2 (k + 2)])
      (by
        show k + 4 = 2 + (k + 2)
        rw [Nat.add_comm 2 (k + 2)])
      (basedRho [1, 1] (k + 7) 0) (dB (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapE12H (k + 7) hl2]
        exact headAtOneD (k + 7) hl5 _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 0 0 h0l h0l 2 0
              (cartDiagD (k + 7) 0))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 0 1 h0l h1l 0 1
            (cartUpD (k + 7) 0 (litNe 1 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 1, _ =>
        rw [kapE12A (k + 7) hl3]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | m + 2, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 2 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      rw [kapE12 (k + 7) (m + 1) hm hm1 (Nat.ne_of_lt hm2l)]
      match m, hm, hml, hm1 with
      | 0, hm, _, _ => exact absurd hm (by decide +kernel)
      | 1, _, hml, _ =>
        exact termTwoBelowD (k + 7) 1 hml _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 2 h2l h2l 2 0 (cartDiagD (k + 7) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 1 2 1 h2l h1l 0 1
            (cartDnD (k + 7) 1 (litNe 3 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | r + 2, _, hml, hm1 =>
        refine serstable.runVanishD (k + 7) (r + 2) _ hml
            (nuOf_length (k + 7) _) ?_ 1 h1l
          (Or.inl (Nat.succ_lt_succ (Nat.succ_pos r))) ?_
        · exact nuVac (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0)
            (r + 2 + 1) hm1
            (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))])
        · exact nuOcc (k + 7)
            (fun i => if i = 1 then 1 else 0)
            (fun _ => 0) 1 h1l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapE12 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4 (Nat.ne_of_lt hT5)]
        exact tailForkD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapE12 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5 (Nat.ne_of_lt hT6)]
        exact tailSubD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 1 then 1 else 0) (fun _ => 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))) rfl
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapE12T (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6 rfl]
        exact termVanishMagD (k + 7) (k + 6) hT6 _ _ _
          (raisedCountD (k + 7) (fun i => if i = 1 then 1 else 0) (fun _ => 0) 2 (k + 6) (k + 6) hT6 hT6 2 0
            (cartDiagD (k + 7) (k + 6)))
          (Or.inl (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc))]
                      exact (by decide +kernel)))
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The spinor sector's witness edge at the twice-raised base plus `e₁ − e₂ + e₃`. -/
theorem edgeD_s7 (l : Nat) (hl : 5 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (basedRho [1, 1] l 0) (dC l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | 1 => decide +kernel
  | k + 2 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (basedRho [1, 1] (k + 7) 0) (dC (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl2 : (2 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hl3 : (3 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 3 (k + 1) 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 3 + (k + 1) + 3
        rw [Nat.add_comm 3 (k + 1)])
      (by
        show k + 4 = 3 + (k + 1)
        rw [Nat.add_comm 3 (k + 1)])
      (basedRho [1, 1] (k + 7) 0) (dC (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapE12H (k + 7) hl2]
        exact termVanishMagD (k + 7) 0 h0l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 0 0 h0l h0l 2 0
            (cartDiagD (k + 7) 0))
          (Or.inl (by decide +kernel))
      | 1, _ =>
        rw [kapE12A (k + 7) hl3]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | 2, _ =>
        rw [kapE12 (k + 7) 2 (by decide +kernel) h2l (litNe 3 k 7 (by decide +kernel))]
        exact termVanishMagD (k + 7) 2 h2l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 2 2 h2l h2l 2 0
            (cartDiagD (k + 7) 2))
          (Or.inl (by decide +kernel))
      | m + 3, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 3 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 2 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapE12 (k + 7) (m + 1) (Nat.le_trans (by decide +kernel) hm) hm1 (Nat.ne_of_lt hm2l)]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 0 h0l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel)), if_neg (fun hc => absurd
                (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 7)
          (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) 0 h0l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapE12 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4 (Nat.ne_of_lt hT5)]
        exact tailForkD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapE12 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5 (Nat.ne_of_lt hT6)]
        exact tailSubD k 0
            (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k))
            (fun i => if i = 0 then 1 else if i = 2 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by rw [if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))])
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapE12T (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6 rfl]
        exact termVanishMagD (k + 7) (k + 6) hT6 _ _ _
          (raisedCountD (k + 7) (fun i => if i = 0 then 1 else if i = 2 then 1 else 0) (fun i => if i = 1 then 1 else 0) 2 (k + 6) (k + 6) hT6 hT6 2 0
            (cartDiagD (k + 7) (k + 6)))
          (Or.inl (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)), if_neg (fun hc => Nat.noConfusion hc), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hc)))]
                      exact (by decide +kernel)))
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))


/-- The spinor sector's witness edge at the twice-raised base plus `e₄ − e₂`. -/
theorem edgeD_s8 (l : Nat) (hl : 6 ≤ l) :
    serstable.letterFoldVal (sertables.tableD l)
      (basedRho [1, 1] l 0) (dD l) = 0 := by
  obtain ⟨n, rfl⟩ := shiftOf hl
  match n with
  | 0 => decide +kernel
  | k + 1 =>
    show serstable.letterFoldVal (sertables.tableD (k + 7))
      (basedRho [1, 1] (k + 7) 0) (dD (k + 7)) = 0
    have h0l : (0 : Nat) < k + 7 := Nat.succ_pos _
    have h1l : (1 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h2l : (2 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have h3l : (3 : Nat) < k + 7 :=
      Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)
    have hl2 : (2 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hl3 : (3 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hl5 : (5 : Nat) ≤ k + 7 :=
      Nat.le_trans (by decide +kernel) (Nat.le_add_left 7 k)
    have hT6 : k + 6 < k + 7 := Nat.lt_succ_self _
    have hT5 : k + 5 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 5)) hT6
    have hT4 : k + 4 < k + 7 :=
      Nat.lt_trans (Nat.lt_succ_self (k + 4)) hT5
    refine foldZeroG (sertables.tableD (k + 7)) 4 k 3 (k + 4)
      (by decide +kernel)
      (by
        show k + 7 = 4 + k + 3
        rw [Nat.add_comm 4 k])
      (by
        show k + 4 = 4 + k
        rw [Nat.add_comm 4 k])
      (basedRho [1, 1] (k + 7) 0) (dD (k + 7)) ?_ ?_ ?_
    · intro i hi
      match i, hi with
      | 0, _ =>
        rw [kapE12H (k + 7) hl2]
        exact headAtOneD (k + 7) hl5 _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 0 0 h0l h0l 2 0
              (cartDiagD (k + 7) 0))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 0 1 h0l h1l 0 1
            (cartUpD (k + 7) 0 (litNe 1 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 1, _ =>
        rw [kapE12A (k + 7) hl3]
        exact termVanishMagD (k + 7) 1 h1l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 2 1 1 h1l h1l 2 0
            (cartDiagD (k + 7) 1))
          (Or.inl (by decide +kernel))
      | 2, _ =>
        rw [kapE12 (k + 7) 2 (by decide +kernel) h2l (litNe 3 k 7 (by decide +kernel))]
        exact termTwoBelowD (k + 7) 1
          (Nat.lt_of_lt_of_le (by decide +kernel) (Nat.le_add_left 7 k)) _
          (BPair.oneValue_trans
            (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 2 2 h2l h2l 2 0
              (cartDiagD (k + 7) 2))
            (BPair.ofCounts_crossed (by decide +kernel)))
          _ _
          (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 2 1 h2l h1l 0 1
            (cartDnD (k + 7) 1 (litNe 3 k 7 (by decide +kernel))
              (litNe 2 k 7 (by decide +kernel))))
          (by decide +kernel)
      | 3, _ =>
        rw [kapE12 (k + 7) 3 (by decide +kernel) h3l (litNe 4 k 7 (by decide +kernel))]
        exact termVanishMagD (k + 7) 3 h3l _ _ _
          (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 1 3 3 h3l h3l 2 0
            (cartDiagD (k + 7) 3))
          (Or.inl (by decide +kernel))
      | m + 4, hm =>
        exact absurd hm (fun hc => ltRefute (Nat.le_add_left 4 m) hc)
    · intro m hm hml'
      have hml : m + 4 < (k + 7) :=
        Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ hml'))
      have hm3l : m + 3 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 3)) hml
      have hm2l : m + 2 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 2)) hm3l
      have hm1 : m + 1 < (k + 7) := Nat.lt_trans (Nat.lt_succ_self (m + 1)) hm2l
      have hmlo : 3 ≤ m := Nat.le_of_succ_le_succ hm
      rw [kapE12 (k + 7) (m + 1) (Nat.le_trans (by decide +kernel) hm) hm1 (Nat.ne_of_lt hm2l)]
      refine serstable.runVanishD (k + 7) m _ hml (nuOf_length (k + 7) _) ?_ 1 h1l
        (Or.inl (Nat.lt_of_lt_of_le (by decide +kernel) hmlo)) ?_
      · exact nuVac (k + 7)
          (fun i => if i = 3 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) (m + 1) hm1
              (by rw [if_neg (fun hc => absurd (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel)), if_neg (fun hc => absurd
                (by rw [Nat.succ.inj hc] at hmlo; exact hmlo)
            (by decide +kernel))])
      · exact nuOcc (k + 7)
          (fun i => if i = 3 then 1 else 0)
          (fun i => if i = 1 then 1 else 0) 1 h1l (by decide +kernel)
    · intro x hx
      match x, hx with
      | 0, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 4)) (k + 4)) = 0
        rw [kapE12 (k + 7) (k + 4) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 4 k)) hT4 (Nat.ne_of_lt hT5)]
        exact tailForkD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 3 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 1, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 5)) (k + 5)) = 0
        rw [kapE12 (k + 7) (k + 5) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 5 k)) hT5 (Nat.ne_of_lt hT6)]
        exact tailSubD k 1 (Nat.le_add_left 4 k)
            (fun i => if i = 3 then 1 else 0)
            (fun i => if i = 1 then 1 else 0)
          (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc)))))
              (if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)))
              (by decide +kernel)
      | 2, _ =>
        show row.thetaCount _
          (raisedG _ _ (ground.getAt 0 _ (k + 6)) (k + 6)) = 0
        rw [kapE12T (k + 7) (k + 6) (Nat.le_trans (by decide +kernel) (Nat.le_add_left 6 k)) hT6 rfl]
        exact termVanishMagD (k + 7) (k + 6) hT6 _ _ _
          (raisedCountD (k + 7) (fun i => if i = 3 then 1 else 0) (fun i => if i = 1 then 1 else 0) 2 (k + 6) (k + 6) hT6 hT6 2 0
            (cartDiagD (k + 7) (k + 6)))
          (Or.inl (by rw [if_neg (fun hc => Nat.noConfusion (Nat.succ.inj hc)), if_neg (fun hc => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))]
                      exact (by decide +kernel)))
      | r + 3, hx =>
        exact absurd hx (fun hc => Nat.not_succ_le_zero r
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
            (Nat.le_of_succ_le_succ hc))))



end serdivisors
