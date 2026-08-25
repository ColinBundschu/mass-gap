import MassGap.Stagesplit
/-!
The check module for `lem:stagesplit`: the batteries re-read the
factorization tier by kernel `decide`.  The gcd chain at
`P = (z-1)²(z+2) = z³ - 3z + 2` — the stated factor with cofactor,
the descent's Bézout witness `3P - z P' = -6(z-1)`, the squarefree
part `z² + z - 2` with its own Bézout at `-9`, and the
multiplicities by iterated divisions (`2` at `z-1`, `1` at `z+2`,
the off-root read at the sum's unit).  The multiplicity tier's
theorems at `(z-1)²(z-2)` — the factorization read with its
cofactor, the count's addition over a product, the root at an
occupied count, the repeated root of the derivative, and the
root-carrying cofactor refusing the uniqueness read.  The
proper-factor value arithmetic at the `√2` bracket
`(1448/1024, 1449/1024)` of
`S = (z-1)(z²-2)` — the equal-members read at the divisor's side
exchange, and the unit witness `(z+1)(z-1) - (z²-2) = 1` at the
side-keeping divisor.  The quadratic tier — the definite datum of
`z²+1` at gap `4`, the discriminant of `z²-5z+6` at `1`, the root
relation at `2` and `3` with the off-root refusal, the located
pairs' root `i`, the conjugation with its norm read, and the square
root `√(3+4i) = 2+i` on its three extensions.  The splitting data
at `2(z-1)(z-2)(z²+1)` with the forged-root refusal, and the split
certificate's reads on it: the definite factor `z²+1` above the
sum's unit at `3`, the root `2` among the listed roots with the
off-root refusal at `3`.  The tower at
`K(√2)(√3)` — the two-extension arithmetic's read
`(√2·√3)² = 6` with the level-one instance `√2² = 2`, the
equal-members read by reduction. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground poly stagesplit

private def u : BPair := BPair.unit

/-! The gcd chain at `P = z³ - 3z + 2`, `P' = 3z² - 3`. -/

private def pG : Poly := [⟨3, 1⟩, ⟨1, 4⟩, u, ⟨2, 1⟩]
private def gG : Poly := [⟨1, 2⟩]
private def aG : Poly := [⟨1, 3⟩, ⟨2, 1⟩, ⟨2, 1⟩]
private def bG : Poly := [⟨4, 1⟩, ⟨4, 1⟩]

example : facRead pG gG aG 1 1 := by decide +kernel
example : facRead (poly.deriv pG) gG bG 1 1 := by decide +kernel
example : bezRead pG (poly.deriv pG) gG [⟨4, 1⟩] [u, ⟨1, 2⟩]
    1 ⟨1, 7⟩ := by decide +kernel
example : sqfreeRead pG gG aG bG aG [⟨4, 1⟩] [u, ⟨1, 2⟩]
    [⟨5, 1⟩] [⟨1, 2⟩, ⟨1, 3⟩] 1 1 1 1 ⟨1, 7⟩ ⟨1, 10⟩ := by decide +kernel

/-! The cleared-top class: the divisor whose rescaled monic form
sits off the integer carrier, the stated top carrying the
descent's total rescaling — the read satisfiable exactly where the
unit-top spelling refused.  `W = 2z - 1` against itself, and
`W² = 4z² - 4z + 1` against its derivative `8z - 4`. -/

private def wG : Poly := [⟨1, 2⟩, ⟨3, 1⟩]
private def w2G : Poly := [⟨2, 1⟩, ⟨1, 5⟩, ⟨5, 1⟩]

example : facRead wG [⟨1, 2⟩] [⟨2, 1⟩] 2 1 := by decide +kernel
example : gcdRead wG wG [⟨1, 2⟩] [⟨2, 1⟩] [⟨2, 1⟩] [⟨2, 1⟩] []
    2 1 1 ⟨2, 1⟩ := by decide +kernel
example : sqfreeRead w2G [⟨1, 2⟩] wG [⟨5, 1⟩] wG [] [⟨2, 1⟩]
    [] [⟨2, 1⟩] 2 1 1 1 ⟨5, 1⟩ ⟨3, 1⟩ := by decide +kernel

/-! The multiplicities by iterated divisions: `2` at `z - 1`, `1`
at `z + 2`, and the off-root read. -/

example : multAt [⟨1, 2⟩] pG = 2 := by decide +kernel
example : multAt [⟨3, 1⟩] pG = 1 := by decide +kernel
example : multAt [⟨1, 6⟩] pG = 0 := by decide +kernel

/-! The multiplicity tier's theorems at `P = (z-1)²(z-2)
= z³ - 4z² + 5z - 2`, the located root one entered as its balance
partner `⟨1 : 2⟩`.  The factorization read: the count is `2` and the
cofactor `z - 2` sits off the root, decided and through
`multAt_of`.  The count adds over the product `(z-1)² · (z-2)`,
reading `2 + 0`.  A located root is an occupied count both ways —
`0 < 2` at the root one, the count `1` at the root two, and the
count `0` with the root refused at three.  The derivative
`3z² - 8z + 5 = (z-1)(3z-5)` has the repeated root one through
`multAt_deriv` at the count from two, with the simple root two
refused.  `multAt_of`'s root-free binder is load-bearing: the same
`P` reads the factorization at the count `1` against the cofactor
`(z-1)(z-2) = z² - 3z + 2`, which carries the root, and the count
there is `2`, not `1`.  The occupancy binders of `multAt_mul` and
`multAt_congr` refuse at the unit tail, where the count is the
carrier's whole length: the product of the unit-tailed `[0, 0]`
with `z - 2` counts three against `2 + 0`, and the two unit-tailed
spellings `[0, 0]` and `[0]` read one value at the counts two and
one. -/

private def pM : Poly := [⟨1, 3⟩, ⟨6, 1⟩, ⟨1, 5⟩, ⟨2, 1⟩]
private def sqM : Poly := [⟨2, 1⟩, ⟨1, 3⟩, ⟨2, 1⟩]
private def cofM : Poly := [⟨1, 3⟩, ⟨2, 1⟩]
private def badM : Poly := [⟨3, 1⟩, ⟨1, 4⟩, ⟨2, 1⟩]

example : poly.oneValue pM (poly.mul sqM cofM) := by decide +kernel
example : multAt [⟨1, 2⟩] pM = 2 := by decide +kernel
example : poly.oneValue pM
    (poly.mul (poly.powOf (linFacM ⟨2, 1⟩) 2) cofM) := by decide +kernel
example : ¬ poly.isRoot cofM ⟨2, 1⟩ := by decide +kernel
example : multAt [⟨1, 2⟩] pM = 2 :=
  multAt_of ⟨2, 1⟩ pM cofM 2 (by decide +kernel) (by decide +kernel)

example : multAt [⟨1, 2⟩] (poly.mul sqM cofM)
    = multAt [⟨1, 2⟩] sqM + multAt [⟨1, 2⟩] cofM :=
  multAt_mul ⟨2, 1⟩ sqM cofM (by decide +kernel) (by decide +kernel)
example : multAt [⟨1, 2⟩] (poly.mul sqM cofM) = 2 := by decide +kernel
example : ¬ (multAt [⟨1, 2⟩] (poly.mul [u, u] cofM)
    = multAt [⟨1, 2⟩] [u, u] + multAt [⟨1, 2⟩] cofM) := by decide +kernel
example : poly.oneValue [u, u] [u] := by decide +kernel
example : ¬ multAt [⟨1, 2⟩] [u, u] = multAt [⟨1, 2⟩] [u] := by decide +kernel

example : 0 < multAt [⟨1, 2⟩] pM :=
  (multAt_pos ⟨2, 1⟩ pM (by decide +kernel)).mp (by decide +kernel)
example : poly.isRoot pM ⟨3, 1⟩ :=
  (multAt_pos ⟨3, 1⟩ pM (by decide +kernel)).mpr (by decide +kernel)
example : multAt [⟨1, 3⟩] pM = 1 := by decide +kernel
example : multAt [⟨1, 4⟩] pM = 0 := by decide +kernel
example : ¬ poly.isRoot pM ⟨4, 1⟩ := by decide +kernel

example : poly.oneValue (poly.deriv pM) [⟨6, 1⟩, ⟨1, 9⟩, ⟨4, 1⟩] := by decide +kernel
example : poly.isRoot (poly.deriv pM) ⟨2, 1⟩ :=
  multAt_deriv ⟨2, 1⟩ pM (by decide +kernel) (by decide +kernel)
example : poly.isRoot (poly.deriv pM) ⟨2, 1⟩ := by decide +kernel
example : ¬ poly.isRoot (poly.deriv pM) ⟨3, 1⟩ := by decide +kernel

example : poly.oneValue pM
    (poly.mul (poly.powOf (linFacM ⟨2, 1⟩) 1) badM) := by decide +kernel
example : poly.isRoot badM ⟨2, 1⟩ := by decide +kernel
example : ¬ multAt [⟨1, 2⟩] pM = 1 := by decide +kernel

/-! The proper-factor value arithmetic at the isolated `√2`
bracket `(1448/1024, 1449/1024)` of `S = (z-1)(z²-2)`, the doubled
width `1/512` under the separation's `1/390`: the equal-members
read at `p = (z-1)(z²-2)` with divisor `z²-2` exchanging sides, and
the unit witness at `p = z-1` with the divisor keeping its side. -/

private def e3 : stage.Ext :=
  ⟨[⟨3, 1⟩, ⟨1, 3⟩, ⟨1, 2⟩], ⟨⟨1449, 1⟩, 1024⟩, ⟨⟨1450, 1⟩, 1024⟩⟩

example : valueNullRead e3 [⟨3, 1⟩, ⟨1, 3⟩, ⟨1, 2⟩, ⟨2, 1⟩]
    [⟨1, 3⟩, u] [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 2⟩, ⟨2, 1⟩] 1 1024 := by
  decide +kernel
example : valueUnitRead e3 [⟨1, 2⟩, ⟨2, 1⟩] [⟨1, 2⟩]
    [⟨1, 3⟩, u, ⟨2, 1⟩] [⟨2, 1⟩, ⟨2, 1⟩] [⟨1, 2⟩] ⟨2, 1⟩ 1
    1024 := by decide +kernel

/-! The quadratic tier: the definite datum, the discriminant, the
root relations, the conjugation, and the square root. -/

example : defRead ⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩ := by decide +kernel
example : ¬ defRead ⟨u, ⟨2, 1⟩, ⟨4, 1⟩⟩ := by decide +kernel
example : discRead ⟨6, 1⟩ ⟨7, 1⟩ ⟨2, 1⟩ := by decide +kernel
example : rootRead ⟨6, 1⟩ ⟨7, 1⟩ ⟨3, 1⟩ := by decide +kernel
example : rootRead ⟨6, 1⟩ ⟨7, 1⟩ ⟨4, 1⟩ := by decide +kernel
example : ¬ rootRead ⟨6, 1⟩ ⟨7, 1⟩ ⟨5, 1⟩ := by decide +kernel
example : rootReadI u ⟨2, 1⟩ u ⟨2, 1⟩ := by decide +kernel
example : poly.oneValue (keySwap ⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩ [u, ⟨2, 1⟩])
    [u, ⟨1, 2⟩] := by decide +kernel
example : poly.oneValue
    (poly.remMul iList [u, ⟨2, 1⟩]
      (keySwap ⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩ [u, ⟨2, 1⟩]))
    [⟨2, 1⟩] := by decide +kernel
example : sqrtRead ⟨4, 1⟩ ⟨5, 1⟩ ⟨6, 1⟩ ⟨3, 1⟩ ⟨2, 1⟩ := by decide +kernel

/-! The splitting data at `2(z-1)(z-2)(z²+1)`, with the
forged-root refusal. -/

private def pF : Poly := [⟨5, 1⟩, ⟨1, 7⟩, ⟨7, 1⟩, ⟨1, 7⟩, ⟨3, 1⟩]

example : factorsRead pF 1 ⟨3, 1⟩ [⟨2, 1⟩, ⟨3, 1⟩]
    [⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩] := by decide +kernel
example : ¬ factorsRead pF 1 ⟨3, 1⟩ [⟨2, 1⟩, ⟨4, 1⟩]
    [⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩] := by decide +kernel

/-! The split certificate's reads at the same data.  The definite
factor `z² + 1` sits above the sum's unit at `3`.  The root `2` of
the split polynomial is one of the listed roots `1, 2`, with the
off-root refusal at `3`. -/

private def qD : QDatum := ⟨u, ⟨2, 1⟩, ⟨5, 1⟩⟩

example : BPair.unit < poly.eval (quadFacM qD) ⟨4, 1⟩ := by decide +kernel
example : BPair.unit < poly.eval (quadFacM qD) ⟨4, 1⟩ :=
  quadFacM_pos qD (by decide +kernel) ⟨4, 1⟩

example : ([⟨2, 1⟩, ⟨3, 1⟩] : List BPair).any
    (fun r => decide ((⟨3, 1⟩ : BPair).oneValue r)) = true := by decide +kernel
example : ([⟨2, 1⟩, ⟨3, 1⟩] : List BPair).any
    (fun r => decide ((⟨3, 1⟩ : BPair).oneValue r)) = true :=
  root_of_factors pF 1 ⟨3, 1⟩ [⟨2, 1⟩, ⟨3, 1⟩] [qD] (by decide +kernel)
    ⟨3, 1⟩ (by decide +kernel)
example : ¬ poly.isRoot pF ⟨4, 1⟩ := by decide +kernel

/-! The tower at `K(√2)(√3)`: the level-one read `√2² = 2` and the
two-extension read `(√2·√3)² = 6`, the equal-members test by
reduction. -/

private def tw1 : TowerData 1 := ((), [⟨1, 3⟩, u])
private def tw2 : TowerData 2 := (tw1, [[⟨1, 4⟩], []])
private def rt2 : TE 1 := [u, ⟨2, 1⟩]
private def x23 : TE 2 := [[], [u, ⟨2, 1⟩]]

example : (opsAt 1 tw1).isNull
    ((opsAt 1 tw1).add ((opsAt 1 tw1).mul rt2 rt2)
      ((opsAt 1 tw1).swap [⟨3, 1⟩])) = true := by decide +kernel
example : (opsAt 2 tw2).isNull
    ((opsAt 2 tw2).add ((opsAt 2 tw2).mul x23 x23)
      ((opsAt 2 tw2).swap [[⟨7, 1⟩]])) = true := by decide +kernel
example : (opsAt 2 tw2).isNull x23 = false := by decide +kernel

/-! The tower unit witness at the side-five factor `t² + t − 1`:
`t (t + 1) = 1` at the remainder arithmetic, with the refusals at
the unit constant and at a wrong witness. -/

example : stagesplit.gWitnessRead 1
    ((), [(BPair.ofNat 1).swap, BPair.ofNat 1])
    [BPair.unit, BPair.ofNat 1] [BPair.ofNat 1, BPair.ofNat 1]
    (BPair.ofNat 1) := by decide +kernel

example : ¬ stagesplit.gWitnessRead 1
    ((), [(BPair.ofNat 1).swap, BPair.ofNat 1])
    [BPair.unit, BPair.ofNat 1] [BPair.ofNat 1, BPair.ofNat 1]
    BPair.unit := by decide +kernel

example : ¬ stagesplit.gWitnessRead 1
    ((), [(BPair.ofNat 1).swap, BPair.ofNat 1])
    [BPair.unit, BPair.ofNat 1] [BPair.unit, BPair.ofNat 1]
    (BPair.ofNat 1) := by decide +kernel
