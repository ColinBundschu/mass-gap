import MassGap.Serpairing
/-!
The check module for `lem:serpairing`: the batteries re-read the
pair-partition tier by kernel `decide`.  The count `(2k-1)!!` at
`1, 3, 15, 105` with the count theorem consumed at every pair
count (`length_allParts`).  The
loop fold at the two-pair partitions through the Gram entries, the
enumeration's positional order `[(0,1),(2,3)]`, `[(0,2),(1,3)]`,
`[(0,3),(1,2)]`: the `B` and `D` diagonal at two loops with the
off-diagonal at one, and the `C` diagonal at two loops with the
crossing member positive and the nested member negated.  The
invariance reads at the dual-pair vectors — `B_2`, `C_3` and `D_4`
at one pair each against their simple raisings.  The in-carrier
Gram identities `gramReadB 2 1` and `gramReadB 2 2` at the cleared
pairing's `2^{2k}` scale, `gramReadC 3 1` and `gramReadD 4 1` at
the identity weight.  The `D` tie at the `ℓ = 2` data instance:
the arrangement sign vector is annihilated by both raisings, and
its residual against the three partition vectors sits off the unit
tail — the exhibit off the span.  The `ℓ = 2` instance sits off
the classification's `D` domain (`D_ℓ` at `ℓ ≥ 4`): the tables
enter as data, and the tie's mechanism is the exhibit rather than
the statement's own instance.  Four committed refusals: the
invariance read at the unit vector on the doubled-key monomial
(a top off the unit content, the content conjunct's isolation),
at the unit vector on a unit-content monomial (the annihilation
conjunct's), at the forged dual matrix — the null entry at plus
two in place of the balance partner of two — whose one-pair
vector refuses the invariance, the displayed sign's own pin, and
the `B` Gram identity with the scale forged to `2^1` in place of
`2^2`, the weighted dot's (`dotWB`) mismatched comparison.
Budget: the
doubled-degree invariance reads and the further Gram instances sit
beyond the battery allowance, `gramReadB 2 2` and the sign
vector's invariance the two kept boundary reads.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground serpairing

/-! The pair-partition count `(2k-1)!!` with the count theorem
consumed at every pair count. -/

example : dfac 1 = 1 := by decide +kernel
example : dfac 2 = 3 := by decide +kernel
example : dfac 3 = 15 := by decide +kernel
example : dfac 4 = 105 := by decide +kernel

example (k : Nat) : (allParts k).length = dfac k := length_allParts k

/-! The loop fold at the two-pair partitions through the Gram
entries, the enumeration's positional order
`[(0,1),(2,3)]`, `[(0,2),(1,3)]`, `[(0,3),(1,2)]`. -/

example : getAt [] (getAt [] (gramBD 2) 0) 0 = dimPow 2 := by decide +kernel
example : getAt [] (getAt [] (gramBD 2) 1) 1 = dimPow 2 := by decide +kernel
example : getAt [] (getAt [] (gramBD 2) 2) 2 = dimPow 2 := by decide +kernel
example : getAt [] (getAt [] (gramBD 2) 0) 1 = dimPow 1 := by decide +kernel
example : getAt [] (getAt [] (gramBD 2) 0) 2 = dimPow 1 := by decide +kernel

example : getAt [] (getAt [] (gramC 2) 0) 0 = rankPow 2 := by decide +kernel
example : getAt [] (getAt [] (gramC 2) 0) 1 = rankPow 1 := by decide +kernel
example : getAt [] (getAt [] (gramC 2) 0) 2 = poly.neg (rankPow 1) := by
  decide +kernel

/-! The invariance reads: the dual-pair vectors against the simple
raisings at one pair each. -/

example : invRead 5 [sertables.raiseB 2 0, sertables.raiseB 2 1]
    (partVec 5 1 (dualB 2) [(0, 1)]) := by decide +kernel
example : invRead 6 [sertables.raiseC 3 0, sertables.raiseC 3 1,
    sertables.raiseC 3 2] (partVec 6 1 (dualC 3) [(0, 1)]) := by decide +kernel
example : invRead 8 [sertables.raiseD 4 0, sertables.raiseD 4 1,
    sertables.raiseD 4 2, sertables.raiseD 4 3]
    (partVec 8 1 (dualD 4) [(0, 1)]) := by decide +kernel

/-! The invariance read's committed refusals, one per conjunct: the
unit vector at the doubled-key monomial `[0, 0]` is a top off the
unit content, the raisings annihilating it with the content
conjunct refusing, and the unit vector at the unit-content monomial
`[0, 2]` refuses at the annihilation. -/

example : ¬ invRead 5 [sertables.raiseB 2 0, sertables.raiseB 2 1]
    (units.scatterAt 0 (BPair.ofNat 1)
      ((places.allMon 5 2).map (fun _ => BPair.unit))) := by decide +kernel
example : ¬ invRead 5 [sertables.raiseB 2 0, sertables.raiseB 2 1]
    (units.scatterAt (places.idxOf [0, 2] (places.allMon 5 2))
      (BPair.ofNat 1)
      ((places.allMon 5 2).map (fun _ => BPair.unit))) := by decide +kernel

/-! The forged-null-sign refusal: the `B` dual matrix with the null
entry at plus two in place of the balance partner of two —
`con:sertables`' displayed sign — whose one-pair partition vector
refuses the invariance read. -/

private def dualBForged : elim.Mat :=
  ground.matOf (sertables.vcountB 2) (sertables.vcountB 2) (fun r c =>
      if r < 2 && c == r + 2 then BPair.ofNat 1
      else if c < 2 && r == c + 2 then BPair.ofNat 1
      else if r == 4 && c == 4 then BPair.ofNat 2
      else BPair.unit)

example : ¬ invRead 5 [sertables.raiseB 2 0, sertables.raiseB 2 1]
    (partVec 5 1 dualBForged [(0, 1)]) := by decide +kernel

/-! The in-carrier Gram identities: `B_2` at the cleared pairing's
scale, `C_3` and `D_4` at the identity weight. -/

example : gramReadB 2 1 := by decide +kernel
example : gramReadB 2 2 := by decide +kernel
example : gramReadC 3 1 := by decide +kernel
example : gramReadD 4 1 := by decide +kernel

/-! The `D` tie at the `ℓ = 2` data instance: the arrangement sign
vector is annihilated by both raisings and its residual against
the partition span sits off the unit tail. -/

example : invRead 4 [sertables.raiseD 2 0, sertables.raiseD 2 1]
    (epsVec 2) := by decide +kernel

private def dSpan : elim.Mat :=
  (allParts 2).map (partVec 4 2 (dualD 2))

example : ¬ poly.unitTail (elim.residV 256 dSpan (epsVec 2)) := by decide +kernel

/-! The committed refusal: the `B` Gram identity's scale forged to
`2^1` in place of `2^2`, the weighted dot (`dotWB`) against the
mismatched multiple. -/

example : ¬ ((dotWB (pwListB 2 (places.allMon 5 2))
    (partVec 5 1 (dualB 2) [(0, 1)])
    (partVec 5 1 (dualB 2) [(0, 1)])).oneValue
    (BPair.ofNat 2 * poly.eval (getAt [] (getAt [] (gramBD 1) 0) 0)
      (BPair.ofNat (gentable.residue (sertables.tableB 2))))) := by decide +kernel
