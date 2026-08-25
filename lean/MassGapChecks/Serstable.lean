import MassGap.Serstable
/-!
The check module for `lem:serstable`(i)'s leading families: the
batteries re-read the members and their displays by kernel
`decide` at the committed words, each decided anchor beside the
same conclusion routed through the general theorem — the coroot
identities of the cleared fold (`corootRead` at `B`, `C` and `D`)
and the displayed Casimir values at the cross-multiplied reads
(`c2Read` against `casNum` and `casDen`).  The binder records sit
beside them: the descent binder is load-bearing (the ascending
word's fold refuses the coroot identities), and the clearance
`a + 2 ≤ ℓ` is load-bearing at `D`, where the last-pair join
breaks one rank short, and at `B`, where the doubled last key
breaks at the word's own length; at `B` and `C` the rank one short
of the clearance survives, so the binder is the reach frame the
statement carries and not a refusal boundary.  The member and the
three simple folds are pinned at their values, the gaps of the
padded word against the leading sums, their doubles and the word's
total at the last key or the last two keys.
-/
set_option maxRecDepth 8192

open serstable

/-! The `B` member's reads at the word `[2, 1]` and the rank four. -/

example : casfloor.corootRead (sertables.tableB 4) (endB [2, 1] 4) := by
  decide +kernel
example : casfloor.corootRead (sertables.tableB 4) (endB [2, 1] 4) :=
  corootRead_B [2, 1] 4 (by decide +kernel) (by decide +kernel)

example : casfloor.c2Read (sertables.tableB 4) (endB [2, 1] 4)
    (casNumB [2, 1] 4) (casDenB 4) := by decide +kernel
example : casfloor.c2Read (sertables.tableB 4) (endB [2, 1] 4)
    (casNumB [2, 1] 4) (casDenB 4) :=
  casRead_B [2, 1] 4 (by decide +kernel) (by decide +kernel)

/-! The `C` member's reads at the same word and rank. -/

example : casfloor.corootRead (sertables.tableC 4) (endC [2, 1] 4) := by
  decide +kernel
example : casfloor.corootRead (sertables.tableC 4) (endC [2, 1] 4) :=
  corootRead_C [2, 1] 4 (by decide +kernel) (by decide +kernel)

example : casfloor.c2Read (sertables.tableC 4) (endC [2, 1] 4)
    (casNumC [2, 1] 4) (casDenC 4) := by decide +kernel
example : casfloor.c2Read (sertables.tableC 4) (endC [2, 1] 4)
    (casNumC [2, 1] 4) (casDenC 4) :=
  casRead_C [2, 1] 4 (by decide +kernel) (by decide +kernel)

/-! The `D` member's reads at the same word and the rank five. -/

example : casfloor.corootRead (sertables.tableD 5) (endD [2, 1] 5) := by
  decide +kernel
example : casfloor.corootRead (sertables.tableD 5) (endD [2, 1] 5) :=
  corootRead_D [2, 1] 5 (by decide +kernel) (by decide +kernel)

example : casfloor.c2Read (sertables.tableD 5) (endD [2, 1] 5)
    (casNumD [2, 1] 5) (casDenD 5) := by decide +kernel
example : casfloor.c2Read (sertables.tableD 5) (endD [2, 1] 5)
    (casNumD [2, 1] 5) (casDenD 5) :=
  casRead_D [2, 1] 5 (by decide +kernel) (by decide +kernel)

/-! The theorems at a longer word and at the vacant word, the
clearance met with room and at its own boundary. -/

example : casfloor.corootRead (sertables.tableB 6) (endB [5, 3, 3, 1] 6) :=
  corootRead_B [5, 3, 3, 1] 6 (by decide +kernel) (by decide +kernel)
example : casfloor.c2Read (sertables.tableD 7) (endD [5, 3, 3, 1, 1] 7)
    (casNumD [5, 3, 3, 1, 1] 7) (casDenD 7) :=
  casRead_D [5, 3, 3, 1, 1] 7 (by decide +kernel) (by decide +kernel)
example : casfloor.c2Read (sertables.tableD 2) (endD [] 2)
    (casNumD [] 2) (casDenD 2) :=
  casRead_D [] 2 (by decide +kernel) (by decide +kernel)

/-! The descent binder is load-bearing: the ascending word's fold
refuses the coroot identities. -/

example : ¬ casfloor.corootRead (sertables.tableB 4) (endB [1, 2] 4) := by
  decide +kernel

/-! The clearance `a + 2 ≤ ℓ` is load-bearing at `D`, the last-pair
join breaking one rank short, and at `B`, the doubled last key
breaking at the word's own length. -/

example : ¬ casfloor.corootRead (sertables.tableD 4) (endD [2, 1, 1] 4) := by
  decide +kernel
example : ¬ casfloor.corootRead (sertables.tableB 2) (endB [2, 1] 2) := by
  decide +kernel

/-! At `B` and `C` the rank one short of the clearance survives:
the binder is the statement's reach frame, not a refusal
boundary. -/

example : casfloor.corootRead (sertables.tableB 3) (endB [2, 1] 3) := by
  decide +kernel
example : casfloor.corootRead (sertables.tableC 3) (endC [2, 1] 3) := by
  decide +kernel

/-! The member and the simple folds at their values, with the
Casimir numerators and denominators beside them. -/

example : member [2, 1] 4 = [1, 1, 0, 0] := by decide +kernel
example : foldB [2, 1] 4 = [2, 3, 3, 3] := by decide +kernel
example : foldC [2, 1] 4 = [4, 6, 6, 3] := by decide +kernel
example : foldD [2, 1] 5 = [4, 6, 6, 3, 3] := by decide +kernel
example : casNumB [2, 1] 4 = 24 := by decide +kernel
example : casNumC [2, 1] 4 = 27 := by decide +kernel
example : casNumD [2, 1] 5 = 27 := by decide +kernel
example : casDenB 4 = 14 := by decide +kernel
example : casDenC 4 = 20 := by decide +kernel
example : casDenD 5 = 16 := by decide +kernel

/-! ## The dimension tier: the cross-multiplied gap identity

The member's dimension is `cor:weyldim`'s gap product: the
displayed numerator against the gap product at `ρ` reads the
denominator against the gap product at `member + ρ`.  Each series'
identity is decided at its word and rank and routed through the
general theorem beside it. -/

example : dimNumB [2, 1] 4 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableB 4) (List.replicate 4 1))
    (List.range (sertables.tableB 4).posFolds.length)
  = dimDenB [2, 1] 4 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableB 4) (memberRho [2, 1] 4))
      (List.range (sertables.tableB 4).posFolds.length) := by decide +kernel
example : dimNumB [2, 1] 4 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableB 4) (List.replicate 4 1))
    (List.range (sertables.tableB 4).posFolds.length)
  = dimDenB [2, 1] 4 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableB 4) (memberRho [2, 1] 4))
      (List.range (sertables.tableB 4).posFolds.length) :=
  dimGap_B [2, 1] 4 (by decide +kernel) (by decide +kernel)

example : dimNumC [2, 1] 4 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableC 4) (List.replicate 4 1))
    (List.range (sertables.tableC 4).posFolds.length)
  = dimDenC [2, 1] 4 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableC 4) (memberRho [2, 1] 4))
      (List.range (sertables.tableC 4).posFolds.length) := by decide +kernel
example : dimNumC [2, 1] 4 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableC 4) (List.replicate 4 1))
    (List.range (sertables.tableC 4).posFolds.length)
  = dimDenC [2, 1] 4 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableC 4) (memberRho [2, 1] 4))
      (List.range (sertables.tableC 4).posFolds.length) :=
  dimGap_C [2, 1] 4 (by decide +kernel) (by decide +kernel)

example : dimNumD [2, 1] 5 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableD 5) (List.replicate 5 1))
    (List.range (sertables.tableD 5).posFolds.length)
  = dimDenD [2, 1] 5 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableD 5) (memberRho [2, 1] 5))
      (List.range (sertables.tableD 5).posFolds.length) := by decide +kernel
example : dimNumD [2, 1] 5 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableD 5) (List.replicate 5 1))
    (List.range (sertables.tableD 5).posFolds.length)
  = dimDenD [2, 1] 5 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableD 5) (memberRho [2, 1] 5))
      (List.range (sertables.tableD 5).posFolds.length) :=
  dimGap_D [2, 1] 5 (by decide +kernel) (by decide +kernel)

/-! The `D` identity at a longer word, decided and through the
theorem. -/

example : dimNumD [2, 2, 1] 5 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableD 5) (List.replicate 5 1))
    (List.range (sertables.tableD 5).posFolds.length)
  = dimDenD [2, 2, 1] 5 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableD 5) (memberRho [2, 2, 1] 5))
      (List.range (sertables.tableD 5).posFolds.length) := by decide +kernel
example : dimNumD [2, 2, 1] 5 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableD 5) (List.replicate 5 1))
    (List.range (sertables.tableD 5).posFolds.length)
  = dimDenD [2, 2, 1] 5 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableD 5) (memberRho [2, 2, 1] 5))
      (List.range (sertables.tableD 5).posFolds.length) :=
  dimGap_D [2, 2, 1] 5 (by decide +kernel) (by decide +kernel)

/-! The theorems at the vacant word and at a longer one: the
identity reads one against one at the vacant content, and the
`B` word of length four at the rank six. -/

example : dimNumB [] 4 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableB 4) (List.replicate 4 1))
    (List.range (sertables.tableB 4).posFolds.length)
  = dimDenB [] 4 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableB 4) (memberRho [] 4))
      (List.range (sertables.tableB 4).posFolds.length) :=
  dimGap_B [] 4 (by decide +kernel) (by decide +kernel)
example : dimNumB [5, 3, 3, 1] 6 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableB 6) (List.replicate 6 1))
    (List.range (sertables.tableB 6).posFolds.length)
  = dimDenB [5, 3, 3, 1] 6 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableB 6) (memberRho [5, 3, 3, 1] 6))
      (List.range (sertables.tableB 6).posFolds.length) :=
  dimGap_B [5, 3, 3, 1] 6 (by decide +kernel) (by decide +kernel)

/-! The descent binder is load-bearing at the dimension identity:
the ascending word's numerator and denominator refuse the
cross-multiplied read, the padded word's gaps truncating at the
raised entry. -/

example : ¬ (dimNumB [1, 2] 4 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableB 4) (List.replicate 4 1))
    (List.range (sertables.tableB 4).posFolds.length)
  = dimDenB [1, 2] 4 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableB 4) (memberRho [1, 2] 4))
      (List.range (sertables.tableB 4).posFolds.length)) := by decide +kernel

/-! The clearance `a + 2 ≤ ℓ` is load-bearing at `D`, where the
last-pair join breaks one rank short, and at `B`, where the word's
own length leaves the short key inside the word. -/

example : ¬ (dimNumD [2, 1, 1] 4 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableD 4) (List.replicate 4 1))
    (List.range (sertables.tableD 4).posFolds.length)
  = dimDenD [2, 1, 1] 4 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableD 4) (memberRho [2, 1, 1] 4))
      (List.range (sertables.tableD 4).posFolds.length)) := by decide +kernel
example : ¬ (dimNumB [2, 1] 2 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableB 2) (List.replicate 2 1))
    (List.range (sertables.tableB 2).posFolds.length)
  = dimDenB [2, 1] 2 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableB 2) (memberRho [2, 1] 2))
      (List.range (sertables.tableB 2).posFolds.length)) := by decide +kernel

/-! At the rank one short of the clearance the `B` and `C`
identities survive: the binder is the statement's reach frame at
those series, not a refusal boundary. -/

example : dimNumB [2, 1] 3 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableB 3) (List.replicate 3 1))
    (List.range (sertables.tableB 3).posFolds.length)
  = dimDenB [2, 1] 3 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableB 3) (memberRho [2, 1] 3))
      (List.range (sertables.tableB 3).posFolds.length) := by decide +kernel
example : dimNumC [2, 1] 3 * ground.famFold Nat.mul 1
    (gapAt (sertables.tableC 3) (List.replicate 3 1))
    (List.range (sertables.tableC 3).posFolds.length)
  = dimDenC [2, 1] 3 * ground.famFold Nat.mul 1
      (gapAt (sertables.tableC 3) (memberRho [2, 1] 3))
      (List.range (sertables.tableC 3).posFolds.length) := by decide +kernel

/-! ## The gap as the form's own read

`B₂`'s fundamental data pairs each positive member's coroot vector
against a coroot list at the concrete gap, decided over three
coroot lists and routed through the general theorem per list. -/

example : ∀ j, j < (sertables.tableB 2).posFolds.length →
    ∀ v ∈ [[1, 1], [2, 1], [3, 2]],
    (sertables.dotB sertables.fundB2
        (sertables.posCorootV (sertables.tableB 2) j)
        (v.map ground.BPair.ofNat)).oneValue
      (ground.BPair.ofNat (sertables.fundB2.scale
        * gapAt (sertables.tableB 2) v j)) := by decide +kernel

example : ∀ j, j < (sertables.tableB 2).posFolds.length →
    (sertables.dotB sertables.fundB2
        (sertables.posCorootV (sertables.tableB 2) j)
        ([3, 2].map ground.BPair.ofNat)).oneValue
      (ground.BPair.ofNat (sertables.fundB2.scale
        * gapAt (sertables.tableB 2) [3, 2] j)) :=
  fun j hj => gapAt_dotB (sertables.tableB 2) sertables.fundB2
    (by decide +kernel) (by decide +kernel) j hj [3, 2] (by decide +kernel)
example : ∀ j, j < (sertables.tableG2).posFolds.length →
    (sertables.dotB sertables.fundG2
        (sertables.posCorootV (sertables.tableG2) j)
        ([1, 1].map ground.BPair.ofNat)).oneValue
      (ground.BPair.ofNat (sertables.fundG2.scale
        * gapAt (sertables.tableG2) [1, 1] j)) :=
  fun j hj => gapAt_dotB sertables.tableG2 sertables.fundG2
    (by decide +kernel) (by decide +kernel) j hj [1, 1] (by decide +kernel)

/-! The raised member, the concrete gaps and the dimension data at
their values. -/

example : memberRho [2, 1] 4 = [2, 2, 1, 1] := by decide +kernel
example : (List.range (sertables.tableB 4).posFolds.length).map
    (gapAt (sertables.tableB 4) (memberRho [2, 1] 4))
  = [4, 8, 4, 10, 6, 2, 18, 14, 10, 12, 8, 4, 11, 7, 3, 1] := by decide +kernel
example : dimNumB [2, 1] 4 = 139708800 := by decide +kernel
example : dimDenB [2, 1] 4 = 604800 := by decide +kernel
example : dimNumC [2, 1] 4 = 96768000 := by decide +kernel
example : dimDenC [2, 1] 4 = 604800 := by decide +kernel
example : dimNumD [2, 2, 1] 5 = 258660864000 := by decide +kernel
example : dimDenD [2, 2, 1] 5 = 87091200 := by decide +kernel

/-! ## The row tier: the letter fold at the vacant target

The fixtures are the members' own data.  The `θ` content list is
built from the table itself — the vacant content at the coordinate
count beside the positive members' coroot vectors and their balance
partners, one each — so the committed list is the read's own
subject rather than a transcription; `thetaFamRead` decides it at
every member below.  The fundamental data at `B_3`, `C_3` and `D_4`
are the cleared Grams off the adjugate solve at the displayed
Cartan rows with the simple positions and the reflections'
permutations of the positive list, each pinned by `permImageRead`
beside the reads the row consumes.

`B_2`'s member at the vacant word carries every raise at one, so
the whole fold is the letters' own reads; `B_3`, `C_3` and `D_4` at
the word `[1]` carry the first raise at two, and the doubled simple
sits off the content list — the raise-beyond-one branch live at
each series, its own count nought while the remaining letters read
one each.  The refusal record isolates the content list: with one
counted letter withdrawn the fold falls by one and the identity
fails, the `θ` content read failing with it. -/

/-- The `θ` content list at a table: the vacant content at the
coordinate count with the positive members and their balance
partners at one each. -/
private def thFamOf (t : gentable.Table) (n : Nat) : List (List ground.BPair) :=
  List.replicate t.rank (List.replicate t.rank ground.BPair.unit)
    ++ (List.range n).map (fun j => poly.pnorm (sertables.posCorootV t j))
    ++ (List.range n).map (fun j =>
         poly.pnorm (poly.neg (sertables.posCorootV t j)))

/-- `B_3`'s fundamental data at the coroot presentation. -/
private def fundB3 : sertables.FundData :=
  ⟨[[ground.BPair.ofNat 4, ground.BPair.ofNat 4, ground.BPair.ofNat 2],
    [ground.BPair.ofNat 4, ground.BPair.ofNat 8, ground.BPair.ofNat 4],
    [ground.BPair.ofNat 2, ground.BPair.ofNat 4, ground.BPair.ofNat 3]],
   2, [0, 2, 8],
   [[0, 2, 1, 3, 5, 4, 7, 6, 8],
    [1, 0, 2, 4, 3, 5, 6, 8, 7],
    [0, 4, 5, 3, 1, 2, 6, 7, 8]]⟩

/-- `C_3`'s fundamental data at the coroot presentation. -/
private def fundC3 : sertables.FundData :=
  ⟨[[ground.BPair.ofNat 1, ground.BPair.ofNat 1, ground.BPair.ofNat 1],
    [ground.BPair.ofNat 1, ground.BPair.ofNat 2, ground.BPair.ofNat 2],
    [ground.BPair.ofNat 1, ground.BPair.ofNat 2, ground.BPair.ofNat 3]],
   1, [0, 2, 8],
   [[0, 2, 1, 3, 5, 4, 7, 6, 8],
    [1, 0, 2, 4, 3, 5, 6, 8, 7],
    [0, 4, 5, 3, 1, 2, 6, 7, 8]]⟩

/-- `D_4`'s fundamental data at the coroot presentation. -/
private def fundD4 : sertables.FundData :=
  ⟨[[ground.BPair.ofNat 2, ground.BPair.ofNat 2, ground.BPair.ofNat 1,
     ground.BPair.ofNat 1],
    [ground.BPair.ofNat 2, ground.BPair.ofNat 4, ground.BPair.ofNat 2,
     ground.BPair.ofNat 2],
    [ground.BPair.ofNat 1, ground.BPair.ofNat 2, ground.BPair.ofNat 2,
     ground.BPair.ofNat 1],
    [ground.BPair.ofNat 1, ground.BPair.ofNat 2, ground.BPair.ofNat 1,
     ground.BPair.ofNat 2]],
   1, [0, 2, 5, 11],
   [[0, 2, 1, 4, 3, 5, 6, 8, 7, 10, 9, 11],
    [1, 0, 2, 3, 5, 4, 7, 6, 8, 9, 11, 10],
    [0, 3, 4, 1, 2, 5, 6, 9, 10, 7, 8, 11],
    [0, 9, 10, 7, 8, 5, 6, 3, 4, 1, 2, 11]]⟩

/-! The `b2` fixture's form and family reads, decided once and
consumed by name at every route. -/

private theorem b2Fund : sertables.fundShape (sertables.tableB 2) (sertables.fundB2) := by decide +kernel
private theorem b2Gram : sertables.gramRead (sertables.tableB 2) (sertables.fundB2) := by decide +kernel
private theorem b2GramSym : sertables.gramSymRead (sertables.fundB2) := by decide +kernel
private theorem b2Refl : sertables.reflSquareRead (sertables.tableB 2) := by decide +kernel
private theorem b2Simple : sertables.simplePosRead (sertables.tableB 2) (sertables.fundB2) := by decide +kernel
private theorem b2RhoDot : sertables.rhoDotRead (sertables.tableB 2) (sertables.fundB2) := by decide +kernel
private theorem b2RhoLen : row.rhoLenRead (sertables.tableB 2) (sertables.fundB2) := by decide +kernel
private theorem b2MShape : memberchar.mShapeRead (sertables.tableB 2) (thFamOf (sertables.tableB 2) 4) := by decide +kernel
private theorem b2Fam : row.thetaFamRead (sertables.tableB 2) (thFamOf (sertables.tableB 2) 4) := by decide +kernel

/-! The `b3` fixture's form and family reads, decided once and
consumed by name at every route. -/

private theorem b3Fund : sertables.fundShape (sertables.tableB 3) (fundB3) := by decide +kernel
private theorem b3Gram : sertables.gramRead (sertables.tableB 3) (fundB3) := by decide +kernel
private theorem b3GramSym : sertables.gramSymRead (fundB3) := by decide +kernel
private theorem b3Refl : sertables.reflSquareRead (sertables.tableB 3) := by decide +kernel
private theorem b3Simple : sertables.simplePosRead (sertables.tableB 3) (fundB3) := by decide +kernel
private theorem b3RhoDot : sertables.rhoDotRead (sertables.tableB 3) (fundB3) := by decide +kernel
private theorem b3RhoLen : row.rhoLenRead (sertables.tableB 3) (fundB3) := by decide +kernel
private theorem b3MShape : memberchar.mShapeRead (sertables.tableB 3) (thFamOf (sertables.tableB 3) 9) := by decide +kernel
private theorem b3Fam : row.thetaFamRead (sertables.tableB 3) (thFamOf (sertables.tableB 3) 9) := by decide +kernel

/-! The `c3` fixture's form and family reads, decided once and
consumed by name at every route. -/

private theorem c3Fund : sertables.fundShape (sertables.tableC 3) (fundC3) := by decide +kernel
private theorem c3Gram : sertables.gramRead (sertables.tableC 3) (fundC3) := by decide +kernel
private theorem c3GramSym : sertables.gramSymRead (fundC3) := by decide +kernel
private theorem c3Refl : sertables.reflSquareRead (sertables.tableC 3) := by decide +kernel
private theorem c3Simple : sertables.simplePosRead (sertables.tableC 3) (fundC3) := by decide +kernel
private theorem c3RhoDot : sertables.rhoDotRead (sertables.tableC 3) (fundC3) := by decide +kernel
private theorem c3RhoLen : row.rhoLenRead (sertables.tableC 3) (fundC3) := by decide +kernel
private theorem c3MShape : memberchar.mShapeRead (sertables.tableC 3) (thFamOf (sertables.tableC 3) 9) := by decide +kernel
private theorem c3Fam : row.thetaFamRead (sertables.tableC 3) (thFamOf (sertables.tableC 3) 9) := by decide +kernel

/-! The `d4` fixture's form and family reads, decided once and
consumed by name at every route. -/

private theorem d4Fund : sertables.fundShape (sertables.tableD 4) (fundD4) := by decide +kernel
private theorem d4Gram : sertables.gramRead (sertables.tableD 4) (fundD4) := by decide +kernel
private theorem d4Simple : sertables.simplePosRead (sertables.tableD 4) (fundD4) := by decide +kernel
private theorem d4RhoDot : sertables.rhoDotRead (sertables.tableD 4) (fundD4) := by decide +kernel
private theorem d4RhoLen : row.rhoLenRead (sertables.tableD 4) (fundD4) := by decide +kernel
private theorem d4MShape : memberchar.mShapeRead (sertables.tableD 4) (thFamOf (sertables.tableD 4) 12) := by decide +kernel
private theorem d4Fam : row.thetaFamRead (sertables.tableD 4) (thFamOf (sertables.tableD 4) 12) := by decide +kernel

/-! The members' data at their reads. -/

example : sertables.fundShape (sertables.tableB 3) fundB3 := by decide +kernel
example : sertables.gramRead (sertables.tableB 3) fundB3 := by decide +kernel
example : sertables.simplePosRead (sertables.tableB 3) fundB3 := by decide +kernel
example : sertables.rhoDotRead (sertables.tableB 3) fundB3 := by decide +kernel
example : sertables.permImageRead (sertables.tableB 3) fundB3 := by decide +kernel
example : row.rhoLenRead (sertables.tableB 3) fundB3 := by decide +kernel
example : row.thetaFamRead (sertables.tableB 3) (thFamOf (sertables.tableB 3) 9) := by
  decide +kernel

example : sertables.fundShape (sertables.tableC 3) fundC3 := by decide +kernel
example : sertables.gramRead (sertables.tableC 3) fundC3 := by decide +kernel
example : sertables.simplePosRead (sertables.tableC 3) fundC3 := by decide +kernel
example : sertables.rhoDotRead (sertables.tableC 3) fundC3 := by decide +kernel
example : sertables.permImageRead (sertables.tableC 3) fundC3 := by decide +kernel
example : row.rhoLenRead (sertables.tableC 3) fundC3 := by decide +kernel
example : row.thetaFamRead (sertables.tableC 3) (thFamOf (sertables.tableC 3) 9) := by
  decide +kernel

example : sertables.fundShape (sertables.tableD 4) fundD4 := by decide +kernel
example : sertables.gramRead (sertables.tableD 4) fundD4 := by decide +kernel
example : sertables.simplePosRead (sertables.tableD 4) fundD4 := by decide +kernel
example : sertables.rhoDotRead (sertables.tableD 4) fundD4 := by decide +kernel
example : sertables.permImageRead (sertables.tableD 4) fundD4 := by decide +kernel
example : row.rhoLenRead (sertables.tableD 4) fundD4 := by decide +kernel
example : row.thetaFamRead (sertables.tableD 4) (thFamOf (sertables.tableD 4) 12) := by
  decide +kernel

/-! The members at the vacant word: every raise at one, the fold the
letters' own reads. -/

example : member [] 2 = [0, 0] := by decide +kernel
example : memberRho [] 2 = [1, 1] := by decide +kernel

example : letterFold (sertables.tableB 2) [] 2
    (List.replicate 2 ground.BPair.unit)
    (thFamOf (sertables.tableB 2) 4)
  = ground.countOf 0 (member [] 2) := by decide +kernel
example : letterFold (sertables.tableB 2) [] 2
    (List.replicate 2 ground.BPair.unit)
    (thFamOf (sertables.tableB 2) 4)
  = ground.countOf 0 (member [] 2) :=
  letterFold_vac_B [] 2 sertables.fundB2 (thFamOf (sertables.tableB 2) 4)
    b2Fund b2Gram b2Simple b2RhoDot b2RhoLen
    b2Fam

/-! The members at the word `[1]`: the first raise at two, the
doubled simple off the content list, so the raised key's own count
is nought and the fold falls to the remaining letters. -/

example : member [1] 3 = [1, 0, 0] := by decide +kernel
example : memberRho [1] 3 = [2, 1, 1] := by decide +kernel
example : member [1] 4 = [1, 0, 0, 0] := by decide +kernel
example : memberRho [1] 4 = [2, 1, 1, 1] := by decide +kernel

example : letterFold (sertables.tableB 3) [1] 3
    (List.replicate 3 ground.BPair.unit)
    (thFamOf (sertables.tableB 3) 9) = 2 := by decide +kernel
example : letterFold (sertables.tableB 3) [1] 3
    (List.replicate 3 ground.BPair.unit)
    (thFamOf (sertables.tableB 3) 9)
  = ground.countOf 0 (member [1] 3) :=
  letterFold_vac_B [1] 3 fundB3 (thFamOf (sertables.tableB 3) 9)
    b3Fund b3Gram b3Simple b3RhoDot b3RhoLen
    b3Fam

example : letterFold (sertables.tableC 3) [1] 3
    (List.replicate 3 ground.BPair.unit)
    (thFamOf (sertables.tableC 3) 9) = 2 := by decide +kernel
example : letterFold (sertables.tableC 3) [1] 3
    (List.replicate 3 ground.BPair.unit)
    (thFamOf (sertables.tableC 3) 9)
  = ground.countOf 0 (member [1] 3) :=
  letterFold_vac_C [1] 3 fundC3 (thFamOf (sertables.tableC 3) 9)
    c3Fund c3Gram c3Simple c3RhoDot c3RhoLen
    c3Fam

example : letterFold (sertables.tableD 4) [1] 4
    (List.replicate 4 ground.BPair.unit)
    (thFamOf (sertables.tableD 4) 12) = 3 := by decide +kernel
example : letterFold (sertables.tableD 4) [1] 4
    (List.replicate 4 ground.BPair.unit)
    (thFamOf (sertables.tableD 4) 12)
  = ground.countOf 0 (member [1] 4) :=
  letterFold_vac_D [1] 4 fundD4 (thFamOf (sertables.tableD 4) 12)
    d4Fund d4Gram d4Simple d4RhoDot d4RhoLen
    d4Fam

/-! The content list is load-bearing: with one counted letter
withdrawn the `θ` content read fails and the fold falls by one, the
identity failing with it. -/

/-- `B_3`'s content list with the second simple's own member
withdrawn. -/
private def thFamB3Cut : List (List ground.BPair) :=
  List.replicate 3 (List.replicate 3 ground.BPair.unit)
    ++ ((List.range 9).filter (fun j => ! (j == 2))).map
         (fun j => poly.pnorm (sertables.posCorootV (sertables.tableB 3) j))
    ++ (List.range 9).map (fun j =>
         poly.pnorm (poly.neg (sertables.posCorootV (sertables.tableB 3) j)))

example : ¬ row.thetaFamRead (sertables.tableB 3) thFamB3Cut := by decide +kernel
example : letterFold (sertables.tableB 3) [1] 3
    (List.replicate 3 ground.BPair.unit) thFamB3Cut = 1 := by decide +kernel
example : ¬ (letterFold (sertables.tableB 3) [1] 3
    (List.replicate 3 ground.BPair.unit) thFamB3Cut
  = ground.countOf 0 (member [1] 3)) := by decide +kernel
/-! ## `lem:serstable`(ii)'s row tier: the two convolution counts

The row theorems are routed at the committed orbits: the graded
image list is the shifted key's own Weyl orbit at its parity
grading, and the support witnesses are the simple folds carrying
each member back to the key.  Each conclusion stands twice — the
decided anchor and the same statement through the general theorem
at the stated reads — at the vacant target, where the odd count is
the member's vacant-key count, and at an occupied dominant content,
where the letter tier carries the count.  The dominance binder is
load-bearing: at a target content whose join with the member reads
a negative coroot pair, both counts leave their values.  The `D`
convolution routes run at rank three, the orbit's own count there;
the letter tier routes at rank four and the content cap decides at
rank five, the fork's displayed range.  The
descent and the reach clearance are frame binders — the statement's
own data — and the batteries record their survivals below the
clearance and against the descent.
-/

/-- `D_3`'s fundamental data at the coroot presentation. -/
private def fundD3 : sertables.FundData :=
  ⟨[[ground.BPair.ofNat 4, ground.BPair.ofNat 2, ground.BPair.ofNat 2],
    [ground.BPair.ofNat 2, ground.BPair.ofNat 3, ground.BPair.ofNat 1],
    [ground.BPair.ofNat 2, ground.BPair.ofNat 1, ground.BPair.ofNat 3]],
   2, [0, 2, 5],
   [[0, 2, 1, 3, 5, 4], [1, 0, 2, 4, 3, 5], [4, 3, 2, 1, 0, 5]]⟩

/-- `D_2`'s fundamental data, the rank one short of the word's
clearance. -/
private def fundD2 : sertables.FundData :=
  ⟨[[ground.BPair.ofNat 1, ground.BPair.unit],
    [ground.BPair.unit, ground.BPair.ofNat 1]],
   1, [0, 1], [[0, 1], [0, 1]]⟩

/-! The `d3` fixture's form and family reads, decided once and
consumed by name at every route. -/

private theorem d3Fund : sertables.fundShape (sertables.tableD 3) (fundD3) := by decide +kernel
private theorem d3Gram : sertables.gramRead (sertables.tableD 3) (fundD3) := by decide +kernel
private theorem d3GramSym : sertables.gramSymRead (fundD3) := by decide +kernel
private theorem d3Refl : sertables.reflSquareRead (sertables.tableD 3) := by decide +kernel
private theorem d3Simple : sertables.simplePosRead (sertables.tableD 3) (fundD3) := by decide +kernel
private theorem d3RhoDot : sertables.rhoDotRead (sertables.tableD 3) (fundD3) := by decide +kernel
private theorem d3RhoLen : row.rhoLenRead (sertables.tableD 3) (fundD3) := by decide +kernel
private theorem d3MShape : memberchar.mShapeRead (sertables.tableD 3) (thFamOf (sertables.tableD 3) 6) := by decide +kernel
private theorem d3Fam : row.thetaFamRead (sertables.tableD 3) (thFamOf (sertables.tableD 3) 6) := by decide +kernel

example : sertables.fundShape (sertables.tableD 3) fundD3 := by decide +kernel
example : sertables.gramRead (sertables.tableD 3) fundD3 := by decide +kernel
example : sertables.gramSymRead fundD3 := by decide +kernel
example : sertables.reflSquareRead (sertables.tableD 3) := by decide +kernel
example : sertables.simplePosRead (sertables.tableD 3) fundD3 := by
  decide +kernel
example : sertables.rhoDotRead (sertables.tableD 3) fundD3 := by decide +kernel
example : sertables.permImageRead (sertables.tableD 3) fundD3 := by
  decide +kernel
example : row.rhoLenRead (sertables.tableD 3) fundD3 := by decide +kernel
example : row.thetaFamRead (sertables.tableD 3)
    (thFamOf (sertables.tableD 3) 6) := by decide +kernel
example : memberchar.mShapeRead (sertables.tableD 3)
    (thFamOf (sertables.tableD 3) 6) := by decide +kernel

example : sertables.fundShape (sertables.tableD 2) fundD2 := by decide +kernel
example : sertables.gramRead (sertables.tableD 2) fundD2 := by decide +kernel
example : sertables.gramSymRead fundD2 := by decide +kernel
example : sertables.reflSquareRead (sertables.tableD 2) := by decide +kernel
example : sertables.simplePosRead (sertables.tableD 2) fundD2 := by
  decide +kernel
example : sertables.rhoDotRead (sertables.tableD 2) fundD2 := by decide +kernel
example : row.rhoLenRead (sertables.tableD 2) fundD2 := by decide +kernel
example : row.thetaFamRead (sertables.tableD 2)
    (thFamOf (sertables.tableD 2) 2) := by decide +kernel
example : memberchar.mShapeRead (sertables.tableD 2)
    (thFamOf (sertables.tableD 2) 2) := by decide +kernel

/-- `B_2`'s shifted key at the vacant word, its Weyl orbit graded -/
private def wB2v : List (List ground.BPair × Bool) :=
  [([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 3], false),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 1).swap], false),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 3).swap], false),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 1], true),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 3], true),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 3).swap], true),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 1).swap], true)]

/-- The same orbit's support witnesses. -/
private def wB2vwits : List (List Nat) :=
  [[2, 1],
   [3, 4],
   [0, 0],
   [1, 3],
   [3, 3],
   [1, 0],
   [2, 4],
   [0, 1]]


/-- `B_3`'s shifted key at the word `[1]`, its Weyl orbit graded -/
private def wB3 : List (List ground.BPair × Bool) :=
  [([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 2, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 3, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 4).swap, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 3], false),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 3).swap], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 1, (ground.BPair.ofNat 3).swap], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 2, ground.BPair.ofNat 3], false),
   ([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 7], false),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 7).swap], false),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 7], false),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 7).swap], false),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 7], false),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 2, (ground.BPair.ofNat 7).swap], false),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 7], false),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap], false),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 1, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 3, (ground.BPair.ofNat 7).swap], false),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 3], false),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 2, (ground.BPair.ofNat 3).swap], false),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 3).swap], false),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 3], false),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 1, ground.BPair.ofNat 1], true),
   ([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 1).swap], true),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 2, (ground.BPair.ofNat 3).swap], true),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 2, ground.BPair.ofNat 3], true),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 3], true),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 3).swap], true),
   ([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 7], true),
   ([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 1).swap], true),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 3, ground.BPair.ofNat 1], true),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 7).swap], true),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 7], true),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 3, (ground.BPair.ofNat 7).swap], true),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 7], true),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 4, (ground.BPair.ofNat 7).swap], true),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 1], true),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 7], true),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 2, (ground.BPair.ofNat 7).swap], true),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 2, (ground.BPair.ofNat 1).swap], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 3).swap], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 3], true),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 3], true),
   ([ground.BPair.ofNat 4, ground.BPair.ofNat 1, (ground.BPair.ofNat 3).swap], true),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap], true),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 1], true)]

/-- The same orbit's support witnesses. -/
private def wB3wits : List (List Nat) :=
  [[7, 7, 8],
   [5, 3, 3],
   [7, 8, 7],
   [4, 2, 4],
   [7, 9, 11],
   [3, 1, 0],
   [7, 10, 10],
   [4, 4, 1],
   [5, 6, 10],
   [2, 0, 1],
   [5, 7, 4],
   [3, 3, 7],
   [2, 3, 0],
   [4, 7, 11],
   [3, 6, 3],
   [5, 10, 11],
   [0, 0, 0],
   [2, 4, 8],
   [4, 9, 8],
   [0, 1, 3],
   [3, 8, 10],
   [0, 2, 1],
   [2, 7, 7],
   [0, 3, 4],
   [7, 7, 7],
   [5, 3, 4],
   [7, 8, 10],
   [4, 2, 1],
   [7, 9, 8],
   [3, 1, 3],
   [5, 6, 3],
   [7, 10, 11],
   [2, 0, 0],
   [4, 4, 8],
   [3, 3, 0],
   [5, 7, 11],
   [4, 7, 4],
   [2, 3, 7],
   [5, 10, 10],
   [2, 4, 1],
   [3, 6, 10],
   [0, 0, 1],
   [4, 9, 11],
   [0, 1, 0],
   [3, 8, 7],
   [0, 2, 4],
   [2, 7, 8],
   [0, 3, 3]]


/-- `C_3`'s shifted key at the word `[1]`, its Weyl orbit graded -/
private def wC3 : List (List ground.BPair × Bool) :=
  [([(ground.BPair.ofNat 6).swap, ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 6).swap, ground.BPair.ofNat 3, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 5).swap, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 2], false),
   ([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 6, (ground.BPair.ofNat 2).swap], false),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 4], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 1, (ground.BPair.ofNat 2).swap], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 2, ground.BPair.ofNat 2], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 4).swap], false),
   ([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 4], false),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 6, (ground.BPair.ofNat 4).swap], false),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 4], false),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 2, (ground.BPair.ofNat 4).swap], false),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap], false),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 1, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 6).swap, ground.BPair.ofNat 2], false),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 6).swap, ground.BPair.ofNat 4], false),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 3, (ground.BPair.ofNat 4).swap], false),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 3, (ground.BPair.ofNat 2).swap], false),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 2], false),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 2).swap], false),
   ([ground.BPair.ofNat 6, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 6, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 6).swap, ground.BPair.ofNat 1, ground.BPair.ofNat 1], true),
   ([(ground.BPair.ofNat 6).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 1).swap], true),
   ([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 2, ground.BPair.ofNat 2], true),
   ([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 3, (ground.BPair.ofNat 2).swap], true),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 2], true),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 4], true),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 6, (ground.BPair.ofNat 4).swap], true),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 6, (ground.BPair.ofNat 2).swap], true),
   ([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 1).swap], true),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 3, ground.BPair.ofNat 1], true),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 4], true),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 3, (ground.BPair.ofNat 4).swap], true),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 6).swap, ground.BPair.ofNat 4], true),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 5, (ground.BPair.ofNat 4).swap], true),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 1], true),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 4], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 2).swap], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 2], true),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 2, (ground.BPair.ofNat 4).swap], true),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 6).swap, ground.BPair.ofNat 2], true),
   ([ground.BPair.ofNat 5, ground.BPair.ofNat 1, (ground.BPair.ofNat 2).swap], true),
   ([ground.BPair.ofNat 6, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap], true),
   ([ground.BPair.ofNat 6, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 1], true)]

/-- The same orbit's support witnesses. -/
private def wC3wits : List (List Nat) :=
  [[8, 8, 5],
   [6, 4, 2],
   [8, 9, 4],
   [5, 3, 3],
   [5, 5, 1],
   [8, 11, 7],
   [3, 1, 0],
   [6, 7, 6],
   [8, 12, 6],
   [2, 0, 1],
   [6, 9, 3],
   [3, 3, 4],
   [2, 3, 0],
   [5, 9, 7],
   [6, 12, 7],
   [0, 0, 0],
   [5, 11, 5],
   [3, 7, 2],
   [2, 5, 5],
   [0, 1, 2],
   [0, 3, 1],
   [3, 9, 6],
   [2, 8, 4],
   [0, 4, 3],
   [8, 8, 4],
   [6, 4, 3],
   [5, 3, 1],
   [8, 9, 6],
   [8, 11, 5],
   [6, 7, 2],
   [5, 5, 5],
   [3, 1, 2],
   [8, 12, 7],
   [2, 0, 0],
   [3, 3, 0],
   [6, 9, 7],
   [5, 9, 3],
   [2, 3, 4],
   [6, 12, 6],
   [0, 0, 1],
   [2, 5, 1],
   [5, 11, 7],
   [0, 1, 0],
   [3, 7, 6],
   [3, 9, 4],
   [0, 3, 3],
   [2, 8, 5],
   [0, 4, 2]]


/-- `D_3`'s shifted key at the word `[1]`, its Weyl orbit graded -/
private def wD3 : List (List ground.BPair × Bool) :=
  [([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 1, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 2, ground.BPair.ofNat 4], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 4, ground.BPair.ofNat 2], false),
   ([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 3], false),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 3, (ground.BPair.ofNat 3).swap], false),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 3], false),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 3, (ground.BPair.ofNat 3).swap], false),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 1, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 4).swap, (ground.BPair.ofNat 2).swap], false),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 4).swap], false),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 3, ground.BPair.ofNat 3], true),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 1], true),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 1, (ground.BPair.ofNat 1).swap], true),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 3, ground.BPair.ofNat 3], true),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 4], true),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 2).swap], true),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 2], true),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 2, (ground.BPair.ofNat 4).swap], true),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 3).swap], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 1], true),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 1, (ground.BPair.ofNat 1).swap], true),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 3).swap], true)]

/-- The same orbit's support witnesses. -/
private def wD3wits : List (List Nat) :=
  [[6, 3, 3],
   [3, 1, 0],
   [3, 0, 1],
   [6, 4, 4],
   [4, 4, 1],
   [4, 1, 4],
   [2, 3, 0],
   [2, 0, 3],
   [0, 0, 0],
   [3, 4, 3],
   [3, 3, 4],
   [0, 1, 1],
   [4, 1, 1],
   [6, 4, 3],
   [6, 3, 4],
   [2, 0, 0],
   [3, 3, 0],
   [3, 0, 3],
   [3, 4, 1],
   [3, 1, 4],
   [4, 4, 4],
   [0, 1, 0],
   [0, 0, 1],
   [2, 3, 3]]


/-- `D_2`'s shifted key at the word `[1]`, one rank short of the clearance -/
private def wD2 : List (List ground.BPair × Bool) :=
  [([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 1).swap], false),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 1], true),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 1).swap], true)]

/-- The same orbit's support witnesses. -/
private def wD2wits : List (List Nat) :=
  [[2, 1],
   [0, 0],
   [2, 0],
   [0, 1]]


/-- `B_3`'s shifted key at the word `[1, 1]`, one rank short of the clearance -/
private def wB3c : List (List ground.BPair × Bool) :=
  [([(ground.BPair.ofNat 6).swap, ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 6).swap, ground.BPair.ofNat 3, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 4).swap, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 5], false),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 6, (ground.BPair.ofNat 5).swap], false),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 7], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 1, ground.BPair.ofNat 5], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 2, (ground.BPair.ofNat 5).swap], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 7).swap], false),
   ([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 7], false),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 6, (ground.BPair.ofNat 7).swap], false),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 1).swap], false),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap], false),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 2, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 7], false),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 1, (ground.BPair.ofNat 7).swap], false),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 6).swap, ground.BPair.ofNat 5], false),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 6).swap, ground.BPair.ofNat 7], false),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 3, (ground.BPair.ofNat 7).swap], false),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 3, (ground.BPair.ofNat 5).swap], false),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 5], false),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 5).swap], false),
   ([ground.BPair.ofNat 6, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 6, (ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 6).swap, ground.BPair.ofNat 2, ground.BPair.ofNat 1], true),
   ([(ground.BPair.ofNat 6).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 1).swap], true),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 1, ground.BPair.ofNat 5], true),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 3, (ground.BPair.ofNat 5).swap], true),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 5], true),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 7], true),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 6, (ground.BPair.ofNat 7).swap], true),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 6, (ground.BPair.ofNat 5).swap], true),
   ([(ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 7], true),
   ([(ground.BPair.ofNat 2).swap, ground.BPair.ofNat 3, (ground.BPair.ofNat 7).swap], true),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 2).swap, (ground.BPair.ofNat 1).swap], true),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 3, ground.BPair.ofNat 1], true),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 1], true),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap], true),
   ([ground.BPair.ofNat 2, (ground.BPair.ofNat 6).swap, ground.BPair.ofNat 7], true),
   ([ground.BPair.ofNat 2, ground.BPair.ofNat 4, (ground.BPair.ofNat 7).swap], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 7], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 2).swap, ground.BPair.ofNat 5], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 5).swap], true),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 1, (ground.BPair.ofNat 7).swap], true),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 6).swap, ground.BPair.ofNat 5], true),
   ([ground.BPair.ofNat 4, ground.BPair.ofNat 2, (ground.BPair.ofNat 5).swap], true),
   ([ground.BPair.ofNat 6, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap], true),
   ([ground.BPair.ofNat 6, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 1], true)]

/-- The same orbit's support witnesses. -/
private def wB3cwits : List (List Nat) :=
  [[7, 7, 8],
   [6, 5, 5],
   [7, 9, 7],
   [4, 3, 6],
   [4, 4, 1],
   [3, 2, 0],
   [7, 10, 13],
   [6, 8, 12],
   [6, 9, 6],
   [3, 3, 7],
   [7, 12, 12],
   [1, 0, 1],
   [6, 12, 13],
   [0, 0, 0],
   [1, 3, 0],
   [4, 9, 13],
   [4, 10, 8],
   [3, 8, 5],
   [1, 4, 8],
   [0, 2, 5],
   [0, 3, 1],
   [3, 9, 12],
   [1, 7, 7],
   [0, 5, 6],
   [7, 7, 7],
   [6, 5, 6],
   [4, 3, 1],
   [7, 9, 12],
   [7, 10, 8],
   [6, 8, 5],
   [4, 4, 8],
   [3, 2, 5],
   [3, 3, 0],
   [6, 9, 13],
   [7, 12, 13],
   [1, 0, 0],
   [6, 12, 12],
   [0, 0, 1],
   [4, 9, 6],
   [1, 3, 7],
   [1, 4, 1],
   [0, 2, 0],
   [4, 10, 13],
   [3, 8, 12],
   [3, 9, 7],
   [0, 3, 6],
   [1, 7, 8],
   [0, 5, 5]]


/-- `B_3`'s shifted key at the ascending word `[1, 2]` -/
private def wB3s : List (List ground.BPair × Bool) :=
  [([(ground.BPair.ofNat 8).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 8).swap, ground.BPair.ofNat 4, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 5).swap, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 7], false),
   ([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 8, (ground.BPair.ofNat 7).swap], false),
   ([(ground.BPair.ofNat 4).swap, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 9], false),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 1, ground.BPair.ofNat 7], false),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 3, (ground.BPair.ofNat 7).swap], false),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 9).swap], false),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 9], false),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 8, (ground.BPair.ofNat 9).swap], false),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 1], false),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 1).swap], false),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 4).swap, (ground.BPair.ofNat 1).swap], false),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 3, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 9], false),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 1, (ground.BPair.ofNat 9).swap], false),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 8).swap, ground.BPair.ofNat 7], false),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 8).swap, ground.BPair.ofNat 9], false),
   ([ground.BPair.ofNat 4, ground.BPair.ofNat 4, (ground.BPair.ofNat 9).swap], false),
   ([ground.BPair.ofNat 4, ground.BPair.ofNat 4, (ground.BPair.ofNat 7).swap], false),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 7], false),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 7).swap], false),
   ([ground.BPair.ofNat 8, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 1], false),
   ([ground.BPair.ofNat 8, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap], false),
   ([(ground.BPair.ofNat 8).swap, ground.BPair.ofNat 3, ground.BPair.ofNat 1], true),
   ([(ground.BPair.ofNat 8).swap, ground.BPair.ofNat 5, (ground.BPair.ofNat 1).swap], true),
   ([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 1, ground.BPair.ofNat 7], true),
   ([(ground.BPair.ofNat 5).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 7).swap], true),
   ([(ground.BPair.ofNat 4).swap, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 7], true),
   ([(ground.BPair.ofNat 4).swap, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 9], true),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 8, (ground.BPair.ofNat 9).swap], true),
   ([(ground.BPair.ofNat 4).swap, ground.BPair.ofNat 8, (ground.BPair.ofNat 7).swap], true),
   ([(ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap, ground.BPair.ofNat 9], true),
   ([(ground.BPair.ofNat 3).swap, ground.BPair.ofNat 4, (ground.BPair.ofNat 9).swap], true),
   ([(ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 3).swap, (ground.BPair.ofNat 1).swap], true),
   ([(ground.BPair.ofNat 1).swap, ground.BPair.ofNat 4, ground.BPair.ofNat 1], true),
   ([ground.BPair.ofNat 1, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 1], true),
   ([ground.BPair.ofNat 1, ground.BPair.ofNat 4, (ground.BPair.ofNat 1).swap], true),
   ([ground.BPair.ofNat 3, (ground.BPair.ofNat 8).swap, ground.BPair.ofNat 9], true),
   ([ground.BPair.ofNat 3, ground.BPair.ofNat 5, (ground.BPair.ofNat 9).swap], true),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 5).swap, ground.BPair.ofNat 9], true),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 3).swap, ground.BPair.ofNat 7], true),
   ([ground.BPair.ofNat 4, (ground.BPair.ofNat 1).swap, (ground.BPair.ofNat 7).swap], true),
   ([ground.BPair.ofNat 4, ground.BPair.ofNat 1, (ground.BPair.ofNat 9).swap], true),
   ([ground.BPair.ofNat 5, (ground.BPair.ofNat 8).swap, ground.BPair.ofNat 7], true),
   ([ground.BPair.ofNat 5, ground.BPair.ofNat 3, (ground.BPair.ofNat 7).swap], true),
   ([ground.BPair.ofNat 8, (ground.BPair.ofNat 4).swap, (ground.BPair.ofNat 1).swap], true),
   ([ground.BPair.ofNat 8, (ground.BPair.ofNat 4).swap, ground.BPair.ofNat 1], true)]

/-- The same orbit's support witnesses. -/
private def wB3swits : List (List Nat) :=
  [[9, 9, 10],
   [8, 7, 7],
   [9, 12, 9],
   [5, 4, 8],
   [5, 5, 1],
   [4, 3, 0],
   [9, 13, 17],
   [8, 11, 16],
   [8, 12, 8],
   [4, 4, 9],
   [9, 16, 16],
   [1, 0, 1],
   [8, 16, 17],
   [0, 0, 0],
   [1, 4, 0],
   [5, 12, 17],
   [5, 13, 10],
   [4, 11, 7],
   [1, 5, 10],
   [0, 3, 7],
   [0, 4, 1],
   [4, 12, 16],
   [1, 9, 9],
   [0, 7, 8],
   [9, 9, 9],
   [8, 7, 8],
   [5, 4, 1],
   [9, 12, 16],
   [9, 13, 10],
   [8, 11, 7],
   [5, 5, 10],
   [4, 3, 7],
   [4, 4, 0],
   [8, 12, 17],
   [9, 16, 17],
   [1, 0, 0],
   [8, 16, 16],
   [0, 0, 1],
   [5, 12, 8],
   [1, 4, 9],
   [1, 5, 1],
   [0, 3, 0],
   [5, 13, 17],
   [4, 11, 16],
   [4, 12, 9],
   [0, 4, 8],
   [1, 9, 10],
   [0, 7, 7]]


/-! The content cap's closed forms at the series' fold families:
the positive list's every member carries the displayed cap, decided
at the first ranks where all three families' generic shapes appear
— the chain's interior keys at `B` and `C`, and the fork's own
middle at `D`. -/

example : ∀ j, j < (sertables.tableB 4).posFolds.length →
    gentable.formNum (sertables.tableB 4)
        (ground.getAt [] (sertables.tableB 4).posFolds j)
        (ground.getAt [] (sertables.tableB 4).posFolds j)
      ≤ ground.BPair.ofNat 4 := by decide +kernel

example : ∀ j, j < (sertables.tableC 4).posFolds.length →
    gentable.formNum (sertables.tableC 4)
        (ground.getAt [] (sertables.tableC 4).posFolds j)
        (ground.getAt [] (sertables.tableC 4).posFolds j)
      ≤ ground.BPair.ofNat 4 := by decide +kernel

example : ∀ j, j < (sertables.tableD 5).posFolds.length →
    gentable.formNum (sertables.tableD 5)
        (ground.getAt [] (sertables.tableD 5).posFolds j)
        (ground.getAt [] (sertables.tableD 5).posFolds j)
      ≤ ground.BPair.ofNat 4 := by decide +kernel

/-! The `B_2` instance at the vacant word: the reads, the vacant
target and an occupied dominant content. -/

/-- `B_2` at the vacant word: the graded image list's shape read. -/
private theorem b2Shape : sertables.wShapeRead (sertables.tableB 2) wB2v := by
  decide +kernel
/-- `B_2` at the vacant word: the closure read. -/
private theorem b2Close : assembly.wCloseRead (sertables.tableB 2) wB2v := by
  decide +kernel
/-- `B_2` at the vacant word: the shifted key's top read. -/
private theorem b2Top : assembly.wTopAt wB2v
    (poly.pnorm (elim.vecAdd (memberV [] 2)
      (sertables.rhoV (sertables.tableB 2)))) := by decide +kernel
/-- `B_2` at the vacant word: the support read at the witness folds. -/
private theorem b2Dom : assembly.wDomAt (sertables.tableB 2) wB2v wB2vwits
    (poly.pnorm (elim.vecAdd (memberV [] 2)
      (sertables.rhoV (sertables.tableB 2)))) := by decide +kernel
/-- `B_2` at the vacant word: the tie's kept square across the orbit. -/
private theorem b2Sq : row.sqAtRead sertables.fundB2 wB2v
    (poly.pnorm (elim.vecAdd (memberV [] 2)
      (sertables.rhoV (sertables.tableB 2)))) := by decide +kernel
/-- `B_2` at the vacant word: the contents' cap through the
theorem, `lem:serstable`(ii)'s derived read at the series table. -/
example : ∀ z ∈ (thFamOf (sertables.tableB 2) 4),
    sertables.dotB sertables.fundB2 z z
      ≤ ground.BPair.ofNat (4 * (sertables.fundB2).scale) :=
  serstable.contentCap_B 2 sertables.fundB2 (thFamOf (sertables.tableB 2) 4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)


example : memberchar.convCount wB2v (thFamOf (sertables.tableB 2) 4)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [] 2)
            (sertables.rhoV (sertables.tableB 2))))
          (List.replicate 2 ground.BPair.unit))) false
      = ground.countOf (List.replicate 2 ground.BPair.unit) (thFamOf (sertables.tableB 2) 4)
    ∧ memberchar.convCount wB2v (thFamOf (sertables.tableB 2) 4)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [] 2)
            (sertables.rhoV (sertables.tableB 2))))
          (List.replicate 2 ground.BPair.unit))) true
      = letterFold (sertables.tableB 2) [] 2 (List.replicate 2 ground.BPair.unit) (thFamOf (sertables.tableB 2) 4) := by
  decide +kernel

example : memberchar.convCount wB2v (thFamOf (sertables.tableB 2) 4)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [] 2)
            (sertables.rhoV (sertables.tableB 2))))
          (List.replicate 2 ground.BPair.unit))) false
      = ground.countOf (List.replicate 2 ground.BPair.unit) (thFamOf (sertables.tableB 2) 4)
    ∧ memberchar.convCount wB2v (thFamOf (sertables.tableB 2) 4)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [] 2)
            (sertables.rhoV (sertables.tableB 2))))
          (List.replicate 2 ground.BPair.unit))) true
      = letterFold (sertables.tableB 2) [] 2 (List.replicate 2 ground.BPair.unit) (thFamOf (sertables.tableB 2) 4) :=
  rowValues_B 2 sertables.fundB2 wB2v wB2vwits
    (thFamOf (sertables.tableB 2) 4) (memberV [] 2) (memberRho [] 2)
    (List.replicate 2 ground.BPair.unit)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    b2Fund b2Gram b2GramSym
    b2Refl b2Simple b2RhoDot b2RhoLen
    b2Shape b2Close b2Dom b2Top b2Sq
    b2MShape b2Fam (by decide +kernel) (by decide +kernel)

example : memberchar.convCount wB2v (thFamOf (sertables.tableB 2) 4)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [] 2)
            (sertables.rhoV (sertables.tableB 2))))
          (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 2)))) false
      = ground.countOf (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 2)) (thFamOf (sertables.tableB 2) 4)
    ∧ memberchar.convCount wB2v (thFamOf (sertables.tableB 2) 4)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [] 2)
            (sertables.rhoV (sertables.tableB 2))))
          (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 2)))) true
      = letterFold (sertables.tableB 2) [] 2 (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 2)) (thFamOf (sertables.tableB 2) 4) := by
  decide +kernel

example : memberchar.convCount wB2v (thFamOf (sertables.tableB 2) 4)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [] 2)
            (sertables.rhoV (sertables.tableB 2))))
          (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 2)))) false
      = ground.countOf (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 2)) (thFamOf (sertables.tableB 2) 4)
    ∧ memberchar.convCount wB2v (thFamOf (sertables.tableB 2) 4)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [] 2)
            (sertables.rhoV (sertables.tableB 2))))
          (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 2)))) true
      = letterFold (sertables.tableB 2) [] 2 (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 2)) (thFamOf (sertables.tableB 2) 4) :=
  rowValues_B 2 sertables.fundB2 wB2v wB2vwits
    (thFamOf (sertables.tableB 2) 4) (memberV [] 2) (memberRho [] 2)
    (poly.pnorm (sertables.posCorootV (sertables.tableB 2) 2))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    b2Fund b2Gram b2GramSym
    b2Refl b2Simple b2RhoDot b2RhoLen
    b2Shape b2Close b2Dom b2Top b2Sq
    b2MShape b2Fam (by decide +kernel) (by decide +kernel)

/-! The `B_3` instance at the word `[1]`. -/

/-- `B_3` at the word `[1]`: the graded image list's shape read. -/
private theorem b3Shape : sertables.wShapeRead (sertables.tableB 3) wB3 := by
  decide +kernel
/-- `B_3` at the word `[1]`: the closure read. -/
private theorem b3Close : assembly.wCloseRead (sertables.tableB 3) wB3 := by
  decide +kernel
/-- `B_3` at the word `[1]`: the shifted key's top read. -/
private theorem b3Top : assembly.wTopAt wB3
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (sertables.rhoV (sertables.tableB 3)))) := by decide +kernel
/-- `B_3` at the word `[1]`: the support read at the witness folds. -/
private theorem b3Dom : assembly.wDomAt (sertables.tableB 3) wB3 wB3wits
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (sertables.rhoV (sertables.tableB 3)))) := by decide +kernel
/-- `B_3` at the word `[1]`: the tie's kept square across the orbit. -/
private theorem b3Sq : row.sqAtRead fundB3 wB3
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (sertables.rhoV (sertables.tableB 3)))) := by decide +kernel
/-- `B_3` at the word `[1]`: the contents' cap. -/
example : ∀ z ∈ (thFamOf (sertables.tableB 3) 9),
    sertables.dotB fundB3 z z
      ≤ ground.BPair.ofNat (4 * (fundB3).scale) :=
  serstable.contentCap_B 3 fundB3 (thFamOf (sertables.tableB 3) 9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)


example : memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (List.replicate 3 ground.BPair.unit))) false
      = ground.countOf (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableB 3) 9)
    ∧ memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (List.replicate 3 ground.BPair.unit))) true
      = letterFold (sertables.tableB 3) [1] 3 (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableB 3) 9) := by
  decide +kernel

example : memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (List.replicate 3 ground.BPair.unit))) false
      = ground.countOf (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableB 3) 9)
    ∧ memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (List.replicate 3 ground.BPair.unit))) true
      = letterFold (sertables.tableB 3) [1] 3 (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableB 3) 9) :=
  rowValues_B 3 fundB3 wB3 wB3wits
    (thFamOf (sertables.tableB 3) 9) (memberV [1] 3) (memberRho [1] 3)
    (List.replicate 3 ground.BPair.unit)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    b3Fund b3Gram b3GramSym
    b3Refl b3Simple b3RhoDot b3RhoLen
    b3Shape b3Close b3Dom b3Top b3Sq
    b3MShape b3Fam (by decide +kernel) (by decide +kernel)

example : memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6)))) false
      = ground.countOf (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6)) (thFamOf (sertables.tableB 3) 9)
    ∧ memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6)))) true
      = letterFold (sertables.tableB 3) [1] 3 (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6)) (thFamOf (sertables.tableB 3) 9) := by
  decide +kernel

example : memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6)))) false
      = ground.countOf (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6)) (thFamOf (sertables.tableB 3) 9)
    ∧ memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6)))) true
      = letterFold (sertables.tableB 3) [1] 3 (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6)) (thFamOf (sertables.tableB 3) 9) :=
  rowValues_B 3 fundB3 wB3 wB3wits
    (thFamOf (sertables.tableB 3) 9) (memberV [1] 3) (memberRho [1] 3)
    (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    b3Fund b3Gram b3GramSym
    b3Refl b3Simple b3RhoDot b3RhoLen
    b3Shape b3Close b3Dom b3Top b3Sq
    b3MShape b3Fam (by decide +kernel) (by decide +kernel)

/-! The `C_3` and `D_3` instances at the word `[1]`. -/

/-- `C_3` at the word `[1]`: the graded image list's shape read. -/
private theorem c3Shape : sertables.wShapeRead (sertables.tableC 3) wC3 := by
  decide +kernel
/-- `C_3` at the word `[1]`: the closure read. -/
private theorem c3Close : assembly.wCloseRead (sertables.tableC 3) wC3 := by
  decide +kernel
/-- `C_3` at the word `[1]`: the shifted key's top read. -/
private theorem c3Top : assembly.wTopAt wC3
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (sertables.rhoV (sertables.tableC 3)))) := by decide +kernel
/-- `C_3` at the word `[1]`: the support read at the witness folds. -/
private theorem c3Dom : assembly.wDomAt (sertables.tableC 3) wC3 wC3wits
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (sertables.rhoV (sertables.tableC 3)))) := by decide +kernel
/-- `C_3` at the word `[1]`: the tie's kept square across the orbit. -/
private theorem c3Sq : row.sqAtRead fundC3 wC3
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (sertables.rhoV (sertables.tableC 3)))) := by decide +kernel
/-- `C_3` at the word `[1]`: the contents' cap. -/
example : ∀ z ∈ (thFamOf (sertables.tableC 3) 9),
    sertables.dotB fundC3 z z
      ≤ ground.BPair.ofNat (4 * (fundC3).scale) :=
  serstable.contentCap_C 3 fundC3 (thFamOf (sertables.tableC 3) 9)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)


example : memberchar.convCount wC3 (thFamOf (sertables.tableC 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableC 3))))
          (List.replicate 3 ground.BPair.unit))) false
      = ground.countOf (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableC 3) 9)
    ∧ memberchar.convCount wC3 (thFamOf (sertables.tableC 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableC 3))))
          (List.replicate 3 ground.BPair.unit))) true
      = letterFold (sertables.tableC 3) [1] 3 (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableC 3) 9) := by
  decide +kernel

example : memberchar.convCount wC3 (thFamOf (sertables.tableC 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableC 3))))
          (List.replicate 3 ground.BPair.unit))) false
      = ground.countOf (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableC 3) 9)
    ∧ memberchar.convCount wC3 (thFamOf (sertables.tableC 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableC 3))))
          (List.replicate 3 ground.BPair.unit))) true
      = letterFold (sertables.tableC 3) [1] 3 (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableC 3) 9) :=
  rowValues_C 3 fundC3 wC3 wC3wits
    (thFamOf (sertables.tableC 3) 9) (memberV [1] 3) (memberRho [1] 3)
    (List.replicate 3 ground.BPair.unit)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    c3Fund c3Gram c3GramSym
    c3Refl c3Simple c3RhoDot c3RhoLen
    c3Shape c3Close c3Dom c3Top c3Sq
    c3MShape c3Fam (by decide +kernel) (by decide +kernel)

example : memberchar.convCount wC3 (thFamOf (sertables.tableC 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableC 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)))) false
      = ground.countOf (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)) (thFamOf (sertables.tableC 3) 9)
    ∧ memberchar.convCount wC3 (thFamOf (sertables.tableC 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableC 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)))) true
      = letterFold (sertables.tableC 3) [1] 3 (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)) (thFamOf (sertables.tableC 3) 9) := by
  decide +kernel

example : memberchar.convCount wC3 (thFamOf (sertables.tableC 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableC 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)))) false
      = ground.countOf (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)) (thFamOf (sertables.tableC 3) 9)
    ∧ memberchar.convCount wC3 (thFamOf (sertables.tableC 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableC 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)))) true
      = letterFold (sertables.tableC 3) [1] 3 (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)) (thFamOf (sertables.tableC 3) 9) :=
  rowValues_C 3 fundC3 wC3 wC3wits
    (thFamOf (sertables.tableC 3) 9) (memberV [1] 3) (memberRho [1] 3)
    (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    c3Fund c3Gram c3GramSym
    c3Refl c3Simple c3RhoDot c3RhoLen
    c3Shape c3Close c3Dom c3Top c3Sq
    c3MShape c3Fam (by decide +kernel) (by decide +kernel)

/-- `D_3` at the word `[1]`: the graded image list's shape read. -/
private theorem d3Shape : sertables.wShapeRead (sertables.tableD 3) wD3 := by
  decide +kernel
/-- `D_3` at the word `[1]`: the closure read. -/
private theorem d3Close : assembly.wCloseRead (sertables.tableD 3) wD3 := by
  decide +kernel
/-- `D_3` at the word `[1]`: the shifted key's top read. -/
private theorem d3Top : assembly.wTopAt wD3
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (sertables.rhoV (sertables.tableD 3)))) := by decide +kernel
/-- `D_3` at the word `[1]`: the support read at the witness folds. -/
private theorem d3Dom : assembly.wDomAt (sertables.tableD 3) wD3 wD3wits
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (sertables.rhoV (sertables.tableD 3)))) := by decide +kernel
/-- `D_3` at the word `[1]`: the tie's kept square across the orbit. -/
private theorem d3Sq : row.sqAtRead fundD3 wD3
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (sertables.rhoV (sertables.tableD 3)))) := by decide +kernel
/-- `D_3` at the word `[1]`: the contents' cap. -/
example : ∀ z ∈ (thFamOf (sertables.tableD 3) 6),
    sertables.dotB fundD3 z z
      ≤ ground.BPair.ofNat (4 * (fundD3).scale) :=
  serstable.contentCap_D 3 fundD3 (thFamOf (sertables.tableD 3) 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)


example : memberchar.convCount wD3 (thFamOf (sertables.tableD 3) 6)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableD 3))))
          (List.replicate 3 ground.BPair.unit))) false
      = ground.countOf (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableD 3) 6)
    ∧ memberchar.convCount wD3 (thFamOf (sertables.tableD 3) 6)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableD 3))))
          (List.replicate 3 ground.BPair.unit))) true
      = letterFold (sertables.tableD 3) [1] 3 (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableD 3) 6) := by
  decide +kernel

example : memberchar.convCount wD3 (thFamOf (sertables.tableD 3) 6)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableD 3))))
          (List.replicate 3 ground.BPair.unit))) false
      = ground.countOf (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableD 3) 6)
    ∧ memberchar.convCount wD3 (thFamOf (sertables.tableD 3) 6)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableD 3))))
          (List.replicate 3 ground.BPair.unit))) true
      = letterFold (sertables.tableD 3) [1] 3 (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableD 3) 6) :=
  rowValues_D 3 fundD3 wD3 wD3wits
    (thFamOf (sertables.tableD 3) 6) (memberV [1] 3) (memberRho [1] 3)
    (List.replicate 3 ground.BPair.unit)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    d3Fund d3Gram d3GramSym
    d3Refl d3Simple d3RhoDot d3RhoLen
    d3Shape d3Close d3Dom d3Top d3Sq
    d3MShape d3Fam (by decide +kernel) (by decide +kernel)

example : memberchar.convCount wD3 (thFamOf (sertables.tableD 3) 6)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableD 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3)))) false
      = ground.countOf (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3)) (thFamOf (sertables.tableD 3) 6)
    ∧ memberchar.convCount wD3 (thFamOf (sertables.tableD 3) 6)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableD 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3)))) true
      = letterFold (sertables.tableD 3) [1] 3 (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3)) (thFamOf (sertables.tableD 3) 6) := by
  decide +kernel

example : memberchar.convCount wD3 (thFamOf (sertables.tableD 3) 6)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableD 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3)))) false
      = ground.countOf (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3)) (thFamOf (sertables.tableD 3) 6)
    ∧ memberchar.convCount wD3 (thFamOf (sertables.tableD 3) 6)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableD 3))))
          (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3)))) true
      = letterFold (sertables.tableD 3) [1] 3 (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3)) (thFamOf (sertables.tableD 3) 6) :=
  rowValues_D 3 fundD3 wD3 wD3wits
    (thFamOf (sertables.tableD 3) 6) (memberV [1] 3) (memberRho [1] 3)
    (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    d3Fund d3Gram d3GramSym
    d3Refl d3Simple d3RhoDot d3RhoLen
    d3Shape d3Close d3Dom d3Top d3Sq
    d3MShape d3Fam (by decide +kernel) (by decide +kernel)

/-! The dominance binder is load-bearing: at `B_3`'s word `[1]` a
balance partner joins the member at a negative coroot pair, and both
counts leave the theorem's values. -/

example : ¬ (∀ k, k < 3 → ground.BPair.unit ≤ ground.getAt
    ground.BPair.unit (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (poly.neg
        (sertables.posCorootV (sertables.tableB 3) 5))))) k) := by
  decide +kernel
example : 0 < ground.countOf (poly.pnorm (poly.neg
    (sertables.posCorootV (sertables.tableB 3) 5)))
    (thFamOf (sertables.tableB 3) 9) := by decide +kernel

example : ¬ (memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (poly.pnorm (poly.neg (sertables.posCorootV (sertables.tableB 3) 5))))) false
      = ground.countOf (poly.pnorm (poly.neg (sertables.posCorootV (sertables.tableB 3) 5))) (thFamOf (sertables.tableB 3) 9)
    ∧ memberchar.convCount wB3 (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (poly.pnorm (poly.neg (sertables.posCorootV (sertables.tableB 3) 5))))) true
      = letterFold (sertables.tableB 3) [1] 3 (poly.pnorm (poly.neg (sertables.posCorootV (sertables.tableB 3) 5))) (thFamOf (sertables.tableB 3) 9)) := by
  decide +kernel


/-! The reach clearance and the descent are the statement's frame,
not refusal boundaries: below the clearance at `D_2` and at `B_3`,
and against the descent at `B_3`'s ascending word, the reads stand
and the two counts keep the theorem's values. -/

example : ¬ (List.length [1] + 2 ≤ 2) := by decide +kernel

example : sertables.wShapeRead (sertables.tableD 2) wD2 := by decide +kernel
example : assembly.wCloseRead (sertables.tableD 2) wD2 := by decide +kernel
example : assembly.wTopAt wD2
    (poly.pnorm (elim.vecAdd (memberV [1] 2)
      (sertables.rhoV (sertables.tableD 2)))) := by decide +kernel
example : assembly.wDomAt (sertables.tableD 2) wD2 wD2wits
    (poly.pnorm (elim.vecAdd (memberV [1] 2)
      (sertables.rhoV (sertables.tableD 2)))) := by decide +kernel
example : row.sqAtRead fundD2 wD2
    (poly.pnorm (elim.vecAdd (memberV [1] 2)
      (sertables.rhoV (sertables.tableD 2)))) := by decide +kernel
example : ∀ z ∈ (thFamOf (sertables.tableD 2) 2), sertables.dotB fundD2 z z
    ≤ ground.BPair.ofNat (4 * (fundD2).scale) := by decide +kernel

example : memberchar.convCount wD2 (thFamOf (sertables.tableD 2) 2)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 2)
            (sertables.rhoV (sertables.tableD 2))))
          (List.replicate 2 ground.BPair.unit))) false
      = ground.countOf (List.replicate 2 ground.BPair.unit) (thFamOf (sertables.tableD 2) 2)
    ∧ memberchar.convCount wD2 (thFamOf (sertables.tableD 2) 2)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1] 2)
            (sertables.rhoV (sertables.tableD 2))))
          (List.replicate 2 ground.BPair.unit))) true
      = letterFold (sertables.tableD 2) [1] 2 (List.replicate 2 ground.BPair.unit) (thFamOf (sertables.tableD 2) 2) := by
  decide +kernel


example : ¬ (List.length [1, 1] + 2 ≤ 3) := by decide +kernel

example : sertables.wShapeRead (sertables.tableB 3) wB3c := by decide +kernel
example : assembly.wCloseRead (sertables.tableB 3) wB3c := by decide +kernel
example : assembly.wTopAt wB3c
    (poly.pnorm (elim.vecAdd (memberV [1, 1] 3)
      (sertables.rhoV (sertables.tableB 3)))) := by decide +kernel
example : assembly.wDomAt (sertables.tableB 3) wB3c wB3cwits
    (poly.pnorm (elim.vecAdd (memberV [1, 1] 3)
      (sertables.rhoV (sertables.tableB 3)))) := by decide +kernel
example : row.sqAtRead fundB3 wB3c
    (poly.pnorm (elim.vecAdd (memberV [1, 1] 3)
      (sertables.rhoV (sertables.tableB 3)))) := by decide +kernel
example : ∀ z ∈ (thFamOf (sertables.tableB 3) 9), sertables.dotB fundB3 z z
    ≤ ground.BPair.ofNat (4 * (fundB3).scale) := by decide +kernel

example : memberchar.convCount wB3c (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1, 1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (List.replicate 3 ground.BPair.unit))) false
      = ground.countOf (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableB 3) 9)
    ∧ memberchar.convCount wB3c (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1, 1] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (List.replicate 3 ground.BPair.unit))) true
      = letterFold (sertables.tableB 3) [1, 1] 3 (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableB 3) 9) := by
  decide +kernel


example : ¬ (∀ i, i + 1 < List.length [1, 2] →
    ground.getAt 0 [1, 2] (i + 1) ≤ ground.getAt 0 [1, 2] i) := by
  decide +kernel

example : sertables.wShapeRead (sertables.tableB 3) wB3s := by decide +kernel
example : assembly.wCloseRead (sertables.tableB 3) wB3s := by decide +kernel
example : assembly.wTopAt wB3s
    (poly.pnorm (elim.vecAdd (memberV [1, 2] 3)
      (sertables.rhoV (sertables.tableB 3)))) := by decide +kernel
example : assembly.wDomAt (sertables.tableB 3) wB3s wB3swits
    (poly.pnorm (elim.vecAdd (memberV [1, 2] 3)
      (sertables.rhoV (sertables.tableB 3)))) := by decide +kernel
example : row.sqAtRead fundB3 wB3s
    (poly.pnorm (elim.vecAdd (memberV [1, 2] 3)
      (sertables.rhoV (sertables.tableB 3)))) := by decide +kernel
example : ∀ z ∈ (thFamOf (sertables.tableB 3) 9), sertables.dotB fundB3 z z
    ≤ ground.BPair.ofNat (4 * (fundB3).scale) := by decide +kernel

example : memberchar.convCount wB3s (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1, 2] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (List.replicate 3 ground.BPair.unit))) false
      = ground.countOf (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableB 3) 9)
    ∧ memberchar.convCount wB3s (thFamOf (sertables.tableB 3) 9)
        (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd (memberV [1, 2] 3)
            (sertables.rhoV (sertables.tableB 3))))
          (List.replicate 3 ground.BPair.unit))) true
      = letterFold (sertables.tableB 3) [1, 2] 3 (List.replicate 3 ground.BPair.unit) (thFamOf (sertables.tableB 3) 9) := by
  decide +kernel

/-! ## The polynomial tier: the rank's own coefficient reads

`lem:serstable`(i) states the Casimir and the dimension as single
polynomial pairs in the rank.  The Casimir's numerator polynomial
is decided at its value against the displayed numerator and routed
through the evaluation bridge beside it; the clearance
`a ≤ ℓ` is load-bearing, the below-clearance rank's truncated key
reads parting from the polynomial's own at every series.  The
dimension pair's cross-multiplied read is decided at the same words
and routed through its bridge, at the vacant word and at a longer
one beside them. -/

example : (poly.eval (casPolyB [2, 1]) (ground.BPair.ofNat 4)).oneValue
    (ground.BPair.ofNat (casNumB [2, 1] 4)) := by decide +kernel
example : (poly.eval (casPolyB [2, 1]) (ground.BPair.ofNat 4)).oneValue
    (ground.BPair.ofNat (casNumB [2, 1] 4)) :=
  casPolyB_eval [2, 1] 4 (by decide +kernel)

example : (poly.eval (casPolyC [2, 1]) (ground.BPair.ofNat 4)).oneValue
    (ground.BPair.ofNat (casNumC [2, 1] 4)) := by decide +kernel
example : (poly.eval (casPolyC [2, 1]) (ground.BPair.ofNat 4)).oneValue
    (ground.BPair.ofNat (casNumC [2, 1] 4)) :=
  casPolyC_eval [2, 1] 4 (by decide +kernel)

example : (poly.eval (casPolyD [2, 1]) (ground.BPair.ofNat 5)).oneValue
    (ground.BPair.ofNat (casNumD [2, 1] 5)) := by decide +kernel
example : (poly.eval (casPolyD [2, 1]) (ground.BPair.ofNat 5)).oneValue
    (ground.BPair.ofNat (casNumD [2, 1] 5)) :=
  casPolyD_eval [2, 1] 5 (by decide +kernel)

/-! The theorems at the vacant word, at a longer word, and at the
clearance's own boundary, where the rank reads the word's length. -/

example : (poly.eval (casPolyB []) (ground.BPair.ofNat 4)).oneValue
    (ground.BPair.ofNat (casNumB [] 4)) :=
  casPolyB_eval [] 4 (by decide +kernel)
example : (poly.eval (casPolyD [5, 3, 3, 1, 1])
      (ground.BPair.ofNat 7)).oneValue
    (ground.BPair.ofNat (casNumD [5, 3, 3, 1, 1] 7)) :=
  casPolyD_eval [5, 3, 3, 1, 1] 7 (by decide +kernel)
example : (poly.eval (casPolyB [2, 1]) (ground.BPair.ofNat 2)).oneValue
    (ground.BPair.ofNat (casNumB [2, 1] 2)) :=
  casPolyB_eval [2, 1] 2 (by decide +kernel)

/-! The clearance is load-bearing: one rank below the word's own
length the truncated key reads part from the polynomial's value at
every series. -/

example : ¬ (poly.eval (casPolyB [1, 1])
    (ground.BPair.ofNat 1)).oneValue
      (ground.BPair.ofNat (casNumB [1, 1] 1)) := by decide +kernel
example : ¬ (poly.eval (casPolyC [1, 1])
    (ground.BPair.ofNat 0)).oneValue
      (ground.BPair.ofNat (casNumC [1, 1] 0)) := by decide +kernel
example : ¬ (poly.eval (casPolyD [1, 1])
    (ground.BPair.ofNat 1)).oneValue
      (ground.BPair.ofNat (casNumD [1, 1] 1)) := by decide +kernel

/-! The dimension pair's cross-multiplied read at the committed
words, decided and through the theorem. -/

example : (poly.eval (dimPolyNumB [2, 1]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimDenB [2, 1] 4)).oneValue
  (poly.eval (dimPolyDenB [2, 1]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimNumB [2, 1] 4)) := by decide +kernel
example : (poly.eval (dimPolyNumB [2, 1]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimDenB [2, 1] 4)).oneValue
  (poly.eval (dimPolyDenB [2, 1]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimNumB [2, 1] 4)) :=
  dimPolyB_eval [2, 1] 4 (by decide +kernel) (by decide +kernel)

example : (poly.eval (dimPolyNumC [2, 1]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimDenC [2, 1] 4)).oneValue
  (poly.eval (dimPolyDenC [2, 1]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimNumC [2, 1] 4)) := by decide +kernel
example : (poly.eval (dimPolyNumC [2, 1]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimDenC [2, 1] 4)).oneValue
  (poly.eval (dimPolyDenC [2, 1]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimNumC [2, 1] 4)) :=
  dimPolyC_eval [2, 1] 4 (by decide +kernel) (by decide +kernel)

example : (poly.eval (dimPolyNumD [2, 1]) (ground.BPair.ofNat 5)
    * ground.BPair.ofNat (dimDenD [2, 1] 5)).oneValue
  (poly.eval (dimPolyDenD [2, 1]) (ground.BPair.ofNat 5)
    * ground.BPair.ofNat (dimNumD [2, 1] 5)) := by decide +kernel
example : (poly.eval (dimPolyNumD [2, 1]) (ground.BPair.ofNat 5)
    * ground.BPair.ofNat (dimDenD [2, 1] 5)).oneValue
  (poly.eval (dimPolyDenD [2, 1]) (ground.BPair.ofNat 5)
    * ground.BPair.ofNat (dimNumD [2, 1] 5)) :=
  dimPolyD_eval [2, 1] 5 (by decide +kernel) (by decide +kernel)

/-! The dimension bridge at the vacant word and at a longer one. -/

example : (poly.eval (dimPolyNumB []) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimDenB [] 4)).oneValue
  (poly.eval (dimPolyDenB []) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimNumB [] 4)) :=
  dimPolyB_eval [] 4 (by decide +kernel) (by decide +kernel)
example : (poly.eval (dimPolyNumD [2, 2, 1]) (ground.BPair.ofNat 6)
    * ground.BPair.ofNat (dimDenD [2, 2, 1] 6)).oneValue
  (poly.eval (dimPolyDenD [2, 2, 1]) (ground.BPair.ofNat 6)
    * ground.BPair.ofNat (dimNumD [2, 2, 1] 6)) :=
  dimPolyD_eval [2, 2, 1] 6 (by decide +kernel) (by decide +kernel)

/-! The dimension bridge's two binders are the leading family's own
frame rather than refusal boundaries: the cross-multiplied read
stands at an ascending word, where the difference factors truncate
on both sides alike, and at the rank reading the word's own length,
where the tail telescopes are vacant on both sides. -/

example : (poly.eval (dimPolyNumB [1, 2]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimDenB [1, 2] 4)).oneValue
  (poly.eval (dimPolyDenB [1, 2]) (ground.BPair.ofNat 4)
    * ground.BPair.ofNat (dimNumB [1, 2] 4)) := by decide +kernel
example : (poly.eval (dimPolyNumB [2, 1]) (ground.BPair.ofNat 2)
    * ground.BPair.ofNat (dimDenB [2, 1] 2)).oneValue
  (poly.eval (dimPolyDenB [2, 1]) (ground.BPair.ofNat 2)
    * ground.BPair.ofNat (dimNumB [2, 1] 2)) := by decide +kernel

/-! ## The diagonal display

`lem:serstable`(ii)'s diagonal: at the member's own display the
channel count joins the word's vacant-key count to the rank.  The
vacant word carries the Kronecker defect — the vacant channel list
against the member's two vacant keys at `B_2` — and the word `[1]`
carries the occupied diagonal at each series, its single channel
against the two remaining vacant keys.  Each read is decided at its
data and routed through the theorem beside it. -/

example : ground.countOf (poly.pnorm (elim.vecScale
      (ground.BPair.ofNat 1) (memberV [] 2))) []
    + ground.countOf 0 (member [] 2) = 2 := by decide +kernel
example : ground.countOf (poly.pnorm (elim.vecScale
      (ground.BPair.ofNat 1) (memberV [] 2))) []
    + ground.countOf 0 (member [] 2) = 2 :=
  diagRead_B [] 2 sertables.fundB2 wB2v wB2vwits
    (thFamOf (sertables.tableB 2) 4) []
    (by decide +kernel) (by decide +kernel) b2Fund b2Gram b2GramSym
    b2Refl b2Simple b2RhoDot b2RhoLen
    b2Shape b2Close b2Dom b2Top b2Sq
    b2MShape b2Fam (by decide +kernel) (by decide +kernel)

example : ground.countOf (poly.pnorm (elim.vecScale
      (ground.BPair.ofNat 1) (memberV [1] 3)))
      [poly.pnorm (elim.vecScale (ground.BPair.ofNat 1) (memberV [1] 3))]
    + ground.countOf 0 (member [1] 3) = 3 := by decide +kernel
example : ground.countOf (poly.pnorm (elim.vecScale
      (ground.BPair.ofNat 1) (memberV [1] 3)))
      [poly.pnorm (elim.vecScale (ground.BPair.ofNat 1) (memberV [1] 3))]
    + ground.countOf 0 (member [1] 3) = 3 :=
  diagRead_B [1] 3 fundB3 wB3 wB3wits (thFamOf (sertables.tableB 3) 9)
    [poly.pnorm (elim.vecScale (ground.BPair.ofNat 1) (memberV [1] 3))]
    (by decide +kernel) (by decide +kernel) b3Fund b3Gram b3GramSym
    b3Refl b3Simple b3RhoDot b3RhoLen
    b3Shape b3Close b3Dom b3Top b3Sq
    b3MShape b3Fam (by decide +kernel) (by decide +kernel)

example : ground.countOf (poly.pnorm (elim.vecScale
      (ground.BPair.ofNat 1) (memberV [1] 3)))
      [poly.pnorm (elim.vecScale (ground.BPair.ofNat 1) (memberV [1] 3))]
    + ground.countOf 0 (member [1] 3) = 3 :=
  diagRead_C [1] 3 fundC3 wC3 wC3wits (thFamOf (sertables.tableC 3) 9)
    [poly.pnorm (elim.vecScale (ground.BPair.ofNat 1) (memberV [1] 3))]
    (by decide +kernel) (by decide +kernel) c3Fund c3Gram c3GramSym
    c3Refl c3Simple c3RhoDot c3RhoLen
    c3Shape c3Close c3Dom c3Top c3Sq
    c3MShape c3Fam (by decide +kernel) (by decide +kernel)

example : ground.countOf (poly.pnorm (elim.vecScale
      (ground.BPair.ofNat 1) (memberV [1] 3)))
      [poly.pnorm (elim.vecScale (ground.BPair.ofNat 1) (memberV [1] 3))]
    + ground.countOf 0 (member [1] 3) = 3 :=
  diagRead_D [1] 3 fundD3 wD3 wD3wits (thFamOf (sertables.tableD 3) 6)
    [poly.pnorm (elim.vecScale (ground.BPair.ofNat 1) (memberV [1] 3))]
    (by decide +kernel) (by decide +kernel) d3Fund d3Gram d3GramSym
    d3Refl d3Simple d3RhoDot d3RhoLen
    d3Shape d3Close d3Dom d3Top d3Sq
    d3MShape d3Fam (by decide +kernel) (by decide +kernel)


/-! `lem:serstable`(ii)'s off-diagonal at-most-one read: each
series' route at an occupied dominant target — `B_3`'s ties evening
at their pairing with the count vacant, `C_3`'s identity tie alone
at count one, and `D_3`'s last-pair boundary member at the reach
clearance's least rank, its count one. -/

example : steinberg.memberAt (sertables.tableB 3) wB3
    (thFamOf (sertables.tableB 3) 9) []
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6)))) := by
  decide +kernel

example : ground.countOf
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6))))
    ([] : List (List ground.BPair)) ≤ 1 :=
  rowOffOne_B [1] 3 fundB3 wB3 wB3wits
    (thFamOf (sertables.tableB 3) 9) []
    (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 6))
    (by decide +kernel) (by decide +kernel) b3Fund b3Gram b3GramSym
    b3Refl b3Simple b3RhoDot b3RhoLen
    b3Shape b3Close b3Dom b3Top b3Sq
    b3MShape b3Fam (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : ground.countOf
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3))))
    [poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)))]
    = 1 := by decide +kernel

example : steinberg.memberAt (sertables.tableC 3) wC3
    (thFamOf (sertables.tableC 3) 9)
    [poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)))]
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)))) := by
  decide +kernel

example : ground.countOf
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3))))
    [poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)))]
    ≤ 1 :=
  rowOffOne_C [1] 3 fundC3 wC3 wC3wits
    (thFamOf (sertables.tableC 3) 9)
    [poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3)))]
    (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 3))
    (by decide +kernel) (by decide +kernel) c3Fund c3Gram c3GramSym
    c3Refl c3Simple c3RhoDot c3RhoLen
    c3Shape c3Close c3Dom c3Top c3Sq
    c3MShape c3Fam (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : steinberg.memberAt (sertables.tableD 3) wD3
    (thFamOf (sertables.tableD 3) 6)
    [poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 2)))]
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 2)))) := by
  decide +kernel

example : ground.countOf
    (poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 2))))
    [poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 2)))]
    ≤ 1 :=
  rowOffOne_D [1] 3 fundD3 wD3 wD3wits
    (thFamOf (sertables.tableD 3) 6)
    [poly.pnorm (elim.vecAdd (memberV [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 2)))]
    (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 2))
    (by decide +kernel) (by decide +kernel) d3Fund d3Gram d3GramSym
    d3Refl d3Simple d3RhoDot d3RhoLen
    d3Shape d3Close d3Dom d3Top d3Sq
    d3MShape d3Fam (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The `D` boundary member at the rank beyond the least: the
last-pair difference member's target loses its dominance, the moved
key's balance partner against the vacant member entry. -/
example : ¬ (∀ k, k < 4 → ground.BPair.unit ≤ ground.getAt
    ground.BPair.unit (poly.pnorm (elim.vecAdd (memberV [1] 4)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 4) 5)))) k) := by
  decide +kernel

/-! `lem:serstable`(ii)'s target confinement: each series' route at
the highest root's coroot content over the vacant word, the entry at
the word's two-clearance vacant — `D_4` at both the interior key and
the fork's last key, the four-clearance met. -/

example : ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd (memberV [] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 3)))) 2
    = ground.BPair.unit :=
  rowConfined_B [] 3 (thFamOf (sertables.tableB 3) 9)
    (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 3)) 2
    b3MShape b3Fam (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd (memberV [] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 6)))) 2
    = ground.BPair.unit :=
  rowConfined_C [] 3 (thFamOf (sertables.tableC 3) 9)
    (poly.pnorm (sertables.posCorootV (sertables.tableC 3) 6)) 2
    c3MShape c3Fam (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd (memberV [] 4)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 4) 6)))) 2
    = ground.BPair.unit :=
  rowConfined_D [] 4 (thFamOf (sertables.tableD 4) 12)
    (poly.pnorm (sertables.posCorootV (sertables.tableD 4) 6)) 2
    d4MShape d4Fam (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd (memberV [] 4)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 4) 6)))) 3
    = ground.BPair.unit :=
  rowConfined_D [] 4 (thFamOf (sertables.tableD 4) 12)
    (poly.pnorm (sertables.posCorootV (sertables.tableD 4) 6)) 3
    d4MShape d4Fam (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! The confinement's binders, isolated at committed refusals: the
dominance binder at an occupied non-dominant target whose beyond-key
entry survives, the occupancy binder at a content off the family,
and `D`'s four-clearance guard at the sum pair whose coroot content
occupies the fork key at the three-clearance rank — the last key's
own read at the boundary-adjacent geometry. -/

example : ¬ (∀ k, k < 3 → ground.BPair.unit ≤ ground.getAt
    ground.BPair.unit (poly.pnorm (elim.vecAdd (memberV [] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 8)))) k) := by
  decide +kernel
example : 0 < ground.countOf
    (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 8))
    (thFamOf (sertables.tableB 3) 9) := by decide +kernel
example : ¬ (ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd (memberV [] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 8)))) 2
    = ground.BPair.unit) := by decide +kernel

example : ground.countOf
    ([ground.BPair.unit, ground.BPair.unit, ground.BPair.ofNat 2])
    (thFamOf (sertables.tableB 3) 9) = 0 := by decide +kernel
example : ∀ k, k < 3 → ground.BPair.unit ≤ ground.getAt
    ground.BPair.unit (poly.pnorm (elim.vecAdd (memberV [] 3)
      [ground.BPair.unit, ground.BPair.unit, ground.BPair.ofNat 2]))
    k := by decide +kernel
example : ¬ (ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd (memberV [] 3)
      [ground.BPair.unit, ground.BPair.unit, ground.BPair.ofNat 2]))
    2 = ground.BPair.unit) := by decide +kernel

example : 0 < ground.countOf
    (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3))
    (thFamOf (sertables.tableD 3) 6) := by decide +kernel
example : ∀ k, k < 3 → ground.BPair.unit ≤ ground.getAt
    ground.BPair.unit (poly.pnorm (elim.vecAdd (memberV [] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3))))
    k := by decide +kernel
example : ¬ (ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd (memberV [] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableD 3) 3)))) 2
    = ground.BPair.unit) := by decide +kernel

/-! ## The alignment tier's committed surface

The family entry functions, the neighbour folds, the Cartan
entries, the column caps and window reads, the coroot vector
entries at both limbs, the raised entry, the run letters and the
letter fold: each public pinned at a decided instance beside its
theorem route, with the load-bearing binders' refusals.  The
column caps' family binder is load-bearing (the constant-three
family breaks the cap at the leading key); the run letters'
own-key vacancy and witness occupancy are load-bearing at both
members (a raised family column reads count one), and the `C`
witness's off-window binder is load-bearing at the two-key dipole
inside the window. -/

example : serstable.fDiff 1 3 0 = 0 ∧ serstable.fDiff 1 3 1 = 1
    ∧ serstable.fDiff 1 3 2 = 1 ∧ serstable.fDiff 1 3 3 = 0 := by
  decide +kernel
example : serstable.fSumB 4 1 2 0 = 0 ∧ serstable.fSumB 4 1 2 1 = 1
    ∧ serstable.fSumB 4 1 2 2 = 2 ∧ serstable.fSumB 4 1 2 3 = 2 := by
  decide +kernel
example : serstable.fSumC 3 1 2 0 = 0 ∧ serstable.fSumC 3 1 2 1 = 1
    ∧ serstable.fSumC 3 1 2 2 = 2 ∧ serstable.fSumC 3 1 2 3 = 1 := by
  decide +kernel
example : serstable.fLong 3 1 0 = 0 ∧ serstable.fLong 3 1 1 = 2
    ∧ serstable.fLong 3 1 2 = 2 ∧ serstable.fLong 3 1 3 = 1 := by
  decide +kernel

example : serstable.nbB 4 (serstable.fSumB 4 1 2) 0 = 1
    ∧ serstable.nbB 4 (serstable.fSumB 4 1 2) 1 = 2
    ∧ serstable.nbB 4 (serstable.fSumB 4 1 2) 2 = 3
    ∧ serstable.nbB 4 (serstable.fSumB 4 1 2) 3 = 4 := by decide +kernel
example : serstable.nbC 4 (serstable.fLong 3 1) 0 = 2
    ∧ serstable.nbC 4 (serstable.fLong 3 1) 1 = 2
    ∧ serstable.nbC 4 (serstable.fLong 3 1) 2 = 4
    ∧ serstable.nbC 4 (serstable.fLong 3 1) 3 = 2 := by decide +kernel

example : (serstable.cartB 4 2 3).oneValue (ground.BPair.ofCounts 0 2)
    ∧ (serstable.cartB 4 1 2).oneValue (ground.BPair.ofCounts 0 1)
    ∧ (serstable.cartB 4 2 1).oneValue (ground.BPair.ofCounts 0 1)
    ∧ (serstable.cartB 4 3 3).oneValue (ground.BPair.ofCounts 2 0)
    ∧ (serstable.cartB 4 0 2).oneValue ground.BPair.unit := by
  decide +kernel
example : (serstable.cartC 4 3 2).oneValue (ground.BPair.ofCounts 0 2)
    ∧ (serstable.cartC 4 2 3).oneValue (ground.BPair.ofCounts 0 1)
    ∧ (serstable.cartC 4 1 1).oneValue (ground.BPair.ofCounts 2 0)
    ∧ (serstable.cartC 4 0 3).oneValue ground.BPair.unit := by
  decide +kernel

/-! The enumeration order of the positive-list builders: the
leading entries of the fold lists at the rank four. -/

example : ground.getAt [] (sertables.foldsB 4) 0
    = (List.range 4).map (serstable.fDiff 0 1) := by decide +kernel
example : ground.getAt [] (sertables.foldsC 4) 0
    = (List.range 4).map (serstable.fDiff 0 1) := by decide +kernel

/-! The column caps at an instance, with the family binder's
refusal at the constant-three family. -/

example : 2 * serstable.fSumB 4 1 2 2
      ≤ serstable.nbB 4 (serstable.fSumB 4 1 2) 2 + 2
    ∧ serstable.nbB 4 (serstable.fSumB 4 1 2) 2
      ≤ 2 * serstable.fSumB 4 1 2 2 + 2 := by decide +kernel
example : 2 * serstable.fSumB 4 1 2 2
      ≤ serstable.nbB 4 (serstable.fSumB 4 1 2) 2 + 2
    ∧ serstable.nbB 4 (serstable.fSumB 4 1 2) 2
      ≤ 2 * serstable.fSumB 4 1 2 2 + 2 :=
  serstable.colB_magLe (serstable.fSumB 4 1 2) 2 4 (by decide +kernel)
    (Or.inr (Or.inl ⟨1, 2, by decide +kernel, by decide +kernel, rfl⟩))
example : ¬ (2 * (3 : Nat) ≤ serstable.nbB 3 (fun _ => 3) 0 + 2) := by
  decide +kernel

example : 2 * serstable.fLong 3 1 1
      ≤ serstable.nbC 4 (serstable.fLong 3 1) 1 + 2
    ∧ serstable.nbC 4 (serstable.fLong 3 1) 1
      ≤ 2 * serstable.fLong 3 1 1 + 2 := by decide +kernel
example : 2 * serstable.fLong 3 1 1
      ≤ serstable.nbC 4 (serstable.fLong 3 1) 1 + 2
    ∧ serstable.nbC 4 (serstable.fLong 3 1) 1
      ≤ 2 * serstable.fLong 3 1 1 + 2 :=
  serstable.colC_magLe (serstable.fLong 3 1) 1 4 (by decide +kernel)
    (Or.inr (Or.inr ⟨3, 1, rfl, by decide +kernel, rfl⟩))
example : ¬ (2 * (3 : Nat) ≤ serstable.nbC 3 (fun _ => 3) 0 + 2) := by
  decide +kernel

/-! The window reads at instances, each beside its theorem
route. -/

example : (2 * serstable.fDiff 2 3 2
      = serstable.fDiff 2 3 1 + serstable.fDiff 2 3 3 + 2)
    ↔ (2 = 2 ∧ 3 = 3) := by decide +kernel
example : (2 * serstable.fDiff 2 3 2
      = serstable.fDiff 2 3 1 + serstable.fDiff 2 3 3 + 2)
    ↔ (2 = 2 ∧ 3 = 3) :=
  serstable.fDiff_two 2 3 1 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : ¬ 2 * serstable.fSumB 4 1 2 2
    = serstable.fSumB 4 1 2 1 + serstable.fSumB 4 1 2 3 + 2 := by
  decide +kernel
example : ¬ 2 * serstable.fSumB 4 1 2 2
    = serstable.fSumB 4 1 2 1 + serstable.fSumB 4 1 2 3 + 2 :=
  serstable.fSumB_two 1 2 1 4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : ¬ 2 * serstable.fDiff 1 4 2
    = serstable.fDiff 1 4 1 + serstable.fDiff 1 4 3 + 2 := by
  decide +kernel
example : ¬ 2 * serstable.fDiff 1 4 2
    = serstable.fDiff 1 4 1 + serstable.fDiff 1 4 3 + 2 :=
  serstable.fShort_two 1 1 4 (by decide +kernel) (by decide +kernel)

example : ¬ serstable.fSumB 4 1 2 1 + serstable.fSumB 4 1 2 3
    = 2 * serstable.fSumB 4 1 2 2 + 2 := by decide +kernel
example : ¬ serstable.fSumB 4 1 2 1 + serstable.fSumB 4 1 2 3
    = 2 * serstable.fSumB 4 1 2 2 + 2 :=
  serstable.colB_notNegTwo (serstable.fSumB 4 1 2) 1 4
    (by decide +kernel)
    (Or.inr (Or.inl ⟨1, 2, by decide +kernel, by decide +kernel, rfl⟩))

example : ¬ serstable.fDiff 1 3 0 + serstable.fDiff 1 3 2
    = 2 * serstable.fDiff 1 3 1 + 2 := by decide +kernel
example : ¬ serstable.fDiff 1 3 0 + serstable.fDiff 1 3 2
    = 2 * serstable.fDiff 1 3 1 + 2 :=
  serstable.fDiff_negTwo_refuse 1 3 0 (by decide +kernel)

example : 2 * serstable.fDiff 2 3 0
    = serstable.nbB 4 (serstable.fDiff 2 3) 0 := by decide +kernel
example : 2 * serstable.fDiff 2 3 0
    = serstable.nbB 4 (serstable.fDiff 2 3) 0 :=
  serstable.fDiff_narrow_off 1 4 0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : 2 * serstable.fDiff 1 3 4
    = serstable.nbB 5 (serstable.fDiff 1 3) 4 := by decide +kernel
example : 2 * serstable.fDiff 1 3 4
    = serstable.nbB 5 (serstable.fDiff 1 3) 4 :=
  serstable.fDiff_off 1 3 4 5 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : 2 * serstable.fSumB 5 1 3 4
    = serstable.nbB 5 (serstable.fSumB 5 1 3) 4 := by decide +kernel
example : 2 * serstable.fSumB 5 1 3 4
    = serstable.nbB 5 (serstable.fSumB 5 1 3) 4 :=
  serstable.fSumB_off 1 3 4 5 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : ¬ 2 * serstable.fSumC 3 1 2 1
    = serstable.fSumC 3 1 2 0 + serstable.fSumC 3 1 2 2 + 2 := by
  decide +kernel
example : ¬ 2 * serstable.fSumC 3 1 2 1
    = serstable.fSumC 3 1 2 0 + serstable.fSumC 3 1 2 2 + 2 :=
  serstable.fSumC_two_refuse 3 1 2 0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : ¬ serstable.fSumC 3 1 2 0 + serstable.fSumC 3 1 2 2
    = 2 * serstable.fSumC 3 1 2 1 + 2 := by decide +kernel
example : ¬ serstable.fSumC 3 1 2 0 + serstable.fSumC 3 1 2 2
    = 2 * serstable.fSumC 3 1 2 1 + 2 :=
  serstable.fSumC_negTwo_refuse 3 1 2 0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : (2 * serstable.fLong 3 1 1
      = serstable.fLong 3 1 0 + serstable.fLong 3 1 2 + 2)
    ↔ (1 = 1 ∧ 2 < 3) := by decide +kernel
example : (2 * serstable.fLong 3 1 1
      = serstable.fLong 3 1 0 + serstable.fLong 3 1 2 + 2)
    ↔ (1 = 1 ∧ 2 < 3) :=
  serstable.fLong_two_head 3 1 0 (by decide +kernel)
    (by decide +kernel)

example : (serstable.fLong 3 2 0 + serstable.fLong 3 2 2
      = 2 * serstable.fLong 3 2 1 + 2)
    ↔ (2 = 2 ∧ 2 < 3) := by decide +kernel
example : (serstable.fLong 3 2 0 + serstable.fLong 3 2 2
      = 2 * serstable.fLong 3 2 1 + 2)
    ↔ (2 = 2 ∧ 2 < 3) :=
  serstable.fLong_negTwo 3 2 0 (by decide +kernel) (by decide +kernel)

example : 2 * serstable.fDiff 1 2 3
    = serstable.nbC 4 (serstable.fDiff 1 2) 3 := by decide +kernel
example : 2 * serstable.fDiff 1 2 3
    = serstable.nbC 4 (serstable.fDiff 1 2) 3 :=
  serstable.fDiffC_narrow_off 0 4 3 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

example : 2 * serstable.fLong 3 1 3
    = serstable.nbC 4 (serstable.fLong 3 1) 3 := by decide +kernel
example : 2 * serstable.fLong 3 1 3
    = serstable.nbC 4 (serstable.fLong 3 1) 3 :=
  serstable.fLong_off 3 1 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

example : 2 * serstable.fSumC 3 1 2 3
    = serstable.nbC 4 (serstable.fSumC 3 1 2) 3 := by decide +kernel
example : 2 * serstable.fSumC 3 1 2 3
    = serstable.nbC 4 (serstable.fSumC 3 1 2) 3 :=
  serstable.fSumC_off 3 1 2 3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! The coroot vector entries at both limbs, and the raised
entry. -/

example : (ground.getAt ground.BPair.unit
    (poly.pnorm (sertables.posCorootV (sertables.tableB 4) 0)) 1).oneValue
    (ground.BPair.ofCounts (2 * serstable.fDiff 0 1 1)
      (serstable.nbB 4 (serstable.fDiff 0 1) 1)) := by decide +kernel
example : (ground.getAt ground.BPair.unit
    (poly.pnorm (sertables.posCorootV (sertables.tableB 4) 0)) 1).oneValue
    (ground.BPair.ofCounts (2 * serstable.fDiff 0 1 1)
      (serstable.nbB 4 (serstable.fDiff 0 1) 1)) :=
  serstable.posCorootV_entry 4 0 1 (serstable.fDiff 0 1)
    (by decide +kernel) (by decide +kernel)

example : (ground.getAt ground.BPair.unit
    (poly.pnorm (poly.neg
      (sertables.posCorootV (sertables.tableB 4) 0))) 1).oneValue
    (ground.BPair.ofCounts (serstable.nbB 4 (serstable.fDiff 0 1) 1)
      (2 * serstable.fDiff 0 1 1)) := by decide +kernel
example : (ground.getAt ground.BPair.unit
    (poly.pnorm (poly.neg
      (sertables.posCorootV (sertables.tableB 4) 0))) 1).oneValue
    (ground.BPair.ofCounts (serstable.nbB 4 (serstable.fDiff 0 1) 1)
      (2 * serstable.fDiff 0 1 1)) :=
  serstable.negCorootV_entry 4 0 1 (serstable.fDiff 0 1)
    (by decide +kernel) (by decide +kernel)

example : (ground.getAt ground.BPair.unit
    (poly.pnorm (sertables.posCorootV (sertables.tableC 4) 0)) 1).oneValue
    (ground.BPair.ofCounts (2 * serstable.fDiff 0 1 1)
      (serstable.nbC 4 (serstable.fDiff 0 1) 1)) := by decide +kernel
example : (ground.getAt ground.BPair.unit
    (poly.pnorm (sertables.posCorootV (sertables.tableC 4) 0)) 1).oneValue
    (ground.BPair.ofCounts (2 * serstable.fDiff 0 1 1)
      (serstable.nbC 4 (serstable.fDiff 0 1) 1)) :=
  serstable.posCorootV_entryC 4 0 1 (serstable.fDiff 0 1)
    (by decide +kernel) (by decide +kernel)

example : (ground.getAt ground.BPair.unit
    (poly.pnorm (poly.neg
      (sertables.posCorootV (sertables.tableC 4) 0))) 1).oneValue
    (ground.BPair.ofCounts (serstable.nbC 4 (serstable.fDiff 0 1) 1)
      (2 * serstable.fDiff 0 1 1)) := by decide +kernel
example : (ground.getAt ground.BPair.unit
    (poly.pnorm (poly.neg
      (sertables.posCorootV (sertables.tableC 4) 0))) 1).oneValue
    (ground.BPair.ofCounts (serstable.nbC 4 (serstable.fDiff 0 1) 1)
      (2 * serstable.fDiff 0 1 1)) :=
  serstable.negCorootV_entryC 4 0 1 (serstable.fDiff 0 1)
    (by decide +kernel) (by decide +kernel)

example : (ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd
      [ground.BPair.ofNat 2, ground.BPair.unit, ground.BPair.unit]
      (elim.vecScale (ground.BPair.ofNat 2)
        (ground.getAt [] (sertables.tableB 3).cartan 1)))) 0).oneValue
    (ground.getAt ground.BPair.unit
        [ground.BPair.ofNat 2, ground.BPair.unit, ground.BPair.unit] 0
      + ground.BPair.ofNat 2 * ground.getAt ground.BPair.unit
          (ground.getAt [] (sertables.tableB 3).cartan 1) 0) := by
  decide +kernel
example : (ground.getAt ground.BPair.unit
    (poly.pnorm (elim.vecAdd
      [ground.BPair.ofNat 2, ground.BPair.unit, ground.BPair.unit]
      (elim.vecScale (ground.BPair.ofNat 2)
        (ground.getAt [] (sertables.tableB 3).cartan 1)))) 0).oneValue
    (ground.getAt ground.BPair.unit
        [ground.BPair.ofNat 2, ground.BPair.unit, ground.BPair.unit] 0
      + ground.BPair.ofNat 2 * ground.getAt ground.BPair.unit
          (ground.getAt [] (sertables.tableB 3).cartan 1) 0) :=
  serstable.raisedAt (sertables.tableB 3) _ (by decide +kernel) 2 1
    (by decide +kernel) 0 (by decide +kernel)

/-! The run letters at an instance each, with the own-key vacancy
and witness occupancy refusals at both members and the off-window
refusal at `C`. -/

example : row.thetaCount (sertables.tableB 4)
    (poly.pnorm (elim.vecAdd
      [ground.BPair.unit, ground.BPair.unit, ground.BPair.unit,
       ground.BPair.ofNat 2]
      (elim.vecScale (ground.BPair.ofNat 1)
        (ground.getAt [] (sertables.tableB 4).cartan 1)))) = 0 := by
  decide +kernel
example : row.thetaCount (sertables.tableB 4)
    (poly.pnorm (elim.vecAdd
      [ground.BPair.unit, ground.BPair.unit, ground.BPair.unit,
       ground.BPair.ofNat 2]
      (elim.vecScale (ground.BPair.ofNat 1)
        (ground.getAt [] (sertables.tableB 4).cartan 1)))) = 0 :=
  serstable.runVanishB 4 0 _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 3 (by decide +kernel)
    (Or.inr (by decide +kernel)) (by decide +kernel)

example : ¬ row.thetaCount (sertables.tableB 5)
    (poly.pnorm (elim.vecAdd
      [ground.BPair.ofNat 2, ground.BPair.ofCounts 0 2,
       ground.BPair.ofNat 1, ground.BPair.ofNat 1,
       ground.BPair.ofCounts 0 2]
      (elim.vecScale (ground.BPair.ofNat 1)
        (ground.getAt [] (sertables.tableB 5).cartan 1)))) = 0 := by
  decide +kernel

example : ¬ row.thetaCount (sertables.tableB 4)
    (poly.pnorm (elim.vecAdd (List.replicate 4 ground.BPair.unit)
      (elim.vecScale (ground.BPair.ofNat 1)
        (ground.getAt [] (sertables.tableB 4).cartan 1)))) = 0 := by
  decide +kernel

example : row.thetaCount (sertables.tableC 5)
    (poly.pnorm (elim.vecAdd
      [ground.BPair.unit, ground.BPair.unit, ground.BPair.unit,
       ground.BPair.ofNat 2, ground.BPair.unit]
      (elim.vecScale (ground.BPair.ofNat 1)
        (ground.getAt [] (sertables.tableC 5).cartan 1)))) = 0 := by
  decide +kernel
example : row.thetaCount (sertables.tableC 5)
    (poly.pnorm (elim.vecAdd
      [ground.BPair.unit, ground.BPair.unit, ground.BPair.unit,
       ground.BPair.ofNat 2, ground.BPair.unit]
      (elim.vecScale (ground.BPair.ofNat 1)
        (ground.getAt [] (sertables.tableC 5).cartan 1)))) = 0 :=
  serstable.runVanishC 5 0 _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) 3 (by decide +kernel)
    (Or.inr (by decide +kernel)) (by decide +kernel)

example : ¬ row.thetaCount (sertables.tableC 5)
    (poly.pnorm (elim.vecAdd
      [ground.BPair.ofNat 1, ground.BPair.ofCounts 0 2,
       ground.BPair.unit, ground.BPair.ofNat 2,
       ground.BPair.ofCounts 0 1]
      (elim.vecScale (ground.BPair.ofNat 1)
        (ground.getAt [] (sertables.tableC 5).cartan 1)))) = 0 := by
  decide +kernel

example : ¬ row.thetaCount (sertables.tableC 4)
    (poly.pnorm (elim.vecAdd
      [ground.BPair.ofCounts 0 1, ground.BPair.unit,
       ground.BPair.ofNat 1, ground.BPair.unit]
      (elim.vecScale (ground.BPair.ofNat 1)
        (ground.getAt [] (sertables.tableC 4).cartan 1)))) = 0 := by
  decide +kernel

example : ¬ row.thetaCount (sertables.tableC 4)
    (poly.pnorm (elim.vecAdd (List.replicate 4 ground.BPair.unit)
      (elim.vecScale (ground.BPair.ofNat 1)
        (ground.getAt [] (sertables.tableC 4).cartan 1)))) = 0 := by
  decide +kernel

/-! The letter fold's bridge: the abstract fold against the value
function at the θ content list, the theorem route beside the
decided twin. -/

example : serstable.letterFoldAt (sertables.tableB 3)
    (serstable.memberRho [1] 3)
    (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 0))
    (thFamOf (sertables.tableB 3) 9)
    = serstable.letterFoldVal (sertables.tableB 3)
      (serstable.memberRho [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 0)) := by
  decide +kernel
example : serstable.letterFoldAt (sertables.tableB 3)
    (serstable.memberRho [1] 3)
    (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 0))
    (thFamOf (sertables.tableB 3) 9)
    = serstable.letterFoldVal (sertables.tableB 3)
      (serstable.memberRho [1] 3)
      (poly.pnorm (sertables.posCorootV (sertables.tableB 3) 0)) :=
  serstable.letterFoldAt_val (sertables.tableB 3) _ _ _ b3Fam
