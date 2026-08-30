import MassGap.Cornerstore

/-! # Checks: the corner disconjugacy certificate's store

The assembled certificate's read at the stated data: the graded
devices and the boundary seed's reads decided by kernel at the
store's data — the derived-object reads at the stored values —
and `certRead`'s twenty-two conjuncts assembled from those reads,
each derived-object conjunct transported along its store tie
(`preTermV_w`, `preSeedV_w`, `postTermV_w`, `postSlopeV_w`).  The
device decides are the module's elaboration weight, the
certificate's kernel verification at its stated data. -/

open ground cornerpivot

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

private theorem dPrePos : gradRead preV preE0n preE0d prePos := by
  decide +kernel

private theorem dPreTerm :
    gradRead preTermV preE0n preE0d preTerm := by decide +kernel

private theorem dPostPos :
    gradRead postSeg.jet preE0n preE0d postSeg.pos := by
  decide +kernel

private theorem dPostTerm :
    gradRead postTermV preE0n preE0d postSeg.term := by
  decide +kernel

private theorem dSlope :
    gradRead postSlopeV preE0n preE0d finSeam.cert := by
  decide +kernel

private theorem sd1 : (depthPoly preV 0).length ≤ seedK + 2 := by
  decide +kernel

private theorem sd2 :
    lowRead (List.drop 1 (depthPoly preV 0)) preE0n preE0d
      seedK := by decide +kernel

private theorem sd3 :
    (depthPoly preSeedV 0).length ≤ seedCK + 2 := by decide +kernel

private theorem sd4 :
    lowRead (List.drop 1 (depthPoly preSeedV 0)) preE0n preE0d
      seedCK := by decide +kernel

private theorem sd5 :
    (depthPoly preTermV 0).length ≤ seedTK + 2 := by decide +kernel

private theorem sd6 :
    lowRead (List.drop 1 (depthPoly preTermV 0)) preE0n preE0d
      seedTK := by decide +kernel

/-- The boundary seed's read, each derived-object arm transported
along its store tie. -/
private theorem cSeed : seedRead preR preQN preQD preE0n preE0d
    preV seedK seedCK seedTK :=
  ⟨sd1, sd2,
   Eq.mpr (congrArg (fun X => (depthPoly X 0).length ≤ seedCK + 2)
     preSeedV_w) sd3,
   Eq.mpr (congrArg (fun X =>
     lowRead (List.drop 1 (depthPoly X 0)) preE0n preE0d seedCK)
     preSeedV_w) sd4,
   Eq.mpr (congrArg (fun X => (depthPoly X 0).length ≤ seedTK + 2)
     preTermV_w) sd5,
   Eq.mpr (congrArg (fun X =>
     lowRead (List.drop 1 (depthPoly X 0)) preE0n preE0d seedTK)
     preTermV_w) sd6⟩

private theorem pd3 : postSeg.pos.lo ≤ postSeg.term.lo := by
  decide +kernel

private theorem pd4 :
    stepClear postSeg.term.hi postSeg.mid preE0n preE0d := by
  decide +kernel

private theorem pd5 :
    stepClear postSeg.mid postSeg.pos.hi preE0n preE0d := by
  decide +kernel

/-- The post segment's read, the termwise arm transported along
its store tie. -/
private theorem cPost : segRead preR preQN preQD preE0n preE0d
    postSeg :=
  ⟨dPostPos,
   Eq.mpr (congrArg (fun X => gradRead X preE0n preE0d postSeg.term)
     postTermV_w) dPostTerm,
   pd3, pd4, pd5⟩

private theorem c1 : 1 ≤ preQD := by decide +kernel
private theorem c2 : 1 ≤ preAlD := by decide +kernel
private theorem c5 : prePos.lo ≤ stage.unitC := by decide +kernel
private theorem c6 : preTerm.lo ≤ stage.unitC := by decide +kernel
private theorem c7 : stepClear preTerm.hi preMid preE0n preE0d := by
  decide +kernel
private theorem c8 : stepClear preMid prePos.hi preE0n preE0d := by
  decide +kernel
private theorem c12 : postSeg.term.lo ≤ posTop preTerm.hi [] := by
  decide +kernel
private theorem c15 : stage.unitC < finSeam.cert.lo := by
  decide +kernel
private theorem c16 : postSeg.term.lo ≤ finSeam.cert.lo := by
  decide +kernel
private theorem c17 :
    stepClear finSeam.cert.lo finB preE0n preE0d := by
  decide +kernel
private theorem c18 : finB ≤ finSeam.cert.hi := by decide +kernel
private theorem c19 : finB ≤ postSeg.term.hi := by decide +kernel
private theorem c20 :
    stage.ofB (BPair.ofNat ((preR + 1) * preQN + preWs))
    ≤ stage.ofB (BPair.ofNat (4 * preQD)) * finSeam.cert.lo := by
  decide +kernel
private theorem c21 :
    stage.ofB (BPair.ofNat (18 * ((preR + 1) * preQD)
      * (preAlN * preAlN))) * finB
    ≤ stage.ofB (BPair.ofNat (preWs * (preAlD * preAlD))) := by
  decide +kernel
private theorem c22 :
    stage.ofB (BPair.ofNat (36 * (preAlN * preAlN)))
    * (finB * (⟨preE0n, preE0d⟩ : CPair))
    ≤ stage.ofB (BPair.ofNat (preAlD * preAlD)) := by
  decide +kernel

example : certRead preR disconjC :=
  ⟨c1, c2, dPrePos,
   Eq.mpr (congrArg (fun X => gradRead X preE0n preE0d preTerm)
     preTermV_w) dPreTerm,
   c5, c6, c7, c8, cSeed, trivial, cPost, c12, trivial,
   Eq.mpr (congrArg (fun X => gradRead X preE0n preE0d finSeam.cert)
     postSlopeV_w) dSlope,
   c15, c16, c17, c18, c19, c20, c21, c22⟩
