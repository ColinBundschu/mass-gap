import MassGap.Certconstruct
/-!
`thm:detector` — the divisor-separation detector: the level-`γ`
requirement's detector pair at a spectral point `λ` is
`(λ² : γλ)`, its site datum the factor read `λ ⟨λ : γ⟩`
(`datum` at the cleared display, `factorRead` the identity), and a
probe's requirement read is the weight fold of the detector data
over the located spectrum (`detFold` at a shared second member,
`passRead` the fold's upper side or equal members).  The side
classification — the kernel point and the edge neutral, weight
below the level driving failure, weight beyond passing — is the
batteries' instance pins beside the moments' spectral coherence
(the fold against `thm:momentform`'s quadratic reads at a diagonal
instance, `lem:split`'s weights the components').
-/

namespace detector
open ground

/-- The detector pair's site datum at a spectral point `[n : d]`
and the level `[gn : gd]`, cleared at the shared second members:
the factor read's value `n (n gd + (gn d)ˇ)`. -/
def datum (n : BPair) (d gn gd : Pos) : BPair :=
  (n * ((n.scale gd) + (BPair.ofPos (gn * d)).swap)).norm

/-- The factor identity: the cleared pair `(λ² : γλ)`'s site datum
is the factor read `λ ⟨λ : γ⟩`, one value at the shared
clearing. -/
def factorRead (n : BPair) (d gn gd : Pos) : Prop :=
  ((n * n).scale gd + (n * BPair.ofPos (gn * d)).swap).oneValue
    (datum n d gn gd)

instance (n : BPair) (d gn gd : Pos) :
    Decidable (factorRead n d gn gd) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- The weight fold of the detector data over a located spectrum at
a shared second member: one weighted datum per point. -/
def detFold (ws : List (Pos × BPair)) (d gn gd : Pos) : BPair :=
  ws.foldl (fun acc r =>
    (acc + BPair.ofPos r.1 * datum r.2 d gn gd).norm) BPair.unit

/-- The requirement's read at a probe: the weight fold on its upper
side or at equal members, the detector pairs' fold at the probe's
weights. -/
def passRead (ws : List (Pos × BPair)) (d gn gd : Pos) : Prop :=
  ¬ detFold ws d gn gd < BPair.unit

instance (ws : List (Pos × BPair)) (d gn gd : Pos) :
    Decidable (passRead ws d gn gd) :=
  inferInstanceAs (Decidable (¬ _ < _))

end detector
