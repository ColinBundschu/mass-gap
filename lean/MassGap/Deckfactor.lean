import MassGap.Hermitesign
/-!
`lem:deckfactor` — the deck symbol, and the interior factor.  A
polynomial with the deck symmetry — coefficients equal at every
index pair joining to `2m`, the unit-monomial coefficient off equal
members — is `deckSymRead`; its deck symbol is the one exact
back-substitution from the top coefficients (`symbolOf` at the deck
monomials `z^i (z²+1)^j`, `assembleSym` the display's own sum, the
map unitriangular), the coherence `symbolRead` holding exactly at
the deck-symmetric data.  The band read is the display's segment
count at the crossing endpoints: the display enters through its
cleared-variable monic (`clearVarBT`, `thm:windowsep`'s stated-top
clearing — the roots rescaled by the top's magnitude at the
homogeneity principle), and `lem:hermitesign`'s bracket pencil at
the doubled magnitude's endpoints reads every root off the closed
crossing segment (`bandClear` at `segCountRead`, the count the
sum's unit).  A root
pair of the deck relation at a chord datum enters at a shared
clearing, `zn zn' = c²` the product-one read; the interior member
is the one at `zn² ≤ c²`, one pair comparison (`interiorRead`),
strict off the crossing values, and the interior margin squares to
the crossing read, `⟨1 : z²⟩² = z² ⟨w² : 4⟩` cleared at the shared
clearing (`marginRead`, the walk's `[9 : 4]` at base two
`thm:channeldiv`'s own instance; the identity is the relation's own
square, the tex display `z⁴ + 1 + 4z² = w²z² + 2z²`, its general
derivation riding at the corner margin's consumers, `lem:corner`'s
deck family, the read the display's verification).  The
factorization
`p = c · p_int · p_ext` reads at the cleared root-pair quadratics,
one per chord datum with the interior clause per pair
(`intExtRead`, `lem:stagesplit`'s factor folds); a definite chord
datum's roots enter over its pair's quadratic extensions and the
stored-tower instances land with the emitted certificates' tier at
their recorded consumers (`thm:decimation`(iii)'s deck divisors,
`lem:spectator`(iii)'s solvent), the reads here their displays. -/

namespace deckfactor
open ground poly elim inertia

/-- The deck symmetry's read at the value: the unit-monomial
coefficient off equal members, the keys beyond the doubled degree
at the sum's unit, and the coefficients equal at every index pair
joining to `2m` (`lem:deckfactor`'s display). -/
def deckSymRead (p : Poly) (m : Nat) : Prop :=
  (ground.getAt BPair.unit p 0).offUnit
  ∧ poly.unitTail (p.drop (2 * m + 1))
  ∧ ((List.range (2 * m + 1)).all (fun i => decide
      ((ground.getAt BPair.unit p i).oneValue
        (ground.getAt BPair.unit p (2 * m - i))))) = true

instance (p : Poly) (m : Nat) : Decidable (deckSymRead p m) :=
  inferInstanceAs (Decidable (¬ _ ∧ _ ∧ _ = _))

/-- The deck monomial's plus factor at a power, `(z² + 1)^j`. -/
def zsq1pow : Nat → Poly
  | 0 => poly.one
  | j + 1 =>
    poly.mul [BPair.ofPos .one, BPair.unit, BPair.ofPos .one]
      (zsq1pow j)

/-- The monomial shift, the keys moved up. -/
def shiftP (i : Nat) (p : Poly) : Poly :=
  List.replicate i BPair.unit ++ p

/-- The deck symbol's display, `p = Σ_{i+j=m} P_j z^i (z²+1)^j`. -/
def assembleSym (P : Poly) (m : Nat) : Poly :=
  (List.range (m + 1)).foldl (fun acc j =>
    poly.add acc (shiftP (m - j)
      (poly.scaleP (ground.getAt BPair.unit P j) (zsq1pow j)))) []

private def symGo (m : Nat) : Nat → Poly → List BPair → List BPair
  | 0, _, acc => acc
  | j + 1, cur, acc =>
    let c := ground.getAt BPair.unit cur (m + j)
    symGo m j
      (poly.add cur ((shiftP (m - j)
        (poly.scaleP c (zsq1pow j))).map BPair.swap))
      (c :: acc)

/-- The deck symbol, one exact back-substitution from the top
coefficients: the map from the symbol's coefficients to the top
coefficients is unitriangular, and the descent peels one key per
step. -/
def symbolOf (p : Poly) (m : Nat) : Poly := symGo m (m + 1) p []

/-- The symbol's coherence: the back-substitution assembles to the
polynomial exactly at the deck-symmetric data. -/
def symbolRead (p : Poly) (m : Nat) : Prop :=
  poly.oneValue p (assembleSym (symbolOf p m) m)

instance (p : Poly) (m : Nat) : Decidable (symbolRead p m) :=
  poly.decOneValue _ _

/-- The interior member at a chord datum, the shared clearing's
read: the relation `zn² + c² = wn zn` with the modulus comparison
`zn² ≤ c²`, one pair comparison, strict off the crossing values. -/
def interiorRead (zn wn : BPair) (c : Pos) : Prop :=
  BPair.oneValue (zn * zn + BPair.ofPos (c * c)) (wn * zn)
  ∧ zn * zn ≤ BPair.ofPos (c * c)

instance (zn wn : BPair) (c : Pos) : Decidable (interiorRead zn wn c) :=
  inferInstanceAs (Decidable (_ ∧ _ ≤ _))

/-- The interior margin squares to the crossing read,
`⟨1 : z²⟩² = z² ⟨w² : 4⟩` cleared at the shared clearing: the
relation's square at the sum `z⁴ + 1 + 4z² = w²z² + 2z²`. -/
def marginRead (zn wn : BPair) (c : Pos) : Prop :=
  BPair.oneValue (zn * zn + BPair.ofPos (c * c)) (wn * zn)
  ∧ BPair.oneValue
      ((BPair.ofPos (c * c) + (zn * zn).swap)
        * (BPair.ofPos (c * c) + (zn * zn).swap))
      ((zn * zn) * (wn * wn + (BPair.ofPos (4 * (c * c))).swap))

instance (zn wn : BPair) (c : Pos) : Decidable (marginRead zn wn c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The factorization `p = c · p_int · p_ext` at cleared root-pair
data, one `(zn, zn', c)` per chord datum: the pair's product-one
read `zn zn' = c²`, the interior clause `zn² ≤ c²` per pair, and
the cleared quadratics' fold against the leading coefficient, the
degrees splitting evenly. -/
def intExtRead (p : Poly) (cl : BPair)
    (pairs : List (BPair × BPair × Pos)) : Prop :=
  cl.offUnit
  ∧ (pairs.all (fun r =>
      decide (BPair.oneValue (r.1 * r.2.1)
        (BPair.ofPos (r.2.2 * r.2.2)))
      && decide (r.1 * r.1
        ≤ BPair.ofPos (r.2.2 * r.2.2)))) = true
  ∧ poly.oneValue
      (p.map (fun x => x.scale
        (pairs.foldl (fun a r => a * r.2.2) Pos.one)))
      (poly.mul [cl] (poly.prodFold (pairs.map (fun r =>
        [BPair.ofPos r.2.2, (r.1 + r.2.1).swap, BPair.ofPos r.2.2]))))

instance (p : Poly) (cl : BPair)
    (pairs : List (BPair × BPair × Pos)) :
    Decidable (intExtRead p cl pairs) :=
  inferInstanceAs (Decidable (¬ _ ∧ _ = _ ∧ _))

private def cvGo (m : BPair) (neg : Bool) :
    List BPair → List BPair × BPair
  | [] => ([], BPair.ofPos .one)
  | x :: t =>
    let r := cvGo m neg t
    (((if neg then x.swap else x) * r.2).norm :: r.1, (m * r.2).norm)

/-- The cleared-variable display's below-top list, read at the
value's representative (`poly.vnorm`, the homogeneity principle's
one-value-per-argument test): each coefficient scaled by the top's
magnitude at its key's gap below the top's predecessor, the members
swapped at a top on its lower side, so the list joined to the unit
top is the display's monic clearing and its roots are the display's
own at the magnitude's rescaling (`thm:windowsep`'s stated-top
clearing); one multiplication per key, the power riding the
walk. -/
def clearVarBT (p : Poly) : Poly :=
  let q := poly.vnorm p
  (cvGo (windowsep.mag (poly.top q))
    (decide (poly.top q < (poly.top q).swap))
    (q.take (q.length - 1))).1

/-- A point rescaled to a display's cleared variable: the top's
magnitude multiple at the value's representative
(`windowsep.radiusD`), the display's roots the cleared monic's at
this map, one value at every representative
(`windowsep.radiusD_congr`). -/
def clearAt (p : Poly) (x : BPair) : BPair := x * windowsep.radiusD p

/-- The band read at a full display: the cleared-variable monic's
segment count at the crossing endpoints rescaled to the doubled
magnitude, every root of the display off the closed crossing
segment. -/
def bandClear {o1 o2 : Nat} (p : Poly) (spH : Split o1)
    (spB : Split o2) : Prop :=
  hermitesign.segCountRead (clearVarBT p)
    (clearAt p ⟨1, 3⟩) (clearAt p ⟨3, 1⟩) Pos.one 0 spH spB

instance {o1 o2 : Nat} (p : Poly) (spH : Split o1) (spB : Split o2) :
    Decidable (bandClear p spH spB) :=
  inferInstanceAs (Decidable (hermitesign.segCountRead _ _ _ _ _ _ _))

end deckfactor
