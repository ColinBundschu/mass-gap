import MassGap.Rankstable
import MassGap.Genericlift
/-!
`lem:chaininstances` — the rank divisors of the chain's comparisons
(`lem:rankstable`(iii)) close, per head bound, on the records of the
unit label's fusion closure under the fundamental pair at the bound's
depth (`con:depthchain`; `lem:rankstable`(ii)), every divisor read at
`n := d_f`, the fundamental count (`con:places`).

Per band family the record is the *excess gap* `gap_λ := d_f Q(λ)`,
`lem:rankstable`(i)'s Casimir polynomial at the family's two words
(`rankstable.casPoly`, its value at every count from the floor
`c2hat.dfQ` of the member, `rankstable.casPoly_eval`) against the
unit label's kernel point, one polynomial in the count per family;
the tex displays each gap as a product of naturals at a gap witness,
`c (n + a) g` at `w + g = n` (`gapPolyOf`), and `gapRead` is the
identity of the two spellings.  The depth-two instance holds the
seven families at the second fusion depth, the fundamental with its
dual, their squares, their second fundamentals and the adjoint
(`fams`, in the displayed order), each at its reach clearance read
at the count, the clearance residue's successor `a + b + 3` at the
words' reaches (`clearanceOf`; `lem:rankstable`(ii)): the gaps
`g (n + 1)` at `1 + g = n`, `2 (n + 2) g` at `1 + g = n`,
`2 (n + 1) g` at `2 + g = n` and `2 n²`, a dual pair reading one gap
(`def:c2hat`).  The *binding comparisons* are the balance pairs
`⟨gap_i : gap_j⟩` over the twenty-one family pairs
(`places.pairsOf`, `compAt`), and the *stencil cap* is
`3 d_L = 6 n` at the fundamental pair's dimension fold `2 n`
(`capPoly`, its identity with three times `rankstable.dimNum` at
the two words `capRead`; `lem:fpcap`): `7 + 21 + 1 = 29` records,
the clearance column read as displayed.

The *classification* is the equal-members reads in the rank domain,
the counts from two: the three dual pairs read one merged level at
every rank, their comparisons the sum's unit at every key
(`mergedPairs`, `mergedDivs`, `poly.unitTail`); and eight isolated
reads, each below a compared family's clearance (`classif`, entered
once): the second fundamentals' pair against the kernel point at the
rank two, the gap `2 (n + 1) g` at the vacant witness where the
second fundamental is the full column, the unit label
(`con:labels`), the squares against the adjoint at the rank two,
`2n² + 2n − 4` against `2n²`, and the fundamental pair against the
second fundamentals' pair at the rank three, `n² − 1` against
`2n² − 2n − 4`.  Every further divisor keeps its leading side at
every rank: each record off the merged levels is `genericlift.Rec`
with `lem:genericlift`'s two reads, the settled side's certificate
at the record's clearance (`genericlift.sideCert`, so
`genericlift.sideUpper` and `sideLower` hold the side at every rank
at or beyond it) and the window below it (`genericlift.rootsCert`,
the ranks from two, the classified ranks read from `classif` at
`genericlift.rootsAt`).  `recsRead` joins the record count, the
clearance column, the isolated reads' count, the seven gap
identities, the cap identity, the merged levels and the two
certificates over the record list.
-/

namespace chaininstances
open ground

/-- A gap's displayed product `c (n + a) g` at `w + g = n`: the
factor against the two linear polynomials `n + a` and `⟨n : w⟩`
(`poly.linP`). -/
def gapPolyOf (c a w : Nat) : poly.Poly :=
  poly.scaleP (BPair.ofNat c) (poly.mul (poly.linP a 0 1) (poly.linP 0 w 1))

set_option genInjectivity false in
/-- A band family's committed datum: `lem:rankstable`(i)'s two words
and the gap's displayed product data, the factor, the shift and the
witness. -/
structure Fam where
  P : List Nat
  Q : List Nat
  c : Nat
  a : Nat
  w : Nat

/-- The seven families of the depth-two closure under the fundamental
pair, in the displayed order: `ω₁`, `ω₁*`, `2ω₁`, `2ω₁*`, `ω₂`,
`ω₂*`, `ω₁ + ω₁*`. -/
def fams : List Fam :=
  [⟨[1], [], 1, 1, 1⟩, ⟨[], [1], 1, 1, 1⟩,
   ⟨[2], [], 2, 2, 1⟩, ⟨[], [2], 2, 2, 1⟩,
   ⟨[0, 1], [], 2, 1, 2⟩, ⟨[], [0, 1], 2, 1, 2⟩,
   ⟨[1], [1], 2, 0, 0⟩]

/-- A family's excess gap at its displayed product. -/
def gapOf (F : Fam) : poly.Poly := gapPolyOf F.c F.a F.w

/-- The gap identity: the Casimir polynomial at the family's words
reads the displayed product. -/
def gapRead (F : Fam) : Prop :=
  poly.oneValue (rankstable.casPoly F.P F.Q) (gapOf F)

instance instChaininstances1 (F : Fam) : Decidable (gapRead F) :=
  inferInstanceAs (Decidable (poly.oneValue _ _))

/-- The reach clearance at the count: the words' reaches `a + b + 2`
at the residue, its successor at `n = r + 1`. -/
def clearanceOf (F : Fam) : Nat := F.P.length + F.Q.length + 3

/-- The stencil cap `3 d_L = 6 n` at the fundamental pair's dimension
fold `2 n`. -/
def capPoly : poly.Poly := poly.linP 0 0 6

/-- The cap identity: the cap reads three times the fundamental
pair's dimension polynomials, `lem:rankstable`(i)'s `dimNum` at the
two words with their denominators one (`d_L = 2 d_f`,
`lem:fpcap`). -/
def capRead : Prop :=
  poly.oneValue capPoly
    (poly.scaleP (BPair.ofNat 3) (poly.add (rankstable.dimNum [1] []) (rankstable.dimNum [] [1])))
  ∧ poly.oneValue (rankstable.dimDen [1] []) (poly.linP 1 0 0)
  ∧ poly.oneValue (rankstable.dimDen [] [1]) (poly.linP 1 0 0)

instance instChaininstances3 : Decidable capRead :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The three dual pairs at their family places. -/
def mergedPairs : List (Nat × Nat) := [(0, 1), (2, 3), (4, 5)]

/-- The eight isolated reads, entered once: the family places and
the rank at each equal-members read, a gap's own read at its place
twice. -/
def classif : List (Nat × Nat × Nat) :=
  [(4, 4, 2), (5, 5, 2), (2, 6, 2), (3, 6, 2), (0, 4, 3), (0, 5, 3), (1, 4, 3), (1, 5, 3)]

/-- The family at a place. -/
def famAt (i : Nat) : Fam := getAt ⟨[], [], 0, 0, 0⟩ fams i

/-- A dual pair's read at a family pair. -/
private def isMerged (pr : Nat × Nat) : Bool :=
  mergedPairs.any (fun m => m.1 == pr.1 && m.2 == pr.2)

/-- A binding comparison's divisor at two family places, the balance
pair of the two gaps. -/
def compAt (i j : Nat) : poly.Poly :=
  poly.add (gapOf (famAt i)) (poly.neg (gapOf (famAt j)))

/-- The merged levels' divisors, the dual pairs' comparisons. -/
def mergedDivs : List poly.Poly := mergedPairs.map (fun pr => compAt pr.1 pr.2)

/-- The records off the merged levels: the seven gaps at their own
clearances, the eighteen binding comparisons off the dual pairs, each
settled at the upper of its two clearances, and the stencil cap
settled from the rank two. -/
def recs : List genericlift.Rec :=
  (List.range fams.length).map
      (fun i => ⟨gapOf (famAt i), 2, clearanceOf (famAt i), clearanceOf (famAt i), genericlift.rootsAt classif i i⟩)
    ++ ((places.pairsOf fams.length).filter (fun pr => !isMerged pr)).map
      (fun pr =>
        ⟨compAt pr.1 pr.2, 2, Nat.max (clearanceOf (famAt pr.1)) (clearanceOf (famAt pr.2)),
         Nat.max (clearanceOf (famAt pr.1)) (clearanceOf (famAt pr.2)),
         genericlift.rootsAt classif pr.1 pr.2⟩)
    ++ [⟨capPoly, 2, 2, 2, []⟩]

/-- The lemma's whole read: the record count, the clearance column
as displayed, the isolated reads' count, the seven gap identities,
the cap identity, the merged levels, and both certificates over the
record list. -/
def recsRead : Prop :=
  recs.length + mergedDivs.length = 29
  ∧ fams.map clearanceOf = [4, 4, 4, 4, 5, 5, 5]
  ∧ classif.length = 8
  ∧ (fams.all (fun F => decide (gapRead F))) = true
  ∧ capRead
  ∧ (mergedDivs.all (fun p => decide (poly.unitTail p))) = true
  ∧ (recs.all (fun R => decide (genericlift.sideCert R))) = true
  ∧ (recs.all (fun R => decide (genericlift.rootsCert R))) = true

instance instChaininstances2 : Decidable recsRead :=
  inferInstanceAs (Decidable (_ ∧ _))

end chaininstances
