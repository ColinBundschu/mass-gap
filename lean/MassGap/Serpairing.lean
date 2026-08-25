import MassGap.Sertables
import MassGap.Split
/-!
`lem:serpairing` — the defining power's invariants at a `B`, `C` or
`D` member.  At rank clearance (rank at or above the pair count, the
`D` series at its successor) the invariants of `V^{⊗2k}` are the
pair-partition span, one vector per pair partition of the `2k`
places at the count `(2k-1)!!` (`dfac`, `allParts` the sorted-pair
enumeration off the least free place, `length_allParts` the count
theorem).  The span's Gram is the loops' fold (`loopFold`): the walk
takes the least unvisited place and alternates the two partitions'
mates until it returns, one loop per orbit, the loop's grading the
first partition's steps joined to the second-slot entries; `B` and
`D` read the dimension `r+3` per loop (`dimPow`, `gramBD`), `C`
reads `2r` per loop at its crossing parity (`rankPow`, `gramC`, the
odd class negated).  The vectors are the dual pair's contractions:
`dualB`, `dualC` and `dualD` the key-coefficient matrices at the
paired keys with `B`'s null square at the balance partner of two,
`partVec` the
coordinate read over `con:places`' monomial enumeration, the pairs'
entry product per monomial.  The invariance is `invRead`'s two
conjuncts, the support at the unit content with the stacked simple
raisings' annihilation at `sertables.actMat`'s Leibniz image over
the degree's own basis, the content conjunct separating the
invariants from the wider raising kernel.  The in-carrier Gram identities
`gramReadB`, `gramReadC` and `gramReadD` read the computed pairing
of the partition vectors against the symbolic Gram at the member's
derived residue (`gentable.residue`) — `B` at its cleared pairing
weights carrying the stated scale `2^{2k}` (`pwListB` the
per-monomial weights hoisted once per read, `dotWB` the weighted
dot), `C` and `D` at the identity weight.  The `D` tie enters at its exhibit: the
arrangement sign vector `epsVec` over the full key content, the
swap grading's read (`places.parity`) with the repeated-key
coordinates at the unit.
-/

namespace serpairing
open ground

/-- The pair-partition count `(2k-1)!!`, the successor's odd
multiplier. -/
def dfac : Nat → Nat
  | 0 => 1
  | k + 1 => (2 * k + 1) * dfac k

/-- The pair partitions of a place list as sorted pair lists: the
least place pairs with each later place, the recursion on the rest
with the partner removed. -/
def partsGo : Nat → List Nat → List (List (Nat × Nat))
  | 0, _ => [[]]
  | _ + 1, [] => [[]]
  | fuel + 1, a :: rest =>
    (List.range rest.length).flatMap (fun j =>
      (partsGo fuel (rest.eraseIdx j)).map
        (fun q => (a, getAt 0 rest j) :: q))

/-- The pair partitions of the `2k` places. -/
def allParts (k : Nat) : List (List (Nat × Nat)) :=
  partsGo (2 * k) (List.range (2 * k))

/-- The scatter fold's length at branches of one length. -/
private theorem length_flatMapRange {β : Type} (f : Nat → List β) :
    ∀ (n c : Nat), (∀ j, j < n → (f j).length = c) →
      ((List.range n).flatMap f).length = n * c
  | 0, c, _ => (Nat.zero_mul c).symm
  | n + 1, c, h => by
    rw [range_succ n, flatMap_append f (List.range n) [n], length_append,
      length_flatMapRange f n c (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    show n * c + ((f n ++ []).length) = (n + 1) * c
    rw [length_append (f n) [], h n (Nat.lt_succ_self n), Nat.succ_mul]
    rfl

/-- The even-place enumeration's length, the odd multipliers'
descent. -/
private theorem partsGoLen : ∀ (fuel m : Nat) (l : List Nat),
    l.length = 2 * m → l.length ≤ fuel →
    (partsGo fuel l).length = dfac m
  | 0, 0, [], _, _ => rfl
  | _ + 1, 0, [], _, _ => rfl
  | _, 0, _ :: _, h, _ => Nat.noConfusion h
  | _, _ + 1, [], h, _ => Nat.noConfusion h
  | 0, _ + 1, _ :: rest, h, hle =>
    absurd hle (Nat.not_succ_le_zero rest.length)
  | fuel + 1, m + 1, a :: rest, h, hle => by
    have hr : rest.length = 2 * m + 1 := Nat.succ.inj h
    show ((List.range rest.length).flatMap (fun j =>
      (partsGo fuel (rest.eraseIdx j)).map
        (fun q => (a, getAt 0 rest j) :: q))).length = dfac (m + 1)
    have hf : rest.length ≤ fuel := Nat.le_of_succ_le_succ hle
    rw [hr] at hf
    rw [length_flatMapRange _ rest.length (dfac m) (fun j hj => by
      rw [length_map]
      have he : (rest.eraseIdx j).length = 2 * m := by
        have h1 := length_eraseIdx rest j hj
        rw [hr] at h1
        exact Nat.succ.inj h1
      exact partsGoLen fuel m (rest.eraseIdx j) he (by
        rw [he]
        exact Nat.le_of_succ_le hf)), hr]
    exact rfl

/-- The count theorem: the enumeration's length is `(2k-1)!!` at
every pair count. -/
theorem length_allParts (k : Nat) : (allParts k).length = dfac k :=
  partsGoLen (2 * k) k (List.range (2 * k))
    (ground.length_range (2 * k))
    (Nat.le_of_eq (ground.length_range (2 * k)))

/-- A place's partner in a partition, the pairs' fold. -/
def mateOf (p : List (Nat × Nat)) (a : Nat) : Nat :=
  p.foldl (fun acc pr =>
    if pr.1 == a then pr.2 else if pr.2 == a then pr.1 else acc) a

private def isSecond (pl : List (Nat × Nat)) (a : Nat) : Bool :=
  pl.any (fun pr => pr.2 == a)

/-- One loop's walk: the alternating mates from the start until the
return, the state the first partition's step count, the second-slot
entry count and the visited places. -/
private def loopGo (p q : List (Nat × Nat)) (start : Nat) :
    Nat → Bool → Nat → Nat × Nat × List Nat → Nat × Nat × List Nat
  | 0, _, _, st => st
  | fuel + 1, pFlag, a, (m, ag, vis) =>
    let pl := if pFlag then p else q
    let m' := if pFlag then m + 1 else m
    let ag' := if isSecond pl a then ag + 1 else ag
    let b := mateOf pl a
    if b == start then (m', ag', vis ++ [a])
    else loopGo p q start fuel (!pFlag) b (m', ag', vis ++ [a])

/-- The loops' fold over two partitions of the places: the walk
takes the least unvisited place and alternates the partitions'
mates until the return, one loop per orbit; the fold reads the loop
count with the grading sum, per loop the first partition's steps
joined to the second-slot entries. -/
def loopFold (p q : List (Nat × Nat)) (n : Nat) : Nat × Nat :=
  let st := (List.range n).foldl (fun st i =>
    if 0 < countOf i st.2.2 then st
    else
      let w := loopGo p q i n true i (0, 0, [])
      (st.1 + 1, (st.2.1 + w.1 + w.2.1, st.2.2 ++ w.2.2)))
    ((0, (0, [])) : Nat × Nat × List Nat)
  (st.1, st.2.1)

/-- The loop count alone. -/
def loopCount (p q : List (Nat × Nat)) (n : Nat) : Nat :=
  (loopFold p q n).1

/-- The dimension's power, a polynomial in the residue at
`r + 3` per loop. -/
def dimPow (c : Nat) : poly.Poly := poly.powOf [⟨4, 1⟩, ⟨2, 1⟩] c

/-- The paired rank's power, a polynomial in the residue at `2r`
per loop. -/
def rankPow (c : Nat) : poly.Poly :=
  poly.powOf [BPair.unit, ⟨3, 1⟩] c

/-- The `B` and `D` symbolic Gram at a pair count: the dimension's
power at the loop count, entrywise over the partitions. -/
def gramBD (k : Nat) : split.PMat :=
  (allParts k).map (fun p => (allParts k).map (fun q =>
    dimPow (loopCount p q (2 * k))))

/-- The `C` symbolic Gram at a pair count: the paired rank's power
at the loop count, the odd grading class negated. -/
def gramC (k : Nat) : split.PMat :=
  (allParts k).map (fun p => (allParts k).map (fun q =>
    let w := loopFold p q (2 * k)
    if w.2 % 2 == 1 then poly.neg (rankPow w.1) else rankPow w.1))

/-- The `B` dual pair over the defining keys: the paired squares at
one, the null square at the balance partner of two —
`con:sertables`' displayed sign, the annihilation's own
forcing. -/
def dualB (l : Nat) : elim.Mat :=
  ground.matOf (sertables.vcountB l) (sertables.vcountB l) (fun r c =>
      if r < l && c == r + l then BPair.ofNat 1
      else if c < l && r == c + l then BPair.ofNat 1
      else if r == 2 * l && c == 2 * l then (BPair.ofNat 2).swap
      else BPair.unit)

/-- The `C` dual pair over the defining keys: the paired squares at
the alternating signs. -/
def dualC (l : Nat) : elim.Mat :=
  ground.matOf (sertables.vcountC l) (sertables.vcountC l) (fun r c =>
      if r < l && c == r + l then BPair.ofNat 1
      else if c < l && r == c + l then (BPair.ofNat 1).swap
      else BPair.unit)

/-- The `D` dual pair over the defining keys: the paired squares at
one. -/
def dualD (l : Nat) : elim.Mat :=
  ground.matOf (sertables.vcountD l) (sertables.vcountD l) (fun r c =>
      if r < l && c == r + l then BPair.ofNat 1
      else if c < l && r == c + l then BPair.ofNat 1
      else BPair.unit)

/-- A pair partition's vector at a dual-pair matrix: the coordinate
at each monomial of the doubled degree is the pairs' entry product,
over `con:places`' enumeration of the key lists. -/
def partVec (n k : Nat) (c : elim.Mat) (p : List (Nat × Nat)) :
    List BPair :=
  (places.allMon n (2 * k)).map (fun m =>
    p.foldl (fun acc pr =>
      acc * getAt BPair.unit (getAt [] c (getAt 0 m pr.1))
        (getAt 0 m pr.2))
      (BPair.ofNat 1))

/-- The `D` tie's exhibit at a rank: the arrangement sign vector
over the full key content, the swap grading read at each
every-key-once monomial and the unit at a repeated key. -/
def epsVec (l : Nat) : List BPair :=
  (places.allMon (2 * l) (2 * l)).map (fun m =>
    if ((List.range (2 * l)).all (fun j => countOf j m == 1)) then
      (if places.parity m then (BPair.ofNat 1).swap else BPair.ofNat 1)
    else BPair.unit)

/-- The degree off the basis count, the divisions' fold. -/
private def degGo (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, len => if len ≤ 1 then 0 else degGo n fuel (len / n) + 1

/-- The Leibniz image of a coordinate vector: the per-monomial
images (`sertables.actMat`) scaled by the coordinates and
collected, the sum's-unit coordinates read off. -/
private def actVecGo (M : elim.Mat) (mons : List (List Nat)) :
    List (List Nat) → List BPair → List BPair → List BPair
  | [], _, acc => acc
  | _ :: _, [], acc => acc
  | m :: ms, c :: cs, acc =>
    actVecGo M mons ms cs
      (if c.oneValue BPair.unit then acc
       else elim.vecAdd acc (elim.vecScale c (sertables.actMat M mons m)))

/-- The invariance read, `lem:serpairing`'s invariant object at its
two conjuncts: the vector's support sits at the unit content (a
monomial at a coordinate off equal members reads `unitContentAt`),
and every stated matrix annihilates the vector under the Leibniz
action, the image's unit tail over the degree's own basis — the
content conjunct separates the invariants from the wider raising
kernel, a top off the unit content passing the annihilation
alone. -/
def invRead (n : Nat) (rs : List elim.Mat) (v : List BPair) : Prop :=
  (let mons := places.allMon n (degGo n v.length v.length)
   (List.zipWith (fun m c =>
       if (c : BPair).oneValue BPair.unit then true
       else sertables.unitContentAt (n / 2) m) mons v).all (fun b => b)
     && rs.all (fun R =>
       if poly.unitTail
           (actVecGo R mons mons v (mons.map (fun _ => BPair.unit)))
       then true else false)) = true

instance (n : Nat) (rs : List elim.Mat) (v : List BPair) :
    Decidable (invRead n rs v) :=
  inferInstanceAs (Decidable (_ = _))

/-- The `B` cleared pairing's weight list at a stated monomial
basis: per monomial the cleared weights' own product, the fold
computed once per Gram read. -/
def pwListB (l : Nat) (mons : List (List Nat)) : List BPair :=
  mons.map (fun m =>
    BPair.ofNat (m.foldl (fun acc c => acc * sertables.pw2B l c) 1))

/-- The `B` cleared-pairing dot at a stated weight list: per
monomial the coordinates' product at the weight, the entries'
fold. -/
def dotWB : List BPair → List BPair → List BPair → BPair
  | [], _, _ => BPair.unit
  | _ :: _, [], _ => BPair.unit
  | _ :: _, _ :: _, [] => BPair.unit
  | w :: ws, a :: s, b :: t => a * b * w + dotWB ws s t

/-- The `B` in-carrier Gram identity at a rank and a pair count:
every partition pair's cleared-pairing dot reads the symbolic Gram
entry at the derived residue, the cleared weights carrying the
stated scale `2^{2k}`. -/
def gramReadB (l k : Nat) : Prop :=
  (let n := sertables.vcountB l
   let mons := places.allMon n (2 * k)
   let ws := pwListB l mons
   let vecs := (allParts k).map (partVec n k (dualB l))
   let g := gramBD k
   let r := BPair.ofNat (gentable.residue (sertables.tableB l))
   let s := BPair.ofNat (2 ^ (2 * k))
   (List.range vecs.length).all (fun i =>
     (List.range vecs.length).all (fun j =>
       if (dotWB ws (getAt [] vecs i) (getAt [] vecs j)).oneValue
           (s * poly.eval (getAt [] (getAt [] g i) j) r)
       then true else false))) = true

instance (l k : Nat) : Decidable (gramReadB l k) :=
  inferInstanceAs (Decidable (_ = _))

/-- The `C` in-carrier Gram identity at a rank and a pair count:
every partition pair's dot at the identity weight reads the
symbolic Gram entry at the derived residue. -/
def gramReadC (l k : Nat) : Prop :=
  (let n := sertables.vcountC l
   let vecs := (allParts k).map (partVec n k (dualC l))
   let g := gramC k
   let r := BPair.ofNat (gentable.residue (sertables.tableC l))
   (List.range vecs.length).all (fun i =>
     (List.range vecs.length).all (fun j =>
       if (elim.dotN (getAt [] vecs i) (getAt [] vecs j)).oneValue
           (poly.eval (getAt [] (getAt [] g i) j) r)
       then true else false))) = true

instance (l k : Nat) : Decidable (gramReadC l k) :=
  inferInstanceAs (Decidable (_ = _))

/-- The `D` in-carrier Gram identity at a rank and a pair count:
every partition pair's dot at the identity weight reads the
symbolic Gram entry at the derived residue. -/
def gramReadD (l k : Nat) : Prop :=
  (let n := sertables.vcountD l
   let vecs := (allParts k).map (partVec n k (dualD l))
   let g := gramBD k
   let r := BPair.ofNat (gentable.residue (sertables.tableD l))
   (List.range vecs.length).all (fun i =>
     (List.range vecs.length).all (fun j =>
       if (elim.dotN (getAt [] vecs i) (getAt [] vecs j)).oneValue
           (poly.eval (getAt [] (getAt [] g i) j) r)
       then true else false))) = true

instance (l k : Nat) : Decidable (gramReadD l k) :=
  inferInstanceAs (Decidable (_ = _))

end serpairing
