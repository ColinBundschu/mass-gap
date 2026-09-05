import MassGap.Serstable
import MassGap.Steinberg
import MassGap.Fusion
/-!
`lem:memberdata` — the member count and involution, the fusion
interface's two constructed fields at a member's table, with the
interface instantiations beneath them (`con:fusion`'s member
clause).

The producers run at the coroot presentation: a label is its
coroot list, the walk carrier the balance vectors, and every form
read goes through one cleared fundamental Gram — `gramOf`, row `i`
the adjugate solve of the Cartan rows at the scaled unit column
(`elim.adjP`), the whole matrix at one positive clearing scale
(the Cartan determinant against the doubled length denominator),
so numerators and denominators compare at matched scales
throughout.  The multiplicity family is the recursion's one solve
(`lem:memberdata`(i)): the dominant keys enter at the coroot box
under the top's `ρ`-dot cap filtered at the fold membership
(`domKeys`, the transposed Cartan's adjugate solve the membership
test), the solve descends the
cleared `ρ`-dots from the top (`famGo`, the trace recursion's
display read per key with each moved count at its dominant image
through the dominance walk `domWalk`, a vacant gap, starved walk
or inexact cofactor refusing the whole family), and the full
family expands the dominant keys over their reflection orbits at
their counts (`multFam`), the fold witnesses `foldWits` the
support reads' own data.  The member count is the
member display's gap read at the family fold (`countM`,
`lem:memberdata`(i)'s display fold): each occupied content's
moved key walks to its dominant image at the walk's letter
parity (`walkP`), a walk ending at the shifted second factor the
tie's one element at the regular reads and every further end off
the ties — the row the occupied targets over the fused window
(`rowM`).  The letters' closure at a shifted key (`orbitFam`,
one parity per image at the regular reads) is `con:sertables`'
word list, the displayed signed-permutation lists
(`sertables.serWeylB/C/D`) reading it one member per element
(`con:sertables`' one-member-each read).  The
involution is the shifted walk (`lem:memberdata`(ii)): the dual
label joined to `ρ` is the dominant image of the shifted key's
balance partner (`dualM`).  The correctness reads are the landed
kit — `memberchar`'s family reads with the trace recursion's own
(`recRead`) at the produced families and the displayed Weyl
lists, the support witnesses `foldWits`' solves, and the Grams'
defining reads — decided in the check module at stated members,
with each walk's fuel a stated datum whose starvation reads the
vacant list, the pins' own refusal.

The instantiations (`con:fusion`): `fusion.dataB`, `dataC` and
`dataD` at the rank and `dataG2`, `dataF4`, `dataE6`, `dataE7`
and `dataE8` at the fixed tables, every field the table's own
derived read — the labels coroot lists at the padded equality,
`θ` the theta fold's coroot list (`thetaKey`, one read at every
member), the count and row the producers', the involution the
shifted walk's, the dimension the member gap product's exact
cofactor (`dimM`, `cor:weyldim`'s member display), the cleared
Casimir the Gram's quadratic read (`c2M`), the base the
`θ`-row diagonal's own count (`prop:row`'s member read), the
enumeration the coroot box at the Casimir cap (`belowM`), and the
class data the displayed remainder reads per member
(`lem:chargedcell`(i)'s class groups at the coroot lists) with
the winding floors the end members' Casimir reads.  The interface
laws' reads at these instances are the check module's pins.
-/

namespace memberdata
open ground

/-- A coroot list on the balance carrier. -/
def natV (m : List Nat) : List BPair := m.map BPair.ofNat

/-- The rank padding: a label read at the table's key count. -/
def padN (l : Nat) (m : List Nat) : List Nat :=
  (List.range l).map (fun k => getAt 0 m k)

/-- A balance vector's coroot list at the magnitudes, the
upper-side gaps at a dominant vector. -/
def natsOf (v : List BPair) : List Nat := v.map BPair.marginN

/-- The shifted key: the coroot list joined to `ρ`, normed. -/
def shiftV (t : gentable.Table) (m : List Nat) : List BPair :=
  poly.pnorm (elim.vecAdd (natV m) (sertables.rhoV t))

/-- The scaled unit column. -/
private def scaledE (n i s : Nat) : List BPair :=
  (List.range n).map (fun k => if k == i then BPair.ofNat s else BPair.unit)

/-- The cleared fundamental Gram: row `i` the adjugate solve of the
Cartan rows at the length-scaled unit column, so the Cartan rows
against row `i` read the determinant-scaled length diagonal — the
whole matrix the fundamentals' pairings at the one positive
clearing scale, the Cartan determinant against the doubled length
denominator (`con:sertables`' adjugate-row form reads at every
member). -/
def gramOf (t : gentable.Table) : elim.Mat :=
  (List.range t.rank).map (fun i =>
    poly.pnorm (elim.adjP t.cartan (scaledE t.rank i (getAt 0 t.lenNums i))))

/-- A fixed member's cleared Gram at its displayed adjugate rows:
`⟨ω_i, ω_j⟩` cleared as `a_ij · len_j` (`con:sertables`' adjugate
rows' form reads, `2e⟨ω_i,ω_j⟩ = a_ij⟨α_j,α_j⟩`), one stated list
against the table's lengths. -/
def gramRows (t : gentable.Table) (rows : List (List Nat)) : elim.Mat :=
  rows.map (fun r => natV (List.zipWith Nat.mul r t.lenNums))

/-- The cleared form at the produced Gram, normed
(`sertables.dotG`'s read at the canonical representative). -/
def formC (G : elim.Mat) (x y : List BPair) : BPair :=
  BPair.norm (sertables.dotG G x y)

/-- The first lower-side key. -/
private def lowGo : List BPair → Nat → Option Nat
  | [], _ => none
  | x :: tl, k => if x < BPair.unit then some k else lowGo tl (k + 1)

/-- The parity walk: the dominance walk with its letter count's
parity, one letter per raise (`lem:memberdata`(i), the walk's
letter count reading the element's parity at the reversed word's
class); a starved walk refuses the read. -/
private def walkP (t : gentable.Table) :
    Nat → List BPair → Bool → Option (List BPair × Bool)
  | 0, v, p =>
    match lowGo v 0 with
    | none => some (v, p)
    | some _ => none
  | fuel + 1, v, p =>
    match lowGo v 0 with
    | none => some (v, p)
    | some i => walkP t fuel (sertables.reflAt t i v) (!p)

/-- The dominance walk: raise at the first lower-side key until
every key sits at or beyond the unit, the parity walk's key read;
a starved walk reads the vacant list. -/
def domWalk (t : gentable.Table) (fuel : Nat) (v : List BPair) :
    List BPair :=
  match walkP t fuel v false with
  | none => []
  | some q => q.1

/-- The dual label at the shifted walk (`lem:memberdata`(ii)): the
label joined to `ρ`, read at its balance partner's dominant image,
withdrawn by `ρ`. -/
def dualM (t : gentable.Table) (fuel : Nat) (a : List Nat) : List Nat :=
  (natsOf (domWalk t fuel
    (poly.pnorm (poly.neg (shiftV t a))))).map (fun x => x - 1)

private def memFstB (v : List BPair) :
    List (List BPair × Bool) → Bool
  | [] => false
  | p :: tl => (p.1 == v) || memFstB v tl

/-- The graded closure's rounds: one frontier member expanded per
round, the reflection images at the flipped parity joined where
new; a starved closure reads the vacant list. -/
private def orbGo (t : gentable.Table) :
    Nat → List (List BPair × Bool) → List (List BPair × Bool) →
      List (List BPair × Bool)
  | 0, acc, [] => acc
  | 0, _, _ :: _ => []
  | _ + 1, acc, [] => acc
  | fuel + 1, acc, h :: tl =>
    let fresh := ((List.range t.rank).map
      (fun i => (sertables.reflAt t i h.1, !h.2))).filter
        (fun q => !(memFstB q.1 acc))
    orbGo t fuel (acc ++ fresh) (tl ++ fresh)

/-- The graded orbit family at a shifted key: the reflection
images with their parities, one parity per image at the shifted
key's regular reads (`con:sertables`). -/
def orbitFam (t : gentable.Table) (fuel : Nat) (v : List BPair) :
    List (List BPair × Bool) :=
  orbGo t fuel [(poly.pnorm v, false)] [(poly.pnorm v, false)]

/-- The ungraded closure's rounds. -/
private def orbSGo (t : gentable.Table) :
    Nat → List (List BPair) → List (List BPair) → List (List BPair)
  | 0, acc, [] => acc
  | 0, _, _ :: _ => []
  | _ + 1, acc, [] => acc
  | fuel + 1, acc, h :: tl =>
    let fresh := ((List.range t.rank).map
      (fun i => sertables.reflAt t i h)).filter
        (fun q => !(ground.containsB acc q))
    orbSGo t fuel (acc ++ fresh) (tl ++ fresh)

/-- A content's reflection orbit, the closure at the letters. -/
def orbitSet (t : gentable.Table) (fuel : Nat) (v : List BPair) :
    List (List BPair) :=
  orbSGo t fuel [poly.pnorm v] [poly.pnorm v]

/-- The fold solve at a gap: the transposed Cartan's adjugate
column, the natural simple fold's determinant-scaled coefficients
(`con:gentable`'s dominance order, the coefficients one solve at
the simple folds' injectivity). -/
private def foldSolve (t : gentable.Table) (v : List BPair) :
    List BPair :=
  elim.adjP (elim.transposeM t.cartan) v

/-- The fold-membership test: every solved entry at or beyond the
unit and at the determinant's own multiple. -/
def foldTest (t : gentable.Table) (v : List BPair) : Bool :=
  let d := BPair.marginN (elim.detL (elim.transposeM t.cartan))
  (foldSolve t v).all (fun x =>
    !(x < BPair.unit) && (BPair.marginN (BPair.norm x) % d == 0))

/-- A member's fold witness at a top: the fold solve read at the
determinant's cofactor (`thm:memberchar`'s support witnesses). -/
def foldWits (t : gentable.Table) (lam nu : List BPair) : List Nat :=
  let d := BPair.marginN (elim.detL (elim.transposeM t.cartan))
  (foldSolve t (elim.vecAdd lam (poly.neg nu))).map (fun x =>
    BPair.marginN (BPair.norm x) / d)

/-- The cleared `ρ`-dot of a coroot list at the Gram. -/
private def rdKey (t : gentable.Table) (G : elim.Mat)
    (m : List Nat) : Nat :=
  BPair.marginN (formC G (natV m) (sertables.rhoV t))

/-- The dominant keys at or below a top: the coroot box under the
top's `ρ`-dot cap, filtered at the fold membership
(`lem:memberdata`(i), the dominant keys' `ρ`-dots capped by the
top's own). -/
def domKeys (t : gentable.Table) (G : elim.Mat) (lam : List Nat) :
    List (List Nat) :=
  let cap := rdKey t G lam
  let bounds := (List.range t.rank).map (fun i =>
    cap / BPair.marginN (elim.dotP (getAt [] G i) (sertables.rhoV t)))
  (ground.boxAll bounds).filter (fun m =>
    decide (rdKey t G m ≤ cap)
      && foldTest t (elim.vecAdd (natV lam) (poly.neg (natV m))))

private def sortDesc (key : List Nat → Nat) :
    List (List Nat) → List (List Nat)
  | [] => []
  | h :: tl => ground.insertKeyDesc key h (sortDesc key tl)

private def lookupN (m : List Nat) (l : List (List Nat × Nat)) : Nat :=
  (fusion.lookupBy (fun a b => a == b) m l).getD 0

/-- One key's moved-fold numerator: per positive member and step
within the `ρ`-dot cap, the moved content's doubled form read
against the member, weighted at the standing family's count at the
moved content's dominant image — the trace recursion's fold side
(`lem:memberdata`(i)); a starved walk refuses the whole read. -/
private def numAt (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (acc : List (List Nat × Nat)) (rdTop : Nat) (m : List Nat) :
    Option BPair :=
  (List.range t.posFolds.length).foldl (fun s j =>
    match s with
    | none => none
    | some sv =>
      let av := poly.pnorm (sertables.posCorootV t j)
      let rda := BPair.marginN (formC G av (sertables.rhoV t))
      let lcap := (rdTop - rdKey t G m) / rda
      (List.range lcap).foldl (fun s2 l0 =>
        match s2 with
        | none => none
        | some sv2 =>
          let mv := poly.pnorm (elim.vecAdd (natV m)
            (elim.vecScale (BPair.ofNat (l0 + 1)) av))
          let w := domWalk t fuel mv
          if w == ([] : List BPair) then none
          else
            let mm := lookupN (natsOf w) acc
            if mm == 0 then some sv2
            else some (sv2 + formC G mv av * BPair.ofNat (2 * mm)))
        (some sv))
    (some BPair.unit)

/-- The dominant solve: the keys in descending `ρ`-dot order, the
top's count one at the top line, each further key's count the
moved-fold numerator's exact cofactor at the two Casimir reads'
gap (`lem:memberdata`(i), the recursion's one solution); a vacant
gap, a starved walk or an inexact cofactor refuses the whole
family, the vacant list the pins' own refusal. -/
private def famGo (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (top : List Nat) (rdTop : Nat) :
    List (List Nat) → List (List Nat × Nat) → List (List Nat × Nat)
  | [], acc => acc
  | m :: tl, acc =>
    if m == top then famGo t G fuel top rdTop tl (acc ++ [(m, 1)])
    else
      let denom := BPair.marginN (BPair.norm
        (formC G (shiftV t top) (shiftV t top)
          + (formC G (shiftV t m) (shiftV t m)).swap))
      if denom == 0 then []
      else
        match numAt t G fuel acc rdTop m with
        | none => []
        | some numer =>
          let n := BPair.marginN (BPair.norm numer)
          if n % denom == 0 then
            famGo t G fuel top rdTop tl (acc ++ [(m, n / denom)])
          else []

/-- The dominant multiplicity family at a top: the solve over the
sorted dominant keys. -/
def domFam (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (lam : List Nat) : List (List Nat × Nat) :=
  famGo t G fuel lam (rdKey t G lam)
    (sortDesc (rdKey t G) (domKeys t G lam)) []

/-- The full multiplicity family: the dominant keys expanded over
their reflection orbits, each at its count — the block's family,
every occupied content at its summand's count, a starved orbit
closure refusing the whole family (`lem:memberdata`(i); the
family the reads of `thm:memberchar`'s kit decide). -/
def multFam (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (lam : List Nat) : List (List BPair) :=
  let parts := (domFam t G fuel lam).map
    (fun p => (orbitSet t fuel (natV p.1), p.2))
  if parts.any (fun q => q.1.isEmpty) then []
  else parts.flatMap (fun q => q.1.flatMap (List.replicate q.2))

/-- The family fold's graded pair at a target: per occupied
content one walk of the moved key, the even and the odd hits at
the shifted second factor collected in one pass; a starved walk
refuses the whole read (`lem:memberdata`(i)'s display fold, one
walk per occupied content). -/
private def famCount (t : gentable.Table) (fuel : Nat)
    (kb kc : List BPair) : List (List BPair) → Option (Nat × Nat)
  | [] => some (0, 0)
  | nu :: tl =>
    match famCount t fuel kb kc tl with
    | none => none
    | some p =>
      match walkP t fuel
          (poly.pnorm (elim.vecAdd kc (poly.neg nu))) false with
      | none => none
      | some w =>
        if w.1 == kb then
          if w.2 then some (p.1, p.2 + 1) else some (p.1 + 1, p.2)
        else some p

/-- The member fusion count: the member display's gap read at the
produced family, the display's fold at the family
(`lem:memberdata`(i); `cor:steinberg`'s member display) — each
occupied content's moved key, the target's shifted key joined to
the content's balance partner, walked to its dominant image at the
walk's letter parity, a walk ending at the shifted second factor
the tie's one element at the regular reads and every further end
off the ties (`con:sertables`); a starved walk reads the vacant
count, the pins' own refusal. -/
def countM (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (a b c : List Nat) : Nat :=
  match famCount t fuel (shiftV t b) (shiftV t c)
      (multFam t G fuel a) with
  | none => 0
  | some p => p.1 - p.2

/-- The fusion row at two labels: the dominant targets at occupied
counts over the fused window, the targets at or below the labels'
sum, the family fold read once per target at the one produced
family (`lem:memberdata`(i)). -/
def rowM (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (a b : List Nat) : List (List Nat) :=
  let kb := shiftV t b
  let La := multFam t G fuel a
  (domKeys t G (List.zipWith Nat.add a b)).filter
    (fun c =>
      match famCount t fuel kb (shiftV t c) La with
      | none => false
      | some p => decide (0 < p.1 - p.2))

/-- `θ`'s coroot list, the theta fold's coroot reads — one read at
every member (`con:sertables`' adjugate rows, the highest root the
fundamental at the fold row's key, with the low-rank sum-family
seeds its further instances). -/
def thetaKey (t : gentable.Table) : List Nat :=
  natsOf ((List.range t.rank).map (gentable.corootAt t t.thetaFold))

/-- The member dimension: the gap product at the shifted label
against the gap product at `ρ`, the exact cofactor
(`cor:weyldim`'s member display at `serstable.gapAt`). -/
def dimM (t : gentable.Table) (m : List Nat) : Nat :=
  ground.prodOver (serstable.gapAt t (m.map (· + 1)))
      (List.range t.posFolds.length)
    / ground.prodOver (serstable.gapAt t (List.replicate t.rank 1))
      (List.range t.posFolds.length)

/-- The cleared Casimir at the produced Gram:
`⟨m, m + 2ρ⟩` at the one clearing scale. -/
def c2M (t : gentable.Table) (G : elim.Mat) (m : List Nat) : Nat :=
  BPair.marginN (formC G (natV m)
    (elim.vecAdd (natV m)
      (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t))))

/-- The below-cutoff enumeration: the nonunit coroot lists of the
box at the Casimir cap (`prop:windowfinite`'s route at the member,
every Gram pairing positive at the natural entries). -/
def belowM (t : gentable.Table) (G : elim.Mat) (k : Nat) :
    List (List Nat) :=
  let bounds := (List.range t.rank).map (fun i =>
    k / (2 * BPair.marginN (elim.dotP (getAt [] G i) (sertables.rhoV t))))
  (ground.boxAll bounds).filter (fun m =>
    (0 < ground.sumNat m) && (c2M t G m ≤ k))

end memberdata

namespace fusion
open ground

/-- A member instantiation at a table with stated class data: every
field the table's own derived read at the coroot lists, the count
and involution `lem:memberdata`'s constructions, the walks' fuel a
stated datum (`con:fusion`'s member clause). -/
def dataOf (t : gentable.Table) (G : elim.Mat) (fuel : Nat)
    (cls : List Nat → Nat) (clsAdd : Nat → Nat → Nat)
    (clsFloorN : Nat → Nat) : Data (List Nat) :=
  let pad := memberdata.padN t.rank
  ⟨(fun a b => pad a == pad b),
   (fun _ => ground.listEqBeq _),
   List.replicate t.rank 0,
   (fun a => memberdata.dualM t fuel (pad a)),
   (fun a b => List.zipWith Nat.add (pad a) (pad b)),
   memberdata.thetaKey t,
   (fun a b c => memberdata.countM t G fuel (pad a) (pad b) (pad c)),
   (fun a b => memberdata.rowM t G fuel (pad a) (pad b)),
   (fun a => memberdata.dimM t (pad a)),
   (fun a => memberdata.c2M t G (pad a)),
   memberdata.c2M t G (memberdata.thetaKey t),
   memberdata.countM t G fuel (memberdata.thetaKey t)
     (memberdata.thetaKey t) (memberdata.thetaKey t),
   (fun k => memberdata.belowM t G k),
   (fun a => cls (memberdata.padN t.rank a)), clsAdd, clsFloorN,
   (fun _ => none)⟩

/-- The signed-permutation order at the rank, the series orbits'
fuel: the closure's round count at the shifted key's whole
orbit. -/
def wFuel (l : Nat) : Nat :=
  2 ^ l * (List.range l).foldl (fun a k => a * (k + 1)) 1 + l

/-- The `B` series' class read: the spinor parity, the last coroot
key's (`lem:chargedcell`(i), the short family's doubled keys
generating the unit class). -/
def clsB (l : Nat) (m : List Nat) : Nat := getAt 0 m (l - 1) % 2

/-- The `C` series' class read: the box parity, the positions'
weighted fold (`lem:chargedcell`(i), the even-sum lists the unit
class). -/
def clsC (m : List Nat) : Nat :=
  (List.range m.length).foldl (fun a i => a + (i + 1) * getAt 0 m i) 0 % 2

/-- The `D` series' class read at even rank: the two spinor
parities as a two-bit code (`lem:chargedcell`(i)'s four classes,
each its own inverse). -/
def clsDEven (l : Nat) (m : List Nat) : Nat :=
  2 * (((List.range (l - 2)).foldl (fun a i => a + (i + 1) * getAt 0 m i) 0
        + getAt 0 m (l - 2)) % 2)
    + ((List.range (l - 2)).foldl (fun a i => a + (i + 1) * getAt 0 m i) 0
        + getAt 0 m (l - 1)) % 2

/-- The `D` series' class read at odd rank: the four-fold cycle,
the spinors at the odd reads (`lem:chargedcell`(i)). -/
def clsDOdd (l : Nat) (m : List Nat) : Nat :=
  (2 * (List.range (l - 2)).foldl (fun a i => a + (i + 1) * getAt 0 m i) 0
    + getAt 0 m (l - 2) + 3 * getAt 0 m (l - 1)) % 4

/-- The `B` member instantiation at the rank. -/
def dataB (l : Nat) : Data (List Nat) :=
  dataOf (sertables.tableB l) (memberdata.gramOf (sertables.tableB l))
    (wFuel l) (clsB l) (fun x y => (x + y) % 2)
    (fun c => if c == 0 then 0
      else memberdata.c2M (sertables.tableB l)
        (memberdata.gramOf (sertables.tableB l))
        ((List.range l).map (fun k => if k + 1 == l then 1 else 0)))

/-- The `C` member instantiation at the rank. -/
def dataC (l : Nat) : Data (List Nat) :=
  dataOf (sertables.tableC l) (memberdata.gramOf (sertables.tableC l))
    (wFuel l) clsC (fun x y => (x + y) % 2)
    (fun c => if c == 0 then 0
      else memberdata.c2M (sertables.tableC l)
        (memberdata.gramOf (sertables.tableC l))
        ((List.range l).map (fun k => if k == 0 then 1 else 0)))

/-- The `D` member instantiation at the rank: the class code and
its sum at the rank's parity, the winding floors the three end
members' reads (`lem:chargedcell`(ii)). -/
def dataD (l : Nat) : Data (List Nat) :=
  dataOf (sertables.tableD l) (memberdata.gramOf (sertables.tableD l))
    (wFuel l)
    (if l % 2 == 0 then clsDEven l else clsDOdd l)
    (if l % 2 == 0 then fun x y => 2 * ((x / 2 + y / 2) % 2) + (x + y) % 2
      else fun x y => (x + y) % 4)
    (fun c =>
      let t := sertables.tableD l
      let G := memberdata.gramOf t
      let e := fun k0 => (List.range l).map (fun k => if k == k0 then 1 else 0)
      if c == 0 then 0
      else if (if l % 2 == 0 then c == 3 else c == 2) then
        memberdata.c2M t G (e 0)
      else if (if l % 2 == 0 then c == 2 else c == 1) then
        memberdata.c2M t G (e (l - 2))
      else memberdata.c2M t G (e (l - 1)))

/-- A trivial-class member instantiation at its displayed adjugate
rows: the one class with the vacant floor (`lem:chargedcell`(i)'s
one-sector read at `G_2`, `F_4` and `E_8`). -/
def dataFixed (t : gentable.Table) (rows : List (List Nat))
    (fuel : Nat) : Data (List Nat) :=
  dataOf t (memberdata.gramRows t rows) fuel
    (fun _ => 0) (fun _ _ => 0) (fun _ => 0)

/-- The `G_2` instantiation. -/
def dataG2 : Data (List Nat) := dataFixed sertables.tableG2 sertables.adjG2 16

/-- The `F_4` instantiation. -/
def dataF4 : Data (List Nat) :=
  dataFixed sertables.tableF4 sertables.adjF4 1200

/-- The `E_6` instantiation: the three classes at the key-three
remainders (`con:sertables`' adjugate rows;
`lem:chargedcell`(i)), the winding floor the paired fundamentals'
shared least. -/
def dataE6 : Data (List Nat) :=
  dataOf sertables.tableE6 (memberdata.gramRows sertables.tableE6 sertables.adjE6)
    52000
    (fun m => (getAt 0 m 0 + 2 * getAt 0 m 2 + getAt 0 m 4
      + 2 * getAt 0 m 5) % 3)
    (fun x y => (x + y) % 3)
    (fun c => if c == 0 then 0
      else memberdata.c2M sertables.tableE6
        (memberdata.gramRows sertables.tableE6 sertables.adjE6)
        [1, 0, 0, 0, 0, 0])

/-- The `E_7` instantiation: the two classes at the key-two
remainders, the winding floor the minuscule member's read. -/
def dataE7 : Data (List Nat) :=
  dataOf sertables.tableE7 (memberdata.gramRows sertables.tableE7 sertables.adjE7)
    2903040
    (fun m => (getAt 0 m 1 + getAt 0 m 4 + getAt 0 m 6) % 2)
    (fun x y => (x + y) % 2)
    (fun c => if c == 0 then 0
      else memberdata.c2M sertables.tableE7
        (memberdata.gramRows sertables.tableE7 sertables.adjE7)
        [0, 0, 0, 0, 0, 0, 1])

/-- The `E_8` instantiation. -/
def dataE8 : Data (List Nat) :=
  dataFixed sertables.tableE8 sertables.adjE8 696729600

end fusion
