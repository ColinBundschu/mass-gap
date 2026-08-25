import MassGap.Pairpencil
import MassGap.Deck
import MassGap.Cellcount
/-!
`lem:fiberdec` — the window floor fibers over momentum, and this
tier owns the fibering's carrier and its translation.  The
fibering's family is the odd tori at side five or beyond, the side
where the lemma's own comparison clears the torus's winding states;
the translation and index reads below hold at every odd side, so
the side-three windows are this tier's structural test bench and
the level claims are the family's alone.  `torusRegion` at `d ≥ 2`
takes the site keys to be the naturals below `L^d` at positional
base-`L` arithmetic, the links `d · L^d` at the key `(direction,
site)`, the plaquettes the unit squares one per site and direction
pair (`torusPlaq`, its boundary word the four oriented links
`con:lattice` asks for), and the two-coloring by the coordinate
sum's parity; `chainRegion` is the `d = 1` carrier, the plaquette
chain — consecutive squares sharing one link `rem:dictionary`'s
lattice item, the closure around a cycle of the stated length
`con:lattice`'s torus-family requirement — `2L`
vertices in two rows with the `L` rungs, the `2L` rails and the `L`
squares, the coloring by the column-and-row sum's parity.

The translation is the shift along one direction (`shiftBy` at the
site keys, `chainBy` at the chain's), a map of the link keys with
its witness the shift at the complementary step, and its reads are
the lemma's own: it permutes the links with that witness (`permRead`,
the two composition reads at `con:places`' transpose-is-inverse),
two directions' shifts compose to one map at either order
(`commutesRead` with its key extraction, `con:lattice`'s
composition clause at a direction carried to itself — the
instance of `intertwineRead`, one map carrying a second to a
third across the keys — and `permMatAt_comm` its matrix read),
it transports the endpoints along the vertex permutation it induces
(`endsRead` at `chainVert` and at the site shift itself, that
vertex map read a permutation of the vertex range at its own
witness by `vertPermRead`, at `chainVertInv` and `shiftSiteInv`),
it maps the plaquette list into itself (`plaqMoveRead`, every image
word a member of the plaquette list), and its `L`-fold iterate is
the identity (`cycleRead` at `iterAt`, the tex's `T^L = 1`).

The index action is the relabeling (`permConf`, the moved link's
label read at the link the witness names), and its three window
reads are the lemma's commuting datum at the index layer: the
content is fixed (`contentFixed`), the occupancy is fixed
(`occFixed`, the vertex data transported along the induced vertex
permutation), and the index maps within itself (`idxFixed`).  The
three take the window's region, whose link width is the relabeled
width, and the index as a stated list, `carrier.idx`'s own value
at the window pinned beside them, so a battery decides each read
against one enumeration rather than against nine.  On the window
matrices the action is the permutation matrix `permMat` on that
index with the unit line at its head, and the commuting read is its
congruence (`commRead`, `Pmᵀ H Pm = H`) — at the free end
(`prop:segment`) `H` is the electric member alone at its own
one-member site (`pairpencil.pencilE` over `windowDiag`), the
diagonal fixed exactly where the contents are,
and the batteries read the congruence at the committed chain
window.

The tier's own remainder is named rather than parked.  The general
form of the three index reads — the content and the occupancy fixed
at every configuration of every region admitting the action, the
congruence at every window — asks for the index list's own
permutation kit, which the tree does not hold; the decidable reads
here are stated at the data and the batteries decide them.

The chord tier stands beneath them.  A polynomial reads at a matrix
of a stated order by the Horner recursion of `def:poly`, the
constant entering at the weighted identity (`polyEvalM`), with the
iterate and the geometric word beside it (`matPow`, `wordSum`), and
the chord operator is `S := T + Tᵀ` (`chordOp`) with the lemma's
word `X := T^m P_L(S)` (`chordWord`, the symbol `deck.pSum`'s).
Four of the lemma's steps are general theorems over the matrix kit.
The permutation matrix's own algebra is the first: the matrix of a
composed map is the matrices' product (`permMatAt_mul`, the entries
`def:elim`'s one-index pairings at the right factor's occupied
key), the matrix of an iterate is the matrix's power
(`permMatAt_pow`), the identity map's matrix is the identity
(`permMatAt_id`), and a translation's transpose is its witness's
own matrix (`transposeM_permMatAt`, `con:places`'
transpose-is-inverse).  On it the isometry clause is derived rather
than decided — `permRead` gives `orthRead` outright
(`permRead_orth`, the permutation read unpacked at a key by
`permRead_at`) — and the tex's `T^L = 1` reaches the matrix level
from the cycle read (`cycleRead_pow`).  The deck relation
`T² + 1 = S T` then collects from the orthogonality read alone
(`chord_deck`, the product `Tᵀ T = 1` collected), and the chord
doubles on a fixed word, `S X = 2 X` from `T X = X` and
`Tᵀ X = X` (`chord_join`).  The word's two fixed reads are derived
besides: the geometric word is the matrix-valued index fold at the
powers (`wordSum` at `elim.msum`), so its `T`-multiple is the
shifted family's fold, which reads the family's own once the
wrapped `T^L` reads `T^0` (`wordSum_fixed` at `elim.msum_wrap`,
the cycle read's own consequence through `cycleRead_pow`), and the
witness's read follows at the orthogonality alone
(`inertia.fixed_transpose`, the product's left congruence against
the identity's own product).  `fixedWordRead`'s content is then a
general theorem at a translation of stated shape (`fixedWord_of`)
and at a window's own two reads (`fixedWord_perm`).  The word
identity and the annihilation are general theorems as well: the
evaluation kit (`evalM_const`, `evalM_consUnit`, `evalM_congr`,
`evalM_add`, `evalM_mulX` over `deck.mulX_read`) reads the deck
families at the operator, the plus read `p_j(S) = T^j + T^b` at
`j + b = k + 1` closes by the two-seed induction on the family
recursion with the neighbor pair `S T^{a+1} = T^{a+2} + T^a`
(`plus_read`, `chord_mul_pow`), the moved symbol collects the
centered power segment (`seg_read`, the grouping about the middle
power at `elim.msum`'s shift and congruence), and the word
identity follows at the count's own join (`word_read`).  The
annihilation descends from the word: the chord commutes past the
power (`chordOp_pow_comm`, the transpose a power at the cycle,
`transpose_as_pow`), the witness's iterate clears the power
(`clearW_pow` at `iterAt_inv`), and `S P_L(S) = 2 P_L(S)` holds at
every translation with its cycle and witness (`annih_of`).  The
decidable reads (`deckOpRead`, `wordOpRead`, `annihRead`) stay the
fast per-window spellings, the batteries discharging them by the
theorems at the committed windows.

The base-rational splitting is the two chord blocks over the
ground: the unit fiber, the kernel of the pair `(S : 2)`'s site
datum (`unitDatum`), whose membership is the fixed read `T v = v`
at the identification `D₁ᵀ D₁ + S = 2` of the datum `D₁` at
`1 + D₁ = T` (`identRead`, `unitFiberRead`); and the kernel of
`P_L(S)`, a spanning list by elimination (`rootBlockRead`), the two
lists' concatenation carrying the window's datum to their block
join (`blockCongrRead`, `baseSplitRead`) with the count splitting
at `lem:inertia`'s `rev_join` — the batteries' own pin.  The
sampled momenta are the chord `2` with `P_L`'s `m` located roots,
each a designated bracket datum at `thm:windowsep`'s separation
(`momentaRead` at `lem:stage`'s isolation).

The doubling tier opens at the block datum `A` of `T = Tᵀ + A`
(`bandDatum`, the site datum over the pair) with its band read a
general theorem over the matrix kit: `A² + 4 = S²` at the
orthogonality alone (`chord_band`), the crossed terms cancelling
against their own swaps and the two products `T Tᵀ = Tᵀ T = 1`
entering as the constant's halves; on a chord block at a located
root the same display reads `A² + 4 = t²`.

Beneath it stand the tier's two output layers, both decidable at
stated data.  The per-orbit layer is the deck-family column
`u = Σ_{b<L} p_b(t) T^b w` written on the orbit's own translate
list over the polynomial carrier, its coordinates the families read modulo
the deck symbol (`deckColumn` at `deck.redP`, `deck.pSum_monic`
the divisor's own monicity), with the lemma's three per-orbit reads
on it: the
membership `S u = x u` at the recursion closing cyclically
(`colMemberRead`), the perpendicularity of the `A`-image
(`perpRead`), and the pair's independence at its Gram determinant's
Bézout witness over the residue (`gramUnitRead`).  The output layer
is the band root `s` at `4s² + t² = 4` (`bandRootRead`, one
quadratic extension adjoined) with the band congruence carrying the
block's level pencil to the fiber pencil (`bandCongrRead` at
`split.congrZ`, the descent's own invertibility witness beside it —
the adjugate against the determinant off equal members, so every
count is fixed at `lem:inertia`), the result a polynomial matrix at
the shape `lem:cellcount`'s counts consume (`fiberPencilRead`,
produced at every window pair by `fiberPencil_produce` at the pair
descent `descT` with its adjugate `descTw`), which
`thm:trigpencil` reads as its symbol.

What the tier still asks for at the per-orbit layer is the
substitution of the band root's square into the congruenced
entries, `fiberPencilRead`'s named remainder.  The Gram tier reads
whole at the wrap frame: the determinant at `4L²` times the band
symbol (`gramDet_wrap`), the divided-cofactor witness at every
side (`gramUnit_wrap` at `deck.gramCof`), the composition on its
own — the band symbol against the joined cofactors at the swapped
side-parity constant (`bandCof_pCong`) — and the interiority's
factor read: an occupied-length factor of the deck symbol refuses
the band symbol's division, the equal-members case refused at
every stored root with the priced side read the lower side's half
(`bandFree_factor`).  The block's entries read at every stated
symbol: the symbol's operator compressed on the pair reads the
symbol's multiple of the doubled side at the top, its multiple of
the band symbol's multiple at the bottom, and the unit tail at
both crossed entries (`blockEntry_top`, `blockEntry_cross`,
`blockEntry_crossT`, `blockEntry_bot` — the datum and the chord
exchanged at the orthogonality alone, `band_chord_comm` with the
Horner recursion's own exchange `evalM_comm`), lem:fiberdec's
entries-to-chord-polynomials sentence at the wrap frame.  The
per-root site data live over
`lem:stagesplit`'s stored tower: the split certificate holds the
symbol's factors with every root's bracket (`splitRead` at
`extAt`, the sampled momenta rebuilt at `splitRead_momenta`), the
per-root tower joins the root's factor to the band quadratic over
it (`rootTower` at `bandModulus`) with `stagesplit.gWitnessRead`
the arithmetic's unit witness, and the batteries read the
depth-two arithmetic with the interiority's priced side at the
committed side.  The
squeeze's residue side stands at the splitting's own lists,
`lem:fiberdec`'s passage sentence for sentence: the joined list
`[orbitSum] ++ pairBase` is independent at the orbit's own count
(`orbitSplit_indep` — the sum's coefficient dies at the word's
value through the ones pairing, the tail splits at the
alternations with the two parts perpendicular, and the triangle
reads the coefficients up the coefficient rows' monic tops with
the image rows' dependency withdrawn at the fixed-member route,
`T w = T^(2m+2) w = (T²)^(m+1) w = w` at the wrap `T^L = 1`), the
width bound turns the count
into the span (`orbitSplit_span` at `elim.span_of_full`), the
pair base sits inside the root datum's kernel at the independence
(`rootBlock_wrap`), and a root-datum kernel member reads through
the pairs alone, its sum coordinate clearing at the word's value
`P_L(2) = L` off the unit (`rootBlock_span`).
The
perpendicularity is no longer among the asks, nor the self-pairing
beside it: `lem:fiberdec`'s independence-over-the-remainder-lists
passage stands at every side at once.  The doubling datum's
pairing against a column clears outright at every square matrix
(`perp_band` over `perpSwapAdj`, the tex's one transpose walk at
every swap-adjoint matrix: the transpose walk moves the matrix
across the pairing, the swap read exchanges it for the memberwise
swap, and the swapped action joins the matrix's own at the sum's
unit, so the pairing reads its own negation and is a unit tail
before any residue is taken — the doubling datum is swap-adjoint
at `band_swapAdj`), the wrap shift its own
instance (`perp_wrap`), and the column's self-pairing reads the
doubled side `2L`
(`deckColumn_selfPair`: the squares collect at the product
families `p_b² = p_{2b} + 2`, the doubled keys read the key list
once — the even keys outright, the odd keys at the upper wrap —
and the key list's own fold reads the symbol's multiple
`p_m P_L`, null at the residue).  The residue's wrap
identities are no longer among the asks — `deck.pFamN_wrapDown`,
`deck.pFamN_wrapUp` and `deck.pFamN_side` are general theorems
over the indices, and `deck.pCong_eval` reads them at a located
root — and the membership's recursion content is general besides:
the family recursion closes cyclically as a class read at every
key (`deck.pFamN_cycMid` at the interior keys, `deck.pFamN_cycBot`
and `deck.pFamN_cycTop` at the two boundary keys over the wraps).
The two residue spellings read one class: `colMemberRead` spells
the residue at `deck.redP`'s division remainder and the class reads
spell it at `deck.pCong`'s stated multiple, and the bridge stands
between them (`deck.redP_pCong`, `deck.redP_congr`,
`deck.pCong_of_redP`, with `prow_redP` the vector form) —
`lem:fiberdec`'s class-read sentence, the located-root read its
evaluation.  The divisor read is the value read, a repair: the
symbol's top representative drifts from `m = 3` on, so an equality
spelling refused every side beyond seven and the membership and
Gram reads were unsatisfiable there; the value read holds at every
side probed, the batteries run through side seven, and the display
is monic at every side outright (`deck.pSum_monic`, the tex's own
parity induction), so the membership and Gram reads carry no
divisor conjunct.  The membership read's identification of
the chord's entries on the orbit's translate list with the
recursion's
neighbour keys stands in general at the wrap shift (`tShift`, its
witness `sShift`): the chord of the shift's permutation matrix
carries the deck-family column to its own chord multiple over the
residue at every side (`colMember_wrap`, the base side's residue
carrier a point so that branch decides), the cyclic reads consumed
entry by entry through the bridge, and a window's lattice
translation meets the wrap shift at one kernel matrix identity per
window, the committed side's battery re-deriving the kernel's read
from the theorem across it.

The count squeeze `1 + 2m = L` reads at stated lists, the residue
side's own splitting.  The orbit's sum is the ones row at the side
(`orbitSum`), the pair base is the deck-family column's coefficient
rows (`pairBase` at `sliceAt`, one row per key below the residue's
top against its image under the doubling datum), and the two join
at the orbit's own count, one member on the unit fiber and two per
root block (`pairBase_len`).  The unit fiber's member sits there
whole.  The identification `D₁ᵀ D₁ + S = 2` of the datum `D₁` at
`1 + D₁ = T` holds at every translation whose matrix is orthogonal
(`ident_of`, the product `Tᵀ T = 1` expanding the datum's square
and the two memberwise swaps clearing against their own) and at the
wrap shift outright (`identRead_wrap`); the orbit's sum is the
fiber's own independent kernel member with its fixed read
(`unitFiber_wrap`, the permutation's row carrying one occupied key
at the witness); and a kernel member of the pair `(S : 2)`'s site
datum reads through the sum's list alone (`unitFiber_span`: the
datum's square pairs against itself at the identification, the
positive pairing withdraws it to `T v = v`, and the fixed read
carries one value along the orbit key by key at the witness's
predecessor).  The Horner read rides the same doubling — a
chord-doubled vector reads every polynomial at the evaluation's own
scale (`polyEval_fixed`, the matrix recursion matched to
`def:poly`'s step for step), so the deck symbol reads the orbit's
sum at the division display's `P_L(2) = L` — and the elimination
read's own width bound reads a full-length independent list
spanning (`elim.span_of_full`), the count frame the squeeze
consumes, with `lem:inertia`'s `rev_join` battery exhibiting
`1 + 2m = 5` at the side-five splitting.  The pair base's own side
runs on the column's Horner read: the chord carries the
deck-family column to a stated polynomial's own multiple over the
residue (`polyEval_column`, `colMember_wrap` iterated along the
Horner recursion, the fold kit riding the residue at
`poly.scaleDot`'s own reads — `scaleDot_pCong`, `scaleDot_mulOut`
and `scaleDot_scaleId` — with the
deck symbol's one-key shift closing the step), so at the symbol
itself the image residues are the symbol's own multiples, the null
class key by key.

The band root's square is not substituted into the
congruenced entries: `fiberPencilRead` states the root datum, the
congruence and the shape side by side, and the substitution tying
`s²` to the fiber pencil's entries asks for the two-variable
`(t, τ)` carrier that `thm:trigpencil` already names a gap — a
`split.PMat` entry is a polynomial in the level alone, so the
substituted entry has no object here to be.
-/

namespace fiberdec
open ground lattice fusion elim carrier

/-! The torus carrier: the site keys at positional base-`L`
arithmetic, the links at the key `(direction, site)`, the unit
squares per site and direction pair. -/

/-- The positional stride at a direction: the site keys' base-`L`
digit weight. -/
private def stride (L e : Nat) : Nat := L ^ e

/-- A site key's digit at a direction. -/
def digitAt (L e s : Nat) : Nat := s / stride L e % L

/-- The site key shifted by a stated count of steps along a
direction, the cycle closing at the side length. -/
private def shiftBy (L e j s : Nat) : Nat :=
  s - digitAt L e s * stride L e
    + (digitAt L e s + j) % L * stride L e

/-- The site key's one step along a direction. -/
def shiftSite (L e s : Nat) : Nat := shiftBy L e 1 s

/-- The site key's step read backwards along a direction, the
step's witness at the complementary count. -/
def shiftSiteInv (L e s : Nat) : Nat := shiftBy L e (L - 1) s

/-- The torus link key at a direction and a site. -/
private def linkAt (d L e s : Nat) : Nat := e * L ^ d + s

/-- The unit square at a site and a direction pair: the boundary a
closed word of four oriented links, the two crossed steps its
corners. -/
private def torusPlaq (d L e f s : Nat) : List (Nat × Bool) :=
  [(linkAt d L e s, true),
   (linkAt d L f (shiftSite L e s), true),
   (linkAt d L e (shiftSite L f s), false),
   (linkAt d L f s, false)]

/-- A site key's coordinate sum, the two-coloring's own read. -/
private def coordSum (d L s : Nat) : Nat :=
  (List.range d).foldl (fun acc e => acc + digitAt L e s) 0

/-- The torus window at a direction count and a side length: the
sites the naturals below `L^d`, the links `d · L^d` at the key
`(direction, site)`, the plaquettes the unit squares per site and
direction pair, and the coloring at the coordinate sum's parity. -/
def torusRegion (d L : Nat) : Region :=
  { links := d * L ^ d,
    verts := L ^ d,
    tail := (List.range d).flatMap (fun _ => List.range (L ^ d)),
    head := (List.range d).flatMap (fun e =>
      (List.range (L ^ d)).map (fun s => shiftSite L e s)),
    plaqs := (List.range (L ^ d)).flatMap (fun s =>
      (List.range d).flatMap (fun e =>
        (List.range d).filterMap (fun f =>
          if e < f then some (torusPlaq d L e f s) else none))),
    color := (List.range (L ^ d)).map (fun s => coordSum d L s % 2 == 0),
    tailLen := by
      show ((List.range d).flatMap
        (fun _ => List.range (L ^ d))).length = d * L ^ d
      rw [ground.length_flatMap (fun _ : Nat => List.range (L ^ d))
          (List.range d),
        ground.famFold_congr_all Nat.add 0
          (fun _ : Nat => (List.range (L ^ d)).length)
          (fun _ : Nat => L ^ d)
          (fun _ => ground.length_range (L ^ d)) (List.range d),
        ground.famFold_const (L ^ d) (List.range d),
        ground.length_range d],
    headLen := by
      show ((List.range d).flatMap
        (fun e => (List.range (L ^ d)).map
          (fun s => shiftSite L e s))).length = d * L ^ d
      rw [ground.length_flatMap
          (fun e : Nat => (List.range (L ^ d)).map
            (fun s => shiftSite L e s)) (List.range d),
        ground.famFold_congr_all Nat.add 0
          (fun e : Nat => ((List.range (L ^ d)).map
            (fun s => shiftSite L e s)).length)
          (fun _ : Nat => L ^ d)
          (fun _ => ground.length_mapRange _ (L ^ d))
          (List.range d),
        ground.famFold_const (L ^ d) (List.range d),
        ground.length_range d] }

/-! The chain carrier at one direction: `rem:dictionary`'s
plaquette chain, consecutive squares sharing one link around a
cycle of the stated length. -/

/-- The plaquette chain at the stated cycle length: `2L` vertices
in two rows, the `L` rungs at the keys below `L`, the `L` lower
rails next and the `L` upper rails last, the `L` squares each two
consecutive rungs with the two rails between them, and the coloring
at the row-and-column sum's parity. -/
def chainRegion (L : Nat) : Region :=
  { links := 3 * L,
    verts := 2 * L,
    tail := (List.range L).map (fun i => 2 * i)
      ++ (List.range L).map (fun i => 2 * i)
      ++ (List.range L).map (fun i => 2 * i + 1),
    head := (List.range L).map (fun i => 2 * i + 1)
      ++ (List.range L).map (fun i => 2 * ((i + 1) % L))
      ++ (List.range L).map (fun i => 2 * ((i + 1) % L) + 1),
    plaqs := (List.range L).map (fun i =>
      [(i, true), (2 * L + i, true), ((i + 1) % L, false),
       (L + i, false)]),
    color := (List.range (2 * L)).map (fun v => (v / 2 + v % 2) % 2 == 0),
    tailLen := by
      rw [ground.length_append, ground.length_append,
        ground.length_map, ground.length_map,
        ground.length_range, Nat.mul_comm 3 L,
        show L * 3 = 0 + L + L + L from rfl, Nat.zero_add],
    headLen := by
      rw [ground.length_append, ground.length_append,
        ground.length_map, ground.length_map, ground.length_map,
        ground.length_range, Nat.mul_comm 3 L,
        show L * 3 = 0 + L + L + L from rfl, Nat.zero_add] }

/-! The translation, one per direction: the shift of the site keys
at every link of the region, the direction fixed. -/

/-- The chain's link keys shifted by a stated count of steps: the
three key ranges move together at the one cycle. -/
private def chainBy (L j l : Nat) : Nat := l / L * L + (l % L + j) % L

/-- The chain's translation, the cycle's one step. -/
def chainTransl (L : Nat) : Nat → Nat := fun l => chainBy L 1 l

/-- The chain's translation read backwards, the step's witness at
the complementary count. -/
def chainTranslInv (L : Nat) : Nat → Nat := fun l => chainBy L (L - 1) l

/-- The chain's induced vertex permutation: the column steps, the
row fixed. -/
def chainVert (L : Nat) : Nat → Nat :=
  fun v => 2 * ((v / 2 + 1) % L) + v % 2

/-- The chain's induced vertex permutation read backwards: the
column step at the complementary count, the row fixed. -/
def chainVertInv (L : Nat) : Nat → Nat :=
  fun v => 2 * ((v / 2 + (L - 1)) % L) + v % 2

/-- The torus's link keys shifted by a stated count of steps along
a direction, the direction fixed. -/
private def torusBy (d L e j l : Nat) : Nat :=
  l / L ^ d * L ^ d + shiftBy L e j (l % L ^ d)

/-- The torus's translation along a direction, the one step. -/
def torusTransl (d L e : Nat) : Nat → Nat := fun l => torusBy d L e 1 l

/-- The torus's translation read backwards, the step's witness at
the complementary count. -/
def torusTranslInv (d L e : Nat) : Nat → Nat :=
  fun l => torusBy d L e (L - 1) l

/-! The translation's four reads, each decidable at stated data. -/

/-- One map carries a second to a third across the region's keys,
`con:lattice`'s composition clause at a moved direction: the
composite at either side one map. -/
def intertwineRead (R : Region) (g t t' : Nat → Nat) : Prop :=
  ((List.range R.links).all (fun l => g (t l) == t' (g l))) = true

instance (R : Region) (g t t' : Nat → Nat) :
    Decidable (intertwineRead R g t t') :=
  inferInstanceAs (Decidable (_ = _))

/-- The intertwining read at a key below the count. -/
theorem intertwineRead_at (R : Region) (g t t' : Nat → Nat)
    (h : intertwineRead R g t t') (l : Nat) (hl : l < R.links) :
    g (t l) = t' (g l) :=
  ground.beqEqOf (ground.all_range_read R.links h l hl)

/-- Two link maps compose to one map at either order on the
region's keys, `con:lattice`'s composition clause at the window:
the directions' composites one map, the intertwining read at a
direction carried to itself. -/
def commutesRead (R : Region) (t s : Nat → Nat) : Prop :=
  intertwineRead R t s s

instance (R : Region) (t s : Nat → Nat) :
    Decidable (commutesRead R t s) :=
  inferInstanceAs (Decidable (_ = _))

/-- The composition read at a key below the count. -/
theorem commutesRead_at (R : Region) (t s : Nat → Nat)
    (h : commutesRead R t s) (l : Nat) (hl : l < R.links) :
    t (s l) = s (t l) :=
  intertwineRead_at R t s s h l hl

/-- The permutation read: the map and its witness compose to the
identity at every link key both ways, each keeping the key
range. -/
def permRead (R : Region) (t s : Nat → Nat) : Prop :=
  ((List.range R.links).all (fun l =>
    (s (t l) == l) && (t (s l) == l)
      && (t l < R.links) && (s l < R.links))) = true

instance (R : Region) (t s : Nat → Nat) : Decidable (permRead R t s) :=
  inferInstanceAs (Decidable (_ = _))

/-- The induced vertex map's permutation read: the vertex map and
its witness compose to the identity at every vertex key both ways,
each keeping the vertex range. -/
def vertPermRead (R : Region) (v w : Nat → Nat) : Prop :=
  ((List.range R.verts).all (fun x =>
    (w (v x) == x) && (v (w x) == x)
      && (v x < R.verts) && (w x < R.verts))) = true

instance (R : Region) (v w : Nat → Nat) : Decidable (vertPermRead R v w) :=
  inferInstanceAs (Decidable (_ = _))

/-- The endpoint read transported: the moved link's tail and head
are the vertex map's values at the link's own. -/
def endsRead (R : Region) (t v : Nat → Nat) : Prop :=
  ground.pairIdxAll (fun l tl hd =>
    (ground.getAt 0 R.tail (t l) == v tl)
      && (ground.getAt 0 R.head (t l) == v hd))
    R.tail R.head 0 = true

instance (R : Region) (t v : Nat → Nat) : Decidable (endsRead R t v) :=
  inferInstanceAs (Decidable (_ = _))

/-- The plaquette read transported: every boundary word's image
under the map is a boundary word of the region, the map's
injectivity on the words its witness's own at `permRead`. -/
def plaqMoveRead (R : Region) (t : Nat → Nat) : Prop :=
  ((R.plaqs.map (fun p => p.map (fun e => (t e.1, e.2)))).all
    (fun w => R.plaqs.any (fun p => w == p))) = true

instance (R : Region) (t : Nat → Nat) : Decidable (plaqMoveRead R t) :=
  inferInstanceAs (Decidable (_ = _))

/-- The map's iterate at a stated count. -/
def iterAt (t : Nat → Nat) : Nat → Nat → Nat
  | 0, l => l
  | n + 1, l => iterAt t n (t l)

/-- The composite shift at a key list: the directions' iterated
steps at the stated counts, one composite map (`con:lattice`'s
composition clause, the keys' one composite). -/
def compShift (d L : Nat) (ks : List Nat) : Nat → Nat :=
  fun l => (List.range d).foldl (fun acc e =>
    iterAt (torusTransl d L e) (ground.getAt 0 ks e) acc) l

/-- The cycle read `T^n = 1`: the iterate at the stated count is
the identity on the key range. -/
def cycleRead (R : Region) (t : Nat → Nat) (n : Nat) : Prop :=
  ((List.range R.links).all (fun l => iterAt t n l == l)) = true

instance (R : Region) (t : Nat → Nat) (n : Nat) :
    Decidable (cycleRead R t n) :=
  inferInstanceAs (Decidable (_ = _))

/-! The index action: the link permutation relabels a
configuration, and the window's three reads sit at the index. -/

/-- The index action at a reversal family: the label at the
witness's key, dualized where the traversal reverses
(`con:lattice`'s two action fields, the orientation reversal
dualizing labels). -/
def dualConf {L : Type} (F : Data L) (s : Nat → Nat)
    (rev : Nat → Bool) (n : Nat) (a : List L) : List L :=
  (List.range n).map (fun l =>
    if rev l then F.dual (getAt F.unit a (s l))
    else getAt F.unit a (s l))

/-- The action on configurations: the label at a link key is the
one the witness's key held, the unoccupied keys reading the
interface's unit — the reversal-free instance. -/
def permConf {L : Type} (F : Data L) (s : Nat → Nat) (n : Nat)
    (a : List L) : List L :=
  dualConf F s (fun _ => false) n a

/-- The content fixed at the action, over a stated index: the
content is the support's Casimir fold and the action relabels the
support alone. -/
def dualContentFixed {L : Type} (F : Data L) (R : Region)
    (ix : List (List L)) (s : Nat → Nat) (rev : Nat → Bool) : Prop :=
  (ix.all (fun a =>
    contentN F (dualConf F s rev R.links a) == contentN F a)) = true

instance {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (s : Nat → Nat) (rev : Nat → Bool) :
    Decidable (dualContentFixed F R ix s rev) :=
  inferInstanceAs (Decidable (_ = _))

def contentFixed {L : Type} (F : Data L) (R : Region)
    (ix : List (List L)) (s : Nat → Nat) : Prop :=
  dualContentFixed F R ix s (fun _ => false)

instance {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (s : Nat → Nat) : Decidable (contentFixed F R ix s) :=
  inferInstanceAs (Decidable (dualContentFixed F R ix s _))

/-- The occupancy fixed at the action: the vertex data transport
along the vertex permutation the link permutation induces. -/
def dualOccFixed {L : Type} (F : Data L) (R : Region)
    (ix : List (List L)) (s : Nat → Nat) (rev : Nat → Bool) : Prop :=
  (ix.all (fun a =>
    occupied F R (dualConf F s rev R.links a) == occupied F R a)) = true

instance {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (s : Nat → Nat) (rev : Nat → Bool) :
    Decidable (dualOccFixed F R ix s rev) :=
  inferInstanceAs (Decidable (_ = _))

def occFixed {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (s : Nat → Nat) : Prop :=
  dualOccFixed F R ix s (fun _ => false)

instance {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (s : Nat → Nat) : Decidable (occFixed F R ix s) :=
  inferInstanceAs (Decidable (dualOccFixed F R ix s _))

/-- The index maps within itself at the action, the witness's own
action the read back. -/
def dualIdxFixed {L : Type} (F : Data L) (R : Region)
    (ix : List (List L)) (s : Nat → Nat) (rev : Nat → Bool) : Prop :=
  (ix.all (fun a =>
    carrier.confMem F (dualConf F s rev R.links a) ix)) = true

instance {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (s : Nat → Nat) (rev : Nat → Bool) :
    Decidable (dualIdxFixed F R ix s rev) :=
  inferInstanceAs (Decidable (_ = _))

def idxFixed {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (s : Nat → Nat) : Prop :=
  dualIdxFixed F R ix s (fun _ => false)

instance {L : Type} (F : Data L) (R : Region) (ix : List (List L))
    (s : Nat → Nat) : Decidable (idxFixed F R ix s) :=
  inferInstanceAs (Decidable (dualIdxFixed F R ix s _))

/-- The induced permutation matrix on a stated index with the unit
line at its head: the column at a configuration reads the one at
its image. -/
def dualMat {L : Type} (F : Data L) (ix : List (List L)) (n : Nat)
    (s : Nat → Nat) (rev : Nat → Bool) : Mat :=
  let ims := ix.map (fun a => dualConf F s rev n a)
  (BPair.ofPos Pos.one :: ix.map (fun _ => BPair.unit))
    :: ix.map (fun b =>
      BPair.unit :: ims.map (fun ia =>
        if eqConf F ia b then BPair.ofPos Pos.one
        else BPair.unit))

/-- The induced permutation matrix at the reversal-free instance,
the images read once per member. -/
def permMat {L : Type} (F : Data L) (ix : List (List L)) (n : Nat)
    (s : Nat → Nat) : Mat :=
  dualMat F ix n s (fun _ => false)

/-- The commuting read at a window matrix: the induced permutation
matrix's congruence fixes the matrix, `Pmᵀ H Pm = H` entrywise. -/
def commRead (Pm H : Mat) : Prop :=
  matOneValue (matMul (transposeM Pm) (matMul H Pm)) H

instance (Pm H : Mat) : Decidable (commRead Pm H) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-! The chord tier: the translation's own permutation matrix at the
key list, the polynomial at a matrix, the chord operator
`S := T + Tᵀ`, and the lemma's operator identities. -/

/-- The permutation matrix of a map on a stated key range: the
column at a key reads the row the map names, `con:places`' place
action written at the key list rather than at the index. -/
def permMatAt (n : Nat) (t : Nat → Nat) : Mat :=
  ground.matOf n n (fun i j =>
    if t j = i then BPair.ofNat 1 else BPair.unit)

/-- The polynomial's Horner read at a matrix of a stated order
(`def:poly`'s recursion `P = c + z Q`): the constant enters at the
weighted identity, the shifted family against the matrix. -/
def polyEvalM (p : poly.Poly) (M : Mat) (n : Nat) : Mat :=
  p.foldr (fun c acc =>
      matAdd (inertia.matScaleB c (inertia.idMat n)) (matMul M acc))
    (inertia.matScaleB BPair.unit (inertia.idMat n))

/-- The matrix's iterate at a stated key, the word's own power. -/
def matPow (M : Mat) (n : Nat) : Nat → Mat
  | 0 => inertia.idMat n
  | k + 1 => matMul M (matPow M n k)

/-- The geometric word `Σ_{a+b+1=L} T^b` at a stated cycle
length. -/
def wordSum (M : Mat) (n L : Nat) : Mat :=
  elim.msum n (matPow M n) (List.range L)

/-- The chord operator `S := T + Tᵀ`, symmetric at the transpose's
own closure. -/
def chordOp (Pm : Mat) : Mat := matAdd Pm (transposeM Pm)

/-- The lemma's word `X := T^m P_L(S)` at the deck symbol
(`deck.pSum`). -/
def chordWord (Pm : Mat) (n m : Nat) : Mat :=
  matMul (matPow Pm n m) (polyEvalM (deck.pSum m) (chordOp Pm) n)

/-- The translation's orthogonality read at the matrix level: the
two products at the identity, `T Tᵀ = 1` and `Tᵀ T = 1`
(`con:places`' transpose-is-inverse). -/
def orthRead (Pm : Mat) (n : Nat) : Prop :=
  matOneValue (matMul Pm (transposeM Pm)) (inertia.idMat n)
  ∧ matOneValue (matMul (transposeM Pm) Pm) (inertia.idMat n)

instance (Pm : Mat) (n : Nat) : Decidable (orthRead Pm n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The deck relation at the translation's matrix, `T² + 1 = S T`
(`def:deck`'s monic quadratic at the chord). -/
def deckOpRead (Pm : Mat) (n : Nat) : Prop :=
  matOneValue (matAdd (matMul Pm Pm) (inertia.idMat n))
    (matMul (chordOp Pm) Pm)

instance (Pm : Mat) (n : Nat) : Decidable (deckOpRead Pm n) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- The word identity at the operator, `Σ_{a+b+1=L} T^b = T^m P_L(S)`
at `2m+1 = L`: the geometric word reads its deck symbol. -/
def wordOpRead (Pm : Mat) (n m : Nat) : Prop :=
  matOneValue (wordSum Pm n (2 * m + 1)) (chordWord Pm n m)

instance (Pm : Mat) (n m : Nat) : Decidable (wordOpRead Pm n m) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- The word's two fixed reads at `T^L = 1`: the word is its own
`T`-multiple, `T X = X`, and the witness against that read gives
`Tᵀ X = X`. -/
def fixedWordRead (Pm : Mat) (n m : Nat) : Prop :=
  matOneValue (matMul Pm (chordWord Pm n m)) (chordWord Pm n m)
  ∧ matOneValue (matMul (transposeM Pm) (chordWord Pm n m))
      (chordWord Pm n m)

instance (Pm : Mat) (n m : Nat) : Decidable (fixedWordRead Pm n m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The annihilation `S P_L(S) = 2 P_L(S)`, the orthogonal `T^m`
cleared at its witness. -/
def annihRead (Pm : Mat) (n m : Nat) : Prop :=
  matOneValue
    (matMul (chordOp Pm) (polyEvalM (deck.pSum m) (chordOp Pm) n))
    (inertia.matScaleB (BPair.ofNat 2)
      (polyEvalM (deck.pSum m) (chordOp Pm) n))

instance (Pm : Mat) (n m : Nat) : Decidable (annihRead Pm n m) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-! The permutation matrix's own composition and power reads, the
place action written at the key list (`con:places`): the matrix of
a composed map is the matrices' product, the matrix of an iterate
is the matrix's power, and the identity map's matrix is the
identity.  Every entry read is `def:elim`'s one-index pairing — a
column of `permMatAt n s` carries its one occupied key at `s j`,
so the product's entry is the composite's own indicator — and the
range clause the maps carry is `permRead`'s own conjunct. -/

/-- The permutation matrix's row count is its order. -/
theorem length_permMatAt (n : Nat) (t : Nat → Nat) :
    (permMatAt n t).length = n :=
  ground.matOf_length n n _

/-- The permutation matrix's rows at its order. -/
theorem rowsLen_permMatAt (n : Nat) (t : Nat → Nat) :
    rowsLen n (permMatAt n t) :=
  elim.rowsLen_matOf n n _

/-- The permutation matrix's entry: the column at a key carries the
one occupied row the map names. -/
theorem getAt_permMatAt (n : Nat) (t : Nat → Nat) (i j : Nat)
    (hi : i < n) (hj : j < n) :
    ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (permMatAt n t) i) j
      = if t j = i then BPair.ofNat 1 else BPair.unit :=
  ground.matOf_entry ([] : List BPair) BPair.unit n n _ i j hi hj

/-- Two maps agreeing on the key range have the one permutation
matrix. -/
theorem permMatAt_congr (n : Nat) (t s : Nat → Nat)
    (h : ∀ j, j < n → t j = s j) : permMatAt n t = permMatAt n s :=
  ground.matOf_congr n n _ _ (fun i j _ hj => by rw [h j hj])

/-- The identity map's permutation matrix is the identity. -/
theorem permMatAt_id (n : Nat) :
    matOneValue (permMatAt n (fun l => l)) (inertia.idMat n) := by
  refine matOne_getAt _ _
    (by rw [length_permMatAt, inertia.idMat_len]) ?_
  intro i hi
  rw [length_permMatAt] at hi
  refine getAt_polyOne _ _
    (by rw [rowsLen_getAt (permMatAt n (fun l => l)) i
        (rowsLen_permMatAt n _) (by rw [length_permMatAt]; exact hi),
      rowsLen_getAt (inertia.idMat n) i (inertia.idMat_rows n)
        (by rw [inertia.idMat_len]; exact hi)]) ?_
  intro j hj
  rw [rowsLen_getAt (permMatAt n (fun l => l)) i (rowsLen_permMatAt n _)
    (by rw [length_permMatAt]; exact hi)] at hj
  rw [getAt_permMatAt n (fun l => l) i j hi hj,
    inertia.getAt_idMat n i j hi hj]
  exact BPair.oneValue_refl _

/-- A permutation matrix's column carries its one occupied key at
the map's value, every other key reading the sum's unit. -/
private theorem permCol_off (n : Nat) (s : Nat → Nat) (j q : Nat)
    (hj : j < n) (hq : q < n) (hne : ¬ q = s j) :
    (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) (transposeM (permMatAt n s)) j)
      q).oneValue BPair.unit := by
  rw [getAt_transposeM BPair.unit (permMatAt n s) (rowsLen_permMatAt n s)
      j q hj (by rw [length_permMatAt]; exact hq),
    getAt_permMatAt n s q j hq hj,
    if_neg (fun hc : s j = q => hne hc.symm)]
  exact BPair.oneValue_refl _

/-- The permutation matrices' product is the composite's, the
entries the one-index pairings of `def:elim` at the right factor's
own occupied key. -/
theorem permMatAt_mul (n : Nat) (t s : Nat → Nat)
    (hs : ∀ j, j < n → s j < n) :
    matOneValue (matMul (permMatAt n t) (permMatAt n s))
      (permMatAt n (fun l => t (s l))) := by
  have hSl : (permMatAt n s).length = n := length_permMatAt n s
  have hSt : (transposeM (permMatAt n s)).length = n :=
    transposeLen (permMatAt n s) (rowsLen_permMatAt n s) hSl
  have hStr : rowsLen n (transposeM (permMatAt n s)) :=
    rowsLen_cast hSl (rowsLen_transposeM (permMatAt n s))
  have hMl : (matMul (permMatAt n t) (permMatAt n s)).length = n :=
    (ground.length_map _ (permMatAt n t)).trans (length_permMatAt n t)
  refine matOne_getAt _ _ (by rw [hMl, length_permMatAt]) ?_
  intro i hi
  rw [hMl] at hi
  rw [getAt_matMul (permMatAt n t) (permMatAt n s) i
    (by rw [length_permMatAt]; exact hi)]
  refine getAt_polyOne _ _
    (by rw [ground.length_map, hSt,
      rowsLen_getAt (permMatAt n (fun l => t (s l))) i
        (rowsLen_permMatAt n _) (by rw [length_permMatAt]; exact hi)]) ?_
  intro j hj
  rw [ground.length_map, hSt] at hj
  rw [ground.getAt_map ([] : List BPair) BPair.unit
      (fun c => dotN (ground.getAt [] (permMatAt n t) i) c)
      (transposeM (permMatAt n s)) j (by rw [hSt]; exact hj),
    getAt_permMatAt n (fun l => t (s l)) i j hi hj]
  refine BPair.oneValue_trans
    (dotN_dotP (ground.getAt [] (permMatAt n t) i) _) ?_
  refine BPair.oneValue_trans
    (dotP_oneIndex (ground.getAt [] (permMatAt n t) i)
      (ground.getAt ([] : List BPair) (transposeM (permMatAt n s)) j)
      (s j)
      (by rw [rowsLen_getAt (permMatAt n t) i (rowsLen_permMatAt n t)
            (by rw [length_permMatAt]; exact hi),
          rowsLen_getAt (transposeM (permMatAt n s)) j hStr
            (by rw [hSt]; exact hj)])
      (by rw [rowsLen_getAt (transposeM (permMatAt n s)) j hStr
            (by rw [hSt]; exact hj)]
          exact hs j hj)
      (fun q hq hne => permCol_off n s j q hj
        (by rw [rowsLen_getAt (transposeM (permMatAt n s)) j hStr
              (by rw [hSt]; exact hj)] at hq
            exact hq) hne)) ?_
  rw [getAt_permMatAt n t i (s j) hi (hs j hj),
    getAt_transposeM BPair.unit (permMatAt n s) (rowsLen_permMatAt n s)
      j (s j) hj (by rw [length_permMatAt]; exact hs j hj),
    getAt_permMatAt n s (s j) j (hs j hj) hj, if_pos rfl]
  exact BPair.mul_ofNat_one _

/-- Commuting maps' matrices commute: the two products read the
one composite at either order (`con:lattice`'s composition clause
at the matrix level, `commutesRead`'s own consequence at the
window's width). -/
theorem permMatAt_comm (n : Nat) (t s : Nat → Nat)
    (ht : ∀ j, j < n → t j < n) (hs : ∀ j, j < n → s j < n)
    (h : ∀ l, l < n → t (s l) = s (t l)) :
    matOneValue (matMul (permMatAt n t) (permMatAt n s))
      (matMul (permMatAt n s) (permMatAt n t)) :=
  matOne_trans (permMatAt_mul n t s hs)
    (matOne_trans
      (permMatAt_congr n (fun l => t (s l)) (fun l => s (t l)) h
        ▸ matOne_refl (permMatAt n (fun l => s (t l))))
      (matOne_symm (permMatAt_mul n s t ht)))

/-- The iterate commutes with its own step. -/
theorem iterAt_step (t : Nat → Nat) : ∀ (k l : Nat),
    iterAt t k (t l) = t (iterAt t k l)
  | 0, _ => rfl
  | k + 1, l => iterAt_step t k (t l)

/-- The iterate keeps the key range its map keeps. -/
theorem iterAt_range (n : Nat) (t : Nat → Nat)
    (ht : ∀ j, j < n → t j < n) : ∀ (k j : Nat), j < n → iterAt t k j < n
  | 0, _, hj => hj
  | k + 1, j, hj => iterAt_range n t ht k (t j) (ht j hj)

/-- The witness's iterate inverts the map's on the range. -/
private theorem iterAt_inv (n : Nat) (t s : Nat → Nat)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l) :
    ∀ (k j : Nat), j < n → iterAt s k (iterAt t k j) = j
  | 0, _, _ => rfl
  | k + 1, j, hj => by
    show iterAt s k (s (iterAt t k (t j))) = j
    rw [iterAt_step t k j,
      hst (iterAt t k j) (iterAt_range n t ht k j hj)]
    exact iterAt_inv n t s ht hst k j hj

/-- At the cycle, the witness is the iterate one short of the
count. -/
private theorem cycle_inv (n L : Nat) (t s : Nat → Nat)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l)
    (hcyc : ∀ l, l < n → iterAt t (L + 1) l = l) :
    ∀ j, j < n → s j = iterAt t L j := by
  intro j hj
  have h1 : t (iterAt t L j) = j := by
    rw [← iterAt_step t L j]; exact hcyc j hj
  calc s j = s (t (iterAt t L j)) := by rw [h1]
    _ = iterAt t L j := hst _ (iterAt_range n t ht L j hj)

/-- The matrix power's shape at a square factor. -/
private theorem matPow_shape (n : Nat) (M : Mat) (hMl : M.length = n) :
    ∀ k : Nat, rowsLen n (matPow M n k) ∧ (matPow M n k).length = n
  | 0 => ⟨inertia.idMat_rows n, inertia.idMat_len n⟩
  | k + 1 =>
    ⟨rowsLen_cast
      (transposeLen (matPow M n k) (matPow_shape n M hMl k).1
        (matPow_shape n M hMl k).2)
      (rowsLen_matMul M (matPow M n k)),
     (ground.length_map _ M).trans hMl⟩

/-- The permutation matrix's power is the iterate's matrix, the
composition read carried along the count. -/
theorem permMatAt_pow (n : Nat) (t : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n) : ∀ k : Nat,
    matOneValue (matPow (permMatAt n t) n k) (permMatAt n (iterAt t k))
  | 0 => matOne_symm (permMatAt_id n)
  | k + 1 => by
    have hsh := matPow_shape n (permMatAt n t) (length_permMatAt n t) k
    refine matOne_trans
      (matMul_congrR (n := n) (k := n) (permMatAt n t)
        (matPow (permMatAt n t) n k) (permMatAt n (iterAt t k))
        hsh.1 (rowsLen_permMatAt n (iterAt t k)) hsh.2
        (length_permMatAt n (iterAt t k)) hn
        (permMatAt_pow n t hn ht k)) ?_
    refine matOne_trans
      (permMatAt_mul n t (iterAt t k) (iterAt_range n t ht k)) ?_
    rw [permMatAt_congr n (fun l => t (iterAt t k l)) (iterAt t (k + 1))
      (fun j _ => (iterAt_step t k j).symm)]
    exact matOne_refl _

/-- Two powers join at the counts' sum. -/
private theorem matPow_add (n : Nat) (M : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hn : 0 < n) : ∀ a b : Nat,
    matOneValue (matMul (matPow M n a) (matPow M n b))
      (matPow M n (a + b))
  | 0, b => by
    rw [Nat.zero_add b]
    exact inertia.idMat_matMul n (matPow M n b)
      (matPow_shape n M hMl b).1 (matPow_shape n M hMl b).2 hn
  | a + 1, b => by
    rw [Nat.add_right_comm a 1 b]
    have hsa := matPow_shape n M hMl a
    have hsb := matPow_shape n M hMl b
    have hsab := matPow_shape n M hMl (a + b)
    show matOneValue (matMul (matMul M (matPow M n a)) (matPow M n b))
      (matMul M (matPow M n (a + b)))
    refine matOne_trans
      (matMul_assoc M (matPow M n a) (matPow M n b)
        hMr hsa.1 hsb.1 hsa.2 hsb.2 hn hn) ?_
    have hml : (matMul (matPow M n a) (matPow M n b)).length = n := by
      have : (matMul (matPow M n a) (matPow M n b)).length
          = (matPow M n a).length := length_matMul _ _
      rw [this, hsa.2]
    exact matMul_congrR (n := n) (k := n) M
      (matMul (matPow M n a) (matPow M n b)) (matPow M n (a + b))
      (rowsLen_cast
        (length_transposeM (matPow M n b) hsb.1 (by rw [hsb.2]; exact hn))
        (rowsLen_matMul (matPow M n a) (matPow M n b)))
      hsab.1 hml hsab.2 hn (matPow_add n M hMl hMr hn a b)

/-- The power grows at the right factor as well. -/
private theorem matPow_succR (n : Nat) (M : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hn : 0 < n) : ∀ m : Nat,
    matOneValue (matMul (matPow M n m) M) (matPow M n (m + 1))
  | 0 =>
    matOne_trans (inertia.idMat_matMul n M hMr hMl hn)
      (matOne_symm (inertia.matMul_idR n M hMr hMl hn hn))
  | m + 1 => by
    have hsm := matPow_shape n M hMl m
    have hsm1 := matPow_shape n M hMl (m + 1)
    refine matOne_trans
      (matMul_assoc M (matPow M n m) M hMr hsm.1 hMr hsm.2 hMl hn hn) ?_
    have hml : (matMul (matPow M n m) M).length = n := by
      have h := length_matMul (matPow M n m) M
      rw [h, hsm.2]
    exact matMul_congrR (n := n) (k := n) M (matMul (matPow M n m) M)
      (matPow M n (m + 1))
      (rowsLen_cast (length_transposeM M hMr (by rw [hMl]; exact hn))
        (rowsLen_matMul (matPow M n m) M))
      hsm1.1 hml hsm1.2 hn (matPow_succR n M hMl hMr hn m)


/-- The translation's permutation read unpacked at a key: the two
composition reads with the two range clauses. -/
theorem permRead_at (R : Region) (t s : Nat → Nat) (h : permRead R t s)
    (l : Nat) (hl : l < R.links) :
    s (t l) = l ∧ t (s l) = l ∧ t l < R.links ∧ s l < R.links := by
  have hb := ground.all_range_read R.links h l hl
  have h1 := ground.andSplitB hb
  have h2 := ground.andSplitB h1.1
  have h3 := ground.andSplitB h2.1
  exact ⟨ground.beqEqOf h3.1, ground.beqEqOf h3.2,
    of_decide_eq_true h2.2, of_decide_eq_true h1.2⟩

/-- The translation's transpose is its witness's matrix
(`con:places`' transpose-is-inverse), the two composition reads
identifying the indicators key by key. -/
theorem transposeM_permMatAt (n : Nat) (t s : Nat → Nat)
    (hst : ∀ l, l < n → s (t l) = l) (hts : ∀ l, l < n → t (s l) = l) :
    transposeM (permMatAt n t) = permMatAt n s := by
  have hTl : (transposeM (permMatAt n t)).length = n :=
    transposeLen (permMatAt n t) (rowsLen_permMatAt n t)
      (length_permMatAt n t)
  refine ground.getAt_ext ([] : List BPair) _ _
    (by rw [hTl, length_permMatAt]) ?_
  intro i hi
  rw [hTl] at hi
  refine ground.getAt_ext BPair.unit _ _
    (by rw [rowsLen_getAt (transposeM (permMatAt n t)) i
        (rowsLen_cast (length_permMatAt n t)
          (rowsLen_transposeM (permMatAt n t))) (by rw [hTl]; exact hi),
      rowsLen_getAt (permMatAt n s) i (rowsLen_permMatAt n s)
        (by rw [length_permMatAt]; exact hi)]) ?_
  intro j hj
  rw [rowsLen_getAt (transposeM (permMatAt n t)) i
    (rowsLen_cast (length_permMatAt n t)
      (rowsLen_transposeM (permMatAt n t))) (by rw [hTl]; exact hi)] at hj
  rw [getAt_transposeM BPair.unit (permMatAt n t) (rowsLen_permMatAt n t)
      i j hi (by rw [length_permMatAt]; exact hj),
    getAt_permMatAt n t j i hj hi, getAt_permMatAt n s i j hi hj]
  by_cases h1 : t i = j
  · rw [if_pos h1, if_pos (show s j = i by rw [← h1]; exact hst i hi)]
  · rw [if_neg h1,
      if_neg (fun h2 : s j = i => h1 (by rw [← h2]; exact hts j hj))]

/-- At the cycle, the transpose is the power one short of the
count (`con:places`' transpose-is-inverse read at the iterate). -/
private theorem transpose_as_pow (n k : Nat) (t s : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l)
    (hts : ∀ l, l < n → t (s l) = l)
    (hcyc : ∀ l, l < n → iterAt t (k + 1) l = l) :
    matOneValue (transposeM (permMatAt n t))
      (matPow (permMatAt n t) n k) := by
  rw [transposeM_permMatAt n t s hst hts,
    permMatAt_congr n s (iterAt t k) (cycle_inv n k t s ht hst hcyc)]
  exact matOne_symm (permMatAt_pow n t hn ht k)

/-- The chord operator commutes past every power of its
translation: at the cycle both summands are powers. -/
private theorem chordOp_pow_comm (n k : Nat) (t s : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l)
    (hts : ∀ l, l < n → t (s l) = l)
    (hcyc : ∀ l, l < n → iterAt t (k + 1) l = l) (m : Nat) :
    matOneValue
      (matMul (chordOp (permMatAt n t)) (matPow (permMatAt n t) n m))
      (matMul (matPow (permMatAt n t) n m) (chordOp (permMatAt n t))) := by
  have hTl := length_permMatAt n t
  have hTr := rowsLen_permMatAt n t
  have hTtr : rowsLen n (transposeM (permMatAt n t)) :=
    rowsLen_cast hTl (rowsLen_transposeM (permMatAt n t))
  have hsm := matPow_shape n (permMatAt n t) hTl m
  have hsm1 := matPow_shape n (permMatAt n t) hTl (m + 1)
  have hskm := matPow_shape n (permMatAt n t) hTl (k + m)
  have hPtr : rowsLen n (transposeM (matPow (permMatAt n t) n m)) :=
    rowsLen_cast hsm.2 (rowsLen_transposeM (matPow (permMatAt n t) n m))
  have hmid1 : matOneValue
      (matMul (permMatAt n t) (matPow (permMatAt n t) n m))
      (matPow (permMatAt n t) n (m + 1)) := matOne_refl _
  have hmid2 : matOneValue
      (matMul (transposeM (permMatAt n t)) (matPow (permMatAt n t) n m))
      (matPow (permMatAt n t) n (k + m)) :=
    matOne_trans
      (matMul_congrL (transposeM (permMatAt n t))
        (matPow (permMatAt n t) n k) (matPow (permMatAt n t) n m)
        (transpose_as_pow n k t s hn ht hst hts hcyc))
      (matPow_add n (permMatAt n t) hTl hTr hn k m)
  have hmid2' : matOneValue
      (matMul (matPow (permMatAt n t) n m) (transposeM (permMatAt n t)))
      (matPow (permMatAt n t) n (k + m)) := by
    refine matOne_trans
      (matMul_congrR (n := n) (k := n) (matPow (permMatAt n t) n m)
        (transposeM (permMatAt n t)) (matPow (permMatAt n t) n k)
        hTtr (matPow_shape n (permMatAt n t) hTl k).1
        (length_transposeM (permMatAt n t) hTr (by rw [hTl]; exact hn))
        (matPow_shape n (permMatAt n t) hTl k).2 hn
        (transpose_as_pow n k t s hn ht hst hts hcyc)) ?_
    rw [Nat.add_comm k m] at hskm ⊢
    exact matPow_add n (permMatAt n t) hTl hTr hn m k
  refine matOne_trans
    (matMul_addL n (matPow (permMatAt n t) n m) hPtr (permMatAt n t)
      (transposeM (permMatAt n t)) hTr hTtr) ?_
  refine matOne_trans
    (matAdd_cong2 n _ _ (matPow (permMatAt n t) n (m + 1))
      (matPow (permMatAt n t) n (k + m))
      (rowsLen_cast (length_transposeM (matPow (permMatAt n t) n m)
        hsm.1 (by rw [hsm.2]; exact hn))
        (rowsLen_matMul (permMatAt n t) (matPow (permMatAt n t) n m)))
      (rowsLen_cast (length_transposeM (matPow (permMatAt n t) n m)
        hsm.1 (by rw [hsm.2]; exact hn))
        (rowsLen_matMul (transposeM (permMatAt n t))
          (matPow (permMatAt n t) n m)))
      hsm1.1 hskm.1 hmid1 hmid2) ?_
  refine matOne_symm ?_
  refine matOne_trans
    (matMul_addR (n := n) (permMatAt n t) (transposeM (permMatAt n t))
      hTr hTtr
      (hTl.trans (length_transposeM (permMatAt n t) hTr
        (by rw [hTl]; exact hn)).symm)
      (by rw [hTl]; exact hn) (matPow (permMatAt n t) n m)
      (rowsLen_cast hTl.symm hsm.1)) ?_
  exact matAdd_cong2 n _ _ (matPow (permMatAt n t) n (m + 1))
    (matPow (permMatAt n t) n (k + m))
    (rowsLen_cast (length_transposeM (permMatAt n t) hTr
      (by rw [hTl]; exact hn))
      (rowsLen_matMul (matPow (permMatAt n t) n m) (permMatAt n t)))
    (rowsLen_cast (length_transposeM (transposeM (permMatAt n t)) hTtr
      (by rw [length_transposeM (permMatAt n t) hTr
        (by rw [hTl]; exact hn)]; exact hn))
      (rowsLen_matMul (matPow (permMatAt n t) n m)
        (transposeM (permMatAt n t))))
    hsm1.1 hskm.1
    (matPow_succR n (permMatAt n t) hTl hTr hn m) hmid2'

/-- The witness power clears its translation power: the two
iterates compose to the identity on the range. -/
private theorem clearW_pow (n : Nat) (t s : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l) (m : Nat) :
    matOneValue
      (matMul (permMatAt n (iterAt s m)) (matPow (permMatAt n t) n m))
      (inertia.idMat n) := by
  have hsk := matPow_shape n (permMatAt n t) (length_permMatAt n t) m
  refine matOne_trans
    (matMul_congrR (n := n) (k := n) (permMatAt n (iterAt s m))
      (matPow (permMatAt n t) n m) (permMatAt n (iterAt t m))
      hsk.1 (rowsLen_permMatAt n (iterAt t m)) hsk.2
      (length_permMatAt n (iterAt t m)) hn
      (permMatAt_pow n t hn ht m)) ?_
  refine matOne_trans
    (permMatAt_mul n (iterAt s m) (iterAt t m)
      (iterAt_range n t ht m)) ?_
  rw [permMatAt_congr n (fun l => iterAt s m (iterAt t m l))
    (fun l => l) (iterAt_inv n t s ht hst m)]
  exact permMatAt_id n

/-- Powers wrap at the cycle: a full turn clears. -/
private theorem matPow_wrap (n k : Nat) (t : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n)
    (hcyc : ∀ l, l < n → iterAt t (k + 1) l = l) (a : Nat) :
    matOneValue (matPow (permMatAt n t) n ((k + 1) + a))
      (matPow (permMatAt n t) n a) := by
  have hTl := length_permMatAt n t
  have hTr := rowsLen_permMatAt n t
  have hsa := matPow_shape n (permMatAt n t) hTl a
  have hsk := matPow_shape n (permMatAt n t) hTl (k + 1)
  refine matOne_trans
    (matOne_symm (matPow_add n (permMatAt n t) hTl hTr hn (k + 1) a)) ?_
  refine matOne_trans
    (matMul_congrL (matPow (permMatAt n t) n (k + 1))
      (inertia.idMat n) (matPow (permMatAt n t) n a) ?_) ?_
  · refine matOne_trans (permMatAt_pow n t hn ht (k + 1)) ?_
    rw [permMatAt_congr n (iterAt t (k + 1)) (fun l => l) hcyc]
    exact permMatAt_id n
  · exact inertia.idMat_matMul n (matPow (permMatAt n t) n a)
      hsa.1 hsa.2 hn

/-- The chord against a positive power: the neighbor pair, the
shift read's own matrix instance. -/
private theorem chord_mul_pow (n k : Nat) (t s : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l)
    (hts : ∀ l, l < n → t (s l) = l)
    (hcyc : ∀ l, l < n → iterAt t (k + 1) l = l) (a : Nat) :
    matOneValue
      (matMul (chordOp (permMatAt n t))
        (matPow (permMatAt n t) n (a + 1)))
      (matAdd (matPow (permMatAt n t) n (a + 2))
        (matPow (permMatAt n t) n a)) := by
  have hTl := length_permMatAt n t
  have hTr := rowsLen_permMatAt n t
  have hTtr : rowsLen n (transposeM (permMatAt n t)) :=
    rowsLen_cast hTl (rowsLen_transposeM (permMatAt n t))
  have hsa1 := matPow_shape n (permMatAt n t) hTl (a + 1)
  have hsa2 := matPow_shape n (permMatAt n t) hTl (a + 2)
  have hsa := matPow_shape n (permMatAt n t) hTl a
  have hska := matPow_shape n (permMatAt n t) hTl (k + (a + 1))
  refine matOne_trans
    (matMul_addL n (matPow (permMatAt n t) n (a + 1))
      (rowsLen_cast hsa1.2
        (rowsLen_transposeM (matPow (permMatAt n t) n (a + 1))))
      (permMatAt n t) (transposeM (permMatAt n t)) hTr hTtr) ?_
  refine matAdd_cong2 n _ _ (matPow (permMatAt n t) n (a + 2))
    (matPow (permMatAt n t) n a)
    (rowsLen_cast (length_transposeM (matPow (permMatAt n t) n (a + 1))
      hsa1.1 (by rw [hsa1.2]; exact hn))
      (rowsLen_matMul (permMatAt n t)
        (matPow (permMatAt n t) n (a + 1))))
    (rowsLen_cast (length_transposeM (matPow (permMatAt n t) n (a + 1))
      hsa1.1 (by rw [hsa1.2]; exact hn))
      (rowsLen_matMul (transposeM (permMatAt n t))
        (matPow (permMatAt n t) n (a + 1))))
    hsa2.1 hsa.1 (matOne_refl _) ?_
  refine matOne_trans
    (matMul_congrL (transposeM (permMatAt n t))
      (matPow (permMatAt n t) n k) (matPow (permMatAt n t) n (a + 1))
      (transpose_as_pow n k t s hn ht hst hts hcyc)) ?_
  refine matOne_trans
    (matPow_add n (permMatAt n t) hTl hTr hn k (a + 1)) ?_
  have hidx : k + (a + 1) = (k + 1) + a := by
    rw [Nat.add_comm k (a + 1), Nat.add_comm (k + 1) a,
      Nat.add_assoc a 1 k, Nat.add_comm 1 k]
  rw [hidx]
  exact matPow_wrap n k t hn ht hcyc a

/-- The translation is orthogonal: at the permutation read its
matrix's two products with its transpose are the identity, the
transpose the witness's own matrix (`lem:fiberdec`'s isometry
clause). -/
theorem permRead_orth (R : Region) (t s : Nat → Nat)
    (h : permRead R t s) :
    orthRead (permMatAt R.links t) R.links := by
  have hT : transposeM (permMatAt R.links t) = permMatAt R.links s :=
    transposeM_permMatAt R.links t s
      (fun l hl => (permRead_at R t s h l hl).1)
      (fun l hl => (permRead_at R t s h l hl).2.1)
  constructor
  · rw [hT]
    refine matOne_trans
      (permMatAt_mul R.links t s
        (fun l hl => (permRead_at R t s h l hl).2.2.2)) ?_
    rw [permMatAt_congr R.links (fun l => t (s l)) (fun l => l)
      (fun l hl => (permRead_at R t s h l hl).2.1)]
    exact permMatAt_id R.links
  · rw [hT]
    refine matOne_trans
      (permMatAt_mul R.links s t
        (fun l hl => (permRead_at R t s h l hl).2.2.1)) ?_
    rw [permMatAt_congr R.links (fun l => s (t l)) (fun l => l)
      (fun l hl => (permRead_at R t s h l hl).1)]
    exact permMatAt_id R.links

/-- The cycle read carried to the matrix: at `T^L = 1` on the key
range the translation's matrix reads the identity at its `L`-th
power, the tex's own `T^L = 1` (`lem:fiberdec`). -/
theorem cycleRead_pow (R : Region) (t s : Nat → Nat) (L : Nat)
    (hn : 0 < R.links) (h : permRead R t s) (hc : cycleRead R t L) :
    matOneValue (matPow (permMatAt R.links t) R.links L)
      (inertia.idMat R.links) := by
  refine matOne_trans
    (permMatAt_pow R.links t hn
      (fun l hl => (permRead_at R t s h l hl).2.2.1) L) ?_
  rw [permMatAt_congr R.links (iterAt t L) (fun l => l)
    (fun l hl => ground.beqEqOf
      (ground.all_range_read R.links hc l hl))]
  exact permMatAt_id R.links

/-! The word's two fixed reads at the fold kit, `lem:fiberdec`'s
`T X = X` and `Tᵀ X = X` as general theorems.  The geometric word
is the matrix-valued index fold at the powers (`elim.msum`), so its
`T`-multiple is the shifted family's fold, which reads the family's
own once the wrapped `T^L` reads `T^0` — the cycle read's own
consequence (`cycleRead_pow`).  The witness's read follows at the
orthogonality alone (`inertia.fixed_transpose`, the product's left
congruence against the identity's own product). -/

/-- The polynomial's read at a matrix keeps the matrix's shape. -/
private theorem evalM_shape (n : Nat) (M : Mat) (hM : rowsLen n M)
    (hMl : M.length = n) (hn : 0 < n) : ∀ p : poly.Poly,
    rowsLen n (polyEvalM p M n) ∧ (polyEvalM p M n).length = n
  | [] =>
    ⟨inertia.rowsLen_scaleB BPair.unit n (inertia.idMat n)
      (inertia.idMat_rows n),
     (inertia.length_scaleB BPair.unit (inertia.idMat n)).trans
       (inertia.idMat_len n)⟩
  | c :: p => by
    have ih := evalM_shape n M hM hMl hn p
    have hsc : rowsLen n (inertia.matScaleB c (inertia.idMat n)) :=
      inertia.rowsLen_scaleB c n (inertia.idMat n) (inertia.idMat_rows n)
    have hscl : (inertia.matScaleB c (inertia.idMat n)).length = n :=
      (inertia.length_scaleB c (inertia.idMat n)).trans (inertia.idMat_len n)
    have hprod : rowsLen n (matMul M (polyEvalM p M n)) :=
      rowsLen_cast
        (length_transposeM (polyEvalM p M n) ih.1 (by rw [ih.2]; exact hn))
        (rowsLen_matMul M (polyEvalM p M n))
    have hprodl : (matMul M (polyEvalM p M n)).length = n :=
      (length_matMul M (polyEvalM p M n)).trans hMl
    exact ⟨rowsLen_matAdd n _ _ hsc hprod,
      (length_matAdd _ _ (hscl.trans hprodl.symm)).trans hscl⟩


private theorem vecScaleB_unit_null : ∀ r : List BPair,
    poly.oneValue (poly.scaleP BPair.unit r)
      (List.replicate r.length BPair.unit)
  | [] => trivial
  | b :: r =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue (BPair.unit * b))
      (BPair.unit_mul b),
     vecScaleB_unit_null r⟩

private theorem scaleB_unit_null {n : Nat} : ∀ X : Mat,
    rowsLen n X →
    matOneValue (inertia.matScaleB BPair.unit X)
      (elim.nullMat X.length n)
  | [], _ => trivial
  | r :: X, hX => by
    refine ⟨?_, scaleB_unit_null X hX.2⟩
    show poly.oneValue (poly.scaleP BPair.unit r)
      (List.replicate n BPair.unit)
    rw [← hX.1]
    exact vecScaleB_unit_null r

/-- A unit-tailed symbol evaluates to the null matrix. -/
private theorem evalM_unitTail (n : Nat) (M : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hn : 0 < n) : ∀ p : poly.Poly,
    poly.unitTail p →
    matOneValue (polyEvalM p M n) (elim.nullMat n n)
  | [], _ => by
    show matOneValue (inertia.matScaleB BPair.unit (inertia.idMat n))
      (elim.nullMat n n)
    have h := scaleB_unit_null (n := n) (inertia.idMat n)
      (inertia.idMat_rows n)
    rw [inertia.idMat_len n] at h
    exact h
  | c :: p, hp => by
    show matOneValue
      (matAdd (inertia.matScaleB c (inertia.idMat n))
        (matMul M (polyEvalM p M n)))
      (elim.nullMat n n)
    have hep := evalM_shape n M hMr hMl hn p
    have h1 : matOneValue (inertia.matScaleB c (inertia.idMat n))
        (elim.nullMat n n) := by
      refine matOne_trans
        (inertia.matScaleB_congr hp.1 (inertia.idMat n)) ?_
      have h := scaleB_unit_null (n := n) (inertia.idMat n)
        (inertia.idMat_rows n)
      rw [inertia.idMat_len n] at h
      exact h
    have h2 : matOneValue (matMul M (polyEvalM p M n))
        (elim.nullMat n n) := by
      refine matOne_trans
        (matMul_congrR (n := n) (k := n) M (polyEvalM p M n)
          (elim.nullMat n n) hep.1 (elim.rowsLen_nullMat n n)
          hep.2 (elim.length_nullMat n n) hn
          (evalM_unitTail n M hMl hMr hn p hp.2)) ?_
      exact elim.matMul_nullMat n M hMl
    refine matOne_trans
      (matAdd_cong2 n _ _ (elim.nullMat n n) (elim.nullMat n n)
        (inertia.rowsLen_scaleB c n (inertia.idMat n)
          (inertia.idMat_rows n))
        (rowsLen_cast (length_transposeM (polyEvalM p M n) hep.1
          (by rw [hep.2]; exact hn))
          (rowsLen_matMul M (polyEvalM p M n)))
        (elim.rowsLen_nullMat n n) (elim.rowsLen_nullMat n n)
        h1 h2) ?_
    exact elim.matAdd_nullL (elim.nullMat n n) (elim.nullMat n n)
      (elim.matNull_nullMat n n)
      rfl (elim.rowsLen_nullMat n n) (elim.rowsLen_nullMat n n)

/-- The evaluation respects the symbols' one-value read. -/
private theorem evalM_congr (n : Nat) (M : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hn : 0 < n) : ∀ p q : poly.Poly,
    poly.oneValue p q →
    matOneValue (polyEvalM p M n) (polyEvalM q M n)
  | [], q, h =>
    matOne_trans (evalM_unitTail n M hMl hMr hn [] trivial)
      (matOne_symm (evalM_unitTail n M hMl hMr hn q h))
  | c :: p, [], h =>
    matOne_trans (evalM_unitTail n M hMl hMr hn (c :: p) h)
      (matOne_symm (evalM_unitTail n M hMl hMr hn [] trivial))
  | c :: p, d :: q, h => by
    have hep := evalM_shape n M hMr hMl hn p
    have heq := evalM_shape n M hMr hMl hn q
    show matOneValue
      (matAdd (inertia.matScaleB c (inertia.idMat n))
        (matMul M (polyEvalM p M n)))
      (matAdd (inertia.matScaleB d (inertia.idMat n))
        (matMul M (polyEvalM q M n)))
    refine matAdd_cong2 n _ _ _ _
      (inertia.rowsLen_scaleB c n (inertia.idMat n)
        (inertia.idMat_rows n))
      (rowsLen_cast (length_transposeM (polyEvalM p M n) hep.1
        (by rw [hep.2]; exact hn))
        (rowsLen_matMul M (polyEvalM p M n)))
      (inertia.rowsLen_scaleB d n (inertia.idMat n)
        (inertia.idMat_rows n))
      (rowsLen_cast (length_transposeM (polyEvalM q M n) heq.1
        (by rw [heq.2]; exact hn))
        (rowsLen_matMul M (polyEvalM q M n)))
      (inertia.matScaleB_congr h.1 (inertia.idMat n)) ?_
    exact matMul_congrR (n := n) (k := n) M (polyEvalM p M n)
      (polyEvalM q M n) hep.1 heq.1 hep.2 heq.2 hn
      (evalM_congr n M hMl hMr hn p q h.2)

/-- The evaluation is additive over the symbols' sum. -/
private theorem evalM_add (n : Nat) (M : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hn : 0 < n) : ∀ p q : poly.Poly,
    matOneValue (polyEvalM (poly.add p q) M n)
      (matAdd (polyEvalM p M n) (polyEvalM q M n))
  | [], q => by
    show matOneValue (polyEvalM q M n)
      (matAdd (inertia.matScaleB BPair.unit (inertia.idMat n))
        (polyEvalM q M n))
    have heq := evalM_shape n M hMr hMl hn q
    have hsb : matOneValue
        (inertia.matScaleB BPair.unit (inertia.idMat n))
        (elim.nullMat n n) := by
      have h := scaleB_unit_null (n := n) (inertia.idMat n)
        (inertia.idMat_rows n)
      rw [inertia.idMat_len n] at h
      exact h
    refine matOne_symm (matOne_trans
      (matAdd_cong2 n _ _ (elim.nullMat n n) (polyEvalM q M n)
        (inertia.rowsLen_scaleB BPair.unit n (inertia.idMat n)
          (inertia.idMat_rows n))
        heq.1 (elim.rowsLen_nullMat n n) heq.1
        hsb (matOne_refl _)) ?_)
    exact elim.matAdd_nullL (elim.nullMat n n) (polyEvalM q M n)
      (elim.matNull_nullMat n n)
      ((elim.length_nullMat n n).trans heq.2.symm)
      (elim.rowsLen_nullMat n n) heq.1
  | c :: p, [] => by
    show matOneValue (polyEvalM (c :: p) M n)
      (matAdd (polyEvalM (c :: p) M n)
        (inertia.matScaleB BPair.unit (inertia.idMat n)))
    rw [matAdd_comm]
    have hcp := evalM_shape n M hMr hMl hn (c :: p)
    have hsb : matOneValue
        (inertia.matScaleB BPair.unit (inertia.idMat n))
        (elim.nullMat n n) := by
      have h := scaleB_unit_null (n := n) (inertia.idMat n)
        (inertia.idMat_rows n)
      rw [inertia.idMat_len n] at h
      exact h
    refine matOne_symm (matOne_trans
      (matAdd_cong2 n _ _ (elim.nullMat n n) (polyEvalM (c :: p) M n)
        (inertia.rowsLen_scaleB BPair.unit n (inertia.idMat n)
          (inertia.idMat_rows n))
        hcp.1 (elim.rowsLen_nullMat n n) hcp.1
        hsb (matOne_refl _)) ?_)
    exact elim.matAdd_nullL (elim.nullMat n n) (polyEvalM (c :: p) M n)
      (elim.matNull_nullMat n n)
      ((elim.length_nullMat n n).trans hcp.2.symm)
      (elim.rowsLen_nullMat n n) hcp.1
  | c :: p, d :: q => by
    have hep := evalM_shape n M hMr hMl hn p
    have heq := evalM_shape n M hMr hMl hn q
    have hea := evalM_shape n M hMr hMl hn (poly.add p q)
    show matOneValue
      (matAdd (inertia.matScaleB (c + d) (inertia.idMat n))
        (matMul M (polyEvalM (poly.add p q) M n)))
      (matAdd
        (matAdd (inertia.matScaleB c (inertia.idMat n))
          (matMul M (polyEvalM p M n)))
        (matAdd (inertia.matScaleB d (inertia.idMat n))
          (matMul M (polyEvalM q M n))))
    rw [matAdd_shuffle (inertia.matScaleB c (inertia.idMat n))
      (matMul M (polyEvalM p M n))
      (inertia.matScaleB d (inertia.idMat n))
      (matMul M (polyEvalM q M n))]
    have hMe : ∀ r : poly.Poly, rowsLen n (matMul M (polyEvalM r M n)) :=
      fun r =>
        rowsLen_cast (length_transposeM (polyEvalM r M n)
          (evalM_shape n M hMr hMl hn r).1
          (by rw [(evalM_shape n M hMr hMl hn r).2]; exact hn))
        (rowsLen_matMul M (polyEvalM r M n))
    refine matAdd_cong2 n _ _ _ _
      (inertia.rowsLen_scaleB (c + d) n (inertia.idMat n)
        (inertia.idMat_rows n))
      (hMe (poly.add p q))
      (rowsLen_matAdd n _ _
        (inertia.rowsLen_scaleB c n (inertia.idMat n)
          (inertia.idMat_rows n))
        (inertia.rowsLen_scaleB d n (inertia.idMat n)
          (inertia.idMat_rows n)))
      (rowsLen_matAdd n _ _ (hMe p) (hMe q))
      (matOne_symm (inertia.matScaleB_add c d (inertia.idMat n)))
      ?_
    have hlen : (matAdd (polyEvalM p M n) (polyEvalM q M n)).length
        = n := (elim.length_matAdd (polyEvalM p M n) (polyEvalM q M n)
          (hep.2.trans heq.2.symm)).trans hep.2
    exact matOne_trans
      (matMul_congrR (n := n) (k := n) M
        (polyEvalM (poly.add p q) M n)
        (matAdd (polyEvalM p M n) (polyEvalM q M n))
        hea.1 (rowsLen_matAdd n _ _ hep.1 heq.1)
        hea.2 hlen hn
        (evalM_add n M hMl hMr hn p q))
      (matMul_addR (n := n) (polyEvalM p M n) (polyEvalM q M n)
        hep.1 heq.1 (hep.2.trans heq.2.symm)
        (by rw [hep.2]; exact hn) M (rowsLen_cast hep.2.symm hMr))

/-- A unit head absorbs: the shifted symbol evaluates through the
product. -/
private theorem evalM_consUnit (n : Nat) (M : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hn : 0 < n) (p : poly.Poly) :
    matOneValue (polyEvalM (BPair.unit :: p) M n)
      (matMul M (polyEvalM p M n)) := by
  have hep := evalM_shape n M hMr hMl hn p
  have hsb : matOneValue
      (inertia.matScaleB BPair.unit (inertia.idMat n))
      (elim.nullMat n n) := by
    have h := scaleB_unit_null (n := n) (inertia.idMat n)
      (inertia.idMat_rows n)
    rw [inertia.idMat_len n] at h
    exact h
  have hMe : rowsLen n (matMul M (polyEvalM p M n)) :=
    rowsLen_cast (length_transposeM (polyEvalM p M n) hep.1
      (by rw [hep.2]; exact hn))
      (rowsLen_matMul M (polyEvalM p M n))
  show matOneValue
    (matAdd (inertia.matScaleB BPair.unit (inertia.idMat n))
      (matMul M (polyEvalM p M n)))
    (matMul M (polyEvalM p M n))
  refine matOne_trans
    (matAdd_cong2 n _ _ (elim.nullMat n n) (matMul M (polyEvalM p M n))
      (inertia.rowsLen_scaleB BPair.unit n (inertia.idMat n)
        (inertia.idMat_rows n))
      hMe (elim.rowsLen_nullMat n n) hMe
      hsb (matOne_refl _)) ?_
  refine elim.matAdd_nullL (elim.nullMat n n) (matMul M (polyEvalM p M n))
    (elim.matNull_nullMat n n) ?_ (elim.rowsLen_nullMat n n) hMe
  rw [elim.length_nullMat n n, length_matMul M (polyEvalM p M n), hMl]

/-- The chord variable's multiple evaluates through the product. -/
private theorem evalM_mulX (n : Nat) (M : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hn : 0 < n) (p : poly.Poly) :
    matOneValue (polyEvalM (poly.mul deck.wPoly p) M n)
      (matMul M (polyEvalM p M n)) :=
  matOne_trans
    (evalM_congr n M hMl hMr hn (poly.mul deck.wPoly p)
      (BPair.unit :: p) (deck.mulX_read p))
    (evalM_consUnit n M hMl hMr hn p)

/-- A constant symbol evaluates to its scaled identity. -/
private theorem evalM_const (n : Nat) (M : Mat) (hMl : M.length = n)
    (hn : 0 < n) (c : BPair) :
    matOneValue (polyEvalM [c] M n)
      (inertia.matScaleB c (inertia.idMat n)) := by
  show matOneValue
    (matAdd (inertia.matScaleB c (inertia.idMat n))
      (matMul M (inertia.matScaleB BPair.unit (inertia.idMat n))))
    (inertia.matScaleB c (inertia.idMat n))
  have hnl : matOneValue
      (matMul M (inertia.matScaleB BPair.unit (inertia.idMat n)))
      (elim.nullMat n n) := by
    refine matOne_trans
      (matMul_congrR (n := n) (k := n) M
        (inertia.matScaleB BPair.unit (inertia.idMat n))
        (elim.nullMat n n)
        (inertia.rowsLen_scaleB BPair.unit n (inertia.idMat n)
          (inertia.idMat_rows n))
        (elim.rowsLen_nullMat n n)
        ((inertia.length_scaleB BPair.unit (inertia.idMat n)).trans
          (inertia.idMat_len n))
        (elim.length_nullMat n n) hn
        (by
          have h := scaleB_unit_null (n := n) (inertia.idMat n)
            (inertia.idMat_rows n)
          rw [inertia.idMat_len n] at h
          exact h)) ?_
    exact elim.matMul_nullMat n M hMl
  rw [matAdd_comm]
  refine matOne_trans
    (matAdd_cong2 n _ _ (elim.nullMat n n)
      (inertia.matScaleB c (inertia.idMat n))
      (rowsLen_cast (length_transposeM
        (inertia.matScaleB BPair.unit (inertia.idMat n))
        (inertia.rowsLen_scaleB BPair.unit n (inertia.idMat n)
          (inertia.idMat_rows n))
        (by
          rw [(inertia.length_scaleB BPair.unit
            (inertia.idMat n)).trans (inertia.idMat_len n)]
          exact hn))
        (rowsLen_matMul M
          (inertia.matScaleB BPair.unit (inertia.idMat n))))
      (inertia.rowsLen_scaleB c n (inertia.idMat n)
        (inertia.idMat_rows n))
      (elim.rowsLen_nullMat n n)
      (inertia.rowsLen_scaleB c n (inertia.idMat n)
        (inertia.idMat_rows n))
      hnl (matOne_refl _)) ?_
  refine elim.matAdd_nullL (elim.nullMat n n) _
    (elim.matNull_nullMat n n) ?_
    (elim.rowsLen_nullMat n n)
    (inertia.rowsLen_scaleB c n (inertia.idMat n)
      (inertia.idMat_rows n))
  rw [elim.length_nullMat n n,
    (inertia.length_scaleB c (inertia.idMat n)).trans
      (inertia.idMat_len n)]

/-- The lemma's word keeps the translation's shape. -/
private theorem chordWord_shape (n m : Nat) (M : Mat) (hM : rowsLen n M)
    (hMl : M.length = n) (hn : 0 < n) :
    rowsLen n (chordWord M n m) ∧ (chordWord M n m).length = n := by
  have hE := evalM_shape n (chordOp M) (rowsLen_matAdd n M (transposeM M)
      hM (rowsLen_cast hMl (rowsLen_transposeM M)))
    ((length_matAdd M (transposeM M)
      (hMl.trans (transposeLen M hM hMl).symm)).trans hMl) hn (deck.pSum m)
  have hP := matPow_shape n M hMl m
  exact ⟨rowsLen_cast (length_transposeM _ hE.1 (by rw [hE.2]; exact hn))
      (rowsLen_matMul (matPow M n m) (polyEvalM (deck.pSum m) (chordOp M) n)),
    (length_matMul _ _).trans hP.2⟩

/-- The geometric word is its own translation multiple: the fold
against its `T`-multiple is the shifted family's fold, and the two
read one value once the wrapped `T^L` reads `T^0`
(`lem:fiberdec`'s `T X = X`). -/
theorem wordSum_fixed (n L : Nat) (M : Mat) (hM : rowsLen n M)
    (hMl : M.length = n) (hn : 0 < n)
    (hcyc : matOneValue (matPow M n L) (inertia.idMat n)) :
    matOneValue (matMul M (wordSum M n L)) (wordSum M n L) :=
  matOne_trans
    (elim.matMul_msum n M hM hMl hn (matPow M n) (matPow_shape n M hMl)
      (List.range L))
    (elim.msum_wrap n (matPow M n) (matPow_shape n M hMl) L hcyc)

/-- The word's two fixed reads at a translation of stated shape:
the word is its own `T`-multiple at the cycle read and its
witness's at the orthogonality, `fixedWordRead`'s content carried
onto the lemma's word by the word identity (`wordOpRead`, the
decidable read the batteries commit). -/
theorem fixedWord_of (n m : Nat) (M : Mat) (hM : rowsLen n M)
    (hMl : M.length = n) (hn : 0 < n)
    (hcyc : matOneValue (matPow M n (2 * m + 1)) (inertia.idMat n))
    (horth : matOneValue (matMul (transposeM M) M) (inertia.idMat n))
    (hword : wordOpRead M n m) : fixedWordRead M n m := by
  have hX := chordWord_shape n m M hM hMl hn
  have hWs := elim.msum_shape n (matPow M n) (matPow_shape n M hMl)
    (List.range (2 * m + 1))
  have hfix : matOneValue (matMul M (chordWord M n m)) (chordWord M n m) := by
    refine matOne_trans
      (matMul_congrR (n := n) (k := n) M (chordWord M n m)
        (wordSum M n (2 * m + 1)) hX.1 hWs.1 hX.2 hWs.2 hn
        (matOne_symm hword)) ?_
    exact matOne_trans (wordSum_fixed n (2 * m + 1) M hM hMl hn hcyc) hword
  exact ⟨hfix,
    inertia.fixed_transpose n M (chordWord M n m) hM hMl hn hX.1 hX.2
      horth hfix⟩

/-- The word's two fixed reads at a translation of the window: the
permutation read supplies the orthogonality and the cycle read the
wrapped power, so `fixedWordRead` is decided by the window's own
two reads and the word identity. -/
theorem fixedWord_perm (R : Region) (t s : Nat → Nat) (m : Nat)
    (hn : 0 < R.links) (hperm : permRead R t s)
    (hcyc : cycleRead R t (2 * m + 1))
    (hword : wordOpRead (permMatAt R.links t) R.links m) :
    fixedWordRead (permMatAt R.links t) R.links m :=
  fixedWord_of R.links m (permMatAt R.links t)
    (rowsLen_permMatAt R.links t) (length_permMatAt R.links t) hn
    (cycleRead_pow R t s (2 * m + 1) hn hperm hcyc)
    (permRead_orth R t s hperm).2 hword

private theorem double_entry (x : BPair) :
    (x + x).oneValue (BPair.ofNat 2 * x).norm :=
  BPair.oneValue_symm (BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.ofNat_add 1 1) (BPair.oneValue_refl x))
      (by
        rw [BPair.right_distrib, BPair.mul_comm (BPair.ofNat 1) x]
        exact BPair.add_congr (BPair.mul_ofNat_one x)
          (BPair.mul_ofNat_one x))))

private theorem vecAdd_double : ∀ r : List BPair,
    poly.oneValue (vecAdd r r)
      (poly.scaleP (BPair.ofNat 2) r)
  | [] => trivial
  | x :: t => ⟨double_entry x, vecAdd_double t⟩

private theorem matAdd_double : ∀ M : Mat,
    matOneValue (matAdd M M) (inertia.matScaleB (BPair.ofNat 2) M)
  | [] => trivial
  | r :: t => ⟨vecAdd_double r, matAdd_double t⟩

/-- The plus read at the operator: the deck family at the chord
operator reads the two matched powers, `def:deck`'s display at the
translation's own root pair. -/
private theorem plus_read (n k : Nat) (t s : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l)
    (hts : ∀ l, l < n → t (s l) = l)
    (hcyc : ∀ l, l < n → iterAt t (k + 1) l = l) :
    ∀ j b : Nat, j + b = k + 1 →
    matOneValue
      (polyEvalM (deck.pFamN j) (chordOp (permMatAt n t)) n)
      (matAdd (matPow (permMatAt n t) n j)
        (matPow (permMatAt n t) n b))
  | 0, b, h => by
    have hb : b = k + 1 := by rw [← Nat.zero_add b]; exact h
    rw [hb]
    have hTl := length_permMatAt n t
    have hSl : (chordOp (permMatAt n t)).length = n :=
      (length_matAdd (permMatAt n t) (transposeM (permMatAt n t))
        (hTl.trans (length_transposeM (permMatAt n t)
          (rowsLen_permMatAt n t) (by rw [hTl]; exact hn)).symm)).trans
        hTl
    refine matOne_trans (evalM_const n (chordOp (permMatAt n t)) hSl hn
      (BPair.ofNat 2)) ?_
    refine matOne_trans (matOne_symm (matAdd_double (inertia.idMat n))) ?_
    exact matAdd_cong2 n _ _ (matPow (permMatAt n t) n 0)
      (matPow (permMatAt n t) n (k + 1))
      (inertia.idMat_rows n) (inertia.idMat_rows n)
      (inertia.idMat_rows n)
      (matPow_shape n (permMatAt n t) hTl (k + 1)).1
      (matOne_refl _)
      (matOne_symm (matPow_wrap n k t hn ht hcyc 0))
  | 1, b, h => by
    have h' : (0 + b) + 1 = k + 1 := by rw [← Nat.add_right_comm 0 1 b]; exact h
    have hb : b = k := by rw [← Nat.zero_add b]; exact Nat.succ.inj h'
    rw [hb]
    have hTl := length_permMatAt n t
    have hTr := rowsLen_permMatAt n t
    have hSr : rowsLen n (chordOp (permMatAt n t)) :=
      rowsLen_matAdd n _ _ hTr
        (rowsLen_cast hTl (rowsLen_transposeM (permMatAt n t)))
    have hSl : (chordOp (permMatAt n t)).length = n :=
      (length_matAdd (permMatAt n t) (transposeM (permMatAt n t))
        (hTl.trans (length_transposeM (permMatAt n t) hTr
          (by rw [hTl]; exact hn)).symm)).trans hTl
    refine matOne_trans
      (evalM_congr n (chordOp (permMatAt n t)) hSl hSr hn
        (deck.pFamN 1) deck.wPoly (by decide +kernel)) ?_
    refine matOne_trans
      (evalM_consUnit n (chordOp (permMatAt n t)) hSl hSr hn
        [BPair.ofPos .one]) ?_
    have hone : matOneValue
        (polyEvalM [BPair.ofPos .one] (chordOp (permMatAt n t)) n)
        (inertia.idMat n) := by
      refine matOne_trans
        (evalM_const n (chordOp (permMatAt n t)) hSl hn
          (BPair.ofPos .one)) ?_
      refine matOne_trans
        (inertia.matScaleB_congr
          (show (BPair.ofPos .one).oneValue (BPair.ofNat 1) by decide +kernel)
          (inertia.idMat n)) ?_
      exact inertia.matScaleB_one (inertia.idMat n)
    refine matOne_trans
      (matMul_congrR (n := n) (k := n) (chordOp (permMatAt n t))
        (polyEvalM [BPair.ofPos .one] (chordOp (permMatAt n t)) n)
        (inertia.idMat n)
        (evalM_shape n (chordOp (permMatAt n t)) hSr hSl hn
          [BPair.ofPos .one]).1
        (inertia.idMat_rows n)
        (evalM_shape n (chordOp (permMatAt n t)) hSr hSl hn
          [BPair.ofPos .one]).2
        (inertia.idMat_len n) hn hone) ?_
    refine matOne_trans
      (inertia.matMul_idR n (chordOp (permMatAt n t)) hSr hSl hn hn) ?_
    refine matAdd_cong2 n _ _ (matPow (permMatAt n t) n 1)
      (matPow (permMatAt n t) n k)
      hTr (rowsLen_cast hTl (rowsLen_transposeM (permMatAt n t)))
      (matPow_shape n (permMatAt n t) hTl 1).1
      (matPow_shape n (permMatAt n t) hTl k).1
      (matOne_symm (inertia.matMul_idR n (permMatAt n t) hTr hTl hn hn))
      (transpose_as_pow n k t s hn ht hst hts hcyc)
  | j + 2, b, h => by
    have hTl := length_permMatAt n t
    have hTr := rowsLen_permMatAt n t
    have hSr : rowsLen n (chordOp (permMatAt n t)) :=
      rowsLen_matAdd n _ _ hTr
        (rowsLen_cast hTl (rowsLen_transposeM (permMatAt n t)))
    have hSl : (chordOp (permMatAt n t)).length = n :=
      (length_matAdd (permMatAt n t) (transposeM (permMatAt n t))
        (hTl.trans (length_transposeM (permMatAt n t) hTr
          (by rw [hTl]; exact hn)).symm)).trans hTl
    rw [Nat.add_right_comm (j + 1) 1 b, Nat.add_right_comm j 1 b] at h
    have hjb2 : j + (b + 2) = k + 1 := h
    have hjb1 : (j + 1) + (b + 1) = k + 1 := by
      rw [Nat.add_right_comm j 1 (b + 1)]; exact h
    have ih1 := plus_read n k t s hn ht hst hts hcyc j (b + 2) hjb2
    have ih2 := plus_read n k t s hn ht hst hts hcyc (j + 1) (b + 1)
      hjb1
    have hshape : ∀ a : Nat,
        rowsLen n (matPow (permMatAt n t) n a) ∧
        (matPow (permMatAt n t) n a).length = n :=
      fun a => matPow_shape n (permMatAt n t) hTl a
    have hev : ∀ r : poly.Poly,
        rowsLen n (polyEvalM r (chordOp (permMatAt n t)) n) ∧
        (polyEvalM r (chordOp (permMatAt n t)) n).length = n :=
      fun r => evalM_shape n (chordOp (permMatAt n t)) hSr hSl hn r
    have step1 : matOneValue
        (matAdd (polyEvalM (deck.pFamN j) (chordOp (permMatAt n t)) n)
          (polyEvalM (deck.pFamN (j + 2)) (chordOp (permMatAt n t)) n))
        (matAdd
          (polyEvalM (deck.pFamN j) (chordOp (permMatAt n t)) n)
          (matAdd (matPow (permMatAt n t) n (j + 2))
            (matPow (permMatAt n t) n b))) := by
      refine matOne_trans
        (matOne_symm (evalM_add n (chordOp (permMatAt n t)) hSl hSr hn
          (deck.pFamN j) (deck.pFamN (j + 2)))) ?_
      refine matOne_trans
        (evalM_congr n (chordOp (permMatAt n t)) hSl hSr hn
          (poly.add (deck.pFamN j) (deck.pFamN (j + 2)))
          (poly.mul deck.wPoly (deck.pFamN (j + 1)))
          (deck.pFamN_rec j)) ?_
      refine matOne_trans
        (evalM_mulX n (chordOp (permMatAt n t)) hSl hSr hn
          (deck.pFamN (j + 1))) ?_
      refine matOne_trans
        (matMul_congrR (n := n) (k := n) (chordOp (permMatAt n t))
          (polyEvalM (deck.pFamN (j + 1)) (chordOp (permMatAt n t)) n)
          (matAdd (matPow (permMatAt n t) n (j + 1))
            (matPow (permMatAt n t) n (b + 1)))
          (hev (deck.pFamN (j + 1))).1
          (rowsLen_matAdd n _ _ (hshape (j + 1)).1 (hshape (b + 1)).1)
          (hev (deck.pFamN (j + 1))).2
          ((elim.length_matAdd _ _ ((hshape (j + 1)).2.trans
            (hshape (b + 1)).2.symm)).trans (hshape (j + 1)).2)
          hn ih2) ?_
      refine matOne_trans
        (matMul_addR (n := n) (matPow (permMatAt n t) n (j + 1))
          (matPow (permMatAt n t) n (b + 1))
          (hshape (j + 1)).1 (hshape (b + 1)).1
          ((hshape (j + 1)).2.trans (hshape (b + 1)).2.symm)
          (by rw [(hshape (j + 1)).2]; exact hn)
          (chordOp (permMatAt n t))
          (rowsLen_cast (hshape (j + 1)).2.symm hSr)) ?_
      refine matOne_trans
        (matAdd_cong2 n _ _
          (matAdd (matPow (permMatAt n t) n (j + 2))
            (matPow (permMatAt n t) n j))
          (matAdd (matPow (permMatAt n t) n (b + 2))
            (matPow (permMatAt n t) n b))
          (rowsLen_cast (length_transposeM _ (hshape (j + 1)).1
            (by rw [(hshape (j + 1)).2]; exact hn))
            (rowsLen_matMul (chordOp (permMatAt n t))
              (matPow (permMatAt n t) n (j + 1))))
          (rowsLen_cast (length_transposeM _ (hshape (b + 1)).1
            (by rw [(hshape (b + 1)).2]; exact hn))
            (rowsLen_matMul (chordOp (permMatAt n t))
              (matPow (permMatAt n t) n (b + 1))))
          (rowsLen_matAdd n _ _ (hshape (j + 2)).1 (hshape j).1)
          (rowsLen_matAdd n _ _ (hshape (b + 2)).1 (hshape b).1)
          (chord_mul_pow n k t s hn ht hst hts hcyc j)
          (chord_mul_pow n k t s hn ht hst hts hcyc b)) ?_
      rw [matAdd_comm (matPow (permMatAt n t) n (j + 2))
        (matPow (permMatAt n t) n j),
        matAdd_shuffle (matPow (permMatAt n t) n j)
          (matPow (permMatAt n t) n (j + 2))
          (matPow (permMatAt n t) n (b + 2))
          (matPow (permMatAt n t) n b)]
      exact matAdd_cong2 n _ _
        (polyEvalM (deck.pFamN j) (chordOp (permMatAt n t)) n)
        (matAdd (matPow (permMatAt n t) n (j + 2))
          (matPow (permMatAt n t) n b))
        (rowsLen_matAdd n _ _ (hshape j).1 (hshape (b + 2)).1)
        (rowsLen_matAdd n _ _ (hshape (j + 2)).1 (hshape b).1)
        (hev (deck.pFamN j)).1
        (rowsLen_matAdd n _ _ (hshape (j + 2)).1 (hshape b).1)
        (matOne_symm ih1) (matOne_refl _)
    rw [matAdd_comm (polyEvalM (deck.pFamN j) (chordOp (permMatAt n t)) n)
        (polyEvalM (deck.pFamN (j + 2)) (chordOp (permMatAt n t)) n),
      matAdd_comm (polyEvalM (deck.pFamN j) (chordOp (permMatAt n t)) n)
        (matAdd (matPow (permMatAt n t) n (j + 2))
          (matPow (permMatAt n t) n b))] at step1
    exact matAdd_cancelR n _ _ _
      (hev (deck.pFamN (j + 2))).1
      (rowsLen_matAdd n _ _ (hshape (j + 2)).1 (hshape b).1)
      (hev (deck.pFamN j)).1
      ((hev (deck.pFamN (j + 2))).2.trans
        ((elim.length_matAdd _ _ ((hshape (j + 2)).2.trans
          (hshape b).2.symm)).trans (hshape (j + 2)).2).symm)
      ((hev (deck.pFamN (j + 2))).2.trans (hev (deck.pFamN j)).2.symm)
      step1


private theorem idxC : ∀ c r : Nat,
    ((c + (r + 1)) + r) + 1 = (c + 1) + (2 * r + 1)
  | _, 0 => rfl
  | c, r + 1 => by
    show ((((c + (r + 1)) + 1) + r) + 1) + 1
      = (((c + 1) + (2 * r + 1)) + 1) + 1
    rw [Nat.add_right_comm (c + (r + 1)) 1 r]
    show ((((c + (r + 1)) + r) + 1) + 1) + 1
      = (((c + 1) + (2 * r + 1)) + 1) + 1
    rw [idxC c r]

private theorem idxW : ∀ m c : Nat, m + (m + c + 1) = (2 * m + 1) + c
  | m, 0 => by rw [Nat.two_mul m]; rfl
  | m, c + 1 => by
    show (m + (m + c + 1)) + 1 = ((2 * m + 1) + c) + 1
    rw [idxW m c]

/-- The windowed word: the translated symbol collects the centered
power segment, `lem:fiberdec`'s grouping about the middle power. -/
private theorem seg_read (n m : Nat) (t s : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l)
    (hts : ∀ l, l < n → t (s l) = l)
    (hcyc : ∀ l, l < n → iterAt t (2 * m + 1) l = l) :
    ∀ (r c : Nat), c + r = m →
    matOneValue
      (matMul (matPow (permMatAt n t) n m)
        (polyEvalM (deck.pSum r) (chordOp (permMatAt n t)) n))
      (msum n (fun b => matPow (permMatAt n t) n (c + b))
        (List.range (2 * r + 1)))
  | 0, c, h => by
    have hc : c = m := h
    have hTl := length_permMatAt n t
    have hTr := rowsLen_permMatAt n t
    have hSr : rowsLen n (chordOp (permMatAt n t)) :=
      rowsLen_matAdd n _ _ hTr
        (rowsLen_cast hTl (rowsLen_transposeM (permMatAt n t)))
    have hSl : (chordOp (permMatAt n t)).length = n :=
      (length_matAdd (permMatAt n t) (transposeM (permMatAt n t))
        (hTl.trans (length_transposeM (permMatAt n t) hTr
          (by rw [hTl]; exact hn)).symm)).trans hTl
    have hsm := matPow_shape n (permMatAt n t) hTl m
    have hone : matOneValue
        (polyEvalM (deck.pSum 0) (chordOp (permMatAt n t)) n)
        (inertia.idMat n) := by
      refine matOne_trans
        (evalM_const n (chordOp (permMatAt n t)) hSl hn
          (BPair.ofPos .one)) ?_
      refine matOne_trans
        (inertia.matScaleB_congr
          (show (BPair.ofPos .one).oneValue (BPair.ofNat 1) by decide +kernel)
          (inertia.idMat n)) ?_
      exact inertia.matScaleB_one (inertia.idMat n)
    show matOneValue
      (matMul (matPow (permMatAt n t) n m)
        (polyEvalM (deck.pSum 0) (chordOp (permMatAt n t)) n))
      (msum n (fun b => matPow (permMatAt n t) n (c + b))
        (List.range 1))
    rw [show List.range 1 = [0] from rfl,
      msum_cons n (fun b => matPow (permMatAt n t) n (c + b)) 0 [],
      hc]
    refine matOne_trans
      (matMul_congrR (n := n) (k := n) (matPow (permMatAt n t) n m)
        (polyEvalM (deck.pSum 0) (chordOp (permMatAt n t)) n)
        (inertia.idMat n)
        (evalM_shape n (chordOp (permMatAt n t)) hSr hSl hn
          (deck.pSum 0)).1
        (inertia.idMat_rows n)
        (evalM_shape n (chordOp (permMatAt n t)) hSr hSl hn
          (deck.pSum 0)).2
        (inertia.idMat_len n) hn hone) ?_
    refine matOne_trans
      (inertia.matMul_idR n (matPow (permMatAt n t) n m)
        hsm.1 hsm.2 hn hn) ?_
    rw [matAdd_comm]
    refine matOne_symm ?_
    exact elim.matAdd_nullL (elim.nullMat n n)
      (matPow (permMatAt n t) n (m + 0))
      (elim.matNull_nullMat n n)
      ((elim.length_nullMat n n).trans
        (matPow_shape n (permMatAt n t) hTl (m + 0)).2.symm)
      (elim.rowsLen_nullMat n n)
      (matPow_shape n (permMatAt n t) hTl (m + 0)).1

  | r + 1, c, h => by
    have h' : (c + 1) + r = m := by rw [Nat.add_right_comm c 1 r]; exact h
    have hTl := length_permMatAt n t
    have hTr := rowsLen_permMatAt n t
    have hSr : rowsLen n (chordOp (permMatAt n t)) :=
      rowsLen_matAdd n _ _ hTr
        (rowsLen_cast hTl (rowsLen_transposeM (permMatAt n t)))
    have hSl : (chordOp (permMatAt n t)).length = n :=
      (length_matAdd (permMatAt n t) (transposeM (permMatAt n t))
        (hTl.trans (length_transposeM (permMatAt n t) hTr
          (by rw [hTl]; exact hn)).symm)).trans hTl
    have hshape : ∀ a : Nat,
        rowsLen n (matPow (permMatAt n t) n a) ∧
        (matPow (permMatAt n t) n a).length = n :=
      fun a => matPow_shape n (permMatAt n t) hTl a
    have hev : ∀ q : poly.Poly,
        rowsLen n (polyEvalM q (chordOp (permMatAt n t)) n) ∧
        (polyEvalM q (chordOp (permMatAt n t)) n).length = n :=
      fun q => evalM_shape n (chordOp (permMatAt n t)) hSr hSl hn q
    have hfc : ∀ c' : Nat, ∀ k : Nat,
        rowsLen n (matPow (permMatAt n t) n (c' + k)) ∧
        (matPow (permMatAt n t) n (c' + k)).length = n :=
      fun c' k => hshape (c' + k)
    have ih := seg_read n m t s hn ht hst hts hcyc r (c + 1) h'
    have hjb : (r + 1) + (m + c + 1) = 2 * m + 1 := by
      rw [← h, Nat.two_mul (c + (r + 1)),
        Nat.add_comm (r + 1) ((c + (r + 1)) + c + 1),
        ← Nat.add_assoc (c + (r + 1)) c (r + 1),
        Nat.add_assoc ((c + (r + 1)) + c) 1 (r + 1),
        Nat.add_comm 1 (r + 1)]
      rfl
    have hidxc : m + (r + 1) = (c + 1) + (2 * r + 1) := by
      rw [← h]; exact idxC c r
    have hidxw : m + (m + c + 1) = (2 * m + 1) + c := idxW m c
    have hwrap : matOneValue
        (matPow (permMatAt n t) n (m + (m + c + 1)))
        (matPow (permMatAt n t) n c) := by
      rw [hidxw]
      exact matPow_wrap n (2 * m) t hn ht hcyc c
    have hchain2 : matOneValue
        (matMul (matPow (permMatAt n t) n m)
          (polyEvalM (deck.pFamN (r + 1)) (chordOp (permMatAt n t)) n))
        (matAdd (matPow (permMatAt n t) n ((c + 1) + (2 * r + 1)))
          (matPow (permMatAt n t) n c)) := by
      refine matOne_trans
        (matMul_congrR (n := n) (k := n) (matPow (permMatAt n t) n m)
          (polyEvalM (deck.pFamN (r + 1)) (chordOp (permMatAt n t)) n)
          (matAdd (matPow (permMatAt n t) n (r + 1))
            (matPow (permMatAt n t) n (m + c + 1)))
          (hev (deck.pFamN (r + 1))).1
          (rowsLen_matAdd n _ _ (hshape (r + 1)).1
            (hshape (m + c + 1)).1)
          (hev (deck.pFamN (r + 1))).2
          ((elim.length_matAdd _ _ ((hshape (r + 1)).2.trans
            (hshape (m + c + 1)).2.symm)).trans (hshape (r + 1)).2)
          hn
          (plus_read n (2 * m) t s hn ht hst hts hcyc (r + 1)
            (m + c + 1) hjb)) ?_
      refine matOne_trans
        (matMul_addR (n := n) (matPow (permMatAt n t) n (r + 1))
          (matPow (permMatAt n t) n (m + c + 1))
          (hshape (r + 1)).1 (hshape (m + c + 1)).1
          ((hshape (r + 1)).2.trans (hshape (m + c + 1)).2.symm)
          (by rw [(hshape (r + 1)).2]; exact hn)
          (matPow (permMatAt n t) n m)
          (rowsLen_cast (hshape (r + 1)).2.symm (hshape m).1)) ?_
      refine matAdd_cong2 n _ _
        (matPow (permMatAt n t) n ((c + 1) + (2 * r + 1)))
        (matPow (permMatAt n t) n c)
        (rowsLen_cast (length_transposeM _ (hshape (r + 1)).1
          (by rw [(hshape (r + 1)).2]; exact hn))
          (rowsLen_matMul (matPow (permMatAt n t) n m)
            (matPow (permMatAt n t) n (r + 1))))
        (rowsLen_cast (length_transposeM _ (hshape (m + c + 1)).1
          (by rw [(hshape (m + c + 1)).2]; exact hn))
          (rowsLen_matMul (matPow (permMatAt n t) n m)
            (matPow (permMatAt n t) n (m + c + 1))))
        (hshape ((c + 1) + (2 * r + 1))).1 (hshape c).1 ?_ ?_
      · rw [← hidxc]
        exact matPow_add n (permMatAt n t) hTl hTr hn m (r + 1)
      · exact matOne_trans
          (matPow_add n (permMatAt n t) hTl hTr hn m (m + c + 1))
          hwrap
    show matOneValue
      (matMul (matPow (permMatAt n t) n m)
        (polyEvalM
          (poly.add (deck.pSum r) (deck.pFam (ground.posOfSucc r)))
          (chordOp (permMatAt n t)) n))
      (msum n (fun b => matPow (permMatAt n t) n (c + b))
        (List.range (2 * (r + 1) + 1)))
    have hseg : matOneValue
        (matMul (matPow (permMatAt n t) n m)
          (polyEvalM
            (poly.add (deck.pSum r) (deck.pFam (ground.posOfSucc r)))
            (chordOp (permMatAt n t)) n))
        (matAdd
          (msum n (fun b => matPow (permMatAt n t) n ((c + 1) + b))
            (List.range (2 * r + 1)))
          (matAdd
            (matPow (permMatAt n t) n ((c + 1) + (2 * r + 1)))
            (matPow (permMatAt n t) n c))) := by
      refine matOne_trans
        (matMul_congrR (n := n) (k := n) (matPow (permMatAt n t) n m)
          (polyEvalM
            (poly.add (deck.pSum r) (deck.pFam (ground.posOfSucc r)))
            (chordOp (permMatAt n t)) n)
          (matAdd (polyEvalM (deck.pSum r) (chordOp (permMatAt n t)) n)
            (polyEvalM (deck.pFam (ground.posOfSucc r))
              (chordOp (permMatAt n t)) n))
          (hev _).1
          (rowsLen_matAdd n _ _ (hev (deck.pSum r)).1
            (hev (deck.pFam (ground.posOfSucc r))).1)
          (hev _).2
          ((elim.length_matAdd _ _ ((hev (deck.pSum r)).2.trans
            (hev (deck.pFam (ground.posOfSucc r))).2.symm)).trans
            (hev (deck.pSum r)).2)
          hn
          (evalM_add n (chordOp (permMatAt n t)) hSl hSr hn
            (deck.pSum r) (deck.pFam (ground.posOfSucc r)))) ?_
      refine matOne_trans
        (matMul_addR (n := n)
          (polyEvalM (deck.pSum r) (chordOp (permMatAt n t)) n)
          (polyEvalM (deck.pFam (ground.posOfSucc r))
            (chordOp (permMatAt n t)) n)
          (hev (deck.pSum r)).1
          (hev (deck.pFam (ground.posOfSucc r))).1
          ((hev (deck.pSum r)).2.trans
            (hev (deck.pFam (ground.posOfSucc r))).2.symm)
          (by rw [(hev (deck.pSum r)).2]; exact hn)
          (matPow (permMatAt n t) n m)
          (rowsLen_cast (hev (deck.pSum r)).2.symm (hshape m).1)) ?_
      exact matAdd_cong2 n _ _
        (msum n (fun b => matPow (permMatAt n t) n ((c + 1) + b))
          (List.range (2 * r + 1)))
        (matAdd (matPow (permMatAt n t) n ((c + 1) + (2 * r + 1)))
          (matPow (permMatAt n t) n c))
        (rowsLen_cast (length_transposeM _ (hev (deck.pSum r)).1
          (by rw [(hev (deck.pSum r)).2]; exact hn))
          (rowsLen_matMul (matPow (permMatAt n t) n m)
            (polyEvalM (deck.pSum r) (chordOp (permMatAt n t)) n)))
        (rowsLen_cast (length_transposeM _
          (hev (deck.pFam (ground.posOfSucc r))).1
          (by rw [(hev (deck.pFam (ground.posOfSucc r))).2]; exact hn))
          (rowsLen_matMul (matPow (permMatAt n t) n m)
            (polyEvalM (deck.pFam (ground.posOfSucc r))
              (chordOp (permMatAt n t)) n)))
        (msum_shape n _ (hfc (c + 1)) (List.range (2 * r + 1))).1
        (rowsLen_matAdd n _ _ (hshape ((c + 1) + (2 * r + 1))).1
          (hshape c).1)
        ih hchain2
    rw [ground.range_succ (2 * (r + 1)),
      msum_append n (fun b => matPow (permMatAt n t) n (c + b))
        (List.range (2 * (r + 1))) (2 * (r + 1))]
    rw [show (2 * (r + 1) : Nat) = (2 * r + 1) + 1 from rfl,
      ← msum_shift n (fun b => matPow (permMatAt n t) n (c + b))
        ((2 * r + 1) + 1)]
    refine matOne_trans hseg ?_
    refine matOne_symm ?_
    rw [show c + 0 = c from rfl,
      ground.range_succ (2 * r + 1),
      msum_append n
        (fun b => matPow (permMatAt n t) n (c + (b + 1)))
        (List.range (2 * r + 1)) (2 * r + 1)]
    refine matOne_trans
      (matAdd_cong2 n _ _ (matPow (permMatAt n t) n c)
        (matAdd
          (msum n (fun b => matPow (permMatAt n t) n ((c + 1) + b))
            (List.range (2 * r + 1)))
          (matPow (permMatAt n t) n ((c + 1) + (2 * r + 1))))
        (hshape c).1
        (rowsLen_matAdd n _ _
          (msum_shape n _ (fun k => hshape (c + (k + 1)))
            (List.range (2 * r + 1))).1
          (hshape (c + ((2 * r + 1) + 1))).1)
        (hshape c).1
        (rowsLen_matAdd n _ _
          (msum_shape n _ (hfc (c + 1)) (List.range (2 * r + 1))).1
          (hshape ((c + 1) + (2 * r + 1))).1)
        (matOne_refl _)
        (matAdd_cong2 n _ _
          (msum n (fun b => matPow (permMatAt n t) n ((c + 1) + b))
            (List.range (2 * r + 1)))
          (matPow (permMatAt n t) n ((c + 1) + (2 * r + 1)))
          (msum_shape n _ (fun k => hshape (c + (k + 1)))
            (List.range (2 * r + 1))).1
          (hshape (c + ((2 * r + 1) + 1))).1
          (msum_shape n _ (hfc (c + 1)) (List.range (2 * r + 1))).1
          (hshape ((c + 1) + (2 * r + 1))).1
          (msum_congr n
            (fun b => matPow (permMatAt n t) n (c + (b + 1)))
            (fun b => matPow (permMatAt n t) n ((c + 1) + b))
            (fun k => hshape (c + (k + 1)))
            (hfc (c + 1))
            (fun k => by rw [Nat.add_right_comm c 1 k]; exact matOne_refl _)
            (List.range (2 * r + 1)))
          (by rw [Nat.add_right_comm c 1 (2 * r + 1)]; exact matOne_refl _))) ?_
    rw [matAdd_comm (matPow (permMatAt n t) n c)
        (matAdd
          (msum n (fun b => matPow (permMatAt n t) n ((c + 1) + b))
            (List.range (2 * r + 1)))
          (matPow (permMatAt n t) n ((c + 1) + (2 * r + 1)))),
      matAdd_assoc
        (msum n (fun b => matPow (permMatAt n t) n ((c + 1) + b))
          (List.range (2 * r + 1)))
        (matPow (permMatAt n t) n ((c + 1) + (2 * r + 1)))
        (matPow (permMatAt n t) n c)]
    exact matOne_refl _
/-- The deck relation at a translation's matrix: at the
orthogonality read the chord's product against `T` collects the
square and the identity, `T² + 1 = S T`, the product `Tᵀ T = 1`
collected (`def:deck`). -/
theorem chord_deck (n : Nat) (Pm : Mat) (hP : rowsLen n Pm)
    (hPt : rowsLen n (transposeM Pm))
    (hPl : (transposeM Pm).length = n)
    (horth : matOneValue (matMul (transposeM Pm) Pm) (inertia.idMat n)) :
    matOneValue (matAdd (matMul Pm Pm) (inertia.idMat n))
      (matMul (chordOp Pm) Pm) :=
  matOne_symm (matOne_trans (matMul_addL n Pm hPt Pm (transposeM Pm) hP hPt)
    (matAdd_cong2 n (matMul Pm Pm) (matMul (transposeM Pm) Pm)
      (matMul Pm Pm) (inertia.idMat n)
      (rowsLen_cast hPl (rowsLen_matMul Pm Pm))
      (rowsLen_cast hPl (rowsLen_matMul (transposeM Pm) Pm))
      (rowsLen_cast hPl (rowsLen_matMul Pm Pm)) (inertia.idMat_rows n)
      (matOne_refl (matMul Pm Pm)) horth))

/-- The chord's join at a fixed word: at the two fixed reads
`T X = X` and `Tᵀ X = X` the chord doubles, `S X = 2 X`, the
lemma's own step at the word `X := T^m P_L(S)`. -/
theorem chord_join (n : Nat) (Pm X : Mat) (hP : rowsLen n Pm)
    (hPt : rowsLen n (transposeM Pm))
    (hXt : rowsLen n (transposeM X))
    (hXl : (transposeM X).length = n) (hXr : rowsLen n X)
    (h1 : matOneValue (matMul Pm X) X)
    (h2 : matOneValue (matMul (transposeM Pm) X) X) :
    matOneValue (matMul (chordOp Pm) X)
      (inertia.matScaleB (BPair.ofNat 2) X) :=
  matOne_trans (matMul_addL n X hXt Pm (transposeM Pm) hP hPt)
    (matOne_trans
      (matAdd_cong2 n (matMul Pm X) (matMul (transposeM Pm) X) X X
        (rowsLen_cast hXl (rowsLen_matMul Pm X))
        (rowsLen_cast hXl (rowsLen_matMul (transposeM Pm) X))
        hXr hXr h1 h2)
      (matAdd_double X))

/-! The doubling tier: the block datum `A` at `T = Tᵀ + A` and its
band read.  `lem:fiberdec`'s doubling opens at the site datum over
the pair, and the square collects against the chord at the
orthogonality alone — `A² + 4 = S²` is a general theorem over the
matrix kit, the two products `T Tᵀ = Tᵀ T = 1` entering as the
constant's two halves and the crossed terms cancelling against
their own swaps. -/

/-- The doubled block's datum `A` at `T = Tᵀ + A`, the site-datum
spelling over the pair (`lem:fiberdec`'s doubling read). -/
def bandDatum (Pm : Mat) : Mat := inertia.siteDatum Pm (transposeM Pm)

/-- The doubling datum's shape at a square matrix: the matrix
joined to its transpose's memberwise swap reads the matrix's own
order at the row count and at the row width. -/
private theorem bandDatum_shape (n : Nat) (Pm : elim.Mat)
    (hM : rowsLen n Pm) (hMl : Pm.length = n) :
    rowsLen n (bandDatum Pm) ∧ (bandDatum Pm).length = n := by
  have hTtl : (transposeM Pm).length = n := transposeLen Pm hM hMl
  have hTt : rowsLen n (transposeM Pm) :=
    rowsLen_cast hMl (rowsLen_transposeM Pm)
  have hSw : rowsLen n (matSwap (transposeM Pm)) :=
    rowsLen_mapRows BPair.swap (transposeM Pm) n hTt
  have hSwl : (matSwap (transposeM Pm)).length = n :=
    (ground.length_map _ (transposeM Pm)).trans hTtl
  exact ⟨rowsLen_matAdd n Pm (matSwap (transposeM Pm)) hM hSw,
    (length_matAdd Pm _ (hMl.trans hSwl.symm)).trans hMl⟩

/-- The doubling datum is swap-adjoint: its key-list exchange reads
its own memberwise swap, the site datum's two members trading
places under the exchange. -/
private theorem band_swapAdj (n : Nat) : ∀ Pm : elim.Mat,
    rowsLen n Pm → Pm.length = n →
    matOneValue (transposeM (bandDatum Pm)) (matSwap (bandDatum Pm))
  | [], _, _ => trivial
  | r :: t, hM, hMl => by
    have hn : 0 < n := by rw [← hMl]; exact Nat.succ_le_succ (Nat.zero_le _)
    have hP : rowsLen n (r :: t) := hM
    have hTtl : (transposeM (r :: t)).length = n :=
      transposeLen (r :: t) hM hMl
    have hTt : rowsLen n (transposeM (r :: t)) :=
      rowsLen_cast hMl (rowsLen_transposeM (r :: t))
    have hSw : rowsLen n (matSwap (transposeM (r :: t))) :=
      rowsLen_mapRows BPair.swap (transposeM (r :: t)) n hTt
    have hSwl : (matSwap (transposeM (r :: t))).length = n :=
      (ground.length_map _ (transposeM (r :: t))).trans hTtl
    have hdouble : transposeM (transposeM (r :: t)) = r :: t :=
      transposeM_transposeM (r :: t) hM hn (by rw [hMl]; exact hn)
    show matOneValue
      (transposeM (matAdd (r :: t) (matSwap (transposeM (r :: t)))))
      (matSwap (matAdd (r :: t) (matSwap (transposeM (r :: t)))))
    rw [transposeM_matAdd (r :: t) (matSwap (transposeM (r :: t))) hP hSw
        (hMl.trans hSwl.symm) (by rw [hMl]; exact hn),
      transposeM_swap (transposeM (r :: t)), hdouble,
      matSwap_matAdd (r :: t) (matSwap (transposeM (r :: t))),
      matSwap_matSwap (transposeM (r :: t)),
      matAdd_comm (matSwap (r :: t)) (transposeM (r :: t))]
    exact matOne_refl _

/-- The band read at the translation's matrix: at the orthogonality
`T Tᵀ = Tᵀ T = 1` the doubling datum squares against the chord,
`A² + 4 = S²`, the two products collected (`lem:fiberdec`).  On a
chord block at a located root the display reads `A² + 4 = t²`, the
root's own instance. -/
theorem chord_band (n : Nat) (Pm : Mat) (hP : rowsLen n Pm)
    (hPl : Pm.length = n) (hn : 0 < n) (horth : orthRead Pm n) :
    matOneValue
      (matAdd (matMul (bandDatum Pm) (bandDatum Pm))
        (inertia.matScaleB (BPair.ofNat 4) (inertia.idMat n)))
      (matMul (chordOp Pm) (chordOp Pm)) := by
  have hTtl : (transposeM Pm).length = n := transposeLen Pm hP hPl
  have hTt : rowsLen n (transposeM Pm) := rowsLen_cast hPl (rowsLen_transposeM Pm)
  have hTtt : (transposeM (transposeM Pm)).length = n :=
    transposeLen (transposeM Pm) hTt hTtl
  have hSw : rowsLen n (matSwap (transposeM Pm)) :=
    rowsLen_mapRows BPair.swap (transposeM Pm) n hTt
  have hSwl : (matSwap (transposeM Pm)).length = n :=
    (ground.length_map _ (transposeM Pm)).trans hTtl
  have hA : rowsLen n (bandDatum Pm) := (bandDatum_shape n Pm hP hPl).1
  have hAl : (bandDatum Pm).length = n := (bandDatum_shape n Pm hP hPl).2
  have hS : rowsLen n (chordOp Pm) := rowsLen_matAdd n Pm (transposeM Pm) hP hTt
  have hSl : (chordOp Pm).length = n :=
    (length_matAdd Pm _ (hPl.trans hTtl.symm)).trans hPl
  have hAt : rowsLen n (transposeM (bandDatum Pm)) :=
    rowsLen_cast hAl (rowsLen_transposeM _)
  have hSt : rowsLen n (transposeM (chordOp Pm)) :=
    rowsLen_cast hSl (rowsLen_transposeM _)
  have hAtl : (transposeM (bandDatum Pm)).length = n :=
    transposeLen (bandDatum Pm) hA hAl
  have hStl : (transposeM (chordOp Pm)).length = n :=
    transposeLen (chordOp Pm) hS hSl
  have hTT : rowsLen n (matMul Pm Pm) := rowsLen_cast hTtl (rowsLen_matMul Pm Pm)
  have hPP : rowsLen n (matMul Pm (transposeM Pm)) :=
    rowsLen_cast hTtt (rowsLen_matMul Pm (transposeM Pm))
  have hQ : rowsLen n (matMul (transposeM Pm) Pm) :=
    rowsLen_cast hTtl (rowsLen_matMul (transposeM Pm) Pm)
  have hQQ : rowsLen n (matMul (transposeM Pm) (transposeM Pm)) :=
    rowsLen_cast hTtt (rowsLen_matMul (transposeM Pm) (transposeM Pm))
  have hswP : rowsLen n (matSwap (matMul Pm (transposeM Pm))) :=
    rowsLen_mapRows BPair.swap _ n hPP
  have hswQ : rowsLen n (matSwap (matMul (transposeM Pm) Pm)) :=
    rowsLen_mapRows BPair.swap _ n hQ
  have hI : rowsLen n (inertia.idMat n) := inertia.idMat_rows n
  -- the doubling datum's square
  have hTA : matOneValue (matMul Pm (bandDatum Pm))
      (matAdd (matMul Pm Pm) (matSwap (matMul Pm (transposeM Pm)))) := by
    have h := matMul_addR Pm (matSwap (transposeM Pm)) hP hSw
      (hPl.trans hSwl.symm) (by rw [hPl]; exact hn) Pm (rowsLen_cast hPl.symm hP)
    rw [matMul_swap] at h
    exact h
  have hTtA : matOneValue (matMul (transposeM Pm) (bandDatum Pm))
      (matAdd (matMul (transposeM Pm) Pm)
        (matSwap (matMul (transposeM Pm) (transposeM Pm)))) := by
    have h := matMul_addR Pm (matSwap (transposeM Pm)) hP hSw
      (hPl.trans hSwl.symm) (by rw [hPl]; exact hn) (transposeM Pm)
      (rowsLen_cast hPl.symm hTt)
    rw [matMul_swap] at h
    exact h
  have hA2 : matOneValue (matMul (bandDatum Pm) (bandDatum Pm))
      (matAdd (matAdd (matMul Pm Pm) (matSwap (matMul Pm (transposeM Pm))))
        (matAdd (matSwap (matMul (transposeM Pm) Pm))
          (matMul (transposeM Pm) (transposeM Pm)))) := by
    refine matOne_trans
      (matMul_addL n (bandDatum Pm) hAt Pm (matSwap (transposeM Pm)) hP hSw) ?_
    refine matAdd_cong2 n _ _ _ _
      (rowsLen_cast hAtl (rowsLen_matMul Pm (bandDatum Pm)))
      (rowsLen_cast hAtl (rowsLen_matMul (matSwap (transposeM Pm))
        (bandDatum Pm)))
      (rowsLen_matAdd n _ _ hTT hswP)
      (rowsLen_matAdd n _ _ hswQ hQQ) hTA ?_
    rw [matMul_swapL]
    refine matOne_trans (matSwap_congr hTtA) ?_
    rw [matSwap_matAdd, matSwap_matSwap]
    exact matOne_refl _
  -- the chord's square
  have hS2 : matOneValue (matMul (chordOp Pm) (chordOp Pm))
      (matAdd (matAdd (matMul Pm Pm) (matMul Pm (transposeM Pm)))
        (matAdd (matMul (transposeM Pm) Pm)
          (matMul (transposeM Pm) (transposeM Pm)))) := by
    refine matOne_trans
      (matMul_addL n (chordOp Pm) hSt Pm (transposeM Pm) hP hTt) ?_
    refine matAdd_cong2 n _ _ _ _
      (rowsLen_cast hStl (rowsLen_matMul Pm (chordOp Pm)))
      (rowsLen_cast hStl (rowsLen_matMul (transposeM Pm) (chordOp Pm)))
      (rowsLen_matAdd n _ _ hTT hPP)
      (rowsLen_matAdd n _ _ hQ hQQ)
      (matMul_addR Pm (transposeM Pm) hP hTt (hPl.trans hTtl.symm)
        (by rw [hPl]; exact hn) Pm (rowsLen_cast hPl.symm hP))
      (matMul_addR Pm (transposeM Pm) hP hTt (hPl.trans hTtl.symm)
        (by rw [hPl]; exact hn) (transposeM Pm) (rowsLen_cast hPl.symm hTt))
  -- the constant collects the two orthogonality reads
  have hFour : matOneValue
      (inertia.matScaleB (BPair.ofNat 4) (inertia.idMat n))
      (matAdd
        (matAdd (matMul Pm (transposeM Pm)) (matMul Pm (transposeM Pm)))
        (matAdd (matMul (transposeM Pm) Pm) (matMul (transposeM Pm) Pm))) := by
    refine matOne_symm (matOne_trans
      (matAdd_cong2 n _ _ _ _
        (rowsLen_matAdd n _ _ hPP hPP) (rowsLen_matAdd n _ _ hQ hQ)
        (rowsLen_matAdd n _ _ hI hI) (rowsLen_matAdd n _ _ hI hI)
        (matAdd_cong2 n _ _ _ _ hPP hPP hI hI horth.1 horth.1)
        (matAdd_cong2 n _ _ _ _ hQ hQ hI hI horth.2 horth.2)) ?_)
    have htwo : matOneValue (matAdd (inertia.idMat n) (inertia.idMat n))
        (inertia.matScaleB (BPair.ofNat 2) (inertia.idMat n)) :=
      matOne_trans
        (matAdd_cong2 n _ _ _ _ hI hI
          (rowsLen_mapRows _ _ n hI) (rowsLen_mapRows _ _ n hI)
          (matOne_symm (inertia.matScaleB_one (inertia.idMat n)))
          (matOne_symm (inertia.matScaleB_one (inertia.idMat n))))
        (matOne_trans
          (inertia.matScaleB_add (BPair.ofNat 1) (BPair.ofNat 1)
            (inertia.idMat n))
          (inertia.matScaleB_congr
            (BPair.oneValue_symm (BPair.ofNat_add 1 1)) (inertia.idMat n)))
    refine matOne_trans
      (matAdd_cong2 n _ _ _ _
        (rowsLen_matAdd n _ _ hI hI) (rowsLen_matAdd n _ _ hI hI)
        (rowsLen_mapRows _ _ n hI) (rowsLen_mapRows _ _ n hI)
        htwo htwo) ?_
    exact matOne_trans
      (inertia.matScaleB_add (BPair.ofNat 2) (BPair.ofNat 2) (inertia.idMat n))
      (inertia.matScaleB_congr
        (BPair.oneValue_symm (BPair.ofNat_add 2 2)) (inertia.idMat n))
  -- the assembly
  refine matOne_trans
    (matAdd_cong2 n _ _ _ _
      (rowsLen_cast hAtl (rowsLen_matMul (bandDatum Pm) (bandDatum Pm)))
      (rowsLen_mapRows _ _ n hI)
      (rowsLen_matAdd n _ _ (rowsLen_matAdd n _ _ hTT hswP)
        (rowsLen_matAdd n _ _ hswQ hQQ))
      (rowsLen_matAdd n _ _ (rowsLen_matAdd n _ _ hPP hPP)
        (rowsLen_matAdd n _ _ hQ hQ))
      hA2 hFour) ?_
  rw [matAdd_shuffle (matAdd (matMul Pm Pm) (matSwap (matMul Pm (transposeM Pm))))
      (matAdd (matSwap (matMul (transposeM Pm) Pm))
        (matMul (transposeM Pm) (transposeM Pm)))
      (matAdd (matMul Pm (transposeM Pm)) (matMul Pm (transposeM Pm)))
      (matAdd (matMul (transposeM Pm) Pm) (matMul (transposeM Pm) Pm)),
    matAdd_assoc (matMul Pm Pm) (matSwap (matMul Pm (transposeM Pm)))
      (matAdd (matMul Pm (transposeM Pm)) (matMul Pm (transposeM Pm))),
    matAdd_assoc (matSwap (matMul (transposeM Pm) Pm))
      (matMul (transposeM Pm) (transposeM Pm))
      (matAdd (matMul (transposeM Pm) Pm) (matMul (transposeM Pm) Pm)),
    matAdd_comm (matMul (transposeM Pm) (transposeM Pm))
      (matAdd (matMul (transposeM Pm) Pm) (matMul (transposeM Pm) Pm)),
    ← matAdd_assoc (matSwap (matMul (transposeM Pm) Pm))
      (matAdd (matMul (transposeM Pm) Pm) (matMul (transposeM Pm) Pm))
      (matMul (transposeM Pm) (transposeM Pm))]
  refine matOne_trans
    (matAdd_cong2 n _ _ _ _
      (rowsLen_matAdd n _ _ hTT (rowsLen_matAdd n _ _ hswP
        (rowsLen_matAdd n _ _ hPP hPP)))
      (rowsLen_matAdd n _ _ (rowsLen_matAdd n _ _ hswQ
        (rowsLen_matAdd n _ _ hQ hQ)) hQQ)
      (rowsLen_matAdd n _ _ hTT hPP)
      (rowsLen_matAdd n _ _ hQ hQQ)
      (matAdd_cong2 n _ _ _ _ hTT
        (rowsLen_matAdd n _ _ hswP (rowsLen_matAdd n _ _ hPP hPP))
        hTT hPP (matOne_refl _) (matSwap_double (matMul Pm (transposeM Pm))))
      (matAdd_cong2 n _ _ _ _
        (rowsLen_matAdd n _ _ hswQ (rowsLen_matAdd n _ _ hQ hQ)) hQQ hQ hQQ
        (matSwap_double (matMul (transposeM Pm) Pm)) (matOne_refl _))) ?_
  exact matOne_symm hS2

/-! The base-rational splitting: the two chord blocks over the
ground, their concatenated lists' congruence and the count. -/

/-- The pair `(S : 2)`'s site datum, the unit fiber's own block. -/
def unitDatum (Pm : Mat) (n : Nat) : Mat :=
  inertia.siteDatum (chordOp Pm)
    (inertia.matScaleB (BPair.ofNat 2) (inertia.idMat n))

/-- The identification at the datum `D₁` of `1 + D₁ = T`: the
product `Tᵀ T = 1` expands and the chord reads `S = 2 + D₁ + D₁ᵀ`,
the two joining at `D₁ᵀ D₁ + S = 2`, so a member of the pair
`(S : 2)`'s kernel reads the fixed line. -/
def identRead (Pm : Mat) (n : Nat) : Prop :=
  matOneValue
    (matAdd
      (matMul (transposeM (inertia.siteDatum Pm (inertia.idMat n)))
        (inertia.siteDatum Pm (inertia.idMat n)))
      (chordOp Pm))
    (inertia.matScaleB (BPair.ofNat 2) (inertia.idMat n))

instance (Pm : Mat) (n : Nat) : Decidable (identRead Pm n) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- A stated list's members sit in a datum's kernel, the action
reading the unit family at each. -/
def kerList (D : Mat) (vs : Mat) : Prop :=
  (vs.all (fun v => decide (poly.unitTail (matVec D v)))) = true

instance (D : Mat) (vs : Mat) : Decidable (kerList D vs) :=
  inferInstanceAs (Decidable (_ = _))

/-- A stated list's members read the translation's fixed line,
`T v = v`. -/
def fixedList (Pm : Mat) (vs : Mat) : Prop :=
  (vs.all (fun v => decide (poly.oneValue (matVec Pm v) v))) = true

instance (Pm : Mat) (vs : Mat) : Decidable (fixedList Pm vs) :=
  inferInstanceAs (Decidable (_ = _))

/-- The unit fiber at a stated window: an independent list whose
members sit in the kernel of the pair `(S : 2)`'s site datum and
read the fixed line `T v = v`, the two identified at
`identRead`. -/
def unitFiberRead (Pm : Mat) (n : Nat) (vs : Mat) : Prop :=
  indepRows n vs ∧ kerList (unitDatum Pm n) vs ∧ fixedList Pm vs

instance (Pm : Mat) (n : Nat) (vs : Mat) :
    Decidable (unitFiberRead Pm n vs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The chord block at `P_L`'s roots read on the base: an
independent spanning list in the kernel of `P_L(S)`
(`def:elim`'s elimination). -/
def rootBlockRead (Pm : Mat) (n m : Nat) (vs : Mat) : Prop :=
  indepRows n vs
  ∧ kerList (polyEvalM (deck.pSum m) (chordOp Pm) n) vs

instance (Pm : Mat) (n m : Nat) (vs : Mat) :
    Decidable (rootBlockRead Pm n m vs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The splitting congruence at the concatenated lists: the
window's datum carried to the two chord blocks' block join, the
off-block reading equal members throughout — `lem:inertia`'s
`rev_join` its consumer, the count splitting with the splitting. -/
def blockCongrRead (D vs P Q : Mat) (k m : Nat) : Prop :=
  matOneValue (matMul vs (matMul D (transposeM vs)))
    (inertia.blockJoin P
      (List.replicate k (List.replicate m BPair.unit)) Q)

instance (D vs P Q : Mat) (k m : Nat) :
    Decidable (blockCongrRead D vs P Q k m) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- The base splitting at a stated window: the two base-rational
chord blocks, their concatenation independent, and its congruence
carrying the window's datum to the blocks' join. -/
def baseSplitRead (Pm D : Mat) (n m : Nat) (Lu Lk P Q : Mat) : Prop :=
  unitFiberRead Pm n Lu
  ∧ rootBlockRead Pm n m Lk
  ∧ indepRows n (Lu ++ Lk)
  ∧ blockCongrRead D (Lu ++ Lk) P Q Lu.length Lk.length

instance (Pm D : Mat) (n m : Nat) (Lu Lk P Q : Mat) :
    Decidable (baseSplitRead Pm D n m Lu Lk P Q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! The sampled momenta: the chord `2` with `P_L`'s located
roots. -/

private def bracketsApart : List stage.Ext → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a.hi < b.lo) && bracketsApart (b :: t)

/-- The sampled momenta at a side `2m+1 = L`: the chord `2` — the
unit fiber, off `P_L`'s roots at the division display's
`P_L(2) = L` — with `P_L`'s `m` located roots, each a designated
bracket datum at `thm:windowsep`'s separation (`lem:stage`'s
isolation at half the separation), the brackets ordered apart and
each bracket's monic polynomial a factor of `P_L`. -/
def momentaRead (m : Nat) (Es : List stage.Ext) (wn wd : Pos) : Prop :=
  BPair.offUnit (poly.eval (deck.pSum m) (BPair.ofNat 2))
  ∧ Es.length = m
  ∧ (Es.all (fun E => decide (stage.bracketRead E)
      && decide (stage.isolRead E wn wd)
      && decide (poly.unitTail (poly.div E.pol (deck.pSum m)).2)))
      = true
  ∧ bracketsApart Es = true

instance (m : Nat) (Es : List stage.Ext) (wn wd : Pos) :
    Decidable (momentaRead m Es wn wd) :=
  inferInstanceAs (Decidable (¬ _ ∧ _ ∧ _ = _ ∧ _ = _))

/-- The bracket datum at an indexed factor: the extension's
polynomial the factor list's own member, the endpoints the stated
bracket's — the certificate's per-root datum one construction, the
factor never copied. -/
def extAt (fs : List poly.Poly) (jE : Nat × (CPair × CPair)) :
    stage.Ext :=
  ⟨ground.getAt [] fs jE.1, jE.2.1, jE.2.2⟩

/-- The split certificate of the symbol at stated data: the monic
factor fold reads the symbol, the root list at the symbol's own
count, each factor's separation read once at the doubled width,
each root's bracket at its factor's side exchange with the width
joining its endpoints, and the brackets ordered apart —
the symbol's ground factorization at `lem:stage`'s brackets
(`lem:stagesplit`'s Kronecker paragraph), the stored data the
per-root tier reads at. -/
def splitRead (m : Nat) (fs : List poly.Poly)
    (rE : List (Nat × (CPair × CPair))) (wn wd : Pos) : Prop :=
  poly.oneValue (poly.prodFold (fs.map poly.monic))
    (deck.pSum m)
  ∧ rE.length = m
  ∧ (fs.all (fun f =>
      decide (windowsep.sepRead (poly.monic f) (2 * wn) wd))) = true
  ∧ (rE.all (fun jE =>
      decide (jE.1 < fs.length)
      && decide (stage.bracketRead (extAt fs jE))
      && decide ((jE.2.1 + ⟨BPair.ofPos wn, wd⟩).oneValue jE.2.2))) = true
  ∧ bracketsApart (rE.map (extAt fs)) = true

instance (m : Nat) (fs : List poly.Poly)
    (rE : List (Nat × (CPair × CPair))) (wn wd : Pos) :
    Decidable (splitRead m fs rE wn wd) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _ ∧ _ = _ ∧ _ = _))

/-- A stated factor of the symbol divides it at the unit
remainder: the fold's cofactor at the factor is the quotient and
the unit family the remainder, the descent's uniqueness the
read. -/
private theorem splitDiv (m : Nat) (fs : List poly.Poly) (j : Nat)
    (hprod : poly.oneValue (poly.prodFold (fs.map poly.monic))
      (deck.pSum m)) (hj : j < fs.length) :
    poly.unitTail
      (poly.div (ground.getAt [] fs j) (deck.pSum m)).2 := by
  have hj' : j < (fs.map poly.monic).length := by
    rw [ground.length_map]
    exact hj
  obtain ⟨A, hA⟩ := poly.prodFold_factor (fs.map poly.monic) j hj'
  rw [ground.getAt_map ([] : poly.Poly) ([] : poly.Poly) poly.monic
    fs j hj] at hA
  have hRu : poly.unitTail
      (List.replicate (ground.getAt ([] : poly.Poly) fs j).length
        BPair.unit) :=
    poly.unitTail_replicate _
  exact poly.unitTail_oneValue_right hRu
    (poly.div_unique (ground.getAt [] fs j) (deck.pSum m) A
      (List.replicate (ground.getAt ([] : poly.Poly) fs j).length
        BPair.unit)
      (ground.length_replicate BPair.unit _)
      (poly.oneValue_trans (poly.add_unitTail _ hRu)
        (poly.oneValue_trans hA hprod))).2

/-- The per-root fold maps the certificate's rows to the momenta's:
the index read gives the division at the row's own factor, the
bracket and the isolation the row's further conjuncts. -/
private theorem splitAll (m : Nat) (fs : List poly.Poly) (wn wd : Pos)
    (hprod : poly.oneValue (poly.prodFold (fs.map poly.monic))
      (deck.pSum m))
    (hsep : (fs.all (fun f =>
      decide (windowsep.sepRead (poly.monic f) (2 * wn) wd))) = true) :
    ∀ rE : List (Nat × (CPair × CPair)),
      (rE.all (fun jE =>
        decide (jE.1 < fs.length)
        && decide (stage.bracketRead (extAt fs jE))
        && decide ((jE.2.1 + ⟨BPair.ofPos wn, wd⟩).oneValue jE.2.2)))
        = true →
      ((rE.map (extAt fs)).all (fun E => decide (stage.bracketRead E)
        && decide (stage.isolRead E wn wd)
        && decide (poly.unitTail
            (poly.div E.pol (deck.pSum m)).2))) = true
  | [], _ => rfl
  | jE :: t, h => by
    have hc : ((decide (jE.1 < fs.length)
          && decide (stage.bracketRead (extAt fs jE))
          && decide ((jE.2.1 + ⟨BPair.ofPos wn, wd⟩).oneValue jE.2.2))
        && (t.all (fun jE =>
          decide (jE.1 < fs.length)
          && decide (stage.bracketRead (extAt fs jE))
          && decide ((jE.2.1 + ⟨BPair.ofPos wn, wd⟩).oneValue jE.2.2))))
        = true := h
    obtain ⟨h1, h2⟩ := ground.andSplitB hc
    obtain ⟨hlt, hwid⟩ := ground.andSplitB h1
    obtain ⟨hlt', hbr⟩ := ground.andSplitB hlt
    have hiso : decide (stage.isolRead (extAt fs jE) wn wd) = true :=
      decide_eq_true
        (⟨of_decide_eq_true hwid,
          of_decide_eq_true
            (ground.all_getAt ([] : poly.Poly) fs hsep jE.1
              (of_decide_eq_true hlt'))⟩ :
          stage.isolRead (extAt fs jE) wn wd)
    have hdiv : decide (poly.unitTail
        (poly.div (extAt fs jE).pol (deck.pSum m)).2) = true :=
      decide_eq_true
        (splitDiv m fs jE.1 hprod (of_decide_eq_true hlt'))
    show ((decide (stage.bracketRead (extAt fs jE))
          && decide (stage.isolRead (extAt fs jE) wn wd)
          && decide (poly.unitTail
              (poly.div (extAt fs jE).pol (deck.pSum m)).2))
        && ((t.map (extAt fs)).all (fun E =>
          decide (stage.bracketRead E)
          && decide (stage.isolRead E wn wd)
          && decide (poly.unitTail
              (poly.div E.pol (deck.pSum m)).2)))) = true
    rw [hbr, hiso, hdiv, splitAll m fs wn wd hprod hsep t h2]
    rfl

/-- The split certificate reads the sampled momenta: the fold's
value at the chord sits off the sum's unit, the images at the
certificate's count, each image's division at the unit remainder
of its own factor, and the brackets ordered apart. -/
theorem splitRead_momenta (m : Nat) (fs : List poly.Poly)
    (rE : List (Nat × (CPair × CPair))) (wn wd : Pos)
    (h : splitRead m fs rE wn wd) :
    momentaRead m (rE.map (extAt fs)) wn wd :=
  ⟨fun hu =>
      BPair.ofNat_off_unit (2 * m + 1) (Nat.succ_pos (2 * m))
        (BPair.oneValue_trans
          (BPair.oneValue_symm (deck.pSum_two m)) hu),
    (ground.length_map (extAt fs) rE).trans h.2.1,
    splitAll m fs wn wd h.1 h.2.2.1 rE h.2.2.2.1,
    h.2.2.2.2⟩

/-! The deck-family column at the residue: the free orbit's own
polynomial carrier.  `lem:fiberdec`'s per-orbit witness is the
column `u = Σ_{b<L} p_b(t) T^b w`, whose coordinates on the
orbit's own translate list are the deck families themselves, so over the polynomial
carrier the column is the family list read modulo the deck symbol
(`deckColumn` at `deck.redP`, `def:poly`'s division by the monic
display, `deck.pSum_monic` the display's own monicity at every
side and `deck.pFamN` the tex's seed `p₀ = 2`).  The chord and
the doubling datum act on the orbit as integer matrices, carried
entry by entry to the polynomial carrier (`pmatVec` at
`poly.scaleP`), and the lemma's three per-orbit reads sit there:
the membership
`S u = x u` at the recursion closing cyclically
(`colMemberRead`), the perpendicularity `⟨u, A u⟩` reading its own
memberwise swap at `Aᵀ = Ǎ` (`perpRead`), and the independence of
the pair `(u, A u)` at their Gram determinant's Bézout witness over
the residue (`gramUnitRead`).  The three are decidable at stated
data and the batteries decide them at the side-five orbit; the
residue's own wrap reads `p_{L-b} = p_b` and `p_L = 2` are
`deck.pFamN_wrapDown` and `deck.pFamN_side`, general theorems over
the indices, and the family recursion closes cyclically as a class
read at every key (`deck.pFamN_cycMid`, `deck.pFamN_cycBot`,
`deck.pFamN_cycTop`); the read here stays the per-window
matrix-entry spelling, its residue `deck.redP`'s remainder carried
onto the class reads' stated multiple by the bridge, entry by entry
at `prow_redP`.  The lemma's count squeeze `1 + 2m = L` reads at
the splitting's own stated lists below: the orbit's sum
(`orbitSum`) joined to the column's coefficient rows, each member
against its image under the doubling datum (`pairBase` at
`sliceAt`), at the orbit's own count (`pairBase_len`), with the
unit fiber's one member reading through the sum's list alone
(`unitFiber_wrap` at `identRead_wrap`, `unitFiber_span`) and the
column's Horner read carrying the chord to a stated polynomial's
own multiple over the residue (`polyEval_column`, the membership
read iterated along `def:poly`'s recursion) —
`lem:inertia`'s `rev_join` battery the count frame's own consumer
at the side-five splitting; the splitting's four reads close at
`orbitSplit_indep`, `orbitSplit_span`, `rootBlock_wrap` and
`rootBlock_span` below. -/

/-- The deck-family column of the free orbit, the coordinates on
the orbit's own translate list read at the residue. -/
def deckColumn (m : Nat) : List poly.Poly :=
  (List.range (2 * m + 1)).map (fun b => deck.redP m (deck.pFamN b))

/-- An integer matrix's action on a polynomial vector, the rows'
folds. -/
def pmatVec (M : Mat) (u : List poly.Poly) : List poly.Poly :=
  M.map (fun r => poly.scaleDot r u)

/-- Two polynomial vectors' pairing, the entries' products
summed. -/
def pdotVec : List poly.Poly → List poly.Poly → poly.Poly
  | [], _ => []
  | _ :: _, [] => []
  | p :: ps, q :: qs => poly.add (poly.mul p q) (pdotVec ps qs)

/-- A polynomial vector's residues at the deck symbol. -/
def redVec (m : Nat) (u : List poly.Poly) : List poly.Poly :=
  u.map (deck.redP m)

/-- The vector bridge: entrywise congruences at the deck symbol
read one residue vector, the class-read spelling carried to the
membership read's own. -/
theorem prow_redP (m : Nat) :
    ∀ (us vs : List poly.Poly),
    us.length = vs.length →
    (∀ i, i < us.length →
      ∃ c, deck.pCong m c (ground.getAt [] us i) (ground.getAt [] vs i)) →
    split.prowOneValue (redVec m us) (redVec m vs)
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | _ :: us, _ :: vs, h, hi =>
    ⟨deck.redP_congr m (hi 0 (Nat.succ_le_succ (Nat.zero_le _))),
      prow_redP m us vs (Nat.succ.inj h)
        (fun i hlt => hi (i + 1) (Nat.succ_lt_succ hlt))⟩

/-- The column's membership read: the chord carries the column to
its own chord multiple over the residue, `S u = x u`, the family
recursion closing cyclically at the wrapped keys. -/
def colMemberRead (m : Nat) (S : Mat) (u : List poly.Poly) : Prop :=
  split.prowOneValue (redVec m (pmatVec S u))
    (redVec m (u.map (fun p => poly.mul deck.wPoly p)))

instance (m : Nat) (S : Mat) (u : List poly.Poly) :
    Decidable (colMemberRead m S u) :=
  inferInstanceAs (Decidable (split.prowOneValue _ _))

/-- The column's perpendicularity read: at `Aᵀ = Ǎ` the pairing
`⟨u, A u⟩` reads its own memberwise swap over the residue, hence
equal members, so the image is perpendicular to the column. -/
def perpRead (m : Nat) (A : Mat) (u : List poly.Poly) : Prop :=
  poly.oneValue (deck.redP m (pdotVec u (pmatVec A u)))
    (deck.redP m (poly.neg (pdotVec u (pmatVec A u))))

instance (m : Nat) (A : Mat) (u : List poly.Poly) :
    Decidable (perpRead m A u) :=
  poly.decOneValue _ _

/-- The pair's Gram determinant at the residue, the two diagonal
pairings against the crossed ones. -/
def gramDet (m : Nat) (A : Mat) (u : List poly.Poly) : poly.Poly :=
  deck.redP m
    (poly.add (poly.mul (pdotVec u u) (pdotVec (pmatVec A u) (pmatVec A u)))
      (poly.neg (poly.mul (pdotVec u (pmatVec A u))
        (pdotVec (pmatVec A u) u))))

/-- The pair's independence read over the residue: the Gram
determinant against a stated cofactor reads an occupied constant
modulo the deck symbol — the Bézout witness of
`lem:stagesplit`'s arithmetic — so `(u, A u)` are the root block's
two independent members. -/
def gramUnitRead (m : Nat) (A : Mat) (u : List poly.Poly)
    (a : poly.Poly) (c : BPair) : Prop :=
  c.offUnit
  ∧ poly.oneValue (deck.redP m (poly.mul (gramDet m A u) a)) [c]

instance (m : Nat) (A : Mat) (u : List poly.Poly) (a : poly.Poly)
    (c : BPair) : Decidable (gramUnitRead m A u a c) :=
  inferInstanceAs (Decidable (¬ _ ∧ _))

/-! The chord's entries on the deck-family column, the membership
read carried from the committed windows to every side.  The
orbit's translation is the wrap shift on the key range — the
successor with the top key wrapped to the seed (`tShift`), its
witness the predecessor with the seed wrapped back (`sShift`) —
and the chord of its permutation matrix carries a key to its two
neighbours: the chord's row at a key is the two permutation rows'
sum, each one-hot at the key its map names, so the column's entry
read there is the two neighbour families' sum, and the recursion's
cyclic reads close that sum at the chord multiple `w p_i`
(`deck.pFamN_cycMid` at the interior keys, `deck.pFamN_cycBot` at
the seed, `deck.pFamN_cycTop` with `deck.pFamN_side` at the top
key).  The identification runs entry by entry through the vector
bridge, the class spelling carried onto the residue's own
(`colMember_wrap` at `prow_redP`). -/

/-- The orbit index's wrap shift: the successor with the top key
wrapped to the seed, the deck-family column's own translation. -/
def tShift (m : Nat) : Nat → Nat := fun b => if b == 2 * m then 0 else b + 1

/-- The wrap shift's witness: the predecessor with the seed wrapped
to the top key. -/
def sShift (m : Nat) : Nat → Nat := fun b => if b == 0 then 2 * m else b - 1

/-- The wrap shift at the top key lands on the seed. -/
private theorem tShift_top (m : Nat) : tShift m (2 * m) = 0 :=
  if_pos (ground.eqBeqOf rfl)

/-- Below the top key the wrap shift is the successor. -/
private theorem tShift_ne (m k : Nat) (h : ¬ (k = 2 * m)) :
    tShift m k = k + 1 :=
  if_neg (fun hh => h (ground.beqEqOf hh))

/-- The witness at the seed lands on the top key. -/
private theorem sShift_zero (m : Nat) : sShift m 0 = 2 * m := if_pos rfl

/-- Above the seed the witness is the predecessor. -/
private theorem sShift_succ (m k : Nat) : sShift m (k + 1) = k :=
  if_neg (ground.boolNe rfl)

/-- The wrap shift's range clause: the key range maps into
itself. -/
theorem tShift_lt (m : Nat) : ∀ j, j < 2 * m + 1 → tShift m j < 2 * m + 1 := by
  intro j hj
  cases hb : (j == 2 * m) with
  | true =>
    rw [ground.beqEqOf hb, tShift_top m]
    exact Nat.succ_le_succ (Nat.zero_le _)
  | false =>
    rw [tShift_ne m j (fun he => ground.boolNe hb (ground.eqBeqOf he))]
    cases Nat.lt_or_ge j (2 * m) with
    | inl h => exact Nat.succ_lt_succ h
    | inr h =>
      exact absurd (Nat.le_antisymm (Nat.le_of_succ_le_succ hj) h)
        (fun he => ground.boolNe hb (ground.eqBeqOf he))

/-- The witness composed after the wrap shift is the identity at
every key: the shift's two branches each land where the witness
reads back, the guard's trichotomy the whole case split. -/
theorem sShift_tShift (m : Nat) :
    ∀ l, sShift m (tShift m l) = l := by
  intro l
  cases hb : (l == 2 * m) with
  | true => rw [ground.beqEqOf hb, tShift_top m, sShift_zero m]
  | false =>
    rw [tShift_ne m l (fun he => ground.boolNe hb (ground.eqBeqOf he)),
      sShift_succ m l]

/-- The wrap shift composed after its witness is the identity on
the key range. -/
theorem tShift_sShift (m : Nat) :
    ∀ l, l < 2 * m + 1 → tShift m (sShift m l) = l := by
  intro l hl
  cases l with
  | zero => rw [sShift_zero m, tShift_top m]
  | succ k =>
    rw [sShift_succ m k,
      tShift_ne m k (fun he => Nat.lt_irrefl (2 * m)
        (by rw [he] at hl; exact Nat.lt_of_succ_lt_succ hl))]

/-- The wrap shift's chord is the shift's matrix joined with its
witness's, the transpose identified at the two composition
reads. -/
private theorem chord_permMatAt (m : Nat) :
    chordOp (permMatAt (2 * m + 1) (tShift m))
      = matAdd (permMatAt (2 * m + 1) (tShift m))
          (permMatAt (2 * m + 1) (sShift m)) := by
  show matAdd (permMatAt (2 * m + 1) (tShift m))
      (transposeM (permMatAt (2 * m + 1) (tShift m))) = _
  rw [transposeM_permMatAt (2 * m + 1) (tShift m) (sShift m)
    (fun l _ => sShift_tShift m l) (tShift_sShift m)]

/-- A row of sum's units against a polynomial vector reads a unit
tail. -/
private theorem scaleDot_unitRow : ∀ (cs : List BPair) (u : List poly.Poly),
    (∀ k, k < cs.length → ground.getAt BPair.unit cs k = BPair.unit) →
    poly.unitTail (poly.scaleDot cs u)
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | c :: cs, p :: u, h => by
    have hc : c = BPair.unit := h 0 (Nat.succ_le_succ (Nat.zero_le _))
    show poly.unitTail (poly.add (poly.scaleP c p) (poly.scaleDot cs u))
    rw [hc]
    exact poly.unitTail_sum (poly.scaleP_unit p)
      (scaleDot_unitRow cs u (fun k hk => h (k + 1) (Nat.succ_lt_succ hk)))

/-- A one-hot row against a polynomial vector reads the vector's
own entry at the occupied key. -/
private theorem scaleDot_hot : ∀ (cs : List BPair) (u : List poly.Poly) (j : Nat),
    cs.length = u.length →
    ground.getAt BPair.unit cs j = BPair.ofPos Pos.one →
    (∀ k, k < cs.length → k ≠ j → ground.getAt BPair.unit cs k = BPair.unit) →
    poly.oneValue (poly.scaleDot cs u) (ground.getAt ([] : poly.Poly) u j)
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, hl, _, _ => Nat.noConfusion hl
  | _ :: _, [], _, hl, _, _ => Nat.noConfusion hl
  | c :: cs, p :: u, 0, _, hh, hc => by
    have hc0 : c = BPair.ofPos Pos.one := hh
    show poly.oneValue (poly.add (poly.scaleP c p) (poly.scaleDot cs u)) p
    rw [hc0]
    exact poly.oneValue_trans
      (poly.add_congr (poly.scaleP_one p) (poly.oneValue_refl (poly.scaleDot cs u)))
      (poly.add_unitTail p
        (scaleDot_unitRow cs u (fun k hk =>
          hc (k + 1) (Nat.succ_lt_succ hk) (fun he => Nat.noConfusion he))))
  | c :: cs, p :: u, j + 1, hl, hh, hc => by
    have hc0 : c = BPair.unit :=
      hc 0 (Nat.succ_le_succ (Nat.zero_le _)) (fun he => Nat.noConfusion he)
    show poly.oneValue (poly.add (poly.scaleP c p) (poly.scaleDot cs u))
      (ground.getAt ([] : poly.Poly) u j)
    rw [hc0]
    exact poly.oneValue_trans (poly.unitTail_add (poly.scaleP_unit p) _)
      (scaleDot_hot cs u j (Nat.succ.inj hl) hh
        (fun k hk hne => hc (k + 1) (Nat.succ_lt_succ hk)
          (fun he => hne (Nat.succ.inj he))))

/-- The row fold splits over a componentwise sum of rows at matched
widths. -/
private theorem scaleDot_vecAdd : ∀ (r q : List BPair) (u : List poly.Poly),
    r.length = q.length →
    poly.oneValue (poly.scaleDot (vecAdd r q) u)
      (poly.add (poly.scaleDot r u) (poly.scaleDot q u))
  | [], [], _, _ => trivial
  | [], _ :: _, _, hl => Nat.noConfusion hl
  | _ :: _, [], _, hl => Nat.noConfusion hl
  | _ :: _, _ :: _, [], _ => trivial
  | c :: r, d :: q, p :: u, hl =>
    poly.oneValue_trans
      (poly.add_congr (poly.scaleP_add c d p)
        (scaleDot_vecAdd r q u (Nat.succ.inj hl)))
      (poly.oneValue_symm (poly.add_shuffle (poly.scaleP c p) (poly.scaleDot r u)
        (poly.scaleP d p) (poly.scaleDot q u)))

/-- A row against its own memberwise swap clears: the two folds
join at a unit tail. -/
private theorem scaleDot_swapNull : ∀ (r : List BPair) (u : List poly.Poly),
    poly.unitTail (poly.add (poly.scaleDot (r.map BPair.swap) u) (poly.scaleDot r u))
  | [], _ => trivial
  | _ :: _, [] => trivial
  | c :: r, p :: u =>
    poly.oneValue_unitTail
      (poly.add_shuffle (poly.scaleP c.swap p)
        (poly.scaleDot (r.map BPair.swap) u) (poly.scaleP c p) (poly.scaleDot r u))
      (poly.unitTail_sum
        (poly.unitTail_oneValue_right
          (poly.scaleP_null (BPair.swap_add_null (BPair.oneValue_refl c)) p)
          (poly.scaleP_add c.swap c p))
        (scaleDot_swapNull r u))

/-- The permutation matrix's row against a polynomial vector reads
the vector's entry at the key the map sends to the row, the row's
entries `getAt_permMatAt`'s own reads. -/
private theorem scaleDot_permRow (n : Nat) (t : Nat → Nat)
    (u : List poly.Poly) (hu : u.length = n) (i j : Nat) (hi : i < n)
    (hj : j < n) (hsel : t j = i)
    (huniq : ∀ k, k < n → k ≠ j → ¬ t k = i) :
    poly.oneValue
      (poly.scaleDot (ground.getAt ([] : List BPair) (permMatAt n t) i) u)
      (ground.getAt ([] : poly.Poly) u j) := by
  have hrow : (ground.getAt ([] : List BPair) (permMatAt n t) i).length
      = n :=
    elim.rowsLen_getAt (permMatAt n t) i (rowsLen_permMatAt n t)
      (by rw [length_permMatAt]; exact hi)
  refine scaleDot_hot _ u j (by rw [hrow, hu]) ?_ ?_
  · rw [getAt_permMatAt n t i j hi hj, if_pos hsel]
    exact rfl
  · intro k hk hne
    rw [hrow] at hk
    rw [getAt_permMatAt n t i k hi hk, if_neg (huniq k hk hne)]

/-- The deck-family column's length is the key count. -/
private theorem deckColumn_len (m : Nat) : (deckColumn m).length = 2 * m + 1 :=
  ground.length_mapRange _ (2 * m + 1)

/-- The deck-family column's entry at a key, the family's residue
there. -/
private theorem deckColumn_getAt (m b : Nat) (hb : b < 2 * m + 1) :
    ground.getAt ([] : poly.Poly) (deckColumn m) b
      = deck.redP m (deck.pFamN b) := by
  rw [show deckColumn m = (List.range (2 * m + 1)).map
      (fun b => deck.redP m (deck.pFamN b)) from rfl,
    ground.getAt_map (0 : Nat) ([] : poly.Poly) _
      (List.range (2 * m + 1)) b
      (by rw [ground.length_range]; exact hb),
    ground.getAt_range (2 * m + 1) b hb]

/-- The chord multiple's entry at a key. -/
private theorem wCol_getAt (m i : Nat) (hi : i < 2 * m + 1) :
    ground.getAt ([] : poly.Poly)
        ((deckColumn m).map (fun p => poly.mul deck.wPoly p)) i
      = poly.mul deck.wPoly (deck.redP m (deck.pFamN i)) := by
  rw [ground.getAt_map ([] : poly.Poly) ([] : poly.Poly) _
      (deckColumn m) i (by rw [deckColumn_len]; exact hi),
    deckColumn_getAt m i hi]

/-- The matrix action's length is the matrix's row count. -/
private theorem pmatVec_len (M : Mat) (u : List poly.Poly) :
    (pmatVec M u).length = M.length :=
  ground.length_map _ M

/-- The matrix action's entry at a key is the row's own fold. -/
private theorem pmatVec_getAt (M : Mat) (u : List poly.Poly) (i : Nat)
    (hi : i < M.length) :
    ground.getAt ([] : poly.Poly) (pmatVec M u) i
      = poly.scaleDot (ground.getAt ([] : List BPair) M i) u :=
  ground.getAt_map ([] : List BPair) ([] : poly.Poly)
    (fun r => poly.scaleDot r u) M i hi

/-- The chord's entry on the deck-family column at a key: the two
neighbour families' residues, the keys the shift and its witness
name. -/
private theorem pmatVec_chord (m i : Nat) (hi : i < 2 * m + 1)
    (jt js : Nat) (hjt : jt < 2 * m + 1) (hjs : js < 2 * m + 1)
    (hselt : tShift m jt = i)
    (huniqt : ∀ k, k < 2 * m + 1 → k ≠ jt → ¬ tShift m k = i)
    (hsels : sShift m js = i)
    (huniqs : ∀ k, k < 2 * m + 1 → k ≠ js → ¬ sShift m k = i) :
    poly.oneValue
      (ground.getAt ([] : poly.Poly)
        (pmatVec (matAdd (permMatAt (2 * m + 1) (tShift m))
          (permMatAt (2 * m + 1) (sShift m))) (deckColumn m)) i)
      (poly.add (deck.redP m (deck.pFamN jt))
        (deck.redP m (deck.pFamN js))) := by
  have hT : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hS : (permMatAt (2 * m + 1) (sShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hA : (matAdd (permMatAt (2 * m + 1) (tShift m))
      (permMatAt (2 * m + 1) (sShift m))).length = 2 * m + 1 := by
    rw [length_matAdd _ _ (by rw [hT, hS]), hT]
  have h1 : poly.oneValue
      (poly.scaleDot (ground.getAt ([] : List BPair)
        (permMatAt (2 * m + 1) (tShift m)) i) (deckColumn m))
      (deck.redP m (deck.pFamN jt)) := by
    rw [← deckColumn_getAt m jt hjt]
    exact scaleDot_permRow (2 * m + 1) (tShift m) (deckColumn m)
      (deckColumn_len m) i jt hi hjt hselt huniqt
  have h2 : poly.oneValue
      (poly.scaleDot (ground.getAt ([] : List BPair)
        (permMatAt (2 * m + 1) (sShift m)) i) (deckColumn m))
      (deck.redP m (deck.pFamN js)) := by
    rw [← deckColumn_getAt m js hjs]
    exact scaleDot_permRow (2 * m + 1) (sShift m) (deckColumn m)
      (deckColumn_len m) i js hi hjs hsels huniqs
  rw [pmatVec_getAt _ _ i (by rw [hA]; exact hi),
    getAt_matAdd _ _ i (by rw [hT]; exact hi) (by rw [hS]; exact hi)]
  exact poly.oneValue_trans
    (scaleDot_vecAdd _ _ (deckColumn m)
      (by rw [rowsLen_getAt (permMatAt (2 * m + 1) (tShift m)) i
            (rowsLen_permMatAt _ _) (by rw [hT]; exact hi),
          rowsLen_getAt (permMatAt (2 * m + 1) (sShift m)) i
            (rowsLen_permMatAt _ _) (by rw [hS]; exact hi)]))
    (poly.add_congr h1 h2)

/-- The entry's class read closed at a cyclic recursion read: the
two neighbour residues' sum is the chord multiple's own residue at
the key. -/
private theorem colWrap_close (m : Nat)
    (x : poly.Poly) (jt js i : Nat)
    (h0 : poly.oneValue x (poly.add (deck.redP m (deck.pFamN jt))
      (deck.redP m (deck.pFamN js))))
    (hcyc : ∃ c, deck.pCong m c
      (poly.add (deck.pFamN jt) (deck.pFamN js))
      (poly.mul deck.wPoly (deck.pFamN i))) :
    ∃ c, deck.pCong m c x
      (poly.mul deck.wPoly (deck.redP m (deck.pFamN i))) :=
  deck.pCong_trans (deck.pCong_of m h0)
    (deck.pCong_trans
      (deck.pCong_addBoth (deck.pCong_symm (deck.redP_pCong m (deck.pFamN jt)))
        (deck.pCong_symm (deck.redP_pCong m (deck.pFamN js))))
      (deck.pCong_trans hcyc
        (deck.pCong_mulL deck.wPoly (deck.redP_pCong m (deck.pFamN i)))))

/-- Below the top key the wrap shift hits the successor key. -/
private theorem tShift_hit (m k : Nat) (hk : k < 2 * m) :
    tShift m k = k + 1 :=
  tShift_ne m k (fun he => Nat.lt_irrefl (2 * m)
    (by rw [he] at hk; exact hk))

/-- The wrap shift hits a successor key at one key alone. -/
private theorem tShift_uniq (m k : Nat) :
    ∀ j, j < 2 * m + 1 → j ≠ k → ¬ tShift m j = k + 1 := by
  intro j _ hne hc
  cases hb : (j == 2 * m) with
  | true =>
    rw [ground.beqEqOf hb, tShift_top m] at hc
    exact Nat.noConfusion hc
  | false =>
    rw [tShift_ne m j
      (fun he => ground.boolNe hb (ground.eqBeqOf he))] at hc
    exact hne (Nat.succ.inj hc)

/-- The chord's entry at a key against the chord multiple's, the
class read at the recursion's own neighbours. -/
private theorem colWrap_entry (m : Nat)
    (hbig : 0 < 2 * m) (i : Nat) (hi : i < 2 * m + 1) :
    ∃ c, deck.pCong m c
      (ground.getAt ([] : poly.Poly)
        (pmatVec (matAdd (permMatAt (2 * m + 1) (tShift m))
          (permMatAt (2 * m + 1) (sShift m))) (deckColumn m)) i)
      (poly.mul deck.wPoly (deck.redP m (deck.pFamN i))) := by
  have hne2m : ¬ 2 * m = 0 := fun hc =>
    absurd (hc ▸ hbig) (Nat.lt_irrefl 0)
  cases i with
  | zero =>
    refine colWrap_close m _ (2 * m) 1 0
      (pmatVec_chord m 0 hi (2 * m) 1 (Nat.le_refl _)
        (Nat.succ_lt_succ hbig)
        (tShift_top m)
        (fun k _ hne => by
          rw [tShift_ne m k hne]
          exact fun hc => Nat.noConfusion hc)
        (sShift_succ m 0)
        ?_)
      (deck.pCong_trans
        (deck.pCong_of m (poly.add_comm (deck.pFamN (2 * m)) (deck.pFamN 1)))
        (deck.pFamN_cycBot m))
    intro k _ hne
    cases k with
    | zero => rw [sShift_zero m]; exact hne2m
    | succ l =>
      rw [sShift_succ m l]
      cases l with
      | zero => exact absurd rfl hne
      | succ j => exact fun hc => Nat.noConfusion hc
  | succ k =>
    have hkm : k < 2 * m := Nat.lt_of_succ_lt_succ hi
    cases Nat.lt_or_ge (k + 1) (2 * m) with
    | inl hlt =>
      exact colWrap_close m _ k (k + 1 + 1) (k + 1)
        (pmatVec_chord m (k + 1) hi k (k + 1 + 1)
          (Nat.le_succ_of_le hkm) (Nat.succ_lt_succ hlt)
          (tShift_hit m k hkm) (tShift_uniq m k)
          (sShift_succ m (k + 1))
          (fun j _ hne => by
            cases j with
            | zero =>
              rw [sShift_zero m]
              exact fun hc => Nat.lt_irrefl (k + 1) (hc ▸ hlt)
            | succ l =>
              rw [sShift_succ m l]
              exact fun hc => hne (congrArg Nat.succ hc)))
        (deck.pFamN_cycMid m k)
    | inr hge =>
      have hkeq : k + 1 = 2 * m :=
        Nat.le_antisymm (Nat.le_of_succ_le_succ hi) hge
      exact colWrap_close m _ k 0 (k + 1)
        (pmatVec_chord m (k + 1) hi k 0
          (Nat.le_succ_of_le hkm) (Nat.succ_le_succ (Nat.zero_le _))
          (tShift_hit m k hkm) (tShift_uniq m k)
          (by rw [sShift_zero m, ← hkeq])
          (fun j hj hne => by
            cases j with
            | zero => exact absurd rfl hne
            | succ l =>
              rw [sShift_succ m l]
              exact fun hc =>
                absurd (by rw [hc, hkeq] at hj; exact hj)
                  (Nat.lt_irrefl (2 * m + 1))))
        (deck.pCong_trans
          (deck.pCong_of m (poly.add_comm (deck.pFamN k) (deck.pFamN 0)))
          (deck.pCong_trans
            (deck.pCong_addBoth (deck.pCong_symm (deck.pFamN_side m))
              (deck.pCong_of m (poly.oneValue_refl (deck.pFamN k))))
            (deck.pFamN_cycTop m k hkeq)))

/-- The chord reads the recursion's neighbour keys on the
deck-family column: at the wrap shift the chord operator carries
the column to its own chord multiple over the residue, the
membership read at every side.  At the base side the symbol is the
scalar one and the residue carrier a point, so that branch decides
at its own data; the fibering's family runs at side five and
beyond, where every entry is a genuine class read. -/
theorem colMember_wrap (m : Nat) :
    colMemberRead m (chordOp (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m) := by
  cases m with
  | zero => decide
  | succ m' =>
    have hbig : 0 < 2 * (m' + 1) := Nat.succ_le_succ (Nat.zero_le _)
    have hT : (permMatAt (2 * (m' + 1) + 1) (tShift (m' + 1))).length
        = 2 * (m' + 1) + 1 := length_permMatAt _ _
    have hS : (permMatAt (2 * (m' + 1) + 1) (sShift (m' + 1))).length
        = 2 * (m' + 1) + 1 := length_permMatAt _ _
    rw [chord_permMatAt (m' + 1)]
    refine prow_redP (m' + 1) _ _ ?_ ?_
    · rw [pmatVec_len, length_matAdd _ _ (by rw [hT, hS]), hT,
        ground.length_map, deckColumn_len]
    · intro i hi
      rw [pmatVec_len, length_matAdd _ _ (by rw [hT, hS]), hT] at hi
      rw [wCol_getAt (m' + 1) i hi]
      exact colWrap_entry (m' + 1) hbig i hi

/-! The per-orbit independence over the remainder lists,
`lem:fiberdec`'s own passage read at every side at once.  The
pairing runs over the key list as a fold at the polynomial carrier
(`pfold`, the ground fold at `poly.add` and its unit), and the
kit beneath it is that fold's algebra: the join, the mapped key
family's read and the top key's own split (`pfold_append`,
`pfold_map`, `pfold_rangeSucc`), the pointwise class reads
(`pfold_congr` at every key, `pfold_brange` below a bound,
`pfold_pCong` at the deck symbol), the memberwise sum's split
(`pfold_split`), the constant two's own count (`pfold_two`), the
vacant family's null read (`pfold_null`), a factor's distribution
over the fold (`pfold_mulL`) and the two key ranges' exchange over
a doubly indexed family (`pfold_fubini`), with `poly.unitTail_sum`
and `ground.range_split` beneath them.  Two mapped families'
pairing is the products' fold (`pdotVec_map`), the row's and the
vector's own pairings are their index folds over the key range
(`scaleDot_getAt`, `pdotVec_getAt`, whence the matrix's double fold
`pdotVec_double`), a matrix sum's action splits (`pdotVec_matAdd`)
and a memberwise swap's action clears against its own
(`pdotVec_swapNull` at `scaleDot_swapNull`, the row scale's null
read).

The perpendicularity is the first output, and it is the transpose
walk at every swap-adjoint matrix rather than anything special to
the wrap shift.  A square matrix whose key-list exchange reads its
own memberwise swap pairs a vector against its own image at the
sum's unit (`perpSwapAdj`): the crossing moves across the pairing's
transpose adjoint (`pdotVec_transpose`: both sides are the one
double fold over the key range, the row and column keys exchanged
at `elim.getAt_transposeM` and the two orders joined by
`pfold_fubini`, with `poly.scaleP_exchange` the rescaled members'
own exchange), the exchange is traded for the memberwise swap
(`pdotVec_matOne`), and the swapped action joins the matrix's own
at a unit tail (`pdotVec_swapNull`), so the pairing reads its own
negation and sits at the unit (`poly.unitTail_of_negRead`).  The
doubling datum is `M - Mᵀ` entrywise and its exchange reads its
own memberwise swap (`band_swapAdj`, the exchange's two splittings
against the swap's), so its pairing clears outright, a unit tail
before any residue is taken, and reads its own memberwise swap
there (`perp_band`), the wrap shift's read that theorem's instance
at the translation's permutation matrix (`perp_wrap`).

The self-pairing is the second.  The squares collect at the
product families, `p_b² = p_{2b} + 2` (`deck.deckProducts`), the
key list's own fold reads the symbol's multiple `p_m P_L`
(`famSum_read`, the telescope `chordTwo_pSum` against the doubling
display `pFamN_pSum` at one induction, whence `famSum_null`), and
the doubled keys read the key list once (`doubled_null`: the even
keys outright at the lower half, the odd keys at the upper wrap
`deck.pFamN_wrapUp`, and the two halves interleaved back to the
key list by `pfold_interleave`), so the fold reads `2L`
(`deckColumn_selfPair`). -/

/-- The fold over a key family at the polynomial carrier, the
ground fold at the sum and its own unit. -/
private def pfold (f : Nat → poly.Poly) : List Nat → poly.Poly :=
  famFold poly.add [] f

/-- A one-key family's fold is its own member. -/
private theorem pfold_single (f : Nat → poly.Poly) (a : Nat) :
    pfold f [a] = f a := poly.add_nil (f a)

/-- The fold over a mapped key family reads the composed family,
the ground fold's own map read at the polynomial carrier. -/
private theorem pfold_map (f : Nat → poly.Poly) (g : Nat → Nat)
    (l : List Nat) : pfold f (l.map g) = pfold (fun j => f (g j)) l :=
  famFold_map poly.add [] f g l

/-- The fold splits over a joined key family. -/
private theorem pfold_append (f : Nat → poly.Poly) :
    ∀ u v : List Nat,
    poly.oneValue (pfold f (u ++ v)) (poly.add (pfold f u) (pfold f v))
  | [], v => poly.oneValue_refl (pfold f v)
  | a :: u, v =>
    poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl (f a)) (pfold_append f u v))
      (poly.add_join (f a) (pfold f u) (pfold f v))

/-- The fold over a key range collects its top key last. -/
private theorem pfold_rangeSucc (f : Nat → poly.Poly) (n : Nat) :
    poly.oneValue (pfold f (List.range (n + 1)))
      (poly.add (pfold f (List.range n)) (f n)) := by
  rw [range_succ n]
  refine poly.oneValue_trans (pfold_append f (List.range n) [n]) ?_
  rw [pfold_single f n]
  exact poly.oneValue_refl _

/-- The fold reads a pointwise class read of its family. -/
private theorem pfold_congr {f g : Nat → poly.Poly}
    (h : ∀ i, poly.oneValue (f i) (g i)) :
    ∀ l : List Nat, poly.oneValue (pfold f l) (pfold g l)
  | [] => trivial
  | a :: t => poly.add_congr (h a) (pfold_congr h t)

/-- The fold over a key range reads a class read holding below the
bound. -/
private theorem pfold_brange {f g : Nat → poly.Poly} :
    ∀ n : Nat, (∀ i, i < n → poly.oneValue (f i) (g i)) →
    poly.oneValue (pfold f (List.range n)) (pfold g (List.range n))
  | 0, _ => trivial
  | n + 1, h =>
    poly.oneValue_trans (pfold_rangeSucc f n)
      (poly.oneValue_trans
        (poly.add_congr
          (pfold_brange n (fun i hi => h i (Nat.lt_succ_of_lt hi)))
          (h n (Nat.le_refl (n + 1))))
        (poly.oneValue_symm (pfold_rangeSucc g n)))

/-- The fold over a key range reads a class read at the deck symbol
holding below the bound. -/
private theorem pfold_pCong (m : Nat) {f g : Nat → poly.Poly} :
    ∀ n : Nat, (∀ i, i < n → ∃ c, deck.pCong m c (f i) (g i)) →
    ∃ c, deck.pCong m c (pfold f (List.range n)) (pfold g (List.range n))
  | 0, _ => deck.pCong_of m trivial
  | n + 1, h =>
    deck.pCong_trans (deck.pCong_of m (pfold_rangeSucc f n))
      (deck.pCong_trans
        (deck.pCong_addBoth
          (pfold_pCong m n (fun i hi => h i (Nat.lt_succ_of_lt hi)))
          (h n (Nat.le_refl (n + 1))))
        (deck.pCong_of m (poly.oneValue_symm (pfold_rangeSucc g n))))

/-- The fold of a memberwise sum splits at the two families. -/
private theorem pfold_split (f g : Nat → poly.Poly) :
    ∀ l : List Nat,
    poly.oneValue (pfold (fun i => poly.add (f i) (g i)) l)
      (poly.add (pfold f l) (pfold g l))
  | [] => trivial
  | a :: t =>
    poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl (poly.add (f a) (g a)))
        (pfold_split f g t))
      (poly.add_shuffle (f a) (g a) (pfold f t) (pfold g t))

/-- The constant two's fold reads the family's own doubled count. -/
private theorem pfold_two : ∀ l : List Nat,
    poly.oneValue (pfold (fun _ => [BPair.ofNat 2]) l)
      [BPair.ofNat (l.length + l.length)]
  | [] => ⟨BPair.oneValue_refl BPair.unit, trivial⟩
  | _ :: t => by
    refine poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl [BPair.ofNat 2]) (pfold_two t)) ?_
    show poly.oneValue [BPair.ofNat 2 + BPair.ofNat (t.length + t.length)]
      [BPair.ofNat (t.length + 1 + (t.length + 1))]
    refine ⟨?_, trivial⟩
    rw [show t.length + 1 + (t.length + 1)
        = t.length + t.length + (1 + 1) from
      Nat.add_add_add_comm t.length 1 t.length 1]
    exact BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm (BPair.ofNat 2) _))
      (BPair.oneValue_symm (BPair.ofNat_add (t.length + t.length) 2))

/-- Two mapped families' pairing is their products' own fold. -/
private theorem pdotVec_map (f g : Nat → poly.Poly) :
    ∀ l : List Nat,
    pdotVec (l.map f) (l.map g) = pfold (fun i => poly.mul (f i) (g i)) l
  | [] => rfl
  | a :: t => by
    show poly.add (poly.mul (f a) (g a)) (pdotVec (t.map f) (t.map g))
      = poly.add (poly.mul (f a) (g a))
        (pfold (fun i => poly.mul (f i) (g i)) t)
    rw [pdotVec_map f g t]

/-- The pairing against a matrix sum's action splits at the two
matrices' own, the row widths matched. -/
private theorem pdotVec_matAdd (n : Nat) (u : List poly.Poly) :
    ∀ (M N : Mat) (v : List poly.Poly), M.length = N.length →
    rowsLen n M → rowsLen n N →
    poly.oneValue (pdotVec v (pmatVec (matAdd M N) u))
      (poly.add (pdotVec v (pmatVec M u)) (pdotVec v (pmatVec N u)))
  | [], [], [], _, _, _ => trivial
  | [], [], _ :: _, _, _, _ => trivial
  | [], _ :: _, _, h, _, _ => Nat.noConfusion h
  | _ :: _, [], _, h, _, _ => Nat.noConfusion h
  | _ :: _, _ :: _, [], _, _, _ => trivial
  | r :: M, s :: N, p :: v, h, hM, hN =>
    poly.oneValue_trans
      (poly.add_congr
        (poly.oneValue_trans
          (poly.mul_congr p
            (scaleDot_vecAdd r s u (hM.1.trans hN.1.symm)))
          (poly.mul_sum p (poly.scaleDot r u) (poly.scaleDot s u)))
        (pdotVec_matAdd n u M N v (Nat.succ.inj h) hM.2 hN.2))
      (poly.add_shuffle (poly.mul p (poly.scaleDot r u))
        (poly.mul p (poly.scaleDot s u)) (pdotVec v (pmatVec M u))
        (pdotVec v (pmatVec N u)))

/-- The pairing against a memberwise-swapped matrix's action clears
against the matrix's own, the two joining at a unit tail. -/
private theorem pdotVec_swapNull (u : List poly.Poly) :
    ∀ (M : Mat) (v : List poly.Poly),
    poly.unitTail (poly.add (pdotVec v (pmatVec (matSwap M) u))
      (pdotVec v (pmatVec M u)))
  | [], [] => trivial
  | [], _ :: _ => trivial
  | _ :: _, [] => trivial
  | r :: M, p :: v =>
    poly.oneValue_unitTail
      (poly.add_shuffle (poly.mul p (poly.scaleDot (r.map BPair.swap) u))
        (pdotVec v (pmatVec (matSwap M) u))
        (poly.mul p (poly.scaleDot r u)) (pdotVec v (pmatVec M u)))
      (poly.unitTail_sum
        (poly.unitTail_oneValue_right
          (poly.mul_unitTail p (scaleDot_swapNull r u))
          (poly.mul_sum p (poly.scaleDot (r.map BPair.swap) u) (poly.scaleDot r u)))
        (pdotVec_swapNull u M v))

/-- The vacant-member family's fold is a unit tail. -/
private theorem pfold_null (f : Nat → poly.Poly)
    (h : ∀ i, poly.unitTail (f i)) :
    ∀ l : List Nat, poly.unitTail (pfold f l)
  | [] => trivial
  | a :: t => poly.unitTail_sum (h a) (pfold_null f h t)

/-- A factor distributes over the fold, the product entering at
every member. -/
private theorem pfold_mulL (p : poly.Poly) (f : Nat → poly.Poly) :
    ∀ l : List Nat,
    poly.oneValue (poly.mul p (pfold f l))
      (pfold (fun i => poly.mul p (f i)) l)
  | [] => poly.unitTail_oneValue (poly.mul_nil p) trivial
  | a :: t =>
    poly.oneValue_trans (poly.mul_sum p (f a) (pfold f t))
      (poly.add_congr (poly.oneValue_refl _) (pfold_mulL p f t))

/-- The two key ranges exchange over a doubly indexed family: the
double fold reads one value in either order. -/
private theorem pfold_fubini (f : Nat → Nat → poly.Poly) (m : Nat) :
    ∀ n : Nat,
    poly.oneValue
      (pfold (fun i => pfold (fun j => f i j) (List.range m)) (List.range n))
      (pfold (fun j => pfold (fun i => f i j) (List.range n)) (List.range m))
  | 0 =>
    poly.unitTail_oneValue trivial
      (pfold_null (fun j => pfold (fun i => f i j) (List.range 0))
        (fun _ => trivial) (List.range m))
  | n + 1 => by
    refine poly.oneValue_trans
      (pfold_rangeSucc (fun i => pfold (fun j => f i j) (List.range m)) n) ?_
    refine poly.oneValue_trans
      (poly.add_congr (pfold_fubini f m n) (poly.oneValue_refl _)) ?_
    refine poly.oneValue_symm (poly.oneValue_trans
      (pfold_congr (fun j => pfold_rangeSucc (fun i => f i j) n)
        (List.range m)) ?_)
    exact pfold_split (fun j => pfold (fun i => f i j) (List.range n))
      (fun j => f n j) (List.range m)

/-- The row's fold reads its own index fold over the key range
(`poly.scaleDot_getAt`). -/
private theorem scaleDot_getAt (r : List BPair) (u : List poly.Poly)
    (h : r.length = u.length) :
    poly.scaleDot r u
      = pfold (fun j => poly.scaleP (ground.getAt BPair.unit r j)
          (ground.getAt ([] : poly.Poly) u j)) (List.range r.length) :=
  poly.scaleDot_getAt r u h

/-- The pairing reads its own index fold over the key range. -/
private theorem pdotVec_getAt : ∀ (x y : List poly.Poly),
    x.length = y.length →
    pdotVec x y
      = pfold (fun i => poly.mul (ground.getAt ([] : poly.Poly) x i)
          (ground.getAt ([] : poly.Poly) y i)) (List.range x.length)
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | p :: x, q :: y, h => by
    show poly.add (poly.mul p q) (pdotVec x y)
      = pfold (fun i => poly.mul (ground.getAt ([] : poly.Poly) (p :: x) i)
          (ground.getAt ([] : poly.Poly) (q :: y) i))
        (List.range (x.length + 1))
    rw [ground.range_cons x.length]
    show poly.add (poly.mul p q) (pdotVec x y)
      = poly.add (poly.mul p q)
        (pfold (fun i => poly.mul (ground.getAt ([] : poly.Poly) (p :: x) i)
            (ground.getAt ([] : poly.Poly) (q :: y) i))
          ((List.range x.length).map (fun j => j + 1)))
    rw [pfold_map _ (fun j => j + 1) (List.range x.length)]
    show poly.add (poly.mul p q) (pdotVec x y)
      = poly.add (poly.mul p q)
        (pfold (fun j => poly.mul (ground.getAt ([] : poly.Poly) x j)
            (ground.getAt ([] : poly.Poly) y j)) (List.range x.length))
    rw [pdotVec_getAt x y (Nat.succ.inj h)]

/-- The matrix's pairing as its own double fold over the key range,
the row's index fold inside the vector's. -/
private theorem pdotVec_double (n : Nat) (M : Mat) (hM : rowsLen n M)
    (hMl : M.length = n) (u v : List poly.Poly)
    (hu : u.length = n) (hv : v.length = n) :
    poly.oneValue (pdotVec v (pmatVec M u))
      (pfold (fun i => pfold (fun j =>
          poly.mul (ground.getAt ([] : poly.Poly) v i)
            (poly.scaleP
              (ground.getAt BPair.unit (ground.getAt ([] : List BPair) M i) j)
              (ground.getAt ([] : poly.Poly) u j)))
        (List.range n)) (List.range n)) := by
  have hml : (pmatVec M u).length = n := by rw [pmatVec_len, hMl]
  rw [pdotVec_getAt v (pmatVec M u) (by rw [hv, hml]), hv]
  refine pfold_brange n (fun i hi => ?_)
  have hiM : i < M.length := by rw [hMl]; exact hi
  have hrow : (ground.getAt ([] : List BPair) M i).length = n :=
    rowsLen_getAt M i hM hiM
  rw [pmatVec_getAt M u i hiM,
    scaleDot_getAt (ground.getAt ([] : List BPair) M i) u (by rw [hrow, hu]),
    hrow]
  exact pfold_mulL _ _ (List.range n)

/-- The pairing's transpose adjoint at the polynomial carrier: the
image's pairing against a second vector reads the first against the
transpose's image, the two double folds the one exchange. -/
private theorem pdotVec_transpose (n : Nat) (M : Mat) (hM : rowsLen n M)
    (hMl : M.length = n) (u v : List poly.Poly)
    (hu : u.length = n) (hv : v.length = n) :
    poly.oneValue (pdotVec v (pmatVec M u))
      (pdotVec u (pmatVec (transposeM M) v)) := by
  have hT : rowsLen n (transposeM M) :=
    rowsLen_cast hMl (rowsLen_transposeM M)
  have hTl : (transposeM M).length = n := transposeLen M hM hMl
  refine poly.oneValue_trans (pdotVec_double n M hM hMl u v hu hv) ?_
  refine poly.oneValue_trans ?_
    (poly.oneValue_symm (pdotVec_double n (transposeM M) hT hTl v u hv hu))
  refine poly.oneValue_trans ?_
    (poly.oneValue_symm (pfold_fubini (fun i j =>
      poly.mul (ground.getAt ([] : poly.Poly) u i)
        (poly.scaleP (ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) (transposeM M) i) j)
          (ground.getAt ([] : poly.Poly) v j))) n n))
  refine pfold_brange n (fun a ha => pfold_brange n (fun b hb => ?_))
  rw [getAt_transposeM BPair.unit M hM b a hb (by rw [hMl]; exact ha)]
  exact poly.scaleP_exchange _ _ _

/-- The rescaling rides the key fold, key by key. -/
private theorem pfold_scaleP (c : BPair) (f : Nat → poly.Poly) :
    ∀ l : List Nat,
    poly.oneValue (poly.scaleP c (pfold f l))
      (pfold (fun i => poly.scaleP c (f i)) l)
  | [] => trivial
  | a :: t =>
    poly.oneValue_trans (poly.scaleP_sum c (f a) (pfold f t))
      (poly.add_congr (poly.oneValue_refl _) (pfold_scaleP c f t))

/-- The row-against-column fold rescales as its own key fold, the
plain fold read one key at a time. -/
private theorem scaleP_dotP (p : poly.Poly) : ∀ r c : List BPair,
    r.length = c.length →
    poly.oneValue (poly.scaleP (dotP r c) p)
      (pfold (fun k => poly.scaleP (ground.getAt BPair.unit r k
          * ground.getAt BPair.unit c k) p) (List.range r.length))
  | [], [], _ => poly.unitTail_oneValue (poly.scaleP_unit p) trivial
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | a :: r, b :: c, h => by
    show poly.oneValue (poly.scaleP (a * b + dotP r c) p)
      (pfold (fun k => poly.scaleP (ground.getAt BPair.unit (a :: r) k
          * ground.getAt BPair.unit (b :: c) k) p)
        (List.range (r.length + 1)))
    rw [ground.range_cons r.length]
    show poly.oneValue (poly.scaleP (a * b + dotP r c) p)
      (poly.add (poly.scaleP (a * b) p)
        (pfold (fun k => poly.scaleP (ground.getAt BPair.unit (a :: r) k
            * ground.getAt BPair.unit (b :: c) k) p)
          ((List.range r.length).map (fun j => j + 1))))
    rw [pfold_map _ (fun j => j + 1) (List.range r.length)]
    exact poly.oneValue_trans (poly.scaleP_add (a * b) (dotP r c) p)
      (poly.add_congr (poly.oneValue_refl _)
        (scaleP_dotP p r c (Nat.succ.inj h)))

/-- The composed action at one row: a matrix product's row against a
polynomial vector reads the left row against the right factor's own
action, the two double folds the one exchange. -/
private theorem scaleDot_matMul (n : Nat) (N : Mat) (hN : rowsLen n N)
    (hNl : N.length = n) (u : List poly.Poly) (hu : u.length = n)
    (r : List BPair) (hr : r.length = n) :
    poly.oneValue (poly.scaleDot ((transposeM N).map (fun c => dotN r c)) u)
      (poly.scaleDot r (pmatVec N u)) := by
  have hTl : (transposeM N).length = n := transposeLen N hN hNl
  have hTr : rowsLen n (transposeM N) :=
    rowsLen_cast hNl (rowsLen_transposeM N)
  have hmapl : ((transposeM N).map (fun c => dotN r c)).length = n :=
    (ground.length_map _ (transposeM N)).trans hTl
  have hpm : (pmatVec N u).length = n := by rw [pmatVec_len, hNl]
  rw [scaleDot_getAt _ u (by rw [hmapl, hu]), hmapl,
    scaleDot_getAt r (pmatVec N u) (by rw [hr, hpm]), hr]
  refine poly.oneValue_trans (pfold_brange n (fun j hj => ?_))
    (poly.oneValue_trans
      (pfold_fubini (fun j k =>
        poly.scaleP (ground.getAt BPair.unit r k
          * ground.getAt BPair.unit
              (ground.getAt ([] : List BPair) N k) j)
          (ground.getAt ([] : poly.Poly) u j)) n n)
      (poly.oneValue_symm (pfold_brange n (fun k hk => ?_))))
  · rw [ground.getAt_map ([] : List BPair) BPair.unit
      (fun c => dotN r c) (transposeM N) j (by rw [hTl]; exact hj)]
    refine poly.oneValue_trans
      (poly.scaleP_congr (dotN_read r
        (ground.getAt ([] : List BPair) (transposeM N) j))
        (ground.getAt ([] : poly.Poly) u j)) ?_
    have hcol : (ground.getAt ([] : List BPair) (transposeM N) j).length = n :=
      rowsLen_getAt (transposeM N) j hTr (by rw [hTl]; exact hj)
    have hstep := scaleP_dotP (ground.getAt ([] : poly.Poly) u j) r
      (ground.getAt ([] : List BPair) (transposeM N) j) (by rw [hr, hcol])
    rw [hr] at hstep
    refine poly.oneValue_trans hstep (pfold_brange n (fun k hk => ?_))
    rw [getAt_transposeM BPair.unit N hN j k hj (by rw [hNl]; exact hk)]
    exact poly.oneValue_refl _
  · have hkN : k < N.length := by rw [hNl]; exact hk
    have hrow : (ground.getAt ([] : List BPair) N k).length = n :=
      rowsLen_getAt N k hN hkN
    rw [pmatVec_getAt N u k hkN,
      scaleDot_getAt (ground.getAt ([] : List BPair) N k) u (by rw [hrow, hu]),
      hrow]
    refine poly.oneValue_trans
      (pfold_scaleP (ground.getAt BPair.unit r k) _ (List.range n)) ?_
    exact pfold_brange n (fun j _ =>
      poly.scaleP_mul (ground.getAt BPair.unit r k)
        (ground.getAt BPair.unit (ground.getAt ([] : List BPair) N k) j)
        (ground.getAt ([] : poly.Poly) u j))

/-- The composed action inside the pairing: the product matrix's
action reads the two actions in turn, one row at a time. -/
private theorem pdotVec_matMul (n : Nat) (M N : Mat) (hM : rowsLen n M)
    (hMl : M.length = n) (hN : rowsLen n N) (hNl : N.length = n)
    (u v : List poly.Poly) (hu : u.length = n) (hv : v.length = n) :
    poly.oneValue (pdotVec v (pmatVec (matMul M N) u))
      (pdotVec v (pmatVec M (pmatVec N u))) := by
  have hMMl : (matMul M N).length = n :=
    (ground.length_map _ M).trans hMl
  have hml : (pmatVec (matMul M N) u).length = n := by
    rw [pmatVec_len, hMMl]
  have hml2 : (pmatVec M (pmatVec N u)).length = n := by
    rw [pmatVec_len, hMl]
  rw [pdotVec_getAt v (pmatVec (matMul M N) u) (by rw [hv, hml]),
    pdotVec_getAt v (pmatVec M (pmatVec N u)) (by rw [hv, hml2]), hv]
  refine pfold_brange n (fun i hi => ?_)
  have hiM : i < M.length := by rw [hMl]; exact hi
  have hrow : (ground.getAt ([] : List BPair) M i).length = n :=
    rowsLen_getAt M i hM hiM
  rw [pmatVec_getAt (matMul M N) u i (by rw [hMMl]; exact hi),
    getAt_matMul M N i hiM, pmatVec_getAt M (pmatVec N u) i hiM]
  exact poly.mul_congr _
    (scaleDot_matMul n N hN hNl u hu (ground.getAt ([] : List BPair) M i) hrow)

/-- A unit-tail row folds to a unit tail. -/
private theorem scaleDot_null : ∀ (r : List BPair) (u : List poly.Poly),
    poly.unitTail r → poly.unitTail (poly.scaleDot r u)
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | _ :: r, p :: u, h =>
    poly.unitTail_sum (poly.scaleP_null h.1 p) (scaleDot_null r u h.2)

/-- The row fold respects the row's own class read. -/
private theorem scaleDot_congr : ∀ (r s : List BPair) (u : List poly.Poly),
    poly.oneValue r s →
    poly.oneValue (poly.scaleDot r u) (poly.scaleDot s u)
  | [], s, u, h => scaleDot_null s u h
  | _ :: _, [], u, h =>
    poly.unitTail_oneValue (scaleDot_null _ u h) trivial
  | _ :: _, _ :: _, [], _ => trivial
  | _ :: r, _ :: s, p :: u, h =>
    poly.add_congr (poly.scaleP_congr h.1 p) (scaleDot_congr r s u h.2)

/-- The pairing respects the acting matrix's own class read. -/
private theorem pdotVec_matOne : ∀ (M N : Mat) (u v : List poly.Poly),
    matOneValue M N →
    poly.oneValue (pdotVec v (pmatVec M u)) (pdotVec v (pmatVec N u))
  | [], [], _, _, _ => poly.oneValue_refl _
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | _ :: _, _ :: _, _, [], _ => trivial
  | r :: M, s :: N, u, p :: v, h =>
    poly.add_congr (poly.mul_congr p (scaleDot_congr r s u h.1))
      (pdotVec_matOne M N u v h.2)

/-- The doubling datum's antisymmetry at two vectors: the pairing
against the datum reads its own memberwise swap with the two members
exchanged, the transpose walk run at both slots. -/
private theorem perp_pair (n : Nat) (M : Mat) (hM : rowsLen n M)
    (hMl : M.length = n) (v w : List poly.Poly)
    (hv : v.length = n) (hw : w.length = n) :
    poly.unitTail
      (poly.add (pdotVec v (pmatVec (bandDatum M) w))
        (pdotVec w (pmatVec (bandDatum M) v))) := by
  have hT : rowsLen n (transposeM M) :=
    rowsLen_cast hMl (rowsLen_transposeM M)
  have hTl : (transposeM M).length = n := transposeLen M hM hMl
  have hSw : rowsLen n (matSwap (transposeM M)) :=
    rowsLen_mapRows BPair.swap (transposeM M) n hT
  have hSwl : (matSwap (transposeM M)).length = n :=
    (ground.length_map _ (transposeM M)).trans hTl
  have hsplit : ∀ x y : List poly.Poly, y.length = n →
      poly.oneValue (pdotVec x (pmatVec (bandDatum M) y))
        (poly.add (pdotVec x (pmatVec M y))
          (pdotVec x (pmatVec (matSwap (transposeM M)) y))) := by
    intro x y _
    exact pdotVec_matAdd n y M (matSwap (transposeM M)) x
      (hMl.trans hSwl.symm) hM hSw
  refine poly.oneValue_unitTail
    (poly.oneValue_trans
      (poly.add_congr (hsplit v w hw) (hsplit w v hv))
      (poly.oneValue_trans
        (poly.add_congr (poly.oneValue_refl _)
          (poly.add_comm (pdotVec w (pmatVec M v))
            (pdotVec w (pmatVec (matSwap (transposeM M)) v))))
        (poly.add_shuffle (pdotVec v (pmatVec M w))
          (pdotVec v (pmatVec (matSwap (transposeM M)) w))
          (pdotVec w (pmatVec (matSwap (transposeM M)) v))
          (pdotVec w (pmatVec M v))))) ?_
  refine poly.unitTail_sum ?_ ?_
  · refine poly.oneValue_unitTail
      (poly.add_congr
        (pdotVec_transpose n M hM hMl w v hw hv) (poly.oneValue_refl _))
      ?_
    exact poly.oneValue_unitTail
      (poly.add_comm (pdotVec w (pmatVec (transposeM M) v))
        (pdotVec w (pmatVec (matSwap (transposeM M)) v)))
      (pdotVec_swapNull v (transposeM M) w)
  · exact poly.oneValue_unitTail
      (poly.add_congr (poly.oneValue_refl _)
        (pdotVec_transpose n M hM hMl v w hv hw))
      (pdotVec_swapNull w (transposeM M) v)

/-- The chord operator is its own transpose. -/
private theorem transposeM_chordOp (n : Nat) (Pm : Mat) (hP : rowsLen n Pm)
    (hPl : Pm.length = n) (hn : 0 < n) :
    matOneValue (transposeM (chordOp Pm)) (chordOp Pm) := by
  have hT : rowsLen n (transposeM Pm) :=
    rowsLen_cast hPl (rowsLen_transposeM Pm)
  have hTl : (transposeM Pm).length = n := transposeLen Pm hP hPl
  rw [show chordOp Pm = matAdd Pm (transposeM Pm) from rfl,
    transposeM_matAdd Pm (transposeM Pm) hP hT (hPl.trans hTl.symm)
      (by rw [hPl]; exact hn),
    transposeM_transposeM Pm hP hn (by rw [hPl]; exact hn),
    matAdd_comm (transposeM Pm) Pm]
  exact matOne_refl _

/-- The pairing carries entrywise residue reads on both members, the
class spelling run at every key. -/
private theorem pdotVec_prowCong (m : Nat) :
    ∀ x x' y y' : List poly.Poly,
    split.prowOneValue (redVec m x) (redVec m x') →
    split.prowOneValue (redVec m y) (redVec m y') →
    ∃ c, deck.pCong m c (pdotVec x y) (pdotVec x' y')
  | [], [], _, _, _, _ => deck.pCong_of m trivial
  | [], _ :: _, _, _, hx, _ => hx.elim
  | _ :: _, [], _, _, hx, _ => hx.elim
  | _ :: _, _ :: _, [], [], _, _ => deck.pCong_of m trivial
  | _ :: _, _ :: _, [], _ :: _, _, hy => hy.elim
  | _ :: _, _ :: _, _ :: _, [], _, hy => hy.elim
  | _ :: x, _ :: x', _ :: y, _ :: y', hx, hy =>
    deck.pCong_addBoth
      (deck.pCong_mulBoth (deck.pCong_of_redP m hx.1)
        (deck.pCong_of_redP m hy.1))
      (pdotVec_prowCong m x x' y y' hx.2 hy.2)

/-- The swap-adjoint engine at the raw carrier: a square matrix
whose key-list exchange reads its own memberwise swap pairs a
vector against its own image at the sum's unit.  The transpose walk
moves the matrix across the pairing, the swap read exchanges it for
the memberwise swap, and the swapped action joins the matrix's own
at a unit tail (`pdotVec_swapNull`), so the pairing reads its own
negation and sits at the unit (`poly.unitTail_of_negRead`).  The
shape binders are the frame of `def:elim`'s stated key lists, the
carrier's member definition. -/
private theorem perpSwapAdj (n : Nat) (M : elim.Mat) (hM : rowsLen n M)
    (hMl : M.length = n)
    (hsw : matOneValue (transposeM M) (matSwap M))
    (u : List poly.Poly) (hu : u.length = n) :
    poly.unitTail (pdotVec u (pmatVec M u)) := by
  have hswap : poly.oneValue (pdotVec u (pmatVec (matSwap M) u))
      (poly.neg (pdotVec u (pmatVec M u))) := by
    refine poly.ov_of_diff ?_
    rw [poly.neg_neg]
    exact pdotVec_swapNull u M u
  refine poly.unitTail_of_negRead ?_
  refine poly.oneValue_trans (pdotVec_transpose n M hM hMl u u hu hu) ?_
  exact poly.oneValue_trans
    (pdotVec_matOne (transposeM M) (matSwap M) u u hsw) hswap

/-- The doubling datum's pairing is perpendicular at every square
matrix: the datum is swap-adjoint (`band_swapAdj`), so the engine's
transpose walk reads the pairing at the sum's unit. -/
theorem perp_band (m n : Nat) (M : elim.Mat) (hM : elim.rowsLen n M)
    (hMl : M.length = n) (u : List poly.Poly) (hu : u.length = n) :
    perpRead m (bandDatum M) u := by
  have hA := bandDatum_shape n M hM hMl
  have hnull : poly.unitTail (pdotVec u (pmatVec (bandDatum M) u)) :=
    perpSwapAdj n (bandDatum M) hA.1 hA.2 (band_swapAdj n M hM hMl) u hu
  exact deck.redP_congr m
    (deck.pCong_of m
      (poly.unitTail_oneValue hnull (poly.unitTail_swapMap _ hnull)))

/-- The wrap shift's own perpendicularity, `perp_band`'s read at the
translation's permutation matrix. -/
theorem perp_wrap (m : Nat) :
    perpRead m (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m) :=
  perp_band m (2 * m + 1) (permMatAt (2 * m + 1) (tShift m))
    (rowsLen_permMatAt (2 * m + 1) (tShift m))
    (length_permMatAt (2 * m + 1) (tShift m))
    (deckColumn m) (deckColumn_len m)

/-- The key list's own fold at the deck families reads the
symbol's multiple, `Σ_{b<L} p_b = p_m P_L`: the telescope
`⟨x:2⟩ P_m + p_m = p_{m+1}` carries the two new keys at each step
and the doubling display `p_L = ⟨x:2⟩ P_L² + 2` collects them
against the square's own product read. -/
private theorem famSum_read : ∀ m : Nat,
    poly.oneValue (pfold deck.pFamN (List.range (2 * m + 1)))
      (poly.mul (deck.pFamN m) (deck.pSum m))
  | 0 => by decide +kernel
  | m + 1 => by
    have hidx : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 :=
      congrArg (fun x => x + 1) (Nat.mul_succ 2 m)
    have hsq : poly.oneValue
        (poly.mul (deck.pFamN (m + 1)) (deck.pFamN (m + 1)))
        (poly.add (deck.pFamN (2 * m + 1 + 1)) [BPair.ofNat 2]) := by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) from (Nat.mul_succ 2 m).symm]
      exact (deck.deckProducts m).2.2
    have hB : poly.oneValue
        (poly.mul (deck.pFamN (m + 1)) (deck.pSum m))
        (poly.add (poly.mul deck.chordTwo (poly.mul (deck.pSum m) (deck.pSum m)))
          (poly.mul (deck.pFamN m) (deck.pSum m))) :=
      poly.oneValue_trans
        (poly.mul_congr_left
          (poly.oneValue_symm (deck.chordTwo_pSum m)) (deck.pSum m))
        (poly.oneValue_trans
          (poly.sum_mul (poly.mul deck.chordTwo (deck.pSum m))
            (deck.pFamN m) (deck.pSum m))
          (poly.add_congr
            (poly.mul_assoc deck.chordTwo (deck.pSum m) (deck.pSum m))
            (poly.oneValue_refl _)))
    rw [hidx]
    refine poly.oneValue_trans (pfold_rangeSucc deck.pFamN (2 * m + 1 + 1)) ?_
    refine poly.oneValue_trans
      (poly.add_congr (pfold_rangeSucc deck.pFamN (2 * m + 1))
        (poly.oneValue_refl _)) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.add_congr (famSum_read m) (deck.pFamN_pSum m))
        (poly.oneValue_refl _)) ?_
    refine poly.oneValue_trans ?_
      (poly.oneValue_symm (poly.oneValue_trans
        (poly.mul_sum (deck.pFamN (m + 1)) (deck.pSum m) (deck.pFamN (m + 1)))
        (poly.add_congr hB hsq)))
    -- the four members rearranged about the two shared products
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.add_join (poly.mul (deck.pFamN m) (deck.pSum m))
          (poly.mul deck.chordTwo (poly.mul (deck.pSum m) (deck.pSum m)))
          [BPair.ofNat 2])
        (poly.oneValue_refl _)) ?_
    refine poly.oneValue_trans
      (poly.add_swap3
        (poly.add (poly.mul (deck.pFamN m) (deck.pSum m))
          (poly.mul deck.chordTwo (poly.mul (deck.pSum m) (deck.pSum m))))
        [BPair.ofNat 2] (deck.pFamN (2 * m + 1 + 1))) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.add_congr
          (poly.add_comm (poly.mul (deck.pFamN m) (deck.pSum m))
            (poly.mul deck.chordTwo (poly.mul (deck.pSum m) (deck.pSum m))))
          (poly.oneValue_refl _))
        (poly.oneValue_refl _)) ?_
    exact poly.oneValue_symm
      (poly.add_join
        (poly.add (poly.mul deck.chordTwo (poly.mul (deck.pSum m) (deck.pSum m)))
          (poly.mul (deck.pFamN m) (deck.pSum m)))
        (deck.pFamN (2 * m + 1 + 1)) [BPair.ofNat 2])

/-- The key list's fold reads the null class at the deck symbol,
the symbol's own multiple. -/
private theorem famSum_null (m : Nat) :
    ∃ c, deck.pCong m c (pfold deck.pFamN (List.range (2 * m + 1))) [] :=
  ⟨deck.pFamN m,
    poly.oneValue_trans (famSum_read m)
      (poly.mul_comm (deck.pFamN m) (deck.pSum m))⟩

/-- The key list's fold interleaves its two parities: the even
keys at the lower half and the odd keys beside them read the key
list once. -/
private theorem pfold_interleave (f : Nat → poly.Poly) : ∀ n : Nat,
    poly.oneValue (pfold f (List.range (2 * n + 1)))
      (poly.add (pfold (fun b => f (2 * b)) (List.range (n + 1)))
        (pfold (fun c => f (2 * c + 1)) (List.range n)))
  | 0 => by
    show poly.oneValue (poly.add (f 0) [])
      (poly.add (poly.add (f (2 * 0)) []) [])
    rw [poly.add_nil, poly.add_nil]
    exact poly.oneValue_refl _
  | n + 1 => by
    have hidx : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 :=
      congrArg (fun x => x + 1) (Nat.mul_succ 2 n)
    have hev : poly.oneValue
        (pfold (fun b => f (2 * b)) (List.range (n + 1 + 1)))
        (poly.add (pfold (fun b => f (2 * b)) (List.range (n + 1)))
          (f (2 * n + 1 + 1))) := by
      refine poly.oneValue_trans
        (pfold_rangeSucc (fun b => f (2 * b)) (n + 1)) ?_
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 from Nat.mul_succ 2 n]
      exact poly.oneValue_refl _
    rw [hidx]
    refine poly.oneValue_trans (pfold_rangeSucc f (2 * n + 1 + 1)) ?_
    refine poly.oneValue_trans
      (poly.add_congr (pfold_rangeSucc f (2 * n + 1)) (poly.oneValue_refl _)) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.add_congr (pfold_interleave f n) (poly.oneValue_refl _))
        (poly.oneValue_refl _)) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (poly.oneValue_symm
          (poly.add_join (pfold (fun b => f (2 * b)) (List.range (n + 1)))
            (pfold (fun c => f (2 * c + 1)) (List.range n)) (f (2 * n + 1))))
        (poly.oneValue_refl _)) ?_
    refine poly.oneValue_trans
      (poly.add_swap3 (pfold (fun b => f (2 * b)) (List.range (n + 1)))
        (poly.add (pfold (fun c => f (2 * c + 1)) (List.range n))
          (f (2 * n + 1)))
        (f (2 * n + 1 + 1))) ?_
    exact poly.add_congr (poly.oneValue_symm hev)
      (poly.oneValue_symm (pfold_rangeSucc (fun c => f (2 * c + 1)) n))

/-- The doubled keys read the key list once at the deck symbol:
the even keys outright at the lower half, the odd keys at the
upper wrap, so their fold reads the null class beside the key
list's own. -/
private theorem doubled_null (m : Nat) :
    ∃ c, deck.pCong m c
      (pfold (fun b => deck.pFamN (2 * b)) (List.range (2 * m + 1))) [] := by
  have hcut : m + 1 + m = 2 * m + 1 := by
    rw [Nat.two_mul, Nat.add_right_comm m 1 m]
  have hsplit : poly.oneValue
      (pfold (fun b => deck.pFamN (2 * b)) (List.range (2 * m + 1)))
      (poly.add (pfold (fun b => deck.pFamN (2 * b)) (List.range (m + 1)))
        (pfold (fun c => deck.pFamN (2 * (m + 1 + c))) (List.range m))) := by
    rw [← hcut, ground.range_split (m + 1) m]
    refine poly.oneValue_trans
      (pfold_append (fun b => deck.pFamN (2 * b)) (List.range (m + 1))
        ((List.range m).map (fun c => m + 1 + c))) ?_
    rw [pfold_map (fun b => deck.pFamN (2 * b)) (fun c => m + 1 + c)
      (List.range m)]
    exact poly.oneValue_refl _
  have hwrap : ∃ c, deck.pCong m c
      (pfold (fun c => deck.pFamN (2 * (m + 1 + c))) (List.range m))
      (pfold (fun c => deck.pFamN (2 * c + 1)) (List.range m)) := by
    refine pfold_pCong m m (fun i _ => ?_)
    rw [show 2 * (m + 1 + i) = 2 * m + 1 + (2 * i + 1) from by
      rw [Nat.two_mul (m + 1 + i), Nat.two_mul m, Nat.two_mul i,
        Nat.add_add_add_comm (m + 1) i (m + 1) i, Nat.add_add_add_comm m 1 m 1,
        Nat.add_add_add_comm (m + m) 1 (i + i) 1,
        Nat.add_right_comm (m + m) (1 + 1) (i + i)]]
    exact deck.pFamN_wrapUp m (2 * i + 1)
  exact deck.pCong_trans (deck.pCong_of m hsplit)
    (deck.pCong_trans
      (deck.pCong_addBoth (deck.pCong_of m (poly.oneValue_refl _)) hwrap)
      (deck.pCong_trans
        (deck.pCong_of m
          (poly.oneValue_symm (pfold_interleave deck.pFamN m)))
        (famSum_null m)))

/-- The column's self-pairing reads the doubled side: the squares
collect at the product families, the doubled keys read the key
list once, and the key list's own fold is the symbol's multiple
`p_m P_L`, null at the residue, so the constants alone stand. -/
theorem deckColumn_selfPair (m : Nat) :
    poly.oneValue
      (deck.redP m (pdotVec (deckColumn m) (deckColumn m)))
      (deck.redP m [ground.BPair.ofNat (2 * (2 * m + 1))]) := by
  refine deck.redP_congr m ?_
  rw [show deckColumn m = (List.range (2 * m + 1)).map
      (fun b => deck.redP m (deck.pFamN b)) from rfl,
    pdotVec_map]
  -- the residues clear at the squares, the product families collect
  refine deck.pCong_trans
    (pfold_pCong m (2 * m + 1) (fun b _ =>
      deck.pCong_mulBoth (deck.pCong_symm (deck.redP_pCong m (deck.pFamN b)))
        (deck.pCong_symm (deck.redP_pCong m (deck.pFamN b))))) ?_
  refine deck.pCong_trans
    (pfold_pCong m (2 * m + 1) (fun b _ =>
      deck.pCong_of m (deck.deckProducts b).1)) ?_
  refine deck.pCong_trans
    (deck.pCong_of m
      (pfold_split (fun b => deck.pFamN (2 * b))
        (fun _ => [BPair.ofNat 2]) (List.range (2 * m + 1)))) ?_
  refine deck.pCong_trans
    (deck.pCong_addBoth (doubled_null m)
      (deck.pCong_of m (pfold_two (List.range (2 * m + 1))))) ?_
  refine deck.pCong_of m ?_
  rw [ground.length_range,
    show 2 * (2 * m + 1) = 2 * m + 1 + (2 * m + 1) from Nat.two_mul (2 * m + 1)]
  exact poly.oneValue_refl _

/-- The band's own symbol `⟨4 : x²⟩`, the constant against the
chord's square that `lem:fiberdec`'s Gram determinant carries. -/
def bandPoly : poly.Poly :=
  [BPair.ofNat 4, BPair.unit, (BPair.ofNat 1).swap]

/-- The crossed pairing is the null class at the residue: the
doubling datum's pairing reads its own memberwise swap
(`perp_wrap`), the residue carries that swap (`deck.redP_neg`), and
a residue reading its own negation is a unit tail
(`poly.unitTail_of_negRead`). -/
theorem deckColumn_crossNull (m : Nat) :
    poly.oneValue
      (deck.redP m (pdotVec (deckColumn m)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m))) (deckColumn m))))
      (deck.redP m []) := by
  have hnull : poly.unitTail
      (deck.redP m (pdotVec (deckColumn m)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)))) :=
    poly.unitTail_of_negRead
      (poly.oneValue_trans (perp_wrap m) (deck.redP_neg m _))
  exact deck.redP_congr m
    (deck.pCong_trans (deck.redP_pCong m _)
      (deck.pCong_of m (poly.unitTail_oneValue hnull trivial)))

/-- The witness's range clause: the key range maps into itself. -/
private theorem sShift_lt (m : Nat) :
    ∀ j, j < 2 * m + 1 → sShift m j < 2 * m + 1 := by
  intro j hj
  cases j with
  | zero =>
    rw [sShift_zero m]
    exact Nat.succ_le_succ (Nat.le_refl (2 * m))
  | succ k =>
    rw [sShift_succ m k]
    exact Nat.lt_of_succ_lt hj

/-- The wrap shift's matrix is orthogonal, its transpose the
witness's own matrix and the two compositions the identity. -/
private theorem orth_wrap (m : Nat) :
    orthRead (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1) := by
  have hT : transposeM (permMatAt (2 * m + 1) (tShift m))
      = permMatAt (2 * m + 1) (sShift m) :=
    transposeM_permMatAt (2 * m + 1) (tShift m) (sShift m)
      (fun l _ => sShift_tShift m l) (tShift_sShift m)
  constructor
  · rw [hT]
    refine matOne_trans
      (permMatAt_mul (2 * m + 1) (tShift m) (sShift m) (sShift_lt m)) ?_
    rw [permMatAt_congr (2 * m + 1) (fun l => tShift m (sShift m l))
      (fun l => l) (fun l hl => tShift_sShift m l hl)]
    exact permMatAt_id (2 * m + 1)
  · rw [hT]
    refine matOne_trans
      (permMatAt_mul (2 * m + 1) (sShift m) (tShift m) (tShift_lt m)) ?_
    rw [permMatAt_congr (2 * m + 1) (fun l => sShift m (tShift m l))
      (fun l => l) (fun l _ => sShift_tShift m l)]
    exact permMatAt_id (2 * m + 1)

/-- A row whose every key reads the sum's unit folds to a unit
tail, the reads taken index by index. -/
private theorem scaleDot_nullIdx : ∀ (cs : List BPair) (u : List poly.Poly),
    (∀ k, k < cs.length →
      (ground.getAt BPair.unit cs k).oneValue BPair.unit) →
    poly.unitTail (poly.scaleDot cs u)
  | [], _, _ => trivial
  | _ :: _, [], _ => trivial
  | _ :: cs, p :: u, h =>
    poly.unitTail_sum
      (poly.scaleP_null (h 0 (Nat.succ_le_succ (Nat.zero_le _))) p)
      (scaleDot_nullIdx cs u (fun k hk => h (k + 1) (Nat.succ_lt_succ hk)))

/-- A one-hot row at a stated member folds to that member's own
rescaling of the selected key. -/
private theorem scaleDot_hotAt (a : BPair) : ∀ (cs : List BPair)
    (u : List poly.Poly) (j : Nat),
    cs.length = u.length →
    (ground.getAt BPair.unit cs j).oneValue a →
    (∀ k, k < cs.length → k ≠ j →
      (ground.getAt BPair.unit cs k).oneValue BPair.unit) →
    poly.oneValue (poly.scaleDot cs u)
      (poly.scaleP a (ground.getAt ([] : poly.Poly) u j))
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, hl, _, _ => Nat.noConfusion hl
  | _ :: _, [], _, hl, _, _ => Nat.noConfusion hl
  | c :: cs, p :: u, 0, _, hh, hc => by
    show poly.oneValue (poly.add (poly.scaleP c p) (poly.scaleDot cs u))
      (poly.scaleP a p)
    exact poly.oneValue_trans
      (poly.add_congr (poly.scaleP_congr hh p) (poly.oneValue_refl _))
      (poly.add_unitTail (poly.scaleP a p)
        (scaleDot_nullIdx cs u (fun k hk =>
          hc (k + 1) (Nat.succ_lt_succ hk) (fun he => Nat.noConfusion he))))
  | c :: cs, p :: u, j + 1, hl, hh, hc => by
    show poly.oneValue (poly.add (poly.scaleP c p) (poly.scaleDot cs u))
      (poly.scaleP a (ground.getAt ([] : poly.Poly) u j))
    exact poly.oneValue_trans
      (poly.unitTail_add
        (poly.scaleP_null
          (hc 0 (Nat.succ_le_succ (Nat.zero_le _))
            (fun he => Nat.noConfusion he)) p) _)
      (scaleDot_hotAt a cs u j (Nat.succ.inj hl) hh
        (fun k hk hne => hc (k + 1) (Nat.succ_lt_succ hk)
          (fun he => hne (Nat.succ.inj he))))

/-- The rescaled identity acts as its own member: the pairing
against it is the plain pairing rescaled. -/
private theorem pdotVec_scaleId (c : BPair) (n : Nat) (u v : List poly.Poly)
    (hu : u.length = n) (hv : v.length = n) :
    poly.oneValue
      (pdotVec v (pmatVec (inertia.matScaleB c (inertia.idMat n)) u))
      (poly.scaleP c (pdotVec v u)) := by
  have hIl : (inertia.idMat n).length = n := inertia.idMat_len n
  have hMl : (inertia.matScaleB c (inertia.idMat n)).length = n :=
    (ground.length_map _ (inertia.idMat n)).trans hIl
  have hml : (pmatVec (inertia.matScaleB c (inertia.idMat n)) u).length = n := by
    rw [pmatVec_len, hMl]
  rw [pdotVec_getAt v (pmatVec (inertia.matScaleB c (inertia.idMat n)) u)
      (by rw [hv, hml]), pdotVec_getAt v u (by rw [hv, hu]), hv]
  refine poly.oneValue_trans (pfold_brange n (fun i hi => ?_))
    (poly.oneValue_symm (pfold_scaleP c
      (fun i => poly.mul (ground.getAt ([] : poly.Poly) v i)
        (ground.getAt ([] : poly.Poly) u i)) (List.range n)))
  have hiM : i < (inertia.matScaleB c (inertia.idMat n)).length := by
    rw [hMl]; exact hi
  have hiI : i < (inertia.idMat n).length := by rw [hIl]; exact hi
  have hrowI : (ground.getAt ([] : List BPair) (inertia.idMat n) i).length = n :=
    rowsLen_getAt (inertia.idMat n) i (inertia.idMat_rows n) hiI
  have hgetRow : ground.getAt ([] : List BPair)
      (inertia.matScaleB c (inertia.idMat n)) i
      = (ground.getAt ([] : List BPair) (inertia.idMat n) i).map
        (fun x => (c * x).norm) :=
    ground.getAt_map ([] : List BPair) ([] : List BPair)
      (poly.scaleP c) (inertia.idMat n) i hiI
  have hrow : (ground.getAt ([] : List BPair)
      (inertia.matScaleB c (inertia.idMat n)) i).length = n := by
    rw [hgetRow, ground.length_map, hrowI]
  have hent : ∀ k, k < n → ground.getAt BPair.unit
      (ground.getAt ([] : List BPair)
        (inertia.matScaleB c (inertia.idMat n)) i) k
      = (c * (if k = i then BPair.ofNat 1 else BPair.unit)).norm := by
    intro k hk
    rw [hgetRow, ground.getAt_map BPair.unit BPair.unit
      (fun x => (c * x).norm) (ground.getAt ([] : List BPair)
        (inertia.idMat n) i) k (by rw [hrowI]; exact hk),
      inertia.getAt_idMat n i k hi hk]
  rw [pmatVec_getAt (inertia.matScaleB c (inertia.idMat n)) u i hiM]
  refine poly.oneValue_trans
    (poly.mul_congr _
      (scaleDot_hotAt c _ u i (by rw [hrow, hu]) ?_ ?_)) ?_
  · rw [hent i hi, if_pos rfl]
    exact BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.mul_ofNat_one c)
  · intro k hk hne
    rw [hrow] at hk
    rw [hent k hk, if_neg hne]
    exact BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_unit c)
  · exact poly.oneValue_trans
      (poly.mul_congr _ (poly.scaleP_single c
        (ground.getAt ([] : poly.Poly) u i)))
      (poly.oneValue_trans
        (poly.oneValue_symm (poly.mul_assoc
          (ground.getAt ([] : poly.Poly) v i)
          (ground.getAt ([] : poly.Poly) u i) [c]))
        (poly.oneValue_symm (poly.scaleP_single c
          (poly.mul (ground.getAt ([] : poly.Poly) v i)
            (ground.getAt ([] : poly.Poly) u i)))))

/-- The image's self-pairing at the residue: the doubling datum's
antisymmetry turns the image pairing into the datum's square
(`perp_pair`), the band read `A² + 4 = S²` transports it to the
chord's square (`chord_band`), the chord acts as the free chord on
the column (`colMember_wrap`), and the column's self-pairing is the
doubled side (`deckColumn_selfPair`) — so the image reads
`⟨4 : x²⟩` against `2L`. -/
theorem deckColumn_imagePair (m : Nat) :
    poly.oneValue
      (deck.redP m (pdotVec
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m))) (deckColumn m))
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m))) (deckColumn m))))
      (deck.redP m (poly.mul bandPoly [BPair.ofNat (2 * (2 * m + 1))])) := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hP : rowsLen (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) :=
    rowsLen_permMatAt (2 * m + 1) (tShift m)
  have hPl : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt (2 * m + 1) (tShift m)
  have hTtl : (transposeM (permMatAt (2 * m + 1) (tShift m))).length = 2 * m + 1 :=
    transposeLen (permMatAt (2 * m + 1) (tShift m)) hP hPl
  have hTt : rowsLen (2 * m + 1)
      (transposeM (permMatAt (2 * m + 1) (tShift m))) :=
    rowsLen_cast hPl (rowsLen_transposeM (permMatAt (2 * m + 1) (tShift m)))
  have hA : rowsLen (2 * m + 1)
      (bandDatum (permMatAt (2 * m + 1) (tShift m))) :=
    (bandDatum_shape (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) hP hPl).1
  have hAl : (bandDatum (permMatAt (2 * m + 1) (tShift m))).length = 2 * m + 1 :=
    (bandDatum_shape (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) hP hPl).2
  have hS : rowsLen (2 * m + 1) (chordOp (permMatAt (2 * m + 1) (tShift m))) :=
    rowsLen_matAdd (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) _ hP hTt
  have hSl : (chordOp (permMatAt (2 * m + 1) (tShift m))).length = 2 * m + 1 :=
    (length_matAdd (permMatAt (2 * m + 1) (tShift m)) _
      (hPl.trans hTtl.symm)).trans hPl
  have hu : (deckColumn m).length = 2 * m + 1 := deckColumn_len m
  have hAu : (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m)).length = 2 * m + 1 := by rw [pmatVec_len, hAl]
  have hSu : (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m)).length = 2 * m + 1 := by rw [pmatVec_len, hSl]
  -- the image pairing is the datum's square, negated
  have hOV : poly.oneValue
      (pdotVec (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)))
      (poly.neg (pdotVec (deckColumn m)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))))) := by
    refine poly.ov_of_diff ?_
    rw [poly.neg_neg]
    exact perp_pair (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) hP hPl
      (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m))) (deckColumn m))
      (deckColumn m) hAu hu
  -- the band read carries the square to the chord's
  have hband : poly.oneValue
      (pdotVec (deckColumn m)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))))
      (poly.add
        (pdotVec (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))
          (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m)))
        (poly.neg (poly.scaleP (BPair.ofNat 4)
          (pdotVec (deckColumn m) (deckColumn m))))) := by
    have hAA : rowsLen (2 * m + 1)
        (matMul (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (bandDatum (permMatAt (2 * m + 1) (tShift m)))) :=
      rowsLen_cast
        (transposeLen (bandDatum (permMatAt (2 * m + 1) (tShift m))) hA hAl)
        (rowsLen_matMul _ _)
    have hAAl : (matMul (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (bandDatum (permMatAt (2 * m + 1) (tShift m)))).length = 2 * m + 1 :=
      (ground.length_map _ _).trans hAl
    have hFour : rowsLen (2 * m + 1)
        (inertia.matScaleB (BPair.ofNat 4) (inertia.idMat (2 * m + 1))) :=
      rowsLen_mapRows (fun x => (BPair.ofNat 4 * x).norm)
        (inertia.idMat (2 * m + 1)) (2 * m + 1)
        (inertia.idMat_rows (2 * m + 1))
    have hFourl : (inertia.matScaleB (BPair.ofNat 4)
        (inertia.idMat (2 * m + 1))).length = 2 * m + 1 :=
      (ground.length_map _ (inertia.idMat (2 * m + 1))).trans
        (inertia.idMat_len (2 * m + 1))
    have hsplit := pdotVec_matAdd (2 * m + 1) (deckColumn m)
      (matMul (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (bandDatum (permMatAt (2 * m + 1) (tShift m))))
      (inertia.matScaleB (BPair.ofNat 4) (inertia.idMat (2 * m + 1)))
      (deckColumn m) (hAAl.trans hFourl.symm) hAA hFour
    have hcb := pdotVec_matOne _ _ (deckColumn m) (deckColumn m)
      (chord_band (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) hP hPl hn
        (orth_wrap m))
    have hcomp := pdotVec_matMul (2 * m + 1)
      (chordOp (permMatAt (2 * m + 1) (tShift m)))
      (chordOp (permMatAt (2 * m + 1) (tShift m))) hS hSl hS hSl
      (deckColumn m) (deckColumn m) hu hu
    have hsym := pdotVec_transpose (2 * m + 1)
      (chordOp (permMatAt (2 * m + 1) (tShift m))) hS hSl
      (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m))) (deckColumn m))
      (deckColumn m) hSu hu
    have hts := pdotVec_matOne
      (transposeM (chordOp (permMatAt (2 * m + 1) (tShift m))))
      (chordOp (permMatAt (2 * m + 1) (tShift m))) (deckColumn m)
      (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m))) (deckColumn m))
      (transposeM_chordOp (2 * m + 1) (permMatAt (2 * m + 1) (tShift m))
        hP hPl hn)
    have hchain : poly.oneValue
        (poly.add
          (pdotVec (deckColumn m)
            (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
              (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
                (deckColumn m))))
          (poly.scaleP (BPair.ofNat 4)
            (pdotVec (deckColumn m) (deckColumn m))))
        (pdotVec (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))
          (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))) := by
      refine poly.oneValue_trans
        (poly.add_congr
          (poly.oneValue_symm (pdotVec_matMul (2 * m + 1)
            (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (bandDatum (permMatAt (2 * m + 1) (tShift m))) hA hAl hA hAl
            (deckColumn m) (deckColumn m) hu hu))
          (poly.oneValue_symm (pdotVec_scaleId (BPair.ofNat 4) (2 * m + 1)
            (deckColumn m) (deckColumn m) hu hu))) ?_
      refine poly.oneValue_trans (poly.oneValue_symm hsplit) ?_
      exact poly.oneValue_trans hcb
        (poly.oneValue_trans hcomp (poly.oneValue_trans hsym hts))
    refine poly.oneValue_trans
      (poly.oneValue_symm
        (poly.oneValue_trans
          (poly.oneValue_symm (poly.add_join
            (pdotVec (deckColumn m)
              (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
                (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
                  (deckColumn m))))
            (poly.scaleP (BPair.ofNat 4)
              (pdotVec (deckColumn m) (deckColumn m)))
            (poly.neg (poly.scaleP (BPair.ofNat 4)
              (pdotVec (deckColumn m) (deckColumn m))))))
          (poly.add_unitTail _
            (poly.add_neg (poly.scaleP (BPair.ofNat 4)
              (pdotVec (deckColumn m) (deckColumn m))))))) ?_
    exact poly.add_congr hchain (poly.oneValue_refl _)
  -- the chord's own square at the residue
  have hchord : ∃ c, deck.pCong m c
      (pdotVec (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))
        (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)))
      (poly.mul (poly.mul deck.wPoly deck.wPoly)
        (pdotVec (deckColumn m) (deckColumn m))) := by
    refine deck.pCong_trans
      (pdotVec_prowCong m _ _ _ _ (colMember_wrap m) (colMember_wrap m)) ?_
    refine deck.pCong_of m ?_
    rw [show (deckColumn m).map (fun p => poly.mul deck.wPoly p)
        = (List.range (2 * m + 1)).map
          (fun b => poly.mul deck.wPoly (deck.redP m (deck.pFamN b))) from
      ground.map_map _ _ (List.range (2 * m + 1)),
      show deckColumn m = (List.range (2 * m + 1)).map
        (fun b => deck.redP m (deck.pFamN b)) from rfl,
      pdotVec_map, pdotVec_map]
    refine poly.oneValue_trans
      (pfold_brange (2 * m + 1) (fun b _ => ?_))
      (poly.oneValue_symm (pfold_mulL (poly.mul deck.wPoly deck.wPoly)
        (fun b => poly.mul (deck.redP m (deck.pFamN b))
          (deck.redP m (deck.pFamN b))) (List.range (2 * m + 1))))
    exact poly.oneValue_trans
      (poly.mul_assoc deck.wPoly (deck.redP m (deck.pFamN b))
        (poly.mul deck.wPoly (deck.redP m (deck.pFamN b))))
      (poly.oneValue_trans
        (poly.mul_congr deck.wPoly
          (poly.mul_left_comm (deck.redP m (deck.pFamN b)) deck.wPoly
            (deck.redP m (deck.pFamN b))))
        (poly.oneValue_symm (poly.mul_assoc deck.wPoly deck.wPoly
          (poly.mul (deck.redP m (deck.pFamN b))
            (deck.redP m (deck.pFamN b))))))
  -- the two members collect against the doubled side
  have hcol : ∃ c, deck.pCong m c
      (poly.add
        (pdotVec (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))
          (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m)))
        (poly.neg (poly.scaleP (BPair.ofNat 4)
          (pdotVec (deckColumn m) (deckColumn m)))))
      (poly.add
        (poly.mul (poly.mul deck.wPoly deck.wPoly)
          [BPair.ofNat (2 * (2 * m + 1))])
        (poly.neg (poly.mul [BPair.ofNat (2 * (2 * m + 1))]
          [BPair.ofNat 4]))) :=
    deck.pCong_addBoth
      (deck.pCong_trans hchord
        (deck.pCong_mulBoth (deck.pCong_of m (poly.oneValue_refl _))
          (deck.pCong_of_redP m (deckColumn_selfPair m))))
      (deck.pCong_neg m (deck.pCong_trans
        (deck.pCong_of m (poly.scaleP_single (BPair.ofNat 4)
          (pdotVec (deckColumn m) (deckColumn m))))
        (deck.pCong_mulBoth (deck.pCong_of_redP m (deckColumn_selfPair m))
          (deck.pCong_of m (poly.oneValue_refl _)))))
  -- the band symbol at the fixed polynomials
  have hband4 : poly.oneValue bandPoly
      (poly.add [BPair.ofNat 4]
        (poly.neg (poly.mul deck.wPoly deck.wPoly))) := by decide +kernel
  have hnegmul : poly.oneValue
      (poly.neg (poly.mul (poly.mul deck.wPoly deck.wPoly)
        [BPair.ofNat (2 * (2 * m + 1))]))
      (poly.mul (poly.neg (poly.mul deck.wPoly deck.wPoly))
        [BPair.ofNat (2 * (2 * m + 1))]) := by
    refine poly.oneValue_trans
      (poly.swapMap_oneValue (poly.mul_comm
        (poly.mul deck.wPoly deck.wPoly)
        [BPair.ofNat (2 * (2 * m + 1))])) ?_
    rw [poly.neg_prod]
    exact poly.mul_comm [BPair.ofNat (2 * (2 * m + 1))]
      (poly.neg (poly.mul deck.wPoly deck.wPoly))
  have hfinal : poly.oneValue
      (poly.neg (poly.add
        (poly.mul (poly.mul deck.wPoly deck.wPoly)
          [BPair.ofNat (2 * (2 * m + 1))])
        (poly.neg (poly.mul [BPair.ofNat (2 * (2 * m + 1))]
          [BPair.ofNat 4]))))
      (poly.mul bandPoly [BPair.ofNat (2 * (2 * m + 1))]) := by
    rw [poly.neg_sum, poly.neg_neg]
    refine poly.oneValue_trans
      (poly.add_congr hnegmul
        (poly.mul_comm [BPair.ofNat (2 * (2 * m + 1))] [BPair.ofNat 4])) ?_
    refine poly.oneValue_trans
      (poly.add_comm
        (poly.mul (poly.neg (poly.mul deck.wPoly deck.wPoly))
          [BPair.ofNat (2 * (2 * m + 1))])
        (poly.mul [BPair.ofNat 4] [BPair.ofNat (2 * (2 * m + 1))])) ?_
    refine poly.oneValue_trans
      (poly.oneValue_symm (poly.sum_mul [BPair.ofNat 4]
        (poly.neg (poly.mul deck.wPoly deck.wPoly))
        [BPair.ofNat (2 * (2 * m + 1))])) ?_
    exact poly.mul_congr_left (poly.oneValue_symm hband4)
      [BPair.ofNat (2 * (2 * m + 1))]
  exact deck.redP_congr m
    (deck.pCong_trans (deck.pCong_of m hOV)
      (deck.pCong_trans (deck.pCong_neg m (deck.pCong_of m hband))
        (deck.pCong_trans (deck.pCong_neg m hcol)
          (deck.pCong_of m hfinal))))

/-- The doubled side's square reads four times the side's own. -/
private theorem sideSq (m : Nat) :
    4 * ((2 * m + 1) * (2 * m + 1))
      = 2 * (2 * m + 1) * (2 * (2 * m + 1)) := by
  rw [ground.natMulAssoc 2 (2 * m + 1) (2 * (2 * m + 1)),
    ← ground.natMulAssoc (2 * m + 1) 2 (2 * m + 1),
    Nat.mul_comm (2 * m + 1) 2,
    ground.natMulAssoc 2 (2 * m + 1) (2 * m + 1),
    ← ground.natMulAssoc 2 2 ((2 * m + 1) * (2 * m + 1))]

/-- The pair's Gram determinant at the wrap shift: the crossed
pairing is null (`deckColumn_crossNull`), so the diagonal product
alone stands — the column's own doubled side against the image's
`⟨4 : x²⟩` read — and the two constants collect at `4L²`. -/
theorem gramDet_wrap (m : Nat) :
    poly.oneValue
      (gramDet m (bandDatum (permMatAt (2 * m + 1) (tShift m))) (deckColumn m))
      (deck.redP m (poly.mul bandPoly
        [BPair.ofNat (4 * ((2 * m + 1) * (2 * m + 1)))])) := by
  have harith : poly.oneValue
      (poly.add (poly.mul [BPair.ofNat (2 * (2 * m + 1))]
          (poly.mul bandPoly [BPair.ofNat (2 * (2 * m + 1))]))
        (poly.neg (poly.mul ([] : poly.Poly)
          (pdotVec (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m)) (deckColumn m)))))
      (poly.mul bandPoly
        [BPair.ofNat (4 * ((2 * m + 1) * (2 * m + 1)))]) := by
    rw [show poly.neg (poly.mul ([] : poly.Poly)
        (pdotVec (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)) (deckColumn m))) = ([] : poly.Poly) from rfl,
      poly.add_nil]
    refine poly.oneValue_trans
      (poly.mul_left_comm [BPair.ofNat (2 * (2 * m + 1))] bandPoly
        [BPair.ofNat (2 * (2 * m + 1))]) ?_
    refine poly.mul_congr bandPoly ?_
    refine poly.oneValue_trans
      (poly.mul_single [BPair.ofNat (2 * (2 * m + 1))]
        (BPair.ofNat (2 * (2 * m + 1)))) ?_
    show poly.oneValue
      [BPair.ofNat (2 * (2 * m + 1)) * BPair.ofNat (2 * (2 * m + 1))]
      [BPair.ofNat (4 * ((2 * m + 1) * (2 * m + 1)))]
    rw [sideSq m]
    exact ⟨BPair.oneValue_symm
      (BPair.ofNat_mul (2 * (2 * m + 1)) (2 * (2 * m + 1))), trivial⟩
  exact deck.redP_congr m
    (deck.pCong_trans
      (deck.pCong_addBoth
        (deck.pCong_mulBoth (deck.pCong_of_redP m (deckColumn_selfPair m))
          (deck.pCong_of_redP m (deckColumn_imagePair m)))
        (deck.pCong_neg m
          (deck.pCong_mulBoth (deck.pCong_of_redP m (deckColumn_crossNull m))
            (deck.pCong_of m (poly.oneValue_refl _)))))
      (deck.pCong_of m harith))

/-- The band symbol against the joined cofactors reads the swapped
side-parity constant modulo the deck symbol: the two ends'
congruences multiply, the chord factors collect to the band
symbol's own negation, and the two remainders' product is the
side against the depth's parity member. -/
theorem bandCof_pCong (m : Nat) :
    ∃ c, deck.pCong m c
      (poly.mul bandPoly (deck.gramCof m))
      [(BPair.ofNat (2 * m + 1) * deck.parityMember m).swap] := by
  have hbp : poly.oneValue bandPoly
      (poly.neg (poly.mul deck.chordTwo deck.chordPartner)) := by decide +kernel
  have hgroup : poly.oneValue (poly.mul bandPoly (deck.gramCof m))
      (poly.neg (poly.mul
        (poly.mul deck.chordTwo
          (poly.div [(BPair.ofNat 2).swap] (deck.pSum m)).1)
        (poly.mul deck.chordPartner
          (poly.div [BPair.ofNat 2] (deck.pSum m)).1))) := by
    refine poly.oneValue_trans
      (poly.mul_congr_left hbp (deck.gramCof m)) ?_
    refine poly.oneValue_trans
      (poly.neg_prod_left (poly.mul deck.chordTwo deck.chordPartner)
        (deck.gramCof m)) ?_
    exact poly.swapMap_oneValue
      (poly.mul_exchange4 deck.chordTwo deck.chordPartner
        (poly.div [(BPair.ofNat 2).swap] (deck.pSum m)).1
        (poly.div [BPair.ofNat 2] (deck.pSum m)).1)
  have hends : ∃ c, deck.pCong m c
      (poly.neg (poly.mul
        (poly.mul deck.chordTwo
          (poly.div [(BPair.ofNat 2).swap] (deck.pSum m)).1)
        (poly.mul deck.chordPartner
          (poly.div [BPair.ofNat 2] (deck.pSum m)).1)))
      (poly.neg (poly.mul (poly.neg [BPair.ofNat (2 * m + 1)])
        (poly.neg [deck.parityMember m]))) :=
    deck.pCong_neg m
      (deck.pCong_mulBoth (deck.cofTwo_pCong m) (deck.cofPartner_pCong m))
  have hclose : poly.oneValue
      (poly.neg (poly.mul (poly.neg [BPair.ofNat (2 * m + 1)])
        (poly.neg [deck.parityMember m])))
      [(BPair.ofNat (2 * m + 1) * deck.parityMember m).swap] := by
    have hpair : poly.oneValue
        (poly.neg (poly.mul (poly.neg [BPair.ofNat (2 * m + 1)])
          (poly.neg [deck.parityMember m])))
        (poly.neg (poly.mul [BPair.ofNat (2 * m + 1)]
          [deck.parityMember m])) := by
      refine poly.swapMap_oneValue ?_
      rw [← poly.neg_prod (poly.neg [BPair.ofNat (2 * m + 1)])
        [deck.parityMember m]]
      refine poly.oneValue_trans
        (poly.swapMap_oneValue
          (poly.neg_prod_left [BPair.ofNat (2 * m + 1)]
            [deck.parityMember m])) ?_
      show poly.oneValue
        (poly.neg (poly.neg (poly.mul [BPair.ofNat (2 * m + 1)]
          [deck.parityMember m])))
        (poly.mul [BPair.ofNat (2 * m + 1)] [deck.parityMember m])
      rw [poly.neg_neg]
      exact poly.oneValue_refl _
    refine poly.oneValue_trans hpair ?_
    refine poly.oneValue_trans
      (poly.swapMap_oneValue
        (poly.mul_single [BPair.ofNat (2 * m + 1)]
          (deck.parityMember m))) ?_
    show poly.oneValue
      [(deck.parityMember m * BPair.ofNat (2 * m + 1)).swap]
      [(BPair.ofNat (2 * m + 1) * deck.parityMember m).swap]
    exact ⟨ground.swap_congr (BPair.oneValue_of_eq
      (BPair.mul_comm (deck.parityMember m) (BPair.ofNat (2 * m + 1)))),
      trivial⟩
  exact deck.pCong_trans (deck.pCong_of m hgroup)
    (deck.pCong_trans hends (deck.pCong_of m hclose))

/-- An occupied-length factor of the deck symbol refuses the band
symbol's division: at a stated monic factor with its cofactor, the
band symbol's remainder at the factor is occupied, the composed
witness's occupied constant refusing the division — the
equal-members case refused at every stored root, the block
pairing's lower side closing the strict interiority. -/
theorem bandFree_factor (m : Nat) (f A : poly.Poly)
    (hf : 0 < f.length)
    (hfac : poly.oneValue (poly.mul (poly.monic f) A) (deck.pSum m)) :
    ¬ poly.unitTail (poly.div f bandPoly).2 := by
  intro hband
  obtain ⟨c, hc⟩ := bandCof_pCong m
  have hstep1 : poly.oneValue
      (poly.mul (poly.monic f) (poly.div f bandPoly).1) bandPoly :=
    poly.oneValue_trans
      (poly.oneValue_symm
        (poly.add_unitTail
          (poly.mul (poly.monic f) (poly.div f bandPoly).1) hband))
      (poly.div_identity f bandPoly)
  have h3 : poly.oneValue
      (poly.mul (poly.monic f)
        (poly.add (poly.mul (poly.div f bandPoly).1 (deck.gramCof m))
          (poly.neg (poly.mul A c))))
      [(BPair.ofNat (2 * m + 1) * deck.parityMember m).swap] := by
    refine poly.oneValue_trans
      (poly.mul_sum (poly.monic f)
        (poly.mul (poly.div f bandPoly).1 (deck.gramCof m))
        (poly.neg (poly.mul A c))) ?_
    have hleft : poly.oneValue
        (poly.mul (poly.monic f)
          (poly.mul (poly.div f bandPoly).1 (deck.gramCof m)))
        (poly.add [(BPair.ofNat (2 * m + 1) * deck.parityMember m).swap]
          (poly.mul (deck.pSum m) c)) :=
      poly.oneValue_trans
        (poly.oneValue_symm
          (poly.mul_assoc (poly.monic f) (poly.div f bandPoly).1
            (deck.gramCof m)))
        (poly.oneValue_trans
          (poly.mul_congr_left hstep1 (deck.gramCof m)) hc)
    have hright : poly.oneValue
        (poly.mul (poly.monic f) (poly.neg (poly.mul A c)))
        (poly.neg (poly.mul (deck.pSum m) c)) := by
      rw [← poly.neg_prod (poly.monic f) (poly.mul A c)]
      refine poly.swapMap_oneValue ?_
      exact poly.oneValue_trans
        (poly.oneValue_symm (poly.mul_assoc (poly.monic f) A c))
        (poly.mul_congr_left hfac c)
    refine poly.oneValue_trans (poly.add_congr hleft hright) ?_
    refine poly.oneValue_trans
      (poly.oneValue_symm
        (poly.add_join [(BPair.ofNat (2 * m + 1) * deck.parityMember m).swap]
          (poly.mul (deck.pSum m) c)
          (poly.neg (poly.mul (deck.pSum m) c)))) ?_
    exact poly.add_unitTail _ (poly.add_neg (poly.mul (deck.pSum m) c))
  have hR : ([(BPair.ofNat (2 * m + 1) * deck.parityMember m).swap]
      : poly.Poly).length ≤ f.length := hf
  have hD : poly.unitTail
      (poly.add (poly.mul (poly.div f bandPoly).1 (deck.gramCof m))
        (poly.neg (poly.mul A c))) :=
    poly.monic_cancel
      (poly.add (poly.mul (poly.div f bandPoly).1 (deck.gramCof m))
        (poly.neg (poly.mul A c))).length f
      (poly.add (poly.mul (poly.div f bandPoly).1 (deck.gramCof m))
        (poly.neg (poly.mul A c)))
      [(BPair.ofNat (2 * m + 1) * deck.parityMember m).swap]
      (Nat.le_refl _) hR h3
  have hu := (poly.unitTail_oneValue_right
    (poly.mul_unitTail (poly.monic f) hD) h3).1
  have hL : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  cases deck.parityMember_cases m with
  | inl he =>
    rw [he] at hu
    refine BPair.ofNat_swap_off (2 * m + 1) hL ?_
    exact BPair.oneValue_trans
      (ground.swap_congr
        (BPair.oneValue_symm
          (BPair.mul_ofNat_one (BPair.ofNat (2 * m + 1)))))
      hu
  | inr he =>
    rw [he, BPair.mul_swap, BPair.swap_swap] at hu
    refine BPair.ofNat_off_unit (2 * m + 1) hL ?_
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.mul_ofNat_one (BPair.ofNat (2 * m + 1))))
      hu

/-- The pair's independence over the remainder lists at every
successor side: the Gram determinant against the band ends' divided
cofactors (`deck.gramCof`) clears `⟨4 : x²⟩` at the composed
witness (`bandCof_pCong`) to the constant `4L³` at the depth's
parity member, occupied at the side's positivity — the Bézout
witness `lem:fiberdec` asks for. -/
theorem gramUnit_wrap (m : Nat) :
    gramUnitRead (m + 1)
      (bandDatum (permMatAt (2 * (m + 1) + 1) (tShift (m + 1))))
      (deckColumn (m + 1)) (deck.gramCof (m + 1))
      (BPair.ofNat (4 * ((2 * (m + 1) + 1)
          * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1))))
        * (deck.parityMember (m + 1)).swap) := by
  have hL : 0 < 2 * (m + 1) + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hN : 0 < 4 * ((2 * (m + 1) + 1)
      * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1))) :=
    Nat.mul_pos (by decide +kernel) (Nat.mul_pos hL (Nat.mul_pos hL hL))
  refine ⟨?_, ?_⟩
  · -- the constant is occupied at either parity
    cases deck.parityMember_cases (m + 1) with
    | inl he =>
      rw [he]
      intro hh
      refine BPair.ofNat_swap_off _ hN ?_
      refine BPair.oneValue_trans ?_ hh
      rw [BPair.mul_swap (BPair.ofNat (4 * ((2 * (m + 1) + 1)
        * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1))))) (BPair.ofNat 1)]
      exact ground.swap_congr (BPair.oneValue_symm
        (BPair.mul_ofNat_one (BPair.ofNat (4 * ((2 * (m + 1) + 1)
          * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))))))
    | inr he =>
      rw [he, BPair.swap_swap]
      intro hh
      refine BPair.ofNat_off_unit _ hN ?_
      exact BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.mul_ofNat_one _)) hh
  · -- the determinant against the cofactor reads the cleared constant
    have hgd : ∃ c, deck.pCong (m + 1) c
        (gramDet (m + 1)
          (bandDatum (permMatAt (2 * (m + 1) + 1) (tShift (m + 1))))
          (deckColumn (m + 1)))
        (poly.mul bandPoly [BPair.ofNat (4 * ((2 * (m + 1) + 1)
          * (2 * (m + 1) + 1)))]) :=
      deck.pCong_trans (deck.pCong_of (m + 1) (gramDet_wrap (m + 1)))
        (deck.pCong_symm (deck.redP_pCong (m + 1) _))
    have hgroup : poly.oneValue
        (poly.mul (poly.mul bandPoly
            [BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))])
          (deck.gramCof (m + 1)))
        (poly.mul (poly.mul bandPoly (deck.gramCof (m + 1)))
          [BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))]) := by
      refine poly.oneValue_trans
        (poly.mul_assoc bandPoly
          [BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))]
          (deck.gramCof (m + 1))) ?_
      refine poly.oneValue_trans
        (poly.mul_congr bandPoly
          (poly.mul_comm
            [BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))]
            (deck.gramCof (m + 1)))) ?_
      exact poly.oneValue_symm
        (poly.mul_assoc bandPoly (deck.gramCof (m + 1))
          [BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))])
    have hclose : poly.oneValue
        (poly.mul
          [(BPair.ofNat (2 * (m + 1) + 1) * deck.parityMember (m + 1)).swap]
          [BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))])
        [BPair.ofNat (4 * ((2 * (m + 1) + 1)
            * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1))))
          * (deck.parityMember (m + 1)).swap] := by
      refine poly.oneValue_trans
        (poly.mul_single
          [(BPair.ofNat (2 * (m + 1) + 1) * deck.parityMember (m + 1)).swap]
          (BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1))))) ?_
      show poly.oneValue
        [BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))
          * (BPair.ofNat (2 * (m + 1) + 1) * deck.parityMember (m + 1)).swap]
        [BPair.ofNat (4 * ((2 * (m + 1) + 1)
            * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1))))
          * (deck.parityMember (m + 1)).swap]
      refine ⟨?_, trivial⟩
      rw [BPair.mul_swap
          (BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1))))
          (BPair.ofNat (2 * (m + 1) + 1) * deck.parityMember (m + 1)),
        ← BPair.mul_assoc
          (BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1))))
          (BPair.ofNat (2 * (m + 1) + 1)) (deck.parityMember (m + 1)),
        ← BPair.mul_swap
          (BPair.ofNat (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))
            * BPair.ofNat (2 * (m + 1) + 1)) (deck.parityMember (m + 1))]
      refine BPair.mul_congr ?_ (BPair.oneValue_refl _)
      refine BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.ofNat_mul
          (4 * ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)))
          (2 * (m + 1) + 1))) ?_
      rw [ground.natMulAssoc 4
          ((2 * (m + 1) + 1) * (2 * (m + 1) + 1)) (2 * (m + 1) + 1),
        ground.natMulAssoc (2 * (m + 1) + 1) (2 * (m + 1) + 1)
          (2 * (m + 1) + 1)]
      exact BPair.oneValue_refl _
    refine poly.oneValue_trans
      (deck.redP_congr (m + 1)
        (deck.pCong_trans
          (deck.pCong_mulBoth hgd
            (deck.pCong_of (m + 1) (poly.oneValue_refl _)))
          (deck.pCong_trans (deck.pCong_of (m + 1) hgroup)
            (deck.pCong_trans
              (deck.pCong_mulBoth (bandCof_pCong (m + 1))
                (deck.pCong_of (m + 1) (poly.oneValue_refl _)))
              (deck.pCong_of (m + 1) hclose))))) ?_
    exact deck.redP_short (m + 1) _ (Nat.succ_le_succ (Nat.zero_le m))

/-! The count squeeze at the residue, `lem:fiberdec`'s own
splitting read at stated lists.  The pair base enters as the
deck-family column's coefficient rows, one row per key below the
residue's top against its image under the doubling datum
(`sliceAt`, `pairBase`), and the orbit's own sum joins them
(`orbitSum`) at the orbit's count `1 + 2m = L`.  The first read
here is the identification at the wrap shift, `D₁ᵀ D₁ + S = 2` at
the datum `D₁` of `1 + D₁ = T` (`identRead_wrap` at `ident_of`,
the product `Tᵀ T = 1` expanded and the two memberwise swaps
clearing against their own). -/

/-- The orbit's own sum: the ones row at the side. -/
def orbitSum (m : Nat) : List BPair :=
  List.replicate (2 * m + 1) (BPair.ofPos .one)

/-- A polynomial vector's degree slice: the stated key's
coefficients. -/
def sliceAt (i : Nat) (u : List poly.Poly) : List BPair :=
  u.map (fun p => ground.getAt BPair.unit p i)

/-- The pair base: the deck-family column's coefficient rows, one
row per key below the residue's top, each member against its
`A`-image (lem:fiberdec's splitting read). -/
def pairBase (m : Nat) : Mat :=
  (List.range m).flatMap (fun i =>
    [sliceAt i (deckColumn m),
     elim.matVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
       (sliceAt i (deckColumn m))])

/-- The orbit sum's count is the side. -/
private theorem orbitSum_len (m : Nat) : (orbitSum m).length = 2 * m + 1 :=
  ground.length_replicate (BPair.ofPos Pos.one) (2 * m + 1)

/-- A paired family's join counts twice its key list. -/
private theorem flatMapPair_len {α : Type} (f g : α → List BPair) :
    ∀ l : List α, (l.flatMap (fun a => [f a, g a])).length = 2 * l.length
  | [] => rfl
  | a :: t => by
    show ([f a, g a] ++ t.flatMap (fun a => [f a, g a])).length
      = 2 * (t.length + 1)
    rw [ground.length_append, flatMapPair_len f g t]
    show 2 + 2 * t.length = 2 * (t.length + 1)
    rw [Nat.mul_succ, Nat.add_comm (2 * t.length) 2]

/-- The pair base's row count is the doubled depth. -/
theorem pairBase_len (m : Nat) : (pairBase m).length = 2 * m :=
  (flatMapPair_len _ _ (List.range m)).trans
    (congrArg (fun k => 2 * k) (ground.length_range m))

/-- The identification at a translation's own matrix: the product
`Tᵀ T = 1` expands the datum's square, the chord joins it, and the
two memberwise swaps clear against their own, `D₁ᵀ D₁ + S = 2` at
the datum `D₁` of `1 + D₁ = T`. -/
private theorem ident_of (n : Nat) (Pm : Mat) (hP : rowsLen n Pm)
    (hPl : Pm.length = n) (hn : 0 < n)
    (horth : matOneValue (matMul (transposeM Pm) Pm) (inertia.idMat n)) :
    identRead Pm n := by
  have hI : rowsLen n (inertia.idMat n) := inertia.idMat_rows n
  have hIl : (inertia.idMat n).length = n := inertia.idMat_len n
  have hSwI : rowsLen n (matSwap (inertia.idMat n)) :=
    rowsLen_mapRows BPair.swap (inertia.idMat n) n hI
  have hSwIl : (matSwap (inertia.idMat n)).length = n :=
    (ground.length_map _ (inertia.idMat n)).trans hIl
  have hT : rowsLen n (transposeM Pm) :=
    rowsLen_cast hPl (rowsLen_transposeM Pm)
  have hTl : (transposeM Pm).length = n := transposeLen Pm hP hPl
  have hSwP : rowsLen n (matSwap Pm) := rowsLen_mapRows BPair.swap Pm n hP
  have hSwPl : (matSwap Pm).length = n :=
    (ground.length_map _ Pm).trans hPl
  have hSwT : rowsLen n (matSwap (transposeM Pm)) :=
    rowsLen_mapRows BPair.swap (transposeM Pm) n hT
  have hSwTl : (matSwap (transposeM Pm)).length = n :=
    (ground.length_map _ (transposeM Pm)).trans hTl
  have hD : rowsLen n (inertia.siteDatum Pm (inertia.idMat n)) :=
    rowsLen_matAdd n Pm (matSwap (inertia.idMat n)) hP hSwI
  have hDl : (inertia.siteDatum Pm (inertia.idMat n)).length = n :=
    (length_matAdd Pm _ (hPl.trans hSwIl.symm)).trans hPl
  have hDt : rowsLen n (transposeM (inertia.siteDatum Pm (inertia.idMat n))) :=
    rowsLen_cast hDl
      (rowsLen_transposeM (inertia.siteDatum Pm (inertia.idMat n)))
  have hDtl : (transposeM (inertia.siteDatum Pm (inertia.idMat n))).length = n :=
    transposeLen (inertia.siteDatum Pm (inertia.idMat n)) hD hDl
  have hSwIt : (transposeM (matSwap (inertia.idMat n))).length = n :=
    transposeLen (matSwap (inertia.idMat n)) hSwI hSwIl
  have hDT : transposeM (inertia.siteDatum Pm (inertia.idMat n))
      = matAdd (transposeM Pm) (matSwap (inertia.idMat n)) := by
    show transposeM (matAdd Pm (matSwap (inertia.idMat n))) = _
    rw [transposeM_matAdd Pm (matSwap (inertia.idMat n)) hP hSwI
        (hPl.trans hSwIl.symm) (by rw [hPl]; exact hn),
      transposeM_swap (inertia.idMat n), inertia.transposeM_idMat n hn]
  -- the datum's square at the two products
  have hleft : matOneValue
      (matMul (transposeM Pm) (inertia.siteDatum Pm (inertia.idMat n)))
      (matAdd (inertia.idMat n) (matSwap (transposeM Pm))) := by
    refine matOne_trans
      (matMul_addR Pm (matSwap (inertia.idMat n)) hP hSwI
        (hPl.trans hSwIl.symm) (by rw [hPl]; exact hn) (transposeM Pm)
        (rowsLen_cast hPl.symm hT)) ?_
    refine matAdd_cong2 n _ _ _ _
      (rowsLen_cast hTl (rowsLen_matMul (transposeM Pm) Pm))
      (rowsLen_cast hSwIt
        (rowsLen_matMul (transposeM Pm) (matSwap (inertia.idMat n))))
      hI hSwT horth ?_
    rw [matMul_swap]
    exact matSwap_congr
      (inertia.matMul_idR n (transposeM Pm) hT hTl hn hn)
  have hright : matOneValue
      (matMul (matSwap (inertia.idMat n))
        (inertia.siteDatum Pm (inertia.idMat n)))
      (matAdd (matSwap Pm) (inertia.idMat n)) := by
    rw [matMul_swapL]
    refine matOne_trans
      (matSwap_congr (inertia.idMat_matMul n
        (inertia.siteDatum Pm (inertia.idMat n)) hD hDl hn)) ?_
    show matOneValue (matSwap (matAdd Pm (matSwap (inertia.idMat n))))
      (matAdd (matSwap Pm) (inertia.idMat n))
    rw [matSwap_matAdd, matSwap_matSwap]
    exact matOne_refl _
  have hsq : matOneValue
      (matMul (transposeM (inertia.siteDatum Pm (inertia.idMat n)))
        (inertia.siteDatum Pm (inertia.idMat n)))
      (matAdd (matAdd (inertia.idMat n) (matSwap (transposeM Pm)))
        (matAdd (matSwap Pm) (inertia.idMat n))) := by
    rw [hDT]
    refine matOne_trans
      (matMul_addL n (inertia.siteDatum Pm (inertia.idMat n)) hDt
        (transposeM Pm) (matSwap (inertia.idMat n)) hT hSwI) ?_
    exact matAdd_cong2 n _ _ _ _
      (rowsLen_cast hDtl
        (rowsLen_matMul (transposeM Pm)
          (inertia.siteDatum Pm (inertia.idMat n))))
      (rowsLen_cast hDtl
        (rowsLen_matMul (matSwap (inertia.idMat n))
          (inertia.siteDatum Pm (inertia.idMat n))))
      (rowsLen_matAdd n _ _ hI hSwT) (rowsLen_matAdd n _ _ hSwP hI)
      hleft hright
  -- the four members collect against the chord's own two
  show matOneValue
    (matAdd (matMul (transposeM (inertia.siteDatum Pm (inertia.idMat n)))
        (inertia.siteDatum Pm (inertia.idMat n)))
      (chordOp Pm))
    (inertia.matScaleB (BPair.ofNat 2) (inertia.idMat n))
  refine matOne_trans
    (matAdd_cong2 n _ _ _ _
      (rowsLen_cast hDtl
        (rowsLen_matMul (transposeM (inertia.siteDatum Pm (inertia.idMat n)))
          (inertia.siteDatum Pm (inertia.idMat n))))
      (rowsLen_matAdd n Pm (transposeM Pm) hP hT)
      (rowsLen_matAdd n _ _ (rowsLen_matAdd n _ _ hI hSwT)
        (rowsLen_matAdd n _ _ hSwP hI))
      (rowsLen_matAdd n _ _ hT hP)
      hsq ?_) ?_
  · show matOneValue (matAdd Pm (transposeM Pm)) (matAdd (transposeM Pm) Pm)
    rw [matAdd_comm Pm (transposeM Pm)]
    exact matOne_refl _
  rw [matAdd_comm (matSwap Pm) (inertia.idMat n),
    matAdd_shuffle (inertia.idMat n) (matSwap (transposeM Pm))
      (inertia.idMat n) (matSwap Pm),
    matAdd_assoc (matAdd (inertia.idMat n) (inertia.idMat n))
      (matAdd (matSwap (transposeM Pm)) (matSwap Pm))
      (matAdd (transposeM Pm) Pm),
    matAdd_shuffle (matSwap (transposeM Pm)) (matSwap Pm)
      (transposeM Pm) Pm,
    matAdd_comm (matAdd (inertia.idMat n) (inertia.idMat n))
      (matAdd (matAdd (matSwap (transposeM Pm)) (transposeM Pm))
        (matAdd (matSwap Pm) Pm)),
    matAdd_assoc (matAdd (matSwap (transposeM Pm)) (transposeM Pm))
      (matAdd (matSwap Pm) Pm)
      (matAdd (inertia.idMat n) (inertia.idMat n))]
  refine matOne_trans
    (matAdd_nullL (matAdd (matSwap (transposeM Pm)) (transposeM Pm)) _
      (matNull_swap_add (matOne_refl (transposeM Pm)))
      (by rw [length_matAdd _ _ (hSwTl.trans hTl.symm),
          length_matAdd (matAdd (matSwap Pm) Pm) _
            (by rw [length_matAdd _ _ (hSwPl.trans hPl.symm), hSwPl,
                length_matAdd _ _ (hIl.trans hIl.symm), hIl]),
          length_matAdd _ _ (hSwPl.trans hPl.symm), hSwTl, hSwPl])
      (rowsLen_matAdd n _ _ hSwT hT)
      (rowsLen_matAdd n _ _ (rowsLen_matAdd n _ _ hSwP hP)
        (rowsLen_matAdd n _ _ hI hI))) ?_
  refine matOne_trans
    (matAdd_nullL (matAdd (matSwap Pm) Pm) _
      (matNull_swap_add (matOne_refl Pm))
      (by rw [length_matAdd _ _ (hSwPl.trans hPl.symm),
          length_matAdd _ _ (hIl.trans hIl.symm), hSwPl, hIl])
      (rowsLen_matAdd n _ _ hSwP hP)
      (rowsLen_matAdd n _ _ hI hI)) ?_
  exact matAdd_double (inertia.idMat n)

/-- The identification at the wrap shift: `D₁ᵀD₁ + S = 2` at the
datum of `1 + D₁ = T`. -/
theorem identRead_wrap (m : Nat) :
    identRead (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1) :=
  ident_of (2 * m + 1) (permMatAt (2 * m + 1) (tShift m))
    (rowsLen_permMatAt _ _) (length_permMatAt _ _)
    (Nat.succ_le_succ (Nat.zero_le _)) (orth_wrap m).2

/-! The unit fiber at the wrap shift, and the Horner read's own
scale.  The orbit's sum reads the translation's fixed line — a
permutation matrix's row carries one occupied key, the witness's
own, so the row's fold against the sum reads the sum's member
(`permMatAt_ones`) — the chord doubles it at the shift and its
witness, and the pair `(S : 2)`'s site datum sends it to the unit
family (`unitFiber_wrap`).  Beside them a doubled-chord fixed
vector reads every Horner read at the evaluation's own scale, the
matrix recursion matched to `def:poly`'s step for step
(`polyEval_fixed`). -/

/-- The rescaled identity's action is the plain rescaling. -/
private theorem matVec_scaleId (c : BPair) (n : Nat) (v : List BPair)
    (hv : v.length = n) :
    poly.oneValue (matVec (inertia.matScaleB c (inertia.idMat n)) v)
      (vecScale c v) :=
  poly.oneValue_trans (inertia.matVec_scaleB c (inertia.idMat n) v)
    (vecScale_oneValue c (matVec (inertia.idMat n) v) v
      (split.matVec_idMat n v hv))

/-- A permutation matrix's action reads the vector's entry at the
witness's own key: the row carries one occupied key. -/
private theorem matVec_permAt (n : Nat) (t s : Nat → Nat) (v : List BPair)
    (hv : v.length = n)
    (hst : ∀ l, l < n → s (t l) = l)
    (hts : ∀ l, l < n → t (s l) = l)
    (hsl : ∀ j, j < n → s j < n) (i : Nat) (hi : i < n) :
    (ground.getAt BPair.unit (matVec (permMatAt n t) v) i).oneValue
      (ground.getAt BPair.unit v (s i)) := by
  have hTl : (permMatAt n t).length = n := length_permMatAt n t
  have hrow : (ground.getAt ([] : List BPair) (permMatAt n t) i).length = n :=
    rowsLen_getAt (permMatAt n t) i (rowsLen_permMatAt n t)
      (by rw [hTl]; exact hi)
  have hsi : s i < n := hsl i hi
  rw [show matVec (permMatAt n t) v
      = (permMatAt n t).map (fun r => dotN r v) from rfl,
    ground.getAt_map ([] : List BPair) BPair.unit _ (permMatAt n t) i
      (by rw [hTl]; exact hi)]
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  rw [dotP_comm (ground.getAt ([] : List BPair) (permMatAt n t) i) v]
  refine BPair.oneValue_trans
    (dotP_oneIndex v (ground.getAt ([] : List BPair) (permMatAt n t) i) (s i)
      (by rw [hv, hrow]) (by rw [hrow]; exact hsi) ?_) ?_
  · intro q hq hne
    rw [hrow] at hq
    rw [getAt_permMatAt n t i q hi hq,
      if_neg (fun hc : t q = i =>
        hne ((hst q hq).symm.trans (congrArg s hc)))]
    exact BPair.oneValue_refl _
  · rw [getAt_permMatAt n t i (s i) hi hsi, if_pos (hts i hi)]
    exact BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (by decide +kernel))
      (BPair.mul_ofNat_one (ground.getAt BPair.unit v (s i)))

/-- A permutation matrix acts on the orbit's own sum at the
translation's fixed line: the row's one occupied key is the
witness's own. -/
private theorem permMatAt_ones (n : Nat) (t s : Nat → Nat)
    (hst : ∀ l, l < n → s (t l) = l)
    (hts : ∀ l, l < n → t (s l) = l)
    (hsl : ∀ j, j < n → s j < n) :
    poly.oneValue
      (matVec (permMatAt n t) (List.replicate n (BPair.ofPos Pos.one)))
      (List.replicate n (BPair.ofPos Pos.one)) := by
  have hTl : (permMatAt n t).length = n := length_permMatAt n t
  refine getAt_polyOne _ _
    (by rw [matVec_length, hTl, ground.length_replicate]) ?_
  intro i hi
  rw [matVec_length, hTl] at hi
  rw [ground.getAt_replicate BPair.unit (BPair.ofPos Pos.one) n i hi]
  refine BPair.oneValue_trans
    (matVec_permAt n t s (List.replicate n (BPair.ofPos Pos.one))
      (ground.length_replicate _ n) hst hts hsl i hi) ?_
  rw [ground.getAt_replicate BPair.unit (BPair.ofPos Pos.one) n (s i)
    (hsl i hi)]
  exact BPair.oneValue_refl _

/-- The wrap shift and its witness both read the orbit's sum at the
fixed line. -/
private theorem wrap_ones (m : Nat) :
    poly.oneValue
      (matVec (permMatAt (2 * m + 1) (tShift m)) (orbitSum m))
      (orbitSum m)
    ∧ poly.oneValue
      (matVec (permMatAt (2 * m + 1) (sShift m)) (orbitSum m))
      (orbitSum m) :=
  ⟨permMatAt_ones (2 * m + 1) (tShift m) (sShift m)
      (fun l _ => sShift_tShift m l) (tShift_sShift m) (sShift_lt m),
   permMatAt_ones (2 * m + 1) (sShift m) (tShift m) (tShift_sShift m)
      (fun l _ => sShift_tShift m l) (tShift_lt m)⟩

/-- The chord doubles the orbit's own sum at the wrap shift. -/
private theorem chord_ones (m : Nat) :
    poly.oneValue
      (matVec (chordOp (permMatAt (2 * m + 1) (tShift m))) (orbitSum m))
      (vecAdd (orbitSum m) (orbitSum m)) := by
  have hlen : (orbitSum m).length = 2 * m + 1 := orbitSum_len m
  rw [chord_permMatAt m]
  refine poly.oneValue_trans
    (matVec_add (permMatAt (2 * m + 1) (tShift m))
      (permMatAt (2 * m + 1) (sShift m)) (orbitSum m)
      (rowsLen_cast hlen.symm (rowsLen_permMatAt _ _))
      (rowsLen_cast hlen.symm (rowsLen_permMatAt _ _))) ?_
  exact polyOne_vecAdd _ _ _ _ (wrap_ones m).1 (wrap_ones m).2
    (by rw [matVec_length, length_permMatAt, hlen])
    (by rw [matVec_length, length_permMatAt, hlen])

/-- The doubling rescale is the memberwise sum with the vector's
own. -/
private theorem vecScale_two : ∀ v : List BPair,
    poly.oneValue (vecScale (BPair.ofNat 2) v) (vecAdd v v)
  | [] => trivial
  | x :: t =>
    ⟨BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.norm_oneValue (BPair.ofNat 2 * x)))
      (BPair.oneValue_symm (double_entry x)),
     vecScale_two t⟩

/-- The unit fiber whole at the orbit sum. -/
theorem unitFiber_wrap (m : Nat) :
    unitFiberRead (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1)
      [orbitSum m] := by
  have hlen : (orbitSum m).length = 2 * m + 1 := orbitSum_len m
  have hoff : ¬ poly.unitTail (orbitSum m) := by
    show ¬ poly.unitTail (List.replicate (2 * m + 1) (BPair.ofPos Pos.one))
    intro h
    exact absurd h.1 (by decide +kernel)
  refine ⟨indep_single (2 * m + 1) (orbitSum m) hlen hoff, ?_, ?_⟩
  · -- the pair `(S : 2)`'s datum reads the sum at the unit family
    have hI : poly.oneValue
        (matVec (inertia.matScaleB (BPair.ofNat 2)
          (inertia.idMat (2 * m + 1))) (orbitSum m))
        (vecAdd (orbitSum m) (orbitSum m)) :=
      poly.oneValue_trans
        (matVec_scaleId (BPair.ofNat 2) (2 * m + 1) (orbitSum m) hlen)
        (vecScale_two (orbitSum m))
    have hlenS : (chordOp (permMatAt (2 * m + 1) (tShift m))).length
        = 2 * m + 1 := by
      show (matAdd (permMatAt (2 * m + 1) (tShift m))
        (transposeM (permMatAt (2 * m + 1) (tShift m)))).length = 2 * m + 1
      rw [length_matAdd _ _
          (by rw [length_permMatAt,
            length_transposeM (permMatAt (2 * m + 1) (tShift m))
              (rowsLen_permMatAt _ _)
              (by rw [length_permMatAt]
                  exact Nat.succ_le_succ (Nat.zero_le _))]),
        length_permMatAt]
    have hlenI : (inertia.matScaleB (BPair.ofNat 2)
        (inertia.idMat (2 * m + 1))).length = 2 * m + 1 :=
      (inertia.length_scaleB (BPair.ofNat 2) (inertia.idMat (2 * m + 1))).trans
        (inertia.idMat_len (2 * m + 1))
    have hker : poly.unitTail
        (matVec (unitDatum (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1))
          (orbitSum m)) := by
      show poly.unitTail
        (matVec (matAdd (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (matSwap (inertia.matScaleB (BPair.ofNat 2)
            (inertia.idMat (2 * m + 1))))) (orbitSum m))
      refine poly.oneValue_unitTail
        (matVec_add _ _ (orbitSum m)
          (rowsLen_cast hlen.symm
            (rowsLen_matAdd (2 * m + 1) _ _ (rowsLen_permMatAt _ _)
              (rowsLen_cast (length_permMatAt _ _)
                (rowsLen_transposeM (permMatAt (2 * m + 1) (tShift m))))))
          (rowsLen_cast hlen.symm
            (rowsLen_mapRows BPair.swap _ (2 * m + 1)
              (rowsLen_mapRows _ _ (2 * m + 1)
                (inertia.idMat_rows (2 * m + 1)))))) ?_
      rw [matVec_swapM, elim.vecAdd_comm]
      exact elim.null_swap_add _ _
        (poly.oneValue_symm
          (poly.oneValue_trans (chord_ones m)
            (poly.oneValue_symm hI)))
    show (decide (poly.unitTail
      (matVec (unitDatum (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1))
        (orbitSum m))) && true) = true
    rw [decide_eq_true hker]
    rfl
  · show (decide (poly.oneValue
      (matVec (permMatAt (2 * m + 1) (tShift m)) (orbitSum m))
      (orbitSum m)) && true) = true
    rw [decide_eq_true (wrap_ones m).1]
    rfl

/-- The rescaling rides the matrix action at every shape. -/
private theorem matVec_scaleArg (c : BPair) : ∀ (T : Mat) (v : List BPair),
    poly.oneValue (matVec T (vecScale c v)) (vecScale c (matVec T v))
  | [], _ => trivial
  | r :: t, v =>
    ⟨BPair.oneValue_trans (dotN_read r (vecScale c v))
      (BPair.oneValue_trans (dotP_vecScale_right r v c)
        (BPair.mul_congr (BPair.oneValue_refl c)
          (BPair.oneValue_symm (dotN_read r v)))),
     matVec_scaleArg c t v⟩

/-- An occupied pair of matrices sums to an occupied one. -/
private theorem matAdd_pos : ∀ A B : Mat, 0 < A.length → 0 < B.length →
    0 < (matAdd A B).length
  | [], _, h, _ => absurd h (Nat.lt_irrefl 0)
  | _ :: _, [], _, h => absurd h (Nat.lt_irrefl 0)
  | _ :: _, _ :: _, _, _ => Nat.succ_le_succ (Nat.zero_le _)

/-- A vacant second member absorbs the entrywise sum. -/
private theorem matAdd_nil_right : ∀ A : Mat, matAdd A [] = []
  | [] => rfl
  | _ :: _ => rfl

/-- The Horner read's own shape at an occupied order and an
occupied matrix: the weighted identity fixes the width and the
count stays occupied. -/
private theorem evalM_shapeOf (n : Nat) (S : Mat) (hn : 0 < n)
    (hS : 0 < S.length) : ∀ q : poly.Poly,
    rowsLen n (polyEvalM q S n) ∧ 0 < (polyEvalM q S n).length
  | [] => by
    refine ⟨rowsLen_mapRows _ (inertia.idMat n) n (inertia.idMat_rows n), ?_⟩
    show 0 < (inertia.matScaleB BPair.unit (inertia.idMat n)).length
    rw [inertia.length_scaleB, inertia.idMat_len]
    exact hn
  | c :: t => by
    have ih := evalM_shapeOf n S hn hS t
    have hIr : rowsLen n (inertia.matScaleB c (inertia.idMat n)) :=
      rowsLen_mapRows _ (inertia.idMat n) n (inertia.idMat_rows n)
    have hIl : 0 < (inertia.matScaleB c (inertia.idMat n)).length := by
      rw [inertia.length_scaleB, inertia.idMat_len]
      exact hn
    have hMr : rowsLen n (matMul S (polyEvalM t S n)) :=
      rowsLen_cast (length_transposeM (polyEvalM t S n) ih.1 ih.2)
        (rowsLen_matMul S (polyEvalM t S n))
    have hMl : 0 < (matMul S (polyEvalM t S n)).length := by
      rw [length_matMul]
      exact hS
    exact ⟨rowsLen_matAdd n _ _ hIr hMr, matAdd_pos _ _ hIl hMl⟩

/-- A map rides the drop, key by key. -/
private theorem map_drop {α β : Type} (f : α → β) :
    ∀ (l : List α) (k : Nat), (l.map f).drop k = (l.drop k).map f
  | [], 0 => rfl
  | [], _ + 1 => rfl
  | _ :: _, 0 => rfl
  | _ :: t, k + 1 => map_drop f t k

/-- Beyond the first member's count the second reads the unit
family. -/
private theorem ov_dropNull : ∀ p q : List BPair, poly.oneValue p q →
    poly.unitTail (q.drop p.length)
  | [], _, h => h
  | _ :: _, [], _ => trivial
  | _ :: p, _ :: q, h => ov_dropNull p q h.2

/-- The doubling's unit read descends to the vector's own. -/
private theorem fixedNil_unit : ∀ v : List BPair,
    poly.unitTail (vecScale (BPair.ofNat 2) v) → poly.unitTail v
  | [], _ => trivial
  | _ :: t, h =>
    ⟨ground.mul_cancel_unit (by decide +kernel) h.1, fixedNil_unit t h.2⟩

/-- The memberwise sum's read at a truncating second member: the
first members' counts match and the second's own count bounds where
both targets read the unit family. -/
private theorem vecAdd_ovTrunc : ∀ X1 X2 Y1 Y2 : List BPair,
    poly.oneValue X1 Y1 → poly.oneValue X2 Y2 →
    X1.length = Y1.length → Y1.length = Y2.length →
    poly.unitTail (Y1.drop X2.length) →
    poly.unitTail (Y2.drop X2.length) →
    poly.oneValue (vecAdd X1 X2) (vecAdd Y1 Y2)
  | [], _, [], _, _, _, _, _, _, _ => trivial
  | [], _, _ :: _, _, _, _, hl, _, _, _ => Nat.noConfusion hl
  | _ :: _, [], _, _, _, _, _, _, hd1, hd2 => unitTail_vecAdd_of hd1 hd2
  | _ :: _, _ :: _, [], _, _, _, hl, _, _, _ => Nat.noConfusion hl
  | _ :: _, _ :: _, _ :: _, [], _, _, _, hy, _, _ => Nat.noConfusion hy
  | _ :: X1, _ :: X2, _ :: Y1, _ :: Y2, h1, h2, hl, hy, hd1, hd2 =>
    ⟨BPair.add_congr h1.1 h2.1,
     vecAdd_ovTrunc X1 X2 Y1 Y2 h1.2 h2.2 (Nat.succ.inj hl)
       (Nat.succ.inj hy) hd1 hd2⟩

/-- The Horner read at a doubled-chord fixed vector, the order and
the matrix occupied: the recursion reads `def:poly`'s own step for
step, the vector's own tail beyond the matrix's count the unit
family the truncation asks for. -/
private theorem evalM_fixed_go (n : Nat) (S : Mat) (v : List BPair)
    (hv : v.length = n) (hn : 0 < n) (hS : 0 < S.length)
    (hfix : poly.oneValue (matVec S v) (vecScale (BPair.ofNat 2) v))
    (hvd : poly.unitTail (v.drop S.length)) :
    ∀ q : poly.Poly,
    poly.oneValue (matVec (polyEvalM q S n) v)
      (vecScale (poly.eval q (BPair.ofNat 2)) v)
  | [] => matVec_scaleId BPair.unit n v hv
  | c :: t => by
    have ih := evalM_fixed_go n S v hv hn hS hfix hvd t
    have hP := evalM_shapeOf n S hn hS t
    have hIr : rowsLen v.length (inertia.matScaleB c (inertia.idMat n)) :=
      rowsLen_cast hv.symm
        (rowsLen_mapRows _ (inertia.idMat n) n (inertia.idMat_rows n))
    have hMr : rowsLen v.length (matMul S (polyEvalM t S n)) :=
      rowsLen_cast hv.symm
        (rowsLen_cast (length_transposeM (polyEvalM t S n) hP.1 hP.2)
          (rowsLen_matMul S (polyEvalM t S n)))
    have hlen2 : (matVec (matMul S (polyEvalM t S n)) v).length = S.length := by
      rw [matVec_length, length_matMul]
    have hdrop : ∀ a : BPair,
        poly.unitTail ((vecScale a v).drop
          (matVec (matMul S (polyEvalM t S n)) v).length) := by
      intro a
      rw [hlen2]
      show poly.unitTail ((v.map (fun x => a * x)).drop S.length)
      rw [map_drop (fun x => a * x) v S.length]
      exact unitTail_vecScale a (v.drop S.length) hvd
    show poly.oneValue
      (matVec (matAdd (inertia.matScaleB c (inertia.idMat n))
        (matMul S (polyEvalM t S n))) v)
      (vecScale (c + BPair.ofNat 2 * poly.eval t (BPair.ofNat 2)) v)
    refine poly.oneValue_trans
      (matVec_add (inertia.matScaleB c (inertia.idMat n))
        (matMul S (polyEvalM t S n)) v hIr hMr) ?_
    have hsecond : poly.oneValue
        (matVec (matMul S (polyEvalM t S n)) v)
        (vecScale (poly.eval t (BPair.ofNat 2) * BPair.ofNat 2) v) := by
      refine poly.oneValue_trans
        (matVec_matMul S (polyEvalM t S n) n hP.1 v hv) ?_
      refine poly.oneValue_trans
        (elim.matVec_congr S (matVec (polyEvalM t S n) v)
          (vecScale (poly.eval t (BPair.ofNat 2)) v) ih) ?_
      refine poly.oneValue_trans
        (matVec_scaleArg (poly.eval t (BPair.ofNat 2)) S v) ?_
      refine poly.oneValue_trans
        (vecScale_oneValue (poly.eval t (BPair.ofNat 2)) _ _ hfix) ?_
      rw [vecScale_vecScale]
      exact poly.oneValue_refl _
    refine poly.oneValue_trans
      (vecAdd_ovTrunc _ _ _ _ (matVec_scaleId c n v hv) hsecond
        (by rw [matVec_length, inertia.length_scaleB, inertia.idMat_len,
            length_vecScale, hv])
        (by rw [length_vecScale, length_vecScale])
        (hdrop c) (hdrop (poly.eval t (BPair.ofNat 2) * BPair.ofNat 2))) ?_
    rw [← vecScale_add c (poly.eval t (BPair.ofNat 2) * BPair.ofNat 2) v]
    exact vecScale_congr
      (BPair.add_congr (BPair.oneValue_refl c)
        (BPair.oneValue_of_eq
          (BPair.mul_comm (poly.eval t (BPair.ofNat 2)) (BPair.ofNat 2)))) v

/-- The wrap shift's chord sits at the side. -/
private theorem chordWrap_shape (m : Nat) :
    rowsLen (2 * m + 1) (chordOp (permMatAt (2 * m + 1) (tShift m)))
    ∧ (chordOp (permMatAt (2 * m + 1) (tShift m))).length = 2 * m + 1 := by
  have hP : rowsLen (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) :=
    rowsLen_permMatAt _ _
  have hPl : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hTt : rowsLen (2 * m + 1)
      (transposeM (permMatAt (2 * m + 1) (tShift m))) :=
    rowsLen_cast hPl (rowsLen_transposeM _)
  have hTtl : (transposeM (permMatAt (2 * m + 1) (tShift m))).length
      = 2 * m + 1 := transposeLen _ hP hPl
  exact ⟨rowsLen_matAdd (2 * m + 1) _ _ hP hTt,
    (length_matAdd _ _ (hPl.trans hTtl.symm)).trans hPl⟩

/-- The memberwise swap read back at both members. -/
private theorem unswap_ov {a b : List BPair}
    (h : poly.oneValue (a.map BPair.swap) (b.map BPair.swap)) :
    poly.oneValue a b := by
  have h2 := poly.swapMap_oneValue h
  rw [show (a.map BPair.swap).map BPair.swap = a from poly.neg_neg a,
    show (b.map BPair.swap).map BPair.swap = b from poly.neg_neg b] at h2
  exact h2

/-- A site datum's kernel member reads the two matrices' actions at
one value, the datum's own split at the memberwise swap. -/
private theorem siteKer_read (A B : Mat) (v : List BPair)
    (hA : rowsLen v.length A) (hB : rowsLen v.length B)
    (hl : (matVec A v).length = (matVec B v).length)
    (hk : poly.unitTail (matVec (inertia.siteDatum A B) v)) :
    poly.oneValue (matVec A v) (matVec B v) := by
  have hsplit : poly.oneValue (matVec (inertia.siteDatum A B) v)
      (vecAdd (matVec A v) ((matVec B v).map BPair.swap)) := by
    show poly.oneValue (matVec (matAdd A (matSwap B)) v) _
    refine poly.oneValue_trans
      (matVec_add A (matSwap B) v hA
        (rowsLen_mapRows BPair.swap B v.length hB)) ?_
    rw [matVec_swapM]
    exact poly.oneValue_refl _
  exact poly.oneValue_symm (unswap_ov
    (swap_of_null_add (matVec A v) ((matVec B v).map BPair.swap)
      (by rw [ground.length_map]; exact hl)
      (poly.unitTail_oneValue_right hk hsplit)))

/-- A unit-datum kernel member joins the orbit sum's span: the
fixed read forces equal coefficients along the orbit. -/
theorem unitFiber_span (m : Nat) (v : List BPair)
    (hv : v.length = 2 * m + 1)
    (hk : poly.unitTail (elim.matVec
      (unitDatum (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1)) v)) :
    elim.spanRel (2 * m + 1) [orbitSum m] v := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hP : rowsLen (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) :=
    rowsLen_permMatAt _ _
  have hPl : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hTt : rowsLen (2 * m + 1)
      (transposeM (permMatAt (2 * m + 1) (tShift m))) :=
    rowsLen_cast hPl (rowsLen_transposeM _)
  have hTtl : (transposeM (permMatAt (2 * m + 1) (tShift m))).length
      = 2 * m + 1 := transposeLen _ hP hPl
  have hS : rowsLen (2 * m + 1) (chordOp (permMatAt (2 * m + 1) (tShift m))) :=
    (chordWrap_shape m).1
  have hSl : (chordOp (permMatAt (2 * m + 1) (tShift m))).length = 2 * m + 1 :=
    (chordWrap_shape m).2
  have hI : rowsLen (2 * m + 1) (inertia.idMat (2 * m + 1)) :=
    inertia.idMat_rows _
  have hIl : (inertia.idMat (2 * m + 1)).length = 2 * m + 1 :=
    inertia.idMat_len _
  have h2I : rowsLen (2 * m + 1)
      (inertia.matScaleB (BPair.ofNat 2) (inertia.idMat (2 * m + 1))) :=
    rowsLen_mapRows _ (inertia.idMat (2 * m + 1)) (2 * m + 1) hI
  have h2Il : (inertia.matScaleB (BPair.ofNat 2)
      (inertia.idMat (2 * m + 1))).length = 2 * m + 1 :=
    (inertia.length_scaleB _ _).trans hIl
  have hD : rowsLen (2 * m + 1)
      (inertia.siteDatum (permMatAt (2 * m + 1) (tShift m))
        (inertia.idMat (2 * m + 1))) :=
    rowsLen_matAdd (2 * m + 1) _ _ hP
      (rowsLen_mapRows BPair.swap (inertia.idMat (2 * m + 1)) _ hI)
  have hDl : (inertia.siteDatum (permMatAt (2 * m + 1) (tShift m))
      (inertia.idMat (2 * m + 1))).length = 2 * m + 1 :=
    (length_matAdd _ _
      (hPl.trans ((ground.length_map _ (inertia.idMat (2 * m + 1))).trans
        hIl).symm)).trans hPl
  -- the chord doubles on the kernel member
  have hSv : poly.oneValue
      (matVec (chordOp (permMatAt (2 * m + 1) (tShift m))) v)
      (matVec (inertia.matScaleB (BPair.ofNat 2)
        (inertia.idMat (2 * m + 1))) v) :=
    siteKer_read _ _ v (rowsLen_cast hv.symm hS) (rowsLen_cast hv.symm h2I)
      (by rw [matVec_length, matVec_length, hSl, h2Il]) hk
  -- the datum's own square reads the unit family
  have hprod : poly.unitTail
      (matVec (matMul (transposeM (inertia.siteDatum
        (permMatAt (2 * m + 1) (tShift m)) (inertia.idMat (2 * m + 1))))
        (inertia.siteDatum (permMatAt (2 * m + 1) (tShift m))
          (inertia.idMat (2 * m + 1)))) v) := by
    have hDD : rowsLen (2 * m + 1)
        (matMul (transposeM (inertia.siteDatum
          (permMatAt (2 * m + 1) (tShift m)) (inertia.idMat (2 * m + 1))))
          (inertia.siteDatum (permMatAt (2 * m + 1) (tShift m))
            (inertia.idMat (2 * m + 1)))) :=
      rowsLen_cast (transposeLen _ hD hDl) (rowsLen_matMul _ _)
    have hDDl : (matMul (transposeM (inertia.siteDatum
        (permMatAt (2 * m + 1) (tShift m)) (inertia.idMat (2 * m + 1))))
        (inertia.siteDatum (permMatAt (2 * m + 1) (tShift m))
          (inertia.idMat (2 * m + 1)))).length = 2 * m + 1 :=
      (length_matMul _ _).trans (transposeLen _ hD hDl)
    have hjoin : poly.oneValue
        (vecAdd (matVec (matMul (transposeM (inertia.siteDatum
            (permMatAt (2 * m + 1) (tShift m)) (inertia.idMat (2 * m + 1))))
            (inertia.siteDatum (permMatAt (2 * m + 1) (tShift m))
              (inertia.idMat (2 * m + 1)))) v)
          (matVec (chordOp (permMatAt (2 * m + 1) (tShift m))) v))
        (matVec (inertia.matScaleB (BPair.ofNat 2)
          (inertia.idMat (2 * m + 1))) v) :=
      poly.oneValue_trans
        (poly.oneValue_symm
          (matVec_add _ _ v (rowsLen_cast hv.symm hDD)
            (rowsLen_cast hv.symm hS)))
        (matVec_matOne _ _ v (identRead_wrap m))
    refine poly.oneValue_unitTail
      (vecAdd_cancel_right _ (List.replicate (2 * m + 1) BPair.unit)
        (matVec (chordOp (permMatAt (2 * m + 1) (tShift m))) v)
        (by rw [matVec_length, hDDl, ground.length_replicate])
        (by rw [matVec_length, hDDl, matVec_length, hSl])
        (poly.oneValue_trans hjoin
          (poly.oneValue_trans (poly.oneValue_symm hSv)
            (poly.oneValue_symm
              (vecAdd_null_left _ _
                ((ground.length_replicate BPair.unit (2 * m + 1)).trans
                  (matVec_length _ v ▸ hSl.symm))
                (poly.unitTail_replicate (2 * m + 1)))))))
      (poly.unitTail_replicate (2 * m + 1))
  -- the datum's own pairing withdraws it
  have hfix : poly.oneValue
      (matVec (permMatAt (2 * m + 1) (tShift m)) v) v := by
    refine poly.oneValue_trans
      (siteKer_read _ _ v (rowsLen_cast hv.symm hP) (rowsLen_cast hv.symm hI)
        (by rw [matVec_length, matVec_length, hPl, hIl]) ?_)
      (split.matVec_idMat (2 * m + 1) v hv)
    refine dotP_self_null _ ?_
    refine BPair.oneValue_trans
      (dotP_matVec_transpose (2 * m + 1) _ v _ hD hv (matVec_length _ v)) ?_
    exact BPair.oneValue_trans
      (dotP_oneValue_right v _ _
        (matVec_comp _ _ v (2 * m + 1) hD hv (rowsLen_transposeM _)))
      (dotP_null_tail_right v _ hprod)
  -- the fixed read forces one value along the orbit
  have hstep : ∀ k, k + 1 < 2 * m + 1 →
      (ground.getAt BPair.unit v k).oneValue
        (ground.getAt BPair.unit v (k + 1)) := by
    intro k hk
    have hread := matVec_permAt (2 * m + 1) (tShift m) (sShift m) v hv
      (fun l _ => sShift_tShift m l) (tShift_sShift m) (sShift_lt m)
      (k + 1) hk
    rw [sShift_succ m k] at hread
    exact BPair.oneValue_trans (BPair.oneValue_symm hread)
      (poly.oneValue_getAt (k + 1) hfix)
  have hall : ∀ k, k < 2 * m + 1 →
      (ground.getAt BPair.unit v k).oneValue
        (ground.getAt BPair.unit v 0) := by
    intro k
    induction k with
    | zero => intro _; exact BPair.oneValue_refl _
    | succ j ih =>
      intro hj
      exact BPair.oneValue_trans
        (BPair.oneValue_symm (hstep j hj))
        (ih (Nat.lt_of_succ_lt hj))
  -- the orbit sum's own combination
  refine span_intro (2 * m + 1) [orbitSum m] v ⟨orbitSum_len m, trivial⟩ hv
    ⟨BPair.ofPos Pos.one, [ground.getAt BPair.unit v 0], by decide +kernel, rfl, ?_⟩
  refine poly.oneValue_trans ?_
    (poly.oneValue_symm
      (vecAdd_null_right (vecScale (ground.getAt BPair.unit v 0) (orbitSum m))
        (List.replicate (2 * m + 1) BPair.unit)
        ((length_vecScale _ (orbitSum m)).trans
          ((orbitSum_len m).trans
            (ground.length_replicate BPair.unit (2 * m + 1)).symm))
        (poly.unitTail_replicate (2 * m + 1))))
  refine getAt_polyOne _ _
    (by rw [length_vecScale, length_vecScale, hv, orbitSum_len]) ?_
  intro i hi
  rw [length_vecScale, hv] at hi
  rw [getAt_vecScale (BPair.ofPos Pos.one) v i (by rw [hv]; exact hi),
    getAt_vecScale (ground.getAt BPair.unit v 0) (orbitSum m) i
      (by rw [orbitSum_len]; exact hi),
    show orbitSum m = List.replicate (2 * m + 1) (BPair.ofPos Pos.one) from rfl,
    ground.getAt_replicate BPair.unit (BPair.ofPos Pos.one) (2 * m + 1) i hi]
  refine BPair.oneValue_trans
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_comm (BPair.ofPos Pos.one)
          (ground.getAt BPair.unit v i)))
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) (by decide +kernel))
        (BPair.mul_ofNat_one (ground.getAt BPair.unit v i))))
    (BPair.oneValue_trans (hall i hi) ?_)
  exact BPair.oneValue_symm
    (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (by decide +kernel))
      (BPair.mul_ofNat_one (ground.getAt BPair.unit v 0)))

/-- A doubled-chord fixed vector reads every Horner read at the
evaluation's own scale. -/
theorem polyEval_fixed (n : Nat) (q : poly.Poly) (S : Mat)
    (v : List BPair) (hv : v.length = n)
    (hfix : poly.oneValue (elim.matVec S v)
      (elim.vecScale (BPair.ofNat 2) v)) :
    poly.oneValue (elim.matVec (polyEvalM q S n) v)
      (elim.vecScale (poly.eval q (BPair.ofNat 2)) v) := by
  cases n with
  | zero =>
    -- the vacant order: every read is the unit family's own
    match v, hv with
    | [], _ =>
      cases q with
      | nil => trivial
      | cons c t =>
        show poly.oneValue
          (matVec (matAdd (inertia.matScaleB c (inertia.idMat 0))
            (matMul S (polyEvalM t S 0))) []) []
        trivial
  | succ n' =>
    cases hSl : S.length with
    | zero =>
      -- the vacant matrix: the fixed read makes the vector its own
      -- unit family
      have hSnil : S = [] := by
        match S, hSl with
        | [], _ => rfl
      have hvu : poly.unitTail v := by
        refine fixedNil_unit v ?_
        rw [hSnil] at hfix
        exact hfix
      rw [hSnil]
      cases q with
      | nil =>
        exact poly.oneValue_trans (matVec_scaleId BPair.unit (n' + 1) v hv)
          (poly.unitTail_oneValue (unitTail_vecScale BPair.unit v hvu)
            (unitTail_vecScale BPair.unit v hvu))
      | cons c t =>
        show poly.oneValue
          (matVec (matAdd (inertia.matScaleB c (inertia.idMat (n' + 1)))
            (matMul [] (polyEvalM t [] (n' + 1)))) v)
          (vecScale (poly.eval (c :: t) (BPair.ofNat 2)) v)
        rw [show matMul ([] : Mat) (polyEvalM t [] (n' + 1)) = [] from rfl,
          matAdd_nil_right (inertia.matScaleB c (inertia.idMat (n' + 1)))]
        exact unitTail_vecScale _ v hvu
    | succ k =>
      refine evalM_fixed_go (n' + 1) S v hv (Nat.succ_le_succ (Nat.zero_le _))
        (by rw [hSl]; exact Nat.succ_le_succ (Nat.zero_le _)) hfix ?_ q
      refine fixedNil_unit (v.drop S.length) ?_
      show poly.unitTail ((v.drop S.length).map (fun x => BPair.ofNat 2 * x))
      rw [← map_drop (fun x => BPair.ofNat 2 * x) v S.length]
      have h := ov_dropNull (matVec S v) (vecScale (BPair.ofNat 2) v) hfix
      rw [matVec_length] at h
      exact h

/-! The column's Horner read at the chord, `colMember_wrap`
iterated along a stated polynomial.  The fold kit rides the residue
beneath it: a row's fold reads a class read of its polynomial
vector key by key (`scaleDot_pCong` at `deck.pCong_mulBoth` and
`poly.scaleP_single`), a polynomial factor rides out of the fold
(`scaleDot_mulOut` at `poly.mul_assoc` and `poly.mul_sum`), and the
rescaled identity's row picks its own key
(`scaleDot_scaleId` at `scaleDot_hotAt`).  The Horner recursion's two
members are then the scaled key and the chord's own multiple of the
step below, and the deck symbol's one-key shift closes the step
(`deck.mulX_read`, the constant entering at
`poly.scaleP_single`). -/

/-- The rescaled identity's row against a polynomial vector reads
the stated key's own rescaling. -/
private theorem scaleDot_scaleId (c : BPair) (n : Nat) (u : List poly.Poly)
    (hu : u.length = n) (i : Nat) (hi : i < n) :
    poly.oneValue
      (poly.scaleDot (ground.getAt ([] : List BPair)
        (inertia.matScaleB c (inertia.idMat n)) i) u)
      (poly.scaleP c (ground.getAt ([] : poly.Poly) u i)) := by
  have hIl : (inertia.idMat n).length = n := inertia.idMat_len n
  have hiI : i < (inertia.idMat n).length := by rw [hIl]; exact hi
  have hrowI : (ground.getAt ([] : List BPair) (inertia.idMat n) i).length = n :=
    rowsLen_getAt (inertia.idMat n) i (inertia.idMat_rows n) hiI
  have hgetRow : ground.getAt ([] : List BPair)
      (inertia.matScaleB c (inertia.idMat n)) i
      = (ground.getAt ([] : List BPair) (inertia.idMat n) i).map
        (fun x => (c * x).norm) :=
    ground.getAt_map ([] : List BPair) ([] : List BPair)
      (poly.scaleP c) (inertia.idMat n) i hiI
  have hrow : (ground.getAt ([] : List BPair)
      (inertia.matScaleB c (inertia.idMat n)) i).length = n := by
    rw [hgetRow, ground.length_map, hrowI]
  have hent : ∀ k, k < n → ground.getAt BPair.unit
      (ground.getAt ([] : List BPair)
        (inertia.matScaleB c (inertia.idMat n)) i) k
      = (c * (if k = i then BPair.ofNat 1 else BPair.unit)).norm := by
    intro k hk
    rw [hgetRow, ground.getAt_map BPair.unit BPair.unit
      (fun x => (c * x).norm) (ground.getAt ([] : List BPair)
        (inertia.idMat n) i) k (by rw [hrowI]; exact hk),
      inertia.getAt_idMat n i k hi hk]
  refine scaleDot_hotAt c _ u i (by rw [hrow, hu]) ?_ ?_
  · rw [hent i hi, if_pos rfl]
    exact BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_ofNat_one c)
  · intro k hk hne
    rw [hrow] at hk
    rw [hent k hk, if_neg hne]
    exact BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_unit c)

/-- A row's fold reads a class read of its polynomial vector, key
by key. -/
private theorem scaleDot_pCong (m : Nat) :
    ∀ (r : List BPair) (x y : List poly.Poly), x.length = y.length →
    (∀ j, j < x.length → ∃ c, deck.pCong m c
      (ground.getAt ([] : poly.Poly) x j)
      (ground.getAt ([] : poly.Poly) y j)) →
    ∃ c, deck.pCong m c (poly.scaleDot r x) (poly.scaleDot r y)
  | [], _, _, _, _ => deck.pCong_of m trivial
  | _ :: _, [], [], _, _ => deck.pCong_of m trivial
  | _ :: _, [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, _ :: _, [], h, _ => Nat.noConfusion h
  | c :: r, p :: x, q :: y, h, hj =>
    deck.pCong_addBoth
      (deck.pCong_trans (deck.pCong_of m (poly.scaleP_single c p))
        (deck.pCong_trans
          (deck.pCong_mulBoth (hj 0 (Nat.succ_le_succ (Nat.zero_le _)))
            (deck.pCong_of m (poly.oneValue_refl [c])))
          (deck.pCong_of m (poly.oneValue_symm (poly.scaleP_single c q)))))
      (scaleDot_pCong m r x y (Nat.succ.inj h)
        (fun j hjj => hj (j + 1) (Nat.succ_lt_succ hjj)))

/-- A polynomial factor rides out of a row's fold. -/
private theorem scaleDot_mulOut (w : poly.Poly) :
    ∀ (r : List BPair) (u : List poly.Poly),
    poly.oneValue (poly.scaleDot r (u.map (fun p => poly.mul w p)))
      (poly.mul w (poly.scaleDot r u))
  | [], _ => poly.unitTail_oneValue trivial (poly.mul_nil w)
  | _ :: _, [] => poly.unitTail_oneValue trivial (poly.mul_nil w)
  | c :: r, p :: u =>
    poly.oneValue_trans
      (poly.add_congr
        (poly.oneValue_trans (poly.scaleP_single c (poly.mul w p))
          (poly.oneValue_trans (poly.mul_assoc w p [c])
            (poly.mul_congr w (poly.oneValue_symm (poly.scaleP_single c p)))))
        (scaleDot_mulOut w r u))
      (poly.oneValue_symm (poly.mul_sum w (poly.scaleP c p) (poly.scaleDot r u)))

/-- A stated key's read off two vectors' own class read at the
residue. -/
private theorem prow_getAt : ∀ (x y : List poly.Poly),
    split.prowOneValue x y → ∀ i, i < x.length →
    poly.oneValue (ground.getAt ([] : poly.Poly) x i)
      (ground.getAt ([] : poly.Poly) y i)
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, h, 0, _ => h.1
  | _ :: x, _ :: y, h, i + 1, hi =>
    prow_getAt x y h.2 i (Nat.lt_of_succ_lt_succ hi)

/-- The residue vector's count is the vector's own. -/
private theorem redVec_len (m : Nat) (u : List poly.Poly) :
    (redVec m u).length = u.length := ground.length_map _ u

/-- The residue vector's entry at a key. -/
private theorem redVec_getAt (m : Nat) (u : List poly.Poly) (i : Nat)
    (hi : i < u.length) :
    ground.getAt ([] : poly.Poly) (redVec m u) i
      = deck.redP m (ground.getAt ([] : poly.Poly) u i) :=
  ground.getAt_map ([] : poly.Poly) ([] : poly.Poly) (deck.redP m) u i hi

/-- The chord's own entry on the column at a key, the membership
read projected. -/
private theorem colMember_entry (m i : Nat) (hi : i < 2 * m + 1) :
    ∃ c, deck.pCong m c
      (ground.getAt ([] : poly.Poly)
        (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m))) (deckColumn m)) i)
      (poly.mul deck.wPoly
        (ground.getAt ([] : poly.Poly) (deckColumn m) i)) := by
  have hlen : (pmatVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m)).length = 2 * m + 1 := by
    rw [pmatVec_len, (chordWrap_shape m).2]
  have hproj := prow_getAt _ _ (colMember_wrap m) i
    (by rw [redVec_len, hlen]; exact hi)
  rw [redVec_getAt m _ i (by rw [hlen]; exact hi),
    redVec_getAt m _ i (by rw [ground.length_map, deckColumn_len]; exact hi),
    ground.getAt_map ([] : poly.Poly) ([] : poly.Poly)
      (fun p => poly.mul deck.wPoly p) (deckColumn m) i
      (by rw [deckColumn_len]; exact hi)] at hproj
  exact deck.pCong_of_redP m hproj

/-- The Horner read's own entry on the column: the recursion's
scaled key against the chord's multiple of the step below, closed
at the deck symbol's one-key shift. -/
private theorem evalCol_entry (m : Nat) : ∀ (q : poly.Poly) (i : Nat),
    i < 2 * m + 1 →
    ∃ c, deck.pCong m c
      (ground.getAt ([] : poly.Poly)
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1)) (deckColumn m)) i)
      (poly.mul q (ground.getAt ([] : poly.Poly) (deckColumn m) i))
  | [], i, hi => by
    have hMl : (inertia.matScaleB BPair.unit
        (inertia.idMat (2 * m + 1))).length = 2 * m + 1 :=
      (inertia.length_scaleB BPair.unit (inertia.idMat (2 * m + 1))).trans
        (inertia.idMat_len (2 * m + 1))
    show ∃ c, deck.pCong m c (ground.getAt ([] : poly.Poly)
      (pmatVec (inertia.matScaleB BPair.unit (inertia.idMat (2 * m + 1)))
        (deckColumn m)) i) []
    rw [pmatVec_getAt _ (deckColumn m) i (by rw [hMl]; exact hi)]
    exact deck.pCong_of m (poly.unitTail_oneValue
      (poly.oneValue_unitTail
        (scaleDot_scaleId BPair.unit (2 * m + 1) (deckColumn m)
          (deckColumn_len m) i hi)
        (poly.scaleP_unit _)) trivial)
  | c :: t, i, hi => by
    have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hSr := (chordWrap_shape m).1
    have hSl := (chordWrap_shape m).2
    have hP := evalM_shape (2 * m + 1)
      (chordOp (permMatAt (2 * m + 1) (tShift m))) hSr hSl hn t
    have hu : (deckColumn m).length = 2 * m + 1 := deckColumn_len m
    have hAr : rowsLen (2 * m + 1)
        (inertia.matScaleB c (inertia.idMat (2 * m + 1))) :=
      inertia.rowsLen_scaleB c (2 * m + 1) (inertia.idMat (2 * m + 1))
        (inertia.idMat_rows (2 * m + 1))
    have hAl : (inertia.matScaleB c (inertia.idMat (2 * m + 1))).length
        = 2 * m + 1 :=
      (inertia.length_scaleB c (inertia.idMat (2 * m + 1))).trans
        (inertia.idMat_len (2 * m + 1))
    have hBr : rowsLen (2 * m + 1)
        (matMul (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (polyEvalM t (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (2 * m + 1))) :=
      rowsLen_cast (length_transposeM _ hP.1 (by rw [hP.2]; exact hn))
        (rowsLen_matMul _ _)
    have hBl : (matMul (chordOp (permMatAt (2 * m + 1) (tShift m)))
        (polyEvalM t (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1))).length = 2 * m + 1 :=
      (length_matMul _ _).trans hSl
    have hjl : (matAdd (inertia.matScaleB c (inertia.idMat (2 * m + 1)))
        (matMul (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (polyEvalM t (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (2 * m + 1)))).length = 2 * m + 1 :=
      (length_matAdd _ _ (hAl.trans hBl.symm)).trans hAl
    have hrowS : (ground.getAt ([] : List BPair)
        (chordOp (permMatAt (2 * m + 1) (tShift m))) i).length = 2 * m + 1 :=
      rowsLen_getAt _ i hSr (by rw [hSl]; exact hi)
    -- the two members of the Horner step
    have hstep1 : poly.oneValue
        (poly.scaleDot (ground.getAt ([] : List BPair)
          (inertia.matScaleB c (inertia.idMat (2 * m + 1))) i) (deckColumn m))
        (poly.scaleP c (ground.getAt ([] : poly.Poly) (deckColumn m) i)) :=
      scaleDot_scaleId c (2 * m + 1) (deckColumn m) hu i hi
    have hstep2 : ∃ d, deck.pCong m d
        (poly.scaleDot (ground.getAt ([] : List BPair)
          (matMul (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (polyEvalM t (chordOp (permMatAt (2 * m + 1) (tShift m)))
              (2 * m + 1))) i) (deckColumn m))
        (poly.mul t (poly.mul deck.wPoly
          (ground.getAt ([] : poly.Poly) (deckColumn m) i))) := by
      rw [getAt_matMul _ _ i (by rw [hSl]; exact hi)]
      refine deck.pCong_trans
        (deck.pCong_of m (scaleDot_matMul (2 * m + 1) _ hP.1 hP.2
          (deckColumn m) hu _ hrowS)) ?_
      refine deck.pCong_trans
        (scaleDot_pCong m _ _ ((deckColumn m).map (fun p => poly.mul t p))
          (by rw [pmatVec_len, hP.2, ground.length_map, hu])
          (fun j hj => ?_)) ?_
      · rw [pmatVec_len, hP.2] at hj
        rw [ground.getAt_map ([] : poly.Poly) ([] : poly.Poly)
          (fun p => poly.mul t p) (deckColumn m) j (by rw [hu]; exact hj)]
        exact evalCol_entry m t j hj
      · refine deck.pCong_trans
          (deck.pCong_of m (scaleDot_mulOut t _ (deckColumn m))) ?_
        refine deck.pCong_mulL t ?_
        rw [← pmatVec_getAt (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m) i (by rw [hSl]; exact hi)]
        exact colMember_entry m i hi
    -- the step's own closing read
    have hclose : poly.oneValue
        (poly.add (poly.scaleP c
            (ground.getAt ([] : poly.Poly) (deckColumn m) i))
          (poly.mul t (poly.mul deck.wPoly
            (ground.getAt ([] : poly.Poly) (deckColumn m) i))))
        (poly.mul (c :: t)
          (ground.getAt ([] : poly.Poly) (deckColumn m) i)) :=
      poly.add_congr
        (poly.oneValue_map (fun x => (c * x).norm) (fun d => c * d)
          (ground.getAt ([] : poly.Poly) (deckColumn m) i)
          (fun x _ => BPair.norm_oneValue (c * x)))
        (poly.oneValue_trans
          (poly.mul_left_comm t deck.wPoly
            (ground.getAt ([] : poly.Poly) (deckColumn m) i))
          (deck.mulX_read
            (poly.mul t
              (ground.getAt ([] : poly.Poly) (deckColumn m) i))))
    show ∃ d, deck.pCong m d (ground.getAt ([] : poly.Poly)
      (pmatVec (matAdd (inertia.matScaleB c (inertia.idMat (2 * m + 1)))
        (matMul (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (polyEvalM t (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (2 * m + 1)))) (deckColumn m)) i)
      (poly.mul (c :: t) (ground.getAt ([] : poly.Poly) (deckColumn m) i))
    rw [pmatVec_getAt _ (deckColumn m) i (by rw [hjl]; exact hi),
      getAt_matAdd _ _ i (by rw [hAl]; exact hi) (by rw [hBl]; exact hi)]
    refine deck.pCong_trans
      (deck.pCong_of m (scaleDot_vecAdd _ _ (deckColumn m)
        (by rw [rowsLen_getAt _ i hAr (by rw [hAl]; exact hi),
            rowsLen_getAt _ i hBr (by rw [hBl]; exact hi)]))) ?_
    exact deck.pCong_trans
      (deck.pCong_addBoth (deck.pCong_of m hstep1) hstep2)
      (deck.pCong_of m hclose)

/-- The column carries every Horner read at the chord to its own
multiple over the residue (colMember_wrap iterated). -/
theorem polyEval_column (m : Nat) (q : poly.Poly) :
    split.prowOneValue
      (redVec m (pmatVec
        (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1))
        (deckColumn m)))
      (redVec m ((deckColumn m).map (fun p => poly.mul q p))) := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hP := evalM_shape (2 * m + 1)
    (chordOp (permMatAt (2 * m + 1) (tShift m)))
    (chordWrap_shape m).1 (chordWrap_shape m).2 hn q
  refine prow_redP m _ _ ?_ ?_
  · rw [pmatVec_len, hP.2, ground.length_map, deckColumn_len]
  · intro i hi
    rw [pmatVec_len, hP.2] at hi
    rw [ground.getAt_map ([] : poly.Poly) ([] : poly.Poly)
      (fun p => poly.mul q p) (deckColumn m) i
      (by rw [deckColumn_len]; exact hi)]
    exact evalCol_entry m q i hi

/-! The block's entries at a stated symbol, `lem:fiberdec`'s
block-entry reads at the pair `(u, A u)`.  The doubling datum
commutes past the chord at the orthogonality alone
(`band_chord_comm`: both products expand to one four-term sum, the
two unit reads entering at the crossed products), and the symbol's
Horner recursion moves the datum through the operator
(`evalM_comm`), so the operator's image of the datum's column is
the datum's image of the operator's own.  The column's eigen read
(`polyEval_column`) enters each slot — the pairing's transpose
walk putting the operator's image on the left where a slot holds
the datum's image — the symbol's multiple rides out of the pairing
(`pdotVec_mapMul`), and the three pairings close at the residue's
own reads: the column's doubled side (`deckColumn_selfPair`), the
crossed null (`deckColumn_crossNull`), and the image's own
`⟨4 : x²⟩` against the doubled side (`deckColumn_imagePair`). -/

/-- The pairing exchanges its two members, the entries' products
exchanged key by key. -/
private theorem pdotVec_comm : ∀ x y : List poly.Poly,
    poly.oneValue (pdotVec x y) (pdotVec y x)
  | [], [] => trivial
  | [], _ :: _ => trivial
  | _ :: _, [] => trivial
  | p :: x, r :: y => poly.add_congr (poly.mul_comm p r) (pdotVec_comm x y)

/-- A symbol's multiple rides out of the pairing's right member. -/
private theorem pdotVec_mapMul (q : poly.Poly) : ∀ x y : List poly.Poly,
    poly.oneValue (pdotVec x (y.map (fun p => poly.mul q p)))
      (poly.mul q (pdotVec x y))
  | [], _ => poly.mul_nil q
  | _ :: _, [] => poly.mul_nil q
  | p :: x, r :: y =>
    poly.oneValue_trans
      (poly.add_congr (poly.mul_left_comm p q r) (pdotVec_mapMul q x y))
      (poly.oneValue_symm (poly.mul_sum q (poly.mul p r) (pdotVec x y)))

/-- A symbol's multiple rides out of the pairing's left member. -/
private theorem pdotVec_mapMulL (q : poly.Poly) (x y : List poly.Poly) :
    poly.oneValue (pdotVec (x.map (fun p => poly.mul q p)) y)
      (poly.mul q (pdotVec x y)) :=
  poly.oneValue_trans (pdotVec_comm (x.map (fun p => poly.mul q p)) y)
    (poly.oneValue_trans (pdotVec_mapMul q y x)
      (poly.mul_congr q (pdotVec_comm y x)))

/-- The doubling datum at the wrap shift keeps the window's
shape. -/
private theorem bandWrap_shape (m : Nat) :
    rowsLen (2 * m + 1) (bandDatum (permMatAt (2 * m + 1) (tShift m)))
    ∧ (bandDatum (permMatAt (2 * m + 1) (tShift m))).length = 2 * m + 1 :=
  bandDatum_shape (2 * m + 1) (permMatAt (2 * m + 1) (tShift m))
    (rowsLen_permMatAt _ _) (length_permMatAt _ _)

/-- The doubling datum commutes past the chord at the orthogonality
alone: both products expand to the four-term sum
`T² + 1 + 1̌ + (TᵀTᵀ)̌ `, the two products `T Tᵀ = Tᵀ T = 1`
entering at the crossed terms in exchanged places. -/
private theorem band_chord_comm (n : Nat) (Pm : Mat) (hP : rowsLen n Pm)
    (hPl : Pm.length = n) (hn : 0 < n) (horth : orthRead Pm n) :
    matOneValue (matMul (bandDatum Pm) (chordOp Pm))
      (matMul (chordOp Pm) (bandDatum Pm)) := by
  have hTtl : (transposeM Pm).length = n := transposeLen Pm hP hPl
  have hTt : rowsLen n (transposeM Pm) :=
    rowsLen_cast hPl (rowsLen_transposeM Pm)
  have hSw : rowsLen n (matSwap (transposeM Pm)) :=
    rowsLen_mapRows BPair.swap (transposeM Pm) n hTt
  have hSwl : (matSwap (transposeM Pm)).length = n :=
    (ground.length_map _ (transposeM Pm)).trans hTtl
  have hA : rowsLen n (bandDatum Pm) := (bandDatum_shape n Pm hP hPl).1
  have hAl : (bandDatum Pm).length = n := (bandDatum_shape n Pm hP hPl).2
  have hS : rowsLen n (chordOp Pm) :=
    rowsLen_matAdd n Pm (transposeM Pm) hP hTt
  have hSl : (chordOp Pm).length = n :=
    (length_matAdd Pm _ (hPl.trans hTtl.symm)).trans hPl
  have hAt : rowsLen n (transposeM (bandDatum Pm)) :=
    rowsLen_cast hAl (rowsLen_transposeM _)
  have hSt : rowsLen n (transposeM (chordOp Pm)) :=
    rowsLen_cast hSl (rowsLen_transposeM _)
  have hAtl : (transposeM (bandDatum Pm)).length = n :=
    transposeLen (bandDatum Pm) hA hAl
  have hStl : (transposeM (chordOp Pm)).length = n :=
    transposeLen (chordOp Pm) hS hSl
  have hTT : rowsLen n (matMul Pm Pm) :=
    rowsLen_cast hTtl (rowsLen_matMul Pm Pm)
  have hPP : rowsLen n (matMul Pm (transposeM Pm)) :=
    rowsLen_cast (transposeLen (transposeM Pm) hTt hTtl)
      (rowsLen_matMul Pm (transposeM Pm))
  have hQ : rowsLen n (matMul (transposeM Pm) Pm) :=
    rowsLen_cast hTtl (rowsLen_matMul (transposeM Pm) Pm)
  have hQQ : rowsLen n (matMul (transposeM Pm) (transposeM Pm)) :=
    rowsLen_cast (transposeLen (transposeM Pm) hTt hTtl)
      (rowsLen_matMul (transposeM Pm) (transposeM Pm))
  have hswP : rowsLen n (matSwap (matMul Pm (transposeM Pm))) :=
    rowsLen_mapRows BPair.swap _ n hPP
  have hswQ : rowsLen n (matSwap (matMul (transposeM Pm) Pm)) :=
    rowsLen_mapRows BPair.swap _ n hQ
  have hswQQ : rowsLen n (matSwap (matMul (transposeM Pm) (transposeM Pm))) :=
    rowsLen_mapRows BPair.swap _ n hQQ
  have hI : rowsLen n (inertia.idMat n) := inertia.idMat_rows n
  have hIsw : rowsLen n (matSwap (inertia.idMat n)) :=
    rowsLen_mapRows BPair.swap _ n hI
  have hTA : matOneValue (matMul Pm (bandDatum Pm))
      (matAdd (matMul Pm Pm) (matSwap (matMul Pm (transposeM Pm)))) := by
    have h := matMul_addR Pm (matSwap (transposeM Pm)) hP hSw
      (hPl.trans hSwl.symm) (by rw [hPl]; exact hn) Pm
      (rowsLen_cast hPl.symm hP)
    rw [matMul_swap] at h
    exact h
  have hTtA : matOneValue (matMul (transposeM Pm) (bandDatum Pm))
      (matAdd (matMul (transposeM Pm) Pm)
        (matSwap (matMul (transposeM Pm) (transposeM Pm)))) := by
    have h := matMul_addR Pm (matSwap (transposeM Pm)) hP hSw
      (hPl.trans hSwl.symm) (by rw [hPl]; exact hn) (transposeM Pm)
      (rowsLen_cast hPl.symm hTt)
    rw [matMul_swap] at h
    exact h
  -- the datum against the chord
  have hAS : matOneValue (matMul (bandDatum Pm) (chordOp Pm))
      (matAdd (matAdd (matMul Pm Pm) (matMul Pm (transposeM Pm)))
        (matAdd (matSwap (matMul (transposeM Pm) Pm))
          (matSwap (matMul (transposeM Pm) (transposeM Pm))))) := by
    refine matOne_trans
      (matMul_addL n (chordOp Pm) hSt Pm (matSwap (transposeM Pm)) hP hSw) ?_
    refine matAdd_cong2 n _ _ _ _
      (rowsLen_cast hStl (rowsLen_matMul Pm (chordOp Pm)))
      (rowsLen_cast hStl
        (rowsLen_matMul (matSwap (transposeM Pm)) (chordOp Pm)))
      (rowsLen_matAdd n _ _ hTT hPP)
      (rowsLen_matAdd n _ _ hswQ hswQQ)
      (matMul_addR Pm (transposeM Pm) hP hTt (hPl.trans hTtl.symm)
        (by rw [hPl]; exact hn) Pm (rowsLen_cast hPl.symm hP)) ?_
    rw [matMul_swapL]
    refine matOne_trans (matSwap_congr
      (matMul_addR Pm (transposeM Pm) hP hTt (hPl.trans hTtl.symm)
        (by rw [hPl]; exact hn) (transposeM Pm)
        (rowsLen_cast hPl.symm hTt))) ?_
    rw [matSwap_matAdd]
    exact matOne_refl _
  -- the chord against the datum
  have hSA : matOneValue (matMul (chordOp Pm) (bandDatum Pm))
      (matAdd (matAdd (matMul Pm Pm) (matSwap (matMul Pm (transposeM Pm))))
        (matAdd (matMul (transposeM Pm) Pm)
          (matSwap (matMul (transposeM Pm) (transposeM Pm))))) := by
    refine matOne_trans
      (matMul_addL n (bandDatum Pm) hAt Pm (transposeM Pm) hP hTt) ?_
    exact matAdd_cong2 n _ _ _ _
      (rowsLen_cast hAtl (rowsLen_matMul Pm (bandDatum Pm)))
      (rowsLen_cast hAtl (rowsLen_matMul (transposeM Pm) (bandDatum Pm)))
      (rowsLen_matAdd n _ _ hTT hswP)
      (rowsLen_matAdd n _ _ hQ hswQQ)
      hTA hTtA
  -- the orthogonality's two unit reads
  have hAS4 : matOneValue
      (matAdd (matAdd (matMul Pm Pm) (matMul Pm (transposeM Pm)))
        (matAdd (matSwap (matMul (transposeM Pm) Pm))
          (matSwap (matMul (transposeM Pm) (transposeM Pm)))))
      (matAdd (matAdd (matMul Pm Pm) (inertia.idMat n))
        (matAdd (matSwap (inertia.idMat n))
          (matSwap (matMul (transposeM Pm) (transposeM Pm))))) :=
    matAdd_cong2 n _ _ _ _
      (rowsLen_matAdd n _ _ hTT hPP) (rowsLen_matAdd n _ _ hswQ hswQQ)
      (rowsLen_matAdd n _ _ hTT hI) (rowsLen_matAdd n _ _ hIsw hswQQ)
      (matAdd_cong2 n _ _ _ _ hTT hPP hTT hI (matOne_refl _) horth.1)
      (matAdd_cong2 n _ _ _ _ hswQ hswQQ hIsw hswQQ
        (matSwap_congr horth.2) (matOne_refl _))
  have hSA4 : matOneValue
      (matAdd (matAdd (matMul Pm Pm) (matSwap (matMul Pm (transposeM Pm))))
        (matAdd (matMul (transposeM Pm) Pm)
          (matSwap (matMul (transposeM Pm) (transposeM Pm)))))
      (matAdd (matAdd (matMul Pm Pm) (matSwap (inertia.idMat n)))
        (matAdd (inertia.idMat n)
          (matSwap (matMul (transposeM Pm) (transposeM Pm))))) :=
    matAdd_cong2 n _ _ _ _
      (rowsLen_matAdd n _ _ hTT hswP) (rowsLen_matAdd n _ _ hQ hswQQ)
      (rowsLen_matAdd n _ _ hTT hIsw) (rowsLen_matAdd n _ _ hI hswQQ)
      (matAdd_cong2 n _ _ _ _ hTT hswP hTT hIsw (matOne_refl _)
        (matSwap_congr horth.1))
      (matAdd_cong2 n _ _ _ _ hQ hswQQ hI hswQQ horth.2 (matOne_refl _))
  refine matOne_trans (matOne_trans hAS hAS4) ?_
  rw [matAdd_shuffle (matMul Pm Pm) (inertia.idMat n)
    (matSwap (inertia.idMat n))
    (matSwap (matMul (transposeM Pm) (transposeM Pm)))]
  exact matOne_symm (matOne_trans hSA hSA4)

/-- A commuting matrix commutes past every symbol's operator at
that matrix: the Horner recursion moves it through the constant's
scaled identity and through the product, the recursion's own step
at the association. -/
private theorem evalM_comm (n : Nat) (M X : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hXl : X.length = n) (hXr : rowsLen n X)
    (hn : 0 < n) (hc : matOneValue (matMul X M) (matMul M X)) :
    ∀ p : poly.Poly,
    matOneValue (matMul X (polyEvalM p M n)) (matMul (polyEvalM p M n) X)
  | [] => by
    have hz := evalM_shape n M hMr hMl hn ([] : poly.Poly)
    have h0 : matOneValue (polyEvalM ([] : poly.Poly) M n)
        (elim.nullMat n n) :=
      evalM_unitTail n M hMl hMr hn [] trivial
    have hleft : matOneValue (matMul X (polyEvalM ([] : poly.Poly) M n))
        (elim.nullMat n n) :=
      matOne_trans
        (matMul_congrR (n := n) (k := n) X (polyEvalM ([] : poly.Poly) M n)
          (elim.nullMat n n) hz.1 (elim.rowsLen_nullMat n n) hz.2
          (elim.length_nullMat n n) hn h0)
        (elim.matMul_nullMat n X hXl)
    have hright : matOneValue (matMul (polyEvalM ([] : poly.Poly) M n) X)
        (elim.nullMat n n) := by
      show matOneValue
        (matMul (inertia.matScaleB BPair.unit (inertia.idMat n)) X)
        (elim.nullMat n n)
      refine matOne_trans
        (inertia.matMul_scaleL BPair.unit (inertia.idMat n) X) ?_
      have h := scaleB_unit_null (n := n) (matMul (inertia.idMat n) X)
        (rowsLen_cast (length_transposeM X hXr (by rw [hXl]; exact hn))
          (rowsLen_matMul (inertia.idMat n) X))
      rw [length_matMul (inertia.idMat n) X, inertia.idMat_len n] at h
      exact h
    exact matOne_trans hleft (matOne_symm hright)
  | c :: p => by
    have ih := evalM_comm n M X hMl hMr hXl hXr hn hc p
    have hep := evalM_shape n M hMr hMl hn p
    have hXt : rowsLen n (transposeM X) :=
      rowsLen_cast hXl (rowsLen_transposeM X)
    have hsc : rowsLen n (inertia.matScaleB c (inertia.idMat n)) :=
      inertia.rowsLen_scaleB c n (inertia.idMat n) (inertia.idMat_rows n)
    have hscl : (inertia.matScaleB c (inertia.idMat n)).length = n :=
      (inertia.length_scaleB c (inertia.idMat n)).trans (inertia.idMat_len n)
    have hprod : rowsLen n (matMul M (polyEvalM p M n)) :=
      rowsLen_cast
        (length_transposeM (polyEvalM p M n) hep.1 (by rw [hep.2]; exact hn))
        (rowsLen_matMul M (polyEvalM p M n))
    have hprodl : (matMul M (polyEvalM p M n)).length = n :=
      (length_matMul M (polyEvalM p M n)).trans hMl
    have hconst : matOneValue
        (matMul X (inertia.matScaleB c (inertia.idMat n)))
        (matMul (inertia.matScaleB c (inertia.idMat n)) X) := by
      refine matOne_trans
        (inertia.matMul_scaleR c n X (inertia.idMat n)
          (inertia.idMat_rows n)) ?_
      refine matOne_trans
        (inertia.matOne_scaleB c
          (inertia.matMul_idR (k := n) n X hXr hXl hn hn)) ?_
      refine matOne_trans
        (matOne_symm (inertia.matOne_scaleB c
          (inertia.idMat_matMul (k := n) n X hXr hXl hn))) ?_
      exact matOne_symm (inertia.matMul_scaleL c (inertia.idMat n) X)
    have hmul : matOneValue (matMul X (matMul M (polyEvalM p M n)))
        (matMul (matMul M (polyEvalM p M n)) X) := by
      refine matOne_trans
        (matOne_symm (matMul_assoc (n := n) (k := n) (s := n) X M
          (polyEvalM p M n) hXr hMr hep.1 hMl hep.2 hn hn)) ?_
      refine matOne_trans (matMul_congrL (matMul X M) (matMul M X)
        (polyEvalM p M n) hc) ?_
      refine matOne_trans
        (matMul_assoc (n := n) (k := n) (s := n) M X (polyEvalM p M n)
          hMr hXr hep.1 hXl hep.2 hn hn) ?_
      refine matOne_trans
        (matMul_congrR (n := n) (k := n) M (matMul X (polyEvalM p M n))
          (matMul (polyEvalM p M n) X)
          (rowsLen_cast
            (length_transposeM (polyEvalM p M n) hep.1
              (by rw [hep.2]; exact hn))
            (rowsLen_matMul X (polyEvalM p M n)))
          (rowsLen_cast (length_transposeM X hXr (by rw [hXl]; exact hn))
            (rowsLen_matMul (polyEvalM p M n) X))
          ((length_matMul X (polyEvalM p M n)).trans hXl)
          ((length_matMul (polyEvalM p M n) X).trans hep.2) hn ih) ?_
      exact matOne_symm (matMul_assoc (n := n) (k := n) (s := n) M
        (polyEvalM p M n) X hMr hep.1 hXr hep.2 hXl hn hn)
    show matOneValue
      (matMul X (matAdd (inertia.matScaleB c (inertia.idMat n))
        (matMul M (polyEvalM p M n))))
      (matMul (matAdd (inertia.matScaleB c (inertia.idMat n))
        (matMul M (polyEvalM p M n))) X)
    refine matOne_trans
      (matMul_addR (inertia.matScaleB c (inertia.idMat n))
        (matMul M (polyEvalM p M n)) hsc hprod (hscl.trans hprodl.symm)
        (by rw [hscl]; exact hn) X (rowsLen_cast hscl.symm hXr)) ?_
    refine matOne_trans ?_
      (matOne_symm (matMul_addL n X hXt
        (inertia.matScaleB c (inertia.idMat n))
        (matMul M (polyEvalM p M n)) hsc hprod))
    exact matAdd_cong2 n _ _ _ _
      (rowsLen_cast (length_transposeM (inertia.matScaleB c (inertia.idMat n))
          hsc (by rw [hscl]; exact hn))
        (rowsLen_matMul X (inertia.matScaleB c (inertia.idMat n))))
      (rowsLen_cast
        (length_transposeM (matMul M (polyEvalM p M n)) hprod
          (by rw [hprodl]; exact hn))
        (rowsLen_matMul X (matMul M (polyEvalM p M n))))
      (rowsLen_cast (length_transposeM X hXr (by rw [hXl]; exact hn))
        (rowsLen_matMul (inertia.matScaleB c (inertia.idMat n)) X))
      (rowsLen_cast (length_transposeM X hXr (by rw [hXl]; exact hn))
        (rowsLen_matMul (matMul M (polyEvalM p M n)) X))
      hconst hmul

/-- The doubling datum commutes past the symbol's operator at the
wrap shift, the orthogonality's own commutation run along the
Horner recursion. -/
private theorem bandEval_comm (m : Nat) (q : poly.Poly) :
    matOneValue
      (matMul (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1)))
      (matMul (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1))
        (bandDatum (permMatAt (2 * m + 1) (tShift m)))) :=
  evalM_comm (2 * m + 1) (chordOp (permMatAt (2 * m + 1) (tShift m)))
    (bandDatum (permMatAt (2 * m + 1) (tShift m)))
    (chordWrap_shape m).2 (chordWrap_shape m).1
    (bandWrap_shape m).2 (bandWrap_shape m).1
    (Nat.succ_le_succ (Nat.zero_le _))
    (band_chord_comm (2 * m + 1) (permMatAt (2 * m + 1) (tShift m))
      (rowsLen_permMatAt _ _) (length_permMatAt _ _)
      (Nat.succ_le_succ (Nat.zero_le _)) (orth_wrap m)) q

/-- The block's top entry at a stated symbol: the column against
the symbol's operator image reads the symbol's multiple of the
doubled side. -/
theorem blockEntry_top (m : Nat) (q : poly.Poly) :
    poly.oneValue
      (deck.redP m (pdotVec (deckColumn m)
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1)) (deckColumn m))))
      (deck.redP m (poly.mul q [BPair.ofNat (2 * (2 * m + 1))])) := by
  refine deck.redP_congr m ?_
  refine deck.pCong_trans
    (pdotVec_prowCong m _ _ _ _ (split.prowOne_refl (redVec m (deckColumn m)))
      (polyEval_column m q)) ?_
  refine deck.pCong_trans
    (deck.pCong_of m (pdotVec_mapMul q (deckColumn m) (deckColumn m))) ?_
  exact deck.pCong_mulBoth (deck.pCong_of m (poly.oneValue_refl q))
    (deck.pCong_of_redP m (deckColumn_selfPair m))
/-- The block's crossed entry at a stated symbol: the column
against the symbol's image of the datum's column reads the unit
tail, the perpendicularity riding the symbol. -/
theorem blockEntry_cross (m : Nat) (q : poly.Poly) :
    poly.unitTail
      (deck.redP m (pdotVec (deckColumn m)
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1))
          (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))))) := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hA := (bandWrap_shape m).1
  have hAl := (bandWrap_shape m).2
  have hOp := evalM_shape (2 * m + 1)
    (chordOp (permMatAt (2 * m + 1) (tShift m)))
    (chordWrap_shape m).1 (chordWrap_shape m).2 hn q
  have hu : (deckColumn m).length = 2 * m + 1 := deckColumn_len m
  have hOpu : (pmatVec
      (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
      (deckColumn m)).length = 2 * m + 1 := by
    rw [pmatVec_len, hOp.2]
  have hAt : rowsLen (2 * m + 1)
      (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m)))) :=
    rowsLen_cast hAl (rowsLen_transposeM _)
  have hAtl : (transposeM
      (bandDatum (permMatAt (2 * m + 1) (tShift m)))).length = 2 * m + 1 :=
    transposeLen _ hA hAl
  have hdouble : transposeM
      (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
      = bandDatum (permMatAt (2 * m + 1) (tShift m)) :=
    transposeM_transposeM _ hA hn (by rw [hAl]; exact hn)
  -- the operator's image of the datum's column at the datum's own
  have hmove : poly.oneValue
      (pdotVec (deckColumn m)
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1))
          (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))))
      (pdotVec
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1)) (deckColumn m))
        (pmatVec (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
          (deckColumn m))) := by
    refine poly.oneValue_trans
      (poly.oneValue_symm (pdotVec_matMul (2 * m + 1)
        (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
        (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        hOp.1 hOp.2 hA hAl (deckColumn m) (deckColumn m) hu hu)) ?_
    refine poly.oneValue_trans
      (pdotVec_matOne _ _ (deckColumn m) (deckColumn m)
        (matOne_symm (bandEval_comm m q))) ?_
    refine poly.oneValue_trans
      (pdotVec_matMul (2 * m + 1)
        (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
        hA hAl hOp.1 hOp.2 (deckColumn m) (deckColumn m) hu hu) ?_
    exact pdotVec_transpose (2 * m + 1)
      (bandDatum (permMatAt (2 * m + 1) (tShift m))) hA hAl
      (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
        (2 * m + 1)) (deckColumn m)) (deckColumn m) hOpu hu
  -- the datum's transpose against the column reads the crossed null
  have hback : poly.oneValue
      (pdotVec (deckColumn m)
        (pmatVec (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
          (deckColumn m)))
      (pdotVec (deckColumn m)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))) := by
    refine poly.oneValue_trans
      (pdotVec_transpose (2 * m + 1)
        (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
        hAt hAtl (deckColumn m) (deckColumn m) hu hu) ?_
    rw [hdouble]
    exact poly.oneValue_refl _
  have hchain : ∃ c, deck.pCong m c
      (pdotVec (deckColumn m)
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1))
          (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m)))) [] := by
    refine deck.pCong_trans (deck.pCong_of m hmove) ?_
    refine deck.pCong_trans
      (pdotVec_prowCong m _ _ _ _ (polyEval_column m q)
        (split.prowOne_refl (redVec m (pmatVec
          (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
          (deckColumn m))))) ?_
    refine deck.pCong_trans
      (deck.pCong_of m (pdotVec_mapMulL q (deckColumn m)
        (pmatVec (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
          (deckColumn m)))) ?_
    refine deck.pCong_trans
      (deck.pCong_mulBoth (deck.pCong_of m (poly.oneValue_refl q))
        (deck.pCong_trans (deck.pCong_of m hback)
          (deck.pCong_of_redP m (deckColumn_crossNull m)))) ?_
    exact deck.pCong_of m (poly.unitTail_oneValue (poly.mul_nil q) trivial)
  exact poly.oneValue_unitTail
    (poly.oneValue_trans (deck.redP_congr m hchain)
      (deck.redP_short m [] (Nat.zero_le m))) trivial

/-- The crossed entry's mirror. -/
theorem blockEntry_crossT (m : Nat) (q : poly.Poly) :
    poly.unitTail
      (deck.redP m (pdotVec
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1)) (deckColumn m)))) := by
  have hchain : ∃ c, deck.pCong m c
      (pdotVec
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1)) (deckColumn m))) [] := by
    refine deck.pCong_trans
      (pdotVec_prowCong m _ _ _ _
        (split.prowOne_refl (redVec m (pmatVec
          (bandDatum (permMatAt (2 * m + 1) (tShift m))) (deckColumn m))))
        (polyEval_column m q)) ?_
    refine deck.pCong_trans
      (deck.pCong_of m (pdotVec_mapMul q
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)) (deckColumn m))) ?_
    refine deck.pCong_trans
      (deck.pCong_mulBoth (deck.pCong_of m (poly.oneValue_refl q))
        (deck.pCong_trans
          (deck.pCong_of m (pdotVec_comm
            (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
              (deckColumn m)) (deckColumn m)))
          (deck.pCong_of_redP m (deckColumn_crossNull m)))) ?_
    exact deck.pCong_of m (poly.unitTail_oneValue (poly.mul_nil q) trivial)
  exact poly.oneValue_unitTail
    (poly.oneValue_trans (deck.redP_congr m hchain)
      (deck.redP_short m [] (Nat.zero_le m))) trivial

/-- The block's bottom entry at a stated symbol: the datum's column
against the symbol's image of itself reads the symbol's multiple of
the band symbol's multiple of the doubled side. -/
theorem blockEntry_bot (m : Nat) (q : poly.Poly) :
    poly.oneValue
      (deck.redP m (pdotVec
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1))
          (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m)))))
      (deck.redP m (poly.mul q (poly.mul bandPoly
        [BPair.ofNat (2 * (2 * m + 1))]))) := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hA := (bandWrap_shape m).1
  have hAl := (bandWrap_shape m).2
  have hOp := evalM_shape (2 * m + 1)
    (chordOp (permMatAt (2 * m + 1) (tShift m)))
    (chordWrap_shape m).1 (chordWrap_shape m).2 hn q
  have hu : (deckColumn m).length = 2 * m + 1 := deckColumn_len m
  have hAu : (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m)).length = 2 * m + 1 := by
    rw [pmatVec_len, hAl]
  have hOpu : (pmatVec
      (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
      (deckColumn m)).length = 2 * m + 1 := by
    rw [pmatVec_len, hOp.2]
  have hAt : rowsLen (2 * m + 1)
      (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m)))) :=
    rowsLen_cast hAl (rowsLen_transposeM _)
  have hAtl : (transposeM
      (bandDatum (permMatAt (2 * m + 1) (tShift m)))).length = 2 * m + 1 :=
    transposeLen _ hA hAl
  have hdouble : transposeM
      (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
      = bandDatum (permMatAt (2 * m + 1) (tShift m)) :=
    transposeM_transposeM _ hA hn (by rw [hAl]; exact hn)
  -- the operator's image of the datum's column at the datum's own
  have hmove : poly.oneValue
      (pdotVec
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1))
          (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))))
      (pdotVec
        (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
          (2 * m + 1)) (deckColumn m))
        (pmatVec (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
          (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m)))) := by
    refine poly.oneValue_trans
      (poly.oneValue_symm (pdotVec_matMul (2 * m + 1)
        (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
        (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        hOp.1 hOp.2 hA hAl (deckColumn m)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)) hu hAu)) ?_
    refine poly.oneValue_trans
      (pdotVec_matOne _ _ (deckColumn m)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)) (matOne_symm (bandEval_comm m q))) ?_
    refine poly.oneValue_trans
      (pdotVec_matMul (2 * m + 1)
        (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
        hA hAl hOp.1 hOp.2 (deckColumn m)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)) hu hAu) ?_
    exact pdotVec_transpose (2 * m + 1)
      (bandDatum (permMatAt (2 * m + 1) (tShift m))) hA hAl
      (pmatVec (polyEvalM q (chordOp (permMatAt (2 * m + 1) (tShift m)))
        (2 * m + 1)) (deckColumn m))
      (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (deckColumn m)) hOpu hAu
  -- the two transposes read the image's own pairing
  have hback : poly.oneValue
      (pdotVec (deckColumn m)
        (pmatVec (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
          (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (deckColumn m))))
      (pdotVec
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))) := by
    refine poly.oneValue_trans
      (pdotVec_transpose (2 * m + 1)
        (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
        hAt hAtl
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)) (deckColumn m) hAu hu) ?_
    rw [hdouble]
    exact poly.oneValue_refl _
  refine deck.redP_congr m ?_
  refine deck.pCong_trans (deck.pCong_of m hmove) ?_
  refine deck.pCong_trans
    (pdotVec_prowCong m _ _ _ _ (polyEval_column m q)
      (split.prowOne_refl (redVec m (pmatVec
        (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m)))))) ?_
  refine deck.pCong_trans
    (deck.pCong_of m (pdotVec_mapMulL q (deckColumn m)
      (pmatVec (transposeM (bandDatum (permMatAt (2 * m + 1) (tShift m))))
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))))) ?_
  exact deck.pCong_mulBoth (deck.pCong_of m (poly.oneValue_refl q))
    (deck.pCong_trans (deck.pCong_of m hback)
      (deck.pCong_of_redP m (deckColumn_imagePair m)))

/-! The count squeeze's slice bridge: the coefficient rows read the
polynomial carrier's folds key by key, so the ground matrices act
on the rows through the column. -/

/-- A scaled entry's key read is the key's scale, the
representative collected. -/
private theorem getAt_scaleP (c : BPair) : ∀ (p : poly.Poly) (i : Nat),
    (ground.getAt BPair.unit (poly.scaleP c p) i).oneValue
      (c * ground.getAt BPair.unit p i)
  | [], _ => BPair.oneValue_symm (BPair.mul_unit c)
  | _ :: _, 0 => BPair.norm_oneValue _
  | _ :: ps, i + 1 => getAt_scaleP c ps i

/-- A row's fold against a slice reads the polynomial fold's key:
the two collected sums exchange at the key's own coefficient. -/
private theorem dotP_slice : ∀ (r : List BPair) (u : List poly.Poly)
    (i : Nat),
    (elim.dotP r (sliceAt i u)).oneValue
      (ground.getAt BPair.unit (poly.scaleDot r u) i)
  | [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ => BPair.oneValue_refl _
  | c :: cs, p :: ps, i => by
    show (c * ground.getAt BPair.unit p i
        + elim.dotP cs (sliceAt i ps)).oneValue
      (ground.getAt BPair.unit
        (poly.add (poly.scaleP c p) (poly.scaleDot cs ps)) i)
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (poly.getAt_add (poly.scaleP c p) (poly.scaleDot cs ps) i) ?_)
    refine BPair.add_congr (getAt_scaleP c p i) ?_
    exact BPair.oneValue_symm (dotP_slice cs ps i)

/-- A ground matrix acts on a slice through the column, row by
row. -/
private theorem matVec_slice : ∀ (M : Mat) (i : Nat)
    (u : List poly.Poly),
    poly.oneValue (elim.matVec M (sliceAt i u))
      (sliceAt i (pmatVec M u))
  | [], _, _ => trivial
  | r :: M, i, u =>
    ⟨BPair.oneValue_trans (elim.dotN_dotP r (sliceAt i u))
      (dotP_slice r u i),
     matVec_slice M i u⟩

/-- The column's entries carry the divisor's own count. -/
private theorem deckColumn_entry_len (m b : Nat) (hb : b < 2 * m + 1) :
    (ground.getAt ([] : poly.Poly) (deckColumn m) b).length = m := by
  rw [deckColumn_getAt m b hb]
  show ((poly.div ((deck.pSum m).dropLast) (deck.pFamN b)).2).length = m
  rw [poly.div_len]
  exact deck.pSum_dropLast_len m

/-- The symbol's multiple reads the null residue. -/
private theorem redP_mulSym (m : Nat) (p : poly.Poly) :
    poly.unitTail (deck.redP m (poly.mul (deck.pSum m) p)) := by
  have hc : ∃ c, deck.pCong m c (poly.mul (deck.pSum m) p) [] :=
    ⟨p, poly.oneValue_refl _⟩
  refine poly.oneValue_unitTail (poly.oneValue_trans
    (deck.redP_congr m hc) (deck.redP_short m [] (Nat.zero_le m))) trivial

/-- A slice at unit-tailed entries reads the unit family. -/
private theorem sliceAt_unitTail : ∀ (u : List poly.Poly) (i : Nat),
    (∀ j, j < u.length →
      poly.unitTail (ground.getAt ([] : poly.Poly) u j)) →
    poly.unitTail (sliceAt i u)
  | [], _, _ => trivial
  | _ :: ps, i, h =>
    ⟨poly.getAt_unitTail (h 0 (Nat.succ_le_succ (Nat.zero_le _))) i,
     sliceAt_unitTail ps i
       (fun j hj => h (j + 1) (Nat.succ_le_succ hj))⟩

/-- The root datum reads the column's entries at the null residue,
entry by entry: the Horner read at the symbol against the column is
the symbol's own multiple. -/
private theorem rootDatum_column (m : Nat) (b : Nat)
    (hb : b < 2 * m + 1) :
    poly.unitTail (ground.getAt ([] : poly.Poly)
      (pmatVec (polyEvalM (deck.pSum m)
        (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
        (deckColumn m)) b) := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hP := evalM_shape (2 * m + 1)
    (chordOp (permMatAt (2 * m + 1) (tShift m)))
    (chordWrap_shape m).1 (chordWrap_shape m).2 hn (deck.pSum m)
  have hcol := polyEval_column m (deck.pSum m)
  have hb' : b < (pmatVec (polyEvalM (deck.pSum m)
      (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
      (deckColumn m)).length := by
    rw [pmatVec_len, hP.2]; exact hb
  have hb1 : b < (pmatVec (polyEvalM (deck.pSum m)
      (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
      (deckColumn m)).length := by
    rw [pmatVec_len, hP.2]; exact hb
  have hb2 : b < ((deckColumn m).map
      (fun p => poly.mul (deck.pSum m) p)).length := by
    rw [ground.length_map, deckColumn_len]; exact hb
  have hred := prow_getAt _ _ hcol b
    (by rw [redVec_len, pmatVec_len, hP.2]; exact hb)
  rw [redVec_getAt m _ b hb1, redVec_getAt m _ b hb2] at hred
  rw [ground.getAt_map ([] : poly.Poly) ([] : poly.Poly)
    (fun p => poly.mul (deck.pSum m) p) (deckColumn m) b
    (by rw [deckColumn_len]; exact hb)] at hred
  have hker : poly.unitTail (deck.redP m
      (ground.getAt ([] : poly.Poly)
        (pmatVec (polyEvalM (deck.pSum m)
          (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
          (deckColumn m)) b)) :=
    poly.oneValue_unitTail hred (redP_mulSym m _)
  have hlen : (ground.getAt ([] : poly.Poly)
      (pmatVec (polyEvalM (deck.pSum m)
        (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
        (deckColumn m)) b).length ≤ m := by
    rw [pmatVec_getAt _ _ b (by rw [hP.2]; exact hb)]
    exact poly.scaleDot_len_le _ _
      (fun j hj => by
        rw [deckColumn_entry_len m j (by rw [deckColumn_len] at hj; exact hj)]
        exact Nat.le_refl m)
  exact poly.unitTail_oneValue_right hker (deck.redP_short m _ hlen)

/-- The action's congruence at its matrix. -/
private theorem matVec_congrM : ∀ (M M' : Mat) (v : List BPair),
    elim.matOneValue M M' →
    poly.oneValue (elim.matVec M v) (elim.matVec M' v)
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | r :: t, r' :: t', v, h =>
    ⟨BPair.oneValue_trans (elim.dotN_dotP r v)
      (BPair.oneValue_trans (elim.dotP_oneValue_left r r' v h.1)
        (BPair.oneValue_symm (elim.dotN_dotP r' v))),
     matVec_congrM t t' v h.2⟩

/-- The chord and the doubling datum exchange at the orthogonality:
either product collects the four crossed terms to one shape, the
two orthogonality reads entering once each. -/
private theorem chord_datum_comm (n : Nat) (Pm : Mat)
    (hP : rowsLen n Pm) (hPl : Pm.length = n) (hn : 0 < n)
    (horth : orthRead Pm n) :
    matOneValue (matMul (chordOp Pm) (bandDatum Pm))
      (matMul (bandDatum Pm) (chordOp Pm)) := by
  have hTtl : (transposeM Pm).length = n := transposeLen Pm hP hPl
  have hTt : rowsLen n (transposeM Pm) :=
    rowsLen_cast hPl (rowsLen_transposeM Pm)
  have hTtT : rowsLen n (transposeM (transposeM Pm)) :=
    rowsLen_cast hTtl (rowsLen_transposeM (transposeM Pm))
  have hSw : rowsLen n (matSwap (transposeM Pm)) :=
    rowsLen_mapRows BPair.swap (transposeM Pm) n hTt
  have hSwl : (matSwap (transposeM Pm)).length = n :=
    (ground.length_map _ (transposeM Pm)).trans hTtl
  have hA : rowsLen n (bandDatum Pm) := (bandDatum_shape n Pm hP hPl).1
  have hAl : (bandDatum Pm).length = n := (bandDatum_shape n Pm hP hPl).2
  have hAt : rowsLen n (transposeM (bandDatum Pm)) :=
    rowsLen_cast hAl (rowsLen_transposeM _)
  have hAtl : (transposeM (bandDatum Pm)).length = n :=
    transposeLen (bandDatum Pm) hA hAl
  have hTT : rowsLen n (matMul Pm Pm) :=
    rowsLen_cast hTtl (rowsLen_matMul Pm Pm)
  have hTtt : (transposeM (transposeM Pm)).length = n :=
    transposeLen (transposeM Pm) hTt hTtl
  have hPP : rowsLen n (matMul Pm (transposeM Pm)) :=
    rowsLen_cast hTtt (rowsLen_matMul Pm (transposeM Pm))
  have hQ : rowsLen n (matMul (transposeM Pm) Pm) :=
    rowsLen_cast hTtl (rowsLen_matMul (transposeM Pm) Pm)
  have hQQ : rowsLen n (matMul (transposeM Pm) (transposeM Pm)) :=
    rowsLen_cast hTtt (rowsLen_matMul (transposeM Pm) (transposeM Pm))
  have hswP : rowsLen n (matSwap (matMul Pm (transposeM Pm))) :=
    rowsLen_mapRows BPair.swap _ n hPP
  have hswQ2 : rowsLen n (matSwap (matMul (transposeM Pm) (transposeM Pm))) :=
    rowsLen_mapRows BPair.swap _ n hQQ
  have hswQ : rowsLen n (matSwap (matMul (transposeM Pm) Pm)) :=
    rowsLen_mapRows BPair.swap _ n hQ
  have hI : rowsLen n (inertia.idMat n) := inertia.idMat_rows n
  have hswI : rowsLen n (matSwap (inertia.idMat n)) :=
    rowsLen_mapRows BPair.swap _ n hI
  -- the left product's collection
  have hTA : matOneValue (matMul Pm (bandDatum Pm))
      (matAdd (matMul Pm Pm) (matSwap (matMul Pm (transposeM Pm)))) := by
    have h := matMul_addR Pm (matSwap (transposeM Pm)) hP hSw
      (hPl.trans hSwl.symm) (by rw [hPl]; exact hn) Pm
      (rowsLen_cast hPl.symm hP)
    rw [matMul_swap] at h
    exact h
  have hTtA : matOneValue (matMul (transposeM Pm) (bandDatum Pm))
      (matAdd (matMul (transposeM Pm) Pm)
        (matSwap (matMul (transposeM Pm) (transposeM Pm)))) := by
    have h := matMul_addR Pm (matSwap (transposeM Pm)) hP hSw
      (hPl.trans hSwl.symm) (by rw [hPl]; exact hn) (transposeM Pm)
      (rowsLen_cast hPl.symm hTt)
    rw [matMul_swap] at h
    exact h
  have hSA : matOneValue (matMul (chordOp Pm) (bandDatum Pm))
      (matAdd
        (matAdd (matMul Pm Pm) (matSwap (inertia.idMat n)))
        (matAdd (inertia.idMat n)
          (matSwap (matMul (transposeM Pm) (transposeM Pm))))) := by
    refine matOne_trans
      (matMul_addL n (bandDatum Pm) hAt Pm (transposeM Pm) hP hTt) ?_
    refine matAdd_cong2 n _ _ _ _
      (rowsLen_cast hAtl (rowsLen_matMul Pm (bandDatum Pm)))
      (rowsLen_cast hAtl (rowsLen_matMul (transposeM Pm) (bandDatum Pm)))
      (rowsLen_matAdd n _ _ hTT hswI)
      (rowsLen_matAdd n _ _ hI hswQ2) ?_ ?_
    · refine matOne_trans hTA ?_
      exact matAdd_cong2 n _ _ _ _ hTT hswP hTT hswI
        (matOne_refl _) (matSwap_congr horth.1)
    · refine matOne_trans hTtA ?_
      exact matAdd_cong2 n _ _ _ _ hQ hswQ2 hI hswQ2
        horth.2 (matOne_refl _)
  -- the right product's collection
  have hAT : matOneValue (matMul (bandDatum Pm) Pm)
      (matAdd (matMul Pm Pm) (matSwap (matMul (transposeM Pm) Pm))) := by
    have h := matMul_addL n Pm hTt Pm (matSwap (transposeM Pm)) hP hSw
    rw [matMul_swapL] at h
    exact h
  have hATt : matOneValue (matMul (bandDatum Pm) (transposeM Pm))
      (matAdd (matMul Pm (transposeM Pm))
        (matSwap (matMul (transposeM Pm) (transposeM Pm)))) := by
    have h := matMul_addL n (transposeM Pm) hTtT Pm
      (matSwap (transposeM Pm)) hP hSw
    rw [matMul_swapL] at h
    exact h
  have hAS : matOneValue (matMul (bandDatum Pm) (chordOp Pm))
      (matAdd
        (matAdd (matMul Pm Pm) (matSwap (inertia.idMat n)))
        (matAdd (inertia.idMat n)
          (matSwap (matMul (transposeM Pm) (transposeM Pm))))) := by
    refine matOne_trans
      (matMul_addR Pm (transposeM Pm) hP hTt (hPl.trans hTtl.symm)
        (by rw [hPl]; exact hn) (bandDatum Pm)
        (rowsLen_cast hPl.symm hA)) ?_
    refine matAdd_cong2 n _ _ _ _
      (rowsLen_cast hTtl (rowsLen_matMul (bandDatum Pm) Pm))
      (rowsLen_cast hTtt (rowsLen_matMul (bandDatum Pm) (transposeM Pm)))
      (rowsLen_matAdd n _ _ hTT hswI)
      (rowsLen_matAdd n _ _ hI hswQ2) ?_ ?_
    · refine matOne_trans hAT ?_
      exact matAdd_cong2 n _ _ _ _ hTT hswQ hTT hswI
        (matOne_refl _) (matSwap_congr horth.2)
    · refine matOne_trans hATt ?_
      exact matAdd_cong2 n _ _ _ _ hPP hswQ2 hI hswQ2
        horth.1 (matOne_refl _)
  exact matOne_trans hSA (matOne_symm hAS)

/-- The doubling datum exchanges with every Horner read at the
chord, the recursion riding the exchange one step per key. -/
private theorem evalM_datum_comm (n : Nat) (Pm : Mat)
    (hP : rowsLen n Pm) (hPl : Pm.length = n) (hn : 0 < n)
    (horth : orthRead Pm n) :
    ∀ q : poly.Poly,
    matOneValue
      (matMul (polyEvalM q (chordOp Pm) n) (bandDatum Pm))
      (matMul (bandDatum Pm) (polyEvalM q (chordOp Pm) n))
  | [] => by
    have hTtl : (transposeM Pm).length = n := transposeLen Pm hP hPl
    have hTt : rowsLen n (transposeM Pm) :=
      rowsLen_cast hPl (rowsLen_transposeM Pm)
    have hA : rowsLen n (bandDatum Pm) := (bandDatum_shape n Pm hP hPl).1
    have hAl : (bandDatum Pm).length = n := (bandDatum_shape n Pm hP hPl).2
    have hIA : rowsLen n (matMul (inertia.idMat n) (bandDatum Pm)) :=
      rowsLen_cast (transposeLen (bandDatum Pm) hA hAl)
        (rowsLen_matMul (inertia.idMat n) (bandDatum Pm))
    have hAI : rowsLen n (matMul (bandDatum Pm) (inertia.idMat n)) :=
      rowsLen_cast (transposeLen (inertia.idMat n) (inertia.idMat_rows n)
        (inertia.idMat_len n))
        (rowsLen_matMul (bandDatum Pm) (inertia.idMat n))
    have hIAl : (matMul (inertia.idMat n) (bandDatum Pm)).length = n :=
      (length_matMul _ _).trans (inertia.idMat_len n)
    have hAIl : (matMul (bandDatum Pm) (inertia.idMat n)).length = n :=
      (length_matMul _ _).trans hAl
    show matOneValue
      (matMul (inertia.matScaleB BPair.unit (inertia.idMat n))
        (bandDatum Pm))
      (matMul (bandDatum Pm)
        (inertia.matScaleB BPair.unit (inertia.idMat n)))
    refine matOne_trans
      (matOne_trans (inertia.matMul_scaleL BPair.unit (inertia.idMat n)
        (bandDatum Pm)) (hIAl ▸ scaleB_unit_null _ hIA)) ?_
    refine matOne_symm (matOne_trans
      (matOne_trans (inertia.matMul_scaleR BPair.unit n (bandDatum Pm)
        (inertia.idMat n) (inertia.idMat_rows n))
        (hAIl ▸ scaleB_unit_null _ hAI)) ?_)
    exact matOne_refl _
  | c :: t => by
    have hTtl : (transposeM Pm).length = n := transposeLen Pm hP hPl
    have hTt : rowsLen n (transposeM Pm) :=
      rowsLen_cast hPl (rowsLen_transposeM Pm)
    have hA : rowsLen n (bandDatum Pm) := (bandDatum_shape n Pm hP hPl).1
    have hAl : (bandDatum Pm).length = n := (bandDatum_shape n Pm hP hPl).2
    have hAt : rowsLen n (transposeM (bandDatum Pm)) :=
      rowsLen_cast hAl (rowsLen_transposeM _)
    have hAtl : (transposeM (bandDatum Pm)).length = n :=
      transposeLen (bandDatum Pm) hA hAl
    have hS : rowsLen n (chordOp Pm) :=
      rowsLen_matAdd n Pm (transposeM Pm) hP hTt
    have hSl : (chordOp Pm).length = n :=
      (length_matAdd Pm _ (hPl.trans hTtl.symm)).trans hPl
    have hE := evalM_shape n (chordOp Pm) hS hSl hn t
    have hEt : (transposeM (polyEvalM t (chordOp Pm) n)).length = n :=
      transposeLen _ hE.1 hE.2
    have hscR : rowsLen n (inertia.matScaleB c (inertia.idMat n)) :=
      inertia.rowsLen_scaleB c n (inertia.idMat n) (inertia.idMat_rows n)
    have hscL : (inertia.matScaleB c (inertia.idMat n)).length = n :=
      (inertia.length_scaleB c (inertia.idMat n)).trans
        (inertia.idMat_len n)
    have hSE : rowsLen n (matMul (chordOp Pm) (polyEvalM t (chordOp Pm) n)) :=
      rowsLen_cast hEt (rowsLen_matMul _ _)
    have hSEl : (matMul (chordOp Pm) (polyEvalM t (chordOp Pm) n)).length
        = n := (length_matMul _ _).trans hSl
    have hSEt : (transposeM (matMul (chordOp Pm)
        (polyEvalM t (chordOp Pm) n))).length = n :=
      transposeLen _ hSE hSEl
    have hscA : matOneValue
        (matMul (inertia.matScaleB c (inertia.idMat n)) (bandDatum Pm))
        (inertia.matScaleB c (bandDatum Pm)) :=
      matOne_trans (inertia.matMul_scaleL c (inertia.idMat n) (bandDatum Pm))
        (inertia.matOne_scaleB c
          (inertia.idMat_matMul n (bandDatum Pm) hA hAl hn))
    have hAsc : matOneValue
        (matMul (bandDatum Pm) (inertia.matScaleB c (inertia.idMat n)))
        (inertia.matScaleB c (bandDatum Pm)) :=
      matOne_trans (inertia.matMul_scaleR c n (bandDatum Pm)
        (inertia.idMat n) (inertia.idMat_rows n))
        (inertia.matOne_scaleB c
          (inertia.matMul_idR n (bandDatum Pm) hA hAl hn hn))
    have hcross : matOneValue
        (matMul (matMul (chordOp Pm) (polyEvalM t (chordOp Pm) n))
          (bandDatum Pm))
        (matMul (bandDatum Pm)
          (matMul (chordOp Pm) (polyEvalM t (chordOp Pm) n))) := by
      refine matOne_trans
        (matMul_assoc (chordOp Pm) (polyEvalM t (chordOp Pm) n)
          (bandDatum Pm) hS hE.1 hA hE.2 hAl hn hn) ?_
      refine matOne_trans
        (matMul_congrR (n := n) (k := n) (chordOp Pm) _ _
          (rowsLen_cast hAtl (rowsLen_matMul _ _))
          (rowsLen_cast hEt (rowsLen_matMul _ _))
          ((length_matMul _ _).trans hE.2)
          ((length_matMul _ _).trans hAl) hn
          (evalM_datum_comm n Pm hP hPl hn horth t)) ?_
      refine matOne_trans
        (matOne_symm (matMul_assoc (chordOp Pm) (bandDatum Pm)
          (polyEvalM t (chordOp Pm) n) hS hA hE.1 hAl hE.2 hn hn)) ?_
      refine matOne_trans
        (matMul_congrL _ _ (polyEvalM t (chordOp Pm) n)
          (chord_datum_comm n Pm hP hPl hn horth)) ?_
      exact matMul_assoc (bandDatum Pm) (chordOp Pm)
        (polyEvalM t (chordOp Pm) n) hA hS hE.1 hSl hE.2 hn hn
    show matOneValue
      (matMul (matAdd (inertia.matScaleB c (inertia.idMat n))
        (matMul (chordOp Pm) (polyEvalM t (chordOp Pm) n)))
        (bandDatum Pm))
      (matMul (bandDatum Pm)
        (matAdd (inertia.matScaleB c (inertia.idMat n))
          (matMul (chordOp Pm) (polyEvalM t (chordOp Pm) n))))
    refine matOne_trans
      (matMul_addL n (bandDatum Pm) hAt _ _ hscR hSE) ?_
    refine matOne_symm (matOne_trans
      (matMul_addR _ _ hscR hSE (hscL.trans hSEl.symm)
        (by rw [hscL]; exact hn) (bandDatum Pm)
        (rowsLen_cast hscL.symm hA)) ?_)
    refine matAdd_cong2 n _ _ _ _
      (rowsLen_cast (transposeLen _ hscR hscL)
        (rowsLen_matMul (bandDatum Pm) _))
      (rowsLen_cast hSEt (rowsLen_matMul (bandDatum Pm) _))
      (rowsLen_cast hAtl
        (rowsLen_matMul (inertia.matScaleB c (inertia.idMat n)) _))
      (rowsLen_cast hAtl (rowsLen_matMul _ (bandDatum Pm))) ?_ ?_
    · exact matOne_trans hAsc (matOne_symm hscA)
    · exact matOne_symm hcross

/-- A member row sits in the root datum's kernel: the slice reads
the column's own symbol multiple at the null residue and the
literal count below the top. -/
private theorem memberRow_ker (m i : Nat) :
    poly.unitTail (elim.matVec
      (polyEvalM (deck.pSum m)
        (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
      (sliceAt i (deckColumn m))) :=
  poly.oneValue_unitTail (matVec_slice _ i (deckColumn m))
    (sliceAt_unitTail _ i (fun b hb =>
      rootDatum_column m b (by
        rw [pmatVec_len,
          (evalM_shape (2 * m + 1)
            (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (chordWrap_shape m).1 (chordWrap_shape m).2
            (Nat.succ_le_succ (Nat.zero_le _)) (deck.pSum m)).2] at hb
        exact hb)))

/-- An image row sits in the root datum's kernel: the datum crosses
the doubling and reads the member row's own null. -/
private theorem imageRow_ker (m i : Nat) :
    poly.unitTail (elim.matVec
      (polyEvalM (deck.pSum m)
        (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
      (elim.matVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (sliceAt i (deckColumn m)))) := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hP : rowsLen (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) :=
    rowsLen_permMatAt _ _
  have hPl : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hA : rowsLen (2 * m + 1)
      (bandDatum (permMatAt (2 * m + 1) (tShift m))) := (bandWrap_shape m).1
  have hE := evalM_shape (2 * m + 1)
    (chordOp (permMatAt (2 * m + 1) (tShift m)))
    (chordWrap_shape m).1 (chordWrap_shape m).2 hn (deck.pSum m)
  have hs : (sliceAt i (deckColumn m)).length = 2 * m + 1 := by
    show ((deckColumn m).map _).length = 2 * m + 1
    rw [ground.length_map, deckColumn_len]
  refine poly.oneValue_unitTail
    (poly.oneValue_symm (elim.matVec_matMul _ _ (2 * m + 1) hA _ hs)) ?_
  refine poly.oneValue_unitTail
    (matVec_congrM _ _ _
      (evalM_datum_comm (2 * m + 1) (permMatAt (2 * m + 1) (tShift m))
        hP hPl hn (orth_wrap m) (deck.pSum m))) ?_
  refine poly.oneValue_unitTail
    (elim.matVec_matMul _ _ (2 * m + 1) hE.1 _ hs) ?_
  exact elim.matVec_null _ _ (memberRow_ker m i)

/-- A paired family's kernel read collects from the two members'
own, key by key. -/
private theorem kerList_flatMapPair (D : Mat) (f g : Nat → List BPair)
    (hf : ∀ i, poly.unitTail (elim.matVec D (f i)))
    (hg : ∀ i, poly.unitTail (elim.matVec D (g i))) :
    ∀ l : List Nat, kerList D (l.flatMap (fun i => [f i, g i]))
  | [] => rfl
  | i :: t => by
    show (decide (poly.unitTail (elim.matVec D (f i)))
      && ((g i :: t.flatMap (fun j => [f j, g j])).all
        (fun v => decide (poly.unitTail (elim.matVec D v))))) = true
    rw [decide_eq_true (hf i)]
    show (decide (poly.unitTail (elim.matVec D (g i)))
      && ((t.flatMap (fun j => [f j, g j])).all
        (fun v => decide (poly.unitTail (elim.matVec D v))))) = true
    rw [decide_eq_true (hg i)]
    exact kerList_flatMapPair D f g hf hg t

/-- The pair base sits in the root datum's kernel whole. -/
private theorem pairBase_ker (m : Nat) :
    kerList (polyEvalM (deck.pSum m)
      (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
      (pairBase m) :=
  kerList_flatMapPair _ _ _ (memberRow_ker m) (imageRow_ker m)
    (List.range m)

/-- A summed row's fold splits at the two rows, the rows at one
count. -/
private theorem scaleDot_addRow : ∀ (r r' : List BPair)
    (u : List poly.Poly), r.length = r'.length →
    poly.oneValue
      (poly.scaleDot (List.zipWith (fun x y => x + y) r r') u)
      (poly.add (poly.scaleDot r u) (poly.scaleDot r' u))
  | [], [], _, _ => poly.oneValue_refl _
  | [], _ :: _, _, hl => Nat.noConfusion hl
  | _ :: _, [], _, hl => Nat.noConfusion hl
  | _ :: _, _ :: _, [], _ => poly.oneValue_refl _
  | c :: r, d :: r', p :: u, hl => by
    show poly.oneValue
      (poly.add (poly.scaleP (c + d) p)
        (poly.scaleDot (List.zipWith (fun x y => x + y) r r') u))
      (poly.add (poly.add (poly.scaleP c p) (poly.scaleDot r u))
        (poly.add (poly.scaleP d p) (poly.scaleDot r' u)))
    refine poly.oneValue_trans
      (poly.add_congr (poly.scaleP_add c d p)
        (scaleDot_addRow r r' u (Nat.succ.inj hl))) ?_
    exact poly.add_shuffle (poly.scaleP c p) (poly.scaleP d p)
      (poly.scaleDot r u) (poly.scaleDot r' u)

/-- A swapped scalar's rescaling reads the rescaling's own
negation, entry by entry. -/
private theorem scaleP_swapScalar (c : BPair) : ∀ p : poly.Poly,
    poly.oneValue (poly.scaleP c.swap p) (poly.neg (poly.scaleP c p))
  | [] => trivial
  | x :: p =>
    ⟨by
      show ((c.swap * x).norm).oneValue (((c * x).norm).swap)
      rw [BPair.swap_mul]
      exact BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_symm
          (ground.swap_congr (BPair.norm_oneValue (c * x)))),
     scaleP_swapScalar c p⟩

/-- A swapped row's fold reads the fold's own negation. -/
private theorem scaleDot_swapRow : ∀ (r : List BPair)
    (u : List poly.Poly),
    poly.oneValue (poly.scaleDot (r.map BPair.swap) u)
      (poly.neg (poly.scaleDot r u))
  | [], _ => poly.oneValue_refl _
  | _ :: _, [] => poly.oneValue_refl _
  | c :: r, p :: u => by
    show poly.oneValue
      (poly.add (poly.scaleP c.swap p) (poly.scaleDot (r.map BPair.swap) u))
      (poly.neg (poly.add (poly.scaleP c p) (poly.scaleDot r u)))
    rw [poly.neg_sum]
    exact poly.add_congr (scaleP_swapScalar c p) (scaleDot_swapRow r u)



/-- Two residues' sum reads the sum's own residue, the congruence
collected at the joined witness and the count below the top. -/
private theorem redP_add (m : Nat) (x y : poly.Poly) :
    poly.oneValue (poly.add (deck.redP m x) (deck.redP m y))
      (deck.redP m (poly.add x y)) := by
  obtain ⟨cx, hx⟩ := deck.redP_pCong m x
  obtain ⟨cy, hy⟩ := deck.redP_pCong m y
  have hw : deck.pCong m (poly.add cx cy) (poly.add x y)
      (poly.add (deck.redP m x) (deck.redP m y)) := by
    show poly.oneValue (poly.add x y)
      (poly.add (poly.add (deck.redP m x) (deck.redP m y))
        (poly.mul (deck.pSum m) (poly.add cx cy)))
    refine poly.oneValue_trans (poly.add_congr hx hy) ?_
    refine poly.oneValue_trans (poly.add_shuffle _ _ _ _) ?_
    exact poly.add_congr (poly.oneValue_refl _)
      (poly.oneValue_symm (poly.mul_sum (deck.pSum m) cx cy))
  have hlx : (deck.redP m x).length = m := by
    show ((poly.div ((deck.pSum m).dropLast) x).2).length = m
    rw [poly.div_len]
    exact deck.pSum_dropLast_len m
  have hly : (deck.redP m y).length = m := by
    show ((poly.div ((deck.pSum m).dropLast) y).2).length = m
    rw [poly.div_len]
    exact deck.pSum_dropLast_len m
  refine poly.oneValue_symm (poly.oneValue_trans
    (deck.redP_congr m ⟨_, hw⟩) ?_)
  exact deck.redP_short m _
    (poly.add_len_le _ _ _ (Nat.le_of_eq hlx) (Nat.le_of_eq hly))

/-- A fold of residues reads the fold's own residue. -/
private theorem redP_pfold (m : Nat) (f : Nat → poly.Poly) :
    ∀ l : List Nat,
    poly.oneValue (pfold (fun b => deck.redP m (f b)) l)
      (deck.redP m (pfold f l))
  | [] =>
    poly.oneValue_symm (deck.redP_short m [] (Nat.zero_le m))
  | a :: t => by
    show poly.oneValue
      (poly.add (deck.redP m (f a)) (pfold (fun b => deck.redP m (f b)) t))
      (deck.redP m (poly.add (f a) (pfold f t)))
    refine poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl _) (redP_pfold m f t)) ?_
    exact redP_add m (f a) (pfold f t)

/-- The orbit sum's fold against a keyed family reads the family's
own fold. -/
private theorem scaleDot_onesMap : ∀ (l : List Nat) (f : Nat → poly.Poly),
    poly.oneValue
      (poly.scaleDot (List.replicate l.length (BPair.ofPos Pos.one)) (l.map f))
      (pfold f l)
  | [], _ => trivial
  | a :: t, f => by
    show poly.oneValue
      (poly.add (poly.scaleP (BPair.ofPos Pos.one) (f a))
        (poly.scaleDot (List.replicate t.length (BPair.ofPos Pos.one)) (t.map f)))
      (poly.add (f a) (pfold f t))
    exact poly.add_congr (poly.scaleP_one (f a)) (scaleDot_onesMap t f)

/-- A member row pairs the orbit sum at the sum's unit: the key
list's fold reads the symbol's own multiple at the null residue. -/
private theorem memberPerp (m i : Nat) :
    (elim.dotP (orbitSum m) (sliceAt i (deckColumn m))).oneValue
      BPair.unit := by
  refine BPair.oneValue_trans (dotP_slice (orbitSum m) (deckColumn m) i) ?_
  have hones : orbitSum m
      = List.replicate (List.range (2 * m + 1)).length (BPair.ofPos Pos.one) := by
    show List.replicate (2 * m + 1) (BPair.ofPos Pos.one) = _
    rw [ground.length_range]
  have hrow : poly.oneValue
      (poly.scaleDot (orbitSum m) (deckColumn m)) [] := by
    rw [hones]
    refine poly.oneValue_trans
      (scaleDot_onesMap (List.range (2 * m + 1))
        (fun b => deck.redP m (deck.pFamN b))) ?_
    refine poly.oneValue_trans
      (redP_pfold m deck.pFamN (List.range (2 * m + 1))) ?_
    refine poly.oneValue_trans (deck.redP_congr m (famSum_null m)) ?_
    exact deck.redP_short m [] (Nat.zero_le m)
  exact poly.getAt_unitTail (poly.oneValue_unitTail hrow trivial) i

/-- A fold of negations reads the fold's own negation. -/
private theorem pfold_neg (f : Nat → poly.Poly) :
    ∀ l : List Nat,
    poly.oneValue (pfold (fun b => poly.neg (f b)) l)
      (poly.neg (pfold f l))
  | [] => trivial
  | a :: t => by
    show poly.oneValue
      (poly.add (poly.neg (f a)) (pfold (fun b => poly.neg (f b)) t))
      (poly.neg (poly.add (f a) (pfold f t)))
    rw [poly.neg_sum]
    exact poly.add_congr (poly.oneValue_refl _) (pfold_neg f t)

/-- A fold over the range reads its wrap-shifted family at one
value, the shift's two witnesses the reindexing's own. -/
private theorem pfold_shift (m : Nat) (g h : Nat → Nat)
    (hgh : ∀ x, x < 2 * m + 1 → h (g x) = x)
    (hhg : ∀ x, x < 2 * m + 1 → g (h x) = x)
    (hgl : ∀ j, j < 2 * m + 1 → g j < 2 * m + 1)
    (hhl : ∀ j, j < 2 * m + 1 → h j < 2 * m + 1)
    (f : Nat → poly.Poly) :
    poly.oneValue
      (pfold (fun b => f (g b)) (List.range (2 * m + 1)))
      (pfold f (List.range (2 * m + 1))) := by
  refine poly.oneValue_symm
    (ground.famFold_reindex_ov poly.polyFoldLaws.toCommLaws []
      f (ground.distinctList_range (2 * m + 1))
      (fun x hx => hgh x (ground.ltOfMem hx))
      (fun x hx => hhg x (ground.ltOfMem hx)) ?_ ?_)
  · intro x hx
    have hxl : x < 2 * m + 1 := ground.ltOfMem hx
    rw [ground.countOf_range_one (hgl x hxl)]
    exact Nat.le_refl 1
  · intro x hx
    have hxl : x < 2 * m + 1 := ground.ltOfMem hx
    rw [ground.countOf_range_one (hhl x hxl)]
    exact Nat.le_refl 1

/-- The doubling datum's entry at a key: the shift's read against
the witness's, the image row the member row's negation. -/
private theorem bandVec_entry (m : Nat) (u : List poly.Poly)
    (hu : u.length = 2 * m + 1) (j : Nat) (hj : j < 2 * m + 1) :
    poly.oneValue
      (ground.getAt ([] : poly.Poly)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m))) u) j)
      (poly.add (ground.getAt ([] : poly.Poly) u (sShift m j))
        (poly.neg (ground.getAt ([] : poly.Poly) u (tShift m j)))) := by
  have hT : transposeM (permMatAt (2 * m + 1) (tShift m))
      = permMatAt (2 * m + 1) (sShift m) :=
    transposeM_permMatAt (2 * m + 1) (tShift m) (sShift m)
      (fun l _ => sShift_tShift m l) (tShift_sShift m)
  have hTl : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hSl : (permMatAt (2 * m + 1) (sShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hswl : (matSwap (permMatAt (2 * m + 1) (sShift m))).length
      = 2 * m + 1 :=
    (ground.length_map _ _).trans hSl
  have hAl : (matAdd (permMatAt (2 * m + 1) (tShift m))
      (matSwap (permMatAt (2 * m + 1) (sShift m)))).length = 2 * m + 1 :=
    (length_matAdd _ _ (hTl.trans hswl.symm)).trans hTl
  have hrowT : (ground.getAt ([] : List BPair)
      (permMatAt (2 * m + 1) (tShift m)) j).length = 2 * m + 1 :=
    rowsLen_getAt _ j (rowsLen_permMatAt _ _) (by rw [hTl]; exact hj)
  have hrowS : (ground.getAt ([] : List BPair)
      (permMatAt (2 * m + 1) (sShift m)) j).length = 2 * m + 1 :=
    rowsLen_getAt _ j (rowsLen_permMatAt _ _) (by rw [hSl]; exact hj)
  show poly.oneValue
    (ground.getAt ([] : poly.Poly)
      (pmatVec (matAdd (permMatAt (2 * m + 1) (tShift m))
        (matSwap (transposeM (permMatAt (2 * m + 1) (tShift m))))) u) j) _
  rw [hT, pmatVec_getAt _ u j (by rw [hAl]; exact hj),
    getAt_matAdd _ _ j (by rw [hTl]; exact hj) (by rw [hswl]; exact hj),
    show ground.getAt ([] : List BPair)
        (matSwap (permMatAt (2 * m + 1) (sShift m))) j
      = (ground.getAt ([] : List BPair)
          (permMatAt (2 * m + 1) (sShift m)) j).map BPair.swap from
      ground.getAt_map ([] : List BPair) ([] : List BPair)
        (fun r => r.map BPair.swap) _ j (by rw [hSl]; exact hj)]
  refine poly.oneValue_trans
    (scaleDot_addRow _ _ u
      (by rw [hrowT, ground.length_map, hrowS])) ?_
  refine poly.add_congr ?_ ?_
  · refine scaleDot_permRow (2 * m + 1) (tShift m) u hu j (sShift m j)
      hj (sShift_lt m j hj) (tShift_sShift m j hj) ?_
    intro k hk hne hc
    exact absurd ((sShift_tShift m k).symm.trans
      (congrArg (sShift m) hc)) hne
  · refine poly.oneValue_trans (scaleDot_swapRow _ u) ?_
    refine poly.swapMap_oneValue ?_
    refine scaleDot_permRow (2 * m + 1) (sShift m) u hu j (tShift m j)
      hj (tShift_lt m j hj) (sShift_tShift m j) ?_
    intro k hk hne hc
    exact absurd ((tShift_sShift m k hk).symm.trans
      (congrArg (tShift m) hc)) hne

/-- An image row pairs the orbit sum at the sum's unit: the two
shifted folds read one value and the negation withdraws them. -/
private theorem imagePerp (m i : Nat) :
    (elim.dotP (orbitSum m)
      (elim.matVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (sliceAt i (deckColumn m)))).oneValue BPair.unit := by
  have hsl : (sliceAt i (deckColumn m)).length = 2 * m + 1 := by
    show ((deckColumn m).map _).length = 2 * m + 1
    rw [ground.length_map, deckColumn_len]
  have hTl : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hAl : (bandDatum (permMatAt (2 * m + 1) (tShift m))).length
      = 2 * m + 1 := by
    show (matAdd _ (matSwap (transposeM _))).length = 2 * m + 1
    refine (length_matAdd _ _ ?_).trans hTl
    rw [hTl]
    show 2 * m + 1
      = ((transposeM (permMatAt (2 * m + 1) (tShift m))).map
        (fun r => r.map BPair.swap)).length
    rw [ground.length_map]
    exact (transposeLen _ (rowsLen_permMatAt _ _) hTl).symm
  have hml : (elim.matVec
      (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (sliceAt i (deckColumn m))).length = 2 * m + 1 := by
    show ((bandDatum _).map _).length = 2 * m + 1
    rw [ground.length_map]
    exact hAl
  have hpl : (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m)).length = 2 * m + 1 := by
    rw [pmatVec_len]
    exact hAl
  have hsll : (sliceAt i (pmatVec
      (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m))).length = 2 * m + 1 := by
    show ((pmatVec _ _).map _).length = 2 * m + 1
    rw [ground.length_map]
    exact hpl
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_right (orbitSum m) _ _
      (matVec_slice _ i (deckColumn m))) ?_
  refine BPair.oneValue_trans
    (dotP_slice (orbitSum m) _ i) ?_
  have hrow : poly.oneValue
      (poly.scaleDot (orbitSum m)
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))) [] := by
    rw [scaleDot_getAt (orbitSum m) _
        (by rw [orbitSum_len, hpl]), orbitSum_len]
    refine poly.oneValue_trans
      (pfold_brange (2 * m + 1) (g := fun j =>
        poly.add (ground.getAt ([] : poly.Poly) (deckColumn m)
          (sShift m j))
        (poly.neg (ground.getAt ([] : poly.Poly) (deckColumn m)
          (tShift m j))))
        (fun j hjl => by
          show poly.oneValue
            (poly.scaleP (ground.getAt BPair.unit (orbitSum m) j) _) _
          rw [show ground.getAt BPair.unit (orbitSum m) j
            = BPair.ofPos Pos.one from
            ground.getAt_replicate BPair.unit (BPair.ofPos Pos.one)
              (2 * m + 1) j hjl]
          refine poly.oneValue_trans (poly.scaleP_one _) ?_
          exact bandVec_entry m (deckColumn m) (deckColumn_len m) j hjl))
      ?_
    refine poly.oneValue_trans
      (pfold_split _ _ (List.range (2 * m + 1))) ?_
    refine poly.oneValue_trans
      (poly.add_congr
        (pfold_shift m (sShift m) (tShift m) (tShift_sShift m)
          (fun l _ => sShift_tShift m l) (sShift_lt m) (tShift_lt m)
          (fun b => ground.getAt ([] : poly.Poly) (deckColumn m) b))
        (poly.oneValue_trans
          (pfold_neg
            (fun b => ground.getAt ([] : poly.Poly) (deckColumn m)
              (tShift m b)) (List.range (2 * m + 1)))
          (poly.swapMap_oneValue
            (pfold_shift m (tShift m) (sShift m)
              (fun l _ => sShift_tShift m l)
              (tShift_sShift m) (tShift_lt m) (sShift_lt m)
              (fun b => ground.getAt ([] : poly.Poly)
                (deckColumn m) b))))) ?_
    exact poly.unitTail_oneValue
      (poly.add_neg (pfold
        (fun b => ground.getAt ([] : poly.Poly) (deckColumn m) b)
        (List.range (2 * m + 1)))) trivial
  exact poly.getAt_unitTail (poly.oneValue_unitTail hrow trivial) i

/-- Two column entries at keys joining to the side read one value,
the reflected wrap's own. -/
private theorem wrapVal (m a b : Nat) (h : a + b = 2 * m + 1)
    (ha : a < 2 * m + 1) (hb : b < 2 * m + 1) :
    poly.oneValue (ground.getAt ([] : poly.Poly) (deckColumn m) a)
      (ground.getAt ([] : poly.Poly) (deckColumn m) b) := by
  rw [deckColumn_getAt m a ha, deckColumn_getAt m b hb]
  exact deck.redP_congr m (deck.pFamN_wrapRefl m a b h)

/-- A negated vector's rescaling reads the rescaling's own
negation. -/
private theorem scaleP_negVec (c : BPair) : ∀ p : poly.Poly,
    poly.oneValue (poly.scaleP c (poly.neg p))
      (poly.neg (poly.scaleP c p))
  | [] => trivial
  | x :: p =>
    ⟨by
      show ((c * x.swap).norm).oneValue (((c * x).norm).swap)
      rw [BPair.mul_swap]
      exact BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_symm
          (ground.swap_congr (BPair.norm_oneValue (c * x)))),
     scaleP_negVec c p⟩

/-- The reflected key's crossed member reads the shifted key's own:
the wrap pairs the keys at the side's join, the middle pair
collapsing at its own wrap. -/
private theorem crossKey (m i b : Nat) (hbl : b < 2 * m + 1) :
    poly.oneValue
      (poly.scaleP (ground.getAt BPair.unit
        (ground.getAt ([] : poly.Poly) (deckColumn m) (2 * m - b)) i)
        (ground.getAt ([] : poly.Poly) (deckColumn m)
          (tShift m (2 * m - b))))
      (poly.scaleP (ground.getAt BPair.unit
        (ground.getAt ([] : poly.Poly) (deckColumn m) (tShift m b)) i)
        (ground.getAt ([] : poly.Poly) (deckColumn m) b)) := by
  have hsub0 : 2 * m - 2 * m = 0 :=
    ground.addCancelL (2 * m)
      ((ground.natAddSubCancel (Nat.le_refl (2 * m))).trans
        (Nat.add_zero (2 * m)).symm)
  cases Nat.lt_or_ge b (2 * m) with
  | inr hge =>
    have hb2m : b = 2 * m :=
      Nat.le_antisymm (Nat.le_of_succ_le_succ hbl) hge
    subst hb2m
    rw [hsub0, tShift_top m]
    cases m with
    | zero => exact poly.oneValue_refl _
    | succ m' =>
      have hpos : (0 : Nat) < 2 * (m' + 1) := by
        rw [Nat.two_mul]
        exact Nat.succ_le_succ (Nat.zero_le _)
      have ht0 : tShift (m' + 1) 0 = 1 :=
        tShift_ne (m' + 1) 0
          (fun he => Nat.lt_irrefl 0 (he ▸ hpos))
      rw [ht0]
      exact poly.oneValue_scaleP _
        (wrapVal (m' + 1) 1 (2 * (m' + 1))
          (by rw [Nat.add_comm])
          (Nat.succ_le_succ (Nat.succ_le_of_lt hpos))
          (Nat.le_refl _))
  | inl hlt =>
    have htb : tShift m b = b + 1 :=
      tShift_ne m b (fun he => Nat.lt_irrefl b (he ▸ hlt))
    have hjoin : (2 * m - b) + (b + 1) = 2 * m + 1 := by
      rw [← Nat.add_assoc (2 * m - b) b 1]
      rw [Nat.add_comm (2 * m - b) b,
        ground.natAddSubCancel (Nat.le_of_lt hlt)]
    have hrb : 2 * m - b < 2 * m + 1 :=
      Nat.succ_le_succ (Nat.sub_le (2 * m) b)
    have hscal : BPair.oneValue
        (ground.getAt BPair.unit
          (ground.getAt ([] : poly.Poly) (deckColumn m) (2 * m - b)) i)
        (ground.getAt BPair.unit
          (ground.getAt ([] : poly.Poly) (deckColumn m) (tShift m b)) i) := by
      rw [htb]
      exact poly.oneValue_getAt i
        (wrapVal m (2 * m - b) (b + 1) hjoin hrb
          (Nat.succ_le_succ (Nat.succ_le_of_lt hlt)))
    cases b with
    | zero =>
      show poly.oneValue
        (poly.scaleP (ground.getAt BPair.unit
          (ground.getAt ([] : poly.Poly) (deckColumn m) (2 * m)) i)
          (ground.getAt ([] : poly.Poly) (deckColumn m)
            (tShift m (2 * m))))
        (poly.scaleP (ground.getAt BPair.unit
          (ground.getAt ([] : poly.Poly) (deckColumn m) (tShift m 0)) i)
          (ground.getAt ([] : poly.Poly) (deckColumn m) 0))
      rw [tShift_top m]
      exact poly.scaleP_congr hscal _
    | succ b' =>
      have hrne : tShift m (2 * m - (b' + 1)) = (2 * m - (b' + 1)) + 1 := by
        refine tShift_ne m (2 * m - (b' + 1)) (fun he => ?_)
        have hb0 : b' + 1 = 0 :=
          ((ground.natSubSubCancel (2 * m) (b' + 1) (Nat.le_of_lt hlt)).symm.trans
            ((congrArg (fun z => 2 * m - z) he).trans hsub0))
        exact Nat.noConfusion hb0
      rw [hrne]
      have hjoin2 : ((2 * m - (b' + 1)) + 1) + (b' + 1) = 2 * m + 1 := by
        rw [Nat.add_comm ((2 * m - (b' + 1)) + 1) (b' + 1),
          ← Nat.add_assoc (b' + 1) (2 * m - (b' + 1)) 1,
          ground.natAddSubCancel (Nat.le_of_lt hlt)]
      have hrb1 : (2 * m - (b' + 1)) + 1 < 2 * m + 1 := by
        refine Nat.succ_le_succ ?_
        have h1 : (2 * m - (b' + 1)) + 1 ≤ (2 * m - (b' + 1)) + (b' + 1) :=
          Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le b')) _
        exact Nat.le_trans h1 (Nat.le_of_eq
          ((Nat.add_comm (2 * m - (b' + 1)) (b' + 1)).trans
            (ground.natAddSubCancel (Nat.le_of_lt hlt))))
      refine poly.oneValue_trans
        (poly.oneValue_scaleP _
          (wrapVal m ((2 * m - (b' + 1)) + 1) (b' + 1) hjoin2 hrb1 hbl)) ?_
      exact poly.scaleP_congr hscal _

/-- A member row pairs an image row at the sum's unit: the two
crossed folds read one family at the wrap's reflection, and the
negation withdraws them. -/
private theorem sliceCross_null (m i j : Nat) :
    (elim.dotP (sliceAt i (deckColumn m))
      (elim.matVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (sliceAt j (deckColumn m)))).oneValue BPair.unit := by
  have hTl : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hAl : (bandDatum (permMatAt (2 * m + 1) (tShift m))).length
      = 2 * m + 1 := by
    show (matAdd _ (matSwap (transposeM _))).length = 2 * m + 1
    refine (length_matAdd _ _ ?_).trans hTl
    rw [hTl]
    show 2 * m + 1
      = ((transposeM (permMatAt (2 * m + 1) (tShift m))).map
        (fun r => r.map BPair.swap)).length
    rw [ground.length_map]
    exact (transposeLen _ (rowsLen_permMatAt _ _) hTl).symm
  have hml : (elim.matVec
      (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (sliceAt j (deckColumn m))).length = 2 * m + 1 := by
    show ((bandDatum _).map _).length = 2 * m + 1
    rw [ground.length_map]
    exact hAl
  have hpl : (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m)).length = 2 * m + 1 := by
    rw [pmatVec_len]
    exact hAl
  have hsll : (sliceAt j (pmatVec
      (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (deckColumn m))).length = 2 * m + 1 := by
    show ((pmatVec _ _).map _).length = 2 * m + 1
    rw [ground.length_map]
    exact hpl
  have hsl : (sliceAt i (deckColumn m)).length = 2 * m + 1 := by
    show ((deckColumn m).map _).length = 2 * m + 1
    rw [ground.length_map, deckColumn_len]
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_right (sliceAt i (deckColumn m)) _ _
      (matVec_slice _ j (deckColumn m))) ?_
  refine BPair.oneValue_trans (dotP_slice (sliceAt i (deckColumn m)) _ j) ?_
  have hrow : poly.oneValue
      (poly.scaleDot (sliceAt i (deckColumn m))
        (pmatVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (deckColumn m))) [] := by
    rw [scaleDot_getAt (sliceAt i (deckColumn m)) _
        (by rw [hsl, hpl]), hsl]
    refine poly.oneValue_trans
      (pfold_brange (2 * m + 1) (g := fun b =>
        poly.add
          (poly.scaleP (ground.getAt BPair.unit
            (ground.getAt ([] : poly.Poly) (deckColumn m) b) i)
            (ground.getAt ([] : poly.Poly) (deckColumn m) (sShift m b)))
          (poly.neg
            (poly.scaleP (ground.getAt BPair.unit
              (ground.getAt ([] : poly.Poly) (deckColumn m) b) i)
              (ground.getAt ([] : poly.Poly) (deckColumn m)
                (tShift m b)))))
        (fun b hbl => by
          show poly.oneValue
            (poly.scaleP (ground.getAt BPair.unit
              (sliceAt i (deckColumn m)) b) _) _
          rw [show ground.getAt BPair.unit (sliceAt i (deckColumn m)) b
            = ground.getAt BPair.unit
                (ground.getAt ([] : poly.Poly) (deckColumn m) b) i from
            ground.getAt_map ([] : poly.Poly) BPair.unit
              (fun p => ground.getAt BPair.unit p i) (deckColumn m) b
              (by rw [deckColumn_len]; exact hbl)]
          refine poly.oneValue_trans
            (poly.oneValue_scaleP _
              (bandVec_entry m (deckColumn m) (deckColumn_len m) b hbl))
            ?_
          refine poly.oneValue_trans (poly.scaleP_sum _ _ _) ?_
          exact poly.add_congr (poly.oneValue_refl _)
            (scaleP_negVec _ _))) ?_
    refine poly.oneValue_trans
      (pfold_split _ _ (List.range (2 * m + 1))) ?_
    refine poly.oneValue_trans
      (poly.add_congr (poly.oneValue_refl _)
        (pfold_neg _ (List.range (2 * m + 1)))) ?_
    -- the two crossed folds read one family
    have hYs : poly.oneValue
        (pfold (fun b =>
          poly.scaleP (ground.getAt BPair.unit
            (ground.getAt ([] : poly.Poly) (deckColumn m) b) i)
            (ground.getAt ([] : poly.Poly) (deckColumn m) (sShift m b)))
          (List.range (2 * m + 1)))
        (pfold (fun b =>
          poly.scaleP (ground.getAt BPair.unit
            (ground.getAt ([] : poly.Poly) (deckColumn m) (tShift m b)) i)
            (ground.getAt ([] : poly.Poly) (deckColumn m) b))
          (List.range (2 * m + 1))) := by
      refine poly.oneValue_trans
        (pfold_brange (2 * m + 1)
          (g := fun b =>
            poly.scaleP (ground.getAt BPair.unit
              (ground.getAt ([] : poly.Poly) (deckColumn m)
                (tShift m (sShift m b))) i)
              (ground.getAt ([] : poly.Poly) (deckColumn m) (sShift m b)))
          (fun b hbl => by
            rw [tShift_sShift m b hbl]
            exact poly.oneValue_refl _)) ?_
      exact pfold_shift m (sShift m) (tShift m) (tShift_sShift m)
        (fun l _ => sShift_tShift m l) (sShift_lt m) (tShift_lt m)
        (fun b =>
          poly.scaleP (ground.getAt BPair.unit
            (ground.getAt ([] : poly.Poly) (deckColumn m) (tShift m b)) i)
            (ground.getAt ([] : poly.Poly) (deckColumn m) b))
    have hYt : poly.oneValue
        (pfold (fun b =>
          poly.scaleP (ground.getAt BPair.unit
            (ground.getAt ([] : poly.Poly) (deckColumn m) b) i)
            (ground.getAt ([] : poly.Poly) (deckColumn m) (tShift m b)))
          (List.range (2 * m + 1)))
        (pfold (fun b =>
          poly.scaleP (ground.getAt BPair.unit
            (ground.getAt ([] : poly.Poly) (deckColumn m) (tShift m b)) i)
            (ground.getAt ([] : poly.Poly) (deckColumn m) b))
          (List.range (2 * m + 1))) := by
      have hrl : ∀ x, x < 2 * m + 1 → 2 * m - x < 2 * m + 1 :=
        fun x _ => Nat.succ_le_succ (Nat.sub_le (2 * m) x)
      have hrr : ∀ x, x < 2 * m + 1 → 2 * m - (2 * m - x) = x :=
        fun x hx => ground.natSubSubCancel (2 * m) x (Nat.le_of_succ_le_succ hx)
      refine poly.oneValue_trans
        (poly.oneValue_symm
          (pfold_shift m (fun b => 2 * m - b) (fun b => 2 * m - b)
            hrr hrr hrl hrl _)) ?_
      exact pfold_brange (2 * m + 1) (fun b hbl => crossKey m i b hbl)
    refine poly.oneValue_trans
      (poly.add_congr hYs (poly.swapMap_oneValue hYt)) ?_
    exact poly.unitTail_oneValue (poly.add_neg _) trivial
  exact poly.getAt_unitTail (poly.oneValue_unitTail hrow trivial) j

/-- The combination's entry, the landed public's read. -/
private theorem combo_getAt (n : Nat) (cs : List BPair) (M : Mat)
    (b : Nat) (hM : elim.rowsLen n M) (hb : b < n) :
    (ground.getAt BPair.unit (elim.combo n cs M) b).oneValue
      (elim.dotP cs (M.map (fun row => ground.getAt BPair.unit row b))) :=
  elim.combo_getAt n cs M b hM hb

private def tailP : poly.Poly → poly.Poly
  | [] => []
  | _ :: t => t

/-- The triangle's kill: a coefficient list pairing every member of
a keyed family at the sum's unit reads the unit family, the keys
past each diagonal at the unit and the diagonal off it, the descent
one head per step. -/
private theorem triAux : ∀ (cs : List BPair) (F : Nat → poly.Poly),
    (∀ b, b < cs.length →
      (elim.dotP cs (F b)).oneValue BPair.unit) →
    (∀ b, b < cs.length → ∀ i, b < i →
      (ground.getAt BPair.unit (F b) i).oneValue BPair.unit) →
    (∀ b, b < cs.length →
      ¬ (ground.getAt BPair.unit (F b) b).oneValue BPair.unit) →
    poly.unitTail cs
  | [], _, _, _, _ => trivial
  | c :: cs, F, hnull, hup, hdiag => by
    have hpos : 0 < (c :: cs).length := Nat.succ_le_succ (Nat.zero_le _)
    have hc : c.oneValue BPair.unit := by
      cases hF : F 0 with
      | nil =>
        refine absurd ?_ (hdiag 0 hpos)
        rw [hF]
        exact BPair.oneValue_refl _
      | cons v0 vt =>
        have hvt : poly.unitTail vt := by
          refine poly.oneValue_unitTail (q := [])
            (poly.ov_of_getAt (fun k => ?_)) trivial
          have h1 := hup 0 hpos (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
          rw [hF] at h1
          exact h1
        have h0 := hnull 0 hpos
        rw [hF] at h0
        have htail : (elim.dotP cs vt).oneValue BPair.unit := by
          rw [elim.dotP_comm cs vt]
          exact elim.dotP_null_tail_left vt cs hvt
        have hcv : (c * v0).oneValue BPair.unit := by
          refine BPair.oneValue_trans
            (BPair.oneValue_trans
              (BPair.oneValue_symm (BPair.add_unit (c * v0)))
              (BPair.add_congr (BPair.oneValue_refl _)
                (BPair.oneValue_symm htail))) h0
        have hv0 : ¬ v0.oneValue BPair.unit := by
          intro hv
          refine hdiag 0 hpos ?_
          rw [hF]
          exact hv
        refine ground.mul_cancel_unit hv0 ?_
        exact BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.mul_comm v0 c)) hcv
    refine ⟨hc, ?_⟩
    refine triAux cs (fun b => tailP (F (b + 1))) ?_ ?_ ?_
    · intro b hb
      have hb1 : b + 1 < (c :: cs).length := Nat.succ_le_succ hb
      have h1 := hnull (b + 1) hb1
      cases hF : F (b + 1) with
      | nil =>
        cases cs with
        | nil => exact BPair.oneValue_refl _
        | cons _ _ => exact BPair.oneValue_refl _
      | cons v0 vt =>
        rw [hF] at h1
        have hcv : (c * v0).oneValue BPair.unit :=
          BPair.oneValue_trans
            (BPair.mul_congr hc (BPair.oneValue_refl v0))
            (BPair.oneValue_trans
              (BPair.oneValue_of_eq (BPair.mul_comm BPair.unit v0))
              (BPair.mul_unit v0))
        refine BPair.oneValue_trans
          (BPair.oneValue_trans
            (BPair.oneValue_symm (BPair.unit_add (elim.dotP cs vt)))
            (BPair.add_congr (BPair.oneValue_symm hcv)
              (BPair.oneValue_refl _))) h1
    · intro b hb i hbi
      have hb1 : b + 1 < (c :: cs).length := Nat.succ_le_succ hb
      cases hF : F (b + 1) with
      | nil => exact BPair.oneValue_refl _
      | cons v0 vt =>
        have h1 := hup (b + 1) hb1 (i + 1) (Nat.succ_le_succ hbi)
        rw [hF] at h1
        exact h1
    · intro b hb
      have hb1 : b + 1 < (c :: cs).length := Nat.succ_le_succ hb
      have hd := hdiag (b + 1) hb1
      cases hF : F (b + 1) with
      | nil =>
        rw [hF] at hd
        exact absurd (BPair.oneValue_refl _) hd
      | cons v0 vt =>
        intro hu
        rw [hF] at hd
        exact hd hu

/-- A null combination of the coefficient rows reads the unit
family: the triangle at the families' below-top displays, the seed
at two. -/
private theorem sliceTriangle (m : Nat) (cs : List BPair)
    (hlen : cs.length = m)
    (hnull : poly.unitTail (elim.combo (2 * m + 1) cs
      ((List.range m).map (fun i => sliceAt i (deckColumn m))))) :
    poly.unitTail cs := by
  have hm : m ≤ 2 * m + 1 := by
    rw [Nat.two_mul]
    exact Nat.le_succ_of_le (Nat.le_add_left m m)
  have hrows : elim.rowsLen (2 * m + 1)
      ((List.range m).map (fun i => sliceAt i (deckColumn m))) :=
    rowsLen_map _ _ (List.range m) (fun x _ => (fun i => by
      show ((deckColumn m).map _).length = 2 * m + 1
      rw [ground.length_map, deckColumn_len]) x)
  have hub : ∀ b, b < m →
      poly.oneValue (ground.getAt ([] : poly.Poly) (deckColumn m) b)
        (deck.pFamN b) := by
    intro b hbm
    rw [deckColumn_getAt m b (Nat.lt_of_lt_of_le hbm hm)]
    refine deck.redP_short m _ ?_
    rw [deck.pFamN_len b]
    exact hbm
  refine triAux cs (fun b => ground.getAt ([] : poly.Poly)
    (deckColumn m) b) ?_ ?_ ?_
  · intro b hb
    have hbm : b < m := hlen ▸ hb
    have hbL : b < 2 * m + 1 := Nat.lt_of_lt_of_le hbm hm
    have hkey := poly.getAt_unitTail hnull b
    have hcg := combo_getAt (2 * m + 1) cs
      ((List.range m).map (fun i => sliceAt i (deckColumn m))) b
      hrows hbL
    have hcol : poly.oneValue
        (((List.range m).map (fun i => sliceAt i (deckColumn m))).map
          (fun row => ground.getAt BPair.unit row b))
        (ground.getAt ([] : poly.Poly) (deckColumn m) b) := by
      refine poly.ov_of_getAt (fun k => ?_)
      cases Nat.lt_or_ge k m with
      | inl hkm =>
        rw [ground.getAt_map ([] : List BPair) BPair.unit
            (fun row => ground.getAt BPair.unit row b)
            ((List.range m).map (fun i => sliceAt i (deckColumn m))) k
            (by rw [ground.length_mapRange]; exact hkm),
          ground.getAt_map (0 : Nat) ([] : List BPair)
            (fun i => sliceAt i (deckColumn m)) (List.range m) k
            (by rw [ground.length_range]; exact hkm),
          ground.getAt_range m k hkm]
        show (ground.getAt BPair.unit
          ((deckColumn m).map (fun p => ground.getAt BPair.unit p k))
          b).oneValue
          (ground.getAt BPair.unit
            (ground.getAt ([] : poly.Poly) (deckColumn m) b) k)
        rw [ground.getAt_map ([] : poly.Poly) BPair.unit
          (fun p => ground.getAt BPair.unit p k) (deckColumn m) b
          (by rw [deckColumn_len]; exact hbL)]
        exact BPair.oneValue_refl _
      | inr hge =>
        have hlm : (((List.range m).map
            (fun i => sliceAt i (deckColumn m))).map
            (fun row => ground.getAt BPair.unit row b)).length ≤ k := by
          rw [ground.length_map, ground.length_mapRange]
          exact hge
        have hub2 : (ground.getAt ([] : poly.Poly)
            (deckColumn m) b).length ≤ k := by
          rw [deckColumn_entry_len m b hbL]
          exact hge
        rw [ground.getAt_over BPair.unit _ _ hlm,
          ground.getAt_over BPair.unit _ _ hub2]
        exact BPair.oneValue_refl _
    have hl2 : (((List.range m).map
        (fun i => sliceAt i (deckColumn m))).map
        (fun row => ground.getAt BPair.unit row b)).length
        = (ground.getAt ([] : poly.Poly) (deckColumn m) b).length := by
      rw [ground.length_map, ground.length_mapRange,
        deckColumn_entry_len m b hbL]
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (elim.dotP_oneValue_right cs _ _ hcol))
      (BPair.oneValue_trans (BPair.oneValue_symm hcg) hkey)
  · intro b hb i hbi
    have hbm : b < m := hlen ▸ hb
    refine BPair.oneValue_trans (poly.oneValue_getAt i (hub b hbm)) ?_
    rw [ground.getAt_over BPair.unit _ _ (by
        rw [deck.pFamN_len b]
        exact hbi)]
    exact BPair.oneValue_refl _
  · intro b hb hu
    have hbm : b < m := hlen ▸ hb
    have hd : (ground.getAt BPair.unit (deck.pFamN b) b).oneValue
        BPair.unit :=
      BPair.oneValue_trans
        (BPair.oneValue_symm (poly.oneValue_getAt b (hub b hbm))) hu
    cases b with
    | zero => exact absurd hd (by decide +kernel)
    | succ b' =>
      exact absurd
        (BPair.oneValue_trans
          (BPair.oneValue_symm (deck.pFamN_top b')) hd)
        (by decide +kernel)

/-- The iterate splits at a summed count, the walk's own
composition. -/
private theorem iterAt_add (t : Nat → Nat) (a : Nat) : ∀ (b l : Nat),
    iterAt t (a + b) l = iterAt t a (iterAt t b l)
  | 0, _ => rfl
  | b + 1, l => iterAt_add t a b (t l)

/-- The walk below the top adds its step count. -/
private theorem walkRun (m : Nat) : ∀ (j l : Nat), l + j ≤ 2 * m →
    iterAt (tShift m) j l = l + j
  | 0, _, _ => rfl
  | j + 1, l, h => by
    show iterAt (tShift m) j (tShift m l) = l + (j + 1)
    have hl : ¬ (l = 2 * m) := by
      intro he
      subst he
      exact Nat.lt_irrefl (2 * m)
        (Nat.lt_of_lt_of_le
          (Nat.lt_succ_of_le (Nat.le_add_right (2 * m) j)) h)
    rw [tShift_ne m l hl, walkRun m j (l + 1) (by
      rw [Nat.add_right_comm l 1 j]
      exact h), Nat.add_right_comm l 1 j]
    rfl

/-- The wrap shift closes its one cycle at the side. -/
private theorem tShift_cyc (m : Nat) : ∀ l, l < 2 * m + 1 →
    iterAt (tShift m) (2 * m + 1) l = l := by
  intro l hl
  have hl2m : l ≤ 2 * m := Nat.le_of_succ_le_succ hl
  have hsplit : 2 * m + 1 = l + (1 + (2 * m - l)) := by
    rw [← Nat.add_assoc l 1 (2 * m - l), Nat.add_comm l 1,
      Nat.add_assoc 1 l (2 * m - l),
      ground.natAddSubCancel hl2m, Nat.add_comm 1 (2 * m)]
  rw [hsplit, iterAt_add (tShift m) l (1 + (2 * m - l)) l,
    iterAt_add (tShift m) 1 (2 * m - l) l,
    walkRun m (2 * m - l) l
      (Nat.le_of_eq (ground.natAddSubCancel hl2m))]
  rw [ground.natAddSubCancel hl2m]
  show iterAt (tShift m) l (tShift m (2 * m)) = l
  rw [tShift_top m,
    walkRun m l 0 (by rw [Nat.zero_add]; exact hl2m),
    Nat.zero_add l]

/-- The entrywise vector sum at one count is the componentwise
sum. -/
private theorem vecAdd_eq_polyAdd : ∀ (u v : List BPair),
    u.length = v.length → elim.vecAdd u v = poly.add u v
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | _ :: u, _ :: v, h => by
    show (_ + _) :: elim.vecAdd u v = (_ + _) :: poly.add u v
    rw [vecAdd_eq_polyAdd u v (Nat.succ.inj h)]

/-- A member-row combination pairs the orbit sum at the sum's
unit. -/
private theorem comboPerp_ones (m : Nat) (cs : List BPair) :
    (elim.dotP (orbitSum m) (elim.combo (2 * m + 1) cs
      ((List.range m).map (fun i => sliceAt i (deckColumn m))))).oneValue
      BPair.unit := by
  have hrows : elim.rowsLen (2 * m + 1)
      ((List.range m).map (fun i => sliceAt i (deckColumn m))) :=
    rowsLen_map _ _ (List.range m) (fun x _ => (fun i => by
      show ((deckColumn m).map _).length = 2 * m + 1
      rw [ground.length_map, deckColumn_len]) x)
  refine BPair.oneValue_trans
    (elim.dotP_combo cs _ (orbitSum m) (2 * m + 1) hrows) ?_
  have hmap : poly.unitTail
      (((List.range m).map (fun i => sliceAt i (deckColumn m))).map
        (fun row => elim.dotP (orbitSum m) row)) := by
    rw [ground.map_map (fun i => sliceAt i (deckColumn m))
      (fun row => elim.dotP (orbitSum m) row) (List.range m)]
    exact poly.unitTail_map _ (List.range m)
      (fun i _ => memberPerp m i)
  rw [elim.dotP_comm]
  exact elim.dotP_null_tail_left _ cs hmap

/-- An image-row combination's kernel read reads its coefficients
at the unit: the two translation images agree, the doubled iterate
fixes the combination and the member reads the translation through
the wrap, `T w = T^(2m+2) w = (T²)^(m+1) w = w` at `T^L = 1`, so
the member sits in the unit fiber, joins the sum's span while
pairing it at the unit, and the positive pairing withdraws it to
the triangle. -/
private theorem imageKill (m : Nat) (cs : List BPair)
    (hlen : cs.length = m)
    (hker : poly.unitTail (matVec
      (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (elim.combo (2 * m + 1) cs
        ((List.range m).map (fun i => sliceAt i (deckColumn m)))))) :
    poly.unitTail cs := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hTl : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hTr : rowsLen (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) :=
    rowsLen_permMatAt _ _
  have hTtr : rowsLen (2 * m + 1)
      (transposeM (permMatAt (2 * m + 1) (tShift m))) :=
    rowsLen_cast hTl (rowsLen_transposeM _)
  have hTtl : (transposeM (permMatAt (2 * m + 1) (tShift m))).length
      = 2 * m + 1 :=
    transposeLen _ hTr hTl
  have hrows : elim.rowsLen (2 * m + 1)
      ((List.range m).map (fun i => sliceAt i (deckColumn m))) :=
    rowsLen_map _ _ (List.range m) (fun x _ => (fun i => by
      show ((deckColumn m).map _).length = 2 * m + 1
      rw [ground.length_map, deckColumn_len]) x)
  have hwl : (elim.combo (2 * m + 1) cs
      ((List.range m).map (fun i => sliceAt i (deckColumn m)))).length
      = 2 * m + 1 :=
    elim.length_combo _ cs _ hrows
  let w := elim.combo (2 * m + 1) cs
    ((List.range m).map (fun i => sliceAt i (deckColumn m)))
  have h1 : poly.oneValue
      (matVec (permMatAt (2 * m + 1) (tShift m)) w)
      (matVec (transposeM (permMatAt (2 * m + 1) (tShift m))) w) := by
    refine siteKer_read _ _ w (hwl ▸ hTr) (hwl ▸ hTtr) ?_ hker
    show ((permMatAt (2 * m + 1) (tShift m)).map _).length
      = ((transposeM (permMatAt (2 * m + 1) (tShift m))).map _).length
    rw [ground.length_map, ground.length_map, hTl, hTtl]
  have h2 : poly.oneValue
      (matVec (permMatAt (2 * m + 1) (tShift m))
        (matVec (permMatAt (2 * m + 1) (tShift m)) w)) w := by
    refine poly.oneValue_trans (elim.matVec_congr _ _ _ h1) ?_
    refine poly.oneValue_trans
      (poly.oneValue_symm
        (elim.matVec_matMul _ _ (2 * m + 1) hTtr w hwl)) ?_
    refine poly.oneValue_trans
      (elim.matVec_matOne _ _ w (orth_wrap m).1) ?_
    exact split.matVec_idMat (2 * m + 1) w hwl
  have h3 : ∀ k : Nat, poly.oneValue
      (matVec (matPow (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1)
        (2 * k)) w) w := by
    intro k
    induction k with
    | zero => exact split.matVec_idMat (2 * m + 1) w hwl
    | succ k ih =>
      have hsm := matPow_shape (2 * m + 1) _ hTl (2 * k)
      have hsm1 := matPow_shape (2 * m + 1) _ hTl (2 * k + 1)
      show poly.oneValue
        (matVec (matMul (permMatAt (2 * m + 1) (tShift m))
          (matMul (permMatAt (2 * m + 1) (tShift m))
            (matPow (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1)
              (2 * k)))) w) w
      refine poly.oneValue_trans
        (elim.matVec_matMul _ _ (2 * m + 1)
          (rowsLen_cast (transposeLen _ hsm.1 hsm.2)
            (rowsLen_matMul _ _)) w hwl) ?_
      refine poly.oneValue_trans
        (elim.matVec_congr _ _ _
          (elim.matVec_matMul _ _ (2 * m + 1) hsm.1 w hwl)) ?_
      refine poly.oneValue_trans
        (elim.matVec_congr _ _ _ (elim.matVec_congr _ _ _ ih)) ?_
      exact h2
  have h4 : poly.oneValue
      (matVec (permMatAt (2 * m + 1) (tShift m)) w) w := by
    have hcyc := matPow_wrap (2 * m + 1) (2 * m) (tShift m) hn
      (tShift_lt m) (tShift_cyc m) 0
    have hTP : matOneValue
        (matPow (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1)
          (2 * (m + 1)))
        (permMatAt (2 * m + 1) (tShift m)) := by
      show matOneValue
        (matMul (permMatAt (2 * m + 1) (tShift m))
          (matPow (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1)
            (2 * m + 1)))
        (permMatAt (2 * m + 1) (tShift m))
      refine matOne_trans
        (matMul_congrR (n := 2 * m + 1) (k := 2 * m + 1) _ _ _
          (matPow_shape (2 * m + 1) _ hTl (2 * m + 1)).1
          (inertia.idMat_rows _)
          (matPow_shape (2 * m + 1) _ hTl (2 * m + 1)).2
          (inertia.idMat_len _) hn hcyc) ?_
      exact inertia.matMul_idR (2 * m + 1) _ hTr hTl hn hn
    refine poly.oneValue_trans
      (poly.oneValue_symm (matVec_congrM _ _ w hTP)) ?_
    exact h3 (m + 1)
  have hker2 : poly.unitTail
      (matVec (unitDatum (permMatAt (2 * m + 1) (tShift m))
        (2 * m + 1)) w) := by
    have hSw : poly.oneValue
        (matVec (chordOp (permMatAt (2 * m + 1) (tShift m))) w)
        (vecAdd w w) := by
      refine poly.oneValue_trans
        (elim.matVec_add _ _ w (hwl ▸ hTr) (hwl ▸ hTtr)) ?_
      exact polyOne_vecAdd _ _ _ _ h4
        (poly.oneValue_trans (poly.oneValue_symm h1) h4)
        ((matVec_length _ _).trans (hTl.trans hwl.symm))
        ((matVec_length _ _).trans (hTtl.trans hwl.symm))
    have hscl : poly.oneValue
        (matVec (inertia.matScaleB (BPair.ofNat 2)
          (inertia.idMat (2 * m + 1))) w)
        (vecAdd w w) :=
      poly.oneValue_trans
        (matVec_scaleId (BPair.ofNat 2) (2 * m + 1) w hwl)
        (vecScale_two w)
    have hscr : rowsLen (2 * m + 1)
        (inertia.matScaleB (BPair.ofNat 2)
          (inertia.idMat (2 * m + 1))) :=
      inertia.rowsLen_scaleB _ _ _ (inertia.idMat_rows _)
    have hsw : rowsLen (2 * m + 1)
        (matSwap (inertia.matScaleB (BPair.ofNat 2)
          (inertia.idMat (2 * m + 1)))) :=
      rowsLen_mapRows _ _ _ hscr
    have hS : rowsLen (2 * m + 1)
        (chordOp (permMatAt (2 * m + 1) (tShift m))) :=
      (chordWrap_shape m).1
    show poly.unitTail (matVec
      (matAdd (chordOp (permMatAt (2 * m + 1) (tShift m)))
        (matSwap (inertia.matScaleB (BPair.ofNat 2)
          (inertia.idMat (2 * m + 1))))) w)
    refine poly.oneValue_unitTail
      (elim.matVec_add _ _ w (hwl ▸ hS) (hwl ▸ hsw)) ?_
    rw [matVec_swapM]
    have hvl : (matVec (chordOp (permMatAt (2 * m + 1) (tShift m)))
        w).length = 2 * m + 1 :=
      (matVec_length _ _).trans (chordWrap_shape m).2
    have hvl2 : (matVec (inertia.matScaleB (BPair.ofNat 2)
        (inertia.idMat (2 * m + 1))) w).length = 2 * m + 1 :=
      (matVec_length _ _).trans
        ((inertia.length_scaleB _ _).trans (inertia.idMat_len _))
    have hswl2 : ((matVec (inertia.matScaleB (BPair.ofNat 2)
        (inertia.idMat (2 * m + 1))) w).map BPair.swap).length
        = 2 * m + 1 := by
      rw [ground.length_map]
      exact hvl2
    rw [vecAdd_eq_polyAdd _ _ (hvl.trans hswl2.symm)]
    refine poly.oneValue_unitTail
      (poly.add_congr hSw (poly.swapMap_oneValue hscl)) ?_
    have hval : ((vecAdd w w).map BPair.swap).length
        = (vecAdd w w).length := ground.length_map _ _
    rw [show (vecAdd w w).map BPair.swap = poly.neg (vecAdd w w)
      from rfl]
    exact poly.add_neg (vecAdd w w)
  have hspan := unitFiber_span m w hwl hker2
  have hperp : (elim.dotP w (orbitSum m)).oneValue BPair.unit := by
    rw [elim.dotP_comm w (orbitSum m)]
    exact comboPerp_ones m cs
  have hself : (elim.dotP w w).oneValue BPair.unit := by
    refine elim.perp_span (2 * m + 1) [orbitSum m] w w
      ⟨orbitSum_len m, trivial⟩ hwl (fun k hk => ?_) hspan
    cases k with
    | zero => exact hperp
    | succ k' =>
      exact absurd (Nat.lt_of_succ_lt_succ hk) (Nat.not_lt_zero k')
  exact sliceTriangle m cs hlen (elim.dotP_self_null w hself)

/-- The action splits at an entrywise vector sum. -/
private theorem matVec_vAdd (n : Nat) : ∀ (M : Mat) (u v : List BPair),
    elim.rowsLen n M → u.length = n → v.length = n →
    poly.oneValue (matVec M (elim.vecAdd u v))
      (elim.vecAdd (matVec M u) (matVec M v))
  | [], _, _, _, _, _ => trivial
  | r :: t, u, v, hM, hu, hv =>
    ⟨BPair.oneValue_trans (elim.dotN_dotP r (elim.vecAdd u v))
      (BPair.oneValue_trans
        (elim.dotP_vecAdd r u v (hu.trans hM.1.symm)
          (hv.trans hM.1.symm))
        (BPair.add_congr
          (BPair.oneValue_symm (elim.dotN_dotP r u))
          (BPair.oneValue_symm (elim.dotN_dotP r v)))),
     matVec_vAdd n t u v hM.2 hu hv⟩

/-- The orbit sum's self-pairing reads the side's own count. -/
private theorem ones_selfDot : ∀ k : Nat,
    (elim.dotP (List.replicate k (BPair.ofPos Pos.one))
      (List.replicate k (BPair.ofPos Pos.one))).oneValue
      (BPair.ofNat k)
  | 0 => by decide +kernel
  | k + 1 => by
    show (BPair.ofPos Pos.one * BPair.ofPos Pos.one
      + elim.dotP (List.replicate k (BPair.ofPos Pos.one))
          (List.replicate k (BPair.ofPos Pos.one))).oneValue
      (BPair.ofNat (k + 1))
    refine BPair.oneValue_trans
      (BPair.add_congr
        (show (BPair.ofPos Pos.one * BPair.ofPos Pos.one).oneValue
          (BPair.ofNat 1) by decide +kernel)
        (ones_selfDot k)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofNat_add 1 k)) ?_
    rw [Nat.add_comm 1 k]
    exact BPair.oneValue_refl _

/-- One is off the doubled counts. -/
private theorem one_ne_double : ∀ k : Nat, ¬ ((1 : Nat) = 2 * k)
  | 0 => fun h => Nat.noConfusion h
  | _ + 1 => fun h => Nat.noConfusion (Nat.succ.inj h)

/-- The alternation's first components. -/
private def altE : List BPair → List BPair
  | [] => []
  | [c] => [c]
  | c :: _ :: t => c :: altE t

/-- The alternation's second components. -/
private def altO : List BPair → List BPair
  | [] => []
  | [_] => []
  | _ :: d :: t => d :: altO t

/-- The two alternations at the unit family read the family
whole. -/
private theorem altEO_unit : ∀ cs : List BPair,
    poly.unitTail (altE cs) → poly.unitTail (altO cs) →
    poly.unitTail cs
  | [], _, _ => trivial
  | [_], he, _ => ⟨he.1, trivial⟩
  | _ :: _ :: t, he, ho =>
    ⟨he.1, ho.1, altEO_unit t he.2 ho.2⟩

/-- The first alternation halves a doubled count. -/
private theorem altE_len : ∀ (cs : List BPair) (k : Nat),
    cs.length = 2 * k → (altE cs).length = k
  | [], 0, _ => rfl
  | [], k + 1, h => Nat.noConfusion h
  | [_], k, h => absurd h (one_ne_double k)
  | _ :: _ :: t, 0, h => Nat.noConfusion h
  | _ :: _ :: t, k + 1, h => by
    show (altE t).length + 1 = k + 1
    refine congrArg Nat.succ (altE_len t k ?_)
    exact Nat.succ.inj (Nat.succ.inj
      (show t.length + 2 = 2 * k + 2 from h))

/-- The second alternation halves a doubled count. -/
private theorem altO_len : ∀ (cs : List BPair) (k : Nat),
    cs.length = 2 * k → (altO cs).length = k
  | [], 0, _ => rfl
  | [], k + 1, h => Nat.noConfusion h
  | [_], k, h => absurd h (one_ne_double k)
  | _ :: _ :: t, 0, h => Nat.noConfusion h
  | _ :: _ :: t, k + 1, h => by
    show (altO t).length + 1 = k + 1
    refine congrArg Nat.succ (altO_len t k ?_)
    exact Nat.succ.inj (Nat.succ.inj
      (show t.length + 2 = 2 * k + 2 from h))

/-- The paired join's rows carry one count. -/
private theorem rowsLen_flatPair (f g : Nat → List BPair) {n : Nat}
    (hf : ∀ a, (f a).length = n) (hg : ∀ a, (g a).length = n) :
    ∀ l : List Nat, elim.rowsLen n (l.flatMap (fun i => [f i, g i]))
  | [] => trivial
  | a :: t => ⟨hf a, hg a, rowsLen_flatPair f g hf hg t⟩

/-- A combination over the paired join splits at the two
alternations. -/
private theorem combo_pairSplit (n : Nat) (f g : Nat → List BPair)
    (hf : ∀ a, (f a).length = n) (hg : ∀ a, (g a).length = n) :
    ∀ (l : List Nat) (cs : List BPair), cs.length = 2 * l.length →
    poly.oneValue
      (elim.combo n cs (l.flatMap (fun i => [f i, g i])))
      (elim.vecAdd (elim.combo n (altE cs) (l.map f))
        (elim.combo n (altO cs) (l.map g)))
  | [], cs, h => by
    have hnil : cs = [] := by
      cases cs with
      | nil => rfl
      | cons c t => exact Nat.noConfusion h
    subst hnil
    show poly.oneValue (List.replicate n BPair.unit)
      (elim.vecAdd (List.replicate n BPair.unit)
        (List.replicate n BPair.unit))
    rw [vecAdd_eq_polyAdd _ _ rfl]
    exact poly.unitTail_oneValue (poly.unitTail_replicate n)
      (poly.oneValue_unitTail
        (poly.unitTail_add (poly.unitTail_replicate n) _)
        (poly.unitTail_replicate n))
  | a :: l, cs, h => by
    cases cs with
    | nil => exact Nat.noConfusion h
    | cons c cs' =>
      cases cs' with
      | nil => exact absurd h (one_ne_double _)
      | cons d t =>
        have hlen : t.length = 2 * l.length :=
          Nat.succ.inj (Nat.succ.inj
            (show t.length + 2 = 2 * l.length + 2 from h))
        have hfr : elim.rowsLen n (l.flatMap (fun i => [f i, g i])) :=
          rowsLen_flatPair f g hf hg l
        have hcl : (elim.combo n t
            (l.flatMap (fun i => [f i, g i]))).length = n :=
          elim.length_combo n t _ hfr
        have hel : (elim.combo n (altE t) (l.map f)).length = n :=
          elim.length_combo n _ _ (rowsLen_map f n l (fun x _ => hf x))
        have hol : (elim.combo n (altO t) (l.map g)).length = n :=
          elim.length_combo n _ _ (rowsLen_map g n l (fun x _ => hg x))
        have hscl : (elim.vecScale c (f a)).length = n :=
          (elim.length_vecScale c _).trans (hf a)
        have hsdl : (elim.vecScale d (g a)).length = n :=
          (elim.length_vecScale d _).trans (hg a)
        have hEO : (elim.vecAdd (elim.combo n (altE t) (l.map f))
            (elim.combo n (altO t) (l.map g))).length = n :=
          elim.length_vecAdd _ _ n hel hol
        have ih : poly.oneValue
            (elim.combo n t (l.flatMap (fun i => [f i, g i])))
            (poly.add (elim.combo n (altE t) (l.map f))
              (elim.combo n (altO t) (l.map g))) := by
          refine poly.oneValue_trans (combo_pairSplit n f g hf hg l t hlen) ?_
          rw [vecAdd_eq_polyAdd _ _ (hel.trans hol.symm)]
          exact poly.oneValue_refl _
        show poly.oneValue
          (elim.vecAdd (elim.vecScale c (f a))
            (elim.vecAdd (elim.vecScale d (g a))
              (elim.combo n t (l.flatMap (fun i => [f i, g i])))))
          (elim.vecAdd
            (elim.vecAdd (elim.vecScale c (f a))
              (elim.combo n (altE t) (l.map f)))
            (elim.vecAdd (elim.vecScale d (g a))
              (elim.combo n (altO t) (l.map g))))
        rw [vecAdd_eq_polyAdd (elim.vecScale d (g a)) _
            (hsdl.trans hcl.symm),
          vecAdd_eq_polyAdd (elim.vecScale c (f a)) _
            (hscl.trans (((poly.add_lenL _ _ (Nat.le_of_eq (hcl.trans hsdl.symm))).trans hsdl).symm)),
          vecAdd_eq_polyAdd (elim.vecScale c (f a))
            (elim.combo n (altE t) (l.map f)) (hscl.trans hel.symm),
          vecAdd_eq_polyAdd (elim.vecScale d (g a))
            (elim.combo n (altO t) (l.map g)) (hsdl.trans hol.symm),
          vecAdd_eq_polyAdd _ _
            (((poly.add_lenL _ _ (Nat.le_of_eq (hel.trans hscl.symm))).trans hscl).trans ((poly.add_lenL _ _ (Nat.le_of_eq (hol.trans hsdl.symm))).trans hsdl).symm)]
        refine poly.oneValue_trans
          (poly.add_congr (poly.oneValue_refl _)
            (poly.add_congr (poly.oneValue_refl _) ih)) ?_
        refine poly.oneValue_trans
          (poly.add_congr (poly.oneValue_refl _)
            (poly.oneValue_trans
              (poly.add_join (elim.vecScale d (g a))
                (elim.combo n (altE t) (l.map f))
                (elim.combo n (altO t) (l.map g)))
              (poly.oneValue_trans
                (poly.add_congr
                  (poly.add_comm (elim.vecScale d (g a))
                    (elim.combo n (altE t) (l.map f)))
                  (poly.oneValue_refl _))
                (poly.oneValue_symm
                  (poly.add_join (elim.combo n (altE t) (l.map f))
                    (elim.vecScale d (g a))
                    (elim.combo n (altO t) (l.map g))))))) ?_
        exact poly.add_join (elim.vecScale c (f a))
          (elim.combo n (altE t) (l.map f))
          (poly.add (elim.vecScale d (g a))
            (elim.combo n (altO t) (l.map g)))

/-- A paired family's mapped reads at the unit collect whole. -/
private theorem mapPairUnit (f g : Nat → List BPair)
    (h : List BPair → BPair)
    (hp : ∀ i, (h (f i)).oneValue BPair.unit)
    (hq : ∀ i, (h (g i)).oneValue BPair.unit) :
    ∀ l : List Nat,
    poly.unitTail ((l.flatMap (fun i => [f i, g i])).map h)
  | [] => trivial
  | a :: t => ⟨hp a, hq a, mapPairUnit f g h hp hq t⟩

/-- The splitting's joined list is independent at the orbit's own
count: the sum's coefficient dies at the side, the two alternations
at the triangle and the fixed-member read. -/
theorem orbitSplit_indep (m : Nat) :
    elim.indepRows (2 * m + 1) ([orbitSum m] ++ pairBase m) := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hTl : (permMatAt (2 * m + 1) (tShift m)).length = 2 * m + 1 :=
    length_permMatAt _ _
  have hTr : rowsLen (2 * m + 1) (permMatAt (2 * m + 1) (tShift m)) :=
    rowsLen_permMatAt _ _
  have hAl : (bandDatum (permMatAt (2 * m + 1) (tShift m))).length
      = 2 * m + 1 := by
    show (matAdd _ (matSwap (transposeM _))).length = 2 * m + 1
    refine (length_matAdd _ _ ?_).trans hTl
    rw [hTl]
    show 2 * m + 1
      = ((transposeM (permMatAt (2 * m + 1) (tShift m))).map
        (fun r => r.map BPair.swap)).length
    rw [ground.length_map]
    exact (transposeLen _ hTr hTl).symm
  have hAr : rowsLen (2 * m + 1)
      (bandDatum (permMatAt (2 * m + 1) (tShift m))) :=
    rowsLen_matAdd _ _ _ hTr
      (rowsLen_mapRows BPair.swap _ _
        (rowsLen_cast hTl (rowsLen_transposeM _)))
  have hslice : ∀ i, (sliceAt i (deckColumn m)).length = 2 * m + 1 :=
    fun i => by
      show ((deckColumn m).map _).length = 2 * m + 1
      rw [ground.length_map, deckColumn_len]
  have himg : ∀ i, (matVec
      (bandDatum (permMatAt (2 * m + 1) (tShift m)))
      (sliceAt i (deckColumn m))).length = 2 * m + 1 :=
    fun i => (matVec_length _ _).trans hAl
  have hurows : elim.rowsLen (2 * m + 1)
      ((List.range m).map (fun i => sliceAt i (deckColumn m))) :=
    rowsLen_map _ _ (List.range m) (fun x _ => hslice x)
  have hrows : elim.rowsLen (2 * m + 1) ([orbitSum m] ++ pairBase m) :=
    ⟨orbitSum_len m, rowsLen_flatPair _ _ hslice himg (List.range m)⟩
  refine elim.indep_intro (2 * m + 1) _ hrows ?_
  intro cs hcslen hcombo
  cases cs with
  | nil => exact trivial
  | cons c0 rest =>
    have hrl : rest.length = 2 * m := by
      refine Nat.succ.inj (show rest.length + 1 = 2 * m + 1 from ?_)
      refine (show (c0 :: rest).length
        = ([orbitSum m] ++ pairBase m).length from hcslen).trans ?_
      show ((orbitSum m :: pairBase m) : Mat).length = 2 * m + 1
      show (pairBase m).length + 1 = 2 * m + 1
      rw [pairBase_len m]
    have hrl' : rest.length = 2 * (List.range m).length := by
      rw [ground.length_range]
      exact hrl
    have hWl : (elim.combo (2 * m + 1) rest (pairBase m)).length
        = 2 * m + 1 :=
      elim.length_combo _ _ _
        (rowsLen_flatPair _ _ hslice himg (List.range m))
    -- the sum's coefficient dies
    have hdot0 : (elim.dotP (orbitSum m)
        (elim.combo (2 * m + 1) (c0 :: rest)
          ([orbitSum m] ++ pairBase m))).oneValue BPair.unit := by
      rw [elim.dotP_comm]
      exact elim.dotP_null_tail_left _ _ hcombo
    have hexp := elim.dotP_combo (c0 :: rest)
      ([orbitSum m] ++ pairBase m) (orbitSum m) (2 * m + 1) hrows
    have hmapt : poly.unitTail ((pairBase m).map
        (fun row => elim.dotP (orbitSum m) row)) :=
      mapPairUnit _ _ _ (fun i => memberPerp m i)
        (fun i => imagePerp m i) (List.range m)
    have htail : (elim.dotP rest ((pairBase m).map
        (fun row => elim.dotP (orbitSum m) row))).oneValue
        BPair.unit := by
      rw [elim.dotP_comm]
      exact elim.dotP_null_tail_left _ rest hmapt
    have hc0L : (c0 * BPair.ofNat (2 * m + 1)).oneValue BPair.unit := by
      refine BPair.oneValue_trans
        (BPair.oneValue_trans
          (BPair.oneValue_symm (BPair.add_unit _))
          (BPair.add_congr
            (BPair.mul_congr (BPair.oneValue_refl c0)
              (BPair.oneValue_symm (ones_selfDot (2 * m + 1))))
            (BPair.oneValue_symm htail))) ?_
      exact BPair.oneValue_trans (BPair.oneValue_symm hexp) hdot0
    have hc0 : c0.oneValue BPair.unit := by
      refine ground.mul_cancel_unit
        (BPair.ofNat_off_unit (2 * m + 1)
          (Nat.succ_le_succ (Nat.zero_le _))) ?_
      exact BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofNat (2 * m + 1))
          c0)) hc0L
    -- the tail's combination dies with it
    have hsc : poly.unitTail (elim.vecScale c0 (orbitSum m)) :=
      poly.unitTail_map (fun x => c0 * x) (orbitSum m)
        (fun x _ => BPair.oneValue_trans
          (BPair.mul_congr hc0 (BPair.oneValue_refl x))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.mul_comm BPair.unit x))
            (BPair.mul_unit x)))
    have hW : poly.unitTail
        (elim.combo (2 * m + 1) rest (pairBase m)) := by
      have hcombo2 : poly.unitTail
          (poly.add (elim.vecScale c0 (orbitSum m))
            (elim.combo (2 * m + 1) rest (pairBase m))) := by
        rw [← vecAdd_eq_polyAdd _ _
          (((elim.length_vecScale c0 _).trans (orbitSum_len m)).trans
            hWl.symm)]
        exact hcombo
      exact poly.unitTail_oneValue_right hcombo2
        (poly.unitTail_add hsc _)
    -- the split at the alternations
    have hsplit := combo_pairSplit (2 * m + 1) _ _ hslice himg
      (List.range m) rest hrl'
    have hUl : (elim.combo (2 * m + 1) (altE rest)
        ((List.range m).map (fun i => sliceAt i (deckColumn m)))).length
        = 2 * m + 1 :=
      elim.length_combo _ _ _ hurows
    have hVl : (elim.combo (2 * m + 1) (altO rest)
        ((List.range m).map (fun i => matVec
          (bandDatum (permMatAt (2 * m + 1) (tShift m)))
          (sliceAt i (deckColumn m))))).length = 2 * m + 1 :=
      elim.length_combo _ _ _ (rowsLen_map _ _ (List.range m) (fun x _ => himg x))
    have hUV : poly.unitTail (elim.vecAdd
        (elim.combo (2 * m + 1) (altE rest)
          ((List.range m).map (fun i => sliceAt i (deckColumn m))))
        (elim.combo (2 * m + 1) (altO rest)
          ((List.range m).map (fun i => matVec
            (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (sliceAt i (deckColumn m)))))) :=
      poly.unitTail_oneValue_right hW hsplit
    -- the two parts are perpendicular
    have hperpUV : (elim.dotP
        (elim.combo (2 * m + 1) (altE rest)
          ((List.range m).map (fun i => sliceAt i (deckColumn m))))
        (elim.combo (2 * m + 1) (altO rest)
          ((List.range m).map (fun i => matVec
            (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (sliceAt i (deckColumn m)))))).oneValue BPair.unit := by
      refine BPair.oneValue_trans
        (elim.dotP_combo (altO rest) _ _ (2 * m + 1)
          (rowsLen_map _ _ (List.range m) (fun x _ => himg x))) ?_
      have hentries : poly.unitTail
          (((List.range m).map (fun i => matVec
            (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (sliceAt i (deckColumn m)))).map
            (fun row => elim.dotP
              (elim.combo (2 * m + 1) (altE rest)
                ((List.range m).map
                  (fun i => sliceAt i (deckColumn m)))) row)) := by
        rw [ground.map_map]
        refine poly.unitTail_map _ (List.range m) (fun j _ => ?_)
        rw [elim.dotP_comm]
        refine BPair.oneValue_trans
          (elim.dotP_combo (altE rest) _ _ (2 * m + 1)
            hurows) ?_
        have hentries2 : poly.unitTail
            (((List.range m).map
              (fun i => sliceAt i (deckColumn m))).map
              (fun row => elim.dotP (matVec
                (bandDatum (permMatAt (2 * m + 1) (tShift m)))
                (sliceAt j (deckColumn m))) row)) := by
          rw [ground.map_map]
          refine poly.unitTail_map _ (List.range m) (fun i _ => ?_)
          rw [elim.dotP_comm]
          exact sliceCross_null m i j
        rw [elim.dotP_comm]
        exact elim.dotP_null_tail_left _ (altE rest) hentries2
      rw [elim.dotP_comm]
      exact elim.dotP_null_tail_left _ (altO rest) hentries
    -- the member part dies at the triangle
    have hself : (elim.dotP
        (elim.combo (2 * m + 1) (altE rest)
          ((List.range m).map (fun i => sliceAt i (deckColumn m))))
        (elim.combo (2 * m + 1) (altE rest)
          ((List.range m).map
            (fun i => sliceAt i (deckColumn m))))).oneValue
        BPair.unit := by
      refine BPair.oneValue_trans
        (BPair.oneValue_trans
          (BPair.oneValue_symm (BPair.add_unit _))
          (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.oneValue_symm hperpUV))) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_symm (elim.dotP_vecAdd _ _ _
          rfl (hVl.trans hUl.symm))) ?_
      rw [elim.dotP_comm]
      exact elim.dotP_null_tail_left _ _ hUV
    have hU : poly.unitTail
        (elim.combo (2 * m + 1) (altE rest)
          ((List.range m).map (fun i => sliceAt i (deckColumn m)))) :=
      elim.dotP_self_null _ hself
    have hE := sliceTriangle m (altE rest) (altE_len rest m hrl) hU
    -- the image part dies at the fixed-member read
    have hV : poly.unitTail
        (elim.combo (2 * m + 1) (altO rest)
          ((List.range m).map (fun i => matVec
            (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (sliceAt i (deckColumn m))))) := by
      have h1 : poly.oneValue
          (elim.vecAdd
            (elim.combo (2 * m + 1) (altE rest)
              ((List.range m).map (fun i => sliceAt i (deckColumn m))))
            (elim.combo (2 * m + 1) (altO rest)
              ((List.range m).map (fun i => matVec
                (bandDatum (permMatAt (2 * m + 1) (tShift m)))
                (sliceAt i (deckColumn m))))))
          (elim.combo (2 * m + 1) (altO rest)
            ((List.range m).map (fun i => matVec
              (bandDatum (permMatAt (2 * m + 1) (tShift m)))
              (sliceAt i (deckColumn m))))) := by
        rw [vecAdd_eq_polyAdd _ _ (hUl.trans hVl.symm)]
        exact poly.unitTail_add hU _
      exact poly.unitTail_oneValue_right hUV h1
    have hAV : poly.unitTail (matVec
        (bandDatum (permMatAt (2 * m + 1) (tShift m)))
        (elim.combo (2 * m + 1) (altO rest)
          ((List.range m).map (fun i => sliceAt i (deckColumn m))))) := by
      have h2 : poly.oneValue
          (elim.combo (2 * m + 1) (altO rest)
            ((List.range m).map (fun i => matVec
              (bandDatum (permMatAt (2 * m + 1) (tShift m)))
              (sliceAt i (deckColumn m)))))
          (matVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (elim.combo (2 * m + 1) (altO rest)
              ((List.range m).map
                (fun i => sliceAt i (deckColumn m))))) := by
        rw [show (List.range m).map (fun i => matVec
            (bandDatum (permMatAt (2 * m + 1) (tShift m)))
            (sliceAt i (deckColumn m)))
          = ((List.range m).map (fun i => sliceAt i (deckColumn m))).map
              (fun r => matVec
                (bandDatum (permMatAt (2 * m + 1) (tShift m))) r) from
          (ground.map_map _ _ (List.range m)).symm]
        have h3 := elim.matVec_combo
          (bandDatum (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1)
          (altO rest) _ hurows
        rw [hAl] at h3
        exact poly.oneValue_symm h3
      exact poly.unitTail_oneValue_right hV h2
    have hO := imageKill m (altO rest) (altO_len rest m hrl) hAV
    exact ⟨hc0, altEO_unit rest hE hO⟩

/-- A rescaled unit family reads the unit family. -/
private theorem vecScale_nullVec (c : BPair) : ∀ {w : List BPair},
    poly.unitTail w → poly.unitTail (elim.vecScale c w)
  | [], _ => trivial
  | _ :: _, h =>
    ⟨BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl c) h.1)
      (BPair.mul_unit c), vecScale_nullVec c h.2⟩

/-- Two unit families' entrywise sum reads the unit family. -/
private theorem vecAdd_null : ∀ {u v : List BPair},
    poly.unitTail u → poly.unitTail v →
    poly.unitTail (elim.vecAdd u v)
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | _ :: _, _ :: _, hu, hv =>
    ⟨BPair.oneValue_trans (BPair.add_congr hu.1 hv.1)
      (BPair.add_unit BPair.unit), vecAdd_null hu.2 hv.2⟩

/-- A combination over unit-familied pair rows reads the unit
family. -/
private theorem comboNull_flatPair (n : Nat) (p q : Nat → List BPair)
    (hp : ∀ i, poly.unitTail (p i)) (hq : ∀ i, poly.unitTail (q i)) :
    ∀ (cs : List BPair) (l : List Nat),
    poly.unitTail (elim.combo n cs (l.flatMap (fun i => [p i, q i])))
  | [], _ => poly.unitTail_replicate n
  | _ :: _, [] => poly.unitTail_replicate n
  | [c], a :: _ =>
    vecAdd_null (vecScale_nullVec c (hp a))
      (poly.unitTail_replicate n)
  | c :: d :: t, a :: l =>
    vecAdd_null (vecScale_nullVec c (hp a))
      (vecAdd_null (vecScale_nullVec d (hq a))
        (comboNull_flatPair n p q hp hq t l))

/-- The pair base reads the root block whole: the coefficient rows
with their images, independent at their own count inside the root
datum's kernel. -/
theorem rootBlock_wrap (m : Nat) :
    rootBlockRead (permMatAt (2 * m + 1) (tShift m)) (2 * m + 1) m
      (pairBase m) :=
  ⟨elim.indep_tail (2 * m + 1) (orbitSum m) (pairBase m)
      (orbitSplit_indep m),
   pairBase_ker m⟩

/-- The squeeze: every orbit vector reads through the splitting. -/
theorem orbitSplit_span (m : Nat) (v : List BPair)
    (hv : v.length = 2 * m + 1) :
    elim.spanRel (2 * m + 1) ([orbitSum m] ++ pairBase m) v := by
  refine elim.span_of_full (2 * m + 1) _ v ?_
    (orbitSplit_indep m) hv
  show (pairBase m).length + 1 = 2 * m + 1
  rw [pairBase_len m]

/-- The pair base's rows read the orbit's own count: the column's
degree slices sit at the side and so do their images under the
doubling datum. -/
private theorem pairBase_rows (m : Nat) : elim.rowsLen (2 * m + 1) (pairBase m) := by
  have hslice : ∀ i, (sliceAt i (deckColumn m)).length = 2 * m + 1 :=
    fun i => by
      show ((deckColumn m).map _).length = 2 * m + 1
      rw [ground.length_map, deckColumn_len]
  have hAl : (bandDatum (permMatAt (2 * m + 1) (tShift m))).length
      = 2 * m + 1 := by
    show (matAdd _ (matSwap (transposeM _))).length = 2 * m + 1
    refine (length_matAdd _ _ ?_).trans (length_permMatAt _ _)
    rw [length_permMatAt]
    show 2 * m + 1
      = ((transposeM (permMatAt (2 * m + 1) (tShift m))).map
        (fun r => r.map BPair.swap)).length
    rw [ground.length_map]
    exact (transposeLen _ (rowsLen_permMatAt _ _)
      (length_permMatAt _ _)).symm
  exact rowsLen_flatPair _ _ hslice
    (fun i => (matVec_length _ _).trans hAl) (List.range m)

/-- The exactly-two read: a root-datum kernel member reads through
the pairs alone, its sum coordinate clearing at the word's value
off the unit. -/
theorem rootBlock_span (m : Nat) (v : List BPair)
    (hv : v.length = 2 * m + 1)
    (hk : poly.unitTail (matVec
      (polyEvalM (deck.pSum m)
        (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1)) v)) :
    elim.spanRel (2 * m + 1) (pairBase m) v := by
  have hn : 0 < 2 * m + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hE := evalM_shape (2 * m + 1)
    (chordOp (permMatAt (2 * m + 1) (tShift m)))
    (chordWrap_shape m).1 (chordWrap_shape m).2 hn (deck.pSum m)
  have hprows : elim.rowsLen (2 * m + 1) (pairBase m) := pairBase_rows m
  obtain ⟨c₀, cs, hc₀, hcl, hone⟩ :=
    elim.span_elim (orbitSplit_span m v hv)
  cases cs with
  | nil =>
    exact absurd
      (show (0 : Nat) = (pairBase m).length + 1 from hcl)
      (fun h => Nat.noConfusion h)
  | cons d0 ds =>
    have hdl : ds.length = (pairBase m).length :=
      Nat.succ.inj
        (show ds.length + 1 = (pairBase m).length + 1 from hcl)
    -- the datum's application kills the sum coordinate
    have hDfix : poly.oneValue
        (matVec (polyEvalM (deck.pSum m)
          (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
          (orbitSum m))
        (elim.vecScale (poly.eval (deck.pSum m) (BPair.ofNat 2))
          (orbitSum m)) :=
      polyEval_fixed (2 * m + 1) (deck.pSum m) _ (orbitSum m)
        (orbitSum_len m)
        (poly.oneValue_trans (chord_ones m)
          (poly.oneValue_symm (vecScale_two (orbitSum m))))
    have hker : poly.unitTail
        (matVec (polyEvalM (deck.pSum m)
          (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
          (elim.combo (2 * m + 1) (d0 :: ds)
            ([orbitSum m] ++ pairBase m))) := by
      refine poly.oneValue_unitTail
        (elim.matVec_congr _ _ _ (poly.oneValue_symm hone)) ?_
      refine poly.oneValue_unitTail
        (matVec_scaleArg c₀ _ v) ?_
      exact vecScale_nullVec c₀ hk
    have hcombN : poly.unitTail
        (elim.combo (2 * m + 1) ds ((pairBase m).map
          (fun r => matVec (polyEvalM (deck.pSum m)
            (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (2 * m + 1)) r))) := by
      rw [show (pairBase m).map
          (fun r => matVec (polyEvalM (deck.pSum m)
            (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (2 * m + 1)) r)
        = (List.range m).flatMap (fun i =>
            [matVec (polyEvalM (deck.pSum m)
              (chordOp (permMatAt (2 * m + 1) (tShift m)))
              (2 * m + 1)) (sliceAt i (deckColumn m)),
             matVec (polyEvalM (deck.pSum m)
              (chordOp (permMatAt (2 * m + 1) (tShift m)))
              (2 * m + 1))
              (matVec (bandDatum (permMatAt (2 * m + 1) (tShift m)))
                (sliceAt i (deckColumn m)))]) from
        ground.map_flatMap _ _ (List.range m)]
      exact comboNull_flatPair (2 * m + 1) _ _
        (fun i => memberRow_ker m i) (fun i => imageRow_ker m i)
        ds (List.range m)
    have hDcomb : poly.unitTail
        (matVec (polyEvalM (deck.pSum m)
          (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
          (elim.combo (2 * m + 1) ds (pairBase m))) :=
      poly.unitTail_oneValue_right hcombN
        (by
          have h3 := elim.matVec_combo
            (polyEvalM (deck.pSum m)
              (chordOp (permMatAt (2 * m + 1) (tShift m)))
              (2 * m + 1))
            (2 * m + 1) ds (pairBase m) hprows
          rw [hE.2] at h3
          exact poly.oneValue_symm h3)
    -- the head component's read
    have hhead : poly.unitTail
        (matVec (polyEvalM (deck.pSum m)
          (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
          (elim.vecScale d0 (orbitSum m))) := by
      have hsplit2 : poly.oneValue
          (matVec (polyEvalM (deck.pSum m)
            (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
            (elim.combo (2 * m + 1) (d0 :: ds)
              ([orbitSum m] ++ pairBase m)))
          (elim.vecAdd
            (matVec (polyEvalM (deck.pSum m)
              (chordOp (permMatAt (2 * m + 1) (tShift m)))
              (2 * m + 1)) (elim.vecScale d0 (orbitSum m)))
            (matVec (polyEvalM (deck.pSum m)
              (chordOp (permMatAt (2 * m + 1) (tShift m)))
              (2 * m + 1))
              (elim.combo (2 * m + 1) ds (pairBase m)))) :=
        matVec_vAdd (2 * m + 1) _ _ _ hE.1
          ((elim.length_vecScale d0 _).trans (orbitSum_len m))
          (elim.length_combo _ ds _ hprows)
      have hall : poly.unitTail (elim.vecAdd
          (matVec (polyEvalM (deck.pSum m)
            (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (2 * m + 1)) (elim.vecScale d0 (orbitSum m)))
          (matVec (polyEvalM (deck.pSum m)
            (chordOp (permMatAt (2 * m + 1) (tShift m)))
            (2 * m + 1))
            (elim.combo (2 * m + 1) ds (pairBase m)))) :=
        poly.unitTail_oneValue_right hker hsplit2
      have hXl : (matVec (polyEvalM (deck.pSum m)
          (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
          (elim.vecScale d0 (orbitSum m))).length = 2 * m + 1 :=
        (matVec_length _ _).trans hE.2
      have hYl : (matVec (polyEvalM (deck.pSum m)
          (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
          (elim.combo (2 * m + 1) ds (pairBase m))).length
          = 2 * m + 1 :=
        (matVec_length _ _).trans hE.2
      rw [vecAdd_eq_polyAdd _ _ (hXl.trans hYl.symm)] at hall
      refine poly.oneValue_unitTail ?_ hall
      refine poly.oneValue_symm ?_
      refine poly.oneValue_trans
        (poly.add_congr (poly.oneValue_refl _)
          (poly.unitTail_oneValue (q := []) hDcomb trivial)) ?_
      rw [poly.add_nil]
      exact poly.oneValue_refl _
    -- the sum coordinate dies at the word's value
    have hd0 : d0.oneValue BPair.unit := by
      have hchain : poly.oneValue
          (matVec (polyEvalM (deck.pSum m)
            (chordOp (permMatAt (2 * m + 1) (tShift m))) (2 * m + 1))
            (elim.vecScale d0 (orbitSum m)))
          (elim.vecScale d0 (elim.vecScale
            (poly.eval (deck.pSum m) (BPair.ofNat 2)) (orbitSum m))) :=
        poly.oneValue_trans (matVec_scaleArg d0 _ (orbitSum m))
          (vecScale_oneValue d0 _ _ hDfix)
      have hct : poly.unitTail (elim.vecScale d0 (elim.vecScale
          (poly.eval (deck.pSum m) (BPair.ofNat 2)) (orbitSum m))) :=
        poly.oneValue_unitTail (poly.oneValue_symm hchain) hhead
      have hc0read := poly.getAt_unitTail hct 0
      rw [show ground.getAt BPair.unit (elim.vecScale d0
          (elim.vecScale (poly.eval (deck.pSum m) (BPair.ofNat 2))
            (orbitSum m))) 0
        = d0 * ((poly.eval (deck.pSum m) (BPair.ofNat 2))
            * BPair.ofPos Pos.one) from rfl] at hc0read
      have hEL : ((poly.eval (deck.pSum m) (BPair.ofNat 2))
          * BPair.ofPos Pos.one).oneValue
          (BPair.ofNat (2 * m + 1)) :=
        BPair.oneValue_trans
          (ground.BPair.mul_one_read (poly.eval (deck.pSum m) (BPair.ofNat 2)))
          (deck.pSum_two m)
      refine ground.mul_cancel_unit
        (BPair.ofNat_off_unit (2 * m + 1) hn) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.mul_comm (BPair.ofNat (2 * m + 1)) d0)) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl d0)
          (BPair.oneValue_symm hEL)) ?_
      exact hc0read
    -- the head withdraws and the pairs read the member whole
    have hscd0 : poly.unitTail (elim.vecScale d0 (orbitSum m)) :=
      poly.unitTail_map (fun x => d0 * x) (orbitSum m)
        (fun x _ => BPair.oneValue_trans
          (BPair.mul_congr hd0 (BPair.oneValue_refl x))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.mul_comm BPair.unit x))
            (BPair.mul_unit x)))
    have hone' : poly.oneValue (elim.vecScale c₀ v)
        (elim.combo (2 * m + 1) ds (pairBase m)) := by
      refine poly.oneValue_trans hone ?_
      show poly.oneValue
        (elim.vecAdd (elim.vecScale d0 (orbitSum m))
          (elim.combo (2 * m + 1) ds (pairBase m)))
        (elim.combo (2 * m + 1) ds (pairBase m))
      rw [vecAdd_eq_polyAdd _ _
        (((elim.length_vecScale d0 _).trans (orbitSum_len m)).trans
          (elim.length_combo _ ds _ hprows).symm)]
      exact poly.unitTail_add hscd0 _
    exact elim.span_intro (2 * m + 1) (pairBase m) v hprows hv
      ⟨c₀, ds, hc₀, hdl, hone'⟩

/-! The band root and the band congruence: the doubled block's
output.  At a located root the doubling reads `A² + 4 = t²` with
`t²` strictly interior to `4`, so the \emph{band root} `s` at
`4s² + t² = 4` adjoins one quadratic extension
(`lem:stagesplit`), the square the datum the per-root tower blocks
carry into the entries (`bandRootRead`, the read cleared at the
chord's own clearing with the square occupied at the interiority).
The \emph{band congruence} then takes the block's list at pairs —
each member against its `A`-image at `def:elim`'s pair descent, the
image columns rescaled at the band datum — and carries the block's
own level pencil to the fiber pencil, a congruence carrying its own
invertibility witness at the integer carrier — the adjugate against
the determinant, the two product reads `T Tw = det · I` and
`Tw T = det · I` off equal members — so every count is fixed at
`lem:inertia`'s congruence invariance (`bandCongrRead` at
`split.congrZ`, the clauses `split.diagRead`'s own).  The output is
the fiber pencil as a polynomial matrix in the chord variable at
the shape `lem:cellcount`'s counts consume (`fiberPencilRead` at
`cellcount.pShapeAt`), the three reads stated side by side at the
window pencil compressed on the block's list. -/

/-- The band quadratic's below-top list over the root's stage:
`w² = 4 − t²`, the cleared adjunction, the constant term the class
of the band symbol's negation. -/
def bandModulus (f : poly.Poly) : List (stagesplit.TE 1) :=
  [stagesplit.gRem stagesplit.baseOps f (poly.neg bandPoly),
   []]

/-- The per-root tower: the root's factor over the ground, the band
quadratic over it, the extension order the type's own —
`lem:stagesplit`'s stored tower at one root, the carrier the
per-root tier's site data live over. -/
def rootTower (f : poly.Poly) : stagesplit.TowerData 2 :=
  (((), f), bandModulus f)

/-- The band root's datum at a located chord: the square `s²` at
`4 s² + t² = 4`, one quadratic extension adjoined
(`lem:stagesplit`), the read cleared at the chord's own clearing
and the square occupied at the root's strict interiority to the
band. -/
def bandRootRead (tn sqn : BPair) (c : Pos) : Prop :=
  BPair.oneValue (BPair.ofNat 4 * sqn + tn * tn)
    (BPair.ofNat 4 * BPair.ofPos (c * c))
  ∧ sqn.offUnit
  ∧ BPair.unit ≤ sqn

instance (tn sqn : BPair) (c : Pos) : Decidable (bandRootRead tn sqn c) :=
  inferInstanceAs (Decidable (_ ∧ ¬ _ ∧ _ ≤ _))

/-- The band congruence at a doubled block: the block's level
pencil carried by the pair descent's congruence to the stated fiber
pencil, the descent entering cleared at the integer carrier
(`inertia.clearedCongr`, `split.diagRead`'s own unit-congruence
clauses), so every count is fixed (`lem:inertia`). -/
def bandCongrRead {o : Nat} (Z : split.PMat) (T Tw : SqMat o)
    (S : split.PMat) : Prop :=
  inertia.clearedCongr T Tw
  ∧ split.pmatOneValue (split.congrZ T.val Z) S

instance {o : Nat} (Z : split.PMat) (T Tw : SqMat o) (S : split.PMat) :
    Decidable (bandCongrRead Z T Tw S) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The fiber pencil at a stated orbit, the three conjuncts stated
side by side: the band root's own datum at the stated chord, the
band congruence carrying the window pencil compressed on the block's
list to the stated fiber pencil, and that pencil at the shape
`lem:cellcount`'s counts consume.  The band root's square is not
substituted into the congruenced entries here — that read is the
tier's named remainder, and the stated pencil carries its own
entries. -/
def fiberPencilRead {o : Nat} (n : Nat) (H G L : Mat) (T Tw : SqMat o)
    (S : split.PMat) (K : Nat) (tn sqn : BPair) (c : Pos) : Prop :=
  bandRootRead tn sqn c
  ∧ sqAt H n
  ∧ sqAt G n
  ∧ bandCongrRead
      (split.zMat (matMul L (matMul H (transposeM L)))
        (matMul L (matMul G (transposeM L)))) T Tw S
  ∧ cellcount.pShapeAt S o K

instance {o : Nat} (n : Nat) (H G L : Mat) (T Tw : SqMat o) (S : split.PMat)
    (K : Nat) (tn sqn : BPair) (c : Pos) :
    Decidable (fiberPencilRead n H G L T Tw S K tn sqn c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-! The fiber pencil produced at every window pair and every
cleared descent: the congruence's shape at the counts' clearing
power, and the producer at `lem:inertia`'s stated congruence
data. -/

theorem congrT_pShape (m : Nat) (T : Mat) (hTl : T.length = 2 * m)
    (hTr : rowsLen (2 * m) T) (A B : Mat)
    (hAl : A.length = 2 * m) (hBl : B.length = 2 * m) :
    cellcount.pShapeAt
      (split.congrZ T (split.zMat A B)) (2 * m) 1 :=
  cellcount.pShapeAt_of
    ((split.congrZ_len _ _).trans (transposeLen _ hTr hTl))
    (split.congrZ_rows _ _ (2 * m) hTl hTr
      (split.zMat_len A B (2 * m) hAl hBl))
    (split.congrZ_ble T (split.zMat A B) 2 (split.zMat_ble A B))

/-- `lem:fiberdec`'s band congruence produced at every window pair
and every cleared descent: the block's list at pairs, each member
against its `A`-image, the descent entering cleared at the integer
carrier as stated data with its invertibility witness beside it —
`inertia.clearedCongr`, `lem:inertia`'s cleared congruence whole —
so every count is fixed and
the output sits at the shape `lem:cellcount`'s counts consume.
The root datum and the window reads ride as the stated hypotheses,
and the band root's square is not substituted into the congruenced
entries: that read is the tier's named remainder, its descent the
band datum's own over the quadratic extension. -/
theorem fiberPencil_produce (m n : Nat) (H G : Mat)
    (T Tw : SqMat (2 * m)) (c : Pos) (tn sqn : BPair)
    (hH : sqAt H n) (hG : sqAt G n)
    (hcl : inertia.clearedCongr T Tw)
    (hroot : bandRootRead tn sqn c) :
    fiberPencilRead n H G (pairBase m) T Tw
      (split.congrZ T.val
        (split.zMat
          (matMul (pairBase m) (matMul H (transposeM (pairBase m))))
          (matMul (pairBase m) (matMul G (transposeM (pairBase m))))))
      1 tn sqn c :=
  ⟨hroot, hH, hG,
   ⟨hcl, split.pmatOne_refl _⟩,
   congrT_pShape m T.val (sqAt_len T.shape) (rowsLen_of_sqAt T.shape) _ _
     ((length_matMul _ _).trans (pairBase_len m))
     ((length_matMul _ _).trans (pairBase_len m))⟩

/-- The word identity holds at every translation: the geometric
word collects to the moved symbol, the theorem the decided read
mirrors. -/
theorem word_read (n m : Nat) (t s : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l)
    (hts : ∀ l, l < n → t (s l) = l)
    (hcyc : ∀ l, l < n → iterAt t (2 * m + 1) l = l) :
    wordOpRead (permMatAt n t) n m := by
  have hTl := length_permMatAt n t
  refine matOne_symm ?_
  refine matOne_trans
    (seg_read n m t s hn ht hst hts hcyc m 0 (Nat.zero_add m)) ?_
  exact msum_congr n
    (fun b => matPow (permMatAt n t) n (0 + b))
    (matPow (permMatAt n t) n)
    (fun k => matPow_shape n (permMatAt n t) hTl (0 + k))
    (fun k => matPow_shape n (permMatAt n t) hTl k)
    (fun k => by rw [Nat.zero_add k]; exact matOne_refl _)
    (List.range (2 * m + 1))

/-- The annihilation at every translation: the chord operator
reads the split polynomial's own factor, the orthogonal power
cleared at its witness's matrix. -/
theorem annih_of (n m : Nat) (t s : Nat → Nat) (hn : 0 < n)
    (ht : ∀ j, j < n → t j < n)
    (hst : ∀ l, l < n → s (t l) = l)
    (hts : ∀ l, l < n → t (s l) = l)
    (hcyc : ∀ l, l < n → iterAt t (2 * m + 1) l = l) :
    annihRead (permMatAt n t) n m := by
  have hTl := length_permMatAt n t
  have hTr := rowsLen_permMatAt n t
  have hSr : rowsLen n (chordOp (permMatAt n t)) :=
    rowsLen_matAdd n _ _ hTr
      (rowsLen_cast hTl (rowsLen_transposeM (permMatAt n t)))
  have hSl : (chordOp (permMatAt n t)).length = n :=
    (length_matAdd (permMatAt n t) (transposeM (permMatAt n t))
      (hTl.trans (length_transposeM (permMatAt n t) hTr
        (by rw [hTl]; exact hn)).symm)).trans hTl
  have hP := evalM_shape n (chordOp (permMatAt n t)) hSr hSl hn
    (deck.pSum m)
  have hsm := matPow_shape n (permMatAt n t) hTl m
  have horth : matOneValue
      (matMul (transposeM (permMatAt n t)) (permMatAt n t))
      (inertia.idMat n) := by
    rw [transposeM_permMatAt n t s hst hts]
    refine matOne_trans (permMatAt_mul n s t ht) ?_
    rw [permMatAt_congr n (fun l => s (t l)) (fun l => l) hst]
    exact permMatAt_id n
  have hcycM : matOneValue
      (matPow (permMatAt n t) n (2 * m + 1)) (inertia.idMat n) :=
    matPow_wrap n (2 * m) t hn ht hcyc 0
  have hfix : fixedWordRead (permMatAt n t) n m :=
    fixedWord_of n m (permMatAt n t) hTr hTl hn hcycM horth
      (word_read n m t s hn ht hst hts hcyc)
  have hSX : matOneValue
      (matMul (chordOp (permMatAt n t))
        (chordWord (permMatAt n t) n m))
      (inertia.matScaleB (BPair.ofNat 2)
        (chordWord (permMatAt n t) n m)) := by
    have hXsh := chordWord_shape n m (permMatAt n t) hTr hTl hn
    exact chord_join n (permMatAt n t) (chordWord (permMatAt n t) n m)
      hTr (rowsLen_cast hTl (rowsLen_transposeM (permMatAt n t)))
      (rowsLen_cast hXsh.2
        (rowsLen_transposeM (chordWord (permMatAt n t) n m)))
      (length_transposeM (chordWord (permMatAt n t) n m) hXsh.1
        (by rw [hXsh.2]; exact hn))
      hXsh.1 hfix.1 hfix.2
  have hSP : rowsLen n (matMul (chordOp (permMatAt n t))
      (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)) :=
    rowsLen_cast (length_transposeM _ hP.1 (by rw [hP.2]; exact hn))
      (rowsLen_matMul (chordOp (permMatAt n t))
        (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n))
  have hSPl : (matMul (chordOp (permMatAt n t))
      (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)).length
      = n := (length_matMul _ _).trans hSl
  have h2P : rowsLen n (inertia.matScaleB (BPair.ofNat 2)
      (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)) :=
    inertia.rowsLen_scaleB (BPair.ofNat 2) n _ hP.1
  have h2Pl : (inertia.matScaleB (BPair.ofNat 2)
      (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)).length
      = n :=
    (inertia.length_scaleB (BPair.ofNat 2) _).trans hP.2
  have f1 : matOneValue
      (matMul (matPow (permMatAt n t) n m)
        (matMul (chordOp (permMatAt n t))
          (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)))
      (matMul (matPow (permMatAt n t) n m)
        (inertia.matScaleB (BPair.ofNat 2)
          (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n))) := by
    refine matOne_trans
      (matOne_symm (matMul_assoc (matPow (permMatAt n t) n m)
        (chordOp (permMatAt n t))
        (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)
        hsm.1 hSr hP.1 hSl hP.2 hn hn)) ?_
    refine matOne_trans
      (matMul_congrL
        (matMul (matPow (permMatAt n t) n m) (chordOp (permMatAt n t)))
        (matMul (chordOp (permMatAt n t)) (matPow (permMatAt n t) n m))
        (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)
        (matOne_symm
          (chordOp_pow_comm n (2 * m) t s hn ht hst hts hcyc m))) ?_
    refine matOne_trans
      (matMul_assoc (chordOp (permMatAt n t))
        (matPow (permMatAt n t) n m)
        (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)
        hSr hsm.1 hP.1 hsm.2 hP.2 hn hn) ?_
    refine matOne_trans hSX ?_
    exact matOne_symm (inertia.matMul_scaleR (BPair.ofNat 2) n
      (matPow (permMatAt n t) n m)
      (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n) hP.1)
  have hW := length_permMatAt n (iterAt s m)
  have hWr := rowsLen_permMatAt n (iterAt s m)
  have hclear : ∀ Y : Mat, rowsLen n Y → Y.length = n →
      matOneValue
        (matMul (permMatAt n (iterAt s m))
          (matMul (matPow (permMatAt n t) n m) Y)) Y := by
    intro Y hYr hYl
    refine matOne_trans
      (matOne_symm (matMul_assoc (permMatAt n (iterAt s m))
        (matPow (permMatAt n t) n m) Y hWr hsm.1 hYr hsm.2 hYl hn hn))
      ?_
    refine matOne_trans
      (matMul_congrL
        (matMul (permMatAt n (iterAt s m))
          (matPow (permMatAt n t) n m))
        (inertia.idMat n) Y
        (clearW_pow n t s hn ht hst m)) ?_
    exact inertia.idMat_matMul n Y hYr hYl hn
  refine matOne_trans (matOne_symm (hclear
    (matMul (chordOp (permMatAt n t))
      (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n))
    hSP hSPl)) ?_
  refine matOne_trans
    (matMul_congrR (n := n) (k := n) (permMatAt n (iterAt s m))
      (matMul (matPow (permMatAt n t) n m)
        (matMul (chordOp (permMatAt n t))
          (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)))
      (matMul (matPow (permMatAt n t) n m)
        (inertia.matScaleB (BPair.ofNat 2)
          (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n)))
      (rowsLen_cast (length_transposeM _ hSP
        (by rw [hSPl]; exact hn))
        (rowsLen_matMul (matPow (permMatAt n t) n m)
          (matMul (chordOp (permMatAt n t))
            (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n))))
      (rowsLen_cast (length_transposeM _ h2P
        (by rw [h2Pl]; exact hn))
        (rowsLen_matMul (matPow (permMatAt n t) n m)
          (inertia.matScaleB (BPair.ofNat 2)
            (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n))))
      ((length_matMul _ _).trans hsm.2)
      ((length_matMul _ _).trans hsm.2)
      hn f1) ?_
  exact hclear
    (inertia.matScaleB (BPair.ofNat 2)
      (polyEvalM (deck.pSum m) (chordOp (permMatAt n t)) n))
    h2P h2Pl

end fiberdec
