import MassGap.States
import MassGap.Serpairing
import MassGap.Mixedinv
/-!
`prop:wg` — the pairing in the permutation presentation.  The
conjugation flips daggers and transposes wirings, the transpose the
inverse permutation (`conjF` at `places.invPerm`).  The invariant
span's Gram is the cycle count, `𝖦_{αβ} = d_f^{#cycles(α βᵀ)}`, a
polynomial matrix in the residue (`gramWg` at `dfPow`,
`lem:mixedinv`'s object at its recorded consumer), the place
permutations `con:places`' enumeration at the unit content
(`places.perms`); the Weingarten value is the adjugate column against
the determinant, `𝖦 w = e_id` the solved witness's whole
verification (`wgPair` at `lem:genericlift`'s adjugate).  The Gram
determinant sits off the sum's unit at every count
(`gramWg_detOcc`, `lem:mixedinv`'s independence read at the
residue point `d_f = k`), and the contraction sum reads the
wiring's cycle words alone: the Gram's entry at two composed keys
is the keys' own (`gramWg_transport`, `con:places`' composition
count) and the adjugate column at a composed key reads the key's
own value (`wgCol_transport`, the pulled column solving the Gram
against the determinant-scaled identity datum with the one
determinant cleared).  The
evaluation of a generator is the contraction sum (`evalPhi` over
the site's own variables, `varsOf`, the recursion over the
variables' permutation pairs, the two-plaquette fiber's read its
instance at the variables `0` and `1`): per variable at
matched dagger counts, over the permutation pairs `(σ, τ)`, the
`δ`-wirings close the chains into loops — the wiring's matching
against the `σ, τ`-matchings at the index slots, `σ` the undaggered
rows against the daggered columns and `τ` the exchange (a daggered
factor's conjugate row is its own column), the loop count the
alternating cycles' half count (`matchIn`,
the loop fold `places.cyclesOf`'s) — each loop a factor `d_f`, the
sum one numerator fold over the one shared determinant, and a
mismatched dagger count reads the sum's unit.  The pairing
of two states on their factor lists is `Eval(Φ̄_A Φ_B)`, the
conjugated key against the second at the concatenated site
(`pairPhi`, `pairFull` the combinations' bilinear fold).  Every
output reads at one of the two tags: the symbolic polynomial pair
at its clearance radius, the factor count
(`lem:genericlift`(iv)'s fold), or the direct per-residue read at
or below it; the mixed-power derivation — the invariants the
permutation span at `k ≤ d_f`, the projection the span's Gram
projection — sits at `lem:mixedinv` with the span's independence,
the batteries' fusion-read instances the scheme's own pins
(`prop:repring`'s displays), the `S₄` closed form the emitted
gate's; and the `B`, `C` and `D` members' presentation runs at
the defining factors' pair partitions with the member Gram
(`lem:serpairing`'s): per variable at an even factor count — an
odd count reads the sum's unit — the contraction sum over the
partition pairs at the member adjugate against its determinant,
the wirings closing the dual-pair and form edges into loops on
the composite graph, the bonds with a daggered factor's two
twist nodes, each loop one value — the dimension `r + 3` at `B`
and `D`, one engine at the shared Gram and loop value
(`evalPhiBD`), and the doubled rank `2r` at `C` at the loop's
parity, half the edge count joined to the dual-pair edges read
forward and the form edges read against (`evalPhiC`) — and the
pairing reads at the engine argument (`pairPhi`, `pairFull` the
combinations' bilinear fold).  And
`rem:kernel`'s gauge-mode sentence reads at the carried
evaluation: the states are indexed gauge-free by the multisets of
oriented cyclic words, so a letter-preserving relabeling of the
site and its carried wiring reads the generator's own value
(`evalPhi_transport`) — the letters' positions carried by the
per-letter slot maps, the composite graph's slots by the doubled
relabeling, the loop count by `places.cyclesOf_transport`, and the
numerator's fold over the tuples of the variables' words reindexed
along the conjugated words at the Weingarten column's own travel.
-/

namespace wg
open ground poly elim places states genericlift

/-- The fundamental count's power, a polynomial in the residue at
`d_f = r + 1`. -/
def dfPow (c : Nat) : Poly := poly.powOf [⟨2, 1⟩, ⟨2, 1⟩] c

/-- The span's Gram: the cycle count `d_f^{#cycles(α βᵀ)}`
entrywise, a polynomial matrix in the residue. -/
def gramWg (k : Nat) : split.PMat :=
  (places.perms k).map (fun a => (places.perms k).map (fun b =>
    dfPow (places.cyclesOf
      (places.expo a (places.invPerm k b))).length))

/-- The Weingarten pair at a class member: the adjugate column
against the determinant, `𝖦 w = e_id` the solved witness. -/
def wgPair (k : Nat) (γ : List Nat) : poly.PPair :=
  (ground.getAt []
    (ground.getAt [] (genericlift.padj (gramWg k))
      (places.idxOf γ (places.perms k)))
    (places.idxOf (List.range k) (places.perms k)),
   split.pminor (gramWg k))

/-- The Gram's row count and shape reads, the enumeration's own. -/
private theorem gramWg_len (k : Nat) :
    (gramWg k).length = (places.perms k).length :=
  ground.length_map _ (places.perms k)

/-- The Gram's rows sit at the enumeration's count. -/
private theorem gramWg_rows (k : Nat) :
    elim.rowsLen (places.perms k).length (gramWg k) :=
  elim.rowsLen_map _ _ (places.perms k)
    (fun _ _ => ground.length_map _ (places.perms k))

/-- The Gram is square at its own row count. -/
private theorem gramWg_sq (k : Nat) :
    elim.rowsLen (gramWg k).length (gramWg k) := by
  rw [gramWg_len]
  exact gramWg_rows k

/-- The Gram's head row sits at the enumeration's count. -/
private theorem gramWg_head (k : Nat) :
    ((gramWg k).headD []).length = (places.perms k).length :=
  elim.headD_len_of _ _ (gramWg_len k) (gramWg_rows k)

/-- The adjugate's row count is the enumeration's. -/
private theorem padj_len (k : Nat) :
    (genericlift.padj (gramWg k)).length = (places.perms k).length :=
  (ground.matOf_length (gramWg k).length (gramWg k).length _).trans
    (gramWg_len k)

/-- The adjugate's rows sit at the enumeration's count. -/
private theorem padj_rows (k : Nat) :
    elim.rowsLen (places.perms k).length
      (genericlift.padj (gramWg k)) := by
  rw [← gramWg_len k]
  exact elim.rowsLen_matOf _ _ _

/-- The adjugate's head row sits at the enumeration's count. -/
private theorem padj_head (k : Nat) :
    ((genericlift.padj (gramWg k)).headD []).length
      = (places.perms k).length :=
  elim.headD_len_of _ _ (padj_len k) (padj_rows k)

/-! `lem:mixedinv`'s Gram at a residue point (`prop:wg`'s Gram with
its independence): the residue power's read at a count, the
evaluated Gram the permutation families' own, and the determinant
off the sum's unit there — so the polynomial minor carries no unit
tail. -/

/-- The residue base's read at a count: `1 + x` reads the
successor. -/
private theorem eval_dfBase (r : Nat) :
    (poly.eval [BPair.ofNat 1, BPair.ofNat 1]
      (BPair.ofNat r)).oneValue (BPair.ofNat (r + 1)) := by
  show (BPair.ofNat 1 + BPair.ofNat r
      * poly.eval [BPair.ofNat 1] (BPair.ofNat r)).oneValue
    (BPair.ofNat (r + 1))
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl (BPair.ofNat 1))
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat r))
        (poly.eval_one (BPair.ofNat 1) (BPair.ofNat r)))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl (BPair.ofNat 1))
      (BPair.mul_ofNat_one (BPair.ofNat r))) ?_
  rw [Nat.add_comm r 1]
  exact BPair.oneValue_symm (BPair.ofNat_add 1 r)

/-- The residue power's read at a count: the fundamental count's
power reads the successor's own power. -/
private theorem eval_dfPow : ∀ (c r : Nat),
    (poly.eval (dfPow c) (BPair.ofNat r)).oneValue
      (BPair.ofNat ((r + 1) ^ c))
  | 0, r => poly.eval_one (BPair.ofNat 1) (BPair.ofNat r)
  | c + 1, r => by
    show (poly.eval (poly.mul [BPair.ofNat 1, BPair.ofNat 1]
        (dfPow c)) (BPair.ofNat r)).oneValue
      (BPair.ofNat ((r + 1) ^ c * (r + 1)))
    refine BPair.oneValue_trans
      (poly.eval_mul [BPair.ofNat 1, BPair.ofNat 1] (dfPow c)
        (BPair.ofNat r)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (eval_dfBase r) (eval_dfPow c r)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
    exact BPair.oneValue_symm (BPair.ofNat_mul ((r + 1) ^ c) (r + 1))

/-- The Gram determinant sits off the sum's unit at every count:
the minor evaluated at the residue `d_f = k` is the permutation
families' Gram determinant, and `lem:mixedinv`'s independence puts
that off the unit. -/
theorem gramWg_detOcc : ∀ k : Nat,
    ¬ poly.unitTail (split.pminor (gramWg k))
  | 0 => by decide +kernel
  | w + 1 => by
    intro hu
    have hGl := gramWg_len (w + 1)
    have hGr := gramWg_rows (w + 1)
    have hGsq := gramWg_sq (w + 1)
    have hEv := poly.eval_unitTail hu (BPair.ofNat w)
    have hmin := elim.eval_minorP (gramWg (w + 1))
      (BPair.ofNat w) hGsq
    have hGel : ((gramWg (w + 1)).map (fun row =>
        poly.pevalB row (BPair.ofNat w))).length
        = (places.perms (w + 1)).length :=
      (ground.length_map _ (gramWg (w + 1))).trans hGl
    have hGer : elim.rowsLen (places.perms (w + 1)).length
        ((gramWg (w + 1)).map (fun row =>
          poly.pevalB row (BPair.ofNat w))) :=
      elim.rowsLen_mapRowsO (fun f => poly.eval f (BPair.ofNat w))
        (gramWg (w + 1)) _ hGr
    have hGesq : elim.rowsLen ((gramWg (w + 1)).map (fun row =>
        poly.pevalB row (BPair.ofNat w))).length
        ((gramWg (w + 1)).map (fun row =>
          poly.pevalB row (BPair.ofNat w))) := by
      rw [hGel]
      exact hGer
    have hLl : (mixedinv.permFlats (w + 1) (w + 1)).length
        = (places.perms (w + 1)).length :=
      ground.length_map _ (places.perms (w + 1))
    have hGraml : (elim.gramM
        (mixedinv.permFlats (w + 1) (w + 1))).length
        = (places.perms (w + 1)).length :=
      (ground.length_map _ (mixedinv.permFlats (w + 1) (w + 1))).trans
        hLl
    have hentry : ∀ a, a < (places.perms (w + 1)).length →
        ∀ b, b < (places.perms (w + 1)).length →
        (ground.getAt BPair.unit (ground.getAt []
            ((gramWg (w + 1)).map (fun row =>
              poly.pevalB row (BPair.ofNat w))) a) b).oneValue
          (ground.getAt BPair.unit (ground.getAt []
            (elim.gramM (mixedinv.permFlats (w + 1) (w + 1))) a) b) := by
      intro a ha b hb
      have hGa : a < (gramWg (w + 1)).length := by
        rw [hGl]
        exact ha
      have hLa : a < (mixedinv.permFlats (w + 1) (w + 1)).length := by
        rw [hLl]
        exact ha
      have hLb : b < (mixedinv.permFlats (w + 1) (w + 1)).length := by
        rw [hLl]
        exact hb
      have hrowl : (ground.getAt ([] : poly.PPoly) (gramWg (w + 1))
          a).length = (places.perms (w + 1)).length :=
        elim.rowsLen_getAt (gramWg (w + 1)) a hGr hGa
      rw [ground.getAt_map ([] : poly.PPoly) ([] : poly.Poly)
          (fun row => poly.pevalB row (BPair.ofNat w))
          (gramWg (w + 1)) a hGa]
      show (ground.getAt BPair.unit
          ((ground.getAt ([] : poly.PPoly) (gramWg (w + 1)) a).map
            (fun f => poly.eval f (BPair.ofNat w))) b).oneValue _
      rw [ground.getAt_map ([] : poly.Poly) BPair.unit
          (fun f => poly.eval f (BPair.ofNat w))
          (ground.getAt [] (gramWg (w + 1)) a) b
          (by rw [hrowl]; exact hb)]
      show (poly.eval (ground.getAt ([] : poly.Poly)
          (ground.getAt ([] : poly.PPoly)
            ((places.perms (w + 1)).map (fun x =>
              (places.perms (w + 1)).map (fun y =>
                dfPow (places.cyclesOf (places.expo x
                  (places.invPerm (w + 1) y))).length))) a) b)
        (BPair.ofNat w)).oneValue _
      rw [ground.getAt_map ([] : List Nat) ([] : poly.PPoly)
          (fun x => (places.perms (w + 1)).map (fun y =>
            dfPow (places.cyclesOf (places.expo x
              (places.invPerm (w + 1) y))).length))
          (places.perms (w + 1)) a ha,
        ground.getAt_map ([] : List Nat) ([] : poly.Poly) _
          (places.perms (w + 1)) b hb,
        elim.gramM_entry (mixedinv.permFlats (w + 1) (w + 1)) a b
          hLa hLb]
      show ground.BPair.oneValue _ (elim.dotP
        (ground.getAt ([] : List BPair)
          ((places.perms (w + 1)).map (fun σ =>
            mixedinv.flatF (w + 1) (w + 1) (mixedinv.permMat σ))) a)
        (ground.getAt ([] : List BPair)
          ((places.perms (w + 1)).map (fun σ =>
            mixedinv.flatF (w + 1) (w + 1) (mixedinv.permMat σ))) b))
      rw [ground.getAt_map ([] : List Nat) ([] : List BPair)
          (fun σ => mixedinv.flatF (w + 1) (w + 1)
            (mixedinv.permMat σ)) (places.perms (w + 1)) a ha,
        ground.getAt_map ([] : List Nat) ([] : List BPair)
          (fun σ => mixedinv.flatF (w + 1) (w + 1)
            (mixedinv.permMat σ)) (places.perms (w + 1)) b hb]
      exact BPair.oneValue_trans (eval_dfPow _ w)
        (BPair.oneValue_symm (mixedinv.perm_gram (w + 1) (w + 1) _ _
          (ground.countOf_getAt_pos ([] : List Nat)
            (places.perms (w + 1)) a ha)
          (ground.countOf_getAt_pos ([] : List Nat)
            (places.perms (w + 1)) b hb)))
    refine elim.indep_det (mixedinv.mixWidth (w + 1) (w + 1))
      (mixedinv.permFlats (w + 1) (w + 1))
      (mixedinv.perm_indep (w + 1) (w + 1) (Nat.le_refl (w + 1))) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (elim.detL_congr_letters _ _ (hGel.trans hGraml.symm)
        (fun a ha b hb => hentry a (by rw [← hGel]; exact ha) b
          (by rw [← hGel]; exact hb)))) ?_
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (elim.minor_detL _ hGesq))
      (BPair.oneValue_trans (BPair.oneValue_symm hmin) hEv)

/-! `prop:wg`'s class read: the Gram's entry at two composed keys
is the keys' own and the adjugate column at a composed key reads
the key's own value — the relabeling a bijection of the
enumeration fixing the identity word, the solved witness moved
across it and the one determinant cleared. -/

/-- The Gram's entry at two enumeration members: the fundamental
count's power at the composite's cycle count. -/
private theorem gramWg_entry (k : Nat) (x y : List Nat)
    (hx : 0 < ground.countOf x (places.perms k))
    (hy : 0 < ground.countOf y (places.perms k)) :
    ground.getAt [] (ground.getAt [] (gramWg k)
        (places.idxOf x (places.perms k)))
      (places.idxOf y (places.perms k))
    = dfPow (places.cyclesOf (places.expo x
        (places.invPerm k y))).length := by
  rw [show gramWg k = (places.perms k).map (fun p =>
      (places.perms k).map (fun q => dfPow (places.cyclesOf
        (places.expo p (places.invPerm k q))).length)) from rfl,
    ground.getAt_map ([] : List Nat) ([] : poly.PPoly) _
      (places.perms k) _ (places.idxOf_lt (places.perms k) x hx),
    ground.getAt_map ([] : List Nat) ([] : poly.Poly) _
      (places.perms k) _ (places.idxOf_lt (places.perms k) y hy),
    places.getAt_idxOf (places.perms k) x hx,
    places.getAt_idxOf (places.perms k) y hy]

/-- The Gram's transport symmetry: the relabeled pair's entry is the
pair's own — the relabeling carries the composite and the cycle
count travels with it. -/
theorem gramWg_transport (k : Nat) (a b ρ : List Nat)
    (ha : 0 < ground.countOf a (places.perms k))
    (hb : 0 < ground.countOf b (places.perms k))
    (hr : 0 < ground.countOf ρ (places.perms k)) :
    ground.getAt [] (ground.getAt [] (gramWg k)
      (places.idxOf ((places.invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 a j))) (places.perms k)))
      (places.idxOf ((places.invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 b j))) (places.perms k))
    = ground.getAt [] (ground.getAt [] (gramWg k)
        (places.idxOf a (places.perms k)))
        (places.idxOf b (places.perms k)) := by
  rw [gramWg_entry k _ _ (places.transport_member k ha hr)
      (places.transport_member k hb hr),
    gramWg_entry k a b ha hb,
    places.invPerm_transport k b ρ hb hr,
    places.expo_transport k a (places.invPerm k b) ρ
      (places.invPerm_member k hb) hr,
    places.cyclesOf_transport k (places.expo_member k ha
      (places.invPerm_member k hb)) hr]

/-- The diagonal's entry at the replicated determinant. -/
private theorem pdiag_entry (k a c : Nat)
    (ha : a < (places.perms k).length)
    (hc : c < (places.perms k).length) :
    ground.getAt [] (ground.getAt []
        (split.pdiag (List.replicate (gramWg k).length
          (split.pminor (gramWg k)))) a) c
      = if c = a then split.pminor (gramWg k) else [] := by
  show ground.getAt ([] : poly.Poly) (ground.getAt []
      (ground.matOf (List.replicate (gramWg k).length
          (split.pminor (gramWg k))).length
        (List.replicate (gramWg k).length
          (split.pminor (gramWg k))).length
        (fun i j => if j = i then ground.getAt ([] : poly.Poly)
          (List.replicate (gramWg k).length
            (split.pminor (gramWg k))) i
          else ([] : poly.Poly))) a) c = _
  rw [ground.matOf_entry ([] : List poly.Poly) ([] : poly.Poly)
    _ _ _ a c (by rw [ground.length_replicate, gramWg_len]; exact ha)
    (by rw [ground.length_replicate, gramWg_len]; exact hc)]
  by_cases hca : c = a
  · rw [if_pos hca, if_pos hca,
      ground.getAt_replicate ([] : poly.Poly) (split.pminor (gramWg k))
        (gramWg k).length a (by rw [gramWg_len]; exact ha)]
  · rw [if_neg hca, if_neg hca]

/-- The adjugate identity's row fold at the Gram: the row against
the adjugate's column collects the determinant on the diagonal and
the sum's unit off it. -/
private theorem gram_adj_row (k a c : Nat)
    (ha : a < (places.perms k).length)
    (hc : c < (places.perms k).length) :
    poly.oneValue (ground.famFold poly.add []
        (fun s => poly.mul
          (ground.getAt [] (ground.getAt [] (gramWg k) a) s)
          (ground.getAt [] (ground.getAt []
            (genericlift.padj (gramWg k)) s) c))
        (List.range (places.perms k).length))
      (if c = a then split.pminor (gramWg k) else []) := by
  have haG : a < (gramWg k).length := by
    rw [gramWg_len]
    exact ha
  have hMl : (split.pmatMul (gramWg k)
      (genericlift.padj (gramWg k))).length = (gramWg k).length :=
    ground.length_map _ (gramWg k)
  have hMr : elim.rowsLen (places.perms k).length
      (split.pmatMul (gramWg k) (genericlift.padj (gramWg k))) :=
    elim.rowsLen_matMulO poly.polyOps _ _ _ (padj_head k)
  have hrow := elim.matMulP_entry (gramWg k)
    (genericlift.padj (gramWg k)) (places.perms k).length
    (places.perms k).length (gramWg_rows k) (padj_head k) a c
    (by rw [hMl] at *; exact haG) hc
  have h1 := ground.matched_entry ([] : List poly.Poly)
    (genericlift.adjRead_all (gramWg k) (gramWg_sq k)) a
    (by rw [hMl]; exact haG)
  have h2 := ground.matched_entry ([] : poly.Poly) h1 c
    (by rw [elim.rowsLen_getAt _ a hMr (by rw [hMl]; exact haG)]
        exact hc)
  rw [pdiag_entry k a c ha hc] at h2
  exact poly.oneValue_trans (poly.oneValue_symm hrow) h2

/-- The adjugate identity's column fold at the Gram, the exchanged
product order. -/
private theorem gram_adj_col (k a c : Nat)
    (ha : a < (places.perms k).length)
    (hc : c < (places.perms k).length) :
    poly.oneValue (ground.famFold poly.add []
        (fun s => poly.mul
          (ground.getAt [] (ground.getAt []
            (genericlift.padj (gramWg k)) a) s)
          (ground.getAt [] (ground.getAt [] (gramWg k) s) c))
        (List.range (places.perms k).length))
      (if c = a then split.pminor (gramWg k) else []) := by
  have haA : a < (genericlift.padj (gramWg k)).length := by
    rw [padj_len]
    exact ha
  have hMl : (split.pmatMul (genericlift.padj (gramWg k))
      (gramWg k)).length = (genericlift.padj (gramWg k)).length :=
    ground.length_map _ (genericlift.padj (gramWg k))
  have hMr : elim.rowsLen (places.perms k).length
      (split.pmatMul (genericlift.padj (gramWg k)) (gramWg k)) :=
    elim.rowsLen_matMulO poly.polyOps _ _ _ (gramWg_head k)
  have hrow := elim.matMulP_entry (genericlift.padj (gramWg k))
    (gramWg k) (places.perms k).length (places.perms k).length
    (padj_rows k) (gramWg_head k) a c haA hc
  have h1 := ground.matched_entry ([] : List poly.Poly)
    (genericlift.adjColRead_all (gramWg k) (gramWg_sq k)) a
    (by rw [hMl]; exact haA)
  have h2 := ground.matched_entry ([] : poly.Poly) h1 c
    (by rw [elim.rowsLen_getAt _ a hMr (by rw [hMl]; exact haA)]
        exact hc)
  rw [pdiag_entry k a c ha hc] at h2
  exact poly.oneValue_trans (poly.oneValue_symm hrow) h2

/-! The relabeling's index map on the enumeration, its two-sided
witness and the identity word's fixity. -/

/-- The relabeled key's own place in the enumeration. -/
private def relIx (k : Nat) (ρ : List Nat) (i : Nat) : Nat :=
  places.idxOf ((places.invPerm k ρ).map (fun j =>
      ground.getAt 0 ρ (ground.getAt 0
        (ground.getAt [] (places.perms k) i) j)))
    (places.perms k)

/-- The composed key's index sits inside the enumeration. -/
private theorem relIx_lt (k : Nat) (ρ : List Nat)
    (hr : 0 < ground.countOf ρ (places.perms k)) (i : Nat)
    (hi : i < (places.perms k).length) :
    relIx k ρ i < (places.perms k).length :=
  places.idxOf_lt (places.perms k) _
    (places.transport_member k
      (ground.countOf_getAt_pos ([] : List Nat) (places.perms k) i hi)
      hr)

/-- The composed key's index reads the composed key back. -/
private theorem relIx_getAt (k : Nat) (ρ : List Nat)
    (hr : 0 < ground.countOf ρ (places.perms k)) (i : Nat)
    (hi : i < (places.perms k).length) :
    ground.getAt [] (places.perms k) (relIx k ρ i)
      = (places.invPerm k ρ).map (fun j =>
          ground.getAt 0 ρ (ground.getAt 0
            (ground.getAt [] (places.perms k) i) j)) :=
  places.getAt_idxOf (places.perms k) _
    (places.transport_member k
      (ground.countOf_getAt_pos ([] : List Nat) (places.perms k) i hi)
      hr)

/-- The partner relabeling's index map composes back to the key. -/
private theorem relIx_inv (k : Nat) (ρ : List Nat)
    (hr : 0 < ground.countOf ρ (places.perms k)) (i : Nat)
    (hi : i < (places.perms k).length) :
    relIx k (places.invPerm k ρ) (relIx k ρ i) = i := by
  show places.idxOf ((places.invPerm k (places.invPerm k ρ)).map
      (fun j => ground.getAt 0 (places.invPerm k ρ)
        (ground.getAt 0 (ground.getAt [] (places.perms k)
          (relIx k ρ i)) j))) (places.perms k) = i
  rw [relIx_getAt k ρ hr i hi,
    places.transport_invol k
      (ground.countOf_getAt_pos ([] : List Nat) (places.perms k) i hi)
      hr,
    places.idxOf_getAt (places.perms k) i (places.perms_distinct k) hi]

/-- The index map at the partner relabeling composes forward to
the key. -/
private theorem relIx_inv' (k : Nat) (ρ : List Nat)
    (hr : 0 < ground.countOf ρ (places.perms k)) (i : Nat)
    (hi : i < (places.perms k).length) :
    relIx k ρ (relIx k (places.invPerm k ρ) i) = i := by
  have h := relIx_inv k (places.invPerm k ρ)
    (places.invPerm_member k hr) i hi
  rw [places.invPerm_invPerm k hr] at h
  exact h

/-- The identity word is an enumeration member. -/
private theorem range_member (k : Nat) (ρ : List Nat)
    (hr : 0 < ground.countOf ρ (places.perms k)) :
    0 < ground.countOf (List.range k) (places.perms k) := by
  have h := places.expo_member k hr (places.invPerm_member k hr)
  rw [show places.expo ρ (places.invPerm k ρ) = List.range k from
    places.invPerm_comp k hr] at h
  exact h

/-- The relabeling fixes the identity word's place. -/
private theorem relIx_fix (k : Nat) (ρ : List Nat)
    (hr : 0 < ground.countOf ρ (places.perms k)) :
    relIx k ρ (places.idxOf (List.range k) (places.perms k))
      = places.idxOf (List.range k) (places.perms k) := by
  obtain ⟨_, _, hival, _⟩ :=
    places.perm_member_reads (places.invPerm_member k hr)
  show places.idxOf ((places.invPerm k ρ).map (fun j =>
      ground.getAt 0 ρ (ground.getAt 0
        (ground.getAt [] (places.perms k)
          (places.idxOf (List.range k) (places.perms k))) j)))
    (places.perms k) = _
  rw [places.getAt_idxOf (places.perms k) (List.range k)
      (range_member k ρ hr),
    ground.map_congr_members
      (fun j => ground.getAt 0 ρ (ground.getAt 0 (List.range k) j))
      (ground.getAt 0 ρ) (places.invPerm k ρ) (fun j hj => by
        rw [ground.getAt_range k j (hival j hj)]),
    places.invPerm_comp k hr]

/-- The Gram's entry at the relabeled index pair is the pair's
own. -/
private theorem gramWg_relIx (k : Nat) (ρ : List Nat)
    (hr : 0 < ground.countOf ρ (places.perms k)) (i j : Nat)
    (hi : i < (places.perms k).length)
    (hj : j < (places.perms k).length) :
    ground.getAt [] (ground.getAt [] (gramWg k) (relIx k ρ i))
        (relIx k ρ j)
      = ground.getAt [] (ground.getAt [] (gramWg k) i) j := by
  have h := gramWg_transport k (ground.getAt [] (places.perms k) i)
    (ground.getAt [] (places.perms k) j) ρ
    (ground.countOf_getAt_pos ([] : List Nat) (places.perms k) i hi)
    (ground.countOf_getAt_pos ([] : List Nat) (places.perms k) j hj)
    hr
  rw [places.idxOf_getAt (places.perms k) i (places.perms_distinct k)
      hi,
    places.idxOf_getAt (places.perms k) j (places.perms_distinct k)
      hj] at h
  exact h

/-- The Weingarten column travels with the relabeling: the
adjugate's identity-column entry at a relabeled key is the key's
own — the pulled column solves the Gram against the same
determinant-scaled identity datum, and the shared determinant
clears. -/
theorem wgCol_transport (k : Nat) (γ ρ : List Nat)
    (hg : 0 < ground.countOf γ (places.perms k))
    (hr : 0 < ground.countOf ρ (places.perms k)) :
    poly.oneValue
      (ground.getAt [] (ground.getAt []
        (genericlift.padj (gramWg k))
        (places.idxOf ((places.invPerm k ρ).map (fun j =>
          ground.getAt 0 ρ (ground.getAt 0 γ j)))
          (places.perms k)))
        (places.idxOf (List.range k) (places.perms k)))
      (ground.getAt [] (ground.getAt []
        (genericlift.padj (gramWg k))
        (places.idxOf γ (places.perms k)))
        (places.idxOf (List.range k) (places.perms k))) := by
  have hidU : places.idxOf (List.range k) (places.perms k)
      < (places.perms k).length :=
    places.idxOf_lt (places.perms k) _ (range_member k ρ hr)
  have hcount : ground.countOf
      (places.idxOf (List.range k) (places.perms k))
      (List.range (places.perms k).length) = 1 := by
    rw [ground.countOf_range, if_pos hidU]
  have hfixIff : ∀ a, a < (places.perms k).length →
      (places.idxOf (List.range k) (places.perms k) = relIx k ρ a
        ↔ places.idxOf (List.range k) (places.perms k) = a) := by
    intro a ha
    constructor
    · intro he
      have h1 := relIx_inv k ρ hr a ha
      rw [← he, relIx_fix k (places.invPerm k ρ)
        (places.invPerm_member k hr)] at h1
      exact h1.symm ▸ rfl
    · intro he
      rw [← he, relIx_fix k ρ hr]
  have hstepA : ∀ a, a < (places.perms k).length →
      poly.oneValue (ground.famFold poly.add []
        (fun s => poly.mul
          (ground.getAt [] (ground.getAt [] (gramWg k) a) s)
          (ground.getAt [] (ground.getAt []
            (genericlift.padj (gramWg k)) (relIx k ρ s))
            (places.idxOf (List.range k) (places.perms k))))
        (List.range (places.perms k).length))
        (if places.idxOf (List.range k) (places.perms k) = a
          then split.pminor (gramWg k) else []) := by
    intro a ha
    refine poly.oneValue_trans
      (ground.famFold_bij_ov poly.polyFoldLaws.toCommLaws []
        _ (fun t => poly.mul
          (ground.getAt [] (ground.getAt [] (gramWg k) a)
            (relIx k (places.invPerm k ρ) t))
          (ground.getAt [] (ground.getAt []
            (genericlift.padj (gramWg k)) t)
            (places.idxOf (List.range k) (places.perms k))))
        (g := relIx k ρ) (h := relIx k (places.invPerm k ρ))
        (ground.distinctList_range _)
        (fun x hx => relIx_inv k ρ hr x (ground.ltOfMem hx))
        (fun x hx => relIx_inv' k ρ hr x (ground.ltOfMem hx))
        (fun x hx => ground.countOf_range_pos
          (relIx_lt k ρ hr x (ground.ltOfMem hx)))
        (fun x hx => ground.countOf_range_pos
          (relIx_lt k (places.invPerm k ρ)
            (places.invPerm_member k hr) x (ground.ltOfMem hx)))
        (fun x hx => by
          rw [relIx_inv k ρ hr x (ground.ltOfMem hx)]
          exact poly.oneValue_refl _)) ?_
    refine poly.oneValue_trans
      (ground.famFold_congr_members_ov poly.oneValue poly.add []
        poly.oneValue_refl (fun h1 h2 => poly.add_congr h1 h2)
        _ (fun t => poly.mul
          (ground.getAt [] (ground.getAt [] (gramWg k)
            (relIx k ρ a)) t)
          (ground.getAt [] (ground.getAt []
            (genericlift.padj (gramWg k)) t)
            (places.idxOf (List.range k) (places.perms k))))
        (List.range (places.perms k).length) (fun t ht => by
          have htn : t < (places.perms k).length := ground.ltOfMem ht
          have hb := gramWg_relIx k ρ hr a
            (relIx k (places.invPerm k ρ) t) ha
            (relIx_lt k (places.invPerm k ρ)
              (places.invPerm_member k hr) t htn)
          rw [relIx_inv' k ρ hr t htn] at hb
          rw [hb]
          exact poly.oneValue_refl _)) ?_
    have hcore := gram_adj_row k (relIx k ρ a)
      (places.idxOf (List.range k) (places.perms k))
      (relIx_lt k ρ hr a ha) hidU
    by_cases hfx : places.idxOf (List.range k) (places.perms k)
        = relIx k ρ a
    · rw [if_pos ((hfixIff a ha).mp hfx)]
      rw [if_pos hfx] at hcore
      exact hcore
    · rw [if_neg (fun he => hfx ((hfixIff a ha).mpr he))]
      rw [if_neg hfx] at hcore
      exact hcore
  have hmain : ∀ r, r < (places.perms k).length →
      poly.oneValue
        (ground.getAt [] (ground.getAt []
          (genericlift.padj (gramWg k)) r)
          (places.idxOf (List.range k) (places.perms k)))
        (ground.getAt [] (ground.getAt []
          (genericlift.padj (gramWg k)) (relIx k ρ r))
          (places.idxOf (List.range k) (places.perms k))) := by
    intro r hr'
    refine poly.pmul_cancel (split.pminor (gramWg k)) _ _
      (gramWg_detOcc k) ?_
    have hB1 : poly.oneValue (ground.famFold poly.add []
        (fun a => poly.mul
          (ground.getAt [] (ground.getAt []
            (genericlift.padj (gramWg k)) r) a)
          (ground.famFold poly.add [] (fun s => poly.mul
            (ground.getAt [] (ground.getAt [] (gramWg k) a) s)
            (ground.getAt [] (ground.getAt []
              (genericlift.padj (gramWg k)) (relIx k ρ s))
              (places.idxOf (List.range k) (places.perms k))))
            (List.range (places.perms k).length)))
        (List.range (places.perms k).length))
        (poly.mul (ground.getAt [] (ground.getAt []
          (genericlift.padj (gramWg k)) r)
          (places.idxOf (List.range k) (places.perms k)))
          (split.pminor (gramWg k))) := by
      refine poly.oneValue_trans
        (ground.famFold_congr_members_ov poly.oneValue poly.add []
          poly.oneValue_refl (fun h1 h2 => poly.add_congr h1 h2)
          _ (fun a => poly.mul
            (ground.getAt [] (ground.getAt []
              (genericlift.padj (gramWg k)) r) a)
            (if places.idxOf (List.range k) (places.perms k) = a
              then split.pminor (gramWg k) else []))
          (List.range (places.perms k).length) (fun a ha =>
            poly.mul_congr _ (hstepA a (ground.ltOfMem ha)))) ?_
      refine ground.famFold_pick_ov poly.polyFoldLaws _
        (places.idxOf (List.range k) (places.perms k)) _
        (List.range (places.perms k).length) hcount ?_ ?_
      · rw [if_pos rfl]
        exact poly.oneValue_refl _
      · intro x _ hxi
        rw [if_neg (fun he => hxi he.symm)]
        exact poly.lovNilO ground.bpairOps ground.bpairRead
          (poly.mul_nil _)
    have hB2 : poly.oneValue (ground.famFold poly.add []
        (fun a => poly.mul
          (ground.getAt [] (ground.getAt []
            (genericlift.padj (gramWg k)) r) a)
          (ground.famFold poly.add [] (fun s => poly.mul
            (ground.getAt [] (ground.getAt [] (gramWg k) a) s)
            (ground.getAt [] (ground.getAt []
              (genericlift.padj (gramWg k)) (relIx k ρ s))
              (places.idxOf (List.range k) (places.perms k))))
            (List.range (places.perms k).length)))
        (List.range (places.perms k).length))
        (poly.mul (split.pminor (gramWg k))
          (ground.getAt [] (ground.getAt []
            (genericlift.padj (gramWg k)) (relIx k ρ r))
            (places.idxOf (List.range k) (places.perms k)))) := by
      refine poly.oneValue_trans
        (ground.famFold_congr_members_ov poly.oneValue poly.add []
          poly.oneValue_refl (fun h1 h2 => poly.add_congr h1 h2)
          _ (fun a => ground.famFold poly.add [] (fun s =>
            poly.mul (poly.mul
              (ground.getAt [] (ground.getAt []
                (genericlift.padj (gramWg k)) r) a)
              (ground.getAt [] (ground.getAt [] (gramWg k) a) s))
              (ground.getAt [] (ground.getAt []
                (genericlift.padj (gramWg k)) (relIx k ρ s))
                (places.idxOf (List.range k) (places.perms k))))
            (List.range (places.perms k).length))
          (List.range (places.perms k).length) (fun a _ =>
            poly.oneValue_trans
              (ground.famFold_mul_ov poly.polyFoldLaws poly.mul _
                (by
                  exact poly.lovNilO ground.bpairOps ground.bpairRead
                    (poly.mul_nil _))
                (by exact fun x y => poly.mul_sum _ x y) _
                (List.range (places.perms k).length))
              (ground.famFold_congr_members_ov poly.oneValue
                poly.add [] poly.oneValue_refl
                (fun h1 h2 => poly.add_congr h1 h2) _ _
                (List.range (places.perms k).length)
                (fun s _ => poly.oneValue_symm
                  (poly.mul_assoc _ _ _))))) ?_
      refine poly.oneValue_trans
        (ground.famFold_swap_ov poly.polyFoldLaws (fun a s => poly.mul (poly.mul
            (ground.getAt [] (ground.getAt []
              (genericlift.padj (gramWg k)) r) a)
            (ground.getAt [] (ground.getAt [] (gramWg k) a) s))
            (ground.getAt [] (ground.getAt []
              (genericlift.padj (gramWg k)) (relIx k ρ s))
              (places.idxOf (List.range k) (places.perms k))))
          (List.range (places.perms k).length)
          (List.range (places.perms k).length)) ?_
      refine poly.oneValue_trans
        (ground.famFold_congr_members_ov poly.oneValue poly.add []
          poly.oneValue_refl (fun h1 h2 => poly.add_congr h1 h2)
          _ (fun s => poly.mul
            (if s = r then split.pminor (gramWg k) else [])
            (ground.getAt [] (ground.getAt []
              (genericlift.padj (gramWg k)) (relIx k ρ s))
              (places.idxOf (List.range k) (places.perms k))))
          (List.range (places.perms k).length) (fun s hs =>
            poly.oneValue_trans
              (ground.famFold_mulR_ov poly.polyFoldLaws poly.mul _
                (by exact poly.oneValue_refl _)
                (by exact fun x y => poly.sum_mul x y _) _
                (List.range (places.perms k).length))
              (poly.mul_congr_left
                (gram_adj_col k r s hr' (ground.ltOfMem hs)) _))) ?_
      refine ground.famFold_pick_ov poly.polyFoldLaws _ r _
        (List.range (places.perms k).length)
        (by rw [ground.countOf_range, if_pos hr']) ?_ ?_
      · rw [if_pos rfl]
        exact poly.oneValue_refl _
      · intro x _ hxr
        rw [if_neg hxr]
        exact poly.oneValue_refl _
    exact poly.oneValue_trans (poly.mul_comm _ _)
      (poly.oneValue_trans (poly.oneValue_symm hB1) hB2)
  have hgi : ground.getAt [] (places.perms k)
      (places.idxOf γ (places.perms k)) = γ :=
    places.getAt_idxOf (places.perms k) γ hg
  have hkey := hmain (places.idxOf γ (places.perms k))
    (places.idxOf_lt (places.perms k) γ hg)
  rw [show relIx k ρ (places.idxOf γ (places.perms k))
      = places.idxOf ((places.invPerm k ρ).map (fun j =>
        ground.getAt 0 ρ (ground.getAt 0 γ j))) (places.perms k) from
    by rw [show relIx k ρ (places.idxOf γ (places.perms k))
        = places.idxOf ((places.invPerm k ρ).map (fun j =>
          ground.getAt 0 ρ (ground.getAt 0 (ground.getAt []
            (places.perms k)
            (places.idxOf γ (places.perms k))) j)))
          (places.perms k) from rfl, hgi]] at hkey
  exact poly.oneValue_symm hkey

/-- The factors at one letter, the positions' filter. -/
def posIf (G : states.FList) (f : states.Factor) : List Nat :=
  (List.range G.length).filter
    (fun i => ground.getAt (0, false) G i == f)

/-- One variable's matching written into the slot list: per slot
the row end against the matched column end, both directions. -/
private def matchIn (m2 : List Nat) (ps qs σ : List Nat)
    (offP offQ : Nat) : List Nat :=
  (List.range ps.length).foldl (fun acc s =>
    let a := 2 * ground.getAt 0 ps s + offP
    let b := 2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ
    (acc.set a b).set b a) m2

/-- The site's key bound, one beyond every variable key: the keys'
sum with one joined. -/
private def keyBound (G : states.FList) : Nat :=
  ground.famFold Nat.add 0 (fun i => (ground.getAt (0, false) G i).1)
    (List.range G.length) + 1

/-- The site's variables: its occupied keys, each once, in the
keys' own order, `prop:wg`'s per-variable index. -/
def varsOf (G : states.FList) : List Nat :=
  (List.range (keyBound G)).filter (fun v =>
    decide (0 < (posIf G (v, false)).length + (posIf G (v, true)).length))

/-- One variable's Weingarten entry at a permutation pair: the
identity key's adjugate column read at the composed key. -/
private def nOf (G : states.FList) (v : Nat) (σ τ : List Nat) : Poly :=
  ground.getAt [] (ground.getAt []
    (genericlift.padj (gramWg (posIf G (v, false)).length))
    (places.idxOf (places.expo σ (places.invPerm
      (posIf G (v, false)).length τ))
      (places.perms (posIf G (v, false)).length)))
    (places.idxOf (List.range (posIf G (v, false)).length)
      (places.perms (posIf G (v, false)).length))

/-- One variable's two matchings joined to a slot wiring: the
undaggered rows against the daggered columns at `σ`, the exchange
at `τ`. -/
private def matchVar (G : states.FList) (v : Nat) (σ τ m2 : List Nat) :
    List Nat :=
  matchIn (matchIn m2 (posIf G (v, false)) (posIf G (v, true)) σ 0 1)
    (posIf G (v, false)) (posIf G (v, true)) τ 1 0

/-- The wiring's matching: each place's row slot against its
image's column slot, both directions. -/
private def mOne (m : Nat) (π : List Nat) : List Nat :=
  (List.range m).foldl (fun acc i =>
    (acc.set (2 * i) (2 * ground.getAt 0 π i + 1)).set
      (2 * ground.getAt 0 π i + 1) (2 * i))
    (List.replicate (2 * m) 0)

/-- The composite walk: the matchings read after the wiring's
matching slot by slot. -/
private def compAt (m : Nat) (m1 m2 : List Nat) : List Nat :=
  (List.range (2 * m)).map (fun i =>
    ground.getAt 0 m2 (ground.getAt 0 m1 i))

/-- The contraction sum's recursion over the site's variables: per
variable the fold over its permutation pairs, each pair's two
matchings joined to the slot wiring and its Weingarten entry to
the coefficient list, and at the variables' end one term, the
coefficients' product against the loop value of the composite
walk, the alternating cycles' half count at a factor `d_f` each. -/
private def contract (G : states.FList) (m1 : List Nat) :
    List Nat → List Nat → List Poly → Poly → Poly
  | [], m2, cs, acc =>
    poly.add acc (cs.foldr poly.mul
      (dfPow ((places.cyclesOf (compAt G.length m1 m2)).length / 2)))
  | v :: vs, m2, cs, acc =>
    (places.perms (posIf G (v, false)).length).foldl (fun acc σ =>
      (places.perms (posIf G (v, false)).length).foldl (fun acc τ =>
        contract G m1 vs (matchVar G v σ τ m2) (cs ++ [nOf G v σ τ]) acc)
        acc) acc

/-- The evaluation of a generator, the contraction sum over the
site's variables: per variable at matched dagger counts — else the
sum's unit — over the permutation pairs `(σ, τ)`, the `δ`-wirings
close into loops at the joint matching of every variable, the
wiring's matching against the `σ, τ`-matchings at the row and
column slots, each loop a factor `d_f`, the coefficient the
Weingarten entries' product and the denominator the Gram
determinants' product, the adjugates and determinants one
evaluation per variable. -/
def evalPhi (G : states.FList) (π : List Nat) : poly.PPair :=
  if (varsOf G).all (fun v =>
      (posIf G (v, false)).length == (posIf G (v, true)).length) then
    (contract G (mOne G.length π) (varsOf G)
      (List.replicate (2 * G.length) 0) [] [],
     (varsOf G).foldr (fun v d =>
       poly.mul (split.pminor (gramWg (posIf G (v, false)).length)) d)
       poly.one)
  else poly.pZero

/-- The conjugation: the daggers flip. -/
def conjF (F : states.FList) : states.FList :=
  F.map (fun f => (f.1, !f.2))

/-! The `B`, `C` and `D` member tier: the presentation at the
defining factors' pair partitions with the member Gram
(`lem:serpairing`), `prop:wg`'s member display. -/

/-- The factors at one variable across both dagger reads, the
member presentation's slot list — the `u`-th factor in list order
the local slot `u`. -/
private def posVar (G : states.FList) (v : Nat) : List Nat :=
  (List.range G.length).filter
    (fun i => (ground.getAt (0, false) G i).1 == v)

/-- A daggered factor's `a`-node on the composite graph: the site
length past two nodes per earlier daggered factor, the `b`-node
its successor; the bonds the nodes below the site length. -/
private def aNode (m : Nat) (dag : List Bool) (j : Nat) : Nat :=
  m + 2 * ground.countOf true (dag.take j)

/-- A factor's row end: the `b`-node at a daggered factor — the
slots exchanged at the form's twist — else its own bond. -/
private def rvar (m : Nat) (dag : List Bool) (j : Nat) : Nat :=
  if ground.getAt false dag j then aNode m dag j + 1 else j

/-- A factor's column end: the `a`-node at a daggered factor, else
the bond of the factor wired onto it. -/
private def svar (m : Nat) (dag : List Bool) (invw : List Nat)
    (j : Nat) : Nat :=
  if ground.getAt false dag j then aNode m dag j
  else ground.getAt 0 invw j

/-- A partition's dual-pair edges at an end read, the local slots
at their global factor indices. -/
private def pairEdges (gs : List Nat) (f : Nat → Nat)
    (pp : List (Nat × Nat)) : List (Nat × Nat × Nat) :=
  pp.map (fun pr =>
    (f (ground.getAt 0 gs pr.1), f (ground.getAt 0 gs pr.2), 0))

/-- A daggered factor's two twist edges in factor order: the bond
onto the `a`-node, then the `b`-node onto the wired bond at the
form tag. -/
private def dagEdges (m : Nat) (dag : List Bool) (invw : List Nat) :
    List (Nat × Nat × Nat) :=
  ((List.range m).filter (fun j => ground.getAt false dag j)).flatMap
    (fun j => [(j, aNode m dag j, 0),
               (aNode m dag j + 1, ground.getAt 0 invw j, 1)])

/-- The other edge at a node — every node carries exactly two edge
ends — the least index off the current. -/
private def otherEdge (edges : List (Nat × Nat × Nat)) (c y : Nat) :
    Nat :=
  (List.range edges.length).foldl (fun acc i =>
    let e := ground.getAt (0, 0, 0) edges i
    if acc == edges.length && i != c && (e.1 == y || e.2.1 == y)
    then i else acc) edges.length

/-- One loop's walk from a start edge: each edge traversed forward
off its from-node, the state the edge count, the dual-pair edges
read forward, the form edges read against, and the visited
edges. -/
private def loopGoSer (edges : List (Nat × Nat × Nat)) (start : Nat) :
    Nat → Nat → Nat → Nat × Nat × Nat × List Nat →
    Nat × Nat × Nat × List Nat
  | 0, _, _, st => st
  | fuel + 1, c, x, (ec, fc, bc, vis) =>
    let e := ground.getAt (0, 0, 0) edges c
    let fwd := e.1 == x
    let y := if fwd then e.2.1 else e.1
    let ec' := ec + 1
    let fc' := if e.2.2 == 0 && fwd then fc + 1 else fc
    let bc' := if e.2.2 == 1 && !fwd then bc + 1 else bc
    let nxt := otherEdge edges c y
    if nxt == start then (ec', fc', bc', vis ++ [c])
    else loopGoSer edges start fuel nxt y (ec', fc', bc', vis ++ [c])

/-- The loops' fold over the composite graph: the walk takes the
least unused edge, one loop per orbit; the fold reads the loop
count with the parity sum, per loop half the edge count joined to
the forward dual-pair and backward form counts —
`serpairing.loopFold`'s walk idiom on the richer graph. -/
private def loopFoldSer (edges : List (Nat × Nat × Nat)) :
    Nat × Nat :=
  let st := (List.range edges.length).foldl (fun st i =>
    if 0 < ground.countOf i st.2.2 then st
    else
      let w := loopGoSer edges i edges.length i
        (ground.getAt (0, 0, 0) edges i).1 (0, 0, 0, [])
      (st.1 + 1,
       (st.2.1 + w.1 / 2 + w.2.1 + w.2.2.1, st.2.2 ++ w.2.2.2)))
    ((0, (0, [])) : Nat × Nat × List Nat)
  (st.1, st.2.1)

/-- The member recursion over the site's variables: per variable
the fold over its partition pairs, each pair's edges joined to the
dual-pair and form edge lists and its member adjugate entry to the
coefficient list, and at the variables' end one term, the
coefficients' product against the loop value at the composite
walk's count, the signed series negating at an odd walk parity. -/
private def contractSer (gram : Nat → split.PMat) (loopPoly : Nat → Poly)
    (signed : Bool) (G : states.FList) (dag : List Bool)
    (invw : List Nat) :
    List Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat) →
    List Poly → Poly → Poly
  | [], rE, sE, cs, acc =>
    let w := loopFoldSer (rE ++ sE ++ dagEdges G.length dag invw)
    let lp := if signed && w.2 % 2 == 1
      then poly.neg (loopPoly w.1) else loopPoly w.1
    poly.add acc (cs.foldr poly.mul lp)
  | v :: vs, rE, sE, cs, acc =>
    (serpairing.allParts ((posVar G v).length / 2)).foldl (fun acc P =>
      (serpairing.allParts ((posVar G v).length / 2)).foldl (fun acc Q =>
        contractSer gram loopPoly signed G dag invw vs
          (rE ++ pairEdges (posVar G v) (rvar G.length dag) P)
          (sE ++ pairEdges (posVar G v) (svar G.length dag invw) Q)
          (cs ++ [ground.getAt [] (ground.getAt []
            (genericlift.padj (gram ((posVar G v).length / 2)))
            (places.idxOf P (serpairing.allParts ((posVar G v).length / 2))))
            (places.idxOf Q
              (serpairing.allParts ((posVar G v).length / 2)))]) acc)
        acc) acc

/-- The member engine's core, `evalPhi`'s architecture at the pair
partitions: per variable at an even factor count — else the sum's
unit — the fold over the partition pairs of the member adjugate
entries against the loop value at the composite walk's count, the
adjugate and determinant one evaluation per variable, the signed
series negating at an odd walk parity. -/
private def evalSer (gram : Nat → split.PMat) (loopPoly : Nat → Poly)
    (signed : Bool) (G : states.FList) (π : List Nat) :
    poly.PPair :=
  if (varsOf G).all (fun v => (posVar G v).length % 2 == 0) then
    (contractSer gram loopPoly signed G (G.map (fun f => f.2))
      (places.invPerm G.length π) (varsOf G) [] [] [] [],
     (varsOf G).foldr (fun v d =>
       poly.mul (split.pminor (gram ((posVar G v).length / 2))) d)
       poly.one)
  else poly.pZero

/-- The `B` and `D` member evaluation — one engine, the Gram and
the loop value shared (`serpairing.gramBD`, the dimension `r + 3`
per loop at `serpairing.dimPow`): the contraction sum over the
pair partitions, `prop:wg`'s member display. -/
def evalPhiBD (G : states.FList) (π : List Nat) : poly.PPair :=
  evalSer serpairing.gramBD serpairing.dimPow false G π

/-- The `C` member evaluation: the doubled rank `2r` per loop
(`serpairing.rankPow`, `serpairing.gramC`), a term at an odd walk
parity entering negated. -/
def evalPhiC (G : states.FList) (π : List Nat) : poly.PPair :=
  evalSer serpairing.gramC serpairing.rankPow true G π

/-- The pairing of two generators at their factor lists at an
evaluator, `Eval(Φ̄_A Φ_B)`: the conjugated key — the daggers
flipped, the wiring transposed — against the second at the
concatenated site; the evaluator the site's own, `evalPhi` at the
variable count or a member engine. -/
def pairPhi (ev : states.FList → List Nat → poly.PPair)
    (Fa Fb : states.FList) (πa πb : List Nat) : poly.PPair :=
  ev (conjF Fa ++ Fb)
    (places.invPerm Fa.length πa ++ states.shiftW Fa.length πb)

/-- The pairing of two states at their factor lists at an
evaluator, the combinations' bilinear fold at the certified
reduction: `lem:genericlift`'s `pAddR` accumulates, so the
representative moves to the descent's own at every term and the
fold's value is the displayed sum's, `pReduce_read` the bridge. -/
def pairFull (ev : states.FList → List Nat → poly.PPair)
    (Fa Fb : states.FList) (a b : states.Comb) : poly.PPair :=
  a.foldl (fun acc ea => b.foldl (fun acc2 eb =>
    genericlift.pAddR acc2 (poly.pMul
      (poly.pMul ea.2 eb.2) (pairPhi ev Fa Fb ea.1 eb.1))) acc)
    poly.pZero

/-! `rem:kernel`'s gauge-mode tier: the evaluation's relabeling
read.  The states are indexed gauge-free by the multisets of
oriented cyclic words in the letters, so the positions of
repeated factors are a gauge mode of the `(π, positions)`
spelling; at the carried evaluation the sentence reads as the
contraction sum's one value at a letter-preserving relabeling of
the site and its wiring (`evalPhi_transport`).  The relabeling's
slot maps carry each letter's positions across (`slotOf`), the
doubled relabeling carries the composite graph's slots (`dbl`),
the two matchings travel with it (`mOne_transport`,
`wireAll_transport`), the composite's loop count is the wiring's
own at `places.cyclesOf_transport`, and the numerator's fold over
the tuples of the variables' words reindexes along the conjugated
words at the Weingarten column's own transport. -/
private theorem evenOdd : ∀ a b : Nat, ¬ 2 * a = 2 * b + 1
  | 0, _ => fun h => Nat.noConfusion h
  | _ + 1, 0 => fun h => Nat.noConfusion (Nat.succ.inj h)
  | a + 1, b + 1 => fun h =>
    evenOdd a b (Nat.succ.inj (Nat.succ.inj h))

/-- The doubling reads its factor back. -/
private theorem twoInj : ∀ a b : Nat, 2 * a = 2 * b → a = b
  | 0, 0 => fun _ => rfl
  | 0, _ + 1 => fun h => Nat.noConfusion h
  | _ + 1, 0 => fun h => Nat.noConfusion h
  | a + 1, b + 1 => fun h =>
    congrArg Nat.succ (twoInj a b (Nat.succ.inj (Nat.succ.inj h)))

/-- The doubled successor reads its factor back. -/
private theorem twoSuccInj (a b : Nat) (h : 2 * a + 1 = 2 * b + 1) :
    a = b := twoInj a b (Nat.succ.inj h)

/-- The doubling keeps the order. -/
private theorem twoMono : ∀ a b : Nat, a ≤ b → 2 * a ≤ 2 * b
  | 0, _, _ => Nat.zero_le _
  | a + 1, 0, h => absurd h (Nat.not_succ_le_zero a)
  | a + 1, b + 1, h =>
    Nat.succ_le_succ (Nat.succ_le_succ
      (twoMono a b (Nat.le_of_succ_le_succ h)))

/-- The doubling keeps the strict order. -/
private theorem twoLt {a b : Nat} (h : a < b) : 2 * a < 2 * b :=
  Nat.le_of_succ_le (twoMono (a + 1) b h)

/-- The doubled successor stays below the doubled bound. -/
private theorem twoSuccLt {a b : Nat} (h : a < b) :
    2 * a + 1 < 2 * b := twoMono (a + 1) b h

/-- The exchange fold: at each key of the walked list the two
named slots take each other's key. -/
private def wireFold (A B : Nat → Nat) (L : List Nat)
    (init : List Nat) : List Nat :=
  L.foldl (fun acc s => (acc.set (A s) (B s)).set (B s) (A s)) init

/-- The exchange fold keeps the slot list's place count. -/
private theorem wireFold_length (A B : Nat → Nat) :
    ∀ (L init : List Nat),
      (wireFold A B L init).length = init.length
  | [], _ => rfl
  | a :: t, init => by
    show (wireFold A B t
      ((init.set (A a) (B a)).set (B a) (A a))).length = init.length
    rw [wireFold_length A B t _,
      ground.length_set (A a) (init.set (A a) (B a)) (B a),
      ground.length_set (B a) init (A a)]

/-- A slot off every written pair keeps its prior read. -/
private theorem wireFold_off (A B : Nat → Nat) :
    ∀ (L init : List Nat) (x : Nat),
      (∀ s, 0 < ground.countOf s L → ¬ x = A s ∧ ¬ x = B s) →
      ground.getAt 0 (wireFold A B L init) x
        = ground.getAt 0 init x
  | [], _, _, _ => rfl
  | a :: t, init, x, h => by
    have hx := h a (by
      rw [ground.countOf_head]
      exact Nat.succ_pos _)
    show ground.getAt 0 (wireFold A B t
        ((init.set (A a) (B a)).set (B a) (A a))) x
      = ground.getAt 0 init x
    rw [wireFold_off A B t _ x (fun s hs => h s (by
        rw [ground.countOf_cons]
        exact Nat.lt_of_lt_of_le hs (Nat.le_add_left _ _))),
      ground.getAt_set_ne 0 (init.set (A a) (B a)) (B a) x (A a) hx.2,
      ground.getAt_set_ne 0 init (A a) x (B a) hx.1]

/-- A written pair's two slots read one another at the walked
key, the later keys' writes off them. -/
private theorem wireFold_read (A B : Nat → Nat) :
    ∀ (L init : List Nat),
      (∀ s, 0 < ground.countOf s L → A s < init.length) →
      (∀ s, 0 < ground.countOf s L → B s < init.length) →
      (∀ s, 0 < ground.countOf s L → ¬ A s = B s) →
      (∀ s t, 0 < ground.countOf s L → 0 < ground.countOf t L →
        ¬ s = t →
        ¬ A s = A t ∧ ¬ A s = B t ∧ ¬ B s = B t) →
      (∀ s, ground.countOf s L ≤ 1) →
      ∀ s, 0 < ground.countOf s L →
        ground.getAt 0 (wireFold A B L init) (A s) = B s
          ∧ ground.getAt 0 (wireFold A B L init) (B s) = A s
  | [], _, _, _, _, _, _, s, hs => absurd hs (Nat.lt_irrefl 0)
  | a :: t, init, hA, hB, hAB, hsep, hdist, s, hs => by
    have hhead : 0 < ground.countOf a (a :: t) := by
      rw [ground.countOf_head]
      exact Nat.succ_pos _
    have hat : ground.countOf a t = 0 := by
      have h1 := hdist a
      rw [ground.countOf_head] at h1
      exact Nat.le_zero.mp (Nat.le_of_succ_le_succ h1)
    have hup : ∀ z, 0 < ground.countOf z t →
        0 < ground.countOf z (a :: t) := fun z hz => by
      rw [ground.countOf_cons]
      exact Nat.lt_of_lt_of_le hz (Nat.le_add_left _ _)
    have hne : ∀ z, 0 < ground.countOf z t → ¬ z = a := fun z hz he => by
      rw [he, hat] at hz
      exact Nat.lt_irrefl 0 hz
    have hlen : ((init.set (A a) (B a)).set (B a) (A a)).length
        = init.length := by
      rw [ground.length_set (A a) (init.set (A a) (B a)) (B a),
        ground.length_set (B a) init (A a)]
    show ground.getAt 0 (wireFold A B t
        ((init.set (A a) (B a)).set (B a) (A a))) (A s) = B s
      ∧ ground.getAt 0 (wireFold A B t
        ((init.set (A a) (B a)).set (B a) (A a))) (B s) = A s
    by_cases hsa : s = a
    · rw [hsa]
      refine ⟨?_, ?_⟩
      · rw [wireFold_off A B t _ (A a) (fun z hz =>
          ⟨(hsep a z hhead (hup z hz) (fun he =>
              hne z hz he.symm)).1,
           (hsep a z hhead (hup z hz) (fun he =>
              hne z hz he.symm)).2.1⟩),
          ground.getAt_set_ne 0 (init.set (A a) (B a)) (B a) (A a)
            (A a) (hAB a hhead),
          ground.getAt_set_self 0 (B a) init (A a) (hA a hhead)]
      · rw [wireFold_off A B t _ (B a) (fun z hz =>
          ⟨fun he => (hsep z a (hup z hz) hhead (hne z hz)).2.1 he.symm,
           fun he => (hsep z a (hup z hz) hhead (hne z hz)).2.2 he.symm⟩),
          ground.getAt_set_self 0 (A a) (init.set (A a) (B a)) (B a)
            (by
              rw [ground.length_set (B a) init (A a)]
              exact hB a hhead)]
    · have hst : 0 < ground.countOf s t := by
        rw [ground.countOf_head_ne hsa] at hs
        exact hs
      exact wireFold_read A B t _
        (fun z hz => by
          rw [hlen]
          exact hA z (hup z hz))
        (fun z hz => by
          rw [hlen]
          exact hB z (hup z hz))
        (fun z hz => hAB z (hup z hz))
        (fun z w hz hw hzw =>
          hsep z w (hup z hz) (hup w hw) hzw)
        (fun z => Nat.le_trans (by
            rw [ground.countOf_cons]
            exact Nat.le_add_left _ _) (hdist z))
        s hst

/-- The letter's positions count: a key sits in the letter's
filter exactly where it is a place of the site reading that
letter. -/
private theorem posIf_count (G : states.FList) (f : states.Factor)
    (i : Nat) :
    ground.countOf i (posIf G f)
      = if ground.getAt (0, false) G i = f then
          (if i < G.length then 1 else 0) else 0 := by
  show ground.countOf i ((List.range G.length).filter
      (fun j => ground.getAt (0, false) G j == f)) = _
  rw [ground.countOf_filter
      (fun j => ground.getAt (0, false) G j == f) i
      (List.range G.length),
    ground.countOf_range i G.length]
  by_cases hf : ground.getAt (0, false) G i = f
  · rw [hf, ground.prodBeqIntro (fun a => ground.eqBeqOf (rfl : a = a))
      ground.boolEqBeq f, if_pos (rfl : f = f)]
    rfl
  · rw [ground.prodBeqRefuse (fun _ _ hh => ground.beqEqOf hh)
      (fun _ _ hh => ground.boolBeqEq hh) hf, if_neg hf]
    rfl

/-- A place reading the letter sits in the letter's positions. -/
private theorem posIf_mem {G : states.FList} {f : states.Factor}
    {i : Nat} (hi : i < G.length)
    (he : ground.getAt (0, false) G i = f) :
    0 < ground.countOf i (posIf G f) := by
  rw [posIf_count G f i, if_pos he, if_pos hi]
  exact Nat.succ_pos 0

/-- The letter's positions sit inside the site. -/
private theorem posIf_lt {G : states.FList} {f : states.Factor}
    {i : Nat} (h : 0 < ground.countOf i (posIf G f)) :
    i < G.length := by
  rw [posIf_count G f i] at h
  by_cases he : ground.getAt (0, false) G i = f
  · rw [if_pos he] at h
    by_cases hi : i < G.length
    · exact hi
    · rw [if_neg hi] at h
      exact absurd h (Nat.lt_irrefl 0)
  · rw [if_neg he] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- A position of the letter's filter reads that letter. -/
private theorem posIf_read {G : states.FList} {f : states.Factor}
    {i : Nat} (h : 0 < ground.countOf i (posIf G f)) :
    ground.getAt (0, false) G i = f := by
  by_cases he : ground.getAt (0, false) G i = f
  · exact he
  · rw [posIf_count G f i, if_neg he] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- The letter's positions are distinct. -/
private theorem posIf_dist (G : states.FList) (f : states.Factor)
    (i : Nat) : ground.countOf i (posIf G f) ≤ 1 := by
  rw [posIf_count G f i]
  by_cases he : ground.getAt (0, false) G i = f
  · rw [if_pos he]
    by_cases hi : i < G.length
    · rw [if_pos hi]
      exact Nat.le_refl 1
    · rw [if_neg hi]
      exact Nat.le_of_lt (Nat.succ_pos 0)
  · rw [if_neg he]
    exact Nat.le_of_lt (Nat.succ_pos 0)

/-- The position list's entry sits inside the site. -/
private theorem posIf_entry_lt (G : states.FList)
    (f : states.Factor) (s : Nat) (hs : s < (posIf G f).length) :
    ground.getAt 0 (posIf G f) s < G.length :=
  posIf_lt (ground.countOf_getAt_pos 0 (posIf G f) s hs)

/-- The position list's entry reads its own letter. -/
private theorem posIf_entry_read (G : states.FList)
    (f : states.Factor) (s : Nat) (hs : s < (posIf G f).length) :
    ground.getAt (0, false) G (ground.getAt 0 (posIf G f) s)
      = f :=
  posIf_read (ground.countOf_getAt_pos 0 (posIf G f) s hs)

/-- The position list reads its slots injectively. -/
private theorem posIf_inj (G : states.FList) (f : states.Factor) :
    ∀ s t, s < (posIf G f).length → t < (posIf G f).length →
      ground.getAt 0 (posIf G f) s = ground.getAt 0 (posIf G f) t →
      s = t :=
  ground.getAt_inj_distinct 0 (posIf G f)
    (fun x _ => posIf_dist G f x)

/-- Two letters' position lists are disjoint. -/
private theorem posIf_class_ne (G : states.FList)
    {f g : states.Factor} (hfg : ¬ f = g) {i j : Nat}
    (hi : 0 < ground.countOf i (posIf G f))
    (hj : 0 < ground.countOf j (posIf G g)) : ¬ i = j := fun he =>
  hfg (by
    rw [← posIf_read hi, he, posIf_read hj])

/-- The relabeled site's letter positions are no more numerous
than the site's own: the relabeling injects the one filter's
entries into the other's. -/
private theorem posIf_len_le (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (f : states.Factor) :
    (posIf G' f).length ≤ (posIf G f).length := by
  obtain ⟨hrlen, _, hrval, _⟩ := places.perm_member_reads hr
  have hrlt : ∀ i, i < m → ground.getAt 0 ρ i < m := fun i hi =>
    hrval _ (ground.countOf_getAt_pos 0 ρ i (by
      rw [hrlen]
      exact hi))
  have hmap : ∀ s, s < (posIf G' f).length →
      ground.getAt 0 ((posIf G' f).map (ground.getAt 0 ρ)) s
        = ground.getAt 0 ρ (ground.getAt 0 (posIf G' f) s) :=
    fun s hs => ground.getAt_map 0 0 (ground.getAt 0 ρ)
      (posIf G' f) s hs
  have hlenL : ((posIf G' f).map (ground.getAt 0 ρ)).length
      = (posIf G' f).length := ground.length_map _ (posIf G' f)
  have hdistL : ∀ x,
      ground.countOf x ((posIf G' f).map (ground.getAt 0 ρ)) ≤ 1 := by
    refine ground.distinctList_all
      (ground.distinct_of_getAt_inj 0 _ ?_)
    intro p q hp hq he
    rw [hlenL] at hp hq
    rw [hmap p hp, hmap q hq] at he
    refine posIf_inj G' f p q hp hq ?_
    refine places.perm_inj m hr _ _ ?_ ?_ he
    · rw [← hm']
      exact posIf_entry_lt G' f p hp
    · rw [← hm']
      exact posIf_entry_lt G' f q hq
  have hcov : ∀ x ∈ (posIf G' f).map (ground.getAt 0 ρ),
      x ∈ posIf G f := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := ground.mem_map_of (ground.getAt 0 ρ)
      (posIf G' f) x hx
    have hac := ground.countOf_pos_of_mem ha
    have halt : a < m := by
      rw [← hm']
      exact posIf_lt hac
    refine ground.mem_of_countOf_pos x _ ?_
    rw [← hax]
    refine posIf_mem ?_ ?_
    · rw [hm]
      exact hrlt a halt
    · rw [← hg a halt]
      exact posIf_read hac
  have hle := ground.length_le_of_distinct_mem
    ((posIf G' f).map (ground.getAt 0 ρ)) (posIf G f)
    hdistL hcov (fun x _ => posIf_dist G f x)
  rw [hlenL] at hle
  exact hle

/-- The relabeled site's letter positions match the site's own in
number. -/
private theorem posIf_len_eq (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (f : states.Factor) :
    (posIf G' f).length = (posIf G f).length := by
  refine Nat.le_antisymm (posIf_len_le G G' ρ m hm hm' hr hg f) ?_
  refine posIf_len_le G' G (places.invPerm m ρ) m hm' hm
    (places.invPerm_member m hr) (fun i hi => ?_) f
  rw [hg (ground.getAt 0 (places.invPerm m ρ) i)
      (perm_inv_lt m hr i hi),
    perm_right m hr i hi]

/-- The letter's slot map at a relabeling: the primed slot's place
carried across the relabeling and named back in the site's own
filter. -/
private def slotOf (G G' : states.FList) (ρ : List Nat)
    (f : states.Factor) : List Nat :=
  (List.range (posIf G' f).length).map (fun s =>
    places.posOf (ground.getAt 0 ρ
      (ground.getAt 0 (posIf G' f) s)) (posIf G f))

/-- The slot map's place count is the relabeled letter list's. -/
private theorem slotOf_length (G G' : states.FList) (ρ : List Nat)
    (f : states.Factor) :
    (slotOf G G' ρ f).length = (posIf G' f).length := by
  show ((List.range (posIf G' f).length).map _).length = _
  rw [ground.length_map, ground.length_range]

/-- The slot map's entry names the relabeled position's image in
the letter's own list. -/
private theorem slotOf_target (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (f : states.Factor) (s : Nat) (hs : s < (posIf G' f).length) :
    0 < ground.countOf (ground.getAt 0 ρ
      (ground.getAt 0 (posIf G' f) s)) (posIf G f) := by
  have hlt : ground.getAt 0 (posIf G' f) s < m := by
    rw [← hm']
    exact posIf_entry_lt G' f s hs
  refine posIf_mem ?_ ?_
  · rw [hm]
    exact perm_lt m hr _ hlt
  · rw [← hg _ hlt]
    exact posIf_entry_read G' f s hs

/-- The letter list's entry at a slot-map key is the relabeling's
image of the relabeled entry. -/
private theorem slotOf_read (G G' : states.FList) (ρ : List Nat)
    (f : states.Factor) (s : Nat) (hs : s < (posIf G' f).length) :
    ground.getAt 0 (slotOf G G' ρ f) s
      = places.posOf (ground.getAt 0 ρ
          (ground.getAt 0 (posIf G' f) s)) (posIf G f) := by
  show ground.getAt 0 ((List.range (posIf G' f).length).map
      (fun t => places.posOf (ground.getAt 0 ρ
        (ground.getAt 0 (posIf G' f) t)) (posIf G f))) s = _
  rw [ground.getAt_map_range 0 _ (posIf G' f).length s, if_pos hs]

/-- The slot map's entries sit inside the letter's list. -/
private theorem slotOf_lt (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (f : states.Factor) (s : Nat) (hs : s < (posIf G' f).length) :
    ground.getAt 0 (slotOf G G' ρ f) s < (posIf G f).length := by
  rw [slotOf_read G G' ρ f s hs]
  exact places.posOf_lt _ (posIf G f)
    (slotOf_target G G' ρ m hm hm' hr hg f s hs)

/-- The slot map reads its slots injectively. -/
private theorem slotOf_getAt (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (f : states.Factor) (s : Nat) (hs : s < (posIf G' f).length) :
    ground.getAt 0 (posIf G f)
        (ground.getAt 0 (slotOf G G' ρ f) s)
      = ground.getAt 0 ρ (ground.getAt 0 (posIf G' f) s) := by
  rw [slotOf_read G G' ρ f s hs]
  exact places.getAt_posOf _ (posIf G f)
    (slotOf_target G G' ρ m hm hm' hr hg f s hs)

/-- The letter's slot map is a place enumeration member at the
letter's position count. -/
private theorem slotOf_member (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (f : states.Factor) :
    0 < ground.countOf (slotOf G G' ρ f)
      (places.perms (posIf G f).length) := by
  have hlen : (slotOf G G' ρ f).length = (posIf G f).length := by
    rw [slotOf_length, posIf_len_eq G G' ρ m hm hm' hr hg f]
  refine places.perm_of_reads _ _ hlen (fun s hs => ?_)
    (fun s t hs ht he => ?_)
  · refine slotOf_lt G G' ρ m hm hm' hr hg f s ?_
    rw [posIf_len_eq G G' ρ m hm hm' hr hg f]
    exact hs
  · have hs' : s < (posIf G' f).length := by
      rw [posIf_len_eq G G' ρ m hm hm' hr hg f]
      exact hs
    have ht' : t < (posIf G' f).length := by
      rw [posIf_len_eq G G' ρ m hm hm' hr hg f]
      exact ht
    have h2 : ground.getAt 0 ρ (ground.getAt 0 (posIf G' f) s)
        = ground.getAt 0 ρ (ground.getAt 0 (posIf G' f) t) := by
      rw [← slotOf_getAt G G' ρ m hm hm' hr hg f s hs',
        ← slotOf_getAt G G' ρ m hm hm' hr hg f t ht', he]
    refine posIf_inj G' f s t hs' ht' ?_
    refine places.perm_inj m hr _ _ ?_ ?_ h2
    · rw [← hm']
      exact posIf_entry_lt G' f s hs'
    · rw [← hm']
      exact posIf_entry_lt G' f t ht'

/-- Every slot halves to a place at one of the two parities. -/
private theorem halveOf : ∀ x : Nat, ∃ s, x = 2 * s ∨ x = 2 * s + 1
  | 0 => ⟨0, Or.inl rfl⟩
  | 1 => ⟨0, Or.inr rfl⟩
  | x + 2 =>
    match halveOf x with
    | ⟨s, Or.inl h⟩ => ⟨s + 1, Or.inl (by
        rw [h, Nat.mul_succ])⟩
    | ⟨s, Or.inr h⟩ => ⟨s + 1, Or.inr (by
        rw [h, Nat.mul_succ])⟩

/-- A slot below the doubled width halves inside the width. -/
private theorem halveLt {x m : Nat} (h : x < 2 * m) :
    ∃ s, s < m ∧ (x = 2 * s ∨ x = 2 * s + 1) := by
  obtain ⟨s, hs⟩ := halveOf x
  refine ⟨s, ?_, hs⟩
  match Nat.lt_or_ge s m with
  | .inl hlt => exact hlt
  | .inr hge =>
    exfalso
    have hbig : 2 * m ≤ x := by
      match hs with
      | Or.inl he =>
        rw [he]
        exact twoMono m s hge
      | Or.inr he =>
        rw [he]
        exact Nat.le_trans (twoMono m s hge) (Nat.le_succ _)
    exact absurd (Nat.lt_of_lt_of_le h hbig) (Nat.lt_irrefl _)

/-- The relabeling doubled at the slots: each place's two slots
carried to the image place's two. -/
private def dbl (ρ : List Nat) : List Nat :=
  ρ.flatMap (fun v => [2 * v, 2 * v + 1])

/-- The doubled relabeling's place count is the doubled one. -/
private theorem dbl_length : ∀ l : List Nat,
    (dbl l).length = 2 * l.length
  | [] => rfl
  | a :: t => by
    show ([2 * a, 2 * a + 1] ++ dbl t).length = 2 * (t.length + 1)
    rw [ground.length_append, dbl_length t, Nat.mul_succ]
    show 2 + 2 * t.length = 2 * t.length + 2
    rw [Nat.add_comm 2 (2 * t.length)]

/-- The doubled relabeling reads the doubled entry at an even
slot. -/
private theorem dbl_read : ∀ (l : List Nat) (s : Nat),
    s < l.length →
      ground.getAt 0 (dbl l) (2 * s) = 2 * ground.getAt 0 l s
      ∧ ground.getAt 0 (dbl l) (2 * s + 1)
          = 2 * ground.getAt 0 l s + 1
  | [], s, h => absurd h (Nat.not_lt_zero s)
  | _ :: _, 0, _ => ⟨rfl, rfl⟩
  | _ :: t, s + 1, h => by
    show ground.getAt 0 (dbl t) (2 * s) = 2 * ground.getAt 0 t s
      ∧ ground.getAt 0 (dbl t) (2 * s + 1)
          = 2 * ground.getAt 0 t s + 1
    exact dbl_read t s (Nat.lt_of_succ_lt_succ h)

/-- The doubled relabeling is a slot enumeration member. -/
private theorem dbl_member (m : Nat) {ρ : List Nat}
    (hr : 0 < ground.countOf ρ (places.perms m)) :
    0 < ground.countOf (dbl ρ) (places.perms (2 * m)) := by
  obtain ⟨hlen, _, _, _⟩ := places.perm_member_reads hr
  refine places.perm_of_reads _ _ (by
      rw [dbl_length, hlen]) (fun x hx => ?_) (fun x y hx hy he => ?_)
  · obtain ⟨s, hs, hxs⟩ := halveLt hx
    have hrl := dbl_read ρ s (by
      rw [hlen]
      exact hs)
    match hxs with
    | Or.inl h1 =>
      rw [h1, hrl.1]
      exact twoLt (perm_lt m hr s hs)
    | Or.inr h1 =>
      rw [h1, hrl.2]
      exact twoSuccLt (perm_lt m hr s hs)
  · obtain ⟨s, hs, hxs⟩ := halveLt hx
    obtain ⟨t, ht, hyt⟩ := halveLt hy
    have hrs := dbl_read ρ s (by
      rw [hlen]
      exact hs)
    have hrt := dbl_read ρ t (by
      rw [hlen]
      exact ht)
    have hst : ground.getAt 0 ρ s = ground.getAt 0 ρ t → s = t :=
      fun h2 => places.perm_inj m hr s t hs ht h2
    match hxs, hyt with
    | Or.inl h1, Or.inl h2 =>
      rw [h1, hrs.1] at he
      rw [h2, hrt.1] at he
      rw [h1, h2, hst (twoInj _ _ he)]
    | Or.inl h1, Or.inr h2 =>
      rw [h1, hrs.1] at he
      rw [h2, hrt.2] at he
      exact absurd he (evenOdd _ _)
    | Or.inr h1, Or.inl h2 =>
      rw [h1, hrs.2] at he
      rw [h2, hrt.1] at he
      exact absurd he.symm (evenOdd _ _)
    | Or.inr h1, Or.inr h2 =>
      rw [h1, hrs.2] at he
      rw [h2, hrt.2] at he
      rw [h1, h2, hst (twoSuccInj _ _ he)]

/-- A value below two is one of the two parities. -/
private theorem ltTwo : ∀ x : Nat, x < 2 → x = 0 ∨ x = 1
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr rfl
  | x + 2, h =>
    absurd (Nat.lt_of_lt_of_le h (Nat.le_add_left 2 x))
      (Nat.lt_irrefl _)

/-- A slot at a fixed parity reads its place back. -/
private theorem offInj : ∀ (o a b : Nat),
    2 * a + o = 2 * b + o → a = b
  | 0, a, b, h => twoInj a b h
  | o + 1, a, b, h => offInj o a b (Nat.succ.inj h)

/-- Slots at distinct parities differ. -/
private theorem offNe {a b oP oQ : Nat} (hoP : oP < 2)
    (hoQ : oQ < 2) (hne : ¬ oP = oQ) :
    ¬ 2 * a + oP = 2 * b + oQ := by
  match ltTwo oP hoP, ltTwo oQ hoQ with
  | Or.inl h1, Or.inl h2 => exact absurd (h1.trans h2.symm) hne
  | Or.inl h1, Or.inr h2 =>
    rw [h1, h2]
    exact evenOdd a b
  | Or.inr h1, Or.inl h2 =>
    rw [h1, h2]
    exact fun he => evenOdd b a he.symm
  | Or.inr h1, Or.inr h2 => exact absurd (h1.trans h2.symm) hne

/-- The key range is distinct. -/
private theorem rangeDist (s m : Nat) :
    ground.countOf s (List.range m) ≤ 1 :=
  ground.distinctList_all (ground.distinctList_range m) s

/-- The matching keeps the slot list's place count. -/
private theorem matchIn_length (m2 ps qs σ : List Nat)
    (offP offQ : Nat) :
    (matchIn m2 ps qs σ offP offQ).length = m2.length :=
  wireFold_length (fun s => 2 * ground.getAt 0 ps s + offP)
    (fun s => 2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ)
    (List.range ps.length) m2

/-- A slot off the matching's write set keeps its prior read. -/
private theorem matchIn_off (m2 ps qs σ : List Nat)
    (offP offQ x : Nat)
    (h : ∀ s, s < ps.length →
      ¬ x = 2 * ground.getAt 0 ps s + offP
      ∧ ¬ x = 2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ) :
    ground.getAt 0 (matchIn m2 ps qs σ offP offQ) x
      = ground.getAt 0 m2 x :=
  wireFold_off (fun s => 2 * ground.getAt 0 ps s + offP)
    (fun s => 2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ)
    (List.range ps.length) m2 x (fun s hs => h s (ground.ltOfMem hs))

/-- The matching's written pair reads both ways at each walked
slot. -/
private theorem matchIn_read (m2 ps qs σ : List Nat)
    (offP offQ : Nat)
    (hps : ∀ s, s < ps.length →
      2 * ground.getAt 0 ps s + offP < m2.length)
    (hqs : ∀ s, s < ps.length →
      2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ < m2.length)
    (hoP : offP < 2) (hoQ : offQ < 2) (hoff : ¬ offP = offQ)
    (hpinj : ∀ s t, s < ps.length → t < ps.length →
      ground.getAt 0 ps s = ground.getAt 0 ps t → s = t)
    (hqinj : ∀ s t, s < ps.length → t < ps.length →
      ground.getAt 0 qs (ground.getAt 0 σ s)
        = ground.getAt 0 qs (ground.getAt 0 σ t) → s = t)
    (s : Nat) (hs : s < ps.length) :
    ground.getAt 0 (matchIn m2 ps qs σ offP offQ)
        (2 * ground.getAt 0 ps s + offP)
      = 2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ
    ∧ ground.getAt 0 (matchIn m2 ps qs σ offP offQ)
        (2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ)
      = 2 * ground.getAt 0 ps s + offP :=
  wireFold_read (fun t => 2 * ground.getAt 0 ps t + offP)
    (fun t => 2 * ground.getAt 0 qs (ground.getAt 0 σ t) + offQ)
    (List.range ps.length) m2
    (fun t ht => hps t (ground.ltOfMem ht))
    (fun t ht => hqs t (ground.ltOfMem ht))
    (fun _ _ => offNe hoP hoQ hoff)
    (fun t u ht hu htu =>
      ⟨fun he => htu (hpinj t u (ground.ltOfMem ht) (ground.ltOfMem hu)
          (offInj offP _ _ he)),
       offNe hoP hoQ hoff,
       fun he => htu (hqinj t u (ground.ltOfMem ht) (ground.ltOfMem hu)
          (offInj offQ _ _ he))⟩)
    (fun t => rangeDist t ps.length) s
    (ground.countOf_range_pos hs)

/-- The wiring's matching reads the image's column slot at a
place's row slot and back. -/
private theorem mOne_read (m : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (places.perms m)) (i : Nat)
    (hi : i < m) :
    ground.getAt 0 (mOne m π) (2 * i)
        = 2 * ground.getAt 0 π i + 1
      ∧ ground.getAt 0 (mOne m π) (2 * ground.getAt 0 π i + 1)
        = 2 * i := by
  have hrep : (List.replicate (2 * m) 0).length = 2 * m :=
    ground.length_replicate 0 (2 * m)
  show ground.getAt 0 (wireFold (fun t => 2 * t)
      (fun t => 2 * ground.getAt 0 π t + 1) (List.range m)
      (List.replicate (2 * m) 0)) (2 * i)
      = 2 * ground.getAt 0 π i + 1
    ∧ ground.getAt 0 (wireFold (fun t => 2 * t)
      (fun t => 2 * ground.getAt 0 π t + 1) (List.range m)
      (List.replicate (2 * m) 0))
      (2 * ground.getAt 0 π i + 1) = 2 * i
  refine wireFold_read (fun t => 2 * t)
    (fun t => 2 * ground.getAt 0 π t + 1) (List.range m)
    (List.replicate (2 * m) 0) (fun t ht => ?_) (fun t ht => ?_)
    (fun _ _ => evenOdd _ _) (fun t u ht hu htu => ⟨?_, ?_, ?_⟩)
    (fun t => rangeDist t m) i (ground.countOf_range_pos hi)
  · rw [hrep]
    exact twoLt (ground.ltOfMem ht)
  · rw [hrep]
    exact twoSuccLt (perm_lt m hπ t (ground.ltOfMem ht))
  · exact fun he => htu (twoInj t u he)
  · exact evenOdd _ _
  · exact fun he => htu (places.perm_inj m hπ t u (ground.ltOfMem ht)
      (ground.ltOfMem hu) (twoSuccInj _ _ he))

/-- Slots of distinct letters' positions differ at every
parity pair. -/
private theorem slotNeClass (G : states.FList) {f g : states.Factor}
    (hfg : ¬ f = g) {a b oa ob : Nat} (hoa : oa < 2) (hob : ob < 2)
    (ha : a < (posIf G f).length) (hb : b < (posIf G g).length) :
    ¬ 2 * ground.getAt 0 (posIf G f) a + oa
      = 2 * ground.getAt 0 (posIf G g) b + ob := by
  by_cases ho : oa = ob
  · rw [ho]
    intro he
    exact posIf_class_ne G hfg
      (ground.countOf_getAt_pos 0 (posIf G f) a ha)
      (ground.countOf_getAt_pos 0 (posIf G g) b hb)
      (offInj ob _ _ he)
  · exact offNe hoa hob ho

/-- Slots differ at a distinct letter or a distinct parity. -/
private theorem slotNeOr (G : states.FList) {f g : states.Factor}
    {a b oa ob : Nat} (hoa : oa < 2) (hob : ob < 2)
    (h : ¬ f = g ∨ ¬ oa = ob)
    (ha : a < (posIf G f).length)
    (hb : b < (posIf G g).length) :
    ¬ 2 * ground.getAt 0 (posIf G f) a + oa
      = 2 * ground.getAt 0 (posIf G g) b + ob := by
  match h with
  | Or.inl hfg => exact slotNeClass G hfg hoa hob ha hb
  | Or.inr hne => exact offNe hoa hob hne

/-- A slot the call does not write keeps its prior value: the
letter classes and the parities separate the call's write set. -/
private theorem matchIn_off_slot (G : states.FList) (acc : List Nat)
    (f g h : states.Factor) (σ : List Nat)
    (hσ : ∀ s, s < (posIf G g).length →
      ground.getAt 0 σ s < (posIf G h).length)
    (oP oQ oa : Nat) (hoP : oP < 2) (hoQ : oQ < 2) (hoa : oa < 2)
    (hP : ¬ f = g ∨ ¬ oa = oP) (hQ : ¬ f = h ∨ ¬ oa = oQ)
    (a : Nat) (ha : a < (posIf G f).length) :
    ground.getAt 0 (matchIn acc (posIf G g) (posIf G h) σ oP oQ)
        (2 * ground.getAt 0 (posIf G f) a + oa)
      = ground.getAt 0 acc
        (2 * ground.getAt 0 (posIf G f) a + oa) :=
  matchIn_off acc (posIf G g) (posIf G h) σ oP oQ _ (fun s hs =>
    ⟨slotNeOr G hoa hoP hP ha hs,
     slotNeOr G hoa hoQ hQ ha (hσ s hs)⟩)

/-- A position's slot sits below the doubled site. -/
private theorem slotLt (G : states.FList) (f : states.Factor)
    (a o : Nat) (ho : o < 2) (ha : a < (posIf G f).length) :
    2 * ground.getAt 0 (posIf G f) a + o < 2 * G.length := by
  have he := posIf_entry_lt G f a ha
  match ltTwo o ho with
  | Or.inl h0 =>
    rw [h0]
    exact twoLt he
  | Or.inr h1 =>
    rw [h1]
    exact twoSuccLt he

/-- The matched image's slot sits below the doubled site. -/
private theorem sigLt (G : states.FList) (g h : states.Factor)
    {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms (posIf G g).length))
    (hgh : (posIf G g).length = (posIf G h).length) :
    ∀ s, s < (posIf G g).length →
      ground.getAt 0 σ s < (posIf G h).length := fun s hs => by
  rw [← hgh]
  exact perm_lt _ hσ s hs

/-- The matched column ends read their slots injectively. -/
private theorem qsInj (G : states.FList) (g h : states.Factor)
    {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms (posIf G g).length))
    (hgh : (posIf G g).length = (posIf G h).length) :
    ∀ s t, s < (posIf G g).length → t < (posIf G g).length →
      ground.getAt 0 (posIf G h) (ground.getAt 0 σ s)
        = ground.getAt 0 (posIf G h) (ground.getAt 0 σ t) →
      s = t := fun s t hs ht he =>
  places.perm_inj _ hσ s t hs ht
    (posIf_inj G h _ _ (sigLt G g h hσ hgh s hs)
      (sigLt G g h hσ hgh t ht) he)

/-- The doubled relabeling reads the relabeled position's even
slot to the position's own. -/
private theorem dblEven (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (f : states.Factor) (s : Nat) (hs : s < (posIf G' f).length) :
    ground.getAt 0 (dbl ρ) (2 * ground.getAt 0 (posIf G' f) s)
      = 2 * ground.getAt 0 (posIf G f)
          (ground.getAt 0 (slotOf G G' ρ f) s) := by
  have hd := dbl_read ρ (ground.getAt 0 (posIf G' f) s) (by
    rw [(places.perm_member_reads hr).1, ← hm']
    exact posIf_entry_lt G' f s hs)
  rw [hd.1, slotOf_getAt G G' ρ m hm hm' hr hg f s hs]

/-- The doubled relabeling reads the relabeled position's odd
slot to the position's own. -/
private theorem dblOdd (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (f : states.Factor) (s : Nat) (hs : s < (posIf G' f).length) :
    ground.getAt 0 (dbl ρ) (2 * ground.getAt 0 (posIf G' f) s + 1)
      = 2 * ground.getAt 0 (posIf G f)
          (ground.getAt 0 (slotOf G G' ρ f) s) + 1 := by
  have hd := dbl_read ρ (ground.getAt 0 (posIf G' f) s) (by
    rw [(places.perm_member_reads hr).1, ← hm']
    exact posIf_entry_lt G' f s hs)
  rw [hd.2, slotOf_getAt G G' ρ m hm hm' hr hg f s hs]

/-- The wiring's first matching travels the relabeling: the
doubled relabeling carries the relabeled wiring's slot reads to
the wiring's own. -/
private theorem mOne_transport (m : Nat) (π π' ρ : List Nat)
    (hπ : 0 < ground.countOf π (places.perms m))
    (hπ' : 0 < ground.countOf π' (places.perms m))
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hc : ∀ s, s < m →
      ground.getAt 0 ρ (ground.getAt 0 π' s)
        = ground.getAt 0 π (ground.getAt 0 ρ s))
    (x : Nat) (hx : x < 2 * m) :
    ground.getAt 0 (dbl ρ) (ground.getAt 0 (mOne m π') x)
      = ground.getAt 0 (mOne m π) (ground.getAt 0 (dbl ρ) x) := by
  have hrlen := (places.perm_member_reads hr).1
  obtain ⟨s, hs, hsx⟩ := halveLt hx
  have hdr := dbl_read ρ s (by
    rw [hrlen]
    exact hs)
  match hsx with
  | Or.inl hev =>
    rw [hev, (mOne_read m hπ' s hs).1, hdr.1,
      (dbl_read ρ (ground.getAt 0 π' s) (by
        rw [hrlen]
        exact perm_lt m hπ' s hs)).2,
      (mOne_read m hπ (ground.getAt 0 ρ s) (perm_lt m hr s hs)).1,
      hc s hs]
  | Or.inr hod =>
    have ht : ground.getAt 0 (places.invPerm m π') s < m :=
      perm_inv_lt m hπ' s hs
    have hpt : ground.getAt 0 π'
        (ground.getAt 0 (places.invPerm m π') s) = s :=
      perm_right m hπ' s hs
    have hu : ground.getAt 0 (places.invPerm m π)
        (ground.getAt 0 ρ s) < m :=
      perm_inv_lt m hπ (ground.getAt 0 ρ s) (perm_lt m hr s hs)
    have hpu : ground.getAt 0 π (ground.getAt 0 (places.invPerm m π)
        (ground.getAt 0 ρ s)) = ground.getAt 0 ρ s :=
      perm_right m hπ (ground.getAt 0 ρ s) (perm_lt m hr s hs)
    have hL := (mOne_read m hπ' _ ht).2
    rw [hpt] at hL
    have hR := (mOne_read m hπ _ hu).2
    rw [hpu] at hR
    have hkey : ground.getAt 0 ρ
          (ground.getAt 0 (places.invPerm m π') s)
        = ground.getAt 0 (places.invPerm m π)
          (ground.getAt 0 ρ s) := by
      refine places.perm_inj m hπ _ _ (perm_lt m hr _ ht) hu ?_
      rw [← hc _ ht, hpt, hpu]
    rw [hod, hL, hdr.2, hR,
      (dbl_read ρ _ (by
        rw [hrlen]
        exact ht)).1, hkey]

/-- A bounded write keeps the entries' bound. -/
private theorem set_bound (N : Nat) (l : List Nat) (p q : Nat)
    (hl : ∀ x, x < l.length → ground.getAt 0 l x < N) (hq : q < N) :
    ∀ x, x < (l.set p q).length → ground.getAt 0 (l.set p q) x < N := by
  intro x hx
  rw [ground.length_set q l p] at hx
  by_cases hxp : x = p
  · rw [hxp, ground.getAt_set_self 0 q l p (by
      rw [← hxp]
      exact hx)]
    exact hq
  · rw [ground.getAt_set_ne 0 l p x q hxp]
    exact hl x hx

/-- The exchange fold keeps a bound written throughout. -/
private theorem wireFold_bound (A B : Nat → Nat) (N : Nat) :
    ∀ (L init : List Nat),
      (∀ s, 0 < ground.countOf s L → A s < N) →
      (∀ s, 0 < ground.countOf s L → B s < N) →
      (∀ x, x < init.length → ground.getAt 0 init x < N) →
      ∀ x, x < init.length →
        ground.getAt 0 (wireFold A B L init) x < N
  | [], _, _, _, hi, x, hx => hi x hx
  | a :: t, init, hA, hB, hi, x, hx => by
    have hhead : 0 < ground.countOf a (a :: t) := by
      rw [ground.countOf_head]
      exact Nat.succ_pos _
    have hup : ∀ z, 0 < ground.countOf z t →
        0 < ground.countOf z (a :: t) := fun z hz => by
      rw [ground.countOf_cons]
      exact Nat.lt_of_lt_of_le hz (Nat.le_add_left _ _)
    have hlen : ((init.set (A a) (B a)).set (B a) (A a)).length
        = init.length := by
      rw [ground.length_set (A a) (init.set (A a) (B a)) (B a),
        ground.length_set (B a) init (A a)]
    show ground.getAt 0 (wireFold A B t
      ((init.set (A a) (B a)).set (B a) (A a))) x < N
    refine wireFold_bound A B N t _ (fun z hz => hA z (hup z hz))
      (fun z hz => hB z (hup z hz)) ?_ x (by
        rw [hlen]
        exact hx)
    refine set_bound N (init.set (A a) (B a)) (B a) (A a) ?_
      (hA a hhead)
    exact set_bound N init (A a) (B a) hi (hB a hhead)

/-- The matching keeps the slot entries' bound. -/
private theorem matchIn_bound (m2 ps qs σ : List Nat)
    (offP offQ N : Nat)
    (hps : ∀ s, s < ps.length →
      2 * ground.getAt 0 ps s + offP < N)
    (hqs : ∀ s, s < ps.length →
      2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ < N)
    (hm2 : ∀ x, x < m2.length → ground.getAt 0 m2 x < N) :
    ∀ x, x < m2.length →
      ground.getAt 0 (matchIn m2 ps qs σ offP offQ) x < N :=
  wireFold_bound (fun s => 2 * ground.getAt 0 ps s + offP)
    (fun s => 2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ) N
    (List.range ps.length) m2
    (fun s hs => hps s (ground.ltOfMem hs))
    (fun s hs => hqs s (ground.ltOfMem hs)) hm2

/-- The vacant slot list's entries sit below any occupied
bound. -/
private theorem replicate_bound (N : Nat) :
    ∀ x, x < (List.replicate N (0 : Nat)).length →
      ground.getAt 0 (List.replicate N 0) x < N := by
  intro x hx
  rw [ground.length_replicate] at hx
  rw [ground.getAt_replicate 0 0 N x hx]
  exact Nat.lt_of_le_of_lt (Nat.zero_le x) hx

/-- The wiring's matching keeps the doubled bound. -/
private theorem mOne_bound (m : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (places.perms m)) :
    ∀ x, x < 2 * m → ground.getAt 0 (mOne m π) x < 2 * m := by
  intro x hx
  show ground.getAt 0 (wireFold (fun t => 2 * t)
    (fun t => 2 * ground.getAt 0 π t + 1) (List.range m)
    (List.replicate (2 * m) 0)) x < 2 * m
  refine wireFold_bound _ _ (2 * m) (List.range m)
    (List.replicate (2 * m) 0)
    (fun t ht => twoLt (ground.ltOfMem ht))
    (fun t ht => twoSuccLt (perm_lt m hπ t (ground.ltOfMem ht)))
    (replicate_bound (2 * m)) x ?_
  rw [ground.length_replicate]
  exact hx

/-- The wiring's matching is its own partner slot by slot. -/
private theorem mOne_invol (m : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (places.perms m)) (x : Nat)
    (hx : x < 2 * m) :
    ground.getAt 0 (mOne m π) (ground.getAt 0 (mOne m π) x) = x := by
  obtain ⟨s, hs, hsx⟩ := halveLt hx
  match hsx with
  | Or.inl hev =>
    rw [hev, (mOne_read m hπ s hs).1, (mOne_read m hπ s hs).2]
  | Or.inr hod =>
    have ht : ground.getAt 0 (places.invPerm m π) s < m :=
      perm_inv_lt m hπ s hs
    have hpt : ground.getAt 0 π
        (ground.getAt 0 (places.invPerm m π) s) = s :=
      perm_right m hπ s hs
    have h1 := (mOne_read m hπ _ ht).2
    have h2 := (mOne_read m hπ _ ht).1
    rw [hpt] at h1 h2
    rw [hod, h1, h2]

/-- The relabeled slot word: a slot permutation conjugated by the
two classes' slot maps. -/
private def conjBy (k : Nat) (a b σ : List Nat) : List Nat :=
  places.expo (places.expo b σ) (places.invPerm k a)

/-- The composed permutation's place count is the width. -/
private theorem conjBy_length (k : Nat) (a b σ : List Nat) :
    (conjBy k a b σ).length = k := by
  show ((places.invPerm k a).map
    (ground.getAt 0 (places.expo b σ))).length = k
  rw [ground.length_map, places.length_invPerm]

/-- The composed permutation's entry, read at the three
factors. -/
private theorem conjBy_read (k : Nat) {a b σ : List Nat}
    (ha : 0 < ground.countOf a (places.perms k))
    (hσ : 0 < ground.countOf σ (places.perms k)) (i : Nat)
    (hi : i < k) :
    ground.getAt 0 (conjBy k a b σ) i
      = ground.getAt 0 b (ground.getAt 0 σ
          (ground.getAt 0 (places.invPerm k a) i)) := by
  show ground.getAt 0 (places.expo (places.expo b σ)
    (places.invPerm k a)) i = _
  rw [places.getAt_expo (places.expo b σ) (places.invPerm k a) i
      (by
        rw [places.length_invPerm]
        exact hi),
    places.getAt_expo b σ _ (by
      rw [(places.perm_member_reads hσ).1]
      exact perm_inv_lt k ha i hi)]

/-- The composed permutation is an enumeration member. -/
private theorem conjBy_member (k : Nat) {a b σ : List Nat}
    (ha : 0 < ground.countOf a (places.perms k))
    (hb : 0 < ground.countOf b (places.perms k))
    (hσ : 0 < ground.countOf σ (places.perms k)) :
    0 < ground.countOf (conjBy k a b σ) (places.perms k) :=
  places.expo_member k (places.expo_member k hb hσ)
    (places.invPerm_member k ha)

/-- The conjugate's defining read: the slot maps carry the word
across. -/
private theorem conjBy_rel (k : Nat) {a b σ : List Nat}
    (ha : 0 < ground.countOf a (places.perms k))
    (hσ : 0 < ground.countOf σ (places.perms k)) (s : Nat)
    (hs : s < k) :
    ground.getAt 0 b (ground.getAt 0 σ s)
      = ground.getAt 0 (conjBy k a b σ) (ground.getAt 0 a s) := by
  rw [conjBy_read k ha hσ _ (perm_lt k ha s hs), perm_left k ha s hs]

/-- The composition at the partner factors reads the permutation
back. -/
private theorem conjBy_inv (k : Nat) {a b σ : List Nat}
    (ha : 0 < ground.countOf a (places.perms k))
    (hb : 0 < ground.countOf b (places.perms k))
    (hσ : 0 < ground.countOf σ (places.perms k)) :
    conjBy k (places.invPerm k a) (places.invPerm k b)
      (conjBy k a b σ) = σ := by
  refine ground.getAt_ext 0 _ _ (by
      rw [conjBy_length, (places.perm_member_reads hσ).1]) ?_
  intro i hi
  rw [conjBy_length] at hi
  rw [conjBy_read k (places.invPerm_member k ha)
      (conjBy_member k ha hb hσ) i hi,
    places.invPerm_invPerm k ha,
    conjBy_read k ha hσ _ (perm_lt k ha i hi),
    perm_left k ha i hi, perm_left k hb _
      (perm_lt k hσ i hi)]

/-- The pair's composite travels the conjugation: the conjugated
words' composite is the composite's own conjugate. -/
private theorem expo_conj (k : Nat) {a b σ' τ' : List Nat}
    (ha : 0 < ground.countOf a (places.perms k))
    (hb : 0 < ground.countOf b (places.perms k))
    (hσ' : 0 < ground.countOf σ' (places.perms k))
    (hτ' : 0 < ground.countOf τ' (places.perms k)) :
    places.expo σ' (places.invPerm k τ')
      = (places.invPerm k (places.invPerm k b)).map (fun j =>
          ground.getAt 0 (places.invPerm k b)
            (ground.getAt 0 (places.expo (conjBy k a b σ')
              (places.invPerm k (conjBy k a b τ'))) j)) := by
  have hσ := conjBy_member k ha hb hσ'
  have hτ := conjBy_member k ha hb hτ'
  refine ground.getAt_ext 0 _ _ (by
      rw [ground.length_map, places.length_invPerm,
        show (places.expo σ' (places.invPerm k τ')).length
          = (places.invPerm k τ').length from
          ground.length_map _ _,
        places.length_invPerm]) ?_
  intro i hi
  rw [show (places.expo σ' (places.invPerm k τ')).length
      = (places.invPerm k τ').length from ground.length_map _ _,
    places.length_invPerm] at hi
  have ht : ground.getAt 0 (places.invPerm k τ') i < k :=
    perm_inv_lt k hτ' i hi
  have hkey : ground.getAt 0 (places.invPerm k
      (conjBy k a b τ')) (ground.getAt 0 b i)
      = ground.getAt 0 a
        (ground.getAt 0 (places.invPerm k τ') i) := by
    have h1 : ground.getAt 0 (conjBy k a b τ')
        (ground.getAt 0 a
          (ground.getAt 0 (places.invPerm k τ') i))
        = ground.getAt 0 b i := by
      rw [← conjBy_rel k ha hτ' _ ht, perm_right k hτ' i hi]
    rw [← h1, perm_left k hτ _ (perm_lt k ha _ ht)]
  rw [places.getAt_expo σ' (places.invPerm k τ') i (by
      rw [places.length_invPerm]
      exact hi),
    ground.getAt_map 0 0 _ (places.invPerm k
      (places.invPerm k b)) i (by
        rw [places.length_invPerm]
        exact hi),
    places.invPerm_invPerm k hb,
    places.getAt_expo (conjBy k a b σ')
      (places.invPerm k (conjBy k a b τ')) _ (by
        rw [places.length_invPerm]
        exact perm_lt k hb i hi),
    hkey, ← conjBy_rel k ha hσ' _ ht, perm_left k hb _
      (perm_lt k hσ' _ ht)]

/-- A seeded fold at a memberwise class read is the seed against
the family fold. -/
private theorem foldlOv {α : Type} (F : α → poly.Poly)
    (step : poly.Poly → α → poly.Poly)
    (hstep : ∀ acc x, poly.oneValue (step acc x)
      (poly.add acc (F x))) :
    ∀ (l : List α) (acc acc' : poly.Poly), poly.oneValue acc acc' →
      poly.oneValue (l.foldl step acc)
        (poly.add acc' (ground.famFold poly.add [] F l))
  | [], _, acc', hov =>
    poly.oneValue_trans hov
      (poly.oneValue_symm (poly.polyFoldLaws.opUnit acc'))
  | a :: t, acc, acc', hov =>
    poly.oneValue_trans
      (foldlOv F step hstep t (step acc a) (poly.add acc' (F a))
        (poly.oneValue_trans (hstep acc a)
          (poly.polyFoldLaws.opCongr hov
            (poly.oneValue_refl (F a)))))
      (poly.polyFoldLaws.opAssoc acc' (F a)
        (ground.famFold poly.add [] F t))

/-- The matched-dagger-count guard, one read per variable. -/
private def guardOf (G : states.FList) : Bool :=
  (varsOf G).all (fun v =>
    (posIf G (v, false)).length == (posIf G (v, true)).length)

/-- The evaluation at its named parts: the guard, the recursion at
the wiring's matching, and the determinants' fold. -/
private theorem evalPhi_unfold (G : states.FList) (π : List Nat) :
    evalPhi G π =
      (if guardOf G = true then
        (contract G (mOne G.length π) (varsOf G)
          (List.replicate (2 * G.length) 0) [] [],
         (varsOf G).foldr (fun v d =>
           poly.mul (split.pminor (gramWg (posIf G (v, false)).length)) d)
           poly.one)
       else poly.pZero) := rfl

/-- Two factors at one key and distinct dagger reads differ. -/
private theorem dagNe (v : Nat) :
    ¬ ((v, false) : states.Factor) = (v, true) :=
  fun h => Bool.noConfusion (congrArg Prod.snd h)

/-- Two factors at distinct keys differ. -/
private theorem keyNe {v w : Nat} (h : ¬ w = v) (d e : Bool) :
    ¬ ((w, d) : states.Factor) = (v, e) :=
  fun he => h (congrArg Prod.fst he)

/-- A variable's matchings keep the slot list's place count. -/
private theorem matchVar_length (G : states.FList) (v : Nat)
    (σ τ m2 : List Nat) : (matchVar G v σ τ m2).length = m2.length := by
  show (matchIn (matchIn m2 _ _ σ 0 1) _ _ τ 1 0).length = _
  rw [matchIn_length, matchIn_length]

/-- A variable's matchings keep the slot entries' bound. -/
private theorem matchVar_bound (G : states.FList) (v : Nat)
    (σ τ m2 : List Nat)
    (hg : (posIf G (v, false)).length = (posIf G (v, true)).length)
    (hσ : 0 < ground.countOf σ
      (places.perms (posIf G (v, false)).length))
    (hτ : 0 < ground.countOf τ
      (places.perms (posIf G (v, false)).length))
    (hb : ∀ x, x < m2.length → ground.getAt 0 m2 x < 2 * G.length) :
    ∀ x, x < m2.length →
      ground.getAt 0 (matchVar G v σ τ m2) x < 2 * G.length := by
  intro x hx
  show ground.getAt 0 (matchIn (matchIn m2 _ _ σ 0 1)
    (posIf G (v, false)) (posIf G (v, true)) τ 1 0) x < _
  refine matchIn_bound _ _ _ _ 1 0 _
    (fun s hs => slotLt G (v, false) s 1 (by decide +kernel) hs)
    (fun s hs => slotLt G (v, true) _ 0 (by decide +kernel)
      (sigLt G (v, false) (v, true) hτ hg s hs))
    (fun y hy => ?_) x (by
      rw [matchIn_length]
      exact hx)
  refine matchIn_bound _ _ _ _ 0 1 _
    (fun s hs => slotLt G (v, false) s 0 (by decide +kernel) hs)
    (fun s hs => slotLt G (v, true) _ 1 (by decide +kernel)
      (sigLt G (v, false) (v, true) hσ hg s hs)) hb y (by
      rw [matchIn_length] at hy
      exact hy)

/-- A variable's two matchings read their slots: the undaggered
place's row slot against its `σ`-match's column slot, both ways,
and the row's exchange slot against its `τ`-match's, both ways. -/
private theorem matchVar_read (G : states.FList) (v : Nat)
    (σ τ m2 : List Nat) (hm2 : m2.length = 2 * G.length)
    (hg : (posIf G (v, false)).length = (posIf G (v, true)).length)
    (hσ : 0 < ground.countOf σ
      (places.perms (posIf G (v, false)).length))
    (hτ : 0 < ground.countOf τ
      (places.perms (posIf G (v, false)).length))
    (s : Nat) (hs : s < (posIf G (v, false)).length) :
    (ground.getAt 0 (matchVar G v σ τ m2)
        (2 * ground.getAt 0 (posIf G (v, false)) s)
      = 2 * ground.getAt 0 (posIf G (v, true)) (ground.getAt 0 σ s) + 1
    ∧ ground.getAt 0 (matchVar G v σ τ m2)
        (2 * ground.getAt 0 (posIf G (v, true)) (ground.getAt 0 σ s) + 1)
      = 2 * ground.getAt 0 (posIf G (v, false)) s)
    ∧ (ground.getAt 0 (matchVar G v σ τ m2)
        (2 * ground.getAt 0 (posIf G (v, false)) s + 1)
      = 2 * ground.getAt 0 (posIf G (v, true)) (ground.getAt 0 τ s)
    ∧ ground.getAt 0 (matchVar G v σ τ m2)
        (2 * ground.getAt 0 (posIf G (v, true)) (ground.getAt 0 τ s))
      = 2 * ground.getAt 0 (posIf G (v, false)) s + 1) := by
  have hbσ := sigLt G (v, false) (v, true) hσ hg
  have hbτ := sigLt G (v, false) (v, true) hτ hg
  have h1 := matchIn_read m2 (posIf G (v, false)) (posIf G (v, true)) σ 0 1
    (fun t ht => by
      rw [hm2]
      exact slotLt G (v, false) t 0 (by decide +kernel) ht)
    (fun t ht => by
      rw [hm2]
      exact slotLt G (v, true) _ 1 (by decide +kernel) (hbσ t ht))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (posIf_inj G (v, false)) (qsInj G (v, false) (v, true) hσ hg) s hs
  have hl1 : (matchIn m2 (posIf G (v, false)) (posIf G (v, true))
      σ 0 1).length = 2 * G.length := by
    rw [matchIn_length, hm2]
  have h2 := matchIn_read
    (matchIn m2 (posIf G (v, false)) (posIf G (v, true)) σ 0 1)
    (posIf G (v, false)) (posIf G (v, true)) τ 1 0
    (fun t ht => by
      rw [hl1]
      exact slotLt G (v, false) t 1 (by decide +kernel) ht)
    (fun t ht => by
      rw [hl1]
      exact slotLt G (v, true) _ 0 (by decide +kernel) (hbτ t ht))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (posIf_inj G (v, false)) (qsInj G (v, false) (v, true) hτ hg) s hs
  refine ⟨⟨?_, ?_⟩, h2⟩
  · show ground.getAt 0 (matchIn (matchIn m2 _ _ σ 0 1)
        (posIf G (v, false)) (posIf G (v, true)) τ 1 0)
        (2 * ground.getAt 0 (posIf G (v, false)) s + 0) = _
    rw [matchIn_off_slot G _ (v, false) (v, false) (v, true) τ hbτ 1 0 0
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inr (by decide +kernel)) (Or.inl (dagNe v)) s hs]
    exact h1.1
  · show ground.getAt 0 (matchIn (matchIn m2 _ _ σ 0 1)
        (posIf G (v, false)) (posIf G (v, true)) τ 1 0)
        (2 * ground.getAt 0 (posIf G (v, true))
          (ground.getAt 0 σ s) + 1) = _
    rw [matchIn_off_slot G _ (v, true) (v, false) (v, true) τ hbτ 1 0 1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (fun h => dagNe v h.symm)) (Or.inr (by decide +kernel))
        _ (hbσ s hs)]
    exact h1.2

/-- A variable's matchings leave every further variable's slots. -/
private theorem matchVar_off (G : states.FList) (v w : Nat)
    (hvw : ¬ w = v) (σ τ m2 : List Nat)
    (hg : (posIf G (v, false)).length = (posIf G (v, true)).length)
    (hσ : 0 < ground.countOf σ
      (places.perms (posIf G (v, false)).length))
    (hτ : 0 < ground.countOf τ
      (places.perms (posIf G (v, false)).length))
    (d : Bool) (o : Nat) (ho : o < 2) (a : Nat)
    (ha : a < (posIf G (w, d)).length) :
    ground.getAt 0 (matchVar G v σ τ m2)
        (2 * ground.getAt 0 (posIf G (w, d)) a + o)
      = ground.getAt 0 m2 (2 * ground.getAt 0 (posIf G (w, d)) a + o) := by
  show ground.getAt 0 (matchIn (matchIn m2 _ _ σ 0 1)
    (posIf G (v, false)) (posIf G (v, true)) τ 1 0) _ = _
  rw [matchIn_off_slot G _ (w, d) (v, false) (v, true) τ
      (sigLt G (v, false) (v, true) hτ hg) 1 0 o
      (by decide +kernel) (by decide +kernel) ho
      (Or.inl (keyNe hvw d false)) (Or.inl (keyNe hvw d true)) a ha,
    matchIn_off_slot G m2 (w, d) (v, false) (v, true) σ
      (sigLt G (v, false) (v, true) hσ hg) 0 1 o
      (by decide +kernel) (by decide +kernel) ho
      (Or.inl (keyNe hvw d false)) (Or.inl (keyNe hvw d true)) a ha]

/-- The tuple's words at the variables: per variable its two
permutation words, members of the variable's enumeration. -/
private def tupMem (G : states.FList) :
    List Nat → List (List Nat) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | _ :: _, [_] => False
  | v :: vs, σ :: τ :: tup =>
    0 < ground.countOf σ (places.perms (posIf G (v, false)).length)
    ∧ 0 < ground.countOf τ (places.perms (posIf G (v, false)).length)
    ∧ tupMem G vs tup

/-- The slot wiring at a tuple of the variables' words: the
variables' matchings joined in order. -/
private def wireAll (G : states.FList) :
    List Nat → List (List Nat) → List Nat → List Nat
  | [], _, m2 => m2
  | _ :: _, [], m2 => m2
  | _ :: _, [_], m2 => m2
  | v :: vs, σ :: τ :: tup, m2 => wireAll G vs tup (matchVar G v σ τ m2)

/-- The coefficient list at a tuple: one Weingarten entry per
variable. -/
private def coefAll (G : states.FList) :
    List Nat → List (List Nat) → List Poly
  | [], _ => []
  | _ :: _, [] => []
  | _ :: _, [_] => []
  | v :: vs, σ :: τ :: tup => nOf G v σ τ :: coefAll G vs tup

/-- The variables' word domains, two enumerations per variable. -/
private def domsOf (G : states.FList) (vs : List Nat) :
    List (List (List Nat)) :=
  vs.flatMap (fun v => [places.perms (posIf G (v, false)).length,
    places.perms (posIf G (v, false)).length])

/-- One tuple's term: the coefficients' product against the loop
value of the composite walk at the tuple's wiring. -/
private def termAt (G : states.FList) (m1 : List Nat) (vs : List Nat)
    (m2 : List Nat) (cs : List Poly) (tup : List (List Nat)) : Poly :=
  (cs ++ coefAll G vs tup).foldr poly.mul
    (dfPow ((places.cyclesOf (compAt G.length m1
      (wireAll G vs tup m2))).length / 2))

/-- The family fold over the product lists at a leading domain
folds the domain outermost, the tail's lists inside. -/
private theorem famFold_prodLists_cons {α : Type} (F : List α → Poly)
    (D : List α) (t : List (List α)) :
    poly.oneValue
      (ground.famFold poly.add [] F (ground.prodLists (D :: t)))
      (ground.famFold poly.add [] (fun x =>
        ground.famFold poly.add [] (fun l => F (x :: l))
          (ground.prodLists t)) D) := by
  show poly.oneValue (ground.famFold poly.add [] F
    (D.flatMap (fun x => (ground.prodLists t).map (fun l => x :: l)))) _
  refine poly.oneValue_trans
    (ground.famFold_flatMap_ov poly.polyFoldLaws F _ D) ?_
  rw [ground.famFold_congr_all poly.add [] _ _ (fun x =>
    ground.famFold_map poly.add [] F (fun l => x :: l)
      (ground.prodLists t)) D]
  exact poly.oneValue_refl _

/-- The recursion is the seed against the family fold of the terms
over the tuples. -/
private theorem contract_flat (G : states.FList) (m1 : List Nat) :
    ∀ (vs : List Nat) (m2 : List Nat) (cs : List Poly) (acc : Poly),
      poly.oneValue (contract G m1 vs m2 cs acc)
        (poly.add acc (ground.famFold poly.add []
          (termAt G m1 vs m2 cs) (ground.prodLists (domsOf G vs))))
  | [], m2, cs, acc => by
    show poly.oneValue (poly.add acc (cs.foldr poly.mul
      (dfPow ((places.cyclesOf (compAt G.length m1 m2)).length / 2))))
      (poly.add acc (poly.add (termAt G m1 [] m2 cs []) []))
    refine poly.polyFoldLaws.opCongr (poly.oneValue_refl acc) ?_
    refine poly.oneValue_trans ?_
      (poly.oneValue_symm (poly.polyFoldLaws.opUnit _))
    show poly.oneValue (cs.foldr poly.mul _) ((cs ++ []).foldr poly.mul _)
    rw [ground.append_nil]
    exact poly.oneValue_refl _
  | v :: vs, m2, cs, acc => by
    have hin : ∀ (σ : List Nat) (a a' : Poly), poly.oneValue a a' →
        poly.oneValue
          ((places.perms (posIf G (v, false)).length).foldl
            (fun acc τ => contract G m1 vs (matchVar G v σ τ m2)
              (cs ++ [nOf G v σ τ]) acc) a)
          (poly.add a' (ground.famFold poly.add [] (fun τ =>
            ground.famFold poly.add []
              (termAt G m1 vs (matchVar G v σ τ m2) (cs ++ [nOf G v σ τ]))
              (ground.prodLists (domsOf G vs)))
            (places.perms (posIf G (v, false)).length))) :=
      fun σ a a' h => foldlOv _ _
        (fun a τ => contract_flat G m1 vs (matchVar G v σ τ m2)
          (cs ++ [nOf G v σ τ]) a) _ a a' h
    refine poly.oneValue_trans
      (foldlOv _ _ (fun a σ => hin σ a a (poly.oneValue_refl a)) _
        acc acc (poly.oneValue_refl acc)) ?_
    refine poly.polyFoldLaws.opCongr (poly.oneValue_refl acc) ?_
    show poly.oneValue _ (ground.famFold poly.add []
      (termAt G m1 (v :: vs) m2 cs)
      (ground.prodLists (places.perms (posIf G (v, false)).length
        :: places.perms (posIf G (v, false)).length :: domsOf G vs)))
    refine poly.oneValue_trans ?_
      (poly.oneValue_symm (famFold_prodLists_cons _ _ _))
    refine ground.famFold_congr_members_ov poly.oneValue poly.add []
      poly.oneValue_refl poly.polyFoldLaws.opCongr _ _ _
      (fun σ _ => ?_)
    refine poly.oneValue_trans ?_
      (poly.oneValue_symm (famFold_prodLists_cons _ _ _))
    refine ground.famFold_congr_members_ov poly.oneValue poly.add []
      poly.oneValue_refl poly.polyFoldLaws.opCongr _ _ _
      (fun τ _ => ?_)
    refine ground.famFold_congr_members_ov poly.oneValue poly.add []
      poly.oneValue_refl poly.polyFoldLaws.opCongr _ _ _
      (fun tup _ => ?_)
    show poly.oneValue
      (((cs ++ [nOf G v σ τ]) ++ coefAll G vs tup).foldr poly.mul _)
      ((cs ++ (nOf G v σ τ :: coefAll G vs tup)).foldr poly.mul _)
    rw [ground.append_assoc]
    exact poly.oneValue_refl _

/-! The variable list's reads: distinct, covering every place's
key, and one value at a relabeling of the site. -/

/-- A key of the site sits below the key bound. -/
private theorem key_lt_bound (G : states.FList) (j : Nat)
    (hj : j < G.length) :
    (ground.getAt (0, false) G j).1 < keyBound G :=
  Nat.lt_succ_of_le (ground.famFold_mem_le
    (fun i => (ground.getAt (0, false) G i).1) (List.range G.length) j
    (ground.mem_of_countOf_pos j _ (ground.countOf_range_pos hj)))

/-- The variable list is distinct. -/
private theorem varsOf_distinct (G : states.FList) :
    ground.distinctList (varsOf G) := by
  intro v _
  show ground.countOf v ((List.range (keyBound G)).filter _) ≤ 1
  rw [ground.countOf_filter]
  cases decide (0 < (posIf G (v, false)).length + (posIf G (v, true)).length) with
  | true => exact rangeDist v (keyBound G)
  | false => exact Nat.zero_le 1

/-- Every place's key is a variable of the site. -/
private theorem varsOf_cover (G : states.FList) (j : Nat)
    (hj : j < G.length) :
    0 < ground.countOf (ground.getAt (0, false) G j).1 (varsOf G) := by
  refine ground.countOf_pos_of_mem (ground.mem_filter_to _
    (ground.mem_of_countOf_pos _ _ (ground.countOf_range_pos
      (key_lt_bound G j hj))) ?_)
  refine decide_eq_true ?_
  have hp : 0 < (posIf G ((ground.getAt (0, false) G j).1,
      (ground.getAt (0, false) G j).2)).length :=
    ground.length_pos_of_countOf (posIf_mem hj rfl)
  cases hd : (ground.getAt (0, false) G j).2 with
  | false =>
    rw [hd] at hp
    exact Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _)
  | true =>
    rw [hd] at hp
    exact Nat.lt_of_lt_of_le hp (Nat.le_add_left _ _)

/-- The key bound is one value at a relabeling of the site. -/
private theorem keyBound_relabel (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i)) :
    keyBound G' = keyBound G := by
  show ground.famFold Nat.add 0 (fun i => (ground.getAt (0, false) G' i).1)
      (List.range G'.length) + 1
    = ground.famFold Nat.add 0 (fun i => (ground.getAt (0, false) G i).1)
      (List.range G.length) + 1
  rw [hm, hm']
  refine congrArg (fun x => x + 1) ?_
  rw [ground.famFold_congr_members Nat.add 0 _
    (fun i => (ground.getAt (0, false) G (ground.getAt 0 ρ i)).1)
    (List.range m) (fun i hi => by rw [hg i (ground.ltOfMem hi)])]
  exact (ground.famFold_reindex_ov ground.natFoldLaws.toCommLaws 0
    (fun i => (ground.getAt (0, false) G i).1)
    (ground.distinctList_range m)
    (fun i hi => perm_left m hr i (ground.ltOfMem hi))
    (fun i hi => perm_right m hr i (ground.ltOfMem hi))
    (fun i hi => ground.countOf_range_pos
      (perm_lt m hr i (ground.ltOfMem hi)))
    (fun i hi => ground.countOf_range_pos
      (perm_inv_lt m hr i (ground.ltOfMem hi)))).symm

/-- A right fold at pointwise equal steps is one value at every
seed. -/
private theorem foldr_ext {α β : Type} (f g : α → β → β)
    (h : ∀ a b, f a b = g a b) :
    ∀ (l : List α) (x : β), l.foldr f x = l.foldr g x
  | [], _ => rfl
  | a :: t, x => by
    show f a (t.foldr f x) = g a (t.foldr g x)
    rw [h a, foldr_ext f g h t x]

/-- The variable list is one value at a relabeling of the site. -/
private theorem varsOf_relabel (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i)) :
    varsOf G' = varsOf G := by
  show (List.range (keyBound G')).filter _
    = (List.range (keyBound G)).filter _
  rw [keyBound_relabel G G' ρ m hm hm' hr hg]
  exact ground.filter_congr _ _ (fun v => by
    rw [posIf_len_eq G G' ρ m hm hm' hr hg (v, false),
      posIf_len_eq G G' ρ m hm hm' hr hg (v, true)]) _

/-- The word domains are one value at a relabeling of the site. -/
private theorem domsOf_relabel (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (vs : List Nat) : domsOf G' vs = domsOf G vs :=
  ground.flatMap_congr_all _ _ (fun v => by
    rw [posIf_len_eq G G' ρ m hm hm' hr hg (v, false)]) vs

/-- The tuple's membership transports across sites at matched
undaggered counts. -/
private theorem tupMem_of_len (G G' : states.FList)
    (hlen : ∀ v, (posIf G' (v, false)).length
      = (posIf G (v, false)).length) :
    ∀ (vs : List Nat) (tup : List (List Nat)),
      tupMem G' vs tup → tupMem G vs tup
  | [], [], h => h
  | [], _ :: _, h => h
  | _ :: _, [], h => h
  | _ :: _, [_], h => h
  | v :: vs, σ :: τ :: tup, ⟨h1, h2, h3⟩ => by
    refine ⟨?_, ?_, tupMem_of_len G G' hlen vs tup h3⟩
    · rw [← hlen v]
      exact h1
    · rw [← hlen v]
      exact h2

/-- A member of the word domains' product lists is a tuple of the
variables' words. -/
private theorem tupMem_of_count (G : states.FList) :
    ∀ (vs : List Nat) (tup : List (List Nat)),
      0 < ground.countOf tup (ground.prodLists (domsOf G vs)) →
      tupMem G vs tup
  | [], [], _ => trivial
  | [], x :: t, h => by
    have h' : 0 < ground.countOf (x :: t) [([] : List (List Nat))] := h
    rw [ground.countOf_head_ne (a := x :: t) (b := ([] : List (List Nat)))
      (fun he => nomatch he) []] at h'
    exact absurd h' (Nat.lt_irrefl 0)
  | v :: vs, [], h => by
    have hl := (ground.mem_prodLists_of [] _ _
      (ground.mem_of_countOf_pos _ _ h)).1
    exact nomatch hl
  | v :: vs, [σ], h => by
    have hl := (ground.mem_prodLists_of [] _ _
      (ground.mem_of_countOf_pos _ _ h)).1
    exact nomatch (Nat.succ.inj hl)
  | v :: vs, σ :: τ :: tup, h => by
    have h' : 0 < ground.countOf (σ :: τ :: tup) (ground.prodLists
        (places.perms (posIf G (v, false)).length
          :: places.perms (posIf G (v, false)).length :: domsOf G vs)) := h
    rw [ground.countOf_prodLists_cons, ground.countOf_prodLists_cons] at h'
    obtain ⟨h1, h23⟩ := ground.mulPosSplit h'
    obtain ⟨h2, h3⟩ := ground.mulPosSplit h23
    exact ⟨h1, h2, tupMem_of_count G vs tup h3⟩

/-- A tuple of the variables' words is a member of the domains'
product lists. -/
private theorem count_of_tupMem (G : states.FList) :
    ∀ (vs : List Nat) (tup : List (List Nat)), tupMem G vs tup →
      0 < ground.countOf tup (ground.prodLists (domsOf G vs))
  | [], [], _ => by
    show 0 < ground.countOf ([] : List (List Nat)) [[]]
    decide +kernel
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | _ :: _, [_], h => False.elim h
  | v :: vs, σ :: τ :: tup, ⟨h1, h2, h3⟩ => by
    show 0 < ground.countOf (σ :: τ :: tup) (ground.prodLists
      (places.perms (posIf G (v, false)).length
        :: places.perms (posIf G (v, false)).length :: domsOf G vs))
    rw [ground.countOf_prodLists_cons, ground.countOf_prodLists_cons]
    exact Nat.mul_pos h1 (Nat.mul_pos h2 (count_of_tupMem G vs tup h3))

/-- Every word domain is distinct, an enumeration of
permutations. -/
private theorem domsOf_distinct (G : states.FList) :
    ∀ (vs : List Nat) (E : List (List Nat)), E ∈ domsOf G vs →
      ground.distinctList E
  | [], _, h => nomatch h
  | v :: vs, E, h => by
    have h' : E ∈ places.perms (posIf G (v, false)).length
        :: places.perms (posIf G (v, false)).length :: domsOf G vs := h
    cases h' with
    | head => exact places.perms_distinct _
    | tail _ h2 =>
      cases h2 with
      | head => exact places.perms_distinct _
      | tail _ h3 => exact domsOf_distinct G vs E h3

/-- The head's count in its own list is positive. -/
private theorem cntHead {α : Type} [DecidableEq α] (a : α) (t : List α) :
    0 < ground.countOf a (a :: t) := by
  rw [ground.countOf_head]
  exact Nat.succ_pos _

/-- A distinct list's head sits off its tail. -/
private theorem distinct_head_off {α : Type} [DecidableEq α] {a : α}
    {t : List α} (hd : ground.distinctList (a :: t)) (u : α)
    (hu : 0 < ground.countOf u t) : ¬ u = a := fun he => by
  have h1 := hd a (List.Mem.head t)
  rw [ground.countOf_head] at h1
  rw [he] at hu
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le
    (Nat.succ_lt_succ hu) h1)

/-- The tuple conjugated by the variables' slot maps. -/
private def conjTup (G G' : states.FList) (ρ : List Nat) :
    List Nat → List (List Nat) → List (List Nat)
  | [], tup => tup
  | _ :: _, [] => []
  | _ :: _, [σ] => [σ]
  | v :: vs, σ :: τ :: tup =>
    conjBy (posIf G (v, false)).length (slotOf G G' ρ (v, false))
        (slotOf G G' ρ (v, true)) σ
      :: conjBy (posIf G (v, false)).length (slotOf G G' ρ (v, false))
        (slotOf G G' ρ (v, true)) τ
      :: conjTup G G' ρ vs tup

/-- The tuple conjugated back, at the partner slot maps. -/
private def conjTupInv (G G' : states.FList) (ρ : List Nat) :
    List Nat → List (List Nat) → List (List Nat)
  | [], tup => tup
  | _ :: _, [] => []
  | _ :: _, [σ] => [σ]
  | v :: vs, σ :: τ :: tup =>
    conjBy (posIf G (v, false)).length
        (places.invPerm (posIf G (v, false)).length
          (slotOf G G' ρ (v, false)))
        (places.invPerm (posIf G (v, false)).length
          (slotOf G G' ρ (v, true))) σ
      :: conjBy (posIf G (v, false)).length
        (places.invPerm (posIf G (v, false)).length
          (slotOf G G' ρ (v, false)))
        (places.invPerm (posIf G (v, false)).length
          (slotOf G G' ρ (v, true))) τ
      :: conjTupInv G G' ρ vs tup

/-- The daggered slot map is a permutation at the undaggered
count. -/
private theorem slotOf_member' (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (v : Nat)
    (hgv : (posIf G (v, false)).length = (posIf G (v, true)).length) :
    0 < ground.countOf (slotOf G G' ρ (v, true))
      (places.perms (posIf G (v, false)).length) := by
  rw [hgv]
  exact slotOf_member G G' ρ m hm hm' hr hg (v, true)

/-- The conjugated tuple conjugates back. -/
private theorem conjTup_inv (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i)) :
    ∀ (vs : List Nat) (tup : List (List Nat)),
      (∀ w, 0 < ground.countOf w vs →
        (posIf G (w, false)).length = (posIf G (w, true)).length) →
      tupMem G vs tup →
      conjTupInv G G' ρ vs (conjTup G G' ρ vs tup) = tup
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, [_], _, _ => rfl
  | v :: vs, σ :: τ :: tup, hmt, ⟨h1, h2, h3⟩ => by
    have ha := slotOf_member G G' ρ m hm hm' hr hg (v, false)
    have hb := slotOf_member' G G' ρ m hm hm' hr hg v (hmt v (cntHead v vs))
    show conjBy _ _ _ (conjBy _ _ _ σ) :: conjBy _ _ _ (conjBy _ _ _ τ)
      :: conjTupInv G G' ρ vs (conjTup G G' ρ vs tup) = _
    rw [conjBy_inv _ ha hb h1, conjBy_inv _ ha hb h2,
      conjTup_inv G G' ρ m hm hm' hr hg vs tup (fun w hw => hmt w (ground.countOf_cons_pos hw)) h3]

/-- The back-conjugated tuple conjugates forward. -/
private theorem conjTup_inv' (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i)) :
    ∀ (vs : List Nat) (tup : List (List Nat)),
      (∀ w, 0 < ground.countOf w vs →
        (posIf G (w, false)).length = (posIf G (w, true)).length) →
      tupMem G vs tup →
      conjTup G G' ρ vs (conjTupInv G G' ρ vs tup) = tup
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, [_], _, _ => rfl
  | v :: vs, σ :: τ :: tup, hmt, ⟨h1, h2, h3⟩ => by
    have ha := slotOf_member G G' ρ m hm hm' hr hg (v, false)
    have hb := slotOf_member' G G' ρ m hm hm' hr hg v (hmt v (cntHead v vs))
    have hσ := conjBy_inv (posIf G (v, false)).length
      (places.invPerm_member _ ha) (places.invPerm_member _ hb) h1
    have hτ := conjBy_inv (posIf G (v, false)).length
      (places.invPerm_member _ ha) (places.invPerm_member _ hb) h2
    rw [places.invPerm_invPerm _ ha, places.invPerm_invPerm _ hb] at hσ hτ
    show conjBy _ _ _ (conjBy _ _ _ σ) :: conjBy _ _ _ (conjBy _ _ _ τ)
      :: conjTup G G' ρ vs (conjTupInv G G' ρ vs tup) = _
    rw [hσ, hτ, conjTup_inv' G G' ρ m hm hm' hr hg vs tup (fun w hw => hmt w (ground.countOf_cons_pos hw)) h3]

/-- The conjugated tuple is a tuple of the variables' words. -/
private theorem conjTup_mem (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i)) :
    ∀ (vs : List Nat) (tup : List (List Nat)),
      (∀ w, 0 < ground.countOf w vs →
        (posIf G (w, false)).length = (posIf G (w, true)).length) →
      tupMem G vs tup → tupMem G vs (conjTup G G' ρ vs tup)
  | [], [], _, h => h
  | [], _ :: _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: _, [_], _, h => h
  | v :: vs, _ :: _ :: tup, hmt, ⟨h1, h2, h3⟩ =>
    ⟨conjBy_member _ (slotOf_member G G' ρ m hm hm' hr hg (v, false))
        (slotOf_member' G G' ρ m hm hm' hr hg v (hmt v (cntHead v vs))) h1,
     conjBy_member _ (slotOf_member G G' ρ m hm hm' hr hg (v, false))
        (slotOf_member' G G' ρ m hm hm' hr hg v (hmt v (cntHead v vs))) h2,
     conjTup_mem G G' ρ m hm hm' hr hg vs tup (fun w hw => hmt w (ground.countOf_cons_pos hw)) h3⟩

/-- The back-conjugated tuple is a tuple of the variables'
words. -/
private theorem conjTupInv_mem (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i)) :
    ∀ (vs : List Nat) (tup : List (List Nat)),
      (∀ w, 0 < ground.countOf w vs →
        (posIf G (w, false)).length = (posIf G (w, true)).length) →
      tupMem G vs tup → tupMem G vs (conjTupInv G G' ρ vs tup)
  | [], [], _, h => h
  | [], _ :: _, _, h => h
  | _ :: _, [], _, h => h
  | _ :: _, [_], _, h => h
  | v :: vs, _ :: _ :: tup, hmt, ⟨h1, h2, h3⟩ =>
    ⟨conjBy_member _ (places.invPerm_member _
          (slotOf_member G G' ρ m hm hm' hr hg (v, false)))
        (places.invPerm_member _
          (slotOf_member' G G' ρ m hm hm' hr hg v (hmt v (cntHead v vs)))) h1,
     conjBy_member _ (places.invPerm_member _
          (slotOf_member G G' ρ m hm hm' hr hg (v, false)))
        (places.invPerm_member _
          (slotOf_member' G G' ρ m hm hm' hr hg v (hmt v (cntHead v vs)))) h2,
     conjTupInv_mem G G' ρ m hm hm' hr hg vs tup (fun w hw => hmt w (ground.countOf_cons_pos hw)) h3⟩

/-- Two coefficient lists at one value entry by entry. -/
private def csOV : List Poly → List Poly → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | a :: t, b :: u => poly.oneValue a b ∧ csOV t u

/-- The product fold reads one value at coefficient lists and seeds
at one value. -/
private theorem foldr_mul_ov : ∀ (cs cs' : List Poly) (x x' : Poly),
    csOV cs cs' → poly.oneValue x x' →
    poly.oneValue (cs.foldr poly.mul x) (cs'.foldr poly.mul x')
  | [], [], _, _, _, hx => hx
  | [], _ :: _, _, _, h, _ => False.elim h
  | _ :: _, [], _, _, h, _ => False.elim h
  | _ :: t, b :: u, x, x', ⟨hab, htu⟩, hx =>
    poly.oneValue_trans (poly.mul_congr_left hab _)
      (poly.mul_congr b (foldr_mul_ov t u x x' htu hx))

/-- A variable's Weingarten entry travels the slot maps: the
relabeled site's entry reads the site's own at the conjugated
words. -/
private theorem nOf_transport (G G' : states.FList) (v : Nat)
    (a b σ' τ' : List Nat)
    (heq : (posIf G' (v, false)).length = (posIf G (v, false)).length)
    (ha : 0 < ground.countOf a
      (places.perms (posIf G (v, false)).length))
    (hb : 0 < ground.countOf b
      (places.perms (posIf G (v, false)).length))
    (hσ' : 0 < ground.countOf σ'
      (places.perms (posIf G (v, false)).length))
    (hτ' : 0 < ground.countOf τ'
      (places.perms (posIf G (v, false)).length)) :
    poly.oneValue (nOf G' v σ' τ')
      (nOf G v (conjBy (posIf G (v, false)).length a b σ')
        (conjBy (posIf G (v, false)).length a b τ')) := by
  show poly.oneValue (ground.getAt [] (ground.getAt []
      (genericlift.padj (gramWg (posIf G' (v, false)).length))
      (places.idxOf (places.expo σ' (places.invPerm
        (posIf G' (v, false)).length τ'))
        (places.perms (posIf G' (v, false)).length)))
      (places.idxOf (List.range (posIf G' (v, false)).length)
        (places.perms (posIf G' (v, false)).length))) _
  rw [heq, expo_conj (posIf G (v, false)).length ha hb hσ' hτ']
  exact wgCol_transport (posIf G (v, false)).length
    (places.expo (conjBy (posIf G (v, false)).length a b σ')
      (places.invPerm (posIf G (v, false)).length
        (conjBy (posIf G (v, false)).length a b τ')))
    (places.invPerm (posIf G (v, false)).length b)
    (places.expo_member _ (conjBy_member _ ha hb hσ')
      (places.invPerm_member _ (conjBy_member _ ha hb hτ')))
    (places.invPerm_member _ hb)

/-- The coefficient list travels the slot maps entry by entry. -/
private theorem coefAll_transport (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i)) :
    ∀ (vs : List Nat) (tup : List (List Nat)),
      (∀ w, 0 < ground.countOf w vs →
        (posIf G (w, false)).length = (posIf G (w, true)).length) →
      tupMem G vs tup →
      csOV (coefAll G' vs tup) (coefAll G vs (conjTup G G' ρ vs tup))
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], _, h => False.elim h
  | _ :: _, [_], _, h => False.elim h
  | v :: vs, σ :: τ :: tup, hmt, ⟨h1, h2, h3⟩ =>
    ⟨nOf_transport G G' v _ _ σ τ
        (posIf_len_eq G G' ρ m hm hm' hr hg (v, false))
        (slotOf_member G G' ρ m hm hm' hr hg (v, false))
        (slotOf_member' G G' ρ m hm hm' hr hg v (hmt v (cntHead v vs)))
        h1 h2,
     coefAll_transport G G' ρ m hm hm' hr hg vs tup (fun w hw => hmt w (ground.countOf_cons_pos hw)) h3⟩

/-! The tuple wiring's reads: the place count, the bound, the
slots left by the further variables, the reads at a variable, the
involution, and the transport along a relabeling. -/

/-- The tuple wiring keeps the slot entries' bound. -/
private theorem wireAll_bound (G : states.FList) :
    ∀ (vs : List Nat) (tup : List (List Nat)) (m2 : List Nat),
      tupMem G vs tup →
      (∀ w, 0 < ground.countOf w vs →
        (posIf G (w, false)).length = (posIf G (w, true)).length) →
      (∀ x, x < m2.length → ground.getAt 0 m2 x < 2 * G.length) →
      ∀ x, x < m2.length →
        ground.getAt 0 (wireAll G vs tup m2) x < 2 * G.length
  | [], _, _, _, _, hb, x, hx => hb x hx
  | _ :: _, [], _, _, _, hb, x, hx => hb x hx
  | _ :: _, [_], _, _, _, hb, x, hx => hb x hx
  | v :: vs, σ :: τ :: tup, m2, ⟨h1, h2, h3⟩, hmt, hb, x, hx => by
    show ground.getAt 0 (wireAll G vs tup (matchVar G v σ τ m2)) x < _
    exact wireAll_bound G vs tup _ h3 (fun w hw => hmt w (ground.countOf_cons_pos hw))
      (fun y hy => matchVar_bound G v σ τ m2 (hmt v (cntHead v vs)) h1 h2 hb y
        (by
          rw [matchVar_length] at hy
          exact hy)) x (by
        rw [matchVar_length]
        exact hx)

/-- The tuple wiring over variables off a letter's key leaves the
letter's slots. -/
private theorem wireAll_off (G : states.FList) (v : Nat) (d : Bool)
    (o : Nat) (ho : o < 2) (a : Nat) (ha : a < (posIf G (v, d)).length) :
    ∀ (vs : List Nat) (tup : List (List Nat)) (m2 : List Nat),
      tupMem G vs tup →
      (∀ w, 0 < ground.countOf w vs →
        (posIf G (w, false)).length = (posIf G (w, true)).length) →
      (∀ w, 0 < ground.countOf w vs → ¬ w = v) →
      ground.getAt 0 (wireAll G vs tup m2)
          (2 * ground.getAt 0 (posIf G (v, d)) a + o)
        = ground.getAt 0 m2 (2 * ground.getAt 0 (posIf G (v, d)) a + o)
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => rfl
  | _ :: _, [_], _, _, _, _ => rfl
  | w :: vs, σ :: τ :: tup, m2, ⟨h1, h2, h3⟩, hmt, hne => by
    show ground.getAt 0 (wireAll G vs tup (matchVar G w σ τ m2)) _ = _
    rw [wireAll_off G v d o ho a ha vs tup _ h3 (fun u hu => hmt u (ground.countOf_cons_pos hu))
        (fun u hu => hne u (ground.countOf_cons_pos hu)),
      matchVar_off G w v (fun e => hne w (cntHead w vs) e.symm) σ τ m2
        (hmt w (cntHead w vs)) h1 h2 d o ho a ha]

/-- The tuple wiring reads a variable's slots at the tuple's words
for that variable: the four reads of the variable's own matchings,
the further variables leaving them. -/
private theorem wireAll_read (G : states.FList) :
    ∀ (vs : List Nat) (tup : List (List Nat)) (m2 : List Nat),
      m2.length = 2 * G.length → ground.distinctList vs →
      tupMem G vs tup →
      (∀ w, 0 < ground.countOf w vs →
        (posIf G (w, false)).length = (posIf G (w, true)).length) →
      ∀ v, 0 < ground.countOf v vs →
      ∃ σ τ, 0 < ground.countOf σ
          (places.perms (posIf G (v, false)).length)
        ∧ 0 < ground.countOf τ
          (places.perms (posIf G (v, false)).length)
        ∧ ∀ s, s < (posIf G (v, false)).length →
          (ground.getAt 0 (wireAll G vs tup m2)
              (2 * ground.getAt 0 (posIf G (v, false)) s)
            = 2 * ground.getAt 0 (posIf G (v, true))
              (ground.getAt 0 σ s) + 1
          ∧ ground.getAt 0 (wireAll G vs tup m2)
              (2 * ground.getAt 0 (posIf G (v, true))
                (ground.getAt 0 σ s) + 1)
            = 2 * ground.getAt 0 (posIf G (v, false)) s)
          ∧ (ground.getAt 0 (wireAll G vs tup m2)
              (2 * ground.getAt 0 (posIf G (v, false)) s + 1)
            = 2 * ground.getAt 0 (posIf G (v, true))
              (ground.getAt 0 τ s)
          ∧ ground.getAt 0 (wireAll G vs tup m2)
              (2 * ground.getAt 0 (posIf G (v, true))
                (ground.getAt 0 τ s))
            = 2 * ground.getAt 0 (posIf G (v, false)) s + 1)
  | [], _, _, _, _, _, _, _, hv => absurd hv (Nat.lt_irrefl 0)
  | _ :: _, [], _, _, _, h, _, _, _ => False.elim h
  | _ :: _, [_], _, _, _, h, _, _, _ => False.elim h
  | w :: vs, σ :: τ :: tup, m2, hm2, hd, ⟨h1, h2, h3⟩, hmt, v, hv => by
    by_cases hvw : v = w
    · rw [hvw]
      refine ⟨σ, τ, h1, h2, fun s hs => ?_⟩
      have hnot : ∀ u, 0 < ground.countOf u vs → ¬ u = w :=
        fun u hu => distinct_head_off hd u hu
      have hmt' : ∀ u, 0 < ground.countOf u vs →
          (posIf G (u, false)).length = (posIf G (u, true)).length :=
        fun u hu => hmt u (ground.countOf_cons_pos hu)
      have hgw := hmt w (cntHead w vs)
      have hbσ := sigLt G (w, false) (w, true) h1 hgw
      have hbτ := sigLt G (w, false) (w, true) h2 hgw
      show (ground.getAt 0 (wireAll G vs tup (matchVar G w σ τ m2))
            (2 * ground.getAt 0 (posIf G (w, false)) s) = _
          ∧ ground.getAt 0 (wireAll G vs tup (matchVar G w σ τ m2)) _ = _)
        ∧ (ground.getAt 0 (wireAll G vs tup (matchVar G w σ τ m2)) _ = _
          ∧ ground.getAt 0 (wireAll G vs tup (matchVar G w σ τ m2)) _ = _)
      have hr := matchVar_read G w σ τ m2 hm2 hgw h1 h2 s hs
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show ground.getAt 0 (wireAll G vs tup (matchVar G w σ τ m2))
          (2 * ground.getAt 0 (posIf G (w, false)) s + 0) = _
        rw [wireAll_off G w false 0 (by decide +kernel) s hs vs tup _
          h3 hmt' hnot]
        exact hr.1.1
      · rw [wireAll_off G w true 1 (by decide +kernel) _ (hbσ s hs) vs tup _
          h3 hmt' hnot]
        exact hr.1.2
      · rw [wireAll_off G w false 1 (by decide +kernel) s hs vs tup _
          h3 hmt' hnot]
        exact hr.2.1
      · show ground.getAt 0 (wireAll G vs tup (matchVar G w σ τ m2))
          (2 * ground.getAt 0 (posIf G (w, true))
            (ground.getAt 0 τ s) + 0) = _
        rw [wireAll_off G w true 0 (by decide +kernel) _ (hbτ s hs) vs tup _
          h3 hmt' hnot]
        exact hr.2.2
    · have hv' : 0 < ground.countOf v vs := by
        rw [ground.countOf_head_ne hvw] at hv
        exact hv
      exact wireAll_read G vs tup (matchVar G w σ τ m2) (by
          rw [matchVar_length]
          exact hm2) (ground.distinct_tail hd) h3
        (fun u hu => hmt u (ground.countOf_cons_pos hu)) v hv'

/-- The tuple wiring over every place's variable is its own
partner slot by slot. -/
private theorem wireAll_invol (G : states.FList) (vs : List Nat)
    (tup : List (List Nat)) (m2 : List Nat)
    (hm2 : m2.length = 2 * G.length) (hd : ground.distinctList vs)
    (ht : tupMem G vs tup)
    (hmt : ∀ w, 0 < ground.countOf w vs →
      (posIf G (w, false)).length = (posIf G (w, true)).length)
    (hcov : ∀ j, j < G.length →
      0 < ground.countOf (ground.getAt (0, false) G j).1 vs)
    (x : Nat) (hx : x < 2 * G.length) :
    ground.getAt 0 (wireAll G vs tup m2)
      (ground.getAt 0 (wireAll G vs tup m2) x) = x := by
  obtain ⟨j, hj, hjx⟩ := halveLt hx
  obtain ⟨σ, τ, hσ, hτ, hreads⟩ :=
    wireAll_read G vs tup m2 hm2 hd ht hmt _ (hcov j hj)
  have hgv := hmt _ (hcov j hj)
  cases hdag : (ground.getAt (0, false) G j).2 with
  | false =>
    have hf : ground.getAt (0, false) G j
        = ((ground.getAt (0, false) G j).1, false) :=
      congrArg (fun b => ((ground.getAt (0, false) G j).1, b)) hdag
    obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G
        ((ground.getAt (0, false) G j).1, false)).length
        ∧ ground.getAt 0 (posIf G
          ((ground.getAt (0, false) G j).1, false)) s = j :=
      ⟨places.posOf j _, places.posOf_lt j _ (posIf_mem hj hf),
       places.getAt_posOf j _ (posIf_mem hj hf)⟩
    match hjx with
    | Or.inl hev =>
      rw [hev, ← hjs, (hreads s hs).1.1, (hreads s hs).1.2]
    | Or.inr hod =>
      rw [hod, ← hjs, (hreads s hs).2.1, (hreads s hs).2.2]
  | true =>
    have hf : ground.getAt (0, false) G j
        = ((ground.getAt (0, false) G j).1, true) :=
      congrArg (fun b => ((ground.getAt (0, false) G j).1, b)) hdag
    have htl : places.posOf j (posIf G
        ((ground.getAt (0, false) G j).1, true))
        < (posIf G ((ground.getAt (0, false) G j).1, false)).length := by
      rw [hgv]
      exact places.posOf_lt j _ (posIf_mem hj hf)
    match hjx with
    | Or.inr hod =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G
          ((ground.getAt (0, false) G j).1, false)).length
          ∧ ground.getAt 0 (posIf G
            ((ground.getAt (0, false) G j).1, true))
              (ground.getAt 0 σ s) = j :=
        ⟨ground.getAt 0 (places.invPerm _ σ)
          (places.posOf j (posIf G ((ground.getAt (0, false) G j).1, true))),
         perm_inv_lt _ hσ _ htl, by
          rw [perm_right _ hσ _ htl]
          exact places.getAt_posOf j _ (posIf_mem hj hf)⟩
      rw [hod, ← hjs, (hreads s hs).1.2, (hreads s hs).1.1]
    | Or.inl hev =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G
          ((ground.getAt (0, false) G j).1, false)).length
          ∧ ground.getAt 0 (posIf G
            ((ground.getAt (0, false) G j).1, true))
              (ground.getAt 0 τ s) = j :=
        ⟨ground.getAt 0 (places.invPerm _ τ)
          (places.posOf j (posIf G ((ground.getAt (0, false) G j).1, true))),
         perm_inv_lt _ hτ _ htl, by
          rw [perm_right _ hτ _ htl]
          exact places.getAt_posOf j _ (posIf_mem hj hf)⟩
      rw [hev, ← hjs, (hreads s hs).2.2, (hreads s hs).2.1]

/-- The composite walk's place count is the doubled site's. -/
private theorem compAt_length (m : Nat) (m1 m2 : List Nat) :
    (compAt m m1 m2).length = 2 * m :=
  ground.length_mapRange _ (2 * m)

/-- The composite walk reads the matching after the wiring's
matching at each slot. -/
private theorem compAt_read (m : Nat) (m1 m2 : List Nat) (x : Nat)
    (hx : x < 2 * m) :
    ground.getAt 0 (compAt m m1 m2) x
      = ground.getAt 0 m2 (ground.getAt 0 m1 x) := by
  show ground.getAt 0 ((List.range (2 * m)).map (fun i =>
    ground.getAt 0 m2 (ground.getAt 0 m1 i))) x = _
  rw [ground.getAt_map_range 0 _ (2 * m) x, if_pos hx]

/-- The composite walk at the full tuple wiring is a slot
permutation. -/
private theorem compAt_member (G : states.FList) (π : List Nat)
    (hπ : 0 < ground.countOf π (places.perms G.length))
    (vs : List Nat) (tup : List (List Nat)) (m2 : List Nat)
    (hm2 : m2.length = 2 * G.length) (hd : ground.distinctList vs)
    (ht : tupMem G vs tup)
    (hmt : ∀ w, 0 < ground.countOf w vs →
      (posIf G (w, false)).length = (posIf G (w, true)).length)
    (hcov : ∀ j, j < G.length →
      0 < ground.countOf (ground.getAt (0, false) G j).1 vs)
    (hb : ∀ x, x < m2.length → ground.getAt 0 m2 x < 2 * G.length) :
    0 < ground.countOf (compAt G.length (mOne G.length π)
      (wireAll G vs tup m2)) (places.perms (2 * G.length)) := by
  refine places.perm_of_reads _ _ (compAt_length _ _ _)
    (fun x hx => ?_) (fun x y hx hy he => ?_)
  · rw [compAt_read _ _ _ x hx]
    exact wireAll_bound G vs tup m2 ht hmt hb _ (by
      rw [hm2]
      exact mOne_bound G.length hπ x hx)
  · rw [compAt_read _ _ _ x hx, compAt_read _ _ _ y hy] at he
    have hw : ground.getAt 0 (mOne G.length π) x
        = ground.getAt 0 (mOne G.length π) y := by
      rw [← wireAll_invol G vs tup m2 hm2 hd ht hmt hcov _
          (mOne_bound G.length hπ x hx), he,
        wireAll_invol G vs tup m2 hm2 hd ht hmt hcov _
          (mOne_bound G.length hπ y hy)]
    rw [← mOne_invol G.length hπ x hx, hw, mOne_invol G.length hπ y hy]

/-- A variable's matchings travel the relabeling: at the slots of
the variable and at the slots the prior matchings related, the
doubled relabeling carries the relabeled matching's slot reads to
the matching's own. -/
private theorem matchVar_transport (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (v : Nat) (σ' τ' : List Nat)
    (hgv : (posIf G (v, false)).length = (posIf G (v, true)).length)
    (hσ' : 0 < ground.countOf σ'
      (places.perms (posIf G (v, false)).length))
    (hτ' : 0 < ground.countOf τ'
      (places.perms (posIf G (v, false)).length))
    (vs : List Nat) (M' M : List Nat)
    (hM' : M'.length = 2 * m) (hM : M.length = 2 * m)
    (hrel : ∀ j o, j < m → o < 2 →
      ¬ (ground.getAt (0, false) G' j).1 = v →
      ¬ 0 < ground.countOf (ground.getAt (0, false) G' j).1 vs →
      ground.getAt 0 (dbl ρ) (ground.getAt 0 M' (2 * j + o))
        = ground.getAt 0 M (ground.getAt 0 (dbl ρ) (2 * j + o))) :
    ∀ j o, j < m → o < 2 →
      ¬ 0 < ground.countOf (ground.getAt (0, false) G' j).1 vs →
      ground.getAt 0 (dbl ρ)
          (ground.getAt 0 (matchVar G' v σ' τ' M') (2 * j + o))
        = ground.getAt 0 (matchVar G v
            (conjBy (posIf G (v, false)).length (slotOf G G' ρ (v, false))
              (slotOf G G' ρ (v, true)) σ')
            (conjBy (posIf G (v, false)).length (slotOf G G' ρ (v, false))
              (slotOf G G' ρ (v, true)) τ') M)
          (ground.getAt 0 (dbl ρ) (2 * j + o)) := by
  intro j o hj ho hnot
  have heF := posIf_len_eq G G' ρ m hm hm' hr hg (v, false)
  have heT := posIf_len_eq G G' ρ m hm hm' hr hg (v, true)
  have hg'v : (posIf G' (v, false)).length
      = (posIf G' (v, true)).length := by
    rw [heF, heT, hgv]
  have ha := slotOf_member G G' ρ m hm hm' hr hg (v, false)
  have hb := slotOf_member' G G' ρ m hm hm' hr hg v hgv
  have hσ'' : 0 < ground.countOf σ'
      (places.perms (posIf G' (v, false)).length) := by
    rw [heF]
    exact hσ'
  have hτ'' : 0 < ground.countOf τ'
      (places.perms (posIf G' (v, false)).length) := by
    rw [heF]
    exact hτ'
  have hcσ := conjBy_member _ ha hb hσ'
  have hcτ := conjBy_member _ ha hb hτ'
  have hjm : j < G'.length := by
    rw [hm']
    exact hj
  have hM'2 : M'.length = 2 * G'.length := by
    rw [hm']
    exact hM'
  have hM2 : M.length = 2 * G.length := by
    rw [hm]
    exact hM
  by_cases hkey : (ground.getAt (0, false) G' j).1 = v
  · cases hdag : (ground.getAt (0, false) G' j).2 with
    | false =>
      have hf : ground.getAt (0, false) G' j = (v, false) := by
        rw [← hkey]
        exact congrArg (fun b => ((ground.getAt (0, false) G' j).1, b)) hdag
      have hmem := posIf_mem hjm hf
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G' (v, false)).length
          ∧ ground.getAt 0 (posIf G' (v, false)) s = j :=
        ⟨places.posOf j _, places.posOf_lt j _ hmem,
         places.getAt_posOf j _ hmem⟩
      have hsk : s < (posIf G (v, false)).length := by
        rw [← heF]
        exact hs
      have hsl := slotOf_lt G G' ρ m hm hm' hr hg (v, false) s hs
      have hbσ : ground.getAt 0 σ' s < (posIf G' (v, true)).length := by
        rw [← hg'v]
        exact perm_lt _ hσ'' s hs
      have hbτ : ground.getAt 0 τ' s < (posIf G' (v, true)).length := by
        rw [← hg'v]
        exact perm_lt _ hτ'' s hs
      match ltTwo o ho with
      | Or.inl h0 =>
        rw [h0]
        show ground.getAt 0 (dbl ρ) (ground.getAt 0 (matchVar G' v σ' τ' M')
            (2 * j)) = ground.getAt 0 (matchVar G v _ _ M)
            (ground.getAt 0 (dbl ρ) (2 * j))
        rw [← hjs, (matchVar_read G' v σ' τ' M' hM'2 hg'v hσ'' hτ'' s hs).1.1,
          dblOdd G G' ρ m hm hm' hr hg (v, true) _ hbσ,
          dblEven G G' ρ m hm hm' hr hg (v, false) s hs,
          (matchVar_read G v _ _ M hM2 hgv hcσ hcτ _ hsl).1.1,
          conjBy_rel _ ha hσ' s hsk]
      | Or.inr h1 =>
        rw [h1, ← hjs, (matchVar_read G' v σ' τ' M' hM'2 hg'v hσ'' hτ'' s hs).2.1,
          dblEven G G' ρ m hm hm' hr hg (v, true) _ hbτ,
          dblOdd G G' ρ m hm hm' hr hg (v, false) s hs,
          (matchVar_read G v _ _ M hM2 hgv hcσ hcτ _ hsl).2.1,
          conjBy_rel _ ha hτ' s hsk]
    | true =>
      have hf : ground.getAt (0, false) G' j = (v, true) := by
        rw [← hkey]
        exact congrArg (fun b => ((ground.getAt (0, false) G' j).1, b)) hdag
      have hmem := posIf_mem hjm hf
      have htl : places.posOf j (posIf G' (v, true))
          < (posIf G' (v, false)).length := by
        rw [hg'v]
        exact places.posOf_lt j _ hmem
      match ltTwo o ho with
      | Or.inr h1 =>
        obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G' (v, false)).length
            ∧ ground.getAt 0 (posIf G' (v, true))
                (ground.getAt 0 σ' s) = j :=
          ⟨ground.getAt 0 (places.invPerm _ σ')
            (places.posOf j (posIf G' (v, true))),
           perm_inv_lt _ hσ'' _ htl, by
            rw [perm_right _ hσ'' _ htl]
            exact places.getAt_posOf j _ hmem⟩
        have hsk : s < (posIf G (v, false)).length := by
          rw [← heF]
          exact hs
        have hsl := slotOf_lt G G' ρ m hm hm' hr hg (v, false) s hs
        have hbσ : ground.getAt 0 σ' s
            < (posIf G' (v, true)).length := by
          rw [← hg'v]
          exact perm_lt _ hσ'' s hs
        rw [h1, ← hjs, (matchVar_read G' v σ' τ' M' hM'2 hg'v hσ'' hτ'' s hs).1.2,
          dblEven G G' ρ m hm hm' hr hg (v, false) s hs,
          dblOdd G G' ρ m hm hm' hr hg (v, true) _ hbσ,
          conjBy_rel _ ha hσ' s hsk,
          (matchVar_read G v _ _ M hM2 hgv hcσ hcτ _ hsl).1.2]
      | Or.inl h0 =>
        obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G' (v, false)).length
            ∧ ground.getAt 0 (posIf G' (v, true))
                (ground.getAt 0 τ' s) = j :=
          ⟨ground.getAt 0 (places.invPerm _ τ')
            (places.posOf j (posIf G' (v, true))),
           perm_inv_lt _ hτ'' _ htl, by
            rw [perm_right _ hτ'' _ htl]
            exact places.getAt_posOf j _ hmem⟩
        have hsk : s < (posIf G (v, false)).length := by
          rw [← heF]
          exact hs
        have hsl := slotOf_lt G G' ρ m hm hm' hr hg (v, false) s hs
        have hbτ : ground.getAt 0 τ' s
            < (posIf G' (v, true)).length := by
          rw [← hg'v]
          exact perm_lt _ hτ'' s hs
        rw [h0]
        show ground.getAt 0 (dbl ρ) (ground.getAt 0 (matchVar G' v σ' τ' M')
            (2 * j)) = ground.getAt 0 (matchVar G v _ _ M)
            (ground.getAt 0 (dbl ρ) (2 * j))
        rw [← hjs, (matchVar_read G' v σ' τ' M' hM'2 hg'v hσ'' hτ'' s hs).2.2,
          dblOdd G G' ρ m hm hm' hr hg (v, false) s hs,
          dblEven G G' ρ m hm hm' hr hg (v, true) _ hbτ,
          conjBy_rel _ ha hτ' s hsk,
          (matchVar_read G v _ _ M hM2 hgv hcσ hcτ _ hsl).2.2]
  · have hmem := posIf_mem hjm (rfl : ground.getAt (0, false) G' j
      = ((ground.getAt (0, false) G' j).1, (ground.getAt (0, false) G' j).2))
    obtain ⟨a', ha', hja'⟩ : ∃ a', a' < (posIf G'
        ((ground.getAt (0, false) G' j).1,
          (ground.getAt (0, false) G' j).2)).length
        ∧ ground.getAt 0 (posIf G' ((ground.getAt (0, false) G' j).1,
          (ground.getAt (0, false) G' j).2)) a' = j :=
      ⟨places.posOf j _, places.posOf_lt j _ hmem,
       places.getAt_posOf j _ hmem⟩
    have hal := slotOf_lt G G' ρ m hm hm' hr hg
      ((ground.getAt (0, false) G' j).1, (ground.getAt (0, false) G' j).2)
      a' ha'
    have hx : 2 * j + o < 2 * m := by
      match ltTwo o ho with
      | Or.inl h0 =>
        rw [h0]
        exact twoLt hj
      | Or.inr h1 =>
        rw [h1]
        exact twoSuccLt hj
    rw [← hja',
      matchVar_off G' v _ hkey σ' τ' M' hg'v hσ'' hτ'' _ o ho a' ha',
      hja', hrel j o hj ho hkey hnot, ← hja']
    match ltTwo o ho with
    | Or.inl h0 =>
      rw [h0]
      show ground.getAt 0 M (ground.getAt 0 (dbl ρ)
          (2 * ground.getAt 0 (posIf G' _) a'))
        = ground.getAt 0 (matchVar G v _ _ M) (ground.getAt 0 (dbl ρ)
          (2 * ground.getAt 0 (posIf G' _) a'))
      rw [dblEven G G' ρ m hm hm' hr hg _ a' ha']
      exact (matchVar_off G v _ hkey _ _ M hgv hcσ hcτ _ 0
        (by decide +kernel) _ hal).symm
    | Or.inr h1 =>
      rw [h1, dblOdd G G' ρ m hm hm' hr hg _ a' ha']
      exact (matchVar_off G v _ hkey _ _ M hgv hcσ hcτ _ 1
        (by decide +kernel) _ hal).symm

/-- The tuple wiring travels the relabeling: at every slot whose
variable the tuple's variables cover, the doubled relabeling
carries the relabeled wiring's slot reads to the wiring's own. -/
private theorem wireAll_transport (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i)) :
    ∀ (vs : List Nat) (tup : List (List Nat)) (M' M : List Nat),
      tupMem G vs tup →
      (∀ w, 0 < ground.countOf w vs →
        (posIf G (w, false)).length = (posIf G (w, true)).length) →
      M'.length = 2 * m → M.length = 2 * m →
      (∀ j o, j < m → o < 2 →
        ¬ 0 < ground.countOf (ground.getAt (0, false) G' j).1 vs →
        ground.getAt 0 (dbl ρ) (ground.getAt 0 M' (2 * j + o))
          = ground.getAt 0 M (ground.getAt 0 (dbl ρ) (2 * j + o))) →
      ∀ j o, j < m → o < 2 →
        ground.getAt 0 (dbl ρ)
            (ground.getAt 0 (wireAll G' vs tup M') (2 * j + o))
          = ground.getAt 0 (wireAll G vs (conjTup G G' ρ vs tup) M)
            (ground.getAt 0 (dbl ρ) (2 * j + o))
  | [], _, _, _, _, _, _, _, hrel, j, o, hj, ho =>
    hrel j o hj ho (Nat.lt_irrefl 0)
  | _ :: _, [], _, _, h, _, _, _, _, _, _, _, _ => False.elim h
  | _ :: _, [_], _, _, h, _, _, _, _, _, _, _, _ => False.elim h
  | v :: vs, σ :: τ :: tup, M', M, ⟨h1, h2, h3⟩, hmt, hM', hM, hrel,
      j, o, hj, ho => by
    show ground.getAt 0 (dbl ρ)
        (ground.getAt 0 (wireAll G' vs tup (matchVar G' v σ τ M')) _)
      = ground.getAt 0 (wireAll G vs (conjTup G G' ρ vs tup)
          (matchVar G v _ _ M)) _
    refine wireAll_transport G G' ρ m hm hm' hr hg vs tup _ _ h3 (fun w hw => hmt w (ground.countOf_cons_pos hw))
      (by
        rw [matchVar_length]
        exact hM')
      (by
        rw [matchVar_length]
        exact hM)
      (fun j' o' hj' ho' hnot =>
        matchVar_transport G G' ρ m hm hm' hr hg v σ τ (hmt v (cntHead v vs))
          h1 h2 vs M' M hM' hM (fun j'' o'' hj'' ho'' hne hnot' =>
            hrel j'' o'' hj'' ho'' (fun hc => by
              rw [ground.countOf_cons] at hc
              have hc' := hc
              by_cases hkv : (ground.getAt (0, false) G' j'').1 = v
              · exact hne hkv
              · rw [if_neg hkv, Nat.zero_add] at hc'
                exact hnot' hc'))
          j' o' hj' ho' hnot)
      j o hj ho

/-- One tuple's term travels the relabeling: the relabeled site's
term at a tuple reads the site's own at the conjugated tuple. -/
private theorem termAt_transport (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (π π' : List Nat)
    (hπ : 0 < ground.countOf π (places.perms m))
    (hπ' : 0 < ground.countOf π' (places.perms m))
    (hcπ : ∀ s, s < m →
      ground.getAt 0 ρ (ground.getAt 0 π' s)
        = ground.getAt 0 π (ground.getAt 0 ρ s))
    (vs : List Nat) (tup : List (List Nat))
    (hd : ground.distinctList vs) (ht : tupMem G vs tup)
    (hmt : ∀ w, 0 < ground.countOf w vs →
      (posIf G (w, false)).length = (posIf G (w, true)).length)
    (hcov : ∀ j, j < G.length →
      0 < ground.countOf (ground.getAt (0, false) G j).1 vs)
    (hcov' : ∀ j, j < G'.length →
      0 < ground.countOf (ground.getAt (0, false) G' j).1 vs) :
    poly.oneValue
      (termAt G' (mOne m π') vs (List.replicate (2 * m) 0) [] tup)
      (termAt G (mOne m π) vs (List.replicate (2 * m) 0) []
        (conjTup G G' ρ vs tup)) := by
  have hdm := dbl_member m hr
  have hmt' : ∀ w, 0 < ground.countOf w vs →
      (posIf G' (w, false)).length = (posIf G' (w, true)).length :=
    fun w hw => by
      rw [posIf_len_eq G G' ρ m hm hm' hr hg (w, false),
        posIf_len_eq G G' ρ m hm hm' hr hg (w, true)]
      exact hmt w hw
  have ht' : tupMem G' vs tup :=
    tupMem_of_len G' G (fun v =>
      (posIf_len_eq G G' ρ m hm hm' hr hg (v, false)).symm) vs tup ht
  have htc := conjTup_mem G G' ρ m hm hm' hr hg vs tup hmt ht
  have hcm : 0 < ground.countOf (compAt G.length (mOne G.length π)
      (wireAll G vs (conjTup G G' ρ vs tup) (List.replicate (2 * G.length) 0)))
      (places.perms (2 * G.length)) :=
    compAt_member G π (by
        rw [hm]
        exact hπ) vs _ _ (ground.length_replicate 0 _) hd htc hmt hcov
      (replicate_bound _)
  have hcm' : 0 < ground.countOf (compAt G'.length (mOne G'.length π')
      (wireAll G' vs tup (List.replicate (2 * G'.length) 0)))
      (places.perms (2 * G'.length)) :=
    compAt_member G' π' (by
        rw [hm']
        exact hπ') vs _ _ (ground.length_replicate 0 _) hd ht' hmt' hcov'
      (replicate_bound _)
  rw [hm] at hcm
  rw [hm'] at hcm'
  have htr : ∀ x, x < 2 * m →
      ground.getAt 0 (dbl ρ) (ground.getAt 0 (compAt m (mOne m π')
        (wireAll G' vs tup (List.replicate (2 * m) 0))) x)
      = ground.getAt 0 (compAt m (mOne m π)
          (wireAll G vs (conjTup G G' ρ vs tup) (List.replicate (2 * m) 0)))
        (ground.getAt 0 (dbl ρ) x) := by
    intro x hx
    have hw := wireAll_transport G G' ρ m hm hm' hr hg vs tup
      (List.replicate (2 * m) 0) (List.replicate (2 * m) 0) ht hmt
      (ground.length_replicate 0 _) (ground.length_replicate 0 _)
      (fun j o hj _ hnot => absurd (hcov' j (by
        rw [hm']
        exact hj)) hnot)
    rw [compAt_read m _ _ x hx, compAt_read m _ _ _ (perm_lt _ hdm x hx),
      ← mOne_transport m π π' ρ hπ hπ' hr hcπ x hx]
    obtain ⟨j', hj', hj'x⟩ := halveLt (mOne_bound m hπ' x hx)
    match hj'x with
    | Or.inl hev =>
      rw [hev]
      exact hw j' 0 hj' (by decide +kernel)
    | Or.inr hod =>
      rw [hod]
      exact hw j' 1 hj' (by decide +kernel)
  have hkey : compAt m (mOne m π') (wireAll G' vs tup (List.replicate (2 * m) 0))
      = (places.invPerm (2 * m) (places.invPerm (2 * m) (dbl ρ))).map (fun j =>
          ground.getAt 0 (places.invPerm (2 * m) (dbl ρ))
            (ground.getAt 0 (compAt m (mOne m π) (wireAll G vs
              (conjTup G G' ρ vs tup) (List.replicate (2 * m) 0))) j)) := by
    refine ground.getAt_ext 0 _ _ (by
        rw [compAt_length, ground.length_map, places.length_invPerm]) ?_
    intro i hi
    rw [compAt_length] at hi
    rw [ground.getAt_map 0 0 _ (places.invPerm (2 * m)
        (places.invPerm (2 * m) (dbl ρ))) i (by
          rw [places.length_invPerm]
          exact hi),
      places.invPerm_invPerm (2 * m) hdm, ← htr i hi,
      perm_left (2 * m) hdm _ (perm_lt (2 * m) hcm' i hi)]
  show poly.oneValue
    (([] ++ coefAll G' vs tup).foldr poly.mul (dfPow ((places.cyclesOf
      (compAt G'.length (mOne m π') (wireAll G' vs tup
        (List.replicate (2 * m) 0)))).length / 2)))
    (([] ++ coefAll G vs (conjTup G G' ρ vs tup)).foldr poly.mul
      (dfPow ((places.cyclesOf (compAt G.length (mOne m π) (wireAll G vs
        (conjTup G G' ρ vs tup) (List.replicate (2 * m) 0)))).length / 2)))
  rw [hm, hm', hkey, places.cyclesOf_transport (2 * m) hcm
    (places.invPerm_member (2 * m) hdm)]
  exact foldr_mul_ov _ _ _ _
    (coefAll_transport G G' ρ m hm hm' hr hg vs tup hmt ht)
    (poly.oneValue_refl _)

/-- The evaluation at a relabeled site and its carried wiring
reads the site's own value: `rem:kernel`'s gauge-mode sentence at
the carried contraction sum — the letters' positions are a gauge
mode of the spelling, so the sum's value is the words' alone. -/
private theorem evalPhi_relabel (G G' : states.FList)
    (π π' ρ : List Nat) (m : Nat)
    (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hπ : 0 < ground.countOf π (places.perms m))
    (hπ' : 0 < ground.countOf π' (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (0, false) G' i
        = ground.getAt (0, false) G (ground.getAt 0 ρ i))
    (hcπ : ∀ s, s < m →
      ground.getAt 0 ρ (ground.getAt 0 π' s)
        = ground.getAt 0 π (ground.getAt 0 ρ s)) :
    genericlift.crossNull (evalPhi G' π') (evalPhi G π) := by
  have hvars := varsOf_relabel G G' ρ m hm hm' hr hg
  have hlen : ∀ v, (posIf G' (v, false)).length = (posIf G (v, false)).length
      ∧ (posIf G' (v, true)).length = (posIf G (v, true)).length :=
    fun v => ⟨posIf_len_eq G G' ρ m hm hm' hr hg (v, false),
      posIf_len_eq G G' ρ m hm hm' hr hg (v, true)⟩
  have hfwd : guardOf G = true → guardOf G' = true := fun hgd => by
    refine ground.all_of_mem_intro _ _ (fun v hv => ?_)
    show ((posIf G' (v, false)).length == (posIf G' (v, true)).length) = true
    rw [(hlen v).1, (hlen v).2]
    exact ground.all_of_mem _ _ hgd v (by
      rw [← hvars]
      exact hv)
  have hbwd : guardOf G' = true → guardOf G = true := fun hgd => by
    refine ground.all_of_mem_intro _ _ (fun v hv => ?_)
    show ((posIf G (v, false)).length == (posIf G (v, true)).length) = true
    rw [← (hlen v).1, ← (hlen v).2]
    exact ground.all_of_mem _ _ hgd v (by
      rw [hvars]
      exact hv)
  by_cases hgd : guardOf G = true
  · have hgd' := hfwd hgd
    rw [evalPhi_unfold G' π', evalPhi_unfold G π, if_pos hgd', if_pos hgd]
    refine (genericlift.crossNull_ov _ _).mpr ?_
    have hD : (varsOf G').foldr (fun v d =>
        poly.mul (split.pminor (gramWg (posIf G' (v, false)).length)) d)
        poly.one
        = (varsOf G).foldr (fun v d =>
          poly.mul (split.pminor (gramWg (posIf G (v, false)).length)) d)
          poly.one := by
      rw [hvars]
      exact foldr_ext _ _ (fun v d => by rw [(hlen v).1]) _ _
    rw [hD]
    refine poly.mul_congr_left ?_ _
    have hmt : ∀ w, 0 < ground.countOf w (varsOf G) →
        (posIf G (w, false)).length = (posIf G (w, true)).length :=
      fun w hw => ground.beqEqOf (ground.all_of_mem _ _ hgd w
        (ground.mem_of_countOf_pos w _ hw))
    have hcov : ∀ j, j < G.length →
        0 < ground.countOf (ground.getAt (0, false) G j).1 (varsOf G) :=
      fun j hj => varsOf_cover G j hj
    have hcov' : ∀ j, j < G'.length →
        0 < ground.countOf (ground.getAt (0, false) G' j).1 (varsOf G) :=
      fun j hj => by
        rw [← hvars]
        exact varsOf_cover G' j hj
    rw [hm, hm', hvars]
    refine poly.oneValue_trans (contract_flat G' _ _ _ _ _)
      (poly.oneValue_trans ?_ (poly.oneValue_symm (contract_flat G _ _ _ _ _)))
    refine poly.polyFoldLaws.opCongr (poly.oneValue_refl []) ?_
    rw [domsOf_relabel G G' ρ m hm hm' hr hg (varsOf G)]
    refine ground.famFold_bij_ov poly.polyFoldLaws.toCommLaws [] _ _
      (ground.distinct_prodLists _ (domsOf_distinct G _))
      (g := conjTup G G' ρ (varsOf G)) (h := conjTupInv G G' ρ (varsOf G))
      (fun tup ht => conjTup_inv G G' ρ m hm hm' hr hg _ tup hmt
        (tupMem_of_count G _ tup ht))
      (fun tup ht => conjTup_inv' G G' ρ m hm hm' hr hg _ tup hmt
        (tupMem_of_count G _ tup ht))
      (fun tup ht => count_of_tupMem G _ _
        (conjTup_mem G G' ρ m hm hm' hr hg _ tup hmt
          (tupMem_of_count G _ tup ht)))
      (fun tup ht => count_of_tupMem G _ _
        (conjTupInv_mem G G' ρ m hm hm' hr hg _ tup hmt
          (tupMem_of_count G _ tup ht)))
      (fun tup ht => ?_)
    exact termAt_transport G G' ρ m hm hm' hr hg π π' hπ hπ' hcπ
      (varsOf G) tup (varsOf_distinct G) (tupMem_of_count G _ tup ht) hmt
      hcov hcov'
  · have hgd' : ¬ guardOf G' = true := fun h => hgd (hbwd h)
    rw [evalPhi_unfold G' π', evalPhi_unfold G π, if_neg hgd', if_neg hgd]
    exact (by decide +kernel : genericlift.crossNull poly.pZero poly.pZero)

/-- `rem:kernel`'s gauge-mode sentence at the carried evaluation:
the states are indexed by the multisets of oriented cyclic words,
so a letter-preserving relabeling of the site and its wiring reads
one value — the relabeled generator's contraction sum and the
generator's own cross to the sum's unit.  The orientation is the
pull: the site reads at the relabeling's places, the wiring
composes between the partner and the relabeling — the reversed
composition parts at a relabeling off its own partner, the check
module's refusal cell. -/
theorem evalPhi_transport (G : states.FList) (π ρ : List Nat)
    (hπ : 0 < ground.countOf π (places.perms G.length))
    (hρ : 0 < ground.countOf ρ (places.perms G.length)) :
    genericlift.crossNull
      (evalPhi (ρ.map (fun j =>
          ground.getAt (0, false) G j))
        (ρ.map (fun j => ground.getAt 0
          (places.invPerm G.length ρ) (ground.getAt 0 π j))))
      (evalPhi G π) := by
  have hrlen := (places.perm_member_reads hρ).1
  have hread : ∀ s, s < G.length →
      ground.getAt 0 (ρ.map (fun j =>
          ground.getAt 0 (places.invPerm G.length ρ)
            (ground.getAt 0 π j))) s
        = ground.getAt 0 (places.invPerm G.length ρ)
          (ground.getAt 0 π (ground.getAt 0 ρ s)) := fun s hs =>
    ground.getAt_map 0 0 _ ρ s (by
      rw [hrlen]
      exact hs)
  have hplt : ∀ s, s < G.length →
      ground.getAt 0 π (ground.getAt 0 ρ s) < G.length := fun s hs =>
    perm_lt G.length hπ _ (perm_lt G.length hρ s hs)
  refine evalPhi_relabel G
    (ρ.map (fun j => ground.getAt (0, false) G j)) π
    (ρ.map (fun j => ground.getAt 0 (places.invPerm G.length ρ)
      (ground.getAt 0 π j))) ρ G.length rfl ?_ hρ hπ ?_ ?_ ?_
  · show (ρ.map (fun j => ground.getAt (0, false) G j)).length
      = G.length
    rw [ground.length_map, hrlen]
  · refine places.perm_of_reads _ _ (by
        show (ρ.map (fun j => ground.getAt 0
          (places.invPerm G.length ρ) (ground.getAt 0 π j))).length
          = G.length
        rw [ground.length_map, hrlen]) (fun i hi => ?_)
      (fun i j hi hj he => ?_)
    · rw [hread i hi]
      exact perm_inv_lt G.length hρ _ (hplt i hi)
    · rw [hread i hi, hread j hj] at he
      refine places.perm_inj G.length hρ i j hi hj ?_
      refine places.perm_inj G.length hπ _ _ (perm_lt G.length hρ i hi)
        (perm_lt G.length hρ j hj) ?_
      refine places.perm_inj G.length
        (places.invPerm_member G.length hρ) _ _ (hplt i hi)
        (hplt j hj) he
  · intro i hi
    show ground.getAt (0, false) (ρ.map (fun j =>
      ground.getAt (0, false) G j)) i = _
    exact ground.getAt_map 0 (0, false) _ ρ i (by
      rw [hrlen]
      exact hi)
  · intro s hs
    rw [hread s hs, perm_right G.length hρ _ (hplt s hs)]

end wg
