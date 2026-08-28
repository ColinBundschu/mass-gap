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
evaluation of a generator is the contraction sum: per variable at
matched dagger counts, over the permutation pairs `(σ, τ)`, the
`δ`-wirings close the chains into loops — the wiring's matching
against the `σ, τ`-matchings at the index slots, `σ` the undaggered
rows against the daggered columns and `τ` the exchange (a daggered
factor's conjugate row is its own column), the loop count the
alternating cycles' half count (`evalPhi`, `matchIn`,
the loop fold `places.cyclesOf`'s) — each loop a factor `d_f`, the
sum one numerator fold over the one shared determinant — the
adjugate and determinant hoisted once per evaluation, the
factorial route's recorded headroom the next tier's rework site —
and a mismatched dagger count reads the sum's unit.  The pairing
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
pairing mirrors at the engine argument (`pairPhiSer`,
`pairFullSer` the combinations' bilinear fold).  And
`rem:kernel`'s gauge-mode sentence reads at the carried
evaluation: the states are indexed gauge-free by the multisets of
oriented cyclic words, so a letter-preserving relabeling of the
site and its carried wiring reads the generator's own value
(`evalPhi_transport`) — the letters' positions carried by the
per-letter slot maps, the composite graph's slots by the doubled
relabeling, the loop count by `places.cyclesOf_transport`, and the
numerator's four-axis fold reindexed along the conjugated words at
the Weingarten column's own travel.
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
    (fun i => ground.getAt (false, false) G i == f)

/-- One variable's matching written into the slot list: per slot
the row end against the matched column end, both directions. -/
private def matchIn (m2 : List Nat) (ps qs σ : List Nat)
    (offP offQ : Nat) : List Nat :=
  (List.range ps.length).foldl (fun acc s =>
    let a := 2 * ground.getAt 0 ps s + offP
    let b := 2 * ground.getAt 0 qs (ground.getAt 0 σ s) + offQ
    (acc.set a b).set b a) m2

/-- The evaluation of a generator, the contraction sum: per
variable at matched dagger counts, over the permutation pairs, the
`δ`-wirings close into loops — the wiring's matching at the row
and column slots against the `σ, τ`-matchings, the loop count the
alternating cycles' half count — each loop a factor `d_f`. -/
def evalPhi (G : states.FList) (π : List Nat) : poly.PPair :=
  let m := G.length
  let uU := posIf G (false, false)
  let dU := posIf G (false, true)
  let uV := posIf G (true, false)
  let dV := posIf G (true, true)
  if uU.length == dU.length && uV.length == dV.length then
    let permsU := places.perms uU.length
    let permsV := places.perms uV.length
    let adjU := genericlift.padj (gramWg uU.length)
    let detU := split.pminor (gramWg uU.length)
    let adjV := genericlift.padj (gramWg uV.length)
    let detV := split.pminor (gramWg uV.length)
    let idU := places.idxOf (List.range uU.length) permsU
    let idV := places.idxOf (List.range uV.length) permsV
    let m1 := (List.range m).foldl (fun acc i =>
      let a := 2 * i
      let b := 2 * ground.getAt 0 π i + 1
      (acc.set a b).set b a) (List.replicate (2 * m) 0)
    let num := permsU.foldl (fun acc σU =>
      permsU.foldl (fun acc τU =>
        permsV.foldl (fun acc σV =>
          permsV.foldl (fun acc τV =>
            let m2 := matchIn (matchIn (matchIn (matchIn
              (List.replicate (2 * m) 0) uU dU σU 0 1) uU dU τU 1 0)
              uV dV σV 0 1) uV dV τV 1 0
            let comp := (List.range (2 * m)).map (fun i =>
              ground.getAt 0 m2 (ground.getAt 0 m1 i))
            let loops := (places.cyclesOf comp).length / 2
            let nU := ground.getAt [] (ground.getAt [] adjU
              (places.idxOf (places.expo σU
                (places.invPerm uU.length τU)) permsU)) idU
            let nV := ground.getAt [] (ground.getAt [] adjV
              (places.idxOf (places.expo σV
                (places.invPerm uV.length τV)) permsV)) idV
            poly.add acc (poly.mul nU (poly.mul nV (dfPow loops))))
            acc) acc) acc) ([] : Poly)
    (num, poly.mul detU detV)
  else poly.pZero

/-- The conjugation: the daggers flip. -/
def conjF (F : states.FList) : states.FList :=
  F.map (fun f => (f.1, !f.2))

/-- The pairing of two generators at their factor lists,
`Eval(Φ̄_A Φ_B)`: the conjugated key — the daggers flipped, the
wiring transposed — against the second at the concatenated
site. -/
def pairPhi (Fa Fb : states.FList) (πa πb : List Nat) :
    poly.PPair :=
  evalPhi (conjF Fa ++ Fb)
    (places.invPerm Fa.length πa ++ states.shiftW Fa.length πb)

/-- The pairing of two states at their factor lists, the
combinations' bilinear fold at the certified reduction:
`lem:genericlift`'s `pAddR` accumulates, so the representative
moves to the descent's own at every term and the fold's value is
the displayed sum's, `pReduce_read` the bridge. -/
def pairFull (Fa Fb : states.FList) (a b : states.Comb) :
    poly.PPair :=
  a.foldl (fun acc ea => b.foldl (fun acc2 eb =>
    genericlift.pAddR acc2 (poly.pMul
      (poly.pMul ea.2 eb.2) (pairPhi Fa Fb ea.1 eb.1))) acc)
    poly.pZero

/-! The `B`, `C` and `D` member tier: the presentation at the
defining factors' pair partitions with the member Gram
(`lem:serpairing`), `prop:wg`'s member display. -/

/-- The factors at one variable across both dagger reads, the
member presentation's slot list — the `u`-th factor in list order
the local slot `u`. -/
private def posVar (G : states.FList) (v : Bool) : List Nat :=
  (List.range G.length).filter
    (fun i => (ground.getAt (false, false) G i).1 == v)

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

/-- The member engine's core, `evalPhi`'s architecture at the pair
partitions: per variable at an even factor count — else the sum's
unit — the fold over the partition pairs of the member adjugate
entries against the loop value at the composite walk's count, the
adjugate and determinant hoisted once per evaluation, the signed
series negating at an odd walk parity. -/
private def evalSer (gram : Nat → split.PMat) (loopPoly : Nat → Poly)
    (signed : Bool) (G : states.FList) (π : List Nat) :
    poly.PPair :=
  let m := G.length
  let pU := posVar G false
  let pV := posVar G true
  if pU.length % 2 == 0 && pV.length % 2 == 0 then
    let kU := pU.length / 2
    let kV := pV.length / 2
    let partsU := serpairing.allParts kU
    let partsV := serpairing.allParts kV
    let adjU := genericlift.padj (gram kU)
    let detU := split.pminor (gram kU)
    let adjV := genericlift.padj (gram kV)
    let detV := split.pminor (gram kV)
    let dag := G.map (fun f => f.2)
    let invw := places.invPerm m π
    let num := partsU.foldl (fun acc PU =>
      partsU.foldl (fun acc QU =>
        partsV.foldl (fun acc PV =>
          partsV.foldl (fun acc QV =>
            let edges :=
              pairEdges pU (rvar m dag) PU
              ++ pairEdges pV (rvar m dag) PV
              ++ pairEdges pU (svar m dag invw) QU
              ++ pairEdges pV (svar m dag invw) QV
              ++ dagEdges m dag invw
            let w := loopFoldSer edges
            let lp := if signed && w.2 % 2 == 1
              then poly.neg (loopPoly w.1) else loopPoly w.1
            let nU := ground.getAt [] (ground.getAt [] adjU
              (places.idxOf PU partsU)) (places.idxOf QU partsU)
            let nV := ground.getAt [] (ground.getAt [] adjV
              (places.idxOf PV partsV)) (places.idxOf QV partsV)
            poly.add acc (poly.mul nU (poly.mul nV lp)))
            acc) acc) acc) ([] : Poly)
    (num, poly.mul detU detV)
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

/-- The member pairing of two generators at an engine, `pairPhi`'s
body: the conjugated key against the second at the concatenated
site. -/
def pairPhiSer (ev : states.FList → List Nat → poly.PPair)
    (Fa Fb : states.FList) (πa πb : List Nat) : poly.PPair :=
  ev (conjF Fa ++ Fb)
    (places.invPerm Fa.length πa ++ states.shiftW Fa.length πb)

/-- The member pairing of two states at an engine, `pairFull`'s
bilinear fold at the certified reduction. -/
def pairFullSer (ev : states.FList → List Nat → poly.PPair)
    (Fa Fb : states.FList) (a b : states.Comb) : poly.PPair :=
  a.foldl (fun acc ea => b.foldl (fun acc2 eb =>
    genericlift.pAddR acc2 (poly.pMul
      (poly.pMul ea.2 eb.2)
      (pairPhiSer ev Fa Fb ea.1 eb.1))) acc)
    poly.pZero

/-! `rem:kernel`'s gauge-mode tier: the evaluation's relabeling
read.  The states are indexed gauge-free by the multisets of
oriented cyclic words in the four letters, so the positions of
repeated factors are a gauge mode of the `(π, positions)`
spelling; at the carried evaluation the sentence reads as the
contraction sum's one value at a letter-preserving relabeling of
the site and its wiring (`evalPhi_transport`).  The relabeling's
slot maps carry each letter's positions across (`slotOf`), the
doubled relabeling carries the composite graph's slots (`dbl`),
the two matchings travel with it (`mOne_transport`,
`wireOf_transport`), the composite's loop count is the wiring's
own at `places.cyclesOf_transport`, and the numerator's four-axis
fold reindexes along the conjugated words at the Weingarten
column's own transport. -/
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
      = if ground.getAt (false, false) G i = f then
          (if i < G.length then 1 else 0) else 0 := by
  show ground.countOf i ((List.range G.length).filter
      (fun j => ground.getAt (false, false) G j == f)) = _
  rw [ground.countOf_filter
      (fun j => ground.getAt (false, false) G j == f) i
      (List.range G.length),
    ground.countOf_range i G.length]
  by_cases hf : ground.getAt (false, false) G i = f
  · rw [hf, ground.prodBeqIntro ground.boolEqBeq
      ground.boolEqBeq f, if_pos (rfl : f = f)]
    rfl
  · rw [ground.prodBeqRefuse (fun _ _ hh => ground.boolBeqEq hh)
      (fun _ _ hh => ground.boolBeqEq hh) hf, if_neg hf]
    rfl

/-- A place reading the letter sits in the letter's positions. -/
private theorem posIf_mem {G : states.FList} {f : states.Factor}
    {i : Nat} (hi : i < G.length)
    (he : ground.getAt (false, false) G i = f) :
    0 < ground.countOf i (posIf G f) := by
  rw [posIf_count G f i, if_pos he, if_pos hi]
  exact Nat.succ_pos 0

/-- The letter's positions sit inside the site. -/
private theorem posIf_lt {G : states.FList} {f : states.Factor}
    {i : Nat} (h : 0 < ground.countOf i (posIf G f)) :
    i < G.length := by
  rw [posIf_count G f i] at h
  by_cases he : ground.getAt (false, false) G i = f
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
    ground.getAt (false, false) G i = f := by
  by_cases he : ground.getAt (false, false) G i = f
  · exact he
  · rw [posIf_count G f i, if_neg he] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- The letter's positions are distinct. -/
private theorem posIf_dist (G : states.FList) (f : states.Factor)
    (i : Nat) : ground.countOf i (posIf G f) ≤ 1 := by
  rw [posIf_count G f i]
  by_cases he : ground.getAt (false, false) G i = f
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
    ground.getAt (false, false) G (ground.getAt 0 (posIf G f) s)
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
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
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
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
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
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
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
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
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
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
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
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
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

/-- The wiring's matching: each place's row slot against its
image's column slot, both directions. -/
private def mOne (m : Nat) (π : List Nat) : List Nat :=
  (List.range m).foldl (fun acc i =>
    (acc.set (2 * i) (2 * ground.getAt 0 π i + 1)).set
      (2 * ground.getAt 0 π i + 1) (2 * i))
    (List.replicate (2 * m) 0)

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

/-- The matched-dagger-count guard, one read per variable. -/
private def guardOf (G : states.FList) : Bool :=
  (posIf G (false, false)).length == (posIf G (false, true)).length
    && (posIf G (true, false)).length == (posIf G (true, true)).length

/-- The first matching, the undaggered `U` rows against the
daggered columns. -/
private def wire1 (G : states.FList) (σU : List Nat) : List Nat :=
  matchIn (List.replicate (2 * G.length) 0)
    (posIf G (false, false)) (posIf G (false, true)) σU 0 1

/-- The second matching joined, the `U` exchange. -/
private def wire2 (G : states.FList) (σU τU : List Nat) : List Nat :=
  matchIn (wire1 G σU)
    (posIf G (false, false)) (posIf G (false, true)) τU 1 0

/-- The third matching joined, the `V` rows against the
columns. -/
private def wire3 (G : states.FList) (σU τU σV : List Nat) :
    List Nat :=
  matchIn (wire2 G σU τU)
    (posIf G (true, false)) (posIf G (true, true)) σV 0 1

/-- The four matchings joined, the term's whole slot wiring. -/
private def wireOf (G : states.FList) (σU τU σV τV : List Nat) :
    List Nat :=
  matchIn (wire3 G σU τU σV)
    (posIf G (true, false)) (posIf G (true, true)) τV 1 0

/-- The second matching's one-step unfolding. -/
private theorem wire2_unfold (G : states.FList) (σU τU : List Nat) :
    wire2 G σU τU = matchIn (wire1 G σU)
      (posIf G (false, false)) (posIf G (false, true)) τU 1 0 := rfl

/-- The third matching's one-step unfolding. -/
private theorem wire3_unfold (G : states.FList)
    (σU τU σV : List Nat) :
    wire3 G σU τU σV = matchIn (wire2 G σU τU)
      (posIf G (true, false)) (posIf G (true, true)) σV 0 1 := rfl

/-- The joined wiring's one-step unfolding. -/
private theorem wireOf_unfold (G : states.FList)
    (σU τU σV τV : List Nat) :
    wireOf G σU τU σV τV = matchIn (wire3 G σU τU σV)
      (posIf G (true, false)) (posIf G (true, true)) τV 1 0 := rfl

/-- The first matching's place count is the doubled site's. -/
private theorem wire1_length (G : states.FList) (σU : List Nat) :
    (wire1 G σU).length = 2 * G.length := by
  show (matchIn (List.replicate (2 * G.length) 0) _ _ _ _ _).length
    = 2 * G.length
  rw [matchIn_length, ground.length_replicate]

/-- The second matching's place count is the doubled site's. -/
private theorem wire2_length (G : states.FList) (σU τU : List Nat) :
    (wire2 G σU τU).length = 2 * G.length := by
  rw [wire2_unfold, matchIn_length, wire1_length]

/-- The third matching's place count is the doubled site's. -/
private theorem wire3_length (G : states.FList)
    (σU τU σV : List Nat) :
    (wire3 G σU τU σV).length = 2 * G.length := by
  rw [wire3_unfold, matchIn_length, wire2_length]

/-- The composite walk, the matchings read after the wiring's
matching slot by slot. -/
private def compOf (G : states.FList) (π σU τU σV τV : List Nat) :
    List Nat :=
  (List.range (2 * G.length)).map (fun i =>
    ground.getAt 0 (wireOf G σU τU σV τV)
      (ground.getAt 0 (mOne G.length π) i))

/-- The `U` variable's Weingarten entry at a permutation pair. -/
private def nUOf (G : states.FList) (σ τ : List Nat) : poly.Poly :=
  ground.getAt [] (ground.getAt []
    (genericlift.padj (gramWg (posIf G (false, false)).length))
    (places.idxOf (places.expo σ (places.invPerm
      (posIf G (false, false)).length τ))
      (places.perms (posIf G (false, false)).length)))
    (places.idxOf (List.range (posIf G (false, false)).length)
      (places.perms (posIf G (false, false)).length))

/-- The `V` variable's Weingarten entry at a permutation pair. -/
private def nVOf (G : states.FList) (σ τ : List Nat) : poly.Poly :=
  ground.getAt [] (ground.getAt []
    (genericlift.padj (gramWg (posIf G (true, false)).length))
    (places.idxOf (places.expo σ (places.invPerm
      (posIf G (true, false)).length τ))
      (places.perms (posIf G (true, false)).length)))
    (places.idxOf (List.range (posIf G (true, false)).length)
      (places.perms (posIf G (true, false)).length))

/-- One tuple's term: the two Weingarten entries against the
loop count's power. -/
private def termOf (G : states.FList) (π σU τU σV τV : List Nat) :
    poly.Poly :=
  poly.mul (nUOf G σU τU) (poly.mul (nVOf G σV τV)
    (dfPow ((places.cyclesOf (compOf G π σU τU σV τV)).length / 2)))

/-- The numerator, the four-axis fold of the terms. -/
private def numOf (G : states.FList) (π : List Nat) : poly.Poly :=
  (places.perms (posIf G (false, false)).length).foldl (fun acc σU =>
    (places.perms (posIf G (false, false)).length).foldl (fun acc τU =>
      (places.perms (posIf G (true, false)).length).foldl (fun acc σV =>
        (places.perms (posIf G (true, false)).length).foldl
          (fun acc τV => poly.add acc (termOf G π σU τU σV τV))
          acc) acc) acc) ([] : poly.Poly)

/-- The numerator's fold spelled at the term function. -/
private theorem numOf_unfold (G : states.FList) (π : List Nat) :
    numOf G π =
      (places.perms (posIf G (false, false)).length).foldl
        (fun acc σU =>
          (places.perms (posIf G (false, false)).length).foldl
            (fun acc τU =>
              (places.perms (posIf G (true, false)).length).foldl
                (fun acc σV =>
                  (places.perms (posIf G (true, false)).length).foldl
                    (fun acc τV =>
                      poly.add acc (termOf G π σU τU σV τV))
                    acc) acc) acc) ([] : poly.Poly) := rfl

/-- The evaluation at its named parts: the guard, the numerator
fold and the shared determinant. -/
private theorem evalPhi_bridge (G : states.FList) (π : List Nat) :
    evalPhi G π =
      (if guardOf G = true then
        (numOf G π,
         poly.mul
           (split.pminor (gramWg (posIf G (false, false)).length))
           (split.pminor (gramWg (posIf G (true, false)).length)))
       else poly.pZero) := rfl

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

/-- The first call's slots: the undaggered `U` place reads the
daggered place at its `σ`-match, and back. -/
private theorem wireOf_read1 (G : states.FList)
    (σU τU σV τV : List Nat)
    (hgU : (posIf G (false, false)).length
      = (posIf G (false, true)).length)
    (hgV : (posIf G (true, false)).length
      = (posIf G (true, true)).length)
    (hσU : 0 < ground.countOf σU
      (places.perms (posIf G (false, false)).length))
    (hτU : 0 < ground.countOf τU
      (places.perms (posIf G (false, false)).length))
    (hσV : 0 < ground.countOf σV
      (places.perms (posIf G (true, false)).length))
    (hτV : 0 < ground.countOf τV
      (places.perms (posIf G (true, false)).length))
    (s : Nat) (hs : s < (posIf G (false, false)).length) :
    ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (false, false)) s)
      = 2 * ground.getAt 0 (posIf G (false, true))
          (ground.getAt 0 σU s) + 1
    ∧ ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (false, true))
          (ground.getAt 0 σU s) + 1)
      = 2 * ground.getAt 0 (posIf G (false, false)) s := by
  have hbU := sigLt G (false, false) (false, true) hσU hgU
  have hbT := sigLt G (false, false) (false, true) hτU hgU
  have hbV := sigLt G (true, false) (true, true) hσV hgV
  have hbW := sigLt G (true, false) (true, true) hτV hgV
  have hcall := matchIn_read (List.replicate (2 * G.length) 0)
    (posIf G (false, false)) (posIf G (false, true)) σU 0 1
    (fun t ht => by
      rw [ground.length_replicate]
      exact slotLt G (false, false) t 0 (by decide +kernel) ht)
    (fun t ht => by
      rw [ground.length_replicate]
      exact slotLt G (false, true) _ 1 (by decide +kernel) (hbU t ht))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (posIf_inj G (false, false))
    (qsInj G (false, false) (false, true) hσU hgU) s hs
  refine ⟨?_, ?_⟩
  · show ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (false, false)) s + 0) = _
    rw [wireOf_unfold,
      matchIn_off_slot G (wire3 G σU τU σV) (false, false)
        (true, false) (true, true) τV hbW 1 0 0
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inl (by decide +kernel)) s hs,
      wire3_unfold,
      matchIn_off_slot G (wire2 G σU τU) (false, false)
        (true, false) (true, true) σV hbV 0 1 0
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inl (by decide +kernel)) s hs,
      wire2_unfold,
      matchIn_off_slot G (wire1 G σU) (false, false)
        (false, false) (false, true) τU hbT 1 0 0
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inr (by decide +kernel)) (Or.inl (by decide +kernel)) s hs]
    exact hcall.1
  · rw [wireOf_unfold,
      matchIn_off_slot G (wire3 G σU τU σV) (false, true)
        (true, false) (true, true) τV hbW 1 0 1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inl (by decide +kernel)) _ (hbU s hs),
      wire3_unfold,
      matchIn_off_slot G (wire2 G σU τU) (false, true)
        (true, false) (true, true) σV hbV 0 1 1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inl (by decide +kernel)) _ (hbU s hs),
      wire2_unfold,
      matchIn_off_slot G (wire1 G σU) (false, true)
        (false, false) (false, true) τU hbT 1 0 1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inr (by decide +kernel)) _ (hbU s hs)]
    exact hcall.2

/-- The second call's slots: the daggered `U` place reads the
undaggered place at its `τ`-match, and back. -/
private theorem wireOf_read2 (G : states.FList)
    (σU τU σV τV : List Nat)
    (hgU : (posIf G (false, false)).length
      = (posIf G (false, true)).length)
    (hgV : (posIf G (true, false)).length
      = (posIf G (true, true)).length)
    (hτU : 0 < ground.countOf τU
      (places.perms (posIf G (false, false)).length))
    (hσV : 0 < ground.countOf σV
      (places.perms (posIf G (true, false)).length))
    (hτV : 0 < ground.countOf τV
      (places.perms (posIf G (true, false)).length))
    (s : Nat) (hs : s < (posIf G (false, false)).length) :
    ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (false, false)) s + 1)
      = 2 * ground.getAt 0 (posIf G (false, true))
          (ground.getAt 0 τU s)
    ∧ ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (false, true))
          (ground.getAt 0 τU s))
      = 2 * ground.getAt 0 (posIf G (false, false)) s + 1 := by
  have hbT := sigLt G (false, false) (false, true) hτU hgU
  have hbV := sigLt G (true, false) (true, true) hσV hgV
  have hbW := sigLt G (true, false) (true, true) hτV hgV
  have hcall := matchIn_read (wire1 G σU)
    (posIf G (false, false)) (posIf G (false, true)) τU 1 0
    (fun t ht => by
      rw [wire1_length]
      exact slotLt G (false, false) t 1 (by decide +kernel) ht)
    (fun t ht => by
      rw [wire1_length]
      exact slotLt G (false, true) _ 0 (by decide +kernel) (hbT t ht))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (posIf_inj G (false, false))
    (qsInj G (false, false) (false, true) hτU hgU) s hs
  refine ⟨?_, ?_⟩
  · rw [wireOf_unfold,
      matchIn_off_slot G (wire3 G σU τU σV) (false, false)
        (true, false) (true, true) τV hbW 1 0 1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inl (by decide +kernel)) s hs,
      wire3_unfold,
      matchIn_off_slot G (wire2 G σU τU) (false, false)
        (true, false) (true, true) σV hbV 0 1 1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inl (by decide +kernel)) s hs,
      wire2_unfold]
    exact hcall.1
  · show ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (false, true))
          (ground.getAt 0 τU s) + 0) = _
    rw [wireOf_unfold,
      matchIn_off_slot G (wire3 G σU τU σV) (false, true)
        (true, false) (true, true) τV hbW 1 0 0
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inl (by decide +kernel)) _ (hbT s hs),
      wire3_unfold,
      matchIn_off_slot G (wire2 G σU τU) (false, true)
        (true, false) (true, true) σV hbV 0 1 0
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inl (by decide +kernel)) _ (hbT s hs),
      wire2_unfold]
    exact hcall.2

/-- The third call's slots: the undaggered `V` place reads the
daggered place at its `σ`-match, and back. -/
private theorem wireOf_read3 (G : states.FList)
    (σU τU σV τV : List Nat)
    (hgV : (posIf G (true, false)).length
      = (posIf G (true, true)).length)
    (hσV : 0 < ground.countOf σV
      (places.perms (posIf G (true, false)).length))
    (hτV : 0 < ground.countOf τV
      (places.perms (posIf G (true, false)).length))
    (s : Nat) (hs : s < (posIf G (true, false)).length) :
    ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (true, false)) s)
      = 2 * ground.getAt 0 (posIf G (true, true))
          (ground.getAt 0 σV s) + 1
    ∧ ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (true, true))
          (ground.getAt 0 σV s) + 1)
      = 2 * ground.getAt 0 (posIf G (true, false)) s := by
  have hbV := sigLt G (true, false) (true, true) hσV hgV
  have hbW := sigLt G (true, false) (true, true) hτV hgV
  have hcall := matchIn_read (wire2 G σU τU)
    (posIf G (true, false)) (posIf G (true, true)) σV 0 1
    (fun t ht => by
      rw [wire2_length]
      exact slotLt G (true, false) t 0 (by decide +kernel) ht)
    (fun t ht => by
      rw [wire2_length]
      exact slotLt G (true, true) _ 1 (by decide +kernel) (hbV t ht))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (posIf_inj G (true, false))
    (qsInj G (true, false) (true, true) hσV hgV) s hs
  refine ⟨?_, ?_⟩
  · show ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (true, false)) s + 0) = _
    rw [wireOf_unfold,
      matchIn_off_slot G (wire3 G σU τU σV) (true, false)
        (true, false) (true, true) τV hbW 1 0 0
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inr (by decide +kernel)) (Or.inl (by decide +kernel)) s hs,
      wire3_unfold]
    exact hcall.1
  · rw [wireOf_unfold,
      matchIn_off_slot G (wire3 G σU τU σV) (true, true)
        (true, false) (true, true) τV hbW 1 0 1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (Or.inl (by decide +kernel)) (Or.inr (by decide +kernel)) _ (hbV s hs),
      wire3_unfold]
    exact hcall.2

/-- The fourth call's slots: the daggered `V` place reads the
undaggered place at its `τ`-match, and back. -/
private theorem wireOf_read4 (G : states.FList)
    (σU τU σV τV : List Nat)
    (hgV : (posIf G (true, false)).length
      = (posIf G (true, true)).length)
    (hτV : 0 < ground.countOf τV
      (places.perms (posIf G (true, false)).length))
    (s : Nat) (hs : s < (posIf G (true, false)).length) :
    ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (true, false)) s + 1)
      = 2 * ground.getAt 0 (posIf G (true, true))
          (ground.getAt 0 τV s)
    ∧ ground.getAt 0 (wireOf G σU τU σV τV)
        (2 * ground.getAt 0 (posIf G (true, true))
          (ground.getAt 0 τV s))
      = 2 * ground.getAt 0 (posIf G (true, false)) s + 1 := by
  have hbW := sigLt G (true, false) (true, true) hτV hgV
  exact matchIn_read (wire3 G σU τU σV)
    (posIf G (true, false)) (posIf G (true, true)) τV 1 0
    (fun t ht => by
      rw [wire3_length]
      exact slotLt G (true, false) t 1 (by decide +kernel) ht)
    (fun t ht => by
      rw [wire3_length]
      exact slotLt G (true, true) _ 0 (by decide +kernel) (hbW t ht))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (posIf_inj G (true, false))
    (qsInj G (true, false) (true, true) hτV hgV) s hs

/-- The four letters, exhaustively. -/
private theorem factorCases (f : states.Factor) :
    f = (false, false) ∨ f = (false, true)
      ∨ f = (true, false) ∨ f = (true, true) := by
  obtain ⟨a, b⟩ := f
  cases a <;> cases b <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr rfl))

/-- The doubled relabeling reads the relabeled position's even
slot to the position's own. -/
private theorem dblEven (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
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
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
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

/-- The wiring travels the relabeling: the doubled relabeling
carries the relabeled site's matched slots to the site's own, at
the slot maps conjugating the four matchings. -/
private theorem wireOf_transport (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
    (σU τU σV τV σU' τU' σV' τV' : List Nat)
    (hgU : (posIf G (false, false)).length
      = (posIf G (false, true)).length)
    (hgV : (posIf G (true, false)).length
      = (posIf G (true, true)).length)
    (hσU : 0 < ground.countOf σU
      (places.perms (posIf G (false, false)).length))
    (hτU : 0 < ground.countOf τU
      (places.perms (posIf G (false, false)).length))
    (hσV : 0 < ground.countOf σV
      (places.perms (posIf G (true, false)).length))
    (hτV : 0 < ground.countOf τV
      (places.perms (posIf G (true, false)).length))
    (hσU' : 0 < ground.countOf σU'
      (places.perms (posIf G' (false, false)).length))
    (hτU' : 0 < ground.countOf τU'
      (places.perms (posIf G' (false, false)).length))
    (hσV' : 0 < ground.countOf σV'
      (places.perms (posIf G' (true, false)).length))
    (hτV' : 0 < ground.countOf τV'
      (places.perms (posIf G' (true, false)).length))
    (hcU : ∀ s, s < (posIf G' (false, false)).length →
      ground.getAt 0 (slotOf G G' ρ (false, true))
          (ground.getAt 0 σU' s)
        = ground.getAt 0 σU
          (ground.getAt 0 (slotOf G G' ρ (false, false)) s))
    (hcT : ∀ s, s < (posIf G' (false, false)).length →
      ground.getAt 0 (slotOf G G' ρ (false, true))
          (ground.getAt 0 τU' s)
        = ground.getAt 0 τU
          (ground.getAt 0 (slotOf G G' ρ (false, false)) s))
    (hcV : ∀ s, s < (posIf G' (true, false)).length →
      ground.getAt 0 (slotOf G G' ρ (true, true))
          (ground.getAt 0 σV' s)
        = ground.getAt 0 σV
          (ground.getAt 0 (slotOf G G' ρ (true, false)) s))
    (hcW : ∀ s, s < (posIf G' (true, false)).length →
      ground.getAt 0 (slotOf G G' ρ (true, true))
          (ground.getAt 0 τV' s)
        = ground.getAt 0 τV
          (ground.getAt 0 (slotOf G G' ρ (true, false)) s))
    (x : Nat) (hx : x < 2 * m) :
    ground.getAt 0 (dbl ρ)
        (ground.getAt 0 (wireOf G' σU' τU' σV' τV') x)
      = ground.getAt 0 (wireOf G σU τU σV τV)
        (ground.getAt 0 (dbl ρ) x) := by
  have heFF := posIf_len_eq G G' ρ m hm hm' hr hg (false, false)
  have heFT := posIf_len_eq G G' ρ m hm hm' hr hg (false, true)
  have heTF := posIf_len_eq G G' ρ m hm hm' hr hg (true, false)
  have heTT := posIf_len_eq G G' ρ m hm hm' hr hg (true, true)
  have hg'U : (posIf G' (false, false)).length
      = (posIf G' (false, true)).length := by
    rw [heFF, heFT, hgU]
  have hg'V : (posIf G' (true, false)).length
      = (posIf G' (true, true)).length := by
    rw [heTF, heTT, hgV]
  obtain ⟨j, hj, hjx⟩ := halveLt hx
  have hjm : j < G'.length := by
    rw [hm']
    exact hj
  match factorCases (ground.getAt (false, false) G' j) with
  | Or.inl hf =>
    obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G' (false, false)).length
        ∧ ground.getAt 0 (posIf G' (false, false)) s = j :=
      ⟨places.posOf j _, places.posOf_lt j _ (posIf_mem hjm hf),
       places.getAt_posOf j _ (posIf_mem hjm hf)⟩
    have hsl : ground.getAt 0 (slotOf G G' ρ (false, false)) s
        < (posIf G (false, false)).length :=
      slotOf_lt G G' ρ m hm hm' hr hg (false, false) s hs
    match hjx with
    | Or.inl hev =>
      have hb : ground.getAt 0 σU' s
          < (posIf G' (false, true)).length := by
        rw [← hg'U]
        exact perm_lt _ hσU' s hs
      rw [hev, ← hjs,
        (wireOf_read1 G' σU' τU' σV' τV' hg'U hg'V hσU' hτU' hσV'
          hτV' s hs).1,
        dblOdd G G' ρ m hm hm' hr hg (false, true) _ hb,
        hcU s hs,
        dblEven G G' ρ m hm hm' hr hg (false, false) s hs,
        (wireOf_read1 G σU τU σV τV hgU hgV hσU hτU hσV hτV _ hsl).1]
    | Or.inr hod =>
      have hb : ground.getAt 0 τU' s
          < (posIf G' (false, true)).length := by
        rw [← hg'U]
        exact perm_lt _ hτU' s hs
      rw [hod, ← hjs,
        (wireOf_read2 G' σU' τU' σV' τV' hg'U hg'V hτU' hσV' hτV'
          s hs).1,
        dblEven G G' ρ m hm hm' hr hg (false, true) _ hb,
        hcT s hs,
        dblOdd G G' ρ m hm hm' hr hg (false, false) s hs,
        (wireOf_read2 G σU τU σV τV hgU hgV hτU hσV hτV _ hsl).1]
  | Or.inr (Or.inl hf) =>
    match hjx with
    | Or.inr hod =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G' (false, false)).length
          ∧ ground.getAt 0 (posIf G' (false, true))
              (ground.getAt 0 σU' s) = j := by
        have htl : places.posOf j (posIf G' (false, true))
            < (posIf G' (false, false)).length := by
          rw [hg'U]
          exact places.posOf_lt j _ (posIf_mem hjm hf)
        refine ⟨ground.getAt 0 (places.invPerm
          (posIf G' (false, false)).length σU')
          (places.posOf j (posIf G' (false, true))),
          perm_inv_lt _ hσU' _ htl, ?_⟩
        rw [perm_right _ hσU' _ htl]
        exact places.getAt_posOf j _ (posIf_mem hjm hf)
      have hsl : ground.getAt 0 (slotOf G G' ρ (false, false)) s
          < (posIf G (false, false)).length :=
        slotOf_lt G G' ρ m hm hm' hr hg (false, false) s hs
      have hb : ground.getAt 0 σU' s
          < (posIf G' (false, true)).length := by
        rw [← hg'U]
        exact perm_lt _ hσU' s hs
      rw [hod, ← hjs,
        (wireOf_read1 G' σU' τU' σV' τV' hg'U hg'V hσU' hτU' hσV'
          hτV' s hs).2,
        dblEven G G' ρ m hm hm' hr hg (false, false) s hs,
        dblOdd G G' ρ m hm hm' hr hg (false, true) _ hb,
        hcU s hs,
        (wireOf_read1 G σU τU σV τV hgU hgV hσU hτU hσV hτV _ hsl).2]
    | Or.inl hev =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G' (false, false)).length
          ∧ ground.getAt 0 (posIf G' (false, true))
              (ground.getAt 0 τU' s) = j := by
        have htl : places.posOf j (posIf G' (false, true))
            < (posIf G' (false, false)).length := by
          rw [hg'U]
          exact places.posOf_lt j _ (posIf_mem hjm hf)
        refine ⟨ground.getAt 0 (places.invPerm
          (posIf G' (false, false)).length τU')
          (places.posOf j (posIf G' (false, true))),
          perm_inv_lt _ hτU' _ htl, ?_⟩
        rw [perm_right _ hτU' _ htl]
        exact places.getAt_posOf j _ (posIf_mem hjm hf)
      have hsl : ground.getAt 0 (slotOf G G' ρ (false, false)) s
          < (posIf G (false, false)).length :=
        slotOf_lt G G' ρ m hm hm' hr hg (false, false) s hs
      have hb : ground.getAt 0 τU' s
          < (posIf G' (false, true)).length := by
        rw [← hg'U]
        exact perm_lt _ hτU' s hs
      rw [hev, ← hjs,
        (wireOf_read2 G' σU' τU' σV' τV' hg'U hg'V hτU' hσV' hτV'
          s hs).2,
        dblOdd G G' ρ m hm hm' hr hg (false, false) s hs,
        dblEven G G' ρ m hm hm' hr hg (false, true) _ hb,
        hcT s hs,
        (wireOf_read2 G σU τU σV τV hgU hgV hτU hσV hτV _ hsl).2]
  | Or.inr (Or.inr (Or.inl hf)) =>
    obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G' (true, false)).length
        ∧ ground.getAt 0 (posIf G' (true, false)) s = j :=
      ⟨places.posOf j _, places.posOf_lt j _ (posIf_mem hjm hf),
       places.getAt_posOf j _ (posIf_mem hjm hf)⟩
    have hsl : ground.getAt 0 (slotOf G G' ρ (true, false)) s
        < (posIf G (true, false)).length :=
      slotOf_lt G G' ρ m hm hm' hr hg (true, false) s hs
    match hjx with
    | Or.inl hev =>
      have hb : ground.getAt 0 σV' s
          < (posIf G' (true, true)).length := by
        rw [← hg'V]
        exact perm_lt _ hσV' s hs
      rw [hev, ← hjs,
        (wireOf_read3 G' σU' τU' σV' τV' hg'V hσV' hτV' s hs).1,
        dblOdd G G' ρ m hm hm' hr hg (true, true) _ hb,
        hcV s hs,
        dblEven G G' ρ m hm hm' hr hg (true, false) s hs,
        (wireOf_read3 G σU τU σV τV hgV hσV hτV _ hsl).1]
    | Or.inr hod =>
      have hb : ground.getAt 0 τV' s
          < (posIf G' (true, true)).length := by
        rw [← hg'V]
        exact perm_lt _ hτV' s hs
      rw [hod, ← hjs,
        (wireOf_read4 G' σU' τU' σV' τV' hg'V hτV' s hs).1,
        dblEven G G' ρ m hm hm' hr hg (true, true) _ hb,
        hcW s hs,
        dblOdd G G' ρ m hm hm' hr hg (true, false) s hs,
        (wireOf_read4 G σU τU σV τV hgV hτV _ hsl).1]
  | Or.inr (Or.inr (Or.inr hf)) =>
    match hjx with
    | Or.inr hod =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G' (true, false)).length
          ∧ ground.getAt 0 (posIf G' (true, true))
              (ground.getAt 0 σV' s) = j := by
        have htl : places.posOf j (posIf G' (true, true))
            < (posIf G' (true, false)).length := by
          rw [hg'V]
          exact places.posOf_lt j _ (posIf_mem hjm hf)
        refine ⟨ground.getAt 0 (places.invPerm
          (posIf G' (true, false)).length σV')
          (places.posOf j (posIf G' (true, true))),
          perm_inv_lt _ hσV' _ htl, ?_⟩
        rw [perm_right _ hσV' _ htl]
        exact places.getAt_posOf j _ (posIf_mem hjm hf)
      have hsl : ground.getAt 0 (slotOf G G' ρ (true, false)) s
          < (posIf G (true, false)).length :=
        slotOf_lt G G' ρ m hm hm' hr hg (true, false) s hs
      have hb : ground.getAt 0 σV' s
          < (posIf G' (true, true)).length := by
        rw [← hg'V]
        exact perm_lt _ hσV' s hs
      rw [hod, ← hjs,
        (wireOf_read3 G' σU' τU' σV' τV' hg'V hσV' hτV' s hs).2,
        dblEven G G' ρ m hm hm' hr hg (true, false) s hs,
        dblOdd G G' ρ m hm hm' hr hg (true, true) _ hb,
        hcV s hs,
        (wireOf_read3 G σU τU σV τV hgV hσV hτV _ hsl).2]
    | Or.inl hev =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G' (true, false)).length
          ∧ ground.getAt 0 (posIf G' (true, true))
              (ground.getAt 0 τV' s) = j := by
        have htl : places.posOf j (posIf G' (true, true))
            < (posIf G' (true, false)).length := by
          rw [hg'V]
          exact places.posOf_lt j _ (posIf_mem hjm hf)
        refine ⟨ground.getAt 0 (places.invPerm
          (posIf G' (true, false)).length τV')
          (places.posOf j (posIf G' (true, true))),
          perm_inv_lt _ hτV' _ htl, ?_⟩
        rw [perm_right _ hτV' _ htl]
        exact places.getAt_posOf j _ (posIf_mem hjm hf)
      have hsl : ground.getAt 0 (slotOf G G' ρ (true, false)) s
          < (posIf G (true, false)).length :=
        slotOf_lt G G' ρ m hm hm' hr hg (true, false) s hs
      have hb : ground.getAt 0 τV' s
          < (posIf G' (true, true)).length := by
        rw [← hg'V]
        exact perm_lt _ hτV' s hs
      rw [hev, ← hjs,
        (wireOf_read4 G' σU' τU' σV' τV' hg'V hτV' s hs).2,
        dblOdd G G' ρ m hm hm' hr hg (true, false) s hs,
        dblEven G G' ρ m hm hm' hr hg (true, true) _ hb,
        hcW s hs,
        (wireOf_read4 G σU τU σV τV hgV hτV _ hsl).2]

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

/-- The joined wiring's entries sit below the doubled site. -/
private theorem wireOf_bound (G : states.FList)
    (σU τU σV τV : List Nat)
    (hgU : (posIf G (false, false)).length
      = (posIf G (false, true)).length)
    (hgV : (posIf G (true, false)).length
      = (posIf G (true, true)).length)
    (hσU : 0 < ground.countOf σU
      (places.perms (posIf G (false, false)).length))
    (hτU : 0 < ground.countOf τU
      (places.perms (posIf G (false, false)).length))
    (hσV : 0 < ground.countOf σV
      (places.perms (posIf G (true, false)).length))
    (hτV : 0 < ground.countOf τV
      (places.perms (posIf G (true, false)).length)) :
    ∀ x, x < 2 * G.length →
      ground.getAt 0 (wireOf G σU τU σV τV) x < 2 * G.length := by
  have hbU := sigLt G (false, false) (false, true) hσU hgU
  have hbT := sigLt G (false, false) (false, true) hτU hgU
  have hbV := sigLt G (true, false) (true, true) hσV hgV
  have hbW := sigLt G (true, false) (true, true) hτV hgV
  have h0 : ∀ x, x < (List.replicate (2 * G.length) (0 : Nat)).length →
      ground.getAt 0 (List.replicate (2 * G.length) 0) x
        < 2 * G.length := replicate_bound (2 * G.length)
  have h1 : ∀ x, x < (wire1 G σU).length →
      ground.getAt 0 (wire1 G σU) x < 2 * G.length := by
    intro x hx
    show ground.getAt 0 (matchIn (List.replicate (2 * G.length) 0)
      (posIf G (false, false)) (posIf G (false, true)) σU 0 1) x
      < 2 * G.length
    refine matchIn_bound _ _ _ _ 0 1 _
      (fun s hs => slotLt G (false, false) s 0 (by decide +kernel) hs)
      (fun s hs => slotLt G (false, true) _ 1 (by decide +kernel)
        (hbU s hs)) h0 x ?_
    rw [ground.length_replicate, ← wire1_length G σU]
    exact hx
  have h2 : ∀ x, x < (wire2 G σU τU).length →
      ground.getAt 0 (wire2 G σU τU) x < 2 * G.length := by
    intro x hx
    rw [wire2_unfold]
    refine matchIn_bound _ _ _ _ 1 0 _
      (fun s hs => slotLt G (false, false) s 1 (by decide +kernel) hs)
      (fun s hs => slotLt G (false, true) _ 0 (by decide +kernel)
        (hbT s hs)) h1 x ?_
    rw [wire1_length, ← wire2_length G σU τU]
    exact hx
  have h3 : ∀ x, x < (wire3 G σU τU σV).length →
      ground.getAt 0 (wire3 G σU τU σV) x < 2 * G.length := by
    intro x hx
    rw [wire3_unfold]
    refine matchIn_bound _ _ _ _ 0 1 _
      (fun s hs => slotLt G (true, false) s 0 (by decide +kernel) hs)
      (fun s hs => slotLt G (true, true) _ 1 (by decide +kernel)
        (hbV s hs)) h2 x ?_
    rw [wire2_length, ← wire3_length G σU τU σV]
    exact hx
  intro x hx
  rw [wireOf_unfold]
  refine matchIn_bound _ _ _ _ 1 0 _
    (fun s hs => slotLt G (true, false) s 1 (by decide +kernel) hs)
    (fun s hs => slotLt G (true, true) _ 0 (by decide +kernel)
      (hbW s hs)) h3 x ?_
  rw [wire3_length]
  exact hx

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

/-- The wiring's second matching exchanges its slots in pairs. -/
private theorem wireOf_invol (G : states.FList)
    (σU τU σV τV : List Nat)
    (hgU : (posIf G (false, false)).length
      = (posIf G (false, true)).length)
    (hgV : (posIf G (true, false)).length
      = (posIf G (true, true)).length)
    (hσU : 0 < ground.countOf σU
      (places.perms (posIf G (false, false)).length))
    (hτU : 0 < ground.countOf τU
      (places.perms (posIf G (false, false)).length))
    (hσV : 0 < ground.countOf σV
      (places.perms (posIf G (true, false)).length))
    (hτV : 0 < ground.countOf τV
      (places.perms (posIf G (true, false)).length))
    (x : Nat) (hx : x < 2 * G.length) :
    ground.getAt 0 (wireOf G σU τU σV τV)
      (ground.getAt 0 (wireOf G σU τU σV τV) x) = x := by
  obtain ⟨j, hj, hjx⟩ := halveLt hx
  match factorCases (ground.getAt (false, false) G j) with
  | Or.inl hf =>
    obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G (false, false)).length
        ∧ ground.getAt 0 (posIf G (false, false)) s = j :=
      ⟨places.posOf j _, places.posOf_lt j _ (posIf_mem hj hf),
       places.getAt_posOf j _ (posIf_mem hj hf)⟩
    match hjx with
    | Or.inl hev =>
      rw [hev, ← hjs,
        (wireOf_read1 G σU τU σV τV hgU hgV hσU hτU hσV hτV s hs).1,
        (wireOf_read1 G σU τU σV τV hgU hgV hσU hτU hσV hτV s hs).2]
    | Or.inr hod =>
      rw [hod, ← hjs,
        (wireOf_read2 G σU τU σV τV hgU hgV hτU hσV hτV s hs).1,
        (wireOf_read2 G σU τU σV τV hgU hgV hτU hσV hτV s hs).2]
  | Or.inr (Or.inl hf) =>
    match hjx with
    | Or.inr hod =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G (false, false)).length
          ∧ ground.getAt 0 (posIf G (false, true))
              (ground.getAt 0 σU s) = j := by
        have htl : places.posOf j (posIf G (false, true))
            < (posIf G (false, false)).length := by
          rw [hgU]
          exact places.posOf_lt j _ (posIf_mem hj hf)
        refine ⟨ground.getAt 0 (places.invPerm
          (posIf G (false, false)).length σU)
          (places.posOf j (posIf G (false, true))),
          perm_inv_lt _ hσU _ htl, ?_⟩
        rw [perm_right _ hσU _ htl]
        exact places.getAt_posOf j _ (posIf_mem hj hf)
      rw [hod, ← hjs,
        (wireOf_read1 G σU τU σV τV hgU hgV hσU hτU hσV hτV s hs).2,
        (wireOf_read1 G σU τU σV τV hgU hgV hσU hτU hσV hτV s hs).1]
    | Or.inl hev =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G (false, false)).length
          ∧ ground.getAt 0 (posIf G (false, true))
              (ground.getAt 0 τU s) = j := by
        have htl : places.posOf j (posIf G (false, true))
            < (posIf G (false, false)).length := by
          rw [hgU]
          exact places.posOf_lt j _ (posIf_mem hj hf)
        refine ⟨ground.getAt 0 (places.invPerm
          (posIf G (false, false)).length τU)
          (places.posOf j (posIf G (false, true))),
          perm_inv_lt _ hτU _ htl, ?_⟩
        rw [perm_right _ hτU _ htl]
        exact places.getAt_posOf j _ (posIf_mem hj hf)
      rw [hev, ← hjs,
        (wireOf_read2 G σU τU σV τV hgU hgV hτU hσV hτV s hs).2,
        (wireOf_read2 G σU τU σV τV hgU hgV hτU hσV hτV s hs).1]
  | Or.inr (Or.inr (Or.inl hf)) =>
    obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G (true, false)).length
        ∧ ground.getAt 0 (posIf G (true, false)) s = j :=
      ⟨places.posOf j _, places.posOf_lt j _ (posIf_mem hj hf),
       places.getAt_posOf j _ (posIf_mem hj hf)⟩
    match hjx with
    | Or.inl hev =>
      rw [hev, ← hjs,
        (wireOf_read3 G σU τU σV τV hgV hσV hτV s hs).1,
        (wireOf_read3 G σU τU σV τV hgV hσV hτV s hs).2]
    | Or.inr hod =>
      rw [hod, ← hjs,
        (wireOf_read4 G σU τU σV τV hgV hτV s hs).1,
        (wireOf_read4 G σU τU σV τV hgV hτV s hs).2]
  | Or.inr (Or.inr (Or.inr hf)) =>
    match hjx with
    | Or.inr hod =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G (true, false)).length
          ∧ ground.getAt 0 (posIf G (true, true))
              (ground.getAt 0 σV s) = j := by
        have htl : places.posOf j (posIf G (true, true))
            < (posIf G (true, false)).length := by
          rw [hgV]
          exact places.posOf_lt j _ (posIf_mem hj hf)
        refine ⟨ground.getAt 0 (places.invPerm
          (posIf G (true, false)).length σV)
          (places.posOf j (posIf G (true, true))),
          perm_inv_lt _ hσV _ htl, ?_⟩
        rw [perm_right _ hσV _ htl]
        exact places.getAt_posOf j _ (posIf_mem hj hf)
      rw [hod, ← hjs,
        (wireOf_read3 G σU τU σV τV hgV hσV hτV s hs).2,
        (wireOf_read3 G σU τU σV τV hgV hσV hτV s hs).1]
    | Or.inl hev =>
      obtain ⟨s, hs, hjs⟩ : ∃ s, s < (posIf G (true, false)).length
          ∧ ground.getAt 0 (posIf G (true, true))
              (ground.getAt 0 τV s) = j := by
        have htl : places.posOf j (posIf G (true, true))
            < (posIf G (true, false)).length := by
          rw [hgV]
          exact places.posOf_lt j _ (posIf_mem hj hf)
        refine ⟨ground.getAt 0 (places.invPerm
          (posIf G (true, false)).length τV)
          (places.posOf j (posIf G (true, true))),
          perm_inv_lt _ hτV _ htl, ?_⟩
        rw [perm_right _ hτV _ htl]
        exact places.getAt_posOf j _ (posIf_mem hj hf)
      rw [hev, ← hjs,
        (wireOf_read4 G σU τU σV τV hgV hτV s hs).2,
        (wireOf_read4 G σU τU σV τV hgV hτV s hs).1]

/-- The composite walk's place count is the doubled site's. -/
private theorem compOf_length (G : states.FList)
    (π σU τU σV τV : List Nat) :
    (compOf G π σU τU σV τV).length = 2 * G.length :=
  ground.length_mapRange _ (2 * G.length)

/-- The composite walk reads the matching after the wiring's
matching at each slot. -/
private theorem compOf_read (G : states.FList)
    (π σU τU σV τV : List Nat) (x : Nat) (hx : x < 2 * G.length) :
    ground.getAt 0 (compOf G π σU τU σV τV) x
      = ground.getAt 0 (wireOf G σU τU σV τV)
        (ground.getAt 0 (mOne G.length π) x) := by
  show ground.getAt 0 ((List.range (2 * G.length)).map (fun i =>
    ground.getAt 0 (wireOf G σU τU σV τV)
      (ground.getAt 0 (mOne G.length π) i))) x = _
  rw [ground.getAt_map_range 0 _ (2 * G.length) x, if_pos hx]

/-- The composite matching is a slot permutation. -/
private theorem compOf_member (G : states.FList)
    (π σU τU σV τV : List Nat)
    (hπ : 0 < ground.countOf π (places.perms G.length))
    (hgU : (posIf G (false, false)).length
      = (posIf G (false, true)).length)
    (hgV : (posIf G (true, false)).length
      = (posIf G (true, true)).length)
    (hσU : 0 < ground.countOf σU
      (places.perms (posIf G (false, false)).length))
    (hτU : 0 < ground.countOf τU
      (places.perms (posIf G (false, false)).length))
    (hσV : 0 < ground.countOf σV
      (places.perms (posIf G (true, false)).length))
    (hτV : 0 < ground.countOf τV
      (places.perms (posIf G (true, false)).length)) :
    0 < ground.countOf (compOf G π σU τU σV τV)
      (places.perms (2 * G.length)) := by
  refine places.perm_of_reads _ _ (compOf_length G π σU τU σV τV)
    (fun x hx => ?_) (fun x y hx hy he => ?_)
  · rw [compOf_read G π σU τU σV τV x hx]
    exact wireOf_bound G σU τU σV τV hgU hgV hσU hτU hσV hτV _
      (mOne_bound G.length hπ x hx)
  · rw [compOf_read G π σU τU σV τV x hx,
      compOf_read G π σU τU σV τV y hy] at he
    have hw : ground.getAt 0 (mOne G.length π) x
        = ground.getAt 0 (mOne G.length π) y := by
      rw [← wireOf_invol G σU τU σV τV hgU hgV hσU hτU hσV hτV _
          (mOne_bound G.length hπ x hx), he,
        wireOf_invol G σU τU σV τV hgU hgV hσU hτU hσV hτV _
          (mOne_bound G.length hπ y hy)]
    rw [← mOne_invol G.length hπ x hx, hw,
      mOne_invol G.length hπ y hy]

/-- The composite matching travels the relabeling. -/
private theorem compOf_transport (G G' : states.FList) (ρ : List Nat)
    (m : Nat) (hm : G.length = m) (hm' : G'.length = m)
    (hr : 0 < ground.countOf ρ (places.perms m))
    (hg : ∀ i, i < m →
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
    (π π' σU τU σV τV σU' τU' σV' τV' : List Nat)
    (hπ : 0 < ground.countOf π (places.perms m))
    (hπ' : 0 < ground.countOf π' (places.perms m))
    (hcπ : ∀ s, s < m →
      ground.getAt 0 ρ (ground.getAt 0 π' s)
        = ground.getAt 0 π (ground.getAt 0 ρ s))
    (hgU : (posIf G (false, false)).length
      = (posIf G (false, true)).length)
    (hgV : (posIf G (true, false)).length
      = (posIf G (true, true)).length)
    (hσU : 0 < ground.countOf σU
      (places.perms (posIf G (false, false)).length))
    (hτU : 0 < ground.countOf τU
      (places.perms (posIf G (false, false)).length))
    (hσV : 0 < ground.countOf σV
      (places.perms (posIf G (true, false)).length))
    (hτV : 0 < ground.countOf τV
      (places.perms (posIf G (true, false)).length))
    (hσU' : 0 < ground.countOf σU'
      (places.perms (posIf G' (false, false)).length))
    (hτU' : 0 < ground.countOf τU'
      (places.perms (posIf G' (false, false)).length))
    (hσV' : 0 < ground.countOf σV'
      (places.perms (posIf G' (true, false)).length))
    (hτV' : 0 < ground.countOf τV'
      (places.perms (posIf G' (true, false)).length))
    (hcU : ∀ s, s < (posIf G' (false, false)).length →
      ground.getAt 0 (slotOf G G' ρ (false, true))
          (ground.getAt 0 σU' s)
        = ground.getAt 0 σU
          (ground.getAt 0 (slotOf G G' ρ (false, false)) s))
    (hcT : ∀ s, s < (posIf G' (false, false)).length →
      ground.getAt 0 (slotOf G G' ρ (false, true))
          (ground.getAt 0 τU' s)
        = ground.getAt 0 τU
          (ground.getAt 0 (slotOf G G' ρ (false, false)) s))
    (hcV : ∀ s, s < (posIf G' (true, false)).length →
      ground.getAt 0 (slotOf G G' ρ (true, true))
          (ground.getAt 0 σV' s)
        = ground.getAt 0 σV
          (ground.getAt 0 (slotOf G G' ρ (true, false)) s))
    (hcW : ∀ s, s < (posIf G' (true, false)).length →
      ground.getAt 0 (slotOf G G' ρ (true, true))
          (ground.getAt 0 τV' s)
        = ground.getAt 0 τV
          (ground.getAt 0 (slotOf G G' ρ (true, false)) s))
    (x : Nat) (hx : x < 2 * m) :
    ground.getAt 0 (dbl ρ)
        (ground.getAt 0 (compOf G' π' σU' τU' σV' τV') x)
      = ground.getAt 0 (compOf G π σU τU σV τV)
        (ground.getAt 0 (dbl ρ) x) := by
  have hdm := dbl_member m hr
  have hRx : ground.getAt 0 (dbl ρ) x < 2 * m :=
    perm_lt (2 * m) hdm x hx
  rw [compOf_read G' π' σU' τU' σV' τV' x (by
      rw [hm']
      exact hx),
    compOf_read G π σU τU σV τV _ (by
      rw [hm]
      exact hRx),
    hm, hm',
    wireOf_transport G G' ρ m hm hm' hr hg σU τU σV τV σU' τU' σV'
      τV' hgU hgV hσU hτU hσV hτV hσU' hτU' hσV' hτV' hcU hcT hcV
      hcW _ (mOne_bound m hπ' x hx),
    mOne_transport m π π' ρ hπ hπ' hr hcπ x hx]

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

/-- The `U` numerator entry travels the slot maps: the relabeled
site's adjugate entry reads the site's own at the conjugated
word. -/
private theorem nUOf_transport (G G' : states.FList)
    (a b σ' τ' : List Nat)
    (heq : (posIf G' (false, false)).length
      = (posIf G (false, false)).length)
    (ha : 0 < ground.countOf a
      (places.perms (posIf G (false, false)).length))
    (hb : 0 < ground.countOf b
      (places.perms (posIf G (false, false)).length))
    (hσ' : 0 < ground.countOf σ'
      (places.perms (posIf G (false, false)).length))
    (hτ' : 0 < ground.countOf τ'
      (places.perms (posIf G (false, false)).length)) :
    poly.oneValue (nUOf G' σ' τ')
      (nUOf G (conjBy (posIf G (false, false)).length a b σ')
        (conjBy (posIf G (false, false)).length a b τ')) := by
  show poly.oneValue (ground.getAt [] (ground.getAt []
      (genericlift.padj (gramWg (posIf G' (false, false)).length))
      (places.idxOf (places.expo σ' (places.invPerm
        (posIf G' (false, false)).length τ'))
        (places.perms (posIf G' (false, false)).length)))
      (places.idxOf (List.range (posIf G' (false, false)).length)
        (places.perms (posIf G' (false, false)).length))) _
  rw [heq, expo_conj (posIf G (false, false)).length ha hb hσ' hτ']
  exact wgCol_transport (posIf G (false, false)).length
    (places.expo
      (conjBy (posIf G (false, false)).length a b σ')
      (places.invPerm (posIf G (false, false)).length
        (conjBy (posIf G (false, false)).length a b τ')))
    (places.invPerm (posIf G (false, false)).length b)
    (places.expo_member _ (conjBy_member _ ha hb hσ')
      (places.invPerm_member _ (conjBy_member _ ha hb hτ')))
    (places.invPerm_member _ hb)

/-- The `V` numerator entry travels the slot maps. -/
private theorem nVOf_transport (G G' : states.FList)
    (a b σ' τ' : List Nat)
    (heq : (posIf G' (true, false)).length
      = (posIf G (true, false)).length)
    (ha : 0 < ground.countOf a
      (places.perms (posIf G (true, false)).length))
    (hb : 0 < ground.countOf b
      (places.perms (posIf G (true, false)).length))
    (hσ' : 0 < ground.countOf σ'
      (places.perms (posIf G (true, false)).length))
    (hτ' : 0 < ground.countOf τ'
      (places.perms (posIf G (true, false)).length)) :
    poly.oneValue (nVOf G' σ' τ')
      (nVOf G (conjBy (posIf G (true, false)).length a b σ')
        (conjBy (posIf G (true, false)).length a b τ')) := by
  show poly.oneValue (ground.getAt [] (ground.getAt []
      (genericlift.padj (gramWg (posIf G' (true, false)).length))
      (places.idxOf (places.expo σ' (places.invPerm
        (posIf G' (true, false)).length τ'))
        (places.perms (posIf G' (true, false)).length)))
      (places.idxOf (List.range (posIf G' (true, false)).length)
        (places.perms (posIf G' (true, false)).length))) _
  rw [heq, expo_conj (posIf G (true, false)).length ha hb hσ' hτ']
  exact wgCol_transport (posIf G (true, false)).length
    (places.expo
      (conjBy (posIf G (true, false)).length a b σ')
      (places.invPerm (posIf G (true, false)).length
        (conjBy (posIf G (true, false)).length a b τ')))
    (places.invPerm (posIf G (true, false)).length b)
    (places.expo_member _ (conjBy_member _ ha hb hσ')
      (places.invPerm_member _ (conjBy_member _ ha hb hτ')))
    (places.invPerm_member _ hb)

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

/-- The four-axis fold collected as nested family folds. -/
private theorem fourFold (PU PV : List (List Nat))
    (T : List Nat → List Nat → List Nat → List Nat → poly.Poly) :
    poly.oneValue
      (PU.foldl (fun acc σ => PU.foldl (fun acc τ =>
        PV.foldl (fun acc x => PV.foldl (fun acc y =>
          poly.add acc (T σ τ x y)) acc) acc) acc) ([] : poly.Poly))
      (ground.famFold poly.add [] (fun σ =>
        ground.famFold poly.add [] (fun τ =>
          ground.famFold poly.add [] (fun x =>
            ground.famFold poly.add [] (fun y => T σ τ x y) PV)
            PV) PU) PU) := by
  have h4 : ∀ (σ τ x : List Nat) (acc acc' : poly.Poly),
      poly.oneValue acc acc' →
      poly.oneValue (PV.foldl (fun a y =>
          poly.add a (T σ τ x y)) acc)
        (poly.add acc' (ground.famFold poly.add []
          (fun y => T σ τ x y) PV)) := fun σ τ x acc acc' hov =>
    foldlOv (fun y => T σ τ x y) _
      (fun a y => poly.oneValue_refl (poly.add a (T σ τ x y)))
      PV acc acc' hov
  have h3 : ∀ (σ τ : List Nat) (acc acc' : poly.Poly),
      poly.oneValue acc acc' →
      poly.oneValue (PV.foldl (fun a x => PV.foldl (fun a y =>
          poly.add a (T σ τ x y)) a) acc)
        (poly.add acc' (ground.famFold poly.add [] (fun x =>
          ground.famFold poly.add []
            (fun y => T σ τ x y) PV) PV)) :=
    fun σ τ acc acc' hov =>
      foldlOv _ _ (fun a x => h4 σ τ x a a (poly.oneValue_refl a))
        PV acc acc' hov
  have h2 : ∀ (σ : List Nat) (acc acc' : poly.Poly),
      poly.oneValue acc acc' →
      poly.oneValue (PU.foldl (fun a τ => PV.foldl (fun a x =>
          PV.foldl (fun a y => poly.add a (T σ τ x y)) a) a) acc)
        (poly.add acc' (ground.famFold poly.add [] (fun τ =>
          ground.famFold poly.add [] (fun x =>
            ground.famFold poly.add []
              (fun y => T σ τ x y) PV) PV) PU)) :=
    fun σ acc acc' hov =>
      foldlOv _ _ (fun a τ => h3 σ τ a a (poly.oneValue_refl a))
        PU acc acc' hov
  refine poly.oneValue_trans
    (foldlOv _ _ (fun a σ => h2 σ a a (poly.oneValue_refl a))
      PU [] [] (poly.oneValue_refl []))
    (poly.polyFoldLaws.unitOp _)

/-- The four-axis fold travels a pair of enumeration bijections:
the primed terms read the moved terms at every tuple. -/
private theorem fourBij (PU PV : List (List Nat))
    (T T' : List Nat → List Nat → List Nat → List Nat → poly.Poly)
    (gU hU gV hV : List Nat → List Nat)
    (hdU : ground.distinctList PU) (hdV : ground.distinctList PV)
    (hghU : ∀ x, 0 < ground.countOf x PU → hU (gU x) = x)
    (hhgU : ∀ x, 0 < ground.countOf x PU → gU (hU x) = x)
    (hgmU : ∀ x, 0 < ground.countOf x PU →
      0 < ground.countOf (gU x) PU)
    (hhmU : ∀ x, 0 < ground.countOf x PU →
      0 < ground.countOf (hU x) PU)
    (hghV : ∀ x, 0 < ground.countOf x PV → hV (gV x) = x)
    (hhgV : ∀ x, 0 < ground.countOf x PV → gV (hV x) = x)
    (hgmV : ∀ x, 0 < ground.countOf x PV →
      0 < ground.countOf (gV x) PV)
    (hhmV : ∀ x, 0 < ground.countOf x PV →
      0 < ground.countOf (hV x) PV)
    (hT : ∀ σ τ x y, 0 < ground.countOf σ PU →
      0 < ground.countOf τ PU → 0 < ground.countOf x PV →
      0 < ground.countOf y PV →
      poly.oneValue (T' σ τ x y) (T (gU σ) (gU τ) (gV x) (gV y))) :
    poly.oneValue
      (PU.foldl (fun acc σ => PU.foldl (fun acc τ =>
        PV.foldl (fun acc x => PV.foldl (fun acc y =>
          poly.add acc (T' σ τ x y)) acc) acc) acc) ([] : poly.Poly))
      (PU.foldl (fun acc σ => PU.foldl (fun acc τ =>
        PV.foldl (fun acc x => PV.foldl (fun acc y =>
          poly.add acc (T σ τ x y)) acc) acc) acc)
        ([] : poly.Poly)) := by
  have hb4 : ∀ σ τ x, 0 < ground.countOf σ PU →
      0 < ground.countOf τ PU → 0 < ground.countOf x PV →
      poly.oneValue
        (ground.famFold poly.add [] (fun y => T' σ τ x y) PV)
        (ground.famFold poly.add []
          (fun y => T (gU σ) (gU τ) (gV x) y) PV) :=
    fun σ τ x hσ hτ hx =>
      ground.famFold_bij_ov poly.polyFoldLaws.toCommLaws []
        (fun y => T' σ τ x y)
        (fun y => T (gU σ) (gU τ) (gV x) y) hdV hghV hhgV hgmV
        hhmV (fun y hy => hT σ τ x y hσ hτ hx hy)
  have hb3 : ∀ σ τ, 0 < ground.countOf σ PU →
      0 < ground.countOf τ PU →
      poly.oneValue
        (ground.famFold poly.add [] (fun x =>
          ground.famFold poly.add [] (fun y => T' σ τ x y) PV) PV)
        (ground.famFold poly.add [] (fun x =>
          ground.famFold poly.add []
            (fun y => T (gU σ) (gU τ) x y) PV) PV) :=
    fun σ τ hσ hτ =>
      ground.famFold_bij_ov poly.polyFoldLaws.toCommLaws []
        (fun x => ground.famFold poly.add []
          (fun y => T' σ τ x y) PV)
        (fun x => ground.famFold poly.add []
          (fun y => T (gU σ) (gU τ) x y) PV) hdV hghV hhgV hgmV
        hhmV (fun x hx => hb4 σ τ x hσ hτ hx)
  have hb2 : ∀ σ, 0 < ground.countOf σ PU →
      poly.oneValue
        (ground.famFold poly.add [] (fun τ =>
          ground.famFold poly.add [] (fun x =>
            ground.famFold poly.add []
              (fun y => T' σ τ x y) PV) PV) PU)
        (ground.famFold poly.add [] (fun τ =>
          ground.famFold poly.add [] (fun x =>
            ground.famFold poly.add []
              (fun y => T (gU σ) τ x y) PV) PV) PU) :=
    fun σ hσ =>
      ground.famFold_bij_ov poly.polyFoldLaws.toCommLaws []
        (fun τ => ground.famFold poly.add [] (fun x =>
          ground.famFold poly.add [] (fun y => T' σ τ x y) PV) PV)
        (fun τ => ground.famFold poly.add [] (fun x =>
          ground.famFold poly.add []
            (fun y => T (gU σ) τ x y) PV) PV) hdU hghU hhgU hgmU
        hhmU (fun τ hτ => hb3 σ τ hσ hτ)
  have hb1 : poly.oneValue
      (ground.famFold poly.add [] (fun σ =>
        ground.famFold poly.add [] (fun τ =>
          ground.famFold poly.add [] (fun x =>
            ground.famFold poly.add []
              (fun y => T' σ τ x y) PV) PV) PU) PU)
      (ground.famFold poly.add [] (fun σ =>
        ground.famFold poly.add [] (fun τ =>
          ground.famFold poly.add [] (fun x =>
            ground.famFold poly.add []
              (fun y => T σ τ x y) PV) PV) PU) PU) :=
    ground.famFold_bij_ov poly.polyFoldLaws.toCommLaws []
      (fun σ => ground.famFold poly.add [] (fun τ =>
        ground.famFold poly.add [] (fun x =>
          ground.famFold poly.add [] (fun y => T' σ τ x y) PV) PV)
        PU)
      (fun σ => ground.famFold poly.add [] (fun τ =>
        ground.famFold poly.add [] (fun x =>
          ground.famFold poly.add [] (fun y => T σ τ x y) PV) PV)
        PU) hdU hghU hhgU hgmU hhmU hb2
  exact poly.oneValue_trans (fourFold PU PV T')
    (poly.oneValue_trans hb1
      (poly.oneValue_symm (fourFold PU PV T)))

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
      ground.getAt (false, false) G' i
        = ground.getAt (false, false) G (ground.getAt 0 ρ i))
    (hcπ : ∀ s, s < m →
      ground.getAt 0 ρ (ground.getAt 0 π' s)
        = ground.getAt 0 π (ground.getAt 0 ρ s)) :
    genericlift.crossNull (evalPhi G' π') (evalPhi G π) := by
  have heFF := posIf_len_eq G G' ρ m hm hm' hr hg (false, false)
  have heFT := posIf_len_eq G G' ρ m hm hm' hr hg (false, true)
  have heTF := posIf_len_eq G G' ρ m hm hm' hr hg (true, false)
  have heTT := posIf_len_eq G G' ρ m hm hm' hr hg (true, true)
  have hguard : guardOf G' = guardOf G := by
    show (((posIf G' (false, false)).length
        == (posIf G' (false, true)).length)
      && ((posIf G' (true, false)).length
        == (posIf G' (true, true)).length)) = _
    rw [heFF, heFT, heTF, heTT]
    rfl
  rw [evalPhi_bridge G' π', evalPhi_bridge G π, hguard]
  by_cases hgd : guardOf G = true
  · rw [if_pos hgd, if_pos hgd]
    have hsplit : ∀ a b : Bool, (a && b) = true →
        a = true ∧ b = true := by
      intro a b h
      cases a <;> cases b <;>
        first
          | exact ⟨rfl, rfl⟩
          | exact Bool.noConfusion h
    have hgd' : (((posIf G (false, false)).length
          == (posIf G (false, true)).length)
        && ((posIf G (true, false)).length
          == (posIf G (true, true)).length)) = true := hgd
    obtain ⟨hA, hB⟩ := hsplit _ _ hgd'
    have hgU : (posIf G (false, false)).length
        = (posIf G (false, true)).length := ground.beqEqOf hA
    have hgV : (posIf G (true, false)).length
        = (posIf G (true, true)).length := ground.beqEqOf hB
    have hg'U : (posIf G' (false, false)).length
        = (posIf G' (false, true)).length := by
      rw [heFF, heFT, hgU]
    have hg'V : (posIf G' (true, false)).length
        = (posIf G' (true, true)).length := by
      rw [heTF, heTT, hgV]
    have haU := slotOf_member G G' ρ m hm hm' hr hg (false, false)
    have haV := slotOf_member G G' ρ m hm hm' hr hg (true, false)
    have hbU : 0 < ground.countOf (slotOf G G' ρ (false, true))
        (places.perms (posIf G (false, false)).length) := by
      rw [hgU]
      exact slotOf_member G G' ρ m hm hm' hr hg (false, true)
    have hbV : 0 < ground.countOf (slotOf G G' ρ (true, true))
        (places.perms (posIf G (true, false)).length) := by
      rw [hgV]
      exact slotOf_member G G' ρ m hm hm' hr hg (true, true)
    have hdm := dbl_member m hr
    have hcyc : ∀ sU tU sV tV : List Nat,
        0 < ground.countOf sU
          (places.perms (posIf G (false, false)).length) →
        0 < ground.countOf tU
          (places.perms (posIf G (false, false)).length) →
        0 < ground.countOf sV
          (places.perms (posIf G (true, false)).length) →
        0 < ground.countOf tV
          (places.perms (posIf G (true, false)).length) →
        (places.cyclesOf (compOf G' π' sU tU sV tV)).length
          = (places.cyclesOf (compOf G π
              (conjBy (posIf G (false, false)).length
                (slotOf G G' ρ (false, false))
                (slotOf G G' ρ (false, true)) sU)
              (conjBy (posIf G (false, false)).length
                (slotOf G G' ρ (false, false))
                (slotOf G G' ρ (false, true)) tU)
              (conjBy (posIf G (true, false)).length
                (slotOf G G' ρ (true, false))
                (slotOf G G' ρ (true, true)) sV)
              (conjBy (posIf G (true, false)).length
                (slotOf G G' ρ (true, false))
                (slotOf G G' ρ (true, true)) tV))).length := by
      intro sU tU sV tV h1 h2 h3 h4
      have h1' : 0 < ground.countOf sU
          (places.perms (posIf G' (false, false)).length) := by
        rw [heFF]
        exact h1
      have h2' : 0 < ground.countOf tU
          (places.perms (posIf G' (false, false)).length) := by
        rw [heFF]
        exact h2
      have h3' : 0 < ground.countOf sV
          (places.perms (posIf G' (true, false)).length) := by
        rw [heTF]
        exact h3
      have h4' : 0 < ground.countOf tV
          (places.perms (posIf G' (true, false)).length) := by
        rw [heTF]
        exact h4
      have hcm' : 0 < ground.countOf (compOf G' π' sU tU sV tV)
          (places.perms (2 * m)) := by
        rw [← hm']
        exact compOf_member G' π' sU tU sV tV (by
            rw [hm']
            exact hπ') hg'U hg'V h1' h2' h3' h4'
      have hcm : 0 < ground.countOf (compOf G π
          (conjBy (posIf G (false, false)).length
            (slotOf G G' ρ (false, false))
            (slotOf G G' ρ (false, true)) sU)
          (conjBy (posIf G (false, false)).length
            (slotOf G G' ρ (false, false))
            (slotOf G G' ρ (false, true)) tU)
          (conjBy (posIf G (true, false)).length
            (slotOf G G' ρ (true, false))
            (slotOf G G' ρ (true, true)) sV)
          (conjBy (posIf G (true, false)).length
            (slotOf G G' ρ (true, false))
            (slotOf G G' ρ (true, true)) tV))
          (places.perms (2 * m)) := by
        rw [← hm]
        exact compOf_member G π _ _ _ _ (by
            rw [hm]
            exact hπ) hgU hgV
          (conjBy_member _ haU hbU h1) (conjBy_member _ haU hbU h2)
          (conjBy_member _ haV hbV h3) (conjBy_member _ haV hbV h4)
      have htr := compOf_transport G G' ρ m hm hm' hr hg π π'
        _ _ _ _ sU tU sV tV hπ hπ' hcπ hgU hgV
        (conjBy_member _ haU hbU h1) (conjBy_member _ haU hbU h2)
        (conjBy_member _ haV hbV h3) (conjBy_member _ haV hbV h4)
        h1' h2' h3' h4'
        (fun s hs => conjBy_rel _ haU h1 s (by
          rw [← heFF]
          exact hs))
        (fun s hs => conjBy_rel _ haU h2 s (by
          rw [← heFF]
          exact hs))
        (fun s hs => conjBy_rel _ haV h3 s (by
          rw [← heTF]
          exact hs))
        (fun s hs => conjBy_rel _ haV h4 s (by
          rw [← heTF]
          exact hs))
      have hkey : compOf G' π' sU tU sV tV
          = (places.invPerm (2 * m)
              (places.invPerm (2 * m) (dbl ρ))).map (fun j =>
            ground.getAt 0 (places.invPerm (2 * m) (dbl ρ))
              (ground.getAt 0 (compOf G π
                (conjBy (posIf G (false, false)).length
                  (slotOf G G' ρ (false, false))
                  (slotOf G G' ρ (false, true)) sU)
                (conjBy (posIf G (false, false)).length
                  (slotOf G G' ρ (false, false))
                  (slotOf G G' ρ (false, true)) tU)
                (conjBy (posIf G (true, false)).length
                  (slotOf G G' ρ (true, false))
                  (slotOf G G' ρ (true, true)) sV)
                (conjBy (posIf G (true, false)).length
                  (slotOf G G' ρ (true, false))
                  (slotOf G G' ρ (true, true)) tV)) j)) := by
        refine ground.getAt_ext 0 _ _ (by
            rw [compOf_length, hm', ground.length_map,
              places.length_invPerm]) ?_
        intro i hi
        rw [compOf_length, hm'] at hi
        rw [ground.getAt_map 0 0 _ (places.invPerm (2 * m)
            (places.invPerm (2 * m) (dbl ρ))) i (by
              rw [places.length_invPerm]
              exact hi),
          places.invPerm_invPerm (2 * m) hdm, ← htr i hi,
          perm_left (2 * m) hdm _ (perm_lt (2 * m) hcm' i hi)]
      rw [hkey]
      exact places.cyclesOf_transport (2 * m) hcm
        (places.invPerm_member (2 * m) hdm)
    rw [numOf_unfold G' π', numOf_unfold G π, heFF, heTF]
    refine (genericlift.crossNull_ov _ _).mpr ?_
    refine poly.mul_congr_left ?_ _
    refine fourBij (places.perms (posIf G (false, false)).length)
      (places.perms (posIf G (true, false)).length)
      (termOf G π) (termOf G' π')
      (conjBy (posIf G (false, false)).length
        (slotOf G G' ρ (false, false))
        (slotOf G G' ρ (false, true)))
      (conjBy (posIf G (false, false)).length
        (places.invPerm (posIf G (false, false)).length
          (slotOf G G' ρ (false, false)))
        (places.invPerm (posIf G (false, false)).length
          (slotOf G G' ρ (false, true))))
      (conjBy (posIf G (true, false)).length
        (slotOf G G' ρ (true, false))
        (slotOf G G' ρ (true, true)))
      (conjBy (posIf G (true, false)).length
        (places.invPerm (posIf G (true, false)).length
          (slotOf G G' ρ (true, false)))
        (places.invPerm (posIf G (true, false)).length
          (slotOf G G' ρ (true, true))))
      (places.perms_distinct _) (places.perms_distinct _)
      (fun x hx => conjBy_inv _ haU hbU hx)
      (fun x hx => by
        have h := conjBy_inv (posIf G (false, false)).length
          (places.invPerm_member _ haU)
          (places.invPerm_member _ hbU) hx
        rw [places.invPerm_invPerm _ haU,
          places.invPerm_invPerm _ hbU] at h
        exact h)
      (fun x hx => conjBy_member _ haU hbU hx)
      (fun x hx => conjBy_member _ (places.invPerm_member _ haU)
        (places.invPerm_member _ hbU) hx)
      (fun x hx => conjBy_inv _ haV hbV hx)
      (fun x hx => by
        have h := conjBy_inv (posIf G (true, false)).length
          (places.invPerm_member _ haV)
          (places.invPerm_member _ hbV) hx
        rw [places.invPerm_invPerm _ haV,
          places.invPerm_invPerm _ hbV] at h
        exact h)
      (fun x hx => conjBy_member _ haV hbV hx)
      (fun x hx => conjBy_member _ (places.invPerm_member _ haV)
        (places.invPerm_member _ hbV) hx)
      (fun s t x y hs ht hx hy => ?_)
    show poly.oneValue (poly.mul (nUOf G' s t)
      (poly.mul (nVOf G' x y) (dfPow ((places.cyclesOf
        (compOf G' π' s t x y)).length / 2)))) _
    rw [hcyc s t x y hs ht hx hy]
    exact poly.oneValue_trans
      (poly.mul_congr_left (nUOf_transport G G'
        (slotOf G G' ρ (false, false)) (slotOf G G' ρ (false, true))
        s t heFF haU hbU hs ht) _)
      (poly.mul_congr _ (poly.mul_congr_left
        (nVOf_transport G G' (slotOf G G' ρ (true, false))
          (slotOf G G' ρ (true, true)) x y heTF haV hbV hx hy) _))
  · rw [if_neg hgd, if_neg hgd]
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
          ground.getAt (false, false) G j))
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
    (ρ.map (fun j => ground.getAt (false, false) G j)) π
    (ρ.map (fun j => ground.getAt 0 (places.invPerm G.length ρ)
      (ground.getAt 0 π j))) ρ G.length rfl ?_ hρ hπ ?_ ?_ ?_
  · show (ρ.map (fun j => ground.getAt (false, false) G j)).length
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
    show ground.getAt (false, false) (ρ.map (fun j =>
      ground.getAt (false, false) G j)) i = _
    exact ground.getAt_map 0 (false, false) _ ρ i (by
      rw [hrlen]
      exact hi)
  · intro s hs
    rw [hread s hs, perm_right G.length hρ _ (hplt s hs)]

end wg
