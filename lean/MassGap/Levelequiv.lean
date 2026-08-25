import MassGap.K
import MassGap.Momentform
/-!
`thm:levelequiv` — the level condition over probes is the spectral
condition: the operator read `Ẽ² ⪰ γ Ẽ` on the word sector at its
split certificate (`opRead`, `def:K`'s cut shape at the level
alone with the two compressed forms as data), and the requirement
at one probe (`reqReadAt`, the two moments' cleared comparison).
The equivalence's two directions are the characterization
theorems: at the spectrum's side the split's positivity holds at
every probe of the window (`probe_intro`, `lem:inertia`'s
transport read at the site datum's decomposition), and at a
failing count the elimination's witness is a sector vector whose
probe fails the requirement outright (`probe_elim`,
`thm:certconstruct`(2)) — the witness against the requirement's
negation the check module's paired pins.  The two directions at
the moment spelling are `cor:momentdivisor`'s window statement,
the recorded consumer.
-/

namespace levelequiv
open ground elim inertia

/-- The operator read at the split certificate: the pair
`(gd Ẽ² : gn Ẽ)` positive semidefinite, the level's spectral
half. -/
def opRead {o : Nat} (Esq Et : Mat) (gn gd : Pos) (sp : Split o) : Prop :=
  sqAt Esq o ∧ sqAt Et o
  ∧ splitRead
      (siteDatum (matScale gd Esq) (matScale gn Et)) sp
  ∧ psdAt sp

instance {o : Nat} (Esq Et : Mat) (gn gd : Pos) (sp : Split o) :
    Decidable (opRead Esq Et gn gd sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The requirement's read at a probe over the two compressed
forms at the carrier: the square's compression beside the gap's,
the moments the forms' own quadratic folds, the orders one by the
types. -/
def reqReadAt {n : Nat} (Esq Et : SqMat n) (y : Vec n)
    (gn gd : Pos) : Prop :=
  ¬ (inertia.quadForm Esq.val y.val).scale gd
      < (inertia.quadForm Et.val y.val).scale gn

instance {n : Nat} (Esq Et : SqMat n) (y : Vec n) (gn gd : Pos) :
    Decidable (reqReadAt Esq Et y gn gd) :=
  inferInstanceAs (Decidable (¬ _ < _))

/-- The spectrum's side: at the operator read's split the
requirement holds at every probe of the window, the split's
positivity transported to each sector vector through the
congruence and read at the site datum's decomposition. -/
theorem probe_intro {n : Nat} (Esq Et : SqMat n) (gn gd : Pos)
    (sp : Split n) (h : opRead Esq.val Et.val gn gd sp) :
    ∀ y : Vec n, reqReadAt Esq Et y gn gd := by
  intro y
  obtain ⟨hEsq, hEt, hsplit, hp⟩ := h
  have hy : y.val.length = n := Nat.eq_of_beq_eq_true y.len
  have hXr : rowsLen y.val.length Esq.val := by
    rw [hy]; exact rowsLen_of_sqAt hEsq
  have hYr : rowsLen y.val.length Et.val := by
    rw [hy]; exact rowsLen_of_sqAt hEt
  exact inertia.scaledSite_side (Esq.rows.trans hy.symm) hXr
    (Et.rows.trans hy.symm) hYr (psd_all _ sp hsplit hp y.val hy)

/-- The failing count's witness: at an occupied reversal count the
elimination exhibits a sector vector whose probe fails the
requirement outright, `thm:certconstruct`(2)'s read at the
window. -/
theorem probe_elim {n : Nat} (Esq Et : SqMat n) (gn gd : Pos)
    (sp : Split n)
    (h : splitRead (siteDatum (matScale gd Esq.val)
        (matScale gn Et.val)) sp)
    (hocc : 1 ≤ revAt sp) :
    ∃ y : Vec n, ¬ reqReadAt Esq Et y gn gd := by
  obtain ⟨u, hu, hlt⟩ := rev_witness _ sp h hocc
  have hXr : rowsLen u.length Esq.val := by
    rw [hu]; exact rowsLen_of_sqAt Esq.shape
  have hYr : rowsLen u.length Et.val := by
    rw [hu]; exact rowsLen_of_sqAt Et.shape
  refine ⟨⟨u, by rw [hu]; exact beqRefl n⟩, fun hreq => hreq ?_⟩
  exact inertia.scaledSite_gap (Esq.rows.trans hu.symm) hXr
    (Et.rows.trans hu.symm) hYr hlt

end levelequiv
