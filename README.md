# The mass gap over the compact simple groups

[![lean](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml/badge.svg)](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22018060.svg)](https://doi.org/10.5281/zenodo.22018060)

This repository presents a complete manuscript, [docs/theory.tex](docs/theory.tex) ([PDF](docs/theory.pdf)), and its in-progress Lean 4 formalization, [lean/](lean/).  The manuscript states and derives a mass gap for lattice gauge theory over every compact
simple group (`thm:main`), with
`rem:dictionary` presenting the results in the conventional
formulation which includes the Jaffe-Witten statement of the Yang-Mills problem.  The proof is constructive over the positive naturals with the sum and the
product; this choice was made explicitly to enable the Lean to be written constructively and eventually emit certified brackets of physical quantities directly comparable to Montecarlo and experimental results.

The tex is the authority and the Lean is its transcription: every top-level
Lean declaration sits in a namespace matching a label in
`theory.tex` (e.g. `gappos.sandwich_lo` transcribes `thm:gappos`, `inertia.rev_add`
transcribes `lem:inertia`).  The docstring at the head of each module under
[lean/MassGap/](lean/MassGap/) states exactly which clauses of its label the
module holds.

## Status

`theory.tex` is a complete proof and any future changes will ideally only improve clarity and add detail.  The Lean tree is
a mostly complete transcription of that proof: this section says exactly which parts are and are
not formalized.

`thm:main` has three clauses. These are stated over the domain `main.Member`
([lean/MassGap/Main.lean](lean/MassGap/Main.lean)): the `A`-series at every residue,
`B_l`, `C_l`, `D_l` at their index floors, and `G2`, `F4`, `E6`,
`E7`, `E8` once each.

Formalized:

- **Clause (i), gap positivity, is closed for every member**:
  `main.clauseI_all` proves both committed chain reads and the required tie throughout the classification. The series cases are parametric in rank at the diagonal windows; D4’s four-loop window and E8’s coupled window are handled separately.
- **Clause (ii), the contact value `(3, H_r)`, is closed at every
  member**: `main.clauseII_all` holds it at the whole
  classification: the order count, the base collection, the
  excess-harmonic value and the occupancy families as theorems
  over every residue and rank, the fixed members by kernel
  `decide` in
  [lean/MassGapChecks/Main.lean](lean/MassGapChecks/Main.lean).
- **The requirement mirrors** `lem:sectorspan` and `lem:attained`.
- **Most of clause (iii)'s support tiers**: `lem:cornerpivot` (the
  corner disconjugacy certificate: the walk, profile, crossing,
  dominance, ground-witness, count and block-chain tiers, the
  graded box devices, and the emitted disconjugacy store with its
  certificate kernel-decided whole), `lem:spectator`'s derivation
  tier,
  `thm:groundreads` whole (clauses (i)-(vii) with (v')),
  `lem:momentfold` whole (the moment streams, the graded system,
  the truncation cap, the scale comparison and the datum
  assembly), `lem:fourpoint` whole, `lem:corner`'s corner-count,
  shifted-scaling, drift, grade-key, cap and count tiers, and
  `thm:restoration`'s first tier.

Open (no Lean yet):

- `lem:cornerpivot`'s remainder (the second root's compression and
  the block-chain lift's remaining clauses) and
  `lem:corner`'s cell-floor clause with the corner-output clauses
  of `thm:decomp` and `thm:twoaction`.
- `lem:cone`, `thm:continuum`, `thm:reconstruct`.
- **Clause (iii)'s composite statement at `main`** (it consumes the
  items above), and the reverse correspondence walk (every tex
  label reached from a Lean namespace).

The snapshot is taken from the development repository at commit
`7e91dceb532f13d0df40deaca9a1a38203df29c5` (2026-08-30).

## FAQ

These questions are real and were raised, in roughly this order and roughly this tone, by two separate skeptical reviewers (one a human physicist, the other an AI model) who read [docs/theory.tex](docs/theory.tex). The presentation of the questions is an aggregate of the two, although it is worth noting the physicist's questions formed a strict subset of the AI's. Ultimately neither of them located an internal error (this is not to be taken as a statement of correctness).

### "This pattern-matches to crankery: solo author, invented vocabulary, Millennium-problem claim. Why should anyone read a more than 100 page PDF of dense, idiosyncratic mathematics?"

Even with the terrible priors aside, I'd argue that no one should read the paper at least initially. And if the only deliverable was the paper, I would have never begun this project. Instead, the construction is built so that every claim in the development will be machine-checked by Lean with zero axioms. The intended order becomes: verify the top level theorems in Lean correspond to real world meaning, then check that the Lean compiles axiom-free.

A related question, which no one has asked directly, is "why work on something where the social consequences will be so severe?" I have a promising career in academia, why tarnish it with a black eye (or worse)? The answer is that I am a firm believer that anyone should be able to make an honest, serious attempt at a hard problem and be treated equally seriously and with respect (I do not think this entitles that person or their work to anyone else's time, energy, or attention). This is a problem that fascinates me, and with the rise of theorem provers like Lean I have an unprecedented opportunity to see my ideas through in a formal way. Nonetheless, this has not been without repercussions. I am deeply disturbed by the level of dehumanization directed toward me both inside and outside of academia when people realize I am working on this problem. It has involved expletives, name calling, and even threats. I request that anyone looking to engage with my work do exactly that: engage with the work.

### "Why does the paper use highly idiosyncratic language at all, such as 'reads,' 'balance pairs,' 'located,' 'priced', instead of standard terminology?"

First, maybe it shouldn't. But it did not end up this way accidentally: a lot of time was spent trying to conform to standard terminology where possible, and each deviation was chosen for a reason and, where one exists, a literature precedent. The paper carries its own translation table (`rem:dictionary`, "The names"). The most salient cases:

- **Balance pairs `⟨u:v⟩` and scalar pairs `[a:b]`.** The entire development is constructive over the positive naturals: there is no subtraction and no division as primitive operations. `⟨u:v⟩` is the difference u−v and `[a:b]` the quotient a/b, *as data with their defining identities* rather than as operations assumed to exist. This is what lets every statement be a statement about naturals, and what made an axiom-free Lean formalization possible.
- **"Located."** Bishop's constructive analysis, by name (`rem:dictionary`). A located root or datum comes with an isolating bracket and a modulus. It is a real number you can compute against, not a real number you have merely proven to exist.
- **"Reversal count."** The negative index of inertia; the two-splits-one-count clause is Sylvester's law of inertia (`lem:inertia`, named in the dictionary). Eigenvalue counting throughout is exact integer LDLᵀ arithmetic, never floating-point.
- **"Deck relation / deck families."** The double cover w = z + 1/z (Joukowski map); the chord t = 2cos k is the Chebyshev variable of the momentum fiber (`rem:dictionary`). Momentum on the lattice is handled by commuting chord operators, exactly.
- **"Labels," "blocks," "contents."** Irreducible representations, their carriers, and weights. The rebuild from scratch (through the Weyl character formula, fusion rules, and Weingarten calculus) exists so that the fusion interface (`con:fusion`) is *derived data*, which is a requirement for the formalization.
- **"Residue" r.** The dual Coxeter number less one, r + 1 = h∨ (`rem:dictionary`, "The members"), the one scalar the whole classification is organized around.

The deviations are systematic, not decorative: they mark exactly the places where the standard term presumes classical operations (subtraction, division, limits, choice) that the construction refuses to presume.

### "There is no bibliography. Zero citations."

This is deliberate and **temporary**. It stems from my workflow: I use AI to proofread changes I make to the proofs in the paper, but for it to cross check my work with other places in the tex it must load the entire paper into context every time. The tex is sufficiently large that it consumes around 500,000 tokens to load in completely. This is both monetarily expensive and gives me little working context to engage with the model's feedback, which is focused primarily on identifying places where I have glossed or taken shortcuts. Once the Lean transcription has finished (thereby verifying the paper's correctness), I will add in an abstract, introduction, citations, etc.

### "Renormalization, asymptotic freedom, beta function, continuum limit: zero occurrences. A Yang–Mills proof cannot fail to contain these."

It can if nothing is expanded. Those words name tools for controlling a perturbative expansion or a limit of measures. This construction is Hamiltonian and exact at every coupling, so there is no series whose divergences need renormalizing. What replaces the running coupling is the **unit map** (`rem:dictionary`): at a physical gap Δ the spacing is a = h/(√2Δ) at the certified corner height h, one equation per scale, the whole trajectory a located function. Calibration is an output, not a scheme choice, and the scheme dependence that does exist is quarantined in the corner outputs (`thm:decomp`). The paper also engages the standard weak-coupling picture directly rather than ignoring it: `rem:dictionary`'s weak-coupling item states the classical comparison (lattice Maxwell per Lie-algebra direction, massless dispersion at k → 0) and identifies the gap as the certified lift *above* that comparison. If your question is "but doesn't the result then conflict with asymptotic-freedom scaling?" then that is the right question, and it has its own entry below.

### "Wouldn't this argument also 'prove' a mass gap for U(1)? If yes, it proves too much."

No, it does not prove a mass gap for U(1). The mechanism dies abelianly, at two named places. First, the channel's base is c₁, the multiplicity of the adjoint in adj⊗adj (`con:xfusion`): positive for every compact simple group, zero for U(1), and with c₁ = 0 the boundary resolvent G₀ = z + c₁zG₀ degenerates to G₀ = z, meaning no mass point, no bound state, and no gap coordinate. Second, the charged tower reads C₂(mθ) = m(m+r) against the abelian tower's m²; the paper names the difference explicitly: "The linear coefficient r is fusion strictness: the abelian tower reads C₂ = m² and this one m(m+r)" (`prop:anchor`). Non-abelian structure is structurally necessary at every stage of the gap mechanism, exactly as the physics demands.

### "The theorem, translated through its own dictionary, says aΔ is bounded below toward weak coupling. Forty years of Monte Carlo scaling studies say aΔ ~ e^(−c/g²). Isn't the paper simply contradicted by the data?"

When stated precisely, this is not a contradiction. Asymptotic-freedom scaling of aΔ comes from perturbative renormalization-group analysis plus numerical simulation: a very well-supported expectation, but not a theorem. The paper proves the negation of that expectation's premise and says so in as many words (`rem:dictionary`: the standard premise "is that the gap in lattice units, aΔ, falls under every floor toward the contact end... Its negation reads: a positive floor on a positive extent, aΔ bounded below toward weak coupling"). One of the two pictures is wrong, and the question is decidable by the constructive apparatus this repository provides: the scheme bridge b_f^equiv = 2n·b_X (`thm:bridge`) calibrates the coupling coordinate against the fundamental-character action, and the certified brackets are finite objects a simulation can be run against. Until that comparison is run, the theorem and the standard scaling picture cannot both describe the measured theory. The repository's position is not "trust the theorem over the data." It is "here is the finite, decisive test."

### "Does the construction satisfy exact Euclidean covariance, given that the corner height (= √2·aΔ) is floored? You prove the degree-4 anisotropy has *positive multiplicity*. Your own theorem seems to forbid exact O(4) invariance."

It is worth going through this carefully and slowly. This was the reviewer's last standing structural objection and the most difficult one for them to overcome. The answer is a mechanism, not a limit. The question presumes the continuum functions are limits of the lattice correlation functions, which never become covariant at any fixed spacing. The construction runs the other way: the reconstructed relativistic families are defined on the **spectral side**, as weight folds over the located roots at the fiber's chord, read at the cone's coordinates (`thm:reconstruct`(ii), `lem:cone`). That is, they are read from the **degree-two** spectral data: located mass, weights, isotropic cone. And at degree two, `thm:restoration` item 1 is an exact ring identity: the degree-2 invariant rings of B_d and of O(d) *coincide*, at every number of arguments and every dimension. The scoping sentence "the statement is about which forms exist rather than about which are small" is the mechanism, not a caveat: at degree two, anisotropic forms **do not exist**. Nothing is approximately small, because there is nothing to be small. The certified degree-4 breaking (positive multiplicity, suppressed two powers of the spacing) never enters the reconstructed object at all; it lives in the certified bracket *widths around* it and the width within which the lattice instrument agrees with the covariant object. The floor on the corner height bounds a bracket width; it does not deform the covariant point inside the bracket.

### "Translations are the lattice's ℤᵈ. The Wightman axioms quantify over ℝ⁴."

Time is continuous by construction (the Hamiltonian's own). Spatial ℝᵈ acts on the reconstructed families exactly, by phase, at the momentum coordinates where they are defined (the chord cells, `thm:reconstruct`(ii)); the lattice translates are the instrument that locates the data, entering through the fibering (`lem:fiberdec`) and the momentum transform (`thm:restoration`), and the reader's continuum point "reads itself in through the rationals beside it." This is the constructive meaning of a function on ℝᵈ: certified brackets with moduli at every rational datum. The same side-switch as the covariance entry: exact at the reconstructed object, certified widths at the instrument.

### "Why isn't the Osterwalder–Schrader reconstruction performed? The Clay text cites those axioms."

Because the construction is Hamiltonian, and OS reconstruction is the Euclidean route *to* a Hamiltonian theory with a spectrum condition, which this formulation holds by construction (`rem:dictionary`, reconstruction item). The clause "axiomatic properties at least as strong as those cited" is answered property by property rather than by re-deriving the properties from a measure: positivity is the families' own Gram read (`thm:reconstruct`(iii)); the spectrum condition is the cut itself, with the gap `thm:main`(i); locality is exact commutativity at equal times with the cone read at unequal times; covariance is the restoration counts' (entries above); growth is capped (`thm:groundreads`(v)); the vacuum is cyclic (`lem:statespace`) and unique as a divisor count (`thm:SO`); and nontriviality is a theorem. The connected four-point read holds a positive located floor separating the object from every generalized free field (`lem:fourpoint`).

### "K = c₁³e^(−H_r) smells like numerology because it has the harmonic numbers in an exponent. Is it even a computed energy?"

What the theory *determines* is the contact pair (3, H_r) as two divisor reads: the order count 3 = 1 + 2 (the mass point's simple pole plus the ι-symmetrized weight's two base orders, off the renewal witness G₀ = z + c₁zG₀, `thm:channeldiv`) read at the base c₁, and the ruler excess H_r (the tower's generating object against the harmonic ruler, an exact finitely-supported polynomial identity, `thm:walkresidue`). The exponential form is those coordinates read against the classical rulers (ln c₁, 1) described as "the axes the usual formulation measures with" (`rem:dictionary`). Nothing is fit and nothing converges: the harmonic number arrives as the value at 1 of an exact polynomial with the geometric derivative, forced by the tower pairing φ_m = r/(m+r). A reader who wants the level as an energy restores the two scales explicitly: K·E₀·C₂(adj) (`rem:dictionary`, "The gap").

### "The Lean formalization doesn't cover the continuum theorems. So what does it actually prove?"

The status section further up this readme is the most accurate and current answer to this question, although it may lag progress in the code.

### "Has anyone actually verified this? One reviewer finding no error is not verification."

Two ambiguities in the question need to be addressed before I answer it. First, I would argue that the word verified is undefined because what counts as verified varies from person to person even within the serious mathematical community. Many verified proofs have fallen when checked by theorem solvers. I tend to take a strict reading to verified, and I hold myself to axiom-free Lean as the standard. Second, Lean only can tell you if a proof is correct, not if it is meaningful in any sense outside of its kernel. As a result, I am still a strong believer in peer review, and I welcome all feedback constructively given especially with regards to whether or not the proofs I make actually satisfy the claims a kernel cannot check. This work has not yet undergone formal peer review. Therefore by my own definition, the current work is not verified.

### "What are your plans for this project moving forward?" (Not actually asked by the reviewer, but I wish it had been!)

A rough sketch:

- Finish the `thm:main` Lean transcription
- Write a standalone repository (hopefully with community input) to define a neutral statement of the Yang-Mills problem in Lean using conventional types and Mathlib. Like with this repo it will be tex-first and the lean will formalize it.
- Write an adapter that connects my proof to the neutral interface
- Submit the work for peer review and possibly also to somewhere like [Palomar](https://palomar-registry.org/)

## Proof Methodology

Every Lean declaration depends solely on the empty axiom set. Specifically, this means no
`propext`, `Quot.sound`, `Classical.choice`, `sorryAx`, and no native
reflection (`native_decide`); the kernel checks everything.  The package is
Lean core alone: `lake-manifest.json` lists no packages and no module
imports outside `MassGap` and `MassGapChecks`.  No declaration is
`noncomputable`, `partial`, `unsafe`, `opaque` or an `axiom`; every object
computes by kernel reduction.  Every public `Prop`-valued definition comes with its `Decidable` instance beside it.  The batteries in
[lean/MassGapChecks/](lean/MassGapChecks/) decide directly by kernel `decide`.

## Building

Install [elan](https://github.com/leanprover/elan); `lean-toolchain` pins
`leanprover/lean4:v4.32.2`, which elan fetches on first use.  Then

    cd lean
    lake build

builds both libraries and every battery.  The build has no
network dependency past the toolchain.  `lakefile.toml` sets
`warningAsError`, so a `sorry` anywhere in either library is a build error.

## Verifying the axiom claim

After the build,

    lake env lean AxiomCheck.lean

walks every constant of both libraries with `Lean.collectAxioms` and prints

    constants read: 31881
    constants depending on axioms: 0

ending in an error if any constant depends on any axiom.  A single
declaration reads the same way in any file importing the libraries:

    import MassGap
    #print axioms main.clauseII
    #print axioms gappos.windowCut

each answering `does not depend on any axioms`.

## Reading the tree

- [lean/MassGap.lean](lean/MassGap.lean) lists the content modules in
  dependency order, from `Ground` (the positive naturals with pairs as data,
  `def:ground`) through the label calculus, the interfaces, the certificates
  and the chain to `Main`.
- [lean/MassGapChecks/](lean/MassGapChecks/) mirrors the content modules
  file for file. Each battery pins committed data, and a refusal
  (`example : ¬ …`) pins the hypothesis it isolates.

## Citing

Every GitHub release of this repository is archived on Zenodo under the
concept DOI [10.5281/zenodo.22018060](https://doi.org/10.5281/zenodo.22018060),
which resolves to the latest version.  The repository is licensed under the Apache License 2.0
([LICENSE](LICENSE)).
