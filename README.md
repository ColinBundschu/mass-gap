# The mass gap over the compact simple groups

[![lean](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml/badge.svg)](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22018060.svg)](https://doi.org/10.5281/zenodo.22018060)

This repository presents a nominally complete manuscript, [docs/theory.tex](docs/theory.tex) ([PDF](docs/theory.pdf)), and its in-progress Lean 4 formalization, [lean/](lean/). The manuscript states and derives a mass gap for lattice gauge theory over every compact simple group (`thm:main`), with `rem:dictionary` translating the result into the conventional formulation, including the Jaffe–Witten statement of the Yang–Mills problem. The proof is constructive over the positive naturals using only addition and multiplication. This restriction was chosen explicitly to keep the Lean transcription constructive and eventually emit certified brackets for physical quantities directly comparable with Monte Carlo and experimental results.

The TeX is authoritative, and the Lean is its transcription. To enforce this structurally, every top-level Lean declaration sits in a namespace matching a label in `theory.tex`, and the docstring of each Lean module under [lean/MassGap/](lean/MassGap/) states exactly which clauses associated with that label the module formalizes.

## Status

While `theory.tex` is in theory a complete proof, this should be weighed against the fact that it has only been reviewed by its author for completeness and correctness. The transcription of `theory.tex` into Lean is mostly complete, and this section details which proofs in `theory.tex` are and are not formalized in Lean.

`thm:main` has three clauses, stated over the domain `main.Member` ([lean/MassGap/Main.lean](lean/MassGap/Main.lean)): the $A$-series at every residue, $B_\ell$, $C_\ell$ and $D_\ell$ at their index floors, and $G_2$, $F_4$, $E_6$, $E_7$ and $E_8$ once each.

**Formalized in Lean.** All three clauses hold at every member:

- Clause (i), gap positivity, at each member's floor window (`main.clauseI_all`)
- Clause (ii), the contact pair $(3, H_r)$ together with the window half that every named cut edge is a located root of the window pencil's symbol attained at a word image, at the TeX's own quantifier (`main.clauseII_all`)
- Clause (iii)'s member layer, the corner cell's floor datum through the one disconjugacy certificate transported across the residues (`main.clauseIII_all`).

The label calculus, the carrier and pencil interfaces, the count certificates, the fibering and decimation tiers, the ground reads, the corner certificate and the tail read's floor-line certificate are landed beneath them.

**Not Yet Formalized in Lean.** These items are not yet transcribed from the TeX:

- Clause (i) at every region, cutoff and interior end-weight ray: the cell list past the free cell, the counts on the decimated head across a cell, and the truncation modulus with the meet over the directed windows.
- The chain's height at the contact end, the tail read `thm:continuum`(iii) consumes for the spacing: the scale key under which a window's height sits below a stated floor, and its join at `main`.
- Clause (iii)'s composite statement at `main`: the datum-level closure and site counts, the corner cell's positive extent, and each cell's edge read at a word image.

**Long-term Objectives.** These items are not directly related to the formalization of the proof, but are essential work.

- Create a standalone repository, with community input where possible, stating the Yang-Mills problem neutrally in Lean over conventional types and Mathlib, TeX-first like this one
- Create an adapter from this proof to that neutral interface
- Submit the proof for peer review, possibly also to a registry such as [Palomar](https://palomar-registry.org/).

## Proof Methodology

Every Lean declaration depends solely on the empty axiom set. Specifically, this means no
`propext`, `Quot.sound`, `Classical.choice`, `sorryAx`, and no native
reflection (`native_decide`); the kernel checks everything. The package is
Lean core alone: `lake-manifest.json` lists no packages and no module
imports outside `MassGap` and `MassGapChecks`. No declaration is
`noncomputable`, `partial`, `unsafe`, `opaque`, or an `axiom`; every object
computes by kernel reduction. Every public `Prop`-valued definition comes with its `Decidable` instance beside it. The batteries in
[lean/MassGapChecks/](lean/MassGapChecks/) decide directly by kernel `decide`.

## Deliverables and Failure Criteria

By construction, everything proven in Lean is mathematically correct for what it states (although emphatically one must be careful reading significance from what is proved). However the same cannot be said for claims in the TeX that are not proven in Lean, errors in mapping between claims in the TeX and the corresponding Lean proofs, or interpretations of the physical relevance of what the Lean proves. If it becomes clear that a fundamental contradiction, inconsistency, or shortfall dooms the top-level proof, then this repository will serve as a constructive tombstone to where this approach failed and why.

That said, the deliverable of this repository is not simply a correct, complete Yang-Mills proof, which remains exceedingly unlikely. Specifically, this repository aims to tackle the fact that every rigorous result on the Yang–Mills gap is analytic and non-algorithmic. Osterwalder-Seiler's strong-coupling gap and Balaban's renormalization-group work are proofs in the ordinary sense: there is no procedure that, given a group and a coupling, produces a certificate that a gap exists there, and no procedure that could return "no" as a theorem either. What this repo does is give the gap a decision structure. In particular, once the transport lemmas make the head's counts uniform in volume and bound the full window by them, the instrument is symmetric: running the certificate on the $K = 0$ sector of the fibered corner head with the vacuum dressing subtracted returns a certified bracket on that gap at every scale $\eta$, and whether the bracket falls under every floor along the tail or holds one is, either way, a theorem about how the $K = 0$ lift of the lattice model scales with $\eta$, not silence. A certified statement that the gap in lattice units goes to zero along the approach, uniform in volume, would be the first rigorous half of a continuum limit; a certified statement that it does not would be more surprising still. Either result would be a machine certified finding, and an unqualified success under the framework of this repository.

## Building

Install [elan](https://github.com/leanprover/elan); `lean-toolchain` pins
`leanprover/lean4:v4.32.2`, which elan fetches on first use. Then

    cd lean
    lake build

builds both libraries and every battery. The build has no
network dependency past the toolchain. `lakefile.toml` sets
`warningAsError`, so a `sorry` anywhere in either library is a build error.

## Verifying the axiom claim

After the build,

    lake env lean AxiomCheck.lean

walks every constant of both libraries with `Lean.collectAxioms` and prints

    constants read: 34643
    constants depending on axioms: 0

ending in an error if any constant depends on any axiom. A single
declaration reads the same way in any file importing the libraries:

    import MassGap
    #print axioms main.clauseII
    #print axioms gappos.windowCut

each reports `does not depend on any axioms`.

## Reading the tree

- [lean/MassGap.lean](lean/MassGap.lean) lists the content modules,
  `Ground` (the positive naturals with pairs as data, `def:ground`)
  first, then the label calculus, the interfaces, the certificates,
  the chain, and `Main`; each module's own `import` lines are its
  dependency order.
- [lean/MassGapChecks/](lean/MassGapChecks/) mirrors the content modules
  file for file. Each battery pins committed data, and a refusal
  (`example : ¬ …`) pins the hypothesis it isolates.

## FAQ

The questions below aggregate, in roughly their original order and tone, objections raised by various reviewers of the repository.

### "This pattern-matches to crankery: solo author, invented vocabulary, Millennium-problem claim. Why should anyone read a PDF of more than 100 pages of dense, idiosyncratic mathematics?"

Even with the terrible priors aside, I'd argue that no one should read the paper at least initially. And if the only deliverable was the paper, I would never have begun this project. Instead, the construction is built so that every claim in the development will be machine-checked by Lean with zero axioms. The intended order becomes: verify the top-level theorems in Lean correspond to real-world meaning, then check that the Lean compiles axiom-free.

### "Why work on something where the social consequences will be so severe? You have a promising career in academia, why tarnish it with a black eye (or worse)?"

I am a firm believer that anyone should be able to make an honest, serious attempt at a hard problem and be treated with basic professional respect (I do not think this entitles that person or their work to anyone else's time, energy, or attention). This is a problem that fascinates me, and with the rise of theorem provers like Lean I have an unprecedented opportunity to see my ideas through in a formal way. Nonetheless, this has not been without repercussions. I am deeply disturbed by the level of dehumanization directed toward me both inside and outside of academia when people realize I am working on this problem. It has involved expletives, name-calling, and even threats. I request that anyone looking to engage with my work do exactly that: engage with the work. An extraordinary claim warrants extraordinary scrutiny. It does not warrant extraordinary cruelty.

### "Why does the paper use highly idiosyncratic language at all, such as 'reads,' 'balance pairs,' 'located,' 'priced', instead of standard terminology?"

First, maybe it shouldn't. But it did not end up this way accidentally: a lot of time was spent trying to conform to standard terminology where possible, and each deviation was chosen for a reason and, where one exists, a precedent in the literature. The paper carries its own translation table (`rem:dictionary`, "The names"). The most salient cases:

- **Balance pairs $\langle u:v\rangle$ and scalar pairs $[a:b]$.** The entire development is constructive over the positive naturals: there is no subtraction and no division as primitive operations. $\langle u:v\rangle$ is the difference $u-v$ and $[a:b]$ the quotient $a/b$, *as data with their defining identities* rather than as operations assumed to exist. This is what lets every statement be a statement about naturals, and what made an axiom-free Lean formalization possible.
- **"Located."** Bishop's constructive analysis, by name (`rem:dictionary`). A located root or datum comes with an isolating bracket and a modulus. It is a real number you can compute against, not a real number you have merely proven to exist.
- **"Reversal count."** The negative index of inertia; the two-splits-one-count clause is Sylvester's law of inertia (`lem:inertia`, named in the dictionary). Eigenvalue counting throughout is exact integer $LDL^{\mathsf T}$ arithmetic, never floating-point.
- **"Deck relation / deck families."** The double cover $w=z+z^{-1}$ (Joukowski map); the chord $t=2\cos k$ is the Chebyshev variable of the momentum fiber (`rem:dictionary`). Momentum on the lattice is handled by commuting chord operators, exactly.
- **"Labels," "blocks," "contents."** Irreducible representations, their carriers, and weights. The rebuild from scratch (through the Weyl character formula, fusion rules, and Weingarten calculus) exists so that the fusion interface (`con:fusion`) is *derived data*, which is a requirement for the formalization.
- **"Residue" $r$.** The dual Coxeter number less one, $r+1=h^\vee$ (`rem:dictionary`, "The members"), the one scalar the whole classification is organized around.

The deviations are systematic, not decorative: they mark exactly the places where the standard term presumes classical operations (subtraction, division, limits, choice) that the construction refuses to presume.

### "There is no bibliography. Zero citations."

This omission is **temporary**, not an assertion that public mathematical claims require no engagement with the literature. During transcription, I repeatedly load the complete TeX into context for AI-assisted cross-checking against the rest of the proof. At approximately 500,000 tokens, the document already consumes substantial cost and working context. Once the Lean transcription is complete, I will add an abstract, introduction, literature positioning, bibliography, and the remaining conventional front matter.

### "Renormalization, asymptotic freedom, beta function, continuum limit: zero occurrences. A Yang–Mills proof cannot fail to contain these."

These terms play different roles in the conventional approach. Renormalization and the beta function control a perturbative expansion, while the continuum limit is ordinarily constructed through a limit of lattice measures. This manuscript uses neither route. It instead claims a Hamiltonian construction exact at every coupling, followed by a direct located reconstruction from its spectral data (`thm:continuum`, `thm:reconstruct`).

The running scale is replaced by the **unit map** (`rem:dictionary`): at physical gap $\Delta$, the spacing is $a=h/(\sqrt{2}\,\Delta)$ at the chain's height $h$ at the scale, a located bracket (`lem:corner`'s cell floor), one equation per scale, so the trajectory's spacings are the heights' reads. Calibration is therefore an output rather than a scheme choice; the scheme dependence that remains is isolated in the corner outputs (`thm:decomp`).

The manuscript also addresses the standard weak-coupling picture directly. The weak-coupling entry in `rem:dictionary` states lattice Maxwell theory in each Lie-algebra direction with massless dispersion as $k\to0$ as the classical comparison and identifies the gap as the certified lift above that comparison.

### "Wouldn't this argument also 'prove' a mass gap for $U(1)$? If yes, it proves too much."

No. The theorem ranges over compact simple groups, so $U(1)$ is not a member of its domain. More importantly, the gap mechanism requires simple-group data that have no literal $U(1)$ specialization: a highest-root adjoint label $\theta$, its self-fusion channel, and the associated fusion-strictness parameter. Since $U(1)$ has no root system and hence no such $\theta$, $c_1$ is not a $U(1)$ multiplicity that can simply be evaluated as zero.

The abelian comparison nevertheless identifies two precise failures. If the absent non-abelian channel is represented by zero channel weight, the boundary resolvent

$$
G_0 = z + c_1 z G_0
$$

reduces to $G_0=z$, leaving no mass pole, bound state, or gap coordinate. Independently, the charged tower loses the strict linear term:

$$
C_2(m\theta) = m(m+r)
\qquad\longrightarrow\qquad
C_2(m) = m^2
$$

in the abelian theory (`prop:anchor`). Thus the two ingredients that produce the mass point (the adjoint self-fusion channel and its positive fusion strictness) are absent. The argument therefore neither states nor derives a mass gap for $U(1)$.

### "Does the construction satisfy exact Euclidean covariance, given that the corner height $`h=\sqrt{2} \, a\Delta`$ is bracketed at every scale? You prove the degree-4 anisotropy has *positive multiplicity*. Your own theorem seems to forbid exact $O(4)$ invariance."

The answer is a reconstruction, not a claim that the lattice correlation functions become exactly covariant at some fixed spacing. At finite spacing the lattice families remain $B_d$-invariant and contain genuine degree-four anisotropic terms. The construction does not discard or deny those terms in the lattice data.

Instead, the lattice system acts as an instrument that locates spectral data: masses, weights, and the quadratic cone. The reconstructed relativistic families are then defined on the spectral side, as weight folds over the located roots at the fiber's chord, evaluated at the cone's coordinates (`thm:reconstruct`(ii), `lem:cone`). The key statement is therefore the factorization

$$
\text{lattice bracket data}
\longrightarrow
\text{located roots, weights, and quadratic cone}
\longrightarrow
\text{relativistic families}.
$$

At degree two, `thm:restoration` item 1 gives an exact ring identity: the degree-two invariant rings of $B_d$ and $O(d)$ coincide, for every number of arguments and in every dimension. Consequently, the cone through which the reconstruction factors is exactly isotropic; there is no degree-two anisotropic form that could deform it. This ring identity alone would not establish covariance of the reconstructed families. What does the work is the additional factorization in `thm:reconstruct`: the reconstructed object depends on the located spectral data and the quadratic cone, not on the higher-degree lattice invariants.

The certified degree-four breaking therefore remains part of the comparison data. It controls the brackets within which the finite-spacing lattice instrument agrees with the reconstructed covariant object, but it is not an input to that object's cone or covariance law. Likewise, the height's bracket at each scale controls the certified comparison width; it does not deform the covariant spectral point inside that bracket.

### "Translations are the lattice's $\mathbb{Z}^d$. The Wightman axioms quantify over $\mathbb{R}^4$."

Time is the pencil's own and continuous through the Hamiltonian evolution. The lattice translations in $\mathbb{Z}^d$ are the instrument that locates the spectral data, entering through the fibering (`lem:fiberdec`) and the momentum transform (`thm:restoration`), and the reconstructed families are stated at the momentum coordinates of the cone (`thm:reconstruct`(ii)), the momenta reading through the $t$-cells at every continuum point (`rem:dictionary`, "Invariance"); a reader's continuum point reads the located brackets in through its own rational comparisons (`rem:dictionary`, "The continuum's points"). Thus the discrete translation action belongs to the lattice instrument, while the reconstructed object is stated at the continuum's coordinates.

### "Why isn't the Osterwalder–Schrader reconstruction performed? The Clay text cites those axioms."

Because the construction is Hamiltonian. Osterwalder–Schrader reconstruction is a route from Euclidean measures to a Hamiltonian theory with a spectrum condition; this manuscript begins with the Hamiltonian structure and instead addresses the required axiomatic properties individually. The manuscript assigns those obligations as follows:

* positivity to the families' Gram reads (`thm:reconstruct`(iii));
* the spectrum condition and positive gap to the cut and `thm:main`(i);
* locality to exact equal-time commutativity (the algebra is commutative, `prop:algebra`) together with the propagation bracket at unequal times (`thm:groundreads`(vi));
* covariance to the restoration and reconstruction statements above;
* growth control to `thm:groundreads`(v);
* cyclicity to `lem:statespace` and uniqueness of the vacuum to the divisor count in `thm:SO`; and
* nontriviality to the positive connected four-point floor in `lem:fourpoint`, which separates the reconstructed object from every generalized free field.

This is the manuscript's claimed Hamiltonian replacement for OS reconstruction; it is not itself an OS reconstruction from a Euclidean measure.

### "$`c_1^3e^{-H_r}`$ smells like numerology because it has the harmonic numbers in an exponent. Is it even a computed energy?"

What the theory *determines* is the contact pair $(3,H_r)$ as two divisor reads: the order count $3=1+2$ (the mass point's simple pole plus the $\iota$-symmetrized weight's two base orders, off the renewal witness $G_0=z+c_1zG_0$, `thm:channeldiv`) read at the base $c_1$, and the ruler excess $H_r$ (the tower's generating object against the harmonic ruler, an exact finitely-supported polynomial identity, `thm:walkresidue`). The exponential form is those coordinates read against the classical rulers $(\ln c_1,1)$ described as "the axes the usual formulation measures with" (`rem:dictionary`). Nothing is fitted and nothing converges: the harmonic number arrives as the value at $1$ of an exact polynomial with the geometric derivative, forced by the tower pairing $\varphi_m=r/(m+r)$. It is not an energy: the contact pair is two counts of the walk's data, free of unit and of scale (`thm:unitschain`), the walk's mass point an isolated pole below its band at base two and at the band's edge at base one (`thm:channeldiv`). The quantity that restores as an energy is a window cut's edge, $`E_0\,\kappa\,C_2(\mathrm{adj})`$ at the edge's pair $\kappa$ (`rem:dictionary`, "The gap").

### "Has anyone actually verified this?"

This work has not been independently verified. The current release has a reproducible Lean build and an empty axiom report for the declarations listed above. That establishes derivability of the encoded statements. It does not establish that the remaining TeX has been transcribed, that the dictionary faithfully states conventional Yang-Mills, or that the argument has survived expert review.

## Citing

Every GitHub release of this repository is archived on Zenodo under the
concept DOI [10.5281/zenodo.22018060](https://doi.org/10.5281/zenodo.22018060),
which resolves to the latest version. The repository is licensed under the Apache License 2.0
([LICENSE](LICENSE)).
