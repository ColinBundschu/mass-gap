# The mass gap over the simply connected compact simple groups

[![lean](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml/badge.svg)](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22018060.svg)](https://doi.org/10.5281/zenodo.22018060)

This repository consists of a manuscript, [docs/theory.tex](docs/theory.tex) ([PDF](docs/theory.pdf)), and its in-progress Lean 4 formalization, [lean/](lean/). The manuscript develops a constructive approach to the lattice mass gap over every simply connected compact simple group (`thm:main`). The intended relativistic continuum conclusion includes the Jaffe–Witten formulation of the Yang–Mills problem; the conventional requirements are described in `rem:dictionary`. The construction builds only on the positive naturals with addition and multiplication. This restriction was chosen explicitly to keep the Lean transcription constructive and eventually emit certified brackets for physical quantities directly comparable with Monte Carlo and experimental results. The Lean development is also a substantial constructive representation theory library in its own right, with exact results on highest-weight representations, tensor-product multiplicities, Weyl characters and dimensions, and Casimir eigenvalues.

In order to ensure strict compliance with the constructive criteria during development and transcription, the TeX and Lean are formulated in what could be described as a carefully designed domain-specific language (or less charitably described as an unconventional idiolect). This presentation makes the work difficult to engage with in its current form, which is a known and considered limitation, and the conventional presentation is a planned deliverable. Because of this, the repository should not be taken to be ready for a general audience, nor should the current form be considered publication-ready by the author's own standard.

The TeX is authoritative, and the Lean is its transcription. To enforce this structurally, public definitions and theorems map to labels in `theory.tex`, either directly by name or through their namespaces, and the docstring of each Lean module under [lean/MassGap/](lean/MassGap/) states exactly which clauses associated with that label the module formalizes.

## Status

The main goals are a positive mass gap for the full lattice theory, uniform in volume and representation cutoff, and a continuum construction with a fixed physical mass gap. The formalization covers the simply connected classical and exceptional compact simple groups.

**Fully Formalized in Lean.**

- **Spectral gap criterion.** Given a certified spectral decomposition, the gap above a finite Hamiltonian’s ground state is characterized by a two-moment positivity test, with equality at the gap eigenvector (`speccut.spec_to_cut`, `speccut.cut_to_spec`, `attained.attained_at`).
- **Gaps in finite truncations.** Positive spectral gaps are certified for selected finite Hamiltonian truncations for every group in the classification, throughout explicit coupling intervals (`main.clauseI_all`, `main.clauseI_counts`).
- **Representation theory.** For $\mathrm{SU}(N)$ at every $N\ge2$, the representation dimensions agree with the Weyl dimension formula, and tensor-product multiplicities satisfy the fusion, dimension, duality and Casimir identities used by the gauge theory (`weyldim.dimOf_spanLen`, `main.fusionLaws_A`).
- **Auxiliary weak-coupling chain.** Positive-gap certificates are verified for the auxiliary one-dimensional chain used in the weak-coupling argument, at an explicit scale for each group (`main.clauseIII_all`).

**Still to Complete.**

- **Uniform lattice mass gap.** Complete the Lean argument extending the existing finite-truncation gap certificates and spectral bounds to a positive gap uniform in spatial volume and representation cutoff for every group, first at strong coupling and then across the full range of finite couplings.
- **Weak-coupling continuum limit.** Derive and formalize the passage from the existing weak-coupling estimates to a relativistic continuum theory in two or more spatial dimensions, as the lattice spacing tends to zero at a fixed physical mass gap, with control of correlation functions, locality and spacetime symmetries.

**Long-term Objectives.** These items are not directly related to the formalization of the proof, but are essential work.

- Create a standalone repository, with community input where possible, stating the Yang-Mills problem neutrally in Lean over conventional types and Mathlib, TeX-first like this one.
- Create an adapter from this proof to that neutral interface.
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

By construction, everything proven in Lean is mathematically correct for what it states (although emphatically one must be careful reading significance from what is proved). However, the same cannot be said for claims in the TeX that are not proven in Lean, errors in mapping between claims in the TeX and the corresponding Lean proofs, or interpretations of the physical relevance of what the Lean proves. If it becomes clear that a fundamental contradiction, inconsistency, or shortfall dooms the top-level proof, then this repository will serve as a constructive tombstone to where this approach failed and why.

That said, the deliverable of this repository is not simply a correct, complete Yang–Mills proof, which remains exceedingly unlikely. Beyond that goal, the project aims to provide executable constructions and independently checkable Lean certificates for spectral bounds, alongside its constructive representation theory library.

The framework aims to produce certified gap brackets together with uniform bounds controlling their behavior along the continuum trajectory. Establishing that behavior requires proofs of the bounds across scales, spatial volumes and representation cutoffs. A proof that the gap in lattice units either tends to zero along the approach or stays bounded away from zero, established with machine-checked certificates and the required uniform bounds, would count as a success under the framework of this repository.

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

walks every constant of both libraries with `Lean.collectAxioms` and prints output of the form

    constants read: <count for this version>
    constants depending on axioms: 0

ending in an error if any constant depends on any axiom. A single
declaration reads the same way in any file importing the libraries:

    import MassGap
    #print axioms main.clauseII
    #print axioms gappos.windowCut

each reports `does not depend on any axioms`.

## FAQ

The questions below aggregate, in roughly their original order and tone, objections raised by various reviewers of the repository.

**The solutions below depend on completing the pending spacetime covariance construction (`pen:covariance`). These answers explain how the paper solves the problems with that construction assumed complete.**

### "Why does the paper use highly idiosyncratic language at all, such as 'reads,' 'balance pairs,' 'located,' 'priced', instead of standard terminology?"

First, maybe it shouldn't, and before it is presented in any official form, it won't. But it did not end up this way accidentally: a lot of time was spent trying to conform to standard terminology where possible, and each deviation was chosen for a reason and, where one exists, a precedent in the literature. The paper carries its own translation table (`rem:dictionary`, "The names"). The most salient cases:

- **Balance pairs $\langle u:v\rangle$ and scalar pairs $[a:b]$.** The entire development is constructive over the positive naturals: there is no subtraction and no division as primitive operations. $\langle u:v\rangle$ is the difference $u-v$ and $[a:b]$ the quotient $a/b$, *as data with their defining identities* rather than as operations assumed to exist. This is what lets every statement be a statement about naturals, and what made an axiom-free Lean formalization possible.
- **"Located."** Bishop's constructive analysis, by name (`rem:dictionary`). A located root or datum comes with an isolating bracket and a modulus. It is a real number you can compute against, not a real number you have merely proven to exist.
- **"Reversal count."** The negative index of inertia; the two-splits-one-count clause is Sylvester's law of inertia (`lem:inertia`, named in the dictionary). Eigenvalue counting throughout is exact integer $LDL^{\mathsf T}$ arithmetic, never floating-point.
- **"Deck relation / deck families."** The double cover $w=z+z^{-1}$ (Joukowski map); the chord $t=2\cos k$ is the Chebyshev variable of the momentum fiber (`rem:dictionary`). Momentum on the lattice is handled by commuting chord operators, exactly.
- **"Labels," "blocks," "contents."** Irreducible representations, their carriers, and weights. The rebuild from scratch (through the Weyl character formula, fusion rules, and Weingarten calculus) exists so that the fusion interface (`con:fusion`) is *derived data*, which is a requirement for the formalization.
- **"Residue" $r$.** The dual Coxeter number less one, $r+1=h^\vee$ (`rem:dictionary`, "The members"), the one scalar the whole classification is organized around.

The deviations are systematic, not decorative: they mark exactly the places where the standard term presumes classical operations (subtraction, division, limits, choice) that the construction refuses to presume.

### "There is no bibliography. Zero citations."

This omission is **temporary**, not an assertion that public mathematical claims require no engagement with the literature. During transcription, I repeatedly load the complete TeX into context for AI-assisted cross-checking against the rest of the proof. Even with the proof environments excluded, these readings consume substantial working context and incur significant cost. Once the Lean transcription is complete, I will add an abstract, introduction, literature positioning, bibliography, and the remaining conventional front matter.

### "Renormalization, asymptotic freedom, beta function, continuum limit: zero occurrences. A Yang–Mills proof cannot fail to contain these."

These terms play different roles in the conventional approach. Renormalization studies how a theory changes with scale, and beta functions describe the scale dependence of its couplings; perturbation theory is one method of studying that dependence. Lattice constructions of a continuum theory must control observables as the spacing tends to zero and the volume grows. The approach combines finite-window Hamiltonian spectral constructions (`thm:reconstruct`) with the continuum correlation reads (`thm:continuum`), keeping the spectral data and their certified brackets as the computational objects.

The physical scale is set by the **unit map** (`rem:dictionary`): at physical gap $\Delta$, the spacing is $a=h/(\sqrt{2}\,\Delta)$ at the chain's height $h$ at the scale, a located bracket (`lem:corner`'s cell floor), one equation per scale, so the trajectory's spacings are the heights' reads. At a specified physical gap, the spacing is therefore an output of the height calculation.

The manuscript also addresses the standard weak-coupling picture directly. The weak-coupling entry in `rem:dictionary` states lattice Maxwell theory in each Lie-algebra direction with massless dispersion as $k\to0$ as the classical comparison and identifies the gap as the certified lift above that comparison.

### "Wouldn't this argument also 'prove' a mass gap for $U(1)$? If yes, it proves too much."

No. The theorem ranges over simply connected compact simple groups, so $U(1)$ is not a member of its domain. More importantly, the gap mechanism requires simple-group data that have no literal $U(1)$ specialization: a highest-root adjoint label $\theta$, its self-fusion channel, and the associated fusion-strictness parameter. Since $U(1)$ has no root system and hence no such $\theta$, $c_1$ is not a $U(1)$ multiplicity that can simply be evaluated as zero.

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

The paper resolves the symmetry mismatch by establishing exact covariance of the full continuum correlations. For a probe configuration $D$ and a spacetime transformation $g$, it proves

$$
C(g\cdot D)=C(D)
$$

by certifying that the difference between the two correlation reads is smaller than every prescribed positive width. The comparisons include the spectral weights, the transformed supports and probe indices, and all higher-degree contributions.

The degree-four multiplicity counts anisotropic tensors allowed by lattice symmetry (`thm:restoration`). It places no positive lower bound on their contribution to the continuum correlations. Those contributions can therefore disappear in the continuum comparison while being present at finite lattice spacing. The quadratic identity identifies the isotropic degree-two part; the full-correlation identity supplies the exact symmetry.

Bracketing $h$ is compatible with that exact result. The bracket specifies the precision of the spacing $a=h/(\sqrt{2}\,\Delta)$ and enters the certified comparison error. Its refinement lets the error fall below any positive tolerance, establishing equality of the values it encloses.

### "Translations are the lattice's $\mathbb{Z}^d$. The Wightman axioms quantify over $\mathbb{R}^4$."

The paper solves this by constructing continuous translations on the continuum word space. For each physical displacement $x$, it defines

$$
U(x)\,A\Omega=(\tau_x A)\Omega,
$$

where $\tau_x A$ is the translated probe. The correlation identities preserve inner products, so $U(x)$ is well-defined on probe-created vectors and extends to the Hilbert-space completion. The opposite translation gives its inverse, hence unitarity; composition gives $U(x+y)=U(x)U(y)$; and the continuity moduli give strong continuity. Time translations agree with Hamiltonian evolution. The resulting group is $\mathbb{R}^{d+1}$, hence $\mathbb{R}^4$ at $d=3$ (`rem:dictionary`, "Invariance").

The discrete lattice determines that action through the physical unit map. A lattice shift $n$ at spacing $a$ has displacement $an$. As the spacing shrinks, these displacements approximate any fixed spatial translation, and the comparison certificates make the limiting correlation independent of the approximating sequence. This identifies the continuous action with the original lattice theory.

### "Why isn't the Osterwalder–Schrader reconstruction performed? The Clay text cites those axioms."

The paper uses a direct Hamiltonian reconstruction. It constructs the Hilbert space from the positive state pairing on probe words, completes that space, and obtains time evolution from the Hamiltonian (`lem:statespace`, `thm:reconstruct`). The spacetime action transports the local observables on this space. Euclidean correlations are computed from the resulting theory as matrix elements of $e^{-t(H-\varepsilon_0)}$ (`thm:groundreads`(v)).

OS reconstruction runs the construction in the other direction: it starts with Euclidean correlation functions and recovers the Hilbert space and dynamics. Here those objects are already the construction's starting data. Reflection positivity, for example, follows directly because the time-reflected quadratic form is a squared Hilbert-space norm. Applying OS reconstruction to those Euclidean correlations would recover a representation of the theory constructed by the Hamiltonian route.

The [Clay statement](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf) specifies the axiomatic strength of the resulting theory, not a mandatory reconstruction algorithm. The paper addresses that requirement by establishing the properties directly on its Hamiltonian theory and local fields. This is why its argument does not need an intervening OS reconstruction from a Euclidean measure.

## Citing

Every GitHub release of this repository is archived on Zenodo under the
concept DOI [10.5281/zenodo.22018060](https://doi.org/10.5281/zenodo.22018060),
which resolves to the latest version. The repository is licensed under the Apache License 2.0
([LICENSE](LICENSE)).
