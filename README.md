# The mass gap over the compact simple groups

[![lean](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml/badge.svg)](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22018060.svg)](https://doi.org/10.5281/zenodo.22018060)

This repo presents a complete manuscript, [docs/theory.tex](docs/theory.tex) ([PDF](docs/theory.pdf)), and its in-progress Lean 4 formalization, [lean/](lean/).  The manuscript states and derives a mass gap for lattice gauge theory over every compact
simple group in `thm:main`, with
`rem:dictionary` presenting the results in the conventional
formulation, the Jaffe-Witten statement of the Yang-Mills problem included.  The proof is constructive over the positive naturals with the sum and the
product; this choice was made explicitly to enable Lean to formalize it with an empty axiom set.

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

`thm:main` has three clauses, stated over the domain `main.Member`
([lean/MassGap/Main.lean](lean/MassGap/Main.lean)): the `A`-series at every residue,
`B_l`, `C_l`, `D_l` at their index floors, and once each for `G2`, `F4`, `E6`,
`E7`, `E8`.

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
  dominance, ground-witness, count and block-chain tiers),
  `thm:groundreads` whole (clauses (i)-(vii) with (v')),
  `lem:momentfold` whole (the moment streams, the graded system,
  the truncation cap, the scale comparison and the datum
  assembly), `lem:fourpoint` whole, `lem:corner`'s corner-count,
  shifted-scaling, drift, grade-key, cap and count tiers, and
  `thm:restoration`'s first tier.

Open (no Lean yet):

- `lem:cornerpivot`'s remainder (the second root's compression and
  the decimated block chain's emitted certificate data) and
  `lem:corner`'s cell-floor clause with the corner-output clauses
  of `thm:decomp` and `thm:twoaction`.
- `lem:cone`, `thm:continuum`, `thm:reconstruct`.
- **Clause (iii)'s composite statement at `main`** (it consumes the
  items above), and the reverse correspondence walk (every tex
  label reached from a Lean namespace).

The snapshot is taken from the development repository at commit
`fe29955ce87a276a0e5aa729006514bedd15d4f0` (2026-08-29).

## Proof Methodology

Every Lean declaration depends soley on the empty axiom set. Specifically, this means no
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

    constants read: 29766
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
