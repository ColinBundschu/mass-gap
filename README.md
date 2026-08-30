# The mass gap over the compact simple groups

[![lean](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml/badge.svg)](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22018060.svg)](https://doi.org/10.5281/zenodo.22018060)

A manuscript and its Lean 4 formalization.  The manuscript,
[docs/theory.tex](docs/theory.tex) ([PDF](docs/theory.pdf)), states and
derives `thm:main`, a mass gap for lattice gauge theory over every compact
simple group, constructively over the positive naturals with the sum and the
product; the in-progress Lean tree under [lean/](lean/) formalizes it with an empty axiom set.

The tex is the authority and the Lean is its transcription: every top-level
Lean declaration sits in a namespace matching a label in
`theory.tex` (e.g. `gappos.sandwich_lo` transcribes `thm:gappos`, `inertia.rev_add`
transcribes `lem:inertia`). The docstring at the head of each module under
[lean/MassGap/](lean/MassGap/) states exactly which clauses of its label the
module holds.

## Status

`theory.tex` provides a complete proof of the Yang-Mills mass gap:
it states and derives every clause of `thm:main`, and
`rem:dictionary` reads the result against the conventional
formulation, the Jaffe-Witten statement included.  The Lean tree is
an in-progress transcription of that proof: most of it is
formalized, and this section says exactly which parts are and are
not.  The docstring at the head of each module is the ledger of
record for what that module holds.

`thm:main` has three clauses, stated over `main.Member`
([lean/MassGap/Main.lean](lean/MassGap/Main.lean)), the
classification's stated domain: the `A`-series at every residue,
`B_l`, `C_l`, `D_l` at their index floors, and `G2`, `F4`, `E6`,
`E7`, `E8`, each member once.

Formalized:

- **Clause (i), gap positivity, is closed at every member**:
  `main.clauseI_all` holds the tie at every member of the
  classification, the two committed chain reads as parametric
  theorems over the rank at the diagonal windows with `E8`'s
  coupled window its own case.  Beneath it sit
  the count certificates (`lem:inertia`, `thm:certconstruct`,
  `lem:stage`, `lem:split`, `lem:stagesplit`, `lem:hermitesign`,
  `lem:deckfactor`, `thm:windowsep`, `lem:cellcount`) and the chain
  (`lem:fiberdec`, `lem:grading`, `lem:relfiber`, `thm:decimation`,
  `lem:chargedcell`, `thm:truncation`, `lem:dualtrunc`,
  `lem:contactcell`, `lem:freecell`, `thm:flatstep`, `lem:speccut`,
  `thm:divisorid`, `thm:gappos`).
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
