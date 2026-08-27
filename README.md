# The mass gap over the compact simple groups

[![lean](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml/badge.svg)](https://github.com/ColinBundschu/mass-gap/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22018060.svg)](https://doi.org/10.5281/zenodo.22018060)

A manuscript and its Lean 4 formalization.  The manuscript,
[docs/theory.tex](docs/theory.tex) ([PDF](docs/theory.pdf)), states and
derives `thm:main`, a mass gap for lattice gauge theory over every compact
simple group, constructively over the positive naturals with the sum and the
product; the Lean tree under [lean/](lean/) formalizes it with an empty axiom set.

The tex is the authority and the Lean is its transcription: every top-level
Lean declaration sits in a namespace matching a label in
`theory.tex` (`gappos.sandwich_lo` transcribes `thm:gappos`, `inertia.rev_add`
transcribes `lem:inertia`). The docstring at the head of each module under
[lean/MassGap/](lean/MassGap/) states exactly which clauses of its label the
module holds.

## Status

While the proof in `theory.tex` is complete, **the Lean is not yet a complete formal proof of the Yang-Mills mass gap.**  What
the tree holds at this release, read off [lean/MassGap/Main.lean](lean/MassGap/Main.lean):

- `main.Member` is the classification's stated domain, with the `A`-series at
  every residue; `B_ℓ`, `C_ℓ`, `D_ℓ` at their index floors, and `G₂`, `F₄`,
  `E₆`, `E₇`, `E₈`. The member's weight table, derived residue, base
  and fusion interface read off the carried datum.
- **Clause (ii)** of `thm:main`, the contact pair `(3, H_r)`, is the
  decidable read `main.clauseII` (`thm:closing` at the member's own base and
  residue), decided by kernel `decide` at every committed member in
  [lean/MassGapChecks/Main.lean](lean/MassGapChecks/Main.lean).
- **Clause (i)**, positivity of the cut of `𝒦` at every interior coupling, is
  not yet stated at `main`.  Its derivation tier is landed: the count
  certificates (`lem:inertia`, `thm:certconstruct`, `lem:stage`,
  `lem:split`, `lem:stagesplit`, `lem:hermitesign`, `lem:deckfactor`,
  `thm:windowsep`, `lem:cellcount` with its boundary clause), the chain
  (`lem:fiberdec`, `lem:grading`, `lem:relfiber`, `thm:decimation`,
  `lem:chargedcell`, `thm:truncation`, `lem:dualtrunc`, `lem:contactcell`,
  `lem:freecell`, `thm:flatstep`, `lem:speccut`, `thm:divisorid`), and
  `thm:gappos`'s sandwich, transport, cell chain, cutoff price and window
  cut.  The wiring of those tiers into one statement over `main.Member`
  is the open item.
- **Clause (iii)**, the continuum reads, is not yet stated at `main`.
  `lem:corner`'s coordinate, shifted scaling, drift, grade-key, cap and
  count tiers and `thm:restoration`'s first tier are landed;
  `lem:cornerpivot`, `thm:groundreads`, `lem:momentfold`, `lem:cone`,
  `lem:fourpoint`, `thm:continuum`, `thm:decomp` and `thm:reconstruct`
  have no Lean yet.
- `lem:sectorspan` and `lem:attained` (the requirement mirrors) have no Lean
  yet.
- `rem:dictionary`, the correspondence between the manuscript's objects and
  the conventional formulation (the Jaffe-Witten statement among them), is
  prose by design and is not formalized: the manuscript's own derivations
  hold with the remark deleted.

The snapshot is taken from the development repository at commit
`9b0e7ce85e5e38914e7b3887a5d7a0c7680bd348` (2026-08-25).

## Proof Methodology

Every Lean declaration depends only on the empty axiom set. Specifically, this means no
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
`warningAsError`, so a `sorry` anywhere in either library is a build error
(`declaration uses sorry`): `lake build` completing indicates that none
exists.

## Verifying the axiom claim

After the build,

    lake env lean AxiomCheck.lean

walks every constant of both libraries with `Lean.collectAxioms` and prints

    constants read: 24174
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
  file for file; a battery pins a read at committed data, and a refusal
  (`example : ¬ …`) pins the hypothesis it isolates.

## Citing

Every GitHub release of this repository is archived on Zenodo under the
concept DOI [10.5281/zenodo.22018060](https://doi.org/10.5281/zenodo.22018060),
which resolves to the latest version.  The repository is licensed under the Apache License 2.0
([LICENSE](LICENSE)).
