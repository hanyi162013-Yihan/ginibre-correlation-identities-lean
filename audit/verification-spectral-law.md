# Actual Gaussian spectral law and correlations — 2026-09-03

## Executed checks

- `lake --no-cache build`: exit 0, 3128 jobs, root target built.
- `lake env lean -j 1 Audit.lean`: exit 0.
- 463 distinct authored theorem declarations and 463 corresponding
  `#print axioms` outputs; no omissions, duplicate names, or extra entries.
- Every audited dependency is in
  `{propext, Classical.choice, Quot.sound}`. There is no `sorryAx`,
  external mathematical axiom, or native-evaluation oracle in those
  dependencies.
- All 76 mathematical modules are in the transitive import closure
  of `Ginibre.lean`.
- Authored-source scan: no `sorry`, `admit`, `unsafe`, custom
  `axiom`, `native_decide`, or `set_option`. No heartbeat,
  recursion-depth, or similar checking limit was raised.
- All 81 source/configuration checksums in
  `sources-spectral-law.sha256` passed `shasum -a256 -c`.
- Pinned mathlib source checkout: clean. Mathlib revision:
  `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Module targets were built serially, followed by the root. Each Lean
  process used one worker. The build has only replayed non-fatal style
  and deprecated-name warnings; no proof warning is suppressed.
- No large cache download, old-project import, vendor migration, or
  modification of reference PDFs occurred.

This checkpoint contains 233 additional theorems in 33 additional
mathematical modules since the historical 230-theorem full-Jacobian
checkpoint. Historical verification files are preserved.

## Actual endpoints, not assumed interfaces

`gaussianMatrixLaw` is the product of the normalized planar Gaussian
entry laws; independence and entry marginals are proved.
`gaussianOrderedSpectralLaw` is its spectral pushforward through a fixed
linear coordinate split. The selected values reproduce the actual
characteristic polynomial on the almost-sure simple-spectrum locus.

The proof supplies Schur existence, ordered phase uniqueness, actual
exponential charts, their full real Jacobians, a spectrum-independent
angular cover, a measurable disjointification, exact product coordinate
volume, auxiliary Gaussian integrals, and spectral measurability.
A proved global proportionality theorem precedes normalization.

`gaussianLabelledSpectralLaw` is the finite uniform mixture of
permutations of that actual ordered law, not a definition by a target
density. The theorem `gaussianLabelledSpectralLaw_eq_withDensity`
identifies it with the normalized explicit determinant density, for
every finite dimension and every `a > 0`. Exchangeability is proved.

For `n = k + m > 0` and scale `a = n`,
`gaussianRetainedSpectralLaw_eq_withDensity` proves the actual
coordinate marginal has density `m!/n! * Re(det K)`.
`ginibreFactorialCorrelationMeasure_eq_kernelDensity` proves that
the factorial-scaled actual marginal measure has density `Re(det K)`.
The zeroth, one-point, and two-point density formulas are also checked.
The factorial correlation convention is documented in
[REMAINING.md](../REMAINING.md).

The previously verified explicit reproducing and weighted projection
identities remain included in the same root and all-theorem audit.
There is no remaining Schur, BC12, or van Handel mathematical interface
in these concrete Gaussian endpoints. The ordinary positive-scale,
dimension, and measurable-test premises are printed by `Audit.lean`.

## Evidence

- [Root build output](build-spectral-law.log)
- [All theorem axioms and endpoint types/definitions](axioms-spectral-law.log)
- [Source/configuration hashes](sources-spectral-law.sha256)
- [Complete file list and mathematical route](../README.md)

This independent task is complete for the two scoped targets. It does
not claim all BC12 asymptotic estimates, a separate injective-index
counting API, downstream Section 3 integration, or GitHub publication.
