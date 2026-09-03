# Scope and completion boundary

The two independently requested targets are complete at the audited
2026-09-03 checkpoint:

1. Explicit Ginibre reproducing/projection identities, including the
   weighted absolute-integrability result.
2. Actual iid complex Gaussian entries -> actual eigenvalue joint density
   -> all finite labelled marginal laws and factorial correlation measures.

The second arrow is not inferred from candidate-density normalization.
The development proves the actual Schur coordinate changes, their
Jacobians, the disjoint angular cover, auxiliary Gaussian integration,
and spectral measurability. Probability normalization is used only after
actual matrix-to-spectrum proportionality is established.

## No remaining external mathematical interface

The endpoint
`gaussianLabelledSpectralLaw_eq_withDensity` takes only a finite
dimension and a positive Gaussian scale. The variance-normalized marginal
and correlation-measure endpoints take `n = k + m > 0`.
They do not take an assumed Schur formula, Jacobian, measurable spectral
selection, angular integral, joint density, or correlation formula.

General supporting lemmas retain ordinary premises, such as unitarity,
triangularity, measurability, integrability, and orthogonality. All such
premises needed by the concrete Gaussian endpoints are discharged
internally. Data records store actual constructed matrices and proved
properties; they are not uninstantiated external interfaces.

Every authored theorem is included in the root import closure and in
`Audit.lean`. See [the final verification record](audit/verification-spectral-law.md).

## Correlation convention

The actual labelled law is constructed by uniformly permuting the
ordered characteristic roots of the actual Gaussian matrix.
Exchangeability is proved. The factorial correlation measure is defined
in the standard equivalent convention as `n!/(n-k)!` times its
`k`-label marginal. Its kernel-determinant density is proved at measure
level, not just as a candidate marginal integral.

The `codex/linear-statistics` extension adds the separate combinatorial
API expressing this measure as the expectation of a sum over injective
index selections, signed spectral integration with L1 transport, and
the actual linear-statistic expectation/covariance/variance formulas.
The L2 hypotheses imply every required intermediate L1 assertion.
Zero and one dimensions are handled explicitly. The extension contains
62 additional theorems in seven modules; its cloud verification status
is stated in the README. It adds no external mathematical interface.

## Outside this independent task

This is not a formalization of every result in BC12. Asymptotic circular-law
estimates, shifted least-singular-value estimates, and other downstream
random-matrix results are outside the two targets above.

No migration to Section 3, vendor replacement, downstream rebuild, or
changes to the original manuscripts were made. Those require a separate
authorized integration task. This development is published in its own
repository, with GitHub Actions for independent build and axiom auditing.

Historical `*-schur-jacobian`, `*-schur-atlas`, and earlier audit
records are preserved as checkpoints, not descriptions of the current
completion boundary.
