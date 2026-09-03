# Ginibre kernel and correlation identities

Independent Lean 4.33.0 + mathlib project. The two requested targets are
complete: the explicit Ginibre kernel projection identities, and the
finite eigenvalue correlation densities derived from **actual independent
complex Gaussian matrix entries**, without assuming a Schur density or
an eigenvalue-distribution interface.

The core root build and all 463 theorem axiom audits passed on 2026-09-03
(3128 build jobs, 76 mathematical modules). See
[audit/verification-spectral-law.md](audit/verification-spectral-law.md).
The only audited axioms are subsets of Lean/mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound`.

The `codex/linear-statistics` development branch adds signed integration,
distinct-index Campbell formulas, and L2 covariance/variance corollaries
(83 modules, 525 theorem declarations in total). This extension is being
checked by GitHub Actions; the preceding 463-theorem checkpoint remains
the last completed audit until the branch run passes.

## What is proved

- `integral_kernel_product` and `integral_kernelWeight_section`:
  the off-diagonal reproducing identity and
  `integral |K_n(z,w)|² dw = n rho_n(z)`.
- `weighted_projection`: absolute integrability and the weighted
  identity for unbounded nonnegative measurable weights whenever
  `g * rho_n` is integrable. No bounded-weight assumption is added.
- `charpoly_eq_prod_schurSpectrum`: the selected spectrum reproduces
  the actual matrix's characteristic polynomial on the simple locus.
  Simple spectrum is proved almost surely from Gaussian entries.
- `aemeasurable_schurCoordinateSpectrum`: almost-sure measurability,
  constructed from the actual Schur atlas rather than assumed.
- `gaussianOrderedSpectralLaw_eq_candidate_chamber`: the actual
  ordered spectrum has density `n! * determinantDensity` on the
  lexicographic chamber.
- `gaussianLabelledSpectralLaw_eq_withDensity`: after uniform finite
  relabelling, the actual joint eigenvalue law has the explicit
  normalized Gaussian–Vandermonde/determinant density.
  `gaussianLabelledSpectralLaw_permute` proves exchangeability.
- `gaussianRetainedSpectralLaw_eq_withDensity`: retaining `k` of
  `k+m` actual labelled eigenvalues gives density
  `m!/(k+m)! * Re(det K)`, by genuine product-coordinate Fubini.
- `ginibreFactorialCorrelationMeasure_eq_kernelDensity`: the actual
  factorial-scaled marginal measure has density `Re(det K)`.
  `ginibreCorrelationDensity_one` and
  `ginibreCorrelationDensity_two` give the one- and two-point formulas.

The correlation measure uses the standard `n!/(n-k)!`-scaled marginal
of an exchangeable labelled spectrum. A separate API for sums over
injective index selections is not used in its definition.

## Models and normalization

`gaussianMatrixLaw n a` is the product law of actual complex matrix
entries with density `(a/pi) exp(-a |z|²)`, for `a > 0`.
The general joint-law theorem allows every finite dimension and every
positive scale. Taking `a = n` for `n > 0` gives the variance-normalized
Ginibre matrix and the kernel

```text
K_n(z,w) = (n/pi) exp(-n(|z|²+|w|²)/2)
           * sum_{j<n} (n z conjugate(w))^j / j!.
```

The ordered selection is set to zero outside the simple-spectrum locus;
that exceptional set is proved Gaussian-null. Uniform relabelling changes
no characteristic root, as proved by
`charpoly_eq_prod_permuted_schurSpectrum`. A sorted vector is never
assigned the symmetric density on the whole product space.

Primary references are Bordenave–Chafai, *Around the circular law*,
[arXiv:1109.3343v4](https://arxiv.org/pdf/1109.3343v4), Section 3, and
HKPV, *Zeros of Gaussian Analytic Functions and Determinantal Point
Processes*, [Sections 6.3–6.4](https://math.iisc.ac.in/~manju/GAF_book.pdf).
The checked BC12 PDF contains inconsistent printed powers of `pi`;
we reconstruct normalized constants from proved Gaussian integrals.
See [SOURCE_NOTES.md](SOURCE_NOTES.md). No reference PDF was modified.

## Why the matrix-to-spectrum step is not an external input

The development proves ordered Schur existence by an eigenbasis and
Gram–Schmidt; constructs actual exponential charts by the inverse function
theorem; computes the full real Jacobian at every parameter; and proves
the exact coordinate product-volume decomposition.

A fixed reference Hermitian orbit supplies a countable angular cover.
Ordered Schur uniqueness proves that overlaps depend on the angle alone.
First-patch selection then produces measurable, disjoint full triangular
domains. Actual Euclidean changes of variables are summed over this cover,
the strict-upper Gaussian variables are integrated out, and probability
normalization determines the remaining angular coefficient. Finally,
the finite chamber partition supplies the factorial label multiplicity.

No Schur-law, angular-volume, measurable-root, Jacobian, Gaussian
correlation, van Handel, or BC12 theorem is taken as an external
mathematical hypothesis. Ordinary theorem premises such as positive
scale, measurability, triangularity, and unitarity remain explicit;
their required Gaussian/model instantiations are proved internally.

## Build, audit, and isolation

The manifest pins mathlib to
`db584cd6d46c92f209a44c0f1c829460d327499d`.

```sh
lake --no-cache build
lake env lean -j 1 Audit.lean
```

Local dependencies are a private APFS copy-on-write snapshot, not shared
writable build directories. No large cache was downloaded. Module builds
were run serially, followed by the root; `weakLeanArgs = ["-j", "1"]`
keeps each Lean process single-worker. No heartbeat, recursion-depth, or
similar checking limit was raised.

All authored mathematical modules are imported by `Ginibre.lean`.
`Audit.lean` audits every theorem and prints the major endpoint types and
the actual spectral-law definitions. The authored sources contain no
`sorry`, `admit`, `unsafe`, custom `axiom`, `native_decide`, or
proof-option overrides.

Execution records:
[build](audit/build-spectral-law.log),
[axioms](audit/axioms-spectral-law.log),
[source checksums](audit/sources-spectral-law.sha256).
Historical audit files are retained and are not the latest checkpoint.

This project neither imports nor writes to Section 3, its vendor tree,
the old random-band-matrix projects, or their downstream chapters.
It is published independently as
[ginibre-correlation-identities-lean](https://github.com/hanyi162013-Yihan/ginibre-correlation-identities-lean).
GitHub Actions performs the root build and checks complete all-theorem
audit coverage against the standard-axiom whitelist. CI logs are retained
as run artifacts; the checked-in logs below document the local checkpoint.
[REMAINING.md](REMAINING.md) records scope and non-goals.

## Mathematical source files

| File | Content |
| --- | --- |
| `Ginibre/Kernel.lean` | Explicit scaled kernel and empirical density |
| `Ginibre/RadialMoments.lean` | Radial moments and integer angular integrals |
| `Ginibre/PolarIntegration.lean` | Polar integration with integrability in both directions |
| `Ginibre/MonomialOrthogonality.lean` | Exact planar Gaussian monomial inner products |
| `Ginibre/FiniteProjection.lean` | Finite-family reproducing-kernel algebra |
| `Ginibre/GaussianBasis.lean` | Gaussian orthonormal basis and exact kernel identification |
| `Ginibre/Projection.lean` | Reproducing and weighted projection endpoints |
| `Ginibre/GaussianEntries.lean` | Gaussian entry law, probability, independence, and marginal laws |
| `Ginibre/MatrixDensity.lean` | Actual product-law density and its closed form |
| `Ginibre/SingletonSpectrum.lean` | End-to-end dimension-one spectral check |
| `Ginibre/SlaterDensity.lean` | Squared-determinant integrability and factorial normalization |
| `Ginibre/DeterminantalDensity.lean` | Normalized candidate density and Vandermonde formula |
| `Ginibre/BorderedDeterminant.lean` | Bordered Laplace expansion and cofactor contraction |
| `Ginibre/DeterminantMarginal.lean` | Integrable one-coordinate determinant recursion |
| `Ginibre/KernelDeterminants.lean` | Gram positivity, continuity, and explicit kernel recursion |
| `Ginibre/FiniteMarginals.lean` | Finite-product integrability and exact candidate marginals |
| `Ginibre/SchurJacobian.lean` | Ordered lower commutator matrix and complex determinant |
| `Ginibre/SchurRealJacobian.lean` | Real coordinate blocks and Vandermonde-square determinant |
| `Ginibre/SchurDifferential.lean` | Skew-Hermitian tangent completion and lower-block identification |
| `Ginibre/SchurCalculus.lean` | Real-parameter derivative of actual matrix conjugation |
| `Ginibre/SchurGaussian.lean` | Unitary energy invariance and actual entry-density substitution |
| `Ginibre/PolynomialZeroSets.lean` | Independent copy of the polynomial null-set proof |
| `Ginibre/SimpleSpectrum.lean` | Almost-sure simple spectrum from Gaussian matrix entries |
| `Ginibre/SchurRegularity.lean` | Almost-sure regularity of every Schur representation |
| `Ginibre/Eigenbasis.lean` | Constructing an eigenbasis from a separable characteristic polynomial |
| `Ginibre/GramSchmidtSchur.lean` | Orthogonalization and upper-triangular change of basis |
| `Ginibre/SchurExistence.lean` | Actual unitary Schur factors and Gaussian a.e. existence |
| `Ginibre/SchurTangent.lean` | Complete real tangent map and its continuous linear inverse |
| `Ginibre/ExpConjugation.lean` | Strict derivative of exponential conjugation in a Banach algebra |
| `Ginibre/SchurCoordinates.lean` | Actual exponential coordinates and the local inverse theorem |
| `Ginibre/SchurChartCoverage.lean` | Translated charts covering every simple-spectrum matrix |
| `Ginibre/SchurCountableAtlas.lean` | One fixed countable atlas covering a Gaussian full-measure set |
| `Ginibre/SchurSmooth.lean` | Smooth coordinates and the strict derivative of the inverse at the center |
| `Ginibre/BlockLinearDeterminant.lean` | Full block determinants and complex-to-real restriction |
| `Ginibre/SchurEntrySplit.lean` | Fixed linear lower/upper splitting of actual matrix entries |
| `Ginibre/SchurFullJacobian.lean` | Full actual coordinate Jacobian at triangular centers |
| `Ginibre/MovingConjugation.lean` | Moving-frame product rule and derivative of the inverse identity |
| `Ginibre/ExpAngularConjugation.lean` | Actual exponential moving-frame derivative at all parameters |
| `Ginibre/SchurMovingFrame.lean` | Vandermonde/angular factorization for the complete tangent map |
| `Ginibre/SchurAngularJacobian.lean` | Actual angular derivative, full moving Jacobian, normalization at zero |
| `Ginibre/MatrixConjugationDeterminant.lean` | Kronecker entry matrix and determinant-one output conjugation |
| `Ginibre/SchurJacobianEverywhere.lean` | Full genuine Jacobian in fixed coordinates at every parameter |
| `Ginibre/SchurLocalIntegration.lean` | Concrete coordinate volume and local change of variables with integrability |
| `Ginibre/SchurSylvester.lean` | Mixed triangular Sylvester determinant and intertwiner uniqueness |
| `Ginibre/SchurPhaseUniqueness.lean` | Ordered simple Schur factors differ only by diagonal unitary phases |
| `Ginibre/SchurProductEntries.lean` | Exact finite reordering of matrix-entry coordinates |
| `Ginibre/SchurProductVolume.lean` | Concrete angular/diagonal/strict-upper product volume |
| `Ginibre/SchurAuxiliaryGaussian.lean` | Strict-upper energy and its actual Gaussian integral |
| `Ginibre/SchurProductGaussian.lean` | Separation of actual Gaussian density times the full Jacobian |
| `Ginibre/SchurAngularPatch.lean` | One fixed angular patch valid for all ordered triangular factors |
| `Ginibre/SchurOrderedSpectrum.lean` | Borel lexicographic ordering and uniqueness of ordered diagonals |
| `Ginibre/SchurOrderedPatch.lean` | Injective charts with unrestricted ordered triangular variables |
| `Ginibre/SchurOrderedBasis.lean` | Construction of ordered orthonormal Schur bases |
| `Ginibre/SchurReferenceOrbit.lean` | Reference Hermitian orbit and an actual open angular neighborhood |
| `Ginibre/SchurAngularCoverage.lean` | One countable angular cover independent of the spectrum |
| `Ginibre/SchurExtendedCoverage.lean` | Extended charts cover every simple-spectrum matrix |
| `Ginibre/SchurExtendedIntegration.lean` | Actual Jacobian integration in all translated extended charts |
| `Ginibre/SchurJacobianRegularity.lean` | Continuity of the actual angular Jacobian and Gaussian weight |
| `Ginibre/GaussianCoordinateLaw.lean` | Actual iid Gaussian law in fixed linear entry coordinates |
| `Ginibre/SchurDensityNormalization.lean` | Matching the actual diagonal weight with the normalized candidate |
| `Ginibre/SchurAngularOverlap.lean` | Overlaps depend only on the angular coordinate |
| `Ginibre/SchurDisjointAtlas.lean` | Measurable first-patch selection and disjoint full coverage |
| `Ginibre/SchurGlobalChartIntegration.lean` | Global Gaussian integration over the disjoint actual charts |
| `Ginibre/SchurSpectrum.lean` | Actual characteristic-root selection on the simple locus |
| `Ginibre/SchurSpectrumMeasurability.lean` | Measurable spectral representatives glued from the actual atlas |
| `Ginibre/SchurSeparatedIntegration.lean` | Cartesian disjoint domains and justified product Tonelli |
| `Ginibre/SchurAngularIntegration.lean` | Integration of auxiliary and angular variables |
| `Ginibre/SchurSpectralLaw.lean` | Actual ordered Gaussian--Vandermonde spectral density |
| `Ginibre/SchurPermutations.lean` | Label invariance, collision vanishing, and volume-preserving permutations |
| `Ginibre/SchurChamberIntegration.lean` | Disjoint ordered chambers and the exact factorial multiplicity |
| `Ginibre/SchurChamberNormalization.lean` | Explicit actual spectral normalization and symmetric statistics |
| `Ginibre/SpectralLabelAveraging.lean` | Uniform label averaging and actual Gaussian spectral test integrals |
| `Ginibre/GaussianLabelledLaw.lean` | Actual exchangeable labelled law equals the determinant density |
| `Ginibre/ActualCorrelations.lean` | All finite correlation densities and the one-/two-point formulas |
| `Ginibre/MarginalCoordinates.lean` | Concrete volume-preserving coordinates for marginal Fubini |
| `Ginibre/ActualMarginals.lean` | Actual retained-label laws and factorial correlation measures |

Other authored files: `Ginibre.lean`, `Audit.lean`, `lean-toolchain`,
`lakefile.toml`, `lake-manifest.json`, `.gitignore`, this README,
`SOURCE_NOTES.md`, `REMAINING.md`, and the audit records.
Ignored `tmp/pdfs/` contains unchanged reference material; `.lake/`
contains only this project's dependency/build snapshot.

The polynomial null-set proof was independently copied from the user's
previous `ShortRingAnchor` development with source attribution. There is
no import or shared writable dependency on that project.
