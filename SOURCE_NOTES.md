# Source and normalization audit

Read: Bordenave--Chafai, *Around the circular law*, arXiv:1109.3343v4,
the PDF served on 2026-09-03 (65 pages, compiled November 27, 2024).
The relevant printed pages 10--11 were rendered and visually checked.
The original PDF is unchanged.

The displayed constants in this PDF are internally inconsistent:

- Theorem 3.2 prints `pi^(-n^2)` in the eigenvalue joint density. The
  normalized density relative to planar Lebesgue measure uses `pi^(-n)`.
- Theorem 3.3 includes an additional `pi^(-k^2)` although each `gamma(z)`
  is already defined to be `exp(-|z|^2)/pi`. At `n=k=1`, this would give
  `exp(-|z|^2)/pi^2`; the one-point formula in Theorem 3.4 instead gives
  the correctly normalized `exp(-|z|^2)/pi`.
- Consequently we reconstruct the constants from integrals rather than
  claiming a proof of these literal printed expressions.

For unscaled eigenvalues the intended symmetric density is

```
exp(-sum |z_i|^2) * product_{i<j} |z_i-z_j|^2
  / (pi^n * product_{j=1}^n j!).
```

For eigenvalues divided by `sqrt n` we use the kernel

```
K_n(z,w) = (n/pi) exp(-n(|z|^2+|w|^2)/2)
           * sum_{k<n} (n z conjugate(w))^k / k!.
```

There are two distinct normalization conventions for correlations:
the marginal of the symmetric probability density is
`(n-k)!/n! * det K`, whereas the factorial point-process correlation
is `det K`. These statements are kept separate in the proved actual-law endpoints.

Theorem 3.2 is the Gaussian-matrix-to-spectrum distribution step. A proof
of projection or of marginal integration of `det K` does not prove that
step. Here that separate step is proved through actual Schur coordinates;
no assumed spectral law is presented as a theorem from entries.

## Schur-coordinate reference

Hough--Krishnapur--Peres--Virag, *Zeros of Gaussian Analytic Functions
and Determinantal Point Processes*,
[Sections 6.3--6.4](https://math.iisc.ac.in/~manju/GAF_book.pdf),
printed pp. 103--106. The relevant text and formulas were checked; this
reference PDF is not modified. In particular, formulas (6.3.2)--(6.3.5)
give the differential calculation used in the Schur modules.

For upper-triangular `S` and a skew-Hermitian tangent matrix `Omega`,
the lower part of the differential of unitary conjugation is
`Omega*S - S*Omega`. Order lower coordinates by decreasing row, then
increasing column. The coefficient matrix is triangular with diagonal
`S_jj-S_ii`. Replacing each complex coefficient by its real 2-by-2
matrix gives determinant `product_{i>j} |S_jj-S_ii|^2`.

The formalization checks the coordinate basis, restores the dependent
upper entries of `Omega`, and differentiates the actual conjugation map.
It also constructs an eigenbasis and an orthonormal Schur representation
on the simple-spectrum locus. The actual local parametrization uses
`exp(Omega)`, with zero diagonal in `Omega`; its strict Frechet derivative
is proved in all independent real coordinates. Inverting the complete
commutator differential gives a genuine local chart by the inverse
function theorem. These are a reconstruction of the local-coordinate
argument, not a literal translation of the book's infinitesimal notation.

The complete actual Jacobian is reconstructed using a fixed split of
matrix entries into lower and upper coordinates. At a general angular
parameter, differentiation of `U^{-1} U = 1` gives the moving-frame
differential `dS + [U^{-1} dU, S]`. The lower commutator only sees the
lower entries of `U^{-1} dU`, so the full block determinant is
`Vandermonde(diag S)^2 * angularJacobian(omega)`. The angular factor is
defined from the derivative of the actual exponential, has no triangular
matrix argument, and equals one at zero. Two-sided matrix multiplication
has entry matrix `A tensor transpose(B)`; its determinant proves that
unitary output rotation contributes exactly one over the real scalars.

The local integration result uses ordinary complex matrix-entry Lebesgue
measure transported through the fixed linear entry split. It is not a
definition of spectral measure. Both the nonnegative change of variables
and absolute-integrability equivalence are checked on measurable pieces
of the actual injective chart. The subsequent global argument discharges the additional obligations,
rather than renaming this local formula a global theorem:

- Mixed triangular Sylvester equations prove that ordered simple Schur
  factors are unique up to diagonal unitary phases.
- A fixed reference Hermitian orbit supplies a countable angular cover;
  the ordered-Schur overlap criterion is independent of the eigenvalues
  and the strictly upper-triangular variables.
- First-patch selection yields measurable pairwise disjoint domains with
  unrestricted ordered triangular variables, covering a Gaussian
  full-measure set.
- The fixed coordinate volume is proved to be the angular/diagonal/
  strict-upper product volume. Actual changes of variables are summed,
  and the strict-upper Gaussian variables are integrated out.
- The remaining coefficient is a sum of actual angular integrals.
  Probability normalization determines it only after the genuine
  matrix-to-spectrum proportionality theorem is proved.
- The permutation chambers give the exact factorial multiplicity.
  Uniformly permuting the actual ordered characteristic roots yields the
  symmetric joint density; the proof also establishes exchangeability.
- A concrete volume-preserving retained/prefix split and product Fubini
  transport the determinant marginal integrals to actual spectral
  marginal measures, with the factorial correlation normalization stated
  separately.

Thus no spectral law has been inferred from candidate-density
normalization alone, and no global Schur formula remains an input.
The final checked endpoints and current audit are listed in
[README.md](README.md).

The repeated-root exclusion is approached using the resultant of the
universal characteristic polynomial and its derivative. Nonzero
multivariate polynomials have null zero sets; the proof in
`PolynomialZeroSets.lean` is independently copied from the user's
previously verified `ShortRingAnchor/PolynomialZeroSets.lean`, with
namespace and documentation adapted. There is no import or writable
dependency on that project.
