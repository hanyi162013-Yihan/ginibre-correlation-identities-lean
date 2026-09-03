# Full-Jacobian and local-integration checkpoint — 2026-09-03

- `lake --no-cache build`: exit 0, 3095 jobs, root target built.
- `lake env lean -j 1 Audit.lean`: exit 0, all 230 theorem audits printed.
- Authored theorem declarations and audit entries: 230 each; no omissions,
  duplicates, or extra entries. The output contains 230 distinct audited names.
- All audited dependencies are contained in `{propext, Classical.choice,
  Quot.sound}`. No external mathematical axiom, admitted proof, or native
  evaluation oracle occurs in these theorem dependencies.
- Authored mathematical source scan: no `sorry`, `admit`, `unsafe`, custom
  `axiom`, `native_decide`, or `set_option` declarations. No heartbeat,
  recursion-depth, or similar checking limit was increased.
- All 48 source/configuration checksums in `sources-schur-jacobian.sha256`
  passed `shasum -a256 -c`.
- The pinned mathlib source checkout remained clean. No old Section 3,
  `ShortRingAnchor`, or `Vendor` import was added. No cache was downloaded.
- Builds were run one module target at a time, then the root. The only
  root-build warnings are replayed style warnings in older modules.

There are 43 authored mathematical modules: 10 new modules and 43 new
theorems since the 187-theorem Schur-atlas checkpoint. Their complete file
list is in `../README.md`.

## What this checkpoint establishes

The full Frechet determinant of the actual exponential Schur map, written
in fixed split-entry coordinates, equals the diagonal Vandermonde square
times an angular factor at **every parameter**. The angular factor is
defined from the actual exponential derivative, is independent of all
triangular variables, and equals one at zero. Output unitary conjugation
has proved real determinant one, via its complete Kronecker entry matrix.

The local integration theorem uses a concrete volume: ordinary complex
matrix-entry Lebesgue measure transported through a fixed linear entry
equivalence. On every measurable piece of the actual injective chart it
proves nonnegative change of variables, real change of variables, and the
absolute-integrability equivalence. No derivative, Jacobian, injectivity,
or spectral-distribution interface is supplied as a mathematical input.
The ordinary premises are triangularity, distinct center diagonal entries,
measurability of the set, and inclusion in the constructed chart source.

The audit also prints the definitions of the coordinate volume and the
angular frame/factor, and the full types of the major boundary theorems.

## What it does not establish

This is not the global Gaussian Schur integration formula. Coordinate
product-volume decomposition, angular chart transitions/overlaps,
diagonal phase and permutation accounting, and auxiliary integration
remain. Consequently the general-dimensional actual Gaussian spectral
law and the resulting actual eigenvalue correlations are still unfinished.
The candidate density and its already-verified marginals are not used as
a definition or an assumption of the actual spectral law. See
`../REMAINING.md` for the next route.
