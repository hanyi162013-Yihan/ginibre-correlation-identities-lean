# Actual Ginibre statistics: verification record

Status: **complete; full cloud build and all-theorem axiom audit passed**
on 2026-09-03 in
[run 33791975299](https://github.com/hanyi162013-Yihan/ginibre-correlation-identities-lean/actions/runs/33791975299),
proof-source commit `5ec13794cbfcc3402805ff4b639332ce975af02f`.
The prior 76-module / 463-theorem core passed independent GitHub
verification in [run 33789493694](https://github.com/hanyi162013-Yihan/ginibre-correlation-identities-lean/actions/runs/33789493694).

## Executed checks

- `lake --no-cache build`: exit 0, 3136 jobs, root `Ginibre` built.
  The build step ran from 18:43:17 to 18:45:07 UTC (110 seconds).
- `lake --no-cache env lean -j 1 Audit.lean`: exit 0; the complete audit
  step, including the result checker, took four seconds.
- 525 distinct authored theorem declarations and 525 corresponding
  axiom outputs; every output uses only a subset of
  `{propext, Classical.choice, Quot.sound}`.
- `scripts/check_audit.py` passed on the downloaded cloud audit log as
  well as in the cloud run itself.
- All 83 authored mathematical modules belong to the root import closure.
- All 88 source/configuration checksums in `sources-statistics.sha256`
  passed local verification; documentation-only completion changes do
  not alter those source files.
- Lean 4.33.0; mathlib commit
  `db584cd6d46c92f209a44c0f1c829460d327499d`. The local mathlib source
  checkout remains clean, and the cloud build uses independent dependencies.
- No forbidden authored proof construct or checking-limit override.

Evidence: [cloud build](statistics-ci/build.log),
[all-theorem axiom log](statistics-ci/axioms.log),
[source hashes](sources-statistics.sha256).

## Scope of the extension

Seven new modules add 62 theorems (83 mathematical modules and 525
theorems in total). The extension derives all statements from the actual
iid Gaussian entry law and the already proved spectral pushforward.

- Signed spectral integrals and genuine L1 transport.
- The Campbell formula for the sum over all injective label selections.
- Actual linear-statistic expectations and mixed second moments.
- L2-to-L1 domination for every one-point, two-point, and kernel-weight
  integral used in the moment calculation.
- Actual covariance and the symmetric variance energy identity.
- The explicit bound `0 <= Var L_f <= 2 * integral f² I_n`.
- Empty and rank-one cases, making the final APIs valid in every finite
  dimension.

Here `I_n = n rho_n` is the one-point intensity. Real measurable tests
may be unbounded; the second-order theorems require square-integrability
against `I_n`. These are test-function premises, not a Gaussian-spectrum,
Schur-law, correlation-function, or moment identity assumed externally.

The covariance is defined from expectations on the actual Gaussian
matrix-entry probability space. Its moment calculation proves the
required integrability, so the total Bochner integral convention cannot
conceal a missing second-moment premise. Rank one uses the one-point law
and a proved rank-one kernel identity, never a two-label marginal.

## Audit policy

`scripts/check_audit.py` checks all authored mathematical modules are
in the root import closure and all theorem declarations are covered
exactly once by `Audit.lean`. It rejects proof shortcuts and option
overrides. For a completed audit log it also rejects missing, duplicate,
or unexpected outputs and any axiom outside
`{propext, Classical.choice, Quot.sound}`.

No heartbeat or recursion-depth limit is raised. Difficult elaboration
steps are rewritten into explicit typed equalities or simpler proofs.
The final verification is performed on GitHub-hosted Linux, with the
pinned Lean/mathlib versions and no uploaded local `.lake` directory.

This record covers the finite Ginibre density/correlation/statistics
development. It does not claim all BC12 asymptotic circular-law or
least-singular-value estimates, and it makes no change to Section 3,
the vendor tree, downstream projects, or the original manuscripts.
