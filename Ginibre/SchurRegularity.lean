import Ginibre.SchurDifferential
import Ginibre.SimpleSpectrum

/-!
# Connecting the Gaussian simple-spectrum event to Schur Jacobian regularity

HKPV (6.3.2)--(6.3.5). The distinct-diagonal premise in the determinant
calculation is discharged for every Schur representation of almost every
Gaussian matrix. This does not assert existence of global Schur coordinates,
fix their phase gauge, or prove a measure transformation.
-/

noncomputable section
open MeasureTheory
namespace Ginibre

/-- HKPV spectral bookkeeping: unitary conjugation preserves the characteristic polynomial. -/
theorem charpoly_unitary_conjugate {n : ℕ} (U S : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) :
    (U * S * U.conjTranspose).charpoly = S.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- HKPV simple-spectrum condition on an upper-triangular factor is
exactly pairwise distinctness of its diagonal entries. -/
theorem upper_charpoly_separable_iff {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) :
    S.charpoly.Separable ↔ Function.Injective (fun i => S i i) := by
  rw [Matrix.charpoly_of_isUpperTriangular S hS, Polynomial.separable_prod_X_sub_C_iff]

/-- HKPV (6.3.4): separability, not an additional quantitative spacing
assumption, suffices for a strictly positive real Jacobian block. -/
theorem det_real_schurLowerMatrix_pos_of_separable {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hsep : S.charpoly.Separable) :
    0 < Matrix.det (realifyMatrix (schurLowerMatrix S)) :=
  det_real_schurLowerMatrix_pos S hS ((upper_charpoly_separable_iff S hS).mp hsep)

/-- **HKPV regular Schur representations for the actual Gaussian law**:
almost surely, every upper-triangular unitary representation has the
nondegenerate Jacobian block proved above. No existence or global-chart
claim is hidden in this universal statement. -/
theorem gaussianMatrix_schur_regular_ae (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ A ∂gaussianMatrixLaw n a,
      ∀ U S : Matrix (Fin n) (Fin n) ℂ,
        U.conjTranspose * U = 1 → S.IsUpperTriangular →
        Matrix.of A.curry = U * S * U.conjTranspose →
        0 < Matrix.det (realifyMatrix (schurLowerMatrix S)) := by
  filter_upwards [gaussianMatrix_charpoly_separable_ae n ha] with A hA
  intro U S hU hS hrep
  apply det_real_schurLowerMatrix_pos_of_separable S hS
  rw [hrep, charpoly_unitary_conjugate U S hU] at hA
  exact hA

end Ginibre
