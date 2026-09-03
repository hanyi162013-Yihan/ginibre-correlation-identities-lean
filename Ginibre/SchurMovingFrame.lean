import Ginibre.SchurFullJacobian

/-!
# The Schur determinant in an arbitrary angular frame

HKPV (6.3.2)--(6.3.5). The lower commutator only sees the lower entries of
the angular variation. This separates the Vandermonde square from the
angular coordinate determinant; no skew-adjointness assumption is needed
for this algebraic step. The actual exponential frame is instantiated
separately in `SchurAngularJacobian`.
-/

noncomputable section
open scoped Matrix
namespace Ginibre

/-- HKPV the lower commutator is unaffected by the upper part of any
matrix variation, not just by a skew-Hermitian completion. -/
theorem schurLowerEntries_commutator {n : ℕ}
    (S K : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) :
    schurLowerEntries (K * S - S * K) =
      schurLowerMatrix S *ᵥ schurLowerEntries K := by
  funext p
  rw [schurLowerMatrix_mulVec]
  have hz := upper_commutator_lower_zero
    (K - schurLowerEmbed (schurLowerEntries K)) S (schur_upper_residual K) hS p
  change (K * S - S * K) (schurRow p) (schurCol p) = _
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply] at *
  linear_combination hz

/-- HKPV the complete tangent map in a moving angular frame. -/
def schurMovingTangentMap {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (K : (SchurLower n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    SchurTangent n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun x := x.2.val + (K x.1 * S - S * K x.1)
  map_add' x y := by
    change (x.2.val + y.2.val) + (K (x.1 + y.1) * S - S * K (x.1 + y.1)) = _
    rw [map_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' r x := by
    change r • x.2.val + (K (r • x.1) * S - S * K (r • x.1)) = _
    rw [map_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub]
    rfl

/-- HKPV the upper translation block remains the identity in every
angular frame. -/
theorem schurMovingTangentMap_upper {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (K : (SchurLower n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (D : schurUpperSubmodule n) : schurMovingTangentMap S K (0, D) = D.val := by
  change D.val + (K 0 * S - S * K 0) = D.val
  rw [map_zero, Matrix.zero_mul, Matrix.mul_zero, sub_self, add_zero]

/-- HKPV **complete moving-frame determinant factorization**. The
Vandermonde factor depends only on the triangular diagonal; the second
factor depends only on the angular frame, even if that frame is singular. -/
theorem det_schurMovingTangentMap {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular)
    (K : (SchurLower n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((schurEntrySplit n).toLinearMap.comp (schurMovingTangentMap S K)) =
      (∏ p : SchurLower n,
        ‖S (schurCol p) (schurCol p) - S (schurRow p) (schurRow p)‖ ^ 2) *
      LinearMap.det (schurLowerEntries.comp K) := by
  have hd : LinearMap.det
      ((schurEntrySplit n).toLinearMap.comp (schurMovingTangentMap S K)) =
      LinearMap.det (((Matrix.toLin' (schurLowerMatrix S)).restrictScalars ℝ).comp
        (schurLowerEntries.comp K)) := by
    apply det_block_lower_identity
    · intro x
      change schurLowerEntries (x.2.val + (K x.1 * S - S * K x.1)) = _
      rw [map_add, schurLowerEntries_upper, zero_add, schurLowerEntries_commutator S _ hS]
      rfl
    · intro D
      change schurUpperEntries (schurMovingTangentMap S K (0, D)) = D
      rw [schurMovingTangentMap_upper, schurUpperEntries_upper]
  rw [hd, LinearMap.det_comp, det_complex_matrix_restrictScalars,
    norm_sq_det_schurLowerMatrix S hS]

end Ginibre
