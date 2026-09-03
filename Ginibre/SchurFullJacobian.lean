import Ginibre.BlockLinearDeterminant
import Ginibre.SchurEntrySplit
import Ginibre.SchurCoordinates

/-!
# The full Jacobian of the actual Schur map at a triangular center

HKPV (6.3.2)--(6.3.5). The fixed entry split identifies input and output
with the same real vector space. The determinant below is therefore the
determinant of the genuine full derivative of the actual exponential
coordinate map, not a determinant of an unrelated bordered matrix.

This supplies the center Jacobian. The angular Jacobian at nonzero angular
parameters and the global integration/overlap accounting remain separate.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV upper variables act by ordinary translation when the angular
variation is zero. No triangularity of the center is needed here. -/
theorem schurTangentMap_upper {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (D : schurUpperSubmodule n) : schurTangentMap S (0, D) = D.val := by
  have hz : schurSkewEmbed (0 : SchurLower n → ℂ) = 0 := by
    simp [schurSkewEmbed, schurLowerEmbed]
  change D.val + (schurSkewEmbed 0 * S - S * schurSkewEmbed 0) = D.val
  rw [hz, Matrix.zero_mul, Matrix.mul_zero, sub_self, add_zero]

/-- HKPV the complete commutator differential in the fixed split-entry coordinates. -/
def schurCoordinateDifferential {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) :
    SchurTangent n →ₗ[ℝ] SchurTangent n :=
  (schurEntrySplit n).toLinearMap.comp (schurTangentMap S)

/-- **HKPV full real determinant**, including every upper and lower coordinate. -/
theorem det_schurCoordinateDifferential {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) :
    LinearMap.det (schurCoordinateDifferential S) =
      ∏ p : SchurLower n,
        ‖S (schurCol p) (schurCol p) - S (schurRow p) (schurRow p)‖ ^ 2 := by
  have hd : LinearMap.det (schurCoordinateDifferential S) =
      LinearMap.det ((Matrix.toLin' (schurLowerMatrix S)).restrictScalars ℝ) := by
    apply det_block_lower_identity
    · intro x
      funext p
      exact schurTangentMap_lower S hS x p
    · intro D
      change schurUpperEntries (schurTangentMap S (0, D)) = D
      rw [schurTangentMap_upper, schurUpperEntries_upper]
  rw [hd, det_complex_matrix_restrictScalars]
  exact norm_sq_det_schurLowerMatrix S hS

/-- HKPV actual exponential coordinates with output written in the fixed
entry split. This is not a linearized or replacement coordinate map. -/
def schurEntryCoordinates {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (x : SchurTangent n) : SchurTangent n :=
  schurEntrySplit n (schurExpCoordinates S x)

/-- HKPV the derivative of the actual map is precisely the full
endomorphism whose determinant was computed above. -/
theorem hasStrictFDerivAt_schurEntryCoordinates {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (schurEntryCoordinates S)
      (schurCoordinateDifferential S).toContinuousLinearMap 0 := by
  convert! ((schurEntrySplit n).toContinuousLinearEquiv.hasStrictFDerivAt.comp 0
    (hasStrictFDerivAt_schurExpCoordinates S)) using 1

/-- **HKPV (6.3.4)--(6.3.5), actual full Frechet Jacobian at the center**.
No arbitrary lower-left block or unproved Jacobian interface remains. -/
theorem det_fderiv_schurEntryCoordinates {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) :
    (fderiv ℝ (schurEntryCoordinates S) 0).det =
      ∏ p : SchurLower n,
        ‖S (schurCol p) (schurCol p) - S (schurRow p) (schurRow p)‖ ^ 2 := by
  rw [(hasStrictFDerivAt_schurEntryCoordinates S).hasFDerivAt.fderiv]
  exact det_schurCoordinateDifferential S hS

/-- HKPV positivity of the actual full Jacobian on the simple-diagonal locus. -/
theorem det_fderiv_schurEntryCoordinates_pos {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i)) :
    0 < (fderiv ℝ (schurEntryCoordinates S) 0).det := by
  rw [det_fderiv_schurEntryCoordinates S hS, ← det_real_schurLowerMatrix S hS]
  exact det_real_schurLowerMatrix_pos S hS hz

end Ginibre
