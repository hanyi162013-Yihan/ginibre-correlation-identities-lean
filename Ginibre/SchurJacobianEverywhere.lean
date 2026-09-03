import Ginibre.SchurAngularJacobian
import Ginibre.MatrixConjugationDeterminant
import Ginibre.SchurSmooth

/-!
# Full Jacobian of the genuine Schur coordinates at every parameter

HKPV (6.3.4)--(6.3.5). Unitary rotation of the output has real determinant
one. Consequently the moving-frame factorization is also the determinant
of the actual coordinate map, in the fixed entry splitting, throughout
its domain. This is a local differential result, not yet a global Schur
measure transformation or an eigenvalue-density theorem.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV two-sided output multiplication in the fixed split-entry coordinates. -/
def schurEntryConjugation {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    SchurTangent n →ₗ[ℝ] SchurTangent n :=
  (schurEntrySplit n).toLinearMap.comp
    (((matrixTwoSidedMul A B).restrictScalars ℝ).comp
      (schurEntrySplit n).symm.toLinearMap)

/-- HKPV inverse output frames have determinant one in these coordinates. -/
theorem det_schurEntryConjugation {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) : LinearMap.det (schurEntryConjugation A B) = 1 := by
  change LinearMap.det ((schurEntrySplit n).toLinearMap.comp
    (((matrixTwoSidedMul A B).restrictScalars ℝ).comp
      (schurEntrySplit n).symm.toLinearMap)) = 1
  rw [LinearMap.det_conj]
  exact det_matrixTwoSidedMul_real_of_inverse A B hAB

/-- HKPV differentiate the fixed entry splitting after the actual matrix map. -/
theorem fderiv_schurEntryCoordinates_apply {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (x v : SchurTangent n) :
    fderiv ℝ (schurEntryCoordinates S) x v =
      schurEntrySplit n (fderiv ℝ (schurExpCoordinates S) x v) := by
  have hf := ((contDiff_schurExpCoordinates 1 S).differentiable (by simp)) x
  have h : HasFDerivAt (schurEntryCoordinates S)
      ((schurEntrySplit n).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (schurExpCoordinates S) x)) x := by
    convert! (schurEntrySplit n).toContinuousLinearEquiv.hasFDerivAt.comp x hf.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- HKPV exact relation between the moving derivative and the derivative
in the fixed matrix-entry coordinates. -/
theorem schurRotatedDifferential_eq_output_comp {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (x : SchurTangent n) :
    schurRotatedDifferential S x =
      (schurEntryConjugation (schurUnitaryParam x).conjTranspose
        (schurUnitaryParam x)).comp (fderiv ℝ (schurEntryCoordinates S) x).toLinearMap := by
  apply LinearMap.ext
  intro v
  change schurEntrySplit n ((schurUnitaryParam x).conjTranspose *
    fderiv ℝ (schurExpCoordinates S) x v * schurUnitaryParam x) =
    schurEntrySplit n ((schurUnitaryParam x).conjTranspose *
      (schurEntrySplit n).symm (fderiv ℝ (schurEntryCoordinates S) x v) *
        schurUnitaryParam x)
  rw [fderiv_schurEntryCoordinates_apply, LinearEquiv.symm_apply_apply]

/-- HKPV rotation does not alter the complete real Jacobian determinant. -/
theorem det_schurRotatedDifferential_eq {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (x : SchurTangent n) :
    LinearMap.det (schurRotatedDifferential S x) =
      (fderiv ℝ (schurEntryCoordinates S) x).det := by
  rw [schurRotatedDifferential_eq_output_comp, LinearMap.det_comp,
    det_schurEntryConjugation _ _ (schurUnitaryParam_unitary x), one_mul]

/-- **HKPV (6.3.4)--(6.3.5), full actual Jacobian at every parameter**.
The angular factor is independent of the eigenvalues and of every upper
entry, and is normalized to one at the chart center by
`schurAngularJacobian_zero`. This asserts no global injectivity. -/
theorem det_fderiv_schurEntryCoordinates_everywhere {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) (x : SchurTangent n) :
    (fderiv ℝ (schurEntryCoordinates S) x).det =
      (∏ p : SchurLower n,
        ‖(S + x.2.val) (schurCol p) (schurCol p) -
          (S + x.2.val) (schurRow p) (schurRow p)‖ ^ 2) * schurAngularJacobian x.1 := by
  rw [← det_schurRotatedDifferential_eq]
  exact det_schurRotatedDifferential S hS x

/-- HKPV nonnegative Jacobian used by change of variables: the only
absolute value left is that of the angular-coordinate factor. -/
theorem abs_det_fderiv_schurEntryCoordinates {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) (x : SchurTangent n) :
    |(fderiv ℝ (schurEntryCoordinates S) x).det| =
      (∏ p : SchurLower n,
        ‖(S + x.2.val) (schurCol p) (schurCol p) -
          (S + x.2.val) (schurRow p) (schurRow p)‖ ^ 2) * |schurAngularJacobian x.1| := by
  rw [det_fderiv_schurEntryCoordinates_everywhere S hS x, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg fun p _ => sq_nonneg _)]

end Ginibre
