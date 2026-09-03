import Ginibre.SchurMovingFrame
import Ginibre.ExpAngularConjugation

/-!
# The full Jacobian factorization for the actual exponential Schur map

HKPV (6.3.2)--(6.3.5). At any angular parameter, rotate the genuine
Frechet derivative back by the constructed unitary matrix. Its complete
determinant factors into the Vandermonde square and a function of the
angular parameter alone. There is no assumed angular derivative or
Jacobian interface. Removing the output rotation and global integration
are separate steps.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV angular embedding without the independent triangular variables. -/
def schurAngularCLM (n : ℕ) : (SchurLower n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (schurSkewTangentCLM n).comp (ContinuousLinearMap.inl ℝ _ _)

/-- HKPV triangular coordinate inclusion, separated from angular parameters. -/
def schurUpperCLM (n : ℕ) : schurUpperSubmodule n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (schurUpperTangentCLM n).comp (ContinuousLinearMap.inr ℝ _ _)

/-- HKPV the actual Maurer--Cartan angular derivative `U⁻¹ dU`. -/
def schurAngularFrame {n : ℕ} (w : SchurLower n → ℂ) :
    (SchurLower n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun v := NormedSpace.exp (-schurAngularCLM n w) *
    fderiv ℝ (fun u => NormedSpace.exp (schurAngularCLM n u)) w v
  map_add' v u := by rw [map_add, Matrix.mul_add]
  map_smul' r v := by rw [map_smul, Matrix.mul_smul]; rfl

/-- HKPV angular Jacobian, defined from the actual angular exponential.
In particular it has no triangular matrix or eigenvalue argument. -/
def schurAngularJacobian {n : ℕ} (w : SchurLower n → ℂ) : ℝ :=
  LinearMap.det (schurLowerEntries.comp (schurAngularFrame w))

/-- **HKPV (6.3.2) for the actual matrix map at every parameter**.
Every differentiability and inverse-frame obligation has been proved. -/
theorem fderiv_schurExpCoordinates_rotated {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (x v : SchurTangent n) :
    (schurUnitaryParam x).conjTranspose *
      fderiv ℝ (schurExpCoordinates S) x v * schurUnitaryParam x =
      schurMovingTangentMap (S + x.2.val) (schurAngularFrame x.1) v := by
  rw [schurUnitaryParam_adjoint]
  convert! fderiv_exp_angular_conjugation_rotated S
    (schurAngularCLM n) (schurUpperCLM n) x v using 1

/-- HKPV actual full Frechet derivative, written in the moving output
frame and then in the fixed split-entry coordinates. -/
def schurRotatedDifferential {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (x : SchurTangent n) : SchurTangent n →ₗ[ℝ] SchurTangent n :=
  (schurEntrySplit n).toLinearMap.comp ({
    toFun v := (schurUnitaryParam x).conjTranspose *
      fderiv ℝ (schurExpCoordinates S) x v * schurUnitaryParam x
    map_add' v u := by rw [map_add, Matrix.mul_add, Matrix.add_mul]
    map_smul' r v := by rw [map_smul, Matrix.mul_smul, Matrix.smul_mul]; rfl } :
      SchurTangent n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)

/-- HKPV the moving-frame algebraic map equals the genuine derivative,
not just a matrix with a matching determinant. -/
theorem schurRotatedDifferential_eq {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (x : SchurTangent n) :
    schurRotatedDifferential S x = (schurEntrySplit n).toLinearMap.comp
      (schurMovingTangentMap (S + x.2.val) (schurAngularFrame x.1)) := by
  apply LinearMap.ext
  intro v
  exact congrArg (schurEntrySplit n) (fderiv_schurExpCoordinates_rotated S x v)

/-- **HKPV full actual Jacobian in the moving frame, at all parameters**.
The eigenvalue dependence is exactly Vandermonde squared. The independent
angular factor is explicitly defined from a proved differentiable map. -/
theorem det_schurRotatedDifferential {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) (x : SchurTangent n) :
    LinearMap.det (schurRotatedDifferential S x) =
      (∏ p : SchurLower n,
        ‖(S + x.2.val) (schurCol p) (schurCol p) -
          (S + x.2.val) (schurRow p) (schurRow p)‖ ^ 2) * schurAngularJacobian x.1 := by
  rw [schurRotatedDifferential_eq]
  exact det_schurMovingTangentMap _ (hS.add x.2.property) _

/-- HKPV at zero the actual angular frame is the original skew completion. -/
theorem schurAngularFrame_zero {n : ℕ} (v : SchurLower n → ℂ) :
    schurAngularFrame (0 : SchurLower n → ℂ) v = schurSkewEmbed v := by
  change NormedSpace.exp (-schurAngularCLM n 0) *
    fderiv ℝ (fun u => NormedSpace.exp (schurAngularCLM n u)) 0 v = _
  have he : HasFDerivAt (fun u => NormedSpace.exp (schurAngularCLM n u))
      (schurAngularCLM n) 0 := by
    convert! (hasStrictFDerivAt_exp_linear (schurAngularCLM n)).hasFDerivAt
  rw [he.fderiv]
  simp only [map_zero, neg_zero, NormedSpace.exp_zero, one_mul]
  rfl

/-- HKPV normalization of the independent angular factor at the chart center. -/
theorem schurAngularJacobian_zero (n : ℕ) :
    schurAngularJacobian (0 : SchurLower n → ℂ) = 1 := by
  have he : schurLowerEntries.comp (schurAngularFrame (0 : SchurLower n → ℂ)) =
      (LinearMap.id : (SchurLower n → ℂ) →ₗ[ℝ] (SchurLower n → ℂ)) := by
    apply LinearMap.ext
    intro v
    funext p
    exact (congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A (schurRow p) (schurCol p))
      (schurAngularFrame_zero v)).trans (schurSkewEmbed_apply_lower v p)
  change LinearMap.det _ = 1
  rw [he, LinearMap.det_id]

end Ginibre
