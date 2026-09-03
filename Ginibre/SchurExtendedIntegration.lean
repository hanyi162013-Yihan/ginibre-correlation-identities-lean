import Ginibre.SchurExtendedCoverage
import Ginibre.SchurProductGaussian

/-!
# Actual change of variables in every fixed extended Schur frame

HKPV (6.3.4)--(6.3.5) and Section 6.4. Unitary output translation
contributes determinant one, and preserves the actual Gaussian entry
density. Thus all members of the spectrum-independent countable atlas
use exactly the same separated Gaussian-Jacobian weight.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV translated actual matrix map in fixed real entry coordinates. -/
def schurExtendedEntryAt {n : ℕ} (U : SchurUnitaryFrame n) (x : SchurTangent n) :
    SchurTangent n := schurEntrySplit n (schurExtendedAt U x)

/-- HKPV output translation is the previously constructed genuine linear map. -/
theorem schurExtendedEntryAt_eq_comp {n : ℕ} (U : SchurUnitaryFrame n) (x : SchurTangent n) :
    schurExtendedEntryAt U x =
      schurEntryConjugation U.val U.val.conjTranspose (schurEntryCoordinates 0 x) := by
  change schurEntrySplit n (U.val * schurExpCoordinates 0 x * U.val.conjTranspose) =
    schurEntrySplit n (U.val * (schurEntrySplit n).symm
      (schurEntrySplit n (schurExpCoordinates 0 x)) * U.val.conjTranspose)
  rw [LinearEquiv.symm_apply_apply]

/-- HKPV the translated map has the actual composed Frechet derivative. -/
theorem hasFDerivAt_schurExtendedEntryAt {n : ℕ} (U : SchurUnitaryFrame n) (x : SchurTangent n) :
    HasFDerivAt (schurExtendedEntryAt U)
      ((schurEntryConjugation U.val U.val.conjTranspose).toContinuousLinearMap.comp
        (fderiv ℝ (schurEntryCoordinates 0) x)) x := by
  have he : schurExtendedEntryAt U = fun y =>
      schurEntryConjugation U.val U.val.conjTranspose (schurEntryCoordinates 0 y) :=
    funext (schurExtendedEntryAt_eq_comp U)
  rw [he]
  exact (schurEntryConjugation U.val U.val.conjTranspose).toContinuousLinearMap.hasFDerivAt.comp
    x (differentiable_schurEntryCoordinates 0 x).hasFDerivAt

/-- HKPV all fixed output frames have the identical computed absolute Jacobian. -/
theorem abs_det_fderiv_schurExtendedEntryAt {n : ℕ}
    (U : SchurUnitaryFrame n) (x : SchurTangent n) :
    |(fderiv ℝ (schurExtendedEntryAt U) x).det| = schurJacobianWeight 0 x := by
  rw [(hasFDerivAt_schurExtendedEntryAt U x).fderiv]
  change |LinearMap.det ((schurEntryConjugation U.val U.val.conjTranspose).comp
    (fderiv ℝ (schurEntryCoordinates 0) x).toLinearMap)| = _
  rw [LinearMap.det_comp, det_schurEntryConjugation _ _ (mul_eq_one_comm.mp U.property), one_mul]
  exact (schurJacobianWeight_eq_abs_det 0 Matrix.blockTriangular_zero x).symm

/-- HKPV translated fixed-entry coordinates are injective on the whole ordered patch. -/
theorem schurExtendedEntryAt_injOn {n : ℕ} (U : SchurUnitaryFrame n)
    (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀) :
    Set.InjOn (schurExtendedEntryAt U) (schurOrderedDomain z₀ hz₀) := by
  intro x hx y hy he
  exact schurExtendedAt_injOn U z₀ hz₀ hx hy ((schurEntrySplit n).injective he)

/-- HKPV images of measurable pieces of an extended patch are genuinely measurable. -/
theorem measurableSet_schurExtendedEntryAt_image {n : ℕ}
    (U : SchurUnitaryFrame n) (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀)
    (s : Set (SchurTangent n)) (hs : MeasurableSet s)
    (hsub : s ⊆ schurOrderedDomain z₀ hz₀) :
    MeasurableSet (schurExtendedEntryAt U '' s) :=
  measurable_image_of_fderivWithin hs
    (fun x _ => (hasFDerivAt_schurExtendedEntryAt U x).hasFDerivWithinAt)
    ((schurExtendedEntryAt_injOn U z₀ hz₀).mono hsub)

/-- **HKPV actual nonnegative integration in every translated extended
patch**, with the same proved Jacobian independent of the chosen frame. -/
theorem lintegral_schurExtendedEntryAt_image {n : ℕ}
    (U : SchurUnitaryFrame n) (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀)
    (s : Set (SchurTangent n)) (hs : MeasurableSet s)
    (hsub : s ⊆ schurOrderedDomain z₀ hz₀) (g : SchurTangent n → ℝ≥0∞) :
    ∫⁻ y in schurExtendedEntryAt U '' s, g y ∂schurCoordinateVolume n =
      ∫⁻ x in s, ENNReal.ofReal (schurJacobianWeight 0 x) *
        g (schurExtendedEntryAt U x) ∂schurCoordinateVolume n := by
  let : Measure.IsAddHaarMeasure (schurCoordinateVolume n) :=
    schurCoordinateVolume_isAddHaarMeasure n
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (schurCoordinateVolume n) hs
    (fun x _ => (hasFDerivAt_schurExtendedEntryAt U x).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    ((schurExtendedEntryAt_injOn U z₀ hz₀).mono hsub) g
  simpa only [abs_det_fderiv_schurExtendedEntryAt] using h

/-- HKPV the actual iid entry density is unchanged under unitary
conjugation; this is an energy identity, not a spectral-law premise. -/
theorem gaussianMatrixDensity_unitary_conjugate {n : ℕ} (a : ℝ)
    (U A : Matrix (Fin n) (Fin n) ℂ) (hU : U.conjTranspose * U = 1) :
    gaussianMatrixDensity n a (fun ij => (U * A * U.conjTranspose) ij.1 ij.2) =
      gaussianMatrixDensity n a (fun ij => A ij.1 ij.2) := by
  simp only [gaussianMatrixDensity_closedForm, Fintype.sum_prod_type]
  change (a / Real.pi) ^ (n * n) * Real.exp (-a * matrixEnergy (U * A * U.conjTranspose)) =
    (a / Real.pi) ^ (n * n) * Real.exp (-a * matrixEnergy A)
  rw [matrixEnergy_unitary_conjugate U A hU]

/-- HKPV all translated extended patches have the same actual Gaussian factor. -/
theorem gaussianMatrixDensity_schurExtendedAt {n : ℕ} (a : ℝ)
    (U : SchurUnitaryFrame n) (x : SchurTangent n) :
    gaussianMatrixDensity n a (fun ij => schurExtendedAt U x ij.1 ij.2) =
      gaussianMatrixDensity n a (fun ij => schurExpCoordinates 0 x ij.1 ij.2) :=
  gaussianMatrixDensity_unitary_conjugate a U.val _ U.property

end Ginibre
