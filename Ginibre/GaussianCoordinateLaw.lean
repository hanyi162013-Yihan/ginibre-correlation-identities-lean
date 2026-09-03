import Ginibre.SchurProductGaussian

/-!
# The actual Gaussian matrix law in fixed entry coordinates

HKPV Section 6.4, probabilistic input to the Schur integration argument.
This is only the fixed linear split of the original iid matrix entries,
not a spectral distribution or a nonlinear Schur pushforward. Its law,
density, and integral conversion are proved directly from the constructed
independent-entry probability measure.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV the actual entry-product density is continuous. -/
theorem continuous_gaussianMatrixDensity (n : ℕ) (a : ℝ) :
    Continuous (gaussianMatrixDensity n a) := by
  unfold gaussianMatrixDensity complexGaussianDensity
  fun_prop

/-- HKPV actual Gaussian matrices, transported only by the fixed linear entry split. -/
def gaussianCoordinateLaw (n : ℕ) (a : ℝ) : Measure (SchurTangent n) :=
  (gaussianMatrixLaw n a).map (schurFlatEntryMeasurableEquiv n)

/-- HKPV density of the same matrix in fixed coordinates, not an eigenvalue density. -/
def gaussianCoordinateDensity (n : ℕ) (a : ℝ) (x : SchurTangent n) : ℝ :=
  gaussianMatrixDensity n a ((schurFlatEntryMeasurableEquiv n).symm x)

/-- HKPV the fixed-coordinate density is measurable by an actual measurable equivalence. -/
theorem measurable_gaussianCoordinateDensity (n : ℕ) (a : ℝ) :
    Measurable (gaussianCoordinateDensity n a) :=
  (continuous_gaussianMatrixDensity n a).measurable.comp
    (schurFlatEntryMeasurableEquiv n).symm.measurable

/-- HKPV this coordinate law is a probability measure because the actual entry law is. -/
theorem gaussianCoordinateLaw_isProbability (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (gaussianCoordinateLaw n a) := by
  let := gaussianMatrixLaw_isProbability n ha
  change IsProbabilityMeasure ((gaussianMatrixLaw n a).map (schurFlatEntryMeasurableEquiv n))
  exact Measure.isProbabilityMeasure_map (schurFlatEntryMeasurableEquiv n).measurable.aemeasurable

/-- HKPV actual Gaussian integration in fixed coordinates. Finite density
and a measurable equivalence permit arbitrary nonnegative integrands;
no Bochner-integrability convention is used. -/
theorem lintegral_gaussianCoordinateLaw (n : ℕ) {a : ℝ} (ha : 0 < a)
    (F : SchurTangent n → ℝ≥0∞) :
    ∫⁻ x, F x ∂gaussianCoordinateLaw n a =
      ∫⁻ x, ENNReal.ofReal (gaussianCoordinateDensity n a x) * F x ∂schurCoordinateVolume n := by
  rw [gaussianCoordinateLaw, lintegral_map_equiv]
  rw [gaussianMatrixLaw_eq_withDensity n ha,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (continuous_gaussianMatrixDensity n a).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have h := (schurFlatEntryMeasurableEquiv_measurePreserving n).lintegral_comp_emb
    (schurFlatEntryMeasurableEquiv n).measurableEmbedding
    (fun x => ENNReal.ofReal (gaussianCoordinateDensity n a x) * F x)
  simpa only [gaussianCoordinateDensity, MeasurableEquiv.symm_apply_apply, Pi.mul_apply] using h

/-- **HKPV actual fixed-coordinate Gaussian density**. This identifies
the pushforward of the iid entry law with its concrete Lebesgue density,
without any nonlinear coordinate or spectral-law assumption. -/
theorem gaussianCoordinateLaw_eq_withDensity (n : ℕ) {a : ℝ} (ha : 0 < a) :
    gaussianCoordinateLaw n a = (schurCoordinateVolume n).withDensity
      (fun x => ENNReal.ofReal (gaussianCoordinateDensity n a x)) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_gaussianCoordinateLaw n ha]
  simpa only [Pi.mul_apply] using
    (lintegral_withDensity_eq_lintegral_mul (schurCoordinateVolume n)
      (measurable_gaussianCoordinateDensity n a).ennreal_ofReal hF).symm

/-- HKPV reading the fixed-coordinate density on an actual matrix
recovers its original iid entry density exactly. -/
theorem gaussianCoordinateDensity_entrySplit {n : ℕ} (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    gaussianCoordinateDensity n a (schurEntrySplit n A) =
      gaussianMatrixDensity n a (fun ij => A ij.1 ij.2) := by
  change gaussianMatrixDensity n a
    (matrixEntryEquiv n ((schurEntrySplit n).symm (schurEntrySplit n A))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

end Ginibre
