import Ginibre.GaussianEntries

/-!
# Actual independent Gaussian matrix density

BC12 Theorem 3.2, input side of the Schur transformation: the product
entry law has the explicit density `(a/pi)^(n*n) exp(-a sum |A_ij|^2)`.
No eigenvalue density is assumed here.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Ginibre

/-- Product of the explicitly normalized entry densities. -/
def gaussianMatrixDensity (n : ℕ) (a : ℝ) (A : (Fin n × Fin n) → ℂ) : ℝ :=
  ∏ ij, complexGaussianDensity a (A ij)

/-- BC12 matrix input: the matrix density is nonnegative. -/
theorem gaussianMatrixDensity_nonneg (n : ℕ) {a : ℝ} (ha : 0 < a)
    (A : (Fin n × Fin n) → ℂ) : 0 ≤ gaussianMatrixDensity n a A := by
  exact Finset.prod_nonneg (fun _ _ => complexGaussianDensity_nonneg ha _)

/-- BC12 matrix input: integrability of the full coordinate density. -/
theorem integrable_gaussianMatrixDensity (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (gaussianMatrixDensity n a) := by
  unfold gaussianMatrixDensity
  exact Integrable.fintype_prod (fun _ => integrable_complexGaussianDensity ha)

/-- BC12 matrix input: normalization of the full coordinate density. -/
theorem integral_gaussianMatrixDensity (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ A, gaussianMatrixDensity n a A) = 1 := by
  unfold gaussianMatrixDensity
  rw [integral_fintype_prod_volume_eq_prod
    (fun _ : Fin n × Fin n => complexGaussianDensity a)]
  simp only [integral_complexGaussianDensity ha, Finset.prod_const_one]

/-- **BC12 Gaussian matrix joint density from independent entry laws.**
The finite product measure is identified with its Lebesgue density by
checking measurable rectangles and applying Fubini. -/
theorem gaussianMatrixLaw_eq_withDensity (n : ℕ) {a : ℝ} (ha : 0 < a) :
    gaussianMatrixLaw n a =
      volume.withDensity (fun A => ENNReal.ofReal (gaussianMatrixDensity n a A)) := by
  let := gaussianEntryLaw_isProbability ha
  unfold gaussianMatrixLaw
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ A in univ.pi s, ENNReal.ofReal (∏ ij, complexGaussianDensity a (A ij))) = _
  have hi : Integrable (fun A : (Fin n × Fin n) → ℂ => ∏ ij, complexGaussianDensity a (A ij))
      ((volume : Measure ((Fin n × Fin n) → ℂ)).restrict (univ.pi s)) := by
    change Integrable (gaussianMatrixDensity n a) _
    exact (integrable_gaussianMatrixDensity n ha).integrableOn
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (gaussianMatrixDensity_nonneg n ha))]
  rw [show (volume : Measure ((Fin n × Fin n) → ℂ)).restrict (univ.pi s) =
      Measure.pi (fun ij => (volume : Measure ℂ).restrict (s ij)) from Measure.restrict_pi_pi _ _]
  rw [integral_fintype_prod_eq_prod
    (fun _ : Fin n × Fin n => complexGaussianDensity a)
    (μ := fun ij => (volume : Measure ℂ).restrict (s ij))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun ij _ => integral_nonneg
    (complexGaussianDensity_nonneg ha))]
  apply Finset.prod_congr rfl
  intro ij _
  rw [gaussianEntryLaw, withDensity_apply _ (hs ij),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_complexGaussianDensity ha).integrableOn
      (Filter.Eventually.of_forall (complexGaussianDensity_nonneg ha))]

/-- BC12's Gaussian matrix weight, with its `n^2` coordinate normalization
distinguished from the different spectral normalization. -/
theorem gaussianMatrixDensity_closedForm (n : ℕ) (a : ℝ)
    (A : (Fin n × Fin n) → ℂ) :
    gaussianMatrixDensity n a A =
      (a / Real.pi) ^ (n * n) * Real.exp (-a * ∑ ij, ‖A ij‖ ^ 2) := by
  simp only [gaussianMatrixDensity, complexGaussianDensity, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [← Real.exp_sum, ← Finset.mul_sum]

end Ginibre
