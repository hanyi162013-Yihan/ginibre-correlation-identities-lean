import Ginibre.GaussianCovariance

/-!
# Ginibre statistics in every finite dimension

BC12 one- and two-point formulas, including the empty and rank-one cases.
The rank-one case is derived directly from the one-point law; it never
invokes a two-label marginal of a one-dimensional matrix.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- BC12 the rank-one kernel has exactly product squared modulus. -/
theorem kernelWeight_one (z w : ℂ) :
    kernelWeight 1 (z, w) = ginibreIntensity 1 z * ginibreIntensity 1 w := by
  have hprod : kernel 1 z w * kernel 1 w z = kernel 1 z z * kernel 1 w w := by
    simp only [kernel_eq_finiteKernel, finiteKernel, Fin.sum_univ_one]
    ring
  have hnorm : ((kernelWeight 1 (z, w) : ℝ) : ℂ) = kernel 1 z w * kernel 1 w z := by
    change ((‖kernel 1 z w‖ ^ 2 : ℝ) : ℂ) = _
    rw [← kernel_star 1 z w, Complex.star_def]
    simpa only [← Complex.ofReal_pow] using (Complex.mul_conj' (kernel 1 z w)).symm
  have h := congrArg Complex.re (hnorm.trans hprod)
  rw [kernel_diagonal, kernel_diagonal] at h
  simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero, ginibreIntensity] using h

/-- BC12 rank-one mixed statistic equals the single statistic of the product. -/
theorem linearStatistic_one_mul (f g : ℂ → ℝ) (z : Fin 1 → ℂ) :
    linearStatistic 1 f z * linearStatistic 1 g z =
      linearStatistic 1 (fun w => f w * g w) z := by
  simp only [linearStatistic, Fin.sum_univ_one]

/-- BC12 covariance in dimension one follows directly from the one-point law. -/
theorem gaussianEigenvalueCovariance_one (f g : ℂ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity 1 z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity 1 z)) :
    gaussianEigenvalueCovariance 1 f g = ginibreCovarianceForm 1 f g := by
  have hf1 := integrable_mul_ginibreIntensity_of_sq 1 f hf hf2
  have hg1 := integrable_mul_ginibreIntensity_of_sq 1 g hg hg2
  have hfg := integrable_mul_mul_ginibreIntensity_of_sq 1 f g hf hg hf2 hg2
  unfold gaussianEigenvalueCovariance
  simp_rw [linearStatistic_one_mul]
  rw [gaussianMatrix_integral_linearStatistic_planar 0 (fun z => f z * g z)
      (hf.mul hg) hfg,
    gaussianMatrix_integral_linearStatistic_planar 0 f hf hf1,
    gaussianMatrix_integral_linearStatistic_planar 0 g hg hg1]
  unfold ginibreCovarianceForm
  have he : (fun p : ℂ × ℂ => f p.1 * g p.2 * kernelWeight 1 p) =
      fun p => (f p.1 * ginibreIntensity 1 p.1) * (g p.2 * ginibreIntensity 1 p.2) := by
    funext p
    rw [show p = (p.1, p.2) from rfl, kernelWeight_one]
    ring
  rw [he]
  have hprod : (∫ p : ℂ × ℂ,
      (f p.1 * ginibreIntensity 1 p.1) * (g p.2 * ginibreIntensity 1 p.2)) =
      (∫ z, f z * ginibreIntensity 1 z) * ∫ z, g z * ginibreIntensity 1 z :=
    integral_prod_mul (fun z => f z * ginibreIntensity 1 z)
      (fun z => g z * ginibreIntensity 1 z)
  rw [hprod]

/-- BC12 first-moment formula for every finite dimension, including zero. -/
theorem gaussianMatrix_integral_linearStatistic_all (n : ℕ)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * ginibreIntensity n z)) :
    (∫ A, linearStatistic n f (schurSpectrum (Matrix.of A.curry))
      ∂gaussianMatrixLaw n n) = ∫ z, f z * ginibreIntensity n z := by
  cases n with
  | zero => simp [linearStatistic, ginibreIntensity]
  | succ m => exact gaussianMatrix_integral_linearStatistic_planar m f hf hi

/-- BC12 actual covariance formula with no lower bound on the dimension. -/
theorem gaussianEigenvalueCovariance_all (n : ℕ) (f g : ℂ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity n z)) :
    gaussianEigenvalueCovariance n f g = ginibreCovarianceForm n f g := by
  cases n with
  | zero =>
    simp [gaussianEigenvalueCovariance, ginibreCovarianceForm, linearStatistic,
      ginibreIntensity, kernelWeight]
  | succ n =>
    cases n with
    | zero => exact gaussianEigenvalueCovariance_one f g hf hg hf2 hg2
    | succ m => exact gaussianEigenvalueCovariance_eq m f g hf hg hf2 hg2

/-- BC12 actual variance energy identity, valid in every finite dimension. -/
theorem gaussianEigenvalueVariance_all_energy (n : ℕ) (f : ℂ → ℝ)
    (hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z)) :
    gaussianEigenvalueVariance n f = (1 / 2 : ℝ) *
      ∫ p : ℂ × ℂ, (f p.1 - f p.2) ^ 2 * kernelWeight n p := by
  unfold gaussianEigenvalueVariance
  rw [gaussianEigenvalueCovariance_all n f f hf hf hf2 hf2,
    ginibreCovarianceForm_eq_energy n f f hf hf hf2 hf2]
  simp only [pow_two]

/-- BC12 L2 variance bound, including the separately verified rank-one case. -/
theorem gaussianEigenvalueVariance_all_le (n : ℕ) (f : ℂ → ℝ)
    (hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z)) :
    0 ≤ gaussianEigenvalueVariance n f ∧
      gaussianEigenvalueVariance n f ≤ 2 * ∫ z, f z ^ 2 * ginibreIntensity n z := by
  have hn : 0 ≤ gaussianEigenvalueVariance n f := by
    rw [gaussianEigenvalueVariance_all_energy n f hf hf2]
    apply mul_nonneg (by norm_num)
    exact integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  refine ⟨hn, ?_⟩
  cases n with
  | zero => simp [gaussianEigenvalueVariance, gaussianEigenvalueCovariance,
      linearStatistic, ginibreIntensity]
  | succ n =>
    cases n with
    | zero =>
      have hf1 := integrable_mul_ginibreIntensity_of_sq 1 f hf hf2
      unfold gaussianEigenvalueVariance gaussianEigenvalueCovariance
      simp_rw [linearStatistic_one_mul]
      have hs : Integrable (fun z => (f z * f z) * ginibreIntensity 1 z) := by
        simpa only [pow_two] using hf2
      rw [gaussianMatrix_integral_linearStatistic_planar 0 (fun z => f z * f z)
          (hf.mul hf) hs,
        gaussianMatrix_integral_linearStatistic_planar 0 f hf hf1]
      simp only [← pow_two]
      have hi : 0 ≤ ∫ z, f z ^ 2 * ginibreIntensity 1 z :=
        integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (ginibreIntensity_nonneg 1 z))
      nlinarith [sq_nonneg (∫ z, f z * ginibreIntensity 1 z)]
    | succ m => exact (gaussianEigenvalueVariance_le m f hf hf2).2

end Ginibre
