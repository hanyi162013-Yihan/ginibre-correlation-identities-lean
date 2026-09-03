import Ginibre.StatisticIntegrability

/-!
# Covariance and variance of actual Ginibre eigenvalue statistics

BC12 covariance step. The expectation and mixed second moment are first
proved on the iid Gaussian matrix-entry space. Projection then yields the
symmetric energy formula and an L2 variance bound. No moment or point-process
identity is assumed.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- BC12 planar first-moment formula for actual Gaussian eigenvalues. -/
theorem gaussianMatrix_integral_linearStatistic_planar (m : ℕ)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * ginibreIntensity (m + 1) z)) :
    (∫ A, linearStatistic (m + 1) f (schurSpectrum (Matrix.of A.curry))
      ∂gaussianMatrixLaw (m + 1) (m + 1 : ℕ)) =
        ∫ z, f z * ginibreIntensity (m + 1) z := by
  have hif : Integrable (fun z : Fin 1 → ℂ =>
      f (z 0) * (kernelDet (kernel (m + 1)) 1 z).re) := by
    simp_rw [kernelDet_one, kernel_diagonal_re]
    exact (integrable_finOne_iff _).mpr hi
  have h := gaussianMatrix_integral_linearStatistic m f hf hif
  simp_rw [kernelDet_one, kernel_diagonal_re] at h
  rw [integral_finOne] at h
  exact h

/-- BC12 L2 against the one-point intensity implies actual statistic L1. -/
theorem gaussianMatrix_integrable_linearStatistic_of_sq (m : ℕ)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity (m + 1) z)) :
    Integrable (fun A => linearStatistic (m + 1) f (schurSpectrum (Matrix.of A.curry)))
      (gaussianMatrixLaw (m + 1) (m + 1 : ℕ)) := by
  have hi := integrable_mul_ginibreIntensity_of_sq (m + 1) f hf hf2
  have hif : Integrable (fun z : Fin 1 → ℂ =>
      f (z 0) * (kernelDet (kernel (m + 1)) 1 z).re) := by
    simp_rw [kernelDet_one, kernel_diagonal_re]
    exact (integrable_finOne_iff _).mpr hi
  exact gaussianMatrix_integrable_linearStatistic m f hf hif

/-- BC12 planar mixed second-moment formula for actual Gaussian eigenvalues. -/
theorem gaussianMatrix_integral_linearStatistic_mul_planar (m : ℕ)
    (f g : ℂ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity (m + 2) z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity (m + 2) z)) :
    (∫ A, linearStatistic (m + 2) f (schurSpectrum (Matrix.of A.curry)) *
        linearStatistic (m + 2) g (schurSpectrum (Matrix.of A.curry))
      ∂gaussianMatrixLaw (m + 2) (m + 2 : ℕ)) =
      (∫ z, (f z * g z) * ginibreIntensity (m + 2) z) +
        ∫ p : ℂ × ℂ, f p.1 * g p.2 * ginibrePairIntensity (m + 2) p.1 p.2 := by
  have hd := integrable_finOne_kernelDet_mul_of_sq (m + 2) f g hf hg hf2 hg2
  have ho := integrable_finTwo_kernelDet_of_sq (m + 2) f g hf hg hf2 hg2
  have h := gaussianMatrix_integral_linearStatistic_mul m f g hf hg hd ho
  simp_rw [kernelDet_one, kernel_diagonal_re, pairStatisticTest, kernelDet_two_re] at h
  rw [integral_finOne, integral_finTwo] at h
  exact h

/-- BC12 analytic covariance functional after inserting the one- and two-point densities. -/
def ginibreCovarianceForm (n : ℕ) (f g : ℂ → ℝ) : ℝ :=
  (∫ z, (f z * g z) * ginibreIntensity n z) -
    ∫ p : ℂ × ℂ, f p.1 * g p.2 * kernelWeight n p

/-- **BC12 covariance formula for actual iid Gaussian matrix eigenvalues**. -/
theorem gaussianEigenvalueCovariance_eq (m : ℕ) (f g : ℂ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity (m + 2) z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity (m + 2) z)) :
    gaussianEigenvalueCovariance (m + 2) f g = ginibreCovarianceForm (m + 2) f g := by
  have hf1 := integrable_mul_ginibreIntensity_of_sq (m + 2) f hf hf2
  have hg1 := integrable_mul_ginibreIntensity_of_sq (m + 2) g hg hg2
  have hk := integrable_kernelWeight_mul_of_sq (m + 2) f g hf hg hf2 hg2
  have hp := hf1.mul_prod hg1
  rw [gaussianEigenvalueCovariance,
    gaussianMatrix_integral_linearStatistic_mul_planar m f g hf hg hf2 hg2,
    gaussianMatrix_integral_linearStatistic_planar (m + 1) f hf hf1,
    gaussianMatrix_integral_linearStatistic_planar (m + 1) g hg hg1]
  have hpair : (∫ p : ℂ × ℂ, f p.1 * g p.2 * ginibrePairIntensity (m + 2) p.1 p.2) =
      (∫ z, f z * ginibreIntensity (m + 2) z) *
        (∫ z, g z * ginibreIntensity (m + 2) z) -
      ∫ p : ℂ × ℂ, f p.1 * g p.2 * kernelWeight (m + 2) p := by
    rw [show (fun p : ℂ × ℂ => f p.1 * g p.2 * ginibrePairIntensity (m + 2) p.1 p.2) =
        fun p => (f p.1 * ginibreIntensity (m + 2) p.1) *
          (g p.2 * ginibreIntensity (m + 2) p.2) -
            f p.1 * g p.2 * kernelWeight (m + 2) p by
      funext p; unfold ginibrePairIntensity; ring,
      integral_sub hp hk, integral_prod_mul]
  rw [hpair]
  unfold ginibreCovarianceForm
  ring

/-- BC12 the covariance form is the symmetric difference energy. -/
theorem ginibreCovarianceForm_eq_energy (n : ℕ) (f g : ℂ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity n z)) :
    ginibreCovarianceForm n f g =
      (1 / 2 : ℝ) * ∫ p : ℂ × ℂ,
        (f p.1 - f p.2) * (g p.1 - g p.2) * kernelWeight n p := by
  have hfg := integrable_mul_mul_ginibreIntensity_of_sq n f g hf hg hf2 hg2
  have hff := integrable_kernelWeight_fst n (fun z => f z * g z) (hf.mul hg) hfg
  have hss := integrable_kernelWeight_snd n (fun z => f z * g z) (hf.mul hg) hfg
  have hfgk := integrable_kernelWeight_mul_of_sq n f g hf hg hf2 hg2
  have hgfk := integrable_kernelWeight_mul_of_sq n g f hg hf hg2 hf2
  have hrevInt : Integrable (fun p : ℂ × ℂ => f p.2 * g p.1 * kernelWeight n p) := by
    apply hgfk.congr
    filter_upwards with p
    ring
  have hrev : (∫ p : ℂ × ℂ, f p.2 * g p.1 * kernelWeight n p) =
      ∫ p : ℂ × ℂ, f p.1 * g p.2 * kernelWeight n p := by
    rw [← integral_prod_swap (fun p : ℂ × ℂ => f p.2 * g p.1 * kernelWeight n p)]
    apply integral_congr_ae
    filter_upwards with p
    rcases p with ⟨z, w⟩
    simp only [Prod.swap]
    rw [kernelWeight_swap]
    ring
  rw [show (fun p : ℂ × ℂ => (f p.1 - f p.2) * (g p.1 - g p.2) * kernelWeight n p) =
      fun p => (f p.1 * g p.1 * kernelWeight n p - f p.1 * g p.2 * kernelWeight n p) -
        (f p.2 * g p.1 * kernelWeight n p - f p.2 * g p.2 * kernelWeight n p) by
    funext p; ring,
    integral_sub (hff.sub hfgk) (hrevInt.sub hss), integral_sub hff hfgk,
    integral_sub hrevInt hss,
    integral_kernelWeight_fst n (fun z => f z * g z) (hf.mul hg) hfg,
    integral_kernelWeight_snd n (fun z => f z * g z) (hf.mul hg) hfg, hrev]
  unfold ginibreCovarianceForm
  ring

/-- BC12 variance is covariance with the same test in both slots. -/
def gaussianEigenvalueVariance (n : ℕ) (f : ℂ → ℝ) : ℝ :=
  gaussianEigenvalueCovariance n f f

/-- **BC12 symmetric energy identity for the actual Gaussian-matrix variance**. -/
theorem gaussianEigenvalueVariance_eq_energy (m : ℕ) (f : ℂ → ℝ)
    (hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity (m + 2) z)) :
    gaussianEigenvalueVariance (m + 2) f =
      (1 / 2 : ℝ) * ∫ p : ℂ × ℂ,
        (f p.1 - f p.2) ^ 2 * kernelWeight (m + 2) p := by
  unfold gaussianEigenvalueVariance
  rw [gaussianEigenvalueCovariance_eq m f f hf hf hf2 hf2,
    ginibreCovarianceForm_eq_energy (m + 2) f f hf hf hf2 hf2]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  ring

/-- **BC12 L2 variance bound for actual Gaussian-matrix eigenvalues**. -/
theorem gaussianEigenvalueVariance_le (m : ℕ) (f : ℂ → ℝ)
    (hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity (m + 2) z)) :
    0 ≤ gaussianEigenvalueVariance (m + 2) f ∧
      gaussianEigenvalueVariance (m + 2) f ≤
        2 * ∫ z, f z ^ 2 * ginibreIntensity (m + 2) z := by
  have hfst := integrable_kernelWeight_fst (m + 2) (fun z => f z ^ 2) (hf.pow_const 2) hf2
  have hsnd := integrable_kernelWeight_snd (m + 2) (fun z => f z ^ 2) (hf.pow_const 2) hf2
  have he : Integrable (fun p : ℂ × ℂ =>
      (f p.1 - f p.2) ^ 2 * kernelWeight (m + 2) p) := by
    apply ((hfst.add hsnd).const_mul 2).mono'
      ((((hf.comp measurable_fst).sub (hf.comp measurable_snd)).pow_const 2).mul
        ((continuous_kernel (m + 2)).measurable.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards with p
    change ‖(f p.1 - f p.2) ^ 2 * ‖kernel (m + 2) p.1 p.2‖ ^ 2‖ ≤
      2 * (f p.1 ^ 2 * ‖kernel (m + 2) p.1 p.2‖ ^ 2 +
        f p.2 ^ 2 * ‖kernel (m + 2) p.1 p.2‖ ^ 2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    have hd : (f p.1 - f p.2) ^ 2 ≤ 2 * (f p.1 ^ 2 + f p.2 ^ 2) := by
      nlinarith [sq_nonneg (f p.1 + f p.2)]
    nlinarith only [mul_le_mul_of_nonneg_right hd (sq_nonneg ‖kernel (m + 2) p.1 p.2‖)]
  rw [gaussianEigenvalueVariance_eq_energy m f hf hf2]
  constructor
  · apply mul_nonneg (by norm_num)
    exact integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · rw [← integral_const_mul]
    have hb : (∫ p : ℂ × ℂ, (1 / 2 : ℝ) *
        ((f p.1 - f p.2) ^ 2 * kernelWeight (m + 2) p)) ≤
        ∫ p : ℂ × ℂ,
          f p.1 ^ 2 * kernelWeight (m + 2) p + f p.2 ^ 2 * kernelWeight (m + 2) p := by
      apply integral_mono ((he.const_mul (1 / 2 : ℝ))) (hfst.add hsnd)
      intro p
      have hd : (1 / 2 : ℝ) * (f p.1 - f p.2) ^ 2 ≤ f p.1 ^ 2 + f p.2 ^ 2 := by
        nlinarith [sq_nonneg (f p.1 + f p.2)]
      have h := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖kernel (m + 2) p.1 p.2‖)
      change (1 / 2 : ℝ) * ((f p.1 - f p.2) ^ 2 * ‖kernel (m + 2) p.1 p.2‖ ^ 2) ≤ _
      nlinarith only [h]
    calc
      _ ≤ _ := hb
      _ = _ := by
        rw [integral_add hfst hsnd,
          integral_kernelWeight_fst (m + 2) (fun z => f z ^ 2) (hf.pow_const 2) hf2,
          integral_kernelWeight_snd (m + 2) (fun z => f z ^ 2) (hf.pow_const 2) hf2]
        ring

end Ginibre
