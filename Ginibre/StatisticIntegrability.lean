import Ginibre.LinearStatistics

/-!
# L2 integrability for Ginibre covariance formulas

BC12 covariance step. Square-integrability against the actual one-point
intensity is shown to imply every L1 assertion used in the one- and
two-point formulas. The proof uses projection, Tonelli/Fubini, and the
Gram-determinant positivity already established upstream.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- The one-point intensity is continuous. -/
theorem continuous_ginibreIntensity (n : ℕ) : Continuous (ginibreIntensity n) := by
  have he : ginibreIntensity n = fun z => (kernel n z z).re := by
    funext z
    exact (kernel_diagonal_re n z).symm
  rw [he]
  have hd : Continuous (fun z : ℂ => (z, z)) := continuous_id.prodMk continuous_id
  have hk : Continuous (fun z : ℂ => kernel n z z) := (continuous_kernel n).comp hd
  exact Complex.continuous_re.comp hk

/-- Elementary product bound used in the L2-to-L1 arguments. -/
theorem abs_mul_le_sq_add_sq_div_two (x y : ℝ) :
    |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]

/-- Squared one-point integrability implies one-point L1. -/
theorem integrable_mul_ginibreIntensity_of_sq (n : ℕ) (f : ℂ → ℝ) (hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z)) :
    Integrable (fun z => f z * ginibreIntensity n z) := by
  have hb : Integrable (fun z => (f z ^ 2 + 1) * ginibreIntensity n z) := by
    apply (hf2.add (integrable_ginibreIntensity n)).congr
    filter_upwards with z
    dsimp only [Pi.add_apply]
    ring
  apply hb.mono' (hf.mul (continuous_ginibreIntensity n).measurable).aestronglyMeasurable
  filter_upwards with z
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ginibreIntensity_nonneg n z)]
  have h : |f z| ≤ f z ^ 2 + 1 := by nlinarith [sq_nonneg (|f z| - 1), sq_abs (f z)]
  exact mul_le_mul_of_nonneg_right h (ginibreIntensity_nonneg n z)

/-- L2 functions have an integrable one-point product. -/
theorem integrable_mul_mul_ginibreIntensity_of_sq (n : ℕ) (f g : ℂ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity n z)) :
    Integrable (fun z => (f z * g z) * ginibreIntensity n z) := by
  have hb : Integrable (fun z => ((f z ^ 2 + g z ^ 2) / 2) * ginibreIntensity n z) := by
    apply ((hf2.add hg2).div_const 2).congr
    filter_upwards with z
    dsimp only [Pi.add_apply]
    ring
  apply hb.mono' ((hf.mul hg).mul (continuous_ginibreIntensity n).measurable).aestronglyMeasurable
  filter_upwards with z
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ginibreIntensity_nonneg n z)]
  exact mul_le_mul_of_nonneg_right (abs_mul_le_sq_add_sq_div_two (f z) (g z))
    (ginibreIntensity_nonneg n z)

/-- Signed weighted projection: L1 against the intensity gives L1 against `|K|^2`. -/
theorem integrable_kernelWeight_fst (n : ℕ) (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * ginibreIntensity n z)) :
    Integrable (fun p : ℂ × ℂ => f p.1 * kernelWeight n p) := by
  have hm : Measurable (fun p : ℂ × ℂ => f p.1 * kernelWeight n p) :=
    (hf.comp measurable_fst).mul ((continuous_kernel n).measurable.norm.pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (fun z =>
    (integrable_kernelWeight_section n z).const_mul (f z)), ?_⟩
  change Integrable (fun z : ℂ => ∫ w : ℂ, ‖f z * kernelWeight n (z, w)‖)
  have he (z : ℂ) : (∫ w : ℂ, ‖f z * kernelWeight n (z, w)‖) =
      ‖f z * ginibreIntensity n z‖ := by
    have hn (w : ℂ) : ‖f z * kernelWeight n (z, w)‖ =
        ‖f z‖ * kernelWeight n (z, w) := by
      have hw : 0 ≤ kernelWeight n (z, w) := sq_nonneg _
      rw [norm_mul, Real.norm_of_nonneg hw]
    simp_rw [hn]
    rw [integral_const_mul, integral_kernelWeight_section]
    rw [norm_mul, Real.norm_of_nonneg (ginibreIntensity_nonneg n z)]
    rfl
  simp_rw [he]
  exact hi.norm

/-- Signed weighted projection integral in the first coordinate. -/
theorem integral_kernelWeight_fst (n : ℕ) (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * ginibreIntensity n z)) :
    (∫ p : ℂ × ℂ, f p.1 * kernelWeight n p) =
      ∫ z, f z * ginibreIntensity n z := by
  have h := integrable_kernelWeight_fst n f hf hi
  change (∫ p : ℂ × ℂ, f p.1 * kernelWeight n p ∂volume.prod volume) = _
  rw [integral_prod _ h]
  simp_rw [integral_const_mul, integral_kernelWeight_section]
  apply integral_congr_ae
  filter_upwards with z
  rfl

/-- The corresponding L1 assertion in the second coordinate. -/
theorem integrable_kernelWeight_snd (n : ℕ) (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * ginibreIntensity n z)) :
    Integrable (fun p : ℂ × ℂ => f p.2 * kernelWeight n p) := by
  have h := (integrable_kernelWeight_fst n f hf hi).swap
  apply h.congr
  filter_upwards with p
  rcases p with ⟨z, w⟩
  simp only [Function.comp_apply, Prod.swap]
  rw [kernelWeight_swap]

/-- The corresponding integral in the second coordinate. -/
theorem integral_kernelWeight_snd (n : ℕ) (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * ginibreIntensity n z)) :
    (∫ p : ℂ × ℂ, f p.2 * kernelWeight n p) =
      ∫ z, f z * ginibreIntensity n z := by
  rw [← integral_kernelWeight_fst n f hf hi]
  change (∫ p : ℂ × ℂ, f p.2 * kernelWeight n p ∂volume.prod volume) =
    ∫ p : ℂ × ℂ, f p.1 * kernelWeight n p ∂volume.prod volume
  have h := integral_prod_swap (μ := (volume : Measure ℂ)) (ν := volume)
    (fun p : ℂ × ℂ => f p.1 * kernelWeight n p)
  have he : (fun p : ℂ × ℂ => f p.swap.1 * kernelWeight n p.swap) =
      fun p => f p.2 * kernelWeight n p := by
    funext p
    change f p.2 * kernelWeight n (p.2, p.1) = f p.2 * kernelWeight n (p.1, p.2)
    rw [kernelWeight_swap n p.2 p.1]
  rw [he] at h
  exact h

/-- L2 against the intensity controls the mixed `|K|^2` integral. -/
theorem integrable_kernelWeight_mul_of_sq (n : ℕ) (f g : ℂ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity n z)) :
    Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * kernelWeight n p) := by
  have hfst := integrable_kernelWeight_fst n (fun z => f z ^ 2) (hf.pow_const 2) hf2
  have hsnd := integrable_kernelWeight_snd n (fun z => g z ^ 2) (hg.pow_const 2) hg2
  have hb := (hfst.add hsnd).div_const 2
  apply hb.mono' (((hf.comp measurable_fst).mul (hg.comp measurable_snd)).mul
    ((continuous_kernel n).measurable.norm.pow_const 2)).aestronglyMeasurable
  filter_upwards with p
  dsimp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply]
  unfold kernelWeight
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have h := mul_le_mul_of_nonneg_right
    (abs_mul_le_sq_add_sq_div_two (f p.1) (g p.2))
    (sq_nonneg ‖kernel n p.1 p.2‖)
  rw [abs_mul] at h
  nlinarith only [h]

/-- The two-point determinant test is L1 under the same L2 hypotheses. -/
theorem integrable_pairIntensity_mul_of_sq (n : ℕ) (f g : ℂ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity n z)) :
    Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * ginibrePairIntensity n p.1 p.2) := by
  have hf1 := integrable_mul_ginibreIntensity_of_sq n f hf hf2
  have hg1 := integrable_mul_ginibreIntensity_of_sq n g hg hg2
  have hp := hf1.mul_prod hg1
  have hk := integrable_kernelWeight_mul_of_sq n f g hf hg hf2 hg2
  apply (hp.sub hk).congr
  filter_upwards with p
  dsimp only [Pi.sub_apply]
  unfold ginibrePairIntensity
  ring

/-- Finite-product version of two-point L1 used by the actual Campbell formula. -/
theorem integrable_finTwo_kernelDet_of_sq (n : ℕ) (f g : ℂ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity n z)) :
    Integrable (fun z : Fin 2 → ℂ =>
      pairStatisticTest f g z * (kernelDet (kernel n) 2 z).re) := by
  rw [show (fun z : Fin 2 → ℂ => pairStatisticTest f g z *
      (kernelDet (kernel n) 2 z).re) = fun z =>
        f (z 0) * g (z 1) * ginibrePairIntensity n (z 0) (z 1) by
      funext z; rw [pairStatisticTest, kernelDet_two_re]]
  exact (integrable_finTwo_iff _).mpr
    (integrable_pairIntensity_mul_of_sq n f g hf hg hf2 hg2)

/-- Finite-product version of one-point L1 used by the actual Campbell formula. -/
theorem integrable_finOne_kernelDet_mul_of_sq (n : ℕ) (f g : ℂ → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hf2 : Integrable (fun z => f z ^ 2 * ginibreIntensity n z))
    (hg2 : Integrable (fun z => g z ^ 2 * ginibreIntensity n z)) :
    Integrable (fun z : Fin 1 → ℂ =>
      (f (z 0) * g (z 0)) * (kernelDet (kernel n) 1 z).re) := by
  rw [show (fun z : Fin 1 → ℂ => (f (z 0) * g (z 0)) *
      (kernelDet (kernel n) 1 z).re) = fun z =>
        (f (z 0) * g (z 0)) * ginibreIntensity n (z 0) by
      funext z; rw [kernelDet_one, kernel_diagonal_re]]
  exact (integrable_finOne_iff _).mpr
    (integrable_mul_mul_ginibreIntensity_of_sq n f g hf hg hf2 hg2)

end Ginibre
