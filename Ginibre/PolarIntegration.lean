import Ginibre.RadialMoments
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability-safe polar integration

Analytic preparation for the monomial orthogonality used in BC12 Theorem
3.3. Both directions keep integrability explicit; no use of the total
integral of a divergent function establishes a formula.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Ginibre

/-- The polar chart's product measure, used for Fubini and Tonelli. -/
theorem polar_restrict_volume :
    (volume : Measure (ℝ × ℝ)).restrict polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
  rw [Measure.prod_restrict]
  rfl

/-- BC12 analytic preparation: integrable polar lift implies planar integrability. -/
theorem integrable_of_polar_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} (hf : StronglyMeasurable f)
    (h : IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      polarCoord.target) : Integrable f := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [← Complex.lintegral_comp_polarCoord_symm (fun z => ENNReal.ofReal ‖f z‖)]
  have he : (∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 • ENNReal.ofReal ‖f (Complex.polarCoord.symm p)‖) =
      ∫⁻ p in polarCoord.target,
        ENNReal.ofReal ‖p.1 • f (Complex.polarCoord.symm p)‖ := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    dsimp only
    rw [norm_smul, Real.norm_of_nonneg hp.1.le, ENNReal.ofReal_mul hp.1.le]
    rfl
  rw [he]
  exact (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral

/-- BC12 analytic preparation: planar integrability implies integrability of its polar lift. -/
theorem integrable_polar_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℂ → E} (hf : StronglyMeasurable f) (h : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      polarCoord.target := by
  have hm : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  refine ⟨(measurable_fst.stronglyMeasurable.smul (hf.comp_measurable hm)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have he : (∫⁻ p in polarCoord.target,
      ENNReal.ofReal ‖p.1 • f (Complex.polarCoord.symm p)‖) =
      ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 • ENNReal.ofReal ‖f (Complex.polarCoord.symm p)‖ := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    dsimp only
    rw [norm_smul, Real.norm_of_nonneg hp.1.le, ENNReal.ofReal_mul hp.1.le]
    rfl
  rw [he, Complex.lintegral_comp_polarCoord_symm (fun z => ENNReal.ofReal ‖f z‖)]
  exact (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral

/-- BC12 Gaussian integrability: every nonnegative integer radial moment exists. -/
theorem integrable_norm_pow_mul_gaussian {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k * Real.exp (-a * ‖z‖ ^ 2)) := by
  have hc : Continuous (fun z : ℂ => ‖z‖ ^ k * Real.exp (-a * ‖z‖ ^ 2)) := by fun_prop
  apply integrable_of_polar_lift hc.stronglyMeasurable
  have h := (integrableOn_radial_moment ha (k + 1)).mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict (Ioo (-Real.pi) Real.pi)))
  rw [IntegrableOn, polar_restrict_volume]
  apply h.congr
  rw [← polar_restrict_volume]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
  simp only [smul_eq_mul, mul_one, pow_succ]
  ring

/-- BC12 orthogonality uses complex monomials; their Gaussian products are integrable. -/
theorem integrable_gaussian_monomial {a : ℝ} (ha : 0 < a) (k l : ℕ) :
    Integrable (fun z : ℂ => z ^ k * star z ^ l * (Real.exp (-a * ‖z‖ ^ 2) : ℂ)) := by
  have hc : Continuous (fun z : ℂ => z ^ k * star z ^ l * (Real.exp (-a * ‖z‖ ^ 2) : ℂ)) := by
    fun_prop
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  have heq : (fun z : ℂ => ‖z ^ k * star z ^ l * (Real.exp (-a * ‖z‖ ^ 2) : ℂ)‖) =
      (fun z => ‖z‖ ^ (k + l) * Real.exp (-a * ‖z‖ ^ 2)) := by
    funext z
    simp only [norm_mul, norm_pow, norm_star, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _), pow_add]
  rw [heq]
  exact integrable_norm_pow_mul_gaussian ha (k + l)

/-- BC12 radial normalization integrated over the plane. -/
theorem integral_norm_even_pow_mul_gaussian {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (∫ z : ℂ, ‖z‖ ^ (2 * k) * Real.exp (-a * ‖z‖ ^ 2)) =
      Real.pi * (Nat.factorial k : ℝ) / a ^ (k + 1) := by
  rw [← Complex.integral_comp_polarCoord_symm]
  have he : (fun p : ℝ × ℝ => p.1 •
      (‖Complex.polarCoord.symm p‖ ^ (2 * k) * Real.exp (-a * ‖Complex.polarCoord.symm p‖ ^ 2)))
      =ᵐ[volume.restrict polarCoord.target]
      (fun p => (p.1 ^ (2 * k + 1) * Real.exp (-a * p.1 ^ 2)) * (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    simp only [smul_eq_mul, mul_one, pow_succ]
    ring
  rw [integral_congr_ae he, polar_restrict_volume,
    integral_prod_mul (fun r : ℝ => r ^ (2 * k + 1) * Real.exp (-a * r ^ 2)) (fun _ : ℝ => 1)]
  rw [integral_radial_even_moment ha k]
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi - -Real.pi)]
  ring

end Ginibre
