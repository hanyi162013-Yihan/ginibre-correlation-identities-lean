import Ginibre.PolarIntegration

/-!
# Orthogonality of the explicit Gaussian monomials

The analytic identity used in BC12 Theorem 3.3, with the Gaussian scale
left arbitrary and positive. This is proved with ordinary Lebesgue
integration; no random-matrix input is involved.
-/

noncomputable section
open MeasureTheory Set Real
open scoped Interval
namespace Ginibre

/-- BC12 angular integration: the polar chart and the conventional circle
average describe the same full turn. -/
theorem angular_integral_eq_circleAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (r : ℝ) :
    (∫ t in Ioo (-Real.pi) Real.pi, f (Complex.polarCoord.symm (r, t))) =
      (2 * Real.pi) • circleAverage f 0 r := by
  have hav := circleAverage_eq_integral_add (f := f) (c := 0) (R := r) (-Real.pi)
  rw [intervalIntegral.integral_comp_add_right (fun t => f (circleMap 0 r t))] at hav
  rw [zero_add, show 2 * Real.pi + -Real.pi = Real.pi by ring,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo] at hav
  have hmap (t : ℝ) : Complex.polarCoord.symm (r, t) = circleMap 0 r t := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  simp_rw [hmap]
  rw [hav, smul_smul, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]

/-- BC12 orthogonality: separating the radial coefficient and the integer angular mode. -/
theorem gaussian_monomial_circle {a r : ℝ} (hr : 0 ≤ r) (k l : ℕ) (t : ℝ) :
    (circleMap 0 r t) ^ k * star (circleMap 0 r t) ^ l *
        (Real.exp (-a * ‖circleMap 0 r t‖ ^ 2) : ℂ) =
      ((r ^ (k + l) * Real.exp (-a * r ^ 2) : ℝ) : ℂ) *
        Complex.exp (((k : ℂ) - (l : ℂ)) * Complex.I * (t : ℂ)) := by
  rw [norm_circleMap_zero, abs_of_nonneg hr]
  simp only [circleMap, zero_add, Complex.star_def, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj, Complex.conj_I, mul_pow]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  rw [Complex.ofReal_mul, Complex.ofReal_pow, pow_add]
  calc
    _ = (r : ℂ) ^ k * (r : ℂ) ^ l * (Real.exp (-a * r ^ 2) : ℂ) *
        (Complex.exp ((k : ℂ) * ((t : ℂ) * Complex.I)) *
          Complex.exp ((l : ℂ) * ((t : ℂ) * -Complex.I))) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2 <;> ring

/-- BC12 orthogonality: the circle average vanishes unless the degrees agree. -/
theorem circleAverage_gaussian_monomial {a r : ℝ} (hr : 0 ≤ r) (k l : ℕ) :
    circleAverage (fun z : ℂ => z ^ k * star z ^ l * (Real.exp (-a * ‖z‖ ^ 2) : ℂ)) 0 r =
      if k = l then ((r ^ (2 * k) * Real.exp (-a * r ^ 2) : ℝ) : ℂ) else 0 := by
  rw [circleAverage]
  simp_rw [gaussian_monomial_circle hr k l]
  have he : (k : ℂ) - (l : ℂ) = ((k - (l : ℤ) : ℤ) : ℂ) := by push_cast; rfl
  rw [he, intervalIntegral.integral_const_mul, integral_angular_mode]
  by_cases hkl : k = l
  · subst l
    simp only [sub_self, if_true, ← two_mul, Complex.real_smul]
    push_cast
    field_simp
  · have hd : (k : ℤ) - l ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hkl)
    simp [hd, hkl]

/-- **BC12 Gaussian monomial orthogonality**, before normalizing the monomials. -/
theorem integral_gaussian_monomial {a : ℝ} (ha : 0 < a) (k l : ℕ) :
    (∫ z : ℂ, z ^ k * star z ^ l * (Real.exp (-a * ‖z‖ ^ 2) : ℂ)) =
      if k = l then ((Real.pi * (Nat.factorial k : ℝ) / a ^ (k + 1) : ℝ) : ℂ) else 0 := by
  let f := fun z : ℂ => z ^ k * star z ^ l * (Real.exp (-a * ‖z‖ ^ 2) : ℂ)
  have hc : Continuous f := by dsimp [f]; fun_prop
  have hp := integrable_polar_lift hc.stronglyMeasurable (integrable_gaussian_monomial ha k l)
  rw [← Complex.integral_comp_polarCoord_symm]
  rw [IntegrableOn, polar_restrict_volume] at hp
  rw [polar_restrict_volume, integral_prod _ hp]
  have he : (fun r : ℝ => ∫ t in Ioo (-Real.pi) Real.pi,
      r • f (Complex.polarCoord.symm (r, t))) =ᵐ[volume.restrict (Ioi 0)]
      (fun r => (2 * Real.pi * r) •
        (if k = l then ((r ^ (2 * k) * Real.exp (-a * r ^ 2) : ℝ) : ℂ) else 0)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    dsimp only [f]
    rw [integral_smul, angular_integral_eq_circleAverage f r,
      circleAverage_gaussian_monomial hr.le k l, smul_smul]
    congr 1
    ring
  rw [integral_congr_ae he]
  by_cases hkl : k = l
  · rw [if_pos hkl]
    simp only [if_pos hkl, Complex.real_smul]
    have heq : (fun r : ℝ => ((2 * Real.pi * r : ℝ) : ℂ) *
        ((r ^ (2 * k) * Real.exp (-a * r ^ 2) : ℝ) : ℂ)) =
        (fun r => ((2 * Real.pi * (r ^ (2 * k + 1) * Real.exp (-a * r ^ 2)) : ℝ) : ℂ)) := by
      ext r
      push_cast
      rw [pow_succ]
      ring
    rw [heq, integral_complex_ofReal, integral_const_mul, integral_radial_even_moment ha k]
    push_cast
    ring
  · simp [hkl]

end Ginibre
