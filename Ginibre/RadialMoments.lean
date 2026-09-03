import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian radial and angular moments

The analytic calculation behind BC12 Theorem 3.3's monomial
orthogonality, with all integrability premises proved explicitly.
-/

noncomputable section
open MeasureTheory Set Real
open scoped Interval
namespace Ginibre

/-- BC12 monomial normalization: Gaussian radial moments are integrable. -/
theorem integrableOn_radial_moment {a : ℝ} (ha : 0 < a) (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * Real.exp (-a * r ^ 2)) (Ioi 0) := by
  simpa only [Real.rpow_natCast] using
    integrableOn_rpow_mul_exp_neg_mul_sq ha
      (by linarith [Nat.cast_nonneg k (α := ℝ)] : -(1 : ℝ) < (k : ℝ))

/-- BC12 monomial normalization: the substitution `u=r^2` gives a factorial. -/
theorem integral_radial_even_moment {a : ℝ} (ha : 0 < a) (k : ℕ) :
    (∫ r : ℝ in Ioi 0, r ^ (2 * k + 1) * Real.exp (-a * r ^ 2)) =
      (Nat.factorial k : ℝ) / (2 * a ^ (k + 1)) := by
  have hsub := integral_comp_rpow_Ioi_of_pos (E := ℝ)
    (g := fun u : ℝ => u ^ k * Real.exp (-(a * u))) (by norm_num : (0 : ℝ) < 2)
  have hpoint (r : ℝ) :
      (2 * r ^ ((2 : ℝ) - 1)) • ((r ^ (2 : ℝ)) ^ k * Real.exp (-(a * r ^ (2 : ℝ)))) =
        2 * (r ^ (2 * k + 1) * Real.exp (-a * r ^ 2)) := by
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
      smul_eq_mul]
    rw [pow_add, pow_one, pow_mul]
    simp only [neg_mul]
    ring
  simp_rw [hpoint] at hsub
  rw [integral_const_mul] at hsub
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (by positivity : (0 : ℝ) < (k : ℝ) + 1) ha
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at hg
  rw [hg] at hsub
  rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast] at hsub
  rw [div_pow, one_pow] at hsub
  calc
    _ = ((1 / a ^ (k + 1)) * (Nat.factorial k : ℝ)) / 2 := by linarith [hsub]
    _ = _ := by ring

/-- BC12 angular orthogonality: every nonconstant integer Fourier mode
has zero integral over a full turn. -/
theorem integral_angular_mode (d : ℤ) :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      Complex.exp ((d : ℂ) * Complex.I * (t : ℂ))) = if d = 0 then 2 * Real.pi else 0 := by
  by_cases hd : d = 0
  · simp [hd]
  · rw [if_neg hd, integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast hd) Complex.I_ne_zero)]
    have he : (d : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) =
        (d : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    rw [he, Complex.exp_int_mul_two_pi_mul_I]
    simp

end Ginibre
