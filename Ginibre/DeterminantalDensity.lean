import Ginibre.GaussianBasis
import Ginibre.SlaterDensity
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The normalized candidate spectral density

This file proves the normalization and determinant form of the explicit
Ginibre density. It deliberately calls it a *candidate*: the general
Gaussian matrix pushforward identification is not proved by normalizing
this density. No theorem in this file asserts that missing identification.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Ginibre

/-- The normalized squared evaluation determinant, not an assumed spectral law. -/
def determinantDensity (n : ℕ) (a : ℝ) (z : Fin n → ℂ) : ℝ :=
  ‖slater (fun i : Fin n => gaussianBasis a i.val) z‖ ^ 2 / (Nat.factorial n : ℝ)

/-- BC12 candidate density is nonnegative. -/
theorem determinantDensity_nonneg (n : ℕ) (a : ℝ) (z : Fin n → ℂ) :
    0 ≤ determinantDensity n a z := by
  unfold determinantDensity
  positivity

/-- BC12 candidate density has a genuine finite integral. -/
theorem integrable_determinantDensity (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (determinantDensity n a) := by
  exact (integrable_slater_norm_sq (fun i : Fin n => gaussianBasis a i.val)
    (fun i j => integrable_gaussianBasis_inner ha i.val j.val)).div_const _

/-- **BC12 candidate density normalization**, proved from Gaussian
orthogonality, not taken from the printed constant. -/
theorem integral_determinantDensity (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ z, determinantDensity n a z) = 1 := by
  unfold determinantDensity
  change (∫ z : Fin n → ℂ, ‖slater (fun i : Fin n => gaussianBasis a i.val) z‖ ^ 2 /
    (Nat.factorial n : ℝ) ∂Measure.pi (fun _ : Fin n => (volume : Measure ℂ))) = 1
  rw [integral_div, integral_slater_norm_sq (fun i : Fin n => gaussianBasis a i.val)
    (fun i j => integrable_gaussianBasis_inner ha i.val j.val)
    (fun i j => by
      rw [integral_gaussianBasis_inner ha]
      simp only [Fin.val_inj])]
  simp [Nat.factorial_ne_zero]

/-- BC12 full-point determinant formula for the explicit density.
This is an algebraic formula about the candidate, not a pushforward theorem. -/
theorem determinantDensity_eq_kernel_determinant (n : ℕ) (z : Fin n → ℂ) :
    (determinantDensity n (n : ℝ) z : ℂ) =
      Matrix.det (fun i j => kernel n (z i) (z j)) / (Nat.factorial n : ℂ) := by
  simp_rw [kernel_eq_finiteKernel]
  rw [det_finiteKernel_eq_slater_norm_sq]
  simp only [determinantDensity, Complex.ofReal_div, Complex.ofReal_natCast]

/-- BC12 Vandermonde step: pull every Gaussian and normalization factor
out of the evaluation determinant. -/
theorem slater_gaussianBasis_vandermonde (n : ℕ) (a : ℝ) (z : Fin n → ℂ) :
    slater (fun i : Fin n => gaussianBasis a i.val) z =
      (∏ i : Fin n, (Real.sqrt (basisCoefficient a i.val) : ℂ)) *
        (∏ j : Fin n, (Real.exp (-a * ‖z j‖ ^ 2 / 2) : ℂ)) *
          Matrix.det (Matrix.vandermonde z) := by
  have hm : (fun i j : Fin n => gaussianBasis a i.val (z j)) =
      Matrix.of (fun i j : Fin n => (Real.sqrt (basisCoefficient a i.val) : ℂ) *
        (Matrix.of (fun i j : Fin n => (Real.exp (-a * ‖z j‖ ^ 2 / 2) : ℂ) *
          (Matrix.vandermonde z).transpose i j)) i j) := by
    ext i j
    simp only [gaussianBasis, Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
    ring
  rw [slater, hm, Matrix.det_mul_column, Matrix.det_mul_row, Matrix.det_transpose]
  ring

/-- BC12 Vandermonde factor: the collision-vanishing product, with no
normalization or probability assertion hidden in it. -/
theorem vandermonde_norm_sq (n : ℕ) (z : Fin n → ℂ) :
    ‖Matrix.det (Matrix.vandermonde z)‖ ^ 2 =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖ ^ 2 := by
  rw [Matrix.det_vandermonde]
  simp only [norm_prod, Finset.prod_pow]

/-- BC12 candidate density in explicit Gaussian--Vandermonde form.
All constants come from proved one-variable Gaussian integrals. -/
theorem determinantDensity_vandermonde (n : ℕ) {a : ℝ} (ha : 0 < a) (z : Fin n → ℂ) :
    determinantDensity n a z =
      ((∏ i : Fin n, basisCoefficient a i.val) / (Nat.factorial n : ℝ)) *
        Real.exp (-a * ∑ j : Fin n, ‖z j‖ ^ 2) *
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖ ^ 2) := by
  have hc : ‖∏ i : Fin n, (Real.sqrt (basisCoefficient a i.val) : ℂ)‖ ^ 2 =
      ∏ i : Fin n, basisCoefficient a i.val := by
    simp only [norm_prod, ← Finset.prod_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (basisCoefficient_pos ha _).le]
  have he : ‖∏ j : Fin n, (Real.exp (-a * ‖z j‖ ^ 2 / 2) : ℂ)‖ ^ 2 =
      Real.exp (-a * ∑ j : Fin n, ‖z j‖ ^ 2) := by
    have hp (j : Fin n) : Real.exp (-a * ‖z j‖ ^ 2 / 2) ^ 2 =
        Real.exp (-a * ‖z j‖ ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    simp only [norm_prod, ← Finset.prod_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _), hp]
    rw [← Real.exp_sum, ← Finset.mul_sum]
  unfold determinantDensity
  rw [slater_gaussianBasis_vandermonde]
  simp only [norm_mul, mul_pow]
  rw [hc, he, vandermonde_norm_sq]
  ring

end Ginibre
