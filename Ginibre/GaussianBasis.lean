import Ginibre.MonomialOrthogonality
import Ginibre.Kernel
import Ginibre.FiniteProjection

/-!
# The normalized Gaussian monomials and the explicit kernel

BC12 Theorem 3.3: ordinary planar Lebesgue measure is used, so the basis
functions absorb the square root of the Gaussian density. All factorial,
pi, and dimension factors are derived here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Ginibre

/-- Squared normalization of the degree-`k` Gaussian monomial. -/
def basisCoefficient (a : ℝ) (k : ℕ) : ℝ := a ^ (k + 1) / (Real.pi * Nat.factorial k)

/-- Gaussian-weighted degree-`k` monomial in planar `L²`. -/
def gaussianBasis (a : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  (Real.sqrt (basisCoefficient a k) : ℂ) * z ^ k * (Real.exp (-a * ‖z‖ ^ 2 / 2) : ℂ)

/-- BC12 normalization: positive Gaussian scale gives positive squared coefficient. -/
theorem basisCoefficient_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < basisCoefficient a k := by
  unfold basisCoefficient
  positivity

/-- BC12 projection measurability: every explicit Gaussian monomial is continuous. -/
theorem continuous_gaussianBasis (a : ℝ) (k : ℕ) : Continuous (gaussianBasis a k) := by
  unfold gaussianBasis
  fun_prop

/-- BC12 orthogonality: isolate the scalar normalizations in the inner product. -/
theorem gaussianBasis_inner_integrand (a : ℝ) (i j : ℕ) (z : ℂ) :
    star (gaussianBasis a i z) * gaussianBasis a j z =
      ((Real.sqrt (basisCoefficient a i) * Real.sqrt (basisCoefficient a j) : ℝ) : ℂ) *
        (z ^ j * star z ^ i * (Real.exp (-a * ‖z‖ ^ 2) : ℂ)) := by
  have he : Real.exp (-a * ‖z‖ ^ 2) =
      Real.exp (-a * ‖z‖ ^ 2 / 2) * Real.exp (-a * ‖z‖ ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [gaussianBasis, star_mul, star_pow, Complex.star_def, Complex.conj_ofReal,
    he, Complex.ofReal_mul]
  ring

/-- BC12 inner products are genuinely integrable; no total-integral shortcut is used. -/
theorem integrable_gaussianBasis_inner {a : ℝ} (ha : 0 < a) (i j : ℕ) :
    Integrable (fun z => star (gaussianBasis a i z) * gaussianBasis a j z) := by
  simp_rw [gaussianBasis_inner_integrand]
  exact (integrable_gaussian_monomial ha j i).const_mul _

/-- **BC12 Gaussian monomial orthonormality**, now fully normalized. -/
theorem integral_gaussianBasis_inner {a : ℝ} (ha : 0 < a) (i j : ℕ) :
    (∫ z, star (gaussianBasis a i z) * gaussianBasis a j z) = if i = j then 1 else 0 := by
  simp_rw [gaussianBasis_inner_integrand]
  rw [integral_const_mul, integral_gaussian_monomial ha j i]
  by_cases hij : i = j
  · subst j
    simp only [if_true, ← pow_two, Real.sq_sqrt (basisCoefficient_pos ha i).le,
      ← Complex.ofReal_mul]
    unfold basisCoefficient
    have he : a ^ (i + 1) / (Real.pi * (Nat.factorial i : ℝ)) *
        (Real.pi * (Nat.factorial i : ℝ) / a ^ (i + 1)) = 1 := by
      field_simp [ne_of_gt ha, Real.pi_ne_zero, Nat.factorial_ne_zero]
    rw [he, Complex.ofReal_one]
  · simp [hij, Ne.symm hij]

/-- BC12 Gaussian weights at two points combine into the weight in the explicit kernel. -/
theorem gaussianBasis_product {a : ℝ} (ha : 0 ≤ a) (k : ℕ) (z w : ℂ) :
    gaussianBasis a k z * star (gaussianBasis a k w) =
      ((a / Real.pi * Real.exp (-(a * (‖z‖ ^ 2 + ‖w‖ ^ 2)) / 2) : ℝ) : ℂ) *
        (((a : ℂ) * z * star w) ^ k / (Nat.factorial k : ℂ)) := by
  have hcoef : 0 ≤ basisCoefficient a k := by unfold basisCoefficient; positivity
  have he : Real.exp (-(a * (‖z‖ ^ 2 + ‖w‖ ^ 2)) / 2) =
      Real.exp (-a * ‖z‖ ^ 2 / 2) * Real.exp (-a * ‖w‖ ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : ((Real.sqrt (basisCoefficient a k) : ℂ) ^ 2) = (basisCoefficient a k : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hcoef]
  simp only [gaussianBasis, star_mul, star_pow, Complex.star_def, Complex.conj_ofReal, he]
  calc
    _ = ((Real.sqrt (basisCoefficient a k) : ℂ) ^ 2) *
        z ^ k * (star w) ^ k * (Real.exp (-a * ‖z‖ ^ 2 / 2) : ℂ) *
        (Real.exp (-a * ‖w‖ ^ 2 / 2) : ℂ) := by
          simp only [Complex.star_def]
          ring
    _ = _ := by
      rw [hc]
      simp only [basisCoefficient, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_pow, Complex.ofReal_natCast, pow_succ, mul_pow, Complex.star_def]
      ring

/-- **Exact closed-form kernel identification**, including every Gaussian normalization factor. -/
theorem kernel_eq_finiteKernel (n : ℕ) (z w : ℂ) :
    kernel n z w = finiteKernel (fun i : Fin n => gaussianBasis (n : ℝ) i.val) z w := by
  simp only [finiteKernel, gaussianBasis_product (Nat.cast_nonneg n), ← Finset.mul_sum,
    Complex.ofReal_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ((n : ℂ) * z * star w) ^ k / (k.factorial : ℂ)) n]
  rfl

end Ginibre
