import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Explicit variance-normalized complex Ginibre kernel

BC12, Theorem 3.3, after the rescaling `lambda -> lambda / sqrt n`.
The Gaussian weight is absorbed into the kernel, which is relative to
ordinary planar Lebesgue measure. No assertion about matrix eigenvalues
is contained in these definitions.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Ginibre

/-- BC12 Theorem 3.3: kernel relative to planar Lebesgue measure. -/
def kernel (n : ℕ) (z w : ℂ) : ℂ :=
  (((n : ℝ) / Real.pi *
    Real.exp (-((n : ℝ) * (‖z‖ ^ 2 + ‖w‖ ^ 2)) / 2) : ℝ) : ℂ) *
      ∑ k ∈ Finset.range n, (((n : ℂ) * z * star w) ^ k) / (Nat.factorial k : ℂ)

/-- BC12 Theorem 3.4: mean empirical density in the same normalization. -/
def onePointDensity (n : ℕ) (z : ℂ) : ℝ :=
  Real.exp (-((n : ℝ) * ‖z‖ ^ 2)) *
    (∑ k ∈ Finset.range n, (((n : ℝ) * ‖z‖ ^ 2) ^ k) / (Nat.factorial k : ℝ)) / Real.pi

/-- The squared kernel used in the projection and covariance formulas. -/
def kernelWeight (n : ℕ) (zw : ℂ × ℂ) : ℝ := ‖kernel n zw.1 zw.2‖ ^ 2

/-- Dimension zero is the zero projection, not an exceptional convention. -/
@[simp] theorem kernel_zero (z w : ℂ) : kernel 0 z w = 0 := by simp [kernel]

/-- The explicit Gaussian-polynomial kernel is continuous in both variables. -/
theorem continuous_kernel (n : ℕ) : Continuous (fun zw : ℂ × ℂ => kernel n zw.1 zw.2) := by
  unfold kernel
  fun_prop

end Ginibre
