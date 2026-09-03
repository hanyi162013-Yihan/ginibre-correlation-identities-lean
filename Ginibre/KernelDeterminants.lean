import Ginibre.DeterminantMarginal
import Ginibre.Projection
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Genuine integrable nonnegative Ginibre determinants

BC12 Theorem 3.3. The marginal recursion is specialized to the explicit
Gaussian kernel. Positivity is obtained from the rectangular Gram matrix,
not assumed as a property of a putative eigenvalue density.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexOrder
namespace Ginibre

/-- BC12 positivity: any finite Gram determinant is nonnegative real. -/
theorem finiteKernelDet_nonneg {I X : Type*} [Fintype I]
    (φ : I → X → ℂ) (k : ℕ) (z : Fin k → X) :
    0 ≤ kernelDet (finiteKernel φ) k z := by
  classical
  let M : Matrix (Fin k) I ℂ := fun i j => φ j (z i)
  exact (Matrix.posSemidef_self_mul_conjTranspose M).det_nonneg

/-- BC12 positivity for the explicit Gaussian kernel, with no distinctness assumption. -/
theorem kernelDet_nonneg (n k : ℕ) (z : Fin k → ℂ) :
    0 ≤ kernelDet (kernel n) k z := by
  have h : kernel n = finiteKernel (fun i : Fin n => gaussianBasis n i.val) := by
    funext z w
    exact kernel_eq_finiteKernel n z w
  rw [h]
  exact finiteKernelDet_nonneg _ k z

/-- BC12 positivity converts the complex determinant's norm to its real part. -/
theorem norm_kernelDet (n k : ℕ) (z : Fin k → ℂ) :
    ‖kernelDet (kernel n) k z‖ = (kernelDet (kernel n) k z).re :=
  (Complex.re_eq_norm.mpr (kernelDet_nonneg n k z)).symm

/-- BC12 determinants depend continuously on all their points. -/
theorem continuous_kernelDet (n k : ℕ) : Continuous (kernelDet (kernel n) k) := by
  have hA : Continuous (fun z : Fin k → ℂ =>
      Matrix.of (fun i j : Fin k => kernel n (z i) (z j))) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hi : Continuous (fun z : Fin k → ℂ => z i) := continuous_apply i
    have hj : Continuous (fun z : Fin k → ℂ => z j) := continuous_apply j
    exact Continuous.comp
      (f := fun z : Fin k → ℂ => (z i, z j))
      (g := fun zw : ℂ × ℂ => kernel n zw.1 zw.2)
      (continuous_kernel n) (hi.prodMk hj)
  exact hA.matrix_det

/-- BC12 trace integrability, specialized to the explicit kernel. -/
theorem integrable_kernel_diagonal (n : ℕ) : Integrable (fun u => kernel n u u) := by
  cases n with
  | zero => simp
  | succ n =>
    have ha : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    simp_rw [kernel_eq_finiteKernel]
    exact integrable_finiteKernel_diagonal
      (fun i : Fin (n + 1) => gaussianBasis ((n + 1 : ℕ) : ℝ) i.val)
      (fun i j => integrable_gaussianBasis_inner ha i.val j.val)

/-- BC12 trace of the explicit rank-`n` projection. -/
theorem integral_kernel_diagonal (n : ℕ) : (∫ u, kernel n u u) = (n : ℂ) := by
  cases n with
  | zero => simp
  | succ n =>
    have ha : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    simp_rw [kernel_eq_finiteKernel]
    simpa only [Fintype.card_fin] using integral_finiteKernel_diagonal
      (fun i : Fin (n + 1) => gaussianBasis ((n + 1 : ℕ) : ℝ) i.val)
      (fun i j => integrable_gaussianBasis_inner ha i.val j.val)
      (fun i j => by rw [integral_gaussianBasis_inner ha]; simp only [Fin.val_inj])

/-- BC12 explicit determinant sections are absolutely integrable. -/
theorem integrable_ginibreKernelDet_cons (n k : ℕ) (z : Fin k → ℂ) :
    Integrable (fun u => kernelDet (kernel n) (k + 1) (Fin.cons u z)) :=
  integrable_kernelDet_cons (kernel n) (integrable_kernel_diagonal n)
    (integrable_kernel_product n) k z

/-- **BC12 explicit one-point integration recursion**, with all analytic
premises discharged by Gaussian orthogonality. -/
theorem integral_ginibreKernelDet_cons (n k : ℕ) (z : Fin k → ℂ) :
    (∫ u, kernelDet (kernel n) (k + 1) (Fin.cons u z)) =
      ((n : ℂ) - (k : ℂ)) * kernelDet (kernel n) k z :=
  integral_kernelDet_cons (kernel n) n (integrable_kernel_diagonal n)
    (integral_kernel_diagonal n) (integrable_kernel_product n)
    (integral_kernel_product n) k z

end Ginibre
