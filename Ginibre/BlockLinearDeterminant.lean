import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Complex.Norm

/-!
# Determinants of the full real block maps occurring in Schur coordinates

HKPV (6.3.4)--(6.3.5). The upper-triangular variables contribute an
identity block. The remaining complex-linear block contributes the square
of the modulus of its complex determinant when viewed over the reals.
These are ordinary finite-dimensional linear algebra theorems.
-/

noncomputable section
open Module
namespace Ginibre

/-- HKPV full-block determinant: arbitrary coupling below the diagonal
does not change the determinant when the second diagonal block is the identity. -/
theorem det_block_lower_identity {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (L : E × F →ₗ[ℝ] E × F) (A : E →ₗ[ℝ] E)
    (hfst : ∀ x, (L x).1 = A x.1) (hsnd : ∀ y, (L (0, y)).2 = y) :
    LinearMap.det L = LinearMap.det A := by
  classical
  let b := Module.finBasis ℝ E
  let c := Module.finBasis ℝ F
  let C := Matrix.of (fun i j => c.repr ((L (b j, 0)).2) i)
  have hmat : LinearMap.toMatrix (b.prod c) (b.prod c) L =
      Matrix.fromBlocks (LinearMap.toMatrix b b A) 0 C 1 := by
    ext (i | i) (j | j)
    · simp [LinearMap.toMatrix_apply, Basis.prod_apply, hfst]
    · simp [LinearMap.toMatrix_apply, Basis.prod_apply, hfst]
    · simp [LinearMap.toMatrix_apply, Basis.prod_apply, C]
    · simp [LinearMap.toMatrix_apply, Basis.prod_apply, hsnd, Matrix.one_apply,
        Finsupp.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix (b.prod c), hmat, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one, LinearMap.det_toMatrix]

/-- HKPV realification: the determinant of a complex matrix acting on
complex coordinates regarded as a real vector space is its norm square. -/
theorem det_complex_matrix_restrictScalars {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) :
    LinearMap.det ((Matrix.toLin' A).restrictScalars ℝ) = ‖A.det‖ ^ 2 := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_eq]
  exact Complex.normSq_eq_norm_sq _

end Ginibre
