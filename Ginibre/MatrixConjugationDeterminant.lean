import Ginibre.BlockLinearDeterminant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Unitary conjugation has real determinant one on matrix entries

HKPV (6.3.4)--(6.3.5), removing the moving output frame. We compute the
complex determinant of `X ↦ A X B` via its Kronecker entry matrix and then
restrict scalars to the reals. No choice of matrix norm or volume
normalization enters this finite-dimensional determinant computation.
-/

noncomputable section
open scoped Matrix Kronecker
namespace Ginibre

/-- HKPV fixed matrix-entry flattening, with no spectral content. -/
def matrixEntryEquiv (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] (Fin n × Fin n → ℂ) where
  toFun X p := X p.1 p.2
  invFun x i j := x (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- HKPV two-sided multiplication acts linearly on actual matrix entries. -/
def matrixTwoSidedMul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := A * X * B
  map_add' _ _ := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' _ _ := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

/-- HKPV the complete entry matrix of `X ↦ A X B` is `A ⊗ Bᵀ`. -/
theorem matrixTwoSidedMul_entries {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) :
    (A ⊗ₖ B.transpose) *ᵥ matrixEntryEquiv n X =
      matrixEntryEquiv n (A * X * B) := by
  funext p
  change (∑ q : Fin n × Fin n, A p.1 q.1 * B q.2 p.2 * X q.1 q.2) = _
  change _ = ∑ k, (∑ j, A p.1 j * X j k) * B k p.2
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_right_comm _ _ _

/-- HKPV complex determinant of the full two-sided matrix-entry map. -/
theorem det_matrixTwoSidedMul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (matrixTwoSidedMul A B) = A.det ^ n * B.det ^ n := by
  have he : (matrixEntryEquiv n).toLinearMap.comp
      ((matrixTwoSidedMul A B).comp (matrixEntryEquiv n).symm.toLinearMap) =
      Matrix.toLin' (A ⊗ₖ B.transpose) := by
    apply LinearMap.ext
    intro v
    exact (matrixTwoSidedMul_entries A B ((matrixEntryEquiv n).symm v)).symm
  have hd := LinearMap.det_conj (matrixTwoSidedMul A B) (matrixEntryEquiv n)
  rw [he, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose,
    Fintype.card_fin] at hd
  exact hd.symm

/-- **HKPV removal of the unitary output frame**: the actual real
matrix-entry determinant is one, not merely nonzero or of unknown size. -/
theorem det_matrixTwoSidedMul_real_of_inverse {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) :
    LinearMap.det ((matrixTwoSidedMul A B).restrictScalars ℝ) = 1 := by
  have hd : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  rw [LinearMap.det_restrictScalars, det_matrixTwoSidedMul, ← mul_pow, hd, one_pow,
    map_one]

end Ginibre
