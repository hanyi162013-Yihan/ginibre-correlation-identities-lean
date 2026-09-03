import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Bordered determinant algebra for the BC12 marginal recursion

The two Laplace expansions below require neither invertibility nor distinct
points. In particular, they remain valid on every collision configuration.
-/

noncomputable section
open scoped BigOperators
namespace Ginibre

/-- Adjoin a first row and a first column to a square matrix. -/
def bordered {R : Type*} {k : ℕ} (a : R) (r c : Fin k → R)
    (B : Matrix (Fin k) (Fin k) R) : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  fun i => Fin.cases (Fin.cases a r) (fun i => Fin.cases (c i) (B i)) i

/-- The usual signed minor; indices refer to the original matrix. -/
def cofactor {R : Type*} [CommRing R] {k : ℕ}
    (B : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (i j : Fin (k + 1)) : R :=
  (-1) ^ (i.val + j.val) * Matrix.det (B.submatrix i.succAbove j.succAbove)

/-- BC12 determinant integration, algebraic step: the bordered determinant
is affine in its corner and bilinear in its off-diagonal borders. -/
theorem det_bordered {R : Type*} [CommRing R] {k : ℕ}
    (a : R) (r c : Fin (k + 1) → R)
    (B : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    Matrix.det (bordered a r c B) = a * Matrix.det B -
      ∑ j, ∑ i, (r j * c i) * cofactor B i j := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [bordered, Fin.cases_zero, Fin.cases_succ, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero, Matrix.submatrix]
  rw [sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_succ_column_zero]
  simp only [Fin.succ_succAbove_zero, Fin.cases_zero, Fin.succ_succAbove_succ,
    Fin.cases_succ, Matrix.submatrix, Matrix.of_apply, Fin.val_succ]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [cofactor, Matrix.submatrix, pow_add, pow_succ]
  ring

/-- BC12 determinant integration, Euler/Laplace identity: contracting all
cofactors with their entries counts the number of rows. -/
theorem sum_entry_cofactor {R : Type*} [CommRing R] {k : ℕ}
    (B : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    (∑ j, ∑ i, B i j * cofactor B i j) = (k + 1 : ℕ) * Matrix.det B := by
  rw [Finset.sum_comm]
  have h (i : Fin (k + 1)) : (∑ j, B i j * cofactor B i j) = Matrix.det B := by
    rw [Matrix.det_succ_row B i]
    apply Finset.sum_congr rfl
    intro j _
    unfold cofactor
    ring
  simp_rw [h]
  simp

end Ginibre
