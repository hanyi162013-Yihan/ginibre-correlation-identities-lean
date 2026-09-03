import Ginibre.PolynomialZeroSets
import Ginibre.MatrixDensity
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable

/-!
# The repeated-eigenvalue locus is null for the actual Gaussian matrix law

HKPV Section 6.3: Schur coordinates may discard repeated eigenvalues.
The proof uses a polynomial in the matrix entries: the resultant of the
universal characteristic polynomial and its derivative. Fixed degree
bounds make evaluation commute with the resultant, including dimension zero.
Nonvanishing is witnessed by a diagonal matrix with distinct integer entries.

No eigenvalue density or correlation identity is used.
-/

noncomputable section
open MeasureTheory
namespace Ginibre

/-- A polynomial in the entries detecting collisions of characteristic roots. -/
def collisionPolynomial (n : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  (Matrix.charpoly.univ ℂ (Fin n)).resultant
    (Matrix.charpoly.univ ℂ (Fin n)).derivative n (n - 1)

/-- HKPV exceptional-locus algebra: evaluating the universal polynomial
gives the characteristic-polynomial resultant of the actual matrix. -/
theorem collisionPolynomial_eval (n : ℕ) (A : (Fin n × Fin n) → ℂ) :
    MvPolynomial.eval A (collisionPolynomial n) =
      (Matrix.of A.curry).charpoly.resultant (Matrix.of A.curry).charpoly.derivative
        n (n - 1) := by
  unfold collisionPolynomial
  change (MvPolynomial.eval₂Hom (RingHom.id ℂ) A) _ = _
  rw [← Polynomial.resultant_map_map (Matrix.charpoly.univ ℂ (Fin n))
    (Matrix.charpoly.univ ℂ (Fin n)).derivative n (n - 1)
    (MvPolynomial.eval₂Hom (RingHom.id ℂ) A), ← Polynomial.derivative_map]
  have hmap : Polynomial.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) A)
      (Matrix.charpoly.univ ℂ (Fin n)) = (Matrix.of A.curry).charpoly :=
    Matrix.charpoly.univ_map_eval₂Hom (Fin n) (RingHom.id ℂ) A
  rw [hmap]

/-- HKPV simple-spectrum criterion, proved via the resultant and separability. -/
theorem collisionPolynomial_eval_ne_zero_iff (n : ℕ) (A : (Fin n × Fin n) → ℂ) :
    MvPolynomial.eval A (collisionPolynomial n) ≠ 0 ↔
      (Matrix.of A.curry).charpoly.Separable := by
  rw [collisionPolynomial_eval n A]
  simpa only [isUnit_iff_ne_zero, Polynomial.separable_def,
    Polynomial.natDegree_derivative, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using
    (Polynomial.isUnit_resultant_iff_isCoprime
      (f := (Matrix.of A.curry).charpoly) (g := (Matrix.of A.curry).charpoly.derivative)
      (Matrix.charpoly_monic (Matrix.of A.curry)))

/-- HKPV nondegeneracy witness: distinct diagonal entries give a separable
characteristic polynomial in every dimension, including the empty matrix. -/
theorem diagonal_nat_charpoly_separable (n : ℕ) :
    (Matrix.diagonal (fun i : Fin n => (i.val : ℂ))).charpoly.Separable := by
  rw [Matrix.charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]
  intro i j hij
  apply Fin.ext
  change (i.val : ℂ) = (j.val : ℂ) at hij
  exact_mod_cast hij

/-- HKPV exceptional-locus polynomial is not identically zero. -/
theorem collisionPolynomial_ne_zero (n : ℕ) : collisionPolynomial n ≠ 0 := by
  let A : (Fin n × Fin n) → ℂ := fun ij =>
    Matrix.diagonal (fun i : Fin n => (i.val : ℂ)) ij.1 ij.2
  have hA : Matrix.of A.curry = Matrix.diagonal (fun i : Fin n => (i.val : ℂ)) := rfl
  have hn : MvPolynomial.eval A (collisionPolynomial n) ≠ 0 :=
    (collisionPolynomial_eval_ne_zero_iff n A).mpr (by
      rw [hA]
      exact diagonal_nat_charpoly_separable n)
  intro hzero
  exact hn (by rw [hzero, map_zero])

/-- **HKPV repeated-eigenvalue exclusion under Lebesgue measure**, with no
assumption about a matrix-to-spectrum density. -/
theorem charpoly_separable_ae_volume (n : ℕ) :
    ∀ᵐ A : (Fin n × Fin n) → ℂ, (Matrix.of A.curry).charpoly.Separable := by
  have h := mvPolynomial_eval_ne_zero_ae_pi (fun _ : Fin n × Fin n => (volume : Measure ℂ))
    (collisionPolynomial n) (collisionPolynomial_ne_zero n)
  filter_upwards [h] with A hA
  exact (collisionPolynomial_eval_ne_zero_iff n A).mp hA

/-- **HKPV repeated-eigenvalue exclusion for the actual iid Gaussian matrix**.
Absolute continuity comes from the previously proved entry-product density. -/
theorem gaussianMatrix_charpoly_separable_ae (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ A ∂gaussianMatrixLaw n a, (Matrix.of A.curry).charpoly.Separable := by
  rw [gaussianMatrixLaw_eq_withDensity n ha]
  exact (withDensity_absolutelyContinuous _ _).ae_le (charpoly_separable_ae_volume n)

end Ginibre
