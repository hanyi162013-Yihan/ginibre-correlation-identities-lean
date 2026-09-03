import Ginibre.MatrixDensity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.NoncommRing

/-!
# The Gaussian factor in Schur coordinates

HKPV Section 6.4: unitary conjugation preserves the entry-square sum, and
diagonal and strictly upper-triangular contributions separate. These are
proved algebraic identities, not Gaussian spectral-law hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace Ginibre

/-- The squared Frobenius norm written without choosing a matrix norm instance. -/
def matrixEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- HKPV Section 6.4: entry-square sum equals the Hermitian trace. -/
theorem matrixEnergy_eq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (matrixEnergy A : ℂ) = Matrix.trace (A.conjTranspose * A) := by
  simp only [matrixEnergy, Complex.ofReal_sum, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.ofReal_pow, Complex.star_def, mul_comm, Complex.mul_conj']

/-- HKPV Section 6.4: the Gaussian matrix energy is invariant under unitary
conjugation. The premise is the ordinary algebraic unitarity equation. -/
theorem matrixEnergy_unitary_conjugate {n : ℕ}
    (U A : Matrix (Fin n) (Fin n) ℂ) (hU : U.conjTranspose * U = 1) :
    matrixEnergy (U * A * U.conjTranspose) = matrixEnergy A := by
  apply Complex.ofReal_injective
  rw [matrixEnergy_eq_trace, matrixEnergy_eq_trace]
  calc
    Matrix.trace ((U * A * U.conjTranspose).conjTranspose * (U * A * U.conjTranspose)) =
      Matrix.trace (U * (A.conjTranspose * (U.conjTranspose * U) * A) * U.conjTranspose) := by
        congr 1
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        noncomm_ring
    _ = Matrix.trace (U * (A.conjTranspose * A) * U.conjTranspose) := by simp [hU]
    _ = Matrix.trace ((U.conjTranspose * U) * (A.conjTranspose * A)) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (A.conjTranspose * A) := by rw [hU, Matrix.one_mul]

/-- HKPV Section 6.4: the diagonal and a zero-diagonal matrix have disjoint
entry support, hence their Gaussian energies add. -/
theorem matrixEnergy_diagonal_add {n : ℕ} (z : Fin n → ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i, T i i = 0) :
    matrixEnergy (Matrix.diagonal z + T) = (∑ i, ‖z i‖ ^ 2) + matrixEnergy T := by
  have h (i j : Fin n) : ‖(Matrix.diagonal z + T) i j‖ ^ 2 =
      (if i = j then ‖z i‖ ^ 2 else 0) + ‖T i j‖ ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp [hT]
    · simp [Matrix.diagonal, hij]
  simp only [matrixEnergy, h, Finset.sum_add_distrib]
  simp

/-- **HKPV Gaussian factorization in Schur coordinates**: the only
eigenvalue-dependent Gaussian factor is `exp(-a sum |z_i|²)`. -/
theorem schur_gaussian_factorization {n : ℕ} (a : ℝ) (z : Fin n → ℂ)
    (U T : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hT : ∀ i, T i i = 0) :
    Real.exp (-a * matrixEnergy (U * (Matrix.diagonal z + T) * U.conjTranspose)) =
      Real.exp (-a * ∑ i, ‖z i‖ ^ 2) * Real.exp (-a * matrixEnergy T) := by
  rw [matrixEnergy_unitary_conjugate U _ hU, matrixEnergy_diagonal_add z T hT,
    mul_add, Real.exp_add]

/-- **HKPV Section 6.4, actual entry-density substitution**: the already-proved
iid matrix density has the expected separated Gaussian factors on Schur
coordinates. The Jacobian and integration over those coordinates are separate. -/
theorem gaussianMatrixDensity_schur {n : ℕ} (a : ℝ) (z : Fin n → ℂ)
    (U T : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hT : ∀ i, T i i = 0) :
    gaussianMatrixDensity n a (fun ij =>
      (U * (Matrix.diagonal z + T) * U.conjTranspose) ij.1 ij.2) =
      (a / Real.pi) ^ (n * n) *
        (Real.exp (-a * ∑ i, ‖z i‖ ^ 2) * Real.exp (-a * matrixEnergy T)) := by
  rw [gaussianMatrixDensity_closedForm]
  rw [Fintype.sum_prod_type]
  change (a / Real.pi) ^ (n * n) *
    Real.exp (-a * matrixEnergy (U * (Matrix.diagonal z + T) * U.conjTranspose)) = _
  rw [schur_gaussian_factorization a z U T hU hT]

end Ginibre
