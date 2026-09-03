import Ginibre.GaussianEntries
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Correlation from actual matrix entries in dimension one

A completely checked base case of BC12 Theorems 3.2--3.4. This is explicitly
dimension one; it must not be mistaken for the general Schur integration
theorem still required in higher dimensions.
-/

noncomputable section
open MeasureTheory
namespace Ginibre

/-- The actual matrix associated to its coordinate sample. -/
def matrixFromEntries {n : ℕ} (A : (Fin n × Fin n) → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A (i, j)

/-- BC12 dimension-one spectral identification, proved using genuine eigenvalues. -/
theorem singleton_hasEigenvalue_iff (A : (Fin 1 × Fin 1) → ℂ) (ζ : ℂ) :
    Module.End.HasEigenvalue (matrixFromEntries A).toLin' ζ ↔ ζ = A (0, 0) := by
  have he : matrixFromEntries A = Matrix.diagonal (fun _ : Fin 1 => A (0, 0)) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    simp [matrixFromEntries, hi, hj]
  rw [he, hasEigenvalue_toLin'_diagonal_iff]
  simp [eq_comm]

/-- **BC12 first correlation formula from Gaussian matrix entries, `n = 1`.**
The only input on the test function is its ordinary measurability and
integrability, not a spectral-law or correlation assumption. -/
theorem singleton_first_correlation (f : ℂ → ℝ) (hf : Measurable f)
    (hint : Integrable f (gaussianEntryLaw 1)) :
    Integrable (fun A : (Fin 1 × Fin 1) → ℂ => f (A (0, 0))) (gaussianMatrixLaw 1 1) ∧
      (∫ A, f (A (0, 0)) ∂gaussianMatrixLaw 1 1) =
        ∫ z, f z * onePointDensity 1 z := by
  let := gaussianEntryLaw_isProbability (by norm_num : (0 : ℝ) < 1)
  constructor
  · exact integrable_comp_eval hint
  · rw [gaussianMatrixLaw, integral_comp_eval hf.aestronglyMeasurable,
      integral_gaussianEntryLaw (by norm_num : (0 : ℝ) < 1)]
    simp_rw [complexGaussianDensity_one]

end Ginibre
