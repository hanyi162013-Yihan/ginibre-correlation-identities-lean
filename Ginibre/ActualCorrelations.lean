import Ginibre.GaussianLabelledLaw
import Ginibre.FiniteMarginals
import Ginibre.Projection

/-!
# Actual Ginibre joint density and all finite correlation densities

BC12 Theorems 3.2--3.4. The joint density below is first identified
with the actual Gaussian spectral pushforward. Its k-point correlation
density uses the standard factorial-normalized marginal integral. The
absolute integrability of every marginal section is recorded explicitly.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Ginibre

/-- BC12 factorial correlation density: integrate `m` of the `k+m`
randomly labelled eigenvalues from their proved actual joint density. -/
def ginibreCorrelationDensity (k m : ℕ) (z : Fin k → ℂ) : ℝ :=
  ((Nat.factorial (k + m) : ℝ) / (Nat.factorial m : ℝ)) *
    ∫ w : Fin m → ℂ, determinantDensity (k + m) (k + m : ℕ) (prependPoints k m w z)

/-- **BC12 Theorem 3.3: every factorial-normalized marginal is the
retained Ginibre kernel determinant**. The density is connected to the
actual matrix law in the combined endpoint below. -/
theorem ginibreCorrelationDensity_eq_kernelDet (k m : ℕ) (z : Fin k → ℂ) :
    ginibreCorrelationDensity k m z = (kernelDet (kernel (k + m)) k z).re := by
  rw [ginibreCorrelationDensity, integral_determinantDensity_prepend_real]
  have hm : (Nat.factorial m : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (Nat.factorial (k + m) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + m)
  field_simp

/-- **BC12 from Gaussian matrix entries to all finite correlation
densities**, in one endpoint: actual spectral-law identification,
absolute marginal integrability, and the determinant formula. -/
theorem gaussian_matrix_density_and_correlations (k m : ℕ) (hn : 0 < k + m) :
    gaussianLabelledSpectralLaw (k + m) (k + m : ℕ) = volume.withDensity
      (fun z => ENNReal.ofReal (determinantDensity (k + m) (k + m : ℕ) z)) ∧
      ∀ z : Fin k → ℂ,
        Integrable (fun w : Fin m → ℂ =>
          determinantDensity (k + m) (k + m : ℕ) (prependPoints k m w z)) ∧
        ginibreCorrelationDensity k m z = (kernelDet (kernel (k + m)) k z).re := by
  refine ⟨gaussianLabelledSpectralLaw_eq_withDensity (k + m) (by exact_mod_cast hn), ?_⟩
  intro z
  exact ⟨integrable_determinantDensity_prepend k m z, ginibreCorrelationDensity_eq_kernelDet k m z⟩

/-- BC12 the zeroth correlation density is one. -/
theorem ginibreCorrelationDensity_zero (m : ℕ) (z : Fin 0 → ℂ) :
    ginibreCorrelationDensity 0 m z = 1 := by
  rw [ginibreCorrelationDensity_eq_kernelDet, kernelDet_zero, Complex.one_re]

/-- **BC12 Theorem 3.4 first correlation density**, with the empirical
normalization distinguished from the unnormalized point intensity. -/
theorem ginibreCorrelationDensity_one (m : ℕ) (z : Fin 1 → ℂ) :
    ginibreCorrelationDensity 1 m z = ((1 + m : ℕ) : ℝ) * onePointDensity (1 + m) (z 0) := by
  rw [ginibreCorrelationDensity_eq_kernelDet, kernelDet_one, kernel_diagonal, Complex.ofReal_re]

/-- BC12 two-point correlation determinant, including its off-diagonal subtraction. -/
theorem ginibreCorrelationDensity_two (m : ℕ) (z : Fin 2 → ℂ) :
    ginibreCorrelationDensity 2 m z =
      (kernel (2 + m) (z 0) (z 0) * kernel (2 + m) (z 1) (z 1) -
        kernel (2 + m) (z 0) (z 1) * kernel (2 + m) (z 1) (z 0)).re := by
  simpa only [kernelDet, Matrix.det_fin_two, Matrix.of_apply] using
    ginibreCorrelationDensity_eq_kernelDet 2 m z

end Ginibre
