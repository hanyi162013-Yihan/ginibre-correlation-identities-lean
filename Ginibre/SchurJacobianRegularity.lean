import Ginibre.SchurProductGaussian
import Ginibre.SchurAngularPatch

/-!
# Measurability of the actual separated Schur integration weight

HKPV (6.3.5), regularity needed for Tonelli and angular globalization.
The angular Jacobian is recovered from the derivative of the actual
smooth full-dimensional map at a fixed reference diagonal. Thus its
continuity is proved, not an additional integration hypothesis.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV the actual entry-coordinate map is smooth in every real variable. -/
theorem contDiff_schurEntryCoordinates {n : ℕ} (k : ℕ∞ω)
    (S : Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ k (schurEntryCoordinates S) := by
  convert! (schurEntrySplit n).toContinuousLinearEquiv.contDiff.comp
    (contDiff_schurExpCoordinates k S)

/-- HKPV the Vandermonde square is positive on every distinct spectrum. -/
theorem schurDiagonalWeight_pos {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z) :
    0 < schurDiagonalWeight z := by
  unfold schurDiagonalWeight
  apply Finset.prod_pos
  intro p _
  exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hz.ne (ne_of_lt p.property)))) 2

/-- HKPV recover the angular factor from a fixed genuine derivative;
the nonzero denominator is proved from the explicit reference spectrum. -/
theorem schurAngularJacobian_eq_reference_quotient {n : ℕ} (w : SchurLower n → ℂ) :
    schurAngularJacobian w =
      (fderiv ℝ (schurEntryCoordinates (Matrix.diagonal (schurReferenceSpectrum n))) (w, 0)).det /
        schurDiagonalWeight (schurReferenceSpectrum n) := by
  apply (eq_div_iff (ne_of_gt (schurDiagonalWeight_pos _ (schurReferenceSpectrum_injective n)))).mpr
  calc
    _ = schurDiagonalWeight (schurReferenceSpectrum n) * schurAngularJacobian w := mul_comm _ _
    _ = _ := by
      have h := det_fderiv_schurEntryCoordinates_everywhere
        (Matrix.diagonal (schurReferenceSpectrum n)) (Matrix.blockTriangular_diagonal _) (w, 0)
      simpa only [schurDiagonalWeight, ZeroMemClass.coe_zero, add_zero,
        Matrix.diagonal_apply_eq] using! h.symm

/-- **HKPV continuity of the actual angular integration factor**, obtained
from the already constructed smooth Schur map, with no angular regularity input. -/
theorem continuous_schurAngularJacobian (n : ℕ) :
    Continuous (schurAngularJacobian : (SchurLower n → ℂ) → ℝ) := by
  let D := Matrix.diagonal (schurReferenceSpectrum n)
  have hf : Continuous (fun x : SchurTangent n => (fderiv ℝ (schurEntryCoordinates D) x).det) :=
    ContinuousLinearMap.continuous_det.comp
      ((contDiff_schurEntryCoordinates 1 D).continuous_fderiv one_ne_zero)
  have hc : Continuous (fun w : SchurLower n → ℂ =>
      (fderiv ℝ (schurEntryCoordinates D) (w, 0)).det /
        schurDiagonalWeight (schurReferenceSpectrum n)) :=
    (hf.comp (continuous_id.prodMk continuous_const)).div_const
      (schurDiagonalWeight (schurReferenceSpectrum n))
  simpa only [D, ← schurAngularJacobian_eq_reference_quotient] using! hc

/-- HKPV the diagonal factor is continuous as a finite product of squared distances. -/
theorem continuous_schurDiagonalWeight (n : ℕ) :
    Continuous (schurDiagonalWeight : (Fin n → ℂ) → ℝ) := by
  unfold schurDiagonalWeight
  fun_prop

/-- HKPV continuity of the actual Gaussian density times the full
Jacobian in separated product coordinates, sufficient for all subsequent Tonelli steps. -/
theorem continuous_schurGaussianProductWeight (n : ℕ) (a : ℝ) :
    Continuous (schurGaussianProductWeight n a) := by
  simp_rw [show schurGaussianProductWeight n a = fun y =>
      ((a / Real.pi) ^ (n * n) *
        (schurDiagonalWeight y.2.1 * Real.exp (-a * ∑ i, ‖y.2.1 i‖ ^ 2)) *
        |schurAngularJacobian y.1|) * Real.exp (-a * ∑ p, ‖y.2.2 p‖ ^ 2) from
    funext (schurGaussianProductWeight_factorization a)]
  have hJ := continuous_schurAngularJacobian n
  have hV := continuous_schurDiagonalWeight n
  fun_prop

end Ginibre
