import Ginibre.SchurSpectralLaw
import Ginibre.SchurChamberIntegration

/-!
# Explicit normalization of the actual Gaussian spectral law

BC12 Theorem 3.2 and HKPV Section 6.4. The proved factorial chamber
partition identifies the remaining normalization. Symmetric statistics
of the actual Gaussian matrix now have exactly the integrals against
the explicit, already normalized determinant density.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- BC12 factorial times the ordered spectral mass equals the known full Gaussian integral. -/
theorem factorial_mul_schurChamberMass (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (Nat.factorial n : ℝ≥0∞) * schurChamberMass n a =
      ENNReal.ofReal ((schurSpectralCoefficient n a)⁻¹) := by
  have h := lintegral_schurWeight_symmetric_eq_factorial_chamber n ha (fun _ => 1)
    (fun _ _ => rfl)
  simp only [mul_one] at h
  rw [lintegral_schurSpectralWeight n ha] at h
  exact h.symm

/-- BC12 the printed determinant normalization and the chamber multiplicity match exactly. -/
theorem factorial_spectralCoefficient_mul_chamberMass (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ((Nat.factorial n : ℝ≥0∞) * ENNReal.ofReal (schurSpectralCoefficient n a)) *
      schurChamberMass n a = 1 := by
  calc
    _ = ENNReal.ofReal (schurSpectralCoefficient n a) *
        ((Nat.factorial n : ℝ≥0∞) * schurChamberMass n a) := by ac_rfl
    _ = ENNReal.ofReal (schurSpectralCoefficient n a) *
        ENNReal.ofReal ((schurSpectralCoefficient n a)⁻¹) := by
      rw [factorial_mul_schurChamberMass n ha]
    _ = 1 := by
      rw [← ENNReal.ofReal_mul (schurSpectralCoefficient_pos n ha).le,
        mul_inv_cancel₀ (ne_of_gt (schurSpectralCoefficient_pos n ha)), ENNReal.ofReal_one]

/-- **BC12 explicit ordered normalization**, derived from the actual
matrix law and the finite chamber partition, without an angular-volume input. -/
theorem inv_schurChamberMass_eq_factorial_coefficient (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (schurChamberMass n a)⁻¹ =
      (Nat.factorial n : ℝ≥0∞) * ENNReal.ofReal (schurSpectralCoefficient n a) :=
  (ENNReal.eq_inv_of_mul_eq_one_left (factorial_spectralCoefficient_mul_chamberMass n ha)).symm

/-- **BC12 actual ordered eigenvalue density**: `n!` times the symmetric
candidate, restricted to the proved lexicographic chamber. -/
theorem gaussianOrderedSpectralLaw_eq_candidate_chamber (n : ℕ) {a : ℝ} (ha : 0 < a) :
    gaussianOrderedSpectralLaw n a = (volume.restrict (schurSpectralChamber n)).withDensity
      (fun z => (Nat.factorial n : ℝ≥0∞) * ENNReal.ofReal (determinantDensity n a z)) := by
  rw [gaussianOrderedSpectralLaw_eq_withDensity n ha,
    inv_schurChamberMass_eq_factorial_coefficient n ha]
  congr 1
  funext z
  rw [determinantDensity_eq_schurSpectralWeight n ha,
    ENNReal.ofReal_mul (schurSpectralCoefficient_pos n ha).le, mul_assoc]

/-- **BC12 symmetric statistics of the actual Gaussian matrix** equal
integrals against the explicit determinant density. This is a genuine
matrix-to-spectrum theorem, not a candidate-density normalization claim. -/
theorem lintegral_schurSpectrum_symmetric (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂ), f (fun i => z (σ i)) = f z) :
    ∫⁻ A, f (schurCoordinateSpectrum A) ∂gaussianCoordinateLaw n a =
      ∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * f z := by
  rw [lintegral_schurSpectrum_normalized n ha f hf,
    inv_schurChamberMass_eq_factorial_coefficient n ha]
  simp_rw [determinantDensity_eq_schurSpectralWeight n ha,
    ENNReal.ofReal_mul (schurSpectralCoefficient_pos n ha).le, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_schurWeight_symmetric_eq_factorial_chamber n ha f hsym]
  ac_rfl

/-- BC12 fixed entry reassembly, factored before applying any spectral selection. -/
theorem schurFlatEntryMeasurableEquiv_apply (n : ℕ) (A : Fin n × Fin n → ℂ) :
    schurFlatEntryMeasurableEquiv n A = schurEntrySplit n (Matrix.of A.curry) := by
  change schurEntrySplit n ((matrixEntryEquiv n).symm A) = _
  apply congrArg (schurEntrySplit n)
  rfl

/-- BC12 the spectral selection commutes with the fixed raw-entry coordinate equivalence. -/
theorem schurCoordinateSpectrum_flatEntry (n : ℕ) (A : Fin n × Fin n → ℂ) :
    schurCoordinateSpectrum (schurFlatEntryMeasurableEquiv n A) =
      schurSpectrum (Matrix.of A.curry) := by
  rw [schurFlatEntryMeasurableEquiv_apply, schurCoordinateSpectrum_entrySplit]

/-- **BC12 from independent Gaussian matrix elements to spectral statistics**,
with all non-probabilistic and Gaussian change-of-variables inputs proved internally. -/
theorem lintegral_gaussianMatrix_symmetric_spectrum (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂ), f (fun i => z (σ i)) = f z) :
    ∫⁻ A, f (schurSpectrum (Matrix.of A.curry)) ∂gaussianMatrixLaw n a =
      ∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * f z := by
  have h := lintegral_schurSpectrum_symmetric n ha f hf hsym
  rw [gaussianCoordinateLaw, lintegral_map_equiv] at h
  simpa only [schurCoordinateSpectrum_flatEntry] using h

end Ginibre
