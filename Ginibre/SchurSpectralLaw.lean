import Ginibre.SchurAngularIntegration
import Ginibre.SchurSpectrumMeasurability

/-!
# The actual ordered Gaussian spectrum has Gaussian--Vandermonde density

HKPV Section 6.4 and BC12 Theorem 3.2. All chart geometry, Jacobians,
overlap removal, coordinate measures, and auxiliary integration are
proved upstream. Probability normalization now removes the unknown
angular coefficient. The chamber integral is retained as the exact
normalizing constant; factorial/permutation simplification is separate.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV the sum of actual disjoint angular integrals, not an assumed constant. -/
def schurGlobalAngularCoefficient (n : ℕ) (a : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal ((a / Real.pi) ^ (n * n) *
    (Real.pi / a) ^ Fintype.card (SchurLower n)) * schurAngularMass n k

/-- HKPV exact ordered diagonal normalizing integral. -/
def schurChamberMass (n : ℕ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in schurSpectralChamber n, ENNReal.ofReal (schurSpectralWeight n a z)

/-- **HKPV global spectral proportionality for the actual Gaussian
matrix**, after all geometric and Gaussian auxiliary variables have
been integrated out internally. -/
theorem lintegral_schurSpectrum_proportional (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ A, f (schurCoordinateSpectrum A) ∂gaussianCoordinateLaw n a =
      schurGlobalAngularCoefficient n a *
        ∫⁻ z in schurSpectralChamber n, ENNReal.ofReal (schurSpectralWeight n a z) * f z := by
  rw [lintegral_gaussianCoordinateLaw_schur_sum n ha]
  calc
    _ = ∑' k : ℕ, ∫⁻ x in schurDisjointDomain n k,
        ENNReal.ofReal (schurJacobianWeight 0 x) *
          (ENNReal.ofReal (gaussianCoordinateDensity n a (schurEntryCoordinates 0 x)) *
            f (fun i => x.2.val i i)) ∂schurCoordinateVolume n := by
      congr 1
      funext k
      apply setLIntegral_congr_fun (measurableSet_schurDisjointDomain n k)
      intro x hx
      exact congrArg (fun z : Fin n → ℂ => ENNReal.ofReal (schurJacobianWeight 0 x) *
        (ENNReal.ofReal (gaussianCoordinateDensity n a (schurEntryCoordinates 0 x)) * f z))
        (schurCoordinateSpectrum_extended (schurAngularAtlasFrame n k) x hx.1)
    _ = ∑' k : ℕ, (ENNReal.ofReal ((a / Real.pi) ^ (n * n) *
          (Real.pi / a) ^ Fintype.card (SchurLower n)) * schurAngularMass n k) *
        ∫⁻ z in schurSpectralChamber n, ENNReal.ofReal (schurSpectralWeight n a z) * f z := by
      congr 1
      funext k
      exact lintegral_schurDisjointDomain_diagonal_separated n ha k f hf
    _ = _ := ENNReal.tsum_mul_right

/-- HKPV total probability determines the product of angular and spectral masses. -/
theorem schurAngularCoefficient_mul_chamberMass (n : ℕ) {a : ℝ} (ha : 0 < a) :
    schurGlobalAngularCoefficient n a * schurChamberMass n a = 1 := by
  let := gaussianCoordinateLaw_isProbability n ha
  have h := lintegral_schurSpectrum_proportional n ha (fun _ => 1) measurable_const
  simpa only [mul_one, lintegral_const, measure_univ, one_mul, schurChamberMass] using h.symm

/-- HKPV the chamber has nonzero finite mass, deduced from actual probability normalization. -/
theorem schurChamberMass_ne_zero_and_ne_top (n : ℕ) {a : ℝ} (ha : 0 < a) :
    schurChamberMass n a ≠ 0 ∧ schurChamberMass n a ≠ ∞ := by
  have h := schurAngularCoefficient_mul_chamberMass n ha
  refine ⟨right_ne_zero_of_mul_eq_one h, ?_⟩
  exact (ENNReal.lt_top_of_mul_ne_top_right (by rw [h]; exact ENNReal.one_ne_top)
    (left_ne_zero_of_mul_eq_one h)).ne

/-- HKPV no unitary-quotient volume formula is needed: normalization fixes the actual coefficient. -/
theorem schurAngularCoefficient_eq_inv_chamberMass (n : ℕ) {a : ℝ} (ha : 0 < a) :
    schurGlobalAngularCoefficient n a = (schurChamberMass n a)⁻¹ :=
  ENNReal.eq_inv_of_mul_eq_one_left (schurAngularCoefficient_mul_chamberMass n ha)

/-- **BC12/HKPV actual ordered spectral integral formula**, with its
normalization determined internally and no remaining geometric interface. -/
theorem lintegral_schurSpectrum_normalized (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ A, f (schurCoordinateSpectrum A) ∂gaussianCoordinateLaw n a =
      (schurChamberMass n a)⁻¹ *
        ∫⁻ z in schurSpectralChamber n, ENNReal.ofReal (schurSpectralWeight n a z) * f z := by
  rw [lintegral_schurSpectrum_proportional n ha f hf,
    schurAngularCoefficient_eq_inv_chamberMass n ha]

/-- BC12 the actual pushforward, defined from Gaussian entries and actual characteristic roots. -/
def gaussianOrderedSpectralLaw (n : ℕ) (a : ℝ) : Measure (Fin n → ℂ) :=
  (gaussianCoordinateLaw n a).map schurCoordinateSpectrum

/-- BC12 the actual spectral pushforward is a probability law. -/
theorem gaussianOrderedSpectralLaw_isProbability (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (gaussianOrderedSpectralLaw n a) := by
  let := gaussianCoordinateLaw_isProbability n ha
  exact Measure.isProbabilityMeasure_map (aemeasurable_schurCoordinateSpectrum n ha)

/-- **BC12/HKPV matrix-to-spectrum density theorem on the ordered chamber**.
The constant is the reciprocal of a proved positive finite explicit
Gaussian--Vandermonde integral, not an externally supplied Schur density. -/
theorem gaussianOrderedSpectralLaw_eq_withDensity (n : ℕ) {a : ℝ} (ha : 0 < a) :
    gaussianOrderedSpectralLaw n a = (volume.restrict (schurSpectralChamber n)).withDensity
      (fun z => (schurChamberMass n a)⁻¹ * ENNReal.ofReal (schurSpectralWeight n a z)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [gaussianOrderedSpectralLaw,
    lintegral_map' hf.aemeasurable (aemeasurable_schurCoordinateSpectrum n ha),
    lintegral_schurSpectrum_normalized n ha f hf]
  have hp : Measurable (fun z : Fin n → ℂ =>
      (schurChamberMass n a)⁻¹ * ENNReal.ofReal (schurSpectralWeight n a z)) :=
    measurable_const.mul (measurable_schurSpectralWeight n a).ennreal_ofReal
  have hd := lintegral_withDensity_eq_lintegral_mul
    (volume.restrict (schurSpectralChamber n)) hp hf
  calc
    _ = ∫⁻ z in schurSpectralChamber n,
        ((schurChamberMass n a)⁻¹ * ENNReal.ofReal (schurSpectralWeight n a z)) * f z := by
      simp only [mul_assoc]
      exact (lintegral_const_mul _
        ((measurable_schurSpectralWeight n a).ennreal_ofReal.mul hf)).symm
    _ = _ := by simpa only [Pi.mul_apply] using! hd.symm

end Ginibre
