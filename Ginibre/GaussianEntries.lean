import Ginibre.PolarIntegration
import Ginibre.Kernel
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Independence.Basic

/-!
# The Gaussian entry probability space

BC12 Theorem 3.2 starts with independent circular complex Gaussian matrix
entries. Here their law is constructed from its planar density and its
normalization and independence are proved. This is not an eigenvalue-law
assumption. The remaining Schur change of variables must connect this
space to the spectral density in order to prove general correlations.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Ginibre

/-- Circular complex Gaussian density; `a` is inverse complex variance. -/
def complexGaussianDensity (a : ℝ) (z : ℂ) : ℝ :=
  a / Real.pi * Real.exp (-a * ‖z‖ ^ 2)

/-- BC12 entry density is continuous. -/
theorem continuous_complexGaussianDensity (a : ℝ) : Continuous (complexGaussianDensity a) := by
  unfold complexGaussianDensity
  fun_prop

/-- BC12 entry density is nonnegative at positive scale. -/
theorem complexGaussianDensity_nonneg {a : ℝ} (ha : 0 < a) (z : ℂ) :
    0 ≤ complexGaussianDensity a z := by
  unfold complexGaussianDensity
  positivity

/-- BC12 entry density has a genuine finite integral. -/
theorem integrable_complexGaussianDensity {a : ℝ} (ha : 0 < a) :
    Integrable (complexGaussianDensity a) := by
  unfold complexGaussianDensity
  simpa only [pow_zero, one_mul] using
    (integrable_norm_pow_mul_gaussian ha 0).const_mul (a / Real.pi)

/-- BC12 entry normalization derived from the proved planar Gaussian integral. -/
theorem integral_complexGaussianDensity {a : ℝ} (ha : 0 < a) :
    (∫ z, complexGaussianDensity a z) = 1 := by
  have h := integral_norm_even_pow_mul_gaussian ha 0
  simp only [mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one,
    mul_one, zero_add, pow_one] at h
  unfold complexGaussianDensity
  rw [integral_const_mul, h]
  field_simp [ne_of_gt ha, Real.pi_ne_zero]

/-- The entry law is defined from Gaussian matrix coordinates, not from eigenvalues. -/
def gaussianEntryLaw (a : ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (complexGaussianDensity a z))

/-- BC12: the constructed positive-scale Gaussian entry law is a probability measure. -/
theorem gaussianEntryLaw_isProbability {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (gaussianEntryLaw a) := by
  constructor
  rw [gaussianEntryLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_complexGaussianDensity ha)
      (Filter.Eventually.of_forall (complexGaussianDensity_nonneg ha)),
    integral_complexGaussianDensity ha, ENNReal.ofReal_one]

/-- Independent Gaussian entries, with pairs used to index actual matrix entries. -/
def gaussianMatrixLaw (n : ℕ) (a : ℝ) : Measure ((Fin n × Fin n) → ℂ) :=
  Measure.pi (fun _ => gaussianEntryLaw a)

/-- BC12: the matrix-entry law is a probability law in every finite dimension. -/
theorem gaussianMatrixLaw_isProbability (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (gaussianMatrixLaw n a) := by
  let := gaussianEntryLaw_isProbability ha
  unfold gaussianMatrixLaw
  infer_instance

/-- BC12: the coordinate entries are independent, proved on the constructed space. -/
theorem gaussianMatrix_entries_independent (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ProbabilityTheory.iIndepFun (fun ij (A : (Fin n × Fin n) → ℂ) => A ij)
      (gaussianMatrixLaw n a) := by
  let := gaussianEntryLaw_isProbability ha
  exact ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

/-- BC12: every matrix entry has the specified circular Gaussian law. -/
theorem gaussianMatrix_entry_map (n : ℕ) {a : ℝ} (ha : 0 < a) (ij : Fin n × Fin n) :
    (gaussianMatrixLaw n a).map (fun A => A ij) = gaussianEntryLaw a := by
  let := gaussianEntryLaw_isProbability ha
  exact (measurePreserving_eval (fun _ : Fin n × Fin n => gaussianEntryLaw a) ij).map_eq

/-- BC12 normalization sanity check: in dimension one, the entry density
and the claimed eigenvalue one-point density are exactly the same function. -/
theorem complexGaussianDensity_one (z : ℂ) :
    complexGaussianDensity 1 z = onePointDensity 1 z := by
  simp [complexGaussianDensity, onePointDensity, div_eq_mul_inv, mul_comm]

/-- BC12 entry integration: conversion to planar Lebesgue integration,
with every density factor visible. -/
theorem integral_gaussianEntryLaw {a : ℝ} (ha : 0 < a) (f : ℂ → ℝ) :
    (∫ z, f z ∂gaussianEntryLaw a) = ∫ z, f z * complexGaussianDensity a z := by
  rw [gaussianEntryLaw, integral_withDensity_eq_integral_toReal_smul
    (continuous_complexGaussianDensity a).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (complexGaussianDensity_nonneg ha _), smul_eq_mul, mul_comm]

/-- BC12 entry integration: integrability is preserved by the density conversion. -/
theorem integrable_gaussianEntryLaw_iff {a : ℝ} (ha : 0 < a) (f : ℂ → ℝ) :
    Integrable f (gaussianEntryLaw a) ↔
      Integrable (fun z => f z * complexGaussianDensity a z) := by
  rw [gaussianEntryLaw, integrable_withDensity_iff_integrable_smul'
    (continuous_complexGaussianDensity a).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (complexGaussianDensity_nonneg ha _), smul_eq_mul, mul_comm]

end Ginibre
