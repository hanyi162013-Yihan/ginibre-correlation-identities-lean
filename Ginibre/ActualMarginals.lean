import Ginibre.ActualCorrelations
import Ginibre.MarginalCoordinates

/-!
# Actual retained-eigenvalue laws and factorial correlation measures

BC12 Theorem 3.3. The joint law is the proved pushforward of actual
Gaussian matrix eigenvalues with uniform labels. We project this law
to `k` retained labels, prove its density by genuine product Fubini,
and identify the factorial-scaled marginal measure with the kernel
determinant density. No marginal-law interface is assumed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Ginibre

/-- BC12 the actual retained block of a labelled spectral tuple. -/
def retainedSpectrum (k m : ℕ) (A : Fin (k + m) → ℂ) : Fin k → ℂ :=
  (marginalProductEquiv k m A).2

/-- BC12 coordinate projection is measurable. -/
theorem measurable_retainedSpectrum (k m : ℕ) : Measurable (retainedSpectrum k m) :=
  measurable_snd.comp (marginalProductEquiv k m).measurable

/-- BC12 the retained coordinates agree with the marginal integration convention. -/
theorem retainedSpectrum_prepend (k m : ℕ) (w : Fin m → ℂ) (z : Fin k → ℂ) :
    retainedSpectrum k m (prependPoints k m w z) = z := by
  unfold retainedSpectrum
  rw [← marginalProductEquiv_symm k m w z, MeasurableEquiv.apply_symm_apply]

/-- BC12 the explicit probability density of `k` labelled eigenvalues. -/
def ginibreMarginalDensity (k m : ℕ) (z : Fin k → ℂ) : ℝ :=
  ((Nat.factorial m : ℝ) / (Nat.factorial (k + m) : ℝ)) *
    (kernelDet (kernel (k + m)) k z).re

/-- BC12 the marginal density is measurable as a continuous determinant expression. -/
theorem measurable_ginibreMarginalDensity (k m : ℕ) :
    Measurable (ginibreMarginalDensity k m) :=
  measurable_const.mul (Complex.continuous_re.comp (continuous_kernelDet (k + m) k)).measurable

/-- BC12 exact nonnegative marginal integration, supported by absolute section integrability. -/
theorem lintegral_determinantDensity_prepend (k m : ℕ) (z : Fin k → ℂ) :
    (∫⁻ w : Fin m → ℂ, ENNReal.ofReal
      (determinantDensity (k + m) (k + m : ℕ) (prependPoints k m w z))) =
        ENNReal.ofReal (ginibreMarginalDensity k m z) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_determinantDensity_prepend k m z)
    (Filter.Eventually.of_forall (fun w => determinantDensity_nonneg _ _ _))]
  exact congrArg ENNReal.ofReal (integral_determinantDensity_prepend_real k m z)

/-- BC12 integrating a retained-coordinate test against the joint density
equals integration against its marginal density, by the proved coordinate split. -/
theorem lintegral_candidate_retained (k m : ℕ) (hn : 0 < k + m)
    (f : (Fin k → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ A, ENNReal.ofReal (determinantDensity (k + m) (k + m : ℕ) A) *
      f (retainedSpectrum k m A)) =
        ∫⁻ z, ENNReal.ofReal (ginibreMarginalDensity k m z) * f z := by
  have ha : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by exact_mod_cast hn
  have hD := measurable_determinantDensity (k + m) ha
  have hH : Measurable (fun A : Fin (k + m) → ℂ =>
      ENNReal.ofReal (determinantDensity (k + m) (k + m : ℕ) A) *
        f (retainedSpectrum k m A)) :=
    hD.ennreal_ofReal.mul (hf.comp (measurable_retainedSpectrum k m))
  rw [lintegral_marginalProduct k m _ hH]
  apply lintegral_congr
  intro z
  simp_rw [retainedSpectrum_prepend]
  have hm : Measurable (fun w : Fin m → ℂ => ENNReal.ofReal
      (determinantDensity (k + m) (k + m : ℕ) (prependPoints k m w z))) :=
    (hD.comp (continuous_prependPoints k m z).measurable).ennreal_ofReal
  rw [lintegral_mul_const (f z) hm, lintegral_determinantDensity_prepend]

/-- BC12 the genuine law of the retained actual eigenvalues. -/
def gaussianRetainedSpectralLaw (k m : ℕ) : Measure (Fin k → ℂ) :=
  (gaussianLabelledSpectralLaw (k + m) (k + m : ℕ)).map (retainedSpectrum k m)

/-- **BC12 actual retained-eigenvalue integral identity**, for every
nonnegative measurable test, with no integrability restriction. -/
theorem lintegral_gaussianRetainedSpectralLaw (k m : ℕ) (hn : 0 < k + m)
    (f : (Fin k → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂gaussianRetainedSpectralLaw k m =
      ∫⁻ z, ENNReal.ofReal (ginibreMarginalDensity k m z) * f z := by
  have ha : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by exact_mod_cast hn
  rw [gaussianRetainedSpectralLaw, lintegral_map hf (measurable_retainedSpectrum k m),
    gaussianLabelledSpectralLaw_eq_withDensity (k + m) ha]
  have h := lintegral_withDensity_eq_lintegral_mul volume
    (measurable_determinantDensity (k + m) ha).ennreal_ofReal
    (hf.comp (measurable_retainedSpectrum k m))
  calc
    _ = ∫⁻ A, ENNReal.ofReal (determinantDensity (k + m) (k + m : ℕ) A) *
        f (retainedSpectrum k m A) := by
      simpa only [Pi.mul_apply, Function.comp_apply] using! h
    _ = _ := lintegral_candidate_retained k m hn f hf

/-- **BC12 actual `k`-label marginal law**, not merely a formal integral of a candidate. -/
theorem gaussianRetainedSpectralLaw_eq_withDensity (k m : ℕ) (hn : 0 < k + m) :
    gaussianRetainedSpectralLaw k m = volume.withDensity
      (fun z => ENNReal.ofReal (ginibreMarginalDensity k m z)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_gaussianRetainedSpectralLaw k m hn f hf]
  exact (lintegral_withDensity_eq_lintegral_mul volume
    (measurable_ginibreMarginalDensity k m).ennreal_ofReal hf).symm

/-- BC12 the standard factorial correlation measure of an exchangeably
labelled `k+m` point spectrum is `n!/m!` times its `k`-label marginal. -/
def ginibreFactorialCorrelationMeasure (k m : ℕ) : Measure (Fin k → ℂ) :=
  ENNReal.ofReal ((Nat.factorial (k + m) : ℝ) / (Nat.factorial m : ℝ)) •
    gaussianRetainedSpectralLaw k m

/-- BC12 the scalar factorial normalization cancels the marginal factor exactly. -/
theorem factorial_mul_ginibreMarginalDensity (k m : ℕ) (z : Fin k → ℂ) :
    ((Nat.factorial (k + m) : ℝ) / (Nat.factorial m : ℝ)) * ginibreMarginalDensity k m z =
      (kernelDet (kernel (k + m)) k z).re := by
  have hm : (Nat.factorial m : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (Nat.factorial (k + m) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + m)
  unfold ginibreMarginalDensity
  field_simp

/-- **BC12 Theorem 3.3 at measure level**: the actual factorial-scaled
spectral marginal has density equal to the Ginibre kernel determinant. -/
theorem ginibreFactorialCorrelationMeasure_eq_kernelDensity (k m : ℕ) (hn : 0 < k + m) :
    ginibreFactorialCorrelationMeasure k m = volume.withDensity
      (fun z => ENNReal.ofReal (kernelDet (kernel (k + m)) k z).re) := by
  have hc : 0 ≤ (Nat.factorial (k + m) : ℝ) / (Nat.factorial m : ℝ) := by positivity
  apply Measure.ext_of_lintegral
  intro f hf
  rw [ginibreFactorialCorrelationMeasure, lintegral_smul_measure,
    lintegral_gaussianRetainedSpectralLaw k m hn f hf]
  simp only [smul_eq_mul]
  have hw : Measurable (fun z : Fin k → ℂ => ENNReal.ofReal (kernelDet (kernel (k + m)) k z).re) :=
    (Complex.continuous_re.comp (continuous_kernelDet (k + m) k)).measurable.ennreal_ofReal
  calc
    _ = ∫⁻ z, ENNReal.ofReal ((Nat.factorial (k + m) : ℝ) / (Nat.factorial m : ℝ)) *
        (ENNReal.ofReal (ginibreMarginalDensity k m z) * f z) :=
      (lintegral_const_mul _ ((measurable_ginibreMarginalDensity k m).ennreal_ofReal.mul hf)).symm
    _ = ∫⁻ z, ENNReal.ofReal (kernelDet (kernel (k + m)) k z).re * f z := by
      apply lintegral_congr
      intro z
      rw [← mul_assoc, ← ENNReal.ofReal_mul hc, factorial_mul_ginibreMarginalDensity]
    _ = _ := (lintegral_withDensity_eq_lintegral_mul volume hw hf).symm

end Ginibre
