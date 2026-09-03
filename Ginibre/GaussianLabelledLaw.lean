import Ginibre.SpectralLabelAveraging

/-!
# Actual randomly labelled Ginibre eigenvalue law

BC12 Theorem 3.2. This law is a finite uniform mixture of permutations
of the actual ordered eigenvalues of the iid Gaussian matrix. Its
identification with the determinant density is proved below, not used
in its definition. Randomizing labels does not randomize or alter the
unordered spectrum.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- BC12 actual eigenvalues with uniform random labels, as a finite mixture of pushforwards. -/
def gaussianLabelledSpectralLaw (n : ℕ) (a : ℝ) : Measure (Fin n → ℂ) :=
  (Nat.factorial n : ℝ≥0∞)⁻¹ •
    ∑ σ : Equiv.Perm (Fin n), (gaussianOrderedSpectralLaw n a).map (schurPermute σ)

/-- BC12 the finite-mixture definition has exactly the uniform label-average integrals. -/
theorem lintegral_gaussianLabelledSpectralLaw (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂gaussianLabelledSpectralLaw n a =
      ∫⁻ A, schurLabelAverage n f (schurCoordinateSpectrum A) ∂gaussianCoordinateLaw n a := by
  have hm (σ : Equiv.Perm (Fin n)) :
      AEMeasurable (fun A : SchurTangent n => f (schurPermute σ (schurCoordinateSpectrum A)))
        (gaussianCoordinateLaw n a) :=
    (hf.comp (schurPermute σ).measurable).comp_aemeasurable (aemeasurable_schurCoordinateSpectrum n ha)
  have hmap (σ : Equiv.Perm (Fin n)) :
      (∫⁻ z, f z ∂(gaussianOrderedSpectralLaw n a).map (schurPermute σ)) =
        ∫⁻ A, f (schurPermute σ (schurCoordinateSpectrum A)) ∂gaussianCoordinateLaw n a := by
    rw [lintegral_map hf (schurPermute σ).measurable, gaussianOrderedSpectralLaw]
    simpa only [Function.comp_apply] using!
      lintegral_map' (hf.comp (schurPermute σ).measurable).aemeasurable
        (aemeasurable_schurCoordinateSpectrum n ha)
  rw [gaussianLabelledSpectralLaw, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [smul_eq_mul]
  simp_rw [hmap]
  change _ = ∫⁻ A, (Nat.factorial n : ℝ≥0∞)⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), f (schurPermute σ (schurCoordinateSpectrum A)) ∂gaussianCoordinateLaw n a
  rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum _ (fun σ _ => hm σ)),
    lintegral_finsetSum' _ (fun σ _ => hm σ)]

/-- **BC12 Theorem 3.2: the actual Gaussian matrix eigenvalue density**.
Every geometric, analytic, Gaussian, and label-accounting premise has
been proved internally. The only mathematical parameter restriction is `a > 0`. -/
theorem gaussianLabelledSpectralLaw_eq_withDensity (n : ℕ) {a : ℝ} (ha : 0 < a) :
    gaussianLabelledSpectralLaw n a = volume.withDensity
      (fun z => ENNReal.ofReal (determinantDensity n a z)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_gaussianLabelledSpectralLaw n ha f hf,
    lintegral_schurSpectrum_symmetric n ha _ (measurable_schurLabelAverage n f hf)
      (schurLabelAverage_symmetric n f), lintegral_candidate_labelAverage n ha f hf]
  exact (lintegral_withDensity_eq_lintegral_mul volume
    (measurable_determinantDensity n ha).ennreal_ofReal hf).symm

/-- BC12 the joint eigenvalue law has total probability one. -/
theorem gaussianLabelledSpectralLaw_isProbability (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (gaussianLabelledSpectralLaw n a) := by
  constructor
  rw [gaussianLabelledSpectralLaw_eq_withDensity n ha, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_determinantDensity n ha)
    (Filter.Eventually.of_forall (determinantDensity_nonneg n a)),
    integral_determinantDensity n ha, ENNReal.ofReal_one]

/-- BC12 the constructed actual labelled spectrum is exchangeable;
label symmetry is a proved property, not a marginal-law premise. -/
theorem gaussianLabelledSpectralLaw_permute (n : ℕ) {a : ℝ} (ha : 0 < a)
    (σ : Equiv.Perm (Fin n)) :
    (gaussianLabelledSpectralLaw n a).map (schurPermute σ) = gaussianLabelledSpectralLaw n a := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (schurPermute σ).measurable, gaussianLabelledSpectralLaw_eq_withDensity n ha]
  have hd := (measurable_determinantDensity n ha).ennreal_ofReal
  calc
    _ = ∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * f (schurPermute σ z) := by
      simpa only [Pi.mul_apply, Function.comp_apply] using!
        lintegral_withDensity_eq_lintegral_mul volume hd (hf.comp (schurPermute σ).measurable)
    _ = ∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * f z := lintegral_candidate_permute n a f σ
    _ = _ := (lintegral_withDensity_eq_lintegral_mul volume hd hf).symm

/-- BC12 finite relabelling leaves the actual characteristic-root multiset unchanged. -/
theorem charpoly_eq_prod_permuted_schurSpectrum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.charpoly.Separable) (σ : Equiv.Perm (Fin n)) :
    A.charpoly = ∏ i : Fin n, (Polynomial.X - Polynomial.C (schurPermute σ (schurSpectrum A) i)) := by
  rw [charpoly_eq_prod_schurSpectrum A hA, schurPermute_apply]
  exact (Equiv.prod_comp σ (fun i => Polynomial.X - Polynomial.C (schurSpectrum A i))).symm

end Ginibre
