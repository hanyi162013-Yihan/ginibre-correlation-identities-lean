import Ginibre.ActualMarginals

/-!
# Signed integrals of the actual Gaussian spectrum

BC12 Theorems 3.2--3.4, passage from probability laws to linear statistics.
All changes of measure use the already proved actual spectral laws.
Integrability equivalences are separate from integral equalities, so the
Bochner integral's value-zero convention cannot conceal a missing L1 proof.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- BC12 positivity of the actual labelled marginal density. -/
theorem ginibreMarginalDensity_nonneg (k m : ℕ) (z : Fin k → ℂ) :
    0 ≤ ginibreMarginalDensity k m z := by
  unfold ginibreMarginalDensity
  rw [← norm_kernelDet]
  positivity

/-- BC12 signed integration against the actual retained eigenvalue law. -/
theorem integral_gaussianRetainedSpectralLaw (k m : ℕ) (hn : 0 < k + m)
    (f : (Fin k → ℂ) → ℝ) :
    (∫ z, f z ∂gaussianRetainedSpectralLaw k m) =
      ∫ z, f z * ginibreMarginalDensity k m z := by
  rw [gaussianRetainedSpectralLaw_eq_withDensity k m hn,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_ginibreMarginalDensity k m).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (ginibreMarginalDensity_nonneg k m _), smul_eq_mul, mul_comm]

/-- BC12 genuine L1 criterion for a signed retained-eigenvalue test. -/
theorem integrable_gaussianRetainedSpectralLaw_iff (k m : ℕ) (hn : 0 < k + m)
    (f : (Fin k → ℂ) → ℝ) :
    Integrable f (gaussianRetainedSpectralLaw k m) ↔
      Integrable (fun z => f z * ginibreMarginalDensity k m z) := by
  rw [gaussianRetainedSpectralLaw_eq_withDensity k m hn,
    integrable_withDensity_iff_integrable_smul'
      (measurable_ginibreMarginalDensity k m).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (ginibreMarginalDensity_nonneg k m _), smul_eq_mul, mul_comm]

/-- BC12 signed integration against the actual uniformly labelled full spectrum. -/
theorem integral_gaussianLabelledSpectralLaw (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ) :
    (∫ z, f z ∂gaussianLabelledSpectralLaw n a) =
      ∫ z, f z * determinantDensity n a z := by
  rw [gaussianLabelledSpectralLaw_eq_withDensity n ha,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_determinantDensity n ha).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (determinantDensity_nonneg n a _), smul_eq_mul, mul_comm]

/-- BC12 the actual ordered spectrum is a.e. measurable in raw iid entry coordinates. -/
theorem aemeasurable_gaussianMatrix_spectrum (n : ℕ) {a : ℝ} (ha : 0 < a) :
    AEMeasurable (fun A : Fin n × Fin n → ℂ => schurSpectrum (Matrix.of A.curry))
      (gaussianMatrixLaw n a) := by
  have h : AEMeasurable (schurCoordinateSpectrum : SchurTangent n → Fin n → ℂ)
      ((gaussianMatrixLaw n a).map (schurFlatEntryMeasurableEquiv n)) :=
    aemeasurable_schurCoordinateSpectrum n ha
  have he : (fun A : Fin n × Fin n → ℂ => schurSpectrum (Matrix.of A.curry)) =
      schurCoordinateSpectrum ∘ schurFlatEntryMeasurableEquiv n := by
    funext A
    exact (schurCoordinateSpectrum_flatEntry n A).symm
  rw [he]
  exact h.comp_measurable (schurFlatEntryMeasurableEquiv n).measurable

/-- BC12 any measurable symmetric real statistic has the same distribution
on the actual matrix and on its uniformly labelled eigenvalues. -/
theorem gaussianMatrix_symmetric_statistic_map (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ) (hf : Measurable f)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) z, f (fun i => z (σ i)) = f z) :
    (gaussianMatrixLaw n a).map (fun A => f (schurSpectrum (Matrix.of A.curry))) =
      (gaussianLabelledSpectralLaw n a).map f := by
  apply Measure.ext_of_lintegral
  intro g hg
  have hF : AEMeasurable (fun A : Fin n × Fin n → ℂ =>
      f (schurSpectrum (Matrix.of A.curry))) (gaussianMatrixLaw n a) :=
    hf.comp_aemeasurable (aemeasurable_gaussianMatrix_spectrum n ha)
  rw [lintegral_map' hg.aemeasurable hF, lintegral_map hg hf,
    gaussianLabelledSpectralLaw_eq_withDensity n ha]
  have h := lintegral_gaussianMatrix_symmetric_spectrum n ha (fun z => g (f z))
    (hg.comp hf) (fun σ z => congrArg g (hsym σ z))
  calc
    _ = ∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * g (f z) := h
    _ = _ := by
      simpa only [Pi.mul_apply, Function.comp_apply] using!
        (lintegral_withDensity_eq_lintegral_mul volume
          (measurable_determinantDensity n ha).ennreal_ofReal (hg.comp hf)).symm

/-- BC12 signed symmetric-statistic integration is transported to actual matrices. -/
theorem integral_gaussianMatrix_symmetric (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ) (hf : Measurable f)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) z, f (fun i => z (σ i)) = f z) :
    (∫ A, f (schurSpectrum (Matrix.of A.curry)) ∂gaussianMatrixLaw n a) =
      ∫ z, f z ∂gaussianLabelledSpectralLaw n a := by
  have h := gaussianMatrix_symmetric_statistic_map n ha f hf hsym
  have hF : AEMeasurable (fun A : Fin n × Fin n → ℂ =>
      f (schurSpectrum (Matrix.of A.curry))) (gaussianMatrixLaw n a) :=
    hf.comp_aemeasurable (aemeasurable_gaussianMatrix_spectrum n ha)
  have he := congrArg (fun μ : Measure ℝ => ∫ t, t ∂μ) h
  rw [integral_map (f := fun t : ℝ => t) hF aestronglyMeasurable_id,
    integral_map (f := fun t : ℝ => t) hf.aemeasurable aestronglyMeasurable_id] at he
  exact he

/-- BC12 L1 transport is proved too, not inferred from an integral equality. -/
theorem integrable_gaussianMatrix_symmetric_iff (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ) (hf : Measurable f)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) z, f (fun i => z (σ i)) = f z) :
    Integrable (fun A => f (schurSpectrum (Matrix.of A.curry))) (gaussianMatrixLaw n a) ↔
      Integrable f (gaussianLabelledSpectralLaw n a) := by
  have h := gaussianMatrix_symmetric_statistic_map n ha f hf hsym
  have hF : AEMeasurable (fun A : Fin n × Fin n → ℂ =>
      f (schurSpectrum (Matrix.of A.curry))) (gaussianMatrixLaw n a) :=
    hf.comp_aemeasurable (aemeasurable_gaussianMatrix_spectrum n ha)
  have he := congrArg (fun μ : Measure ℝ => Integrable id μ) h
  simp only [integrable_map_measure aestronglyMeasurable_id hF,
    integrable_map_measure aestronglyMeasurable_id hf.aemeasurable, Function.id_comp] at he
  exact iff_of_eq he

end Ginibre
