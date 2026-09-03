import Ginibre.SpectralIntegrals
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Correlations as actual sums over distinct eigenvalue indices

BC12 Theorem 3.3. The factorial correlation measure is connected to its
usual counting interpretation, not only to a scaled labelled marginal.
Signed tests are admitted under their genuine weighted L1 condition.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- BC12 read a tuple of pairwise distinct labels. -/
def selectedSpectrum {k n : ℕ} (e : Fin k ↪ Fin n) (z : Fin n → ℂ) : Fin k → ℂ :=
  fun i => z (e i)

/-- BC12 every finite label selection is measurable. -/
theorem measurable_selectedSpectrum {k n : ℕ} (e : Fin k ↪ Fin n) :
    Measurable (selectedSpectrum e) := measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))

/-- BC12 the retained-coordinate address is injective. -/
theorem marginalRetainedIndex_injective (k m : ℕ) :
    Function.Injective (marginalRetainedIndex k m) := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  exact Nat.add_left_cancel hv

/-- BC12 every distinct label tuple has exactly the proved retained marginal law. -/
theorem gaussianLabelled_selected_map (k m : ℕ) (hn : 0 < k + m)
    (e : Fin k ↪ Fin (k + m)) :
    (gaussianLabelledSpectralLaw (k + m) (k + m : ℕ)).map (selectedSpectrum e) =
      gaussianRetainedSpectralLaw k m := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (marginalRetainedIndex k m) e (marginalRetainedIndex_injective k m) e.injective
  have he : selectedSpectrum e = retainedSpectrum k m ∘ schurPermute σ := by
    funext z i
    change z (e i) = (marginalProductEquiv k m (schurPermute σ z)).2 i
    rw [marginalProductEquiv_retained, schurPermute_apply]
    change z (e i) = z (σ (marginalRetainedIndex k m i))
    rw [hσ]
  rw [he, ← Measure.map_map (measurable_retainedSpectrum k m) (schurPermute σ).measurable,
    gaussianLabelledSpectralLaw_permute (k + m) (by exact_mod_cast hn)]
  rfl

/-- BC12 signed selected-tuple integrals equal the same actual marginal integral. -/
theorem integral_gaussianLabelled_selected (k m : ℕ) (hn : 0 < k + m)
    (e : Fin k ↪ Fin (k + m)) (f : (Fin k → ℂ) → ℝ) (hf : Measurable f) :
    (∫ z, f (selectedSpectrum e z) ∂gaussianLabelledSpectralLaw (k + m) (k + m : ℕ)) =
      ∫ z, f z ∂gaussianRetainedSpectralLaw k m := by
  rw [← gaussianLabelled_selected_map k m hn e,
    integral_map (measurable_selectedSpectrum e).aemeasurable hf.aestronglyMeasurable]

/-- BC12 the same selected-tuple transport preserves L1. -/
theorem integrable_gaussianLabelled_selected_iff (k m : ℕ) (hn : 0 < k + m)
    (e : Fin k ↪ Fin (k + m)) (f : (Fin k → ℂ) → ℝ) (hf : Measurable f) :
    Integrable (fun z => f (selectedSpectrum e z))
      (gaussianLabelledSpectralLaw (k + m) (k + m : ℕ)) ↔
        Integrable f (gaussianRetainedSpectralLaw k m) := by
  rw [← gaussianLabelled_selected_map k m hn e]
  exact (integrable_map_measure hf.aestronglyMeasurable
    (measurable_selectedSpectrum e).aemeasurable).symm

/-- BC12 the exact number of ordered distinct label choices is n!/m!. -/
theorem card_spectralSelections (k m : ℕ) :
    (Fintype.card (Fin k ↪ Fin (k + m)) : ℝ) =
      (Nat.factorial (k + m) : ℝ) / (Nat.factorial m : ℝ) := by
  rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero m)).mpr
  have h := Nat.factorial_mul_descFactorial (n := k + m) (k := k) (by omega)
  have hs : k + m - k = m := by omega
  rw [hs, Nat.mul_comm] at h
  exact_mod_cast h

/-- BC12 the actual factorial statistic sums over all ordered distinct labels. -/
def factorialStatistic (k n : ℕ) (f : (Fin k → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  ∑ e : Fin k ↪ Fin n, f (selectedSpectrum e z)

/-- BC12 the finite factorial statistic is measurable. -/
theorem measurable_factorialStatistic (k n : ℕ) (f : (Fin k → ℂ) → ℝ) (hf : Measurable f) :
    Measurable (factorialStatistic k n f) :=
  Finset.measurable_fun_sum _ (fun e _ => hf.comp (measurable_selectedSpectrum e))

/-- BC12 counting distinct labels does not depend on the chosen spectral ordering. -/
theorem factorialStatistic_symmetric (k n : ℕ) (f : (Fin k → ℂ) → ℝ)
    (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂ) :
    factorialStatistic k n f (fun i => z (σ i)) = factorialStatistic k n f z := by
  have h := Equiv.sum_comp (Equiv.embeddingCongr (Equiv.refl (Fin k)) σ)
    (fun e : Fin k ↪ Fin n => f (selectedSpectrum e z))
  change (∑ e : Fin k ↪ Fin n, f (fun i => z (σ (e i)))) = _
  exact h

/-- BC12 weighted correlation integrability implies actual marginal integrability. -/
theorem integrable_marginal_of_kernelDet (k m : ℕ) (hn : 0 < k + m)
    (f : (Fin k → ℂ) → ℝ)
    (hi : Integrable (fun z => f z * (kernelDet (kernel (k + m)) k z).re)) :
    Integrable f (gaussianRetainedSpectralLaw k m) := by
  rw [integrable_gaussianRetainedSpectralLaw_iff k m hn f]
  apply (hi.const_mul ((Nat.factorial m : ℝ) / (Nat.factorial (k + m) : ℝ))).congr
  filter_upwards with z
  dsimp only [ginibreMarginalDensity]
  ring

/-- BC12 absolute integrability of the actual signed distinct-index sum. -/
theorem integrable_factorialStatistic (k m : ℕ) (hn : 0 < k + m)
    (f : (Fin k → ℂ) → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * (kernelDet (kernel (k + m)) k z).re)) :
    Integrable (factorialStatistic k (k + m) f)
      (gaussianLabelledSpectralLaw (k + m) (k + m : ℕ)) := by
  apply integrable_finsetSum
  intro e _
  exact (integrable_gaussianLabelled_selected_iff k m hn e f hf).mpr
    (integrable_marginal_of_kernelDet k m hn f hi)

/-- **BC12 signed factorial Campbell formula for the actual spectrum**,
with its weighted integrability premise rather than a correlation-law input. -/
theorem integral_factorialStatistic (k m : ℕ) (hn : 0 < k + m)
    (f : (Fin k → ℂ) → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * (kernelDet (kernel (k + m)) k z).re)) :
    (∫ z, factorialStatistic k (k + m) f z
      ∂gaussianLabelledSpectralLaw (k + m) (k + m : ℕ)) =
        ∫ z, f z * (kernelDet (kernel (k + m)) k z).re := by
  have hsel (e : Fin k ↪ Fin (k + m)) :=
    (integrable_gaussianLabelled_selected_iff k m hn e f hf).mpr
      (integrable_marginal_of_kernelDet k m hn f hi)
  change (∫ z, (∑ e : Fin k ↪ Fin (k + m), f (selectedSpectrum e z))
      ∂gaussianLabelledSpectralLaw (k + m) (k + m : ℕ)) = _
  rw [integral_finsetSum _ (fun e _ => hsel e)]
  simp_rw [integral_gaussianLabelled_selected k m hn _ f hf]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_spectralSelections,
    integral_gaussianRetainedSpectralLaw k m hn f, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  rw [mul_left_comm, factorial_mul_ginibreMarginalDensity]

/-- **BC12 distinct-index formula on the original Gaussian entry space**.
This closes the counting interpretation without an assumed point-process identity. -/
theorem gaussianMatrix_factorialStatistic (k m : ℕ) (hn : 0 < k + m)
    (f : (Fin k → ℂ) → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * (kernelDet (kernel (k + m)) k z).re)) :
    Integrable (fun A => factorialStatistic k (k + m) f (schurSpectrum (Matrix.of A.curry)))
      (gaussianMatrixLaw (k + m) (k + m : ℕ)) ∧
    (∫ A, factorialStatistic k (k + m) f (schurSpectrum (Matrix.of A.curry))
      ∂gaussianMatrixLaw (k + m) (k + m : ℕ)) =
        ∫ z, f z * (kernelDet (kernel (k + m)) k z).re := by
  have ha : (0 : ℝ) < ((k + m : ℕ) : ℝ) := by exact_mod_cast hn
  refine ⟨(integrable_gaussianMatrix_symmetric_iff (k + m) ha _
    (measurable_factorialStatistic k (k + m) f hf)
    (factorialStatistic_symmetric k (k + m) f)).mpr
      (integrable_factorialStatistic k m hn f hf hi), ?_⟩
  rw [integral_gaussianMatrix_symmetric (k + m) ha _
    (measurable_factorialStatistic k (k + m) f hf)
    (factorialStatistic_symmetric k (k + m) f)]
  exact integral_factorialStatistic k m hn f hf hi

end Ginibre
