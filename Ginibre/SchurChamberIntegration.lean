import Ginibre.SchurPermutations

/-!
# Integrating over all label chambers

BC12 Theorem 3.2: the finitely many ordered chambers partition every
distinct spectral tuple. The Vandermonde factor vanishes elsewhere.
Coordinate permutations preserve Lebesgue volume, so a symmetric
spectral integral is exactly `n!` times its ordered-chamber integral.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Ginibre

/-- BC12 the chamber selected by a specified label ordering. -/
def schurPermutedChamber {n : ℕ} (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℂ) :=
  (schurPermute σ) ⁻¹' schurSpectralChamber n

/-- BC12 all ordering chambers are Borel. -/
theorem measurableSet_schurPermutedChamber {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (schurPermutedChamber σ) :=
  (measurableSet_schurSpectralChamber n).preimage (schurPermute σ).measurable

/-- BC12 distinct label orderings give disjoint chambers. -/
theorem pairwise_schurPermutedChamber (n : ℕ) :
    Pairwise (fun σ τ : Equiv.Perm (Fin n) =>
      Disjoint (schurPermutedChamber σ) (schurPermutedChamber τ)) := by
  intro σ τ hst
  apply Set.disjoint_left.mpr
  intro z hs ht
  apply hst
  apply schurOrderingPermutation_unique z σ τ
  · simpa only [schurPermutedChamber, Set.mem_preimage, schurPermute_apply,
      schurSpectralChamber, Set.mem_ofPred_eq] using hs
  · simpa only [schurPermutedChamber, Set.mem_preimage, schurPermute_apply,
      schurSpectralChamber, Set.mem_ofPred_eq] using ht

/-- BC12 the ordering chambers cover every distinct spectral tuple. -/
theorem injective_mem_iUnion_schurPermutedChamber {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) : z ∈ ⋃ σ : Equiv.Perm (Fin n), schurPermutedChamber σ := by
  obtain ⟨σ, hσ⟩ := exists_schurOrderingPermutation z hz
  refine Set.mem_iUnion_of_mem σ ?_
  simpa only [schurPermutedChamber, Set.mem_preimage, schurPermute_apply,
    schurSpectralChamber, Set.mem_ofPred_eq] using hσ

/-- BC12 a symmetric spectral integral is identical on each permuted chamber. -/
theorem lintegral_schurPermutedChamber_symmetric (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ≥0∞)
    (hf : ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂ), f (fun i => z (σ i)) = f z)
    (σ : Equiv.Perm (Fin n)) :
    (∫⁻ z in schurPermutedChamber σ, ENNReal.ofReal (schurSpectralWeight n a z) * f z) =
      ∫⁻ z in schurSpectralChamber n, ENNReal.ofReal (schurSpectralWeight n a z) * f z := by
  have hp := (schurPermute_measurePreserving σ).restrict_preimage_emb
    (schurPermute σ).measurableEmbedding (schurSpectralChamber n)
  have h := hp.lintegral_comp_emb (schurPermute σ).measurableEmbedding
    (fun z => ENNReal.ofReal (schurSpectralWeight n a z) * f z)
  simpa only [schurPermutedChamber, schurPermute_apply, schurSpectralWeight_permute n ha, hf σ] using! h

/-- BC12 tuples outside all ordered chambers contribute zero, even for
infinite nonnegative tests, because the Vandermonde square vanishes there. -/
theorem lintegral_schurWeight_eq_iUnion_chambers (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ≥0∞) :
    (∫⁻ z, ENNReal.ofReal (schurSpectralWeight n a z) * f z) =
      ∫⁻ z in ⋃ σ : Equiv.Perm (Fin n), schurPermutedChamber σ,
        ENNReal.ofReal (schurSpectralWeight n a z) * f z := by
  classical
  let H := fun z => ENNReal.ofReal (schurSpectralWeight n a z) * f z
  let S := ⋃ σ : Equiv.Perm (Fin n), schurPermutedChamber σ
  have hI : S.indicator H = H := by
    funext z
    by_cases hz : z ∈ S
    · exact Set.indicator_of_mem hz H
    · have hn : ¬ Function.Injective z := fun hi => hz (injective_mem_iUnion_schurPermutedChamber z hi)
      rw [Set.indicator_of_notMem hz]
      simp only [H, schurSpectralWeight_eq_zero_of_not_injective n ha z hn,
        ENNReal.ofReal_zero, zero_mul]
  have hS : MeasurableSet S := MeasurableSet.iUnion measurableSet_schurPermutedChamber
  calc
    _ = ∫⁻ z, S.indicator H z := by rw [hI]
    _ = _ := lintegral_indicator hS H

/-- **BC12 exact factorial chamber multiplicity**, with volume preservation
and collision vanishing both proved rather than treated as a normalization input. -/
theorem lintegral_schurWeight_symmetric_eq_factorial_chamber (n : ℕ)
    {a : ℝ} (ha : 0 < a) (f : (Fin n → ℂ) → ℝ≥0∞)
    (hf : ∀ (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂ), f (fun i => z (σ i)) = f z) :
    (∫⁻ z, ENNReal.ofReal (schurSpectralWeight n a z) * f z) =
      (Nat.factorial n : ℝ≥0∞) *
        ∫⁻ z in schurSpectralChamber n, ENNReal.ofReal (schurSpectralWeight n a z) * f z := by
  classical
  rw [lintegral_schurWeight_eq_iUnion_chambers n ha f,
    lintegral_iUnion measurableSet_schurPermutedChamber (pairwise_schurPermutedChamber n)]
  simp_rw [lintegral_schurPermutedChamber_symmetric n ha f hf]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]

end Ginibre
