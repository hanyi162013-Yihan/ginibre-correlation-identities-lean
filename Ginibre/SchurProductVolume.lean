import Ginibre.SchurProductEntries
import Ginibre.SchurLocalIntegration
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual Schur coordinate volume is a product volume

HKPV (6.3.4)--(6.3.5): connect the exact permutation of matrix-entry
Lebesgue measure with the coordinates used in the actual local Jacobian
theorem. No volume normalization or auxiliary integral is assumed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV fixed linear coordinate split, as a measurable equivalence. -/
def schurFlatEntryMeasurableEquiv (n : ℕ) :
    (Fin n × Fin n → ℂ) ≃ᵐ SchurTangent n :=
  (schurFlatEntryEquiv n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

/-- HKPV the transported volume is exactly the measure used in local
change of variables, with no undetermined scalar. -/
theorem schurFlatEntryMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (schurFlatEntryMeasurableEquiv n) volume (schurCoordinateVolume n) :=
  ⟨(schurFlatEntryMeasurableEquiv n).measurable, rfl⟩

/-- HKPV angular, diagonal, and strictly upper coordinates of the actual
real parameter space. This map is fixed and linear, not a spectral map. -/
def schurProductEquiv (n : ℕ) : SchurTangent n ≃ᵐ SchurProductCoordinates n :=
  (schurFlatEntryMeasurableEquiv n).symm.trans (schurFlatProductEquiv n)

/-- HKPV this decomposition preserves the concrete coordinate volume. -/
theorem schurProductEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (schurProductEquiv n) (schurCoordinateVolume n) volume :=
  (MeasurePreserving.symm _ (schurFlatEntryMeasurableEquiv_measurePreserving n)).trans
    (schurFlatProductEquiv_measurePreserving n)

/-- HKPV reading the angular coordinates does not involve the triangular factor. -/
theorem schurProductEquiv_lower {n : ℕ} (x : SchurTangent n) :
    (schurProductEquiv n x).1 = x.1 := by
  funext p
  change (schurFlatProductEquiv n ((schurFlatEntryMeasurableEquiv n).symm x)).1 p = _
  rw [schurFlatProductEquiv_lower]
  change (schurLowerEmbed x.1 + x.2.val) (schurRow p) (schurCol p) = x.1 p
  have hz : x.2.val (schurRow p) (schurCol p) = 0 := x.2.property p.property
  rw [Matrix.add_apply, schurLowerEmbed_apply_lower, hz, add_zero]

/-- HKPV the second product coordinate is the actual triangular diagonal. -/
theorem schurProductEquiv_diagonal {n : ℕ} (x : SchurTangent n) (i : Fin n) :
    (schurProductEquiv n x).2.1 i = x.2.val i i := by
  change (schurFlatProductEquiv n ((schurFlatEntryMeasurableEquiv n).symm x)).2.1 i = _
  rw [schurFlatProductEquiv_diagonal]
  change (schurLowerEmbed x.1 + x.2.val) i i = x.2.val i i
  rw [Matrix.add_apply, schurLowerEmbed_apply_of_le _ _ _ le_rfl, zero_add]

/-- HKPV the third product coordinate is the actual strict-upper entry array. -/
theorem schurProductEquiv_upper {n : ℕ} (x : SchurTangent n) (p : SchurLower n) :
    (schurProductEquiv n x).2.2 p = x.2.val (schurCol p) (schurRow p) := by
  change (schurFlatProductEquiv n ((schurFlatEntryMeasurableEquiv n).symm x)).2.2 p = _
  rw [schurFlatProductEquiv_upper]
  change (schurLowerEmbed x.1 + x.2.val) (schurCol p) (schurRow p) = _
  have hz : schurLowerEmbed x.1 (schurCol p) (schurRow p) = 0 :=
    schurLowerEmbed_apply_of_le x.1 (schurCol p) (schurRow p) p.property.le
  rw [Matrix.add_apply, hz, zero_add]

/-- **HKPV exact nonnegative product-volume integration**. This transports
arbitrary nonnegative integrands, so no hidden integrability assumption
can mask a missing normalization argument. -/
theorem lintegral_schurProductCoordinates {n : ℕ} (f : SchurTangent n → ℝ≥0∞) :
    ∫⁻ x, f x ∂schurCoordinateVolume n =
      ∫⁻ y : SchurProductCoordinates n, f ((schurProductEquiv n).symm y) := by
  exact ((MeasurePreserving.symm _ (schurProductEquiv_measurePreserving n)).lintegral_comp_emb
    (schurProductEquiv n).symm.measurableEmbedding f).symm

/-- HKPV Tonelli in the actual angular/diagonal/strict-upper coordinates,
with only ordinary measurability of the chosen nonnegative integrand. -/
theorem lintegral_schurProductCoordinates_iterated {n : ℕ}
    (f : SchurTangent n → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂schurCoordinateVolume n =
      ∫⁻ w : SchurLower n → ℂ, ∫⁻ z : Fin n → ℂ, ∫⁻ t : SchurLower n → ℂ,
        f ((schurProductEquiv n).symm (w, z, t)) := by
  rw [lintegral_schurProductCoordinates]
  have hm := hf.comp (schurProductEquiv n).symm.measurable
  calc
    _ = ∫⁻ w : SchurLower n → ℂ,
        ∫⁻ u : (Fin n → ℂ) × (SchurLower n → ℂ),
          f ((schurProductEquiv n).symm (w, u)) :=
      lintegral_prod _ hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro w
      exact lintegral_prod _ (hm.comp measurable_prodMk_left).aemeasurable

end Ginibre
