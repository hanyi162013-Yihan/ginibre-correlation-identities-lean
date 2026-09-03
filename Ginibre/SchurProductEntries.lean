import Ginibre.SchurEntrySplit
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Exact product volume for split Schur entry coordinates

HKPV (6.3.4)--(6.3.5), separating ordinary coordinate volume before
integrating the Gaussian factors. This is a permutation of the original
complex matrix entries into lower, diagonal, and strictly upper entries.
It therefore preserves ordinary product Lebesgue measure exactly, without
an unknown scalar or a postulated coordinate-volume identity.
-/

noncomputable section
open OrderDual MeasureTheory
namespace Ginibre

/-- HKPV three disjoint kinds of complex matrix entry. -/
abbrev SchurEntryIndex (n : ℕ) := SchurLower n ⊕ (Fin n ⊕ SchurLower n)

/-- HKPV the original matrix location of each split coordinate. -/
def schurEntryAddress {n : ℕ} : SchurEntryIndex n → Fin n × Fin n
  | .inl p => (schurRow p, schurCol p)
  | .inr (.inl i) => (i, i)
  | .inr (.inr p) => (schurCol p, schurRow p)

/-- HKPV no matrix entry is counted twice in the coordinate split. -/
theorem schurEntryAddress_injective (n : ℕ) : Function.Injective (@schurEntryAddress n) := by
  rintro (p | (i | p)) (q | (j | q)) h
  all_goals simp only [schurEntryAddress, Prod.mk.injEq] at h
  · exact congrArg Sum.inl (schurLower_ext h.1 h.2)
  · have hp : schurCol p < schurRow p := p.property
    omega
  · have hp : schurCol p < schurRow p := p.property
    have hq : schurCol q < schurRow q := q.property
    omega
  · have hq : schurCol q < schurRow q := q.property
    omega
  · exact congrArg (fun i => Sum.inr (Sum.inl i)) h.1
  · have hq : schurCol q < schurRow q := q.property
    omega
  · have hp : schurCol p < schurRow p := p.property
    have hq : schurCol q < schurRow q := q.property
    omega
  · have hp : schurCol p < schurRow p := p.property
    omega
  · exact congrArg (fun p => Sum.inr (Sum.inr p)) (schurLower_ext h.2 h.1)

/-- HKPV every matrix entry is lower, diagonal, or strictly upper. -/
theorem schurEntryAddress_surjective (n : ℕ) : Function.Surjective (@schurEntryAddress n) := by
  rintro ⟨i, j⟩
  rcases lt_trichotomy i j with h | h | h
  · exact ⟨.inr (.inr ⟨toLex (toDual j, i), h⟩), rfl⟩
  · subst j
    exact ⟨.inr (.inl i), rfl⟩
  · exact ⟨.inl ⟨toLex (toDual i, j), h⟩, rfl⟩

/-- HKPV finite permutation underlying the coordinate-volume split. -/
def schurEntryIndexEquiv (n : ℕ) : SchurEntryIndex n ≃ (Fin n × Fin n) :=
  Equiv.ofBijective schurEntryAddress
    ⟨schurEntryAddress_injective n, schurEntryAddress_surjective n⟩

/-- HKPV independent lower, diagonal, and strict-upper coordinate arrays. -/
abbrev SchurProductCoordinates (n : ℕ) :=
  (SchurLower n → ℂ) × ((Fin n → ℂ) × (SchurLower n → ℂ))

/-- HKPV fixed measurable entry reordering, not the nonlinear Schur map. -/
def schurFlatProductEquiv (n : ℕ) :
    (Fin n × Fin n → ℂ) ≃ᵐ SchurProductCoordinates n :=
  (MeasurableEquiv.piCongrLeft (fun _ : SchurEntryIndex n => ℂ)
      (schurEntryIndexEquiv n).symm).trans
    ((MeasurableEquiv.sumPiEquivProdPi (fun _ : SchurEntryIndex n => ℂ)).trans
      ((MeasurableEquiv.refl (SchurLower n → ℂ)).prodCongr
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ SchurLower n => ℂ))))

/-- HKPV the first coordinate array is the actual lower matrix entries. -/
theorem schurFlatProductEquiv_lower {n : ℕ} (A : Fin n × Fin n → ℂ) (p : SchurLower n) :
    (schurFlatProductEquiv n A).1 p = A (schurRow p, schurCol p) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : SchurEntryIndex n => ℂ)
    (schurEntryIndexEquiv n).symm
    A (schurEntryIndexEquiv n (.inl p))
  simpa only [Equiv.symm_apply_apply] using! h

/-- HKPV the second coordinate array is the actual diagonal. -/
theorem schurFlatProductEquiv_diagonal {n : ℕ} (A : Fin n × Fin n → ℂ) (i : Fin n) :
    (schurFlatProductEquiv n A).2.1 i = A (i, i) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : SchurEntryIndex n => ℂ)
    (schurEntryIndexEquiv n).symm
    A (schurEntryIndexEquiv n (.inr (.inl i)))
  simpa only [Equiv.symm_apply_apply] using! h

/-- HKPV the third coordinate array is the actual strictly upper entries. -/
theorem schurFlatProductEquiv_upper {n : ℕ} (A : Fin n × Fin n → ℂ) (p : SchurLower n) :
    (schurFlatProductEquiv n A).2.2 p = A (schurCol p, schurRow p) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : SchurEntryIndex n => ℂ)
    (schurEntryIndexEquiv n).symm
    A (schurEntryIndexEquiv n (.inr (.inr p)))
  simpa only [Equiv.symm_apply_apply] using! h

/-- **HKPV exact product-volume decomposition for matrix entries**.
All three coordinate factors carry their usual complex Lebesgue product
measure; there is no unproved or undetermined normalization constant. -/
theorem schurFlatProductEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (schurFlatProductEquiv n)
      (volume : Measure (Fin n × Fin n → ℂ))
      (volume : Measure (SchurProductCoordinates n)) := by
  have h₁ := volume_measurePreserving_piCongrLeft (fun _ : SchurEntryIndex n => ℂ)
    (schurEntryIndexEquiv n).symm
  have h₂ := volume_measurePreserving_sumPiEquivProdPi (fun _ : SchurEntryIndex n => ℂ)
  have h₃ := (MeasurePreserving.id (volume : Measure (SchurLower n → ℂ))).prod
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ SchurLower n => ℂ))
  exact h₃.comp (h₂.comp h₁)

end Ginibre
