import Ginibre.FiniteMarginals
import Ginibre.SchurProductVolume

/-!
# Concrete product coordinates for spectral marginals

BC12 Theorem 3.3. The recursive prefix convention used in the proved
determinant marginal formula is an actual permutation of coordinate
Lebesgue measure. This supplies the measure-theoretic, not just pointwise,
connection between the joint density and the retained eigenvalue law.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Ginibre

/-- BC12 index of an integrated prefix coordinate. -/
def marginalPrefixIndex (k m : ℕ) (i : Fin m) : Fin (k + m) := ⟨i.val, by omega⟩

/-- BC12 index of a retained spectral coordinate. -/
def marginalRetainedIndex (k m : ℕ) (i : Fin k) : Fin (k + m) := ⟨m + i.val, by omega⟩

/-- BC12 recursive prefixing reads back the integrated coordinates. -/
theorem prependPoints_prefix (k m : ℕ) (w : Fin m → ℂ) (z : Fin k → ℂ) (i : Fin m) :
    prependPoints k m w z (marginalPrefixIndex k m i) = w i := by
  revert w i
  induction m with
  | zero => intro w i; exact Fin.elim0 i
  | succ m ih =>
    intro w i
    refine Fin.cases ?_ (fun j => ?_) i
    · have he : marginalPrefixIndex k (m + 1) 0 = 0 := Fin.ext rfl
      rw [he, prependPoints, Fin.cons_zero]
    · have he : marginalPrefixIndex k (m + 1) j.succ = (marginalPrefixIndex k m j).succ := Fin.ext rfl
      rw [he, prependPoints, Fin.cons_succ]
      exact ih (Fin.tail w) j

/-- BC12 recursive prefixing reads back the retained coordinates. -/
theorem prependPoints_retained (k m : ℕ) (w : Fin m → ℂ) (z : Fin k → ℂ) (i : Fin k) :
    prependPoints k m w z (marginalRetainedIndex k m i) = z i := by
  revert w
  induction m with
  | zero =>
    intro w
    have he : marginalRetainedIndex k 0 i = i := Fin.ext (Nat.zero_add _)
    rw [he]
    rfl
  | succ m ih =>
    intro w
    have he : marginalRetainedIndex k (m + 1) i = (marginalRetainedIndex k m i).succ := by
      apply Fin.ext
      dsimp only [marginalRetainedIndex, Fin.val_succ]
      omega
    rw [he, prependPoints, Fin.cons_succ]
    exact ih (Fin.tail w)

/-- BC12 the combined index address. -/
def marginalIndexAddress (k m : ℕ) : Fin m ⊕ Fin k → Fin (k + m) :=
  Sum.elim (marginalPrefixIndex k m) (marginalRetainedIndex k m)

/-- BC12 no entry is duplicated in the product-coordinate split. -/
theorem marginalIndexAddress_injective (k m : ℕ) : Function.Injective (marginalIndexAddress k m) := by
  intro p q h
  have hv := congrArg Fin.val h
  rcases p with i | i <;> rcases q with j | j
  · exact congrArg Sum.inl (Fin.ext hv)
  · dsimp only [marginalIndexAddress, Sum.elim, marginalPrefixIndex, marginalRetainedIndex] at hv
    have hi := i.isLt
    omega
  · dsimp only [marginalIndexAddress, Sum.elim, marginalPrefixIndex, marginalRetainedIndex] at hv
    have hj := j.isLt
    omega
  · apply congrArg Sum.inr
    apply Fin.ext
    dsimp only [marginalIndexAddress, Sum.elim, marginalRetainedIndex] at hv
    omega

/-- BC12 every entry belongs to the prefix or the retained block. -/
theorem marginalIndexAddress_surjective (k m : ℕ) : Function.Surjective (marginalIndexAddress k m) := by
  intro i
  by_cases hi : i.val < m
  · exact ⟨.inl ⟨i.val, hi⟩, Fin.ext rfl⟩
  · refine ⟨.inr ⟨i.val - m, by have hil := i.isLt; omega⟩, ?_⟩
    apply Fin.ext
    dsimp only [marginalIndexAddress, Sum.elim, marginalRetainedIndex]
    omega

/-- BC12 the actual finite index permutation behind marginal integration. -/
def marginalIndexEquiv (k m : ℕ) : Fin m ⊕ Fin k ≃ Fin (k + m) :=
  Equiv.ofBijective (marginalIndexAddress k m)
    ⟨marginalIndexAddress_injective k m, marginalIndexAddress_surjective k m⟩

/-- BC12 split a labelled tuple into integrated and retained coordinates. -/
def marginalProductEquiv (k m : ℕ) :
    (Fin (k + m) → ℂ) ≃ᵐ ((Fin m → ℂ) × (Fin k → ℂ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin m ⊕ Fin k => ℂ) (marginalIndexEquiv k m).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin k => ℂ))

/-- BC12 the first product block consists of the actual prefix entries. -/
theorem marginalProductEquiv_prefix (k m : ℕ) (A : Fin (k + m) → ℂ) (i : Fin m) :
    (marginalProductEquiv k m A).1 i = A (marginalPrefixIndex k m i) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin m ⊕ Fin k => ℂ)
    (marginalIndexEquiv k m).symm A (marginalIndexEquiv k m (.inl i))
  simpa only [Equiv.symm_apply_apply] using! h

/-- BC12 the second product block consists of the actual retained entries. -/
theorem marginalProductEquiv_retained (k m : ℕ) (A : Fin (k + m) → ℂ) (i : Fin k) :
    (marginalProductEquiv k m A).2 i = A (marginalRetainedIndex k m i) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin m ⊕ Fin k => ℂ)
    (marginalIndexEquiv k m).symm A (marginalIndexEquiv k m (.inr i))
  simpa only [Equiv.symm_apply_apply] using! h

/-- BC12 the inverse product split is exactly the previously integrated prefix map. -/
theorem marginalProductEquiv_symm (k m : ℕ) (w : Fin m → ℂ) (z : Fin k → ℂ) :
    (marginalProductEquiv k m).symm (w, z) = prependPoints k m w z := by
  apply (marginalProductEquiv k m).injective
  rw [MeasurableEquiv.apply_symm_apply]
  apply Prod.ext
  · funext i
    rw [marginalProductEquiv_prefix, prependPoints_prefix]
  · funext i
    rw [marginalProductEquiv_retained, prependPoints_retained]

/-- BC12 the marginal split preserves ordinary product Lebesgue measure exactly. -/
theorem marginalProductEquiv_measurePreserving (k m : ℕ) :
    MeasurePreserving (marginalProductEquiv k m) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin k => ℂ)).comp
    (volume_measurePreserving_piCongrLeft (fun _ : Fin m ⊕ Fin k => ℂ) (marginalIndexEquiv k m).symm)

/-- **BC12 genuine Fubini identity for the marginal convention**. This
justifies integrating the joint spectral density over the discarded labels. -/
theorem lintegral_marginalProduct (k m : ℕ) (H : (Fin (k + m) → ℂ) → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ A, H A) = ∫⁻ z : Fin k → ℂ, ∫⁻ w : Fin m → ℂ, H (prependPoints k m w z) := by
  have hp := MeasurePreserving.symm _ (marginalProductEquiv_measurePreserving k m)
  calc
    _ = ∫⁻ p : (Fin m → ℂ) × (Fin k → ℂ), H ((marginalProductEquiv k m).symm p) :=
      (hp.lintegral_comp_emb (marginalProductEquiv k m).symm.measurableEmbedding H).symm
    _ = ∫⁻ z : Fin k → ℂ, ∫⁻ w : Fin m → ℂ, H ((marginalProductEquiv k m).symm (w, z)) :=
      lintegral_prod_symm _ (hH.comp (marginalProductEquiv k m).symm.measurable).aemeasurable
    _ = _ := by simp only [marginalProductEquiv_symm]

end Ginibre
