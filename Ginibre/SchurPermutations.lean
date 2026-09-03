import Ginibre.SchurSeparatedIntegration

/-!
# Label permutation bookkeeping for the spectral chamber

BC12 Theorem 3.2: a sorted spectrum has density on one chamber, not
the symmetric density on all of complex coordinate space. These
lemmas prove invariance and collision vanishing needed to pass to
symmetric eigenvalue statistics without confusing the two laws.
-/

noncomputable section
open MeasureTheory
namespace Ginibre

/-- BC12 permuting eigenvalue labels leaves the squared Slater determinant unchanged. -/
theorem slater_norm_sq_permute {n : ℕ} {X : Type*} (φ : Fin n → X → ℂ)
    (z : Fin n → X) (σ : Equiv.Perm (Fin n)) :
    ‖slater φ (fun i => z (σ i))‖ ^ 2 = ‖slater φ z‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← det_finiteKernel_eq_slater_norm_sq, ← det_finiteKernel_eq_slater_norm_sq]
  exact Matrix.det_submatrix_equiv_self σ (fun i j => finiteKernel φ (z i) (z j))

/-- BC12 the candidate density is symmetric in all labels. -/
theorem determinantDensity_permute (n : ℕ) (a : ℝ) (z : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) :
    determinantDensity n a (fun i => z (σ i)) = determinantDensity n a z := by
  unfold determinantDensity
  rw [slater_norm_sq_permute]

/-- BC12 repeated spectral coordinates make the determinant density zero. -/
theorem determinantDensity_eq_zero_of_not_injective (n : ℕ) (a : ℝ)
    (z : Fin n → ℂ) (hz : ¬ Function.Injective z) : determinantDensity n a z = 0 := by
  classical
  obtain ⟨i, j, he, hij⟩ : ∃ i j, z i = z j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, _root_.not_imp, exists_prop] using hz
  have hd : slater (fun i : Fin n => gaussianBasis a i.val) z = 0 := by
    apply Matrix.det_zero_of_column_eq hij
    intro k
    rw [he]
  simp only [determinantDensity, hd, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]

/-- HKPV the actual diagonal Gaussian--Jacobian weight is label-invariant. -/
theorem schurSpectralWeight_permute (n : ℕ) {a : ℝ} (ha : 0 < a)
    (z : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) :
    schurSpectralWeight n a (fun i => z (σ i)) = schurSpectralWeight n a z := by
  rw [schurSpectralWeight_eq_inv_coefficient_mul_candidate n ha,
    schurSpectralWeight_eq_inv_coefficient_mul_candidate n ha, determinantDensity_permute]

/-- HKPV the actual diagonal weight vanishes on every collision tuple. -/
theorem schurSpectralWeight_eq_zero_of_not_injective (n : ℕ) {a : ℝ} (ha : 0 < a)
    (z : Fin n → ℂ) (hz : ¬ Function.Injective z) : schurSpectralWeight n a z = 0 := by
  rw [schurSpectralWeight_eq_inv_coefficient_mul_candidate n ha,
    determinantDensity_eq_zero_of_not_injective n a z hz, mul_zero]

/-- BC12 the actual measurable coordinate permutation. -/
def schurPermute {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℂ) σ.symm

/-- BC12 this equivalence is precisely relabelling, with no density transformation. -/
theorem schurPermute_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂ) :
    schurPermute σ z = fun i => z (σ i) := by
  funext i
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℂ)
    σ.symm z (σ i)
  simpa only [Equiv.symm_apply_apply] using! h

/-- BC12 all label permutations preserve the concrete product Lebesgue measure. -/
theorem schurPermute_measurePreserving {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (schurPermute σ) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℂ) σ.symm

/-- BC12 ordering after a permutation implies that the original tuple is distinct. -/
theorem injective_of_schurOrdered_permute {n : ℕ} (z : Fin n → ℂ)
    (σ : Equiv.Perm (Fin n)) (hz : schurDiagonalOrdered (fun i => z (σ i))) :
    Function.Injective z := by
  intro i j he
  apply σ.symm.injective
  apply schurDiagonalOrdered_injective hz
  simpa only [Equiv.apply_symm_apply] using he

/-- BC12 a distinct spectral tuple has at most one ordering permutation. -/
theorem schurOrderingPermutation_unique {n : ℕ} (z : Fin n → ℂ)
    (σ τ : Equiv.Perm (Fin n))
    (hs : schurDiagonalOrdered (fun i => z (σ i)))
    (ht : schurDiagonalOrdered (fun i => z (τ i))) : σ = τ := by
  have hz := injective_of_schurOrdered_permute z σ hs
  have hr : Set.range (fun i => z (σ i)) = Set.range (fun i => z (τ i)) := by
    change Set.range (z ∘ σ) = Set.range (z ∘ τ)
    simp only [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  have he := schurDiagonalOrdered_eq_of_range_eq hs ht hr
  apply Equiv.ext
  intro i
  exact hz (congrFun he i)

end Ginibre
