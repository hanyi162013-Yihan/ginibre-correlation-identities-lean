import Ginibre.SchurProductEntries
import Ginibre.SchurGaussian

/-!
# Integrating the actual strict-upper Gaussian variables

HKPV Section 6.4: the strict-upper triangular factor contributes one
ordinary complex Gaussian integral per independent entry. The matrix
energy is proved equal to the coordinate energy before any integral is
evaluated. This does not yet assert a global Schur integration formula.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix
namespace Ginibre

/-- HKPV actual strict-upper matrix associated to independent complex entries. -/
def schurStrictUpper {n : ℕ} (t : SchurLower n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (schurLowerEmbed t).transpose

/-- HKPV these matrices are upper triangular by their entry support. -/
theorem schurStrictUpper_isUpperTriangular {n : ℕ} (t : SchurLower n → ℂ) :
    (schurStrictUpper t).IsUpperTriangular := by
  intro i j hij
  exact schurLowerEmbed_apply_of_le t j i hij.le

/-- HKPV the strict-upper auxiliary factor has zero diagonal. -/
theorem schurStrictUpper_diag {n : ℕ} (t : SchurLower n → ℂ) (i : Fin n) :
    schurStrictUpper t i i = 0 :=
  schurLowerEmbed_apply_of_le t i i le_rfl

/-- HKPV each independent coordinate is the designated strict-upper entry. -/
theorem schurStrictUpper_apply_upper {n : ℕ} (t : SchurLower n → ℂ) (p : SchurLower n) :
    schurStrictUpper t (schurCol p) (schurRow p) = t p :=
  schurLowerEmbed_apply_lower t p

/-- HKPV entrywise Frobenius energy splits along the three exact coordinate sets. -/
theorem matrixEnergy_entry_partition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixEnergy A = (∑ p : SchurLower n, ‖A (schurRow p) (schurCol p)‖ ^ 2) +
      ((∑ i, ‖A i i‖ ^ 2) + ∑ p : SchurLower n, ‖A (schurCol p) (schurRow p)‖ ^ 2) := by
  unfold matrixEnergy
  have h := (schurEntryIndexEquiv n).sum_comp (fun ij => ‖A ij.1 ij.2‖ ^ 2)
  simpa only [SchurEntryIndex, Fintype.sum_sum_type, Fintype.sum_prod_type,
    schurEntryIndexEquiv, Equiv.ofBijective_apply, schurEntryAddress] using! h.symm

/-- HKPV the lower part of an upper-triangular matrix contributes no energy. -/
theorem matrixEnergy_upper_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) :
    matrixEnergy A = (∑ i, ‖A i i‖ ^ 2) +
      ∑ p : SchurLower n, ‖A (schurCol p) (schurRow p)‖ ^ 2 := by
  rw [matrixEnergy_entry_partition]
  have hz : ∀ p : SchurLower n, A (schurRow p) (schurCol p) = 0 := fun p => hA p.property
  simp only [hz,
    norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_add]

/-- HKPV strict-upper matrix energy is exactly the independent coordinate energy. -/
theorem matrixEnergy_schurStrictUpper {n : ℕ} (t : SchurLower n → ℂ) :
    matrixEnergy (schurStrictUpper t) = ∑ p, ‖t p‖ ^ 2 := by
  rw [matrixEnergy_upper_entries _ (schurStrictUpper_isUpperTriangular t)]
  simp only [schurStrictUpper_diag, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_add, schurStrictUpper_apply_upper]

/-- HKPV finite-dimensional Gaussian factorization in arbitrary complex coordinates. -/
theorem exp_neg_sum_norm_sq_eq_prod {ι : Type*} [Fintype ι] (a : ℝ) (t : ι → ℂ) :
    Real.exp (-a * ∑ i, ‖t i‖ ^ 2) = ∏ i, Real.exp (-a * ‖t i‖ ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]

/-- HKPV absolute integrability of all auxiliary Gaussian entries, proved by Fubini. -/
theorem integrable_exp_neg_sum_norm_sq {ι : Type*} [Fintype ι]
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ι → ℂ => Real.exp (-a * ∑ i, ‖t i‖ ^ 2)) := by
  simp_rw [exp_neg_sum_norm_sq_eq_prod]
  have h : Integrable (fun z : ℂ => Real.exp (-a * ‖z‖ ^ 2)) := by
    simpa only [pow_zero, one_mul] using integrable_norm_pow_mul_gaussian ha 0
  simpa only using! (Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ))
    (f := fun _ z => Real.exp (-a * ‖z‖ ^ 2)) (fun _ => h))

/-- HKPV the exact finite-dimensional auxiliary Gaussian integral. -/
theorem integral_exp_neg_sum_norm_sq {ι : Type*} [Fintype ι]
    {a : ℝ} (ha : 0 < a) :
    (∫ t : ι → ℂ, Real.exp (-a * ∑ i, ‖t i‖ ^ 2)) =
      (Real.pi / a) ^ Fintype.card ι := by
  have h : (∫ z : ℂ, Real.exp (-a * ‖z‖ ^ 2)) = Real.pi / a := by
    simpa only [mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one,
      mul_one, zero_add, pow_one] using integral_norm_even_pow_mul_gaussian ha 0
  simp_rw [exp_neg_sum_norm_sq_eq_prod]
  rw [integral_fintype_prod_volume_eq_prod (fun _ : ι => fun z : ℂ => Real.exp (-a * ‖z‖ ^ 2))]
  simp only [h, Finset.prod_const, Finset.card_univ]

/-- **HKPV auxiliary triangular integration**, for the actual matrix energy
and ordinary complex coordinate volume. There is no auxiliary-integral input. -/
theorem integral_schurStrictUpper_gaussian (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t : SchurLower n → ℂ, Real.exp (-a * matrixEnergy (schurStrictUpper t))) =
      (Real.pi / a) ^ Fintype.card (SchurLower n) := by
  simp_rw [matrixEnergy_schurStrictUpper]
  exact integral_exp_neg_sum_norm_sq ha

/-- HKPV the same auxiliary integral as a nonnegative integral, valid for Tonelli. -/
theorem lintegral_schurStrictUpper_gaussian (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫⁻ t : SchurLower n → ℂ,
      ENNReal.ofReal (Real.exp (-a * matrixEnergy (schurStrictUpper t)))) =
      ENNReal.ofReal ((Real.pi / a) ^ Fintype.card (SchurLower n)) := by
  simp_rw [matrixEnergy_schurStrictUpper]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_sum_norm_sq ha)
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
    integral_exp_neg_sum_norm_sq ha]

end Ginibre
