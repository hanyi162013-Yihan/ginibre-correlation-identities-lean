import Ginibre.SchurProductGaussian
import Ginibre.DeterminantalDensity

/-!
# Matching the actual Schur diagonal weight to the normalized candidate

HKPV Section 6.4 and BC12 Theorem 3.2: reconcile the actual Jacobian
indexing with the Gaussian--Vandermonde candidate whose integral was
proved from orthogonality. This determines the diagonal normalization
without assuming any spectral law or any angular quotient volume.
-/

noncomputable section
open OrderDual MeasureTheory
open scoped ENNReal
namespace Ginibre

/-- HKPV independent lower positions are exactly unordered distinct index pairs,
represented with the smaller index first. -/
def schurPairIndexEquiv (n : ℕ) : SchurLower n ≃ (Σ i : Fin n, ↥(Finset.Ioi i)) where
  toFun p := ⟨schurCol p, ⟨schurRow p, Finset.mem_Ioi.mpr p.property⟩⟩
  invFun q := ⟨toLex (toDual q.2.val, q.1), Finset.mem_Ioi.mp q.2.property⟩
  left_inv p := schurLower_ext rfl rfl
  right_inv q := by rcases q with ⟨i, j, hj⟩; rfl

/-- HKPV the actual Jacobian weight is the same Vandermonde square used
in the candidate density, despite the different elimination indexing. -/
theorem schurDiagonalWeight_eq_pair_product {n : ℕ} (z : Fin n → ℂ) :
    schurDiagonalWeight z = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ‖z j - z i‖ ^ 2 := by
  calc
    _ = ∏ p : SchurLower n, ‖z (schurRow p) - z (schurCol p)‖ ^ 2 := by
      apply Finset.prod_congr rfl
      intro p _
      rw [norm_sub_rev]
    _ = ∏ q : (Σ i : Fin n, ↥(Finset.Ioi i)), ‖z q.2.val - z q.1‖ ^ 2 := by
      exact (schurPairIndexEquiv n).prod_comp (fun q => ‖z q.2.val - z q.1‖ ^ 2)
    _ = _ := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro i _
      simpa only using! (Finset.prod_coe_sort (Finset.Ioi i) (fun j => ‖z j - z i‖ ^ 2))

/-- BC12 the known candidate's normalization coefficient, derived earlier from
one-variable Gaussian orthogonality. -/
def schurSpectralCoefficient (n : ℕ) (a : ℝ) : ℝ :=
  (∏ i : Fin n, basisCoefficient a i.val) / (Nat.factorial n : ℝ)

/-- HKPV the actual diagonal-dependent factor after auxiliary integration. -/
def schurSpectralWeight (n : ℕ) (a : ℝ) (z : Fin n → ℂ) : ℝ :=
  schurDiagonalWeight z * Real.exp (-a * ∑ i, ‖z i‖ ^ 2)

/-- BC12 positivity of the explicit diagonal normalization coefficient. -/
theorem schurSpectralCoefficient_pos (n : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < schurSpectralCoefficient n a :=
  div_pos (Finset.prod_pos (fun _ _ => basisCoefficient_pos ha _))
    (Nat.cast_pos.mpr (Nat.factorial_pos n))

/-- **HKPV/BC12 exact match of the diagonal weights**. This is a comparison
of explicit functions, not yet a Gaussian matrix pushforward theorem. -/
theorem determinantDensity_eq_schurSpectralWeight (n : ℕ) {a : ℝ} (ha : 0 < a)
    (z : Fin n → ℂ) :
    determinantDensity n a z = schurSpectralCoefficient n a * schurSpectralWeight n a z := by
  rw [determinantDensity_vandermonde n ha, ← schurDiagonalWeight_eq_pair_product]
  unfold schurSpectralCoefficient schurSpectralWeight
  ring

/-- HKPV the diagonal Gaussian-Jacobian factor is nonnegative everywhere. -/
theorem schurSpectralWeight_nonneg (n : ℕ) (a : ℝ) (z : Fin n → ℂ) :
    0 ≤ schurSpectralWeight n a z :=
  mul_nonneg (schurDiagonalWeight_nonneg z) (Real.exp_pos _).le

/-- HKPV the proved candidate normalization can be transferred to the
actual diagonal factor by a finite, positive constant. -/
theorem schurSpectralWeight_eq_inv_coefficient_mul_candidate (n : ℕ)
    {a : ℝ} (ha : 0 < a) (z : Fin n → ℂ) :
    schurSpectralWeight n a z = (schurSpectralCoefficient n a)⁻¹ * determinantDensity n a z := by
  rw [determinantDensity_eq_schurSpectralWeight n ha, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt (schurSpectralCoefficient_pos n ha)), one_mul]

/-- HKPV absolute integrability of the actual diagonal factor in every dimension. -/
theorem integrable_schurSpectralWeight (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (schurSpectralWeight n a) := by
  have h := (integrable_determinantDensity n ha).const_mul (schurSpectralCoefficient n a)⁻¹
  simpa only [← schurSpectralWeight_eq_inv_coefficient_mul_candidate n ha] using h

/-- HKPV exact full diagonal normalization, with no angular-volume assumption. -/
theorem integral_schurSpectralWeight (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ z, schurSpectralWeight n a z) = (schurSpectralCoefficient n a)⁻¹ := by
  simp_rw [schurSpectralWeight_eq_inv_coefficient_mul_candidate n ha]
  rw [integral_const_mul, integral_determinantDensity n ha, mul_one]

/-- HKPV nonnegative normalization used in the global Tonelli argument. -/
theorem lintegral_schurSpectralWeight (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫⁻ z, ENNReal.ofReal (schurSpectralWeight n a z)) =
      ENNReal.ofReal ((schurSpectralCoefficient n a)⁻¹) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_schurSpectralWeight n ha)
    (Filter.Eventually.of_forall (schurSpectralWeight_nonneg n a)), integral_schurSpectralWeight n ha]

end Ginibre
