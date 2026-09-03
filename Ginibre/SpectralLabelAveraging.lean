import Ginibre.SchurChamberNormalization

/-!
# Uniform labels for the actual Gaussian spectrum

BC12 Theorems 3.2--3.3. Averaging over every finite label permutation
converts an arbitrary spectral test into a symmetric one. This is the
usual random-label convention for joint eigenvalue densities; it is not
an assumption about the matrix distribution.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- BC12 exact finite uniform averaging over eigenvalue labels. -/
def schurLabelAverage (n : ℕ) (f : (Fin n → ℂ) → ℝ≥0∞) (z : Fin n → ℂ) : ℝ≥0∞ :=
  (Nat.factorial n : ℝ≥0∞)⁻¹ * ∑ σ : Equiv.Perm (Fin n), f (schurPermute σ z)

/-- BC12 finite label averaging preserves measurability. -/
theorem measurable_schurLabelAverage (n : ℕ) (f : (Fin n → ℂ) → ℝ≥0∞)
    (hf : Measurable f) : Measurable (schurLabelAverage n f) := by
  apply measurable_const.mul
  exact Finset.measurable_fun_sum _ (fun σ _ => hf.comp (schurPermute σ).measurable)

/-- BC12 uniform label averaging is symmetric, by the group permutation bijection. -/
theorem schurLabelAverage_symmetric (n : ℕ) (f : (Fin n → ℂ) → ℝ≥0∞)
    (σ : Equiv.Perm (Fin n)) (z : Fin n → ℂ) :
    schurLabelAverage n f (fun i => z (σ i)) = schurLabelAverage n f z := by
  unfold schurLabelAverage
  congr 1
  simp_rw [schurPermute_apply]
  have h := Equiv.sum_comp (Equiv.mulLeft σ)
    (fun τ : Equiv.Perm (Fin n) => f (fun i => z (τ i)))
  simpa only [Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_apply] using h

/-- BC12 the determinant density is a measurable explicit function. -/
theorem measurable_determinantDensity (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Measurable (determinantDensity n a) := by
  have he : determinantDensity n a = fun z =>
      schurSpectralCoefficient n a * schurSpectralWeight n a z :=
    funext (determinantDensity_eq_schurSpectralWeight n ha)
  rw [he]
  exact measurable_const.mul (measurable_schurSpectralWeight n a)

/-- BC12 full candidate integration is unchanged by any permutation of a test's labels. -/
theorem lintegral_candidate_permute (n : ℕ) (a : ℝ)
    (f : (Fin n → ℂ) → ℝ≥0∞) (σ : Equiv.Perm (Fin n)) :
    (∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * f (schurPermute σ z)) =
      ∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * f z := by
  have h := (schurPermute_measurePreserving σ).lintegral_comp_emb
    (schurPermute σ).measurableEmbedding (fun z => ENNReal.ofReal (determinantDensity n a z) * f z)
  simpa only [schurPermute_apply, determinantDensity_permute] using h

/-- BC12 uniform averaging also leaves the candidate integral unchanged,
with every finite-sum and integral exchange justified. -/
theorem lintegral_candidate_labelAverage (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * schurLabelAverage n f z) =
      ∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * f z := by
  have hm (σ : Equiv.Perm (Fin n)) : Measurable (fun z =>
      ENNReal.ofReal (determinantDensity n a z) * f (schurPermute σ z)) :=
    (measurable_determinantDensity n ha).ennreal_ofReal.mul (hf.comp (schurPermute σ).measurable)
  have hpoint (z : Fin n → ℂ) :
      ENNReal.ofReal (determinantDensity n a z) * schurLabelAverage n f z =
        (Nat.factorial n : ℝ≥0∞)⁻¹ * ∑ σ : Equiv.Perm (Fin n),
          ENNReal.ofReal (determinantDensity n a z) * f (schurPermute σ z) := by
    rw [schurLabelAverage, mul_left_comm, Finset.mul_sum]
  simp_rw [hpoint]
  rw [lintegral_const_mul _ (Finset.measurable_fun_sum _ (fun σ _ => hm σ)),
    lintegral_finsetSum _ (fun σ _ => hm σ)]
  simp_rw [lintegral_candidate_permute]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc]
  rw [ENNReal.inv_mul_cancel, one_mul]
  · exact_mod_cast Nat.factorial_ne_zero n
  · exact ENNReal.natCast_ne_top _

/-- **BC12 complete random-label joint integral formula from the actual
Gaussian matrix**, for arbitrary nonnegative measurable spectral tests. -/
theorem lintegral_gaussianMatrix_labelAverage (n : ℕ) {a : ℝ} (ha : 0 < a)
    (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ A, schurLabelAverage n f (schurSpectrum (Matrix.of A.curry)) ∂gaussianMatrixLaw n a =
      ∫⁻ z, ENNReal.ofReal (determinantDensity n a z) * f z := by
  rw [lintegral_gaussianMatrix_symmetric_spectrum n ha _
    (measurable_schurLabelAverage n f hf) (schurLabelAverage_symmetric n f),
    lintegral_candidate_labelAverage n ha f hf]

end Ginibre
