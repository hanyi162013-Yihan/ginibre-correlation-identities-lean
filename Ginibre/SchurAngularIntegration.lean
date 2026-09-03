import Ginibre.SchurSeparatedIntegration

/-!
# Integrating the angular and auxiliary Schur variables

HKPV Section 6.4: after genuine overlap removal, each patch contributes
an angular mass times the same ordered Gaussian--Vandermonde integral.
The angular masses need not be evaluated geometrically; later probability
normalization determines their total coefficient.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV the actual angular integral on a disjointified reference patch. -/
def schurAngularMass (n : ℕ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ w in schurAngularRegion n k, ENNReal.ofReal |schurAngularJacobian w|

/-- HKPV reading the diagonal after the exact inverse product split. -/
theorem schurProductEquiv_symm_diagonal {n : ℕ} (y : SchurProductCoordinates n) :
    (fun i => ((schurProductEquiv n).symm y).2.val i i) = y.2.1 := by
  funext i
  rw [schurProductEquiv_symm_upper, Matrix.add_apply, Matrix.diagonal_apply_eq,
    schurStrictUpper_diag, add_zero]

/-- HKPV the diagonal spectral factor is measurable directly from its explicit formula. -/
theorem measurable_schurSpectralWeight (n : ℕ) (a : ℝ) :
    Measurable (schurSpectralWeight n a) := by
  apply Continuous.measurable
  have hV := continuous_schurDiagonalWeight n
  unfold schurSpectralWeight
  fun_prop

/-- **HKPV complete auxiliary and angular separation in one disjoint
patch**. The spectral test is arbitrary measurable and nonnegative;
no integrability premise is used to conceal a missing normalization. -/
theorem lintegral_schurProduct_test_separated (n : ℕ) {a : ℝ} (ha : 0 < a)
    (k : ℕ) (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in schurAngularRegion n k ×ˢ (schurSpectralChamber n ×ˢ Set.univ),
      ENNReal.ofReal (schurGaussianProductWeight n a y) * f y.2.1) =
      (ENNReal.ofReal ((a / Real.pi) ^ (n * n) * (Real.pi / a) ^ Fintype.card (SchurLower n)) *
        schurAngularMass n k) *
        ∫⁻ z in schurSpectralChamber n, ENNReal.ofReal (schurSpectralWeight n a z) * f z := by
  have hH : Measurable (fun y : SchurProductCoordinates n =>
      ENNReal.ofReal (schurGaussianProductWeight n a y) * f y.2.1) :=
    (continuous_schurGaussianProductWeight n a).measurable.ennreal_ofReal.mul
      (hf.comp (measurable_fst.comp measurable_snd))
  rw [setLIntegral_schurProduct_iterated n k _ hH]
  simp_rw [lintegral_schurProduct_test_auxiliary ha, mul_assoc]
  let c := ENNReal.ofReal ((a / Real.pi) ^ (n * n) *
    (Real.pi / a) ^ Fintype.card (SchurLower n))
  let I := ∫⁻ z in schurSpectralChamber n, ENNReal.ofReal (schurSpectralWeight n a z) * f z
  calc
    _ = ∫⁻ w in schurAngularRegion n k, c * (ENNReal.ofReal |schurAngularJacobian w| * I) := by
      apply lintegral_congr
      intro w
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = c * (schurAngularMass n k * I) := by
      dsimp only [c, schurAngularMass]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_mul_const I (continuous_schurAngularJacobian n).abs.measurable.ennreal_ofReal]
    _ = _ := rfl

/-- HKPV the actual source integrand becomes the separated product
integrand under the proved coordinate-volume equivalence. -/
theorem lintegral_schurDisjointDomain_diagonal_product (n : ℕ) (a : ℝ)
    (k : ℕ) (f : (Fin n → ℂ) → ℝ≥0∞) :
    (∫⁻ x in schurDisjointDomain n k,
      ENNReal.ofReal (schurJacobianWeight 0 x) *
        (ENNReal.ofReal (gaussianCoordinateDensity n a (schurEntryCoordinates 0 x)) *
          f (fun i => x.2.val i i)) ∂schurCoordinateVolume n) =
      ∫⁻ y in schurAngularRegion n k ×ˢ (schurSpectralChamber n ×ˢ Set.univ),
        ENNReal.ofReal (schurGaussianProductWeight n a y) * f y.2.1 := by
  rw [setLIntegral_schurDisjointDomain_product]
  apply lintegral_congr
  intro y
  rw [← mul_assoc, schurCoordinateGaussianWeight_eq_product,
    MeasurableEquiv.apply_symm_apply, schurProductEquiv_symm_diagonal]

/-- **HKPV a genuine Gaussian disjoint-source integral factors into a
common spectral integral and a spectrum-independent angular mass**. -/
theorem lintegral_schurDisjointDomain_diagonal_separated (n : ℕ) {a : ℝ} (ha : 0 < a)
    (k : ℕ) (f : (Fin n → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in schurDisjointDomain n k,
      ENNReal.ofReal (schurJacobianWeight 0 x) *
        (ENNReal.ofReal (gaussianCoordinateDensity n a (schurEntryCoordinates 0 x)) *
          f (fun i => x.2.val i i)) ∂schurCoordinateVolume n) =
      (ENNReal.ofReal ((a / Real.pi) ^ (n * n) * (Real.pi / a) ^ Fintype.card (SchurLower n)) *
        schurAngularMass n k) *
        ∫⁻ z in schurSpectralChamber n, ENNReal.ofReal (schurSpectralWeight n a z) * f z := by
  rw [lintegral_schurDisjointDomain_diagonal_product]
  exact lintegral_schurProduct_test_separated n ha k f hf

end Ginibre
