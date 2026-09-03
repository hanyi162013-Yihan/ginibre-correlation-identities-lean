import Ginibre.SchurProductVolume
import Ginibre.SchurAuxiliaryGaussian

/-!
# Integrating the auxiliary variables of the actual Gaussian Schur weight

HKPV (6.3.5) and Section 6.4. These identities combine the actual full
Jacobian, the actual iid matrix density, and the exact product volume.
Only the remaining angular factor survives strict-upper integration.
Global angular overlap accounting remains a separate obligation.
-/

noncomputable section
open OrderDual MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV reconstruction of an upper-triangular matrix from its diagonal
and independent strict-upper entries. -/
theorem upper_eq_diagonal_add_schurStrictUpper {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) :
    S = Matrix.diagonal (fun i => S i i) +
      schurStrictUpper (fun p => S (schurCol p) (schurRow p)) := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · let p : SchurLower n := ⟨toLex (toDual j, i), hij⟩
    have hu := schurStrictUpper_apply_upper (fun p => S (schurCol p) (schurRow p)) p
    change schurStrictUpper (fun p => S (schurCol p) (schurRow p)) i j = S i j at hu
    simp only [Matrix.add_apply, Matrix.diagonal, Matrix.of_apply,
      if_neg (ne_of_lt hij), zero_add, hu]
  · subst j
    simp only [Matrix.add_apply, Matrix.diagonal_apply_eq, schurStrictUpper_diag, add_zero]
  · have hu := schurStrictUpper_isUpperTriangular
      (fun p => S (schurCol p) (schurRow p)) hij
    simp only [Matrix.add_apply, Matrix.diagonal, Matrix.of_apply, if_neg (ne_of_gt hij),
      hu, hS hij, add_zero]

/-- HKPV the inverse product coordinate map retains the angular array. -/
theorem schurProductEquiv_symm_lower {n : ℕ} (y : SchurProductCoordinates n) :
    ((schurProductEquiv n).symm y).1 = y.1 := by
  have h := schurProductEquiv_lower ((schurProductEquiv n).symm y)
  simpa only [MeasurableEquiv.apply_symm_apply] using h.symm

/-- HKPV the inverse product coordinate map reconstructs the actual
upper factor, rather than a new auxiliary model. -/
theorem schurProductEquiv_symm_upper {n : ℕ} (y : SchurProductCoordinates n) :
    ((schurProductEquiv n).symm y).2.val = Matrix.diagonal y.2.1 + schurStrictUpper y.2.2 := by
  let x := (schurProductEquiv n).symm y
  have hd : (fun i => x.2.val i i) = y.2.1 := by
    funext i
    have h := schurProductEquiv_diagonal x i
    simpa only [x, MeasurableEquiv.apply_symm_apply] using h.symm
  have hu : (fun p => x.2.val (schurCol p) (schurRow p)) = y.2.2 := by
    funext p
    have h := schurProductEquiv_upper x p
    simpa only [x, MeasurableEquiv.apply_symm_apply] using h.symm
  change x.2.val = _
  rw [upper_eq_diagonal_add_schurStrictUpper x.2.val x.2.property, hd, hu]

/-- HKPV Vandermonde square in the actual Schur entry indexing. -/
def schurDiagonalWeight {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ p : SchurLower n, ‖z (schurCol p) - z (schurRow p)‖ ^ 2

/-- HKPV positivity needed for nonnegative integration, without a spacing hypothesis. -/
theorem schurDiagonalWeight_nonneg {n : ℕ} (z : Fin n → ℂ) :
    0 ≤ schurDiagonalWeight z := Finset.prod_nonneg (fun _ _ => sq_nonneg _)

/-- HKPV the full computed Jacobian in the exact product coordinates. -/
theorem schurJacobianWeight_product {n : ℕ} (y : SchurProductCoordinates n) :
    schurJacobianWeight 0 ((schurProductEquiv n).symm y) =
      schurDiagonalWeight y.2.1 * |schurAngularJacobian y.1| := by
  unfold schurJacobianWeight schurDiagonalWeight
  rw [schurProductEquiv_symm_lower, schurProductEquiv_symm_upper]
  simp only [Matrix.add_apply, Matrix.zero_apply, zero_add, Matrix.diagonal_apply_eq,
    schurStrictUpper_diag, add_zero]

/-- HKPV actual iid Gaussian density after the actual Schur map,
now with every independent variable visible. -/
theorem gaussianMatrixDensity_schur_product {n : ℕ} (a : ℝ)
    (y : SchurProductCoordinates n) :
    gaussianMatrixDensity n a (fun ij =>
      schurExpCoordinates 0 ((schurProductEquiv n).symm y) ij.1 ij.2) =
      (a / Real.pi) ^ (n * n) *
        (Real.exp (-a * ∑ i, ‖y.2.1 i‖ ^ 2) * Real.exp (-a * ∑ p, ‖y.2.2 p‖ ^ 2)) := by
  simp_rw [schurExpCoordinates_eq_conjugation, zero_add, schurProductEquiv_symm_upper]
  rw [gaussianMatrixDensity_schur a _ _ _ (schurUnitaryParam_unitary _)
    (schurStrictUpper_diag _), matrixEnergy_schurStrictUpper]

/-- HKPV actual matrix density times actual absolute Jacobian, not a
candidate spectral law. -/
def schurGaussianProductWeight (n : ℕ) (a : ℝ) (y : SchurProductCoordinates n) : ℝ :=
  schurJacobianWeight 0 ((schurProductEquiv n).symm y) *
    gaussianMatrixDensity n a (fun ij =>
      schurExpCoordinates 0 ((schurProductEquiv n).symm y) ij.1 ij.2)

/-- HKPV exact separation of the full actual Gaussian-Jacobian weight. -/
theorem schurGaussianProductWeight_factorization {n : ℕ} (a : ℝ)
    (y : SchurProductCoordinates n) :
    schurGaussianProductWeight n a y =
      ((a / Real.pi) ^ (n * n) *
        (schurDiagonalWeight y.2.1 * Real.exp (-a * ∑ i, ‖y.2.1 i‖ ^ 2)) *
        |schurAngularJacobian y.1|) * Real.exp (-a * ∑ p, ‖y.2.2 p‖ ^ 2) := by
  rw [schurGaussianProductWeight, schurJacobianWeight_product,
    gaussianMatrixDensity_schur_product]
  ring

/-- **HKPV actual auxiliary integration after the full Jacobian**.
The right side has no strict-upper variables and no unknown Gaussian
normalization. The angular integration and overlaps are not assumed here. -/
theorem lintegral_schurGaussianProductWeight_auxiliary {n : ℕ} {a : ℝ} (ha : 0 < a)
    (w : SchurLower n → ℂ) (z : Fin n → ℂ) :
    (∫⁻ t : SchurLower n → ℂ, ENNReal.ofReal (schurGaussianProductWeight n a (w, z, t))) =
      ENNReal.ofReal (((a / Real.pi) ^ (n * n) *
        (schurDiagonalWeight z * Real.exp (-a * ∑ i, ‖z i‖ ^ 2)) *
        |schurAngularJacobian w|) * (Real.pi / a) ^ Fintype.card (SchurLower n)) := by
  let C := (a / Real.pi) ^ (n * n) *
    (schurDiagonalWeight z * Real.exp (-a * ∑ i, ‖z i‖ ^ 2)) * |schurAngularJacobian w|
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (pow_nonneg (div_nonneg ha.le Real.pi_pos.le) _)
      (mul_nonneg (schurDiagonalWeight_nonneg z) (Real.exp_pos _).le)) (abs_nonneg _)
  simp_rw [schurGaussianProductWeight_factorization]
  change (∫⁻ t : SchurLower n → ℂ, ENNReal.ofReal (C * Real.exp (-a * ∑ p, ‖t p‖ ^ 2))) = _
  simp_rw [ENNReal.ofReal_mul hC]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_sum_norm_sq ha)
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
    integral_exp_neg_sum_norm_sq ha, ← ENNReal.ofReal_mul hC]

end Ginibre
