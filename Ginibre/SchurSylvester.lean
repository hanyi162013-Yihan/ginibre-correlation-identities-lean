import Ginibre.SchurEntrySplit

/-!
# Triangular Sylvester equations and ordered Schur intertwiners

HKPV Section 6.3, the uniqueness/overlap step after the local Jacobian
calculation. The mixed map `X ↦ X T - S X` uses the same elimination
order as (6.3.2). With matching distinct ordered diagonals, its lower
block is invertible, forcing every intertwiner to be upper triangular.
No Schur uniqueness or spectral-distribution interface is assumed.
-/

noncomputable section
open OrderDual
open scoped Matrix
namespace Ginibre

/-- HKPV ordered-factor comparison: the lower Sylvester coefficient matrix. -/
def schurSylvesterMatrix {n : ℕ} (S T : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (SchurLower n) (SchurLower n) ℂ :=
  Matrix.of (fun p q =>
    (if schurRow p = schurRow q then T (schurCol q) (schurCol p) else 0) -
    (if schurCol p = schurCol q then S (schurRow p) (schurRow q) else 0))

/-- HKPV the diagonal differences in the mixed triangular equations. -/
theorem schurSylvesterMatrix_diag {n : ℕ} (S T : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurLower n) :
    schurSylvesterMatrix S T p p =
      T (schurCol p) (schurCol p) - S (schurRow p) (schurRow p) := by
  simp [schurSylvesterMatrix]

/-- HKPV decreasing-row/increasing-column elimination works for two
different triangular factors, not just for a commutator. -/
theorem schurSylvesterMatrix_isLowerTriangular {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) : (schurSylvesterMatrix S T).IsLowerTriangular := by
  intro p q hpq
  rcases (schurLower_lt_iff p q).mp hpq with hr | ⟨hr, hc⟩
  · have hne : schurRow p ≠ schurRow q := ne_of_gt hr
    have hz : S (schurRow p) (schurRow q) = 0 := hS hr
    simp [schurSylvesterMatrix, hne, hz]
  · have hne : schurCol p ≠ schurCol q := ne_of_lt hc
    have hz : T (schurCol q) (schurCol p) = 0 := hT hc
    simp [schurSylvesterMatrix, hr, hne, hz]

/-- HKPV determinant of the mixed lower Sylvester block. -/
theorem det_schurSylvesterMatrix {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) :
    (schurSylvesterMatrix S T).det =
      ∏ p : SchurLower n, (T (schurCol p) (schurCol p) - S (schurRow p) (schurRow p)) := by
  rw [Matrix.det_of_isLowerTriangular _ (schurSylvesterMatrix_isLowerTriangular S T hS hT)]
  simp only [schurSylvesterMatrix_diag]

/-- HKPV coordinate-basis verification of the mixed lower block. -/
theorem schurSylvesterMatrix_single {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℂ) (p q : SchurLower n) :
    schurSylvesterMatrix S T p q =
      ((Matrix.single (schurRow q) (schurCol q) (1 : ℂ) : Matrix (Fin n) (Fin n) ℂ) * T -
        S * (Matrix.single (schurRow q) (schurCol q) (1 : ℂ) :
          Matrix (Fin n) (Fin n) ℂ)) (schurRow p) (schurCol p) := by
  simp only [schurSylvesterMatrix, Matrix.of_apply, Matrix.sub_apply]
  by_cases hr : schurRow p = schurRow q <;>
    by_cases hc : schurCol p = schurCol q
  · simp [hr, hc, Matrix.single_mul_apply_same, Matrix.mul_single_apply_same]
  · simp [hr, hc, Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne]
  · simp [hr, hc, Matrix.single_mul_apply_of_ne, Matrix.mul_single_apply_same]
  · simp [hr, hc, Matrix.single_mul_apply_of_ne, Matrix.mul_single_apply_of_ne]

/-- HKPV the coefficient calculation on arbitrary lower variations. -/
theorem schurSylvesterMatrix_mulVec {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℂ) (w : SchurLower n → ℂ) (p : SchurLower n) :
    (schurSylvesterMatrix S T *ᵥ w) p =
      (schurLowerEmbed w * T - S * schurLowerEmbed w) (schurRow p) (schurCol p) := by
  simp only [schurLowerEmbed, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    ← Finset.sum_sub_distrib, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro q _
  rw [schurSylvesterMatrix_single]
  simp only [Matrix.sub_apply]
  ring

/-- HKPV upper residuals do not affect the lower Sylvester equations. -/
theorem schurLowerEntries_sylvester {n : ℕ}
    (S T X : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) :
    schurLowerEntries (X * T - S * X) =
      schurSylvesterMatrix S T *ᵥ schurLowerEntries X := by
  funext p
  rw [schurSylvesterMatrix_mulVec]
  have hR := schur_upper_residual X
  have hRT := hR.mul hT p.property
  have hSR := hS.mul hR p.property
  change (X * T - S * X) (schurRow p) (schurCol p) = _
  change ((X - schurLowerEmbed (schurLowerEntries X)) * T) (schurRow p) (schurCol p) = 0 at hRT
  change (S * (X - schurLowerEmbed (schurLowerEntries X))) (schurRow p) (schurCol p) = 0 at hSR
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply] at *
  linear_combination hRT - hSR

/-- HKPV the lower equations are nonsingular for matching simple ordered diagonals. -/
theorem isUnit_schurSylvesterMatrix {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i = S i i)
    (hz : Function.Injective (fun i => S i i)) : IsUnit (schurSylvesterMatrix S T) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [det_schurSylvesterMatrix S T hS hT]
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  rw [hd]
  exact sub_ne_zero.mpr (hz.ne (ne_of_lt p.property))

/-- **HKPV ordered-Schur uniqueness step**: an intertwiner between upper
triangular factors with the same distinct ordered diagonal is upper triangular. -/
theorem upperTriangular_of_ordered_intertwiner {n : ℕ}
    (S T X : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i = S i i)
    (hz : Function.Injective (fun i => S i i)) (hX : X * T = S * X) :
    X.IsUpperTriangular := by
  have hzero : schurLowerEntries X = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr (isUnit_schurSylvesterMatrix S T hS hT hd hz))
    rw [← schurLowerEntries_sylvester S T X hS hT, hX, sub_self, map_zero,
      Matrix.mulVec_zero]
  intro i j hij
  let p : SchurLower n := ⟨toLex (toDual i, j), hij⟩
  exact congrFun hzero p

end Ginibre
