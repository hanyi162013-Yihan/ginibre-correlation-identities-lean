import Ginibre.SchurRealJacobian
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.LinearCombination

/-!
# Identifying the Schur commutator on genuine unitary tangent coordinates

HKPV (6.3.2)--(6.3.4). The independent coordinates of a skew-Hermitian
matrix are its strictly lower entries. The upper entries forced by
skew-Hermitian symmetry do not change the lower commutator block when
the triangular factor is upper triangular.

This is an algebraic tangent-space identification. No global Schur chart,
spectral measure identity, or change-of-variables conclusion is assumed.
-/

noncomputable section
open OrderDual
open scoped BigOperators Matrix
namespace Ginibre

/-- HKPV lower-coordinate indexing is faithful to the original row and column. -/
theorem schurLower_ext {n : ℕ} {p q : SchurLower n}
    (hr : schurRow p = schurRow q) (hc : schurCol p = schurCol q) : p = q := by
  apply Subtype.ext
  exact Prod.ext hr hc

/-- HKPV: the lower-coordinate embedding retains each independent entry exactly. -/
theorem schurLowerEmbed_apply_lower {n : ℕ} (ω : SchurLower n → ℂ)
    (p : SchurLower n) :
    schurLowerEmbed ω (schurRow p) (schurCol p) = ω p := by
  classical
  simp only [schurLowerEmbed, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    have hne : ¬ (schurRow q = schurRow p ∧ schurCol q = schurCol p) := by
      rintro ⟨hr, hc⟩
      exact hqp (schurLower_ext hr hc)
    rw [Matrix.single_apply_of_ne _ _ _ _ _ hne, mul_zero]
  · simp

/-- HKPV: no diagonal or upper entry is introduced by the lower embedding. -/
theorem schurLowerEmbed_apply_of_le {n : ℕ} (ω : SchurLower n → ℂ)
    (i j : Fin n) (hij : i ≤ j) : schurLowerEmbed ω i j = 0 := by
  classical
  simp only [schurLowerEmbed, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro q _
  have hne : ¬ (schurRow q = i ∧ schurCol q = j) := by
    rintro ⟨hr, hc⟩
    have hq : schurCol q < schurRow q := q.property
    rw [hr, hc] at hq
    exact (not_lt_of_ge hij) hq
  simp [Matrix.single_apply_of_ne _ _ _ _ _ hne]

/-- HKPV unitary tangent coordinates: complete the lower matrix by its negative adjoint. -/
def schurSkewEmbed {n : ℕ} (ω : SchurLower n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  schurLowerEmbed ω - (schurLowerEmbed ω).conjTranspose

/-- HKPV: the completed variation satisfies the actual skew-Hermitian equation. -/
theorem schurSkewEmbed_conjTranspose {n : ℕ} (ω : SchurLower n → ℂ) :
    (schurSkewEmbed ω).conjTranspose = -schurSkewEmbed ω := by
  simp [schurSkewEmbed, neg_sub]

/-- HKPV tangent coordinates remain the prescribed lower entries after completion. -/
theorem schurSkewEmbed_apply_lower {n : ℕ} (ω : SchurLower n → ℂ)
    (p : SchurLower n) : schurSkewEmbed ω (schurRow p) (schurCol p) = ω p := by
  have hz : schurLowerEmbed ω (schurCol p) (schurRow p) = 0 :=
    schurLowerEmbed_apply_of_le ω (schurCol p) (schurRow p) (le_of_lt p.property)
  simp only [schurSkewEmbed, Matrix.sub_apply, schurLowerEmbed_apply_lower,
    Matrix.conjTranspose_apply, hz, star_zero, sub_zero]

/-- HKPV independent tangent coordinates have no hidden kernel. -/
theorem schurSkewEmbed_injective (n : ℕ) :
    Function.Injective (@schurSkewEmbed n) := by
  intro ω η h
  funext p
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ =>
    A (schurRow p) (schurCol p)) h
  simpa only [schurSkewEmbed_apply_lower] using he

/-- HKPV: the adjoint correction is upper triangular. -/
theorem schurLowerEmbed_conjTranspose_upper {n : ℕ} (ω : SchurLower n → ℂ) :
    (schurLowerEmbed ω).conjTranspose.IsUpperTriangular := by
  intro i j hij
  simp only [Matrix.conjTranspose_apply,
    schurLowerEmbed_apply_of_le ω j i (le_of_lt hij), star_zero]

/-- HKPV (6.3.2): multiplying upper-triangular matrices cannot create a lower entry. -/
theorem upper_commutator_lower_zero {n : ℕ}
    (A S : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hS : S.IsUpperTriangular) (p : SchurLower n) :
    (A * S - S * A) (schurRow p) (schurCol p) = 0 := by
  have hp : schurCol p < schurRow p := p.property
  have hAS : (A * S) (schurRow p) (schurCol p) = 0 := hA.mul hS hp
  have hSA : (S * A) (schurRow p) (schurCol p) = 0 := hS.mul hA hp
  simp only [Matrix.sub_apply, hAS, hSA, sub_self]

/-- **HKPV (6.3.2), genuine skew-Hermitian variations**: the already-computed
Jacobian block remains correct after the dependent upper entries are restored. -/
theorem schurLowerMatrix_mulVec_skew {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (ω : SchurLower n → ℂ) (p : SchurLower n) :
    (schurLowerMatrix S *ᵥ ω) p =
      (schurSkewEmbed ω * S - S * schurSkewEmbed ω) (schurRow p) (schurCol p) := by
  rw [schurLowerMatrix_mulVec]
  have hz := upper_commutator_lower_zero (schurLowerEmbed ω).conjTranspose S
    (schurLowerEmbed_conjTranspose_upper ω) hS p
  simp only [schurSkewEmbed, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply] at *
  linear_combination hz

/-- HKPV (6.3.2): the upper-triangular variation of `S` has zero lower block. -/
theorem schur_differential_lower {n : ℕ}
    (S D : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (hD : D.IsUpperTriangular)
    (ω : SchurLower n → ℂ) (p : SchurLower n) :
    (D + (schurSkewEmbed ω * S - S * schurSkewEmbed ω))
      (schurRow p) (schurCol p) = (schurLowerMatrix S *ᵥ ω) p := by
  have hDz : D (schurRow p) (schurCol p) = 0 := hD p.property
  rw [Matrix.add_apply, hDz, zero_add]
  exact (schurLowerMatrix_mulVec_skew S hS ω p).symm

/-- HKPV simple-spectrum locus: the real lower-block Jacobian is strictly
positive when the diagonal eigenvalues are pairwise distinct. -/
theorem det_real_schurLowerMatrix_pos {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hdiag : Function.Injective (fun i => S i i)) :
    0 < Matrix.det (realifyMatrix (schurLowerMatrix S)) := by
  rw [det_real_schurLowerMatrix S hS]
  apply Finset.prod_pos
  intro p _
  apply pow_pos
  apply norm_pos_iff.mpr
  exact sub_ne_zero.mpr (hdiag.ne (ne_of_lt p.property))

end Ginibre
