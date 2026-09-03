import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Prod.Lex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Ring

/-!
# The triangular Jacobian block in Schur coordinates

HKPV, Sections 6.3--6.4, especially (6.3.2)--(6.3.5).

This file proves the finite-dimensional determinant calculation. It does
not assume a Schur measure identity and does not assert a global change
of variables. Lower-triangular indices are ordered by decreasing row and
then increasing column, exactly the order used to triangularize the
commutator differential.
-/

noncomputable section
open OrderDual
open scoped BigOperators Matrix
namespace Ginibre

/-- Strictly lower-triangular coordinates, in Schur's elimination order. -/
abbrev SchurLower (n : ℕ) :=
  {p : (Fin n)ᵒᵈ ×ₗ Fin n // (ofLex p).2 < ofDual (ofLex p).1}

-- Give the coordinate type stable named instances. This prevents elaboration
-- from repeatedly expanding the filtered lexicographic finite enumeration.
instance schurLowerDecidableEq (n : ℕ) : DecidableEq (SchurLower n) := inferInstance
instance schurLowerFintype (n : ℕ) : Fintype (SchurLower n) := inferInstance
instance schurLowerLinearOrder (n : ℕ) : LinearOrder (SchurLower n) := inferInstance

/-- The original matrix row of a lower-triangular coordinate. -/
def schurRow {n : ℕ} (p : SchurLower n) : Fin n := ofDual (ofLex p.val).1

/-- The original matrix column of a lower-triangular coordinate. -/
def schurCol {n : ℕ} (p : SchurLower n) : Fin n := (ofLex p.val).2

/-- HKPV (6.3.2): the coefficient matrix of the lower part of `[Ω,S]`,
where `S` is upper triangular. No eigenvalue or Jacobian premise is hidden here. -/
def schurLowerMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (SchurLower n) (SchurLower n) ℂ :=
  Matrix.of (fun p q =>
    (if schurRow p = schurRow q then S (schurCol q) (schurCol p) else 0) -
    (if schurCol p = schurCol q then S (schurRow p) (schurRow q) else 0))

/-- HKPV's coordinate ordering: decreasing row, then increasing column. -/
theorem schurLower_lt_iff {n : ℕ} (p q : SchurLower n) :
    p < q ↔ schurRow q < schurRow p ∨
      schurRow p = schurRow q ∧ schurCol p < schurCol q := by
  exact Prod.Lex.lt_iff

/-- HKPV (6.3.2): the diagonal coefficient is the difference of eigenvalues. -/
@[simp] theorem schurLowerMatrix_diag {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurLower n) :
    schurLowerMatrix S p p = S (schurCol p) (schurCol p) - S (schurRow p) (schurRow p) := by
  simp [schurLowerMatrix]

/-- HKPV (6.3.3)--(6.3.4): the lower commutator block is triangular in
the explicit elimination order. This is valid for every upper-triangular `S`. -/
theorem schurLowerMatrix_isLowerTriangular {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) :
    (schurLowerMatrix S).IsLowerTriangular := by
  intro p q hpq
  have h : p < q := hpq
  rcases (schurLower_lt_iff p q).mp h with hr | ⟨hr, hc⟩
  · have hne : schurRow p ≠ schurRow q := ne_of_gt hr
    have hz : S (schurRow p) (schurRow q) = 0 := hS hr
    simp [schurLowerMatrix, hne, hz]
  · have hne : schurCol p ≠ schurCol q := ne_of_lt hc
    have hz : S (schurCol q) (schurCol p) = 0 := hS hc
    simp [schurLowerMatrix, hr, hne, hz]

/-- **HKPV Schur Jacobian block, complex determinant**: all off-diagonal
entries of the triangular factor disappear from the determinant. -/
theorem det_schurLowerMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) :
    Matrix.det (schurLowerMatrix S) =
      ∏ p : SchurLower n, (S (schurCol p) (schurCol p) - S (schurRow p) (schurRow p)) := by
  rw [Matrix.det_of_isLowerTriangular _ (schurLowerMatrix_isLowerTriangular S hS)]
  simp only [schurLowerMatrix_diag]

/-- HKPV (6.3.4), the squared modulus of the complex Jacobian block.
This is the Vandermonde-square factor; real-coordinate identification is
proved separately, rather than encoded in this theorem's name. -/
theorem norm_sq_det_schurLowerMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) :
    ‖Matrix.det (schurLowerMatrix S)‖ ^ 2 =
      ∏ p : SchurLower n,
        ‖S (schurCol p) (schurCol p) - S (schurRow p) (schurRow p)‖ ^ 2 := by
  rw [det_schurLowerMatrix S hS, norm_prod, Finset.prod_pow]

/-- HKPV (6.3.2), checked on each coordinate basis vector: the displayed
Jacobian matrix is genuinely the lower block of the commutator map. -/
theorem schurLowerMatrix_eq_commutator_single {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (p q : SchurLower n) :
    schurLowerMatrix S p q =
      ((Matrix.single (schurRow q) (schurCol q) (1 : ℂ) : Matrix (Fin n) (Fin n) ℂ) * S -
        S * (Matrix.single (schurRow q) (schurCol q) (1 : ℂ) :
          Matrix (Fin n) (Fin n) ℂ)) (schurRow p) (schurCol p) := by
  simp only [schurLowerMatrix, Matrix.of_apply, Matrix.sub_apply]
  by_cases hr : schurRow p = schurRow q <;>
    by_cases hc : schurCol p = schurCol q
  · simp [hr, hc, Matrix.single_mul_apply_same, Matrix.mul_single_apply_same]
  · simp [hr, hc, Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne]
  · simp [hr, hc, Matrix.single_mul_apply_of_ne, Matrix.mul_single_apply_same]
  · simp [hr, hc, Matrix.single_mul_apply_of_ne, Matrix.mul_single_apply_of_ne]

/-- Embed the independent lower-triangular coordinates into a full matrix. -/
def schurLowerEmbed {n : ℕ} (ω : SchurLower n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ q, ω q • Matrix.single (schurRow q) (schurCol q) 1

/-- HKPV (6.3.2): the coefficient calculation extends to every lower
variation, not only basis vectors. -/
theorem schurLowerMatrix_mulVec {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (ω : SchurLower n → ℂ) (p : SchurLower n) :
    (schurLowerMatrix S *ᵥ ω) p =
      (schurLowerEmbed ω * S - S * schurLowerEmbed ω) (schurRow p) (schurCol p) := by
  simp only [schurLowerEmbed, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    ← Finset.sum_sub_distrib, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro q _
  rw [schurLowerMatrix_eq_commutator_single]
  simp only [Matrix.sub_apply]
  ring

end Ginibre
