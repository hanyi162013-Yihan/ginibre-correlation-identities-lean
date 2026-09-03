import Ginibre.Eigenbasis
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Orthogonalizing an eigenbasis gives an upper-triangular operator matrix

HKPV Section 6.3, Schur existence on the simple-spectrum locus.
Gram--Schmidt gives an upper-triangular change of basis. Its inverse is
upper triangular as well, so conjugating the diagonal eigenvalue matrix
produces an upper-triangular matrix in an orthonormal basis.
-/

noncomputable section
open Module InnerProductSpace
namespace Ginibre

/-- HKPV change-of-basis bookkeeping: the reverse change of basis is the
actual nonsingular inverse, not an assumed inverse matrix. -/
theorem basisToMatrix_inverse {E : Type*} [AddCommGroup E] [Module ℂ E] {n : ℕ}
    (b c : Basis (Fin n) ℂ E) : (b.toMatrix c)⁻¹ = c.toMatrix b :=
  Matrix.inv_eq_left_inv (c.toMatrix_mul_toMatrix_flip b)

/-- HKPV triangularity survives inversion of a change-of-basis matrix. -/
theorem basisToMatrix_upper_reverse {E : Type*} [AddCommGroup E] [Module ℂ E] {n : ℕ}
    (b c : Basis (Fin n) ℂ E) (hbc : (b.toMatrix c).IsUpperTriangular) :
    (c.toMatrix b).IsUpperTriangular := by
  letI := b.invertibleToMatrix c
  have h := Matrix.blockTriangular_inv_of_blockTriangular hbc
  rwa [basisToMatrix_inverse] at h

/-- HKPV Gram--Schmidt step: an eigenbasis produces an orthonormal basis
in which the same operator is upper triangular. -/
theorem gramSchmidt_eigenbasis_upper {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}
    (f : Module.End ℂ E) (b : Basis (Fin n) ℂ E) (z : Fin n → ℂ)
    (hb : ∀ i, f (b i) = z i • b i) :
    ∃ q : OrthonormalBasis (Fin n) ℂ E,
      (LinearMap.toMatrix q.toBasis q.toBasis f).IsUpperTriangular := by
  classical
  let hdim : finrank ℂ E = Fintype.card (Fin n) := finrank_eq_card_basis b
  let q := gramSchmidtOrthonormalBasis hdim (b : Fin n → E)
  have hR : (q.toBasis.toMatrix b).IsUpperTriangular :=
    gramSchmidtOrthonormalBasis_inv_isUpperTriangular hdim (b : Fin n → E)
  have hR' : (b.toMatrix q.toBasis).IsUpperTriangular :=
    basisToMatrix_upper_reverse q.toBasis b hR
  have hD : (Matrix.diagonal z).IsUpperTriangular := Matrix.blockTriangular_diagonal z
  have hprod := (hR.mul hD).mul hR'
  have hdiag := toMatrix_eigenbasis f b z hb
  rw [← hdiag] at hprod
  have heq : q.toBasis.toMatrix b * LinearMap.toMatrix b b f * b.toMatrix q.toBasis =
      LinearMap.toMatrix q.toBasis q.toBasis f :=
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix q.toBasis b q.toBasis b f
  rw [heq] at hprod
  exact ⟨q, hprod⟩

/-- **HKPV orthonormal Schur basis on the simple-spectrum locus**.
Every hypothesis is an ordinary finite-dimensional linear-algebra condition. -/
theorem exists_orthonormal_schur_basis {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (n : ℕ) (f : Module.End ℂ E) (hdim : finrank ℂ E = n)
    (hsep : f.charpoly.Separable) :
    ∃ q : OrthonormalBasis (Fin n) ℂ E,
      (LinearMap.toMatrix q.toBasis q.toBasis f).IsUpperTriangular := by
  obtain ⟨b, z, _, hb⟩ := exists_eigenbasis_of_charpoly_separable n f hdim hsep
  exact gramSchmidt_eigenbasis_upper f b z hb

end Ginibre
