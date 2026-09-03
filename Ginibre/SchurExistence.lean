import Ginibre.GramSchmidtSchur
import Ginibre.SchurRegularity

/-!
# Actual Schur representations of Gaussian matrices

HKPV Section 6.3, existence and regularity of the Schur factors. On the
simple-spectrum locus an eigenbasis can be orthogonalized, so the unitary
and upper-triangular factors here are constructed, not postulated.
The final almost-everywhere theorem uses the actual product Gaussian law.

These existence theorems do not assert a measurable or continuous choice
of factors. Phase-fixed charts and a global measure transformation are
separate remaining tasks.
-/

noncomputable section
open Module MeasureTheory
namespace Ginibre

/-- HKPV Schur factorization on the simple-spectrum locus, constructed
from an eigenbasis and Gram--Schmidt in the Euclidean matrix space. -/
theorem exists_unitary_schur_of_separable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hsep : A.charpoly.Separable) :
    ∃ U S : Matrix (Fin n) (Fin n) ℂ,
      U.conjTranspose * U = 1 ∧ S.IsUpperTriangular ∧
        A = U * S * U.conjTranspose := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  let f : Module.End ℂ (EuclideanSpace ℂ (Fin n)) := Matrix.toLin e.toBasis e.toBasis A
  have hf : f.charpoly.Separable := by
    change (Matrix.toLin e.toBasis e.toBasis A).charpoly.Separable
    rwa [Matrix.charpoly_toLin]
  have hdim : finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by
    rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  obtain ⟨q, hq⟩ := exists_orthonormal_schur_basis n f hdim hf
  let U := e.toBasis.toMatrix q.toBasis
  let S := LinearMap.toMatrix q.toBasis q.toBasis f
  have hU : U.conjTranspose * U = 1 :=
    e.toMatrix_orthonormalBasis_conjTranspose_mul_self q
  have hrev : q.toBasis.toMatrix e.toBasis = U.conjTranspose :=
    Matrix.right_inv_eq_left_inv (e.toBasis.toMatrix_mul_toMatrix_flip q.toBasis) hU
  have heq : U * S * q.toBasis.toMatrix e.toBasis = A := by
    change e.toBasis.toMatrix q.toBasis * LinearMap.toMatrix q.toBasis q.toBasis f *
      q.toBasis.toMatrix e.toBasis = A
    rw [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
    exact LinearMap.toMatrix_toLin e.toBasis e.toBasis A
  rw [hrev] at heq
  exact ⟨U, S, hU, hq, heq.symm⟩

/-- HKPV (6.3.4): each simple-spectrum matrix has a Schur representation
with a strictly positive real lower-block Jacobian. -/
theorem exists_regular_unitary_schur_of_separable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hsep : A.charpoly.Separable) :
    ∃ U S : Matrix (Fin n) (Fin n) ℂ,
      U.conjTranspose * U = 1 ∧ S.IsUpperTriangular ∧
        A = U * S * U.conjTranspose ∧
        0 < Matrix.det (realifyMatrix (schurLowerMatrix S)) := by
  obtain ⟨U, S, hU, hS, hrep⟩ := exists_unitary_schur_of_separable A hsep
  refine ⟨U, S, hU, hS, hrep, det_real_schurLowerMatrix_pos_of_separable S hS ?_⟩
  rwa [hrep, charpoly_unitary_conjugate U S hU] at hsep

/-- **HKPV Schur existence and regularity for the actual Gaussian law**:
almost every matrix admits the nondegenerate representation above. No
external spectral law, eigenbasis, or Schur-existence input is assumed. -/
theorem gaussianMatrix_exists_regular_schur_ae (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ A ∂gaussianMatrixLaw n a,
      ∃ U S : Matrix (Fin n) (Fin n) ℂ,
        U.conjTranspose * U = 1 ∧ S.IsUpperTriangular ∧
          Matrix.of A.curry = U * S * U.conjTranspose ∧
          0 < Matrix.det (realifyMatrix (schurLowerMatrix S)) := by
  filter_upwards [gaussianMatrix_charpoly_separable_ae n ha] with A hA
  exact exists_regular_unitary_schur_of_separable (Matrix.of A.curry) hA

end Ginibre
