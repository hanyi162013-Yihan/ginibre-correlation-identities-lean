import Ginibre.GramSchmidtSchur
import Ginibre.SchurExistence
import Ginibre.SchurOrderedSpectrum
import Mathlib.Data.Finset.Sort

/-!
# Constructing Schur bases in the chosen spectral chamber

HKPV Section 6.3, existence with explicit permutation bookkeeping.
First order a genuine eigenbasis by a finite permutation. Gram--Schmidt
preserves the ordered diagonal because all change-of-basis factors are
upper triangular. No ordered Schur existence assumption is introduced.
-/

noncomputable section
open Module InnerProductSpace MeasureTheory
namespace Ginibre

/-- HKPV every distinct complex spectrum has a finite ordering permutation. -/
theorem exists_schurOrderingPermutation {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) :
    ∃ e : Equiv.Perm (Fin n), schurDiagonalOrdered (fun i => z (e i)) := by
  classical
  let f := schurLexCode ∘ z
  have hf : Function.Injective f := schurLexCode_injective.comp hz
  let s : Finset (ℝ ×ₗ ℝ) := Finset.univ.image f
  have hc : s.card = n := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  let g : Fin n → s := fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hg : Function.Bijective g := by
    refine ⟨fun i j h => hf (congrArg Subtype.val h), ?_⟩
    rintro ⟨v, hv⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    exact ⟨i, Subtype.ext hi⟩
  let e : Equiv.Perm (Fin n) :=
    (s.orderIsoOfFin hc).toEquiv.trans (Equiv.ofBijective g hg).symm
  refine ⟨e, ?_⟩
  have he (i : Fin n) : f (e i) = s.orderEmbOfFin hc i := by
    have h := congrArg Subtype.val ((Equiv.ofBijective g hg).apply_symm_apply
      (s.orderIsoOfFin hc i))
    exact h
  change StrictMono (fun i => f (e i))
  simpa only [he] using (s.orderEmbOfFin hc).strictMono

/-- HKPV upper-triangular multiplication preserves diagonal products. -/
theorem upper_mul_apply_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

/-- HKPV triangular conjugation of a diagonal matrix preserves its
diagonal in the same order, not just as an unordered set. -/
theorem upper_conjugation_diagonal {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (z : Fin n → ℂ) (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular)
    (hAB : A * B = 1) (i : Fin n) :
    (A * Matrix.diagonal z * B) i i = z i := by
  have hD : (Matrix.diagonal z).IsUpperTriangular := Matrix.blockTriangular_diagonal z
  rw [upper_mul_apply_diag _ B (hA.mul hD) hB,
    upper_mul_apply_diag A _ hA hD, Matrix.diagonal_apply_eq]
  have hi : A i i * B i i = 1 := by
    rw [← upper_mul_apply_diag A B hA hB, hAB, Matrix.one_apply_eq]
  calc
    A i i * z i * B i i = z i * (A i i * B i i) := by ring
    _ = z i := by rw [hi, mul_one]

/-- HKPV Gram--Schmidt gives both upper triangularity and the original
ordered eigenvalue diagonal. -/
theorem gramSchmidt_eigenbasis_diagonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}
    (f : Module.End ℂ E) (b : Basis (Fin n) ℂ E) (z : Fin n → ℂ)
    (hb : ∀ i, f (b i) = z i • b i) :
    ∃ q : OrthonormalBasis (Fin n) ℂ E,
      (LinearMap.toMatrix q.toBasis q.toBasis f).IsUpperTriangular ∧
      ∀ i, LinearMap.toMatrix q.toBasis q.toBasis f i i = z i := by
  classical
  let hdim : finrank ℂ E = Fintype.card (Fin n) := finrank_eq_card_basis b
  let q := gramSchmidtOrthonormalBasis hdim (b : Fin n → E)
  have hR : (q.toBasis.toMatrix b).IsUpperTriangular :=
    gramSchmidtOrthonormalBasis_inv_isUpperTriangular hdim (b : Fin n → E)
  have hR' : (b.toMatrix q.toBasis).IsUpperTriangular :=
    basisToMatrix_upper_reverse q.toBasis b hR
  have hD : (Matrix.diagonal z).IsUpperTriangular := Matrix.blockTriangular_diagonal z
  have heq : q.toBasis.toMatrix b * Matrix.diagonal z * b.toMatrix q.toBasis =
      LinearMap.toMatrix q.toBasis q.toBasis f := by
    rw [← toMatrix_eigenbasis f b z hb]
    exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      q.toBasis b q.toBasis b f
  refine ⟨q, ?_, ?_⟩
  · rw [← heq]
    exact (hR.mul hD).mul hR'
  · intro i
    rw [← heq]
    exact upper_conjugation_diagonal _ _ z hR hR'
      (q.toBasis.toMatrix_mul_toMatrix_flip b) i

/-- **HKPV ordered Schur basis existence**, constructed from actual
characteristic roots, a finite permutation, and Gram--Schmidt. -/
theorem exists_orthonormal_ordered_schur_basis {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (n : ℕ) (f : Module.End ℂ E) (hdim : finrank ℂ E = n)
    (hsep : f.charpoly.Separable) :
    ∃ q : OrthonormalBasis (Fin n) ℂ E,
      (LinearMap.toMatrix q.toBasis q.toBasis f).IsUpperTriangular ∧
      schurDiagonalOrdered (fun i => LinearMap.toMatrix q.toBasis q.toBasis f i i) := by
  obtain ⟨b, z, hz, hb⟩ := exists_eigenbasis_of_charpoly_separable n f hdim hsep
  obtain ⟨e, he⟩ := exists_schurOrderingPermutation z hz
  have hb' : ∀ i, f ((b.reindex e.symm) i) = z (e i) • (b.reindex e.symm) i := by
    intro i
    simpa only [Basis.reindex_apply, Equiv.symm_symm] using hb (e i)
  obtain ⟨q, hq, hd⟩ := gramSchmidt_eigenbasis_diagonal f (b.reindex e.symm)
    (fun i => z (e i)) hb'
  refine ⟨q, hq, ?_⟩
  simpa only [hd] using he

/-- **HKPV actual ordered unitary Schur representation**. Ordering is
proved in the construction and is not supplied as an external premise. -/
theorem exists_unitary_ordered_schur_of_separable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hsep : A.charpoly.Separable) :
    ∃ U S : Matrix (Fin n) (Fin n) ℂ,
      U.conjTranspose * U = 1 ∧ S.IsUpperTriangular ∧
        schurDiagonalOrdered (fun i => S i i) ∧ A = U * S * U.conjTranspose := by
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  let f : Module.End ℂ (EuclideanSpace ℂ (Fin n)) := Matrix.toLin e.toBasis e.toBasis A
  have hf : f.charpoly.Separable := by
    change (Matrix.toLin e.toBasis e.toBasis A).charpoly.Separable
    rwa [Matrix.charpoly_toLin]
  have hdim : finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by
    rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  obtain ⟨q, hq, ho⟩ := exists_orthonormal_ordered_schur_basis n f hdim hf
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
  exact ⟨U, S, hU, hq, ho, heq.symm⟩

/-- HKPV the actual Gaussian matrix almost surely has an ordered Schur
representation, with no eigenvalue-law or ordering-existence input. -/
theorem gaussianMatrix_exists_ordered_schur_ae (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ A ∂gaussianMatrixLaw n a,
      ∃ U S : Matrix (Fin n) (Fin n) ℂ,
        U.conjTranspose * U = 1 ∧ S.IsUpperTriangular ∧
          schurDiagonalOrdered (fun i => S i i) ∧
            Matrix.of A.curry = U * S * U.conjTranspose := by
  filter_upwards [gaussianMatrix_charpoly_separable_ae n ha] with A hA
  exact exists_unitary_ordered_schur_of_separable (Matrix.of A.curry) hA

end Ginibre
