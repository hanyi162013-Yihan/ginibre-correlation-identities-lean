import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable

/-!
# An eigenvector basis on the simple-spectrum locus

HKPV Section 6.3, existence part of Schur coordinates. A separable complex
characteristic polynomial has exactly as many distinct roots as the vector
space dimension. Choosing one eigenvector for each root gives a basis.
This is an existence theorem, not a claim that this choice is continuous
or measurable as a function of the matrix.
-/

noncomputable section
open Module
namespace Ginibre

/-- HKPV simple-spectrum bookkeeping: all characteristic roots are distinct
and their number is the dimension, including dimension zero. -/
theorem card_charpoly_distinct_roots {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (f : Module.End ℂ E) (hsep : f.charpoly.Separable) :
    f.charpoly.roots.toFinset.card = finrank ℂ E := by
  classical
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
    ← (IsAlgClosed.splits f.charpoly).natDegree_eq_card_roots, LinearMap.charpoly_natDegree]

/-- **HKPV eigenbasis construction**: no diagonalizability or eigenbasis
interface is assumed; separability supplies every required eigenvector. -/
theorem exists_eigenbasis_of_charpoly_separable {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (n : ℕ) (f : Module.End ℂ E) (hdim : finrank ℂ E = n)
    (hsep : f.charpoly.Separable) :
    ∃ (b : Basis (Fin n) ℂ E) (z : Fin n → ℂ),
      Function.Injective z ∧ ∀ i, f (b i) = z i • b i := by
  classical
  let roots := f.charpoly.roots.toFinset
  have hc : Fintype.card roots = n := by
    rw [Fintype.card_coe, card_charpoly_distinct_roots f hsep, hdim]
  let e : Fin n ≃ roots := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hc.symm)
  let z : Fin n → ℂ := fun i => (e i).val
  have hz : Function.Injective z := Subtype.val_injective.comp e.injective
  have hev (i : Fin n) : f.HasEigenvalue (z i) := by
    apply (Module.End.hasEigenvalue_iff_isRoot_charpoly f (z i)).mpr
    apply (Polynomial.mem_roots (LinearMap.charpoly_monic f).ne_zero).mp
    exact Multiset.mem_toFinset.mp (e i).property
  choose v hv using (fun i => (hev i).exists_hasEigenvector)
  have hli : LinearIndependent ℂ v := f.eigenvectors_linearIndependent' z hz v hv
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simpa only [Fintype.card_fin] using hdim.symm)
  let b : Basis (Fin n) ℂ E := Basis.mk hli hspan.ge
  refine ⟨b, z, hz, ?_⟩
  intro i
  simpa only [b, Basis.coe_mk] using (hv i).apply_eq_smul

/-- HKPV eigenbasis coordinates: the operator matrix is genuinely diagonal. -/
theorem toMatrix_eigenbasis {E : Type*} [AddCommGroup E] [Module ℂ E] {n : ℕ}
    (f : Module.End ℂ E) (b : Basis (Fin n) ℂ E) (z : Fin n → ℂ)
    (hb : ∀ i, f (b i) = z i • b i) :
    LinearMap.toMatrix b b f = Matrix.diagonal z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrix_apply, hb, Matrix.diagonal_apply]
  · simp [LinearMap.toMatrix_apply, hb, Matrix.diagonal_apply, Finsupp.single_apply,
      hij, Ne.symm hij]

end Ginibre
