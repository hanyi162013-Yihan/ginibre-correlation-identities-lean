import Ginibre.SchurTangent

/-!
# Splitting matrix-entry coordinates into the independent Schur variables

HKPV (6.3.2)--(6.3.5). This is a fixed real-linear coordinate isomorphism,
not the nonlinear Schur map and not a postulated spectral distribution.
The lower coordinates are literal matrix entries, and the upper component
retains all the other entries. This permits a determinant of the full
Schur differential as an endomorphism of a single coordinate space.
-/

noncomputable section
open OrderDual
namespace Ginibre

/-- HKPV the fixed projection onto strictly lower matrix entries. -/
def schurLowerEntries {n : ℕ} :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (SchurLower n → ℂ) where
  toFun A p := A (schurRow p) (schurCol p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- HKPV the lower-entry embedding, now packaged as a real-linear map. -/
def schurLowerEntryMap (n : ℕ) :
    (SchurLower n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := schurLowerEmbed
  map_add' := schurLowerEmbed_add
  map_smul' := schurLowerEmbed_real_smul

/-- HKPV reading back the lower entries is a left inverse to their embedding. -/
theorem schurLowerEntries_embed {n : ℕ} (ω : SchurLower n → ℂ) :
    schurLowerEntries (schurLowerEmbed ω) = ω := by
  funext p
  exact schurLowerEmbed_apply_lower ω p

/-- HKPV strictly lower entries of an upper-triangular matrix vanish. -/
theorem schurLowerEntries_upper {n : ℕ} (D : schurUpperSubmodule n) :
    schurLowerEntries D.val = 0 := by
  funext p
  exact D.property p.property

/-- HKPV subtracting exactly the lower entries leaves an upper-triangular matrix. -/
theorem schur_upper_residual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A - schurLowerEmbed (schurLowerEntries A)).IsUpperTriangular := by
  intro i j hij
  let p : SchurLower n := ⟨toLex (toDual i, j), hij⟩
  have he := schurLowerEmbed_apply_lower (schurLowerEntries A) p
  change schurLowerEmbed (schurLowerEntries A) i j = A i j at he
  exact sub_eq_zero.mpr he.symm

/-- HKPV the fixed upper-entry projection, including the diagonal entries. -/
def schurUpperEntries {n : ℕ} :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] schurUpperSubmodule n :=
  LinearMap.codRestrict (schurUpperSubmodule n)
    (LinearMap.id - (schurLowerEntryMap n).comp schurLowerEntries)
    schur_upper_residual

/-- HKPV this projection fixes every upper-triangular matrix. -/
theorem schurUpperEntries_upper {n : ℕ} (D : schurUpperSubmodule n) :
    schurUpperEntries D.val = D := by
  apply Subtype.ext
  change D.val - schurLowerEmbed (schurLowerEntries D.val) = D.val
  rw [schurLowerEntries_upper]
  have hz : schurLowerEmbed (0 : SchurLower n → ℂ) = 0 := (schurLowerEntryMap n).map_zero
  rw [hz, sub_zero]

/-- HKPV fixed matrix-entry coordinates: lower entries together with all
upper entries. This equivalence contains no choice of eigenvectors. -/
def schurEntrySplit (n : ℕ) : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] SchurTangent n where
  toFun A := (schurLowerEntries A, schurUpperEntries A)
  invFun x := schurLowerEmbed x.1 + x.2.val
  left_inv A := by
    change schurLowerEmbed (schurLowerEntries A) +
      (A - schurLowerEmbed (schurLowerEntries A)) = A
    abel
  right_inv x := by
    have hl : schurLowerEntries (schurLowerEmbed x.1 + x.2.val) = x.1 := by
      rw [map_add, schurLowerEntries_embed, schurLowerEntries_upper, add_zero]
    apply Prod.ext hl
    apply Subtype.ext
    change (schurLowerEmbed x.1 + x.2.val) -
      schurLowerEmbed (schurLowerEntries (schurLowerEmbed x.1 + x.2.val)) = x.2.val
    rw [hl]
    abel
  map_add' A B := by
    exact Prod.ext (schurLowerEntries.map_add A B) (schurUpperEntries.map_add A B)
  map_smul' r A := by
    exact Prod.ext (schurLowerEntries.map_smul r A) (schurUpperEntries.map_smul r A)

/-- HKPV the split is exactly the two stated entry projections. -/
theorem schurEntrySplit_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    schurEntrySplit n A = (schurLowerEntries A, schurUpperEntries A) := rfl

/-- HKPV reconstructing a matrix from its split coordinates just joins its entries. -/
theorem schurEntrySplit_symm_apply {n : ℕ} (x : SchurTangent n) :
    (schurEntrySplit n).symm x = schurLowerEmbed x.1 + x.2.val := rfl

end Ginibre
