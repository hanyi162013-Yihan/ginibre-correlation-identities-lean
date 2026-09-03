import Ginibre.SchurRegularity
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The complete real Schur tangent map is an isomorphism

HKPV (6.3.2)--(6.3.4). The lower block determines the independent
skew-Hermitian variation uniquely; subtracting its commutator leaves the
unique upper-triangular variation. This proves invertibility of the full
real-linear map, not merely a determinant identity for one block.

The map is real-linear, not complex-linear: completion by the negative
adjoint conjugates the independent coordinates. Actual phase-fixed charts
and their strict Fréchet derivatives are separate from this linear result.
-/

noncomputable section
open OrderDual
open scoped Matrix
namespace Ginibre

/-- HKPV triangular tangent variables, with their genuine real vector-space structure. -/
def schurUpperSubmodule (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  (Matrix.blockTriangularSubalgebra ℝ ℂ (id : Fin n → Fin n)).toSubmodule

/-- HKPV independent tangent variables after removal of the diagonal phase directions. -/
abbrev SchurTangent (n : ℕ) := (SchurLower n → ℂ) × schurUpperSubmodule n

/-- HKPV coordinate embedding respects addition. -/
theorem schurLowerEmbed_add {n : ℕ} (ω η : SchurLower n → ℂ) :
    schurLowerEmbed (ω + η) = schurLowerEmbed ω + schurLowerEmbed η := by
  simp only [schurLowerEmbed, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- HKPV coordinate embedding respects real scaling. -/
theorem schurLowerEmbed_real_smul {n : ℕ} (r : ℝ) (ω : SchurLower n → ℂ) :
    schurLowerEmbed (r • ω) = r • schurLowerEmbed ω := by
  simp only [schurLowerEmbed, Pi.smul_apply, smul_assoc, Finset.smul_sum]

/-- HKPV the skew-Hermitian completion is additive. -/
theorem schurSkewEmbed_add {n : ℕ} (ω η : SchurLower n → ℂ) :
    schurSkewEmbed (ω + η) = schurSkewEmbed ω + schurSkewEmbed η := by
  simp only [schurSkewEmbed, schurLowerEmbed_add, Matrix.conjTranspose_add]
  abel

/-- HKPV the skew-Hermitian completion is linear over the real scalars. -/
theorem schurSkewEmbed_real_smul {n : ℕ} (r : ℝ) (ω : SchurLower n → ℂ) :
    schurSkewEmbed (r • ω) = r • schurSkewEmbed ω := by
  simp [schurSkewEmbed, schurLowerEmbed_real_smul, Matrix.conjTranspose_smul, smul_sub]

/-- HKPV (6.3.2), all output entries: `(ω,D) ↦ D + [Ω(ω),S]`. -/
def schurTangentMap {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) :
    SchurTangent n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun x := x.2.val + (schurSkewEmbed x.1 * S - S * schurSkewEmbed x.1)
  map_add' x y := by
    change (x.2.val + y.2.val) +
      (schurSkewEmbed (x.1 + y.1) * S - S * schurSkewEmbed (x.1 + y.1)) = _
    rw [schurSkewEmbed_add, Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' r x := by
    change r • x.2.val +
      (schurSkewEmbed (r • x.1) * S - S * schurSkewEmbed (r • x.1)) = _
    rw [schurSkewEmbed_real_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_add, smul_sub]
    rfl

/-- HKPV simple diagonal entries make the complex lower block invertible. -/
theorem isUnit_schurLowerMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (hz : Function.Injective (fun i => S i i)) :
    IsUnit (schurLowerMatrix S) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [det_schurLowerMatrix S hS]
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact sub_ne_zero.mpr (hz.ne (ne_of_lt p.property))

/-- HKPV the lower rows of the complete map are exactly the previously
computed Vandermonde-producing block. -/
theorem schurTangentMap_lower {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (x : SchurTangent n) (p : SchurLower n) :
    schurTangentMap S x (schurRow p) (schurCol p) =
      (schurLowerMatrix S *ᵥ x.1) p :=
  schur_differential_lower S x.2.val hS x.2.property x.1 p

/-- HKPV no tangent direction remains in the kernel once diagonal
unitary phases have been removed and the spectrum is simple. -/
theorem schurTangentMap_injective {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (hz : Function.Injective (fun i => S i i)) :
    Function.Injective (schurTangentMap S) := by
  rintro ⟨ω, D⟩ ⟨η, E⟩ h
  have hl : schurLowerMatrix S *ᵥ ω = schurLowerMatrix S *ᵥ η := by
    funext p
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ =>
      A (schurRow p) (schurCol p)) h
    simpa only [schurTangentMap_lower S hS] using he
  have hω : ω = η := (Matrix.mulVec_injective_iff_isUnit.mpr
    (isUnit_schurLowerMatrix S hS hz)) hl
  apply Prod.ext hω
  apply Subtype.ext
  change D.val + (schurSkewEmbed ω * S - S * schurSkewEmbed ω) =
    E.val + (schurSkewEmbed η * S - S * schurSkewEmbed η) at h
  rw [hω] at h
  exact add_right_cancel h

/-- HKPV constructive linear solve: solve the lower equations for `ω`,
then the residual is the required upper-triangular `D`. -/
theorem schurTangentMap_surjective {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (hz : Function.Injective (fun i => S i i)) :
    Function.Surjective (schurTangentMap S) := by
  intro B
  obtain ⟨ω, hω⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    (isUnit_schurLowerMatrix S hS hz)) (fun p => B (schurRow p) (schurCol p))
  let C := schurSkewEmbed ω * S - S * schurSkewEmbed ω
  have hD : (B - C).IsUpperTriangular := by
    intro i j hij
    let p : SchurLower n := ⟨toLex (toDual i, j), hij⟩
    have he := congrFun hω p
    rw [schurLowerMatrix_mulVec_skew S hS] at he
    change C i j = B i j at he
    exact sub_eq_zero.mpr he.symm
  refine ⟨(ω, ⟨B - C, hD⟩), ?_⟩
  change B - C + C = B
  exact sub_add_cancel B C

/-- HKPV the full tangent map, as a continuous real-linear equivalence.
This is ready to serve as the derivative in a local inverse theorem. -/
def schurTangentEquiv {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (hz : Function.Injective (fun i => S i i)) :
    SchurTangent n ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (LinearEquiv.ofBijective (schurTangentMap S)
    ⟨schurTangentMap_injective S hS hz,
      schurTangentMap_surjective S hS hz⟩).toContinuousLinearEquiv

/-- HKPV the equivalence really is the commutator differential, not
an unrelated dimension-counting isomorphism. -/
theorem schurTangentEquiv_apply {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (hz : Function.Injective (fun i => S i i))
    (x : SchurTangent n) :
    schurTangentEquiv S hS hz x =
      x.2.val + (schurSkewEmbed x.1 * S - S * schurSkewEmbed x.1) := rfl

end Ginibre
