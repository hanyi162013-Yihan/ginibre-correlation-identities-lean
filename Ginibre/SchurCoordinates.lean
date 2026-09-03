import Ginibre.SchurTangent
import Ginibre.ExpConjugation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Instances.Matrix

/-!
# Actual local Schur coordinates from the matrix exponential

HKPV Section 6.3, local-coordinate justification for (6.3.2).
We use the transversal `exp Ω(ω)`, where `Ω` is skew-Hermitian with zero
diagonal. The coordinate map is an actual unitary conjugation of `S + D`.
Its strict Fréchet derivative at zero is the complete Schur tangent map.
The inverse function theorem therefore provides an injective open chart
around each simple-diagonal upper-triangular matrix.

Choosing the usual operator matrix norm below only equips the existing
finite-dimensional topology with a submultiplicative norm for calculus.
It does not change the matrix measure or postulate a change of variables.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV independent angular variation as a continuous real-linear map. -/
def schurSkewTangentCLM (n : ℕ) : SchurTangent n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => schurSkewEmbed x.1
    map_add' := fun x y => schurSkewEmbed_add x.1 y.1
    map_smul' := fun r x => schurSkewEmbed_real_smul r x.1 }

/-- HKPV upper-triangular variation as a continuous real-linear map. -/
def schurUpperTangentCLM (n : ℕ) : SchurTangent n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => x.2.val
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- HKPV local angular parametrization, with diagonal phase directions removed. -/
def schurUnitaryParam {n : ℕ} (x : SchurTangent n) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (schurSkewTangentCLM n x)

/-- HKPV this parametrization really takes its values in the unitary group. -/
theorem schurUnitaryParam_unitary {n : ℕ} (x : SchurTangent n) :
    (schurUnitaryParam x).conjTranspose * schurUnitaryParam x = 1 := by
  change (NormedSpace.exp (schurSkewEmbed x.1)).conjTranspose *
    NormedSpace.exp (schurSkewEmbed x.1) = 1
  rw [← Matrix.exp_conjTranspose, schurSkewEmbed_conjTranspose, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))

/-- HKPV the right exponential is exactly the adjoint of the left one. -/
theorem schurUnitaryParam_adjoint {n : ℕ} (x : SchurTangent n) :
    (schurUnitaryParam x).conjTranspose =
      NormedSpace.exp (-schurSkewTangentCLM n x) := by
  change star (NormedSpace.exp (schurSkewEmbed x.1)) = _
  rw [NormedSpace.star_exp, Matrix.star_eq_conjTranspose, schurSkewEmbed_conjTranspose]
  rfl

/-- HKPV actual local Schur parametrization, not a formal linearization. -/
def schurExpCoordinates {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (x : SchurTangent n) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (schurSkewTangentCLM n x) * (S + schurUpperTangentCLM n x) *
    NormedSpace.exp (-schurSkewTangentCLM n x)

/-- HKPV the parametrization has the prescribed triangular center. -/
theorem schurExpCoordinates_zero {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) :
    schurExpCoordinates S 0 = S := by
  simp [schurExpCoordinates]

/-- HKPV the coordinate formula is unitary conjugation at every parameter. -/
theorem schurExpCoordinates_eq_conjugation {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (x : SchurTangent n) :
    schurExpCoordinates S x =
      schurUnitaryParam x * (S + x.2.val) * (schurUnitaryParam x).conjTranspose := by
  rw [schurUnitaryParam_adjoint]
  rfl

/-- **HKPV (6.3.2), full strict Fréchet derivative**: this differentiates
an explicitly constructed map in all independent real coordinates. -/
theorem hasStrictFDerivAt_schurExpCoordinates {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (schurExpCoordinates S)
      (LinearMap.toContinuousLinearMap (schurTangentMap S)) 0 := by
  convert! (hasStrictFDerivAt_exp_conjugation S
    (schurSkewTangentCLM n) (schurUpperTangentCLM n)) using 1
  apply ContinuousLinearMap.ext
  intro x
  change x.2.val + (schurSkewEmbed x.1 * S - S * schurSkewEmbed x.1) =
    x.2.val + schurSkewEmbed x.1 * S - S * schurSkewEmbed x.1
  abel

/-- HKPV local invertibility follows from the proved full differential,
not from an assumed Schur-chart interface. -/
def schurLocalChart {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (hz : Function.Injective (fun i => S i i)) :
    OpenPartialHomeomorph (SchurTangent n) (Matrix (Fin n) (Fin n) ℂ) :=
  (show HasStrictFDerivAt (schurExpCoordinates S)
    (schurTangentEquiv S hS hz : SchurTangent n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) 0 from
      hasStrictFDerivAt_schurExpCoordinates S).toOpenPartialHomeomorph (schurExpCoordinates S)

/-- HKPV zero belongs to the source of the constructed injective chart. -/
theorem schurLocalChart_zero_mem_source {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i)) :
    0 ∈ (schurLocalChart S hS hz).source :=
  (show HasStrictFDerivAt (schurExpCoordinates S)
    (schurTangentEquiv S hS hz : SchurTangent n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) 0 from
      hasStrictFDerivAt_schurExpCoordinates S).mem_toOpenPartialHomeomorph_source

/-- HKPV the target is an actual open neighborhood of the matrix `S`. -/
theorem schurLocalChart_center_mem_target {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i)) :
    S ∈ (schurLocalChart S hS hz).target := by
  have h := (schurLocalChart S hS hz).map_source (schurLocalChart_zero_mem_source S hS hz)
  change schurExpCoordinates S 0 ∈ _ at h
  rwa [schurExpCoordinates_zero] at h

end Ginibre
