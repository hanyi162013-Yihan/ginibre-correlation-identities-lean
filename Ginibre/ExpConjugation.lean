import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Abel

/-!
# Strict differentiation of exponential conjugation in a Banach algebra

The analytic lemma underlying the actual Schur coordinates, HKPV (6.3.2).
Working in an arbitrary real Banach algebra keeps the calculus separate
from choices of equivalent norms on finite-dimensional matrix spaces.
-/

noncomputable section
open scoped RightActions
namespace Ginibre

/-- HKPV exponential coordinates: a linear angular map exponentiates
to a map with the same strict derivative at the origin. -/
theorem hasStrictFDerivAt_exp_linear {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    (W : E →L[ℝ] R) :
    HasStrictFDerivAt (fun x => NormedSpace.exp (W x)) W 0 := by
  have he : HasStrictFDerivAt (NormedSpace.exp : R → R) (1 : R →L[ℝ] R) (W 0) := by
    simpa only [map_zero] using (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := R))
  simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using
    he.comp 0 W.hasStrictFDerivAt

/-- **HKPV (6.3.2), analytic product rule**: the strict derivative of
`exp(W x) * (S + T x) * exp(-W x)` is `T x + W x*S - S*W x`. -/
theorem hasStrictFDerivAt_exp_conjugation {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    (S : R) (W T : E →L[ℝ] R) :
    HasStrictFDerivAt
      (fun x => NormedSpace.exp (W x) * (S + T x) * NormedSpace.exp (-W x))
      (T + (W <• S) - S • W) 0 := by
  have hW := hasStrictFDerivAt_exp_linear W
  have hN : HasStrictFDerivAt (fun x => NormedSpace.exp (-W x)) (-W) 0 :=
    hasStrictFDerivAt_exp_linear (-W)
  have hT : HasStrictFDerivAt (fun x => S + T x) T 0 := T.hasStrictFDerivAt.const_add S
  have h := (hW.fun_mul' hT).fun_mul' hN
  apply h.congr_fderiv
  ext x
  simp only [map_zero, neg_zero, NormedSpace.exp_zero, add_zero, one_mul, one_smul]
  change S * (-W x) + (T x + W x * S) * 1 = T x + W x * S - S * W x
  rw [mul_one, mul_neg, sub_eq_add_neg]
  abel

end Ginibre
