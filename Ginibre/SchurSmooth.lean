import Ginibre.SchurCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness and the inverse derivative of the actual Schur charts

HKPV Section 6.3, analytic regularity of the exponential-coordinate map.
Smoothness holds on the whole parameter space; the inverse derivative is
proved at the center of the injective local chart. No integration formula
or global invertibility of the exponential is asserted.
-/

noncomputable section
open scoped ContDiff
namespace Ginibre

/-- HKPV exponential-coordinate regularity, in a general real Banach algebra. -/
theorem contDiff_exp_conjugation {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    (k : ℕ∞ω) (S : R) (W T : E →L[ℝ] R) :
    ContDiff ℝ k
      (fun x => NormedSpace.exp (W x) * (S + T x) * NormedSpace.exp (-W x)) := by
  have he : ContDiff ℝ k (NormedSpace.exp : R → R) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : R → R) Set.univ from
      fun x _ => NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiff
  exact ((he.comp W.contDiff).mul (contDiff_const.add T.contDiff)).mul
    (he.comp W.contDiff.neg)

open scoped Matrix Matrix.Norms.Operator

/-- HKPV the constructed matrix coordinate map is smooth (indeed analytic)
on its entire parameter space, not just differentiable at one point. -/
theorem contDiff_schurExpCoordinates {n : ℕ} (k : ℕ∞ω)
    (S : Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ k (schurExpCoordinates S) := by
  convert! contDiff_exp_conjugation k S (schurSkewTangentCLM n) (schurUpperTangentCLM n)

/-- HKPV inverse-coordinate regularity at the center: the inverse chart
has exactly the inverse of the proved commutator differential. -/
theorem hasStrictFDerivAt_schurLocalChart_symm {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i)) :
    HasStrictFDerivAt (schurLocalChart S hS hz).symm
      ((schurTangentEquiv S hS hz).symm : Matrix (Fin n) (Fin n) ℂ →L[ℝ] SchurTangent n) S := by
  have h : HasStrictFDerivAt (schurExpCoordinates S)
      (schurTangentEquiv S hS hz : SchurTangent n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) 0 :=
    hasStrictFDerivAt_schurExpCoordinates S
  have hi := h.to_localInverse
  rw [schurExpCoordinates_zero] at hi
  exact hi

end Ginibre
