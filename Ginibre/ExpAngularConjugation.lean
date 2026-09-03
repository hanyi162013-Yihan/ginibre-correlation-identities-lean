import Ginibre.MovingConjugation

/-!
# The actual exponential moving frame at arbitrary angular parameters

HKPV (6.3.2). The angular derivative is the derivative of an explicitly
defined exponential, not an unspecified matrix-valued input. Separating
the angular and triangular variables makes its independence of the
triangular factor a theorem of the construction.
-/

noncomputable section
namespace Ginibre

/-- HKPV analytic angular parametrization is differentiable everywhere. -/
theorem differentiable_exp_linear {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    (W : E →L[ℝ] R) : Differentiable ℝ (fun w => NormedSpace.exp (W w)) := by
  intro w
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) (W w)).differentiableAt.comp w
    W.differentiableAt

/-- HKPV inverse frame: negative angular exponentials are actual left
inverses at every parameter. -/
theorem exp_neg_linear_mul_exp {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    (W : E →L[ℝ] R) (w : E) :
    NormedSpace.exp (-W w) * NormedSpace.exp (W w) = 1 := by
  let : NormedAlgebra ℚ R := NormedAlgebra.restrictScalars ℚ ℝ R
  rw [← NormedSpace.exp_add_of_commute (Commute.refl (W w)).neg_left,
    neg_add_cancel, NormedSpace.exp_zero]

/-- **HKPV full moving-frame derivative at any angular parameter**.
`U⁻¹ dU` depends on `x.1` and `v.1` alone. Both exponentials and their
derivatives are actual functions; every differentiability premise is
discharged here. -/
theorem fderiv_exp_angular_conjugation_rotated {E F R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    (S : R) (W : E →L[ℝ] R) (T : F →L[ℝ] R) (x v : E × F) :
    NormedSpace.exp (-W x.1) *
      (fderiv ℝ (fun y : E × F => NormedSpace.exp (W y.1) *
        (S + T y.2) * NormedSpace.exp (-W y.1)) x v) * NormedSpace.exp (W x.1) =
      T v.2 +
        ((NormedSpace.exp (-W x.1) *
            fderiv ℝ (fun w => NormedSpace.exp (W w)) x.1 v.1) * (S + T x.2) -
          (S + T x.2) * (NormedSpace.exp (-W x.1) *
            fderiv ℝ (fun w => NormedSpace.exp (W w)) x.1 v.1)) := by
  have hU : HasFDerivAt (fun y : E × F => NormedSpace.exp (W y.1))
      ((fderiv ℝ (fun w => NormedSpace.exp (W w)) x.1).comp
        (ContinuousLinearMap.fst ℝ E F)) x :=
    ((differentiable_exp_linear W x.1).hasFDerivAt).comp x
      (ContinuousLinearMap.fst ℝ E F).hasFDerivAt
  have hV : DifferentiableAt ℝ
      (fun y : E × F => NormedSpace.exp (-W y.1)) x :=
    (differentiable_exp_linear (-W) x.1).comp x
      (ContinuousLinearMap.fst ℝ E F).differentiableAt
  have hT : HasFDerivAt (fun y : E × F => S + T y.2)
      (T.comp (ContinuousLinearMap.snd ℝ E F)) x :=
    (T.comp (ContinuousLinearMap.snd ℝ E F)).hasFDerivAt.const_add S
  have h := fderiv_conjugation_rotated hU.differentiableAt hV hT.differentiableAt
    (fun y => exp_neg_linear_mul_exp W y.1) v
  rw [hU.fderiv, hT.fderiv] at h
  exact h

end Ginibre
