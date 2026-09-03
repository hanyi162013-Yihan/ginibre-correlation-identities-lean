import Ginibre.ExpConjugation

/-!
# Differentiation in a moving conjugation frame

HKPV (6.3.2), away from the center of a Schur chart. These Banach-algebra
lemmas prove the moving-frame product rule without assuming a formula for
the derivative of the exponential or for a matrix spectral density.
-/

noncomputable section
namespace Ginibre

/-- HKPV product rule evaluated on a tangent vector, retaining the order
of multiplication in a possibly noncommutative algebra. -/
theorem fderiv_mul_apply {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R]
    {f g : E → R} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y * g y) x v =
      f x * fderiv ℝ g x v + fderiv ℝ f x v * g x := by
  rw [(hf.hasFDerivAt.fun_mul' hg.hasFDerivAt).fderiv]
  rfl

/-- HKPV differentiation of the inverse-frame identity `V U = 1`. -/
theorem inverse_frame_derivative {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R]
    {U V : E → R} {x : E}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hVU : ∀ y, V y * U y = 1) (v : E) :
    fderiv ℝ V x v * U x = -(V x * fderiv ℝ U x v) := by
  have he := fderiv_mul_apply hV hU v
  have hc : (fun y => V y * U y) = fun _ => (1 : R) := funext hVU
  rw [hc] at he
  have hz : fderiv ℝ (fun _ : E => (1 : R)) x = 0 := (hasFDerivAt_const (1 : R) x).fderiv
  rw [hz] at he
  exact eq_neg_of_add_eq_zero_right he.symm

/-- **HKPV (6.3.2), at every differentiable parameter**: rotating the
actual derivative back to its triangular frame yields `dS + [V dU, S]`.
The inverse derivative is deduced from `VU=1`, not supplied as an input. -/
theorem fderiv_conjugation_rotated {E R : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing R] [NormedAlgebra ℝ R]
    {U V S : E → R} {x : E}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hS : DifferentiableAt ℝ S x) (hVU : ∀ y, V y * U y = 1) (v : E) :
    V x * (fderiv ℝ (fun y => U y * S y * V y) x v) * U x =
      fderiv ℝ S x v +
        ((V x * fderiv ℝ U x v) * S x - S x * (V x * fderiv ℝ U x v)) := by
  have hUS : DifferentiableAt ℝ (fun y => U y * S y) x := hU.mul hS
  rw [fderiv_mul_apply hUS hV v, fderiv_mul_apply hU hS v]
  have hi := inverse_frame_derivative hU hV hVU v
  calc
    _ = S x * (fderiv ℝ V x v * U x) +
        fderiv ℝ S x v + (V x * fderiv ℝ U x v) * S x := by
      simp only [mul_add, add_mul, mul_assoc, hVU x, mul_one]
      simp only [← mul_assoc, hVU x, one_mul]
      abel
    _ = _ := by rw [hi, mul_neg]; abel

end Ginibre
