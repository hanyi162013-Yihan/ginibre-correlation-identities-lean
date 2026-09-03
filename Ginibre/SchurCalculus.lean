import Ginibre.SchurDifferential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Differentiating matrix conjugation in Schur coordinates

HKPV (6.3.2). These are derivatives of the actual conjugation map, checked
entry by entry over the real parameter field. This avoids imposing a
particular norm on the matrix algebra. The hypotheses are ordinary
derivatives of coordinate curves, not a spectral-law interface.
-/

noncomputable section
open scoped BigOperators Matrix
namespace Ginibre

/-- HKPV differential bookkeeping: the usual product rule for matrix entries. -/
theorem hasDerivAt_matrix_mul_entry {n : ℕ}
    (A B : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (A' B' : Matrix (Fin n) (Fin n) ℂ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) x)
    (hB : ∀ i j, HasDerivAt (fun t => B t i j) (B' i j) x)
    (i j : Fin n) :
    HasDerivAt (fun t => (A t * B t) i j)
      ((A' * B x + A x * B') i j) x := by
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hA i k).fun_mul (hB k j)))

/-- HKPV (6.3.2): adjoint differentiation is real-linear, with no holomorphicity claim. -/
theorem hasDerivAt_matrix_conjTranspose_entry {n : ℕ}
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ) (Ω : Matrix (Fin n) (Fin n) ℂ) (x : ℝ)
    (hU : ∀ i j, HasDerivAt (fun t => U t i j) (Ω i j) x) (i j : Fin n) :
    HasDerivAt (fun t => (U t).conjTranspose i j) (Ω.conjTranspose i j) x :=
  (hU j i).star

/-- **HKPV (6.3.2), derivative of actual conjugation** at the identity frame. -/
theorem hasDerivAt_schur_conjugation_entry {n : ℕ}
    (U V : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (Ω D S : Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i j, HasDerivAt (fun t => U t i j) (Ω i j) 0)
    (hV : ∀ i j, HasDerivAt (fun t => V t i j) (D i j) 0)
    (hU0 : U 0 = 1) (hV0 : V 0 = S) (i j : Fin n) :
    HasDerivAt (fun t => (U t * V t * (U t).conjTranspose) i j)
      ((Ω * S + D + S * Ω.conjTranspose) i j) 0 := by
  have hUV := hasDerivAt_matrix_mul_entry U V Ω D 0 hU hV
  have h := hasDerivAt_matrix_mul_entry (fun t => U t * V t)
    (fun t => (U t).conjTranspose) (Ω * V 0 + U 0 * D) Ω.conjTranspose 0
    hUV (hasDerivAt_matrix_conjTranspose_entry U Ω 0 hU) i j
  simpa only [hU0, hV0, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using h

/-- HKPV tangent-space justification: differentiating a unitary curve gives
the skew-Hermitian constraint, rather than adding it as an external input. -/
theorem unitary_curve_derivative_skew {n : ℕ}
    (U : ℝ → Matrix (Fin n) (Fin n) ℂ) (Ω : Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ i j, HasDerivAt (fun t => U t i j) (Ω i j) 0)
    (hU0 : U 0 = 1) (hunit : ∀ t, (U t).conjTranspose * U t = 1) :
    Ω.conjTranspose = -Ω := by
  ext i j
  have h := hasDerivAt_matrix_mul_entry (fun t => (U t).conjTranspose) U
    Ω.conjTranspose Ω 0 (hasDerivAt_matrix_conjTranspose_entry U Ω 0 hU) hU i j
  have hc : HasDerivAt (fun t => ((U t).conjTranspose * U t) i j) 0 0 := by
    simpa only [hunit] using (hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℂ) i j))
  have heq := h.unique hc
  simp only [hU0, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.add_apply] at heq
  exact eq_neg_of_add_eq_zero_left heq

/-- **HKPV (6.3.2)--(6.3.4), analytic identification of the Jacobian block**:
the lower derivative of matrix conjugation is the matrix whose determinant
was proved to be the Vandermonde factor. -/
theorem hasDerivAt_schur_lower_entry {n : ℕ}
    (U V : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (D S : Matrix (Fin n) (Fin n) ℂ) (ω : SchurLower n → ℂ)
    (hU : ∀ i j, HasDerivAt (fun t => U t i j) (schurSkewEmbed ω i j) 0)
    (hV : ∀ i j, HasDerivAt (fun t => V t i j) (D i j) 0)
    (hU0 : U 0 = 1) (hV0 : V 0 = S)
    (hS : S.IsUpperTriangular) (hD : D.IsUpperTriangular) (p : SchurLower n) :
    HasDerivAt (fun t => (U t * V t * (U t).conjTranspose) (schurRow p) (schurCol p))
      ((schurLowerMatrix S *ᵥ ω) p) 0 := by
  apply (hasDerivAt_schur_conjugation_entry U V (schurSkewEmbed ω) D S
    hU hV hU0 hV0 (schurRow p) (schurCol p)).congr_deriv
  rw [schurSkewEmbed_conjTranspose, Matrix.mul_neg]
  have heq : schurSkewEmbed ω * S + D + -(S * schurSkewEmbed ω) =
      D + (schurSkewEmbed ω * S - S * schurSkewEmbed ω) := by abel
  rw [heq]
  exact schur_differential_lower S D hS hD ω p

end Ginibre
