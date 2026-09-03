import Ginibre.SpectralCounting
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# One- and two-point weights for Ginibre linear statistics

BC12 Theorems 3.3--3.4. These are the concrete planar forms of the
one- and two-point correlation determinants. The coordinate equivalences
below make the passage from `Fin 1` and `Fin 2` product volume explicit.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- BC12 unnormalized one-point intensity. -/
def ginibreIntensity (n : ℕ) (z : ℂ) : ℝ := (n : ℝ) * onePointDensity n z

/-- BC12 two-point intensity in its off-diagonal-subtraction form. -/
def ginibrePairIntensity (n : ℕ) (z w : ℂ) : ℝ :=
  ginibreIntensity n z * ginibreIntensity n w - kernelWeight n (z, w)

/-- BC12 the diagonal of the kernel is the one-point intensity. -/
theorem kernel_diagonal_re (n : ℕ) (z : ℂ) : (kernel n z z).re = ginibreIntensity n z := by
  rw [kernel_diagonal]
  rfl

/-- BC12 the one-point intensity is nonnegative. -/
theorem ginibreIntensity_nonneg (n : ℕ) (z : ℂ) : 0 ≤ ginibreIntensity n z := by
  rw [← kernel_diagonal_re]
  have h := norm_kernelDet n 1 (fun _ => z)
  rw [kernelDet_one] at h
  rw [← h]
  exact norm_nonneg _

/-- BC12 exact total mass of the one-point intensity. -/
theorem integrable_ginibreIntensity (n : ℕ) : Integrable (ginibreIntensity n) := by
  have h := (integrable_kernel_diagonal n).re
  apply h.congr
  filter_upwards with z
  simpa only [RCLike.re_eq_complex_re] using kernel_diagonal_re n z

/-- BC12 the intensity integrates to the matrix dimension. -/
theorem integral_ginibreIntensity (n : ℕ) : (∫ z, ginibreIntensity n z) = n := by
  have h := integral_re (integrable_kernel_diagonal n)
  rw [integral_kernel_diagonal] at h
  have he : (fun z => RCLike.re (kernel n z z)) = ginibreIntensity n := by
    funext z
    simpa only [RCLike.re_eq_complex_re] using kernel_diagonal_re n z
  rw [he] at h
  norm_num at h
  exact h

/-- BC12 the `Fin 2` determinant is the usual two-point expression. -/
theorem kernelDet_two_re (n : ℕ) (z : Fin 2 → ℂ) :
    (kernelDet (kernel n) 2 z).re = ginibrePairIntensity n (z 0) (z 1) := by
  simp only [kernelDet, Matrix.det_fin_two, Matrix.of_apply, ginibrePairIntensity, kernelWeight]
  rw [← kernel_star n (z 0) (z 1), Complex.star_def, Complex.mul_conj']
  rw [kernel_diagonal, kernel_diagonal]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  norm_num [ginibreIntensity]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

/-- BC12 positivity of the two-point intensity follows from Gram positivity. -/
theorem ginibrePairIntensity_nonneg (n : ℕ) (z w : ℂ) :
    0 ≤ ginibrePairIntensity n z w := by
  have h := kernelDet_nonneg n 2 (fun i => Fin.cases z (fun _ => w) i)
  have hr := (Complex.le_def.mp h).1
  rw [kernelDet_two_re] at hr
  exact hr

/-- BC12 product volume in one coordinate is ordinary planar volume. -/
theorem integral_finOne (f : ℂ → ℝ) :
    (∫ z : Fin 1 → ℂ, f (z 0)) = ∫ z, f z := by
  have h := (volume_preserving_piUnique (fun _ : Fin 1 => ℂ)).integral_comp' f
  have he : (fun z : Fin 1 → ℂ => f (z default)) = fun z => f (z 0) := by
    funext z
    congr 2
  rw [← he]
  simpa only [Function.comp_apply, MeasurableEquiv.piUnique_apply] using h

/-- BC12 the corresponding L1 equivalence in one coordinate. -/
theorem integrable_finOne_iff (f : ℂ → ℝ) :
    Integrable (fun z : Fin 1 → ℂ => f (z 0)) ↔ Integrable f := by
  have h := (volume_preserving_piUnique (fun _ : Fin 1 => ℂ)).integrable_comp_emb
    (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℂ)).measurableEmbedding (g := f)
  have he : (fun z : Fin 1 → ℂ => f (z default)) = fun z => f (z 0) := by
    funext z
    congr 2
  change Integrable (fun z : Fin 1 → ℂ => f (z default)) ↔ Integrable f at h
  rw [he] at h
  exact h

/-- BC12 product volume in two coordinates is ordinary planar product volume. -/
theorem integral_finTwo (f : ℂ × ℂ → ℝ) :
    (∫ z : Fin 2 → ℂ, f (z 0, z 1)) = ∫ p : ℂ × ℂ, f p := by
  have h := (volume_preserving_finTwoArrow ℂ).integral_comp' f
  simpa only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply] using h

/-- BC12 the corresponding L1 equivalence in two coordinates. -/
theorem integrable_finTwo_iff (f : ℂ × ℂ → ℝ) :
    Integrable (fun z : Fin 2 → ℂ => f (z 0, z 1)) ↔ Integrable f := by
  have h := (volume_preserving_finTwoArrow ℂ).integrable_comp_emb
    (MeasurableEquiv.finTwoArrow (α := ℂ)).measurableEmbedding (g := f)
  have he : f ∘ MeasurableEquiv.finTwoArrow = fun z : Fin 2 → ℂ => f (z 0, z 1) := rfl
  rw [← he]
  exact h

end Ginibre
