import Ginibre.FiniteProjection
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum

/-!
# Normalization of the determinant density

BC12 Theorem 3.3, finite-dimensional integration. A determinant made from
an orthonormal family has squared integral `n!`. The theorem is about an
explicit density and does not assert that it is the law of eigenvalues of
a Gaussian matrix; that requires the separate Schur measure transformation.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Ginibre

/-- Evaluation determinant of a finite family of functions. -/
def slater {I X : Type*} [Fintype I] [DecidableEq I]
    (φ : I → X → ℂ) (z : I → X) : ℂ := Matrix.det (fun i j => φ i (z j))

/-- BC12 determinant algebra: complex-valued permutation signs have square one. -/
theorem sign_mul_sign {I : Type*} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) :
    (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ)) = 1 := by
  exact_mod_cast Int.units_coe_mul_self (Equiv.Perm.sign σ)

/-- BC12 determinant algebra: expand the squared determinant into products
which are independently integrable in each coordinate. -/
theorem slater_norm_sq_expand {I X : Type*} [Fintype I] [DecidableEq I]
    (φ : I → X → ℂ) (z : I → X) :
    ((‖slater φ z‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ : Equiv.Perm I, ∑ τ : Equiv.Perm I,
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
          ∏ i, star (φ (σ i) (z i)) * φ (τ i) (z i) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
  simp only [slater]
  rw [Matrix.det_apply' (fun i j : I => φ i (z j))]
  simp only [Complex.star_def, map_sum, map_mul, map_prod, map_intCast,
    Finset.prod_mul_distrib]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

/-- BC12 determinant integration: every term in the permutation expansion
is integrable, so exchanging finite sums and integrals is justified. -/
theorem integrable_slater_norm_sq {I X : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    (φ : I → X → ℂ)
    (hint : ∀ i j, Integrable (fun u => star (φ i u) * φ j u) μ) :
    Integrable (fun z : I → X => ‖slater φ z‖ ^ 2) (Measure.pi (fun _ => μ)) := by
  have hc : Integrable (fun z : I → X => ((‖slater φ z‖ ^ 2 : ℝ) : ℂ))
      (Measure.pi (fun _ => μ)) := by
    simp_rw [slater_norm_sq_expand]
    exact integrable_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ =>
      (Integrable.fintype_prod (fun i => hint (σ i) (τ i))).const_mul _))
  simpa only [RCLike.re_eq_complex_re, ← Complex.ofReal_pow, Complex.ofReal_re] using hc.re

/-- BC12 determinant integration: orthogonality kills every off-diagonal
pair of permutations. -/
theorem integral_permutation_product {I X : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    (φ : I → X → ℂ)
    (hortho : ∀ i j, (∫ u, star (φ i u) * φ j u ∂μ) = if i = j then 1 else 0)
    (σ τ : Equiv.Perm I) :
    (∫ z : I → X, ∏ i, star (φ (σ i) (z i)) * φ (τ i) (z i)
      ∂Measure.pi (fun _ => μ)) = if σ = τ then 1 else 0 := by
  rw [integral_fintype_prod_eq_prod
    (fun i (u : X) => star (φ (σ i) u) * φ (τ i) u) (μ := fun _ : I => μ)]
  simp_rw [hortho]
  rw [Fintype.prod_boole]
  by_cases h : σ = τ
  · simp [h]
  · have hn : ¬ ∀ i, σ i = τ i := fun hp => h (Equiv.ext hp)
    simp only [if_neg hn, if_neg h]

/-- **BC12 determinant normalization**: the squared evaluation determinant
of an orthonormal family has integral `card(I)!`. -/
theorem integral_slater_norm_sq {I X : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    (φ : I → X → ℂ)
    (hint : ∀ i j, Integrable (fun u => star (φ i u) * φ j u) μ)
    (hortho : ∀ i j, (∫ u, star (φ i u) * φ j u ∂μ) = if i = j then 1 else 0) :
    (∫ z : I → X, ‖slater φ z‖ ^ 2 ∂Measure.pi (fun _ => μ)) =
      (Nat.factorial (Fintype.card I) : ℝ) := by
  have h (σ τ : Equiv.Perm I) :=
    (Integrable.fintype_prod (fun i => hint (σ i) (τ i))).const_mul
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ))
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [slater_norm_sq_expand]
  rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ => h σ τ))]
  simp_rw [integral_finsetSum _ (fun τ _ => h _ τ), integral_const_mul,
    integral_permutation_product φ hortho]
  simp [sign_mul_sign, Fintype.card_perm]

/-- BC12 full-point determinant formula: the kernel Gram determinant is
the squared evaluation determinant, purely algebraically. -/
theorem det_finiteKernel_eq_slater_norm_sq {I X : Type*} [Fintype I] [DecidableEq I]
    (φ : I → X → ℂ) (z : I → X) :
    Matrix.det (fun i j => finiteKernel φ (z i) (z j)) = ((‖slater φ z‖ ^ 2 : ℝ) : ℂ) := by
  let M : Matrix I I ℂ := fun i j => φ j (z i)
  have hm : (fun i j => finiteKernel φ (z i) (z j)) = M * M.conjTranspose := by
    rfl
  rw [hm, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj']
  have hd : Matrix.det M = slater φ z := by
    exact Matrix.det_transpose (fun i j => φ i (z j))
  rw [hd]
  push_cast
  rfl

end Ginibre
