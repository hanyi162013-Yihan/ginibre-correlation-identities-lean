import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic.Ring

/-!
# Finite orthonormal families give projection kernels

The finite algebra/Fubini part of BC12 Theorem 3.3. These lemmas are generic:
the concrete Gaussian monomial hypotheses are to be supplied by proved
analytic lemmas, not by a new external random-matrix assumption.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Ginibre

/-- The kernel of a finite family, with the Gaussian weights included in the functions. -/
def finiteKernel {I X : Type*} [Fintype I] (φ : I → X → ℂ) (z w : X) : ℂ :=
  ∑ i, φ i z * star (φ i w)

/-- BC12 projection algebra: a finite Gram kernel is conjugate symmetric. -/
theorem finiteKernel_star {I X : Type*} [Fintype I] (φ : I → X → ℂ) (z w : X) :
    star (finiteKernel φ z w) = finiteKernel φ w z := by
  simp only [finiteKernel, star_sum, star_mul, star_star]

/-- BC12 projection algebra: each expanded summand is a scalar multiple of an inner product. -/
theorem finiteKernel_product_expand {I X : Type*} [Fintype I]
    (φ : I → X → ℂ) (z u w : X) :
    finiteKernel φ z u * finiteKernel φ u w =
      ∑ i, ∑ j, (φ i z * star (φ j w)) * (star (φ i u) * φ j u) := by
  unfold finiteKernel
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- BC12 projection: integrability of the finite kernel product follows
from integrability of all basis inner products. -/
theorem integrable_finiteKernel_product {I X : Type*} [Fintype I] [MeasurableSpace X]
    {μ : Measure X} (φ : I → X → ℂ)
    (hint : ∀ i j, Integrable (fun u => star (φ i u) * φ j u) μ) (z w : X) :
    Integrable (fun u => finiteKernel φ z u * finiteKernel φ u w) μ := by
  simp_rw [finiteKernel_product_expand]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hint i j).const_mul _))

/-- BC12 projection identity, before specializing to Gaussian monomials. -/
theorem integral_finiteKernel_product {I X : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace X]
    {μ : Measure X} (φ : I → X → ℂ)
    (hint : ∀ i j, Integrable (fun u => star (φ i u) * φ j u) μ)
    (hortho : ∀ i j, (∫ u, star (φ i u) * φ j u ∂μ) = if i = j then 1 else 0)
    (z w : X) :
    (∫ u, finiteKernel φ z u * finiteKernel φ u w ∂μ) = finiteKernel φ z w := by
  classical
  simp_rw [finiteKernel_product_expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hint i j).const_mul _))]
  simp_rw [integral_finsetSum _ (fun j _ => (hint _ j).const_mul _), integral_const_mul, hortho]
  simp [finiteKernel]

/-- BC12 squared-kernel identity as a complex identity. -/
theorem finiteKernel_norm_sq {I X : Type*} [Fintype I] (φ : I → X → ℂ) (z u : X) :
    ((‖finiteKernel φ z u‖ ^ 2 : ℝ) : ℂ) =
      finiteKernel φ z u * finiteKernel φ u z := by
  rw [← finiteKernel_star φ z u]
  simpa only [← Complex.ofReal_pow, Complex.star_def] using
    (Complex.mul_conj' (finiteKernel φ z u)).symm

/-- BC12 squared-kernel projection: the integrability assertion is proved separately. -/
theorem integrable_finiteKernel_norm_sq {I X : Type*} [Fintype I] [MeasurableSpace X]
    {μ : Measure X} (φ : I → X → ℂ)
    (hint : ∀ i j, Integrable (fun u => star (φ i u) * φ j u) μ) (z : X) :
    Integrable (fun u => ‖finiteKernel φ z u‖ ^ 2) μ := by
  have h := (integrable_finiteKernel_product φ hint z z).re
  simp_rw [← finiteKernel_norm_sq] at h
  simpa only [RCLike.re_eq_complex_re, ← Complex.ofReal_pow, Complex.ofReal_re] using h

/-- BC12 squared-kernel projection, real form. -/
theorem integral_finiteKernel_norm_sq {I X : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace X]
    {μ : Measure X} (φ : I → X → ℂ)
    (hint : ∀ i j, Integrable (fun u => star (φ i u) * φ j u) μ)
    (hortho : ∀ i j, (∫ u, star (φ i u) * φ j u ∂μ) = if i = j then 1 else 0)
    (z : X) : (∫ u, ‖finiteKernel φ z u‖ ^ 2 ∂μ) = (finiteKernel φ z z).re := by
  have h := congrArg Complex.re (integral_finiteKernel_product φ hint hortho z z)
  have hr := integral_re (integrable_finiteKernel_product φ hint z z)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [← hr] at h
  simp_rw [← finiteKernel_norm_sq] at h
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using h

end Ginibre
