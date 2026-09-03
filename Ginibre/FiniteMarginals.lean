import Ginibre.KernelDeterminants
import Ginibre.DeterminantalDensity
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Finite-product marginal integrals of the explicit Ginibre density

BC12 Theorem 3.3, determinantal integration step. The results in this file
are about the explicit density; identifying it with the actual spectrum of
a Gaussian matrix remains a logically separate theorem.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Ginibre

/-- Prefix a tuple of integration variables to the retained points.
The length is written `k + m` so recursive prefixing has no casts. -/
def prependPoints {X : Type*} (k : ℕ) :
    (m : ℕ) → (Fin m → X) → (Fin k → X) → (Fin (k + m) → X)
  | 0, _, z => z
  | m + 1, w, z => Fin.cons (w 0) (prependPoints k m (Fin.tail w) z)

/-- BC12 product-coordinate bookkeeping: prefixing a `cons` tuple. -/
@[simp] theorem prependPoints_cons {X : Type*} (k m : ℕ) (u : X)
    (w : Fin m → X) (z : Fin k → X) :
    prependPoints k (m + 1) (Fin.cons u w) z =
      Fin.cons u (prependPoints k m w z) := by
  simp only [prependPoints, Fin.cons_zero, Fin.tail_cons]

/-- BC12 measurability bookkeeping, proved in the stronger continuous form. -/
theorem continuous_prependPoints (k m : ℕ) (z : Fin k → ℂ) :
    Continuous (fun w => prependPoints k m w z) := by
  induction m with
  | zero => exact continuous_const
  | succ m ih =>
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_apply 0
    · exact (continuous_apply j).comp
        (ih.comp (continuous_pi (fun l => continuous_apply l.succ)))

/-- BC12 Fubini bookkeeping: the `Fin (m+1)` product is a scalar times a
`Fin m` product, as an equivalence of integrability assertions. -/
theorem integrable_fin_cons_iff (m : ℕ) (f : (Fin (m + 1) → ℂ) → ℂ) :
    Integrable f ↔ Integrable (fun p : ℂ × (Fin m → ℂ) => f (Fin.cons p.1 p.2)) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0).symm
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero, cast_eq] using
    (h.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f)).symm

/-- BC12 Fubini bookkeeping: the corresponding exact integral identity. -/
theorem integral_fin_cons (m : ℕ) (f : (Fin (m + 1) → ℂ) → ℂ) :
    (∫ w, f w) = ∫ p : ℂ × (Fin m → ℂ), f (Fin.cons p.1 p.2) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0).symm
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero, cast_eq] using (h.integral_comp' f).symm

/-- BC12 absolute integrability of every finite-product determinant section.
The proof uses positivity and the already-proved one-coordinate recursion. -/
theorem integrable_kernelDet_prepend (n k m : ℕ) (z : Fin k → ℂ) :
    Integrable (fun w => kernelDet (kernel n) (k + m) (prependPoints k m w z)) := by
  induction m with
  | zero =>
    change Integrable (fun _ : Fin 0 → ℂ => kernelDet (kernel n) k z)
      (Measure.pi (fun _ : Fin 0 => (volume : Measure ℂ)))
    rw [Measure.pi_of_empty]
    exact integrable_const _
  | succ m ih =>
    rw [integrable_fin_cons_iff]
    simp_rw [prependPoints_cons]
    have hc : Continuous (fun p : ℂ × (Fin m → ℂ) =>
        kernelDet (kernel n) (k + m + 1) (Fin.cons p.1 (prependPoints k m p.2 z))) := by
      apply (continuous_kernelDet n _).comp
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact continuous_fst
      · exact (continuous_apply j).comp ((continuous_prependPoints k m z).comp continuous_snd)
    apply (integrable_prod_iff' hc.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun w =>
      integrable_ginibreKernelDet_cons n (k + m) (prependPoints k m w z)), ?_⟩
    have hnorm (w : Fin m → ℂ) :
        (∫ u, ‖kernelDet (kernel n) (k + m + 1)
          (Fin.cons u (prependPoints k m w z))‖) =
        ((n : ℝ) - ((k + m : ℕ) : ℝ)) *
          (kernelDet (kernel n) (k + m) (prependPoints k m w z)).re := by
      simp_rw [norm_kernelDet]
      have hr := integral_re
        (integrable_ginibreKernelDet_cons n (k + m) (prependPoints k m w z))
      simp only [RCLike.re_eq_complex_re] at hr
      rw [hr, integral_ginibreKernelDet_cons]
      simp
    simp_rw [hnorm]
    simpa only [RCLike.re_eq_complex_re] using
      ih.re.const_mul ((n : ℝ) - ((k + m : ℕ) : ℝ))

/-- **BC12 finite-product integration formula**: integrating `m` points
gives the descending rank factor times the retained determinant. -/
theorem integral_kernelDet_prepend (n k m : ℕ) (z : Fin k → ℂ) :
    (∫ w, kernelDet (kernel n) (k + m) (prependPoints k m w z)) =
      (∏ j ∈ Finset.range m, ((n : ℂ) - ((k + j : ℕ) : ℂ))) *
        kernelDet (kernel n) k z := by
  induction m with
  | zero =>
    change (∫ _ : Fin 0 → ℂ, kernelDet (kernel n) k z
      ∂Measure.pi (fun _ : Fin 0 => (volume : Measure ℂ))) = _
    rw [Measure.pi_of_empty]
    simp
  | succ m ih =>
    rw [integral_fin_cons]
    simp_rw [prependPoints_cons]
    have hi := (integrable_fin_cons_iff m
      (fun w => kernelDet (kernel n) (k + (m + 1))
        (prependPoints k (m + 1) w z))).mp (integrable_kernelDet_prepend n k (m + 1) z)
    simp only [prependPoints_cons] at hi
    change Integrable (fun p : ℂ × (Fin m → ℂ) =>
      kernelDet (kernel n) (k + m + 1) (Fin.cons p.1 (prependPoints k m p.2 z)))
      ((volume : Measure ℂ).prod (volume : Measure (Fin m → ℂ))) at hi
    change (∫ p : ℂ × (Fin m → ℂ), kernelDet (kernel n) (k + m + 1)
      (Fin.cons p.1 (prependPoints k m p.2 z))
      ∂(volume : Measure ℂ).prod (volume : Measure (Fin m → ℂ))) = _
    rw [integral_prod_symm _ hi]
    simp_rw [integral_ginibreKernelDet_cons]
    rw [integral_const_mul, ih, Finset.prod_range_succ]
    ring

/-- BC12 normalization combinatorics: for `n = k+m` the descending factor
is precisely `m!`, including the endpoint `m = 0`. -/
theorem marginal_factorial (k m : ℕ) :
    (∏ j ∈ Finset.range m, (((k + m : ℕ) : ℂ) - ((k + j : ℕ) : ℂ))) =
      (Nat.factorial m : ℂ) := by
  have hprod : (∏ j ∈ Finset.range m, (((k + m : ℕ) : ℂ) - ((k + j : ℕ) : ℂ))) =
      ∏ j ∈ Finset.range m, ((m - j : ℕ) : ℂ) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_range.mp hj))]
    push_cast
    ring
  rw [hprod, ← Nat.cast_prod, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]

/-- **BC12 `k`-point marginal of the normalized explicit density**.
The factor is `m!/(k+m)!`; factorial correlations multiply it by its inverse.
This theorem does not assume or assert a matrix-to-spectrum identification. -/
theorem integral_determinantDensity_prepend (k m : ℕ) (z : Fin k → ℂ) :
    (∫ w, (determinantDensity (k + m) (k + m : ℕ)
      (prependPoints k m w z) : ℂ)) =
        ((Nat.factorial m : ℂ) / (Nat.factorial (k + m) : ℂ)) *
          kernelDet (kernel (k + m)) k z := by
  simp_rw [determinantDensity_eq_kernel_determinant]
  change (∫ w, kernelDet (kernel (k + m)) (k + m) (prependPoints k m w z) /
    (Nat.factorial (k + m) : ℂ)) = _
  rw [integral_div, integral_kernelDet_prepend, marginal_factorial]
  ring

/-- BC12 density marginals have genuine absolute integrability, separately
from their displayed integral value. -/
theorem integrable_determinantDensity_prepend (k m : ℕ) (z : Fin k → ℂ) :
    Integrable (fun w => determinantDensity (k + m) (k + m : ℕ)
      (prependPoints k m w z)) := by
  have hc : Integrable (fun w => (determinantDensity (k + m) (k + m : ℕ)
      (prependPoints k m w z) : ℂ)) := by
    have h := (integrable_kernelDet_prepend (k + m) k m z).div_const
      (Nat.factorial (k + m) : ℂ)
    apply h.congr
    filter_upwards with w
    exact (determinantDensity_eq_kernel_determinant (k + m) (prependPoints k m w z)).symm
  simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re] using hc.re

/-- BC12 real-valued marginal density: retaining `k` of `k+m` coordinates
has density `m!/(k+m)!` times the real kernel determinant. -/
theorem integral_determinantDensity_prepend_real (k m : ℕ) (z : Fin k → ℂ) :
    (∫ w, determinantDensity (k + m) (k + m : ℕ) (prependPoints k m w z)) =
      ((Nat.factorial m : ℝ) / (Nat.factorial (k + m) : ℝ)) *
        (kernelDet (kernel (k + m)) k z).re := by
  have h := congrArg Complex.re (integral_determinantDensity_prepend k m z)
  rw [integral_complex_ofReal] at h
  simpa using h

end Ginibre
