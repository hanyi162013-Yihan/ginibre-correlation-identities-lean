import Ginibre.GaussianBasis

/-!
# The explicit Ginibre kernel is a projection

The analytic input needed in BC12 Theorem 3.3's covariance calculation.
These are unconditional theorems about the explicit kernel, not fields of
an external formula interface. The weighted theorem includes integrability
and accepts unbounded nonnegative measurable weights.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Ginibre

/-- BC12 kernel symmetry, derived from its finite orthonormal expansion. -/
theorem kernel_star (n : ℕ) (z w : ℂ) : star (kernel n z w) = kernel n w z := by
  simp_rw [kernel_eq_finiteKernel]
  exact finiteKernel_star _ z w

/-- BC12's squared kernel is invariant under swapping its two arguments. -/
theorem kernelWeight_swap (n : ℕ) (z w : ℂ) :
    kernelWeight n (z, w) = kernelWeight n (w, z) := by
  unfold kernelWeight
  rw [← kernel_star n z w, norm_star]

/-- The Gaussian kernel diagonal is exactly `n` times the empirical density. -/
theorem kernel_diagonal (n : ℕ) (z : ℂ) :
    kernel n z z = (((n : ℝ) * onePointDensity n z : ℝ) : ℂ) := by
  have hz : (n : ℂ) * z * star z = (((n : ℝ) * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  have he : -((n : ℝ) * (‖z‖ ^ 2 + ‖z‖ ^ 2)) / 2 = -((n : ℝ) * ‖z‖ ^ 2) := by ring
  unfold kernel onePointDensity
  rw [hz, he]
  push_cast
  ring

/-- BC12 reproducing identity: the kernel product is integrable. -/
theorem integrable_kernel_product (n : ℕ) (z w : ℂ) :
    Integrable (fun u => kernel n z u * kernel n u w) := by
  cases n with
  | zero => simp
  | succ n =>
    have ha : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    simp_rw [kernel_eq_finiteKernel]
    exact integrable_finiteKernel_product
      (fun i : Fin (n + 1) => gaussianBasis ((n + 1 : ℕ) : ℝ) i.val)
      (fun i j => integrable_gaussianBasis_inner ha i.val j.val) z w

/-- **Explicit Ginibre reproducing-kernel identity**, including off-diagonal points. -/
theorem integral_kernel_product (n : ℕ) (z w : ℂ) :
    (∫ u, kernel n z u * kernel n u w) = kernel n z w := by
  cases n with
  | zero => simp
  | succ n =>
    have ha : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    simp_rw [kernel_eq_finiteKernel]
    exact integral_finiteKernel_product
      (fun i : Fin (n + 1) => gaussianBasis ((n + 1 : ℕ) : ℝ) i.val)
      (fun i j => integrable_gaussianBasis_inner ha i.val j.val)
      (fun i j => by
        rw [integral_gaussianBasis_inner ha]
        simp only [Fin.val_inj]) z w

/-- BC12 projection: each section of the squared kernel is integrable. -/
theorem integrable_kernelWeight_section (n : ℕ) (z : ℂ) :
    Integrable (fun w => kernelWeight n (z, w)) := by
  cases n with
  | zero => simp [kernelWeight]
  | succ n =>
    have ha : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    simp only [kernelWeight, kernel_eq_finiteKernel]
    exact integrable_finiteKernel_norm_sq
      (fun i : Fin (n + 1) => gaussianBasis ((n + 1 : ℕ) : ℝ) i.val)
      (fun i j => integrable_gaussianBasis_inner ha i.val j.val) z

/-- **Explicit Ginibre projection identity** relative to planar Lebesgue measure. -/
theorem integral_kernelWeight_section (n : ℕ) (z : ℂ) :
    (∫ w, kernelWeight n (z, w)) = (n : ℝ) * onePointDensity n z := by
  cases n with
  | zero => simp [kernelWeight]
  | succ n =>
    have h := integral_finiteKernel_norm_sq
      (fun i : Fin (n + 1) => gaussianBasis ((n + 1 : ℕ) : ℝ) i.val)
      (fun i j => integrable_gaussianBasis_inner (by positivity) i.val j.val)
      (fun i j => by
        rw [integral_gaussianBasis_inner (by positivity)]
        simp only [Fin.val_inj]) z
    simp only [← kernel_eq_finiteKernel, kernel_diagonal, Complex.ofReal_re] at h
    exact h

/-- BC12 weighted projection: integrability follows from the diagonal
weighted integral, even for an unbounded weight. -/
theorem integrable_weighted_kernel_fst (n : ℕ) {g : ℂ → ℝ}
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hint : Integrable (fun z => g z * onePointDensity n z)) :
    Integrable (fun zw : ℂ × ℂ => g zw.1 * kernelWeight n zw) := by
  have hm : Measurable (fun zw : ℂ × ℂ => g zw.1 * kernelWeight n zw) :=
    (hg.comp measurable_fst).mul ((continuous_kernel n).measurable.norm.pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall (fun z =>
    (integrable_kernelWeight_section n z).const_mul (g z)), ?_⟩
  change Integrable (fun z : ℂ => ∫ w : ℂ, ‖g z * kernelWeight n (z, w)‖)
  have he (z : ℂ) : (∫ w, ‖g z * kernelWeight n (z, w)‖) =
      (n : ℝ) * (g z * onePointDensity n z) := by
    have hn (w : ℂ) : ‖g z * kernelWeight n (z, w)‖ = g z * kernelWeight n (z, w) :=
      Real.norm_of_nonneg (mul_nonneg (hg0 z) (sq_nonneg _))
    simp_rw [hn]
    rw [integral_const_mul, integral_kernelWeight_section]
    ring
  simp_rw [he]
  exact hint.const_mul (n : ℝ)

/-- BC12 weighted projection, one-variable form. -/
theorem integral_weighted_kernel_fst (n : ℕ) {g : ℂ → ℝ}
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hint : Integrable (fun z => g z * onePointDensity n z)) :
    (∫ zw : ℂ × ℂ, g zw.1 * kernelWeight n zw) =
      (n : ℝ) * ∫ z, g z * onePointDensity n z := by
  have h := integrable_weighted_kernel_fst n hg hg0 hint
  change (∫ zw : ℂ × ℂ, g zw.1 * kernelWeight n zw ∂volume.prod volume) = _
  rw [integral_prod _ h]
  simp_rw [integral_const_mul, integral_kernelWeight_section]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by ring)

/-- **The complete symmetric weighted projection identity** used by the
existing Section 3 development. Both integrability and equality are proved;
there is no Gaussian-spectrum or correlation-formula hypothesis. -/
theorem weighted_projection (n : ℕ) {g : ℂ → ℝ}
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hint : Integrable (fun z => g z * onePointDensity n z)) :
    Integrable (fun zw : ℂ × ℂ => (g zw.1 + g zw.2) * kernelWeight n zw) ∧
      (∫ zw : ℂ × ℂ, (g zw.1 + g zw.2) * kernelWeight n zw) =
        2 * (n : ℝ) * ∫ z, g z * onePointDensity n z := by
  have hfst := integrable_weighted_kernel_fst n hg hg0 hint
  have hsnd : Integrable (fun zw : ℂ × ℂ => g zw.2 * kernelWeight n zw) := by
    have hh := hfst.swap
    apply hh.congr
    filter_upwards with zw
    rcases zw with ⟨z, w⟩
    dsimp only [Function.comp_def, Prod.swap]
    rw [kernelWeight_swap]
  have he : (∫ zw : ℂ × ℂ, g zw.2 * kernelWeight n zw) =
      (n : ℝ) * ∫ z, g z * onePointDensity n z := by
    rw [← integral_weighted_kernel_fst n hg hg0 hint]
    change (∫ zw : ℂ × ℂ, g zw.2 * kernelWeight n zw ∂volume.prod volume) =
      ∫ zw : ℂ × ℂ, g zw.1 * kernelWeight n zw ∂volume.prod volume
    rw [← integral_prod_swap (fun zw : ℂ × ℂ => g zw.2 * kernelWeight n zw)]
    apply integral_congr_ae
    filter_upwards with zw
    rcases zw with ⟨z, w⟩
    dsimp only [Prod.swap]
    rw [kernelWeight_swap]
  constructor
  · apply (hfst.add hsnd).congr
    filter_upwards with zw
    dsimp only [Pi.add_apply]
    ring
  · simp_rw [add_mul]
    rw [integral_add hfst hsnd, integral_weighted_kernel_fst n hg hg0 hint, he]
    ring

end Ginibre
