import Ginibre.StatisticKernels

/-!
# Moments of actual Gaussian eigenvalue linear statistics

BC12 Theorems 3.3--3.4. Distinct-index Campbell formulas are combined
with a finite diagonal/off-diagonal decomposition. The results concern
the actual iid Gaussian entry space, not a candidate point process.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- BC12 linear statistic of a labelled spectral tuple. -/
def linearStatistic (n : ℕ) (f : ℂ → ℝ) (z : Fin n → ℂ) : ℝ := ∑ i, f (z i)

/-- BC12 a one-label factorial statistic is the ordinary linear statistic. -/
theorem factorialStatistic_one (n : ℕ) (f : ℂ → ℝ) (z : Fin n → ℂ) :
    factorialStatistic 1 n (fun u => f (u 0)) z = linearStatistic n f z := by
  unfold factorialStatistic selectedSpectrum linearStatistic
  change (∑ e : Fin 1 ↪ Fin n, f (z (e 0))) = ∑ i : Fin n, f (z i)
  exact Equiv.sum_comp Equiv.uniqueEmbeddingEquivResult (fun i : Fin n => f (z i))

/-- BC12 the two-label test used in mixed second moments. -/
def pairStatisticTest (f g : ℂ → ℝ) (z : Fin 2 → ℂ) : ℝ := f (z 0) * g (z 1)

/-- BC12 all two-label embeddings are exactly all ordered unequal pairs. -/
theorem factorialStatistic_two (n : ℕ) (f g : ℂ → ℝ) (z : Fin n → ℂ) :
    factorialStatistic 2 n (pairStatisticTest f g) z =
      ∑ p : {p : Fin n × Fin n // p.1 ≠ p.2}, f (z p.val.1) * g (z p.val.2) := by
  unfold factorialStatistic pairStatisticTest selectedSpectrum
  have h := Equiv.sum_comp Function.Embedding.twoEmbeddingEquiv
    (fun p : {p : Fin n × Fin n // p.1 ≠ p.2} => f (z p.val.1) * g (z p.val.2))
  exact h

/-- BC12 finite diagonal/off-diagonal decomposition of a product of sums. -/
theorem linearStatistic_mul (n : ℕ) (f g : ℂ → ℝ) (z : Fin n → ℂ) :
    linearStatistic n f z * linearStatistic n g z =
      linearStatistic n (fun w => f w * g w) z +
        factorialStatistic 2 n (pairStatisticTest f g) z := by
  classical
  let e : Fin n ≃ {p : Fin n × Fin n // ¬p.1 ≠ p.2} :=
    { toFun := fun i => ⟨(i, i), by simp⟩
      invFun := fun p => p.val.1
      left_inv := fun _ => rfl
      right_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact Classical.not_not.mp p.property }
  have hdiag := Equiv.sum_comp e
    (fun p : {p : Fin n × Fin n // ¬p.1 ≠ p.2} => f (z p.val.1) * g (z p.val.2))
  have hoff := factorialStatistic_two n f g z
  have hpart := Fintype.sum_subtype_add_sum_subtype (p := fun p : Fin n × Fin n => p.1 ≠ p.2)
    (fun p => f (z p.1) * g (z p.2))
  have hfull : (∑ p : Fin n × Fin n, f (z p.1) * g (z p.2)) =
      linearStatistic n f z * linearStatistic n g z := by
    rw [Fintype.sum_prod_type]
    unfold linearStatistic
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hdiag' : (∑ p : {p : Fin n × Fin n // ¬p.1 ≠ p.2},
      f (z p.val.1) * g (z p.val.2)) = linearStatistic n (fun w => f w * g w) z := by
    exact hdiag.symm
  rw [← hoff, hdiag', hfull] at hpart
  linarith

/-- BC12 first moment of an actual Gaussian-matrix eigenvalue statistic. -/
theorem gaussianMatrix_integral_linearStatistic (m : ℕ)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z : Fin 1 → ℂ =>
      f (z 0) * (kernelDet (kernel (m + 1)) 1 z).re)) :
    (∫ A, linearStatistic (m + 1) f (schurSpectrum (Matrix.of A.curry))
      ∂gaussianMatrixLaw (m + 1) (m + 1 : ℕ)) =
        ∫ z : Fin 1 → ℂ, f (z 0) * (kernelDet (kernel (m + 1)) 1 z).re := by
  have h := gaussianMatrix_factorialStatistic 1 m (by omega)
    (fun z => f (z 0)) (hf.comp (measurable_pi_apply 0))
  rw [Nat.add_comm 1 m] at h
  simpa only [factorialStatistic_one] using (h hi).2

/-- BC12 L1 of the first-moment weight gives L1 of the actual statistic. -/
theorem gaussianMatrix_integrable_linearStatistic (m : ℕ)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z : Fin 1 → ℂ =>
      f (z 0) * (kernelDet (kernel (m + 1)) 1 z).re)) :
    Integrable (fun A => linearStatistic (m + 1) f (schurSpectrum (Matrix.of A.curry)))
      (gaussianMatrixLaw (m + 1) (m + 1 : ℕ)) := by
  have h := gaussianMatrix_factorialStatistic 1 m (by omega)
    (fun z => f (z 0)) (hf.comp (measurable_pi_apply 0))
  rw [Nat.add_comm 1 m] at h
  exact (h hi).1.congr (Filter.Eventually.of_forall (fun A => factorialStatistic_one _ f _))

/-- BC12 actual mixed second moment, with diagonal and unequal-index terms separated. -/
theorem gaussianMatrix_integral_linearStatistic_mul (m : ℕ)
    (f g : ℂ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hdiag : Integrable (fun z : Fin 1 → ℂ =>
      (f (z 0) * g (z 0)) * (kernelDet (kernel (m + 2)) 1 z).re))
    (hoff : Integrable (fun z : Fin 2 → ℂ =>
      pairStatisticTest f g z * (kernelDet (kernel (m + 2)) 2 z).re)) :
    (∫ A, linearStatistic (m + 2) f (schurSpectrum (Matrix.of A.curry)) *
        linearStatistic (m + 2) g (schurSpectrum (Matrix.of A.curry))
      ∂gaussianMatrixLaw (m + 2) (m + 2 : ℕ)) =
      (∫ z : Fin 1 → ℂ,
        (f (z 0) * g (z 0)) * (kernelDet (kernel (m + 2)) 1 z).re) +
      ∫ z : Fin 2 → ℂ, pairStatisticTest f g z *
        (kernelDet (kernel (m + 2)) 2 z).re := by
  have hd := gaussianMatrix_factorialStatistic 1 (m + 1) (by omega)
    (fun z => f (z 0) * g (z 0))
    ((hf.comp (measurable_pi_apply 0)).mul (hg.comp (measurable_pi_apply 0)))
  rw [show 1 + (m + 1) = m + 2 by omega] at hd
  specialize hd hdiag
  have ho := gaussianMatrix_factorialStatistic 2 m (by omega) (pairStatisticTest f g)
    ((hf.comp (measurable_pi_apply 0)).mul (hg.comp (measurable_pi_apply 1)))
  rw [Nat.add_comm 2 m] at ho
  specialize ho hoff
  rw [← hd.2, ← ho.2, ← integral_add hd.1 ho.1]
  apply integral_congr_ae
  filter_upwards with A
  rw [factorialStatistic_one (m + 2) (fun w => f w * g w)]
  exact linearStatistic_mul (m + 2) f g _

/-- BC12 covariance functional of actual Gaussian-matrix eigenvalue statistics. -/
def gaussianEigenvalueCovariance (n : ℕ) (f g : ℂ → ℝ) : ℝ :=
  (∫ A, linearStatistic n f (schurSpectrum (Matrix.of A.curry)) *
      linearStatistic n g (schurSpectrum (Matrix.of A.curry))
    ∂gaussianMatrixLaw n n) -
  (∫ A, linearStatistic n f (schurSpectrum (Matrix.of A.curry)) ∂gaussianMatrixLaw n n) *
    ∫ A, linearStatistic n g (schurSpectrum (Matrix.of A.curry)) ∂gaussianMatrixLaw n n

end Ginibre
