import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Nonzero multivariate complex polynomials have null zero sets

HKPV Section 6.3: polynomial exceptional loci are Lebesgue null.
This proof is copied, with an independent namespace, from the previously
verified ShortRingAnchor development; that project is not imported or edited.  The proof is finite-dimensional induction:
separate one variable, keep a nonzero coefficient outside its null zero set,
then apply Fubini to the finite root set of the remaining univariate polynomial.
No density bound or probability estimate is needed: arbitrary sigma-finite
nonatomic coordinate measures suffice.
-/

noncomputable section

open MeasureTheory Set

namespace Ginibre

/-- The one-variable geometric step: a nonzero polynomial has only finitely
many roots, hence its zero set is null for a nonatomic measure. -/
theorem polynomial_eval_ne_zero_ae
    (mu : Measure ℂ) [NullSingletonClass mu]
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∀ᵐ x ∂mu, Polynomial.eval x p ≠ 0 := by
  rw [ae_iff]
  simpa only [not_ne_iff, Polynomial.IsRoot] using
    (Polynomial.finite_setOfPred_isRoot hp).measure_zero (μ := mu)

/-- HKPV exceptional-locus step: a nonzero complex
multivariate polynomial vanishes on a null set for every finite product of
sigma-finite nonatomic coordinate measures. -/
theorem mvPolynomial_eval_ne_zero_ae_pi
    {sigma : Type*} [Fintype sigma]
    (mu : sigma → Measure ℂ) [∀ i, SigmaFinite (mu i)]
    [∀ i, NullSingletonClass (mu i)]
    (p : MvPolynomial sigma ℂ) (hp : p ≠ 0) :
    ∀ᵐ x ∂Measure.pi mu, MvPolynomial.eval x p ≠ 0 := by
  classical
  refine Fintype.induction_empty_option
    (P := fun sigma _ => ∀ (mu : sigma → Measure ℂ)
      [∀ i, SigmaFinite (mu i)] [∀ i, NullSingletonClass (mu i)]
      (p : MvPolynomial sigma ℂ), p ≠ 0 →
      ∀ᵐ x ∂Measure.pi mu, MvPolynomial.eval x p ≠ 0) ?_ ?_ ?_ sigma mu p hp
  · intro alpha beta _ e ih mu _ _ p hp
    let : Fintype alpha := Fintype.ofEquiv beta e.symm
    let q := MvPolynomial.rename e.symm p
    have hq : q ≠ 0 := by
      intro h
      apply hp
      exact (MvPolynomial.rename_injective e.symm e.symm.injective) (by simpa using h)
    have h := ih (fun i => mu (e i)) q hq
    have he := measurePreserving_piCongrLeft (α := fun _ : beta => ℂ) mu e
    rw [← he.map_eq]
    apply (ae_map_iff he.measurable.aemeasurable
      ((measurableSet_singleton 0).preimage p.continuous_eval.measurable).compl).2
    filter_upwards [h] with x hx
    change MvPolynomial.eval (MeasurableEquiv.piCongrLeft (fun _ : beta => ℂ) e x) p ≠ 0
    convert hx using 1
    dsimp [q]
    rw [MvPolynomial.eval_rename]
    congr 2
    funext b
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  · intro mu _ _ p hp
    apply Filter.Eventually.of_forall
    intro x hx
    apply hp
    have hc : p = MvPolynomial.C (MvPolynomial.constantCoeff p) := by
      ext d
      have hd : d = 0 := by ext i; exact PEmpty.elim i
      simp [hd, ← MvPolynomial.constantCoeff_eq]
    rw [hc, MvPolynomial.eval_C] at hx
    rw [hc, hx, map_zero]
  · intro alpha _ ih mu _ _ p hp
    let q := MvPolynomial.optionEquivLeft ℂ alpha p
    have hq : q ≠ 0 := by
      intro h
      apply hp
      exact (MvPolynomial.optionEquivLeft ℂ alpha).injective (by simpa only [map_zero] using h)
    obtain ⟨k, hk⟩ : ∃ k, q.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hq (Polynomial.ext fun k => by simpa using h k)
    have hcoeff := ih (fun i => mu (some i)) (q.coeff k) hk
    let e := (MeasurableEquiv.piOptionEquivProd (fun _ : Option alpha => ℂ)).symm
    have hmap := Measure.pi_map_piOptionEquivProd mu
    rw [← hmap]
    apply (ae_map_iff e.measurable.aemeasurable
      ((measurableSet_singleton 0).preimage p.continuous_eval.measurable).compl).2
    apply (Measure.ae_prod_iff_ae_ae
      (((measurableSet_singleton 0).preimage
        (p.continuous_eval.measurable.comp e.measurable)).compl)).2
    filter_upwards [hcoeff] with x hx
    have hqx : Polynomial.map (MvPolynomial.eval x) q ≠ 0 := by
      intro hz
      have := congrArg (fun r : Polynomial ℂ => r.coeff k) hz
      apply hx
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using this
    have hroots := polynomial_eval_ne_zero_ae (mu none)
      (Polynomial.map (MvPolynomial.eval x) q) hqx
    filter_upwards [hroots] with y hy
    change MvPolynomial.eval (e (x, y)) p ≠ 0
    have hexy : e (x, y) = fun i => Option.elim i y x := by
      funext i
      cases i <;> rfl
    rw [hexy, MvPolynomial.optionEquivLeft_elim_eval]
    exact hy

/-- HKPV exceptional-locus step, stated as a null-set identity for finite products of
sigma-finite nonatomic complex measures. -/
theorem mvPolynomial_zeroSet_measure_pi
    {sigma : Type*} [Fintype sigma]
    (mu : sigma → Measure ℂ) [∀ i, SigmaFinite (mu i)]
    [∀ i, NullSingletonClass (mu i)]
    (p : MvPolynomial sigma ℂ) (hp : p ≠ 0) :
    Measure.pi mu {x | MvPolynomial.eval x p = 0} = 0 := by
  simpa only [ae_iff, not_ne_iff] using
    mvPolynomial_eval_ne_zero_ae_pi mu p hp

/-- HKPV exceptional-locus step specialized to finite-dimensional complex
Lebesgue measure, with no probability or spectral-law assumption. -/
theorem mvPolynomial_zeroSet_volume
    {sigma : Type*} [Fintype sigma]
    (p : MvPolynomial sigma ℂ) (hp : p ≠ 0) :
    volume {x : sigma → ℂ | MvPolynomial.eval x p = 0} = 0 :=
  mvPolynomial_zeroSet_measure_pi (fun _ => volume) p hp

end Ginibre
