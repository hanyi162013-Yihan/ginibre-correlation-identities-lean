import Ginibre.SchurJacobianEverywhere
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Actual local Schur change of variables

HKPV (6.3.4)--(6.3.5), the local measure-transformation step. The volume
below is the transport of ordinary complex matrix-entry Lebesgue measure
through a fixed linear coordinate splitting, not a definition of a
spectral law. The proved full Jacobian is used on the actual injective
chart source. No Jacobian or integrability hypothesis is postulated.

Global overlaps, diagonal phases, permutation multiplicities, and
integration over the auxiliary coordinates are not resolved by a local
change-of-variables identity.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV measurable coordinates use the Borel sigma-algebra of the
already constructed finite-dimensional real parameter space. -/
instance schurTangentMeasurableSpace (n : ℕ) : MeasurableSpace (SchurTangent n) :=
  borel (SchurTangent n)

/-- The coordinate sigma-algebra is Borel by definition, not an input. -/
instance schurTangentBorelSpace (n : ℕ) : BorelSpace (SchurTangent n) := ⟨rfl⟩

/-- The norm used by calculus induces the same Borel sigma-algebra. -/
instance schurTangentNormBorelSpace (n : ℕ) :
    @BorelSpace (SchurTangent n)
      (inferInstance : NormedAddCommGroup (SchurTangent n)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (schurTangentMeasurableSpace n) := ⟨rfl⟩

/-- HKPV fixed linear entry coordinates; this has no eigenvalue selection. -/
def schurFlatEntryEquiv (n : ℕ) : (Fin n × Fin n → ℂ) ≃ₗ[ℝ] SchurTangent n :=
  ((matrixEntryEquiv n).symm.restrictScalars ℝ).trans (schurEntrySplit n)

/-- HKPV actual matrix-entry Lebesgue volume, expressed in the fixed split.
This is not the nonlinear Schur pushforward and not a spectral measure. -/
def schurCoordinateVolume (n : ℕ) : Measure (SchurTangent n) :=
  Measure.map (schurFlatEntryEquiv n) (volume : Measure (Fin n × Fin n → ℂ))

/-- HKPV the concrete coordinate volume is an additive Haar measure. -/
theorem schurCoordinateVolume_isAddHaarMeasure (n : ℕ) :
    Measure.IsAddHaarMeasure (schurCoordinateVolume n) := by
  change Measure.IsAddHaarMeasure (Measure.map (schurFlatEntryEquiv n)
    (volume : Measure (Fin n × Fin n → ℂ)))
  exact Measure.MapLinearEquiv.isAddHaarMeasure
    (volume : Measure (Fin n × Fin n → ℂ)) (schurFlatEntryEquiv n)

/-- The same proved Haar property in the norm-derived structures used by
the Jacobian theorem; this only reconciles equivalent instance spellings. -/
instance schurCoordinateVolume_normHaar (n : ℕ) :
    @Measure.IsAddHaarMeasure (SchurTangent n)
      (inferInstance : NormedAddCommGroup (SchurTangent n)).toAddCommGroup.toAddGroup
      (inferInstance : NormedAddCommGroup (SchurTangent n)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (schurTangentMeasurableSpace n) (schurCoordinateVolume n) := by
  convert! schurCoordinateVolume_isAddHaarMeasure n

/-- HKPV nonnegative full coordinate Jacobian, with separated dependence. -/
def schurJacobianWeight {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (x : SchurTangent n) : ℝ :=
  (∏ p : SchurLower n,
    ‖(S + x.2.val) (schurCol p) (schurCol p) -
      (S + x.2.val) (schurRow p) (schurRow p)‖ ^ 2) * |schurAngularJacobian x.1|

/-- HKPV the weight used in integration is the determinant of the actual map. -/
theorem schurJacobianWeight_eq_abs_det {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) (x : SchurTangent n) :
    schurJacobianWeight S x = |(fderiv ℝ (schurEntryCoordinates S) x).det| :=
  (abs_det_fderiv_schurEntryCoordinates S hS x).symm

/-- HKPV actual chart injectivity survives the fixed output entry splitting. -/
theorem schurEntryCoordinates_injOn_source {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i)) :
    Set.InjOn (schurEntryCoordinates S) (schurLocalChart S hS hz).source := by
  intro x hx y hy he
  exact (schurLocalChart S hS hz).injOn hx hy ((schurEntrySplit n).injective he)

/-- HKPV differentiability on the actual chart, with no regularity input. -/
theorem differentiable_schurEntryCoordinates {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) : Differentiable ℝ (schurEntryCoordinates S) := by
  intro x
  have hf := ((contDiff_schurExpCoordinates 1 S).differentiable (by simp)) x
  convert! (schurEntrySplit n).toContinuousLinearEquiv.differentiableAt.comp x hf

/-- **HKPV actual local nonnegative change of variables** for every
measurable piece of the constructed injective chart. The measure is
concretely fixed by ordinary matrix-entry Lebesgue measure. -/
theorem lintegral_schurEntryCoordinates_image {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i))
    (s : Set (SchurTangent n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart S hS hz).source) (g : SchurTangent n → ℝ≥0∞) :
    ∫⁻ y in schurEntryCoordinates S '' s, g y ∂schurCoordinateVolume n =
      ∫⁻ x in s, ENNReal.ofReal (schurJacobianWeight S x) *
        g (schurEntryCoordinates S x) ∂schurCoordinateVolume n := by
  let : Measure.IsAddHaarMeasure (schurCoordinateVolume n) :=
    schurCoordinateVolume_isAddHaarMeasure n
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (schurCoordinateVolume n) hs
    (fun x _ => (differentiable_schurEntryCoordinates S x).hasFDerivAt.hasFDerivWithinAt)
    ((schurEntryCoordinates_injOn_source S hS hz).mono hsub) g
  simpa only [schurJacobianWeight_eq_abs_det S hS] using h

/-- **HKPV local absolute-integrability equivalence**. This guards against
using the zero value of an undefined Bochner integral as a density proof. -/
theorem integrableOn_schurEntryCoordinates_image_iff {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i))
    (s : Set (SchurTangent n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart S hS hz).source) (g : SchurTangent n → ℝ) :
    IntegrableOn g (schurEntryCoordinates S '' s) (schurCoordinateVolume n) ↔
      IntegrableOn (fun x => schurJacobianWeight S x * g (schurEntryCoordinates S x)) s
        (schurCoordinateVolume n) := by
  let : Measure.IsAddHaarMeasure (schurCoordinateVolume n) :=
    schurCoordinateVolume_isAddHaarMeasure n
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (schurCoordinateVolume n) hs
    (fun x _ => (differentiable_schurEntryCoordinates S x).hasFDerivAt.hasFDerivWithinAt)
    ((schurEntryCoordinates_injOn_source S hS hz).mono hsub) g
  simpa only [schurJacobianWeight_eq_abs_det S hS, smul_eq_mul] using h

/-- **HKPV actual local real integral transformation**, with the full
Vandermonde-square/angle factor computed internally. -/
theorem integral_schurEntryCoordinates_image {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i))
    (s : Set (SchurTangent n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart S hS hz).source) (g : SchurTangent n → ℝ) :
    ∫ y in schurEntryCoordinates S '' s, g y ∂schurCoordinateVolume n =
      ∫ x in s, schurJacobianWeight S x * g (schurEntryCoordinates S x)
        ∂schurCoordinateVolume n := by
  let : Measure.IsAddHaarMeasure (schurCoordinateVolume n) :=
    schurCoordinateVolume_isAddHaarMeasure n
  have h := integral_image_eq_integral_abs_det_fderiv_smul (schurCoordinateVolume n) hs
    (fun x _ => (differentiable_schurEntryCoordinates S x).hasFDerivAt.hasFDerivWithinAt)
    ((schurEntryCoordinates_injOn_source S hS hz).mono hsub) g
  simpa only [schurJacobianWeight_eq_abs_det S hS, smul_eq_mul] using h

end Ginibre
