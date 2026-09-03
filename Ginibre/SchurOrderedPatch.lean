import Ginibre.SchurAngularPatch
import Ginibre.SchurOrderedSpectrum
import Ginibre.SchurProductVolume

/-!
# Schur integration patches with unrestricted triangular variables

HKPV (6.3.4)--(6.3.5), removing the dependence of the chart domain on
the triangular center. A fixed angular patch is injective for all
lexicographically ordered simple diagonals and all strict-upper entries.
The resulting change of variables no longer requires the full parameter
to lie in a small inverse-function-theorem neighborhood.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV the fixed lexicographic chamber is Borel, including spectra
whose different eigenvalues have equal real parts. -/
theorem measurableSet_schurDiagonalOrdered (n : ℕ) :
    MeasurableSet {z : Fin n → ℂ | schurDiagonalOrdered z} := by
  simp only [schurDiagonalOrdered, StrictMono, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => ?_
  have hri : Measurable (fun z : Fin n → ℂ => (z i).re) := by fun_prop
  have hrj : Measurable (fun z : Fin n → ℂ => (z j).re) := by fun_prop
  have hii : Measurable (fun z : Fin n → ℂ => (z i).im) := by fun_prop
  have hij : Measurable (fun z : Fin n → ℂ => (z j).im) := by fun_prop
  simp only [schurLexCode, Prod.Lex.toLex_lt_toLex]
  exact (measurableSet_lt hri hrj).union
    ((measurableSet_eq_fun hri hrj).inter (measurableSet_lt hii hij))

/-- HKPV an angular patch times the whole ordered triangular chamber. -/
def schurOrderedDomain {n : ℕ} (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀) :
    Set (SchurTangent n) :=
  {x | x.1 ∈ schurAngularSource z₀ hz₀ ∧
    schurDiagonalOrdered (fun i => x.2.val i i)}

/-- HKPV the extended integration domain is measurable. -/
theorem measurableSet_schurOrderedDomain {n : ℕ}
    (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀) :
    MeasurableSet (schurOrderedDomain z₀ hz₀) := by
  have hf : Continuous (fun x : SchurTangent n => x.1) := continuous_fst
  have hg : Continuous (fun x : SchurTangent n => fun i => x.2.val i i) := by
    apply continuous_pi
    intro i
    convert! (schurUpperTangentCLM n).continuous.matrix_elem i i using 1
  exact ((isOpen_schurAngularSource z₀ hz₀).preimage hf).measurableSet.inter
    ((measurableSet_schurDiagonalOrdered n).preimage hg.measurable)

/-- **HKPV extended Schur injectivity**. Only the angular parameter is
restricted to the fixed local patch; every ordered simple spectrum and
every strict-upper triangular factor are allowed. -/
theorem schurExpCoordinates_injOn_orderedDomain {n : ℕ}
    (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀) :
    Set.InjOn (schurExpCoordinates (0 : Matrix (Fin n) (Fin n) ℂ))
      (schurOrderedDomain z₀ hz₀) := by
  intro x hx y hy he
  have he' : schurAngularUnitary x.1 * x.2.val * (schurAngularUnitary x.1).conjTranspose =
      schurAngularUnitary y.1 * y.2.val * (schurAngularUnitary y.1).conjTranspose := by
    simpa only [schurExpCoordinates_eq_conjugation, zero_add] using! he
  have hc : x.2.val.charpoly = y.2.val.charpoly := by
    rw [← charpoly_unitary_conjugate _ x.2.val (schurAngularUnitary_unitary x.1),
      ← charpoly_unitary_conjugate _ y.2.val (schurAngularUnitary_unitary y.1), he']
  have hd := ordered_upper_diagonals_eq_of_charpoly_eq x.2.val y.2.val
    x.2.property y.2.property hx.2 hy.2 hc
  obtain ⟨hw, hS⟩ := schurAngularSource_full_ordered_collision z₀ hz₀ x.1 y.1 hx.1 hy.1
    x.2.val y.2.val x.2.property y.2.property (fun i => (congrFun hd i).symm)
    (schurDiagonalOrdered_injective hx.2) he'
  exact Prod.ext hw (Subtype.ext hS)

/-- HKPV the extended injectivity survives the fixed output entry split. -/
theorem schurEntryCoordinates_injOn_orderedDomain {n : ℕ}
    (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀) :
    Set.InjOn (schurEntryCoordinates (0 : Matrix (Fin n) (Fin n) ℂ))
      (schurOrderedDomain z₀ hz₀) := by
  intro x hx y hy he
  exact schurExpCoordinates_injOn_orderedDomain z₀ hz₀ hx hy ((schurEntrySplit n).injective he)

/-- **HKPV nonnegative Schur change of variables on a full triangular
chamber**. Unlike the original local theorem, the source restriction
places no smallness condition on eigenvalues or strict-upper entries. -/
theorem lintegral_schurEntryCoordinates_ordered_image {n : ℕ}
    (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀)
    (s : Set (SchurTangent n)) (hs : MeasurableSet s)
    (hsub : s ⊆ schurOrderedDomain z₀ hz₀) (g : SchurTangent n → ℝ≥0∞) :
    ∫⁻ y in schurEntryCoordinates 0 '' s, g y ∂schurCoordinateVolume n =
      ∫⁻ x in s, ENNReal.ofReal (schurJacobianWeight 0 x) *
        g (schurEntryCoordinates 0 x) ∂schurCoordinateVolume n := by
  let : Measure.IsAddHaarMeasure (schurCoordinateVolume n) :=
    schurCoordinateVolume_isAddHaarMeasure n
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (schurCoordinateVolume n) hs
    (fun x _ => (differentiable_schurEntryCoordinates 0 x).hasFDerivAt.hasFDerivWithinAt)
    ((schurEntryCoordinates_injOn_orderedDomain z₀ hz₀).mono hsub) g
  simpa only [schurJacobianWeight_eq_abs_det 0 Matrix.blockTriangular_zero] using h

/-- HKPV absolute integrability on the extended chamber, with the
computed actual Jacobian rather than an external transformation input. -/
theorem integrableOn_schurEntryCoordinates_ordered_image_iff {n : ℕ}
    (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀)
    (s : Set (SchurTangent n)) (hs : MeasurableSet s)
    (hsub : s ⊆ schurOrderedDomain z₀ hz₀) (g : SchurTangent n → ℝ) :
    IntegrableOn g (schurEntryCoordinates 0 '' s) (schurCoordinateVolume n) ↔
      IntegrableOn (fun x => schurJacobianWeight 0 x * g (schurEntryCoordinates 0 x)) s
        (schurCoordinateVolume n) := by
  let : Measure.IsAddHaarMeasure (schurCoordinateVolume n) :=
    schurCoordinateVolume_isAddHaarMeasure n
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (schurCoordinateVolume n) hs
    (fun x _ => (differentiable_schurEntryCoordinates 0 x).hasFDerivAt.hasFDerivWithinAt)
    ((schurEntryCoordinates_injOn_orderedDomain z₀ hz₀).mono hsub) g
  simpa only [schurJacobianWeight_eq_abs_det 0 Matrix.blockTriangular_zero, smul_eq_mul] using h

end Ginibre
