import Ginibre.SchurGlobalChartIntegration
import Ginibre.SchurSpectrum

/-!
# Almost-sure measurability of actual Gaussian eigenvalues

HKPV Section 6.4 and BC12 Theorem 3.2. A measurable inverse exists on
each constructed injective Schur patch. The countable disjoint cover
glues these into a measurable representative of the actual ordered
spectrum. No measurable-root or eigenvector-selection theorem is assumed.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV the actual spectral selection reads the diagonal in fixed-entry charts. -/
theorem schurCoordinateSpectrum_extended {n : ℕ} (U : SchurUnitaryFrame n)
    (x : SchurTangent n)
    (hx : x ∈ schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n)) :
    schurCoordinateSpectrum (schurExtendedEntryAt U x) = fun i => x.2.val i i := by
  rw [schurExtendedEntryAt, schurCoordinateSpectrum_entrySplit]
  exact schurSpectrum_schurExtendedAt U x hx

/-- HKPV the coordinate diagonal is measurable independently of any spectral selection. -/
theorem measurable_schurCoordinateDiagonal (n : ℕ) :
    Measurable (fun x : SchurTangent n => fun i => x.2.val i i) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  convert! (schurUpperTangentCLM n).continuous.matrix_elem i i using 1

/-- HKPV a genuine measurable spectral representative on each actual chart image. -/
theorem exists_measurable_schurSpectrum_patch (n : ℕ) (k : ℕ) :
    ∃ g : SchurTangent n → Fin n → ℂ, Measurable g ∧
      Set.EqOn g schurCoordinateSpectrum (schurDisjointEntryImage n k) := by
  let s := schurDisjointDomain n k
  let U := schurAngularAtlasFrame n k
  have hemb : MeasurableEmbedding (s.domRestrict (schurExtendedEntryAt U)) :=
    measurableEmbedding_of_fderivWithin (measurableSet_schurDisjointDomain n k)
      (fun x _ => (hasFDerivAt_schurExtendedEntryAt U x).hasFDerivWithinAt)
      ((schurExtendedEntryAt_injOn U _ _).mono (schurDisjointDomain_subset_ordered n k))
  have hd : Measurable (fun x : s => fun i => x.val.2.val i i) :=
    (measurable_schurCoordinateDiagonal n).comp measurable_subtype_coe
  obtain ⟨g, hg, he⟩ := hemb.exists_measurable_extend hd (fun _ => ⟨0⟩)
  refine ⟨g, hg, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxg := congrFun he (⟨x, hx⟩ : s)
  exact hxg.trans (schurCoordinateSpectrum_extended U x hx.1).symm

/-- **HKPV countable measurable spectral gluing**, with equality on the
entire proved full-measure cover, not merely a local inverse assertion. -/
theorem exists_measurable_schurCoordinateSpectrum (n : ℕ) :
    ∃ g : SchurTangent n → Fin n → ℂ, Measurable g ∧
      Set.EqOn g schurCoordinateSpectrum (⋃ k, schurDisjointEntryImage n k) := by
  choose g hg he using exists_measurable_schurSpectrum_patch n
  have hagree : Pairwise (fun i j => Set.EqOn (g i) (g j)
      (schurDisjointEntryImage n i ∩ schurDisjointEntryImage n j)) := by
    intro i j hij x hx
    exact False.elim ((Set.disjoint_left.mp (pairwise_schurDisjointEntryImage n hij)) hx.1 hx.2)
  obtain ⟨f, hf, hfg⟩ := exists_measurable_piecewise (schurDisjointEntryImage n)
    (measurableSet_schurDisjointEntryImage n) g hg hagree
  refine ⟨f, hf, ?_⟩
  intro x hx
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  exact (hfg k hk).trans (he k hk)

/-- **BC12 the actual ordered Gaussian spectrum is almost everywhere
measurable**, proved from the Schur atlas rather than assumed as an input. -/
theorem aemeasurable_schurCoordinateSpectrum (n : ℕ) {a : ℝ} (ha : 0 < a) :
    AEMeasurable (schurCoordinateSpectrum : SchurTangent n → Fin n → ℂ)
      (gaussianCoordinateLaw n a) := by
  obtain ⟨g, hg, he⟩ := exists_measurable_schurCoordinateSpectrum n
  apply hg.aemeasurable.congr
  filter_upwards [gaussianCoordinate_mem_iUnion_schurDisjointEntryImage_ae n ha] with x hx
  exact he hx

end Ginibre
