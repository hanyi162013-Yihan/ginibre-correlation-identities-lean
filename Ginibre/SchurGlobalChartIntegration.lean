import Ginibre.SchurDisjointAtlas
import Ginibre.GaussianCoordinateLaw

/-!
# Global Gaussian integration through disjoint actual Schur charts

HKPV Section 6.3--6.4: sum actual Euclidean changes of variables over
the proved disjoint cover of a Gaussian full-measure set. At this stage
the angular and triangular integrations are still written explicitly.
No global Schur formula or eigenvalue distribution is an input.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV the disjoint actual matrix images in fixed linear entry coordinates. -/
def schurDisjointEntryImage (n : ℕ) (k : ℕ) : Set (SchurTangent n) :=
  schurExtendedEntryAt (schurAngularAtlasFrame n k) '' schurDisjointDomain n k

/-- HKPV each full-dimensional integration image is measurable. -/
theorem measurableSet_schurDisjointEntryImage (n : ℕ) (k : ℕ) :
    MeasurableSet (schurDisjointEntryImage n k) :=
  measurableSet_schurExtendedEntryAt_image _ _ _ _
    (measurableSet_schurDisjointDomain n k) (schurDisjointDomain_subset_ordered n k)

/-- HKPV fixed linear entry splitting does not change the chart multiplicity. -/
theorem schurDisjointEntryImage_eq_split_image (n : ℕ) (k : ℕ) :
    schurDisjointEntryImage n k = schurEntrySplit n ''
      (schurExtendedAt (schurAngularAtlasFrame n k) '' schurDisjointDomain n k) := by
  rw [Set.image_image]
  rfl

/-- HKPV no double counting persists in the actual integration coordinates. -/
theorem pairwise_schurDisjointEntryImage (n : ℕ) :
    Pairwise (fun i j => Disjoint (schurDisjointEntryImage n i) (schurDisjointEntryImage n j)) := by
  intro i j hij
  rw [schurDisjointEntryImage_eq_split_image, schurDisjointEntryImage_eq_split_image,
    Set.disjoint_image_iff (schurEntrySplit n).injective]
  exact pairwiseDisjoint_schurExtendedAt_disjointDomain n (Set.mem_univ i) (Set.mem_univ j) hij

/-- HKPV every simple actual matrix lies in the union of the fixed-entry images. -/
theorem entrySplit_simple_mem_iUnion_schurDisjointEntryImage {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.charpoly.Separable) :
    schurEntrySplit n A ∈ ⋃ k, schurDisjointEntryImage n k := by
  obtain ⟨k, x, hx, he⟩ := Set.mem_iUnion.mp (simple_mem_iUnion_schurExtendedAt_disjointDomain A hA)
  refine Set.mem_iUnion_of_mem k ⟨x, hx, ?_⟩
  exact congrArg (schurEntrySplit n) he

/-- **HKPV the disjoint integration images cover the actual Gaussian law almost surely**. -/
theorem gaussianCoordinate_mem_iUnion_schurDisjointEntryImage_ae (n : ℕ)
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ A ∂gaussianCoordinateLaw n a, A ∈ ⋃ k, schurDisjointEntryImage n k := by
  change ∀ᵐ A ∂(gaussianMatrixLaw n a).map (schurFlatEntryMeasurableEquiv n),
    A ∈ ⋃ k, schurDisjointEntryImage n k
  apply (ae_map_iff (schurFlatEntryMeasurableEquiv n).measurable.aemeasurable
    (MeasurableSet.iUnion (measurableSet_schurDisjointEntryImage n))).mpr
  filter_upwards [gaussianMatrix_charpoly_separable_ae n ha] with A hA
  exact entrySplit_simple_mem_iUnion_schurDisjointEntryImage (Matrix.of A.curry) hA

/-- HKPV the actual Gaussian fixed-coordinate density on a measurable set,
for arbitrary nonnegative test functions. -/
theorem setLIntegral_gaussianCoordinateLaw (n : ℕ) {a : ℝ} (ha : 0 < a)
    (s : Set (SchurTangent n)) (hs : MeasurableSet s) (F : SchurTangent n → ℝ≥0∞) :
    ∫⁻ x in s, F x ∂gaussianCoordinateLaw n a =
      ∫⁻ x in s, ENNReal.ofReal (gaussianCoordinateDensity n a x) * F x ∂schurCoordinateVolume n := by
  rw [gaussianCoordinateLaw_eq_withDensity n ha]
  exact setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _
    (measurable_gaussianCoordinateDensity n a).ennreal_ofReal F hs
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))

/-- HKPV a disjoint patch integral uses the actual Jacobian and actual iid density. -/
theorem lintegral_gaussian_schurDisjointEntryImage (n : ℕ) {a : ℝ} (ha : 0 < a)
    (k : ℕ) (F : SchurTangent n → ℝ≥0∞) :
    ∫⁻ y in schurDisjointEntryImage n k, F y ∂gaussianCoordinateLaw n a =
      ∫⁻ x in schurDisjointDomain n k,
        ENNReal.ofReal (schurJacobianWeight 0 x) *
          (ENNReal.ofReal (gaussianCoordinateDensity n a (schurEntryCoordinates 0 x)) *
            F (schurExtendedEntryAt (schurAngularAtlasFrame n k) x)) ∂schurCoordinateVolume n := by
  rw [setLIntegral_gaussianCoordinateLaw n ha _ (measurableSet_schurDisjointEntryImage n k)]
  rw [schurDisjointEntryImage, lintegral_schurExtendedEntryAt_image _ _ _ _
    (measurableSet_schurDisjointDomain n k) (schurDisjointDomain_subset_ordered n k)]
  apply lintegral_congr
  intro x
  rw [schurExtendedEntryAt, schurEntryCoordinates,
    gaussianCoordinateDensity_entrySplit, gaussianCoordinateDensity_entrySplit,
    gaussianMatrixDensity_schurExtendedAt]

/-- **HKPV global Gaussian Schur chart integration**. The right side is
a sum over a proved measurable disjoint cover, not an assumed global
measure-transformation identity. The angular/diagonal separation is the
next step, and is not asserted by this theorem alone. -/
theorem lintegral_gaussianCoordinateLaw_schur_sum (n : ℕ) {a : ℝ} (ha : 0 < a)
    (F : SchurTangent n → ℝ≥0∞) :
    ∫⁻ y, F y ∂gaussianCoordinateLaw n a =
      ∑' k : ℕ, ∫⁻ x in schurDisjointDomain n k,
        ENNReal.ofReal (schurJacobianWeight 0 x) *
          (ENNReal.ofReal (gaussianCoordinateDensity n a (schurEntryCoordinates 0 x)) *
            F (schurExtendedEntryAt (schurAngularAtlasFrame n k) x)) ∂schurCoordinateVolume n := by
  calc
    _ = ∫⁻ y in ⋃ k, schurDisjointEntryImage n k, F y ∂gaussianCoordinateLaw n a := by
      rw [Measure.restrict_eq_self_of_ae_mem
        (gaussianCoordinate_mem_iUnion_schurDisjointEntryImage_ae n ha)]
    _ = ∑' k, ∫⁻ y in schurDisjointEntryImage n k, F y ∂gaussianCoordinateLaw n a :=
      lintegral_iUnion (measurableSet_schurDisjointEntryImage n)
        (pairwise_schurDisjointEntryImage n) F
    _ = _ := by
      congr 1
      funext k
      exact lintegral_gaussian_schurDisjointEntryImage n ha k F

end Ginibre
