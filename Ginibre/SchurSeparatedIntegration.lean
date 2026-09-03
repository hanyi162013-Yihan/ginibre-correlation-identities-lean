import Ginibre.SchurDisjointAtlas
import Ginibre.GaussianCoordinateLaw
import Ginibre.SchurJacobianRegularity
import Ginibre.SchurDensityNormalization

/-!
# Product integration on the disjoint Schur domains

HKPV Section 6.4: disjointification has left a Cartesian angular domain
times the entire ordered spectral chamber times all strict-upper entries.
This file turns that proved geometry into genuine iterated integrals.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV the complete ordered spectral chamber. -/
def schurSpectralChamber (n : ℕ) : Set (Fin n → ℂ) := {z | schurDiagonalOrdered z}

/-- HKPV the spectral chamber is Borel, with no restriction on real-part ties. -/
theorem measurableSet_schurSpectralChamber (n : ℕ) : MeasurableSet (schurSpectralChamber n) :=
  measurableSet_schurDiagonalOrdered n

/-- **HKPV exact product domain after removing overlaps**. Neither the
spectral chamber nor the strict-upper domain depends on the angular patch. -/
theorem schurDisjointDomain_eq_product_preimage (n : ℕ) (k : ℕ) :
    schurDisjointDomain n k = (schurProductEquiv n) ⁻¹'
      (schurAngularRegion n k ×ˢ (schurSpectralChamber n ×ˢ Set.univ)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
    schurProductEquiv_lower]
  have hd : (schurProductEquiv n x).2.1 = fun i => x.2.val i i :=
    funext (schurProductEquiv_diagonal x)
  rw [hd]
  change ((x.1 ∈ schurAngularSource (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n) ∧
    schurDiagonalOrdered (fun i => x.2.val i i)) ∧ x.1 ∈ schurAngularRegion n k) ↔
    x.1 ∈ schurAngularRegion n k ∧ schurDiagonalOrdered (fun i => x.2.val i i)
  constructor
  · exact fun hx => ⟨hx.2, hx.1.2⟩
  · exact fun hx => ⟨⟨hx.1.1, hx.2⟩, hx.1⟩

/-- HKPV exact product-volume transport on each disjoint source. -/
theorem setLIntegral_schurDisjointDomain_product (n : ℕ) (k : ℕ)
    (F : SchurTangent n → ℝ≥0∞) :
    ∫⁻ x in schurDisjointDomain n k, F x ∂schurCoordinateVolume n =
      ∫⁻ y in schurAngularRegion n k ×ˢ (schurSpectralChamber n ×ˢ Set.univ),
        F ((schurProductEquiv n).symm y) := by
  rw [schurDisjointDomain_eq_product_preimage]
  have hp := (schurProductEquiv_measurePreserving n).restrict_preimage_emb
    (schurProductEquiv n).measurableEmbedding
    (schurAngularRegion n k ×ˢ (schurSpectralChamber n ×ˢ Set.univ))
  exact ((MeasurePreserving.symm _ hp).lintegral_comp_emb
    (schurProductEquiv n).symm.measurableEmbedding F).symm

/-- HKPV Tonelli on the actual disjoint angular/diagonal/auxiliary domain. -/
theorem setLIntegral_schurProduct_iterated (n : ℕ) (k : ℕ)
    (H : SchurProductCoordinates n → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ y in schurAngularRegion n k ×ˢ (schurSpectralChamber n ×ˢ Set.univ), H y =
      ∫⁻ w in schurAngularRegion n k, ∫⁻ z in schurSpectralChamber n,
        ∫⁻ t : SchurLower n → ℂ, H (w, z, t) := by
  calc
    _ = ∫⁻ w in schurAngularRegion n k,
        ∫⁻ u in schurSpectralChamber n ×ˢ Set.univ, H (w, u) :=
      setLIntegral_prod H hH.aemeasurable.restrict
    _ = _ := by
      apply lintegral_congr
      intro w
      simpa only [Measure.restrict_univ] using!
        (setLIntegral_prod (μ := (volume : Measure (Fin n → ℂ)))
          (ν := (volume : Measure (SchurLower n → ℂ)))
          (s := schurSpectralChamber n) (t := Set.univ) (fun u => H (w, u))
          (hH.comp measurable_prodMk_left).aemeasurable.restrict)

/-- HKPV the two actual density/Jacobian factors are the already computed
separated product weight, in the exact fixed coordinate measure. -/
theorem schurCoordinateGaussianWeight_eq_product {n : ℕ} (a : ℝ) (x : SchurTangent n) :
    ENNReal.ofReal (schurJacobianWeight 0 x) *
      ENNReal.ofReal (gaussianCoordinateDensity n a (schurEntryCoordinates 0 x)) =
        ENNReal.ofReal (schurGaussianProductWeight n a (schurProductEquiv n x)) := by
  have hJ : 0 ≤ schurJacobianWeight 0 x := by
    rw [schurJacobianWeight_eq_abs_det 0 Matrix.blockTriangular_zero]
    exact abs_nonneg _
  rw [← ENNReal.ofReal_mul hJ, schurGaussianProductWeight,
    MeasurableEquiv.symm_apply_apply]
  rw [schurEntryCoordinates, gaussianCoordinateDensity_entrySplit]

/-- HKPV positivity of the explicit Gaussian coefficient left after
strict-upper integration. -/
theorem schurGaussianScale_pos (n : ℕ) {a : ℝ} (ha : 0 < a) :
    0 < (a / Real.pi) ^ (n * n) * (Real.pi / a) ^ Fintype.card (SchurLower n) :=
  mul_pos (pow_pos (div_pos ha Real.pi_pos) _) (pow_pos (div_pos Real.pi_pos ha) _)

/-- HKPV integrate the full auxiliary Gaussian, including an arbitrary
nonnegative diagonal test; infinite test values cause no division issue. -/
theorem lintegral_schurProduct_test_auxiliary {n : ℕ} {a : ℝ} (ha : 0 < a)
    (w : SchurLower n → ℂ) (z : Fin n → ℂ) (b : ℝ≥0∞) :
    (∫⁻ t : SchurLower n → ℂ, ENNReal.ofReal (schurGaussianProductWeight n a (w, z, t)) * b) =
      ENNReal.ofReal ((a / Real.pi) ^ (n * n) * (Real.pi / a) ^ Fintype.card (SchurLower n)) *
        ENNReal.ofReal |schurAngularJacobian w| * ENNReal.ofReal (schurSpectralWeight n a z) * b := by
  have hm : Measurable (fun t : SchurLower n → ℂ =>
      ENNReal.ofReal (schurGaussianProductWeight n a (w, z, t))) := by
    apply Measurable.ennreal_ofReal
    exact (continuous_schurGaussianProductWeight n a).measurable.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  rw [lintegral_mul_const b hm, lintegral_schurGaussianProductWeight_auxiliary ha]
  congr 1
  rw [← ENNReal.ofReal_mul (schurGaussianScale_pos n ha).le,
    ← ENNReal.ofReal_mul (mul_nonneg (schurGaussianScale_pos n ha).le (abs_nonneg _))]
  congr 1
  unfold schurSpectralWeight
  ring

end Ginibre
