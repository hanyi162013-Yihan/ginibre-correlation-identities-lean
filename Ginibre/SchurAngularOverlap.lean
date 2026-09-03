import Ginibre.SchurExtendedIntegration

/-!
# Schur overlaps depend only on the angular variable

HKPV Section 6.3, overlap accounting before global integration. The
reference matrix is an actual conjugate of diag(0,...,n-1), not an
assumed quotient coordinate. Ordered Schur uniqueness proves that
overlap membership is independent of every triangular variable.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV the matrix sets below use the actual ambient Borel sigma-algebra. -/
instance schurMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _

instance schurMatrixBorelSpace (n : ℕ) :
    BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩

instance schurMatrixNormBorelSpace (n : ℕ) :
    @BorelSpace (Matrix (Fin n) (Fin n) ℂ)
      (inferInstance : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (schurMatrixMeasurableSpace n) := ⟨rfl⟩

/-- HKPV the actual total frame in a translated angular patch. -/
def schurFrameAt {n : ℕ} (U : SchurUnitaryFrame n) (w : SchurLower n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := U.val * schurAngularUnitary w

/-- HKPV multiplication of the fixed frame and the angular frame preserves unitarity. -/
theorem schurFrameAt_unitary {n : ℕ} (U : SchurUnitaryFrame n) (w : SchurLower n → ℂ) :
    (schurFrameAt U w).conjTranspose * schurFrameAt U w = 1 := by
  unfold schurFrameAt
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (schurAngularUnitary w).conjTranspose * (U.val.conjTranspose * U.val) *
        schurAngularUnitary w := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [U.property, Matrix.mul_one, schurAngularUnitary_unitary]

/-- HKPV the extended matrix is represented by the total frame and the full upper factor. -/
theorem schurExtendedAt_eq_frame {n : ℕ} (U : SchurUnitaryFrame n) (x : SchurTangent n) :
    schurExtendedAt U x = schurFrameAt U x.1 * x.2.val * (schurFrameAt U x.1).conjTranspose := by
  unfold schurExtendedAt
  rw [schurExpCoordinates_eq_conjugation, zero_add]
  change U.val * (schurAngularUnitary x.1 * x.2.val * (schurAngularUnitary x.1).conjTranspose) *
    U.val.conjTranspose = _
  simp only [schurFrameAt, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- HKPV the reference conjugate records the ordered angular flag. -/
def schurReferenceAt {n : ℕ} (U : SchurUnitaryFrame n) (w : SchurLower n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  schurFrameAt U w * Matrix.diagonal (schurReferenceSpectrum n) * (schurFrameAt U w).conjTranspose

/-- HKPV the concrete reference-orbit parametrization is continuous. -/
theorem continuous_schurReferenceAt {n : ℕ} (U : SchurUnitaryFrame n) :
    Continuous (schurReferenceAt U) := by
  have hslice : Continuous (fun w : SchurLower n → ℂ =>
      schurExpCoordinates (Matrix.diagonal (schurReferenceSpectrum n)) (w, 0)) :=
    (contDiff_schurExpCoordinates 0 (Matrix.diagonal (schurReferenceSpectrum n))).continuous.comp
      (continuous_id.prodMk continuous_const)
  have h := (unitaryConjugationHomeomorph U.val U.property).continuous.comp hslice
  change Continuous (fun w : SchurLower n → ℂ => U.val *
    schurExpCoordinates (Matrix.diagonal (schurReferenceSpectrum n)) (w, 0) * U.val.conjTranspose) at h
  change Continuous (fun w : SchurLower n → ℂ =>
    (U.val * schurAngularUnitary w) * Matrix.diagonal (schurReferenceSpectrum n) *
      (U.val * schurAngularUnitary w).conjTranspose)
  simpa only [schurReferenceAt, schurFrameAt, schurExpCoordinates_eq_conjugation,
    schurAngularUnitary, ZeroMemClass.coe_zero, add_zero,
    Matrix.conjTranspose_mul, Matrix.mul_assoc] using! h

/-- HKPV each concrete reference-orbit parametrization is injective on the common patch. -/
theorem schurReferenceAt_injOn {n : ℕ} (U : SchurUnitaryFrame n) :
    Set.InjOn (schurReferenceAt U)
      (schurAngularSource (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n)) := by
  intro w hw v hv he
  apply schurAngularSource_reference_injOn _ _ hw hv
  apply (unitaryConjugationHomeomorph U.val U.property).injective
  change U.val * (schurAngularUnitary w * Matrix.diagonal (schurReferenceSpectrum n) *
    (schurAngularUnitary w).conjTranspose) * U.val.conjTranspose =
    U.val * (schurAngularUnitary v * Matrix.diagonal (schurReferenceSpectrum n) *
    (schurAngularUnitary v).conjTranspose) * U.val.conjTranspose
  simpa only [schurReferenceAt, schurFrameAt, Matrix.conjTranspose_mul,
    Matrix.mul_assoc] using! he

/-- HKPV every angular reference-patch image is a Borel matrix set. -/
theorem measurableSet_schurReferenceAt_image {n : ℕ} (U : SchurUnitaryFrame n) :
    MeasurableSet (schurReferenceAt U ''
      schurAngularSource (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n)) :=
  (isOpen_schurAngularSource _ _).measurableSet.image_of_continuousOn_injOn
    (continuous_schurReferenceAt U).continuousOn (schurReferenceAt_injOn U)

/-- HKPV ordered Schur collisions give exactly the same reference conjugate. -/
theorem ordered_schur_collision_reference {n : ℕ}
    (P Q S T : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.conjTranspose * P = 1) (hQ : Q.conjTranspose * Q = 1)
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hs : schurDiagonalOrdered (fun i => S i i))
    (ht : schurDiagonalOrdered (fun i => T i i))
    (he : P * S * P.conjTranspose = Q * T * Q.conjTranspose) :
    P * Matrix.diagonal (schurReferenceSpectrum n) * P.conjTranspose =
      Q * Matrix.diagonal (schurReferenceSpectrum n) * Q.conjTranspose := by
  have hc : S.charpoly = T.charpoly := by
    rw [← charpoly_unitary_conjugate P S hP, ← charpoly_unitary_conjugate Q T hQ, he]
  have hd := ordered_upper_diagonals_eq_of_charpoly_eq S T hS hT hs ht hc
  have hdiag := schur_relative_frame_diagonal P Q S T hP hQ hS hT
    (fun i => (congrFun hd i).symm) (schurDiagonalOrdered_injective hs) he
  let d : Fin n → ℂ := fun i => (P.conjTranspose * Q) i i
  have hdu : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1 := by
    rw [← hdiag]
    exact schur_relative_frame_unitary P Q hP hQ
  have hframe : Q = P * Matrix.diagonal d := by
    rw [← hdiag, ← Matrix.mul_assoc, mul_eq_one_comm.mp hP, Matrix.one_mul]
  exact phase_frames_reference_eq P Q d (schurReferenceSpectrum n) hdu hframe

/-- HKPV a collision between two extended ordered patches is an angular collision. -/
theorem schurExtendedAt_collision_reference {n : ℕ}
    (U V : SchurUnitaryFrame n) (x y : SchurTangent n)
    (hx : x ∈ schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n))
    (hy : y ∈ schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n))
    (he : schurExtendedAt U x = schurExtendedAt V y) :
    schurReferenceAt U x.1 = schurReferenceAt V y.1 := by
  rw [schurExtendedAt_eq_frame, schurExtendedAt_eq_frame] at he
  exact ordered_schur_collision_reference _ _ _ _
    (schurFrameAt_unitary U x.1) (schurFrameAt_unitary V y.1)
    x.2.property y.2.property hx.2 hy.2 he

/-- HKPV converse overlap law: equal reference conjugates transport every
upper factor, preserving its entire diagonal. No density formula is assumed. -/
theorem reference_collision_upper_transport {n : ℕ}
    (P Q S : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.conjTranspose * P = 1) (hQ : Q.conjTranspose * Q = 1)
    (hS : S.IsUpperTriangular)
    (he : P * Matrix.diagonal (schurReferenceSpectrum n) * P.conjTranspose =
      Q * Matrix.diagonal (schurReferenceSpectrum n) * Q.conjTranspose) :
    ∃ T : Matrix (Fin n) (Fin n) ℂ, T.IsUpperTriangular ∧
      (∀ i, T i i = S i i) ∧ P * S * P.conjTranspose = Q * T * Q.conjTranspose := by
  let R := Matrix.diagonal (schurReferenceSpectrum n)
  have hR : R.IsUpperTriangular := Matrix.blockTriangular_diagonal _
  have hz : Function.Injective (fun i => R i i) := by
    simpa only [R, Matrix.diagonal_apply_eq] using schurReferenceSpectrum_injective n
  have hdiag := schur_relative_frame_diagonal P Q R R hP hQ hR hR (fun _ => rfl) hz he
  let d : Fin n → ℂ := fun i => (P.conjTranspose * Q) i i
  let D := Matrix.diagonal d
  have hdu : D.conjTranspose * D = 1 := by
    change (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1
    rw [← hdiag]
    exact schur_relative_frame_unitary P Q hP hQ
  have hframe : Q = P * D := by
    change Q = P * Matrix.diagonal d
    rw [← hdiag, ← Matrix.mul_assoc, mul_eq_one_comm.mp hP, Matrix.one_mul]
  have hD : D.IsUpperTriangular := Matrix.blockTriangular_diagonal _
  have hD' : D.conjTranspose.IsUpperTriangular := by
    rw [Matrix.diagonal_conjTranspose]
    exact Matrix.blockTriangular_diagonal _
  let T := D.conjTranspose * S * D
  refine ⟨T, (hD'.mul hS).mul hD, ?_, ?_⟩
  · intro i
    have hi : D.conjTranspose i i * D i i = 1 := by
      rw [← upper_mul_apply_diag _ _ hD' hD, hdu, Matrix.one_apply_eq]
    change (D.conjTranspose * S * D) i i = S i i
    rw [upper_mul_apply_diag _ _ (hD'.mul hS) hD, upper_mul_apply_diag _ _ hD' hS]
    calc
      _ = S i i * (D.conjTranspose i i * D i i) := by ring
      _ = S i i := by rw [hi, mul_one]
  · rw [hframe]
    symm
    calc
      _ = P * (D * D.conjTranspose) * S * (D * D.conjTranspose) * P.conjTranspose := by
        simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [mul_eq_one_comm.mp hdu, Matrix.mul_one, Matrix.mul_one]

/-- **HKPV spectrum-independent overlap equivalence**. Membership in
another full ordered Schur image is determined solely by the reference
angular conjugate, so disjointification need not restrict eigenvalues
or auxiliary Gaussian entries. -/
theorem schurExtendedAt_mem_image_iff_reference {n : ℕ}
    (U V : SchurUnitaryFrame n) (x : SchurTangent n)
    (hx : x ∈ schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n)) :
    schurExtendedAt U x ∈ schurExtendedAt V ''
        schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n) ↔
      schurReferenceAt U x.1 ∈ schurReferenceAt V ''
        schurAngularSource (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n) := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y.1, hy.1, (schurExtendedAt_collision_reference U V x y hx hy he.symm).symm⟩
  · rintro ⟨v, hv, he⟩
    obtain ⟨T, hT, hd, hrep⟩ := reference_collision_upper_transport
      (schurFrameAt U x.1) (schurFrameAt V v) x.2.val
      (schurFrameAt_unitary U x.1) (schurFrameAt_unitary V v) x.2.property he.symm
    let y : SchurTangent n := (v, ⟨T, hT⟩)
    have hy : y ∈ schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n) := by
      refine ⟨hv, ?_⟩
      change schurDiagonalOrdered (fun i => T i i)
      simpa only [hd] using hx.2
    refine ⟨y, hy, ?_⟩
    simpa only [schurExtendedAt_eq_frame] using! hrep.symm

end Ginibre
