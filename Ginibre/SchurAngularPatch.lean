import Ginibre.SchurPhaseUniqueness
import Ginibre.SchurCoordinates

/-!
# Angular patches independent of the triangular variables

HKPV Section 6.3, globalization preparation. A single reference diagonal
with distinct entries fixes an actual open angular patch. Its phase
injectivity then applies to every other distinct ordered diagonal and
arbitrary strict-upper entries. Thus the patch itself is not chosen from
the eigenvalues or the auxiliary Gaussian variables.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV a concrete reference spectrum, fixed before choosing any matrix. -/
def schurReferenceSpectrum (n : ℕ) : Fin n → ℂ := fun i => (i.val : ℂ)

/-- HKPV the chosen reference spectrum is distinct in every dimension. -/
theorem schurReferenceSpectrum_injective (n : ℕ) :
    Function.Injective (schurReferenceSpectrum n) := by
  intro i j h
  apply Fin.ext
  exact Nat.cast_injective h

/-- HKPV a diagonal unitary acts trivially on every diagonal matrix. -/
theorem diagonal_unitary_conjugates_diagonal {n : ℕ} (d z : Fin n → ℂ)
    (hd : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1) :
    Matrix.diagonal d * Matrix.diagonal z * (Matrix.diagonal d).conjTranspose =
      Matrix.diagonal z := by
  have hc : Matrix.diagonal d * Matrix.diagonal z =
      Matrix.diagonal z * Matrix.diagonal d := by
    simp only [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hc, Matrix.mul_assoc, mul_eq_one_comm.mp hd, Matrix.mul_one]

/-- HKPV phase-related frames represent the same reference flag matrix,
for every reference diagonal, independently of their triangular factors. -/
theorem phase_frames_reference_eq {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℂ) (d z : Fin n → ℂ)
    (hd : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1)
    (hV : V = U * Matrix.diagonal d) :
    U * Matrix.diagonal z * U.conjTranspose =
      V * Matrix.diagonal z * V.conjTranspose := by
  rw [hV, Matrix.conjTranspose_mul]
  calc
    _ = U * (Matrix.diagonal d * Matrix.diagonal z * (Matrix.diagonal d).conjTranspose) *
        U.conjTranspose := by rw [diagonal_unitary_conjugates_diagonal d z hd]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- HKPV angular exponential with the triangular parameter set to zero. -/
def schurAngularUnitary {n : ℕ} (w : SchurLower n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  schurUnitaryParam (w, 0)

/-- HKPV the angular frame is an actual unitary matrix. -/
theorem schurAngularUnitary_unitary {n : ℕ} (w : SchurLower n → ℂ) :
    (schurAngularUnitary w).conjTranspose * schurAngularUnitary w = 1 :=
  schurUnitaryParam_unitary (w, 0)

/-- HKPV reference-diagonal exponential chart already constructed by the inverse theorem. -/
def schurDiagonalChart {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z) :
    OpenPartialHomeomorph (SchurTangent n) (Matrix (Fin n) (Fin n) ℂ) :=
  schurLocalChart (Matrix.diagonal z) (Matrix.blockTriangular_diagonal z)
    (by simpa only [Matrix.diagonal_apply_eq] using hz)

/-- HKPV one fixed angular patch, obtained from the actual reference chart. -/
def schurAngularSource {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z) :
    Set (SchurLower n → ℂ) :=
  {w | (w, 0) ∈ (schurDiagonalChart z hz).source}

/-- HKPV the selected angular patch is open. -/
theorem isOpen_schurAngularSource {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z) :
    IsOpen (schurAngularSource z hz) :=
  (schurDiagonalChart z hz).open_source.preimage (continuous_id.prodMk continuous_const)

/-- HKPV this patch contains the identity-frame parameter. -/
theorem zero_mem_schurAngularSource {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z) :
    0 ∈ schurAngularSource z hz :=
  schurLocalChart_zero_mem_source (Matrix.diagonal z) _ _

/-- HKPV the reference chart slice is exactly conjugation by the angular frame. -/
theorem schurDiagonalChart_slice {n : ℕ} (z : Fin n → ℂ) (hz : Function.Injective z)
    (w : SchurLower n → ℂ) :
    schurDiagonalChart z hz (w, 0) =
      schurAngularUnitary w * Matrix.diagonal z * (schurAngularUnitary w).conjTranspose := by
  change schurExpCoordinates (Matrix.diagonal z) (w, 0) = _
  simpa only [ZeroMemClass.coe_zero, add_zero] using!
    schurExpCoordinates_eq_conjugation (Matrix.diagonal z) (w, 0)

/-- HKPV reference conjugation is injective on the constructed angular patch. -/
theorem schurAngularSource_reference_injOn {n : ℕ} (z : Fin n → ℂ)
    (hz : Function.Injective z) :
    Set.InjOn (fun w => schurAngularUnitary w * Matrix.diagonal z *
      (schurAngularUnitary w).conjTranspose) (schurAngularSource z hz) := by
  intro w hw v hv he
  have h : schurDiagonalChart z hz (w, 0) = schurDiagonalChart z hz (v, 0) := by
    simpa only [schurDiagonalChart_slice] using he
  exact congrArg Prod.fst ((schurDiagonalChart z hz).injOn hw hv h)

/-- **HKPV angular injectivity independent of spectral and strict-upper
coordinates**. A collision of ordered simple Schur representations in
one fixed reference patch forces the same angular parameter. -/
theorem schurAngularSource_ordered_collision {n : ℕ}
    (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀)
    (w v : SchurLower n → ℂ) (hw : w ∈ schurAngularSource z₀ hz₀)
    (hv : v ∈ schurAngularSource z₀ hz₀)
    (S T : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i = S i i)
    (hz : Function.Injective (fun i => S i i))
    (he : schurAngularUnitary w * S * (schurAngularUnitary w).conjTranspose =
      schurAngularUnitary v * T * (schurAngularUnitary v).conjTranspose) : w = v := by
  let U := schurAngularUnitary w
  let V := schurAngularUnitary v
  have hU := schurAngularUnitary_unitary w
  have hV := schurAngularUnitary_unitary v
  have hdiag := schur_relative_frame_diagonal U V S T hU hV hS hT hd hz he
  let d : Fin n → ℂ := fun i => (U.conjTranspose * V) i i
  have hdu : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1 := by
    rw [← hdiag]
    exact schur_relative_frame_unitary U V hU hV
  have hVD : V = U * Matrix.diagonal d := by
    rw [← hdiag, ← Matrix.mul_assoc, mul_eq_one_comm.mp hU, Matrix.one_mul]
  exact schurAngularSource_reference_injOn z₀ hz₀ hw hv
    (phase_frames_reference_eq U V d z₀ hdu hVD)

/-- **HKPV full ordered-parameter uniqueness on a fixed angular patch**:
the same patch works for arbitrary triangular factors sharing any simple
ordered diagonal, not just for factors near the reference matrix. -/
theorem schurAngularSource_full_ordered_collision {n : ℕ}
    (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀)
    (w v : SchurLower n → ℂ) (hw : w ∈ schurAngularSource z₀ hz₀)
    (hv : v ∈ schurAngularSource z₀ hz₀)
    (S T : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) (hd : ∀ i, T i i = S i i)
    (hz : Function.Injective (fun i => S i i))
    (he : schurAngularUnitary w * S * (schurAngularUnitary w).conjTranspose =
      schurAngularUnitary v * T * (schurAngularUnitary v).conjTranspose) : w = v ∧ S = T := by
  have hwv := schurAngularSource_ordered_collision z₀ hz₀ w v hw hv S T hS hT hd hz he
  refine ⟨hwv, ?_⟩
  subst v
  have h := schur_relative_frame_intertwines _ _ S T
    (schurAngularUnitary_unitary w) (schurAngularUnitary_unitary w) he
  simpa only [schurAngularUnitary_unitary, Matrix.one_mul, Matrix.mul_one] using h.symm

end Ginibre
