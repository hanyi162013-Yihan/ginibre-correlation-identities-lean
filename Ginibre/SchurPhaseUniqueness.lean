import Ginibre.SchurSylvester
import Mathlib.Tactic.Linarith

/-!
# Ordered Schur factors differ only by diagonal unitary phases

HKPV Section 6.3, uniqueness needed for angular-chart overlap accounting.
The mixed Sylvester calculation proves triangularity of an intertwiner;
unitarity then forces it to be diagonal. The conclusion is an actual
comparison of two Schur representations of the same matrix. This does
not yet construct quotient charts or integrate over their overlaps.
-/

noncomputable section
open scoped Matrix
namespace Ginibre

/-- HKPV phase uniqueness: an upper-triangular unitary is diagonal. -/
theorem unitary_upper_eq_diagonal {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.conjTranspose * Q = 1) (hupper : Q.IsUpperTriangular) :
    Q = Matrix.diagonal (fun i => Q i i) := by
  let : Invertible Q := invertibleOfLeftInverse Q Q.conjTranspose hQ
  have hi : Q⁻¹.IsUpperTriangular := Matrix.blockTriangular_inv_of_blockTriangular hupper
  have hstar : Q.conjTranspose.IsUpperTriangular := by
    rwa [Matrix.inv_eq_left_inv hQ] at hi
  have hoff (i j : Fin n) (hij : i ≠ j) : Q i j = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · have hz := hstar h
      simpa only [Matrix.conjTranspose_apply, star_eq_zero] using hz
    · exact hupper h
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Matrix.diagonal, hij, hoff i j hij]

/-- HKPV a unitary diagonal consists of scalar unitary phases. -/
theorem unitary_diagonal_phase_equation {n : ℕ} (d : Fin n → ℂ)
    (hd : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1) (i : Fin n) :
    star (d i) * d i = 1 := by
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i) hd
  simpa only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply] using he

/-- HKPV each diagonal phase has modulus one, with no normalization input. -/
theorem norm_unitary_diagonal_phase {n : ℕ} (d : Fin n → ℂ)
    (hd : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1) (i : Fin n) :
    ‖d i‖ = 1 := by
  have he := congrArg norm (unitary_diagonal_phase_equation d hd i)
  simp only [norm_mul, norm_star, norm_one] at he
  nlinarith [norm_nonneg (d i)]

/-- HKPV relative unitary frame of two actual Schur representations. -/
theorem schur_relative_frame_unitary {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1) :
    (U.conjTranspose * V).conjTranspose * (U.conjTranspose * V) = 1 := by
  have hU' : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = V.conjTranspose * (U * U.conjTranspose) * V := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU', Matrix.mul_one, hV]

/-- HKPV equality of actual represented matrices gives the intertwining equation. -/
theorem schur_relative_frame_intertwines {n : ℕ}
    (U V S T : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (he : U * S * U.conjTranspose = V * T * V.conjTranspose) :
    (U.conjTranspose * V) * T = S * (U.conjTranspose * V) := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => U.conjTranspose * A * V) he
  have hl : U.conjTranspose * (U * S * U.conjTranspose) * V =
      S * (U.conjTranspose * V) := by
    calc
      _ = (U.conjTranspose * U) * S * (U.conjTranspose * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.one_mul]
  have hr : U.conjTranspose * (V * T * V.conjTranspose) * V =
      (U.conjTranspose * V) * T := by
    calc
      _ = (U.conjTranspose * V) * T * (V.conjTranspose * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  rw [hl, hr] at h
  exact h.symm

/-- **HKPV ordered simple Schur uniqueness**: the relative frame of two
representations is diagonal. The order and distinctness assumptions are
explicit; no uniqueness theorem is used as an external input. -/
theorem schur_relative_frame_diagonal {n : ℕ}
    (U V S T : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hd : ∀ i, T i i = S i i) (hz : Function.Injective (fun i => S i i))
    (he : U * S * U.conjTranspose = V * T * V.conjTranspose) :
    U.conjTranspose * V = Matrix.diagonal (fun i => (U.conjTranspose * V) i i) := by
  exact unitary_upper_eq_diagonal _ (schur_relative_frame_unitary U V hU hV)
    (upperTriangular_of_ordered_intertwiner S T _ hS hT hd hz
      (schur_relative_frame_intertwines U V S T hU hV he))

/-- **HKPV phase comparison, in its usable form**: the two unitary
frames and the two triangular factors are related by the same diagonal
unitary. This is the algebraic transition law needed for globalization. -/
theorem ordered_schur_factors_phase_unique {n : ℕ}
    (U V S T : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hV : V.conjTranspose * V = 1)
    (hS : S.IsUpperTriangular) (hT : T.IsUpperTriangular)
    (hd : ∀ i, T i i = S i i) (hz : Function.Injective (fun i => S i i))
    (he : U * S * U.conjTranspose = V * T * V.conjTranspose) :
    ∃ d : Fin n → ℂ, (∀ i, ‖d i‖ = 1) ∧
      V = U * Matrix.diagonal d ∧
      T = (Matrix.diagonal d).conjTranspose * S * Matrix.diagonal d := by
  let d : Fin n → ℂ := fun i => (U.conjTranspose * V) i i
  have hdiag : U.conjTranspose * V = Matrix.diagonal d :=
    schur_relative_frame_diagonal U V S T hU hV hS hT hd hz he
  have hdu : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1 := by
    rw [← hdiag]
    exact schur_relative_frame_unitary U V hU hV
  have hVD : V = U * Matrix.diagonal d := by
    rw [← hdiag, ← Matrix.mul_assoc, mul_eq_one_comm.mp hU, Matrix.one_mul]
  refine ⟨d, norm_unitary_diagonal_phase d hdu, hVD, ?_⟩
  have hi := schur_relative_frame_intertwines U V S T hU hV he
  rw [hdiag] at hi
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => (Matrix.diagonal d).conjTranspose * A) hi
  simpa only [← Matrix.mul_assoc, hdu, Matrix.one_mul] using h

end Ginibre
