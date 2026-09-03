import Ginibre.SchurAngularPatch
import Ginibre.SchurOrderedSpectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# An actual neighborhood of the reference unitary orbit

HKPV Section 6.3, angular coverage. On the orbit of a fixed real simple
diagonal, a sufficiently small actual Schur chart has zero triangular
variation. Hermitian triangularity and finite spectral exclusion prove
this directly. Thus angular coverage is derived from the previously
constructed inverse-function chart, not assumed as a quotient interface.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV a Hermitian upper-triangular matrix is diagonal. -/
theorem hermitian_upper_eq_diagonal {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (hH : S.IsHermitian) :
    S = Matrix.diagonal (fun i => S i i) := by
  have hoff (i j : Fin n) (hij : i ≠ j) : S i j = 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · have he : star (S i j) = S j i := by
        simpa only [Matrix.conjTranspose_apply] using
          congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A j i) hH
      exact star_eq_zero.mp (he.trans (hS h))
    · exact hS h
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Matrix.diagonal, hij, hoff i j hij]

/-- HKPV the fixed reference diagonal is Hermitian, by its real entries. -/
theorem schurReferenceDiagonal_isHermitian (n : ℕ) :
    (Matrix.diagonal (schurReferenceSpectrum n)).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [schurReferenceSpectrum, isSelfAdjoint_iff]

/-- HKPV exclude the finitely many incorrect diagonal labels near the
reference center; this restriction does not select a random spectrum. -/
def schurReferenceAdmissible (n : ℕ) : Set (SchurTangent n) :=
  {x | ∀ i j : Fin n, i ≠ j →
    (Matrix.diagonal (schurReferenceSpectrum n) + x.2.val) i i ≠ schurReferenceSpectrum n j}

/-- HKPV the finite reference-label exclusion is an open condition. -/
theorem isOpen_schurReferenceAdmissible (n : ℕ) :
    IsOpen (schurReferenceAdmissible n) := by
  simp only [schurReferenceAdmissible, Set.ofPred_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => ?_
  have hc : Continuous (fun x : SchurTangent n =>
      (Matrix.diagonal (schurReferenceSpectrum n) + x.2.val) i i) := by
    convert! (continuous_const.add ((schurUpperTangentCLM n).continuous.matrix_elem i i)) using 1
  exact isOpen_ne.preimage hc

/-- HKPV the reference center satisfies every finite exclusion. -/
theorem zero_mem_schurReferenceAdmissible (n : ℕ) :
    0 ∈ schurReferenceAdmissible n := by
  intro i j hij
  change (Matrix.diagonal (schurReferenceSpectrum n) + (0 : Matrix (Fin n) (Fin n) ℂ)) i i ≠ _
  rw [add_zero, Matrix.diagonal_apply_eq]
  exact (schurReferenceSpectrum_injective n).ne hij

/-- HKPV on the reference orbit, finite exclusion fixes all diagonal
labels, using the actual characteristic polynomial. -/
theorem schurReferenceAdmissible_diagonal {n : ℕ} (x : SchurTangent n)
    (hx : x ∈ schurReferenceAdmissible n)
    (V : Matrix (Fin n) (Fin n) ℂ) (hV : V.conjTranspose * V = 1)
    (he : schurExpCoordinates (Matrix.diagonal (schurReferenceSpectrum n)) x =
      V * Matrix.diagonal (schurReferenceSpectrum n) * V.conjTranspose) :
    ∀ i, (Matrix.diagonal (schurReferenceSpectrum n) + x.2.val) i i =
      schurReferenceSpectrum n i := by
  let D := Matrix.diagonal (schurReferenceSpectrum n)
  let T := D + x.2.val
  have hT : T.IsUpperTriangular :=
    (Matrix.blockTriangular_diagonal _).add x.2.property
  have hc : T.charpoly = D.charpoly := by
    rw [← charpoly_unitary_conjugate _ T (schurUnitaryParam_unitary x)]
    change (schurUnitaryParam x * (D + x.2.val) * (schurUnitaryParam x).conjTranspose).charpoly = _
    rw [← schurExpCoordinates_eq_conjugation, he, charpoly_unitary_conjugate _ _ hV]
  have hr := upper_diagonal_range_eq_of_charpoly_eq T D hT
    (Matrix.blockTriangular_diagonal _) hc
  intro i
  have hm : T i i ∈ Set.range (fun j => D j j) := hr ▸ Set.mem_range_self i
  obtain ⟨j, hj⟩ := hm
  have hj' : T i i = schurReferenceSpectrum n j := by
    simpa only [D, Matrix.diagonal_apply_eq] using hj.symm
  by_cases hij : i = j
  · simpa only [← hij] using hj'
  · exact (hx i j hij hj').elim

/-- **HKPV reference-orbit slice**: the actual inverse Schur parameter
has zero triangular variation on this neighborhood of the reference orbit. -/
theorem schurReferenceAdmissible_upper_zero {n : ℕ} (x : SchurTangent n)
    (hx : x ∈ schurReferenceAdmissible n)
    (V : Matrix (Fin n) (Fin n) ℂ) (hV : V.conjTranspose * V = 1)
    (he : schurExpCoordinates (Matrix.diagonal (schurReferenceSpectrum n)) x =
      V * Matrix.diagonal (schurReferenceSpectrum n) * V.conjTranspose) : x.2 = 0 := by
  let D := Matrix.diagonal (schurReferenceSpectrum n)
  let T := D + x.2.val
  let Q := schurUnitaryParam x
  have hQ : Q.conjTranspose * Q = 1 := schurUnitaryParam_unitary x
  have hA : (schurExpCoordinates D x).IsHermitian := by
    rw [he]
    exact Matrix.isHermitian_mul_mul_conjTranspose V (schurReferenceDiagonal_isHermitian n)
  have hT : T.IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul Q hA
    rw [schurExpCoordinates_eq_conjugation] at h
    have hc : Q.conjTranspose * (Q * T * Q.conjTranspose) * Q = T := by
      calc
        _ = (Q.conjTranspose * Q) * T * (Q.conjTranspose * Q) := by simp only [Matrix.mul_assoc]
        _ = T := by rw [hQ, Matrix.one_mul, Matrix.mul_one]
    exact hc ▸ h
  have hupper : T.IsUpperTriangular :=
    (Matrix.blockTriangular_diagonal _).add x.2.property
  have hdiag : T = D := by
    rw [hermitian_upper_eq_diagonal T hupper hT]
    congr 1
    funext i
    exact schurReferenceAdmissible_diagonal x hx V hV he i
  apply Subtype.ext
  exact add_left_cancel (show D + x.2.val = D + 0 by simpa only [add_zero] using hdiag)

/-- **HKPV an open neighborhood with actual angular coverage**. Every
unitary conjugate of the reference diagonal in this neighborhood is
represented by the fixed angular patch, with no auxiliary triangular term. -/
theorem exists_open_referenceOrbit_neighborhood (n : ℕ) :
    ∃ O : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen O ∧
      Matrix.diagonal (schurReferenceSpectrum n) ∈ O ∧
      ∀ V : Matrix (Fin n) (Fin n) ℂ, V.conjTranspose * V = 1 →
        V * Matrix.diagonal (schurReferenceSpectrum n) * V.conjTranspose ∈ O →
        ∃ w ∈ schurAngularSource (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n),
          V * Matrix.diagonal (schurReferenceSpectrum n) * V.conjTranspose =
            schurAngularUnitary w * Matrix.diagonal (schurReferenceSpectrum n) *
              (schurAngularUnitary w).conjTranspose := by
  let z := schurReferenceSpectrum n
  let hz := schurReferenceSpectrum_injective n
  let c := schurDiagonalChart z hz
  let s := c.source ∩ schurReferenceAdmissible n
  refine ⟨c '' s, c.isOpen_image_source_inter (isOpen_schurReferenceAdmissible n), ?_, ?_⟩
  · refine ⟨0, ⟨schurLocalChart_zero_mem_source _ _ _, zero_mem_schurReferenceAdmissible n⟩, ?_⟩
    exact schurExpCoordinates_zero _
  · intro V hV hO
    obtain ⟨x, hx, he⟩ := hO
    have hx0 := schurReferenceAdmissible_upper_zero x hx.2 V hV he
    have hxpair : x = (x.1, 0) := Prod.ext rfl hx0
    refine ⟨x.1, ?_, ?_⟩
    · change (x.1, 0) ∈ c.source
      exact hxpair ▸ hx.1
    · rw [hxpair, schurDiagonalChart_slice] at he
      exact he.symm

end Ginibre
