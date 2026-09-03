import Ginibre.SchurExtendedCoverage

/-!
# An actual ordered spectrum of the sampled matrix

HKPV Section 6.4 and BC12 Theorem 3.2. This is chosen from a Schur
representation whose existence was proved from the characteristic
polynomial. It is not defined by the candidate density. Values outside
the simple-spectrum locus are set to zero; that locus is Gaussian-null.
Measurability is a separate theorem proved using the constructed atlas.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV actual ordered Schur data, not an external hypothesis package. -/
structure OrderedSchurData {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) where
  frame : SchurUnitaryFrame n
  upper : schurUpperSubmodule n
  ordered : schurDiagonalOrdered (fun i => upper.val i i)
  represents : A = frame.val * upper.val * frame.val.conjTranspose

/-- HKPV every simple matrix has the data used in the spectral definition. -/
theorem orderedSchurData_nonempty {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.charpoly.Separable) : Nonempty (OrderedSchurData A) := by
  obtain ⟨U, S, hU, hS, hs, he⟩ := exists_unitary_ordered_schur_of_separable A hA
  exact ⟨⟨⟨U, hU⟩, ⟨S, hS⟩, hs, he⟩⟩

/-- HKPV actual matrix eigenvalues in the fixed lexicographic chamber;
the value on the repeated-spectrum exceptional set is immaterial. -/
def schurSpectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℂ := by
  classical
  exact if hA : A.charpoly.Separable then
    fun i => (Classical.choice (orderedSchurData_nonempty A hA)).upper.val i i
  else 0

/-- HKPV the selected spectrum really is ordered on the simple locus. -/
theorem schurSpectrum_ordered {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.charpoly.Separable) : schurDiagonalOrdered (schurSpectrum A) := by
  rw [schurSpectrum, dif_pos hA]
  exact (Classical.choice (orderedSchurData_nonempty A hA)).ordered

/-- HKPV the chosen eigenvalues are distinct on the simple locus. -/
theorem schurSpectrum_injective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.charpoly.Separable) : Function.Injective (schurSpectrum A) :=
  schurDiagonalOrdered_injective (schurSpectrum_ordered A hA)

/-- **HKPV genuine characteristic roots**: the selected values reproduce
the sampled matrix's characteristic polynomial, including multiplicity. -/
theorem charpoly_eq_prod_schurSpectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.charpoly.Separable) :
    A.charpoly = ∏ i : Fin n, (Polynomial.X - Polynomial.C (schurSpectrum A i)) := by
  rw [schurSpectrum, dif_pos hA]
  let d := Classical.choice (orderedSchurData_nonempty A hA)
  change A.charpoly = ∏ i : Fin n, (Polynomial.X - Polynomial.C (d.upper.val i i))
  calc
    A.charpoly = (d.frame.val * d.upper.val * d.frame.val.conjTranspose).charpoly :=
      congrArg Matrix.charpoly d.represents
    _ = _ := by
      rw [charpoly_unitary_conjugate d.frame.val d.upper.val d.frame.property,
        Matrix.charpoly_of_isUpperTriangular d.upper.val d.upper.property]

/-- HKPV the choice is forced by any actual ordered Schur representation. -/
theorem schurSpectrum_unitary_upper {n : ℕ}
    (U S : Matrix (Fin n) (Fin n) ℂ) (hU : U.conjTranspose * U = 1)
    (hS : S.IsUpperTriangular) (hs : schurDiagonalOrdered (fun i => S i i)) :
    schurSpectrum (U * S * U.conjTranspose) = fun i => S i i := by
  let A := U * S * U.conjTranspose
  have hA : A.charpoly.Separable := by
    rw [charpoly_unitary_conjugate U S hU]
    exact (upper_charpoly_separable_iff S hS).mpr (schurDiagonalOrdered_injective hs)
  change schurSpectrum A = _
  rw [schurSpectrum, dif_pos hA]
  let d := Classical.choice (orderedSchurData_nonempty A hA)
  have hc : d.upper.val.charpoly = S.charpoly := by
    calc
      d.upper.val.charpoly = (d.frame.val * d.upper.val * d.frame.val.conjTranspose).charpoly :=
        (charpoly_unitary_conjugate d.frame.val d.upper.val d.frame.property).symm
      _ = A.charpoly := congrArg Matrix.charpoly d.represents.symm
      _ = S.charpoly := charpoly_unitary_conjugate U S hU
  exact ordered_upper_diagonals_eq_of_charpoly_eq d.upper.val S d.upper.property hS
    d.ordered hs hc

/-- HKPV the actual spectral map reads the diagonal in every extended chart. -/
theorem schurSpectrum_schurExtendedAt {n : ℕ} (U : SchurUnitaryFrame n) (x : SchurTangent n)
    (hx : x ∈ schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n)) :
    schurSpectrum (schurExtendedAt U x) = fun i => x.2.val i i := by
  have hQ : (U.val * schurAngularUnitary x.1).conjTranspose *
      (U.val * schurAngularUnitary x.1) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = (schurAngularUnitary x.1).conjTranspose * (U.val.conjTranspose * U.val) *
          schurAngularUnitary x.1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [U.property, Matrix.mul_one, schurAngularUnitary_unitary]
  have he : schurExtendedAt U x =
      (U.val * schurAngularUnitary x.1) * x.2.val *
        (U.val * schurAngularUnitary x.1).conjTranspose := by
    unfold schurExtendedAt
    rw [schurExpCoordinates_eq_conjugation, zero_add]
    change U.val * (schurAngularUnitary x.1 * x.2.val * (schurAngularUnitary x.1).conjTranspose) *
      U.val.conjTranspose = _
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he]
  exact schurSpectrum_unitary_upper _ _ hQ x.2.property hx.2

/-- HKPV the same actual spectrum in fixed linear entry coordinates. -/
def schurCoordinateSpectrum {n : ℕ} (x : SchurTangent n) : Fin n → ℂ :=
  schurSpectrum ((schurEntrySplit n).symm x)

/-- HKPV fixed entry splitting changes no eigenvalue. -/
theorem schurCoordinateSpectrum_entrySplit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    schurCoordinateSpectrum (schurEntrySplit n A) = schurSpectrum A := by
  rw [schurCoordinateSpectrum, LinearEquiv.symm_apply_apply]

end Ginibre
