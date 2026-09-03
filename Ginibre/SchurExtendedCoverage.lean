import Ginibre.SchurAngularCoverage
import Ginibre.SchurOrderedBasis
import Ginibre.SchurOrderedPatch
import Ginibre.SchurChartCoverage

/-!
# A fixed countable extended Schur cover of the entire simple locus

HKPV Section 6.3, the coverage needed for separated global integration.
The countably many frames depend only on the reference angular atlas,
not on the spectrum or auxiliary triangular entries. Unlike the earlier
full-dimensional local atlas, each domain permits all ordered spectra
and every strict-upper entry. Overlap disjointification remains separate.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV full triangular Schur parametrization in a fixed selected frame. -/
def schurExtendedAt {n : ℕ} (U : SchurUnitaryFrame n) (x : SchurTangent n) :
    Matrix (Fin n) (Fin n) ℂ :=
  U.val * schurExpCoordinates 0 x * U.val.conjTranspose

/-- HKPV fixed output frame changes preserve the extended patch injectivity. -/
theorem schurExtendedAt_injOn {n : ℕ} (U : SchurUnitaryFrame n)
    (z₀ : Fin n → ℂ) (hz₀ : Function.Injective z₀) :
    Set.InjOn (schurExtendedAt U) (schurOrderedDomain z₀ hz₀) := by
  intro x hx y hy he
  apply schurExpCoordinates_injOn_orderedDomain z₀ hz₀ hx hy
  exact (unitaryConjugationHomeomorph U.val U.property).injective he

/-- HKPV diagonal unitary changes of frame leave an upper factor's
ordered diagonal unchanged, including all its strict-upper entries. -/
theorem upper_diagonal_unitary_conjugation_diag {n : ℕ}
    (d : Fin n → ℂ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hd : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1) (i : Fin n) :
    (Matrix.diagonal d * S * (Matrix.diagonal d).conjTranspose) i i = S i i := by
  have hD : (Matrix.diagonal d).IsUpperTriangular := Matrix.blockTriangular_diagonal _
  have hD' : (Matrix.diagonal d).conjTranspose.IsUpperTriangular := by
    rw [Matrix.diagonal_conjTranspose]
    exact Matrix.blockTriangular_diagonal _
  have hi : (Matrix.diagonal d) i i * (Matrix.diagonal d).conjTranspose i i = 1 := by
    rw [← upper_mul_apply_diag _ _ hD hD', mul_eq_one_comm.mp hd, Matrix.one_apply_eq]
  rw [upper_mul_apply_diag _ _ (hD.mul hS) hD', upper_mul_apply_diag _ _ hD hS]
  calc
    _ = S i i * ((Matrix.diagonal d) i i * (Matrix.diagonal d).conjTranspose i i) := by ring
    _ = S i i := by rw [hi, mul_one]

/-- **HKPV a fixed countable extended Schur cover**. Every simple matrix
is represented in an injective patch whose only geometric restriction is
on the angle. No smallness restriction remains on the triangular factor. -/
theorem exists_countable_extended_schur_cover (n : ℕ) :
    ∃ C : Set (SchurUnitaryFrame n), C.Countable ∧
      ∀ A : Matrix (Fin n) (Fin n) ℂ, A.charpoly.Separable →
        ∃ U ∈ C, ∃ x ∈ schurOrderedDomain (schurReferenceSpectrum n)
            (schurReferenceSpectrum_injective n), A = schurExtendedAt U x := by
  obtain ⟨C, hC, hcover⟩ := exists_countable_schur_angular_atlas n
  refine ⟨C, hC, ?_⟩
  intro A hA
  obtain ⟨V, S, hV, hS, horder, hrep⟩ := exists_unitary_ordered_schur_of_separable A hA
  obtain ⟨U, hUC, w, hw, d, _, hdu, hframe⟩ := hcover ⟨V, hV⟩
  change V = U.val * schurAngularUnitary w * Matrix.diagonal d at hframe
  let D := Matrix.diagonal d
  have hD : D.IsUpperTriangular := Matrix.blockTriangular_diagonal _
  have hD' : D.conjTranspose.IsUpperTriangular := by
    rw [Matrix.diagonal_conjTranspose]
    exact Matrix.blockTriangular_diagonal _
  let T := D * S * D.conjTranspose
  have hT : T.IsUpperTriangular := (hD.mul hS).mul hD'
  have hordT : schurDiagonalOrdered (fun i => T i i) := by
    simpa only [T, D, upper_diagonal_unitary_conjugation_diag d S hS hdu] using horder
  let x : SchurTangent n := (w, ⟨T, hT⟩)
  refine ⟨U, hUC, x, ⟨hw, hordT⟩, ?_⟩
  rw [hrep, hframe]
  change (U.val * schurAngularUnitary w * D) * S *
      (U.val * schurAngularUnitary w * D).conjTranspose =
    U.val * schurExpCoordinates 0 x * U.val.conjTranspose
  rw [schurExpCoordinates_eq_conjugation]
  change (U.val * schurAngularUnitary w * D) * S *
      (U.val * schurAngularUnitary w * D).conjTranspose =
    U.val * (schurAngularUnitary w * (0 + T) * (schurAngularUnitary w).conjTranspose) *
      U.val.conjTranspose
  simp only [zero_add, Matrix.conjTranspose_mul, Matrix.mul_assoc, T]

/-- **HKPV fixed extended coverage for the actual Gaussian law**.
The countable family is selected before sampling and has no dependence
on eigenvalues or strict-upper Gaussian variables. -/
theorem gaussianMatrix_countable_extended_schur_cover_ae (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : Set (SchurUnitaryFrame n), C.Countable ∧
      ∀ᵐ A ∂gaussianMatrixLaw n a,
        ∃ U ∈ C, ∃ x ∈ schurOrderedDomain (schurReferenceSpectrum n)
            (schurReferenceSpectrum_injective n), Matrix.of A.curry = schurExtendedAt U x := by
  obtain ⟨C, hC, hcover⟩ := exists_countable_extended_schur_cover n
  refine ⟨C, hC, ?_⟩
  filter_upwards [gaussianMatrix_charpoly_separable_ae n ha] with A hA
  exact hcover (Matrix.of A.curry) hA

end Ginibre
