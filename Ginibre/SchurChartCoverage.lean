import Ginibre.SchurCoordinates
import Ginibre.SchurExistence
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Schur charts cover the simple-spectrum matrix locus

HKPV Section 6.3, chart existence and coverage. Translate the actual
exponential chart by the unitary factor of a constructed Schur
representation. Every simple-spectrum matrix is the center of one of
these open, injective coordinate charts; this also holds almost surely
for the actual Gaussian matrix law.

This is topological coverage. It does not identify an angular quotient
measure, compute chart transition multiplicities, or integrate out the
angular and strictly upper-triangular variables.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV change of ambient frame: unitary conjugation is an actual
homeomorphism, with conjugation by the adjoint as its inverse. -/
def unitaryConjugationHomeomorph {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) :
    Matrix (Fin n) (Fin n) ℂ ≃ₜ Matrix (Fin n) (Fin n) ℂ where
  toFun B := U * B * U.conjTranspose
  invFun B := U.conjTranspose * B * U
  left_inv B := by
    calc
      U.conjTranspose * (U * B * U.conjTranspose) * U =
          (U.conjTranspose * U) * B * (U.conjTranspose * U) := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [hU, Matrix.one_mul, Matrix.mul_one]
  right_inv B := by
    have hU' : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
    calc
      U * (U.conjTranspose * B * U) * U.conjTranspose =
          (U * U.conjTranspose) * B * (U * U.conjTranspose) := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [hU', Matrix.one_mul, Matrix.mul_one]
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

/-- HKPV exponential Schur chart transported into the actual matrix frame. -/
def schurChartAt {n : ℕ} (U S : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i)) :
    OpenPartialHomeomorph (SchurTangent n) (Matrix (Fin n) (Fin n) ℂ) :=
  (schurLocalChart S hS hz).transHomeomorph (unitaryConjugationHomeomorph U hU)

/-- HKPV the chart retains the explicit exponential conjugation formula. -/
theorem schurChartAt_apply {n : ℕ} (U S : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i)) (x : SchurTangent n) :
    schurChartAt U S hU hS hz x = U * schurExpCoordinates S x * U.conjTranspose := rfl

/-- HKPV a chart centered at `U S U*` has zero in its coordinate domain. -/
theorem schurChartAt_zero_mem_source {n : ℕ} (U S : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i)) :
    0 ∈ (schurChartAt U S hU hS hz).source :=
  schurLocalChart_zero_mem_source S hS hz

/-- HKPV the target of this injective chart is an open neighborhood of
the prescribed Schur-represented matrix. -/
theorem schurChartAt_center_mem_target {n : ℕ} (U S : Matrix (Fin n) (Fin n) ℂ)
    (hU : U.conjTranspose * U = 1) (hS : S.IsUpperTriangular)
    (hz : Function.Injective (fun i => S i i)) :
    U * S * U.conjTranspose ∈ (schurChartAt U S hU hS hz).target := by
  have h := (schurChartAt U S hU hS hz).map_source
    (schurChartAt_zero_mem_source U S hU hS hz)
  rwa [schurChartAt_apply, schurExpCoordinates_zero] at h

/-- **HKPV chart coverage**: every simple-spectrum complex matrix lies
in the open target of a constructed, injective Schur coordinate chart. -/
theorem exists_schur_chart_of_separable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hsep : A.charpoly.Separable) :
    ∃ (U S : Matrix (Fin n) (Fin n) ℂ) (hU : U.conjTranspose * U = 1)
      (hS : S.IsUpperTriangular) (hz : Function.Injective (fun i => S i i)),
      A = U * S * U.conjTranspose ∧ A ∈ (schurChartAt U S hU hS hz).target := by
  obtain ⟨U, S, hU, hS, hrep⟩ := exists_unitary_schur_of_separable A hsep
  have hsepS : S.charpoly.Separable := by
    rwa [hrep, charpoly_unitary_conjugate U S hU] at hsep
  have hz := (upper_charpoly_separable_iff S hS).mp hsepS
  refine ⟨U, S, hU, hS, hz, hrep, ?_⟩
  rw [hrep]
  exact schurChartAt_center_mem_target U S hU hS hz

/-- **HKPV actual Gaussian chart coverage**: no assumed Schur
representation, local inverse, or spectral-law interface is needed. -/
theorem gaussianMatrix_schur_chart_coverage_ae (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ A ∂gaussianMatrixLaw n a,
      ∃ (U S : Matrix (Fin n) (Fin n) ℂ) (hU : U.conjTranspose * U = 1)
        (hS : S.IsUpperTriangular) (hz : Function.Injective (fun i => S i i)),
        Matrix.of A.curry = U * S * U.conjTranspose ∧
          Matrix.of A.curry ∈ (schurChartAt U S hU hS hz).target := by
  filter_upwards [gaussianMatrix_charpoly_separable_ae n ha] with A hA
  exact exists_schur_chart_of_separable (Matrix.of A.curry) hA

end Ginibre
