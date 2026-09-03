import Ginibre.SchurChartCoverage
import Mathlib.Topology.Bases

/-!
# One countable Schur atlas covers almost every Gaussian matrix

HKPV Section 6.3, the countable-cover step needed before measure
globalization. The selected family is fixed before sampling the matrix;
this is stronger than choosing a chart separately for each outcome.
The selection uses second countability of finite-dimensional matrix space,
not an assumed measurable selection of eigenvectors.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- Concrete data indexing the already constructed charts. This record
is not an external interface: existence is proved below for every simple
matrix from its eigenbasis and the exponential inverse theorem. -/
structure SchurFrame (n : ℕ) where
  U : Matrix (Fin n) (Fin n) ℂ
  S : Matrix (Fin n) (Fin n) ℂ
  unitary : U.conjTranspose * U = 1
  upper : S.IsUpperTriangular
  distinct : Function.Injective (fun i => S i i)

/-- The actual chart indexed by a concrete unitary and triangular pair. -/
def SchurFrame.chart {n : ℕ} (c : SchurFrame n) :
    OpenPartialHomeomorph (SchurTangent n) (Matrix (Fin n) (Fin n) ℂ) :=
  schurChartAt c.U c.S c.unitary c.upper c.distinct

/-- HKPV every simple-spectrum matrix is in a chart from this concrete family. -/
theorem exists_schurFrame_target {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hsep : A.charpoly.Separable) :
    ∃ c : SchurFrame n, A ∈ c.chart.target := by
  obtain ⟨U, S, hU, hS, hz, _, ht⟩ := exists_schur_chart_of_separable A hsep
  exact ⟨⟨U, S, hU, hS, hz⟩, ht⟩

/-- **HKPV countable Schur atlas**: a single countable family of open
injective charts covers the entire simple-spectrum locus. -/
theorem exists_countable_schur_atlas (n : ℕ) :
    ∃ C : Set (SchurFrame n), C.Countable ∧
      ∀ A : Matrix (Fin n) (Fin n) ℂ, A.charpoly.Separable →
        ∃ c ∈ C, A ∈ c.chart.target := by
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  obtain ⟨C, hc, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : SchurFrame n => c.chart.target) (fun c => c.chart.open_target)
  refine ⟨C, hc, ?_⟩
  intro A hA
  obtain ⟨c, ht⟩ := exists_schurFrame_target A hA
  have hmem : A ∈ ⋃ d : SchurFrame n, d.chart.target := Set.mem_iUnion_of_mem c ht
  rw [← hcover] at hmem
  simpa only [Set.mem_iUnion, exists_prop] using hmem

/-- **HKPV countable coverage for the actual Gaussian law**: the family
is fixed, countable, and covers a set of probability one. Overlap weights
and the Schur integration identity are not asserted by this theorem. -/
theorem gaussianMatrix_countable_schur_atlas_ae (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : Set (SchurFrame n), C.Countable ∧
      ∀ᵐ A ∂gaussianMatrixLaw n a, ∃ c ∈ C, Matrix.of A.curry ∈ c.chart.target := by
  obtain ⟨C, hc, hcover⟩ := exists_countable_schur_atlas n
  refine ⟨C, hc, ?_⟩
  filter_upwards [gaussianMatrix_charpoly_separable_ae n ha] with A hA
  exact hcover (Matrix.of A.curry) hA

end Ginibre
