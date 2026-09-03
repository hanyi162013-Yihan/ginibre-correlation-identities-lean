import Ginibre.SchurReferenceOrbit
import Mathlib.Topology.Bases

/-!
# A fixed countable angular atlas covers all unitary frames modulo phase

HKPV Section 6.3, angular globalization. The open reference-orbit
neighborhood is constructed from the actual Schur chart. Its translates
give a countable cover of actual unitary matrices. The same angular
parameter patch works for every triangular factor and every simple
spectrum. No Haar quotient or measurable-selection interface is assumed.
-/

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV actual unitary frames, with the ambient matrix topology. -/
abbrev SchurUnitaryFrame (n : ℕ) :=
  {U : Matrix (Fin n) (Fin n) ℂ // U.conjTranspose * U = 1}

/-- **HKPV countable angular coverage independent of the spectrum**.
Every actual unitary frame is a fixed selected frame times an angular
exponential from the same constructed patch, times a diagonal unitary.
Both the phase norms and its matrix unitarity are proved in the result. -/
theorem exists_countable_schur_angular_atlas (n : ℕ) :
    ∃ C : Set (SchurUnitaryFrame n), C.Countable ∧
      ∀ V : SchurUnitaryFrame n,
        ∃ U ∈ C, ∃ w ∈ schurAngularSource (schurReferenceSpectrum n)
            (schurReferenceSpectrum_injective n),
          ∃ d : Fin n → ℂ, (∀ i, ‖d i‖ = 1) ∧
            (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1 ∧
            V.val = U.val * schurAngularUnitary w * Matrix.diagonal d := by
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  let : SecondCountableTopology (SchurUnitaryFrame n) := by
    convert! (TopologicalSpace.Subtype.secondCountableTopology
      {U : Matrix (Fin n) (Fin n) ℂ | U.conjTranspose * U = 1})
  obtain ⟨O, hO, hcenter, hslice⟩ := exists_open_referenceOrbit_neighborhood n
  let D := Matrix.diagonal (schurReferenceSpectrum n)
  let N : SchurUnitaryFrame n → Set (SchurUnitaryFrame n) := fun U =>
    {V | (U.val.conjTranspose * V.val) * D *
      (U.val.conjTranspose * V.val).conjTranspose ∈ O}
  have hopen (U : SchurUnitaryFrame n) : IsOpen (N U) := by
    apply hO.preimage
    fun_prop
  have hself (U : SchurUnitaryFrame n) : U ∈ N U := by
    change (U.val.conjTranspose * U.val) * D *
      (U.val.conjTranspose * U.val).conjTranspose ∈ O
    simpa only [U.property, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] using hcenter
  obtain ⟨C, hC, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable N hopen
  refine ⟨C, hC, ?_⟩
  intro V
  have hmem : V ∈ ⋃ U : SchurUnitaryFrame n, N U := Set.mem_iUnion_of_mem V (hself V)
  rw [← hcover] at hmem
  obtain ⟨U, hUC, hVU⟩ : ∃ U ∈ C, V ∈ N U := by
    simpa only [Set.mem_iUnion, exists_prop] using hmem
  let R := U.val.conjTranspose * V.val
  have hR : R.conjTranspose * R = 1 :=
    schur_relative_frame_unitary U.val V.val U.property V.property
  obtain ⟨w, hw, hRef⟩ := hslice R hR hVU
  let Q := schurAngularUnitary w
  have hQ : Q.conjTranspose * Q = 1 := schurAngularUnitary_unitary w
  have hD : D.IsUpperTriangular := Matrix.blockTriangular_diagonal _
  have hz : Function.Injective (fun i => D i i) := by
    simpa only [D, Matrix.diagonal_apply_eq] using schurReferenceSpectrum_injective n
  obtain ⟨d, hd, hphase, _⟩ := ordered_schur_factors_phase_unique
    Q R D D hQ hR hD hD (fun _ => rfl) hz hRef.symm
  have hdiag : Q.conjTranspose * R = Matrix.diagonal d := by
    rw [hphase, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have hdu : (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1 := by
    rw [← hdiag]
    exact schur_relative_frame_unitary Q R hQ hR
  refine ⟨U, hUC, w, hw, d, hd, hdu, ?_⟩
  calc
    V.val = U.val * R := by
      change V.val = U.val * (U.val.conjTranspose * V.val)
      rw [← Matrix.mul_assoc, mul_eq_one_comm.mp U.property, Matrix.one_mul]
    _ = U.val * (Q * Matrix.diagonal d) := by rw [hphase]
    _ = U.val * schurAngularUnitary w * Matrix.diagonal d := (Matrix.mul_assoc _ _ _).symm

end Ginibre
