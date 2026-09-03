import Ginibre.SchurRegularity
import Mathlib.Order.WellFounded

/-!
# A deterministic ordering for injective Schur patches

HKPV Section 6.3, permutation bookkeeping. Lexicographic ordering of
real and imaginary parts is used only to select an injective chamber.
It is not asserted that sorted eigenvalues have a symmetric density on
the whole product space. The final spectral statements must still use
symmetric observables or explicitly account for label permutations.
-/

noncomputable section
namespace Ginibre

/-- HKPV one fixed total-order coordinate for complex eigenvalues. -/
def schurLexCode (z : ℂ) : ℝ ×ₗ ℝ := toLex (z.re, z.im)

/-- HKPV ordering retains the full complex number, not just its real part. -/
theorem schurLexCode_injective : Function.Injective schurLexCode := by
  intro z w h
  have hp := congrArg ofLex h
  exact Complex.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)

/-- HKPV the chamber of pairwise distinct lexicographically ordered eigenvalues. -/
def schurDiagonalOrdered {n : ℕ} (z : Fin n → ℂ) : Prop :=
  StrictMono (fun i => schurLexCode (z i))

/-- HKPV ordered diagonals are simple, without an extra spectral assumption. -/
theorem schurDiagonalOrdered_injective {n : ℕ} {z : Fin n → ℂ}
    (hz : schurDiagonalOrdered z) : Function.Injective z := by
  intro i j h
  exact hz.injective (congrArg schurLexCode h)

/-- HKPV the diagonal set of an upper-triangular matrix is exactly its root set. -/
theorem mem_range_diagonal_iff_charpoly_eval_eq_zero {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular) (z : ℂ) :
    z ∈ Set.range (fun i => S i i) ↔ Polynomial.eval z S.charpoly = 0 := by
  rw [Matrix.charpoly_of_isUpperTriangular S hS, Polynomial.eval_prod]
  simp only [Set.mem_range, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  constructor
  · rintro ⟨i, hi⟩
    exact Finset.prod_eq_zero_iff.mpr ⟨i, Finset.mem_univ _, sub_eq_zero.mpr hi.symm⟩
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp h
    exact ⟨i, (sub_eq_zero.mp hi).symm⟩

/-- HKPV equality of characteristic polynomials identifies the diagonal sets. -/
theorem upper_diagonal_range_eq_of_charpoly_eq {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular) (h : S.charpoly = T.charpoly) :
    Set.range (fun i => S i i) = Set.range (fun i => T i i) := by
  ext z
  rw [mem_range_diagonal_iff_charpoly_eval_eq_zero S hS,
    mem_range_diagonal_iff_charpoly_eval_eq_zero T hT, h]

/-- HKPV finite ordered enumerations of the same distinct spectral set agree. -/
theorem schurDiagonalOrdered_eq_of_range_eq {n : ℕ} {z w : Fin n → ℂ}
    (hz : schurDiagonalOrdered z) (hw : schurDiagonalOrdered w)
    (h : Set.range z = Set.range w) : z = w := by
  have hr : Set.range (fun i => schurLexCode (z i)) =
      Set.range (fun i => schurLexCode (w i)) := by
    change Set.range (schurLexCode ∘ z) = Set.range (schurLexCode ∘ w)
    rw [Set.range_comp, Set.range_comp, h]
  have he := (hz.range_inj hw).mp hr
  funext i
  exact schurLexCode_injective (congrFun he i)

/-- **HKPV ordered Schur diagonals agree** for the same characteristic
polynomial. This discharges the diagonal-matching premise of phase
uniqueness on the ordered chamber. -/
theorem ordered_upper_diagonals_eq_of_charpoly_eq {n : ℕ}
    (S T : Matrix (Fin n) (Fin n) ℂ) (hS : S.IsUpperTriangular)
    (hT : T.IsUpperTriangular)
    (hordS : schurDiagonalOrdered (fun i => S i i))
    (hordT : schurDiagonalOrdered (fun i => T i i))
    (h : S.charpoly = T.charpoly) : (fun i => S i i) = (fun i => T i i) :=
  schurDiagonalOrdered_eq_of_range_eq hordS hordT
    (upper_diagonal_range_eq_of_charpoly_eq S T hS hT h)

end Ginibre
