import Ginibre.SchurJacobian
import Mathlib.Tactic.FinCases

/-!
# Real-coordinate determinant of the Schur lower block

HKPV (6.3.4)--(6.3.5): multiplication by a complex number has a real
two-by-two matrix with determinant its squared modulus. Applying the
block-triangular determinant theorem makes the Vandermonde square a
genuine real determinant, not merely a norm identity.
-/

noncomputable section
open OrderDual
open scoped BigOperators Matrix
namespace Ginibre

/-- Real-coordinate matrix of multiplication by a complex number. -/
def complexRealBlock (a : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a.re, -a.im; a.im, a.re]

/-- HKPV real Jacobian: a complex scalar contributes its squared modulus. -/
theorem det_complexRealBlock (a : ℂ) :
    Matrix.det (complexRealBlock a) = ‖a‖ ^ 2 := by
  rw [complexRealBlock, Matrix.det_fin_two, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]
  change a.re * a.re - (-a.im) * a.im = a.re * a.re + a.im * a.im
  ring

/-- HKPV real-coordinate bookkeeping: zero scalar gives the zero block. -/
@[simp] theorem complexRealBlock_zero : complexRealBlock 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complexRealBlock]

/-- HKPV real-coordinate identification: the two-by-two block actually
acts as complex multiplication on real and imaginary parts. -/
theorem complexRealBlock_mulVec (a z : ℂ) :
    complexRealBlock a *ᵥ ![z.re, z.im] = ![(a * z).re, (a * z).im] := by
  ext i
  fin_cases i <;>
    simp [complexRealBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- Replace each complex coefficient with its actual real two-by-two block. -/
def realifyMatrix {I : Type*} (A : Matrix I I ℂ) : Matrix (I × Fin 2) (I × Fin 2) ℝ :=
  Matrix.of (fun p q => complexRealBlock (A p.1 q.1) p.2 q.2)

/-- The coordinates inside a diagonal real block are precisely `Fin 2`. -/
def realBlockIndexEquiv {I : Type*} (i : I) :
    {p : I × Fin 2 // toDual p.1 = toDual i} ≃ Fin 2 where
  toFun p := p.val.2
  invFun j := ⟨(i, j), rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext p.property.symm rfl
  right_inv _ := rfl

/-- HKPV block Jacobian: each diagonal block contributes exactly one
squared modulus, independently of the surrounding off-diagonal blocks. -/
theorem det_realifyMatrix_block {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (i : I) :
    Matrix.det ((realifyMatrix A).toSquareBlock (fun p => toDual p.1) (toDual i)) =
      ‖A i i‖ ^ 2 := by
  let e := realBlockIndexEquiv i
  let B := (realifyMatrix A).toSquareBlock (fun p => toDual p.1) (toDual i)
  have hB : Matrix.reindex e e B = complexRealBlock (A i i) := by
    ext r c
    rfl
  calc
    Matrix.det B = Matrix.det (Matrix.reindex e e B) := (Matrix.det_reindex_self e B).symm
    _ = Matrix.det (complexRealBlock (A i i)) := congrArg Matrix.det hB
    _ = ‖A i i‖ ^ 2 := det_complexRealBlock _

/-- HKPV (6.3.4): realification preserves lower block triangularity. -/
theorem realifyMatrix_blockTriangular {I : Type*} [LinearOrder I]
    (A : Matrix I I ℂ) (hA : A.IsLowerTriangular) :
    (realifyMatrix A).BlockTriangular (fun p => toDual p.1) := by
  intro p q hpq
  have h : A p.1 q.1 = 0 := hA hpq
  simp [realifyMatrix, h]

/-- HKPV real determinant calculation for any triangular complex block. -/
theorem det_realifyMatrix_of_lowerTriangular {I : Type*} [Fintype I] [LinearOrder I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsLowerTriangular) :
    Matrix.det (realifyMatrix A) = ∏ i, ‖A i i‖ ^ 2 := by
  rw [(realifyMatrix_blockTriangular A hA).det_fintype]
  change (∏ i : I, Matrix.det ((realifyMatrix A).toSquareBlock
    (fun p => toDual p.1) (toDual i))) = _
  simp only [det_realifyMatrix_block]

/-- **HKPV Schur lower-block Jacobian, real determinant**.
Every index represents the pair `(Re Ω_ij, Im Ω_ij)` for `i > j`. -/
theorem det_real_schurLowerMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) :
    Matrix.det (realifyMatrix (schurLowerMatrix S)) =
      ∏ p : SchurLower n,
        ‖S (schurCol p) (schurCol p) - S (schurRow p) (schurRow p)‖ ^ 2 := by
  calc
    Matrix.det (realifyMatrix (schurLowerMatrix S)) =
        ∏ p : SchurLower n, ‖schurLowerMatrix S p p‖ ^ 2 :=
      det_realifyMatrix_of_lowerTriangular (I := SchurLower n) (schurLowerMatrix S)
        (schurLowerMatrix_isLowerTriangular S hS)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p _
      rw [schurLowerMatrix_diag]

/-- HKPV (6.3.4)--(6.3.5): adding the upper-triangular differential
coordinates contributes an identity block. Its coupling to lower
coordinates has no effect on the determinant. This is a block-algebra
theorem, not an assumed change-of-measure formula. -/
theorem det_schur_bordered_differential {n : ℕ} {J : Type*}
    [Fintype J] [DecidableEq J] (S : Matrix (Fin n) (Fin n) ℂ)
    (hS : S.IsUpperTriangular) (C : Matrix J (SchurLower n × Fin 2) ℝ) :
    Matrix.det (Matrix.fromBlocks (realifyMatrix (schurLowerMatrix S))
      (0 : Matrix (SchurLower n × Fin 2) J ℝ) C (1 : Matrix J J ℝ)) =
      ∏ p : SchurLower n,
        ‖S (schurCol p) (schurCol p) - S (schurRow p) (schurRow p)‖ ^ 2 := by
  calc
    Matrix.det (Matrix.fromBlocks (realifyMatrix (schurLowerMatrix S))
        (0 : Matrix (SchurLower n × Fin 2) J ℝ) C (1 : Matrix J J ℝ)) =
        Matrix.det (realifyMatrix (schurLowerMatrix S)) * Matrix.det (1 : Matrix J J ℝ) :=
      Matrix.det_fromBlocks_zero₁₂ (realifyMatrix (schurLowerMatrix S)) C (1 : Matrix J J ℝ)
    _ = Matrix.det (realifyMatrix (schurLowerMatrix S)) := by rw [Matrix.det_one, mul_one]
    _ = _ := det_real_schurLowerMatrix S hS

end Ginibre
