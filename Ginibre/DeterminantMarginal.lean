import Ginibre.BorderedDeterminant
import Ginibre.FiniteProjection

/-!
# Integrating one coordinate of a finite projection determinant

BC12 Theorem 3.3: the determinant recursion is proved from integrability,
the trace, and the reproducing identity. These are subsequently discharged
for the explicit Gaussian family; no spectral-distribution input is used.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Ginibre

/-- The `k` by `k` evaluation determinant of a kernel. -/
def kernelDet {X : Type*} (K : X → X → ℂ) (k : ℕ) (z : Fin k → X) : ℂ :=
  Matrix.det (Matrix.of (fun i j => K (z i) (z j)))

/-- BC12 empty-point convention: the empty determinant is one. -/
@[simp] theorem kernelDet_zero {X : Type*} (K : X → X → ℂ) (z : Fin 0 → X) :
    kernelDet K 0 z = 1 := Matrix.det_isEmpty

/-- BC12 one-point convention: the determinant is the diagonal kernel. -/
@[simp] theorem kernelDet_one {X : Type*} (K : X → X → ℂ) (z : Fin 1 → X) :
    kernelDet K 1 z = K (z 0) (z 0) := by
  exact Matrix.det_fin_one (fun i j : Fin 1 => K (z i) (z j))

/-- BC12 marginal algebra: isolate the coordinate which will be integrated. -/
theorem kernelDet_cons_eq {X : Type*} (K : X → X → ℂ) (k : ℕ)
    (u : X) (z : Fin k → X) :
    kernelDet K (k + 1) (Fin.cons u z) = Matrix.det
      (bordered (K u u) (fun j => K u (z j)) (fun i => K (z i) u)
        (Matrix.of (fun i j => K (z i) (z j)))) := by
  unfold kernelDet
  congr 1
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl

/-- BC12 trace identity for an integrable finite orthonormal family. -/
theorem integrable_finiteKernel_diagonal {I X : Type*} [Fintype I]
    [MeasurableSpace X] {μ : Measure X} (φ : I → X → ℂ)
    (hint : ∀ i j, Integrable (fun u => star (φ i u) * φ j u) μ) :
    Integrable (fun u => finiteKernel φ u u) μ := by
  unfold finiteKernel
  apply integrable_finsetSum
  intro i _
  simpa only [mul_comm] using hint i i

/-- BC12 trace identity: the integral of the diagonal equals the rank. -/
theorem integral_finiteKernel_diagonal {I X : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace X] {μ : Measure X} (φ : I → X → ℂ)
    (hint : ∀ i j, Integrable (fun u => star (φ i u) * φ j u) μ)
    (hortho : ∀ i j, (∫ u, star (φ i u) * φ j u ∂μ) = if i = j then 1 else 0) :
    (∫ u, finiteKernel φ u u ∂μ) = (Fintype.card I : ℂ) := by
  unfold finiteKernel
  simp_rw [mul_comm (φ _ _)]
  rw [integral_finsetSum _ (fun i _ => hint i i)]
  simp only [Complex.star_def] at hortho
  simp [hortho]

/-- BC12 one-coordinate marginal: absolute integrability of every section
is established before exchanging the integral and the determinant expansion. -/
theorem integrable_kernelDet_cons {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (K : X → X → ℂ)
    (hdiag : Integrable (fun u => K u u) μ)
    (hprod : ∀ z w, Integrable (fun u => K z u * K u w) μ)
    (k : ℕ) (z : Fin k → X) :
    Integrable (fun u => kernelDet K (k + 1) (Fin.cons u z)) μ := by
  cases k with
  | zero =>
    have heq : (fun u => kernelDet K (0 + 1) (Fin.cons u z)) = (fun u => K u u) := by
      funext u
      exact kernelDet_one K (Fin.cons u z)
    rw [heq]
    exact hdiag
  | succ k =>
    simp_rw [kernelDet_cons_eq, det_bordered]
    refine (hdiag.mul_const _).sub (integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun i _ => ?_)))
    have h := (hprod (z i) (z j)).mul_const
      (cofactor (Matrix.of (fun i j => K (z i) (z j))) i j)
    apply h.congr
    filter_upwards with u
    ring

/-- **BC12 determinant recursion**: integrating one point multiplies the
remaining determinant by `rank - k`. This is valid even at collisions. -/
theorem integral_kernelDet_cons {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (K : X → X → ℂ) (rank : ℂ)
    (hdiag : Integrable (fun u => K u u) μ)
    (htrace : (∫ u, K u u ∂μ) = rank)
    (hprod : ∀ z w, Integrable (fun u => K z u * K u w) μ)
    (hproj : ∀ z w, (∫ u, K z u * K u w ∂μ) = K z w)
    (k : ℕ) (z : Fin k → X) :
    (∫ u, kernelDet K (k + 1) (Fin.cons u z) ∂μ) =
      (rank - (k : ℂ)) * kernelDet K k z := by
  cases k with
  | zero =>
    have heq : (fun u => kernelDet K (0 + 1) (Fin.cons u z)) = (fun u => K u u) := by
      funext u
      exact kernelDet_one K (Fin.cons u z)
    rw [heq, kernelDet_zero, Nat.cast_zero, sub_zero, mul_one]
    exact htrace
  | succ k =>
    let B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j => K (z i) (z j)
    have hint (j i : Fin (k + 1)) : Integrable
        (fun u => (K u (z j) * K (z i) u) * cofactor B i j) μ := by
      have h := (hprod (z i) (z j)).mul_const (cofactor B i j)
      apply h.congr
      filter_upwards with u
      ring
    have hvalue (j i : Fin (k + 1)) :
        (∫ u, (K u (z j) * K (z i) u) * cofactor B i j ∂μ) =
          B i j * cofactor B i j := by
      rw [integral_mul_const]
      rw [show (fun u => K u (z j) * K (z i) u) =
        (fun u => K (z i) u * K u (z j)) by funext u; ring, hproj]
    simp_rw [kernelDet_cons_eq]
    change (∫ u, Matrix.det
      (bordered (K u u) (fun j => K u (z j)) (fun i => K (z i) u) B) ∂μ) =
      (rank - ((k + 1 : ℕ) : ℂ)) * Matrix.det B
    simp_rw [det_bordered]
    rw [integral_sub (hdiag.mul_const _)
      (integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hint j i))),
      integral_mul_const, htrace,
      integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hint j i))]
    simp_rw [integral_finsetSum _ (fun i _ => hint _ i), hvalue]
    rw [sum_entry_cofactor]
    ring

/-- BC12 determinant recursion specialized to a proved orthonormal family;
the only assumptions are the explicit scalar inner-product identities. -/
theorem integral_finiteKernelDet_cons {I X : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace X] {μ : Measure X} (φ : I → X → ℂ)
    (hint : ∀ i j, Integrable (fun u => star (φ i u) * φ j u) μ)
    (hortho : ∀ i j, (∫ u, star (φ i u) * φ j u ∂μ) = if i = j then 1 else 0)
    (k : ℕ) (z : Fin k → X) :
    (∫ u, kernelDet (finiteKernel φ) (k + 1) (Fin.cons u z) ∂μ) =
      ((Fintype.card I : ℂ) - (k : ℂ)) * kernelDet (finiteKernel φ) k z := by
  exact integral_kernelDet_cons (finiteKernel φ) (Fintype.card I)
    (integrable_finiteKernel_diagonal φ hint) (integral_finiteKernel_diagonal φ hint hortho)
    (integrable_finiteKernel_product φ hint) (integral_finiteKernel_product φ hint hortho) k z

end Ginibre
