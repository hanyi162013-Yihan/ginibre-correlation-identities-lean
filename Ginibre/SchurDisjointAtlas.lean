import Ginibre.SchurAngularOverlap

/-!
# A measurable disjoint Schur atlas

HKPV Section 6.3--6.4. We enumerate the proved countable angular cover
and assign each reference flag to its first patch. The overlap theorem
then shows that the corresponding full triangular images are pairwise
disjoint and still cover every simple-spectrum matrix.
-/

noncomputable section
open MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Ginibre

/-- HKPV one selected countable angular cover; its existence was proved. -/
def schurAngularAtlasSet (n : ℕ) : Set (SchurUnitaryFrame n) :=
  Classical.choose (exists_countable_schur_angular_atlas n)

/-- HKPV the selected angular cover is countable. -/
theorem schurAngularAtlasSet_countable (n : ℕ) : (schurAngularAtlasSet n).Countable :=
  (Classical.choose_spec (exists_countable_schur_angular_atlas n)).1

/-- HKPV selection retains the already proved angular coverage. -/
theorem schurAngularAtlasSet_covers (n : ℕ) :
    ∀ V : SchurUnitaryFrame n,
      ∃ U ∈ schurAngularAtlasSet n, ∃ w ∈ schurAngularSource (schurReferenceSpectrum n)
          (schurReferenceSpectrum_injective n),
        ∃ d : Fin n → ℂ, (∀ i, ‖d i‖ = 1) ∧
          (Matrix.diagonal d).conjTranspose * Matrix.diagonal d = 1 ∧
          V.val = U.val * schurAngularUnitary w * Matrix.diagonal d :=
  (Classical.choose_spec (exists_countable_schur_angular_atlas n)).2

/-- HKPV the cover is nonempty, including dimension zero. -/
theorem schurAngularAtlasSet_nonempty (n : ℕ) : (schurAngularAtlasSet n).Nonempty := by
  let I : SchurUnitaryFrame n := ⟨1, by simp⟩
  obtain ⟨U, hU, _⟩ := schurAngularAtlasSet_covers n I
  exact ⟨U, hU⟩

/-- HKPV a concrete enumeration of the selected countable cover. -/
def schurAngularAtlasFrame (n : ℕ) : ℕ → SchurUnitaryFrame n :=
  Classical.choose ((schurAngularAtlasSet_countable n).exists_eq_range
    (schurAngularAtlasSet_nonempty n))

/-- HKPV enumeration neither omits nor adds a frame. -/
theorem range_schurAngularAtlasFrame (n : ℕ) :
    Set.range (schurAngularAtlasFrame n) = schurAngularAtlasSet n :=
  (Classical.choose_spec ((schurAngularAtlasSet_countable n).exists_eq_range
    (schurAngularAtlasSet_nonempty n))).symm

/-- HKPV the Borel reference-orbit image of the `k`th patch. -/
def schurAngularPatchImage (n : ℕ) (k : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  schurReferenceAt (schurAngularAtlasFrame n k) ''
    schurAngularSource (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n)

/-- HKPV each selected angular image is Borel. -/
theorem measurableSet_schurAngularPatchImage (n : ℕ) (k : ℕ) :
    MeasurableSet (schurAngularPatchImage n k) :=
  measurableSet_schurReferenceAt_image (schurAngularAtlasFrame n k)

/-- HKPV points of patch `k` whose reference flag did not occur earlier. -/
def schurAngularRegion (n : ℕ) (k : ℕ) : Set (SchurLower n → ℂ) :=
  schurAngularSource (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n) ∩
    schurReferenceAt (schurAngularAtlasFrame n k) ⁻¹'
      (⋃ j ∈ Finset.range k, schurAngularPatchImage n j)ᶜ

/-- HKPV first-patch selection gives a measurable angular region. -/
theorem measurableSet_schurAngularRegion (n : ℕ) (k : ℕ) :
    MeasurableSet (schurAngularRegion n k) := by
  apply (isOpen_schurAngularSource _ _).measurableSet.inter
  apply MeasurableSet.preimage
  · exact (Finset.measurableSet_biUnion _ fun j _ =>
      measurableSet_schurAngularPatchImage n j).compl
  · exact (continuous_schurReferenceAt _).measurable

/-- HKPV the `k`th disjointified angular region times the whole ordered upper chamber. -/
def schurDisjointDomain (n : ℕ) (k : ℕ) : Set (SchurTangent n) :=
  schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n) ∩
    {x | x.1 ∈ schurAngularRegion n k}

/-- HKPV the disjointified full triangular source is measurable. -/
theorem measurableSet_schurDisjointDomain (n : ℕ) (k : ℕ) :
    MeasurableSet (schurDisjointDomain n k) := by
  have hf : Continuous (fun x : SchurTangent n => x.1) := continuous_fst
  apply (measurableSet_schurOrderedDomain _ _).inter
  exact (measurableSet_schurAngularRegion n k).preimage hf.measurable

/-- HKPV disjointification only shrinks the proved injective domain. -/
theorem schurDisjointDomain_subset_ordered (n : ℕ) (k : ℕ) :
    schurDisjointDomain n k ⊆
      schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n) :=
  fun _ hx => hx.1

/-- **HKPV no double counting**: the images of the disjointified full
triangular domains are pairwise disjoint. -/
theorem pairwiseDisjoint_schurExtendedAt_disjointDomain (n : ℕ) :
    Set.PairwiseDisjoint Set.univ (fun k =>
      schurExtendedAt (schurAngularAtlasFrame n k) '' schurDisjointDomain n k) := by
  intro i _ j _ hij
  change Disjoint (schurExtendedAt (schurAngularAtlasFrame n i) '' schurDisjointDomain n i)
    (schurExtendedAt (schurAngularAtlasFrame n j) '' schurDisjointDomain n j)
  apply Set.disjoint_left.mpr
  intro A hi hj
  rcases hi with ⟨x, hx, rfl⟩
  rcases hj with ⟨y, hy, he⟩
  have href := schurExtendedAt_collision_reference
    (schurAngularAtlasFrame n i) (schurAngularAtlasFrame n j) x y hx.1 hy.1 he.symm
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hm : schurReferenceAt (schurAngularAtlasFrame n j) y.1 ∈
        ⋃ q ∈ Finset.range j, schurAngularPatchImage n q := by
      refine Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hij) ?_)
      exact ⟨x.1, hx.2.1, href⟩
    exact hy.2.2 hm
  · have hm : schurReferenceAt (schurAngularAtlasFrame n i) x.1 ∈
        ⋃ q ∈ Finset.range i, schurAngularPatchImage n q := by
      refine Set.mem_iUnion_of_mem j (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hji) ?_)
      exact ⟨y.1, hy.2.1, href.symm⟩
    exact hx.2.2 hm

/-- HKPV the selected angular family gives full triangular coverage. -/
theorem schurAngularAtlasSet_extended_covers {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.charpoly.Separable) :
    ∃ U ∈ schurAngularAtlasSet n, ∃ x ∈ schurOrderedDomain (schurReferenceSpectrum n)
      (schurReferenceSpectrum_injective n), A = schurExtendedAt U x := by
  obtain ⟨V, S, hV, hS, horder, hrep⟩ := exists_unitary_ordered_schur_of_separable A hA
  obtain ⟨U, hUC, w, hw, d, _, hdu, hframe⟩ := schurAngularAtlasSet_covers n ⟨V, hV⟩
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
  rw [hrep, hframe, schurExtendedAt_eq_frame]
  change (U.val * schurAngularUnitary w * D) * S *
      (U.val * schurAngularUnitary w * D).conjTranspose =
    (U.val * schurAngularUnitary w) * T * (U.val * schurAngularUnitary w).conjTranspose
  simp only [T, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- HKPV countable first-patch selection, isolated from all matrix algebra. -/
theorem exists_first_schurAngularPatch (n : ℕ) (r : Matrix (Fin n) (Fin n) ℂ)
    (hp : ∃ k, r ∈ schurAngularPatchImage n k) :
    ∃ k, r ∈ schurAngularPatchImage n k ∧ ∀ j < k, r ∉ schurAngularPatchImage n j := by
  classical
  exact ⟨Nat.find hp, Nat.find_spec hp, fun _ hj => Nat.find_min hp hj⟩

/-- **HKPV global coverage without multiplicity**: every simple matrix
lies in exactly one of the disjointified full triangular patch images. -/
theorem simple_mem_iUnion_schurExtendedAt_disjointDomain {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.charpoly.Separable) :
    A ∈ ⋃ k : ℕ, schurExtendedAt (schurAngularAtlasFrame n k) '' schurDisjointDomain n k := by
  obtain ⟨U, hU, x, hx, hrep⟩ := schurAngularAtlasSet_extended_covers A hA
  have hUr : U ∈ Set.range (schurAngularAtlasFrame n) := by
    rw [range_schurAngularAtlasFrame n]
    exact hU
  obtain ⟨i, hi⟩ := hUr
  let r := schurReferenceAt U x.1
  have hp : ∃ k, r ∈ schurAngularPatchImage n k := by
    refine ⟨i, ?_⟩
    change r ∈ schurReferenceAt (schurAngularAtlasFrame n i) ''
      schurAngularSource (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n)
    rw [hi]
    exact ⟨x.1, hx.1, rfl⟩
  obtain ⟨k, hk, hmin⟩ := exists_first_schurAngularPatch n r hp
  have himage : schurExtendedAt U x ∈ schurExtendedAt (schurAngularAtlasFrame n k) ''
      schurOrderedDomain (schurReferenceSpectrum n) (schurReferenceSpectrum_injective n) :=
    (schurExtendedAt_mem_image_iff_reference U (schurAngularAtlasFrame n k) x hx).mpr hk
  rcases himage with ⟨y, hy, hey⟩
  have href : schurReferenceAt (schurAngularAtlasFrame n k) y.1 = r := by
    exact (schurExtendedAt_collision_reference U (schurAngularAtlasFrame n k) x y hx hy hey.symm).symm
  have hyr : y.1 ∈ schurAngularRegion n k := by
    refine ⟨hy.1, ?_⟩
    intro hm
    simp only [Set.mem_iUnion, exists_prop] at hm
    obtain ⟨j, hj, hmj⟩ := hm
    apply hmin j (Finset.mem_range.mp hj)
    rwa [← href]
  refine Set.mem_iUnion_of_mem k ⟨y, ⟨hy, hyr⟩, ?_⟩
  exact hey.trans hrep.symm

end Ginibre
