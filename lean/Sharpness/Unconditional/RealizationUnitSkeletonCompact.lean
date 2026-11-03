import Sharpness.Unconditional.RealizationUnitSkeleton
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-! Compact subsets of a countable exhaustive weak filtration are bounded
in the filtration. The topology and separation hypotheses are explicit. This
is a topological finite-stage theorem, not preservation of arbitrary colimits
by singular chains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Set

private theorem finite_subset_monotone_cover {X : Type u} (A : ℕ → Set X)
    (hmono : Monotone A) (hcover : ∀ x, ∃ n, x ∈ A n)
    {s : Set X} (hs : s.Finite) : ∃ n, s ⊆ A n := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x s hx hs ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm⟩ := hcover x
    refine ⟨max n m, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · exact hmono (Nat.le_max_right _ _) hm
    · exact hmono (Nat.le_max_left _ _) (hn hy)

/-- A compact subset of an exhaustive countable weak filtration of a T1
space lies in one stage. The stage maps need not be assumed injective:
the proof only uses their actual ranges, continuity, and final topology. -/
theorem compact_subset_weakFiltration {X : Type u} [TopologicalSpace X] [T1Space X]
    {Y : ℕ → Type v} [∀ n, TopologicalSpace (Y n)] (f : ∀ n, Y n → X)
    (hf : ∀ n, Continuous (f n)) (hmono : Monotone (fun n => Set.range (f n)))
    (hcover : ∀ x, ∃ n, x ∈ Set.range (f n))
    (hfinal : ∀ s : Set X, (∀ n, IsClosed (f n ⁻¹' s)) → IsClosed s)
    {K : Set X} (hK : IsCompact K) : ∃ n, K ⊆ Set.range (f n) := by
  classical
  by_contra h
  have hex : ∀ n, ∃ x, x ∈ K ∧ x ∉ Set.range (f n) := by
    simpa only [not_exists, Set.not_subset] using h
  choose x hxK hxout using hex
  have hrangeK : Set.range x ⊆ K := by
    rintro _ ⟨n, rfl⟩
    exact hxK n
  have hinfinite : (Set.range x).Infinite := by
    intro hfin
    obtain ⟨n, hn⟩ := finite_subset_monotone_cover _ hmono hcover hfin
    exact hxout n (hn ⟨n, rfl⟩)
  have hfinite (B : Set X) (hB : B ⊆ Set.range x) (n : ℕ) :
      (B ∩ Set.range (f n)).Finite := by
    apply ((Finset.range n).finite_toSet.image x).subset
    rintro z ⟨hzB, hzn⟩
    obtain ⟨k, rfl⟩ := hB hzB
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hkn
    exact hxout k (hmono (Nat.le_of_not_gt hkn) hzn)
  have hclosed (B : Set X) (hB : B ⊆ Set.range x) : IsClosed B := by
    apply hfinal B
    intro n
    have he : f n ⁻¹' B = f n ⁻¹' (B ∩ Set.range (f n)) := by
      ext y
      simp
    rw [he]
    exact (hfinite B hB n).isClosed.preimage (hf n)
  have hdiscrete : IsDiscrete (Set.range x) := by
    apply isDiscrete_iff_forall_exists_isOpen.mpr
    intro y hy
    refine ⟨(Set.range x \ {y})ᶜ, (hclosed _ Set.sdiff_subset).isOpen_compl, ?_⟩
    ext z
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzr⟩
      by_contra hzy
      exact hz ⟨hzr, hzy⟩
    · rintro rfl
      exact ⟨by simp, hy⟩
  exact hinfinite ((hK.of_isClosed_subset (hclosed _ (Set.Subset.refl _)) hrangeK).finite hdiscrete)

/-- Every compact subset of an actual sequential TopCat colimit with T1
colimit space is contained in the image of one structure map. -/
theorem compact_subset_sequentialColimit (F : ℕ ⥤ TopCat.{u})
    (c : Cocone F) (hc : IsColimit c) [T1Space c.pt]
    {K : Set c.pt} (hK : IsCompact K) : ∃ n, K ⊆ Set.range (c.ι.app n) := by
  apply @compact_subset_weakFiltration c.pt c.pt.str inferInstance
    (fun n => F.obj n) (fun n => (F.obj n).str)
    (fun n => (c.ι.app n).hom) (fun n => (c.ι.app n).hom.continuous)
  · intro n m hnm z hz
    obtain ⟨y, rfl⟩ := hz
    refine ⟨F.map (homOfLE hnm) y, ?_⟩
    exact ConcreteCategory.congr_hom (c.w (homOfLE hnm)) y
  · intro z
    obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget TopCat) hc) z
    exact ⟨n, y, hy⟩
  · intro s hs
    exact (TopCat.isClosed_iff_of_isColimit c hc s).mpr hs
  · exact hK

open Simplicial in
/-- Applied to the actual skeletal colimit. The T1 realization hypothesis is
explicit and must be established from the geometric attachment construction. -/
theorem compact_subset_realizationSkeleton (X : SSet.{u}) [T1Space |X|]
    {K : Set |X|} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range (SSet.toTop.map (X.skeleton n).ι) := by
  letI : T1Space (realizationSkeletonCocone X).pt :=
    inferInstanceAs (T1Space |X|)
  exact compact_subset_sequentialColimit (realizationSkeletonDiagram X)
    (realizationSkeletonCocone X) (realizationSkeletonIsColimit X) hK

end Sharpness.RealizationUnitHomology
