import Sharpness.Unconditional.SingularChainExcisionRelative

/-! Relative-chain comparison for a map of actual open covers. This is the
excision step used by an attachment when its complementary open pieces
and their collar intersections are identified geometrically. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits
open Sharpness.SingularChainExcision

variable (R : Type u) [CommRing R]

def restrictedMap {X Y : TopCat.{u}} (f : X ⟶ Y) {U : Set X} {V : Set Y}
    (h : Set.MapsTo f U V) : TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨f x.val, h x.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem restrictedMap_inclusion {X Y : TopCat.{u}} (f : X ⟶ Y) {U : Set X} {V : Set Y}
    (h : Set.MapsTo f U V) :
    restrictedMap f h ≫ subsetInclusion Y V = subsetInclusion X U ≫ f := rfl

def relativeSubspaceMap {X Y : TopCat.{u}} (f : X ⟶ Y) {U : Set X} {V : Set Y}
    (h : Set.MapsTo f U V) :
    cokernel ((SingularCohomology.chainsFunctor R).map (subsetInclusion X U)) ⟶
      cokernel ((SingularCohomology.chainsFunctor R).map (subsetInclusion Y V)) :=
  cokernel.map _ _
    ((SingularCohomology.chainsFunctor R).map (restrictedMap f h))
    ((SingularCohomology.chainsFunctor R).map f) (by
      rw [← (SingularCohomology.chainsFunctor R).map_comp,
        ← (SingularCohomology.chainsFunctor R).map_comp]
      rfl)

variable {X Y : TopCat.{u}} (f : X ⟶ Y) {U N : Set X} {V M : Set Y}
  (hU : Set.MapsTo f U V) (hN : Set.MapsTo f N M)

def intersectionMapsTo : Set.MapsTo f (U ∩ N) (V ∩ M) :=
  fun _ h => ⟨hU h.1, hN h.2⟩

def relativeIntersectionMap :
    cokernel ((SingularCohomology.chainsFunctor R).map
      (subsetMap X (Set.inter_subset_left : U ∩ N ⊆ U))) ⟶
      cokernel ((SingularCohomology.chainsFunctor R).map
        (subsetMap Y (Set.inter_subset_left : V ∩ M ⊆ V))) :=
  cokernel.map _ _
    ((SingularCohomology.chainsFunctor R).map (restrictedMap f (intersectionMapsTo f hU hN)))
    ((SingularCohomology.chainsFunctor R).map (restrictedMap f hU)) (by
      rw [← (SingularCohomology.chainsFunctor R).map_comp,
        ← (SingularCohomology.chainsFunctor R).map_comp]
      rfl)

theorem relativeExcisionMap_naturality :
    relativeExcisionMap R X U N ≫ relativeSubspaceMap R f hN =
      relativeIntersectionMap R f hU hN ≫ relativeExcisionMap R Y V M := by
  apply (cancel_epi (cokernel.π _)).mp
  simp only [relativeExcisionMap, relativeSubspaceMap, relativeIntersectionMap,
    cokernel.map, cokernel.π_desc_assoc]
  rw [Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc,
    ← Category.assoc, ← Category.assoc,
    ← (SingularCohomology.chainsFunctor R).map_comp,
    ← (SingularCohomology.chainsFunctor R).map_comp]
  rfl

theorem relativeIntersectionMap_isIso
    [IsIso (restrictedMap f hU)]
    [IsIso (restrictedMap f (intersectionMapsTo f hU hN))] :
    IsIso (relativeIntersectionMap R f hU hN) := by
  unfold relativeIntersectionMap
  infer_instance

/-- Excision makes a map of pairs a homology equivalence when its
complementary open pieces and their overlaps are actual isomorphisms. -/
theorem relativeSubspaceMap_quasiIso_of_openCovers
    (hUo : IsOpen U) (hNo : IsOpen N) (hX : ∀ x : X, x ∈ U ∨ x ∈ N)
    (hVo : IsOpen V) (hMo : IsOpen M) (hY : ∀ y : Y, y ∈ V ∨ y ∈ M)
    [IsIso (restrictedMap f hU)]
    [IsIso (restrictedMap f (intersectionMapsTo f hU hN))] :
    QuasiIso (relativeSubspaceMap R f hN) := by
  letI := relativeExcisionMap_quasiIso R X U N hUo hNo hX
  letI := relativeExcisionMap_quasiIso R Y V M hVo hMo hY
  letI := relativeIntersectionMap_isIso R f hU hN
  haveI : QuasiIso (relativeExcisionMap R X U N ≫ relativeSubspaceMap R f hN) := by
    rw [relativeExcisionMap_naturality R f hU hN]
    infer_instance
  exact quasiIso_of_comp_left (relativeExcisionMap R X U N) (relativeSubspaceMap R f hN)

end Sharpness.SingularAttachmentComparison
