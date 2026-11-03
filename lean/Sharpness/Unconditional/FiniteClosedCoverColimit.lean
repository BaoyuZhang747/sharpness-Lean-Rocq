import Mathlib.CategoryTheory.Limits.Types.Multicoequalizer
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.LocallyFinite

/-! Finite closed covers as actual topological multicoequalizers.
The objects are literal subspaces and the maps are literal inclusions.
Closedness is needed only relative to the covered subspace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v w
namespace Sharpness.FiniteClosedCover
open CategoryTheory CategoryTheory.Limits

variable {X : Type u} [TopologicalSpace X]

/-- The actual subspace diagram, with its inclusion maps. -/
def subsetFunctor : Set X ⥤ TopCat.{u} where
  obj A := TopCat.of A
  map f := TopCat.ofHom (ContinuousMap.inclusion (leOfHom f))

@[simp] theorem subsetFunctor_obj (A : Set X) :
    subsetFunctor.obj A = TopCat.of A := rfl

@[simp] theorem subsetFunctor_map_apply {A B : Set X} (f : A ⟶ B) (x : A) :
    subsetFunctor.map f x = ⟨x.val, leOfHom f x.property⟩ := rfl

/-- Native continuous gluing on a finite family of relatively closed subspaces. -/
theorem continuous_of_cover {I : Type v} [Finite I]
    {A : Set X} (U : I → Set X) (hUA : ∀ i, U i ⊆ A)
    (hcover : ∀ x ∈ A, ∃ i, x ∈ U i)
    (hclosed : ∀ i, IsClosed (Subtype.val ⁻¹' U i : Set A))
    {Y : Type w} [TopologicalSpace Y] (f : A → Y)
    (hf : ∀ i, Continuous (fun x : U i => f ⟨x.val, hUA i x.property⟩)) :
    Continuous f := by
  let W : I → Set A := fun i => Subtype.val ⁻¹' U i
  apply (locallyFinite_of_finite W).continuous
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := hcover x.val x.property
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · exact hclosed
  · intro i
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun x : W i => (⟨x.val.val, x.property⟩ : U i)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (hf i).comp hc

variable {I : Type v} [Finite I] {A : Set X}
    {U : I → Set X} {V : I → I → Set X}

omit [Finite I] in
@[simp] theorem multicofork_π_apply
    (h : CompleteLattice.MulticoequalizerDiagram A U V) (i : I) (x : U i) :
    (h.multicofork.map subsetFunctor).π i x =
      ⟨x.val, ((le_iSup U i).trans h.iSup_eq.le) x.property⟩ := rfl

/-- The literal subspace A is the colimit of a finite relatively closed cover
and all its pairwise intersections, including empty intersections. -/
def isColimit (h : CompleteLattice.MulticoequalizerDiagram A U V)
    (hclosed : ∀ i, IsClosed (Subtype.val ⁻¹' U i : Set A)) :
    IsColimit (h.multicofork.map subsetFunctor) := by
  let K := h.multicofork.map (subsetFunctor (X := X))
  let hTypes : IsColimit (K.map (forget TopCat)) :=
    Types.isColimitOfMulticoequalizerDiagram h
  let desc (E : Multicofork (h.multispanIndex.map (subsetFunctor (X := X)))) :
      K.pt ⟶ E.pt := TopCat.ofHom
    { toFun := hTypes.desc (E.map (forget TopCat))
      continuous_toFun := by
        apply continuous_of_cover U
          (fun i => (le_iSup U i).trans h.iSup_eq.le)
          (fun x hx => by
            rw [← h.iSup_eq, Set.iSup_eq_iUnion] at hx
            exact Set.mem_iUnion.mp hx) hclosed
        intro i
        have he := hTypes.fac (E.map (forget TopCat)) (WalkingMultispan.right i)
        have he' : (fun x : U i =>
            hTypes.desc (E.map (forget TopCat))
              ⟨x.val, ((le_iSup U i).trans h.iSup_eq.le) x.property⟩) = E.π i := by
          funext x
          exact congrArg (fun f => f x) he
        rw [he']
        exact (E.π i).hom.continuous }
  refine Multicofork.IsColimit.mk K desc ?_ ?_
  · intro E i
    apply (forget TopCat).map_injective
    exact hTypes.fac (E.map (forget TopCat)) (WalkingMultispan.right i)
  · intro E m hm
    apply (forget TopCat).map_injective
    apply Multicofork.IsColimit.hom_ext hTypes
    intro i
    exact ((forget TopCat).congr_map (hm i)).trans
      (hTypes.fac (E.map (forget TopCat)) (WalkingMultispan.right i)).symm

/-- Ambient closedness is sufficient for the relative-closed cover theorem. -/
def isColimit_of_isClosed (h : CompleteLattice.MulticoequalizerDiagram A U V)
    (hclosed : ∀ i, IsClosed (U i)) :
    IsColimit (h.multicofork.map subsetFunctor) :=
  isColimit h (fun i => (hclosed i).preimage continuous_subtype_val)

/-- The same actual colimit, retaining only pairwise intersections indexed by i < j. -/
def isColimit' [LinearOrder I]
    (h : CompleteLattice.MulticoequalizerDiagram A U V)
    (hclosed : ∀ i, IsClosed (Subtype.val ⁻¹' U i : Set A)) :
    IsColimit (h.multicofork.toLinearOrder.map subsetFunctor) :=
  Multicofork.isColimitToLinearOrder _ (isColimit h hclosed)
    { iso i j := subsetFunctor.mapIso (eqToIso (by
        dsimp
        rw [h.eq_inf, h.eq_inf, inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

end Sharpness.FiniteClosedCover
