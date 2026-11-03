import Sharpness.Unconditional.RealizationSeparationSequential
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Closed embeddings and T1 separation for actual topological coproducts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v w

namespace Sharpness.RealizationSeparation
open CategoryTheory CategoryTheory.Limits Topology Set

theorem sigma_map_isClosedEmbedding {I : Type u} {A B : I → TopCat.{u}}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, IsClosedEmbedding (f i)) :
    IsClosedEmbedding (@_root_.Sigma.map I I (fun i => A i) (fun i => B i)
      id (fun i => (f i : A i → B i))) := by
  refine ⟨(isEmbedding_sigmaMap Function.injective_id).mpr (fun i => (hf i).isEmbedding), ?_⟩
  change IsClosed (Set.range (fun x : Σ i, A i => (⟨x.1, f x.1 x.2⟩ : Σ i, B i)))
  rw [← Set.sigma_univ_range_eq (f := fun i => (f i : A i → B i))]
  apply isClosed_sigma_iff.mpr
  intro i
  rw [Set.mk_preimage_sigma (Set.mem_univ i)]
  exact (hf i).isClosed_range

theorem coproduct_map_isClosedEmbedding {I : Type u} {A B : I → TopCat.{u}}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, IsClosedEmbedding (f i)) :
    IsClosedEmbedding (Limits.Sigma.map f) := by
  let a := TopCat.homeoOfIso (TopCat.sigmaIsoSigma A)
  let b := TopCat.homeoOfIso (TopCat.sigmaIsoSigma B)
  have heq : (Limits.Sigma.map f : (∐ A : TopCat) → (∐ B : TopCat)) =
      b.symm ∘ _root_.Sigma.map id (fun i => (f i : A i → B i)) ∘ a := by
    apply funext
    intro x
    obtain ⟨⟨i, y⟩, rfl⟩ := a.symm.surjective x
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    change (Limits.Sigma.map f) ((TopCat.sigmaIsoSigma A).inv ⟨i, y⟩) =
      (TopCat.sigmaIsoSigma B).inv ⟨i, f i y⟩
    rw [TopCat.sigmaIsoSigma_inv_apply, TopCat.sigmaIsoSigma_inv_apply]
    exact ConcreteCategory.congr_hom (Limits.Sigma.ι_map f i) y
  rw [heq]
  exact b.symm.isClosedEmbedding.comp ((sigma_map_isClosedEmbedding f hf).comp a.isClosedEmbedding)

theorem coproduct_t1Space {I : Type u} (A : I → TopCat.{u})
    (hA : ∀ i, T1Space (A i)) : T1Space (∐ A : TopCat.{u}) := by
  letI := hA
  letI : T1Space (Σ i, A i) := ⟨fun ⟨i, x⟩ => by
    have h : IsClosed ((Sigma.mk i) '' ({x} : Set (A i)) : Set (Σ j, A j)) :=
      IsClosedEmbedding.sigmaMk.isClosedMap _ isClosed_singleton
    simpa only [Set.image_singleton] using h⟩
  exact (TopCat.homeoOfIso (TopCat.sigmaIsoSigma A)).isEmbedding.t1Space

theorem mapped_coproduct_isClosedEmbedding {C : Type v} [Category.{w} C]
    {I : Type u} {A B : I → C} [HasCoproduct A] [HasCoproduct B]
    (G : C ⥤ TopCat.{u})
    [PreservesColimit (Discrete.functor A) G] [PreservesColimit (Discrete.functor B) G]
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, IsClosedEmbedding (G.map (f i))) :
    IsClosedEmbedding (G.map (Limits.Sigma.map f)) := by
  let a := PreservesCoproduct.iso G A
  let b := PreservesCoproduct.iso G B
  have heq : G.map (Limits.Sigma.map f) =
      a.hom ≫ Limits.Sigma.map (fun i => G.map (f i)) ≫ b.inv := by
    apply (isColimitOfHasCoproductOfPreservesColimit G A).hom_ext
    rintro ⟨i⟩
    dsimp
    have ha : G.map (Limits.Sigma.ι A i) ≫ a.hom =
        Limits.Sigma.ι (fun j => G.obj (A j)) i :=
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (isColimitOfHasCoproductOfPreservesColimit G A) (colimit.isColimit _) (Discrete.mk i)
    have hb : Limits.Sigma.ι (fun j => G.obj (B j)) i ≫ b.inv =
        G.map (Limits.Sigma.ι B i) :=
      IsColimit.comp_coconePointUniqueUpToIso_inv
        (isColimitOfHasCoproductOfPreservesColimit G B) (colimit.isColimit _) (Discrete.mk i)
    rw [← Category.assoc, ← Category.assoc, ha, Limits.Sigma.ι_map, Category.assoc, hb]
    rw [← G.map_comp, ← G.map_comp, Limits.Sigma.ι_map]
  rw [heq]
  exact (TopCat.homeoOfIso b).symm.isClosedEmbedding.comp
    ((coproduct_map_isClosedEmbedding _ hf).comp (TopCat.homeoOfIso a).isClosedEmbedding)

theorem mapped_coproduct_t1Space {C : Type v} [Category.{w} C]
    {I : Type u} (A : I → C) [HasCoproduct A] (G : C ⥤ TopCat.{u})
    [PreservesColimit (Discrete.functor A) G] (hA : ∀ i, T1Space (G.obj (A i))) :
    T1Space (G.obj (∐ A)) := by
  letI := coproduct_t1Space (fun i => G.obj (A i)) hA
  exact (TopCat.homeoOfIso (PreservesCoproduct.iso G A)).isEmbedding.t1Space

end Sharpness.RealizationSeparation
