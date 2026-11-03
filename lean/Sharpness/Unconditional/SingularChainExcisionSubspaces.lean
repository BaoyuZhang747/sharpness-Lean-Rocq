import Sharpness.Unconditional.SingularChainExcisionSubcomplex

/-! Actual singular simplices in subspaces, their intersection, and the
two-open-set small subcomplex. No topological excision is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularChainExcision
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open Sharpness.RealizationUnitHomology

variable (X : TopCat.{u})

def singularInSubcomplex (U : Set X) : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | ∀ t, X.toSSetObjEquiv n σ t ∈ U}
  map f _ hσ t := hσ (_root_.stdSimplex.map f.unop t)

theorem singularInSubcomplex_inf (U V : Set X) :
    singularInSubcomplex X (U ∩ V) = singularInSubcomplex X U ⊓ singularInSubcomplex X V := by
  apply Subfunctor.ext
  funext n
  apply Set.ext
  intro σ
  change (∀ t, _ ∈ U ∩ V) ↔ (∀ t, _ ∈ U) ∧ (∀ t, _ ∈ V)
  exact forall_and

theorem singularInSubcomplex_sup (U V : Set X) :
    singularInSubcomplex X U ⊔ singularInSubcomplex X V =
      singularSmallSubcomplex X (fun b : Bool => if b then U else V) := by
  apply Subfunctor.ext
  funext n
  apply Set.ext
  intro σ
  change (∀ t, X.toSSetObjEquiv n σ t ∈ U) ∨ (∀ t, X.toSSetObjEquiv n σ t ∈ V) ↔ _
  constructor
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inr hb
    · exact Or.inl hb

def subsetInclusion (U : Set X) : TopCat.of U ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def subsetMap {U V : Set X} (h : U ⊆ V) : TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩

theorem singularInSubcomplex_mono {U V : Set X} (h : U ⊆ V) :
    singularInSubcomplex X U ≤ singularInSubcomplex X V := fun _ _ hσ t => h (hσ t)

def singularSubsetMap (U : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ⟶ (singularInSubcomplex X U).toSSet :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (subsetInclusion X U)) (by
    rintro n _ ⟨σ, rfl⟩ t
    exact ((TopCat.of U).toSSetObjEquiv n σ t).property)

theorem singularSubsetMap_isIso (U : Set X) : IsIso (singularSubsetMap X U) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  constructor
  · intro σ τ h
    apply ((TopCat.of U).toSSetObjEquiv n).injective
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    exact congrArg (fun q : (singularInSubcomplex X U).obj n => X.toSSetObjEquiv n q.val t) h
  · rintro ⟨σ, hσ⟩
    let f : C(_root_.stdSimplex ℝ (Fin (n.unop.len + 1)), U) :=
      ⟨fun t => ⟨X.toSSetObjEquiv n σ t, hσ t⟩,
        (X.toSSetObjEquiv n σ).continuous.subtype_mk _⟩
    refine ⟨((TopCat.of U).toSSetObjEquiv n).symm f, ?_⟩
    apply Subtype.ext
    apply (X.toSSetObjEquiv n).injective
    apply ContinuousMap.ext
    intro t
    rfl

def singularSubsetIso (U : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ≅ (singularInSubcomplex X U).toSSet := by
  letI := singularSubsetMap_isIso X U
  exact asIso (singularSubsetMap X U)

theorem singularSubsetIso_hom_inclusion (U : Set X) :
    (singularSubsetIso X U).hom ≫ (singularInSubcomplex X U).ι =
      TopCat.toSSet.map (subsetInclusion X U) := rfl

theorem singularSubsetIso_naturality {U V : Set X} (h : U ⊆ V) :
    TopCat.toSSet.map (subsetMap X h) ≫ (singularSubsetIso X V).hom =
      (singularSubsetIso X U).hom ≫
        SSet.Subcomplex.homOfLE (singularInSubcomplex_mono X h) := by
  apply (cancel_mono (singularInSubcomplex X V).ι).mp
  rw [Category.assoc, singularSubsetIso_hom_inclusion,
    Category.assoc, SSet.Subcomplex.homOfLE_ι, singularSubsetIso_hom_inclusion,
    ← TopCat.toSSet.map_comp]
  rfl

def singularSubsetChainsIso (R : Type u) [CommRing R] (U : Set X) :
    ((SingularCohomology.chainsFunctor R).obj (TopCat.of U)) ≅
      (singularInSubcomplex X U).toSSet.chainComplex (ModuleCat.of R R) :=
  (chains R).mapIso (singularSubsetIso X U)

theorem singularSubsetChainsIso_hom_inclusion (R : Type u) [CommRing R] (U : Set X) :
    (singularSubsetChainsIso X R U).hom ≫
        SSet.chainComplexMap (singularInSubcomplex X U).ι (ModuleCat.of R R) =
      (SingularCohomology.chainsFunctor R).map (subsetInclusion X U) :=
  ((chains R).map_comp _ _).symm

theorem singularSubsetChainsIso_naturality (R : Type u) [CommRing R]
    {U V : Set X} (h : U ⊆ V) :
    (SingularCohomology.chainsFunctor R).map (subsetMap X h) ≫
        (singularSubsetChainsIso X R V).hom =
      (singularSubsetChainsIso X R U).hom ≫
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE (singularInSubcomplex_mono X h))
          (ModuleCat.of R R) := by
  exact ((chains R).map_comp _ _).symm.trans
    ((congrArg (chains R).map (singularSubsetIso_naturality X h)).trans
      ((chains R).map_comp _ _))

instance subsetChainsMap_mono (R : Type u) [CommRing R] {U V : Set X} (h : U ⊆ V) :
    Mono ((SingularCohomology.chainsFunctor R).map (subsetMap X h)) := by
  haveI : Mono ((SingularCohomology.chainsFunctor R).map (subsetMap X h) ≫
      (singularSubsetChainsIso X R V).hom) := by
    rw [singularSubsetChainsIso_naturality]
    infer_instance
  exact mono_of_mono _ (singularSubsetChainsIso X R V).hom

end Sharpness.SingularChainExcision
