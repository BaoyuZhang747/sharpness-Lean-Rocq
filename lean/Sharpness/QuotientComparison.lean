import Sharpness.QuotientCoefficients

/-! The source orbit category embeds in O(F), and the descended native
contravariant coefficient has an actual comparison isomorphism. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

def quotientSourceRawInclusion : F.QuotientLiftCategory (Z := Z) ⥤ F.Object :=
  inducedFunctor (fun A : Subgroup (S ⧸ Z) => (⟨F.quotientPreimage Z A⟩ : F.Object))

def quotientSourceInclusion : F.QuotientLiftOrbit (Z := Z) ⥤ F.Orbit :=
  CategoryTheory.Quotient.lift (F.quotientLiftInner (Z := Z))
    (F.quotientSourceRawInclusion (Z := Z) ⋙ F.toOrbit)
    (fun _ _ f g h => (F.orbit_map_eq_iff f.hom g.hom).mpr h)

instance quotientSourceInclusion_full : (F.quotientSourceInclusion (Z := Z)).Full where
  map_surjective := by
    rintro ⟨A⟩ ⟨B⟩ f
    obtain ⟨g, rfl⟩ := F.toOrbit.map_surjective f
    exact ⟨(CategoryTheory.Quotient.functor (F.quotientLiftInner (Z := Z))).map
      (InducedCategory.homMk g), rfl⟩

instance quotientSourceInclusion_faithful : (F.quotientSourceInclusion (Z := Z)).Faithful where
  map_injective := by
    rintro ⟨A⟩ ⟨B⟩ f g h
    obtain ⟨f', rfl⟩ := (CategoryTheory.Quotient.functor
      (F.quotientLiftInner (Z := Z))).map_surjective f
    obtain ⟨g', rfl⟩ := (CategoryTheory.Quotient.functor
      (F.quotientLiftInner (Z := Z))).map_surjective g
    exact (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).mpr
      ((F.orbit_map_eq_iff f'.hom g'.hom).mp h)

variable {k : Type u} [Field k] [CharP k p]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (hZQ : Z ≤ label.Q.as.subgroup)

include label hZQ

theorem quotientPull_raw {A B : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩) :
    F.quotientPull hZ p hS sat I M (F.rawQuotientOrbitMap hZ p hS sat I f) =
      M.pull (F.toOrbit.map f) := by
  exact (F.simple_maps_eq_of_same_quotientOrbit hZ p hS sat I M label hZQ _ f
    (F.quotientOrbitLift_map hZ p hS sat I _)).1

def quotientCoefficientComparison :
    (F.quotientOrbitFunctor hZ p hS sat I).op ⋙
        F.quotientContravariant hZ p hS sat I M label hZQ ≅
      (F.quotientSourceInclusion (Z := Z)).op ⋙ F.coefficient M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    simp only [Functor.comp_map, Functor.op_map, Iso.refl_hom,
      Category.id_comp, Category.comp_id]
    apply ModuleCat.hom_ext
    obtain ⟨g, hg⟩ := (CategoryTheory.Quotient.functor
      (F.quotientLiftInner (Z := Z))).map_surjective f.unop
    change F.quotientPull hZ p hS sat I M
      ((F.quotientOrbitFunctor hZ p hS sat I).map f.unop) =
        M.pull ((F.quotientSourceInclusion (Z := Z)).map f.unop)
    rw [← hg]
    exact F.quotientPull_raw hZ p hS sat I M label hZQ g.hom)

end Sharpness.FusionSystem
