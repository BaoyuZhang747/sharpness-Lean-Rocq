import Sharpness.MappingConeCompDelta

/-! The native composition-triangle differential, under the actual
cone-to-cokernel comparison, is the short-exact-sequence connecting
map followed by projection to the next cokernel. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    {A B C : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) (g : B ⟶ C)

def homotopyConeCokernelIso [Mono f] (n : ℤ) :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj
      ((HomotopyCategory.quotient _ _).obj (CochainComplex.mappingCone f)) ≅
        (cokernel f).homology n :=
  (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) n).app _ ≪≫
    monoMappingConeCokernelCohomologyIso f n

set_option backward.isDefEq.respectTransparency false in
theorem mappingConeComp_delta_cokernel [Mono f] [Mono g] (n n' : ℤ) (hn : n+1 = n') :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh f g) n n' hn ≫
      (homotopyConeCokernelIso f n').hom =
    (homotopyConeCokernelIso g n).hom ≫
      (monoCokernelShortComplex_shortExact g).δ n n' hn ≫
        HomologicalComplex.homologyMap (cokernel.π f) n' := by
  let e := fun i : ℤ =>
    HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (ComplexShape.up ℤ) i
  have hnat :
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n').map
          ((HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.inr f)) ≫
        ((e n').app (CochainComplex.mappingCone f)).hom =
      ((e n').app B).hom ≫ HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n' :=
    (e n').hom.naturality (CochainComplex.mappingCone.inr f)
  have hi : HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) n' ≫
      HomologicalComplex.homologyMap (monoMappingConeToCokernel f) n' =
        HomologicalComplex.homologyMap (cokernel.π f) n' :=
    (HomologicalComplex.homologyMap_comp _ _ n').symm.trans
      (congrArg (fun t => HomologicalComplex.homologyMap t n') (monoMappingConeToCokernel_inr f))
  have htail :
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n').map
          ((HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.inr f)) ≫
        (((e n').app (CochainComplex.mappingCone f)).hom ≫
          HomologicalComplex.homologyMap (monoMappingConeToCokernel f) n') =
      ((e n').app B).hom ≫ HomologicalComplex.homologyMap (cokernel.π f) n' := by
    calc
      _ = ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n').map
          ((HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.inr f)) ≫
            ((e n').app (CochainComplex.mappingCone f)).hom) ≫
          HomologicalComplex.homologyMap (monoMappingConeToCokernel f) n' := (Category.assoc _ _ _).symm
      _ = (((e n').app B).hom ≫ HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr f) n') ≫
            HomologicalComplex.homologyMap (monoMappingConeToCokernel f) n' :=
        congrArg (fun t => t ≫ HomologicalComplex.homologyMap (monoMappingConeToCokernel f) n') hnat
      _ = _ := (Category.assoc _ _ _).trans (congrArg (fun t => ((e n').app B).hom ≫ t) hi)
  have hs := CochainComplex.mappingCone.homologySequenceδ_triangleh
    (monoCokernelShortComplex_shortExact g) n n' hn
  let d : (cokernel g).homology n ⟶ B.homology n' :=
    (monoCokernelShortComplex_shortExact g).δ n n' hn
  let s :
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj
          (CochainComplex.mappingCone g) ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n').obj B :=
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingCone.triangleh g) n n' hn
  let t :
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).obj
          (CochainComplex.mappingCone g) ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n').obj
          (CochainComplex.mappingCone f) :=
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).homologySequenceδ
      (CochainComplex.mappingConeCompTriangleh f g) n n' hn
  have hs' : s = ((e n).app (CochainComplex.mappingCone g)).hom ≫
      HomologicalComplex.homologyMap (monoMappingConeToCokernel g) n ≫ d ≫ ((e n').app B).inv := hs
  have ht : t = s ≫
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n').map
        ((HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.inr f)) :=
    mappingConeCompTriangle_delta f g n n' hn
  change t ≫ (((e n').app (CochainComplex.mappingCone f)).hom ≫
      HomologicalComplex.homologyMap (monoMappingConeToCokernel f) n') =
    (((e n).app (CochainComplex.mappingCone g)).hom ≫
      HomologicalComplex.homologyMap (monoMappingConeToCokernel g) n) ≫
        d ≫
          HomologicalComplex.homologyMap (cokernel.π f) n'
  rw [ht, Category.assoc, htail, hs']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_assoc]

end Sharpness
