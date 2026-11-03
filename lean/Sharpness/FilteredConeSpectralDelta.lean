import Sharpness.HomologicalSpectralObject
import Sharpness.MappingConeCokernelDelta
import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject

/-! The connecting maps of the actual filtered mapping-cone spectral
object are the actual composition-triangle connecting maps, and hence
the short-exact-sequence connecting maps after cokernel comparison. -/
set_option autoImplicit false
noncomputable section
universe u v t
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
attribute [-simp] Fin.reduceFinMk
variable {R : Type u} [CommRing R] {J : Type t} [Category.{v} J]
    (I : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ)

def filteredConeSpectralObject : Abelian.SpectralObject (ModuleCat.{u} R) J :=
  homologicalSpectralObject
    ((HomotopyCategory.spectralObjectMappingCone (ModuleCat.{u} R)).precomp I)
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0)

variable {a b c : J} (f : a ⟶ b) (g : b ⟶ c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem filteredConeSpectralObject_delta (n n' : ℤ) (hn : n+1 = n') :
    (filteredConeSpectralObject I).δ f g n n' hn =
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh (I.map f) (I.map g)) n n' hn := by
  dsimp only [filteredConeSpectralObject, Abelian.SpectralObject.δ,
    homologicalSpectralObject, Functor.homologySequenceδ]
  congr 1
  dsimp [Triangulated.SpectralObject.ω₂, Triangulated.SpectralObject.precomp,
    Pretriangulated.Triangle.functorMk, Functor.mapTriangle, ComposableArrows.isoMk₁,
    HomotopyCategory.spectralObjectMappingCone, HomotopyCategory.composableArrowsFunctor,
    Functor.mapComposableArrowsObjMk₁Iso, CochainComplex.mappingConeCompTriangleh,
    Functor.mapComposableArrows, ComposableArrows.homMk₁, ComposableArrows.homMk,
    ComposableArrows.functorArrows, ComposableArrows.mk₁, ComposableArrows.mk₂,
    ComposableArrows.precomp, ComposableArrows.Precomp.obj, ComposableArrows.Precomp.map,
    ComposableArrows.Mk₁.map, ComposableArrows.Mk₁.obj, Functor.whiskeringRight, Functor.whiskeringLeft]
  erw [CochainComplex.mappingCone.map_id (I.map g), CochainComplex.mappingCone.map_id (I.map f)]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem filteredConeSpectralObject_delta_cokernel [Mono (I.map f)] [Mono (I.map g)]
    (n n' : ℤ) (hn : n+1 = n') :
    (filteredConeSpectralObject I).δ f g n n' hn ≫ (homotopyConeCokernelIso (I.map f) n').hom =
      (homotopyConeCokernelIso (I.map g) n).hom ≫
        (monoCokernelShortComplex_shortExact (I.map g)).δ n n' hn ≫
          HomologicalComplex.homologyMap (cokernel.π (I.map f)) n' :=
  (congrArg (fun t => t ≫ (homotopyConeCokernelIso (I.map f) n').hom)
    (filteredConeSpectralObject_delta I f g n n' hn)).trans
      (mappingConeComp_delta_cokernel (I.map f) (I.map g) n n' hn)

attribute [simp] Fin.reduceFinMk
end Sharpness
