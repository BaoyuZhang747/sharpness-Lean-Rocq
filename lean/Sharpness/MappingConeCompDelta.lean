import Sharpness.MonoMappingConeCokernel
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! The connecting map in the mapping-cone composition triangle
factors through the standard cone triangle. This supplies the actual
connecting map used by the filtered-complex first differential. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    {A B C : CochainComplex (ModuleCat.{u} R) ℤ} (f : A ⟶ B) (g : B ⟶ C)

set_option backward.isDefEq.respectTransparency false in
def mappingConeCompTriangleFromStandard :
    CochainComplex.mappingCone.triangle g ⟶ CochainComplex.mappingConeCompTriangle f g where
  hom₁ := CochainComplex.mappingCone.inr f
  hom₂ := CochainComplex.mappingCone.inr (f ≫ g)
  hom₃ := 𝟙 _
  comm₁ := (CochainComplex.mappingCone.triangleMap f (f ≫ g) (𝟙 A) g
    (by rw [Category.id_comp])).comm₂.symm
  comm₂ := by
    calc
      _ = CochainComplex.mappingCone.inr g := Category.comp_id _
      _ = (𝟙 C) ≫ CochainComplex.mappingCone.inr g := (Category.id_comp _).symm
      _ = _ := (CochainComplex.mappingCone.triangleMap (f ≫ g) g f (𝟙 C)
        (by rw [Category.comp_id])).comm₂.symm
  comm₃ := (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
theorem mappingConeCompTriangle_delta (n n' : ℤ) (hn : n+1 = n') :
    (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh f g) n n' hn =
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingCone.triangleh g) n n' hn ≫
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n').map
        ((HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.inr f)) := by
  have h := Functor.homologySequenceδ_naturality
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0)
      (CochainComplex.mappingCone.triangleh g) (CochainComplex.mappingConeCompTriangleh f g)
      ((HomotopyCategory.quotient _ _).mapTriangle.map (mappingConeCompTriangleFromStandard f g))
      n n' hn
  have h' :
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
        ((HomotopyCategory.quotient _ _).map (𝟙 (CochainComplex.mappingCone g))) ≫
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh f g) n n' hn = _ := h
  have hid := congrArg
    (fun t => (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map t)
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_id
      (CochainComplex.mappingCone g))
  have hid' :
      (HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map
        ((HomotopyCategory.quotient _ _).map (𝟙 (CochainComplex.mappingCone g))) = 𝟙 _ :=
    hid.trans ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n).map_id _)
  exact (Category.id_comp _).symm.trans
    ((congrArg (fun t => t ≫ (HomotopyCategory.homologyFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh f g) n n' hn) hid').symm.trans h')

end Sharpness
