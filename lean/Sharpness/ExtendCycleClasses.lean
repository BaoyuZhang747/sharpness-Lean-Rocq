import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! The native extension cohomology comparison preserves the class
of a specified cycle under an actual complex morphism. -/
set_option autoImplicit false
noncomputable section
universe u v t t'
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex C c') (L : HomologicalComplex C c)
    (φ : K ⟶ L.extend e)

set_option backward.isDefEq.respectTransparency false in
theorem extendCycleClass_comparison {M : C} (i k : ι) (i' k' : ι')
    (hi : e.f i = i') (hk : c.next i = k) (hk' : c'.next i' = k')
    (x : M ⟶ K.X i') (hx : x ≫ K.d i' k' = 0)
    (y : M ⟶ L.X i) (hy : y ≫ L.d i k = 0)
    (hxy : x ≫ φ.f i' ≫ (L.extendXIso e hi).hom = y) :
    (K.liftCycles x k' hk' hx ≫ K.homologyπ i') ≫
        HomologicalComplex.homologyMap φ i' ≫ (L.extendHomologyIso e hi).hom =
      L.liftCycles y k hk hy ≫ L.homologyπ i := by
  have hc : K.liftCycles x k' hk' hx ≫ HomologicalComplex.cyclesMap φ i' ≫
      (L.extendCyclesIso e hi).hom = L.liftCycles y k hk hy := by
    apply (cancel_mono (L.iCycles i)).mp
    simpa only [Category.assoc, HomologicalComplex.extendCyclesIso_hom_iCycles,
      HomologicalComplex.cyclesMap_i_assoc, HomologicalComplex.liftCycles_i_assoc,
      HomologicalComplex.liftCycles_i] using hxy
  calc
    _ = K.liftCycles x k' hk' hx ≫ HomologicalComplex.cyclesMap φ i' ≫
        (L.extend e).homologyπ i' ≫ (L.extendHomologyIso e hi).hom := by
      simp only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
    _ = (K.liftCycles x k' hk' hx ≫ HomologicalComplex.cyclesMap φ i' ≫
        (L.extendCyclesIso e hi).hom) ≫ L.homologyπ i := by
      simp only [Category.assoc, HomologicalComplex.homologyπ_extendHomologyIso_hom]
    _ = _ := congrArg (fun t => t ≫ L.homologyπ i) hc

end Sharpness
