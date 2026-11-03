import Sharpness.ExtensionDegreeLifts
import Sharpness.ExtensionCokernelClasses

/-! Extend the actual two lifts for a connecting map and preserve
their quotient cycle class under the canonical cokernel comparison. -/
set_option autoImplicit false
noncomputable section
universe u t t'
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c')
    {A B : HomologicalComplex (ModuleCat.{u} R) c} (f : A ⟶ B)

theorem extensionConnectingLift_relation {M : ModuleCat.{u} R}
    (i j : ι) (i' j' : ι') (hi : e.f i=i') (hj : e.f j=j')
    (x₂ : M ⟶ B.X i) (x₁ : M ⟶ A.X j)
    (hx : x₁ ≫ f.f j = x₂ ≫ B.d i j) :
    extensionDegreeLift e A j j' hj x₁ ≫ (HomologicalComplex.extendMap f e).f j' =
      extensionDegreeLift e B i i' hi x₂ ≫ (B.extend e).d i' j' := by
  calc
    _ = extensionDegreeLift e B j j' hj (x₁ ≫ f.f j) := extensionDegreeLift_map e A f j j' hj x₁
    _ = extensionDegreeLift e B j j' hj (x₂ ≫ B.d i j) :=
      congrArg (fun t => extensionDegreeLift e B j j' hj t) hx
    _ = _ := (extensionDegreeLift_d e B i j i' j' hi hj x₂).symm

set_option backward.isDefEq.respectTransparency false in
theorem extensionCokernelCycleClass_comparison {M : ModuleCat.{u} R}
    (i j : ι) (i' j' : ι') (hi : e.f i=i') (hj : e.f j=j')
    (hnext : c.next i=j) (hnext' : c'.next i'=j') (x₂ : M ⟶ B.X i)
    (hx : (x₂ ≫ (cokernel.π f).f i) ≫ (cokernel f).d i j = 0)
    (hx' : (extensionDegreeLift e B i i' hi x₂ ≫
        (cokernel.π (HomologicalComplex.extendMap f e)).f i') ≫
          (cokernel (HomologicalComplex.extendMap f e)).d i' j' = 0) :
    ((cokernel (HomologicalComplex.extendMap f e)).liftCycles
          (extensionDegreeLift e B i i' hi x₂ ≫ (cokernel.π (HomologicalComplex.extendMap f e)).f i')
          j' hnext' hx' ≫ (cokernel (HomologicalComplex.extendMap f e)).homologyπ i') ≫
      HomologicalComplex.homologyMap (extensionCokernelIso e f).hom i' ≫
        ((cokernel f).extendHomologyIso e hi).hom =
    (cokernel f).liftCycles (x₂ ≫ (cokernel.π f).f i) j hnext hx ≫ (cokernel f).homologyπ i := by
  have hxy : (extensionDegreeLift e B i i' hi x₂ ≫
      (cokernel.π (HomologicalComplex.extendMap f e)).f i') ≫
        (extensionCokernelIso e f).hom.f i' ≫ ((cokernel f).extendXIso e hi).hom =
      x₂ ≫ (cokernel.π f).f i := by
    calc
      _ = extensionDegreeLift e B i i' hi x₂ ≫ (B.extendXIso e hi).hom ≫ (cokernel.π f).f i := by
        simpa only [Category.assoc] using congrArg (fun t => extensionDegreeLift e B i i' hi x₂ ≫ t)
          (extensionCokernelIso_projection_component e f i i' hi)
      _ = _ := by simp only [extensionDegreeLift, Category.assoc, Iso.inv_hom_id_assoc]
  exact extendCycleClass_comparison e (cokernel (HomologicalComplex.extendMap f e)) (cokernel f)
    (extensionCokernelIso e f).hom i j i' j' hi hnext hnext'
      _ hx' _ hx hxy

end Sharpness
