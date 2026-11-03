import Sharpness.MackeyCategory
import Sharpness.MackeyCovariant

/-! Forgetful functors from the actual full Mackey category to both
native coefficient categories. Full Mackey isomorphisms therefore give
actual contravariant and covariant natural isomorphisms. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {R : Type u} [CommRing R]

def coefficientFunctor : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape ⥤ CoefficientCategory R F.Orbit where
  obj := F.coefficient
  map f :=
    { app P := ModuleCat.ofHom (f.app P.unop)
      naturality {P Q} t := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact f.pull_comm t.unop x }
  map_id M := by
    apply NatTrans.ext
    funext P
    apply ModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext P
    apply ModuleCat.hom_ext
    rfl

def covariantFunctor : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape ⥤ (F.Orbit ⥤ ModuleCat.{u} R) where
  obj M := M.covariant
  map f :=
    { app P := ModuleCat.ofHom (f.app P)
      naturality {P Q} t := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact f.push_comm t x }
  map_id M := by
    apply NatTrans.ext
    funext P
    apply ModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext P
    apply ModuleCat.hom_ext
    rfl

end Sharpness.FusionSystem
