import Sharpness.RestrictedMackey
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Restricting scalars preserves the full and the restricted Mackey
identities. This constructs the coefficient object used with DP Theorem A. -/
set_option autoImplicit false
noncomputable section
universe u v w
namespace Sharpness
open CategoryTheory

namespace MackeyModule
variable {k : Type u} [CommRing k] (R : Type u) [CommRing R] [Algebra R k]
    {C : Type v} [Category.{v} C] {B : MackeyShape C} (M : MackeyModule.{u,v,w} k C B)

local instance valueRestrict (P : C) : Module R (M.Value P) := Module.restrictScalars R k _
local instance valueTower (P : C) : IsScalarTower R k (M.Value P) :=
  IsScalarTower.restrictScalars R k _

def restrictScalars : MackeyModule R C B where
  Value := M.Value
  valueAddCommGroup := M.valueAddCommGroup
  valueModule P := valueRestrict R M P
  pull f := (M.pull f).restrictScalars R
  push f := (M.push f).restrictScalars R
  pull_id P := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.pull_id P) x
  push_id P := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.push_id P) x
  pull_comp f g := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.pull_comp f g) x
  push_comp f g := by apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.push_comp f g) x
  pull_iso f := by intro hf; apply LinearMap.ext; intro x; exact LinearMap.congr_fun (M.pull_iso f) x
  mackey f g := by
    apply LinearMap.ext
    intro x
    have h := LinearMap.congr_fun (M.mackey f g) x
    simpa only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.restrictScalars_apply] using h

end MackeyModule

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k R : Type u} [CommRing k] [CommRing R] [Algebra R k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)

def centricRestrictScalarsIso :
    F.centricCoefficient (M.restrictScalars R) ≅
      F.centricCoefficient M ⋙ ModuleCat.restrictScalars (algebraMap R k) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end FusionSystem
end Sharpness
