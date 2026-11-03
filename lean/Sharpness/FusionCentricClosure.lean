import Sharpness.CentralSupport

/-! Closure of the actual centric collection under overgroups. This uses
the image of the smaller subgroup under each conjugating fusion map. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem centric_overgroup {P Q : Subgroup S} (hP : F.IsCentric P) (hPQ : P ≤ Q) :
    F.IsCentric Q := by
  intro R _ e he x hx
  let f : (⟨P⟩ : F.Object) ⟶ ⟨R⟩ :=
    F.inclusion hPQ ≫ (F.isoOfMulEquiv e he).hom
  let a := F.toOrbit.mapIso (F.imageIso f)
  have hL := hP (F.imageSubgroup f) le_top (F.groupEquivOfOrbitIso a)
    (F.groupEquivOfOrbitIso_allowed a)
  rw [inf_top_eq] at hL
  exact (F.image_le f) (hL ((Subgroup.centralizer_le (F.image_le f)) hx.1))

end Sharpness.FusionSystem
