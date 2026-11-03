import Sharpness.SubsystemEmbedding
import Sharpness.MackeyFunctorData

/-! Pulling both actual coefficient functors through the subsystem orbit
functor. No Mackey identity for this restriction is assumed here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S) (T : Subgroup S)
    (H : FusionSystem T) (h : F.SubsystemEmbedding T H)
    {R : Type u} [Ring R] (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape)

def subsystemFunctorData : MackeyFunctorData.{u,u} R H.Orbit where
  Value P := M.Value ((F.subsystemOrbitFunctor T H h).obj P)
  valueAddCommGroup P := M.valueAddCommGroup _
  valueModule P := M.valueModule _
  pull f := M.pull ((F.subsystemOrbitFunctor T H h).map f)
  push f := M.push ((F.subsystemOrbitFunctor T H h).map f)
  pull_id P := (congrArg (fun f => M.pull f) ((F.subsystemOrbitFunctor T H h).map_id P)).trans
    (M.pull_id _)
  push_id P := (congrArg (fun f => M.push f) ((F.subsystemOrbitFunctor T H h).map_id P)).trans
    (M.push_id _)
  pull_comp f g := (congrArg (fun f => M.pull f) ((F.subsystemOrbitFunctor T H h).map_comp f g)).trans
    (M.pull_comp _ _)
  push_comp f g := (congrArg (fun f => M.push f) ((F.subsystemOrbitFunctor T H h).map_comp f g)).trans
    (M.push_comp _ _)
  pull_iso f := by
    intro hf
    let J := F.subsystemOrbitFunctor T H h
    letI : IsIso (J.map f) := (J.mapIso (asIso f)).isIso_hom
    exact (M.pull_iso (J.map f)).trans (congrArg (fun t => M.push t) (J.map_inv f).symm)

theorem subsystemFunctorData_pull_raw {P Q : H.Object} (f : P ⟶ Q) :
    (F.subsystemFunctorData T H h M).pull (H.toOrbit.map f) =
      M.pull (F.toOrbit.map ((F.subsystemRawFunctor T H h).map f)) := rfl

theorem subsystemFunctorData_push_raw {P Q : H.Object} (f : P ⟶ Q) :
    (F.subsystemFunctorData T H h M).push (H.toOrbit.map f) =
      M.push (F.toOrbit.map ((F.subsystemRawFunctor T H h).map f)) := rfl

end Sharpness.FusionSystem
