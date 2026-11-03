import Sharpness.MackeyFunctorData
import Sharpness.QuotientIsoLaw
import Sharpness.QuotientComparison

/-! The proved two quotient functor structures and inverse-isomorphism
law, packaged without assuming a quotient Mackey formula. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)
    {k : Type u} [Field k] [CharP k p]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (hZQ : Z ≤ label.Q.as.subgroup)

def quotientFunctorData : MackeyFunctorData.{u,u} k I.system.Orbit where
  Value P := M.Value (F.toOrbit.obj ⟨F.quotientPreimage Z P.as.subgroup⟩)
  valueAddCommGroup P := M.valueAddCommGroup _
  valueModule P := M.valueModule _
  pull := F.quotientPull hZ p hS sat I M
  push := F.quotientPush hZ p hS sat I M
  pull_id P := (F.quotient_maps_id hZ p hS sat I M label hZQ P).1
  push_id P := (F.quotient_maps_id hZ p hS sat I M label hZQ P).2
  pull_comp f g := (F.quotient_maps_comp hZ p hS sat I M label hZQ f g).1
  push_comp f g := (F.quotient_maps_comp hZ p hS sat I M label hZQ f g).2
  pull_iso f := by
    intro hf
    exact F.quotient_pull_iso hZ p hS sat I M label hZQ f

include label hZQ

theorem quotientPush_raw {A B : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩) :
    F.quotientPush hZ p hS sat I M (F.rawQuotientOrbitMap hZ p hS sat I f) =
      M.push (F.toOrbit.map f) :=
  (F.simple_maps_eq_of_same_quotientOrbit hZ p hS sat I M label hZQ _ f
    (F.quotientOrbitLift_map hZ p hS sat I _)).2

end Sharpness.FusionSystem
