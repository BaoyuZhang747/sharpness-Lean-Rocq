import Sharpness.QuotientSpanSquares
import Sharpness.QuotientFunctorData

/-! Each actual quotient Mackey summand equals the corresponding original
summand. The full Mackey formula is not used for the quotient functor data. -/
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
    {A B C : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩)
    (g : (⟨F.quotientPreimage Z B⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩)
    (u : F.quotientPreimage Z C)

theorem quotientFunctorData_spanOperator_projected :
    I.system.functorDataSpanOperator (F.quotientFunctorData hZ p hS sat I M label hZQ)
      (F.projectedFusionHom hZ p hS sat I f) (F.projectedFusionHom hZ p hS sat I g)
      (F.subgroupProjection Z C u) = F.rawSpanOperator f g M u := by
  have hl : F.rawQuotientOrbitMap hZ p hS sat I (F.spanQuotientLeft hZ p hS sat I f g u) =
      I.system.toOrbit.map (I.system.spanLeft (F.projectedFusionHom hZ p hS sat I f)
        (F.projectedFusionHom hZ p hS sat I g) (F.subgroupProjection Z C u)) :=
    (F.rawQuotientOrbitMap_projected hZ p hS sat I _).trans
      (congrArg (fun t => I.system.toOrbit.map t) (F.projected_spanQuotientLeft hZ p hS sat I f g u))
  have hr : F.rawQuotientOrbitMap hZ p hS sat I (F.spanQuotientRight hZ p hS sat I f g u) =
      I.system.toOrbit.map (I.system.concreteSpan (F.projectedFusionHom hZ p hS sat I f)
        (F.projectedFusionHom hZ p hS sat I g) (F.subgroupProjection Z C u)).right :=
    (F.rawQuotientOrbitMap_projected hZ p hS sat I _).trans
      (congrArg (fun t => I.system.toOrbit.map t) (F.projected_spanQuotientRight hZ p hS sat I f g u))
  change (F.quotientPush hZ p hS sat I M (I.system.toOrbit.map
      (I.system.spanLeft (F.projectedFusionHom hZ p hS sat I f)
        (F.projectedFusionHom hZ p hS sat I g) (F.subgroupProjection Z C u)))).comp
      (F.quotientPull hZ p hS sat I M (I.system.toOrbit.map
        (I.system.concreteSpan (F.projectedFusionHom hZ p hS sat I f)
          (F.projectedFusionHom hZ p hS sat I g) (F.subgroupProjection Z C u)).right)) = _
  have hpush := (congrArg (F.quotientPush hZ p hS sat I M) hl).symm.trans
    (F.quotientPush_raw hZ p hS sat I M label hZQ _)
  have hpull := (congrArg (F.quotientPull hZ p hS sat I M) hr).symm.trans
    (F.quotientPull_raw hZ p hS sat I M label hZQ _)
  have hcomp := congrArg₂ (fun a b => a.comp b) hpush hpull
  let e := F.spanQuotientPreimageIso hZ p hS sat I f g u
  let t : MackeySpan F.Orbit (F.toOrbit.obj ⟨F.quotientPreimage Z A⟩)
      (F.toOrbit.obj ⟨F.quotientPreimage Z B⟩) :=
    { apex := F.toOrbit.obj ⟨F.quotientPreimage Z (F.projectedSpanApex hZ p hS sat I f g u).subgroup⟩
      left := F.toOrbit.map (F.spanQuotientLeft hZ p hS sat I f g u)
      right := F.toOrbit.map (F.spanQuotientRight hZ p hS sat I f g u) }
  exact hcomp.trans (M.span_operator_of_iso t (F.concreteOrbitSpan f g u) (F.toOrbit.mapIso e.symm)
    (F.toOrbit.map_comp _ _) (F.toOrbit.map_comp _ _))

end Sharpness.FusionSystem
