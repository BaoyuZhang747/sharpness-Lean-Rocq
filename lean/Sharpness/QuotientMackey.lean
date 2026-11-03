import Sharpness.QuotientSpanOperators
import Sharpness.QuotientDoubleCosets
import Sharpness.RawMackey

/-! The full quotient Mackey identity. Every double-coset summand is
compared through actual group projections and apex isomorphisms, then the
original full Mackey identity is applied. No quotient identity is assumed. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators
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

local instance originalTermFintype : Fintype (F.RawDoubleCosetTerm f g) :=
  F.rawDoubleCosetTermFintype f g

local instance projectedTermFintype :
    Fintype (I.system.RawDoubleCosetTerm (F.projectedFusionHom hZ p hS sat I f)
      (F.projectedFusionHom hZ p hS sat I g)) :=
  I.system.rawDoubleCosetTermFintype _ _

theorem quotientFunctorData_doubleCosetOperator_projected (i : F.RawDoubleCosetTerm f g) :
    I.system.functorDataDoubleCosetOperator (F.quotientFunctorData hZ p hS sat I M label hZQ)
      (F.projectedFusionHom hZ p hS sat I f) (F.projectedFusionHom hZ p hS sat I g)
      (F.projectedDoubleCosetEquiv hZ p hS sat I f g i) = F.rawDoubleCosetOperator f g M i := by
  refine Quotient.inductionOn i fun u => ?_
  exact F.quotientFunctorData_spanOperator_projected hZ p hS sat I M label hZQ f g u

theorem quotientFunctorData_raw_identity_projected :
    ((F.quotientFunctorData hZ p hS sat I M label hZQ).pull
      (I.system.toOrbit.map (F.projectedFusionHom hZ p hS sat I f))).comp
      ((F.quotientFunctorData hZ p hS sat I M label hZQ).push
        (I.system.toOrbit.map (F.projectedFusionHom hZ p hS sat I g))) =
      ∑ i : I.system.RawDoubleCosetTerm (F.projectedFusionHom hZ p hS sat I f)
          (F.projectedFusionHom hZ p hS sat I g),
        I.system.functorDataDoubleCosetOperator (F.quotientFunctorData hZ p hS sat I M label hZQ)
          (F.projectedFusionHom hZ p hS sat I f) (F.projectedFusionHom hZ p hS sat I g) i := by
  have hpull := (congrArg (F.quotientPull hZ p hS sat I M)
      (F.rawQuotientOrbitMap_projected hZ p hS sat I f)).symm.trans
    (F.quotientPull_raw hZ p hS sat I M label hZQ f)
  have hpush := (congrArg (F.quotientPush hZ p hS sat I M)
      (F.rawQuotientOrbitMap_projected hZ p hS sat I g)).symm.trans
    (F.quotientPush_raw hZ p hS sat I M label hZQ g)
  have hcomp := congrArg₂ (fun a b => a.comp b) hpull hpush
  have hsum : (∑ i : I.system.RawDoubleCosetTerm (F.projectedFusionHom hZ p hS sat I f)
        (F.projectedFusionHom hZ p hS sat I g),
      I.system.functorDataDoubleCosetOperator (F.quotientFunctorData hZ p hS sat I M label hZQ)
        (F.projectedFusionHom hZ p hS sat I f) (F.projectedFusionHom hZ p hS sat I g) i) =
      ∑ i : F.RawDoubleCosetTerm f g, F.rawDoubleCosetOperator f g M i := by
    calc
      _ = ∑ i : F.RawDoubleCosetTerm f g,
          I.system.functorDataDoubleCosetOperator (F.quotientFunctorData hZ p hS sat I M label hZQ)
            (F.projectedFusionHom hZ p hS sat I f) (F.projectedFusionHom hZ p hS sat I g)
            (F.projectedDoubleCosetEquiv hZ p hS sat I f g i) :=
        ((F.projectedDoubleCosetEquiv hZ p hS sat I f g).sum_comp _).symm
      _ = _ := Finset.sum_congr rfl (fun i _ =>
        F.quotientFunctorData_doubleCosetOperator_projected hZ p hS sat I M label hZQ f g i)
  exact hcomp.trans ((F.mackey_raw f g M).trans hsum.symm)

theorem quotientFunctorData_raw_identity {A B C : I.system.Object} (f : A ⟶ C) (g : B ⟶ C) :
    ((F.quotientFunctorData hZ p hS sat I M label hZQ).pull (I.system.toOrbit.map f)).comp
      ((F.quotientFunctorData hZ p hS sat I M label hZQ).push (I.system.toOrbit.map g)) =
      ∑ i : I.system.RawDoubleCosetTerm f g,
        I.system.functorDataDoubleCosetOperator (F.quotientFunctorData hZ p hS sat I M label hZQ) f g i := by
  let fP := F.quotientRawLift hZ p hS sat I f
  let gP := F.quotientRawLift hZ p hS sat I g
  have hf : F.projectedFusionHom hZ p hS sat I fP = f := by
    apply Subtype.ext
    exact F.quotientRawLift_map hZ p hS sat I f
  have hg : F.projectedFusionHom hZ p hS sat I gP = g := by
    apply Subtype.ext
    exact F.quotientRawLift_map hZ p hS sat I g
  have h := F.quotientFunctorData_raw_identity_projected hZ p hS sat I M label hZQ fP gP
  have hc := congrArg₂ (fun (ff : A ⟶ C) (gg : B ⟶ C) =>
    ((F.quotientFunctorData hZ p hS sat I M label hZQ).pull (I.system.toOrbit.map ff)).comp
      ((F.quotientFunctorData hZ p hS sat I M label hZQ).push (I.system.toOrbit.map gg))) hf hg
  have hs := congrArg₂ (fun (ff : A ⟶ C) (gg : B ⟶ C) =>
    ∑ i : I.system.RawDoubleCosetTerm ff gg,
      I.system.functorDataDoubleCosetOperator (F.quotientFunctorData hZ p hS sat I M label hZQ) ff gg i) hf hg
  exact hc.symm.trans (h.trans hs)

def quotientMackey : MackeyModule.{u,u,u} k I.system.Orbit I.system.mackeyShape :=
  I.system.fullMackeyOfRawIdentity (F.quotientFunctorData hZ p hS sat I M label hZQ)
    (F.quotientFunctorData_raw_identity hZ p hS sat I M label hZQ)

def quotientMackeyCoefficientIso :
    I.system.coefficient (F.quotientMackey hZ p hS sat I M label hZQ) ≅
      F.quotientContravariant hZ p hS sat I M label hZQ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end Sharpness.FusionSystem
