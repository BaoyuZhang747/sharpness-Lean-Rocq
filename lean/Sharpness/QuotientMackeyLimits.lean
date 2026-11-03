import Sharpness.QuotientMackey
import Sharpness.QuotientActualCollection

/-! The actual full quotient coefficients in the central comparison.
The isomorphisms are native natural isomorphisms of ModuleCat-valued
functors. Transfer of Ext along the category equivalences remains separate. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)
    {k : Type u} [Field k] [CharP k p]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (hZQ : Z ≤ label.Q.as.subgroup)

def quotientMackeyCentricCoefficientIso :
    I.system.centricCoefficient (F.quotientMackey hZ p hS sat I M label hZQ) ≅
      I.system.centricInclusion.op ⋙ F.quotientContravariant hZ p hS sat I M label hZQ :=
  Functor.isoWhiskerLeft I.system.centricInclusion.op
    (F.quotientMackeyCoefficientIso hZ p hS sat I M label hZQ)

theorem quotientCoefficient_acyclic_of_sharp
    [EnoughProjectives (CoefficientCategory k I.system.CentricOrbit)]
    (sharp : I.system.Sharp (R := k)) :
    Acyclic (I.system.centricInclusion.op ⋙ F.quotientContravariant hZ p hS sat I M label hZQ) :=
  acyclic_of_iso (F.quotientMackeyCentricCoefficientIso hZ p hS sat I M label hZQ).symm
    (sharp (F.quotientMackey hZ p hS sat I M label hZQ))

def quotientMackeyLiftCentricCoefficientIso :
    (F.quotientCentricFunctor hZ p hS sat I).op ⋙
        I.system.centricCoefficient (F.quotientMackey hZ p hS sat I M label hZQ) ≅
      (F.quotientLiftToCollection hZ p hS sat I).op ⋙
        (F.quotientComparisonCollection p hS sat hZ I).toCentric.op ⋙ F.centricCoefficient M := by
  let j := ObjectProperty.ι (fun A : F.QuotientLiftOrbit (Z := Z) => I.system.IsCentric A.as)
  let e₀ : (F.quotientCentricFunctor hZ p hS sat I).op ⋙
        I.system.centricCoefficient (F.quotientMackey hZ p hS sat I M label hZQ) ≅
      j.op ⋙ ((F.quotientOrbitFunctor hZ p hS sat I).op ⋙
        F.quotientContravariant hZ p hS sat I M label hZQ) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  let e₂ : j.op ⋙ ((F.quotientSourceInclusion (Z := Z)).op ⋙ F.coefficient M) ≅
      (F.quotientLiftToCollection hZ p hS sat I).op ⋙
        (F.quotientComparisonCollection p hS sat hZ I).toCentric.op ⋙ F.centricCoefficient M :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  exact e₀ ≪≫ Functor.isoWhiskerLeft j.op (F.quotientCoefficientComparison hZ p hS sat I M label hZQ) ≪≫ e₂

end Sharpness.FusionSystem
