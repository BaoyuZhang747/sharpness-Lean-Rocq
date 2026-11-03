import Sharpness.QuotientCoefficients

/-! The chosen lift of a quotient-orbit isomorphism is an actual fusion
isomorphism. This proves the two descended coefficient maps agree on
isomorphisms in the required inverse directions. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

def quotientOrbitLiftIso {A B : I.system.Orbit} (f : A ⟶ B) [IsIso f] :
    (⟨F.quotientPreimage Z A.as.subgroup⟩ : F.Object) ≅
      ⟨F.quotientPreimage Z B.as.subgroup⟩ :=
  F.isoOfEqualOrder (F.quotientOrbitLift hZ p hS sat I f)
    (le_antisymm (F.order_mono (F.quotientOrbitLift hZ p hS sat I f))
      (F.order_mono (F.quotientOrbitLift hZ p hS sat I (inv f))))

theorem quotientOrbitLiftIso_inv_map {A B : I.system.Orbit} (f : A ⟶ B) [IsIso f] :
    F.rawQuotientOrbitMap hZ p hS sat I (F.quotientOrbitLiftIso hZ p hS sat I f).inv = inv f := by
  let e := F.quotientOrbitLiftIso hZ p hS sat I f
  have he : F.rawQuotientOrbitMap hZ p hS sat I e.hom = f :=
    F.quotientOrbitLift_map hZ p hS sat I f
  apply IsIso.eq_inv_of_hom_inv_id (f := f)
  calc
    f ≫ F.rawQuotientOrbitMap hZ p hS sat I e.inv =
        F.rawQuotientOrbitMap hZ p hS sat I e.hom ≫
          F.rawQuotientOrbitMap hZ p hS sat I e.inv :=
      congrArg (fun t => t ≫ F.rawQuotientOrbitMap hZ p hS sat I e.inv) he.symm
    _ = F.rawQuotientOrbitMap hZ p hS sat I (e.hom ≫ e.inv) :=
      (F.rawQuotientOrbitMap_comp hZ p hS sat I _ _).symm
    _ = 𝟙 _ := by rw [e.hom_inv_id, F.rawQuotientOrbitMap_id]

variable {k : Type u} [Field k] [CharP k p]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (hZQ : Z ≤ label.Q.as.subgroup)

include label hZQ

theorem quotient_pull_iso {A B : I.system.Orbit} (f : A ⟶ B) [IsIso f] :
    F.quotientPull hZ p hS sat I M f = F.quotientPush hZ p hS sat I M (inv f) := by
  let e := F.quotientOrbitLiftIso hZ p hS sat I f
  have same : F.rawQuotientOrbitMap hZ p hS sat I e.inv =
      F.rawQuotientOrbitMap hZ p hS sat I (F.quotientOrbitLift hZ p hS sat I (inv f)) := by
    rw [F.quotientOrbitLiftIso_inv_map, F.quotientOrbitLift_map]
  have eqs := F.simple_maps_eq_of_same_quotientOrbit hZ p hS sat I M label hZQ _ _ same
  letI : IsIso (F.toOrbit.map e.hom) := (F.toOrbit.mapIso e).isIso_hom
  change M.pull (F.toOrbit.map e.hom) = _
  rw [M.pull_iso]
  have hi : inv (F.toOrbit.map e.hom) = F.toOrbit.map e.inv := by
    apply IsIso.inv_eq_of_hom_inv_id (f := F.toOrbit.map e.hom)
    rw [← F.toOrbit.map_comp, e.hom_inv_id, F.toOrbit.map_id]
  rw [hi]
  exact eqs.2

end Sharpness.FusionSystem
