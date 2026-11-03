import Sharpness.QuotientLifts

/-! The two actual coefficient functors on O(F/Z), with proved choice
independence and functor laws. The full Mackey identity is a separate step. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)
    {k : Type u} [Field k] [CharP k p]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (hZQ : Z ≤ label.Q.as.subgroup)

def quotientPull {A B : I.system.Orbit} (f : A ⟶ B) :
    M.Value (F.toOrbit.obj ⟨F.quotientPreimage Z B.as.subgroup⟩) →ₗ[k]
      M.Value (F.toOrbit.obj ⟨F.quotientPreimage Z A.as.subgroup⟩) :=
  M.pull (F.toOrbit.map (F.quotientOrbitLift hZ p hS sat I f))

def quotientPush {A B : I.system.Orbit} (f : A ⟶ B) :
    M.Value (F.toOrbit.obj ⟨F.quotientPreimage Z A.as.subgroup⟩) →ₗ[k]
      M.Value (F.toOrbit.obj ⟨F.quotientPreimage Z B.as.subgroup⟩) :=
  M.push (F.toOrbit.map (F.quotientOrbitLift hZ p hS sat I f))

include label hZQ

theorem quotient_maps_id (A : I.system.Orbit) :
    F.quotientPull hZ p hS sat I M (𝟙 A) = LinearMap.id ∧
      F.quotientPush hZ p hS sat I M (𝟙 A) = LinearMap.id := by
  have same : F.rawQuotientOrbitMap hZ p hS sat I (F.quotientOrbitLift hZ p hS sat I (𝟙 A)) =
      F.rawQuotientOrbitMap hZ p hS sat I (𝟙 (⟨F.quotientPreimage Z A.as.subgroup⟩ : F.Object)) := by
    rw [F.quotientOrbitLift_map, F.rawQuotientOrbitMap_id]
    rfl
  have h := F.simple_maps_eq_of_same_quotientOrbit hZ p hS sat I M label hZQ _ _ same
  simpa only [quotientPull, quotientPush, F.toOrbit.map_id, M.pull_id, M.push_id] using h

theorem quotient_maps_comp {A B C : I.system.Orbit} (f : A ⟶ B) (g : B ⟶ C) :
    F.quotientPull hZ p hS sat I M (f ≫ g) =
      (F.quotientPull hZ p hS sat I M f).comp (F.quotientPull hZ p hS sat I M g) ∧
    F.quotientPush hZ p hS sat I M (f ≫ g) =
      (F.quotientPush hZ p hS sat I M g).comp (F.quotientPush hZ p hS sat I M f) := by
  have same : F.rawQuotientOrbitMap hZ p hS sat I (F.quotientOrbitLift hZ p hS sat I (f ≫ g)) =
      F.rawQuotientOrbitMap hZ p hS sat I
        (F.quotientOrbitLift hZ p hS sat I f ≫ F.quotientOrbitLift hZ p hS sat I g) := by
    rw [F.quotientOrbitLift_map, F.rawQuotientOrbitMap_comp,
      F.quotientOrbitLift_map, F.quotientOrbitLift_map]
    rfl
  have h := F.simple_maps_eq_of_same_quotientOrbit hZ p hS sat I M label hZQ _ _ same
  simpa only [quotientPull, quotientPush, F.toOrbit.map_comp, M.pull_comp, M.push_comp] using h

def quotientContravariant : CoefficientCategory k I.system.Orbit where
  obj A := ModuleCat.of k (M.Value (F.toOrbit.obj ⟨F.quotientPreimage Z A.unop.as.subgroup⟩))
  map f := ModuleCat.ofHom (F.quotientPull hZ p hS sat I M f.unop)
  map_id A := by
    apply ModuleCat.hom_ext
    exact (F.quotient_maps_id hZ p hS sat I M label hZQ A.unop).1
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (F.quotient_maps_comp hZ p hS sat I M label hZQ g.unop f.unop).1

def quotientCovariant : I.system.Orbit ⥤ ModuleCat.{u} k where
  obj A := ModuleCat.of k (M.Value (F.toOrbit.obj ⟨F.quotientPreimage Z A.as.subgroup⟩))
  map f := ModuleCat.ofHom (F.quotientPush hZ p hS sat I M f)
  map_id A := by
    apply ModuleCat.hom_ext
    exact (F.quotient_maps_id hZ p hS sat I M label hZQ A).2
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact (F.quotient_maps_comp hZ p hS sat I M label hZQ f g).2

end Sharpness.FusionSystem
