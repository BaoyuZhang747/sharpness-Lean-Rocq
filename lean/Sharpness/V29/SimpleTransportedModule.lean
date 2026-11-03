import Sharpness.V29.SimpleDecomposition

/-! Identification of every trace-image summand with the image on the
transported outer-automorphism module `α M(Q)` in Díaz–Park formula (4). -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (Q U : Subgroup S) (L : F.SimpleInclusion Q U)

/-- A chosen fusion-orbit isomorphism. Its representatives are actual
fusion isomorphisms; inner changes act identically on the Mackey values. -/
def simpleLabelIso : F.toOrbit.obj ⟨Q⟩ ≅ F.toOrbit.obj ⟨L.val⟩ :=
  Classical.choice L.property.2

def simpleModuleTransport : M.Value (F.toOrbit.obj ⟨Q⟩) ≃ₗ[k]
    M.Value (F.toOrbit.obj ⟨L.val⟩) := M.isoLinearEquiv (F.simpleLabelIso Q U L)

/-- The outer action on `α M(Q)`: an automorphism of L is pulled back to
Q by the chosen fusion isomorphism. -/
def simpleTransportedOuterAction :
    Aut (F.toOrbit.obj ⟨L.val⟩) →* Module.End k (M.Value (F.toOrbit.obj ⟨Q⟩)) :=
  (M.automorphismAction (F.toOrbit.obj ⟨Q⟩)).comp
    (Aut.autMulEquivOfIso (F.simpleLabelIso Q U L).symm).toMonoidHom

theorem simpleModuleTransport_intertwines
    (a : Aut (F.toOrbit.obj ⟨L.val⟩)) (x : M.Value (F.toOrbit.obj ⟨Q⟩)) :
    F.simpleModuleTransport M Q U L (F.simpleTransportedOuterAction M Q U L a x) =
      M.automorphismAction _ a (F.simpleModuleTransport M Q U L x) := by
  let e := F.simpleLabelIso Q U L
  change M.push e.hom (M.push (e.hom ≫ a.hom ≫ e.inv) x) =
    M.push a.hom (M.push e.hom x)
  rw [M.push_comp, M.push_comp]
  exact M.push_hom_apply e _

def simpleTransportedTrace : M.Value (F.toOrbit.obj ⟨Q⟩) →ₗ[k]
    M.Value (F.toOrbit.obj ⟨Q⟩) :=
  letI : Fintype (F.NormalizerQuotient U L.val) := Fintype.ofFinite _
  ∑ a : F.NormalizerQuotient U L.val,
    F.simpleTransportedOuterAction M Q U L (F.normalizerQuotientToAut U L.val a)

theorem simpleModuleTransport_trace (x : M.Value (F.toOrbit.obj ⟨Q⟩)) :
    F.simpleModuleTransport M Q U L (F.simpleTransportedTrace M Q U L x) =
      F.normalizerTrace M U L.val (F.simpleModuleTransport M Q U L x) := by
  classical
  letI : Fintype (F.NormalizerQuotient U L.val) := Fintype.ofFinite _
  simp only [simpleTransportedTrace, normalizerTrace, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun a _ => F.simpleModuleTransport_intertwines M Q U L _ x)

/-- The summands are genuine trace images of the transported minimal
module, not arbitrary copies of the values at conjugate subgroups. -/
def simpleTransportedTraceRangeEquiv :
    LinearMap.range (F.simpleTransportedTrace M Q U L) ≃ₗ[k]
      LinearMap.range (F.normalizerTrace M U L.val) where
  toFun x := ⟨F.simpleModuleTransport M Q U L x.val, by
    obtain ⟨y, hy⟩ := x.property
    refine ⟨F.simpleModuleTransport M Q U L y, ?_⟩
    rw [← F.simpleModuleTransport_trace M Q U L y, hy]⟩
  invFun y := ⟨(F.simpleModuleTransport M Q U L).symm y.val, by
    obtain ⟨z, hz⟩ := y.property
    refine ⟨(F.simpleModuleTransport M Q U L).symm z, ?_⟩
    apply (F.simpleModuleTransport M Q U L).injective
    rw [F.simpleModuleTransport_trace, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, hz]⟩
  left_inv x := Subtype.ext ((F.simpleModuleTransport M Q U L).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((F.simpleModuleTransport M Q U L).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (map_smul _ _ _)

def DiazParkSimpleValue : Type u :=
  (c : F.SimpleConjugacyClass Q U) →
    LinearMap.range (F.simpleTransportedTrace M Q U (F.simpleClassRepresentative c))

instance : AddCommGroup (F.DiazParkSimpleValue M Q U) := inferInstanceAs
  (AddCommGroup ((c : F.SimpleConjugacyClass Q U) →
    LinearMap.range (F.simpleTransportedTrace M Q U (F.simpleClassRepresentative c))))

instance : Module k (F.DiazParkSimpleValue M Q U) := inferInstanceAs
  (Module k ((c : F.SimpleConjugacyClass Q U) →
    LinearMap.range (F.simpleTransportedTrace M Q U (F.simpleClassRepresentative c))))

def diazParkTraceValueEquiv : F.DiazParkSimpleValue M Q U ≃ₗ[k]
    F.SimpleTraceValue M Q U :=
  LinearEquiv.piCongrRight (fun c =>
    F.simpleTransportedTraceRangeEquiv M Q U (F.simpleClassRepresentative c))

variable (hM : M.IsSimple) (hQ : F.IsMinimalSupport M Q)

def simpleDiazParkEquiv : M.Value (F.toOrbit.obj ⟨U⟩) ≃ₗ[k]
    F.DiazParkSimpleValue M Q U :=
  (F.simpleTraceEquiv M hM Q hQ U).trans (F.diazParkTraceValueEquiv M Q U).symm

end Sharpness.FusionSystem
