import Sharpness.Unconditional.FiniteGroupFusionReceptive
import Sharpness.Unconditional.SaturationCharacterization

/-! The fusion system induced by a Sylow subgroup of a finite group satisfies
both saturation axioms, with no saturation or extension premise. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
variable {G : Type u} [Group G] [Finite G]

/-- A finite group's fusion system on any Sylow subgroup is saturated. -/
theorem finiteGroupFusion_saturated (p : ℕ) [Fact p.Prime] (S : Sylow p G) :
    (finiteGroupFusion (S : Subgroup G)).Saturated p :=
  (finiteGroupFusion (S : Subgroup G)).saturated_of_fullyNormalized_sylow_receptive p
    S.isPGroup' (finiteGroupFusion_fullyNormalized_sylow p S)
    (finiteGroupFusion_fullyNormalized_receptive p S)

end Sharpness
