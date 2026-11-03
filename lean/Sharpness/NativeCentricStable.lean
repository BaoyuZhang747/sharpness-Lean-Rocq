import Sharpness.NativeLimitCompatible
import Sharpness.StableFunctors
import Sharpness.OrdinaryCohomologyCoefficients

/-! The native centric inverse limit maps isomorphically to actual
stable elements by evaluation at the top subgroup. The Alperin
propagation and compatible-family construction are proved earlier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S R : Type u} [Group S] [Finite S] [CommRing R]
    (F : FusionSystem S) (BLO : F.AlperinInput)

def nativeCentricStableIso (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) :
    limit (F.centricCoefficient M) ≅ ModuleCat.of R (F.stableElements M) :=
  ((F.coefficientData M).onFull F.centricProperty).nativeLimitCompatibleIso ≪≫
    (F.compatibleStableLinearEquiv BLO M).toModuleIso

theorem nativeCentricStableIso_evaluation
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape) :
    (F.nativeCentricStableIso BLO M).hom ≫ ModuleCat.ofHom (F.stableElements M).subtype =
      limit.π (F.centricCoefficient M) (op ⟨F.topOrbit, F.top_centric⟩) := by
  rfl

variable {A : Type u} [AddCommGroup A] [Module R A] {n : ℕ}
    (I : F.GroupCohomologyTransferLaws (R := R) A n)

def ordinaryLimitStableIso :
    limit (F.ordinaryCohomologyCoefficient I) ≅
      ModuleCat.of R (F.stableElements (F.groupCohomologyMackey I)) :=
  HasLimit.isoOfNatIso (F.groupCohomologyCoefficientIso I).symm ≪≫
    F.nativeCentricStableIso BLO (F.groupCohomologyMackey I)

theorem ordinaryLimitStableIso_evaluation :
    (F.ordinaryLimitStableIso BLO I).hom ≫
        ModuleCat.ofHom (F.stableElements (F.groupCohomologyMackey I)).subtype =
      limit.π (F.ordinaryCohomologyCoefficient I) (op ⟨F.topOrbit, F.top_centric⟩) := by
  calc
    _ = (HasLimit.isoOfNatIso (F.groupCohomologyCoefficientIso I).symm).hom ≫
        ((F.nativeCentricStableIso BLO (F.groupCohomologyMackey I)).hom ≫
          ModuleCat.ofHom (F.stableElements (F.groupCohomologyMackey I)).subtype) := by
      simp only [ordinaryLimitStableIso, Iso.trans_hom, Category.assoc]
    _ = (HasLimit.isoOfNatIso (F.groupCohomologyCoefficientIso I).symm).hom ≫
        limit.π (F.centricCoefficient (F.groupCohomologyMackey I))
          (op ⟨F.topOrbit, F.top_centric⟩) := by
      rw [nativeCentricStableIso_evaluation]
    _ = _ := by
      rw [HasLimit.isoOfNatIso_hom_π]
      rfl

end Sharpness.FusionSystem
