import Sharpness.GroupCohomologyMackey
import Sharpness.HigherLimits

/-! The native ordinary group-cohomology coefficient functor and its
natural comparison with the constructed full Mackey object's
contravariant part. No acyclicity is included in the comparison. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)
    {A : Type u} [AddCommGroup A] [Module R A]
    {n : ℕ} (I : F.GroupCohomologyTransferLaws (R := R) A n)

def ordinaryCohomologyOrbitCoefficient : CoefficientCategory R F.Orbit where
  obj P := OrdinaryCohomology.value R P.unop.as.subgroup A n
  map f := ModuleCat.ofHom (F.groupCohomologyOrbitPull f.unop)
  map_id P := by
    apply ModuleCat.hom_ext
    exact F.groupCohomologyOrbitPull_id I P.unop
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact F.groupCohomologyOrbitPull_comp I g.unop f.unop

def ordinaryCohomologyCoefficient : CoefficientCategory R F.CentricOrbit :=
  F.centricInclusion.op ⋙ F.ordinaryCohomologyOrbitCoefficient I

theorem ordinaryCohomologyOrbitCoefficient_map_raw {P Q : F.Object} (f : P ⟶ Q) :
    (F.ordinaryCohomologyOrbitCoefficient I).map (F.toOrbit.map f).op =
      OrdinaryCohomology.pull (R := R) (A := A) f.val n := by
  apply ModuleCat.hom_ext
  exact F.groupCohomologyOrbitPull_raw I f

def groupCohomologyCoefficientIso :
    F.centricCoefficient (F.groupCohomologyMackey I) ≅ F.ordinaryCohomologyCoefficient I :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end Sharpness.FusionSystem
