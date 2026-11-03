import Sharpness.Manuscript.CohomologyOrbitDescent
import Sharpness.Unconditional.GroupCohomologyInner
import Sharpness.OrdinaryCohomologyCoefficients

/-! The manuscript's ordinary cohomology coefficient functor, constructed
without transfer data. Its values are native group cohomology of trivial
modules and its maps are the native pullbacks of group homomorphisms. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)
    {A : Type u} [AddCommGroup A] [Module R A] (n : ℕ)

theorem cohomologyRawPull_inner_unconditional (P : F.Object) (r : P.subgroup) :
    F.groupCohomologyRawPull (R := R) (A := A) (F.inner P r) n = LinearMap.id := by
  have hmap : (F.inner P r).val = (MulAut.conj r⁻¹).toMonoidHom := by
    ext x
    simp [FusionSystem.inner, subgroupConjugation, MulAut.conj_apply]
  simpa only [groupCohomologyRawPull, hmap] using
    OrdinaryCohomology.pullLinear_inner (R := R) (A := A) r⁻¹ n

/-- Native ordinary cohomology on the full fusion orbit category. -/
def cohomologyOrbitCoefficient : CoefficientCategory R F.Orbit :=
  F.cohomologyOrbitCoefficientOfInner n
    (F.cohomologyRawPull_inner_unconditional (R := R) (A := A) n)

/-- Passage P2.3, for arbitrary trivial module coefficients. -/
def cohomologyCoefficient : CoefficientCategory R F.CentricOrbit :=
  F.centricInclusion.op ⋙ F.cohomologyOrbitCoefficient (R := R) (A := A) n

theorem cohomologyOrbitCoefficient_obj (P : F.Orbitᵒᵖ) :
    (F.cohomologyOrbitCoefficient (R := R) (A := A) n).obj P =
      OrdinaryCohomology.value R P.unop.as.subgroup A n := rfl

theorem cohomologyOrbitCoefficient_map_raw {P Q : F.Object} (f : P ⟶ Q) :
    (F.cohomologyOrbitCoefficient (R := R) (A := A) n).map (F.toOrbit.map f).op =
      OrdinaryCohomology.pull (R := R) (A := A) f.val n :=
  F.cohomologyOrbitCoefficientOfInner_map_raw n
    (F.cohomologyRawPull_inner_unconditional (R := R) (A := A) n) f

/-- Any actual transfer structure on these fixed values has precisely this
centric contravariant part. The target functor is independent of the structure. -/
def cohomologyMackeyCentricIso
    (I : F.GroupCohomologyTransferLaws (R := R) A n) :
    F.centricCoefficient (F.groupCohomologyMackey I) ≅
      F.cohomologyCoefficient (R := R) (A := A) n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end Sharpness.FusionSystem
