import Sharpness.SubsystemEmbedding
import Sharpness.Manuscript.CohomologyCoefficient
import Sharpness.Unconditional.GroupCohomologyIsoTransport

/-! Native cohomology transport for actual embedded fusion subsystems.
Every component is the pullback along the literal subgroup-image equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] (F : FusionSystem S)
    (T : Subgroup S) (H : FusionSystem T) (h : F.SubsystemEmbedding T H)

def subsystemCohomologyOrbitIso (n : ℕ) :
    (F.subsystemOrbitFunctor T H h).op ⋙ F.cohomologyOrbitCoefficient (R := R) (A := A) n ≅
      H.cohomologyOrbitCoefficient (R := R) (A := A) n :=
  NatIso.ofComponents (fun P => OrdinaryCohomology.pullIso
    (subgroupAmbientEquiv T P.unop.as.subgroup) n) (by
      intro P Q f
      let g := H.orbitRepresentative f.unop
      have hg : H.toOrbit.map g = f.unop := H.orbitRepresentative_map f.unop
      change (F.cohomologyOrbitCoefficient n).map
          ((F.subsystemOrbitFunctor T H h).map f.unop).op ≫
          OrdinaryCohomology.pull (subgroupAmbientEquiv T Q.unop.as.subgroup).toMonoidHom n =
        OrdinaryCohomology.pull (subgroupAmbientEquiv T P.unop.as.subgroup).toMonoidHom n ≫
          (H.cohomologyOrbitCoefficient n).map f
      rw [← hg, F.subsystemOrbitFunctor_map_raw, F.cohomologyOrbitCoefficient_map_raw]
      have hf : f = (H.toOrbit.map g).op := congrArg Quiver.Hom.op hg.symm
      rw [hf, H.cohomologyOrbitCoefficient_map_raw,
        ← OrdinaryCohomology.pull_comp, ← OrdinaryCohomology.pull_comp]
      congr 1
      apply MonoidHom.ext
      intro x
      exact ambientHom_apply T g.val x)

@[simp] theorem subsystemCohomologyOrbitIso_hom_app (n : ℕ) (P : H.Orbit) :
    (F.subsystemCohomologyOrbitIso (R := R) (A := A) T H h n).hom.app (op P) =
      OrdinaryCohomology.pull (subgroupAmbientEquiv T P.as.subgroup).toMonoidHom n := rfl

end Sharpness.FusionSystem
