import Sharpness.LinkingSubgroupDiagram
import Sharpness.FusionMackey

/-! Actual centric orbit objects viewed as linking objects, and lifts of
actual orbit arrows. Lifts are used only to prove naturality; the maps
of the already constructed subgroup diagram never depend on a lift. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

def linkingObjectOfOrbit (P : F.CentricOrbit) : L.Object :=
  ⟨⟨P.obj.as.subgroup, P.property⟩⟩

theorem orbitProjection_linkingObjectOfOrbit (P : F.CentricOrbit) :
    L.orbitProjection.obj (L.linkingObjectOfOrbit P) = P := rfl

def liftOrbitArrow {P Q : F.CentricOrbit} (a : P ⟶ Q) :
    L.linkingObjectOfOrbit P ⟶ L.linkingObjectOfOrbit Q :=
  Classical.choose (L.projection_surjective (L.linkingObjectOfOrbit P)
    (L.linkingObjectOfOrbit Q) (F.orbitRepresentative a.hom))

theorem projection_liftOrbitArrow {P Q : F.CentricOrbit} (a : P ⟶ Q) :
    L.projection.map (L.liftOrbitArrow a) = F.orbitRepresentative a.hom :=
  Classical.choose_spec (L.projection_surjective (L.linkingObjectOfOrbit P)
    (L.linkingObjectOfOrbit Q) (F.orbitRepresentative a.hom))

theorem orbitProjection_liftOrbitArrow {P Q : F.CentricOrbit} (a : P ⟶ Q) :
    L.orbitProjection.map (L.liftOrbitArrow a) = a := by
  apply ObjectProperty.hom_ext
  exact (congrArg (fun f => F.toOrbit.map f) (L.projection_liftOrbitArrow a)).trans
    (F.orbitRepresentative_map a.hom)

end Sharpness.FusionSystem.CentricLinkingSystem
