import Sharpness.CentralizerDefinitions
import Sharpness.CentralSupport
import Sharpness.SubgroupAmbientGeometry

/-! The manuscript's deduction E ≤ Z(C_F(E)) from the defining
centralizer extensions. Centrality is proved, rather than included in
the structural reference record. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
variable {S : Type u} [Group S] (T : Subgroup S)

theorem ambientHom_inclusion {P Q : Subgroup T} (h : P ≤ Q) :
    ambientHom T (subgroupInclusion P Q h) =
      subgroupInclusion (ambientSubgroup T P) (ambientSubgroup T Q) (Subgroup.map_mono h) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨x₀, rfl⟩ := (subgroupAmbientEquiv T P).surjective x
  apply Subtype.ext
  exact congrArg (fun z : ambientSubgroup T Q => z.val)
    (ambientHom_apply T (subgroupInclusion P Q h) x₀)

namespace FusionSystem
open CategoryTheory
variable (F : FusionSystem S)

theorem ambientHom_inclusion_allowed {P Q : Subgroup T} (h : P ≤ Q) :
    F.IsHom (ambientHom T (subgroupInclusion P Q h)) := by
  rw [ambientHom_inclusion]
  exact F.inclusion_mem _

variable [Finite S] (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : F.ElementaryCategory p)

theorem elementaryInCentralizer_in_center :
    F.elementaryInCentralizer p E ≤ Subgroup.center (F.centralizerGroup p E) := by
  intro z hz
  apply Subgroup.mem_center_iff.mpr
  intro t
  apply Subtype.ext
  exact ((Subgroup.mem_centralizer_iff.mp t.property) z.val hz).symm

theorem elementaryInCentralizer_nontrivial : F.elementaryInCentralizer p E ≠ ⊥ := by
  intro hz
  apply E.property.1
  have he : ambientSubgroup (F.centralizerGroup p E) (F.elementaryInCentralizer p E) =
      E.obj.subgroup :=
    ambientSubgroup_subgroupOf _ _ (F.elementary_le_centralizer p E)
  exact he.symm.trans (by simp only [hz, ambientSubgroup, Subgroup.map_bot])

theorem centralizer_central_subgroup (C : F.AKOCentralizerInput p hS sat E) :
    C.system.CentralSubgroup (F.elementaryInCentralizer p E) := by
  refine ⟨F.elementaryInCentralizer_in_center p E, ?_⟩
  intro P Q f hf
  obtain ⟨_, g, hgF, hgP, hgZ⟩ := (C.hom_iff f).mp hf
  refine ⟨g, ?_, hgP, hgZ⟩
  apply (C.hom_iff g).mpr
  refine ⟨hgF, ?_⟩
  let A := P ⊔ F.elementaryInCentralizer p E
  let B := Q ⊔ F.elementaryInCentralizer p E
  let pre : (A ⊔ F.elementaryInCentralizer p E : Subgroup (F.centralizerGroup p E)) →* A :=
    subgroupInclusion _ _ (sup_le le_rfl le_sup_right)
  let post : B →* (B ⊔ F.elementaryInCentralizer p E : Subgroup (F.centralizerGroup p E)) :=
    subgroupInclusion _ _ le_sup_left
  let g' := post.comp (g.comp pre)
  have hg' : F.IsHom (ambientHom (F.centralizerGroup p E) g') := by
    change F.IsHom (ambientHom (F.centralizerGroup p E) (post.comp (g.comp pre)))
    rw [ambientHom_comp, ambientHom_comp]
    exact F.comp_mem _ _
      (F.comp_mem _ _ (F.ambientHom_inclusion_allowed _ _) hgF)
      (F.ambientHom_inclusion_allowed _ _)
  exact ⟨g', hg', (fun _ => rfl), hgZ⟩

end FusionSystem
end Sharpness
