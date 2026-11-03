import Sharpness.SubsystemEmbedding
import Sharpness.SubgroupEqualityIso

/-! Subgroup correspondence and centralizers for T ≤ S, on the actual
ambient groups. These lemmas connect the native subsystem to stability. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
variable {S : Type u} [Group S] (T : Subgroup S)

theorem ambientSubgroup_le (P : Subgroup T) : ambientSubgroup T P ≤ T := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem ambientSubgroup_top : ambientSubgroup T ⊤ = T := by
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

theorem ambientSubgroup_subgroupOf (P : Subgroup S) (hPT : P ≤ T) :
    ambientSubgroup T (P.subgroupOf T) = P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hPT hx⟩, hx, rfl⟩

theorem ambient_bad_centralizer (P : Subgroup T)
    (bad : ¬ Subgroup.centralizer (P : Set T) ≤ P) :
    ¬ Subgroup.centralizer (ambientSubgroup T P : Set S) ⊓ T ≤ ambientSubgroup T P := by
  intro small
  apply bad
  intro c hc
  have hSC : c.val ∈ Subgroup.centralizer (ambientSubgroup T P : Set S) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨yT, hyT, rfl⟩ := hy
    exact congrArg (fun x : T => x.val) ((Subgroup.mem_centralizer_iff.mp hc) yT hyT)
  obtain ⟨yT, hyT, he⟩ := small ⟨hSC, c.property⟩
  have hyc : yT = c := Subtype.ext he
  exact hyc ▸ hyT

namespace FusionSystem
open CategoryTheory
variable (F : FusionSystem S) (H : FusionSystem T) (h : F.SubsystemEmbedding T H)

def subsystemTopIso : (F.subsystemRawFunctor T H h).obj ⟨⊤⟩ ≅ (⟨T⟩ : F.Object) :=
  F.subgroupEqualityIso (ambientSubgroup_top T)

theorem subsystem_top_inclusion_square (P : Subgroup T) :
    (F.subsystemRawFunctor T H h).map (H.inclusion (P := ⟨P⟩) (Q := ⟨⊤⟩) le_top) =
      F.inclusion (ambientSubgroup_le T P) ≫ (F.subsystemTopIso T H h).inv := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  obtain ⟨x₀, rfl⟩ := (subgroupAmbientEquiv T P).surjective x
  apply Subtype.ext
  change (ambientHom T (subgroupInclusion P ⊤ le_top) (subgroupAmbientEquiv T P x₀)).val =
    (subgroupAmbientEquiv T P x₀).val
  rw [ambientHom_apply]
  rfl

end FusionSystem
end Sharpness
