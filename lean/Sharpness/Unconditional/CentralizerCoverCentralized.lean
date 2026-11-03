import Sharpness.Unconditional.CentralizerCoverOmega
import Sharpness.Unconditional.CentralizerCentric
import Sharpness.FullyNormalized

/-! Restricting the concrete centralizer cover to fully centralized elementary
subgroups is an equivalence, proved using ambient saturation extensions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] (F : FusionSystem S) (p : ℕ)

namespace CentralizerCover

variable {F p} (A B : F.CentralizerCover p)

/-- An ambient fusion isomorphism carrying the elementary subgroup onto the
target elementary subgroup gives an isomorphism of cover objects. -/
def isoOfMulEquiv (e : A.centric.obj.as.subgroup ≃* B.centric.obj.as.subgroup)
    (he : F.IsHom e.toMonoidHom)
    (hE : ∀ a : A.elementary,
      (e ⟨a.val, A.le_subgroup a.property⟩).val ∈ B.elementary)
    (hsurj : A.Covers B ⟨e.toMonoidHom, he⟩) : A ≅ B := by
  let eC : A.centric ≅ B.centric := ObjectProperty.isoMk _
    (F.toOrbit.mapIso (F.isoOfMulEquiv e he))
  refine
    { hom := ⟨eC.hom, ⟨e.toMonoidHom, he⟩, rfl, hsurj⟩
      inv := ⟨eC.inv, ⟨e.symm.toMonoidHom, F.inverse_mem e he⟩, rfl, ?_⟩
      hom_inv_id := Subtype.ext eC.hom_inv_id
      inv_hom_id := Subtype.ext eC.inv_hom_id }
  intro a
  refine ⟨⟨(e ⟨a.val, A.le_subgroup a.property⟩).val, hE a⟩, ?_⟩
  exact congrArg Subtype.val (e.symm_apply_apply ⟨a.val, A.le_subgroup a.property⟩)

end CentralizerCover

variable [Finite S]

def centralizerCoverCentralizedProperty : ObjectProperty (F.CentralizerCover p) :=
  fun A => F.FullyCentralized A.elementary

abbrev CentralizedCentralizerCover := (F.centralizerCoverCentralizedProperty p).FullSubcategory

def centralizedCentralizerCoverInclusion :
    F.CentralizedCentralizerCover p ⥤ F.CentralizerCover p :=
  (F.centralizerCoverCentralizedProperty p).ι

theorem centralizerCover_exists_fullyCentralized (sat : F.Saturated p)
    (A : F.CentralizerCover p) :
    ∃ B : F.CentralizerCover p, F.FullyCentralized B.elementary ∧ Nonempty (A ≅ B) := by
  obtain ⟨E₀, e₀, he₀, hE₀⟩ := F.exists_fullyNormalized A.elementary
  have hE₀c := (sat.fully_normalized E₀ hE₀).1
  have hPC : A.centric.obj.as.subgroup ≤ Subgroup.centralizer (A.elementary : Set S) := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.mp (A.centralizes hz)) x hx).symm
  obtain ⟨b, hb, hbE⟩ := F.centralizer_extension_of_fullyCentralized p sat e₀ he₀ hE₀c
  let g : A.centric.obj.as.subgroup →* Subgroup.centralizer (E₀ : Set S) :=
    b.comp (subgroupInclusion _ _ hPC)
  have hg : F.IsHom g := F.comp_mem _ _ (F.inclusion_mem hPC) hb
  let D : Subgroup S := ((Subgroup.centralizer (E₀ : Set S)).subtype.comp g).range
  let eP : A.centric.obj.as.subgroup ≃* D := MonoidHom.ofInjective
    (Subtype.val_injective.comp (F.injective g hg))
  have hDC : D ≤ Subgroup.centralizer (E₀ : Set S) := by
    rintro x ⟨a, rfl⟩
    exact (g a).property
  have heP : F.IsHom eP.toMonoidHom := by
    apply F.codomain_restrict_mem g hg hDC eP.toMonoidHom
    ext a
    rfl
  have hePE : ∀ a : A.elementary,
      (eP ⟨a.val, A.le_subgroup a.property⟩).val = (e₀ a).val := by
    intro a
    exact hbE a (hPC (A.le_subgroup a.property))
  have hE₀D : E₀ ≤ D := by
    intro z hz
    obtain ⟨a, ha⟩ := e₀.surjective ⟨z, hz⟩
    refine ⟨⟨a.val, A.le_subgroup a.property⟩, ?_⟩
    exact (hePE a).trans (congrArg Subtype.val ha)
  have hE₀nontriv : E₀ ≠ ⊥ := by
    intro hbot
    apply A.nontrivial
    apply le_antisymm _ bot_le
    intro z hz
    have heq : e₀ ⟨z, hz⟩ = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ (e₀ ⟨z, hz⟩).property))
    have hz1 : (⟨z, hz⟩ : A.elementary) = 1 :=
      e₀.injective (heq.trans e₀.map_one.symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hz1)
  let B : F.CentralizerCover p :=
    { centric := ⟨F.toOrbit.obj ⟨D⟩, F.isoSystem.centricIn_of_iso eP heP A.centric.property⟩
      elementary := E₀
      nontrivial := hE₀nontriv
      le_subgroup := hE₀D
      centralizes := by
        intro z hz
        apply Subgroup.mem_centralizer_iff.mpr
        intro x hx
        exact ((Subgroup.mem_centralizer_iff.mp (hDC hx)) z hz).symm
      exponent := by
        intro z hz
        obtain ⟨a, ha⟩ := e₀.surjective ⟨z, hz⟩
        have hapow : a ^ p = 1 := Subtype.ext (A.exponent a.val a.property)
        have hh := congrArg (fun a : A.elementary => (e₀ a).val) hapow
        simpa only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one,
          ha] using hh }
  refine ⟨B, hE₀c, ⟨A.isoOfMulEquiv B eP heP ?_ ?_⟩⟩
  · intro a
    change (eP ⟨a.val, A.le_subgroup a.property⟩).val ∈ E₀
    rw [hePE]
    exact (e₀ a).property
  · intro z
    obtain ⟨a, ha⟩ := e₀.surjective z
    exact ⟨a, (hePE a).trans (congrArg Subtype.val ha)⟩

def centralizedCentralizerCoverEquivalence (sat : F.Saturated p) :
    F.CentralizedCentralizerCover p ≌ F.CentralizerCover p := by
  letI : (F.centralizedCentralizerCoverInclusion p).EssSurj :=
    { mem_essImage A := by
        obtain ⟨B, hB, e⟩ := F.centralizerCover_exists_fullyCentralized p sat A
        exact ⟨⟨B, hB⟩, ⟨e.some.symm⟩⟩ }
  letI : (F.centralizedCentralizerCoverInclusion p).IsEquivalence :=
    { full := by
        change (F.centralizerCoverCentralizedProperty p).ι.Full
        infer_instance
      faithful := by
        change (F.centralizerCoverCentralizedProperty p).ι.Faithful
        infer_instance }
  exact (F.centralizedCentralizerCoverInclusion p).asEquivalence

end Sharpness.FusionSystem
