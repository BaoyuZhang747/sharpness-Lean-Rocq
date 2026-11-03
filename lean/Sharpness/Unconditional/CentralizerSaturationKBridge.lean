import Sharpness.Unconditional.CentralizerSaturationCentralized
import Sharpness.Unconditional.CentralizerConstructionConjugates
import Sharpness.Unconditional.KNormalization

/-! The actual joint automorphism subgroup for centralizer saturation. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def centralizerJoinAutToAmbient (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) :
    (F.subgroupRestriction (F.centralizerGroup p E)).centralizingJoinAutomorphisms
      (F.elementaryInCentralizer p E) P →*
      F.automorphismSubgroup
        (ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E)) where
  toFun a := ⟨(subgroupAmbientEquiv _ _).symm.trans (a.val.trans (subgroupAmbientEquiv _ _)),
    a.property.1⟩
  map_one' := by
    apply Subtype.ext
    ext x
    simp
  map_mul' a b := by
    apply Subtype.ext
    ext x
    simp

theorem centralizerJoinAutToAmbient_injective (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) :
    Function.Injective (F.centralizerJoinAutToAmbient p E P) := by
  intro a b h
  apply Subtype.ext
  ext x
  have hh := congrArg (fun a => (a.val
    (subgroupAmbientEquiv (F.centralizerGroup p E)
      (P ⊔ F.elementaryInCentralizer p E) x)).val) h
  simpa only [centralizerJoinAutToAmbient, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, subgroupAmbientEquiv_val] using hh

def centralizerJoinK (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) :=
  (F.centralizerJoinAutToAmbient p E P).range

/-- The joint automorphism subgroup is exactly the centralizer automorphism group. -/
def centralizerJoinKEquiv (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) :
    F.centralizerJoinK p E P ≃* (F.centralizerSystem p E).automorphismSubgroup P :=
  (MonoidHom.ofInjective (F.centralizerJoinAutToAmbient_injective p E P)).symm.trans
    ((F.subgroupRestriction (F.centralizerGroup p E)).centralizingAutomorphismEquiv
      (F.elementaryInCentralizer p E) P (F.centralizerSystem_central p E).in_center)

theorem centralizerJoinK_preserves (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) (a : F.centralizerJoinK p E P)
    (x : ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E)) :
    (a.val.val x).val ∈ ambientSubgroup (F.centralizerGroup p E) P ↔
      x.val ∈ ambientSubgroup (F.centralizerGroup p E) P := by
  obtain ⟨b, hb⟩ := a.property
  obtain ⟨y, rfl⟩ := (subgroupAmbientEquiv (F.centralizerGroup p E)
    (P ⊔ F.elementaryInCentralizer p E)).surjective x
  rw [← hb]
  simp only [centralizerJoinAutToAmbient, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  change ((subgroupAmbientEquiv _ _) (b.val y)).val ∈ ambientSubgroup _ P ↔
    (subgroupAmbientEquiv _ _ y).val ∈ ambientSubgroup _ P
  have hmem : ∀ z : (P ⊔ F.elementaryInCentralizer p E :
      Subgroup (F.centralizerGroup p E)),
      (subgroupAmbientEquiv (F.centralizerGroup p E) _ z).val ∈
        ambientSubgroup (F.centralizerGroup p E) P ↔ z.val ∈ P := by
    intro z
    constructor
    · rintro ⟨t, ht, htval⟩
      exact (show t = z.val from Subtype.ext htval) ▸ ht
    · intro hz
      exact ⟨z.val, hz, rfl⟩
  rw [hmem, hmem]
  exact b.property.2.1 y

theorem centralizerJoinK_fixes (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E)) (a : F.centralizerJoinK p E P)
    (z : F.elementaryInCentralizer p E) :
    (a.val.val (subgroupAmbientEquiv (F.centralizerGroup p E)
      (P ⊔ F.elementaryInCentralizer p E) ⟨z.val, Subgroup.mem_sup_right z.property⟩)).val =
      z.val.val := by
  obtain ⟨b, hb⟩ := a.property
  rw [← hb]
  simp only [centralizerJoinAutToAmbient, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  change ((subgroupAmbientEquiv _ _) (b.val ⟨z.val, Subgroup.mem_sup_right z.property⟩)).val = _
  exact congrArg (fun t : F.centralizerGroup p E => t.val) (b.property.2.2 z)

end Sharpness.FusionSystem
