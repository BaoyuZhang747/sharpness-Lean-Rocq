import Sharpness.Unconditional.AbelianCentralizerConjugates
import Sharpness.Unconditional.KNormalization

/-! The actual joint automorphism subgroup for centralizer saturation. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

def abelianCentralizerJoinAutToAmbient (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) :
    (F.subgroupRestriction (F.abelianCentralizerGroup E)).centralizingJoinAutomorphisms
      (F.abelianInCentralizer E) P →*
      F.automorphismSubgroup
        (ambientSubgroup (F.abelianCentralizerGroup E) (P ⊔ F.abelianInCentralizer E)) where
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

theorem abelianCentralizerJoinAutToAmbient_injective (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) :
    Function.Injective (F.abelianCentralizerJoinAutToAmbient E P) := by
  intro a b h
  apply Subtype.ext
  ext x
  have hh := congrArg (fun a => (a.val
    (subgroupAmbientEquiv (F.abelianCentralizerGroup E)
      (P ⊔ F.abelianInCentralizer E) x)).val) h
  simpa only [abelianCentralizerJoinAutToAmbient, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, subgroupAmbientEquiv_val] using hh

def abelianCentralizerJoinK (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) :=
  (F.abelianCentralizerJoinAutToAmbient E P).range

/-- The joint automorphism subgroup is exactly the centralizer automorphism group. -/
def abelianCentralizerJoinKEquiv (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) :
    F.abelianCentralizerJoinK E P ≃* (F.abelianCentralizerSystem E).automorphismSubgroup P :=
  (MonoidHom.ofInjective (F.abelianCentralizerJoinAutToAmbient_injective E P)).symm.trans
    ((F.subgroupRestriction (F.abelianCentralizerGroup E)).centralizingAutomorphismEquiv
      (F.abelianInCentralizer E) P (F.abelianCentralizerSystem_central E).in_center)

theorem abelianCentralizerJoinK_preserves (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) (a : F.abelianCentralizerJoinK E P)
    (x : ambientSubgroup (F.abelianCentralizerGroup E) (P ⊔ F.abelianInCentralizer E)) :
    (a.val.val x).val ∈ ambientSubgroup (F.abelianCentralizerGroup E) P ↔
      x.val ∈ ambientSubgroup (F.abelianCentralizerGroup E) P := by
  obtain ⟨b, hb⟩ := a.property
  obtain ⟨y, rfl⟩ := (subgroupAmbientEquiv (F.abelianCentralizerGroup E)
    (P ⊔ F.abelianInCentralizer E)).surjective x
  rw [← hb]
  simp only [abelianCentralizerJoinAutToAmbient, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  change ((subgroupAmbientEquiv _ _) (b.val y)).val ∈ ambientSubgroup _ P ↔
    (subgroupAmbientEquiv _ _ y).val ∈ ambientSubgroup _ P
  have hmem : ∀ z : (P ⊔ F.abelianInCentralizer E :
      Subgroup (F.abelianCentralizerGroup E)),
      (subgroupAmbientEquiv (F.abelianCentralizerGroup E) _ z).val ∈
        ambientSubgroup (F.abelianCentralizerGroup E) P ↔ z.val ∈ P := by
    intro z
    constructor
    · rintro ⟨t, ht, htval⟩
      exact (show t = z.val from Subtype.ext htval) ▸ ht
    · intro hz
      exact ⟨z.val, hz, rfl⟩
  rw [hmem, hmem]
  exact b.property.2.1 y

theorem abelianCentralizerJoinK_fixes (E : F.AbelianCentralizerData)
    (P : Subgroup (F.abelianCentralizerGroup E)) (a : F.abelianCentralizerJoinK E P)
    (z : F.abelianInCentralizer E) :
    (a.val.val (subgroupAmbientEquiv (F.abelianCentralizerGroup E)
      (P ⊔ F.abelianInCentralizer E) ⟨z.val, Subgroup.mem_sup_right z.property⟩)).val =
      z.val.val := by
  obtain ⟨b, hb⟩ := a.property
  rw [← hb]
  simp only [abelianCentralizerJoinAutToAmbient, MonoidHom.coe_mk, OneHom.coe_mk,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  change ((subgroupAmbientEquiv _ _) (b.val ⟨z.val, Subgroup.mem_sup_right z.property⟩)).val = _
  exact congrArg (fun t : F.abelianCentralizerGroup E => t.val) (b.property.2.2 z)

end Sharpness.FusionSystem
