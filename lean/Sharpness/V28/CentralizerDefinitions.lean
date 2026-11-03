import Sharpness.Unconditional.CentralizerConstruction
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Centralizer fusion systems at arbitrary, possibly nonabelian, subgroups.
Extensions are taken over joins in the original ambient group. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.V28
variable {S : Type u} [Group S] (F : FusionSystem S)

open scoped Pointwise

/-- The ambient join used in an extension is the actual subgroup product. -/
theorem centralizerJoin_eq_product (E : Subgroup S)
    (P : Subgroup (Subgroup.centralizer (E : Set S))) :
    ((ambientSubgroup (Subgroup.centralizer (E : Set S)) P ⊔ E : Subgroup S) : Set S) =
      (ambientSubgroup (Subgroup.centralizer (E : Set S)) P : Set S) * (E : Set S) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((ambientSubgroup_le _ P).trans (Subgroup.centralizer_le_normalizer (E : Set S)))

/-- Conjugation by an element centralizing a subgroup extends fixing it. -/
theorem centralizingHom_conjugation_of_mem_centralizer
    (E P Q : Subgroup S) (s : S)
    (hs : s ∈ Subgroup.centralizer (E : Set S))
    (h : ∀ x ∈ P, s⁻¹ * x * s ∈ Q) :
    F.CentralizingHom E (subgroupConjugation P Q s h) := by
  have hfix : ∀ z ∈ E, s⁻¹ * z * s = z := by
    intro z hz
    have hc := (Subgroup.mem_centralizer_iff.mp hs) z hz
    calc
      s⁻¹ * z * s = s⁻¹ * (z * s) := mul_assoc _ _ _
      _ = s⁻¹ * (s * z) := congrArg (s⁻¹ * ·) hc
      _ = z := inv_mul_cancel_left s z
  have hsup : ∀ x ∈ P ⊔ E, s⁻¹ * x * s ∈ Q ⊔ E := by
    have hle : P ⊔ E ≤ (Q ⊔ E).comap (MulAut.conj s⁻¹).toMonoidHom := by
      apply sup_le
      · intro x hx
        change s⁻¹ * x * (s⁻¹)⁻¹ ∈ Q ⊔ E
        simpa only [inv_inv] using Subgroup.mem_sup_left (h x hx)
      · intro z hz
        change s⁻¹ * z * (s⁻¹)⁻¹ ∈ Q ⊔ E
        simpa only [inv_inv, hfix z hz] using Subgroup.mem_sup_right hz
    intro x hx
    have hx' := hle hx
    change s⁻¹ * x * (s⁻¹)⁻¹ ∈ Q ⊔ E at hx'
    simpa only [inv_inv] using hx'
  exact ⟨F.conjugation_mem _ _ _ _, subgroupConjugation _ _ s hsup,
    F.conjugation_mem _ _ _ _, (fun _ => rfl), (fun z => hfix z.val z.property)⟩

/-- The centralizer of any subgroup, with extensions fixing that full subgroup. -/
def centralizerOfSubgroup (E : Subgroup S) :
    FusionSystem (Subgroup.centralizer (E : Set S)) where
  IsHom f := F.CentralizingHom E (ambientHom (Subgroup.centralizer (E : Set S)) f)
  injective f hf := by
    intro x y h
    apply (subgroupAmbientEquiv _ _).injective
    apply F.injective _ hf.1
    simpa only [ambientHom_apply] using congrArg (subgroupAmbientEquiv _ _) h
  id_mem P := by rw [ambientHom_id]; exact F.centralizingHom_id E _
  comp_mem f g hf hg := by
    rw [ambientHom_comp]
    exact F.centralizingHom_comp E _ _ hf hg
  inclusion_mem h := by
    rw [ambientHom_inclusion]
    exact F.centralizingHom_inclusion E _
  conjugation_mem P Q s h := by
    let C := Subgroup.centralizer (E : Set S)
    let h' : ∀ x ∈ ambientSubgroup C P, s.val⁻¹ * x * s.val ∈ ambientSubgroup C Q := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨s⁻¹ * y * s, h y hy, rfl⟩
    have heq : ambientHom C (subgroupConjugation P Q s h) =
        subgroupConjugation _ _ s.val h' := by
      ext x
      obtain ⟨y, rfl⟩ := (subgroupAmbientEquiv C P).surjective x
      exact congrArg Subtype.val (ambientHom_apply C _ y)
    rw [heq]
    exact centralizingHom_conjugation_of_mem_centralizer F E _ _ s.val s.property h'
  inverse_mem e he := by
    let e' := (subgroupAmbientEquiv _ _).symm.trans
      (e.trans (subgroupAmbientEquiv _ _))
    exact F.centralizingHom_inverse E e' he
  codomain_restrict_mem f hf hRQ g hgf := by
    apply F.centralizingHom_codomain_restrict E (ambientHom _ f) hf (Subgroup.map_mono hRQ)
    rw [← ambientHom_inclusion _ hRQ, ← ambientHom_comp, hgf]

/-- The defining ambient join-extension condition, with no abelian hypothesis. -/
theorem centralizerOfSubgroup_hom_iff (E : Subgroup S)
    {P Q : Subgroup (Subgroup.centralizer (E : Set S))} (f : P →* Q) :
    (centralizerOfSubgroup F E).IsHom f ↔
      F.CentralizingHom E (ambientHom (Subgroup.centralizer (E : Set S)) f) := Iff.rfl

/-- The inclusion of a centralizer system into the original fusion system. -/
def centralizerOfSubgroup_embedding (E : Subgroup S) :
    F.SubsystemEmbedding (Subgroup.centralizer (E : Set S)) (centralizerOfSubgroup F E) where
  hom_mem _ hf := hf.1

end Sharpness.FusionSystem.V28
