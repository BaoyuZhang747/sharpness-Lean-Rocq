import Sharpness.Unconditional.CentralizerSaturationExtension

/-! A fusion map on the ambient join which fixes `E` supplies an actual
centralizer conjugate of the original subgroup. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

theorem centralizerSystem_conjugate_of_join_map (p : ℕ) (E : F.ElementaryCategory p)
    (P : Subgroup (F.centralizerGroup p E))
    (f : ambientSubgroup (F.centralizerGroup p E) (P ⊔ F.elementaryInCentralizer p E) →*
      F.centralizerGroup p E) (hf : F.IsHom f)
    (hfix : ∀ z : F.elementaryInCentralizer p E,
      f (subgroupAmbientEquiv (F.centralizerGroup p E)
        (P ⊔ F.elementaryInCentralizer p E) ⟨z.val, Subgroup.mem_sup_right z.property⟩) = z.val) :
    ∃ (Q : Subgroup (F.centralizerGroup p E)) (v : P ≃* Q),
      (F.centralizerSystem p E).IsHom v.toMonoidHom ∧
      ∀ x : P, (v x).val = f (subgroupAmbientEquiv (F.centralizerGroup p E)
        (P ⊔ F.elementaryInCentralizer p E) ⟨x.val, Subgroup.mem_sup_left x.property⟩) := by
  let T := F.centralizerGroup p E
  let Z := F.elementaryInCentralizer p E
  let C := F.centralizerSystem p E
  let gJ : (P ⊔ Z : Subgroup T) →* (⊤ : Subgroup T) :=
    { toFun x := ⟨f (subgroupAmbientEquiv T (P ⊔ Z) x), trivial⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' x y := by apply Subtype.ext; simp }
  have hgJ : F.IsHom (ambientHom T gJ) := by
    apply F.codomain_restrict_mem f hf (ambientSubgroup_le T ⊤) (ambientHom T gJ)
    apply MonoidHom.ext
    intro x
    obtain ⟨x, rfl⟩ := (subgroupAmbientEquiv T (P ⊔ Z)).surjective x
    apply Subtype.ext
    change (ambientHom T gJ (subgroupAmbientEquiv T (P ⊔ Z) x)).val = _
    rw [ambientHom_apply]
    rfl
  have hgJC : C.IsHom gJ := centralizingHom_of_fixes (F.subgroupRestriction T)
    (show Z ≤ P ⊔ Z from le_sup_right) gJ hgJ hfix
  let gP := gJ.comp (subgroupInclusion P (P ⊔ Z) le_sup_left)
  have hgPC : C.IsHom gP := C.comp_mem _ _ (C.inclusion_mem le_sup_left) hgJC
  let gRaw : P →* T := (⊤ : Subgroup T).subtype.comp gP
  have hRaw : Function.Injective gRaw := Subtype.val_injective.comp (C.injective gP hgPC)
  let Q : Subgroup T := gRaw.range
  let v : P ≃* Q := MonoidHom.ofInjective hRaw
  refine ⟨Q, v, ?_, fun _ => rfl⟩
  apply C.codomain_restrict_mem gP hgPC le_top v.toMonoidHom
  ext x
  rfl

end Sharpness.FusionSystem
