import Sharpness.CentricLinkingSystem

/-! Every actual linking-system morphism is a categorical
monomorphism. Injectivity of the actual raw fusion map and the
unique central-fiber axiom give cancellation directly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

theorem projection_cancel_right {P Q T : L.Object} (a b : P ⟶ Q) (h : Q ⟶ T)
    (hab : a ≫ h = b ≫ h) : L.projection.map a = L.projection.map b := by
  have hp := congrArg (fun t => L.projection.map t) hab
  rw [L.projection.map_comp, L.projection.map_comp] at hp
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply F.injective (L.projection.map h).val (L.projection.map h).property
  exact congrArg (fun t => t.val x) hp

theorem cancel_right {P Q T : L.Object} (a b : P ⟶ Q) (h : Q ⟶ T)
    (hab : a ≫ h = b ≫ h) : a = b := by
  obtain ⟨z, hz, _⟩ := (L.central_fiber a b).mp (L.projection_cancel_right a b h hab)
  obtain ⟨w, _, hw⟩ := (L.central_fiber (a ≫ h) (a ≫ h)).mp rfl
  have hz' : (L.distinguished P z.val).hom ≫ (a ≫ h) = a ≫ h := by
    calc
      _ = ((L.distinguished P z.val).hom ≫ a) ≫ h := (Category.assoc _ _ _).symm
      _ = b ≫ h := congrArg (fun t => t ≫ h) hz
      _ = a ≫ h := hab.symm
  have h1 : (L.distinguished P (1 : Subgroup.center P.as.val).val).hom ≫ (a ≫ h) = a ≫ h := by
    simp only [Subgroup.coe_one, map_one]
    change (𝟙 P) ≫ (a ≫ h) = a ≫ h
    exact Category.id_comp _
  have hz1 : z = 1 := (hw z hz').trans (hw 1 h1).symm
  rw [hz1] at hz
  simp only [Subgroup.coe_one, map_one] at hz
  change (𝟙 P) ≫ a = b at hz
  simpa only [Category.id_comp] using hz

instance linking_mono {P Q : L.Object} (h : P ⟶ Q) : Mono h where
  right_cancellation a b hab := L.cancel_right a b h hab

end Sharpness.FusionSystem.CentricLinkingSystem
