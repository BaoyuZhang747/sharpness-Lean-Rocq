import Sharpness.FusionSystem

/-! Equality of actual subgroups as an explicit fusion isomorphism, whose
two homomorphisms are inclusions and hence act identically on elements. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

def subgroupEqualityIso {P Q : Subgroup S} (h : P = Q) :
    (⟨P⟩ : F.Object) ≅ ⟨Q⟩ where
  hom := F.inclusion h.le
  inv := F.inclusion h.ge
  hom_inv_id := by apply Subtype.ext; apply MonoidHom.ext; intro x; rfl
  inv_hom_id := by apply Subtype.ext; apply MonoidHom.ext; intro x; rfl

end Sharpness.FusionSystem
