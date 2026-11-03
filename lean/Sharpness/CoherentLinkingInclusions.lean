import Sharpness.LinkingMonomorphisms
import Sharpness.ReferenceInputs

/-! Coherent lifts of actual subgroup inclusions. Choose maps to the
top subgroup once. Central fibers give a compatible lift of each
inclusion, and categorical cancellation proves uniqueness, identity,
and composition. This construction uses no additional reference input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def topObject : L.Object := ⟨⟨⊤, F.top_centric⟩⟩

def topInclusionLift (P : L.Object) : P ⟶ L.topObject :=
  Classical.choose (L.projection_surjective P L.topObject (F.inclusion le_top))

theorem projection_topInclusionLift (P : L.Object) :
    L.projection.map (L.topInclusionLift P) = F.inclusion le_top :=
  Classical.choose_spec (L.projection_surjective P L.topObject (F.inclusion le_top))

theorem exists_inclusion_over_top {P Q : L.Object} (h : P.as.val ≤ Q.as.val) :
    ∃ f : P ⟶ Q, f ≫ L.topInclusionLift Q = L.topInclusionLift P := by
  obtain ⟨f, hf⟩ := L.projection_surjective P Q (F.inclusion h)
  have hp : L.projection.map (f ≫ L.topInclusionLift Q) =
      L.projection.map (L.topInclusionLift P) := by
    rw [L.projection.map_comp, hf, L.projection_topInclusionLift,
      L.projection_topInclusionLift]
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    rfl
  obtain ⟨z, hz, _⟩ := (L.central_fiber (f ≫ L.topInclusionLift Q)
    (L.topInclusionLift P)).mp hp
  exact ⟨(L.distinguished P z.val).hom ≫ f, by
    simpa only [Category.assoc] using hz⟩

def inclusionLift {P Q : L.Object} (h : P.as.val ≤ Q.as.val) : P ⟶ Q :=
  Classical.choose (L.exists_inclusion_over_top h)

theorem inclusionLift_comp_top {P Q : L.Object} (h : P.as.val ≤ Q.as.val) :
    L.inclusionLift h ≫ L.topInclusionLift Q = L.topInclusionLift P :=
  Classical.choose_spec (L.exists_inclusion_over_top h)

theorem projection_inclusionLift {P Q : L.Object} (h : P.as.val ≤ Q.as.val) :
    L.projection.map (L.inclusionLift h) = F.inclusion h := by
  have hp := congrArg (fun f => L.projection.map f) (L.inclusionLift_comp_top h)
  rw [L.projection.map_comp, L.projection_topInclusionLift,
    L.projection_topInclusionLift] at hp
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun f => (f.val x).val) hp

theorem inclusionLift_unique {P Q : L.Object} (h : P.as.val ≤ Q.as.val)
    (f : P ⟶ Q) (hf : f ≫ L.topInclusionLift Q = L.topInclusionLift P) :
    f = L.inclusionLift h :=
  L.cancel_right f (L.inclusionLift h) (L.topInclusionLift Q)
    (hf.trans (L.inclusionLift_comp_top h).symm)

@[simp] theorem inclusionLift_refl (P : L.Object) :
    L.inclusionLift (le_refl P.as.val) = 𝟙 P := by
  apply L.cancel_right _ _ (L.topInclusionLift P)
  rw [L.inclusionLift_comp_top, Category.id_comp]

@[simp] theorem inclusionLift_comp {P Q T : L.Object}
    (hPQ : P.as.val ≤ Q.as.val) (hQT : Q.as.val ≤ T.as.val) :
    L.inclusionLift hPQ ≫ L.inclusionLift hQT = L.inclusionLift (hPQ.trans hQT) := by
  apply L.cancel_right _ _ (L.topInclusionLift T)
  rw [Category.assoc, L.inclusionLift_comp_top, L.inclusionLift_comp_top,
    L.inclusionLift_comp_top]

theorem inclusionLift_distinguished {P Q : L.Object} (h : P.as.val ≤ Q.as.val)
    (x : P.as.val) :
    (L.distinguished P x).hom ≫ L.inclusionLift h =
      L.inclusionLift h ≫ (L.distinguished Q (subgroupInclusion _ _ h x)).hom := by
  have hc := L.commutation (L.inclusionLift h) x
  rw [L.projection_inclusionLift] at hc
  change _ = L.inclusionLift h ≫ (L.distinguished Q ⟨x.val, h x.property⟩).hom
  change _ = L.inclusionLift h ≫ (L.distinguished Q ⟨x.val, h x.property⟩).hom at hc
  exact hc

end Sharpness.FusionSystem.CentricLinkingSystem
