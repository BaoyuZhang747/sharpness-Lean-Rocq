import Sharpness.FusionSystem

/-! Restriction of an actual raw fusion isomorphism to subgroups it
maps onto one another. The allowed restricted map is obtained from
the fusion-system codomain-restriction axiom, not a new input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

def restrictRawIso {P Q A B : Subgroup S} (hAP : A ≤ P) (hBQ : B ≤ Q)
    (e : (⟨P⟩ : F.Object) ≅ ⟨Q⟩)
    (hm : ∀ x : P, x.val ∈ A ↔ (e.hom.val x).val ∈ B) :
    (⟨A⟩ : F.Object) ≅ ⟨B⟩ := by
  let f : A →* B :=
    { toFun x := ⟨(e.hom.val ⟨x.val, hAP x.property⟩).val,
        (hm ⟨x.val, hAP x.property⟩).mp x.property⟩
      map_one' := by
        apply Subtype.ext
        change (e.hom.val (1 : P)).val = (1 : Q).val
        exact congrArg (fun z : Q => z.val) (e.hom.val.map_one)
      map_mul' x y := by
        apply Subtype.ext
        change (e.hom.val (⟨x.val, hAP x.property⟩ * ⟨y.val, hAP y.property⟩)).val =
          ((e.hom.val ⟨x.val, hAP x.property⟩) * (e.hom.val ⟨y.val, hAP y.property⟩)).val
        exact congrArg (fun z : Q => z.val) (e.hom.val.map_mul ⟨x.val, hAP x.property⟩
          ⟨y.val, hAP y.property⟩) }
  have hf : F.IsHom f := F.codomain_restrict_mem
    (e.hom.val.comp (subgroupInclusion A P hAP))
    (F.comp_mem _ _ (F.inclusion_mem hAP) e.hom.property) hBQ f (by
      apply MonoidHom.ext
      intro x
      rfl)
  have hinj : Function.Injective f := by
    intro x y hxy
    have hval : (e.hom.val ⟨x.val, hAP x.property⟩).val =
        (e.hom.val ⟨y.val, hAP y.property⟩).val := congrArg (fun z : B => z.val) hxy
    have h := F.injective e.hom.val e.hom.property (Subtype.ext hval)
    exact Subtype.ext (congrArg (fun z : P => z.val) h)
  have hsurj : Function.Surjective f := by
    intro y
    let y' : Q := ⟨y.val, hBQ y.property⟩
    let x : P := e.inv.val y'
    have hx : e.hom.val x = y' := congrArg (fun g => g.val y') e.inv_hom_id
    have hxA : x.val ∈ A := (hm x).mpr (by rw [hx]; exact y.property)
    refine ⟨⟨x.val, hxA⟩, ?_⟩
    apply Subtype.ext
    change (e.hom.val x).val = y.val
    exact congrArg (fun z : Q => z.val) hx
  let e' : A ≃* B := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  exact
    { hom := ⟨f, hf⟩
      inv := ⟨e'.symm.toMonoidHom, F.inverse_mem e' hf⟩
      hom_inv_id := by
        apply Subtype.ext
        apply MonoidHom.ext
        intro x
        exact e'.symm_apply_apply x
      inv_hom_id := by
        apply Subtype.ext
        apply MonoidHom.ext
        intro x
        exact e'.apply_symm_apply x }

theorem restrictRawIso_hom_apply {P Q A B : Subgroup S} (hAP : A ≤ P) (hBQ : B ≤ Q)
    (e : (⟨P⟩ : F.Object) ≅ ⟨Q⟩)
    (hm : ∀ x : P, x.val ∈ A ↔ (e.hom.val x).val ∈ B) (x : A) :
    ((F.restrictRawIso hAP hBQ e hm).hom.val x).val =
      (e.hom.val ⟨x.val, hAP x.property⟩).val := rfl

end Sharpness.FusionSystem
