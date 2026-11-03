import Sharpness.Unconditional.FusionCohomologyPush

/-! Native fusion pushforward can be computed using any actual
isomorphism followed by a literal subgroup inclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {R S A : Type u} [CommRing R] [Group S] [Finite S]
  [AddCommGroup A] [Module R A] (F : FusionSystem S)

omit [Finite S] in
theorem imageSubgroup_comp_inclusion {P D Q : F.Object} (f : P ⟶ D)
    (h : D.subgroup ≤ Q.subgroup) :
    F.imageSubgroup (f ≫ F.inclusion h) = F.imageSubgroup f := rfl

theorem nativeGroupCohomologyRawPush_iso_inclusion {P D Q : F.Object}
    (e : P ≅ D) (h : D.subgroup ≤ Q.subgroup) (n : ℕ) :
    F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
        (e.hom ≫ F.inclusion h) =
      (OrdinaryCohomology.subgroupTransfer D.subgroup Q.subgroup h n).comp
        (F.groupCohomologyRawPull e.inv n) := by
  let f := e.hom ≫ F.inclusion h
  let I := F.imageSubgroup f
  have hI : I = D.subgroup := (F.imageSubgroup_comp_inclusion e.hom h).trans
    (F.imageSubgroup_iso e)
  have hID : I ≤ D.subgroup := hI.le
  have hDI : D.subgroup ≤ I := hI.ge
  have hi : (F.imageIso f).inv.val = e.inv.val.comp (Subgroup.inclusion hID) := by
    apply MonoidHom.ext
    intro x
    apply F.injective _ e.hom.property
    have h1 := congrArg (fun k : (⟨I⟩ : F.Object) ⟶ Q => (k.val x).val)
      (F.imageIso_inv_factorization f)
    have h2 := congrArg (fun k : D ⟶ D => k.val (Subgroup.inclusion hID x))
      e.inv_hom_id
    apply Subtype.ext
    exact h1.trans (congrArg Subtype.val h2).symm
  change (OrdinaryCohomology.subgroupTransfer (R := R) (A := A)
      I Q.subgroup (F.image_le f) n).comp
        (OrdinaryCohomology.pullLinear (F.imageIso f).inv.val n) = _
  rw [hi, OrdinaryCohomology.pullLinear_comp, ← LinearMap.comp_assoc,
    OrdinaryCohomology.subgroupTransfer_comp_pull_eq _ _ _ hID hDI]
  rfl

theorem nativeGroupCohomologyRawPush_precomp_iso {X P Q : F.Object}
    (e : X ≅ P) (f : P ⟶ Q) (n : ℕ) :
    F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
        (e.hom ≫ f) =
      (F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
        f).comp (F.groupCohomologyRawPull e.inv n) := by
  have hf : f = (F.imageIso f).hom ≫ F.inclusion (F.image_le f) :=
    (F.image_factorization f).symm
  calc
    F.groupCohomologyRawPush _ (e.hom ≫ f) =
        F.groupCohomologyRawPush _ ((e.trans (F.imageIso f)).hom ≫
          F.inclusion (F.image_le f)) := by rw [hf, ← Category.assoc]; rfl
    _ = (OrdinaryCohomology.subgroupTransfer (F.imageSubgroup f) Q.subgroup
        (F.image_le f) n).comp (F.groupCohomologyRawPull (e.trans (F.imageIso f)).inv n) :=
      F.nativeGroupCohomologyRawPush_iso_inclusion _ _ n
    _ = _ := by
      change (OrdinaryCohomology.subgroupTransfer (F.imageSubgroup f) Q.subgroup
        (F.image_le f) n).comp
          (F.groupCohomologyRawPull ((F.imageIso f).inv ≫ e.inv) n) = _
      rw [groupCohomologyRawPull_comp, ← LinearMap.comp_assoc]
      rfl

end Sharpness.FusionSystem
