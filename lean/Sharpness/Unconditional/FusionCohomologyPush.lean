import Sharpness.GroupCohomologyTransferInput
import Sharpness.Unconditional.GroupCohomologyTransferIdentity

/-! The actual native transfer has the required pushforward behavior on
fusion isomorphisms. The image subgroup is the literal image used by the
manuscript's covariant map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology

variable {R S A : Type u} [CommRing R] [Group S] [Finite S]
  [AddCommGroup A] [Module R A]

theorem subgroupTransfer_eq_pull_of_eq (P Q : Subgroup S)
    (h : P ≤ Q) (h' : Q ≤ P) (n : ℕ) :
    subgroupTransfer (R := R) (A := A) P Q h n =
      pullLinear (Subgroup.inclusion h') n := by
  have he : P = Q := le_antisymm h h'
  subst Q
  rw [subgroupTransfer_self]
  have hi : Subgroup.inclusion h' = MonoidHom.id P := by ext x; rfl
  rw [hi, pullLinear_id]

theorem subgroupTransfer_comp_pull_eq (P D Q : Subgroup S)
    (hDP : D ≤ P) (hPD : P ≤ D) (hDQ : D ≤ Q) (n : ℕ) :
    (subgroupTransfer (R := R) (A := A) D Q hDQ n).comp
        (pullLinear (Subgroup.inclusion hDP) n) =
      subgroupTransfer P Q (hPD.trans hDQ) n := by
  have he : P = D := le_antisymm hPD hDP
  subst D
  have hi : Subgroup.inclusion hDP = MonoidHom.id P := by ext x; rfl
  rw [hi, pullLinear_id, LinearMap.comp_id]

end Sharpness.OrdinaryCohomology

namespace Sharpness.FusionSystem
open CategoryTheory

variable {R S A : Type u} [CommRing R] [Group S] [Finite S]
  [AddCommGroup A] [Module R A] (F : FusionSystem S)

omit [Finite S] in
/-- The image of an actual fusion isomorphism is its whole target subgroup. -/
theorem imageSubgroup_iso {P Q : F.Object} (e : P ≅ Q) :
    F.imageSubgroup e.hom = Q.subgroup := by
  apply le_antisymm (F.image_le e.hom)
  intro x hx
  refine ⟨e.inv.val ⟨x, hx⟩, ?_⟩
  have h := congrArg (fun f : Q ⟶ Q => f.val ⟨x, hx⟩) e.inv_hom_id
  exact congrArg Subtype.val h

/-- The actual finite-index transfers on all literal subgroups. -/
def nativeGroupCohomologyTransfer (n : ℕ) : ModuleGroupCohomologyTransfer R S A n :=
  fun P Q h => OrdinaryCohomology.subgroupTransfer P Q h n

theorem nativeGroupCohomologyRawPush_iso {P Q : F.Object} (e : P ≅ Q) (n : ℕ) :
    F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
        e.hom = F.groupCohomologyRawPull e.inv n := by
  have hrev : Q.subgroup ≤ F.imageSubgroup e.hom := (F.imageSubgroup_iso e).ge
  have hi : (F.imageIso e.hom).inv.val.comp (Subgroup.inclusion hrev) = e.inv.val := by
    apply MonoidHom.ext
    intro x
    apply (F.injective _ (F.imageIso e.hom).hom.property)
    have h1 := congrArg
      (fun f : (⟨F.imageSubgroup e.hom⟩ : F.Object) ⟶ ⟨F.imageSubgroup e.hom⟩ =>
        f.val (Subgroup.inclusion hrev x)) (F.imageIso e.hom).inv_hom_id
    have h2 := congrArg (fun f : Q ⟶ Q => f.val x) e.inv_hom_id
    apply Subtype.ext
    exact (congrArg Subtype.val h1).trans (congrArg Subtype.val h2).symm
  change (OrdinaryCohomology.subgroupTransfer (R := R) (A := A)
      (F.imageSubgroup e.hom) Q.subgroup (F.image_le e.hom) n).comp
        (OrdinaryCohomology.pullLinear (F.imageIso e.hom).inv.val n) =
      OrdinaryCohomology.pullLinear e.inv.val n
  rw [OrdinaryCohomology.subgroupTransfer_eq_pull_of_eq _ _ _ hrev,
    ← OrdinaryCohomology.pullLinear_comp, hi]

omit [Finite S] in
theorem imageSubgroup_inclusion {P Q : F.Object} (h : P.subgroup ≤ Q.subgroup) :
    F.imageSubgroup (F.inclusion h) = P.subgroup := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact y.property
  · intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite S] in
theorem imageIso_inv_factorization {P Q : F.Object} (f : P ⟶ Q) :
    (F.imageIso f).inv ≫ f = F.inclusion (F.image_le f) := by
  conv_lhs => arg 2; rw [← F.image_factorization f]
  change (F.imageIso f).inv ≫ ((F.imageIso f).hom ≫ _) = _
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem nativeGroupCohomologyRawPush_inclusion {P Q : F.Object}
    (h : P.subgroup ≤ Q.subgroup) (n : ℕ) :
    F.groupCohomologyRawPush (nativeGroupCohomologyTransfer (R := R) (S := S) (A := A) n)
        (F.inclusion h) = OrdinaryCohomology.subgroupTransfer P.subgroup Q.subgroup h n := by
  let D := F.imageSubgroup (F.inclusion h)
  have hDP : D ≤ P.subgroup := (F.imageSubgroup_inclusion h).le
  have hPD : P.subgroup ≤ D := (F.imageSubgroup_inclusion h).ge
  have hi : (F.imageIso (F.inclusion h)).inv.val = Subgroup.inclusion hDP := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : (⟨D⟩ : F.Object) ⟶ Q => (f.val x).val)
      (F.imageIso_inv_factorization (F.inclusion h))
  change (OrdinaryCohomology.subgroupTransfer (R := R) (A := A)
      D Q.subgroup (F.image_le (F.inclusion h)) n).comp
        (OrdinaryCohomology.pullLinear (F.imageIso (F.inclusion h)).inv.val n) = _
  rw [hi, OrdinaryCohomology.subgroupTransfer_comp_pull_eq _ _ _ hDP hPD]

end Sharpness.FusionSystem
