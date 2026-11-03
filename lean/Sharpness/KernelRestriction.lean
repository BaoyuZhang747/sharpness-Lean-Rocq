import Sharpness.SimpleTransport
import Sharpness.MackeyPullback

/-! Restriction of a central quotient-kernel automorphism to every
overgroup of Z, with literal subgroup maps and commuting inclusion square. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z P : Subgroup S} (hZ : F.CentralSubgroup Z) (hZP : Z ≤ P)
    [(Z.subgroupOf P).Normal]

theorem gamma_modZ (a : F.Gamma hZ hZP) (x : P) :
    x⁻¹ * a.val.val x ∈ Z.subgroupOf P :=
  quotient_kernel_modZ (F.automorphismSubgroup P).subtype (Z.subgroupOf P)
    (F.central_aut_fixed hZ hZP) a x

theorem gamma_preserves_overgroup (a : F.Gamma hZ hZP)
    {L : Subgroup S} (hZL : Z ≤ L) (hLP : L ≤ P) (x : L) :
    (a.val.val ⟨x.val, hLP x.property⟩).val ∈ L := by
  let xP : P := ⟨x.val, hLP x.property⟩
  have hx := F.gamma_modZ hZ hZP a xP
  have hz : x.val⁻¹ * (a.val.val xP).val ∈ Z := hx
  have hl := L.mul_mem x.property (hZL hz)
  simpa only [mul_inv_cancel_left] using hl

def gammaRestrictionHom (a : F.Gamma hZ hZP)
    {L : Subgroup S} (hZL : Z ≤ L) (hLP : L ≤ P) : L →* L where
  toFun x := ⟨(a.val.val ⟨x.val, hLP x.property⟩).val,
    F.gamma_preserves_overgroup hZ hZP a hZL hLP x⟩
  map_one' := by
    apply Subtype.ext
    change (a.val.val (1 : P)).val = (1 : S)
    exact congrArg (fun q : P => q.val) (map_one a.val.val)
  map_mul' x y := by
    apply Subtype.ext
    change (a.val.val (⟨x.val, hLP x.property⟩ * ⟨y.val, hLP y.property⟩)).val =
      (a.val.val ⟨x.val, hLP x.property⟩).val * (a.val.val ⟨y.val, hLP y.property⟩).val
    exact congrArg (fun q : P => q.val) (map_mul a.val.val _ _)

def gammaRestrictionEquiv (a : F.Gamma hZ hZP)
    {L : Subgroup S} (hZL : Z ≤ L) (hLP : L ≤ P) : L ≃* L :=
  { F.gammaRestrictionHom hZ hZP a hZL hLP with
    invFun := F.gammaRestrictionHom hZ hZP a⁻¹ hZL hLP
    left_inv := by
      intro x
      apply Subtype.ext
      change (a.val.val.symm (a.val.val ⟨x.val, hLP x.property⟩)).val = x.val
      exact congrArg (fun q : P => q.val) (a.val.val.symm_apply_apply ⟨x.val, hLP x.property⟩)
    right_inv := by
      intro x
      apply Subtype.ext
      change (a.val.val (a.val.val.symm ⟨x.val, hLP x.property⟩)).val = x.val
      exact congrArg (fun q : P => q.val) (a.val.val.apply_symm_apply ⟨x.val, hLP x.property⟩) }

theorem gammaRestriction_allowed (a : F.Gamma hZ hZP)
    {L : Subgroup S} (hZL : Z ≤ L) (hLP : L ≤ P) :
    F.IsHom (F.gammaRestrictionEquiv hZ hZP a hZL hLP).toMonoidHom := by
  let f := a.val.val.toMonoidHom.comp (subgroupInclusion L P hLP)
  have hf : F.IsHom f := F.comp_mem _ _ (F.inclusion_mem hLP) a.val.property
  apply F.codomain_restrict_mem f hf hLP
    (F.gammaRestrictionEquiv hZ hZP a hZL hLP).toMonoidHom
  ext x
  rfl

def gammaRestriction (a : F.Gamma hZ hZP)
    {L : Subgroup S} (hZL : Z ≤ L) (hLP : L ≤ P) [(Z.subgroupOf L).Normal] :
    F.Gamma hZ hZL := by
  let e := F.gammaRestrictionEquiv hZ hZP a hZL hLP
  let aL : F.automorphismSubgroup L := ⟨e, F.gammaRestriction_allowed hZ hZP a hZL hLP⟩
  refine ⟨aL, ?_⟩
  apply (quotient_kernel_iff (F.automorphismSubgroup L).subtype (Z.subgroupOf L)
    (F.central_aut_fixed hZ hZL) aL).mpr
  intro x
  exact F.gamma_modZ hZ hZP a ⟨x.val, hLP x.property⟩

theorem gamma_inclusion_square (a : F.Gamma hZ hZP)
    {L : Subgroup S} (hZL : Z ≤ L) (hLP : L ≤ P) [(Z.subgroupOf L).Normal] :
    F.toOrbit.map (F.inclusion hLP) ≫ (F.automorphismToOrbitAut P a.val).hom =
      (F.automorphismToOrbitAut L (F.gammaRestriction hZ hZP a hZL hLP).val).hom ≫
        F.toOrbit.map (F.inclusion hLP) := by
  change F.toOrbit.map _ ≫ F.toOrbit.map _ = F.toOrbit.map _ ≫ F.toOrbit.map _
  rw [← F.toOrbit.map_comp, ← F.toOrbit.map_comp]
  congr 1

end Sharpness.FusionSystem
