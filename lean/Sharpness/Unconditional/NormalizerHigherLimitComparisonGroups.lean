import Sharpness.Unconditional.NormalizerSubdivisionCommaLifts
import Sharpness.Unconditional.KNormalizationProperties

/-! The actual linking-automorphism projection and its center kernel.
The kernel is a normal subgroup isomorphic to the center of the underlying
subgroup; its image is not asserted to be central in the full automorphism
group. Finiteness and all maps follow from the linking-system axioms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

/-- Projection of a linking automorphism to its actual fusion automorphism. -/
def linkingAutProjection (P : L.Object) : Aut P →* F.automorphismSubgroup P.as.val where
  toFun a := ⟨{
    toFun := (L.projection.map a.hom).val
    invFun := (L.projection.map a.inv).val
    left_inv x := by
      have h := congrArg (fun f => L.projection.map f) a.hom_inv_id
      rw [L.projection.map_comp, L.projection.map_id] at h
      exact congrArg (fun f => f.val x) h
    right_inv x := by
      have h := congrArg (fun f => L.projection.map f) a.inv_hom_id
      rw [L.projection.map_comp, L.projection.map_id] at h
      exact congrArg (fun f => f.val x) h
    map_mul' := (L.projection.map a.hom).val.map_mul },
    (L.projection.map a.hom).property⟩
  map_one' := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change (L.projection.map (𝟙 P)).val x = x
    rw [L.projection.map_id]
    rfl
  map_mul' a b := by
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change (L.projection.map (b.hom ≫ a.hom)).val x = _
    rw [L.projection.map_comp]
    rfl

omit [Finite S] in
theorem linkingAutProjection_apply (P : L.Object) (a : Aut P) (x : P.as.val) :
    (L.linkingAutProjection P a).val x = (L.projection.map a.hom).val x := rfl

omit [Finite S] in
theorem linkingAutProjection_surjective (P : L.Object) :
    Function.Surjective (L.linkingAutProjection P) := by
  intro a
  let e := F.isoOfMulEquiv a.val a.property
  obtain ⟨t, ht⟩ := L.normalizer_exists_linkingIso (P := P) (Q := P) e
  refine ⟨t, ?_⟩
  apply Subtype.ext
  apply MulEquiv.ext
  intro x
  change (L.projection.map t.hom).val x = a.val x
  rw [ht]
  rfl

omit [Finite S] in
theorem linkingAutProjection_eq_one_iff (P : L.Object) (a : Aut P) :
    L.linkingAutProjection P a = 1 ↔ L.projection.map a.hom = 𝟙 (L.projection.obj P) := by
  constructor
  · intro h
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact congrArg (fun b : F.automorphismSubgroup P.as.val => b.val x) h
  · intro h
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact congrArg (fun f => f.val x) h

theorem distinguished_center_projection (P : L.Object) (z : Subgroup.center P.as.val) :
    L.linkingAutProjection P (L.distinguished P z.val) = 1 := by
  apply (L.linkingAutProjection_eq_one_iff P _).mpr
  rw [L.project_distinguished]
  apply Subtype.ext
  change (F.inner (L.toLinkingCategoryData.rawObject P) z.val⁻¹).val = MonoidHom.id P.as.val
  apply MonoidHom.ext
  intro x
  change (z.val⁻¹)⁻¹ * (show P.as.val from x) * z.val⁻¹ = (show P.as.val from x)
  rw [inv_inv, ← (Subgroup.mem_center_iff.mp z.property) x, mul_assoc, mul_inv_cancel, mul_one]

/-- The center embeds onto the literal kernel, with the distinguished map. -/
def linkingCenterToKernel (P : L.Object) :
    Subgroup.center P.as.val →* (L.linkingAutProjection P).ker where
  toFun z := ⟨L.distinguished P z.val, L.distinguished_center_projection P z⟩
  map_one' := Subtype.ext (map_one (L.distinguished P))
  map_mul' z w := Subtype.ext (map_mul (L.distinguished P) z.val w.val)

theorem linkingCenterToKernel_bijective (P : L.Object) :
    Function.Bijective (L.linkingCenterToKernel P) := by
  constructor
  · intro z w h
    apply Subtype.ext
    exact L.distinguished_injective P (congrArg Subtype.val h)
  · intro a
    have hp := (L.linkingAutProjection_eq_one_iff P a.val).mp a.property
    have hp' : L.projection.map (𝟙 P) = L.projection.map a.val.hom :=
      (L.projection.map_id P).trans hp.symm
    obtain ⟨z, hz, _⟩ := (L.central_fiber (𝟙 P) a.val.hom).mp hp'
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply Iso.ext
    change (L.distinguished P z.val).hom = a.val.hom
    simpa only [Category.comp_id] using hz

def linkingCenterKernelEquiv (P : L.Object) :
    Subgroup.center P.as.val ≃* (L.linkingAutProjection P).ker :=
  MulEquiv.ofBijective (L.linkingCenterToKernel P) (L.linkingCenterToKernel_bijective P)

instance linkingAutFinite (P : L.Object) : Finite (Aut P) := by
  letI : Finite (L.linkingAutProjection P).ker :=
    Finite.of_equiv (Subgroup.center P.as.val) (L.linkingCenterKernelEquiv P).toEquiv
  exact (L.linkingAutProjection P).finite_iff_finite_ker_range.mpr
    ⟨inferInstance, inferInstance⟩

instance chainAutFinite (σ : F.CentricChain) : Finite (L.ChainAut σ) := inferInstance

theorem linkingAutProjection_kernel_isPGroup (p : ℕ) (hS : IsPGroup p S)
    (P : L.Object) : IsPGroup p (L.linkingAutProjection P).ker :=
  ((hS.to_subgroup P.as.val).to_subgroup (Subgroup.center P.as.val)).of_equiv
    (L.linkingCenterKernelEquiv P)

end Sharpness.FusionSystem.CentricLinkingSystem
