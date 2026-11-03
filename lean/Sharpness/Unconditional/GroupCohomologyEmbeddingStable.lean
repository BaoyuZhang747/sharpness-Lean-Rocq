import Sharpness.Unconditional.GroupCohomologyEmbeddingStableTransport

/-! Native group cohomology is the fusion-stable module on the literal domain
of an injective group embedding of invertible index. The forward map is the
actual restriction along the embedding and the top-subgroup inclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G T A : Type u} [CommRing R] [Group G] [Finite G]
    [Group T] [Finite T] [AddCommGroup A] [Module R A]

def finiteGroupTransportStableComparison (H : Subgroup G) (e : T ≃* H) (n : ℕ) :
    stableElements (R := R) (A := A) H n ≃ₗ[R]
      ((finiteGroupFusion H).groupTransport e).stableElements
        (((finiteGroupFusion H).groupTransport e).nativeGroupCohomologyMackey
          (R := R) (A := A) n) := by
  let k := (pullIso (R := R) (A := A)
    ((Subgroup.topEquiv : (⊤ : Subgroup T) ≃* T).trans e) n).toLinearEquiv
  let q := ((finiteGroupFusion H).groupTransport e).stableElements
    (((finiteGroupFusion H).groupTransport e).nativeGroupCohomologyMackey
      (R := R) (A := A) n)
  exact
    { toFun := fun x => ⟨k x.1, (finiteGroupTransport_mem_fusionStable_iff H e n x.1).mpr x.2⟩
      invFun := fun y => ⟨k.symm y.1,
        (finiteGroupTransport_mem_fusionStable_iff H e n (k.symm y.1)).mp (by
          change k (k.symm y.1) ∈ q
          rw [k.apply_symm_apply]
          exact y.2)⟩
      left_inv := fun x => Subtype.ext (k.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (k.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (k.map_add x.1 y.1)
      map_smul' := fun r x => Subtype.ext (k.map_smul r x.1) }

@[simp] theorem finiteGroupTransportStableComparison_apply
    (H : Subgroup G) (e : T ≃* H) (n : ℕ)
    (x : stableElements (R := R) (A := A) H n) :
    (finiteGroupTransportStableComparison H e n x).1 =
      pull (e.toMonoidHom.comp (⊤ : Subgroup T).subtype) n x.1 := rfl

def finiteGroupFusionAlongCohomologyStableIso (i : T →* G) (hi : Function.Injective i)
    (n : ℕ) (hindex : IsUnit (i.range.index : R)) :
    value R G A n ≅ ModuleCat.of R
      ((finiteGroupFusionAlong i hi).stableElements
        ((finiteGroupFusionAlong i hi).nativeGroupCohomologyMackey
          (R := R) (A := A) n)) :=
  (restrictionStableElementsEquiv i.range n hindex).toModuleIso ≪≫
    (finiteGroupTransportStableComparison i.range (MonoidHom.ofInjective hi) n).toModuleIso

@[simp] theorem finiteGroupFusionAlongCohomologyStableIso_apply
    (i : T →* G) (hi : Function.Injective i) (n : ℕ) (hindex : IsUnit (i.range.index : R))
    (x : value R G A n) :
    ((finiteGroupFusionAlongCohomologyStableIso i hi n hindex).hom x).1 =
      pull (i.comp (⊤ : Subgroup T).subtype) n x := by
  change (pull i.range.subtype n ≫
    pull ((MonoidHom.ofInjective hi).toMonoidHom.comp (⊤ : Subgroup T).subtype) n).hom x = _
  rw [← pull_comp]
  rfl

/-- The comparison's forward map is literally restriction, including the
native top-subgroup chart. -/
@[reassoc] theorem finiteGroupFusionAlongCohomologyStableIso_hom_subtype
    (i : T →* G) (hi : Function.Injective i) (n : ℕ) (hindex : IsUnit (i.range.index : R)) :
    (finiteGroupFusionAlongCohomologyStableIso (R := R) (A := A) i hi n hindex).hom ≫
      ModuleCat.ofHom ((finiteGroupFusionAlong i hi).stableElements
        ((finiteGroupFusionAlong i hi).nativeGroupCohomologyMackey
          (R := R) (A := A) n)).subtype =
      pull (i.comp (⊤ : Subgroup T).subtype) n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact finiteGroupFusionAlongCohomologyStableIso_apply i hi n hindex

end Sharpness.OrdinaryCohomology
