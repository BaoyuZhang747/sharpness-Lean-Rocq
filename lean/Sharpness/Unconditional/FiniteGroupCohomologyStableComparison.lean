import Sharpness.Unconditional.GroupCohomologySylowStableElements
import Sharpness.Unconditional.GroupCohomologyIsoTransport
import Sharpness.Unconditional.FiniteGroupFusion
import Sharpness.Manuscript.CohomologyUnconditional
import Sharpness.StableToTopCondition
import Sharpness.NativeCentricStable

/-! Identify the actual finite-group stable elements with the native fusion
Mackey stable elements, including the top-subgroup transport. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G A : Type u} [CommRing R] [Group G] [Finite G]
  [AddCommGroup A] [Module R A] (S : Subgroup G) (n : ℕ)

theorem finiteGroup_mem_fusionStable_iff (x : value R S A n) :
    pull (⊤ : Subgroup S).subtype n x ∈
        (finiteGroupFusion S).stableElements
          ((finiteGroupFusion S).nativeGroupCohomologyMackey (R := R) (A := A) n) ↔
      x ∈ stableElements (R := R) (A := A) S n := by
  let F := finiteGroupFusion S
  refine (F.mem_ordinaryStableElements_iff_raw_toTop (F.cohomologyTransferLaws n) _).trans ?_
  rw [mem_stableElements_iff_partial_conjugations]
  constructor
  · intro hx P f g hf
    let t : P →* (⊤ : Subgroup S) := (Subgroup.topEquiv.symm.toMonoidHom).comp f
    let a : (⟨P⟩ : F.Object) ⟶ (⟨⊤⟩ : F.Object) := ⟨t, g, hf⟩
    have h := hx ⟨P⟩ a
    change (pull (⊤ : Subgroup S).subtype n ≫ pull t n).hom x =
      (pull (⊤ : Subgroup S).subtype n ≫
        pull (F.inclusion (show P ≤ ⊤ from le_top)).val n).hom x at h
    rw [← pull_comp, ← pull_comp] at h
    exact h
  · intro hx P f
    obtain ⟨g, hg⟩ := f.property
    have h := hx P.subgroup ((⊤ : Subgroup S).subtype.comp f.val) g hg
    change (pull (⊤ : Subgroup S).subtype n ≫ pull f.val n).hom x =
      (pull (⊤ : Subgroup S).subtype n ≫
        pull (F.inclusion (show P.subgroup ≤ ⊤ from le_top)).val n).hom x
    rw [← pull_comp, ← pull_comp]
    exact h

def finiteGroupStableComparison :
    stableElements (R := R) (A := A) S n ≃ₗ[R]
      (finiteGroupFusion S).stableElements
      ((finiteGroupFusion S).nativeGroupCohomologyMackey (R := R) (A := A) n) := by
  let e := (pullIso (R := R) (A := A) (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S) n).toLinearEquiv
  let q := (finiteGroupFusion S).stableElements
    ((finiteGroupFusion S).nativeGroupCohomologyMackey (R := R) (A := A) n)
  exact
    { toFun := fun x => ⟨e x.1, (finiteGroup_mem_fusionStable_iff S n x.1).mpr x.2⟩
      invFun := fun y => ⟨e.symm y.1, (finiteGroup_mem_fusionStable_iff S n (e.symm y.1)).mp (by
        change e (e.symm y.1) ∈ q
        rw [e.apply_symm_apply]
        exact y.2)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_add' := fun x y => Subtype.ext (e.map_add x.1 y.1)
      map_smul' := fun r x => Subtype.ext (e.map_smul r x.1) }

@[simp] theorem finiteGroupStableComparison_apply
    (x : stableElements (R := R) (A := A) S n) :
    (finiteGroupStableComparison S n x).1 = pull (⊤ : Subgroup S).subtype n x.1 := rfl

def finiteGroupCohomologyFusionStableIso (hindex : IsUnit (S.index : R)) :
    value R G A n ≅ ModuleCat.of R
      ((finiteGroupFusion S).stableElements
        ((finiteGroupFusion S).nativeGroupCohomologyMackey (R := R) (A := A) n)) :=
  (restrictionStableElementsEquiv S n hindex).toModuleIso ≪≫
    (finiteGroupStableComparison S n).toModuleIso

end Sharpness.OrdinaryCohomology
