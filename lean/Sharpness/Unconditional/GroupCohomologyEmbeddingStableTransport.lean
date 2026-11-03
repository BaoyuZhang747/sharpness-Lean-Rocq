import Sharpness.Unconditional.FiniteGroupCohomologyStableComparison
import Sharpness.Unconditional.FusionSystemGroupTransportFinite

/-! Transport the actual stable-element condition to the literal domain of a
group embedding. All comparison maps are native cohomological restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G T A : Type u} [CommRing R] [Group G]
    [Group T] [Finite T] [AddCommGroup A] [Module R A]

private theorem embedding_pull_comp_apply {U V W : Type u}
    [Group U] [Group V] [Group W] (f : U →* V) (g : V →* W)
    (n : ℕ) (x : value R W A n) :
    pull f n (pull g n x) = pull (g.comp f) n x :=
  congrArg (fun z => z.hom x) (pull_comp (R := R) (A := A) f g n).symm

theorem finiteGroupTransport_mem_fusionStable_iff (H : Subgroup G) (e : T ≃* H)
    (n : ℕ) (x : value R H A n) :
    pull (e.toMonoidHom.comp (⊤ : Subgroup T).subtype) n x ∈
      ((finiteGroupFusion H).groupTransport e).stableElements
        (((finiteGroupFusion H).groupTransport e).nativeGroupCohomologyMackey
          (R := R) (A := A) n) ↔
      x ∈ stableElements (R := R) (A := A) H n := by
  let F := (finiteGroupFusion H).groupTransport e
  refine (F.mem_ordinaryStableElements_iff_raw_toTop (F.cohomologyTransferLaws n) _).trans ?_
  rw [mem_stableElements_iff_partial_conjugations]
  constructor
  · intro hx P f g hf
    let Q := P.map e.symm.toMonoidHom
    let j : P ≃* Q := e.symm.subgroupMap P
    let t : Q →* (⊤ : Subgroup T) := Subgroup.topEquiv.symm.toMonoidHom.comp
      (e.symm.toMonoidHom.comp (f.comp j.symm.toMonoidHom))
    have ht : F.IsHom t := by
      apply (groupTransport_finiteGroupFusion_isHom_iff H e t).mpr
      refine ⟨g, ?_⟩
      intro y
      have hv : ((j.symm y : P) : H) = e (y : T) := rfl
      simpa [t, hv] using hf (j.symm y)
    have h := hx ⟨Q⟩ ⟨t, ht⟩
    change pull t n (pull (e.toMonoidHom.comp (⊤ : Subgroup T).subtype) n x) =
      pull (subgroupInclusion Q ⊤ le_top) n
        (pull (e.toMonoidHom.comp (⊤ : Subgroup T).subtype) n x) at h
    have hp := congrArg (fun z => pull (R := R) (A := A) j.toMonoidHom n z) h
    simp only [embedding_pull_comp_apply] at hp
    have hleft : ((e.toMonoidHom.comp (⊤ : Subgroup T).subtype).comp t).comp
        j.toMonoidHom = f := by
      ext y
      simp [t]
    have hright : ((e.toMonoidHom.comp (⊤ : Subgroup T).subtype).comp
        (subgroupInclusion Q ⊤ le_top)).comp j.toMonoidHom = P.subtype := by
      ext y
      change (e (e.symm (y : H)) : G) = ((y : H) : G)
      rw [e.apply_symm_apply]
    rwa [hleft, hright] at hp
  · intro hx Q f
    obtain ⟨g, hg⟩ := (groupTransport_finiteGroupFusion_isHom_iff H e f.val).mp f.property
    let P := Q.subgroup.map e.toMonoidHom
    let j : Q.subgroup ≃* P := e.subgroupMap Q.subgroup
    let t : P →* H := e.toMonoidHom.comp
      ((⊤ : Subgroup T).subtype.comp (f.val.comp j.symm.toMonoidHom))
    have ht : ∀ y : P, (t y : G) = g * ((y : H) : G) * g⁻¹ := by
      intro y
      have hv : e ((j.symm y : Q.subgroup) : T) = (y : H) := e.apply_symm_apply _
      simpa [t, hv] using hg (j.symm y)
    have h := congrArg (fun z => pull (R := R) (A := A) j.toMonoidHom n z)
      (hx P t g ht)
    simp only [embedding_pull_comp_apply] at h
    change pull f.val n (pull (e.toMonoidHom.comp (⊤ : Subgroup T).subtype) n x) =
      pull (subgroupInclusion Q.subgroup ⊤ le_top) n
        (pull (e.toMonoidHom.comp (⊤ : Subgroup T).subtype) n x)
    simp only [embedding_pull_comp_apply]
    have hleft : t.comp j.toMonoidHom =
        (e.toMonoidHom.comp (⊤ : Subgroup T).subtype).comp f.val := by
      ext y
      simp [t]
    have hright : P.subtype.comp j.toMonoidHom =
        (e.toMonoidHom.comp (⊤ : Subgroup T).subtype).comp
          (subgroupInclusion Q.subgroup ⊤ le_top) := rfl
    rwa [hleft, hright] at h

end Sharpness.OrdinaryCohomology
