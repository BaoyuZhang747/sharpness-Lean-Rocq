import Sharpness.Unconditional.NormalizerHigherLimitComparisonGroupsStabilizer

/-! Transport of an actual strict centric chain along a fusion isomorphism
of its top subgroup. The transported entries are actual image subgroups. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricChain
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (σ : F.CentricChain) {Q : Subgroup S} (e : σ.topSubgroup ≃* Q)
    (he : F.IsHom e.toMonoidHom)

def transportArrow (i : Fin (σ.length + 1)) :
    (⟨σ.subgroup i⟩ : F.Object) ⟶ ⟨Q⟩ :=
  F.inclusion (σ.subgroup_mono (Fin.le_last i)) ≫ (F.isoOfMulEquiv e he).hom

theorem transportArrow_image_mem (i : Fin (σ.length + 1)) (x : σ.topSubgroup) :
    (e x).val ∈ F.imageSubgroup (σ.transportArrow e he i) ↔ x.val ∈ σ.subgroup i := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : e ⟨y.val, σ.subgroup_mono (Fin.le_last i) y.property⟩ = e x :=
      Subtype.ext hy
    have hx := congrArg Subtype.val (e.injective hy')
    exact hx ▸ y.property
  · intro hx
    exact ⟨⟨x.val, hx⟩, rfl⟩

def transport : F.CentricChain where
  length := σ.length
  entry i := ⟨F.imageSubgroup (σ.transportArrow e he i), by
    let f := σ.transportArrow e he i
    have hinj : Function.Injective (Q.subtype.comp f.val) :=
      Subtype.val_injective.comp (F.injective f.val f.property)
    let a := MonoidHom.ofInjective hinj
    exact F.isoSystem.centricIn_of_iso a (F.toImage f).property (σ.centric i)⟩
  strict := by
    intro i j hij
    refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨⟨x.val, σ.subgroup_mono hij.le x.property⟩, rfl⟩
    · intro hji
      apply (not_le_of_gt (σ.subgroup_strict hij))
      intro x hx
      let xt : σ.topSubgroup := ⟨x, σ.subgroup_mono (Fin.le_last j) hx⟩
      exact (σ.transportArrow_image_mem e he i xt).mp
        (hji ((σ.transportArrow_image_mem e he j xt).mpr hx))

theorem transport_subgroup (i : Fin (σ.length + 1)) :
    (σ.transport e he).subgroup i = F.imageSubgroup (σ.transportArrow e he i) := rfl

theorem transport_mem (i : Fin (σ.length + 1)) (x : σ.topSubgroup) :
    x.val ∈ σ.subgroup i ↔ (e x).val ∈ (σ.transport e he).subgroup i :=
  (σ.transportArrow_image_mem e he i x).symm

theorem transport_top : (σ.transport e he).topSubgroup = Q := by
  apply le_antisymm (F.image_le (σ.transportArrow e he (Fin.last σ.length)))
  intro x hx
  let y := e.symm ⟨x, hx⟩
  refine ⟨y, ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

/-- The raw top isomorphism, with its actual image-subgroup target. -/
def transportTopIso : σ.topRawObject ≅ (σ.transport e he).topRawObject :=
  F.imageIso (σ.transportArrow e he (Fin.last σ.length))

theorem transportTopIso_apply (x : σ.topSubgroup) :
    ((σ.transportTopIso e he).hom.val x).val = (e x).val := rfl

def transportConjugacy : Conjugacy σ (σ.transport e he) where
  indices := OrderIso.refl _
  topIso := σ.transportTopIso e he
  maps i x := σ.transport_mem e he i x

end Sharpness.FusionSystem.CentricChain
