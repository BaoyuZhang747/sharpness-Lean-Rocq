import Sharpness.Unconditional.CentralizerCoverLift

/-! The concrete lifts are strongly cocartesian: their universal property
follows from the inverse restriction equations and the underlying orbit
isomorphism. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S) (p : ℕ)

namespace CentralizerCover
variable {F p} (A B D : F.CentralizerCover p)

theorem factor_through_orbit_iso (f : A ⟶ B) [IsIso f.val] (g : A ⟶ D)
    (η : (⟨D.elementary⟩ : F.Object) ⟶ ⟨B.elementary⟩)
    (hη : A.inverseRestriction D g = η ≫ A.inverseRestriction B f) :
    ∃! h : B ⟶ D, B.inverseRestriction D h = η ∧ f ≫ h = g := by
  obtain ⟨f₀, hf₀, _⟩ := f.property
  obtain ⟨g₀, hg₀, _⟩ := g.property
  have hcard : Nat.card A.centric.obj.as.subgroup = Nat.card B.centric.obj.as.subgroup :=
    le_antisymm (F.orbitOrder_mono f.val.hom) (F.orbitOrder_mono (inv f.val).hom)
  let e := F.isoOfEqualOrder f₀ hcard
  let eC : A.centric ≅ B.centric := ObjectProperty.isoMk _ (F.toOrbit.mapIso e)
  have heC : eC.hom = f.val := InducedCategory.hom_ext hf₀
  let h₀ : B.centric.obj.as ⟶ D.centric.obj.as := e.inv ≫ g₀
  have h₀point : ∀ d : D.elementary,
      (h₀.val ⟨(η.val d).val, B.le_subgroup (η.val d).property⟩).val = d.val := by
    intro d
    let b := η.val d
    let a := (A.inverseRestriction B f).val b
    have hfa := A.inverseRestriction_spec B f f₀ hf₀ b
    have hi : e.inv.val ⟨b.val, B.le_subgroup b.property⟩ =
        ⟨a.val, A.le_subgroup a.property⟩ := by
      apply F.injective f₀.val f₀.property
      have heinv := congrArg
        (fun k : B.centric.obj.as ⟶ B.centric.obj.as =>
          k.val ⟨b.val, B.le_subgroup b.property⟩) e.inv_hom_id
      change f₀.val (e.inv.val ⟨b.val, B.le_subgroup b.property⟩) =
        ⟨b.val, B.le_subgroup b.property⟩ at heinv
      exact heinv.trans (Subtype.ext hfa).symm
    have hηd : (A.inverseRestriction D g).val d = a :=
      congrArg (fun k : (⟨D.elementary⟩ : F.Object) ⟶ ⟨A.elementary⟩ => k.val d) hη
    have ha : (⟨((A.inverseRestriction D g).val d).val,
        A.le_subgroup ((A.inverseRestriction D g).val d).property⟩ :
        A.centric.obj.as.subgroup) = ⟨a.val, A.le_subgroup a.property⟩ :=
      Subtype.ext (congrArg (fun a : A.elementary => a.val) hηd)
    have hg := A.inverseRestriction_spec D g g₀ hg₀ d
    change (g₀.val (e.inv.val ⟨b.val, B.le_subgroup b.property⟩)).val = d.val
    rw [hi, ← ha]
    exact hg
  have hh₀ : F.toOrbit.map h₀ = (eC.inv ≫ g.val).hom := by
    rw [F.toOrbit.map_comp, hg₀]
    rfl
  let h : B ⟶ D := ⟨eC.inv ≫ g.val, h₀, hh₀, fun d => ⟨η.val d, h₀point d⟩⟩
  have hh : B.inverseRestriction D h = η := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro d
    exact B.inverseRestriction_unique D h d (η.val d) h₀ hh₀ (h₀point d)
  have hfac : f ≫ h = g := by
    apply Subtype.ext
    change f.val ≫ (eC.inv ≫ g.val) = g.val
    rw [← heC, Iso.hom_inv_id_assoc]
  refine ⟨h, ⟨hh, hfac⟩, ?_⟩
  intro h' hh'
  apply Subtype.ext
  apply (cancel_epi f.val).mp
  exact congrArg Subtype.val (hh'.2.trans hfac.symm)

end CentralizerCover

theorem centralizerCover_stronglyCocartesian
    {A B : F.CentralizedCentralizerCover p} (φ : A ⟶ B) [IsIso φ.hom.val] :
    (F.centralizerCoverProjection p).IsStronglyCocartesian
      ((F.centralizerCoverProjection p).map φ) φ := by
  refine ⟨?_⟩
  intro D γ ψ hψ
  have hq := IsHomLift.eq_of_isHomLift (F.centralizerCoverProjection p)
    ((F.centralizerCoverProjection p).map φ ≫ γ) ψ
  have hη : A.obj.inverseRestriction D.obj ψ.hom =
      γ.unop.hom ≫ A.obj.inverseRestriction B.obj φ.hom := by
    have hh := congrArg (fun k => k.unop.hom) hq
    exact hh.symm
  obtain ⟨χ₀, ⟨hχ₀, hfac⟩, huniq⟩ :=
    A.obj.factor_through_orbit_iso B.obj D.obj φ.hom ψ.hom γ.unop.hom hη
  let χ : B ⟶ D := ObjectProperty.homMk χ₀
  have hχ : (F.centralizerCoverProjection p).map χ = γ := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    exact hχ₀
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hχ]
    infer_instance
  · exact InducedCategory.hom_ext hfac
  · intro χ' hχ'
    apply InducedCategory.hom_ext
    apply huniq
    refine ⟨?_, ?_⟩
    · have hh := @IsHomLift.eq_of_isHomLift _ _ _ _ (F.centralizerCoverProjection p)
        B D γ χ' hχ'.1
      exact congrArg (fun k => k.unop.hom) hh.symm
    · exact congrArg (fun k => k.hom) hχ'.2

end Sharpness.FusionSystem
