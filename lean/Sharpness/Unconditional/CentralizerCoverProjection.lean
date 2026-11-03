import Sharpness.Unconditional.CentralizerCoverCentralized

/-! The projection of the fully centralized cover to the opposite elementary
fusion category, given by actual inverse restrictions of orbit morphisms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite

variable {S : Type u} [Group S] (F : FusionSystem S) (p : ℕ)

namespace CentralizerCover
variable {F p} (A B : F.CentralizerCover p)

theorem elementary_value_of_orbit_eq
    {f g : A.centric.obj.as ⟶ B.centric.obj.as}
    (hfg : F.toOrbit.map f = F.toOrbit.map g)
    (a : A.centric.obj.as.subgroup) (b : B.elementary)
    (hab : (f.val a).val = b.val) : (g.val a).val = b.val := by
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff f g).mp hfg
  have hc := (Subgroup.mem_centralizer_iff.mp (B.centralizes b.property)) r.val r.property
  have hgr := congrArg Subtype.val (hr a)
  change (g.val a).val = r.val⁻¹ * (f.val a).val * r.val at hgr
  rw [hgr, hab, mul_assoc, ← hc, inv_mul_cancel_left]

theorem exists_inverseRestriction (f : A.centric.obj.as ⟶ B.centric.obj.as)
    (hf : A.Covers B f) :
    ∃ r : B.elementary →* A.elementary, F.IsHom r ∧
      ∀ b : B.elementary,
        (f.val ⟨(r b).val, A.le_subgroup (r b).property⟩).val = b.val := by
  let D := F.imageSubgroup f
  let e : A.centric.obj.as.subgroup ≃* D := MonoidHom.ofInjective
    (Subtype.val_injective.comp (F.injective f.val f.property))
  have he : F.IsHom e.toMonoidHom := (F.toImage f).property
  have hED : B.elementary ≤ D := by
    intro b hb
    obtain ⟨a, ha⟩ := hf ⟨b, hb⟩
    exact ⟨⟨a.val, A.le_subgroup a.property⟩, ha⟩
  let r₀ : B.elementary →* A.centric.obj.as.subgroup :=
    e.symm.toMonoidHom.comp (subgroupInclusion _ _ hED)
  have hr₀ : F.IsHom r₀ :=
    F.comp_mem _ _ (F.inclusion_mem hED) (F.inverse_mem e he)
  have hr₀val : ∀ b : B.elementary, (f.val (r₀ b)).val = b.val := by
    intro b
    exact congrArg Subtype.val (e.apply_symm_apply ⟨b.val, hED b.property⟩)
  have hr₀mem : ∀ b : B.elementary, (r₀ b).val ∈ A.elementary := by
    intro b
    obtain ⟨a, ha⟩ := hf b
    have heq : r₀ b = ⟨a.val, A.le_subgroup a.property⟩ :=
      F.injective f.val f.property (Subtype.ext ((hr₀val b).trans ha.symm))
    rw [heq]
    exact a.property
  let r : B.elementary →* A.elementary :=
    (A.centric.obj.as.subgroup.subtype.comp r₀).codRestrict A.elementary hr₀mem
  refine ⟨r, F.codomain_restrict_mem r₀ hr₀ A.le_subgroup r (by ext b; rfl), ?_⟩
  intro b
  exact hr₀val b

def inverseRestriction (f : A ⟶ B) :
    (⟨B.elementary⟩ : F.Object) ⟶ ⟨A.elementary⟩ := by
  let g := f.property.choose
  have hg := f.property.choose_spec
  let r := (A.exists_inverseRestriction B g hg.2).choose
  exact ⟨r, (A.exists_inverseRestriction B g hg.2).choose_spec.1⟩

theorem inverseRestriction_spec (f : A ⟶ B)
    (g : A.centric.obj.as ⟶ B.centric.obj.as) (hg : F.toOrbit.map g = f.val.hom)
    (b : B.elementary) :
    (g.val ⟨((A.inverseRestriction B f).val b).val,
      A.le_subgroup ((A.inverseRestriction B f).val b).property⟩).val = b.val := by
  let g₀ := f.property.choose
  have hg₀ := f.property.choose_spec
  apply A.elementary_value_of_orbit_eq B (hg₀.1.trans hg.symm)
  exact (A.exists_inverseRestriction B g₀ hg₀.2).choose_spec.2 b

theorem inverseRestriction_unique (f : A ⟶ B) (b : B.elementary)
    (a : A.elementary) (g : A.centric.obj.as ⟶ B.centric.obj.as)
    (hg : F.toOrbit.map g = f.val.hom)
    (ha : (g.val ⟨a.val, A.le_subgroup a.property⟩).val = b.val) :
    (A.inverseRestriction B f).val b = a := by
  have h := F.injective g.val g.property
    (Subtype.ext ((A.inverseRestriction_spec B f g hg b).trans ha.symm))
  exact Subtype.ext (congrArg (fun x : A.centric.obj.as.subgroup => x.val) h)

theorem inverseRestriction_id :
    A.inverseRestriction A (𝟙 A) = 𝟙 (⟨A.elementary⟩ : F.Object) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro a
  exact A.inverseRestriction_unique A (𝟙 A) a a (𝟙 A.centric.obj.as)
    (F.toOrbit.map_id _) rfl

theorem inverseRestriction_comp {D : F.CentralizerCover p} (f : A ⟶ B) (g : B ⟶ D) :
    A.inverseRestriction D (f ≫ g) =
      B.inverseRestriction D g ≫ A.inverseRestriction B f := by
  obtain ⟨f₀, hf₀, _⟩ := f.property
  obtain ⟨g₀, hg₀, _⟩ := g.property
  apply Subtype.ext
  apply MonoidHom.ext
  intro d
  apply A.inverseRestriction_unique D (f ≫ g) d _ (f₀ ≫ g₀)
  · rw [F.toOrbit.map_comp, hf₀, hg₀]
    rfl
  · have hf := A.inverseRestriction_spec B f f₀ hf₀
      ((B.inverseRestriction D g).val d)
    have hg := B.inverseRestriction_spec D g g₀ hg₀ d
    have hf' : f₀.val
        ⟨((A.inverseRestriction B f).val ((B.inverseRestriction D g).val d)).val,
          A.le_subgroup ((A.inverseRestriction B f).val
            ((B.inverseRestriction D g).val d)).property⟩ =
        ⟨((B.inverseRestriction D g).val d).val,
          B.le_subgroup ((B.inverseRestriction D g).val d).property⟩ := Subtype.ext hf
    exact (congrArg (fun b : B.centric.obj.as.subgroup => (g₀.val b).val) hf').trans hg

end CentralizerCover

variable [Finite S]

def centralizedCoverElementary (A : F.CentralizedCentralizerCover p) : F.ElementaryCategory p :=
  { obj := ⟨A.obj.elementary⟩
    property := ⟨A.obj.nontrivial, (by
      intro x y
      apply Subtype.ext
      exact ((Subgroup.mem_centralizer_iff.mp (A.obj.centralizes x.property))
        y.val (A.obj.le_subgroup y.property)).symm),
      (by intro x; exact Subtype.ext (A.obj.exponent x.val x.property)), A.property⟩ }

def centralizerCoverProjection : F.CentralizedCentralizerCover p ⥤ (F.ElementaryCategory p)ᵒᵖ where
  obj A := op (F.centralizedCoverElementary p A)
  map {A B} f := (ObjectProperty.homMk (A.obj.inverseRestriction B.obj f.hom)).op
  map_id A := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    exact A.obj.inverseRestriction_id
  map_comp {A B D} f g := by
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    exact A.obj.inverseRestriction_comp B.obj f.hom g.hom

end Sharpness.FusionSystem
