import Sharpness.CentralizerDefinitions
import Sharpness.ReferenceInputs

/-! The finite category of centric subgroups equipped with nontrivial central
elementary abelian subgroups. Its arrows are actual fusion-orbit arrows whose
inverse restrictions carry the target elementary subgroup into the source. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] (F : FusionSystem S) (p : ℕ)

structure CentralizerCover where
  centric : F.CentricOrbit
  elementary : Subgroup S
  nontrivial : elementary ≠ ⊥
  le_subgroup : elementary ≤ centric.obj.as.subgroup
  centralizes : elementary ≤ Subgroup.centralizer (centric.obj.as.subgroup : Set S)
  exponent : ∀ x ∈ elementary, x ^ p = 1

namespace CentralizerCover

variable {F p} (A B D : F.CentralizerCover p)

abbrev Covers (f : A.centric.obj.as ⟶ B.centric.obj.as) : Prop :=
  ∀ b : B.elementary, ∃ a : A.elementary,
    (f.val ⟨a.val, A.le_subgroup a.property⟩).val = b.val

theorem covers_id : (A.Covers A (𝟙 A.centric.obj.as)) := by
  intro a
  exact ⟨a, rfl⟩

theorem covers_comp {f : A.centric.obj.as ⟶ B.centric.obj.as}
    {g : B.centric.obj.as ⟶ D.centric.obj.as}
    (hf : A.Covers B f) (hg : B.Covers D g) : A.Covers D (f ≫ g) := by
  intro d
  obtain ⟨b, hb⟩ := hg d
  obtain ⟨a, ha⟩ := hf b
  refine ⟨a, ?_⟩
  have hfa : f.val ⟨a.val, A.le_subgroup a.property⟩ =
      ⟨b.val, B.le_subgroup b.property⟩ := Subtype.ext ha
  change (g.val (f.val ⟨a.val, A.le_subgroup a.property⟩)).val = d.val
  rw [hfa]
  exact hb

/-- The covering condition is independent of target-inner representatives. -/
theorem covers_of_orbit_eq {f g : A.centric.obj.as ⟶ B.centric.obj.as}
    (hfg : F.toOrbit.map f = F.toOrbit.map g) (hf : A.Covers B f) : A.Covers B g := by
  obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff f g).mp hfg
  intro b
  obtain ⟨a, ha⟩ := hf b
  refine ⟨a, ?_⟩
  have hc := (Subgroup.mem_centralizer_iff.mp (B.centralizes b.property)) r.val r.property
  have hgr := congrArg Subtype.val (hr ⟨a.val, A.le_subgroup a.property⟩)
  change (g.val ⟨a.val, A.le_subgroup a.property⟩).val =
    r.val⁻¹ * (f.val ⟨a.val, A.le_subgroup a.property⟩).val * r.val at hgr
  rw [hgr, ha, mul_assoc, ← hc, inv_mul_cancel_left]

abbrev Hom := {f : A.centric ⟶ B.centric //
  ∃ g : A.centric.obj.as ⟶ B.centric.obj.as,
    F.toOrbit.map g = f.hom ∧ A.Covers B g}

def identity : A.Hom A :=
  ⟨𝟙 A.centric, 𝟙 A.centric.obj.as, F.toOrbit.map_id _, A.covers_id⟩

def composition (f : A.Hom B) (g : B.Hom D) : A.Hom D := by
  refine ⟨f.val ≫ g.val, ?_⟩
  obtain ⟨f₀, hf₀, hf⟩ := f.property
  obtain ⟨g₀, hg₀, hg⟩ := g.property
  refine ⟨f₀ ≫ g₀, ?_, A.covers_comp B D hf hg⟩
  rw [F.toOrbit.map_comp, hf₀, hg₀]
  rfl

instance : Category (F.CentralizerCover p) where
  Hom A B := A.Hom B
  id A := A.identity
  comp f g := composition _ _ _ f g
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

@[ext] theorem hom_ext {A B : F.CentralizerCover p} (f g : A ⟶ B)
    (h : f.val = g.val) : f = g := Subtype.ext h

def homMk {A B : F.CentralizerCover p} (f : A.centric ⟶ B.centric)
    (g : A.centric.obj.as ⟶ B.centric.obj.as)
    (hg : F.toOrbit.map g = f.hom) (hc : A.Covers B g) : A ⟶ B :=
  ⟨f, g, hg, hc⟩

theorem covers_of_hom {A B : F.CentralizerCover p} (f : A ⟶ B)
    (g : A.centric.obj.as ⟶ B.centric.obj.as) (hg : F.toOrbit.map g = f.val.hom) :
    A.Covers B g := by
  obtain ⟨g₀, hg₀, hc⟩ := f.property
  exact A.covers_of_orbit_eq B (hg₀.trans hg.symm) hc

end CentralizerCover

def centralizerCoverForget : F.CentralizerCover p ⥤ F.CentricOrbit where
  obj A := A.centric
  map f := f.val

instance centralizerCoverForget_faithful : (F.centralizerCoverForget p).Faithful where
  map_injective h := Subtype.ext h

instance centralizerCover_finite [Finite S] : Finite (F.CentralizerCover p) := by
  letI : Finite F.CentricOrbit := Finite.of_injective
    (fun A : F.CentricOrbit => A.obj) (by
      intro A B h
      cases A
      cases B
      cases h
      rfl)
  apply Finite.of_injective (fun A : F.CentralizerCover p => (A.centric, A.elementary))
  intro A B h
  cases A
  cases B
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  cases h₁
  cases h₂
  rfl

instance centralizerCover_hom_finite [Finite S] (A B : F.CentralizerCover p) :
    Finite (A ⟶ B) := by
  letI : Finite (A.centric ⟶ B.centric) := Finite.of_injective
    (fun f : A.centric ⟶ B.centric => f.hom) (fun _ _ h => InducedCategory.hom_ext h)
  exact inferInstanceAs (Finite (A.Hom B))

end Sharpness.FusionSystem
