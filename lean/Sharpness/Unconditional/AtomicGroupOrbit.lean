import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.GroupTheory.PGroup

/-!
The ordinary orbit category of the p-subgroups of a group. Its morphisms
are transporter elements modulo right multiplication by the target. A
normal p-subgroup gives the reflector P ↦ P ⊔ N onto its overgroups.
This is the categorical input to normal-p-subgroup atomic vanishing.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.AtomicGroupOrbit
open CategoryTheory
variable (p : ℕ) (G : Type u) [Group G]

structure Object where
  subgroup : Subgroup G
  isPGroup : IsPGroup p subgroup

variable {p G}

abbrev Transporter (P Q : Object p G) :=
  {g : G // ∀ x ∈ P.subgroup, g⁻¹ * x * g ∈ Q.subgroup}

instance : Category (Object p G) where
  Hom := Transporter
  id P := ⟨1, by intro x hx; simpa using hx⟩
  comp f g := ⟨f.val * g.val, by
    intro x hx
    simpa [mul_assoc] using g.property _ (f.property x hx)⟩
  id_comp f := by apply Subtype.ext; exact one_mul _
  comp_id f := by apply Subtype.ext; exact mul_one _
  assoc f g h := by apply Subtype.ext; exact mul_assoc _ _ _

def targetRelation : HomRel (Object p G) :=
  fun {_ Q} f g => ∃ q : Q.subgroup, g.val = f.val * q.val

instance : Congruence (targetRelation (p := p) (G := G)) where
  equivalence :=
    { refl := fun f => ⟨1, (mul_one f.val).symm⟩
      symm := by
        intro f g h
        obtain ⟨q, hq⟩ := h
        refine ⟨q⁻¹, ?_⟩
        simp only [hq, Subgroup.coe_inv, mul_inv_cancel_right]
      trans := by
        intro f g h hfg hgh
        obtain ⟨q, hq⟩ := hfg
        obtain ⟨r, hr⟩ := hgh
        exact ⟨q * r, by simp only [hr, hq, Subgroup.coe_mul, mul_assoc]⟩ }
  comp_left := by
    intro P Q T f g g' h
    obtain ⟨q, hq⟩ := h
    exact ⟨q, by
      change f.val * g'.val = (f.val * g.val) * q.val
      rw [hq, mul_assoc]⟩
  comp_right := by
    intro P Q T f f' g h
    obtain ⟨q, hq⟩ := h
    refine ⟨⟨g.val⁻¹ * q.val * g.val, g.property q.val q.property⟩, ?_⟩
    change f'.val * g.val = (f.val * g.val) * (g.val⁻¹ * q.val * g.val)
    rw [hq]
    group

abbrev Orbit := CategoryTheory.Quotient (targetRelation (p := p) (G := G))

abbrev toOrbit : Object p G ⥤ Orbit (p := p) (G := G) :=
  CategoryTheory.Quotient.functor _

/-- Equality is exactly equality of the represented right cosets. -/
theorem orbit_map_eq_iff {P Q : Object p G} (f g : P ⟶ Q) :
    (toOrbit (p := p) (G := G)).map f = toOrbit.map g ↔
      ∃ q : Q.subgroup, g.val = f.val * q.val :=
  CategoryTheory.Quotient.functor_map_eq_iff _ f g

variable (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)

def closeObject (P : Object p G) : Object p G :=
  ⟨P.subgroup ⊔ N, P.isPGroup.to_sup_of_normal_right hN⟩

private theorem conjugates_sup {P Q : Subgroup G} (g : G)
    (hg : ∀ x ∈ P, g⁻¹ * x * g ∈ Q) :
    ∀ x ∈ P ⊔ N, g⁻¹ * x * g ∈ Q ⊔ N := by
  let c : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hc : P ⊔ N ≤ (Q ⊔ N).comap c := by
    apply sup_le
    · intro x hx
      change g⁻¹ * x * (g⁻¹)⁻¹ ∈ Q ⊔ N
      simpa only [inv_inv] using (le_sup_left : Q ≤ Q ⊔ N) (hg x hx)
    · intro x hx
      change g⁻¹ * x * (g⁻¹)⁻¹ ∈ Q ⊔ N
      exact (le_sup_right : N ≤ Q ⊔ N)
        ((inferInstance : N.Normal).conj_mem x hx g⁻¹)
  intro x hx
  simpa [c, MulAut.conj_apply] using hc hx

def closeRaw : Object p G ⥤ Object p G where
  obj := closeObject N hN
  map f := ⟨f.val, conjugates_sup N f.val f.property⟩
  map_id P := by apply Subtype.ext; rfl
  map_comp f g := by apply Subtype.ext; rfl

def close : Orbit (p := p) (G := G) ⥤ Orbit (p := p) (G := G) :=
  CategoryTheory.Quotient.lift _ (closeRaw N hN ⋙ toOrbit) (by
    intro P Q f g h
    apply CategoryTheory.Quotient.sound
    obtain ⟨q, hq⟩ := h
    exact ⟨⟨q.val, (le_sup_left : Q.subgroup ≤ Q.subgroup ⊔ N) q.property⟩, hq⟩)

@[simp]
theorem close_map {P Q : Object p G} (f : P ⟶ Q) :
    (close N hN).map (toOrbit.map f) = toOrbit.map ((closeRaw N hN).map f) := rfl

/-- The full orbit subcategory on p-subgroups containing `N`. -/
abbrev Overgroups := ObjectProperty.FullSubcategory
  (fun P : Orbit (p := p) (G := G) => N ≤ P.as.subgroup)

def overgroupInclusion : Overgroups (p := p) N ⥤ Orbit (p := p) (G := G) :=
  ObjectProperty.ι _

def reflector : Orbit (p := p) (G := G) ⥤ Overgroups (p := p) N where
  obj P := ⟨(close N hN).obj P, le_sup_right⟩
  map f := ObjectProperty.homMk ((close N hN).map f)
  map_id P := by apply ObjectProperty.hom_ext; exact (close N hN).map_id P
  map_comp f g := by apply ObjectProperty.hom_ext; exact (close N hN).map_comp f g

def inclusionHom {P Q : Object p G} (h : P.subgroup ≤ Q.subgroup) : P ⟶ Q :=
  ⟨1, by intro x hx; simpa only [inv_one, one_mul, mul_one] using h hx⟩

def reflectorUnit : 𝟭 (Orbit (p := p) (G := G)) ⟶
    reflector N hN ⋙ overgroupInclusion N where
  app P := toOrbit.map (inclusionHom (P := P.as) (Q := closeObject N hN P.as) le_sup_left)
  naturality {P Q} f := by
    obtain ⟨g, rfl⟩ := toOrbit.map_surjective f
    change toOrbit.map g ≫ toOrbit.map _ = toOrbit.map _ ≫ toOrbit.map _
    rw [← toOrbit.map_comp, ← toOrbit.map_comp]
    congr 1
    apply Subtype.ext
    change g.val * 1 = 1 * g.val
    simp

def reflectorCounit : overgroupInclusion (p := p) N ⋙ reflector N hN ⟶
    𝟭 (Overgroups (p := p) N) where
  app P := ObjectProperty.homMk (toOrbit.map
    (inclusionHom (P := closeObject N hN P.obj.as) (Q := P.obj.as)
      (sup_le le_rfl P.property)))
  naturality {P Q} f := by
    apply ObjectProperty.hom_ext
    obtain ⟨g, hg⟩ := toOrbit.map_surjective f.hom
    change (close N hN).map f.hom ≫ toOrbit.map _ = toOrbit.map _ ≫ f.hom
    rw [← hg]
    change toOrbit.map ((closeRaw N hN).map g) ≫ toOrbit.map _ = toOrbit.map _ ≫ toOrbit.map g
    rw [← toOrbit.map_comp, ← toOrbit.map_comp]
    congr 1
    apply Subtype.ext
    change g.val * 1 = 1 * g.val
    simp

/-- The coset-preserving reflector is left adjoint to the inclusion. -/
def reflectorAdjunction : reflector N hN ⊣ overgroupInclusion (p := p) N where
  unit := reflectorUnit N hN
  counit := reflectorCounit N hN
  left_triangle_components P := by
    apply ObjectProperty.hom_ext
    change toOrbit.map _ ≫ toOrbit.map _ = toOrbit.map _
    rw [← toOrbit.map_comp]
    congr 1
    apply Subtype.ext
    change (1 : G) * 1 = 1
    exact one_mul _
  right_triangle_components P := by
    change toOrbit.map _ ≫ toOrbit.map _ = toOrbit.map _
    rw [← toOrbit.map_comp]
    congr 1
    apply Subtype.ext
    change (1 : G) * 1 = 1
    exact one_mul _

end Sharpness.AtomicGroupOrbit
