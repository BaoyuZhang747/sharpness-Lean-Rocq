import Sharpness.Mackey
import Sharpness.StableZero
import Mathlib.CategoryTheory.Quotient

/-!
Concrete subgroup and morphism objects for the paper. This file supplies
the fusion category and its orbit category. It does not attempt to reprove
any literature theorem about saturation or higher limits.

The orbit relation is proved to be exactly postcomposition by an inner
automorphism of the target; it is not a renamed abstract category.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory

def subgroupInclusion {S : Type u} [Group S] (P Q : Subgroup S) (h : P ≤ Q) : P →* Q where
  toFun x := ⟨x.val, h x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def subgroupConjugation {S : Type u} [Group S] (P Q : Subgroup S) (s : S)
    (h : ∀ x ∈ P, s⁻¹ * x * s ∈ Q) : P →* Q where
  toFun x := ⟨s⁻¹ * x.val * s, h x.val x.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp [mul_assoc]

/-- The ordinary fusion-category axioms, on actual subgroups and injective
group homomorphisms. Saturation results are reserved for the cited theory. -/
structure FusionSystem (S : Type u) [Group S] where
  IsHom : ∀ {P Q : Subgroup S}, (P →* Q) → Prop
  injective : ∀ {P Q : Subgroup S} (f : P →* Q), IsHom f → Function.Injective f
  id_mem : ∀ P : Subgroup S, IsHom (MonoidHom.id P)
  comp_mem : ∀ {P Q T : Subgroup S} (f : P →* Q) (g : Q →* T),
    IsHom f → IsHom g → IsHom (g.comp f)
  inclusion_mem : ∀ {P Q : Subgroup S} (h : P ≤ Q), IsHom (subgroupInclusion P Q h)
  conjugation_mem : ∀ (P Q : Subgroup S) (s : S)
    (h : ∀ x ∈ P, s⁻¹ * x * s ∈ Q), IsHom (subgroupConjugation P Q s h)
  inverse_mem : ∀ {P Q : Subgroup S} (e : P ≃* Q),
    IsHom e.toMonoidHom → IsHom e.symm.toMonoidHom
  codomain_restrict_mem : ∀ {P Q R : Subgroup S} (f : P →* Q), IsHom f →
    ∀ (hRQ : R ≤ Q) (g : P →* R), (subgroupInclusion R Q hRQ).comp g = f → IsHom g

namespace FusionSystem
variable {S : Type u} [Group S] (F : FusionSystem S)

structure Object (F : FusionSystem S) where
  subgroup : Subgroup S

abbrev Morphism (P Q : F.Object) :=
  {f : P.subgroup →* Q.subgroup // F.IsHom f}

instance : Category.{u} F.Object where
  Hom := F.Morphism
  id P := ⟨MonoidHom.id _, F.id_mem _⟩
  comp f g := ⟨g.val.comp f.val, F.comp_mem _ _ f.property g.property⟩
  id_comp f := by apply Subtype.ext; rfl
  comp_id f := by apply Subtype.ext; rfl
  assoc f g h := by apply Subtype.ext; rfl

@[simp] theorem comp_apply {P Q T : F.Object} (f : P ⟶ Q) (g : Q ⟶ T)
    (x : P.subgroup) : (f ≫ g).val x = g.val (f.val x) := rfl

def inclusion {P Q : F.Object} (h : P.subgroup ≤ Q.subgroup) : P ⟶ Q :=
  ⟨subgroupInclusion _ _ h, F.inclusion_mem h⟩

def inner (P : F.Object) (r : P.subgroup) : P ⟶ P :=
  ⟨subgroupConjugation P.subgroup P.subgroup r.val
      (fun _x hx => P.subgroup.mul_mem (P.subgroup.mul_mem (P.subgroup.inv_mem r.property) hx) r.property),
    F.conjugation_mem _ _ _ _⟩

/-- The exact orbit equivalence relation used in the manuscript. -/
def targetInner : HomRel F.Object :=
  fun {P Q} f g => ∃ r : Q.subgroup, ∀ x : P.subgroup, g.val x = r⁻¹ * f.val x * r

instance targetInner_congruence : CategoryTheory.Congruence F.targetInner where
  equivalence :=
    { refl := fun f => ⟨1, by intro x; simp⟩
      symm := by
        intro f g h
        obtain ⟨r, hr⟩ := h
        refine ⟨r⁻¹, ?_⟩
        intro x
        rw [hr x]
        simp [mul_assoc]
      trans := by
        intro f g h hfg hgh
        obtain ⟨r, hr⟩ := hfg
        obtain ⟨s, hs⟩ := hgh
        refine ⟨r * s, ?_⟩
        intro x
        rw [hs x, hr x]
        simp [mul_assoc] }
  comp_left := by
    intro P Q T f g g' h
    obtain ⟨r, hr⟩ := h
    exact ⟨r, fun x => hr (f.val x)⟩
  comp_right := by
    intro P Q T f f' g h
    obtain ⟨r, hr⟩ := h
    refine ⟨g.val r, ?_⟩
    intro x
    change g.val (f'.val x) = _
    rw [hr x]
    simp only [map_mul, map_inv, comp_apply]

abbrev Orbit := CategoryTheory.Quotient F.targetInner

abbrev toOrbit : F.Object ⥤ F.Orbit := CategoryTheory.Quotient.functor F.targetInner

theorem orbit_map_eq_iff {P Q : F.Object} (f g : P ⟶ Q) :
    F.toOrbit.map f = F.toOrbit.map g ↔
      ∃ r : Q.subgroup, ∀ x : P.subgroup, g.val x = r⁻¹ * f.val x * r :=
  CategoryTheory.Quotient.functor_map_eq_iff F.targetInner f g

theorem inner_orbit_eq_id (P : F.Object) (r : P.subgroup) :
    F.toOrbit.map (F.inner P r) = 𝟙 (F.toOrbit.obj P) := by
  have h : F.toOrbit.map (𝟙 P) = F.toOrbit.map (F.inner P r) := by
    apply (F.orbit_map_eq_iff _ _).mpr
    refine ⟨r, ?_⟩
    intro x
    apply Subtype.ext
    rfl
  exact h.symm.trans (F.toOrbit.map_id P)

instance objectFinite [Finite S] : Finite F.Object := by
  apply Finite.of_injective (fun P : F.Object => P.subgroup)
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

instance orbitFinite [Finite S] : Finite F.Orbit := by
  let e := CategoryTheory.Quotient.equiv F.targetInner
  apply Finite.of_injective e
  exact e.injective

instance morphismFinite [Finite S] (P Q : F.Object) : Finite (P ⟶ Q) := by
  apply Finite.of_injective (fun f : P ⟶ Q => (f.val : P.subgroup → Q.subgroup))
  intro f g h
  apply Subtype.ext
  exact MonoidHom.ext (congrFun h)

instance orbitMorphismFinite [Finite S] (P Q : F.Orbit) : Finite (P ⟶ Q) := by
  rcases P with ⟨P⟩
  rcases Q with ⟨Q⟩
  exact Finite.of_surjective (fun f : P ⟶ Q => F.toOrbit.map f)
    F.toOrbit.map_surjective

theorem order_mono [Finite S] {P Q : F.Object} (f : P ⟶ Q) :
    Nat.card P.subgroup ≤ Nat.card Q.subgroup :=
  Nat.card_le_card_of_injective f.val (F.injective _ f.property)

def isoOfEqualOrder [Finite S] {P Q : F.Object} (f : P ⟶ Q)
    (heq : Nat.card P.subgroup = Nat.card Q.subgroup) : P ≅ Q := by
  let e : P.subgroup ≃* Q.subgroup := MulEquiv.ofBijective f.val
    ((Nat.bijective_iff_injective_and_card f.val).mpr ⟨F.injective _ f.property, heq⟩)
  exact
    { hom := f
      inv := ⟨e.symm.toMonoidHom, F.inverse_mem e f.property⟩
      hom_inv_id := by
        apply Subtype.ext
        ext x
        exact congrArg Subtype.val (e.symm_apply_apply x)
      inv_hom_id := by
        apply Subtype.ext
        ext x
        exact congrArg Subtype.val (e.apply_symm_apply x) }

def orbitOrder (P : F.Orbit) : ℕ := Nat.card P.as.subgroup

theorem orbitOrder_mono [Finite S] {P Q : F.Orbit} (f : P ⟶ Q) :
    F.orbitOrder P ≤ F.orbitOrder Q := by
  rcases P with ⟨P⟩
  rcases Q with ⟨Q⟩
  obtain ⟨g, rfl⟩ := F.toOrbit.map_surjective f
  exact F.order_mono g

theorem orbit_isIso_of_equal_order [Finite S] {P Q : F.Orbit} (f : P ⟶ Q)
    (h : F.orbitOrder P = F.orbitOrder Q) : IsIso f := by
  rcases P with ⟨P⟩
  rcases Q with ⟨Q⟩
  obtain ⟨g, rfl⟩ := F.toOrbit.map_surjective f
  exact (F.toOrbit.mapIso (F.isoOfEqualOrder g h)).isIso_hom

/-- The actual isomorphism part used in the stable-zero proof. -/
def isoSystem : FusionIsoSystem S where
  Allowed e := F.IsHom e.toMonoidHom
  id_mem := F.id_mem
  comp_mem _ _ he hf := F.comp_mem _ _ he hf
  inv_mem e he := F.inverse_mem e he

def IsCentric (P : Subgroup S) : Prop :=
  F.isoSystem.CentricIn ⊤ P

abbrev CentricOrbit := ObjectProperty.FullSubcategory (fun P : F.Orbit => F.IsCentric P.as.subgroup)

end FusionSystem
end Sharpness
