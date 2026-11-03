import Sharpness.Unconditional.InclusionMackeyBridgeDoubleCosets

/-! The manuscript's Mackey formula for subgroup inclusions implies the
existing arbitrary-arrow Mackey formula. The underlying functor data have
no Mackey field, so this construction does not assume its conclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory
open scoped BigOperators

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {R : Type u} [Ring R] (E : MackeyFunctorData.{u,w} R F.Orbit)

/-- The full double-coset formula, assumed only for actual subgroup inclusions. -/
def HasInclusionMackeyFormula : Prop :=
  ∀ {P Q T : F.Object} (hP : P.subgroup ≤ T.subgroup) (hQ : Q.subgroup ≤ T.subgroup),
    (E.pull (F.toOrbit.map (F.inclusion hP))).comp
        (E.push (F.toOrbit.map (F.inclusion hQ))) =
      ∑ i : F.RawDoubleCosetTerm (F.inclusion hP) (F.inclusion hQ),
        F.functorDataDoubleCosetOperator E (F.inclusion hP) (F.inclusion hQ) i

/-- General fusion maps reduce to subgroup inclusions by their actual image
isomorphisms; the actual double-coset summands are transported individually. -/
theorem rawMackeyFormula_of_inclusions (identity : F.HasInclusionMackeyFormula E)
    {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T) :
    (E.pull (F.toOrbit.map f)).comp (E.push (F.toOrbit.map g)) =
      ∑ i : F.RawDoubleCosetTerm f g, F.functorDataDoubleCosetOperator E f g i := by
  classical
  let f' : (⟨F.imageSubgroup f⟩ : F.Object) ⟶ T := F.inclusion (F.image_le f)
  let g' : (⟨F.imageSubgroup g⟩ : F.Object) ⟶ T := F.inclusion (F.image_le g)
  letI : Fintype (F.RawDoubleCosetTerm f' g') := F.rawDoubleCosetTermFintype f' g'
  let a := F.imageIso f
  let b := F.imageIso g
  have ha : a.hom ≫ f' = f := F.image_factorization f
  have hb : b.hom ≫ g' = g := F.image_factorization g
  have hf := F.range_eq_of_source_iso f f' a ha
  have hg := F.range_eq_of_source_iso g g' b hb
  let e := F.rawDoubleCosetSameRangeEquiv f g f' g' hf hg
  have hfm : F.toOrbit.map f = F.toOrbit.map a.hom ≫ F.toOrbit.map f' := by
    rw [← F.toOrbit.map_comp, ha]
  have hgm : F.toOrbit.map g = F.toOrbit.map b.hom ≫ F.toOrbit.map g' := by
    rw [← F.toOrbit.map_comp, hb]
  calc
    _ = (E.pull (F.toOrbit.map a.hom)).comp
        (((E.pull (F.toOrbit.map f')).comp (E.push (F.toOrbit.map g'))).comp
          (E.push (F.toOrbit.map b.hom))) := by
      rw [hfm, hgm, E.pull_comp, E.push_comp]
      rfl
    _ = (E.pull (F.toOrbit.map a.hom)).comp
        ((∑ j : F.RawDoubleCosetTerm f' g', F.functorDataDoubleCosetOperator E f' g' j).comp
          (E.push (F.toOrbit.map b.hom))) := by
      rw [identity (F.image_le f) (F.image_le g)]
    _ = ∑ j : F.RawDoubleCosetTerm f' g', (E.pull (F.toOrbit.map a.hom)).comp
        ((F.functorDataDoubleCosetOperator E f' g' j).comp
          (E.push (F.toOrbit.map b.hom))) := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
    _ = ∑ i : F.RawDoubleCosetTerm f g, (E.pull (F.toOrbit.map a.hom)).comp
        ((F.functorDataDoubleCosetOperator E f' g' (e i)).comp
          (E.push (F.toOrbit.map b.hom))) := (e.sum_comp _).symm
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      (F.functorDataDoubleCosetOperator_transport f g f' g' hf hg a b ha hb E i).symm)

/-- A full Mackey functor from precisely its two functors, compatibility on
isomorphisms, and the manuscript's inclusion-only double-coset formula. -/
def fullMackeyOfInclusionIdentity (identity : F.HasInclusionMackeyFormula E) :
    MackeyModule R F.Orbit F.mackeyShape :=
  F.fullMackeyOfRawIdentity E (F.rawMackeyFormula_of_inclusions E identity)

/-- The inclusion-only and arbitrary-arrow raw axiom lists are equivalent. -/
theorem hasInclusionMackeyFormula_iff_raw : F.HasInclusionMackeyFormula E ↔
    ∀ {P Q T : F.Object} (f : P ⟶ T) (g : Q ⟶ T),
      (E.pull (F.toOrbit.map f)).comp (E.push (F.toOrbit.map g)) =
        ∑ i : F.RawDoubleCosetTerm f g, F.functorDataDoubleCosetOperator E f g i :=
  ⟨F.rawMackeyFormula_of_inclusions E,
    fun h _ _ _ hP hQ => h (F.inclusion hP) (F.inclusion hQ)⟩

@[simp] theorem fullMackeyOfInclusionIdentity_value
    (identity : F.HasInclusionMackeyFormula E) (P : F.Orbit) :
    (F.fullMackeyOfInclusionIdentity E identity).Value P = E.Value P := rfl

@[simp] theorem fullMackeyOfInclusionIdentity_pull
    (identity : F.HasInclusionMackeyFormula E) {P Q : F.Orbit} (f : P ⟶ Q) :
    (F.fullMackeyOfInclusionIdentity E identity).pull f = E.pull f := rfl

@[simp] theorem fullMackeyOfInclusionIdentity_push
    (identity : F.HasInclusionMackeyFormula E) {P Q : F.Orbit} (f : P ⟶ Q) :
    (F.fullMackeyOfInclusionIdentity E identity).push f = E.push f := rfl

end Sharpness.FusionSystem
