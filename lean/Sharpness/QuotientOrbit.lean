import Sharpness.CentralQuotientDefinition

/-! The quotient functor q on actual orbit categories. Its source is the
orbit category on the full preimages of subgroups of S/Z; the group
correspondence identifies these with precisely the overgroups of Z.
Object bijectivity and arrow surjectivity are proved, not imported. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (saturated : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS saturated)

abbrev QuotientLiftCategory := InducedCategory F.Object
  (fun A : Subgroup (S ⧸ Z) => (⟨F.quotientPreimage Z A⟩ : F.Object))

def quotientRawFunctor : F.QuotientLiftCategory (Z := Z) ⥤ I.system.Object where
  obj A := ⟨A⟩
  map f := ⟨F.quotientInducedHom hZ f.hom, (I.isHom_iff _).mpr ⟨f.hom, rfl⟩⟩
  map_id A := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro a
    obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
    exact F.quotientInducedHom_apply hZ (𝟙 _) x
  map_comp {A B C} f g := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro a
    obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
    change F.quotientInducedHom hZ (f.hom ≫ g.hom) (F.subgroupProjection Z A x) =
      F.quotientInducedHom hZ g.hom
        (F.quotientInducedHom hZ f.hom (F.subgroupProjection Z A x))
    rw [F.quotientInducedHom_apply, F.quotientInducedHom_apply,
      F.quotientInducedHom_apply]
    rfl

def quotientLiftInner : HomRel (F.QuotientLiftCategory (Z := Z)) :=
  fun {_ _} f g => F.targetInner f.hom g.hom

instance quotientLiftInner_congruence : Congruence (F.quotientLiftInner (Z := Z)) where
  equivalence :=
    { refl := fun f => (inferInstance : Congruence F.targetInner).equivalence.refl f.hom
      symm := fun h => (inferInstance : Congruence F.targetInner).equivalence.symm h
      trans := fun h h' => (inferInstance : Congruence F.targetInner).equivalence.trans h h' }
  comp_left := by
    intro A B C f g g' h
    exact HomRel.comp_left (r := F.targetInner) f.hom h
  comp_right := by
    intro A B C f f' g h
    exact HomRel.comp_right (r := F.targetInner) g.hom h

abbrev QuotientLiftOrbit := CategoryTheory.Quotient (F.quotientLiftInner (Z := Z))

theorem quotientRaw_respects_inner {A B : F.QuotientLiftCategory (Z := Z)}
    (f g : A ⟶ B) (related : F.quotientLiftInner f g) :
    (F.quotientRawFunctor hZ p hS saturated I ⋙ I.system.toOrbit).map f =
      (F.quotientRawFunctor hZ p hS saturated I ⋙ I.system.toOrbit).map g := by
  apply (I.system.orbit_map_eq_iff _ _).mpr
  obtain ⟨r, hr⟩ := related
  refine ⟨F.subgroupProjection Z B r, ?_⟩
  intro a
  obtain ⟨x, rfl⟩ := F.subgroupProjection_surjective Z A a
  change F.quotientInducedHom hZ g.hom (F.subgroupProjection Z A x) =
    (F.subgroupProjection Z B r)⁻¹ *
      F.quotientInducedHom hZ f.hom (F.subgroupProjection Z A x) *
        F.subgroupProjection Z B r
  rw [F.quotientInducedHom_apply, F.quotientInducedHom_apply, hr x, map_mul, map_mul, map_inv]

def quotientOrbitFunctor : F.QuotientLiftOrbit (Z := Z) ⥤ I.system.Orbit :=
  CategoryTheory.Quotient.lift (F.quotientLiftInner (Z := Z))
    (F.quotientRawFunctor hZ p hS saturated I ⋙ I.system.toOrbit)
    (fun _ _ f g h => F.quotientRaw_respects_inner hZ p hS saturated I f g h)

def quotientOrbitObjectEquiv : F.QuotientLiftOrbit (Z := Z) ≃ I.system.Orbit where
  toFun := (F.quotientOrbitFunctor hZ p hS saturated I).obj
  invFun P := ⟨P.as.subgroup⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

instance quotientOrbitFunctor_full : (F.quotientOrbitFunctor hZ p hS saturated I).Full where
  map_surjective := by
    rintro ⟨A⟩ ⟨B⟩ f
    obtain ⟨g, rfl⟩ := I.system.toOrbit.map_surjective f
    obtain ⟨l, hl⟩ := (I.isHom_iff g.val).mp g.property
    refine ⟨(CategoryTheory.Quotient.functor (F.quotientLiftInner (Z := Z))).map
      (InducedCategory.homMk l), ?_⟩
    change I.system.toOrbit.map _ = I.system.toOrbit.map g
    congr 1
    apply Subtype.ext
    exact hl

end Sharpness.FusionSystem
