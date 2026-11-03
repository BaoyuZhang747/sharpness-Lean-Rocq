import Sharpness.QuotientCentric

/-! Faithfulness of the central quotient on quotient-centric objects.
Equal quotient-orbit arrows are compared by actual inner adjustments and
the proved inner-kernel theorem. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

theorem rawOrbit_eq_of_quotientOrbit_eq
    {A B : Subgroup (S ⧸ Z)} (hA : I.system.IsCentric A)
    (f g : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩)
    (same : F.rawQuotientOrbitMap hZ p hS sat I f = F.rawQuotientOrbitMap hZ p hS sat I g) :
    F.toOrbit.map f = F.toOrbit.map g := by
  obtain ⟨r, hr⟩ := (I.system.orbit_map_eq_iff _ _).mp same
  let rB : B := r
  have hrB (x : A) : F.quotientInducedHom hZ g x =
      rB⁻¹ * F.quotientInducedHom hZ f x * rB := hr x
  obtain ⟨rP, hrP⟩ := F.subgroupProjection_surjective Z B rB
  let f' := f ≫ F.inner (⟨F.quotientPreimage Z B⟩ : F.Object) rP
  have modZ (x : F.quotientPreimage Z A) : (f'.val x).val⁻¹ * (g.val x).val ∈ Z := by
    have h := hrB (F.subgroupProjection Z A x)
    rw [F.quotientInducedHom_apply, F.quotientInducedHom_apply, ← hrP] at h
    have hval := congrArg (fun b : B => b.val) h
    change (QuotientGroup.mk (g.val x).val : S ⧸ Z) =
      (QuotientGroup.mk rP.val : S ⧸ Z)⁻¹ * QuotientGroup.mk (f.val x).val *
        QuotientGroup.mk rP.val at hval
    apply QuotientGroup.eq.mp
    rw [hval]
    change (QuotientGroup.mk (rP.val⁻¹ * (f.val x).val * rP.val) : S ⧸ Z) = _
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  letI := F.central_subgroupOf_normal hZ (F.quotientPreimage Z A)
  obtain ⟨a, ha⟩ := F.exists_gamma_of_same_modZ hZ
    (QuotientGroup.le_comap_mk' Z A) f' g modZ
  obtain ⟨s, hs⟩ := F.gamma_inner_of_quotient_centric hZ p hS sat I A hA a
  have hi : F.toOrbit.map (F.isoOfMulEquiv a.val.val a.val.property).hom =
      𝟙 (F.toOrbit.obj (⟨F.quotientPreimage Z A⟩ : F.Object)) := by
    have hh : (F.isoOfMulEquiv a.val.val a.val.property).hom =
        F.inner (⟨F.quotientPreimage Z A⟩ : F.Object) s := by
      apply Subtype.ext
      apply MonoidHom.ext
      intro x
      exact hs x
    exact (congrArg (fun t => F.toOrbit.map t) hh).trans
      (F.inner_orbit_eq_id (⟨F.quotientPreimage Z A⟩ : F.Object) s)
  calc
    F.toOrbit.map f = F.toOrbit.map f' := by
      rw [F.toOrbit.map_comp, F.inner_orbit_eq_id, Category.comp_id]
    _ = F.toOrbit.map g := by
      have hc := F.toOrbit.map_comp (F.isoOfMulEquiv a.val.val a.val.property).hom f'
      have he := hc.trans ((congrArg (fun t => t ≫ F.toOrbit.map f') hi).trans
        (Category.id_comp (F.toOrbit.map f')))
      exact he.symm.trans (congrArg (fun t => F.toOrbit.map t) ha)

abbrev QuotientCentricLiftOrbit := ObjectProperty.FullSubcategory
  (fun A : F.QuotientLiftOrbit (Z := Z) => I.system.IsCentric A.as)

def quotientCentricFunctor : F.QuotientCentricLiftOrbit hZ p hS sat I ⥤ I.system.CentricOrbit where
  obj A := ⟨(F.quotientOrbitFunctor hZ p hS sat I).obj A.obj, A.property⟩
  map f := ObjectProperty.homMk ((F.quotientOrbitFunctor hZ p hS sat I).map f.hom)
  map_id A := by
    apply InducedCategory.hom_ext
    exact (F.quotientOrbitFunctor hZ p hS sat I).map_id A.obj
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (F.quotientOrbitFunctor hZ p hS sat I).map_comp f.hom g.hom

instance quotientCentricFunctor_faithful : (F.quotientCentricFunctor hZ p hS sat I).Faithful where
  map_injective := by
    intro A B f g h
    apply InducedCategory.hom_ext
    have hmap := congrArg (fun t => t.hom) h
    obtain ⟨f', hf⟩ := (CategoryTheory.Quotient.functor
      (F.quotientLiftInner (Z := Z))).map_surjective f.hom
    obtain ⟨g', hg⟩ := (CategoryTheory.Quotient.functor
      (F.quotientLiftInner (Z := Z))).map_surjective g.hom
    rw [← hf, ← hg]
    apply (CategoryTheory.Quotient.functor_map_eq_iff _ _ _).mpr
    apply (F.orbit_map_eq_iff _ _).mp
    apply F.rawOrbit_eq_of_quotientOrbit_eq hZ p hS sat I A.property f'.hom g'.hom
    exact (congrArg ((F.quotientOrbitFunctor hZ p hS sat I).map) hf).trans
      (hmap.trans (congrArg ((F.quotientOrbitFunctor hZ p hS sat I).map) hg).symm)

instance quotientCentricFunctor_full : (F.quotientCentricFunctor hZ p hS sat I).Full where
  map_surjective := by
    intro A B f
    obtain ⟨g, hg⟩ := (F.quotientOrbitFunctor hZ p hS sat I).map_surjective f.hom
    refine ⟨ObjectProperty.homMk g, ?_⟩
    apply InducedCategory.hom_ext
    exact hg

theorem quotientCentricFunctor_obj_surjective :
    Function.Surjective (F.quotientCentricFunctor hZ p hS sat I).obj := by
  rintro ⟨⟨⟨A⟩⟩, hA⟩
  exact ⟨⟨⟨A⟩, hA⟩, rfl⟩

instance quotientCentricFunctor_essSurj : (F.quotientCentricFunctor hZ p hS sat I).EssSurj where
  mem_essImage A := by
    obtain ⟨P, hP⟩ := F.quotientCentricFunctor_obj_surjective hZ p hS sat I A
    exact ⟨P, ⟨eqToIso hP⟩⟩

instance quotientCentricFunctor_isEquivalence :
    (F.quotientCentricFunctor hZ p hS sat I).IsEquivalence where

def quotientCentricEquivalence : F.QuotientCentricLiftOrbit hZ p hS sat I ≌ I.system.CentricOrbit :=
  (F.quotientCentricFunctor hZ p hS sat I).asEquivalence

end Sharpness.FusionSystem
