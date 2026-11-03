import Sharpness.Unconditional.GroupCohomologyNestedPull

/-! Native restriction computed on arbitrary projective resolutions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory Finsupp
variable {R G H : Type u} [CommRing R] [Group G] [Group H]

/-- A group isomorphism induces the actual restriction equivalence of representation categories. -/
def resEquivalence (e : H ≃* G) : Rep.{u} R G ≌ Rep.{u} R H where
  functor := Rep.resFunctor e.toMonoidHom
  inverse := Rep.resFunctor e.symm.toMonoidHom
  unitIso := NatIso.ofComponents (fun V => Rep.mkIso
    (Representation.Equiv.mk (LinearEquiv.refl R V) (fun g => by
      ext x
      change V.ρ g x = V.ρ (e (e.symm g)) x
      rw [e.apply_symm_apply]))) (by intros; apply Rep.hom_ext; ext x; rfl)
  counitIso := NatIso.ofComponents (fun V => Rep.mkIso
    (Representation.Equiv.mk (LinearEquiv.refl R V) (fun h => by
      ext x
      change V.ρ (e.symm (e h)) x = V.ρ h x
      rw [e.symm_apply_apply]))) (by intros; apply Rep.hom_ext; ext x; rfl)
  functor_unitIso_comp V := by apply Rep.hom_ext; ext x; rfl

instance resFunctor_isEquivalence (e : H ≃* G) :
    (Rep.resFunctor.{u} (k := R) e.toMonoidHom).IsEquivalence :=
  (resEquivalence (R := R) e).isEquivalence_functor

variable (f : H →* G) [(Rep.resFunctor.{u} (k := R) f).PreservesProjectiveObjects]

theorem barRestriction_general_augmentation :
    (barRestrictionChain (R := R) f).f 0 ≫
        ((Rep.resFunctor f).mapProjectiveResolution (Rep.barResolution R G)).π.f 0 =
      (Rep.barResolution R H).π.f 0 := by
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution R G).π.f 0).hom
      ((barRestrictionComponent f 0).hom (single x (single 1 1))) =
    ((Rep.barResolution R H).π.f 0).hom (single x (single 1 1))
  rw [barRestrictionComponent_single, map_one, barAugmentation_single,
    barAugmentation_single]

/-- On the bar resolution, restriction agrees with native cochain pullback. -/
theorem homomorphism_restriction_bar_comparison (V : Rep.{u} R G) (n : ℕ) :
    groupCohomology.map f (𝟙 (Rep.res f V)) n ≫
        (groupCohomologyIso (Rep.res f V) n
          ((Rep.resFunctor f).mapProjectiveResolution (Rep.barResolution R G))).hom =
      (groupCohomologyIso V n (Rep.barResolution R G)).hom ≫
        HomologicalComplex.homologyMap
          (homComplexRestrict f (Rep.barResolution R G).complex V) n := by
  let P := (Rep.resFunctor f).mapProjectiveResolution (Rep.barResolution R G)
  let a := homComplexPrecomp (Rep.res f V) (barRestrictionChain f)
  have ha := groupCohomologyIso_hom_precomp (Rep.barResolution R H) P (Rep.res f V)
    (barRestrictionChain f) (barRestriction_general_augmentation f) n
  rw [groupCohomologyIso_bar_hom] at ha
  have ha' : HomologicalComplex.homologyMap a n =
      (groupCohomologyIso (Rep.res f V) n P).inv ≫
        HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso (Rep.res f V)).hom n := by
    rw [← ha]
    simp [a]
  haveI : IsIso (HomologicalComplex.homologyMap a n) := by rw [ha']; infer_instance
  apply (cancel_mono (HomologicalComplex.homologyMap a n)).mp
  rw [Category.assoc, ha, groupCohomologyIso_bar_hom, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  simpa only [HomologicalComplex.homologyMap_comp, Category.assoc] using
    (congrArg (fun c => HomologicalComplex.homologyMap c n)
      (bar_restriction_cochain_comparison f V)).symm

omit [(Rep.resFunctor.{u} (k := R) f).PreservesProjectiveObjects] in
theorem homComplexRestrict_precomp {X Y : ChainComplex (Rep.{u} R G) ℕ}
    (φ : X ⟶ Y) (V : Rep.{u} R G) :
    homComplexRestrict f Y V ≫ homComplexPrecomp (Rep.res f V)
        (((Rep.resFunctor f).mapHomologicalComplex _).map φ) =
      homComplexPrecomp V φ ≫ homComplexRestrict f X V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (Rep.resFunctor f).map_comp (φ.f n) a

theorem homomorphism_restriction_resolution_comparison_zero
    (P Q : ProjectiveResolution (Rep.trivial R G R))
    (φ : P.complex ⟶ Q.complex) (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) :
    ((((Rep.resFunctor f).mapHomologicalComplex _).map φ).f 0) ≫
        ((Rep.resFunctor f).mapProjectiveResolution Q).π.f 0 =
      ((Rep.resFunctor f).mapProjectiveResolution P).π.f 0 := by
  change (Rep.resFunctor f).map (φ.f 0) ≫
      ((Rep.resFunctor f).map (Q.π.f 0) ≫ _) =
    (Rep.resFunctor f).map (P.π.f 0) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, hφ]

/-- Native restriction agrees with restriction on Hom cochains for any actual
projective resolution whose restriction is projective. -/
theorem homomorphism_restriction_resolution_comparison
    (P : ProjectiveResolution (Rep.trivial R G R)) (V : Rep.{u} R G) (n : ℕ) :
    groupCohomology.map f (𝟙 (Rep.res f V)) n ≫
        (groupCohomologyIso (Rep.res f V) n
          ((Rep.resFunctor f).mapProjectiveResolution P)).hom =
      (groupCohomologyIso V n P).hom ≫
        HomologicalComplex.homologyMap (homComplexRestrict f P.complex V) n := by
  let Q := Rep.barResolution R G
  let φ := ProjectiveResolution.lift (𝟙 (Rep.trivial R G R)) P Q
  have hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 := by simp [φ]
  have hG := groupCohomologyIso_hom_precomp P Q V φ hφ n
  have hH := groupCohomologyIso_hom_precomp
    ((Rep.resFunctor f).mapProjectiveResolution P)
    ((Rep.resFunctor f).mapProjectiveResolution Q) (Rep.res f V)
    (((Rep.resFunctor f).mapHomologicalComplex _).map φ)
    (homomorphism_restriction_resolution_comparison_zero f P Q φ hφ) n
  rw [← hH, ← Category.assoc, homomorphism_restriction_bar_comparison, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, homComplexRestrict_precomp,
    HomologicalComplex.homologyMap_comp, ← Category.assoc, hG]

end Sharpness.OrdinaryCohomology
