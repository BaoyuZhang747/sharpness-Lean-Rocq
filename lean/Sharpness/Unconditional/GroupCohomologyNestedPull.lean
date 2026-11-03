import Sharpness.Unconditional.GroupCohomologyShapiroMap
import Sharpness.Unconditional.GroupCohomologyAmbientTransfer

/-! Native pullback along the canonical identification of a subgroup with its
nested subgroup type, computed on the same ambient bar resolution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory Finsupp
variable {R G H : Type u} [CommRing R] [Group G] [Group H]

/-- Restriction of both arguments of the Hom complex along a group homomorphism. -/
def homComplexRestrict (f : H →* G) (X : ChainComplex (Rep.{u} R G) ℕ)
    (V : Rep.{u} R G) : X.linearYonedaObj R V ⟶
      ChainComplex.linearYonedaObj
        (((Rep.resFunctor f).mapHomologicalComplex _).obj X) R (Rep.res f V) where
  f n := ModuleCat.ofHom ((Rep.resFunctor f).mapLinearMap R)
  comm' i j _ := by
    ext a
    exact ((Rep.resFunctor f).map_comp (X.d j i) a).symm

/-- Native pullback is restriction on the bar Hom model. -/
theorem bar_restriction_cochain_comparison (f : H →* G) (V : Rep.{u} R G) :
    (groupCohomology.inhomogeneousCochainsIso V).hom ≫
        homComplexRestrict f (Rep.barResolution R G).complex V ≫
        homComplexPrecomp (Rep.res f V) (barRestrictionChain f) =
      groupCohomology.cochainsMap f (𝟙 (Rep.res f V)) ≫
        (groupCohomology.inhomogeneousCochainsIso (Rep.res f V)).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Rep.free_ext
  intro y
  change (Rep.freeLift R G V x).hom
      ((barRestrictionComponent f n).hom (single y (single 1 1))) =
    (Rep.freeLift R H (Rep.res f V) (fun z => x (f ∘ z))).hom
      (single y (single 1 1))
  rw [barRestrictionComponent_single, map_one]
  simp [Rep.freeLift, Representation.freeLift_single_single]

/-- The literal change to a nested subgroup type is a map of Hom complexes. -/
def subgroupHomComplexToNested (P Q : Subgroup G) (h : P ≤ Q)
    (X : ChainComplex (Rep.{u} R G) ℕ) (V : Rep.{u} R G) :
    restrictedHomComplex P X V ⟶
      restrictedHomComplex (P.subgroupOf Q)
        (((Rep.resFunctor Q.subtype).mapHomologicalComplex _).obj X)
        (Rep.res Q.subtype V) :=
  homComplexRestrict (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
    (((Rep.resFunctor P.subtype).mapHomologicalComplex _).obj X) (Rep.res P.subtype V)

/-- Restrict the ambient bar resolution in two stages. -/
def nestedBarResolution (P Q : Subgroup G) :
    ProjectiveResolution (Rep.trivial R (P.subgroupOf Q) R) :=
  (Rep.resFunctor (P.subgroupOf Q).subtype).mapProjectiveResolution
    (ambientBarResolution (R := R) Q)

/-- The coordinate map from the nested group's bar resolution to the ambient bar. -/
def nestedBarChain (P Q : Subgroup G) :
    (Rep.barResolution R (P.subgroupOf Q)).complex ⟶
      (nestedBarResolution (R := R) P Q).complex :=
  barRestrictionChain (P.subgroupOf Q).subtype ≫
    ((Rep.resFunctor (P.subgroupOf Q).subtype).mapHomologicalComplex _).map
      (barRestrictionChain Q.subtype)

theorem nestedBarChain_augmentation (P Q : Subgroup G) :
    (nestedBarChain (R := R) P Q).f 0 ≫ (nestedBarResolution P Q).π.f 0 =
      (Rep.barResolution R (P.subgroupOf Q)).π.f 0 := by
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution R G).π.f 0).hom
      ((barRestrictionComponent Q.subtype 0).hom
        ((barRestrictionComponent (P.subgroupOf Q).subtype 0).hom
          (single x (single 1 1)))) =
    ((Rep.barResolution R (P.subgroupOf Q)).π.f 0).hom (single x (single 1 1))
  rw [barRestrictionComponent_single, map_one, barRestrictionComponent_single,
    map_one, barAugmentation_single, barAugmentation_single]

theorem nestedBarChain_cochain_factor (P Q : Subgroup G) (h : P ≤ Q)
    (V : Rep.{u} R G) :
    subgroupHomComplexToNested P Q h (Rep.barResolution R G).complex V ≫
        homComplexPrecomp (Rep.res (P.subgroupOf Q).subtype (Rep.res Q.subtype V))
          (nestedBarChain P Q) =
      homComplexPrecomp (Rep.res P.subtype V) (barRestrictionChain P.subtype) ≫
        homComplexRestrict (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
          (Rep.barResolution R P).complex (Rep.res P.subtype V) ≫
        homComplexPrecomp (Rep.res (P.subgroupOf Q).subtype (Rep.res Q.subtype V))
          (barRestrictionChain (Subgroup.subgroupOfEquivOfLe h).toMonoidHom) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Rep.res P.subtype (Rep.free R G (Fin n → G)) ⟶ Rep.res P.subtype V at a
  apply Rep.free_ext
  intro x
  change a.hom ((barRestrictionComponent Q.subtype n).hom
      ((barRestrictionComponent (P.subgroupOf Q).subtype n).hom
        (single x (single 1 1)))) =
    a.hom ((barRestrictionComponent P.subtype n).hom
      ((barRestrictionComponent (Subgroup.subgroupOfEquivOfLe h).toMonoidHom n).hom
        (single x (single 1 1))))
  apply congrArg a.hom
  rw [barRestrictionComponent_single (R := R), map_one,
    barRestrictionComponent_single (R := R), map_one,
    barRestrictionComponent_single (R := R), map_one,
    barRestrictionComponent_single (R := R), map_one]
  rfl

/-- Native pullback along the canonical subgroup equivalence is precisely
the literal change of equivariance group on the common ambient Hom complex. -/
theorem subgroupOfEquiv_pull_comparison {A : Type u} [AddCommGroup A] [Module R A]
    (P Q : Subgroup G) (h : P ≤ Q) (n : ℕ) :
    pull (R := R) (A := A) (Subgroup.subgroupOfEquivOfLe h).toMonoidHom n ≫
        (groupCohomologyIso (Rep.trivial R (P.subgroupOf Q) A) n
          (nestedBarResolution P Q)).hom =
      (ambientBarCohomologyIso P (Rep.trivial R G A) n).hom ≫
        HomologicalComplex.homologyMap
          (subgroupHomComplexToNested P Q h (Rep.barResolution R G).complex
            (Rep.trivial R G A)) n := by
  let V := Rep.trivial R G A
  let W := Rep.trivial R (P.subgroupOf Q) A
  let J := groupCohomologyIso W n (nestedBarResolution (R := R) P Q)
  let b := homComplexPrecomp W (nestedBarChain (R := R) P Q)
  have hn := groupCohomologyIso_hom_precomp (Rep.barResolution R (P.subgroupOf Q))
    (nestedBarResolution P Q) W (nestedBarChain P Q)
    (nestedBarChain_augmentation P Q) n
  rw [groupCohomologyIso_bar_hom] at hn
  have hn' : HomologicalComplex.homologyMap b n = J.inv ≫
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso W).hom n := by
    rw [← hn]
    simp [J, b]
  haveI : IsIso (HomologicalComplex.homologyMap b n) := by
    rw [hn']
    infer_instance
  have hp := groupCohomologyIso_hom_precomp (Rep.barResolution R P)
    (ambientBarResolution (R := R) P) (Rep.res P.subtype V)
    (barRestrictionChain P.subtype) (by
      have ha := barRestriction_augmentation (R := R) P
      erw [Category.comp_id] at ha
      exact ha) n
  rw [groupCohomologyIso_bar_hom] at hp
  let e := (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
  let a := homComplexPrecomp (Rep.res P.subtype V) (barRestrictionChain P.subtype)
  let c := homComplexRestrict e (Rep.barResolution R P).complex (Rep.res P.subtype V) ≫
    homComplexPrecomp W (barRestrictionChain e)
  let t := subgroupHomComplexToNested P Q h (Rep.barResolution R G).complex V
  have hf : t ≫ b = a ≫ c := nestedBarChain_cochain_factor P Q h V
  have hc : (groupCohomology.inhomogeneousCochainsIso (Rep.trivial R P A)).hom ≫ c =
      cochainPull (R := R) (A := A) e ≫
        (groupCohomology.inhomogeneousCochainsIso W).hom :=
    bar_restriction_cochain_comparison e (Rep.res P.subtype V)
  apply (cancel_mono (HomologicalComplex.homologyMap b n)).mp
  change (pull e n ≫ J.hom) ≫ HomologicalComplex.homologyMap b n =
    ((ambientBarCohomologyIso P V n).hom ≫ HomologicalComplex.homologyMap t n) ≫ _
  calc
    _ = pull e n ≫ HomologicalComplex.homologyMap
        (groupCohomology.inhomogeneousCochainsIso W).hom n := by
      rw [Category.assoc]
      exact congrArg (fun f => pull e n ≫ f) hn
    _ = HomologicalComplex.homologyMap
        (cochainPull e ≫ (groupCohomology.inhomogeneousCochainsIso W).hom) n := by
      rw [HomologicalComplex.homologyMap_comp]
      rfl
    _ = HomologicalComplex.homologyMap
        ((groupCohomology.inhomogeneousCochainsIso (Rep.trivial R P A)).hom ≫ c) n :=
      congrArg (fun f => HomologicalComplex.homologyMap f n) hc.symm
    _ = ((ambientBarCohomologyIso P V n).hom ≫ HomologicalComplex.homologyMap a n) ≫
        HomologicalComplex.homologyMap c n := by
      rw [HomologicalComplex.homologyMap_comp]
      exact congrArg (fun f => f ≫ HomologicalComplex.homologyMap c n) hp.symm
    _ = (ambientBarCohomologyIso P V n).hom ≫
        HomologicalComplex.homologyMap (a ≫ c) n := by
      simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
    _ = (ambientBarCohomologyIso P V n).hom ≫
        HomologicalComplex.homologyMap (t ≫ b) n :=
      congrArg (fun f => (ambientBarCohomologyIso P V n).hom ≫
        HomologicalComplex.homologyMap f n) hf.symm
    _ = _ := by simp only [HomologicalComplex.homologyMap_comp, Category.assoc]

end Sharpness.OrdinaryCohomology
