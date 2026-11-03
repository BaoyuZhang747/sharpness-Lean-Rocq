import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Sharpness.Unconditional.GroupCohomologyResolutionNaturality

/-! Identification of the native Shapiro map with restriction and evaluation
at the identity. All comparison maps use the actual projective bar resolution. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory Finsupp
open scoped TensorProduct

variable {R G H : Type u} [CommRing R] [Group G] [Group H]

/-- The standard bar map induced by a group homomorphism. -/
def barRestrictionComponent (f : H →* G) (n : ℕ) :
    Rep.free R H (Fin n → H) ⟶ Rep.res f (Rep.free R G (Fin n → G)) :=
  Rep.freeLift R H _ fun x => single (f ∘ x) (single 1 1)

@[simp]
theorem barRestrictionComponent_single (f : H →* G) (n : ℕ)
    (x : Fin n → H) (h : H) (r : R) :
    (barRestrictionComponent (R := R) f n).hom (single x (single h r)) =
      single (f ∘ x) (single (f h) r) := by
  simp [barRestrictionComponent, Rep.freeLift, Representation.freeLift_single_single,
    smul_single, smul_eq_mul]

theorem barRestrictionComponent_comm (f : H →* G) (n : ℕ) :
    barRestrictionComponent (R := R) f (n + 1) ≫
        (Rep.resFunctor f).map (Rep.barComplex.d R G n) =
      Rep.barComplex.d R H n ≫ barRestrictionComponent f n := by
  apply Rep.free_ext
  intro x
  simp [Rep.barComplex.d, barRestrictionComponent, Rep.freeLift,
    Representation.freeLift_single_single, map_add, map_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Fin.comp_contractNth (· * ·) (· * ·) (map_mul f)]

/-- Applying the homomorphism to each bar coordinate is a chain map. -/
def barRestrictionChain (f : H →* G) :
    Rep.barComplex R H ⟶
      ((Rep.resFunctor f).mapHomologicalComplex _).obj (Rep.barComplex R G) where
  f n := barRestrictionComponent f n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    simpa only [Functor.mapHomologicalComplex_obj_d, Rep.barComplex, ChainComplex.of_d]
      using barRestrictionComponent_comm (R := R) f j

/-- The bar augmentation sends each standard free generator to one. -/
theorem barAugmentation_single (x : Fin 0 → G) :
    ((Rep.barResolution R G).π.f 0).hom (single x (single 1 1)) = (1 : R) := by
  simp only [Rep.barResolution, HomologicalComplex.comp_f, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply, Rep.barComplex.isoStandardComplex,
    HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.symm_hom]
  change (Rep.standardComplex.ε R G).hom
    ((Rep.diagonalSuccIsoFree R G 0).inv.hom (single x (single 1 1))) = (1 : R)
  simp [Rep.standardComplex.ε, Rep.diagonalSuccIsoFree, Rep.μ_hom,
    Representation.linearizeOfMulActionIso, Representation.linearizeTrivialIso]
  change Finsupp.linearCombination R (fun _ : Fin 1 → G => (1 : R))
    ((Representation.linearizeMap (Action.diagonalSuccIsoTensorTrivial G 0).inv)
      ((Representation.LinearizeMonoidal.μ (Action.leftRegular G)
        (Action.trivial G (Fin 0 → G)))
        (single (1 : G) (1 : R) ⊗ₜ[R] single x (1 : R)))) = 1
  rw [Representation.LinearizeMonoidal.μ_apply_single_single]
  erw [Representation.linearizeMap_single]
  simp

/-- Restriction of the ambient bar resolution has the expected augmentation. -/
theorem barRestriction_augmentation (K : Subgroup G) :
    (barRestrictionChain (R := R) K.subtype).f 0 ≫
        ((Rep.resFunctor K.subtype).mapProjectiveResolution (Rep.barResolution R G)).π.f 0 =
      (Rep.barResolution R K).π.f 0 ≫ 𝟙 (Rep.trivial R K R) := by
  erw [Category.comp_id]
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution R G).π.f 0).hom
      ((barRestrictionComponent K.subtype 0).hom (single x (single 1 1))) =
    ((Rep.barResolution R K).π.f 0).hom (single x (single 1 1))
  rw [barRestrictionComponent_single, map_one, barAugmentation_single,
    barAugmentation_single]

/-- The canonical restriction chain map is a map of projective resolutions
lifting the identity of the trivial representation. -/
def barRestrictionResolutionHom (K : Subgroup G) :
    ProjectiveResolution.Hom (Rep.barResolution R K)
      ((Rep.resFunctor K.subtype).mapProjectiveResolution (Rep.barResolution R G))
      (𝟙 (Rep.trivial R K R)) where
  hom := barRestrictionChain K.subtype
  hom_f_zero_comp_π_f_zero := by
    simpa only [ChainComplex.single₀_map_f_zero] using
      barRestriction_augmentation (R := R) K

/-- At cochain level, the coinduction adjunction and bar restriction are
restriction of cochain coordinates followed by evaluation at the identity. -/
theorem shapiro_cochain_comparison (K : Subgroup G) (A : Rep.{u} R K) :
    (groupCohomology.inhomogeneousCochainsIso (Rep.coind K.subtype A)).hom ≫
        (groupCohomology.linearYonedaObjResProjectiveResolutionIso
          (Rep.barResolution R G) A).inv ≫
        homComplexPrecomp A (barRestrictionChain K.subtype) =
      groupCohomology.cochainsMap K.subtype
        ((Rep.resCoindAdjunction.{u} R K.subtype).counit.app A) ≫
        (groupCohomology.inhomogeneousCochainsIso A).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Rep.free_ext
  intro y
  change ((Rep.resCoindHomEquiv.{u} K.subtype (Rep.free R G (Fin n → G)) A).symm
      (Rep.freeLift R G (Rep.coind K.subtype A) x)).hom
        ((barRestrictionComponent K.subtype n).hom (single y (single 1 1))) =
    (Rep.freeLift R K A (fun z =>
      ((Rep.resCoindAdjunction.{u} R K.subtype).counit.app A).hom (x (K.subtype ∘ z)))).hom
      (single y (single 1 1))
  rw [barRestrictionComponent_single, map_one]
  simp [Rep.resCoindHomEquiv, Rep.freeLift, Representation.freeLift_single_single,
    Rep.resCoindAdjunction]

/-- The forward map of native Shapiro is precisely ordinary restriction,
followed by evaluation of a coinduced coefficient at the identity. -/
theorem coindIso_hom_eq_map (K : Subgroup G) (A : Rep.{u} R K) (n : ℕ) :
    (groupCohomology.coindIso A n).hom =
      groupCohomology.map K.subtype
        ((Rep.resCoindAdjunction.{u} R K.subtype).counit.app A) n := by
  let P := (Rep.resFunctor K.subtype).mapProjectiveResolution (Rep.barResolution R G)
  have hφ : (barRestrictionChain (R := R) K.subtype).f 0 ≫ P.π.f 0 =
      (Rep.barResolution R K).π.f 0 := by
    have h := barRestriction_augmentation (R := R) K
    erw [Category.comp_id] at h
    exact h
  have hc := groupCohomologyIso_hom_precomp (Rep.barResolution R K) P A
    (barRestrictionChain K.subtype) hφ n
  rw [groupCohomologyIso_bar_hom] at hc
  apply (cancel_mono (HomologicalComplex.homologyMap
    (groupCohomology.inhomogeneousCochainsIso A).hom n)).mp
  calc
    _ = HomologicalComplex.homologyMap
        ((groupCohomology.inhomogeneousCochainsIso (Rep.coind K.subtype A)).hom ≫
          (groupCohomology.linearYonedaObjResProjectiveResolutionIso
            (Rep.barResolution R G) A).inv) n ≫
          HomologicalComplex.homologyMap
            (homComplexPrecomp A (barRestrictionChain K.subtype)) n := by
      change (HomologicalComplex.homologyMap
        ((groupCohomology.inhomogeneousCochainsIso (Rep.coind K.subtype A)).hom ≫
          (groupCohomology.linearYonedaObjResProjectiveResolutionIso
            (Rep.barResolution R G) A).inv) n ≫
          (groupCohomologyIso A n P).inv) ≫ _ = _
      rw [Category.assoc, ← hc, Iso.inv_hom_id_assoc]
    _ = _ := by
      simpa only [HomologicalComplex.homologyMap_comp, Category.assoc,
        groupCohomology.map] using
        congrArg (fun f => HomologicalComplex.homologyMap f n)
          (shapiro_cochain_comparison K A)

end Sharpness.OrdinaryCohomology
