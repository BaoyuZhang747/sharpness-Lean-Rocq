import Sharpness.Unconditional.GroupCohomologyTransferComparison
import Sharpness.Unconditional.GroupCohomologyResolutionNaturality

/-! Native transfer may be computed on any projective resolution of the trivial
representation, in particular a bar resolution inherited from an ambient group. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory

variable {R G : Type u} [CommRing R] [Group G]

/-- The Hom-complex transfer is natural in an arbitrary map of ambient complexes. -/
theorem homComplexTransfer_precomp (H : Subgroup G) [H.FiniteIndex]
    {X Y : ChainComplex (Rep.{u} R G) ℕ} (φ : X ⟶ Y) (V : Rep.{u} R G) :
    homComplexPrecomp (Rep.res H.subtype V)
        (((Rep.resFunctor H.subtype).mapHomologicalComplex _).map φ) ≫
          homComplexTransfer H X V =
      homComplexTransfer H Y V ≫ homComplexPrecomp V φ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact homTransfer_precomp H (φ.f n) f

/-- Native transfer in the ambient group's own bar model, with both comparisons explicit. -/
theorem corestriction_bar_comparison (H : Subgroup G) [H.FiniteIndex]
    (V : Rep.{u} R G) (n : ℕ) :
    corestriction H V n ≫ (groupCohomologyIso V n (Rep.barResolution R G)).hom =
      (ambientBarCohomologyIso H V n).hom ≫
        HomologicalComplex.homologyMap
          (homComplexTransfer H (Rep.barResolution R G).complex V) n := by
  rw [corestriction_eq_homComplexTransfer, groupCohomologyIso_bar_hom]
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Restriction carries the augmentation condition of a comparison map to the
augmentation condition for the restricted projective resolutions. -/
theorem restricted_resolution_comparison_zero (H : Subgroup G)
    (P Q : ProjectiveResolution (Rep.trivial R G R))
    (φ : P.complex ⟶ Q.complex) (hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0) :
    ((((Rep.resFunctor H.subtype).mapHomologicalComplex _).map φ).f 0) ≫
        ((Rep.resFunctor H.subtype).mapProjectiveResolution Q).π.f 0 =
      ((Rep.resFunctor H.subtype).mapProjectiveResolution P).π.f 0 := by
  change (Rep.resFunctor H.subtype).map (φ.f 0) ≫
      ((Rep.resFunctor H.subtype).map (Q.π.f 0) ≫ _) =
    (Rep.resFunctor H.subtype).map (P.π.f 0) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, hφ]

/-- Transfer computed on any actual projective resolution agrees with native
corestriction. No comparison or transfer coherence is supplied as an assumption. -/
theorem corestriction_resolution_comparison (H : Subgroup G) [H.FiniteIndex]
    (P : ProjectiveResolution (Rep.trivial R G R)) (V : Rep.{u} R G) (n : ℕ) :
    corestriction H V n ≫ (groupCohomologyIso V n P).hom =
      (groupCohomologyIso (Rep.res H.subtype V) n
        ((Rep.resFunctor H.subtype).mapProjectiveResolution P)).hom ≫
        HomologicalComplex.homologyMap (homComplexTransfer H P.complex V) n := by
  let Q := Rep.barResolution R G
  let φ := ProjectiveResolution.lift (𝟙 (Rep.trivial R G R)) P Q
  have hφ : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 := by
    simp [φ]
  have hG := groupCohomologyIso_hom_precomp P Q V φ hφ n
  have hH := groupCohomologyIso_hom_precomp
    ((Rep.resFunctor H.subtype).mapProjectiveResolution P)
    ((Rep.resFunctor H.subtype).mapProjectiveResolution Q)
    (Rep.res H.subtype V)
    (((Rep.resFunctor H.subtype).mapHomologicalComplex _).map φ)
    (restricted_resolution_comparison_zero H P Q φ hφ) n
  rw [← hG, ← Category.assoc, corestriction_bar_comparison]
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← homComplexTransfer_precomp, HomologicalComplex.homologyMap_comp,
    ← Category.assoc]
  exact congrArg (fun f => f ≫
    HomologicalComplex.homologyMap (homComplexTransfer H P.complex V) n) hH

end Sharpness.OrdinaryCohomology
