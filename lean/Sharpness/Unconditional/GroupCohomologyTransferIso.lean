import Sharpness.Unconditional.GroupCohomologyPullResolution
import Sharpness.Unconditional.GroupCohomologyTransferResolution
import Sharpness.Unconditional.GroupCohomologyHomTransport

/-! Covariance of native transfer under arbitrary group isomorphisms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G K : Type u} [CommRing R] [Group G] [Group K]

theorem homComplexTransfer_mulEquiv [Finite G] [Finite K]
    (e : G ≃* K) (H : Subgroup G) (X : ChainComplex (Rep.{u} R G) ℕ)
    (V : Rep.{u} R G) :
    homComplexTransfer H X V ≫ homComplexRestrict e.symm.toMonoidHom X V =
      homComplexRestrict (e.subgroupMap H).symm.toMonoidHom
          (((Rep.resFunctor H.subtype).mapHomologicalComplex _).obj X) (Rep.res H.subtype V) ≫
        homComplexTransfer (H.map e.toMonoidHom)
          (((Rep.resFunctor e.symm.toMonoidHom).mapHomologicalComplex _).obj X)
          (Rep.res e.symm.toMonoidHom V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact (homTransfer_transport e H (X.X n) V f).symm

private theorem homComplexPrecomp_id (V : Rep.{u} R G) (X : ChainComplex (Rep.{u} R G) ℕ) :
    homComplexPrecomp V (𝟙 X) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact Category.id_comp f

/-- Native transfer commutes with arbitrary group isomorphisms. -/
theorem transfer_mulEquiv [Finite G] [Finite K]
    {A : Type u} [AddCommGroup A] [Module R A]
    (e : G ≃* K) (H : Subgroup G) (n : ℕ) :
    transfer (R := R) (A := A) H n ≫ pull e.symm.toMonoidHom n =
      pull (e.subgroupMap H).symm.toMonoidHom n ≫
        transfer (R := R) (A := A) (H.map e.toMonoidHom) n := by
  let V := Rep.trivial R G A
  let W := Rep.trivial R K A
  let PG := Rep.barResolution R G
  let PK : ProjectiveResolution (Rep.trivial R K R) :=
    (Rep.resFunctor e.symm.toMonoidHom).mapProjectiveResolution PG
  let PH : ProjectiveResolution (Rep.trivial R H R) :=
    (Rep.resFunctor H.subtype).mapProjectiveResolution PG
  let HK := H.map e.toMonoidHom
  let PHK : ProjectiveResolution (Rep.trivial R HK R) :=
    (Rep.resFunctor HK.subtype).mapProjectiveResolution PK
  let PHK' : ProjectiveResolution (Rep.trivial R HK R) :=
    (Rep.resFunctor (e.subgroupMap H).symm.toMonoidHom).mapProjectiveResolution PH
  let VH := Rep.trivial R H A
  let VHK := Rep.trivial R HK A
  let JG := groupCohomologyIso V n PG
  let JK := groupCohomologyIso W n PK
  let JH := groupCohomologyIso VH n PH
  let JHK := groupCohomologyIso VHK n PHK
  have hπ : (𝟙 PHK.complex : PHK.complex ⟶ PHK'.complex).f 0 ≫
      PHK'.π.f 0 = PHK.π.f 0 := by
    apply Rep.hom_ext
    ext x
    change (PG.π.f 0).hom x = (PG.π.f 0).hom x
    rfl
  have hsame := groupCohomologyIso_hom_precomp PHK PHK' VHK
    (𝟙 PHK.complex : PHK.complex ⟶ PHK'.complex) hπ n
  erw [homComplexPrecomp_id, HomologicalComplex.homologyMap_id, Category.comp_id] at hsame
  have hG : pull (R := R) (A := A) e.symm.toMonoidHom n ≫ JK.hom =
      JG.hom ≫ HomologicalComplex.homologyMap
        (homComplexRestrict e.symm.toMonoidHom PG.complex V) n :=
    homomorphism_restriction_resolution_comparison e.symm.toMonoidHom PG V n
  have hH : pull (R := R) (A := A) (e.subgroupMap H).symm.toMonoidHom n ≫ JHK.hom =
      JH.hom ≫ HomologicalComplex.homologyMap
        (homComplexRestrict (e.subgroupMap H).symm.toMonoidHom PH.complex VH) n := by
    have h : pull (R := R) (A := A) (e.subgroupMap H).symm.toMonoidHom n ≫
        (groupCohomologyIso VHK n PHK').hom = JH.hom ≫
          HomologicalComplex.homologyMap
            (homComplexRestrict (e.subgroupMap H).symm.toMonoidHom PH.complex VH) n :=
      homomorphism_restriction_resolution_comparison (e.subgroupMap H).symm.toMonoidHom PH VH n
    rw [hsame] at h
    exact h
  have htG : transfer (R := R) (A := A) H n ≫ JG.hom =
      JH.hom ≫ HomologicalComplex.homologyMap (homComplexTransfer H PG.complex V) n :=
    corestriction_resolution_comparison H PG V n
  have htK : transfer (R := R) (A := A) HK n ≫ JK.hom =
      JHK.hom ≫ HomologicalComplex.homologyMap (homComplexTransfer HK PK.complex W) n :=
    corestriction_resolution_comparison HK PK W n
  have hc : homComplexTransfer H PG.complex V ≫
      homComplexRestrict e.symm.toMonoidHom PG.complex V =
    homComplexRestrict (e.subgroupMap H).symm.toMonoidHom PH.complex VH ≫
      homComplexTransfer HK PK.complex W := homComplexTransfer_mulEquiv e H PG.complex V
  apply (cancel_mono JK.hom).mp
  rw [Category.assoc, hG, ← Category.assoc, htG, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, hc,
    HomologicalComplex.homologyMap_comp, ← Category.assoc, ← hH,
    Category.assoc, ← htK, ← Category.assoc]

end Sharpness.OrdinaryCohomology
