import Sharpness.Unconditional.GroupCohomologyTransferHom

/-! The cochain transfer on the restricted ambient bar resolution agrees with
the native inverse-Shapiro transfer. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory

variable {R G : Type u} [CommRing R] [Group G]

/-- Postcomposition in the coefficient representation, as a Hom cochain map. -/
def homComplexPostcomp (X : ChainComplex (Rep.{u} R G) ℕ)
    {V W : Rep.{u} R G} (a : V ⟶ W) : X.linearYonedaObj R V ⟶ X.linearYonedaObj R W where
  f n := ModuleCat.ofHom (Linear.rightComp R (X.X n) a)
  comm' i j _ := by
    ext f
    exact (Category.assoc (X.d j i) f a).symm

/-- The Hom transfer factors through the genuine coinduction adjunction isomorphism. -/
theorem homComplexTransfer_factor (H : Subgroup G) [H.FiniteIndex]
    (P : ProjectiveResolution (Rep.trivial R G R)) (V : Rep.{u} R G) :
    homComplexTransfer H P.complex V =
      (groupCohomology.linearYonedaObjResProjectiveResolutionIso P
        (Rep.res H.subtype V)).hom ≫ homComplexPostcomp P.complex (coinductionTrace H V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rfl

/-- Coefficient maps agree under the native inhomogeneous-cochain/Hom isomorphism. -/
theorem inhomogeneousCochainsIso_inv_postcomp {V W : Rep.{u} R G} (a : V ⟶ W) :
    (groupCohomology.inhomogeneousCochainsIso V).inv ≫
        groupCohomology.cochainsMap (MonoidHom.id G) a =
      homComplexPostcomp (Rep.barResolution R G).complex a ≫
        (groupCohomology.inhomogeneousCochainsIso W).inv := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The explicit transfer on the common bar model computes native corestriction. -/
theorem corestriction_eq_homComplexTransfer (H : Subgroup G) [H.FiniteIndex]
    (V : Rep.{u} R G) (n : ℕ) :
    corestriction H V n =
      (ambientBarCohomologyIso H V n).hom ≫
        HomologicalComplex.homologyMap
          (homComplexTransfer H (Rep.barResolution R G).complex V ≫
            (groupCohomology.inhomogeneousCochainsIso V).inv) n := by
  unfold corestriction groupCohomology.coindIso
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  change
    ((ambientBarCohomologyIso H V n).hom ≫ HomologicalComplex.homologyMap
      ((groupCohomology.linearYonedaObjResProjectiveResolutionIso
        (Rep.barResolution R G) (Rep.res H.subtype V)).hom ≫
        (groupCohomology.inhomogeneousCochainsIso
          (Rep.coind H.subtype (Rep.res H.subtype V))).inv) n) ≫
      HomologicalComplex.homologyMap
        (groupCohomology.cochainsMap (MonoidHom.id G) (coinductionTrace H V)) n = _
  rw [Category.assoc, ← HomologicalComplex.homologyMap_comp]
  congr 2

end Sharpness.OrdinaryCohomology
