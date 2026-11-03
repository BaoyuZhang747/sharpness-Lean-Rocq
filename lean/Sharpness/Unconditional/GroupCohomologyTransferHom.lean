import Sharpness.Unconditional.GroupCohomologyTransferConstruction

/-!
# Transfer on the Hom model of group cohomology

Restriction and transfer are defined before taking cohomology. They apply to
an arbitrary complex of representations, and hence in particular to the same
ambient bar resolution restricted to different subgroups.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory
open scoped BigOperators

variable {R G : Type u} [CommRing R] [Group G]

/-- Transfer of an equivariant map, obtained from the coinduction adjunction and trace. -/
def homTransfer (H : Subgroup G) [H.FiniteIndex] (X V : Rep.{u} R G) :
    (Rep.res H.subtype X ⟶ Rep.res H.subtype V) →ₗ[R] (X ⟶ V) :=
  (Linear.rightComp R X (coinductionTrace H V)).comp
    (Rep.resCoindHomEquiv.{u} H.subtype X (Rep.res H.subtype V)).toLinearMap

theorem homTransfer_def (H : Subgroup G) [H.FiniteIndex] (X V : Rep.{u} R G)
    (f : Rep.res H.subtype X ⟶ Rep.res H.subtype V) :
    homTransfer H X V f =
      Rep.resCoindToHom H.subtype X (Rep.res H.subtype V) f ≫ coinductionTrace H V :=
  rfl

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

set_option backward.isDefEq.respectTransparency false in
/-- The Hom-model transfer is the classical coset sum. -/
theorem homTransfer_apply (H : Subgroup G) [H.FiniteIndex] (X V : Rep.{u} R G)
    (f : Rep.res H.subtype X ⟶ Rep.res H.subtype V) (x : X) :
    (homTransfer H X V f).hom x =
      ∑ q : Quotient (QuotientGroup.rightRel H), V.ρ q.out⁻¹ (f.hom (X.ρ q.out x)) := by
  rw [homTransfer_def]
  change (coinductionTrace H V).hom
    ((Rep.resCoindToHom H.subtype X (Rep.res H.subtype V) f).hom x) = _
  rw [coinductionTrace_apply]
  rfl

/-- Transfer commutes with precomposition by an ambient equivariant map. -/
theorem homTransfer_precomp (H : Subgroup G) [H.FiniteIndex]
    {X Y V : Rep.{u} R G} (a : X ⟶ Y)
    (f : Rep.res H.subtype Y ⟶ Rep.res H.subtype V) :
    homTransfer H X V ((Rep.resFunctor H.subtype).map a ≫ f) =
      a ≫ homTransfer H Y V f := by
  rw [homTransfer_def, homTransfer_def, ← Category.assoc]
  congr 1
  apply Rep.hom_ext
  ext x g
  simp [Rep.resCoindToHom, Rep.hom_comm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Transfer commutes with postcomposition by an ambient equivariant map. -/
theorem homTransfer_postcomp (H : Subgroup G) [H.FiniteIndex]
    {X V W : Rep.{u} R G}
    (f : Rep.res H.subtype X ⟶ Rep.res H.subtype V) (a : V ⟶ W) :
    homTransfer H X W (f ≫ (Rep.resFunctor H.subtype).map a) =
      homTransfer H X V f ≫ a := by
  rw [homTransfer_def, homTransfer_def, Category.assoc]
  rw [← coinductionTrace_naturality H a, ← Category.assoc]
  congr 1

/-- Restriction applied to the first and second arguments of a Hom complex. -/
abbrev restrictedHomComplex (H : Subgroup G) (X : ChainComplex (Rep.{u} R G) ℕ)
    (V : Rep.{u} R G) : CochainComplex (ModuleCat R) ℕ :=
  ChainComplex.linearYonedaObj
    (((Rep.resFunctor H.subtype).mapHomologicalComplex _).obj X) R (Rep.res H.subtype V)

/-- Literal restriction of equivariant maps gives a map of Hom cochain complexes. -/
def homComplexRestriction (H : Subgroup G) (X : ChainComplex (Rep.{u} R G) ℕ)
    (V : Rep.{u} R G) : X.linearYonedaObj R V ⟶ restrictedHomComplex H X V where
  f n := ModuleCat.ofHom ((Rep.resFunctor H.subtype).mapLinearMap R)
  comm' i j _ := by
    ext f
    exact ((Rep.resFunctor H.subtype).map_comp (X.d j i) f).symm

/-- The actual Hom-model transfer is a cochain map. -/
def homComplexTransfer (H : Subgroup G) [H.FiniteIndex]
    (X : ChainComplex (Rep.{u} R G) ℕ) (V : Rep.{u} R G) :
    restrictedHomComplex H X V ⟶ X.linearYonedaObj R V where
  f n := ModuleCat.ofHom (homTransfer H (X.X n) V)
  comm' i j _ := by
    ext f
    exact (homTransfer_precomp H (X.d j i) f).symm

/-- The common ambient bar resolution, restricted to a subgroup. -/
def ambientBarResolution (H : Subgroup G) :
    ProjectiveResolution (Rep.trivial R H R) :=
  (Rep.resFunctor H.subtype).mapProjectiveResolution (Rep.barResolution R G)

/-- Native group cohomology is computed by the restricted ambient bar Hom complex. -/
def ambientBarCohomologyIso (H : Subgroup G) (V : Rep.{u} R G) (n : ℕ) :
    groupCohomology (Rep.res H.subtype V) n ≅
      (restrictedHomComplex H (Rep.barResolution R G).complex V).homology n :=
  groupCohomologyIso (Rep.res H.subtype V) n (ambientBarResolution H)

end Sharpness.OrdinaryCohomology
