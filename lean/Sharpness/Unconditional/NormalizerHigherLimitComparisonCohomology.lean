import Sharpness.Unconditional.NormalizerHigherLimitComparisonMaps
import Sharpness.Unconditional.CanonicalLibmanNormalizerData
import Sharpness.Unconditional.HeterogeneousNerveAdjunction
import Sharpness.RealizationPullQuasiIso
import Sharpness.CanonicalClassifyingCochains
import Sharpness.NormalizerCochainDiagram
import Sharpness.Unconditional.ProjectiveCoefficients

/-! Comparison of the actual singular-cohomology diagram with the native
chain-automorphism cohomology diagram, for every commutative ring and every
constant module. The comparison is natural in every indexing arrow, not
merely objectwise. The sole geometric premise is the realization-unit
chain theorem, isolated by its existing interface. This file does not
assert normalizer sharpness or compare with centric-orbit higher limits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
universe u

namespace Sharpness.OrdinaryCohomology
open CategoryTheory
variable {R G H : Type u} [CommRing R] [Group G] [Group H]
    {A : ModuleCat.{u} R}

theorem canonicalClassifyingIso_functor (real : RealizationUnitInput.{u} R)
    (T : SingleObj G ⥤ SingleObj H) (n : ℕ) :
    SingularCohomology.pull R (SSet.toTop.map (nerveMap T)) A n ≫
        (canonicalClassifyingIso R G A real n).hom =
      (canonicalClassifyingIso R H A real n).hom ≫ functorPull T n := by
  have h := canonicalClassifyingIso_group (R := R) (A := A) real
    ((SingleObj.mapHom G H).symm T) n
  simpa only [classifyingMap, classifyingSpace, functorPull, Equiv.apply_symm_apply] using h

end Sharpness.OrdinaryCohomology

namespace Sharpness.NormalizerReflection
open CategoryTheory CategoryTheory.Limits Opposite
variable {D : Type u} [Category.{u} D] (K : D ⥤ Cat.{u,u})
    (G : D → Type u) [∀ d, Group (G d)]
    (J : ∀ d, SingleObj (G d) ⥤ K.obj d)
    (P : ∀ d, K.obj d ⥤ SingleObj (G d))
    (adj : ∀ d, P d ⊣ J d)
    (R : Type u) [CommRing R] (A : ModuleCat.{u} R)
    (real : RealizationUnitInput.{u} R)

def spaceCoefficient (n : ℕ) : Dᵒᵖ ⥤ ModuleCat.{u} R :=
  (K ⋙ nerveFunctor ⋙ SSet.toTop).op ⋙ SingularCohomology.cochainFunctor R A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n

def comparisonIso (d : D) (n : ℕ) :
    (spaceCoefficient K R A n).obj (op d) ≅ OrdinaryCohomology.value R (G d) A n := by
  letI : QuasiIso ((simplicialChainsFunctor R).map (heterogeneousNerveMap (J d))) :=
    heterogeneousNerveAdjunction_right_quasiIso (adj d) (ModuleCat.of R R)
  letI := realizationCochainPull_quasiIso R (heterogeneousNerveMap (J d)) A real
  exact asIso (HomologicalComplex.homologyMap
      (SingularCohomology.cochainPull R (SSet.toTop.map (heterogeneousNerveMap (J d))) A) n) ≪≫
    OrdinaryCohomology.canonicalClassifyingIso R (G d) A real n

theorem comparisonIso_hom (d : D) (n : ℕ) :
    (comparisonIso K G J P adj R A real d n).hom =
      SingularCohomology.pull R (SSet.toTop.map (heterogeneousNerveMap (J d))) A n ≫
        (OrdinaryCohomology.canonicalClassifyingIso R (G d) A real n).hom := rfl

theorem comparisonIso_naturality {d e : D} (f : d ⟶ e) (n : ℕ) :
    (spaceCoefficient K R A n).map f.op ≫ (comparisonIso K G J P adj R A real d n).hom =
      (comparisonIso K G J P adj R A real e n).hom ≫
        OrdinaryCohomology.functorPull (arrowFunctor K G J P f) n := by
  let T := arrowFunctor K G J P f
  let η : J d ⋙ (K.map f).toFunctor ⟶ T ⋙ J e :=
    Functor.whiskerLeft (J d ⋙ (K.map f).toFunctor) (adj e).unit
  have h := realizationHomotopy (heterogeneousNerveHomotopy η)
  have hl : heterogeneousNerveMap (J d ⋙ (K.map f).toFunctor) =
      heterogeneousNerveMap (J d) ≫ nerveMap (K.map f).toFunctor := rfl
  have hr : heterogeneousNerveMap (T ⋙ J e) =
      nerveMap T ≫ heterogeneousNerveMap (J e) := rfl
  rw [hl, hr, SSet.toTop.map_comp, SSet.toTop.map_comp] at h
  rw [comparisonIso_hom, comparisonIso_hom]
  change SingularCohomology.pull R (SSet.toTop.map (nerveMap (K.map f).toFunctor)) A n ≫
      (SingularCohomology.pull R (SSet.toTop.map (heterogeneousNerveMap (J d))) A n ≫ _) = _
  rw [← Category.assoc, ← SingularCohomology.pull_comp,
    SingularCohomology.pull_eq_of_homotopy R h A n, SingularCohomology.pull_comp,
    Category.assoc, OrdinaryCohomology.canonicalClassifyingIso_functor real T n,
    ← Category.assoc]

/-- All arrows use the actual induced group homomorphisms. -/
def coefficientIso (n : ℕ) :
    spaceCoefficient K R A n ≅ coefficient K G J P adj R A n :=
  NatIso.ofComponents (fun d => comparisonIso K G J P adj R A real d.unop n)
    (fun f => comparisonIso_naturality K G J P adj R A real f.unop n)

/-- The native Ext higher limits of the two actual diagrams agree in every degree. -/
def higherLimitIso (n i : ℕ) :
    higherLimit (spaceCoefficient K R A n) i ≅
      higherLimit (coefficient K G J P adj R A n) i :=
  Sharpness.higherLimitIso (coefficientIso K G J P adj R A real n) i

end Sharpness.NormalizerReflection

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)
    (R : Type u) [CommRing R] (A : ModuleCat.{u} R)
    (real : RealizationUnitInput.{u} R)

def normalizerOrdinaryDiagramIso (n : ℕ) :
    L.canonicalLibmanNormalizerData.cohomologyDiagram R A n ≅
      L.normalizerOrdinaryDiagram R A n :=
  NormalizerReflection.coefficientIso (CostructuredArrow.functor L.normalizerSubdivisionProjection)
    (fun d => L.ChainAut (normalizerRepresentative (F := F) d))
    L.normalizerRepresentativeComparison L.normalizerRepresentativeReflection
    L.normalizerRepresentativeAdjunction R A real n

def normalizerOrdinaryHigherLimitIso (n i : ℕ) :
    higherLimit (L.canonicalLibmanNormalizerData.cohomologyDiagram R A n) i ≅
      higherLimit (L.normalizerOrdinaryDiagram R A n) i :=
  Sharpness.higherLimitIso (L.normalizerOrdinaryDiagramIso R A real n) i

end Sharpness.FusionSystem.CentricLinkingSystem
