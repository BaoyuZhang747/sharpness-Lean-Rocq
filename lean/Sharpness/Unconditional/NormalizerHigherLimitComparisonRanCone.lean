import Sharpness.Unconditional.NormalizerHigherLimitComparisonNative
import Sharpness.Unconditional.NormalizerOrbitPairLinkingLiftLadder
import Sharpness.Manuscript.CohomologyCoefficient

/-! The genuine native restriction transformation on the pair category.
Its naturality uses a linking lift of each simultaneous fusion extension.
No choice of a lift needs to compose: its actual natural transformation
already gives the exact equality on native group cohomology. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def normalizerPairSection (X : F.NormalizerOrbitPair) :
    SingleObj X.centric.obj.as.subgroup ⥤
      CostructuredArrow L.normalizerSubdivisionProjection (F.normalizerClass X.chain) :=
  (L.normalizerPairActingHom X).toFunctor ⋙ L.normalizerSubdivisionChainComparison X.chain

def normalizerPairSection_naturality {X Y : F.NormalizerOrbitPair}
    (f : X.centric.obj.as ⟶ Y.centric.obj.as)
    (a : F.NormalizerChainExtension X.chain Y.chain f) :
    L.normalizerPairSection X ⋙ CostructuredArrow.map
      (F.normalizerOrbitPairProjection.map (NormalizerOrbitPair.homMk f a)) ⟶
      f.val.toFunctor ⋙ L.normalizerPairSection Y :=
  SingleObj.natTrans
    (CostructuredArrow.homMk (L.normalizerPairLinkingLift f a)
      (by apply Subsingleton.elim)) (by
      intro x
      apply CostructuredArrow.hom_ext
      exact L.normalizerPairLinkingLift_intertwines f a x)

variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R) (n : ℕ)

def normalizerPairNativeComponent (X : F.NormalizerOrbitPair) :
    (L.normalizerOrdinaryDiagram R A n).obj (op (F.normalizerClass X.chain)) ⟶
      OrdinaryCohomology.value R X.centric.obj.as.subgroup A n :=
  OrdinaryCohomology.functorPull
    (L.normalizerPairSection X ⋙ L.normalizerRepresentativeReflection (F.normalizerClass X.chain)) n

theorem normalizerPairNativeComponent_eq (X : F.NormalizerOrbitPair) :
    L.normalizerPairNativeComponent R A n X =
      (L.normalizerNativeChainIso R A X.chain n).hom ≫
        OrdinaryCohomology.pull (L.normalizerPairActingHom X) n :=
  OrdinaryCohomology.functorPull_comp (L.normalizerPairActingHom X).toFunctor
    (L.normalizerSubdivisionChainComparison X.chain ⋙
      L.normalizerRepresentativeReflection (F.normalizerClass X.chain)) n

theorem normalizerPairNativeComponent_naturality_raw {X Y : F.NormalizerOrbitPair}
    (f : X.centric.obj.as ⟶ Y.centric.obj.as)
    (a : F.NormalizerChainExtension X.chain Y.chain f) :
    (L.normalizerOrdinaryDiagram R A n).map
        (F.normalizerOrbitPairProjection.map (NormalizerOrbitPair.homMk f a)).op ≫
        L.normalizerPairNativeComponent R A n X =
      L.normalizerPairNativeComponent R A n Y ≫ OrdinaryCohomology.pull f.val n :=
  NormalizerReflection.native_comparison_naturality
    (CostructuredArrow.functor L.normalizerSubdivisionProjection)
    (fun d => L.ChainAut (normalizerRepresentative (F := F) d))
    L.normalizerRepresentativeComparison L.normalizerRepresentativeReflection
    L.normalizerRepresentativeAdjunction
    (F.normalizerOrbitPairProjection.map (NormalizerOrbitPair.homMk f a)) f.val
    (L.normalizerPairSection_naturality f a) n

/-- Native restriction from the actual chain-automorphism diagram to the
native cohomology of each acting subgroup, as a genuine natural transformation. -/
def normalizerPairNativeRestriction :
    F.normalizerOrbitPairProjection.op ⋙ L.normalizerOrdinaryDiagram R A n ⟶
      F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n where
  app X := L.normalizerPairNativeComponent R A n X.unop
  naturality {X Y} f := by
    obtain ⟨g, hg, ⟨a⟩⟩ := f.unop.property
    have hf : f.unop = NormalizerOrbitPair.homMk g a := by
      apply NormalizerOrbitPair.hom_ext
      apply InducedCategory.hom_ext
      exact hg.symm
    have hf' : f = (NormalizerOrbitPair.homMk g a).op := congrArg Quiver.Hom.op hf
    subst f
    change (L.normalizerOrdinaryDiagram R A n).map
        (F.normalizerOrbitPairProjection.map (NormalizerOrbitPair.homMk g a)).op ≫ _ =
      _ ≫ (F.cohomologyOrbitCoefficient n).map (F.toOrbit.map g).op
    rw [F.cohomologyOrbitCoefficient_map_raw]
    exact L.normalizerPairNativeComponent_naturality_raw R A n g a

@[simp] theorem normalizerPairNativeRestriction_app (X : F.NormalizerOrbitPair) :
    (L.normalizerPairNativeRestriction R A n).app (op X) =
      (L.normalizerNativeChainIso R A X.chain n).hom ≫
        OrdinaryCohomology.pull (L.normalizerPairActingHom X) n :=
  L.normalizerPairNativeComponent_eq R A n X

end Sharpness.FusionSystem.CentricLinkingSystem
