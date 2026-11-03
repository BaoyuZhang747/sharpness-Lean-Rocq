import Sharpness.Unconditional.SubsystemCohomologyTransport
import Sharpness.Unconditional.NormalizerOrbitLocalCategory
import Sharpness.Manuscript.CohomologyUnconditional

/-! The actual ambient coefficient on the local normalizer collection is
naturally isomorphic to the native local group-cohomology coefficient.
No coefficient object or arrow is replaced by an abstract copy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Opposite
variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (σ : F.CentricChain)

/-- The actual ambient centric-orbit map on the normalizer collection. -/
def normalizerAmbientCollectionFunctor :
    (L.normalizerAmbientCollection p hS sat σ).Orbit ⥤ F.CentricOrbit where
  obj P := ⟨(F.subsystemOrbitFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
    (L.chainNormalizerSubsystemEmbedding p sat σ)).obj P.obj, P.property⟩
  map f := ObjectProperty.homMk
    ((F.subsystemOrbitFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
      (L.chainNormalizerSubsystemEmbedding p sat σ)).map f.hom)
  map_id P := by
    apply InducedCategory.hom_ext
    exact (F.subsystemOrbitFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
      (L.chainNormalizerSubsystemEmbedding p sat σ)).map_id P.obj
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (F.subsystemOrbitFunctor σ.normalizerSubgroup (L.chainNormalizerFusion σ)
      (L.chainNormalizerSubsystemEmbedding p sat σ)).map_comp f.hom g.hom

def normalizerLocalCohomologyCoefficient (n : ℕ) :
    CoefficientCategory R (L.normalizerAmbientCollection p hS sat σ).Orbit :=
  (L.normalizerAmbientCollection p hS sat σ).toCentric.op ⋙
    (L.chainNormalizerFusion σ).cohomologyCoefficient (R := R) (A := A) n

def normalizerAmbientCohomologyCoefficient (n : ℕ) :
    CoefficientCategory R (L.normalizerAmbientCollection p hS sat σ).Orbit :=
  (L.normalizerAmbientCollectionFunctor p hS sat σ).op ⋙
    F.cohomologyCoefficient (R := R) (A := A) n

/-- The components are the native pullbacks along actual subgroup-image equivalences. -/
def normalizerAmbientCohomologyIso (n : ℕ) :
    L.normalizerAmbientCohomologyCoefficient (R := R) (A := A) p hS sat σ n ≅
      L.normalizerLocalCohomologyCoefficient (R := R) (A := A) p hS sat σ n :=
  NatIso.ofComponents (fun P => OrdinaryCohomology.pullIso
    (σ.normalizerAmbientEquiv P.unop.obj.as.subgroup) n) (by
      intro P Q f
      exact (F.subsystemCohomologyOrbitIso (R := R) (A := A)
        σ.normalizerSubgroup (L.chainNormalizerFusion σ)
        (L.chainNormalizerSubsystemEmbedding p sat σ) n).hom.naturality f.unop.hom.op)

@[simp] theorem normalizerAmbientCohomologyIso_hom_app (n : ℕ)
    (P : (L.normalizerAmbientCollection p hS sat σ).Orbit) :
    (L.normalizerAmbientCohomologyIso (R := R) (A := A) p hS sat σ n).hom.app (op P) =
      OrdinaryCohomology.pull (σ.normalizerAmbientEquiv P.obj.as.subgroup).toMonoidHom n := rfl

/-- The ambient diagram has exactly the higher limits of the full local
centric diagram, with all comparison hypotheses proved. -/
def normalizerRepresentativeAmbientHigherLimitIso (d : F.NormalizerCategory) (n i : ℕ) :
    higherLimit (L.normalizerAmbientCohomologyCoefficient (R := R) (A := A) p hS sat
      (L.normalizerSylowRepresentative p hS sat d) n) i ≅
      higherLimit ((L.chainNormalizerFusion
        (L.normalizerSylowRepresentative p hS sat d)).cohomologyCoefficient
          (R := R) (A := A) n) i :=
  higherLimitIso (L.normalizerAmbientCohomologyIso p hS sat
    (L.normalizerSylowRepresentative p hS sat d) n) i ≪≫
  (L.normalizerRepresentativeCollectionHigherLimitIso p hS sat d R
    ((L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d)).cohomologyCoefficient
      (R := R) (A := A) n) i).symm

end Sharpness.FusionSystem.CentricLinkingSystem
