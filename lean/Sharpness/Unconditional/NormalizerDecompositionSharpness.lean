import Sharpness.Unconditional.NormalizerDecompositionAugmentation
import Sharpness.Unconditional.ElementaryReplacementLimitEdge

/-! The literal normalizer restriction is the actual augmentation followed by
the elementary replacement edge. Positive higher-limit vanishing is kept as
an explicit premise here; no normalizer vanishing theorem is assumed as data.
The comparison applies to every commutative coefficient ring and module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (A : ModuleCat.{u} R)

/-- Restriction along the actual forgetful cocone of the canonical model. -/
def normalizerRestrictionToLimit (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ⟶
      limit (L.canonicalLibmanNormalizerData.cohomologyDiagram R A n) :=
  (L.canonicalLibmanNormalizerInput p hS sat).restrictionToLimit R A n

@[reassoc] theorem normalizerRestrictionToLimit_component
    (n : ℕ) (d : F.NormalizerCategory) :
    L.normalizerRestrictionToLimit R p hS sat A n ≫
        limit.π (L.canonicalLibmanNormalizerData.cohomologyDiagram R A n) (op d) =
      SingularCohomology.pull R
        ((L.canonicalLibmanNormalizerInput p hS sat).forgetMap d) A n :=
  (L.canonicalLibmanNormalizerInput p hS sat).restrictionToLimit_component R A n d

theorem normalizerRestrictionToLimit_eq_elementary (n : ℕ) :
    L.normalizerRestrictionToLimit R p hS sat A n =
      HomologicalComplex.homologyMap
        ((L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A) n ≫
        elementaryReplacementLimitEdge
          (L.canonicalLibmanNormalizerData.cochainDiagram R A) n := by
  apply limit.hom_ext
  intro d
  calc
    _ = SingularCohomology.pull R
        ((L.canonicalLibmanNormalizerInput p hS sat).forgetMap d.unop) A n :=
      L.normalizerRestrictionToLimit_component R p hS sat A n d.unop
    _ = HomologicalComplex.homologyMap
        ((L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A) n ≫
          HomologicalComplex.homologyMap
            (L.normalizerDecompositionTotalProjection R A d.unop) n :=
      (L.normalizerDecompositionCohomologyIso_component R p hS sat A d.unop n).symm
    _ = HomologicalComplex.homologyMap
        ((L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A) n ≫
          (elementaryReplacementLimitEdge
            (L.canonicalLibmanNormalizerData.cochainDiagram R A) n ≫
              limit.π (L.canonicalLibmanNormalizerData.cohomologyDiagram R A n) d) :=
      congrArg (fun t => HomologicalComplex.homologyMap
        ((L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A) n ≫ t)
        (elementaryReplacementLimitEdge_component
          (L.canonicalLibmanNormalizerData.cochainDiagram R A) n d.unop).symm
    _ = _ := (Category.assoc _ _ _).symm

theorem normalizerRestrictionToLimit_isIso_of_acyclic
    (h : ∀ q, Acyclic (L.canonicalLibmanNormalizerData.cohomologyDiagram R A q))
    (n : ℕ) : IsIso (L.normalizerRestrictionToLimit R p hS sat A n) := by
  letI := L.canonicalNormalizerCochainAugmentation_quasiIso_unconditional R p hS sat A
  letI := elementaryReplacementLimitEdge_isIso
    (L.canonicalLibmanNormalizerData.cochainDiagram R A)
    (fun q j => h q (j+1) (Nat.succ_pos _)) n
  rw [L.normalizerRestrictionToLimit_eq_elementary R p hS sat A n]
  infer_instance

theorem normalizerCohomology_acyclic_of_ordinary
    (h : ∀ q, Acyclic (L.normalizerOrdinaryDiagram R A q)) (n : ℕ) :
    Acyclic (L.canonicalLibmanNormalizerData.cohomologyDiagram R A n) :=
  acyclic_of_iso (L.normalizerOrdinaryDiagramIso_unconditional R A n) (h n)

theorem normalizerRestrictionToLimit_isIso_of_ordinary_acyclic
    (h : ∀ q, Acyclic (L.normalizerOrdinaryDiagram R A q)) (n : ℕ) :
    IsIso (L.normalizerRestrictionToLimit R p hS sat A n) :=
  L.normalizerRestrictionToLimit_isIso_of_acyclic R p hS sat A
    (L.normalizerCohomology_acyclic_of_ordinary R A h) n

/-- The actual ordinary-cohomology restriction cone is obtained by the proved
all-arrow comparison of the two actual diagrams. -/
def normalizerOrdinaryRestrictionCone (n : ℕ) :
    Cone (L.normalizerOrdinaryDiagram R A n) where
  pt := SingularCohomology.cohomology R L.classifyingSpace A n
  π := ((L.canonicalLibmanNormalizerInput p hS sat).restrictionCone R A n).π ≫
    (L.normalizerOrdinaryDiagramIso_unconditional R A n).hom

def normalizerOrdinaryRestrictionToLimit (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ⟶
      limit (L.normalizerOrdinaryDiagram R A n) :=
  limit.lift _ (L.normalizerOrdinaryRestrictionCone R p hS sat A n)

@[reassoc] theorem normalizerOrdinaryRestrictionToLimit_component
    (n : ℕ) (d : F.NormalizerCategory) :
    L.normalizerOrdinaryRestrictionToLimit R p hS sat A n ≫
        limit.π (L.normalizerOrdinaryDiagram R A n) (op d) =
      SingularCohomology.pull R
        ((L.canonicalLibmanNormalizerInput p hS sat).forgetMap d) A n ≫
          (L.normalizerOrdinaryDiagramIso_unconditional R A n).hom.app (op d) :=
  limit.lift_π _ _

theorem normalizerOrdinaryRestrictionToLimit_eq (n : ℕ) :
    L.normalizerOrdinaryRestrictionToLimit R p hS sat A n =
      L.normalizerRestrictionToLimit R p hS sat A n ≫
        (HasLimit.isoOfNatIso (L.normalizerOrdinaryDiagramIso_unconditional R A n)).hom := by
  apply limit.hom_ext
  intro d
  rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc,
    normalizerRestrictionToLimit_component]
  exact limit.lift_π _ _

theorem normalizerOrdinaryRestrictionToLimit_eq_elementary (n : ℕ) :
    L.normalizerOrdinaryRestrictionToLimit R p hS sat A n =
      HomologicalComplex.homologyMap
        ((L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A) n ≫
          elementaryReplacementLimitEdge
            (L.canonicalLibmanNormalizerData.cochainDiagram R A) n ≫
              (HasLimit.isoOfNatIso
                (L.normalizerOrdinaryDiagramIso_unconditional R A n)).hom := by
  rw [L.normalizerOrdinaryRestrictionToLimit_eq R p hS sat A n,
    L.normalizerRestrictionToLimit_eq_elementary R p hS sat A n, Category.assoc]

theorem normalizerOrdinaryRestrictionToLimit_isIso_of_ordinary_acyclic
    (h : ∀ q, Acyclic (L.normalizerOrdinaryDiagram R A q)) (n : ℕ) :
    IsIso (L.normalizerOrdinaryRestrictionToLimit R p hS sat A n) := by
  letI := L.normalizerRestrictionToLimit_isIso_of_ordinary_acyclic R p hS sat A h n
  rw [L.normalizerOrdinaryRestrictionToLimit_eq R p hS sat A n]
  infer_instance

/-- Both sharpness conclusions for the literal geometric normalizer diagram,
conditional only on the stated actual ordinary higher-limit vanishing. -/
theorem normalizer_decomposition_sharp_of_ordinary_acyclic
    (h : ∀ q, Acyclic (L.normalizerOrdinaryDiagram R A q)) :
    (∀ i n : ℕ, 0 < i → IsZero
      (higherLimit (L.canonicalLibmanNormalizerData.cohomologyDiagram R A n) i)) ∧
      (∀ n : ℕ, IsIso (L.normalizerRestrictionToLimit R p hS sat A n)) :=
  ⟨fun i n hi => L.normalizerCohomology_acyclic_of_ordinary R A h n i hi,
    fun n => L.normalizerRestrictionToLimit_isIso_of_ordinary_acyclic R p hS sat A h n⟩

def normalizerRestrictionIso_of_ordinary_acyclic
    (h : ∀ q, Acyclic (L.normalizerOrdinaryDiagram R A q)) (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ≅
      limit (L.canonicalLibmanNormalizerData.cohomologyDiagram R A n) := by
  letI := L.normalizerRestrictionToLimit_isIso_of_ordinary_acyclic R p hS sat A h n
  exact asIso (L.normalizerRestrictionToLimit R p hS sat A n)

@[simp] theorem normalizerRestrictionIso_of_ordinary_acyclic_hom
    (h : ∀ q, Acyclic (L.normalizerOrdinaryDiagram R A q)) (n : ℕ) :
    (L.normalizerRestrictionIso_of_ordinary_acyclic R p hS sat A h n).hom =
      L.normalizerRestrictionToLimit R p hS sat A n := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
