import Sharpness.V28.NormalizerComparison
import Sharpness.Unconditional.NormalizerDecompositionSharpness

/-! Sharpness and the actual geometric and ordinary normalizer restriction maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem.V28
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k)

include p hS sat

theorem normalizerCohomology_acyclic (n : ℕ) :
    Acyclic (L.canonicalLibmanNormalizerData.cohomologyDiagram k A n) :=
  L.normalizerCohomology_acyclic_of_ordinary k A
    (fun q => normalizerOrdinary_acyclic L p hS sat k A q) n

theorem normalizerRestrictionToLimit_isIso (n : ℕ) :
    IsIso (L.normalizerRestrictionToLimit k p hS sat A n) :=
  L.normalizerRestrictionToLimit_isIso_of_ordinary_acyclic k p hS sat A
    (fun q => normalizerOrdinary_acyclic L p hS sat k A q) n

theorem normalizer_decomposition_sharp :
    (∀ i n : ℕ, 0 < i → IsZero
      (higherLimit (L.canonicalLibmanNormalizerData.cohomologyDiagram k A n) i)) ∧
      (∀ n : ℕ, IsIso (L.normalizerRestrictionToLimit k p hS sat A n)) :=
  L.normalizer_decomposition_sharp_of_ordinary_acyclic k p hS sat A
    (fun q => normalizerOrdinary_acyclic L p hS sat k A q)

theorem normalizerOrdinaryRestrictionToLimit_isIso (n : ℕ) :
    IsIso (L.normalizerOrdinaryRestrictionToLimit k p hS sat A n) :=
  L.normalizerOrdinaryRestrictionToLimit_isIso_of_ordinary_acyclic k p hS sat A
    (fun q => normalizerOrdinary_acyclic L p hS sat k A q) n

def normalizerRestrictionIso (n : ℕ) :
    SingularCohomology.cohomology k L.classifyingSpace A n ≅
      limit (L.canonicalLibmanNormalizerData.cohomologyDiagram k A n) := by
  letI := normalizerRestrictionToLimit_isIso L p hS sat k A n
  exact asIso (L.normalizerRestrictionToLimit k p hS sat A n)

theorem normalizerRestrictionIso_hom (n : ℕ) :
    (normalizerRestrictionIso L p hS sat k A n).hom =
      L.normalizerRestrictionToLimit k p hS sat A n := rfl

theorem normalizerRestrictionIso_component (n : ℕ) (d : F.NormalizerCategory) :
    (normalizerRestrictionIso L p hS sat k A n).hom ≫
        limit.π (L.canonicalLibmanNormalizerData.cohomologyDiagram k A n) (op d) =
      SingularCohomology.pull k
        ((L.canonicalLibmanNormalizerInput p hS sat).forgetMap d) A n :=
  L.normalizerRestrictionToLimit_component k p hS sat A n d

def normalizerOrdinaryRestrictionIso (n : ℕ) :
    SingularCohomology.cohomology k L.classifyingSpace A n ≅
      limit (L.normalizerOrdinaryDiagram k A n) := by
  letI := normalizerOrdinaryRestrictionToLimit_isIso L p hS sat k A n
  exact asIso (L.normalizerOrdinaryRestrictionToLimit k p hS sat A n)

theorem normalizerOrdinaryRestrictionIso_hom (n : ℕ) :
    (normalizerOrdinaryRestrictionIso L p hS sat k A n).hom =
      L.normalizerOrdinaryRestrictionToLimit k p hS sat A n := rfl

theorem normalizerOrdinaryRestrictionIso_component (n : ℕ) (d : F.NormalizerCategory) :
    (normalizerOrdinaryRestrictionIso L p hS sat k A n).hom ≫
        limit.π (L.normalizerOrdinaryDiagram k A n) (op d) =
      SingularCohomology.pull k
        ((L.canonicalLibmanNormalizerInput p hS sat).forgetMap d) A n ≫
          (L.normalizerOrdinaryDiagramIso_unconditional k A n).hom.app (op d) :=
  L.normalizerOrdinaryRestrictionToLimit_component k p hS sat A n d

end Sharpness.FusionSystem.CentricLinkingSystem.V28
