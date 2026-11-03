import Sharpness.Unconditional.NormalizerDecompositionSharpness
import Sharpness.Unconditional.NormalizerHigherLimitComparisonUnconditional

/-! Sharpness of the actual normalizer decomposition, including the literal
restriction isomorphism. The ordinary higher-limit vanishing premise of the
elementary edge argument is supplied by the proved global comparison and
Diaz--Park theorem. No spectral sequence or auxiliary comparison input occurs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k)

include p hS sat in
theorem normalizerCohomology_acyclic_unconditional (n : ℕ) :
    Acyclic (L.canonicalLibmanNormalizerData.cohomologyDiagram k A n) :=
  L.normalizerCohomology_acyclic_of_ordinary k A
    (fun q => L.normalizerOrdinary_acyclic_unconditional p hS sat k A q) n

theorem normalizerRestrictionToLimit_isIso_unconditional (n : ℕ) :
    IsIso (L.normalizerRestrictionToLimit k p hS sat A n) :=
  L.normalizerRestrictionToLimit_isIso_of_ordinary_acyclic k p hS sat A
    (fun q => L.normalizerOrdinary_acyclic_unconditional p hS sat k A q) n

theorem normalizerOrdinaryRestrictionToLimit_isIso_unconditional (n : ℕ) :
    IsIso (L.normalizerOrdinaryRestrictionToLimit k p hS sat A n) :=
  L.normalizerOrdinaryRestrictionToLimit_isIso_of_ordinary_acyclic k p hS sat A
    (fun q => L.normalizerOrdinary_acyclic_unconditional p hS sat k A q) n

/-- Vanishing and the literal restriction isomorphism for every cohomology
degree and every trivial module over every field of characteristic p. -/
theorem centric_normalizer_decomposition_sharp_unconditional :
    (∀ i n : ℕ, 0 < i → IsZero
      (higherLimit (L.canonicalLibmanNormalizerData.cohomologyDiagram k A n) i)) ∧
      (∀ n : ℕ, IsIso (L.normalizerRestrictionToLimit k p hS sat A n)) :=
  L.normalizer_decomposition_sharp_of_ordinary_acyclic k p hS sat A
    (fun q => L.normalizerOrdinary_acyclic_unconditional p hS sat k A q)

def normalizerRestrictionIso_unconditional (n : ℕ) :
    SingularCohomology.cohomology k L.classifyingSpace A n ≅
      limit (L.canonicalLibmanNormalizerData.cohomologyDiagram k A n) := by
  letI := L.normalizerRestrictionToLimit_isIso_unconditional p hS sat k A n
  exact asIso (L.normalizerRestrictionToLimit k p hS sat A n)

@[simp] theorem normalizerRestrictionIso_unconditional_hom (n : ℕ) :
    (L.normalizerRestrictionIso_unconditional p hS sat k A n).hom =
      L.normalizerRestrictionToLimit k p hS sat A n := rfl

@[reassoc] theorem normalizerRestrictionIso_unconditional_component
    (n : ℕ) (d : F.NormalizerCategory) :
    (L.normalizerRestrictionIso_unconditional p hS sat k A n).hom ≫
        limit.π (L.canonicalLibmanNormalizerData.cohomologyDiagram k A n) (op d) =
      SingularCohomology.pull k
        ((L.canonicalLibmanNormalizerInput p hS sat).forgetMap d) A n :=
  L.normalizerRestrictionToLimit_component k p hS sat A n d

def normalizerOrdinaryRestrictionIso_unconditional (n : ℕ) :
    SingularCohomology.cohomology k L.classifyingSpace A n ≅
      limit (L.normalizerOrdinaryDiagram k A n) := by
  letI := L.normalizerOrdinaryRestrictionToLimit_isIso_unconditional p hS sat k A n
  exact asIso (L.normalizerOrdinaryRestrictionToLimit k p hS sat A n)

@[simp] theorem normalizerOrdinaryRestrictionIso_unconditional_hom (n : ℕ) :
    (L.normalizerOrdinaryRestrictionIso_unconditional p hS sat k A n).hom =
      L.normalizerOrdinaryRestrictionToLimit k p hS sat A n := rfl

@[reassoc] theorem normalizerOrdinaryRestrictionIso_unconditional_component
    (n : ℕ) (d : F.NormalizerCategory) :
    (L.normalizerOrdinaryRestrictionIso_unconditional p hS sat k A n).hom ≫
        limit.π (L.normalizerOrdinaryDiagram k A n) (op d) =
      SingularCohomology.pull k
        ((L.canonicalLibmanNormalizerInput p hS sat).forgetMap d) A n ≫
          (L.normalizerOrdinaryDiagramIso_unconditional k A n).hom.app (op d) :=
  L.normalizerOrdinaryRestrictionToLimit_component k p hS sat A n d

end Sharpness.FusionSystem.CentricLinkingSystem
