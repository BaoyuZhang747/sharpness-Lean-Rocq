import Sharpness.Unconditional.SingularAttachmentComparisonCollars
import Sharpness.Unconditional.SingularAttachmentComparisonFiveLemma
import Sharpness.Unconditional.SingularAttachmentComparisonUnitCoproducts

/-! Native realization-unit comparison across a simplicial attachment.
The relative singular comparison is an explicit input here, to be supplied
by the proved geometric collar criterion for actual cell attachments. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open Sharpness.SingularChainExcision

variable (R : Type u) [CommRing R]

theorem simplicialChainsMap_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    Mono ((simplicialChainsFunctor R).map i) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono ((sigmaConst.obj (ModuleCat.of R R)).map (i.app (op ⦋n⦌)))
  infer_instance

def relativeUnitChainMap {A B : SSet.{u}} (i : A ⟶ B) :
    cokernel ((simplicialChainsFunctor R).map i) ⟶
      cokernel ((SingularCohomology.chainsFunctor R).map (SSet.toTop.map i)) :=
  cokernel.map _ _ (realizationUnitChainMap R A) (realizationUnitChainMap R B)
    (realizationUnitChainMap_naturality R i)

def relativeUnitSequenceMap {A B : SSet.{u}} (i : A ⟶ B) :
    ShortComplex.cokernelSequence ((simplicialChainsFunctor R).map i) ⟶
      ShortComplex.cokernelSequence
        ((SingularCohomology.chainsFunctor R).map (SSet.toTop.map i)) where
  τ₁ := realizationUnitChainMap R A
  τ₂ := realizationUnitChainMap R B
  τ₃ := relativeUnitChainMap R i
  comm₁₂ := (realizationUnitChainMap_naturality R i).symm
  comm₂₃ := by simp [relativeUnitChainMap]

theorem relativeUnitChainMap_quasiIso_of_units {A B : SSet.{u}} (i : A ⟶ B)
    [Mono i] [Mono (SSet.toTop.map i)]
    [QuasiIso (realizationUnitChainMap R A)] [QuasiIso (realizationUnitChainMap R B)] :
    QuasiIso (relativeUnitChainMap R i) := by
  letI := simplicialChainsMap_mono R i
  letI := singularChainsMap_mono R (SSet.toTop.map i)
  exact cokernelMap_quasiIso_of_mono R ((simplicialChainsFunctor R).map i)
    ((SingularCohomology.chainsFunctor R).map (SSet.toTop.map i))
    (realizationUnitChainMap R A) (realizationUnitChainMap R B)
    (realizationUnitChainMap_naturality R i)

theorem realizationUnitChainMap_quasiIso_of_relative {A B : SSet.{u}} (i : A ⟶ B)
    [Mono i] [Mono (SSet.toTop.map i)]
    [QuasiIso (realizationUnitChainMap R A)] [QuasiIso (relativeUnitChainMap R i)] :
    QuasiIso (realizationUnitChainMap R B) := by
  letI := simplicialChainsMap_mono R i
  letI := singularChainsMap_mono R (SSet.toTop.map i)
  letI : QuasiIso (relativeUnitSequenceMap R i).τ₁ := by
    change QuasiIso (realizationUnitChainMap R A)
    infer_instance
  letI : QuasiIso (relativeUnitSequenceMap R i).τ₃ := by
    change QuasiIso (relativeUnitChainMap R i)
    infer_instance
  exact shortExact_middle_quasiIso (relativeUnitSequenceMap R i)
    (monoCokernelSequence_shortExact R _) (monoCokernelSequence_shortExact R _)

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {p : A ⟶ X} {q : B ⟶ Y} {j : X ⟶ Y}
  (h : IsPushout i p q j)

def simplicialPushoutRelativeMap :
    cokernel ((simplicialChainsFunctor R).map i) ⟶
      cokernel ((simplicialChainsFunctor R).map j) := by
  haveI : PreservesColimit (span i p) (simplicialChainsFunctor R) := by
    change PreservesColimit (span i p) (chains R)
    infer_instance
  exact cokernel.map _ _ ((simplicialChainsFunctor R).map p)
    ((simplicialChainsFunctor R).map q) (h.map (simplicialChainsFunctor R)).w

theorem simplicialPushoutRelativeMap_isIso : IsIso (simplicialPushoutRelativeMap R h) := by
  haveI : PreservesColimit (span i p) (simplicialChainsFunctor R) := by
    change PreservesColimit (span i p) (chains R)
    infer_instance
  exact isIso_cokernel_map_of_isPushout (h.map (simplicialChainsFunctor R))

def realizedPushoutRelativeMap :
    cokernel ((SingularCohomology.chainsFunctor R).map (SSet.toTop.map i)) ⟶
      cokernel ((SingularCohomology.chainsFunctor R).map (SSet.toTop.map j)) :=
  relativeArrowMap R (SSet.toTop.map i) (SSet.toTop.map j)
    (SSet.toTop.map p) (SSet.toTop.map q) (h.map SSet.toTop).w

theorem relativeUnitChainMap_pushout_naturality :
    simplicialPushoutRelativeMap R h ≫ relativeUnitChainMap R j =
      relativeUnitChainMap R i ≫ realizedPushoutRelativeMap R h := by
  apply (cancel_epi (cokernel.π _)).mp
  simp only [simplicialPushoutRelativeMap, relativeUnitChainMap,
    realizedPushoutRelativeMap, relativeArrowMap, cokernel.map, cokernel.π_desc_assoc]
  rw [Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc,
    ← Category.assoc, ← Category.assoc, realizationUnitChainMap_naturality R q]

/-- The actual unit on a pushout follows from the three known units and
the actual relative singular attachment comparison. -/
theorem realizationUnitChainMap_pushout_quasiIso
    [Mono i] [Mono j] [Mono (SSet.toTop.map i)] [Mono (SSet.toTop.map j)]
    [QuasiIso (realizationUnitChainMap R A)] [QuasiIso (realizationUnitChainMap R B)]
    [QuasiIso (realizationUnitChainMap R X)]
    (hrel : QuasiIso (realizedPushoutRelativeMap R h)) :
    QuasiIso (realizationUnitChainMap R Y) := by
  letI := hrel
  letI := simplicialPushoutRelativeMap_isIso R h
  letI := relativeUnitChainMap_quasiIso_of_units R i
  haveI : QuasiIso (simplicialPushoutRelativeMap R h ≫ relativeUnitChainMap R j) := by
    rw [relativeUnitChainMap_pushout_naturality]
    infer_instance
  letI := quasiIso_of_comp_left (simplicialPushoutRelativeMap R h) (relativeUnitChainMap R j)
  exact realizationUnitChainMap_quasiIso_of_relative R j

end Sharpness.SingularAttachmentComparison
