import Sharpness.Unconditional.CentralizerCoverFiberFull

/-! The fiber of the cover projection is the actual centralizer centric
orbit category, compatibly with the ambient centric-orbit inclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (C : F.AKOCentralizerInput p hS sat E)

private theorem cover_object_ext {A B : F.CentralizerCover p}
    (hC : A.centric = B.centric) (hE : A.elementary = B.elementary) : A = B := by
  cases A
  cases B
  cases hC
  cases hE
  rfl

theorem localCentricToCoverFiber_obj_surjective :
    Function.Surjective (F.localCentricToCoverFiber p hS sat E C).obj := by
  intro X
  let A := X.val.obj
  let T := F.centralizerGroup p E
  have hE : A.elementary = E.obj.subgroup :=
    congrArg (fun D : (F.ElementaryCategory p)ᵒᵖ => D.unop.obj.subgroup) X.property
  have hAT : A.centric.obj.as.subgroup ≤ T := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    have hzA : z ∈ A.elementary := hE.symm ▸ hz
    exact ((Subgroup.mem_centralizer_iff.mp (A.centralizes hzA)) x hx).symm
  let P := A.centric.obj.as.subgroup.subgroupOf T
  have hambient : ambientSubgroup T P = A.centric.obj.as.subgroup :=
    ambientSubgroup_subgroupOf T _ hAT
  have hPc : C.system.IsCentric P := by
    apply ((F.yalcinCentralizerCentricInput p hS sat E C).lemma_8_11 P).1.mpr
    rw [hambient]
    exact A.centric.property
  let L : C.system.CentricOrbit := ⟨C.system.toOrbit.obj ⟨P⟩, hPc⟩
  refine ⟨L, ?_⟩
  apply Subtype.ext
  apply ObjectProperty.FullSubcategory.ext
  apply cover_object_ext F p
  · apply ObjectProperty.FullSubcategory.ext
    change F.toOrbit.obj ⟨ambientSubgroup T P⟩ = A.centric.obj
    rw [hambient]
    rfl
  · exact hE.symm

instance localCentricToCoverFiber_essSurj : (F.localCentricToCoverFiber p hS sat E C).EssSurj :=
  (F.localCentricToCoverFiber p hS sat E C).essSurj_of_surj
    (F.localCentricToCoverFiber_obj_surjective p hS sat E C)

instance localCentricToCoverFiber_isEquivalence :
    (F.localCentricToCoverFiber p hS sat E C).IsEquivalence where

def centralizerCoverFiberEquivalence : C.system.CentricOrbit ≌
    Functor.Fiber (F.centralizerCoverProjection p) (op E) :=
  (F.localCentricToCoverFiber p hS sat E C).asEquivalence

theorem localCentricToCoverFiber_forget :
    F.localCentricToCoverFiber p hS sat E C ⋙ Functor.Fiber.fiberInclusion ⋙
      F.centralizedCentralizerCoverInclusion p ⋙ F.centralizerCoverForget p =
    F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
      (F.yalcinCentralizerCentricInput p hS sat E C).centric := rfl

end Sharpness.FusionSystem
