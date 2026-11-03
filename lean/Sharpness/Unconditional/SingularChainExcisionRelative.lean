import Sharpness.Unconditional.SingularChainExcisionOpenCover
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-! Relative singular-chain excision for an actual binary open cover.
The quotient complexes and map are native cokernels of subspace inclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularChainExcision
open CategoryTheory CategoryTheory.Limits
open Sharpness.RealizationUnitHomology

variable (R : Type u) [CommRing R]

theorem monoCokernelSequence_shortExact
    {A B : ChainComplex (ModuleCat.{u} R) ℕ} (f : A ⟶ B) [Mono f] :
    (ShortComplex.cokernelSequence f).ShortExact where
  exact := ShortComplex.cokernelSequence_exact f
  mono_f := by change Mono f; infer_instance

theorem cokernelMap_quasiIso_of_mono
    {A B A' B' : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : A ⟶ B) (g : A' ⟶ B') (p : A ⟶ A') (q : B ⟶ B')
    (w : f ≫ q = p ≫ g) [Mono f] [Mono g] [QuasiIso p] [QuasiIso q] :
    QuasiIso (cokernel.map f g p q w) := by
  let φ : ShortComplex.cokernelSequence f ⟶ ShortComplex.cokernelSequence g :=
    { τ₁ := p
      τ₂ := q
      τ₃ := cokernel.map f g p q w
      comm₁₂ := w.symm
      comm₂₃ := by simp }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (monoCokernelSequence_shortExact R f) (monoCokernelSequence_shortExact R g)
    inferInstance inferInstance

instance subcomplexInclusionChains_mono {K : SSet.{u}} (A : K.Subcomplex) :
    Mono (SSet.chainComplexMap A.ι (ModuleCat.of R R)) := by
  haveI : IsIso (⊤ : K.Subcomplex).ι :=
    (Subfunctor.eq_top_iff_isIso _).mp rfl
  have h : SSet.chainComplexMap A.ι (ModuleCat.of R R) =
      SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_top : A ≤ ⊤)) (ModuleCat.of R R) ≫
        SSet.chainComplexMap (⊤ : K.Subcomplex).ι (ModuleCat.of R R) := by
    change (chains R).map _ = (chains R).map _ ≫ (chains R).map _
    rw [← (chains R).map_comp]
    rfl
  rw [h]
  infer_instance

variable (X : TopCat.{u}) (U V : Set X)

instance subsetInclusionChains_mono :
    Mono ((SingularCohomology.chainsFunctor R).map (subsetInclusion X U)) := by
  rw [← singularSubsetChainsIso_hom_inclusion X R U]
  infer_instance

instance binarySmallRight_mono : Mono (binarySmallRight R X U V) := by
  unfold binarySmallRight
  infer_instance

/-- The first excision map is already an isomorphism at chain level. -/
def relativeSmallExcisionMap :
    cokernel ((SingularCohomology.chainsFunctor R).map
      (subsetMap X (Set.inter_subset_left : U ∩ V ⊆ U))) ⟶
      cokernel (binarySmallRight R X U V) :=
  cokernel.map _ _
    ((SingularCohomology.chainsFunctor R).map
      (subsetMap X (Set.inter_subset_right : U ∩ V ⊆ V)))
    (binarySmallLeft R X U V) (subspaceUnion_isPushout R X U V).w

instance relativeSmallExcisionMap_isIso : IsIso (relativeSmallExcisionMap R X U V) :=
  isIso_cokernel_map_of_isPushout (subspaceUnion_isPushout R X U V)

def relativeSmallInclusionMap :
    cokernel (binarySmallRight R X U V) ⟶
      cokernel ((SingularCohomology.chainsFunctor R).map (subsetInclusion X V)) :=
  cokernel.map _ _ (𝟙 _)
    (smallSingularChainsInclusion X (fun b : Bool => if b then U else V) R)
    (by simpa using binarySmallRight_inclusion R X U V)

/-- The literal relative chain map induced by (U,U∩V) → (X,V). -/
def relativeExcisionMap :
    cokernel ((SingularCohomology.chainsFunctor R).map
      (subsetMap X (Set.inter_subset_left : U ∩ V ⊆ U))) ⟶
      cokernel ((SingularCohomology.chainsFunctor R).map (subsetInclusion X V)) :=
  cokernel.map _ _
    ((SingularCohomology.chainsFunctor R).map
      (subsetMap X (Set.inter_subset_right : U ∩ V ⊆ V)))
    ((SingularCohomology.chainsFunctor R).map (subsetInclusion X U)) (by
      rw [← (SingularCohomology.chainsFunctor R).map_comp,
        ← (SingularCohomology.chainsFunctor R).map_comp]
      rfl)

theorem relativeExcisionMap_factorization :
    relativeSmallExcisionMap R X U V ≫ relativeSmallInclusionMap R X U V =
      relativeExcisionMap R X U V := by
  apply (cancel_epi (cokernel.π _)).mp
  simp only [relativeSmallExcisionMap, relativeSmallInclusionMap,
    relativeExcisionMap, cokernel.map, cokernel.π_desc_assoc, cokernel.π_desc]
  rw [Category.assoc, cokernel.π_desc, ← Category.assoc, binarySmallLeft_inclusion]

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : ∀ x : X, x ∈ U ∨ x ∈ V)
include hU hV hcover

theorem relativeSmallInclusionMap_quasiIso :
    QuasiIso (relativeSmallInclusionMap R X U V) := by
  letI := binarySmallInclusion_quasiIso R X U V hU hV hcover
  exact cokernelMap_quasiIso_of_mono R _ _ (𝟙 _)
    (smallSingularChainsInclusion X (fun b : Bool => if b then U else V) R)
    (by simpa using binarySmallRight_inclusion R X U V)

theorem relativeExcisionMap_quasiIso : QuasiIso (relativeExcisionMap R X U V) := by
  letI := relativeSmallInclusionMap_quasiIso R X U V hU hV hcover
  rw [← relativeExcisionMap_factorization]
  infer_instance

def relativeExcisionHomologyIso (n : ℕ) :
    (cokernel ((SingularCohomology.chainsFunctor R).map
      (subsetMap X (Set.inter_subset_left : U ∩ V ⊆ U)))).homology n ≅
      (cokernel ((SingularCohomology.chainsFunctor R).map
        (subsetInclusion X V))).homology n := by
  letI := relativeExcisionMap_quasiIso R X U V hU hV hcover
  exact isoOfQuasiIsoAt (relativeExcisionMap R X U V) n

end Sharpness.SingularChainExcision
