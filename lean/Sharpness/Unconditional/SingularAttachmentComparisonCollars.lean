import Sharpness.Unconditional.SingularAttachmentComparisonRelativeCovers
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.CategoryTheory.Limits.MonoCoprod

/-! Actual relative attachment comparison from explicit open neighborhoods,
complement identifications, and geometric homotopy equivalences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open Sharpness.SingularChainExcision

variable (R : Type u) [CommRing R]

theorem singularChainsMap_mono {X Y : TopCat.{u}} (f : X ⟶ Y) [Mono f] :
    Mono ((SingularCohomology.chainsFunctor R).map f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  change Mono ((sigmaConst.obj (ModuleCat.of R R)).map ((TopCat.toSSet.map f).app (op ⦋n⦌)))
  infer_instance

def geometricHomotopyEquivChains {X Y : TopCat.{u}} (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv ((SingularCohomology.chainsFunctor R).obj X)
      ((SingularCohomology.chainsFunctor R).obj Y) where
  hom := (SingularCohomology.chainsFunctor R).map (TopCat.ofHom e.toFun)
  inv := (SingularCohomology.chainsFunctor R).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    let h : TopCat.Homotopy (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) :=
      e.left_inv.some
    have H := h.singularChainComplexFunctorObjMap (ModuleCat.of R R)
    change _root_.Homotopy ((SingularCohomology.chainsFunctor R).map
      (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun))
      ((SingularCohomology.chainsFunctor R).map (𝟙 X)) at H
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using H
  homotopyInvHomId := by
    let h : TopCat.Homotopy (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) :=
      e.right_inv.some
    have H := h.singularChainComplexFunctorObjMap (ModuleCat.of R R)
    change _root_.Homotopy ((SingularCohomology.chainsFunctor R).map
      (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun))
      ((SingularCohomology.chainsFunctor R).map (𝟙 Y)) at H
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using H

theorem geometricHomotopyEquivChains_quasiIso {X Y : TopCat.{u}}
    (e : ContinuousMap.HomotopyEquiv X Y) :
    QuasiIso ((SingularCohomology.chainsFunctor R).map (TopCat.ofHom e.toFun)) :=
  (geometricHomotopyEquivChains R e).quasiIso_hom

def relativeArrowMap {A B X Y : TopCat.{u}} (i : A ⟶ B) (j : X ⟶ Y)
    (p : A ⟶ X) (q : B ⟶ Y) (w : i ≫ q = p ≫ j) :
    cokernel ((SingularCohomology.chainsFunctor R).map i) ⟶
      cokernel ((SingularCohomology.chainsFunctor R).map j) :=
  cokernel.map _ _ ((SingularCohomology.chainsFunctor R).map p)
    ((SingularCohomology.chainsFunctor R).map q) (by
      rw [← (SingularCohomology.chainsFunctor R).map_comp,
        ← (SingularCohomology.chainsFunctor R).map_comp, w])

variable {A B X Y : TopCat.{u}} (i : A ⟶ B) (j : X ⟶ Y)
  (p : A ⟶ X) (q : B ⟶ Y) (w : i ≫ q = p ≫ j)
  {N : Set B} {M : Set Y} (hN : Set.MapsTo q N M)
  (eA : ContinuousMap.HomotopyEquiv A N) (eX : ContinuousMap.HomotopyEquiv X M)
  (hA : TopCat.ofHom eA.toFun ≫ subsetInclusion B N = i)
  (hX : TopCat.ofHom eX.toFun ≫ subsetInclusion Y M = j)

def collarRelativeMapLeft :
    cokernel ((SingularCohomology.chainsFunctor R).map i) ⟶
      cokernel ((SingularCohomology.chainsFunctor R).map (subsetInclusion B N)) :=
  relativeArrowMap R i (subsetInclusion B N) (TopCat.ofHom eA.toFun) (𝟙 B)
    (by simpa using hA.symm)

theorem collarRelativeMapLeft_quasiIso [Mono i] :
    QuasiIso (collarRelativeMapLeft R i eA hA) := by
  letI := geometricHomotopyEquivChains_quasiIso R (X := A) (Y := TopCat.of N) eA
  letI := singularChainsMap_mono R i
  unfold collarRelativeMapLeft relativeArrowMap
  apply cokernelMap_quasiIso_of_mono R

theorem collarRelativeMap_square :
    collarRelativeMapLeft R i eA hA ≫ relativeSubspaceMap R q hN =
      relativeArrowMap R i j p q w ≫ collarRelativeMapLeft R j eX hX := by
  apply (cancel_epi (cokernel.π _)).mp
  simp only [collarRelativeMapLeft, relativeArrowMap, relativeSubspaceMap,
    cokernel.map, cokernel.π_desc_assoc]
  rw [Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.id_comp]

include eA eX hA hX

theorem relativeArrowMap_quasiIso_of_neighborhoods [Mono i] [Mono j]
    (h : QuasiIso (relativeSubspaceMap R q hN)) :
    QuasiIso (relativeArrowMap R i j p q w) := by
  letI := h
  letI := collarRelativeMapLeft_quasiIso R i eA hA
  letI := collarRelativeMapLeft_quasiIso R j eX hX
  haveI : QuasiIso (relativeArrowMap R i j p q w ≫ collarRelativeMapLeft R j eX hX) := by
    rw [← collarRelativeMap_square R i j p q w hN eA eX hA hX]
    infer_instance
  exact quasiIso_of_comp_right _ (collarRelativeMapLeft R j eX hX)

/-- The collar excision criterion. All hypotheses describe actual spaces,
maps, open covers and homotopies; the relative chain comparison is proved. -/
theorem relativeAttachmentMap_quasiIso [Mono i] [Mono j]
    {U : Set B} {V : Set Y} (hU : Set.MapsTo q U V)
    (hUo : IsOpen U) (hNo : IsOpen N) (hB : ∀ b : B, b ∈ U ∨ b ∈ N)
    (hVo : IsOpen V) (hMo : IsOpen M) (hY : ∀ y : Y, y ∈ V ∨ y ∈ M)
    [IsIso (restrictedMap q hU)]
    [IsIso (restrictedMap q (intersectionMapsTo q hU hN))] :
    QuasiIso (relativeArrowMap R i j p q w) :=
  relativeArrowMap_quasiIso_of_neighborhoods R i j p q w hN eA eX hA hX
    (relativeSubspaceMap_quasiIso_of_openCovers R q hU hN hUo hNo hB hVo hMo hY)

end Sharpness.SingularAttachmentComparison
