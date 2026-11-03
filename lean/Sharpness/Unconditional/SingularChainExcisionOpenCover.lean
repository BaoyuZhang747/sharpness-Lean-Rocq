import Sharpness.Unconditional.SingularChainExcisionSequence
import Sharpness.Unconditional.SmallChainComparison
import Mathlib.Algebra.Homology.HomologySequence

/-! Open-cover Mayer--Vietoris from the constructed small-chain comparison.
The maps retain the actual topological subspace inclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularChainExcision
open CategoryTheory CategoryTheory.Limits
open Sharpness.RealizationUnitHomology

variable (R : Type u) [CommRing R] (X : TopCat.{u}) (U V : Set X)

theorem binarySmallChainsIso_hom_inclusion :
    (binarySmallChainsIso R X U V).hom ≫
      smallSingularChainsInclusion X (fun b : Bool => if b then U else V) R =
    SSet.chainComplexMap (singularInSubcomplex X U ⊔ singularInSubcomplex X V).ι
      (ModuleCat.of R R) := by
  change (chains R).map _ ≫ (chains R).map _ = (chains R).map _
  rw [← (chains R).map_comp]
  rfl

theorem binarySmallLeft_inclusion :
    binarySmallLeft R X U V ≫
      smallSingularChainsInclusion X (fun b : Bool => if b then U else V) R =
    (SingularCohomology.chainsFunctor R).map (subsetInclusion X U) := by
  unfold binarySmallLeft
  rw [Category.assoc, Category.assoc, binarySmallChainsIso_hom_inclusion]
  change _ ≫ ((chains R).map _ ≫ (chains R).map _) = _
  rw [← (chains R).map_comp]
  exact singularSubsetChainsIso_hom_inclusion X R U

theorem binarySmallRight_inclusion :
    binarySmallRight R X U V ≫
      smallSingularChainsInclusion X (fun b : Bool => if b then U else V) R =
    (SingularCohomology.chainsFunctor R).map (subsetInclusion X V) := by
  unfold binarySmallRight
  rw [Category.assoc, Category.assoc, binarySmallChainsIso_hom_inclusion]
  change _ ≫ ((chains R).map _ ≫ (chains R).map _) = _
  rw [← (chains R).map_comp]
  exact singularSubsetChainsIso_hom_inclusion X R V

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : ∀ x : X, x ∈ U ∨ x ∈ V)
include hU hV hcover

theorem binarySmallInclusion_quasiIso :
    QuasiIso (smallSingularChainsInclusion X (fun b : Bool => if b then U else V) R) := by
  apply smallSingularChainsInclusion_quasiIso R X
  · intro b
    cases b
    · exact hV
    · exact hU
  · intro x
    rcases hcover x with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩

def mayerVietorisHomologyIso (n : ℕ) :
    (subspaceUnionSequence R X U V).X₃.homology n ≅
      ((SingularCohomology.chainsFunctor R).obj X).homology n := by
  letI := binarySmallInclusion_quasiIso R X U V hU hV hcover
  exact isoOfQuasiIsoAt
    (smallSingularChainsInclusion X (fun b : Bool => if b then U else V) R) n

def mayerVietorisConnecting (n : ℕ) :
    ((SingularCohomology.chainsFunctor R).obj X).homology (n + 1) ⟶
      (subspaceUnionSequence R X U V).X₁.homology n :=
  (mayerVietorisHomologyIso R X U V hU hV hcover (n + 1)).inv ≫
    (subspaceUnionSequence_shortExact R X U V).δ (n + 1) n rfl

def mayerVietorisMiddle (n : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (HomologicalComplex.homologyMap (subspaceUnionSequence R X U V).f n)
    (HomologicalComplex.homologyMap (subspaceUnionSequence R X U V).g n ≫
      (mayerVietorisHomologyIso R X U V hU hV hcover n).hom) (by
        rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
          (subspaceUnionSequence R X U V).zero, HomologicalComplex.homologyMap_zero,
          Limits.zero_comp])

theorem mayerVietorisMiddle_exact (n : ℕ) :
    (mayerVietorisMiddle R X U V hU hV hcover n).Exact := by
  let h := (subspaceUnionSequence_shortExact R X U V).homology_exact₂ n
  apply ShortComplex.exact_of_iso _ h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (mayerVietorisHomologyIso R X U V hU hV hcover n) (by simp [mayerVietorisMiddle])
      (by simp [mayerVietorisMiddle])

def mayerVietorisAtAmbient (n : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (HomologicalComplex.homologyMap (subspaceUnionSequence R X U V).g (n + 1) ≫
      (mayerVietorisHomologyIso R X U V hU hV hcover (n + 1)).hom)
    (mayerVietorisConnecting R X U V hU hV hcover n) (by
      simp only [mayerVietorisConnecting, Category.assoc, Iso.hom_inv_id_assoc,
        ShortComplex.ShortExact.comp_δ])

theorem mayerVietorisAtAmbient_exact (n : ℕ) :
    (mayerVietorisAtAmbient R X U V hU hV hcover n).Exact := by
  let h := (subspaceUnionSequence_shortExact R X U V).homology_exact₃ (n + 1) n rfl
  apply ShortComplex.exact_of_iso _ h
  exact ShortComplex.isoMk (Iso.refl _)
    (mayerVietorisHomologyIso R X U V hU hV hcover (n + 1)) (Iso.refl _)
    (by simp [mayerVietorisAtAmbient])
    (by simp [mayerVietorisAtAmbient, mayerVietorisConnecting])

def mayerVietorisAtIntersection (n : ℕ) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (mayerVietorisConnecting R X U V hU hV hcover n)
    (HomologicalComplex.homologyMap (subspaceUnionSequence R X U V).f n) (by
      simp only [mayerVietorisConnecting, Category.assoc,
        ShortComplex.ShortExact.δ_comp, Limits.comp_zero])

theorem mayerVietorisAtIntersection_exact (n : ℕ) :
    (mayerVietorisAtIntersection R X U V hU hV hcover n).Exact := by
  let h := (subspaceUnionSequence_shortExact R X U V).homology_exact₁ (n + 1) n rfl
  apply ShortComplex.exact_of_iso _ h
  exact ShortComplex.isoMk
    (mayerVietorisHomologyIso R X U V hU hV hcover (n + 1)) (Iso.refl _) (Iso.refl _)
    (by simp [mayerVietorisAtIntersection, mayerVietorisConnecting])
    (by simp [mayerVietorisAtIntersection])

end Sharpness.SingularChainExcision
