import Sharpness.Unconditional.RealizationUnitHomologySmallChains
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! The actual short exact chain sequence of two simplicial subcomplexes.
The proof uses native subcomplex pushouts and explicit degreewise retractions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace Sharpness.SingularChainExcision
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable (R : Type u) [CommRing R]

abbrev chains : SSet.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)

instance chains_preservesColimitsOfShape (J : Type v) [Category.{w} J] :
    PreservesColimitsOfShape J (chains R) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J
    ((evaluation _ _).obj (op ⦋n⦌) ⋙ sigmaConst.obj (ModuleCat.of R R))
  infer_instance

variable {X : SSet.{u}} {A B : X.Subcomplex}

def subcomplexDegreeRetraction (_h : A ≤ B) (n : ℕ) :
    (B.toSSet.chainComplex (ModuleCat.of R R)).X n ⟶
      (A.toSSet.chainComplex (ModuleCat.of R R)).X n := by
  classical
  exact Sigma.desc fun σ => if ha : σ.val ∈ A.obj (op ⦋n⦌) then
    A.toSSet.ιChainComplex ⟨σ.val, ha⟩ else 0

theorem subcomplexDegreeRetraction_id (h : A ≤ B) (n : ℕ) :
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) (ModuleCat.of R R)).f n ≫
      subcomplexDegreeRetraction R h n = 𝟙 _ := by
  classical
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  change Sigma.ι (fun _ : B.obj (op ⦋n⦌) => ModuleCat.of R R) _ ≫ Sigma.desc _ = _
  rw [Sigma.ι_desc]
  change (if ha : σ.val ∈ A.obj (op ⦋n⦌) then A.toSSet.ιChainComplex ⟨σ.val, ha⟩ else 0) =
    A.toSSet.ιChainComplex σ ≫ 𝟙 _
  rw [dif_pos σ.property, Category.comp_id]
  rfl

instance subcomplexChainMap_degree_mono (h : A ≤ B) (n : ℕ) :
    Mono ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) (ModuleCat.of R R)).f n) := by
  letI : IsSplitMono ((SSet.chainComplexMap (SSet.Subcomplex.homOfLE h)
      (ModuleCat.of R R)).f n) :=
    IsSplitMono.mk' ⟨subcomplexDegreeRetraction R h n, subcomplexDegreeRetraction_id R h n⟩
  infer_instance

instance subcomplexChainMap_mono (h : A ≤ B) :
    Mono (SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) (ModuleCat.of R R)) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)

variable (A B)

theorem subcomplexUnion_isPushout :
    IsPushout
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) (ModuleCat.of R R))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) (ModuleCat.of R R))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) (ModuleCat.of R R))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) (ModuleCat.of R R)) := by
  have h : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  exact h.isPushout.map (chains R)

/-- The maps are (i,-j) from the intersection and (k,l) into the union. -/
def subcomplexUnionSequence : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  (subcomplexUnion_isPushout R A B).shortComplex

theorem subcomplexUnionSequence_shortExact : (subcomplexUnionSequence R A B).ShortExact where
  exact := (subcomplexUnion_isPushout R A B).exact_shortComplex
  mono_f := by
    have h : (subcomplexUnionSequence R A B).f ≫ biprod.fst =
        SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
          (ModuleCat.of R R) := biprod.lift_fst _ _
    haveI : Mono ((subcomplexUnionSequence R A B).f ≫ biprod.fst) := by
      rw [h]
      infer_instance
    exact mono_of_mono _ biprod.fst
  epi_g := (subcomplexUnion_isPushout R A B).epi_shortComplex_g

end Sharpness.SingularChainExcision
