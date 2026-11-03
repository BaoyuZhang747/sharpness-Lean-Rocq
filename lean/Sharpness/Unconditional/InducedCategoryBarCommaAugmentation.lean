import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.Algebra.Category.ModuleCat.Basic
import Sharpness.CategoryChains
import Mathlib.CategoryTheory.PUnit
import Sharpness.Unconditional.InducedCategoryBarCommaLinearization

/-! The ordinary augmentation of native simplicial chains, with a direct
contraction of the point nerve. All degree-zero generators augment to one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Simplicial Opposite AlgebraicTopology
variable (R : Type u) [CommRing R]

def inducedCommaNerveModuleAugmented (X : SSet.{u}) :
    SimplicialObject.Augmented (ModuleCat.{u} R) where
  left := X ⋙ sigmaConst.obj (ModuleCat.of R R)
  right := ModuleCat.of R R
  hom :=
    { app n := Sigma.desc (fun _ : X.obj n => 𝟙 (ModuleCat.of R R))
      naturality {n m} f := by
        apply Sigma.hom_ext
        intro x
        simp [sigmaConst] }

def inducedCommaNerveAugmentation (X : SSet.{u}) :
    X.chainComplex (ModuleCat.of R R) ⟶
      (ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R R) :=
  AlternatingFaceMapComplex.ε.app (inducedCommaNerveModuleAugmented R X)

@[reassoc (attr := simp)]
theorem inducedCommaNerveAugmentation_ι (X : SSet.{u}) (x : X _⦋0⦌) :
    X.ιChainComplex x ≫ (inducedCommaNerveAugmentation R X).f 0 = 𝟙 _ := by
  change Sigma.ι _ x ≫ Sigma.desc (fun _ : X _⦋0⦌ => 𝟙 (ModuleCat.of R R)) = _
  exact Sigma.ι_desc _ _

theorem inducedCommaNerveAugmentation_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.chainComplexMap f (ModuleCat.of R R) ≫ inducedCommaNerveAugmentation R Y =
      inducedCommaNerveAugmentation R X := by
  apply HomologicalComplex.to_single_hom_ext
  apply SSet.chainComplex_hom_ext
  intro x
  simp

def inducedCommaSingletonCoproductIso (B : Type u) [Unique B] :
    (sigmaConst.obj (ModuleCat.of R R)).obj B ≅ ModuleCat.of R R where
  hom := Sigma.desc (fun _ : B => 𝟙 (ModuleCat.of R R))
  inv := Sigma.ι (fun _ : B => ModuleCat.of R R) default
  hom_inv_id := by
    apply Sigma.hom_ext
    intro b
    simp only [Sigma.ι_desc_assoc, Category.id_comp]
    exact congrArg (Sigma.ι (fun _ : B => ModuleCat.of R R)) (Subsingleton.elim _ _)
  inv_hom_id := Sigma.ι_desc _ _

abbrev inducedCommaPointStringUnique (n : ℕ) :
    Unique (ComposableArrows (Discrete PUnit.{u+1}) n) where
  default := Functor.star _
  uniq s := Functor.punit_ext' s _

def inducedCommaPointSimplicialIso :
    (inducedCommaNerveModuleAugmented R (nerve (Discrete PUnit.{u+1}))).left ≅
      (SimplicialObject.const (ModuleCat.{u} R)).obj (ModuleCat.of R R) := by
  letI := inducedCommaPointStringUnique
  exact NatIso.ofComponents (fun n => inducedCommaSingletonCoproductIso R
    (ComposableArrows (Discrete PUnit.{u+1}) n.unop.len)) (by
      intro n m f
      apply Sigma.hom_ext
      intro s
      simp [inducedCommaNerveModuleAugmented, inducedCommaSingletonCoproductIso, sigmaConst]
      erw [Sigma.ι_desc, Sigma.ι_desc_assoc, Category.id_comp])

def inducedCommaPointAugmentedIso :
    inducedCommaNerveModuleAugmented R (nerve (Discrete PUnit.{u+1})) ≅
      SimplicialObject.Augmented.const.obj (ModuleCat.of R R) :=
  Comma.isoMk (inducedCommaPointSimplicialIso R) (Iso.refl _) (by
    apply NatTrans.ext
    funext n
    simp [inducedCommaPointSimplicialIso, inducedCommaNerveModuleAugmented,
      inducedCommaSingletonCoproductIso]
    exact Category.comp_id _)

def inducedCommaPointContraction :
    HomotopyEquiv ((nerve (Discrete PUnit.{u+1})).chainComplex (ModuleCat.of R R))
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R R)) :=
  ((SimplicialObject.Augmented.ExtraDegeneracy.const (ModuleCat.of R R)).ofIso
    (inducedCommaPointAugmentedIso R).symm).homotopyEquiv

instance inducedCommaPointAugmentation_quasiIso :
    QuasiIso (inducedCommaNerveAugmentation R (nerve (Discrete PUnit.{u+1}))) :=
  (inducedCommaPointContraction R).quasiIso_hom

theorem inducedCommaNerveAugmentation_quasiIso_of_star (C : Type u) [Category.{u} C]
    (h : QuasiIso (SSet.chainComplexMap (nerveMap (Functor.star.{u} C)) (ModuleCat.of R R))) :
    QuasiIso (inducedCommaNerveAugmentation R (nerve C)) := by
  letI := h
  rw [← inducedCommaNerveAugmentation_naturality R (nerveMap (Functor.star.{u} C))]
  infer_instance

end Sharpness.Unconditional
