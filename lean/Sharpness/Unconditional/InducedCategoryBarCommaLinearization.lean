import Sharpness.Unconditional.InducedCategoryBarCommaStrings
import Sharpness.Unconditional.InducedCategoryBarComparison
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-! The explicit free-module bar generators are exactly the native nerve-chain
generators. The comparison is natural for all simplicial operators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable (R : Type u) [CommRing R]

def inducedCommaFreeCoproductIso (B : Type u) :
    (ModuleCat.free R).obj B ≅ (sigmaConst.obj (ModuleCat.of R R)).obj B where
  hom := ModuleCat.freeDesc (↾fun b => Sigma.ι (fun _ : B => ModuleCat.of R R) b 1)
  inv := Sigma.desc (fun b => ModuleCat.ofHom
    (LinearMap.toSpanSingleton R ((ModuleCat.free R).obj B) (ModuleCat.freeMk b)))
  hom_inv_id := by
    apply ModuleCat.free_hom_ext
    intro b
    simp only [ModuleCat.comp_apply, ModuleCat.freeDesc_apply, ModuleCat.id_apply]
    change (Sigma.ι (fun _ : B => ModuleCat.of R R) b ≫
      Sigma.desc (fun b => ModuleCat.ofHom
        (LinearMap.toSpanSingleton R ((ModuleCat.free R).obj B) (ModuleCat.freeMk b)))) 1 = _
    rw [Sigma.ι_desc]
    exact one_smul R (ModuleCat.freeMk (R := R) b)
  inv_hom_id := by
    apply Sigma.hom_ext
    intro b
    erw [Sigma.ι_desc_assoc, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (ModuleCat.freeDesc (↾fun b => Sigma.ι (fun _ : B => ModuleCat.of R R) b 1))
      (r • ModuleCat.freeMk b) = Sigma.ι (fun _ : B => ModuleCat.of R R) b r
    rw [map_smul, ModuleCat.freeDesc_apply]
    simpa using (map_smul (Sigma.ι (fun _ : B => ModuleCat.of R R) b).hom r (1 : R)).symm

@[simp] theorem inducedCommaFreeCoproductIso_hom_freeMk {B : Type u} (b : B) :
    (inducedCommaFreeCoproductIso R B).hom (ModuleCat.freeMk b) =
      Sigma.ι (fun _ : B => ModuleCat.of R R) b 1 := ModuleCat.freeDesc_apply _ _

theorem inducedCommaFreeCoproductIso_naturality {B E : Type u} (f : B ⟶ E) :
    (ModuleCat.free R).map f ≫ (inducedCommaFreeCoproductIso R E).hom =
      (inducedCommaFreeCoproductIso R B).hom ≫
        (sigmaConst.obj (ModuleCat.of R R)).map f := by
  apply ModuleCat.free_hom_ext
  intro b
  simp only [ModuleCat.comp_apply, inducedCommaFreeCoproductIso_hom_freeMk]
  change (inducedCommaFreeCoproductIso R E).hom
    ((ModuleCat.free R).map f (ModuleCat.freeMk b)) =
      ((Sigma.ι (fun _ : B => ModuleCat.of R R) b) ≫
        (sigmaConst.obj (ModuleCat.of R R)).map f) 1
  rw [ModuleCat.free_map_apply, inducedCommaFreeCoproductIso_hom_freeMk]
  simp [sigmaConst]

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (q : C ⥤ D) (X : D)

def inducedCategoryBarCommaDegreeIso (n : ℕ) :
    (inducedCategoryBarTerm R q n).obj (op X) ≅
      (nerve (StructuredArrow X q) ⋙ sigmaConst.obj (ModuleCat.of R R)).obj (op ⦋n⦌) :=
  (ModuleCat.free R).mapIso (inducedBarCommaBasisEquiv q X n).toIso ≪≫
    inducedCommaFreeCoproductIso R _

@[simp] theorem inducedCategoryBarCommaDegreeIso_hom_freeMk (n : ℕ)
    (b : inducedCategoryBarBasis q n (op X)) :
    (inducedCategoryBarCommaDegreeIso R q X n).hom (ModuleCat.freeMk b) =
      Sigma.ι (fun _ : ComposableArrows (StructuredArrow X q) n => ModuleCat.of R R)
        (inducedBarCommaBasisEquiv q X n b) 1 := by
  simp only [inducedCategoryBarCommaDegreeIso, Iso.trans_hom, Functor.mapIso_hom,
    ModuleCat.comp_apply, ModuleCat.free_map_apply]
  exact inducedCommaFreeCoproductIso_hom_freeMk R _

def inducedCategoryBarCommaSimplicialIso :
    inducedCategoryBarSimplicial R q ⋙ (evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op X) ≅
      nerve (StructuredArrow X q) ⋙ sigmaConst.obj (ModuleCat.of R R) :=
  NatIso.ofComponents (fun n => inducedCategoryBarCommaDegreeIso R q X n.unop.len) (by
    intro a b f
    apply ModuleCat.free_hom_ext
    rintro ⟨s, g⟩
    simp only [ModuleCat.comp_apply]
    change (inducedCategoryBarCommaDegreeIso R q X b.unop.len).hom
        ((inducedCategoryBarMap f.unop).app (op X) (ModuleCat.freeMk ⟨s, g⟩)) =
      (sigmaConst.obj (ModuleCat.of R R)).map ((nerve (StructuredArrow X q)).map f)
        ((inducedCategoryBarCommaDegreeIso R q X a.unop.len).hom (ModuleCat.freeMk ⟨s, g⟩))
    rw [inducedCategoryBarMap_freeMk, inducedCategoryBarCommaDegreeIso_hom_freeMk,
      inducedCategoryBarCommaDegreeIso_hom_freeMk]
    change _ = ((Sigma.ι (fun _ : ComposableArrows (StructuredArrow X q) a.unop.len => ModuleCat.of R R)
        (inducedBarCommaString q s g)) ≫
        (sigmaConst.obj (ModuleCat.of R R)).map ((nerve (StructuredArrow X q)).map f)) 1
    simp only [sigmaConst, Sigma.ι_comp_map', Category.id_comp]
    change Sigma.ι (fun _ : ComposableArrows (StructuredArrow X q) b.unop.len => ModuleCat.of R R)
      (inducedBarCommaString q (restrictCategoryChain f.unop s)
        (g ≫ q.map (categoryChainHeadArrow f.unop s))) 1 = _
    rw [inducedBarCommaString_restrict]
    rfl)

end Sharpness.Unconditional
