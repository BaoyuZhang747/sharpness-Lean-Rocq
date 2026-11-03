import Sharpness.Unconditional.PuigProductDecomposition
import Mathlib.CategoryTheory.EpiMono

/-! Uniqueness of representable summands in a product decomposition.
The comparison is canonical and preserves both projection legs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.ProductDecomposition
open CategoryTheory
variable {C : Type u} [Category.{u} C] {P Q : C}
    (D E : ProductDecomposition P Q)

def comparison (i : D.Index) : Σ j, D.apex i ⟶ E.apex j :=
  (E.homEquiv (D.apex i)).symm (D.left i, D.right i)

@[reassoc (attr := simp)]
theorem comparison_left (i : D.Index) :
    (D.comparison E i).2 ≫ E.left (D.comparison E i).1 = D.left i :=
  congrArg Prod.fst ((E.homEquiv (D.apex i)).apply_symm_apply (D.left i, D.right i))

@[reassoc (attr := simp)]
theorem comparison_right (i : D.Index) :
    (D.comparison E i).2 ≫ E.right (D.comparison E i).1 = D.right i :=
  congrArg Prod.snd ((E.homEquiv (D.apex i)).apply_symm_apply (D.left i, D.right i))

theorem comparison_comp (i : D.Index) :
    (⟨(E.comparison D (D.comparison E i).1).1,
      (D.comparison E i).2 ≫ (E.comparison D (D.comparison E i).1).2⟩ :
        Σ j, D.apex i ⟶ D.apex j) = ⟨i, 𝟙 (D.apex i)⟩ := by
  apply (D.homEquiv (D.apex i)).injective
  apply Prod.ext <;> simp [homEquiv_apply, Category.assoc]

@[simp]
theorem comparison_index_comp (i : D.Index) :
    (E.comparison D (D.comparison E i).1).1 = i :=
  congrArg Sigma.fst (D.comparison_comp E i)

/-- The canonical bijection between the two indexing types. -/
@[reducible] def indexEquiv : D.Index ≃ E.Index where
  toFun i := (D.comparison E i).1
  invFun j := (E.comparison D j).1
  left_inv := D.comparison_index_comp E
  right_inv := E.comparison_index_comp D

private theorem sigma_hom_eq_iff {I : Type u} (A : I → C) (X : C)
    {i j : I} (f : X ⟶ A i) (g : X ⟶ A j) (h : i = j) :
    (⟨i, f⟩ : Σ k, X ⟶ A k) = ⟨j, g⟩ ↔ f ≫ eqToHom (congrArg A h) = g := by
  subst j
  simp

def comparisonInverse (i : D.Index) : E.apex (D.indexEquiv E i) ⟶ D.apex i :=
  (E.comparison D (D.comparison E i).1).2 ≫
    eqToHom (congrArg D.apex (D.comparison_index_comp E i))

@[simp]
theorem comparison_hom_inv_id (i : D.Index) :
    (D.comparison E i).2 ≫ D.comparisonInverse E i = 𝟙 (D.apex i) := by
  rw [comparisonInverse, ← Category.assoc]
  exact (sigma_hom_eq_iff D.apex (D.apex i) _ _
    (D.comparison_index_comp E i)).mp (D.comparison_comp E i)

instance comparison_hom_isSplitMono (i : D.Index) :
    IsSplitMono (D.comparison E i).2 :=
  ⟨⟨⟨D.comparisonInverse E i, D.comparison_hom_inv_id E i⟩⟩⟩

instance comparisonInverse_mono (i : D.Index) : Mono (D.comparisonInverse E i) := by
  dsimp [comparisonInverse]
  infer_instance

/-- The paired summands are isomorphic through their canonical comparison. -/
def apexIso (i : D.Index) : D.apex i ≅ E.apex (D.indexEquiv E i) where
  hom := (D.comparison E i).2
  inv := D.comparisonInverse E i
  hom_inv_id := D.comparison_hom_inv_id E i
  inv_hom_id := by
    apply (cancel_mono (D.comparisonInverse E i)).mp
    simp only [Category.assoc, D.comparison_hom_inv_id E i, Category.comp_id,
      Category.id_comp]

@[reassoc (attr := simp)]
theorem apexIso_hom_left (i : D.Index) :
    (D.apexIso E i).hom ≫ E.left (D.indexEquiv E i) = D.left i :=
  D.comparison_left E i

@[reassoc (attr := simp)]
theorem apexIso_hom_right (i : D.Index) :
    (D.apexIso E i).hom ≫ E.right (D.indexEquiv E i) = D.right i :=
  D.comparison_right E i

end Sharpness.ProductDecomposition
