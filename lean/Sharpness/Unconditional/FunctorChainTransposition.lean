import Mathlib.Algebra.Homology.Functor

/-! Evaluation transposes an actual functor to chain complexes into an actual
chain complex of functors. These elementary adapters preserve all components. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w z
namespace Sharpness
open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {V : Type w} [Category.{z} V]
  [HasZeroMorphisms V]

/-- Transpose an actual functor to chain complexes by evaluating each degree. -/
def functorChainComplex (F : C ⥤ ChainComplex V ℕ) : ChainComplex (C ⥤ V) ℕ where
  X n := F ⋙ HomologicalComplex.eval V (ComplexShape.down ℕ) n
  d i j :=
    { app X := (F.obj X).d i j
      naturality {X Y} f := (F.map f).comm i j }
  shape i j hij := by
    ext X
    exact (F.obj X).shape i j hij
  d_comp_d' i j k _ _ := by
    ext X
    exact (F.obj X).d_comp_d i j k

/-- Transpose an actual natural transformation of chain-complex functors. -/
def functorChainComplexMap {F G : C ⥤ ChainComplex V ℕ} (τ : F ⟶ G) :
    functorChainComplex F ⟶ functorChainComplex G where
  f n :=
    { app X := (τ.app X).f n
      naturality {X Y} f := congrArg (fun h => h.f n) (τ.naturality f) }
  comm' i j _ := by
    ext X
    exact (τ.app X).comm i j

@[simp] theorem functorChainComplex_X_obj (F : C ⥤ ChainComplex V ℕ) (n : ℕ) (X : C) :
    ((functorChainComplex F).X n).obj X = (F.obj X).X n := rfl

@[simp] theorem functorChainComplex_d_app (F : C ⥤ ChainComplex V ℕ) (i j : ℕ) (X : C) :
    ((functorChainComplex F).d i j).app X = (F.obj X).d i j := rfl

@[simp] theorem functorChainComplexMap_f_app {F G : C ⥤ ChainComplex V ℕ}
    (τ : F ⟶ G) (n : ℕ) (X : C) :
    ((functorChainComplexMap τ).f n).app X = (τ.app X).f n := rfl

@[simp] theorem functorChainComplexMap_id (F : C ⥤ ChainComplex V ℕ) :
    functorChainComplexMap (𝟙 F) = 𝟙 (functorChainComplex F) := rfl

@[simp] theorem functorChainComplexMap_comp {F G H : C ⥤ ChainComplex V ℕ}
    (τ : F ⟶ G) (υ : G ⟶ H) :
    functorChainComplexMap (τ ≫ υ) = functorChainComplexMap τ ≫ functorChainComplexMap υ := rfl

/-- Evaluating the transposed complex recovers the original actual complex. -/
@[simp] theorem functorChainComplex_evaluation (F : C ⥤ ChainComplex V ℕ) (X : C) :
    (((evaluation C V).obj X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (functorChainComplex F) = F.obj X := rfl

/-- The transpose is functorial, with the literal component maps above. -/
def functorChainTransposition : (C ⥤ ChainComplex V ℕ) ⥤ ChainComplex (C ⥤ V) ℕ where
  obj := functorChainComplex
  map := functorChainComplexMap

end Sharpness
