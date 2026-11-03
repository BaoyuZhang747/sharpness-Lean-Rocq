import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.LinearAlgebra.Span.Basic

/-! Genuine presentations of module-valued functors by model generators.
The data contain freeness alone, with no exactness or homotopy premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w r t

namespace Sharpness
open CategoryTheory

variable {C : Type u} [Category.{v} C] {R : Type r} [Ring R]

/-- A model-generator presentation with its actual extension operation
and uniqueness on all generators. -/
structure ModelPresentation (P : C ⥤ ModuleCat.{w} R) {I : Type t} (models : I → C) where
  generator : ∀ i, P.obj (models i)
  lift : ∀ (F : C ⥤ ModuleCat.{w} R), (∀ i, F.obj (models i)) → (P ⟶ F)
  lift_generator : ∀ (F : C ⥤ ModuleCat.{w} R) (x : ∀ i, F.obj (models i)) (i : I),
    (lift F x).app (models i) (generator i) = x i
  hom_ext : ∀ {F : C ⥤ ModuleCat.{w} R} (a b : P ⟶ F),
    (∀ i, a.app (models i) (generator i) = b.app (models i) (generator i)) → a = b

namespace ModelPresentation
variable {P F G : C ⥤ ModuleCat.{w} R} {I : Type t} {models : I → C}
    (p : ModelPresentation P models)

/-- Lift a natural map using chosen actual preimages of its model generators. -/
def liftAlong (τ : F ⟶ G) (c : P ⟶ G)
    (hpre : ∀ i, ∃ x : F.obj (models i), τ.app (models i) x = c.app (models i) (p.generator i)) :
    P ⟶ F :=
  p.lift F (fun i => (hpre i).choose)

theorem liftAlong_generator (τ : F ⟶ G) (c : P ⟶ G)
    (hpre : ∀ i, ∃ x : F.obj (models i), τ.app (models i) x = c.app (models i) (p.generator i))
    (i : I) :
    (p.liftAlong τ c hpre).app (models i) (p.generator i) = (hpre i).choose :=
  p.lift_generator F _ i

theorem liftAlong_comp (τ : F ⟶ G) (c : P ⟶ G)
    (hpre : ∀ i, ∃ x : F.obj (models i), τ.app (models i) x = c.app (models i) (p.generator i)) :
    p.liftAlong τ c hpre ≫ τ = c := by
  apply p.hom_ext
  intro i
  change τ.app (models i) ((p.liftAlong τ c hpre).app (models i) (p.generator i)) = _
  rw [p.liftAlong_generator]
  exact (hpre i).choose_spec

end ModelPresentation

section Adjunction
variable {R : Type w} [Ring R]

/-- The rank-one scalar map attached to a vector in a module. -/
def modelScalarMap (M : ModuleCat.{w} R) (x : M) : ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

@[simp] theorem modelScalarMap_one (M : ModuleCat.{w} R) (x : M) :
    modelScalarMap M x 1 = x :=
  LinearMap.toSpanSingleton_apply_one R M x

theorem modelScalarMap_hom_ext {M : ModuleCat.{w} R}
    (a b : ModuleCat.of R R ⟶ M) (h : a 1 = b 1) : a = b := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have ha : a x = x • a 1 := by
    simpa only [smul_eq_mul, mul_one] using a.hom.map_smul x (1 : R)
  have hb : b x = x • b 1 := by
    simpa only [smul_eq_mul, mul_one] using b.hom.map_smul x (1 : R)
  rw [ha, hb, h]

/-- An actual left adjoint to evaluation supplies a one-model presentation.
The generator is the unit evaluated at the scalar `1`. -/
def ModelPresentation.ofAdjunction (M : C)
    (L : ModuleCat.{w} R ⥤ (C ⥤ ModuleCat.{w} R))
    (adj : L ⊣ (evaluation C (ModuleCat.{w} R)).obj M) :
    ModelPresentation (L.obj (ModuleCat.of R R)) (fun _ : Unit => M) where
  generator _ := adj.unit.app (ModuleCat.of R R) (1 : R)
  lift F x := (adj.homEquiv (ModuleCat.of R R) F).symm (modelScalarMap (F.obj M) (x ()))
  lift_generator F x i := by
    cases i
    have h := (adj.homEquiv (ModuleCat.of R R) F).apply_symm_apply
      (modelScalarMap (F.obj M) (x ()))
    rw [Adjunction.homEquiv_unit] at h
    have h1 := congrArg (fun f : ModuleCat.of R R ⟶ F.obj M => f 1) h
    change ((adj.homEquiv (ModuleCat.of R R) F).symm
      (modelScalarMap (F.obj M) (x ()))).app M
        (adj.unit.app (ModuleCat.of R R) (1 : R)) = modelScalarMap (F.obj M) (x ()) (1 : R) at h1
    rw [modelScalarMap_one] at h1
    exact h1
  hom_ext a b h := by
    apply (adj.homEquiv _ _).injective
    apply modelScalarMap_hom_ext
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change a.app M (adj.unit.app (ModuleCat.of R R) (1 : R)) =
      b.app M (adj.unit.app (ModuleCat.of R R) (1 : R))
    exact h ()

end Adjunction
end Sharpness
