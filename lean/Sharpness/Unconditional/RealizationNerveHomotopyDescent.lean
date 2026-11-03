import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Homotopy.TopCat.Basic

/-! Descent of compatible simplex homotopies to the actual geometric realization.
Continuity uses the compact-open path space and local compactness of the unit
interval, rather than any unrestricted product-preservation assertion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

open CategoryTheory Simplicial Opposite

namespace Sharpness

/-- Evaluation at a fixed time on the compact-open path space. -/
def realizationPathEvaluation (Y : TopCat.{u}) (t : unitInterval) :
    TopCat.of C(unitInterval, Y) ⟶ Y :=
  TopCat.ofHom ⟨fun p => p t, continuous_eval_const t⟩

/-- An adjoint simplicial path map with the specified endpoints gives an actual
topological homotopy of the geometric realization. -/
def realizationHomotopyOfPathMap {X : SSet.{u}} {Y : TopCat.{u}}
    {f g : |X| ⟶ Y}
    (h : X ⟶ TopCat.toSSet.obj (TopCat.of C(unitInterval, Y)))
    (h₀ : h ≫ TopCat.toSSet.map (realizationPathEvaluation Y 0) =
      sSetTopAdj.homEquiv X Y f)
    (h₁ : h ≫ TopCat.toSSet.map (realizationPathEvaluation Y 1) =
      sSetTopAdj.homEquiv X Y g) : TopCat.Homotopy f g := by
  let k := (sSetTopAdj.homEquiv X (TopCat.of C(unitInterval, Y))).symm h
  have hk₀ : k ≫ realizationPathEvaluation Y 0 = f := by
    apply (sSetTopAdj.homEquiv X Y).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    exact h₀
  have hk₁ : k ≫ realizationPathEvaluation Y 1 = g := by
    apply (sSetTopAdj.homEquiv X Y).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    exact h₁
  exact
    { toFun := fun p => k p.2 p.1
      continuous_toFun := continuous_eval.comp ((k.hom.continuous.comp continuous_snd).prodMk
        continuous_fst)
      map_zero_left := fun x => ConcreteCategory.congr_hom hk₀ x
      map_one_left := fun x => ConcreteCategory.congr_hom hk₁ x }

/-- The actual characteristic map of a simplex, expressed through the unit of
the geometric-realization/singular-set adjunction. -/
def realizationSimplex {X : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n)) :
    C(stdSimplex ℝ (Fin (n.len + 1)), |X|) :=
  TopCat.toSSetObjEquiv _ _ ((sSetTopAdj.unit.app X).app _ x)

theorem realizationSimplex_naturality {X : SSet.{u}} {n m : SimplexCategory}
    (a : n ⟶ m) (x : X.obj (op m)) (z : stdSimplex ℝ (Fin (n.len + 1))) :
    realizationSimplex (X.map a.op x) z = realizationSimplex x (stdSimplex.map a z) := by
  have h := NatTrans.naturality_apply (sSetTopAdj.unit.app X) a.op x
  exact congrArg (fun y => TopCat.toSSetObjEquiv |X| (op n) y z) h

theorem realizationSimplex_map {X Z : SSet.{u}} (a : X ⟶ Z)
    {n : SimplexCategory} (x : X.obj (op n)) (z : stdSimplex ℝ (Fin (n.len + 1))) :
    realizationSimplex (a.app _ x) z = SSet.toTop.map a (realizationSimplex x z) := by
  have h := ConcreteCategory.congr_hom (congr_app (sSetTopAdj.unit.naturality a) (op n)) x
  exact congrArg (fun y => TopCat.toSSetObjEquiv |Z| (op n) y z) h

variable {X : SSet.{u}} {Y : TopCat.{u}} {f g : |X| ⟶ Y}

/-- A compatible family of homotopies on the actual characteristic simplices
defines the simplicial map into the compact-open path space. -/
def realizationSimplexPathMap
    (H : ∀ (n : SimplexCategory) (x : X.obj (op n)),
      ContinuousMap.Homotopy (f.hom.comp (realizationSimplex x))
        (g.hom.comp (realizationSimplex x)))
    (hnat : ∀ {n m : SimplexCategory} (a : n ⟶ m) (x : X.obj (op m))
      (t : unitInterval) (z : stdSimplex ℝ (Fin (n.len + 1))),
      H n (X.map a.op x) (t, z) = H m x (t, stdSimplex.map a z)) :
    X ⟶ TopCat.toSSet.obj (TopCat.of C(unitInterval, Y)) where
  app n := ↾fun x => (TopCat.toSSetObjEquiv _ _).symm
    (ContinuousMap.curry ((H n.unop x).toContinuousMap.comp ContinuousMap.prodSwap))
  naturality := by
    intro n m a
    ext x
    apply (TopCat.toSSetObjEquiv _ _).injective
    ext z t
    exact hnat a.unop x t z

/-- Compatible homotopies on every characteristic simplex descend to the
actual geometric realization. The compact interval is the only exponent used. -/
def realizationHomotopyOfSimplexHomotopies
    (H : ∀ (n : SimplexCategory) (x : X.obj (op n)),
      ContinuousMap.Homotopy (f.hom.comp (realizationSimplex x))
        (g.hom.comp (realizationSimplex x)))
    (hnat : ∀ {n m : SimplexCategory} (a : n ⟶ m) (x : X.obj (op m))
      (t : unitInterval) (z : stdSimplex ℝ (Fin (n.len + 1))),
      H n (X.map a.op x) (t, z) = H m x (t, stdSimplex.map a z)) :
    TopCat.Homotopy f g :=
  realizationHomotopyOfPathMap (realizationSimplexPathMap H hnat)
    (by
      ext n x
      apply (TopCat.toSSetObjEquiv _ _).injective
      ext z
      exact (H n.unop x).map_zero_left z)
    (by
      ext n x
      apply (TopCat.toSSetObjEquiv _ _).injective
      ext z
      exact (H n.unop x).map_one_left z)

end Sharpness
