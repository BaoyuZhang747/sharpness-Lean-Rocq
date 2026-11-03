import Sharpness.Unconditional.AtomicHigherLimits
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
The homological product argument of Jackowski--McClure Proposition 5.1,
using the project's original module-valued Ext throughout. No acyclicity
comparison with another Ext construction is needed.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness.Burnside

open CategoryTheory CategoryTheory.Limits Opposite

variable {J : Type u} [Category.{u} J] {V : Type v} [Category.{w} V]

set_option backward.isDefEq.respectTransparency false in
/-- At an initial object, evaluation is right adjoint to the constant diagram
functor. The formula is explicit, including both inverse identities. -/
def constEvaluationAdjunction {I : J} (hI : IsInitial I) :
    Functor.const J ⊣ (evaluation J V).obj I :=
  Adjunction.mkOfHomEquiv
    { homEquiv X F :=
        { toFun := fun η => η.app I
          invFun := fun f =>
            { app := fun j => f ≫ F.map (hI.to j)
              naturality := by
                intro j k g
                change X ⟶ F.obj I at f
                change (𝟙 X) ≫ (f ≫ F.map (hI.to k)) =
                  (f ≫ F.map (hI.to j)) ≫ F.map g
                rw [Category.id_comp, Category.assoc, ← F.map_comp]
                rw [hI.hom_ext (hI.to j ≫ g) (hI.to k)] }
          left_inv := by
            intro η
            apply NatTrans.ext
            funext j
            change η.app I ≫ F.map (hI.to j) = η.app j
            have h := η.naturality (hI.to j)
            change (𝟙 X) ≫ η.app j = η.app I ≫ F.map (hI.to j) at h
            simpa only [Category.id_comp] using h.symm
          right_inv := by
            intro f
            change X ⟶ F.obj I at f
            change f ≫ F.map (hI.to I) = f
            rw [hI.to_self, F.map_id, Category.comp_id] }
      homEquiv_naturality_left_symm := by
        intro X Y F f g
        apply NatTrans.ext
        funext j
        exact Category.assoc f g (F.map (hI.to j))
      homEquiv_naturality_right := by intros; rfl }

/-- The constant rank-one coefficient is projective when the indexing
category has a terminal object. -/
theorem constantCoefficient_projective_of_terminal
    (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    {T : C} (hT : IsTerminal T) : Projective (constantCoefficient R C) := by
  exact (constEvaluationAdjunction (V := ModuleCat.{u} R) hT.op).map_projective
    (ModuleCat.of R R) inferInstance

/-- All positive higher inverse limits vanish over a category with a terminal
object, directly for the module-valued Ext used by the manuscript proof. -/
theorem acyclic_of_terminal
    (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    {T : C} (hT : IsTerminal T) (M : CoefficientCategory R C) : Acyclic M := by
  letI := constantCoefficient_projective_of_terminal R hT
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact isZero_Ext_succ_of_projective (constantCoefficient R C) M m

/-- Every coefficient on the actual slice category is acyclic. -/
theorem over_acyclic
    (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    (P : C) (N : CoefficientCategory R (Over P)) : Acyclic N :=
  acyclic_of_terminal R (Over.mkIdTerminal (X := P)) N

/-- Pulling a coefficient on the slice back along the product right adjoint
gives an acyclic coefficient on the base category. -/
theorem productRightAdjoint_acyclic
    (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    [HasBinaryProducts C] (P : C) (N : CoefficientCategory R (Over P)) :
    Acyclic ((Over.star P).op ⋙ N) := by
  intro n hn
  exact IsZero.of_iso (over_acyclic R P N n hn)
    (higherLimitRightAdjointIso R (Over.forget P) (Over.star P)
      (Over.forgetAdjStar P) N n).symm

/-- Jackowski--McClure Proposition 5.1: the coefficient taking Q to
M(P × Q) is acyclic. The product functor is expressed through the actual
forgetful/product adjunction of the slice category. -/
theorem productCoefficient_acyclic
    (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    [HasBinaryProducts C] (P : C) (M : CoefficientCategory R C) :
    Acyclic ((Over.star P).op ⋙ (Over.forget P).op ⋙ M) :=
  productRightAdjoint_acyclic R P ((Over.forget P).op ⋙ M)

/-- An endomorphism factoring through an acyclic coefficient acts by zero
on every positive higher limit. This is the functorial step in JM 5.6. -/
theorem higherLimit_map_zero_of_acyclic_factorization
    (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    {M N : CoefficientCategory R C} (hN : Acyclic N)
    (α : M ⟶ N) (β : N ⟶ M) (n : ℕ) (hn : 0 < n) :
    (higherLimitFunctor R C n).map (α ≫ β) = 0 := by
  rw [Functor.map_comp]
  have hz : (higherLimitFunctor R C n).map α = 0 := (hN n hn).eq_of_tgt _ _
  rw [hz, Limits.zero_comp]

/-- If that coefficient endomorphism is invertible, the original coefficient
is itself acyclic. -/
theorem acyclic_of_invertible_acyclic_factorization
    (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    {M N : CoefficientCategory R C} (hN : Acyclic N)
    (α : M ⟶ N) (β : N ⟶ M) [IsIso (α ≫ β)] : Acyclic M := by
  intro n hn
  let e := asIso ((higherLimitFunctor R C n).map (α ≫ β))
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 (higherLimit M n) = e.hom ≫ e.inv := e.hom_inv_id.symm
    _ = 0 := by
      rw [show e.hom = 0 from higherLimit_map_zero_of_acyclic_factorization R hN α β n hn]
      exact Limits.zero_comp

/-- Factoring through M(P × -) always annihilates positive higher limits. -/
theorem product_factorization_kills_higherLimits
    (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    [HasBinaryProducts C] (P : C) (M : CoefficientCategory R C)
    (α : M ⟶ (Over.star P).op ⋙ (Over.forget P).op ⋙ M)
    (β : (Over.star P).op ⋙ (Over.forget P).op ⋙ M ⟶ M)
    (n : ℕ) (hn : 0 < n) : (higherLimitFunctor R C n).map (α ≫ β) = 0 :=
  higherLimit_map_zero_of_acyclic_factorization R (productCoefficient_acyclic R P M) α β n hn

/-- The general quasi-unit criterion, before construction of the concrete
product and the invertible Mackey push-pull operator. -/
theorem acyclic_of_invertible_product_factorization
    (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    [HasBinaryProducts C] (P : C) (M : CoefficientCategory R C)
    (α : M ⟶ (Over.star P).op ⋙ (Over.forget P).op ⋙ M)
    (β : (Over.star P).op ⋙ (Over.forget P).op ⋙ M ⟶ M)
    [IsIso (α ≫ β)] : Acyclic M :=
  acyclic_of_invertible_acyclic_factorization R (productCoefficient_acyclic R P M) α β

end Sharpness.Burnside
