import Sharpness.Unconditional.PuigProductDecomposition
import Sharpness.Unconditional.BurnsideSliceMarks
import Sharpness.Unconditional.CentricHomCounts

/-! The slice marks of the product with the top centric subgroup are
actual Hom counts, hence are units in the p-local coefficient ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory

namespace ProductDecomposition
variable {C : Type u} [Category.{u} C] {P Q : C} (D : ProductDecomposition P Q)

def sliceFactorMap (X : Over P) :
    (Σ i, X ⟶ Over.mk (D.left i)) → (X.left ⟶ Q) :=
  fun z => z.2.left ≫ D.right z.1

theorem sliceFactorMap_bijective (X : Over P) :
    Function.Bijective (D.sliceFactorMap X) := by
  constructor
  · rintro ⟨i, f⟩ ⟨j, g⟩ h
    have he : (⟨i, f.left⟩ : Σ k, X.left ⟶ D.apex k) = ⟨j, g.left⟩ :=
      (D.bijective X.left).1 (Prod.ext ((Over.w f).trans (Over.w g).symm) h)
    obtain ⟨hij, hfg⟩ := Sigma.mk.inj_iff.mp he
    subst j
    have hfg' : f = g := Over.OverMorphism.ext (eq_of_heq hfg)
    subst g
    rfl
  · intro g
    obtain ⟨⟨i, f⟩, hf⟩ := (D.bijective X.left).2 (X.hom, g)
    refine ⟨⟨i, Over.homMk f (congrArg Prod.fst hf)⟩, ?_⟩
    exact congrArg Prod.snd hf

/-- Fixing the left leg of a product cone leaves precisely an arrow to Q. -/
def sliceHomEquiv (X : Over P) :
    (Σ i, X ⟶ Over.mk (D.left i)) ≃ (X.left ⟶ Q) :=
  Equiv.ofBijective _ (D.sliceFactorMap_bijective X)

local instance : Fintype D.Index := Fintype.ofFinite D.Index

theorem sliceHom_card [∀ X Y : C, Finite (X ⟶ Y)] (X : Over P) :
    (∑ i : D.Index, Nat.card (X ⟶ Over.mk (D.left i))) =
      Nat.card (X.left ⟶ Q) := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr (D.sliceHomEquiv X)

/-- The finite product, viewed as a virtual object over its left factor. -/
def virtualProductSlice (R : Type u) [CommRing R] : Skeleton (Over P) →₀ R :=
  ∑ i : D.Index, Finsupp.single (toSkeleton (Over.mk (D.left i))) 1

theorem virtualProductSlice_marks (R : Type u) [CommRing R]
    [∀ X Y : C, Finite (X ⟶ Y)] :
    Burnside.virtualObjectMarks R (D.virtualProductSlice R) =
      fun X => (Nat.card (((fromSkeleton (Over P)).obj X).left ⟶ Q) : R) := by
  classical
  rw [virtualProductSlice, map_sum]
  simp only [Burnside.virtualObjectMarks_object]
  ext X
  simp only [Finset.sum_apply]
  change (∑ i : D.Index,
      (Nat.card ((fromSkeleton (Over P)).obj X ⟶ Over.mk (D.left i)) : R)) = _
  simpa only [Nat.cast_sum] using! congrArg (fun n : ℕ => (n : R))
    (D.sliceHom_card ((fromSkeleton (Over P)).obj X))

end ProductDecomposition

namespace FusionSystem
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

local instance topMarksHomFinite (P Q : F.CentricOrbit) : Finite (P ⟶ Q) :=
  Finite.of_injective (fun f : P ⟶ Q => f.hom) (fun _ _ h => InducedCategory.hom_ext h)

theorem virtualTopProduct_marks_primeTo (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (P : F.CentricOrbit)
    (X : Skeleton (Over P)) :
    ¬ p ∣ Nat.card (((fromSkeleton (Over P)).obj X).left ⟶ F.centricTopObject) :=
  F.centricOrbit_hom_top_card_primeTo p hS sat _

theorem virtualTopProduct_marks_isUnit (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) {P : F.CentricOrbit}
    (D : ProductDecomposition P F.centricTopObject) (X : Skeleton (Over P)) :
    IsUnit (Burnside.virtualObjectMarks (PrimeLocalRing.{u} p)
      (D.virtualProductSlice (PrimeLocalRing.{u} p)) X) := by
  rw [D.virtualProductSlice_marks]
  exact Burnside.isUnit_natCast_primeLocalRing p _
    (F.virtualTopProduct_marks_primeTo p hS sat P X)

end FusionSystem
end Sharpness
