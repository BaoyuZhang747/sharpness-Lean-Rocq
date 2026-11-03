import Sharpness.Unconditional.BurnsidePullbackDecomposition
import Sharpness.Unconditional.BurnsideCategoryMarks

/-! Products of actual slice objects are finite sums of the retained
double-coset spans. Their marks obey multiplication by a proved bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {P : F.CentricOrbit} (A B : Over P)

def centricSliceProductTerm
    (i : RestrictedTerm F.mackeyShape (fun Q => F.IsCentric Q.as.subgroup) A.hom B.hom) :
    Over P := Over.mk ((restrictedSpan F.mackeyShape _ A.hom B.hom i).left ≫ A.hom)

def centricSliceProductLeft
    (i : RestrictedTerm F.mackeyShape (fun Q => F.IsCentric Q.as.subgroup) A.hom B.hom) :
    F.centricSliceProductTerm A B i ⟶ A :=
  Over.homMk (restrictedSpan F.mackeyShape _ A.hom B.hom i).left

def centricSliceProductRight
    (i : RestrictedTerm F.mackeyShape (fun Q => F.IsCentric Q.as.subgroup) A.hom B.hom) :
    F.centricSliceProductTerm A B i ⟶ B :=
  Over.homMk (restrictedSpan F.mackeyShape _ A.hom B.hom i).right
    (F.restrictedCentricSpan_comm A.hom B.hom i).symm

def centricSliceProductFactorMap (X : Over P) :
    (Σ i : RestrictedTerm F.mackeyShape (fun Q => F.IsCentric Q.as.subgroup) A.hom B.hom,
      X ⟶ F.centricSliceProductTerm A B i) → ((X ⟶ A) × (X ⟶ B)) :=
  fun ⟨i, c⟩ => ⟨c ≫ F.centricSliceProductLeft A B i, c ≫ F.centricSliceProductRight A B i⟩

theorem centricSliceProductFactorMap_bijective (X : Over P) :
    Function.Bijective (F.centricSliceProductFactorMap A B X) := by
  constructor
  · rintro ⟨i, c⟩ ⟨j, d⟩ h
    have hl := congrArg (fun z : (X ⟶ A) × (X ⟶ B) => z.1.left) h
    have hr := congrArg (fun z : (X ⟶ A) × (X ⟶ B) => z.2.left) h
    have hij := F.centric_restrictedSpan_index_eq A.hom B.hom i j c.left d.left hl hr
    subst j
    have hcd : c = d := Over.OverMorphism.ext
      (F.centric_restrictedSpan_jointly_monic A.hom B.hom i c.left d.left hl hr)
    subst d
    rfl
  · rintro ⟨a, b⟩
    have hab : a.left ≫ A.hom = b.left ≫ B.hom := (Over.w a).trans (Over.w b).symm
    obtain ⟨i, c, hc, hd⟩ := F.centric_cone_factors_through_restrictedSpan
      A.hom B.hom a.left b.left hab
    let c' : X ⟶ F.centricSliceProductTerm A B i := Over.homMk c (by
      change c ≫ ((restrictedSpan F.mackeyShape _ A.hom B.hom i).left ≫ A.hom) = X.hom
      rw [← Category.assoc, hc, Over.w a])
    refine ⟨⟨i, c'⟩, ?_⟩
    exact Prod.ext (Over.OverMorphism.ext hc) (Over.OverMorphism.ext hd)

/-- The universal property of the finite slice product decomposition. -/
def centricSliceProductHomEquiv (X : Over P) :
    (Σ i : RestrictedTerm F.mackeyShape (fun Q => F.IsCentric Q.as.subgroup) A.hom B.hom,
      X ⟶ F.centricSliceProductTerm A B i) ≃ ((X ⟶ A) × (X ⟶ B)) :=
  Equiv.ofBijective _ (F.centricSliceProductFactorMap_bijective A B X)

local instance centricHomFinite (X Y : F.CentricOrbit) : Finite (X ⟶ Y) :=
  Finite.of_injective (fun f : X ⟶ Y => f.hom) (fun _ _ h => InducedCategory.hom_ext h)

/-- Multiplicativity of actual slice marks follows from the Hom-set
bijection, including precisely the retained centric terms. -/
theorem centricSliceProduct_card (X : Over P) :
    (∑ i : RestrictedTerm F.mackeyShape (fun Q => F.IsCentric Q.as.subgroup) A.hom B.hom,
      Nat.card (X ⟶ F.centricSliceProductTerm A B i)) =
      Nat.card (X ⟶ A) * Nat.card (X ⟶ B) := by
  rw [← Nat.card_sigma, ← Nat.card_prod]
  exact Nat.card_congr (F.centricSliceProductHomEquiv A B X)

end Sharpness.FusionSystem
