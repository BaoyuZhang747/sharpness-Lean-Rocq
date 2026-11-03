import Sharpness.Unconditional.PuigProductDecomposition
import Sharpness.Unconditional.BurnsidePullbackDecomposition

/-! Pulling back every summand of a representable product along a centric
orbit arrow gives another genuine representable product decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {P Q Q' : F.CentricOrbit} (D : ProductDecomposition P Q) (f : Q' ⟶ Q)

abbrev PulledProductIndex :=
  Σ i : D.Index, RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f (D.right i)

def pulledProductSpan (i : F.PulledProductIndex D f) :
    MackeySpan F.CentricOrbit Q' (D.apex i.1) :=
  restrictedSpan F.mackeyShape _ f (D.right i.1) i.2

def pulledProductFactorMap (X : F.CentricOrbit) :
    (Σ i : F.PulledProductIndex D f, X ⟶ (F.pulledProductSpan D f i).apex) →
      ((X ⟶ P) × (X ⟶ Q')) :=
  fun z => (z.2 ≫ ((F.pulledProductSpan D f z.1).right ≫ D.left z.1.1),
    z.2 ≫ (F.pulledProductSpan D f z.1).left)

theorem pulledProductFactorMap_bijective (X : F.CentricOrbit) :
    Function.Bijective (F.pulledProductFactorMap D f X) := by
  constructor
  · rintro ⟨⟨i, j⟩, c⟩ ⟨⟨i', j'⟩, d⟩ h
    have hl := congrArg Prod.fst h
    have hr := congrArg Prod.snd h
    change c ≫ (_ ≫ D.left i) = d ≫ (_ ≫ D.left i') at hl
    change c ≫ (restrictedSpan F.mackeyShape _ f (D.right i) j).left =
      d ≫ (restrictedSpan F.mackeyShape _ f (D.right i') j').left at hr
    have hD : (⟨i, c ≫ (restrictedSpan F.mackeyShape _ f (D.right i) j).right⟩ :
        Σ i, X ⟶ D.apex i) =
        ⟨i', d ≫ (restrictedSpan F.mackeyShape _ f (D.right i') j').right⟩ := by
      apply (D.homEquiv X).injective
      apply Prod.ext
      · exact (Category.assoc _ _ _).trans (hl.trans (Category.assoc _ _ _).symm)
      · change (c ≫ _) ≫ D.right i = (d ≫ _) ≫ D.right i'
        rw [Category.assoc, Category.assoc,
          ← F.restrictedCentricSpan_comm f (D.right i) j,
          ← F.restrictedCentricSpan_comm f (D.right i') j',
          ← Category.assoc, ← Category.assoc, hr]
    have hii : i = i' := congrArg Sigma.fst hD
    subst i'
    have hc : c ≫ (restrictedSpan F.mackeyShape _ f (D.right i) j).right =
        d ≫ (restrictedSpan F.mackeyShape _ f (D.right i) j').right := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hD
    have hjj := F.centric_restrictedSpan_index_eq f (D.right i) j j' c d hr hc
    subst j'
    have hcd := F.centric_restrictedSpan_jointly_monic f (D.right i) j c d hr hc
    subst d
    rfl
  · rintro ⟨a, b⟩
    obtain ⟨⟨i, c⟩, hc⟩ := (D.homEquiv X).surjective (a, b ≫ f)
    have hl : c ≫ D.left i = a := congrArg Prod.fst hc
    have hr : c ≫ D.right i = b ≫ f := congrArg Prod.snd hc
    obtain ⟨j, d, hd, he⟩ := F.centric_cone_factors_through_restrictedSpan
      f (D.right i) b c hr.symm
    refine ⟨⟨⟨i, j⟩, d⟩, ?_⟩
    apply Prod.ext
    · change d ≫ ((restrictedSpan F.mackeyShape _ f (D.right i) j).right ≫ D.left i) = a
      rw [← Category.assoc, he, hl]
    · exact hd

/-- The pulled-back decomposition has all and only the actual retained
Mackey spans, and has the complete universal product property. -/
def pulledProductDecomposition : ProductDecomposition P Q' where
  Index := F.PulledProductIndex D f
  finiteIndex := by infer_instance
  apex i := (F.pulledProductSpan D f i).apex
  left i := (F.pulledProductSpan D f i).right ≫ D.left i.1
  right i := (F.pulledProductSpan D f i).left
  bijective X := F.pulledProductFactorMap_bijective D f X

end Sharpness.FusionSystem
