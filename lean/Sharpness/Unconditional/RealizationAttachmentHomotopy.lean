import Sharpness.Unconditional.RealizationNerveHomotopyDescent
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-! Descent of compatible actual homotopies over an actual topological
pushout. Continuity uses the compact-open path space and local compactness
of the interval, not unrestricted preservation of pushouts by products. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.AttachmentHomotopy
open CategoryTheory CategoryTheory.Limits

def homotopyPathMap {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    X ⟶ TopCat.of C(unitInterval, Y) :=
  TopCat.ofHom (ContinuousMap.curry (H.toContinuousMap.comp ContinuousMap.prodSwap))

theorem homotopyPathMap_zero {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    homotopyPathMap H ≫ realizationPathEvaluation Y 0 = f := by
  ext x
  exact H.map_zero_left x

theorem homotopyPathMap_one {X Y : TopCat.{u}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    homotopyPathMap H ≫ realizationPathEvaluation Y 1 = g := by
  ext x
  exact H.map_one_left x

variable {A B C D Y : TopCat.{u}} {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}

def pushoutHomotopy (h : IsPushout t l r b) {f g : D ⟶ Y}
    (HB : TopCat.Homotopy (r ≫ f) (r ≫ g))
    (HC : TopCat.Homotopy (b ≫ f) (b ≫ g))
    (hcompat : ∀ (s : unitInterval) (a : A), HB (s, t a) = HC (s, l a)) :
    TopCat.Homotopy f g := by
  have hw : t ≫ homotopyPathMap HB = l ≫ homotopyPathMap HC := by
    ext a s
    exact hcompat s a
  let k := h.desc (homotopyPathMap HB) (homotopyPathMap HC) hw
  have hk0 : k ≫ realizationPathEvaluation Y 0 = f := by
    apply h.hom_ext
    · rw [← Category.assoc, h.inl_desc]
      exact homotopyPathMap_zero HB
    · rw [← Category.assoc, h.inr_desc]
      exact homotopyPathMap_zero HC
  have hk1 : k ≫ realizationPathEvaluation Y 1 = g := by
    apply h.hom_ext
    · rw [← Category.assoc, h.inl_desc]
      exact homotopyPathMap_one HB
    · rw [← Category.assoc, h.inr_desc]
      exact homotopyPathMap_one HC
  exact
    { toFun := fun p => k p.2 p.1
      continuous_toFun := continuous_eval.comp ((k.hom.continuous.comp continuous_snd).prodMk
        continuous_fst)
      map_zero_left := fun x => ConcreteCategory.congr_hom hk0 x
      map_one_left := fun x => ConcreteCategory.congr_hom hk1 x }

end Sharpness.AttachmentHomotopy
