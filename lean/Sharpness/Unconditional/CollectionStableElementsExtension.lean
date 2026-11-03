import Sharpness.NativeCentricStable
import Sharpness.StableToTopCondition

/-! A compatible family is stable when every fusion map extends to an
object of the collection. This is a purely algebraic compatibility argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S R : Type u} [Group S] [Finite S] [CommRing R] (F : FusionSystem S)
    (K : ObjectProperty F.Orbit) (hTop : K F.topOrbit)
    (extension : ∀ (P : F.Object) (f : P ⟶ (⟨⊤⟩ : F.Object)),
      ∃ Q : Subgroup S, K (F.toOrbit.obj ⟨Q⟩) ∧ ∃ hPQ : P.subgroup ≤ Q,
        ∃ g : (⟨Q⟩ : F.Object) ⟶ ⟨⊤⟩, F.inclusion hPQ ≫ g = f)
    (M : MackeyModule.{u,u,u} R F.Orbit F.mackeyShape)

/-- Evaluation at the actual top is the forward map. -/
def collectionCompatibleStableLinearEquiv :
    ((F.coefficientData M).onFull K).limit ≃ₗ[R] F.stableElements M where
  toFun c := ⟨c.val ⟨F.topOrbit, hTop⟩, by
    apply (F.mem_stableElements_iff_toTop M _).mpr
    intro P f
    let a := F.orbitRepresentative f
    obtain ⟨Q, hQ, hPQ, g, hag⟩ := extension P.as a
    let B : K.FullSubcategory := ⟨F.toOrbit.obj ⟨Q⟩, hQ⟩
    let inc := F.toOrbit.map (F.inclusion hPQ)
    let t := F.toOrbit.map g
    have hf : inc ≫ t = f := by
      rw [← F.toOrbit.map_comp, hag]
      exact F.orbitRepresentative_map f
    have ht : M.pull t (c.val ⟨F.topOrbit, hTop⟩) = c.val B :=
      c.property (show B ⟶ ⟨F.topOrbit, hTop⟩ from ⟨t⟩)
    have hinc : M.pull (F.toTop B.obj) (c.val ⟨F.topOrbit, hTop⟩) = c.val B :=
      c.property (show B ⟶ ⟨F.topOrbit, hTop⟩ from ⟨F.toTop B.obj⟩)
    have hcomp : inc ≫ F.toTop B.obj = F.toTop P := by
      change F.toOrbit.map (F.inclusion hPQ) ≫ F.toOrbit.map (F.inclusion le_top) = _
      rw [← F.toOrbit.map_comp]
      rfl
    calc
      _ = M.pull inc (M.pull t (c.val ⟨F.topOrbit, hTop⟩)) := by
        rw [← hf, M.pull_comp]
        rfl
      _ = M.pull inc (c.val B) := by rw [ht]
      _ = M.pull inc (M.pull (F.toTop B.obj) (c.val ⟨F.topOrbit, hTop⟩)) := by rw [hinc]
      _ = _ := by
        rw [← LinearMap.comp_apply, ← M.pull_comp, hcomp]
        rfl⟩
  invFun x := ⟨fun P => M.pull (F.toTop P.obj) x.val, by
    intro P Q f
    exact x.property f.hom⟩
  left_inv c := by
    apply Subtype.ext
    funext P
    exact c.property (show P ⟶ (⟨F.topOrbit, hTop⟩ : K.FullSubcategory) from ⟨F.toTop P.obj⟩)
  right_inv x := by
    apply Subtype.ext
    change M.pull (F.toTop F.topOrbit) x.val = x.val
    rw [F.toTop_top, M.pull_id]
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Sharpness.FusionSystem

