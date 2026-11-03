import Sharpness.RestrictedMackey
import Sharpness.SpanEquations
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
The canonical action of virtual slice objects on a restricted Mackey functor.
Isomorphic slice objects induce the same operator. Composition of operators
is the actual centric double-coset formula, proved from the Mackey axiom.
No assertion about positive higher limits is assumed or made here.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Sharpness.RestrictedMackeyModule

open CategoryTheory
open scoped BigOperators

variable {R : Type u} [CommRing R] {C : Type v} [Category.{v} C]
    {B : MackeyShape C} {K : ObjectProperty C}
    (M : RestrictedMackeyModule.{u,v,w} R C B K)

/-- The push-pull operator attached to an object of the slice category. -/
def sliceOperator {P : K.FullSubcategory} (X : Over P) : Module.End R (M.Value P) :=
  (M.push X.hom).comp (M.pull X.hom)

theorem push_pull_iso {P Q : K.FullSubcategory} (e : P ≅ Q) :
    (M.push e.hom).comp (M.pull e.hom) = LinearMap.id := by
  have hi : M.pull e.hom = M.push e.inv := by simpa using M.pull_iso e.hom
  rw [hi, ← M.push_comp, e.inv_hom_id, M.push_id]

theorem sliceOperator_id (P : K.FullSubcategory) :
    M.sliceOperator (Over.mk (𝟙 P)) = LinearMap.id := by
  change (M.push (𝟙 P)).comp (M.pull (𝟙 P)) = LinearMap.id
  rw [M.push_id, M.pull_id, LinearMap.id_comp]

/-- The operator depends only on the isomorphism class of the slice object. -/
theorem sliceOperator_eq_of_iso {P : K.FullSubcategory} {X Y : Over P}
    (e : X ≅ Y) : M.sliceOperator X = M.sliceOperator Y := by
  have h := Over.w e.hom
  let ei : X.left ≅ Y.left :=
    { hom := e.hom.left
      inv := e.inv.left
      hom_inv_id := Over.hom_left_inv_left e
      inv_hom_id := Over.inv_left_hom_left e }
  change e.hom.left ≫ Y.hom = X.hom at h
  unfold sliceOperator
  rw [← h, M.push_comp, M.pull_comp]
  apply LinearMap.ext
  intro x
  have he := LinearMap.congr_fun (M.push_pull_iso ei) (M.pull Y.hom x)
  change M.push e.hom.left (M.pull e.hom.left (M.pull Y.hom x)) = M.pull Y.hom x at he
  change M.push Y.hom (M.push e.hom.left (M.pull e.hom.left (M.pull Y.hom x))) = _
  rw [he]
  rfl

/-- Extension of the canonical action to formal R-linear combinations of
slice isomorphism classes, the additive module underlying the Burnside ring. -/
def virtualSliceAction (P : K.FullSubcategory) :
    (Skeleton (Over P) →₀ R) →ₗ[R] Module.End R (M.Value P) :=
  Finsupp.linearCombination R
    (fun X => M.sliceOperator ((fromSkeleton (Over P)).obj X))

theorem virtualSliceAction_single (P : K.FullSubcategory)
    (X : Skeleton (Over P)) (r : R) :
    M.virtualSliceAction P (Finsupp.single X r) =
      r • M.sliceOperator ((fromSkeleton (Over P)).obj X) := by
  simp [virtualSliceAction]

/-- Every actual slice object acts by its defining push-pull operator. -/
theorem virtualSliceAction_object {P : K.FullSubcategory} (X : Over P) :
    M.virtualSliceAction P (Finsupp.single (toSkeleton X) 1) = M.sliceOperator X := by
  rw [M.virtualSliceAction_single, one_smul]
  exact M.sliceOperator_eq_of_iso (fromSkeletonToSkeletonIso X)

/-- Composition before identifying the two legs of each pullback term. -/
theorem sliceOperator_comp_expansion {P Q T : K.FullSubcategory}
    (f : P ⟶ T) (g : Q ⟶ T) :
    (M.sliceOperator (Over.mk f)).comp (M.sliceOperator (Over.mk g)) =
      ∑ i : RestrictedTerm B K f g,
        (M.push ((restrictedSpan B K f g i).left ≫ f)).comp
          (M.pull ((restrictedSpan B K f g i).right ≫ g)) := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (M.mackey f g) (M.pull g x)
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h
  change M.push f (M.pull f (M.push g (M.pull g x))) = _
  rw [h, map_sum]
  simp only [LinearMap.sum_apply, M.push_comp, M.pull_comp, LinearMap.comp_apply]

end Sharpness.RestrictedMackeyModule

namespace Sharpness.FusionSystem

open CategoryTheory
open scoped BigOperators

variable {S : Type v} [Group S] (F : FusionSystem S)

/-- The actual orbit double-coset spans commute. The conjugating element is
precisely the chosen double-coset representative. -/
theorem doubleCosetSpan_comm {P Q T : F.Orbit} (f : P ⟶ T) (g : Q ⟶ T)
    (i : F.DoubleCosetTerm f g) :
    (F.doubleCosetSpan f g i).left ≫ f = (F.doubleCosetSpan f g i).right ≫ g := by
  let f₀ := F.orbitRepresentative f
  let g₀ := F.orbitRepresentative g
  let t := F.concreteSpan f₀ g₀ i.out
  calc
    _ = F.toOrbit.map (t.left ≫ f₀) := by
      simp only [Functor.map_comp, orbitRepresentative_map, f₀]
      rfl
    _ = F.toOrbit.map (t.right ≫ g₀) := by
      apply (F.orbit_map_eq_iff _ _).mpr
      refine ⟨i.out, ?_⟩
      intro x
      exact F.concreteSpan_right_equation f₀ g₀ i.out x
    _ = _ := by
      simp only [Functor.map_comp, orbitRepresentative_map, g₀]
      rfl

variable [Finite S]

/-- The commutative-square identity survives the centric truncation. -/
theorem restrictedCentricSpan_comm {P Q T : F.CentricOrbit} (f : P ⟶ T) (g : Q ⟶ T)
    (i : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g) :
    (restrictedSpan F.mackeyShape _ f g i).left ≫ f =
      (restrictedSpan F.mackeyShape _ f g i).right ≫ g := by
  apply InducedCategory.hom_ext
  exact F.doubleCosetSpan_comm f.hom g.hom i.val

/-- The canonical restricted Mackey action satisfies the centric
double-coset multiplication law on slice objects. -/
theorem centricSliceOperator_comp
    {R : Type u} [CommRing R]
    (M : RestrictedMackeyModule.{u,v,w} R F.Orbit F.mackeyShape
      (fun P => F.IsCentric P.as.subgroup))
    {P Q T : F.CentricOrbit} (f : P ⟶ T) (g : Q ⟶ T) :
    (M.sliceOperator (Over.mk f)).comp (M.sliceOperator (Over.mk g)) =
      ∑ i : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g,
        M.sliceOperator (Over.mk ((restrictedSpan F.mackeyShape _ f g i).left ≫ f)) := by
  rw [M.sliceOperator_comp_expansion]
  apply Finset.sum_congr rfl
  intro i _
  unfold RestrictedMackeyModule.sliceOperator
  rw [F.restrictedCentricSpan_comm f g i]
  rfl

/-- Pullback compatibility of the canonical action, with the pullback
expressed by its actual centric double-coset summands. -/
theorem centricSliceOperator_pull
    {R : Type u} [CommRing R]
    (M : RestrictedMackeyModule.{u,v,w} R F.Orbit F.mackeyShape
      (fun P => F.IsCentric P.as.subgroup))
    {P Q T : F.CentricOrbit} (f : P ⟶ T) (g : Q ⟶ T) :
    (M.pull f).comp (M.sliceOperator (Over.mk g)) =
      (∑ i : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g,
        M.sliceOperator (Over.mk (restrictedSpan F.mackeyShape _ f g i).left)).comp
          (M.pull f) := by
  change (M.pull f).comp ((M.push g).comp (M.pull g)) =
    (∑ i : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g,
      (M.push (restrictedSpan F.mackeyShape _ f g i).left).comp
        (M.pull (restrictedSpan F.mackeyShape _ f g i).left)).comp (M.pull f)
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (M.mackey f g) (M.pull g x)
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrArg M.pull (F.restrictedCentricSpan_comm f g i)
  simp only [M.pull_comp] at he
  exact congrArg (M.push (restrictedSpan F.mackeyShape _ f g i).left)
    (LinearMap.congr_fun he x).symm

/-- Pushforward compatibility (the projection formula) for the same action. -/
theorem centricSliceOperator_push
    {R : Type u} [CommRing R]
    (M : RestrictedMackeyModule.{u,v,w} R F.Orbit F.mackeyShape
      (fun P => F.IsCentric P.as.subgroup))
    {P Q T : F.CentricOrbit} (f : P ⟶ T) (g : Q ⟶ T) :
    (M.sliceOperator (Over.mk g)).comp (M.push f) =
      (M.push f).comp
        (∑ i : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) g f,
          M.sliceOperator (Over.mk (restrictedSpan F.mackeyShape _ g f i).right)) := by
  change ((M.push g).comp (M.pull g)).comp (M.push f) =
    (M.push f).comp
      (∑ i : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) g f,
        (M.push (restrictedSpan F.mackeyShape _ g f i).right).comp
          (M.pull (restrictedSpan F.mackeyShape _ g f i).right))
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun (M.mackey g f) x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [h, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrArg M.push (F.restrictedCentricSpan_comm g f i)
  simp only [M.push_comp] at he
  exact LinearMap.congr_fun he (M.pull (restrictedSpan F.mackeyShape _ g f i).right x)

end Sharpness.FusionSystem
