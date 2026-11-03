import Sharpness.Unconditional.BurnsidePullbacks
import Sharpness.MackeyFunctorData

/-! Transport of the concrete Mackey spans along the source isomorphisms
in the actual image factorization of fusion morphisms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q P' Q' T : F.Object} (f : P ⟶ T) (g : Q ⟶ T)
    (f' : P' ⟶ T) (g' : Q' ⟶ T) (a : P ≅ P') (b : Q ≅ Q')
    (ha : a.hom ≫ f' = f) (hb : b.hom ≫ g' = g) (u : T.subgroup)

def rawSpanTransport : F.spanApex f g u ⟶ F.spanApex f' g' u :=
  F.rawSpanLift f' g' u ((F.concreteSpan f g u).left ≫ a.hom)
    ((F.concreteSpan f g u).right ≫ b.hom) (by
      intro x
      have he : ((F.concreteSpan f g u).right ≫ b.hom) ≫ g' =
          ((F.concreteSpan f g u).left ≫ a.hom) ≫ f' ≫ F.conjugateEnd T u := by
        calc
          _ = (F.concreteSpan f g u).right ≫ g := by rw [Category.assoc, hb]
          _ = ((F.concreteSpan f g u).left ≫ f) ≫ F.conjugateEnd T u :=
            F.concreteSpan_right_comp f g u
          _ = _ := by rw [← ha]; simp only [Category.assoc]
      exact congrArg (fun h => h.val x) he)

theorem rawSpanTransport_left : F.rawSpanTransport f g f' g' a b ha hb u ≫
    (F.concreteSpan f' g' u).left = (F.concreteSpan f g u).left ≫ a.hom :=
  F.rawSpanLift_left _ _ _ _ _ _

theorem rawSpanTransport_right : F.rawSpanTransport f g f' g' a b ha hb u ≫
    (F.concreteSpan f' g' u).right = (F.concreteSpan f g u).right ≫ b.hom :=
  F.rawSpanLift_right _ _ _ _ _ _

def rawSpanTransportIso : F.spanApex f g u ≅ F.spanApex f' g' u where
  hom := F.rawSpanTransport f g f' g' a b ha hb u
  inv := F.rawSpanTransport f' g' f g a.symm b.symm
    (by rw [← ha]; simp) (by rw [← hb]; simp) u
  hom_inv_id := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (a.inv.val (a.hom.val ((F.concreteSpan f g u).left.val x))).val = x.val
    exact congrArg Subtype.val (congrArg (fun h : P ⟶ P => h.val _) a.hom_inv_id)
  inv_hom_id := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (a.hom.val (a.inv.val ((F.concreteSpan f' g' u).left.val x))).val = x.val
    exact congrArg Subtype.val (congrArg (fun h : P' ⟶ P' => h.val _) a.inv_hom_id)

include ha in
theorem range_eq_of_source_iso : f.val.range = f'.val.range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨a.hom.val y, congrArg (fun h : P ⟶ T => h.val y) ha⟩
  · rintro ⟨y, rfl⟩
    refine ⟨a.inv.val y, ?_⟩
    have he : a.inv ≫ f = f' := by rw [← ha]; simp
    exact congrArg (fun h : P' ⟶ T => h.val y) he

variable {R : Type u} [Ring R] (E : MackeyFunctorData.{u,w} R F.Orbit)

include ha hb in
theorem functorDataSpanOperator_transport :
    F.functorDataSpanOperator E f g u =
      (E.pull (F.toOrbit.map a.hom)).comp
        ((F.functorDataSpanOperator E f' g' u).comp (E.push (F.toOrbit.map b.hom))) := by
  let s := F.concreteOrbitSpan f g u
  let t := F.concreteOrbitSpan f' g' u
  let e := F.toOrbit.mapIso (F.rawSpanTransportIso f g f' g' a b ha hb u)
  let t' : MackeySpan F.Orbit (F.toOrbit.obj P) (F.toOrbit.obj Q) :=
    ⟨t.apex, t.left ≫ F.toOrbit.map a.inv, t.right ≫ F.toOrbit.map b.inv⟩
  have hl : s.left = e.hom ≫ t'.left := by
    have he : (F.concreteSpan f g u).left =
        (F.rawSpanTransportIso f g f' g' a b ha hb u).hom ≫
          (F.concreteSpan f' g' u).left ≫ a.inv := by
      change (F.concreteSpan f g u).left = F.rawSpanTransport f g f' g' a b ha hb u ≫
        (F.concreteSpan f' g' u).left ≫ a.inv
      rw [← Category.assoc, F.rawSpanTransport_left]
      simp
    exact (congrArg F.toOrbit.map he).trans (by simp only [Functor.map_comp]; rfl)
  have hr : s.right = e.hom ≫ t'.right := by
    have he : (F.concreteSpan f g u).right =
        (F.rawSpanTransportIso f g f' g' a b ha hb u).hom ≫
          (F.concreteSpan f' g' u).right ≫ b.inv := by
      change (F.concreteSpan f g u).right = F.rawSpanTransport f g f' g' a b ha hb u ≫
        (F.concreteSpan f' g' u).right ≫ b.inv
      rw [← Category.assoc, F.rawSpanTransport_right]
      simp
    exact (congrArg F.toOrbit.map he).trans (by simp only [Functor.map_comp]; rfl)
  have hpa : E.pull (F.toOrbit.map a.hom) = E.push (F.toOrbit.map a.inv) := by
    have he : inv (F.toOrbit.map a.hom) = F.toOrbit.map a.inv :=
      IsIso.inv_eq_of_hom_inv_id (by rw [← F.toOrbit.map_comp, a.hom_inv_id, F.toOrbit.map_id])
    exact (E.pull_iso _).trans (congrArg E.push he)
  have hpb : E.pull (F.toOrbit.map b.inv) = E.push (F.toOrbit.map b.hom) := by
    have he : inv (F.toOrbit.map b.inv) = F.toOrbit.map b.hom :=
      IsIso.inv_eq_of_hom_inv_id (by rw [← F.toOrbit.map_comp, b.inv_hom_id, F.toOrbit.map_id])
    exact (E.pull_iso _).trans (congrArg E.push he)
  calc
    _ = E.spanOperator t' := E.spanOperator_of_iso s t' e hl hr
    _ = _ := by
      dsimp [MackeyFunctorData.spanOperator, t', t, functorDataSpanOperator]
      rw [E.push_comp, E.pull_comp, hpa, hpb]
      rfl

end Sharpness.FusionSystem
