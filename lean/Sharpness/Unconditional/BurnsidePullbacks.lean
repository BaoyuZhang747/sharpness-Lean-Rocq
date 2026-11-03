import Sharpness.SpanEquations
import Sharpness.FusionCentricClosure
import Sharpness.Unconditional.BurnsideMackeyAction
import Sharpness.SpanOperator
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
Actual universal properties of the concrete fusion-system intersection spans.
This first proves the pullback before quotienting by target conjugation. A
centric incoming cone necessarily lands in a centric intersection, explaining
the removal of noncentric summands in the restricted Mackey formula.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem

open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] (F : FusionSystem S)
    {P Q T X : F.Object} (f : P ⟶ T) (g : Q ⟶ T) (u : T.subgroup)
    (a : X ⟶ P) (b : X ⟶ Q)
    (h : ∀ x : X.subgroup, g.val (b.val x) = u⁻¹ * f.val (a.val x) * u)

/-- The unique lift of a compatible pair of concrete fusion morphisms into
the actual intersection subgroup used by the Mackey formula. -/
def rawSpanLift : X ⟶ F.spanApex f g u := by
  let l : X.subgroup →* (F.spanApex f g u).subgroup :=
    { toFun := fun x => ⟨(a.val x).val,
        (F.mem_spanApex_iff f g u _).mpr ⟨a.val x, rfl, b.val x, h x⟩⟩
      map_one' := by
        apply Subtype.ext
        exact congrArg (fun z : P.subgroup => z.val) (map_one a.val)
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact congrArg (fun z : P.subgroup => z.val) (map_mul a.val x y) }
  refine ⟨l, F.codomain_restrict_mem a.val a.property
    (lifted_le P.subgroup (F.spanInternal f g u)) l ?_⟩
  ext x
  rfl

theorem rawSpanLift_left :
    F.rawSpanLift f g u a b h ≫ (F.concreteSpan f g u).left = a := by
  apply Subtype.ext
  ext x
  rfl

theorem rawSpanLift_right :
    F.rawSpanLift f g u a b h ≫ (F.concreteSpan f g u).right = b := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply F.injective g.val g.property
  exact (F.concreteSpan_right_equation f g u
    ((F.rawSpanLift f g u a b h).val x)).trans (h x).symm

theorem rawSpanLift_unique (l : X ⟶ F.spanApex f g u)
    (hl : l ≫ (F.concreteSpan f g u).left = a) : l = F.rawSpanLift f g u a b h := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun t : X ⟶ P => (t.val x).val) hl

variable {a b h}

/-- The concrete intersection is a pullback of the conjugated first leg and
the second leg in the actual fusion category. -/
def rawSpanPullbackCone : PullbackCone (f ≫ F.conjugateEnd T u) g :=
  PullbackCone.mk (F.concreteSpan f g u).left (F.concreteSpan f g u).right
    (F.concreteSpan_right_comp f g u).symm

/-- No saturation hypothesis is needed for this actual universal property. -/
def rawSpanPullbackIsLimit : IsLimit (F.rawSpanPullbackCone f g u) := by
  apply PullbackCone.IsLimit.mk
    (F.concreteSpan_right_comp f g u).symm
    (fun c => F.rawSpanLift f g u c.fst c.snd
      (fun x => (congrArg (fun m : c.pt ⟶ T => m.val x) c.condition).symm))
  · intro c
    exact F.rawSpanLift_left f g u _ _ _
  · intro c
    exact F.rawSpanLift_right f g u _ _ _
  · intro c l hl _
    exact F.rawSpanLift_unique f g u c.fst c.snd _ l hl

/-- A centric cone cannot factor through a noncentric intersection. This
proves that discarding noncentric terms loses no centric incoming cones. -/
theorem rawSpanApex_centric_of_centric_cone [Finite S]
    (a : X ⟶ P) (b : X ⟶ Q)
    (h : ∀ x : X.subgroup, g.val (b.val x) = u⁻¹ * f.val (a.val x) * u)
    (hX : F.IsCentric X.subgroup) : F.IsCentric (F.spanApex f g u).subgroup := by
  let l := F.rawSpanLift f g u a b h
  let e := F.toOrbit.mapIso (F.imageIso l)
  have hL : F.IsCentric (F.imageSubgroup l) :=
    F.isoSystem.centricIn_of_iso (F.groupEquivOfOrbitIso e)
      (F.groupEquivOfOrbitIso_allowed e) hX
  exact F.centric_overgroup hL (F.image_le l)

/-- Changing the representative within a double coset gives an isomorphism
of both orbit-span legs, not merely equal operators on one Mackey functor. -/
theorem exists_concreteOrbitSpanIso_of_doubleCoset_eq (v : T.subgroup)
    (same : DoubleCoset.mk f.val.range g.val.range u =
      DoubleCoset.mk f.val.range g.val.range v) :
    ∃ e : (F.concreteOrbitSpan f g u).apex ≅ (F.concreteOrbitSpan f g v).apex,
      (F.concreteOrbitSpan f g u).left = e.hom ≫ (F.concreteOrbitSpan f g v).left ∧
      (F.concreteOrbitSpan f g u).right = e.hom ≫ (F.concreteOrbitSpan f g v).right := by
  obtain ⟨c, hc, d, hd, hv⟩ := DoubleCoset.rel_iff.mp (Quotient.exact same)
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨b, rfl⟩ := hd
  rw [hv]
  exact ⟨F.toOrbit.mapIso (F.spanShiftIso f g u a b),
    F.spanShift_orbit_left f g u a b, F.spanShift_orbit_right f g u a b⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every centric cone factors through one of the actual retained
double-coset terms. This is the existence part of the finite pullback
decomposition in the centric orbit category. -/
theorem centric_cone_factors_through_restrictedSpan [Finite S]
    {P Q T X : F.CentricOrbit} (f : P ⟶ T) (g : Q ⟶ T)
    (a : X ⟶ P) (b : X ⟶ Q) (comm : a ≫ f = b ≫ g) :
    ∃ i : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g,
      ∃ c : X ⟶ (restrictedSpan F.mackeyShape _ f g i).apex,
        c ≫ (restrictedSpan F.mackeyShape _ f g i).left = a ∧
        c ≫ (restrictedSpan F.mackeyShape _ f g i).right = b := by
  let f₀ := F.orbitRepresentative f.hom
  let g₀ := F.orbitRepresentative g.hom
  let a₀ := F.orbitRepresentative a.hom
  let b₀ := F.orbitRepresentative b.hom
  have horbit : F.toOrbit.map (a₀ ≫ f₀) = F.toOrbit.map (b₀ ≫ g₀) := by
    simpa only [Functor.map_comp, f₀, g₀, a₀, b₀, orbitRepresentative_map,
      ObjectProperty.FullSubcategory.comp_hom] using!
      congrArg (fun h : X ⟶ T => h.hom) comm
  obtain ⟨u, hu⟩ := (F.orbit_map_eq_iff (a₀ ≫ f₀) (b₀ ≫ g₀)).mp horbit
  let l := F.rawSpanLift f₀ g₀ u a₀ b₀ hu
  have hA : F.IsCentric (F.spanApex f₀ g₀ u).subgroup :=
    F.rawSpanApex_centric_of_centric_cone f₀ g₀ u a₀ b₀ hu X.property
  let i : F.DoubleCosetTerm f.hom g.hom := DoubleCoset.mk f₀.val.range g₀.val.range u
  obtain ⟨e, hel, her⟩ := F.exists_concreteOrbitSpanIso_of_doubleCoset_eq
    f₀ g₀ u i.out (Quotient.out_eq i).symm
  have hi : F.IsCentric (F.doubleCosetSpan f.hom g.hom i).apex.as.subgroup :=
    F.isoSystem.centricIn_of_iso (F.groupEquivOfOrbitIso e)
      (F.groupEquivOfOrbitIso_allowed e) hA
  let term : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g := ⟨i, hi⟩
  let c : X ⟶ (restrictedSpan F.mackeyShape _ f g term).apex :=
    ⟨F.toOrbit.map l ≫ e.hom⟩
  refine ⟨term, c, ?_, ?_⟩
  · apply InducedCategory.hom_ext
    change (F.toOrbit.map l ≫ e.hom) ≫ (F.concreteOrbitSpan f₀ g₀ i.out).left = a.hom
    erw [Category.assoc, ← hel]
    calc
      _ = F.toOrbit.map (l ≫ (F.concreteSpan f₀ g₀ u).left) :=
        (F.toOrbit.map_comp _ _).symm
      _ = F.toOrbit.map a₀ := congrArg F.toOrbit.map (F.rawSpanLift_left f₀ g₀ u a₀ b₀ hu)
      _ = a.hom := F.orbitRepresentative_map a.hom
  · apply InducedCategory.hom_ext
    change (F.toOrbit.map l ≫ e.hom) ≫ (F.concreteOrbitSpan f₀ g₀ i.out).right = b.hom
    erw [Category.assoc, ← her]
    calc
      _ = F.toOrbit.map (l ≫ (F.concreteSpan f₀ g₀ u).right) :=
        (F.toOrbit.map_comp _ _).symm
      _ = F.toOrbit.map b₀ := congrArg F.toOrbit.map (F.rawSpanLift_right f₀ g₀ u a₀ b₀ hu)
      _ = b.hom := F.orbitRepresentative_map b.hom

end Sharpness.FusionSystem
