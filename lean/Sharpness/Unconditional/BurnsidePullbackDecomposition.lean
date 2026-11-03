import Sharpness.Unconditional.BurnsidePullbackUniqueness

/-! The centric double-coset formula is a genuine finite pullback
decomposition on Hom sets, not only a relation imposed on Mackey modules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {P Q T X : F.CentricOrbit} (f : P ⟶ T) (g : Q ⟶ T)

theorem centric_restrictedSpan_index_eq
    (i j : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g)
    (c : X ⟶ (restrictedSpan F.mackeyShape _ f g i).apex)
    (d : X ⟶ (restrictedSpan F.mackeyShape _ f g j).apex)
    (hl : c ≫ (restrictedSpan F.mackeyShape _ f g i).left =
      d ≫ (restrictedSpan F.mackeyShape _ f g j).left)
    (hr : c ≫ (restrictedSpan F.mackeyShape _ f g i).right =
      d ≫ (restrictedSpan F.mackeyShape _ f g j).right) : i = j := by
  let f₀ := F.orbitRepresentative f.hom
  let g₀ := F.orbitRepresentative g.hom
  let c₀ := F.orbitRepresentative c.hom
  let d₀ := F.orbitRepresentative d.hom
  have hl₀ : F.toOrbit.map (c₀ ≫ (F.concreteSpan f₀ g₀ i.val.out).left) =
      F.toOrbit.map (d₀ ≫ (F.concreteSpan f₀ g₀ j.val.out).left) := by
    simpa only [Functor.map_comp, c₀, d₀, orbitRepresentative_map] using!
      congrArg (fun h : X ⟶ P => h.hom) hl
  have hr₀ : F.toOrbit.map (c₀ ≫ (F.concreteSpan f₀ g₀ i.val.out).right) =
      F.toOrbit.map (d₀ ≫ (F.concreteSpan f₀ g₀ j.val.out).right) := by
    simpa only [Functor.map_comp, c₀, d₀, orbitRepresentative_map] using!
      congrArg (fun h : X ⟶ Q => h.hom) hr
  have hij := F.span_doubleCoset_eq_of_orbit_legs f₀ g₀ i.val.out j.val.out
    X.property c₀ d₀ hl₀ hr₀
  apply Subtype.ext
  exact (Quotient.out_eq i.val).symm.trans (hij.trans (Quotient.out_eq j.val))

theorem centric_restrictedSpan_jointly_monic
    (i : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g)
    (c d : X ⟶ (restrictedSpan F.mackeyShape _ f g i).apex)
    (hl : c ≫ (restrictedSpan F.mackeyShape _ f g i).left =
      d ≫ (restrictedSpan F.mackeyShape _ f g i).left)
    (hr : c ≫ (restrictedSpan F.mackeyShape _ f g i).right =
      d ≫ (restrictedSpan F.mackeyShape _ f g i).right) : c = d := by
  let f₀ := F.orbitRepresentative f.hom
  let g₀ := F.orbitRepresentative g.hom
  let c₀ := F.orbitRepresentative c.hom
  let d₀ := F.orbitRepresentative d.hom
  have hl₀ : F.toOrbit.map (c₀ ≫ (F.concreteSpan f₀ g₀ i.val.out).left) =
      F.toOrbit.map (d₀ ≫ (F.concreteSpan f₀ g₀ i.val.out).left) := by
    simpa only [Functor.map_comp, c₀, d₀, orbitRepresentative_map] using!
      congrArg (fun h : X ⟶ P => h.hom) hl
  have hr₀ : F.toOrbit.map (c₀ ≫ (F.concreteSpan f₀ g₀ i.val.out).right) =
      F.toOrbit.map (d₀ ≫ (F.concreteSpan f₀ g₀ i.val.out).right) := by
    simpa only [Functor.map_comp, c₀, d₀, orbitRepresentative_map] using!
      congrArg (fun h : X ⟶ Q => h.hom) hr
  apply InducedCategory.hom_ext
  simpa only [c₀, d₀, orbitRepresentative_map] using!
    F.span_orbit_factor_unique_of_orbit_legs f₀ g₀ i.val.out X.property c₀ d₀ hl₀ hr₀

/-- The actual incoming factors into the retained spans. -/
def centricSpanFactors (X : F.CentricOrbit) :=
  Σ i : RestrictedTerm F.mackeyShape (fun P => F.IsCentric P.as.subgroup) f g,
    X ⟶ (restrictedSpan F.mackeyShape _ f g i).apex

/-- Compatible pairs of centric orbit morphisms over the common target. -/
def centricConePairs (X : F.CentricOrbit) :=
  { ab : (X ⟶ P) × (X ⟶ Q) // ab.1 ≫ f = ab.2 ≫ g }

def centricSpanFactorMap : F.centricSpanFactors f g X → F.centricConePairs f g X :=
  fun ⟨i, c⟩ => ⟨⟨c ≫ (restrictedSpan F.mackeyShape _ f g i).left,
      c ≫ (restrictedSpan F.mackeyShape _ f g i).right⟩, by
    simp only [Category.assoc, F.restrictedCentricSpan_comm f g i]⟩

theorem centricSpanFactorMap_bijective : Function.Bijective (F.centricSpanFactorMap f g (X := X)) := by
  constructor
  · rintro ⟨i, c⟩ ⟨j, d⟩ h
    have hl := congrArg (fun z : F.centricConePairs f g X => z.val.1) h
    have hr := congrArg (fun z : F.centricConePairs f g X => z.val.2) h
    have hij := F.centric_restrictedSpan_index_eq f g i j c d hl hr
    subst j
    have hcd := F.centric_restrictedSpan_jointly_monic f g i c d hl hr
    subst d
    rfl
  · rintro ⟨⟨a, b⟩, hab⟩
    obtain ⟨i, c, hc, hd⟩ := F.centric_cone_factors_through_restrictedSpan f g a b hab
    refine ⟨⟨i, c⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext hc hd

/-- The finite pullback decomposition required by the actual restricted
Mackey and Burnside constructions. -/
def centricPullbackHomEquiv : F.centricSpanFactors f g X ≃ F.centricConePairs f g X :=
  Equiv.ofBijective _ (F.centricSpanFactorMap_bijective f g)

end Sharpness.FusionSystem
