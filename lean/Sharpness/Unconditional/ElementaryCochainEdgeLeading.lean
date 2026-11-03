import Sharpness.Unconditional.ElementaryCochainEdgeSupport

/-! The leading component of a total cocycle is a vertical cocycle whose
class is horizontally closed. Positive horizontal exactness lifts that class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def verticalHomology (q : ℕ) : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K

def PositiveHorizontalExact : Prop :=
  ∀ q p : ℕ, (verticalHomology K q).ExactAt (p+1)

theorem horizontal_cycle_lift (hK : PositiveHorizontalExact K) (p q : ℕ)
    (x : (K.X (p+1)).X q) (hx : Cycle (K.X (p+1)) q x)
    (hnext : homologyMap (K.d (p+1) (p+2)) q (cycleClass (K.X (p+1)) q x hx) = 0) :
    ∃ (a : (K.X p).X q) (ha : Cycle (K.X p) q a)
      (b : (K.X (p+1)).X (q-1)),
      (K.X (p+1)).d (q-1) q b = x - (K.d p (p+1)).f q a := by
  have hc : Cycle (verticalHomology K q) (p+1) (cycleClass (K.X (p+1)) q x hx) := by
    apply (cycle_iff _ _ _).mpr
    exact hnext
  obtain ⟨c, hc⟩ := exactAt_succ_boundary (verticalHomology K q) p (hK q p) _ hc
  obtain ⟨a, ha, rfl⟩ := cycleClass_surjective (K.X p) q c
  refine ⟨a, ha, ?_⟩
  apply (cycleClass_eq_iff (K.X (p+1)) q x _ hx (cycle_map (K.d p (p+1)) q a ha)).mp
  rw [← cycleClass_map]
  exact hc.symm

theorem leading_cycle (p q n : ℕ) (hpq : p+q=n)
    (x : (K.total (ComplexShape.up ℕ)).X n) (hx : Cycle (K.total (ComplexShape.up ℕ)) n x)
    (hs : SupportedFrom K x p) :
    Cycle (K.X p) q (totalSummandProjectionAt K p q n hpq x) := by
  apply (cycle_iff _ _ _).mpr
  cases p with
  | zero =>
    have hqn : q=n := by omega
    subst q
    have h := differential_component_zero_column K n x
    rw [hx (n+1), map_zero] at h
    exact h.symm
  | succ p =>
    have h := differential_component K p q n (by omega) x
    rw [hx (n+1), map_zero, hs p (q+1) (by omega) (by omega), map_zero, zero_add] at h
    have h' := congrArg (fun z => ((-1 : ℤˣ)^(p+1))⁻¹ • z) h.symm
    simpa only [inv_smul_smul, smul_zero] using h'

theorem leading_horizontal_cycle (p q n : ℕ) (hpq : p+q=n)
    (x : (K.total (ComplexShape.up ℕ)).X n) (hx : Cycle (K.total (ComplexShape.up ℕ)) n x)
    (hs : SupportedFrom K x p) :
    homologyMap (K.d p (p+1)) q
      (cycleClass (K.X p) q (totalSummandProjectionAt K p q n hpq x)
        (leading_cycle K p q n hpq x hx hs)) = 0 := by
  rw [cycleClass_map]
  apply (cycleClass_eq_zero_iff _ _ _ _).mpr
  cases q with
  | zero =>
    have hpn : p=n := by omega
    subst p
    have h := differential_component_zero_row K n x
    rw [hx (n+1), map_zero] at h
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact h
  | succ q =>
    have h := differential_component K p q n hpq x
    rw [hx (n+1), map_zero] at h
    refine ⟨- ((-1 : ℤˣ)^(p+1) • totalSummandProjectionAt K (p+1) q n (by omega) x), ?_⟩
    rw [map_neg, moduleHom_units_smul]
    exact (eq_neg_of_add_eq_zero_left h.symm).symm

end Sharpness.ElementaryCochainEdge
