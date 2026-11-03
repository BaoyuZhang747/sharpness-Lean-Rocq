import Sharpness.QuotientOrbit

/-! Concrete lifts of quotient-orbit arrows, and independence of both
coefficient maps even when the quotient homomorphisms differ by inner
automorphisms. This is the orbit-representative step in Lemma 3.3. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (I : F.AKOQuotientInput (p := p) hZ hS sat)

abbrev rawQuotientOrbitMap {A B : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩) :
    I.system.toOrbit.obj ⟨A⟩ ⟶ I.system.toOrbit.obj ⟨B⟩ :=
  (F.quotientRawFunctor hZ p hS sat I ⋙ I.system.toOrbit).map (InducedCategory.homMk f)

theorem rawQuotientOrbitMap_id (A : Subgroup (S ⧸ Z)) :
    F.rawQuotientOrbitMap hZ p hS sat I (𝟙 (⟨F.quotientPreimage Z A⟩ : F.Object)) = 𝟙 _ :=
  (F.quotientRawFunctor hZ p hS sat I ⋙ I.system.toOrbit).map_id A

theorem rawQuotientOrbitMap_comp {A B C : Subgroup (S ⧸ Z)}
    (f : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩)
    (g : (⟨F.quotientPreimage Z B⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z C⟩) :
    F.rawQuotientOrbitMap hZ p hS sat I (f ≫ g) =
      F.rawQuotientOrbitMap hZ p hS sat I f ≫ F.rawQuotientOrbitMap hZ p hS sat I g :=
  (F.quotientRawFunctor hZ p hS sat I ⋙ I.system.toOrbit).map_comp
    (InducedCategory.homMk f) (InducedCategory.homMk g)

def quotientRawLift {A B : I.system.Object} (f : A ⟶ B) :
    (⟨F.quotientPreimage Z A.subgroup⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B.subgroup⟩ :=
  Classical.choose ((I.isHom_iff f.val).mp f.property)

theorem quotientRawLift_map {A B : I.system.Object} (f : A ⟶ B) :
    F.quotientInducedHom hZ (F.quotientRawLift hZ p hS sat I f) = f.val :=
  Classical.choose_spec ((I.isHom_iff f.val).mp f.property)

def quotientOrbitLift {A B : I.system.Orbit} (f : A ⟶ B) :
    (⟨F.quotientPreimage Z A.as.subgroup⟩ : F.Object) ⟶
      ⟨F.quotientPreimage Z B.as.subgroup⟩ :=
  F.quotientRawLift hZ p hS sat I (I.system.orbitRepresentative f)

theorem quotientOrbitLift_map {A B : I.system.Orbit} (f : A ⟶ B) :
    F.rawQuotientOrbitMap hZ p hS sat I (F.quotientOrbitLift hZ p hS sat I f) = f := by
  change I.system.toOrbit.map _ = f
  have h : (F.quotientRawFunctor hZ p hS sat I).map
      (InducedCategory.homMk (F.quotientOrbitLift hZ p hS sat I f)) =
        I.system.orbitRepresentative f := by
    apply Subtype.ext
    exact F.quotientRawLift_map hZ p hS sat I _
  rw [h, I.system.orbitRepresentative_map]

theorem simple_maps_eq_of_same_quotientOrbit
    {k : Type u} [Field k] [CharP k p]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (hZQ : Z ≤ label.Q.as.subgroup) {A B : Subgroup (S ⧸ Z)}
    (f g : (⟨F.quotientPreimage Z A⟩ : F.Object) ⟶ ⟨F.quotientPreimage Z B⟩)
    (same : F.rawQuotientOrbitMap hZ p hS sat I f = F.rawQuotientOrbitMap hZ p hS sat I g) :
    M.pull (F.toOrbit.map f) = M.pull (F.toOrbit.map g) ∧
      M.push (F.toOrbit.map f) = M.push (F.toOrbit.map g) := by
  obtain ⟨r, hr⟩ := (I.system.orbit_map_eq_iff _ _).mp same
  let rB : B := r
  have hrB (x : A) : F.quotientInducedHom hZ g x =
      rB⁻¹ * F.quotientInducedHom hZ f x * rB := hr x
  obtain ⟨rP, hrP⟩ := F.subgroupProjection_surjective Z B rB
  let f' := f ≫ F.inner (⟨F.quotientPreimage Z B⟩ : F.Object) rP
  have modZ (x : F.quotientPreimage Z A) : (f'.val x).val⁻¹ * (g.val x).val ∈ Z := by
    have h := hrB (F.subgroupProjection Z A x)
    rw [F.quotientInducedHom_apply, F.quotientInducedHom_apply, ← hrP] at h
    have hval := congrArg (fun b : B => b.val) h
    change (QuotientGroup.mk (g.val x).val : S ⧸ Z) =
      (QuotientGroup.mk rP.val : S ⧸ Z)⁻¹ * QuotientGroup.mk (f.val x).val *
        QuotientGroup.mk rP.val at hval
    apply QuotientGroup.eq.mp
    change (QuotientGroup.mk (f'.val x).val : S ⧸ Z) = QuotientGroup.mk (g.val x).val
    rw [hval]
    change (QuotientGroup.mk (rP.val⁻¹ * (f.val x).val * rP.val) : S ⧸ Z) = _
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have eqs := F.simple_maps_eq_of_same_modZ hZ (QuotientGroup.le_comap_mk' Z A)
    f' g modZ p hS M label hZQ
  have hf' : F.toOrbit.map f' = F.toOrbit.map f := by
    rw [F.toOrbit.map_comp, F.inner_orbit_eq_id, Category.comp_id]
  constructor
  · exact (congrArg (fun f => M.pull f) hf').symm.trans eqs.1
  · exact (congrArg (fun f => M.push f) hf').symm.trans eqs.2

end Sharpness.FusionSystem
