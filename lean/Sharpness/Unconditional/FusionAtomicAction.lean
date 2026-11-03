import Sharpness.Radical
import Sharpness.Unconditional.TraceFormulaSpans

/-! Automorphism actions on actual fusion-orbit morphisms. The stabilizer
of an inclusion is exactly the image of its relative normalizer. These are
the finite-group inputs to the atomic higher-limit comparison. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

/-- Precomposition by the inverse gives a left automorphism action. -/
@[reducible]
def orbitHomAction (Q P : F.Orbit) : MulAction (Aut Q) (Q ⟶ P) where
  smul a f := a.inv ≫ f
  one_smul f := Category.id_comp f
  mul_smul a b f := Category.assoc a.inv b.inv f

/-- The stabilizer, stated with the forward automorphism for convenience. -/
def orbitHomStabilizer {Q P : F.Orbit} (f : Q ⟶ P) : Subgroup (Aut Q) where
  carrier := {a | a.hom ≫ f = f}
  one_mem' := Category.id_comp f
  mul_mem' {a b} ha hb := by
    change (b.hom ≫ a.hom) ≫ f = f
    rw [Category.assoc, ha, hb]
  inv_mem' {a} ha := by
    change a.inv ≫ f = f
    calc
      a.inv ≫ f = a.inv ≫ (a.hom ≫ f) := by rw [ha]
      _ = f := a.inv_hom_id_assoc f

theorem mem_orbitHomStabilizer_iff {Q P : F.Orbit} (f : Q ⟶ P) (a : Aut Q) :
    a ∈ F.orbitHomStabilizer f ↔ a.hom ≫ f = f := Iff.rfl

theorem orbitHomAction_stabilizer (Q P : F.Orbit) (f : Q ⟶ P) :
    letI := F.orbitHomAction Q P
    MulAction.stabilizer (Aut Q) f = F.orbitHomStabilizer f := by
  letI := F.orbitHomAction Q P
  ext a
  change a.inv ≫ f = f ↔ a.hom ≫ f = f
  constructor
  · intro h
    calc
      a.hom ≫ f = a.hom ≫ (a.inv ≫ f) := by rw [h]
      _ = f := a.hom_inv_id_assoc f
  · intro h
    calc
      a.inv ≫ f = a.inv ≫ (a.hom ≫ f) := by rw [h]
      _ = f := a.inv_hom_id_assoc f

variable {L T : Subgroup S} (hLT : L ≤ T)

theorem relativeNormalizerToAut_fixes_inclusion (n : F.relativeNormalizer T L) :
    (F.relativeNormalizerToAut T L n).hom ≫ F.toOrbit.map (F.inclusion hLT) =
      F.toOrbit.map (F.inclusion hLT) := by
  change F.toOrbit.map _ ≫ F.toOrbit.map _ = _
  rw [← F.toOrbit.map_comp]
  apply (F.orbit_map_eq_iff _ _).mpr
  refine ⟨⟨n.val, n.property.2⟩, ?_⟩
  intro x
  apply Subtype.ext
  change x.val = n.val⁻¹ * (n.val * x.val * n.val⁻¹) * n.val
  group

/-- All automorphisms fixing an inclusion are induced by actual elements
of its target normalizing the source. -/
theorem relativeNormalizerToAut_range :
    (F.relativeNormalizerToAut T L).range =
      F.orbitHomStabilizer (F.toOrbit.map (F.inclusion hLT)) := by
  apply le_antisymm
  · rintro a ⟨n, rfl⟩
    exact F.relativeNormalizerToAut_fixes_inclusion hLT n
  · intro a ha
    let c := F.groupEquivOfOrbitIso a
    let ca : (⟨L⟩ : F.Object) ⟶ ⟨L⟩ :=
      ⟨c.toMonoidHom, F.groupEquivOfOrbitIso_allowed a⟩
    have hca : F.toOrbit.map ca = a.hom := F.orbitRepresentative_map a.hom
    have hfix : F.toOrbit.map (ca ≫ F.inclusion hLT) =
        F.toOrbit.map (F.inclusion hLT) := by
      rw [F.toOrbit.map_comp, hca]
      exact ha
    obtain ⟨r, hr⟩ := (F.orbit_map_eq_iff _ _).mp hfix
    have hc (x : L) : (c x).val = r.val * x.val * r.val⁻¹ := by
      have hx := congrArg (fun z : T => z.val) (hr x)
      change x.val = r.val⁻¹ * (c x).val * r.val at hx
      calc
        (c x).val = r.val * (r.val⁻¹ * (c x).val * r.val) * r.val⁻¹ := by group
        _ = r.val * x.val * r.val⁻¹ := by rw [← hx]
    have hn : r.val ∈ Subgroup.normalizer (L : Set S) := by
      apply Subgroup.mem_normalizer_iff.mpr
      intro x
      constructor
      · intro hx
        exact hc ⟨x, hx⟩ ▸ (c ⟨x, hx⟩).property
      · intro hx
        let y := c.symm ⟨r.val * x * r.val⁻¹, hx⟩
        have hy : r.val * y.val * r.val⁻¹ = r.val * x * r.val⁻¹ := by
          rw [← hc y]
          exact congrArg Subtype.val (c.apply_symm_apply _)
        have hyx : y.val = x := mul_left_cancel (mul_right_cancel hy)
        exact hyx ▸ y.property
    refine ⟨⟨r.val, hn, r.property⟩, ?_⟩
    apply Iso.ext
    change F.toOrbit.map _ = a.hom
    rw [← hca]
    apply congrArg (fun z => F.toOrbit.map z)
    apply Subtype.ext
    ext x
    exact (hc x).symm

/-- Inclusion stabilizers in the outer automorphism action are p-groups. -/
theorem orbitHomStabilizer_inclusion_isPGroup (p : ℕ) (hS : IsPGroup p S) :
    IsPGroup p (F.orbitHomStabilizer (F.toOrbit.map (F.inclusion hLT))) := by
  rw [← F.relativeNormalizerToAut_range hLT]
  exact (hS.to_subgroup (F.relativeNormalizer T L)).of_surjective
    (F.relativeNormalizerToAut T L).rangeRestrict
    (F.relativeNormalizerToAut T L).rangeRestrict_surjective

theorem orbitHomStabilizer_comp_iso {Q Q' P : F.Orbit} (e : Q ≅ Q') (g : Q' ⟶ P) :
    F.orbitHomStabilizer (e.hom ≫ g) =
      (F.orbitHomStabilizer g).comap (Aut.autMulEquivOfIso e).toMonoidHom := by
  ext a
  change a.hom ≫ (e.hom ≫ g) = e.hom ≫ g ↔
    (e.inv ≫ a.hom ≫ e.hom) ≫ g = g
  constructor
  · intro h
    rw [Category.assoc, Category.assoc, h, e.inv_hom_id_assoc]
  · intro h
    have hh := congrArg (fun t => e.hom ≫ t) h
    simpa only [Category.assoc, e.hom_inv_id_assoc] using hh

/-- Every isotropy group in the automorphism action on fusion-orbit
morphisms is a p-group, without requiring saturation. -/
theorem orbitHomStabilizer_isPGroup (p : ℕ) (hS : IsPGroup p S)
    {Q P : F.Orbit} (f : Q ⟶ P) : IsPGroup p (F.orbitHomStabilizer f) := by
  rw [← F.arrow_factorization f, F.orbitHomStabilizer_comp_iso]
  exact (F.orbitHomStabilizer_inclusion_isPGroup (F.arrowImage_le f) p hS).comap_of_injective
    (Aut.autMulEquivOfIso (F.arrowImageIso f)).toMonoidHom
    (Aut.autMulEquivOfIso (F.arrowImageIso f)).injective

end Sharpness.FusionSystem
