import Sharpness.FusionMackey

/-!
The inclusion-map version of manuscript Lemma 2.5. The passage from arbitrary
orbit morphisms to actual subgroup inclusions is proved by the concrete
image factorization. Published simple-functor classification supplies only
the explicit simplicity and minimality hypotheses below.
-/
set_option autoImplicit false
noncomputable section
universe u w
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

def arrowImage {P T : F.Orbit} (f : P ⟶ T) : Subgroup S :=
  F.imageSubgroup (F.orbitRepresentative f)

theorem arrowImage_le {P T : F.Orbit} (f : P ⟶ T) : F.arrowImage f ≤ T.as.subgroup :=
  F.image_le (F.orbitRepresentative f)

def arrowImageIso {P T : F.Orbit} (f : P ⟶ T) :
    P ≅ F.toOrbit.obj ⟨F.arrowImage f⟩ :=
  F.toOrbit.mapIso (F.imageIso (F.orbitRepresentative f))

def arrowImageInclusion {P T : F.Orbit} (f : P ⟶ T) :
    F.toOrbit.obj ⟨F.arrowImage f⟩ ⟶ T :=
  F.toOrbit.map (F.inclusion (F.arrowImage_le f))

theorem arrow_factorization {P T : F.Orbit} (f : P ⟶ T) :
    (F.arrowImageIso f).hom ≫ F.arrowImageInclusion f = f := by
  change F.toOrbit.map (F.toImage (F.orbitRepresentative f)) ≫
    F.toOrbit.map (F.inclusion (F.image_le (F.orbitRepresentative f))) = f
  rw [← F.toOrbit.map_comp, F.image_factorization]
  exact F.orbitRepresentative_map f

def MinimalInclusionIndex (Q T : F.Orbit) : Type u :=
  {L : Subgroup S // L ≤ T.as.subgroup ∧ Nonempty (Q ≅ F.toOrbit.obj ⟨L⟩)}

def minimalInclusion {Q T : F.Orbit} (L : F.MinimalInclusionIndex Q T) :
    F.toOrbit.obj ⟨L.val⟩ ⟶ T := F.toOrbit.map (F.inclusion L.property.1)

variable [Finite S] {k : Type w} [Field k] (M : F.FullMackey k) (Q : F.Orbit)
    (small_zero : ∀ P, F.orbitOrder P < F.orbitOrder Q → ∀ x : M.Value P, x = 0)
    (simple : M.IsSimple) (nonzero : ∃ x : M.Value Q, x ≠ 0)

include small_zero simple nonzero

/-- Generation by transfers along actual inclusions of subgroups in the
minimal orbit-isomorphism class. -/
theorem simple_inclusion_generation (T : F.Orbit) :
    (⨆ L : F.MinimalInclusionIndex Q T,
      LinearMap.range (M.push (F.minimalInclusion L))) = ⊤ := by
  have hle : M.generated Q T ≤
      ⨆ L : F.MinimalInclusionIndex Q T,
        LinearMap.range (M.push (F.minimalInclusion L)) := by
    refine iSup_le fun s y hy => ?_
    obtain ⟨x, rfl⟩ := hy
    let L : F.MinimalInclusionIndex Q T :=
      ⟨F.arrowImage s.2.2, F.arrowImage_le s.2.2,
        ⟨s.2.1.trans (F.arrowImageIso s.2.2)⟩⟩
    rw [← F.arrow_factorization s.2.2, M.push_comp, LinearMap.comp_apply]
    exact le_iSup (fun L : F.MinimalInclusionIndex Q T =>
      LinearMap.range (M.push (F.minimalInclusion L))) L
        ⟨M.push (F.arrowImageIso s.2.2).hom x, rfl⟩
  rw [M.transfer_generation Q small_zero simple nonzero T] at hle
  exact top_unique hle

/-- Restriction to those actual included subgroups detects every value. -/
theorem simple_inclusion_detection (T : F.Orbit) :
    Function.Injective (restrictionProduct
      (fun L : F.MinimalInclusionIndex Q T => M.pull (F.minimalInclusion L))) := by
  rw [restrictionProduct_injective_iff]
  intro x hx
  apply (restrictionProduct_injective_iff _).mp
    (M.restriction_detection Q small_zero simple nonzero T) x
  intro s
  let L : F.MinimalInclusionIndex Q T :=
    ⟨F.arrowImage s.2.2, F.arrowImage_le s.2.2,
      ⟨s.2.1.trans (F.arrowImageIso s.2.2)⟩⟩
  have hi := hx L
  rw [← F.arrow_factorization s.2.2, M.pull_comp, LinearMap.comp_apply]
  change M.pull (F.arrowImageIso s.2.2).hom (M.pull (F.minimalInclusion L) x) = 0
  rw [hi, map_zero]

end Sharpness.FusionSystem
