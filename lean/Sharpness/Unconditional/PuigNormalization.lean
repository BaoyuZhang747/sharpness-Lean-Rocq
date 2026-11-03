import Sharpness.Unconditional.PuigCentricEpi
import Sharpness.Unconditional.PuigMaximalInduction

/-! Normalize centric spans by taking the actual image of the left leg.
For a span already prescribed on a subgroup, adjust its representative by
an inner automorphism so that this subgroup is contained literally in the
normalized image. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

abbrev puigObject (A : Subgroup S) (hA : F.IsCentric A) : F.CentricOrbit :=
  ⟨F.toOrbit.obj ⟨A⟩, hA⟩

def puigInclusion {A B : Subgroup S} {hA : F.IsCentric A} {hB : F.IsCentric B}
    (hAB : A ≤ B) : F.puigObject A hA ⟶ F.puigObject B hB :=
  ObjectProperty.homMk (F.toOrbit.map (F.inclusion hAB))

/-- Normalize one centric orbit morphism as an isomorphism followed by
the literal inclusion of its image. -/
theorem normalize_centric_arrow {X P : F.CentricOrbit} (a : X ⟶ P) :
    ∃ (A : Subgroup S) (hA : F.IsCentric A) (hAP : A ≤ P.obj.as.subgroup)
      (e : X ≅ F.puigObject A hA),
      e.hom ≫ F.puigInclusion hAP = a := by
  let a₀ := F.orbitRepresentative a.hom
  let A := F.imageSubgroup a₀
  have hA : F.IsCentric A := F.isoSystem.centricIn_of_iso
    (F.atomicImageEquiv a₀) (F.atomicImageEquiv_allowed a₀) X.property
  let e : X ≅ F.puigObject A hA :=
    ObjectProperty.isoMk _ (F.toOrbit.mapIso (F.imageIso a₀))
  refine ⟨A, hA, F.image_le a₀, e, ?_⟩
  apply InducedCategory.hom_ext
  change F.toOrbit.map (F.toImage a₀) ≫ F.toOrbit.map (F.inclusion (F.image_le a₀)) = a.hom
  rw [← F.toOrbit.map_comp, F.image_factorization, F.orbitRepresentative_map]

/-- An extension of an inclusion can be normalized with its original
subgroup still included literally in the image. -/
theorem normalize_centric_factor {R : Subgroup S} (hR : F.IsCentric R)
    {X P : F.CentricOrbit} (hRP : R ≤ P.obj.as.subgroup)
    (a : X ⟶ P) (b : F.puigObject R hR ⟶ X)
    (hb : b ≫ a = F.puigInclusion hRP) :
    ∃ (A : Subgroup S) (hA : F.IsCentric A) (hRA : R ≤ A)
      (hAP : A ≤ P.obj.as.subgroup) (e : X ≅ F.puigObject A hA),
      e.hom ≫ F.puigInclusion hAP = a ∧
        b ≫ e.hom = F.puigInclusion hRA := by
  let a₀ := F.orbitRepresentative a.hom
  let b₀ := F.orbitRepresentative b.hom
  have heq : F.toOrbit.map (b₀ ≫ a₀) = F.toOrbit.map (F.inclusion hRP) := by
    have hh := congrArg (fun f : F.puigObject R hR ⟶ P => f.hom) hb
    change b.hom ≫ a.hom = F.toOrbit.map (F.inclusion hRP) at hh
    simpa only [Functor.map_comp, a₀, b₀, F.orbitRepresentative_map] using
      hh
  obtain ⟨t, ht⟩ := (F.orbit_map_eq_iff _ _).mp heq
  let a₁ := a₀ ≫ F.inner P.obj.as t
  have hraw : b₀ ≫ a₁ = F.inclusion hRP := by
    apply Subtype.ext
    ext x
    exact congrArg Subtype.val (ht x).symm
  let A := F.imageSubgroup a₁
  have hA : F.IsCentric A := F.isoSystem.centricIn_of_iso
    (F.atomicImageEquiv a₁) (F.atomicImageEquiv_allowed a₁) X.property
  have hRA : R ≤ A := by
    intro x hx
    refine ⟨b₀.val ⟨x, hx⟩, ?_⟩
    exact congrArg (fun f => (f.val ⟨x, hx⟩).val) hraw
  let e : X ≅ F.puigObject A hA :=
    ObjectProperty.isoMk _ (F.toOrbit.mapIso (F.imageIso a₁))
  refine ⟨A, hA, hRA, F.image_le a₁, e, ?_, ?_⟩
  · apply InducedCategory.hom_ext
    change F.toOrbit.map (F.toImage a₁) ≫ F.toOrbit.map (F.inclusion (F.image_le a₁)) = a.hom
    rw [← F.toOrbit.map_comp, F.image_factorization]
    simp only [a₁, F.toOrbit.map_comp, F.inner_orbit_eq_id, Category.comp_id,
      a₀, F.orbitRepresentative_map]
  · apply InducedCategory.hom_ext
    change b.hom ≫ F.toOrbit.map (F.toImage a₁) = F.toOrbit.map (F.inclusion hRA)
    rw [← F.orbitRepresentative_map b.hom, ← F.toOrbit.map_comp]
    congr 1
    apply Subtype.ext
    ext x
    exact congrArg (fun f => (f.val x).val) hraw

end Sharpness.FusionSystem
