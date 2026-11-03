import Sharpness.Unconditional.CentralizerCoverProjection
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-! The actual centralizer centric orbit category inside a fiber of the
centralizer-cover projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory Opposite
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (E : F.ElementaryCategory p) (C : F.AKOCentralizerInput p hS sat E)

private theorem local_hom_fixes {P Q : Subgroup (F.centralizerGroup p E)}
    (hP : F.elementaryInCentralizer p E ≤ P) (g : P →* Q) (hg : C.system.IsHom g)
    (z : F.elementaryInCentralizer p E) :
    (g ⟨z.val, hP z.property⟩).val = z.val := by
  obtain ⟨_, f, _, hfP, hfZ⟩ := (C.hom_iff g).mp hg
  exact (hfP ⟨z.val, hP z.property⟩).symm.trans (hfZ z)

def localCentricCoverObject (P : C.system.CentricOrbit) : F.CentralizerCover p where
  centric := (F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
    (F.yalcinCentralizerCentricInput p hS sat E C).centric).obj P
  elementary := E.obj.subgroup
  nontrivial := E.property.1
  le_subgroup := by
    intro z hz
    exact ⟨⟨z, F.elementary_le_centralizer p E hz⟩,
      F.elementaryInCentralizer_le_of_centric p hS sat E C P.obj.as.subgroup P.property hz, rfl⟩
  centralizes := by
    intro z hz
    apply Subgroup.mem_centralizer_iff.mpr
    rintro x ⟨y, _, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.mp y.property) z hz).symm
  exponent z hz := congrArg Subtype.val (E.property.2.2.1 ⟨z, hz⟩)

def localCentricCoverMap {P Q : C.system.CentricOrbit} (f : P ⟶ Q) :
    F.localCentricCoverObject p hS sat E C P ⟶ F.localCentricCoverObject p hS sat E C Q := by
  let g := C.system.orbitRepresentative f.hom
  let a := (F.subsystemRawFunctor (F.centralizerGroup p E) C.system C.embedding).map g
  refine ⟨(F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
    (F.yalcinCentralizerCentricInput p hS sat E C).centric).map f, a, ?_, ?_⟩
  · change (F.subsystemOrbitFunctor (F.centralizerGroup p E) C.system C.embedding).map
      (C.system.toOrbit.map g) = _
    rw [C.system.orbitRepresentative_map]
    rfl
  · intro z
    refine ⟨z, ?_⟩
    let z' : F.elementaryInCentralizer p E :=
      ⟨⟨z.val, F.elementary_le_centralizer p E z.property⟩, z.property⟩
    have hP := F.elementaryInCentralizer_le_of_centric p hS sat E C P.obj.as.subgroup P.property
    have hf := local_hom_fixes F p hS sat E C hP g.val g.property z'
    change (ambientHom (F.centralizerGroup p E) g.val
      (subgroupAmbientEquiv (F.centralizerGroup p E) P.obj.as.subgroup
        ⟨z'.val, hP z'.property⟩)).val = z.val
    rw [ambientHom_apply]
    exact congrArg (fun x : F.centralizerGroup p E => x.val) hf

def localCentricToCentralizedCover : C.system.CentricOrbit ⥤ F.CentralizedCentralizerCover p where
  obj P := ⟨F.localCentricCoverObject p hS sat E C P, E.property.2.2.2⟩
  map f := ObjectProperty.homMk (F.localCentricCoverMap p hS sat E C f)
  map_id P := by
    apply InducedCategory.hom_ext
    apply Subtype.ext
    exact (F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
      (F.yalcinCentralizerCentricInput p hS sat E C).centric).map_id P
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply Subtype.ext
    exact (F.subsystemCentricFunctor (F.centralizerGroup p E) C.system C.embedding
      (F.yalcinCentralizerCentricInput p hS sat E C).centric).map_comp f g

theorem localCentricToCentralizedCover_projection_map {P Q : C.system.CentricOrbit} (f : P ⟶ Q) :
    (F.centralizerCoverProjection p).map ((F.localCentricToCentralizedCover p hS sat E C).map f) =
      𝟙 (op E) := by
  apply Quiver.Hom.unop_inj
  apply InducedCategory.hom_ext
  apply Subtype.ext
  apply MonoidHom.ext
  intro z
  let A := F.localCentricCoverObject p hS sat E C P
  let B := F.localCentricCoverObject p hS sat E C Q
  let g := C.system.orbitRepresentative f.hom
  let a := (F.subsystemRawFunctor (F.centralizerGroup p E) C.system C.embedding).map g
  apply A.inverseRestriction_unique B (F.localCentricCoverMap p hS sat E C f) z z a
  · change (F.subsystemOrbitFunctor (F.centralizerGroup p E) C.system C.embedding).map
      (C.system.toOrbit.map g) = _
    rw [C.system.orbitRepresentative_map]
    rfl
  · let z' : F.elementaryInCentralizer p E :=
      ⟨⟨z.val, F.elementary_le_centralizer p E z.property⟩, z.property⟩
    have hP := F.elementaryInCentralizer_le_of_centric p hS sat E C P.obj.as.subgroup P.property
    have hf := local_hom_fixes F p hS sat E C hP g.val g.property z'
    change (ambientHom (F.centralizerGroup p E) g.val
      (subgroupAmbientEquiv (F.centralizerGroup p E) P.obj.as.subgroup
        ⟨z'.val, hP z'.property⟩)).val = z.val
    rw [ambientHom_apply]
    exact congrArg (fun x : F.centralizerGroup p E => x.val) hf

def localCentricToCoverFiber : C.system.CentricOrbit ⥤
    Functor.Fiber (F.centralizerCoverProjection p) (op E) where
  obj P := ⟨(F.localCentricToCentralizedCover p hS sat E C).obj P, rfl⟩
  map f := by
    refine ⟨(F.localCentricToCentralizedCover p hS sat E C).map f, ?_⟩
    apply IsHomLift.of_fac' (F.centralizerCoverProjection p) (𝟙 (op E)) _ rfl rfl
    rw [F.localCentricToCentralizedCover_projection_map p hS sat E C f]
    apply Quiver.Hom.unop_inj
    apply InducedCategory.hom_ext
    apply Subtype.ext
    rfl
  map_id P := Subtype.ext ((F.localCentricToCentralizedCover p hS sat E C).map_id P)
  map_comp f g := Subtype.ext ((F.localCentricToCentralizedCover p hS sat E C).map_comp f g)

instance localCentricToCoverFiber_faithful : (F.localCentricToCoverFiber p hS sat E C).Faithful where
  map_injective h := by
    apply InducedCategory.hom_ext
    apply (F.subsystemOrbitFunctor (F.centralizerGroup p E) C.system C.embedding).map_injective
    exact congrArg (fun a => a.val.hom.val.hom) h

end Sharpness.FusionSystem
